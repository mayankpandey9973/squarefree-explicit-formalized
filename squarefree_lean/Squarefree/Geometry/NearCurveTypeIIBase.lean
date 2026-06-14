import Squarefree.Geometry.NearCurveGreedy
import Squarefree.Geometry.NearCurveStrip
import Squarefree.Geometry.NearCurveAux
import Mathlib

/-!
# §4.3 Type II backbone — base (writeup 608–615)

Witness extraction for Type II points, the line set `typeIILines`, and the first
mechanical sub-lemmas: the denominator bound `q ≤ 4√(δ/λ)`, the per-line
`ν`-count, and the harmonic-sum estimate.  Split out of `NearCurveTypeII` to keep
each module small.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## Witness extraction for Type II points (off `OnMajorArc`) -/

/-- The `OnMajorArc` witness package for a major point `n`, packaged so
`Classical.choose` yields a total witness *line* function. -/
private def typeIIWitnessProp (f : ℝ → ℝ) (N δ : ℝ) (n : ℤ) : Prop :=
  ∃ (D : MajorLine) (a b : ℤ),
    a ∈ nearSet f N δ ∧ b ∈ nearSet f N δ ∧ n ∈ nearSet f N δ ∧
    a < n ∧ n < b ∧ OnLine f D a ∧ OnLine f D n ∧ OnLine f D b ∧
    (D.denom : ℝ) ≤ denomCutoff / δ

private theorem typeIIWitnessProp_of_mem {n : ℤ} (hn : n ∈ typeIISet f N lam δ) :
    typeIIWitnessProp f N δ n := by
  have hmaj : n ∈ majorSet f N δ := (mem_typeIISet.mp hn).1
  exact (mem_majorSet.mp hmaj).2

/-- An arbitrary fallback line (used off `typeIISet`). -/
private def fallbackLineII : MajorLine := ⟨0, 0⟩

/-- The chosen Type II witness *line* of `n` (its `OnMajorArc` small-denominator line). -/
noncomputable def witnessLineII (f : ℝ → ℝ) (N δ : ℝ) (n : ℤ) : MajorLine :=
  if h : typeIIWitnessProp f N δ n then h.choose else fallbackLineII

/-- **Witness defining property.**  For `n ∈ typeIISet`, the chosen witness line
carries the `OnMajorArc` collinear triple `a < n < b` and has small denominator. -/
theorem witnessII_spec {n : ℤ} (hn : n ∈ typeIISet f N lam δ) :
    ∃ (a b : ℤ),
      a ∈ nearSet f N δ ∧ b ∈ nearSet f N δ ∧ n ∈ nearSet f N δ ∧
      a < n ∧ n < b ∧
      OnLine f (witnessLineII f N δ n) a ∧ OnLine f (witnessLineII f N δ n) n ∧
      OnLine f (witnessLineII f N δ n) b ∧
      ((witnessLineII f N δ n).denom : ℝ) ≤ denomCutoff / δ := by
  have h : typeIIWitnessProp f N δ n := typeIIWitnessProp_of_mem hn
  have hD : witnessLineII f N δ n = h.choose := by
    simp only [witnessLineII, h, dif_pos]
  obtain ⟨a, b, ha, hb, hnN, han, hnb, hoa, hon, hob, hq⟩ := h.choose_spec
  rw [hD]
  exact ⟨a, b, ha, hb, hnN, han, hnb, hoa, hon, hob, hq⟩

/-! ## The finite set of Type II witness lines -/

/-- **The Type II witness lines**: the (finite) image of `typeIISet` under the
witness-line map. -/
noncomputable def typeIILines (f : ℝ → ℝ) (N lam δ : ℝ) : Finset MajorLine :=
  (typeIISet f N lam δ).image (witnessLineII f N δ)

theorem mem_typeIILines {D : MajorLine} :
    D ∈ typeIILines f N lam δ ↔
      ∃ n ∈ typeIISet f N lam δ, witnessLineII f N δ n = D := by
  simp only [typeIILines, Finset.mem_image]

/-- For a Type II witness line `D`, its proper arc has `≥ 2` lattice points: the
carrier of `D` contains the collinear triple `a < n < b`, so `#lineCarrier' ≥ 3`,
and the carrier splits into ≤2 components each `≤ #properArc'`. -/
theorem two_le_properArc'II {D : MajorLine}
    (hD : D ∈ typeIILines f N lam δ) :
    2 ≤ (properArc' f N δ D).card := by
  classical
  obtain ⟨m, hm, hDm⟩ := mem_typeIILines.mp hD
  obtain ⟨a, b, haN, hbN, hmN, ham, hmb, hoa, hom, hob, _⟩ := witnessII_spec hm
  rw [hDm] at hoa hom hob
  have haC : a ∈ lineCarrier' f N δ D := mem_lineCarrier'.mpr ⟨haN, hoa⟩
  have hmC : m ∈ lineCarrier' f N δ D := mem_lineCarrier'.mpr ⟨hmN, hom⟩
  have hbC : b ∈ lineCarrier' f N δ D := mem_lineCarrier'.mpr ⟨hbN, hob⟩
  have hsub : ({a, m, b} : Finset ℤ) ⊆ lineCarrier' f N δ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact h ▸ haC
    · exact h ▸ hmC
    · exact h ▸ hbC
  have hcard3 : ({a, m, b} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have h3 : 3 ≤ (lineCarrier' f N δ D).card := by
    calc 3 = ({a, m, b} : Finset ℤ).card := hcard3.symm
      _ ≤ (lineCarrier' f N δ D).card := Finset.card_le_card hsub
  have h2 : (lineCarrier' f N δ D).card ≤ 2 * (properArc' f N δ D).card :=
    lineCarrier'_card_le_two_properArc'
  omega

/-! ## Lemma 2 — denominator bound `q ≤ 4√(δ/λ)` -/

/-- **`typeII_denom_le`** (writeup 612–615).  Every Type II witness line `D` has
`(D.denom : ℝ) ≤ 4√(δ/λ)`: its proper arc has `≥ 2` lattice points, so
`q = D.denom ≤ span ≤ 4√(δ/λ)`. -/
theorem typeII_denom_le (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ)
    (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    {D : MajorLine} (hD : D ∈ typeIILines f N lam δ) :
    (D.denom : ℝ) ≤ 4 * Real.sqrt (δ / lam) := by
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'II hD
  have hq_span : (D.denom : ℝ)
      ≤ (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ) :=
    one_denom_le_properArc'_span_of_two h2
  have hspan : (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)
      ≤ 4 * Real.sqrt (δ / lam) := properArc'_span_le hf hlam hδ hN2 hlower
  linarith

/-! ## Lemma 3 — per-line residue count `ν ≤ 4√(δ/λ)/q + 1` -/

/-- **`typeII_nu_per_line`** (writeup 654).  The proper arc of a Type II witness line
`D` has `#properArc' ≤ 4√(δ/λ)/q + 1`: its lattice points lie in one residue class
mod `q = D.denom` inside `[properLo', properHi']` (span `≤ 4√(δ/λ)`). -/
theorem typeII_nu_per_line (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ)
    (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (D : MajorLine) :
    ((properArc' f N δ D).card : ℝ)
      ≤ 4 * Real.sqrt (δ / lam) / (D.denom : ℝ) + 1 := by
  classical
  -- residue count `#properArc' ≤ (hi − lo)/q + 1`.
  have hcount : ((properArc' f N δ D).card : ℝ)
      ≤ ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)) / (D.denom : ℝ) + 1 := by
    refine onLine_window_card_le (f := f) (D := D)
      (lo := (properLo' f N δ D : ℝ)) (hi := (properHi' f N δ D : ℝ))
      ?_ (properArc' f N δ D) ?_
    · exact_mod_cast properLo'_le_properHi' (f := f) (N := N) (δ := δ) (D := D)
    · intro m hm
      obtain ⟨_, hon, hlo, hhi⟩ := mem_properArc'_facts hm
      exact ⟨⟨hlo, hhi⟩, hon⟩
  -- bound the numerator by `4√(δ/λ)`.
  have hspan : (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)
      ≤ 4 * Real.sqrt (δ / lam) := properArc'_span_le hf hlam hδ hN2 hlower
  have hqpos : (0 : ℝ) < (D.denom : ℝ) := by
    have := D.denom_pos; exact_mod_cast this
  have hdiv : ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)) / (D.denom : ℝ)
      ≤ 4 * Real.sqrt (δ / lam) / (D.denom : ℝ) :=
    div_le_div_of_nonneg_right hspan hqpos.le
  linarith


/-! ## Lemma 4 — the harmonic-sum bound -/

/-- **`typeII_harmonic_sum`** (writeup 662, the harmonic estimate).
`∑_{q=1}^{Qn} 1/q ≤ 1 + log Qn`.  Directly from
`harmonic_eq_sum_Icc` + `harmonic_le_one_add_log`. -/
theorem typeII_harmonic_sum (Qn : ℕ) :
    (∑ q ∈ Finset.Icc 1 Qn, (1 : ℝ) / q) ≤ 1 + Real.log Qn := by
  have hcast : (∑ q ∈ Finset.Icc 1 Qn, (1 : ℝ) / q)
      = ((harmonic Qn : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro q _
    rw [one_div]
  rw [hcast]
  exact_mod_cast harmonic_le_one_add_log Qn

end Squarefree.Geometry
