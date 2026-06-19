import Squarefree.Geometry.NearCurveTypeIClass
import Squarefree.Geometry.NearCurvePacking
import Mathlib

/-!
# §4.3 Type I greedy selected-set construction (writeup 599–604), LINE-keyed

This module performs the greedy disjoint-interval *construction* left abstract by
`exists_greedyPacking` in `NearCurvePacking`.  The §4.3 counting object is the
**un-windowed proper major arc** of a witness *line* (`properArc'` from
`NearCurveStrip`, the maximal strip component), not a per-point window.  Accordingly
the greedy is keyed by the **witness line** alone: one selected rep per distinct line.

* a **witness-choice** layer (`typeIWitness*`): every Type I point `n` carries a
  concrete witness line `D_n`, a near-set collinear triple `a_n < n < b_n` with
  `q_n ≤ 1/(4δ)`, and — definitionally from `OnTypeIArc` — the *component* span
  `properHi' D_n − properLo' D_n ≤ δ√(q_n/λ)`.  Extracted via `Classical.choose`.

* the per-LINE arc-density / residue-set (`densAt`, `windowResidueSet`), pointing at
  the un-windowed proper arc of `D_n`: `windowResidueSet n = properArc' D_n`,
  `densAt n = densArc' D_n`.  The per-arc count `windowResidueSet_card_le`
  (`#properArc' ≤ 2δ·densArc'`) is `arc_residue_count_two` over the `≥2`-point arc.

* the geometric **`GreedySel`** structure: a selected set `G ⊆ typeISet`, ≤1 rep per
  distinct line, whose proper-arc packing windows `[repArc g, repArc g + densAt g/24)`
  are pairwise disjoint (distinct-line gap, `offLine_gap_arc`) and whose line-sets
  cover `typeISet`.  From a `GreedySel` we build a `GreedyPacking`.

Disjointness uses that two distinct lines share at most one lattice point
(`onLine_eq_of_two_points`): the rep `repArc g'` of a *different* line cannot lie on
`D_g` (its proper arc has `≥2` points on `D_{g'}`), so it is off `D_g` and
`offLine_gap_arc` applies — the same-line case is vacuous.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## Witness extraction for Type I points -/

/-- The full Type I witness package for a point `n` (defaulted off `typeISet`):
the existential of `mem_typeISet`, packaged so `Classical.choose` yields total
witness functions.  For `n ∈ typeISet`, `witness_spec` recovers the data.

**Component-span design.**  We carry the *un-windowed proper-arc/component* span
`properHi' D − properLo' D ≤ δ√(q/λ)` (the faithful Type I condition `OnTypeIArc`),
not a per-witness `b − a` span.  The collinear triple `a < n < b` is kept only as
structural witness data (small denominator, near-set on `D`); the greedy reads its
counting object off the un-windowed proper arc of `D`. -/
private def typeIWitnessProp (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : Prop :=
  ∃ (D : MajorLine) (a b : ℤ),
    a ∈ nearSet f N δ ∧ b ∈ nearSet f N δ ∧ a < n ∧ n < b ∧
    OnLine f D a ∧ OnLine f D n ∧ OnLine f D b ∧
    (D.denom : ℝ) ≤ denomCutoff / δ ∧
    ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)) ≤ δ * Real.sqrt (D.denom / (256 * lam))

/-- **Witness extraction, DEFINITIONAL from `OnTypeIArc`.**  The faithful `typeISet`
(`NearCurveTypeIClass`) classifies a Type I point by exactly this package: a
small-denominator witness line `D`, a collinear near-set triple `a < n < b`, and the
*component* span `properHi' D − properLo' D ≤ δ√(q/λ)`. -/
private theorem typeIWitnessProp_of_mem {n : ℤ} (hn : n ∈ typeISet f N lam δ) :
    typeIWitnessProp f N lam δ n := by
  obtain ⟨D, a, b, ha, hb, _hn, hab, hnb, hoa, hon, hob, hq, hspan⟩ :=
    (mem_typeISet.mp hn).2
  exact ⟨D, a, b, ha, hb, hab, hnb, hoa, hon, hob, hq, hspan⟩

/-- An arbitrary concrete fallback line (used off `typeISet`). -/
private def fallbackLine : MajorLine := ⟨0, 0⟩

/-- The chosen witness line for `n`. -/
private noncomputable def witnessLine (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : MajorLine :=
  if h : typeIWitnessProp f N lam δ n then h.choose else fallbackLine

/-- The chosen left arc endpoint for `n`. -/
private noncomputable def witnessLo (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : ℤ :=
  if h : typeIWitnessProp f N lam δ n then h.choose_spec.choose else 0

/-- The chosen right arc endpoint for `n`. -/
private noncomputable def witnessHi (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : ℤ :=
  if h : typeIWitnessProp f N lam δ n then h.choose_spec.choose_spec.choose else 0

/-- **Witness defining property.**  For `n ∈ typeISet`, the chosen witness data
satisfies the full witness conjunction (collinear near-set triple on `D` plus the
component span of `D`). -/
private theorem witness_spec {n : ℤ} (hn : n ∈ typeISet f N lam δ) :
    (witnessLo f N lam δ n) ∈ nearSet f N δ ∧ (witnessHi f N lam δ n) ∈ nearSet f N δ ∧
    (witnessLo f N lam δ n) < n ∧ n < (witnessHi f N lam δ n) ∧
    OnLine f (witnessLine f N lam δ n) (witnessLo f N lam δ n) ∧
    OnLine f (witnessLine f N lam δ n) n ∧
    OnLine f (witnessLine f N lam δ n) (witnessHi f N lam δ n) ∧
    ((witnessLine f N lam δ n).denom : ℝ) ≤ denomCutoff / δ ∧
    ((properHi' f N δ (witnessLine f N lam δ n) : ℝ)
        - (properLo' f N δ (witnessLine f N lam δ n) : ℝ))
      ≤ δ * Real.sqrt ((witnessLine f N lam δ n).denom / (256 * lam)) := by
  have h : typeIWitnessProp f N lam δ n := typeIWitnessProp_of_mem hn
  have hD : witnessLine f N lam δ n = h.choose := by
    simp only [witnessLine, h, dif_pos]
  have hLo : witnessLo f N lam δ n = h.choose_spec.choose := by
    simp only [witnessLo, h, dif_pos]
  have hHi : witnessHi f N lam δ n = h.choose_spec.choose_spec.choose := by
    simp only [witnessHi, h, dif_pos]
  rw [hD, hLo, hHi]
  exact h.choose_spec.choose_spec.choose_spec

/-! ## Per-line proper-arc density and residue-set (UN-WINDOWED)

The genuine §4.3 object is the **un-windowed proper major arc** of a witness line `D`
(`properArc'`, the maximal strip component).  Per Type I rep `g`, the residue-set is
`properArc' D_g`, the density is `densArc' D_g = (properHi' D_g − properLo' D_g)/(qδ)`,
and the proper-arc base is `properLo' D_g`. -/

/-- The proper-arc density `d(A_g) = (properHi' − properLo')/(q_g δ)` of `g`'s witness
**line** `D_g` (un-windowed). -/
noncomputable def densAt (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : ℝ :=
  densArc' f N δ (witnessLine f N lam δ n)

/-- The **un-windowed proper major arc** of `n`'s witness line `D_n` (writeup 532):
the maximal strip component `properArc' D_n`.  The genuine per-line counting object. -/
noncomputable def windowResidueSet (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : Finset ℤ :=
  properArc' f N δ (witnessLine f N lam δ n)

/-- The proper arc `properLo' ≤ properHi'` (it is a finset interval span). -/
theorem properLo'_le_properHi' {D : MajorLine} :
    (properLo' f N δ D : ℝ) ≤ (properHi' f N δ D : ℝ) := by
  by_cases h : (properArc' f N δ D).Nonempty
  · obtain ⟨m, hm⟩ := h
    have hlo : (properLo' f N δ D : ℝ) ≤ (m : ℝ) :=
      (mem_properArc'_facts hm).2.2.1
    have hhi : (m : ℝ) ≤ (properHi' f N δ D : ℝ) :=
      (mem_properArc'_facts hm).2.2.2
    linarith
  · simp only [properLo', properHi', h, dif_neg, not_false_iff, le_refl]

/-- `densArc'` is nonnegative (`properLo' ≤ properHi'`, `qδ > 0`). -/
private theorem densArc'_nonneg {D : MajorLine} (hδ : 0 < δ) :
    0 ≤ densArc' f N δ D := by
  have hq : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  have hlohi := properLo'_le_properHi' (f := f) (N := N) (δ := δ) (D := D)
  unfold densArc' arcDensity
  apply div_nonneg (by linarith)
  positivity

/-- `densAt` is nonnegative for a Type I point. -/
theorem densAt_nonneg {n : ℤ} (hδ : 0 < δ) (_hn : n ∈ typeISet f N lam δ) :
    0 ≤ densAt f N lam δ n :=
  densArc'_nonneg hδ

/-- The membership facts of every proper-arc point, packaged for
`arc_residue_count_two`. -/
private theorem properArc'_mem_window {D : MajorLine} :
    ∀ m ∈ properArc' f N δ D,
      (((properLo' f N δ D : ℝ) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (properHi' f N δ D : ℝ)) ∧ OnLine f D m) := by
  intro m hm
  obtain ⟨_, hon, hlo, hhi⟩ := mem_properArc'_facts hm
  exact ⟨⟨hlo, hhi⟩, hon⟩

/-- **Proper-arc residue spacing `q ≤ properHi'−properLo'`, from ≥2 lattice points.**
The proper-arc lattice points are `q`-separated (one residue class mod `q`,
`denom_dvd_sub_of_onLine`).  Given `≥2` of them, the two extreme endpoints differ by
one gap `≥ q`. -/
theorem one_denom_le_properArc'_span_of_two {D : MajorLine}
    (h2 : 2 ≤ (properArc' f N δ D).card) :
    (D.denom : ℝ)
      ≤ (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ) := by
  classical
  have hne : (properArc' f N δ D).Nonempty := Finset.card_pos.mp (by omega)
  have hloeq : properLo' f N δ D = (properArc' f N δ D).min' hne := by
    simp only [properLo', hne, dif_pos]
  have hhieq : properHi' f N δ D = (properArc' f N δ D).max' hne := by
    simp only [properHi', hne, dif_pos]
  set lo := (properArc' f N δ D).min' hne with hlo
  set hi := (properArc' f N δ D).max' hne with hhi
  have hlomem : lo ∈ properArc' f N δ D := (properArc' f N δ D).min'_mem hne
  have hhimem : hi ∈ properArc' f N δ D := (properArc' f N δ D).max'_mem hne
  have hlohi_ne : lo ≠ hi := by
    intro heq
    have hsub : properArc' f N δ D ⊆ {lo} := by
      intro x hx
      have hx1 : lo ≤ x := (properArc' f N δ D).min'_le x hx
      have hx2 : x ≤ hi := (properArc' f N δ D).le_max' x hx
      rw [← heq] at hx2
      simp only [Finset.mem_singleton]; omega
    have : (properArc' f N δ D).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    omega
  have hOn : ∀ {x}, x ∈ properArc' f N δ D → OnLine f D x :=
    fun hx => (mem_properArc'_facts hx).2.1
  have hq0 : 0 < D.denom := D.denom_pos
  have hdiv : D.denom ∣ (hi - lo) := denom_dvd_sub_of_onLine (hOn hhimem) (hOn hlomem)
  have hlh : lo ≤ hi := (properArc' f N δ D).min'_le hi hhimem
  have hpos : 0 < hi - lo := by omega
  have hle : D.denom ≤ hi - lo := Int.le_of_dvd hpos hdiv
  rw [hloeq, hhieq]
  have hR := (by exact_mod_cast hle : ((D.denom : ℝ)) ≤ ((hi : ℝ) - (lo : ℝ)))
  push_cast at hR ⊢; linarith

/-- **Three collinear near-set lattice points on a Type I witness line.**  The witness
data of a Type I point `n` provides `a := witnessLo n < n < b := witnessHi n`, all
near-set points on `D := witnessLine n`, hence `3 ≤ #(lineCarrier' D)`. -/
private theorem three_le_lineCarrier'_of_typeI {n : ℤ}
    (hn : n ∈ typeISet f N lam δ) :
    3 ≤ (lineCarrier' f N δ (witnessLine f N lam δ n)).card := by
  classical
  obtain ⟨haN, hbN, han, hnb, haOn, hnOn, hbOn, _, _⟩ := witness_spec hn
  set D := witnessLine f N lam δ n with hD
  set a := witnessLo f N lam δ n with ha
  set b := witnessHi f N lam δ n with hb
  have hnN : n ∈ nearSet f N δ := by
    have hmaj : n ∈ majorSet f N δ := (mem_typeISet.mp hn).1
    simp only [majorSet, Finset.mem_filter] at hmaj; exact hmaj.1
  have haC : a ∈ lineCarrier' f N δ D := mem_lineCarrier'.mpr ⟨haN, haOn⟩
  have hnC : n ∈ lineCarrier' f N δ D := mem_lineCarrier'.mpr ⟨hnN, hnOn⟩
  have hbC : b ∈ lineCarrier' f N δ D := mem_lineCarrier'.mpr ⟨hbN, hbOn⟩
  have hsub : ({a, n, b} : Finset ℤ) ⊆ lineCarrier' f N δ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact h ▸ haC
    · exact h ▸ hnC
    · exact h ▸ hbC
  have hcard3 : ({a, n, b} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  calc 3 = ({a, n, b} : Finset ℤ).card := hcard3.symm
    _ ≤ (lineCarrier' f N δ D).card := Finset.card_le_card hsub

/-- **Two lattice points on a Type I proper arc.**  Since `#(lineCarrier' D) ≥ 3` and
the carrier splits into ≤2 half-runs each `≤ #properArc'`, the proper arc has `≥ 2`
points. -/
private theorem two_le_properArc'_of_typeI {n : ℤ}
    (hn : n ∈ typeISet f N lam δ) :
    2 ≤ (properArc' f N δ (witnessLine f N lam δ n)).card := by
  set D := witnessLine f N lam δ n with hD
  have h3 : 3 ≤ (lineCarrier' f N δ D).card := three_le_lineCarrier'_of_typeI hn
  have h2 : (lineCarrier' f N δ D).card ≤ 2 * (properArc' f N δ D).card :=
    lineCarrier'_card_le_two_properArc'
  omega

/-- **§4.3 proper major-arc count `ν(A) ≤ 2δ d(A)`** (writeup 516–532, 601).  On a
witness line `D` supporting a Type I point, the un-windowed proper major arc has `≥ 2`
lattice points (its line carries the 3 collinear near-set points `a < n < b`), giving
`#properArc' = ν(A) ≤ 2·δ·d(A) = 2δ·densArc'`. -/
private theorem proper_major_arc_count
    (hδ : 0 < δ) {n : ℤ} (hn : n ∈ typeISet f N lam δ) :
    ((properArc' f N δ (witnessLine f N lam δ n)).card : ℝ)
      ≤ 2 * (δ * densArc' f N δ (witnessLine f N lam δ n)) := by
  set D := witnessLine f N lam δ n with hD
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'_of_typeI hn
  refine arc_residue_count_two (f := f) (D := D) (δ := δ)
    (a := properLo' f N δ D) (b := properHi' f N δ D) hδ ?_
    (one_denom_le_properArc'_span_of_two h2) _
    (properArc'_mem_window (f := f) (N := N) (δ := δ) (D := D))
  exact_mod_cast properLo'_le_properHi' (f := f) (N := N) (δ := δ) (D := D)

/-- **Per-arc residue count.**  For `n ∈ typeISet`, the proper-arc residue-set has
`#windowResidueSet n ≤ 2·δ·densAt n` — the proper major-arc count
`proper_major_arc_count`. -/
theorem windowResidueSet_card_le (hδ : 0 < δ) {n : ℤ} (hn : n ∈ typeISet f N lam δ) :
    ((windowResidueSet f N lam δ n).card : ℝ) ≤ 2 * (δ * densAt f N lam δ n) :=
  proper_major_arc_count hδ hn

/-! ## The greedy selection output and the packing it produces

A `GreedySel` is the geometric *output* of the greedy leftmost-uncovered
construction (writeup 599–604): a finite selected set `G ⊆ typeISet`, ≤1 rep per
distinct witness *line*, such that

* (`gap`) the proper-arc windows `[repArc g, repArc g + densAt g/24)` are pairwise
  disjoint (distinct-line gap), and
* (`cover`) the line-sets of `G` cover `typeISet`,
* (`base_mem`) each base `repArc g` lies in `[⌊N⌋, ⌊2N⌋]`. -/

/-- **The witness key** of a point `n`: its witness *line* `D_n = witnessLine n`.  In
the un-windowed design the proper-arc counting object `windowResidueSet n = properArc'
D_n` depends on `n` only through its line, so the greedy is indexed by lines (one rep
per distinct line). -/
private noncomputable def witnessKey (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : MajorLine :=
  witnessLine f N lam δ n

/-- The Type I points sharing rep `g`'s **witness line**.  Distinct reps (distinct
lines) have disjoint `lineSet`s, and every Type I point lies in the `lineSet` of its
own line's rep — this is the definitional cover. -/
noncomputable def lineSet (f : ℝ → ℝ) (N lam δ : ℝ) (g : ℤ) : Finset ℤ :=
  (typeISet f N lam δ).filter (fun n => witnessKey f N lam δ n = witnessKey f N lam δ g)

private theorem mem_lineSet {g n : ℤ} :
    n ∈ lineSet f N lam δ g ↔
      n ∈ typeISet f N lam δ ∧ witnessKey f N lam δ n = witnessKey f N lam δ g := by
  simp only [lineSet, Finset.mem_filter]

/-- `g ∈ lineSet g` whenever `g` is a Type I point (`g` shares its own line). -/
private theorem self_mem_lineSet {g : ℤ} (hg : g ∈ typeISet f N lam δ) :
    g ∈ lineSet f N lam δ g := mem_lineSet.mpr ⟨hg, rfl⟩

/-- Two points with the same witness line share the same proper arc and density. -/
private theorem windowResidueSet_eq_of_key {g n : ℤ}
    (h : witnessKey f N lam δ n = witnessKey f N lam δ g) :
    windowResidueSet f N lam δ n = windowResidueSet f N lam δ g := by
  simp only [witnessKey] at h
  simp only [windowResidueSet, h]

private theorem densAt_eq_of_key {g n : ℤ}
    (h : witnessKey f N lam δ n = witnessKey f N lam δ g) :
    densAt f N lam δ n = densAt f N lam δ g := by
  simp only [witnessKey] at h
  simp only [densAt, h]

/-- **Proper-arc left endpoint** (writeup 591, the first `x`-coordinate `n_j` of the
proper arc `A_j`): the left endpoint `properLo'` of the un-windowed proper major arc
of `g`'s witness line `D_g`; the packing window `[repArc g, repArc g + densArc'/24)` is
attached to it. -/
private noncomputable def repArc (f : ℝ → ℝ) (N lam δ : ℝ) (g : ℤ) : ℤ :=
  properLo' f N δ (witnessLine f N lam δ g)

/-- The geometric output of the §4.3 **line-indexed** greedy selection.  Each rep `g`
contributes its proper arc base `repArc g`. -/
structure GreedySel (f : ℝ → ℝ) (N lam δ : ℝ) where
  /-- The greedy selected reps (≤1 per distinct witness line). -/
  G : Finset ℤ
  /-- Selected reps are Type I points. -/
  mem : ∀ g ∈ G, g ∈ typeISet f N lam δ
  /-- Proper-arc packing-window *bases* `repArc g` lie in the near-set window
  `[⌊N⌋, ⌊2N⌋]`. -/
  base_mem : ∀ g ∈ G,
    (⌊N⌋ : ℝ) ≤ (repArc f N lam δ g : ℝ) ∧ (repArc f N lam δ g : ℝ) ≤ (⌊2 * N⌋ : ℝ)
  /-- The proper strip-arc densities are bounded (Type I shortness + curvature floor):
  `densAt g = d(A_g) ≤ N ≤ 24·N`. -/
  dens_le : ∀ g ∈ G, densAt f N lam δ g ≤ 24 * N
  /-- Proper-arc packing windows are pairwise disjoint (distinct-line gap, `/48`). -/
  gap : (G : Set ℤ).PairwiseDisjoint
    (fun g => Set.Ico (repArc f N lam δ g : ℝ)
      ((repArc f N lam δ g : ℝ) + densAt f N lam δ g / 48))
  /-- **Definitional cover**: every Type I point lies in its line-rep's `lineSet`. -/
  cover : typeISet f N lam δ ⊆ G.biUnion (fun g => lineSet f N lam δ g)
  /-- **≤2-components per line** (writeup 532): the proper-arc residue count
  `#windowResidueSet g` (the line's proper major arc) dominates half its line's Type
  I points. -/
  line_two : ∀ g ∈ G,
    (lineSet f N lam δ g).card ≤ 2 * (windowResidueSet f N lam δ g).card

/-- **From a greedy selection to a full greedy packing (fully proven).**
`nu g := #windowResidueSet (repArc g)`, `lo g := repArc g`, `dens g := densAt (repArc g)`.
`nu_le` is `windowResidueSet_card_le`; `card_le_two_sum_nu` is `card_le_card cover`
chased through `card_biUnion_le` and the per-line factor 2 `line_two`. -/
noncomputable def greedyPacking_of_greedySel
    (hN2 : 2 ≤ N) (_hlam : 0 < lam) (hδ : 0 < δ) (_hf : ContDiff ℝ 2 f)
    (_hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (S : GreedySel f N lam δ) :
    GreedyPacking f N lam δ where
  G := S.G
  lo := fun g => (repArc f N lam δ g : ℝ)
  dens := fun g => densAt f N lam δ g
  nu := fun g => ((windowResidueSet f N lam δ g).card : ℝ)
  densCap := 24 * N
  dens_nonneg := fun g hg => densAt_nonneg hδ (S.mem g hg)
  nu_le := fun g hg => windowResidueSet_card_le hδ (S.mem g hg)
  dens_le_cap := S.dens_le
  cap_le := by linarith only [hN2]
  base_mem := S.base_mem
  interval_disjoint := S.gap
  card_le_two_sum_nu := by
    classical
    have hcard_le : (typeISet f N lam δ).card
        ≤ (S.G.biUnion (fun g => lineSet f N lam δ g)).card :=
      Finset.card_le_card S.cover
    have hbu : (S.G.biUnion (fun g => lineSet f N lam δ g)).card
        ≤ ∑ g ∈ S.G, (lineSet f N lam δ g).card :=
      Finset.card_biUnion_le
    have hline : ∑ g ∈ S.G, (lineSet f N lam δ g).card
        ≤ ∑ g ∈ S.G, 2 * (windowResidueSet f N lam δ g).card :=
      Finset.sum_le_sum S.line_two
    have hchain : (typeISet f N lam δ).card
        ≤ ∑ g ∈ S.G, 2 * (windowResidueSet f N lam δ g).card :=
      le_trans hcard_le (le_trans hbu hline)
    have hcastsum : ((∑ g ∈ S.G, 2 * (windowResidueSet f N lam δ g).card
          : ℕ) : ℝ)
        = 2 * ∑ g ∈ S.G, ((windowResidueSet f N lam δ g).card : ℝ) := by
      rw [Finset.mul_sum]
      push_cast
      rfl
    calc ((typeISet f N lam δ).card : ℝ)
        ≤ ((∑ g ∈ S.G, 2 * (windowResidueSet f N lam δ g).card
            : ℕ) : ℝ) := by exact_mod_cast hchain
      _ = 2 * ∑ g ∈ S.G, ((windowResidueSet f N lam δ g).card : ℝ) :=
          hcastsum

/-! ## The greedy *line-rep* selection (writeup 599–604, LINE-indexed)

The §4.3 greedy is indexed by *witness lines* / proper-arc representatives, not by
points: each selected rep `g` carries a distinct witness line, with at most ONE rep
per distinct line.  We make the selection concrete: process `typeISet` in ascending
order and fold, marking a point `n` *covered* if some already-selected rep `g` has the
**same witness line** (`witnessKey g = witnessKey n`); otherwise we select `n` as the
rep for its line.

* **`cover` is DEFINITIONAL**: every Type I point `n` shares the witness line of the
  rep selected for its line, hence lies in that rep's `lineSet`.
* **Disjointness** (`offLine_gap_arc`) is invoked between reps with DISTINCT lines;
  the rep of the other line lies *off* `D_g` (two distinct lines meet in ≤1 lattice
  point), so the off-line gap closes it. -/

/-- `n` is *covered* by the already-selected reps `sel`: some rep `g ∈ sel` has the
**same witness line** as `n` (`witnessKey g = witnessKey n`).  This enforces the
≤1-rep-per-line invariant of the line-indexed greedy. -/
private def isCoveredBy (f : ℝ → ℝ) (N lam δ : ℝ) (sel : List ℤ) (n : ℤ) : Prop :=
  ∃ g ∈ sel, witnessKey f N lam δ g = witnessKey f N lam δ n

/-- One greedy step: prepend `n` to the selected list unless it is already covered. -/
private noncomputable def greedyStep (f : ℝ → ℝ) (N lam δ : ℝ)
    (sel : List ℤ) (n : ℤ) : List ℤ :=
  if isCoveredBy f N lam δ sel n then sel else n :: sel

/-- The greedy selected list: fold `greedyStep` over `typeISet` in ascending order. -/
private noncomputable def greedySelList (f : ℝ → ℝ) (N lam δ : ℝ) : List ℤ :=
  ((typeISet f N lam δ).sort (· ≤ ·)).foldl (greedyStep f N lam δ) []

/-- The greedy selected set. -/
private noncomputable def greedySelSet (f : ℝ → ℝ) (N lam δ : ℝ) : Finset ℤ :=
  (greedySelList f N lam δ).toFinset

/-- **Fold invariant: every selected element comes from the processed prefix.** -/
private theorem mem_foldl_greedyStep {l : List ℤ} :
    ∀ {sel : List ℤ} {acc : Finset ℤ},
      (∀ x ∈ sel, x ∈ acc) →
      ∀ x ∈ l.foldl (greedyStep f N lam δ) sel, x ∈ acc ∨ x ∈ l := by
  induction l with
  | nil => intro sel acc hsel x hx; exact Or.inl (hsel x hx)
  | cons n t ih =>
      intro sel acc hsel x hx
      have hstep : ∀ y ∈ greedyStep f N lam δ sel n, y ∈ insert n acc := by
        intro y hy
        unfold greedyStep at hy
        by_cases hc : isCoveredBy f N lam δ sel n
        · rw [if_pos hc] at hy; exact Finset.mem_insert_of_mem (hsel y hy)
        · rw [if_neg hc] at hy
          rcases List.mem_cons.mp hy with h | h
          · exact h ▸ Finset.mem_insert_self n acc
          · exact Finset.mem_insert_of_mem (hsel y h)
      have := ih (sel := greedyStep f N lam δ sel n) (acc := insert n acc) hstep x hx
      rcases this with h | h
      · rcases Finset.mem_insert.mp h with h' | h'
        · exact Or.inr (List.mem_cons.mpr (Or.inl h'))
        · exact Or.inl h'
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- **`greedySelSet ⊆ typeISet`** — selected points are Type I points. -/
private theorem greedySelSet_subset :
    ∀ g ∈ greedySelSet f N lam δ, g ∈ typeISet f N lam δ := by
  intro g hg
  rw [greedySelSet, List.mem_toFinset, greedySelList] at hg
  have := mem_foldl_greedyStep (f := f) (N := N) (lam := lam) (δ := δ)
    (l := (typeISet f N lam δ).sort (· ≤ ·)) (sel := []) (acc := (∅ : Finset ℤ))
    (by intro x hx; simp at hx) g hg
  rcases this with h | h
  · simp at h
  · exact (Finset.mem_sort _).mp h

/-! ### Fold invariants for the greedy geometry (`gap` and `cover`) -/

/-- The pairwise *gap* relation on the selected reps: `b` and `a` have **distinct
witness lines**.  This is the line-indexed disjointness relation: it holds for any two
reps because the greedy never selects two reps with the same line. -/
private def gapRel (f : ℝ → ℝ) (N lam δ : ℝ) (b a : ℤ) : Prop :=
  witnessKey f N lam δ a ≠ witnessKey f N lam δ b

/-- **Gap fold invariant.**  If `sel` is pairwise-`gapRel`, then so is the result of
folding `greedyStep`. -/
private theorem pairwise_gapRel_foldl {l : List ℤ} :
    ∀ {sel : List ℤ}, sel.Pairwise (gapRel f N lam δ) →
      (l.foldl (greedyStep f N lam δ) sel).Pairwise (gapRel f N lam δ) := by
  induction l with
  | nil => intro sel hsel; simpa using hsel
  | cons n t ih =>
      intro sel hsel
      have hstep : (greedyStep f N lam δ sel n).Pairwise (gapRel f N lam δ) := by
        unfold greedyStep
        by_cases hc : isCoveredBy f N lam δ sel n
        · rw [if_pos hc]; exact hsel
        · rw [if_neg hc]
          refine List.pairwise_cons.mpr ⟨?_, hsel⟩
          intro a ha hcov
          exact hc ⟨a, ha, hcov⟩
      exact ih hstep

/-- **Descending-order fold invariant.**  Folding `greedyStep` over a strictly
increasing list `l`, starting from a `sel` all of whose elements are strictly below
every element of `l` (and pairwise `>`), yields a strictly decreasing list. -/
private theorem pairwise_gt_foldl {l : List ℤ} :
    ∀ {sel : List ℤ}, sel.Pairwise (· > ·) → (∀ x ∈ sel, ∀ y ∈ l, x < y) →
      l.Pairwise (· < ·) →
      (l.foldl (greedyStep f N lam δ) sel).Pairwise (· > ·) := by
  induction l with
  | nil => intro sel hsel _ _; simpa using hsel
  | cons n t ih =>
      intro sel hsel hlt hsorted
      have hsortedt : t.Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
      have hnt : ∀ y ∈ t, n < y := (List.pairwise_cons.mp hsorted).1
      have hstep_pw : (greedyStep f N lam δ sel n).Pairwise (· > ·) := by
        unfold greedyStep
        by_cases hc : isCoveredBy f N lam δ sel n
        · rw [if_pos hc]; exact hsel
        · rw [if_neg hc]
          refine List.pairwise_cons.mpr ⟨?_, hsel⟩
          intro a ha
          exact hlt a ha n List.mem_cons_self
      have hstep_lt : ∀ x ∈ greedyStep f N lam δ sel n, ∀ y ∈ t, x < y := by
        intro x hx y hy
        unfold greedyStep at hx
        by_cases hc : isCoveredBy f N lam δ sel n
        · rw [if_pos hc] at hx; exact hlt x hx y (List.mem_cons_of_mem _ hy)
        · rw [if_neg hc] at hx
          rcases List.mem_cons.mp hx with h | h
          · exact h ▸ hnt y hy
          · exact hlt x h y (List.mem_cons_of_mem _ hy)
      exact ih hstep_pw hstep_lt hsortedt

/-- Disjointness of two half-open windows from a one-sided gap. -/
private theorem window_disjoint_of_le {p q : ℤ}
    (h : (p : ℝ) + densAt f N lam δ p / 24 ≤ (q : ℝ)) :
    Disjoint (Set.Ico (p : ℝ) ((p : ℝ) + densAt f N lam δ p / 24))
      (Set.Ico (q : ℝ) ((q : ℝ) + densAt f N lam δ q / 24)) := by
  rw [Set.disjoint_left]
  intro x hx hx2
  simp only [Set.mem_Ico] at hx hx2
  linarith [hx.2, hx2.1]

/-- Every element of `sel` survives the rest of the fold. -/
private theorem greedyStep_foldl_mem_of_mem {l : List ℤ} {sel : List ℤ} {x : ℤ}
    (hx : x ∈ sel) : x ∈ l.foldl (greedyStep f N lam δ) sel := by
  induction l generalizing sel with
  | nil => simpa using hx
  | cons m t ih =>
      rw [List.foldl_cons]
      refine ih ?_
      unfold greedyStep
      by_cases hc : isCoveredBy f N lam δ sel m
      · rw [if_pos hc]; exact hx
      · rw [if_neg hc]; exact List.mem_cons_of_mem _ hx

/-- **Cover fold invariant (line-indexed).**  After folding over `l`, every processed
point `n ∈ l` has *some rep with its line* selected. -/
private theorem cover_foldl {l : List ℤ} :
    ∀ {sel : List ℤ}, ∀ n ∈ l,
      n ∈ (l.foldl (greedyStep f N lam δ) sel) ∨
        ∃ g ∈ (l.foldl (greedyStep f N lam δ) sel),
          witnessKey f N lam δ g = witnessKey f N lam δ n := by
  classical
  induction l with
  | nil => intro sel n hn; simp at hn
  | cons m t ih =>
      intro sel n hn
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hn with hnm | hnt
      · subst hnm
        by_cases hc : isCoveredBy f N lam δ sel n
        · obtain ⟨g, hg, hline⟩ := hc
          refine Or.inr ⟨g, ?_, hline⟩
          refine greedyStep_foldl_mem_of_mem ?_
          rw [greedyStep, if_pos ⟨g, hg, hline⟩]; exact hg
        · refine Or.inl (greedyStep_foldl_mem_of_mem ?_)
          rw [greedyStep, if_neg hc]; exact List.mem_cons_self
      · exact ih (sel := greedyStep f N lam δ sel m) n hnt

/-! ### Geometric gap step: greedy non-coverage ⇒ window separation -/

/-- A near-set point's real coordinate lies in `[N/2, 5N/2]` (when `N ≥ 2`). -/
private theorem nearSet_coord_mem_Icc {p : ℤ} (hN2 : 2 ≤ N) (hp : p ∈ nearSet f N δ) :
    (p : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := by
  rw [mem_nearSet] at hp
  obtain ⟨⟨hlo, hhi⟩, _⟩ := hp
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hloR : (⌊N⌋ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo
  have hhiR : (p : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by exact_mod_cast hhi
  have hflo : N - 1 < (⌊N⌋ : ℝ) := by have := Int.sub_one_lt_floor N; linarith
  have hfhi : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
  constructor
  · linarith
  · linarith

/-- For an `OnLine` near-set point `p`, the line-residual is small: `|g(p)| ≤ δ`. -/
private theorem lineRes_le_of_onLine_nearSet {D : MajorLine} {p : ℤ}
    (hp : p ∈ nearSet f N δ) (hon : OnLine f D p) :
    |lineRes f D (p : ℝ)| ≤ δ := by
  rw [lineRes, lineVal_eq_latticeY hon]
  exact nearSet_dist_le hp

/-- **Two distinct lattice points determine the line.**  If `n ≠ m` both lie on lines
`D` and `D'`, then `D = D'`. -/
private theorem onLine_eq_of_two_points {D D' : MajorLine} {n m : ℤ} (hnm : n ≠ m)
    (hDn : OnLine f D n) (hDm : OnLine f D m)
    (hD'n : OnLine f D' n) (hD'm : OnLine f D' m) : D = D' := by
  have hnmQ : ((n : ℚ) - (m : ℚ)) ≠ 0 := by
    intro h
    apply hnm
    have : (n : ℚ) = (m : ℚ) := by linarith
    exact_mod_cast this
  have key : ∀ E : MajorLine, OnLine f E n → OnLine f E m →
      E.slope = ((latticeY f n : ℚ) - (latticeY f m : ℚ)) / ((n : ℚ) - (m : ℚ)) := by
    intro E hEn hEm
    have h1 : (E.slope.den : ℤ) * latticeY f n = E.slope.num * n + E.shift := hEn
    have h2 : (E.slope.den : ℤ) * latticeY f m = E.slope.num * m + E.shift := hEm
    have hZ : (E.slope.den : ℤ) * (latticeY f n - latticeY f m)
        = E.slope.num * (n - m) := by ring_nf; omega
    have hQ : (E.slope.den : ℚ) * ((latticeY f n : ℚ) - (latticeY f m : ℚ))
        = (E.slope.num : ℚ) * ((n : ℚ) - (m : ℚ)) := by exact_mod_cast hZ
    have hqQ : (E.slope.den : ℚ) ≠ 0 := by
      have : 0 < E.slope.den := E.slope.pos; exact_mod_cast this.ne'
    have hslope : E.slope = (E.slope.num : ℚ) / (E.slope.den : ℚ) := (Rat.num_div_den _).symm
    rw [hslope, div_eq_div_iff hqQ hnmQ]
    linarith [hQ]
  have hslopes : D.slope = D'.slope := (key D hDn hDm).trans (key D' hD'n hD'm).symm
  have hp : D.slope.num = D'.slope.num := by rw [hslopes]
  have hq : (D.slope.den : ℤ) = (D'.slope.den : ℤ) := by rw [hslopes]
  have hshift : D.shift = D'.shift := by
    have e1 : (D.slope.den : ℤ) * latticeY f n = D.slope.num * n + D.shift := hDn
    have e2 : (D'.slope.den : ℤ) * latticeY f n = D'.slope.num * n + D'.shift := hD'n
    rw [hp, hq] at e1; omega
  cases D; cases D'; simp_all

/-- **The Type I proper-arc span bound, DEFINITIONAL** (writeup 583–585).  For a Type I
point `n`, the un-windowed proper strip-arc of its witness line `D := witnessLine n`
satisfies the **Type I** sharp bound `properHi' − properLo' ≤ δ·√(q/λ)`, `q := D.denom`.
This is exactly the `OnTypeIArc` filter condition, recovered through `witness_spec`. -/
theorem properArc_span_typeI {f : ℝ → ℝ} {N lam δ : ℝ}
    (_hlam : 0 < lam) {n : ℤ} (hn : n ∈ typeISet f N lam δ) :
    (properHi' f N δ (witnessLine f N lam δ n) : ℝ)
        - (properLo' f N δ (witnessLine f N lam δ n) : ℝ)
      ≤ δ * Real.sqrt ((witnessLine f N lam δ n).denom / (256 * lam)) :=
  (witness_spec hn).2.2.2.2.2.2.2.2

/-- **Density cap from the Type I span + curvature floor.**  `densAt n = densArc'(D_n) =
(properHi'−properLo')/(qδ) ≤ δ√(q/λ)/(qδ) = 1/√(qλ) ≤ 1/√λ ≤ N`, using `q ≥ 1`, the
Type I span `properArc_span_typeI`, and the curvature floor `N²λ ≥ 1`. -/
theorem densAt_le_floor {f : ℝ → ℝ} {N lam δ : ℝ}
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hfloor : 1 ≤ N ^ 2 * lam) {n : ℤ}
    (hn : n ∈ typeISet f N lam δ) :
    densAt f N lam δ n ≤ N := by
  set D := witnessLine f N lam δ n with hD
  set q : ℝ := (D.denom : ℝ) with hq
  have hqpos : 0 < q := by rw [hq]; have := D.denom_pos; exact_mod_cast this
  have hq1 : (1 : ℝ) ≤ q := by rw [hq]; have := D.denom_pos; exact_mod_cast this
  have hNpos : 0 < N := by linarith
  have hspan : (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)
      ≤ δ * Real.sqrt (q / lam) := by
    have hsp := properArc_span_typeI (f := f) (N := N) (δ := δ) hlam hn
    rw [← hD] at hsp
    -- weaken the tightened split `δ√(q/(256λ))` to the original `δ√(q/λ)`.
    have hmono : Real.sqrt (q / (256 * lam)) ≤ Real.sqrt (q / lam) :=
      Real.sqrt_le_sqrt (by
        apply div_le_div_of_nonneg_left (by positivity) hlam (by linarith [hlam]))
    calc (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)
        ≤ δ * Real.sqrt (q / (256 * lam)) := by rw [hq]; exact hsp
      _ ≤ δ * Real.sqrt (q / lam) := by
          apply mul_le_mul_of_nonneg_left hmono (le_of_lt hδ)
  have hdens : densAt f N lam δ n
      = ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)) / (q * δ) := by
    simp only [densAt, densArc', arcDensity, hD, hq]
  have hsqle : Real.sqrt (q / lam) ≤ N * q := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hlam]
    have hq2 : q ≤ q ^ 2 := by nlinarith only [hq1]
    nlinarith only [hfloor, hq2, hqpos, mul_pos hNpos hqpos, hlam.le,
      mul_nonneg (mul_nonneg (sq_nonneg N) hlam.le) (sq_nonneg q)]
  rw [hdens]
  have hqδ : (0 : ℝ) < q * δ := by positivity
  have hbound : ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)) / (q * δ)
      ≤ (δ * Real.sqrt (q / lam)) / (q * δ) :=
    (div_le_div_iff_of_pos_right hqδ).mpr hspan
  refine le_trans hbound ?_
  have heq : (δ * Real.sqrt (q / lam)) / (q * δ) = Real.sqrt (q / lam) / q := by
    field_simp
  rw [heq, div_le_iff₀ hqpos]; exact hsqle

/-- **The SECOND lattice point `properLo' + q` of a Type I proper arc lies in it**
(writeup 595 re-anchor, the `δ < 1/2` step).  For a Type I rep `g` with witness line
`D := witnessLine g` and `δ < 1/2`, the next residue point `properLo'(D) + D.denom`
after the base is again in the proper arc `properArc'(D)`.

PROOF (the `δ < 1/2` case split's payoff).  Write `q := D.denom`, `lo := properLo'(D)`,
`hi := properHi'(D)`.  The arc has `≥2` lattice points, so `q ≤ hi − lo`
(`one_denom_le_properArc'_span_of_two`), giving `lo + q ≤ hi`.  The strip-continuity
bound `properArc'_continuous_strip` then yields `|f(lo+q) − P(lo+q)| ≤ δ` on the
monotone proper side, where `P = lineVal D`.  But `OnLine f D lo` makes the line value
`P(lo+q) = round(f(lo)) + D.slope.num` an **integer** `Pint` (since
`q·(latticeY lo + p) = p·(lo+q) + shift`).  Hence `|f(lo+q) − Pint| ≤ δ < 1/2`, forcing
`round(f(lo+q)) = Pint` (`round_eq_iff`) — so `lo+q` is a near-set point ON `D`, i.e. in
the carrier; and lying between the proper-arc points `lo` and `hi`, it is on the proper
side (`mem_properArc'_of_between`). -/
private theorem second_point_mem_properArc'
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (_hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    {g : ℤ} (hg : g ∈ typeISet f N lam δ) :
    (properLo' f N δ (witnessLine f N lam δ g) + (witnessLine f N lam δ g).denom)
      ∈ properArc' f N δ (witnessLine f N lam δ g) := by
  classical
  set D := witnessLine f N lam δ g with hD
  set q : ℤ := D.denom with hq
  -- ≥2 lattice points on the proper arc.
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'_of_typeI hg
  have hne : (properArc' f N δ D).Nonempty := Finset.card_pos.mp (by omega)
  set lo := properLo' f N δ D with hloeq
  set hi := properHi' f N δ D with hhieq
  have hloArc : lo ∈ properArc' f N δ D := by rw [hloeq]; exact properLo'_mem hne
  have hhiArc : hi ∈ properArc' f N δ D := by rw [hhieq]; exact properHi'_mem hne
  obtain ⟨hloNear, hloOn, _, _⟩ := mem_properArc'_facts hloArc
  -- `q ≤ hi − lo`, hence `lo + q ≤ hi` and `lo ≤ lo + q`.
  have hspan : (q : ℝ) ≤ (hi : ℝ) - (lo : ℝ) :=
    one_denom_le_properArc'_span_of_two h2
  have hqpos : (0 : ℤ) < q := by rw [hq]; exact D.denom_pos
  have hloqhi : lo + q ≤ hi := by
    have : (lo : ℝ) + (q : ℝ) ≤ (hi : ℝ) := by linarith
    have h2 : ((lo + q : ℤ) : ℝ) ≤ (hi : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hloloq : lo ≤ lo + q := by omega
  -- The line value at `lo + q` is the integer `Pint := latticeY f lo + p`.
  set p : ℤ := D.slope.num with hpeq
  set Pint : ℤ := latticeY f lo + p with hPint
  have hqR : (D.denom : ℝ) ≠ 0 := by have := D.denom_pos; positivity
  -- The integer identity `p·(lo+q) + shift = Pint·q` (from `OnLine f D lo`).
  have hOnEq : (D.denom : ℤ) * latticeY f lo = D.slope.num * lo + D.shift := hloOn
  have hintEq : D.slope.num * (lo + q) + D.shift = Pint * D.denom := by
    rw [hPint, hpeq, hq]; ring_nf; ring_nf at hOnEq; omega
  have hlineVal : lineVal D ((lo + q : ℤ) : ℝ) = (Pint : ℝ) := by
    rw [lineVal, div_eq_iff hqR]
    have hc : ((D.slope.num * (lo + q) + D.shift : ℤ) : ℝ)
        = ((Pint * D.denom : ℤ) : ℝ) := by exact_mod_cast hintEq
    push_cast at hc ⊢; linarith
  -- Strip continuity: `|lineRes f D (lo+q)| ≤ δ`.
  have hloHi : lo ≤ hi := by omega
  have hstrip : |lineRes f D ((lo + q : ℤ) : ℝ)| ≤ δ := by
    refine properArc'_continuous_strip (lam := lam) hf hlam hN2 hlower hloArc hhiArc
      hloHi ((lo + q : ℤ) : ℝ) ?_
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · have : (lo : ℝ) ≤ ((lo + q : ℤ) : ℝ) := by exact_mod_cast hloloq
      exact this
    · have : ((lo + q : ℤ) : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hloqhi
      exact this
  -- So `|f(lo+q) − Pint| ≤ δ < 1/2`, forcing `round(f(lo+q)) = Pint`.
  have hfP : |f ((lo + q : ℤ) : ℝ) - (Pint : ℝ)| ≤ δ := by
    rw [lineRes, hlineVal] at hstrip; exact hstrip
  have hround : round (f ((lo + q : ℤ) : ℝ)) = Pint := by
    rw [round_eq_iff]
    rw [abs_le] at hfP
    refine Set.mem_Ico.mpr ⟨by linarith [hfP.1], by linarith [hfP.2]⟩
  -- `latticeY f (lo+q) = Pint`, giving near-set and OnLine.
  have hlatEq : latticeY f (lo + q) = Pint := by rw [latticeY]; exact_mod_cast hround
  have hnear : (lo + q) ∈ nearSet f N δ := by
    rw [mem_nearSet]
    constructor
    · -- `⌊N⌋ ≤ lo+q ≤ ⌊2N⌋`: `lo+q ∈ [lo, hi]`, both near-set.
      obtain ⟨⟨hloFl, _⟩, _⟩ := mem_nearSet.mp hloNear
      obtain ⟨hhiNear, _, _, _⟩ := mem_properArc'_facts hhiArc
      obtain ⟨⟨_, hhiFl⟩, _⟩ := mem_nearSet.mp hhiNear
      exact ⟨by omega, by omega⟩
    · -- `distInt(f(lo+q)) ≤ δ`: `|f(lo+q) − round| = |f(lo+q) − Pint| ≤ δ`.
      rw [distInt, hround]; exact hfP
  have hon : OnLine f D (lo + q) := by
    simp only [OnLine, hlatEq]
    rw [mul_comm] at hintEq; linarith [hintEq]
  -- `lo+q` is a carrier point between proper-arc points `lo` and `hi`.
  exact mem_properArc'_of_between hloArc hhiArc
    (mem_lineCarrier'.mpr ⟨hnear, hon⟩) hloloq hloqhi

/-- **There is an off-`D_g` near-set point in `g'`'s proper arc** (FULLY DERIVED).  For
two Type I reps `g ≠ g'` on **distinct** witness lines `D_g ≠ D_{g'}`, `g'`'s proper arc
`properArc'(D_{g'})` (which carries `≥2` lattice points on `D_{g'}`) has *some* point `p`
that is **off** `D_g`, with `p` a near-set point on `D_{g'}`, lying in
`[properLo'(D_{g'}), properHi'(D_{g'})]`.  This is the half of the writeup's line-595 claim
that is unconditionally true: two distinct lines share `≤1` lattice point
(`onLine_eq_of_two_points`), so at most one of `properLo'`, `properHi'` lies on `D_g` and
the other is off it. -/
private theorem exists_offLine_in_properArc'
    {g g' : ℤ} (hg' : g' ∈ typeISet f N lam δ)
    (hgap : witnessLine f N lam δ g ≠ witnessLine f N lam δ g') :
    ∃ p : ℤ, p ∈ nearSet f N δ ∧ OnLine f (witnessLine f N lam δ g') p ∧
      ¬ OnLine f (witnessLine f N lam δ g) p ∧
      (properLo' f N δ (witnessLine f N lam δ g') : ℝ) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ (properHi' f N δ (witnessLine f N lam δ g') : ℝ) := by
  classical
  set D := witnessLine f N lam δ g with hD
  set D' := witnessLine f N lam δ g' with hD'
  -- `g'`'s proper arc has `≥2` points: its `min'` and `max'` are distinct and on `D'`.
  have h2' : 2 ≤ (properArc' f N δ D').card := two_le_properArc'_of_typeI hg'
  have hne' : (properArc' f N δ D').Nonempty := Finset.card_pos.mp (by omega)
  set lo := properLo' f N δ D' with hloeq
  set hi := properHi' f N δ D' with hhieq
  have hloE : lo = (properArc' f N δ D').min' hne' := by
    rw [hloeq]; simp only [properLo', hne', dif_pos]
  have hhiE : hi = (properArc' f N δ D').max' hne' := by
    rw [hhieq]; simp only [properHi', hne', dif_pos]
  have hloArc : lo ∈ properArc' f N δ D' := by rw [hloE]; exact (properArc' f N δ D').min'_mem hne'
  have hhiArc : hi ∈ properArc' f N δ D' := by rw [hhiE]; exact (properArc' f N δ D').max'_mem hne'
  obtain ⟨hloNear, hloOn', hloLo, hloHi⟩ := mem_properArc'_facts hloArc
  obtain ⟨hhiNear, hhiOn', hhiLo, hhiHi⟩ := mem_properArc'_facts hhiArc
  -- `lo ≠ hi` (else the arc would be a singleton).
  have hlohi_ne : lo ≠ hi := by
    intro heq
    have hsub : properArc' f N δ D' ⊆ {lo} := by
      intro x hx
      have h1 : lo ≤ x := by rw [hloE]; exact (properArc' f N δ D').min'_le x hx
      have h2 : x ≤ hi := by rw [hhiE]; exact (properArc' f N δ D').le_max' x hx
      rw [← heq] at h2; simp only [Finset.mem_singleton]; omega
    have : (properArc' f N δ D').card ≤ 1 := by simpa using Finset.card_le_card hsub
    omega
  -- At most ONE of `lo`, `hi` lies on `D`: else `D = D'` by `onLine_eq_of_two_points`.
  by_cases hloOnD : OnLine f D lo
  · -- `lo` is on `D`; then `hi` must be off `D`.
    refine ⟨hi, hhiNear, hhiOn', ?_, ?_, le_refl _⟩
    · intro hhiOnD
      exact hgap (onLine_eq_of_two_points hlohi_ne hloOnD hhiOnD hloOn' hhiOn')
    · -- `lo ≤ hi`.
      have hlh : lo ≤ hi := by
        rw [hloE]; exact (properArc' f N δ D').min'_le hi hhiArc
      have hR : (lo : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hlh
      linarith
  · -- `lo` itself is off `D`.
    exact ⟨lo, hloNear, hloOn', hloOnD, le_refl _, by
      have hlh : lo ≤ hi := by
        rw [hloE]; exact (properArc' f N δ D').min'_le hi hhiArc
      exact_mod_cast hlh⟩

/-- **The §4.3 proper-arc directed distinct-line gap, writeup 595–598** (re-anchored,
`δ < 1/2`).  For two Type I reps `g ≠ g'` with **distinct witness lines** and
`repArc g ≤ repArc g'`, the right end of `g`'s `/48`-window does not reach `g'`'s base:
`repArc g + densArc'(D_g)/48 ≤ repArc g'`.

PROOF (writeup 595, the re-anchor).  Write `D := D_g`, `D' := D_{g'}`, `lo_k := repArc g'
= properLo'(D')`, `q_k := D'.denom`, `lo_j := repArc g = properLo'(D)`.  The two residue
points `lo_k` and `lo_k + q_k` are BOTH in `properArc'(D')` (`second_point_mem_properArc'`),
hence both on `D'`.  Two distinct lines share `≤1` point (`onLine_eq_of_two_points`), so at
most one of `{lo_k, lo_k+q_k}` is on `D`; the off-`D` one `m ∈ {lo_k, lo_k+q_k}` is a
near-set point with `lo_k ≤ m ≤ lo_k + q_k`.  `offLine_gap_arc` (base `lo_j`) gives
`d(A_j)/24 ≤ m − lo_j`, so `lo_k ≥ m − q_k ≥ lo_j + d(A_j)/24 − q_k`.  Finally `q_k ≤
d(A_j)/64` (from `q_k·δ ≤ denomCutoff = 1/64` and the `D`-span `q_j ≤ B_j − A_j`), giving
`lo_k ≥ lo_j + d(A_j)/24 − d(A_j)/64 ≥ lo_j + d(A_j)/48`. -/
private theorem properArc_directed_gap
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    {g g' : ℤ} (hg : g ∈ typeISet f N lam δ) (hg' : g' ∈ typeISet f N lam δ)
    (hgap : witnessKey f N lam δ g ≠ witnessKey f N lam δ g')
    (hle : (repArc f N lam δ g : ℝ) ≤ (repArc f N lam δ g' : ℝ)) :
    (repArc f N lam δ g : ℝ) + densAt f N lam δ g / 48 ≤ (repArc f N lam δ g' : ℝ) := by
  classical
  set D := witnessLine f N lam δ g with hD
  set D' := witnessLine f N lam δ g' with hD'
  have hDD' : D ≠ D' := by
    intro h; apply hgap; simp only [witnessKey, hD, hD'] at *; rw [h]
  -- `g`'s proper arc has `≥ 2` points.
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'_of_typeI hg
  have hne : (properArc' f N δ D).Nonempty := Finset.card_pos.mp (by omega)
  set pLo := properLo' f N δ D with hpLo
  set pHi := properHi' f N δ D with hpHi
  have hrepLo : repArc f N lam δ g = pLo := rfl
  have hdenom_le : (D.denom : ℝ) ≤ (pHi : ℝ) - (pLo : ℝ) :=
    one_denom_le_properArc'_span_of_two h2
  have hqpos : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  have hloHi : pLo < pHi := by
    have : (pLo : ℝ) < (pHi : ℝ) := by linarith
    exact_mod_cast this
  have hpLoArc : pLo ∈ properArc' f N δ D := by rw [hpLo]; exact properLo'_mem hne
  have hpHiArc : pHi ∈ properArc' f N δ D := by rw [hpHi]; exact properHi'_mem hne
  obtain ⟨hpLoNear, hpLoOn, _, _⟩ := mem_properArc'_facts hpLoArc
  obtain ⟨hpHiNear, hpHiOn, _, _⟩ := mem_properArc'_facts hpHiArc
  have hgA : |lineRes f D (pLo : ℝ)| ≤ δ := lineRes_le_of_onLine_nearSet hpLoNear hpLoOn
  have hgB : |lineRes f D (pHi : ℝ)| ≤ δ := lineRes_le_of_onLine_nearSet hpHiNear hpHiOn
  -- The Type I cutoff: `q_j ≤ denomCutoff/δ = 1/(64δ)`, hence the `1/(4δ)` form.
  have hqcut64 : (D.denom : ℝ) ≤ 1 / (64 * δ) := by
    have hcut := (witness_spec hg).2.2.2.2.2.2.2.1
    have hrw : denomCutoff / δ = 1 / (64 * δ) := by
      rw [denomCutoff]; field_simp
    rwa [hrw] at hcut
  have hqcut : (D.denom : ℝ) ≤ 1 / (4 * δ) := by
    have h64 : (1 : ℝ) / (64 * δ) ≤ 1 / (4 * δ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hδ])
    linarith [hqcut64]
  have hspan : ((pHi : ℝ) - (pLo : ℝ)) ≤ δ * Real.sqrt ((D.denom : ℝ) / (256 * lam)) :=
    properArc_span_typeI hlam hg
  -- `g'`'s proper arc has `≥ 2` points; `lo_k = repArc g'` and `lo_k + q_k` are BOTH on `D'`.
  set qk : ℤ := D'.denom with hqk
  set lok : ℤ := properLo' f N δ D' with hlok
  have hrepArc' : repArc f N lam δ g' = lok := rfl
  have hne' : (properArc' f N δ D').Nonempty := by
    have h2' : 2 ≤ (properArc' f N δ D').card := two_le_properArc'_of_typeI hg'
    exact Finset.card_pos.mp (by omega)
  have hlokArc : lok ∈ properArc' f N δ D' := by rw [hlok]; exact properLo'_mem hne'
  have hsndArc : lok + qk ∈ properArc' f N δ D' := by
    have := second_point_mem_properArc' (lam := lam) hN2 hlam hδ hδhalf hf hlower hg'
    simpa only [← hD', ← hqk, ← hlok] using this
  obtain ⟨hlokNear, hlokOn', _, _⟩ := mem_properArc'_facts hlokArc
  obtain ⟨hsndNear, hsndOn', _, _⟩ := mem_properArc'_facts hsndArc
  have hqkpos : (0 : ℤ) < qk := by rw [hqk]; exact D'.denom_pos
  -- At most one of `{lo_k, lo_k+q_k}` is on `D`; pick the off-`D` one `m`.
  have hlokne : lok ≠ lok + qk := by omega
  have hmexists : ∃ m : ℤ, (lok ≤ m ∧ m ≤ lok + qk) ∧ ¬ OnLine f D m ∧ m ∈ nearSet f N δ := by
    by_cases hlokOnD : OnLine f D lok
    · -- `lo_k` on `D`; then `lo_k + q_k` is off `D` (else `D = D'`).
      refine ⟨lok + qk, ⟨by omega, le_refl _⟩, ?_, hsndNear⟩
      intro hsndOnD
      exact hDD' (onLine_eq_of_two_points hlokne hlokOnD hsndOnD hlokOn' hsndOn')
    · exact ⟨lok, ⟨le_refl _, by omega⟩, hlokOnD, hlokNear⟩
  obtain ⟨m, ⟨hmlo, hmhi⟩, hmoff, hmNear⟩ := hmexists
  have hfm : |f (m : ℝ) - (latticeY f m : ℝ)| ≤ δ := nearSet_dist_le hmNear
  have hdensEq : densAt f N lam δ g = arcDensity D δ pLo pHi := rfl
  -- domain containment for `offLine_gap_arc` (over `[min pLo m, max pHi m]`).
  have hpLoIcc : (pLo : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := nearSet_coord_mem_Icc hN2 hpLoNear
  have hpHiIcc : (pHi : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := nearSet_coord_mem_Icc hN2 hpHiNear
  have hmIcc : (m : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := nearSet_coord_mem_Icc hN2 hmNear
  have hdom : ∀ x ∈ Set.Icc (min (pLo : ℝ) (m : ℝ)) (max (pHi : ℝ) (m : ℝ)),
      |iteratedDeriv 2 f x| ≤ 256 * lam := by
    intro x hx
    rw [Set.mem_Icc] at hx
    refine hupper x (Set.mem_Icc.mpr ⟨?_, ?_⟩)
    · rw [Set.mem_Icc] at hpLoIcc hmIcc
      exact le_trans (le_min hpLoIcc.1 hmIcc.1) hx.1
    · rw [Set.mem_Icc] at hpHiIcc hmIcc
      exact le_trans hx.2 (max_le hpHiIcc.2 hmIcc.2)
  have hm₀ : (pLo : ℝ) ∈ Set.Icc (pLo : ℝ) (pHi : ℝ) :=
    Set.mem_Icc.mpr ⟨le_refl _, by exact_mod_cast hloHi.le⟩
  -- `m ≠ pLo` (else `m` on `D`, contradicting off-`D`).
  have hmne : (m : ℝ) ≠ (pLo : ℝ) := by
    intro heq
    apply hmoff
    have heqI : m = pLo := by exact_mod_cast heq
    rw [heqI]; exact hpLoOn
  have hgap_arc :
      arcDensity D δ pLo pHi / 24 ≤ |(m : ℝ) - (pLo : ℝ)| :=
    offLine_gap_arc hf hlam hδ hloHi hqcut hdom hgA hgB hm₀ hgA hmne hmoff hfm hspan
  -- `m ≥ lo_k ≥ pLo`, so the abs is `m − pLo`.
  have hlokR : (pLo : ℝ) ≤ (lok : ℝ) := by rw [hrepLo, hrepArc'] at hle; exact hle
  have hmloR : (lok : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmlo
  rw [abs_of_nonneg (by linarith)] at hgap_arc
  -- `m ≤ lo_k + q_k`, so `lo_k ≥ m − q_k ≥ pLo + d(A_j)/24 − q_k`.
  have hmhiR : (m : ℝ) ≤ (lok : ℝ) + (qk : ℝ) := by
    have : (m : ℝ) ≤ ((lok + qk : ℤ) : ℝ) := by exact_mod_cast hmhi
    push_cast at this; linarith
  -- `q_k ≤ d(A_j)/64`: from `q_k·δ ≤ 1/64` and `q_j ≤ B_j − A_j` (so `q_j/(B_j−A_j) ≤ 1`).
  have hdens_pos_or : 0 ≤ arcDensity D δ pLo pHi := by
    rw [arcDensity]; apply div_nonneg (by linarith) (by positivity)
  have hqkcut : (qk : ℝ) * δ ≤ 1 / 64 := by
    have hcut := (witness_spec hg').2.2.2.2.2.2.2.1
    rw [denomCutoff] at hcut
    have : (D'.denom : ℝ) ≤ (1/64) / δ := hcut
    rw [hqk]
    rw [le_div_iff₀ hδ] at this; linarith [this]
  have hqk_le : (qk : ℝ) ≤ arcDensity D δ pLo pHi / 64 := by
    -- `d(A_j) = (B_j − A_j)/(q_j δ) ≥ q_j/(q_j δ) = 1/δ` so `q_k ≤ (1/64)/δ = d?`...
    -- direct: `d(A_j)·64 = 64(B_j−A_j)/(q_j δ) ≥ 64·q_j/(q_j δ) = 64/δ ≥ 64·q_k`
    -- since `q_k ≤ 1/(64δ)` ⟹ `64 q_k ≤ 1/δ ≤ 64·d?`.  We show `64 q_k ≤ d(A_j)`.
    rw [arcDensity, le_div_iff₀ (by norm_num : (0:ℝ) < 64)]
    have hqjpos : (0:ℝ) < (D.denom : ℝ) := hqpos
    -- `((B−A)/(qδ)) ≥ 1/δ` from `q ≤ B−A`.
    have hdge : (1:ℝ)/δ ≤ ((pHi : ℝ) - (pLo : ℝ)) / ((D.denom : ℝ) * δ) := by
      rw [div_le_div_iff₀ hδ (by positivity)]
      have : (D.denom : ℝ) ≤ (pHi : ℝ) - (pLo : ℝ) := hdenom_le
      nlinarith only [this, hqjpos, hδ]
    -- `q_k·64·δ ≤ 1`, so `q_k·64 ≤ 1/δ ≤ d(A_j)`.
    have hqk64 : (qk : ℝ) * 64 ≤ 1/δ := by
      rw [le_div_iff₀ hδ]; nlinarith only [hqkcut]
    calc (qk : ℝ) * 64 ≤ 1/δ := hqk64
      _ ≤ ((pHi : ℝ) - (pLo : ℝ)) / ((D.denom : ℝ) * δ) := hdge
  -- assemble: `lo_k ≥ m − q_k ≥ pLo + d/24 − d/64 ≥ pLo + d/48`.
  rw [hdensEq, hrepLo, hrepArc']
  set d : ℝ := arcDensity D δ pLo pHi with hd
  -- abstract `d ≥ 0`, the gap `d/24 ≤ m − pLo`, and `q_k ≤ d/64`.
  have hkey : d / 24 ≤ (m : ℝ) - (pLo : ℝ) := hgap_arc
  have hqk_le' : (qk : ℝ) ≤ d / 64 := hqk_le
  have hd0 : 0 ≤ d := hdens_pos_or
  -- `(lok : ℝ) ≥ m − qk ≥ pLo + d/24 − d/64 ≥ pLo + d/48`.
  have hstep : (pLo : ℝ) + d / 48 ≤ (lok : ℝ) := by
    have h1 : (m : ℝ) - (qk : ℝ) ≤ (lok : ℝ) := by linarith [hmhiR]
    have h2 : (pLo : ℝ) + d / 24 - d / 64 ≤ (m : ℝ) - (qk : ℝ) := by
      linarith [hkey, hqk_le']
    have h3 : (pLo : ℝ) + d / 48 ≤ (pLo : ℝ) + d / 24 - d / 64 := by linarith [hd0]
    linarith [h1, h2, h3]
  exact hstep

/-- **Distinct-line proper-arc window disjointness, FULLY DERIVED** from the directed
gap `properArc_directed_gap`. -/
private theorem gap_of_gapRel
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    {g g' : ℤ} (hg : g ∈ typeISet f N lam δ) (hg' : g' ∈ typeISet f N lam δ)
    (hgap : witnessKey f N lam δ g ≠ witnessKey f N lam δ g') :
    Disjoint
      (Set.Ico (repArc f N lam δ g : ℝ)
        ((repArc f N lam δ g : ℝ) + densAt f N lam δ g / 48))
      (Set.Ico (repArc f N lam δ g' : ℝ)
        ((repArc f N lam δ g' : ℝ) + densAt f N lam δ g' / 48)) := by
  rcases le_total (repArc f N lam δ g : ℝ) (repArc f N lam δ g' : ℝ) with hle | hle
  · have hgaple := properArc_directed_gap hN2 hlam hδ hδhalf hf hlower hupper hg hg' hgap hle
    rw [Set.disjoint_left]
    intro x hx hx2
    simp only [Set.mem_Ico] at hx hx2
    linarith [hx.2, hx2.1]
  · have hgaple := properArc_directed_gap hN2 hlam hδ hδhalf hf hlower hupper hg' hg hgap.symm hle
    rw [Set.disjoint_left]
    intro x hx hx2
    simp only [Set.mem_Ico] at hx hx2
    linarith [hx2.2, hx.1]

/-- **Order-extraction from a pairwise-related descending list.** -/
private theorem rel_of_lt_of_pairwise_gt {R : ℤ → ℤ → Prop} :
    ∀ {l : List ℤ}, l.Pairwise R → l.Pairwise (· > ·) →
      ∀ {p q : ℤ}, p ∈ l → q ∈ l → p < q → R q p := by
  intro l
  induction l with
  | nil => intro _ _ p q hp _ _; simp at hp
  | cons c t ih =>
      intro hR hgt p q hp hq hpq
      have hRhead := (List.pairwise_cons.mp hR).1
      have hRtail := (List.pairwise_cons.mp hR).2
      have hgthead := (List.pairwise_cons.mp hgt).1
      have hgttail := (List.pairwise_cons.mp hgt).2
      rcases List.mem_cons.mp hp with hpc | hpt
      · subst hpc
        rcases List.mem_cons.mp hq with hqc | hqt
        · subst hqc; exact absurd hpq (lt_irrefl _)
        · exact absurd (hgthead q hqt) (by simp [not_lt]; linarith)
      · rcases List.mem_cons.mp hq with hqc | hqt
        · subst hqc; exact hRhead p hpt
        · exact ih hRtail hgttail hpt hqt hpq

/-- **`repArc g` is a near-set coordinate** for a Type I rep `g`: it is
`properLo'(D_g)`, the `min'` of the nonempty proper arc, hence a near-set point on
`D_g`, so `⌊N⌋ ≤ repArc g ≤ ⌊2N⌋`. -/
private theorem repArc_mem_Icc {g : ℤ} (hg : g ∈ typeISet f N lam δ) :
    (⌊N⌋ : ℝ) ≤ (repArc f N lam δ g : ℝ) ∧
      (repArc f N lam δ g : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by
  set D := witnessLine f N lam δ g with hD
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'_of_typeI hg
  have hne : (properArc' f N δ D).Nonempty := Finset.card_pos.mp (by omega)
  have hloeq : repArc f N lam δ g = (properArc' f N δ D).min' hne := by
    show properLo' f N δ D = (properArc' f N δ D).min' hne
    simp only [properLo', dif_pos hne]
  have hmem : (properArc' f N δ D).min' hne ∈ properArc' f N δ D :=
    (properArc' f N δ D).min'_mem hne
  have hnear : (properArc' f N δ D).min' hne ∈ nearSet f N δ :=
    (mem_properArc'_facts hmem).1
  rw [mem_nearSet] at hnear
  obtain ⟨⟨hlo, hhi⟩, _⟩ := hnear
  rw [hloeq]
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- **Packing-window bases lie in `[⌊N⌋, ⌊2N⌋]`** (the bases-packing input). -/
private theorem greedySel_base_mem :
    ∀ g ∈ greedySelSet f N lam δ,
      (⌊N⌋ : ℝ) ≤ (repArc f N lam δ g : ℝ) ∧
        (repArc f N lam δ g : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by
  intro g hg
  exact repArc_mem_Icc (greedySelSet_subset g hg)

/-- **Density cap `densAt g ≤ 24·N`** (the bases-packing length cap), from the sharp
Type I cap `densAt_le_floor` (`densAt g ≤ N`) and `N ≥ 0`. -/
private theorem greedySel_dens_le
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hfloor : 1 ≤ N ^ 2 * lam) :
    ∀ g ∈ greedySelSet f N lam δ, densAt f N lam δ g ≤ 24 * N := by
  intro g hg
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have := densAt_le_floor hN2 hlam hδ hfloor (greedySelSet_subset g hg)
  linarith only [this, hN0]

/-! ### The ≤2-components combinatorics (LINE-keyed)

`lineSet g` consists of the Type I points sharing `g`'s **witness line** `D_g`.  Each
such `n` lies on `D_g` and is a near-set point, hence `lineSet g ⊆ lineCarrier' D_g`,
the un-windowed carrier, which splits into its ≤2 side half-runs each `≤ #properArc' =
#windowResidueSet g` (`lineCarrier'_card_le_two_properArc'`), giving `#lineSet g ≤
2·#windowResidueSet g`. -/

/-- A point of `lineSet g` lies on `D := witnessLine g` and is a near-set point. -/
private theorem mem_lineSet_facts {g n : ℤ} (hn : n ∈ lineSet f N lam δ g) :
    OnLine f (witnessLine f N lam δ g) n ∧ n ∈ nearSet f N δ := by
  obtain ⟨hnT, hwn⟩ := mem_lineSet.mp hn
  simp only [witnessKey] at hwn
  have hnnear : n ∈ nearSet f N δ := by
    have hmaj : n ∈ majorSet f N δ := (mem_typeISet.mp hnT).1
    simp only [majorSet, Finset.mem_filter] at hmaj; exact hmaj.1
  have hOnSelf : OnLine f (witnessLine f N lam δ n) n := (witness_spec hnT).2.2.2.2.2.1
  have hOn : OnLine f (witnessLine f N lam δ g) n := by rw [← hwn]; exact hOnSelf
  exact ⟨hOn, hnnear⟩

/-- **`lineSet g ⊆ lineCarrier' D_g`** (the un-windowed carrier): every point sharing
`g`'s witness line is a near-set point on `D_g`. -/
private theorem lineSet_subset_lineCarrier' {g : ℤ} :
    lineSet f N lam δ g ⊆ lineCarrier' f N δ (witnessLine f N lam δ g) := by
  intro n hn
  obtain ⟨hOn, hnear⟩ := mem_lineSet_facts hn
  exact mem_lineCarrier'.mpr ⟨hnear, hOn⟩

/-- **≤2-components-per-line** (writeup 532), FULLY PROVEN.  On each selected rep `g`,
the proper arc `windowResidueSet g = properArc' D_g` dominates *half* the line's Type I
points: `#lineSet g ≤ 2·#windowResidueSet g`. -/
private theorem line_two_components {g : ℤ} (_hg : g ∈ greedySelSet f N lam δ) :
    (lineSet f N lam δ g).card
      ≤ 2 * (windowResidueSet f N lam δ g).card := by
  calc (lineSet f N lam δ g).card
      ≤ (lineCarrier' f N δ (witnessLine f N lam δ g)).card :=
        Finset.card_le_card lineSet_subset_lineCarrier'
    _ ≤ 2 * (properArc' f N δ (witnessLine f N lam δ g)).card :=
        lineCarrier'_card_le_two_properArc'
    _ = 2 * (windowResidueSet f N lam δ g).card := rfl

/-- **The geometric facts of the greedy selection** (writeup 599–604, LINE-indexed). -/
private theorem greedySel_geometry
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hfloor : 1 ≤ N ^ 2 * lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    (∀ g ∈ greedySelSet f N lam δ,
        (⌊N⌋ : ℝ) ≤ (repArc f N lam δ g : ℝ) ∧
          (repArc f N lam δ g : ℝ) ≤ (⌊2 * N⌋ : ℝ)) ∧
      (∀ g ∈ greedySelSet f N lam δ, densAt f N lam δ g ≤ 24 * N) ∧
      ((greedySelSet f N lam δ : Set ℤ).PairwiseDisjoint
        (fun g => Set.Ico (repArc f N lam δ g : ℝ)
          ((repArc f N lam δ g : ℝ) + densAt f N lam δ g / 48))) ∧
      (typeISet f N lam δ ⊆
        (greedySelSet f N lam δ).biUnion (fun g => lineSet f N lam δ g)) ∧
      (∀ g ∈ greedySelSet f N lam δ,
        (lineSet f N lam δ g).card
          ≤ 2 * (windowResidueSet f N lam δ g).card) := by
  classical
  refine ⟨greedySel_base_mem,
    greedySel_dens_le hN2 hlam hδ hfloor, ?_, ?_, ?_⟩
  · have hpw : (greedySelList f N lam δ).Pairwise (gapRel f N lam δ) := by
      rw [greedySelList]; exact pairwise_gapRel_foldl (by simp)
    have hsortedlt : ((typeISet f N lam δ).sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort _).pairwise
    have hgtw : (greedySelList f N lam δ).Pairwise (· > ·) := by
      rw [greedySelList]
      exact pairwise_gt_foldl (by simp) (by simp) hsortedlt
    have hlinesne : ∀ p ∈ greedySelSet f N lam δ, ∀ q ∈ greedySelSet f N lam δ, p ≠ q →
        witnessKey f N lam δ p ≠ witnessKey f N lam δ q := by
      intro p hp q hq hpq
      have hpmem : p ∈ greedySelList f N lam δ := by
        rwa [greedySelSet, List.mem_toFinset] at hp
      have hqmem : q ∈ greedySelList f N lam δ := by
        rwa [greedySelSet, List.mem_toFinset] at hq
      rcases lt_or_gt_of_ne hpq with hlt | hgt
      · exact rel_of_lt_of_pairwise_gt hpw hgtw hpmem hqmem hlt
      · exact (rel_of_lt_of_pairwise_gt hpw hgtw hqmem hpmem hgt).symm
    intro p hp q hq hpne
    simp only [Finset.mem_coe] at hp hq
    have hpT : p ∈ typeISet f N lam δ := greedySelSet_subset p hp
    have hqT : q ∈ typeISet f N lam δ := greedySelSet_subset q hq
    exact gap_of_gapRel hN2 hlam hδ hδhalf hf hlower hupper hpT hqT (hlinesne p hp q hq hpne)
  · intro n hn
    have hnlist : n ∈ (typeISet f N lam δ).sort (· ≤ ·) := (Finset.mem_sort _).mpr hn
    have hcov := cover_foldl (f := f) (N := N) (lam := lam) (δ := δ)
      (l := (typeISet f N lam δ).sort (· ≤ ·)) (sel := []) n hnlist
    rw [← greedySelList] at hcov
    rcases hcov with hsel | ⟨g, hg, hline⟩
    · have hnG : n ∈ greedySelSet f N lam δ := by
        rw [greedySelSet, List.mem_toFinset]; exact hsel
      exact Finset.mem_biUnion.mpr ⟨n, hnG, mem_lineSet.mpr ⟨hn, rfl⟩⟩
    · have hgG : g ∈ greedySelSet f N lam δ := by
        rw [greedySelSet, List.mem_toFinset]; exact hg
      exact Finset.mem_biUnion.mpr ⟨g, hgG, mem_lineSet.mpr ⟨hn, hline.symm⟩⟩
  · intro g hg
    exact line_two_components hg

/-- **Every Type I configuration admits a greedy selection** (writeup 599–604). -/
theorem exists_greedySel
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hfloor : 1 ≤ N ^ 2 * lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    Nonempty (GreedySel f N lam δ) := by
  obtain ⟨hbase, hdens, hgap, hcov, htwo⟩ :=
    greedySel_geometry hN2 hlam hδ hδhalf hf hfloor hlower hupper
  exact ⟨{
    G := greedySelSet f N lam δ
    mem := greedySelSet_subset
    base_mem := hbase
    dens_le := hdens
    gap := hgap
    cover := hcov
    line_two := htwo }⟩

/-- **Every Type I set admits a greedy packing** (writeup 599–604). -/
theorem exists_greedyPacking
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hfloor : 1 ≤ N ^ 2 * lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    Nonempty (GreedyPacking f N lam δ) := by
  obtain ⟨S⟩ := exists_greedySel hN2 hlam hδ hδhalf hf hfloor hlower hupper
  exact ⟨greedyPacking_of_greedySel hN2 hlam hδ hf hlower S⟩

/-- **The Type I greedy-packing total** (writeup 599–605).
`#typeISet ≤ 384·(N·δ + 1)` (the `/48`-window doubles the `/24` constant). -/
theorem typeI_arc_sum
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ < 1/2) (hf : ContDiff ℝ 2 f)
    (hfloor : 1 ≤ N ^ 2 * lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    ((typeISet f N lam δ).card : ℝ) ≤ 384 * (N * δ + 1) := by
  obtain ⟨P⟩ := exists_greedyPacking hN2 hlam hδ hδhalf hf hfloor hlower hupper
  exact card_le_of_greedyPacking (by linarith) hδ (by linarith) P

end Squarefree.Geometry
