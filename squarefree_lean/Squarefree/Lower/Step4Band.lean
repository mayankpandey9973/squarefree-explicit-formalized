import Mathlib

/-!
# §5 large-defect `v`-band lattice count

The foundational counting step of the §5 large-defect "square-difference" localization.

If a finite set `F` of reals consists of points of the lattice `ℓ₁⁻¹ℤ`, each lying in the
`v²`-band `|C·v² − c| ≤ E` for a common center `c` and a positive scale `C` (with
`0 ≤ E < c`), then the band pins `v²` to an interval of length `2E/C` about `c/C`, i.e. `v`
to two intervals each of length `≤ E/√(C(c−E))`; each holds `≤ 1 + ℓ₁·length` lattice
points.  Hence `#F ≤ 2 + 2·ℓ₁·E/√(C(c−E))`.
-/

open Real Finset

namespace Squarefree

/-- A finite set of `ℓ₁⁻¹ℤ`-lattice points contained in a real interval `[a, b]` has at most
`1 + ℓ₁·(b − a)` elements. -/
private theorem interval_lattice_count {ℓ₁ a b : ℝ} (hℓ₁ : 0 < ℓ₁) (hab : a ≤ b)
    (G : Finset ℝ)
    (hlat : ∀ v ∈ G, ∃ k : ℤ, v = (k : ℝ) / ℓ₁)
    (hin : ∀ v ∈ G, a ≤ v ∧ v ≤ b) :
    (G.card : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
  classical
  -- The integer `mOf v := ℓ₁·v` (an integer by `hlat`).
  set mOf : ℝ → ℤ := fun v => ⌊ℓ₁ * v⌋ with hmdef
  -- On `G`, `(mOf v : ℝ) = ℓ₁ * v`.
  have hexact : ∀ v ∈ G, (mOf v : ℝ) = ℓ₁ * v := by
    intro v hv
    obtain ⟨k, rfl⟩ := hlat v hv
    have : ℓ₁ * ((k : ℝ) / ℓ₁) = (k : ℝ) := by
      field_simp
    rw [hmdef]; simp only; rw [this, Int.floor_intCast]
  -- `mOf` is injective on `G`.
  have hinj : Set.InjOn mOf (G : Set ℝ) := by
    intro x hx y hy hxy
    have ex := hexact x hx
    have ey := hexact y hy
    have : ℓ₁ * x = ℓ₁ * y := by rw [← ex, ← ey, hxy]
    exact mul_left_cancel₀ (ne_of_gt hℓ₁) this
  set m₀ : ℤ := ⌈ℓ₁ * a⌉ with hm0
  set m₁ : ℤ := ⌊ℓ₁ * b⌋ with hm1
  -- every `mOf v` lands in `Icc m₀ m₁`
  have hmem : ∀ v ∈ G, mOf v ∈ Finset.Icc m₀ m₁ := by
    intro v hv
    have he := hexact v hv
    obtain ⟨hav, hvb⟩ := hin v hv
    rw [Finset.mem_Icc]
    constructor
    · -- m₀ = ⌈ℓ₁a⌉ ≤ mOf v, since (mOf v : ℝ) = ℓ₁v ≥ ℓ₁a
      rw [hm0]
      refine Int.ceil_le.mpr ?_
      rw [he]
      exact mul_le_mul_of_nonneg_left hav hℓ₁.le
    · -- mOf v ≤ ⌊ℓ₁b⌋ = m₁, since (mOf v : ℝ) = ℓ₁v ≤ ℓ₁b
      rw [hm1]
      refine Int.le_floor.mpr ?_
      rw [he]
      exact mul_le_mul_of_nonneg_left hvb hℓ₁.le
  -- card G ≤ card (Icc m₀ m₁)
  have hcardle : G.card ≤ (Finset.Icc m₀ m₁).card := by
    have himg : G.image mOf ⊆ Finset.Icc m₀ m₁ := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨v, hv, rfl⟩ := hm
      exact hmem v hv
    calc G.card = (G.image mOf).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc m₀ m₁).card := Finset.card_le_card himg
  -- card (Icc m₀ m₁) = (m₁ + 1 - m₀).toNat ≤ m₁ - m₀ + 1
  have hcardIcc : (Finset.Icc m₀ m₁).card = (m₁ + 1 - m₀).toNat := by
    rw [Int.card_Icc]
  -- Bound (m₁ + 1 - m₀ : ℝ) ≤ ℓ₁(b-a) + 1
  have hm0le : ℓ₁ * a ≤ (m₀ : ℝ) := by rw [hm0]; exact Int.le_ceil _
  have hm1le : (m₁ : ℝ) ≤ ℓ₁ * b := by rw [hm1]; exact Int.floor_le _
  -- card G ≤ (m₁ + 1 - m₀).toNat, work in ℝ via toNat ≤ value when value possibly negative.
  have htoNat : ((m₁ + 1 - m₀).toNat : ℝ) ≤ (m₁ : ℝ) + 1 - (m₀ : ℝ) ∨
      ((m₁ + 1 - m₀).toNat : ℝ) = 0 := by
    rcases le_or_gt (0 : ℤ) (m₁ + 1 - m₀) with hle | hlt
    · left
      have : ((m₁ + 1 - m₀).toNat : ℤ) = m₁ + 1 - m₀ := Int.toNat_of_nonneg hle
      have : ((m₁ + 1 - m₀).toNat : ℝ) = (m₁ : ℝ) + 1 - (m₀ : ℝ) := by
        have h2 := this; push_cast at h2 ⊢; exact_mod_cast h2
      rw [this]
    · right
      have : (m₁ + 1 - m₀).toNat = 0 := Int.toNat_of_nonpos (by linarith)
      rw [this]; simp
  have hcardR : (G.card : ℝ) ≤ ((m₁ + 1 - m₀).toNat : ℝ) := by
    have : (G.card : ℝ) ≤ ((Finset.Icc m₀ m₁).card : ℝ) := by exact_mod_cast hcardle
    rwa [hcardIcc] at this
  have hgoal : (G.card : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
    rcases htoNat with h | h
    · have : (G.card : ℝ) ≤ (m₁ : ℝ) + 1 - (m₀ : ℝ) := le_trans hcardR h
      have hlin : (m₁ : ℝ) + 1 - (m₀ : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
        have : ℓ₁ * (b - a) = ℓ₁ * b - ℓ₁ * a := by ring
        linarith [hm0le, hm1le]
      linarith
    · have : (G.card : ℝ) ≤ 0 := le_trans hcardR (le_of_eq h)
      have hcnn : (0 : ℝ) ≤ G.card := by positivity
      have hrhs : (0 : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
        have : 0 ≤ ℓ₁ * (b - a) := mul_nonneg hℓ₁.le (by linarith)
        linarith
      linarith
  exact hgoal

/-- The two `v`-intervals from the `v²`-band have length `≤ E/√(C(c−E))`.
Concretely `√((c+E)/C) − √((c−E)/C) ≤ E/√(C(c−E))`. -/
private theorem sqrt_band_length_le {C c E : ℝ} (hC : 0 < C) (hE : 0 ≤ E) (hcE : E < c) :
    Real.sqrt ((c + E) / C) - Real.sqrt ((c - E) / C) ≤ E / Real.sqrt (C * (c - E)) := by
  have hcEpos : 0 < c - E := by linarith
  have hcpE : 0 < c + E := by linarith
  set x := (c + E) / C with hx
  set y := (c - E) / C with hy
  have hxpos : 0 < x := by rw [hx]; positivity
  have hypos : 0 < y := by rw [hy]; positivity
  have hxy : y ≤ x := by
    rw [hx, hy]
    gcongr
    linarith
  -- (√x − √y)(√x + √y) = x − y
  have hsx := Real.sq_sqrt hxpos.le
  have hsy := Real.sq_sqrt hypos.le
  have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsypos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hypos
  have hprod : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    have : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y)
        = Real.sqrt x ^ 2 - Real.sqrt y ^ 2 := by ring
    rw [this, hsx, hsy]
  -- x − y = (2E)/C
  have hxmy : x - y = 2 * E / C := by rw [hx, hy]; field_simp; ring
  -- √x + √y ≥ 2√y
  have hsum_ge : 2 * Real.sqrt y ≤ Real.sqrt x + Real.sqrt y := by
    have : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hxy
    linarith
  -- So √x − √y = (x−y)/(√x+√y) ≤ (x−y)/(2√y).
  have hdiff_nn : 0 ≤ Real.sqrt x - Real.sqrt y :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hxy)
  have hkey : (Real.sqrt x - Real.sqrt y) * (2 * Real.sqrt y) ≤ x - y := by
    calc (Real.sqrt x - Real.sqrt y) * (2 * Real.sqrt y)
        ≤ (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) :=
          mul_le_mul_of_nonneg_left hsum_ge hdiff_nn
      _ = x - y := hprod
  -- Hence √x − √y ≤ (x − y)/(2√y).
  have hbound1 : Real.sqrt x - Real.sqrt y ≤ (x - y) / (2 * Real.sqrt y) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hkey]
  -- Now (x−y)/(2√y) = (2E/C)/(2√y) = E/(C√y), and C√y = √(C²y) = √(C(c−E)).
  have hCy : C * Real.sqrt y = Real.sqrt (C * (c - E)) := by
    have hCsq : C = Real.sqrt (C ^ 2) := by
      rw [Real.sqrt_sq hC.le]
    have : C * Real.sqrt y = Real.sqrt (C ^ 2) * Real.sqrt y := by rw [← hCsq]
    rw [this, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [hy]; field_simp
  have hrhs_eq : (x - y) / (2 * Real.sqrt y) = E / Real.sqrt (C * (c - E)) := by
    rw [hxmy, ← hCy]
    have hCne : (C : ℝ) ≠ 0 := ne_of_gt hC
    have hsyne : Real.sqrt y ≠ 0 := ne_of_gt hsypos
    field_simp
  rw [← hrhs_eq]
  exact hbound1

/-- **§5 large-defect `v`-band lattice count.**  If a finite set `F` of reals consists of
points of the lattice `ℓ₁⁻¹ℤ`, each lying in the `v²`-band `|C·v² − c| ≤ E` for a common
center `c` and a positive scale `C` (with `0 ≤ E < c`), then `F` has at most
`2 + 2·ℓ₁·E/√(C(c−E))` elements.  (The band pins `v²` to an interval of length `2E/C` about
`c/C`, i.e. `v` to two intervals each of length `≤ E/√(C(c−E))`; each holds `≤ 1+ℓ₁·length`
lattice points.) -/
theorem vband_card_le {ℓ₁ C c E : ℝ}
    (hℓ₁ : 0 < ℓ₁) (hC : 0 < C) (hE : 0 ≤ E) (hcE : E < c)
    (F : Finset ℝ)
    (hlat : ∀ v ∈ F, ∃ k : ℤ, v = (k : ℝ) / ℓ₁)
    (hband : ∀ v ∈ F, |C * v ^ 2 - c| ≤ E) :
    (F.card : ℝ) ≤ 2 + 2 * ℓ₁ * E / Real.sqrt (C * (c - E)) := by
  classical
  have hcEpos : 0 < c - E := by linarith
  -- Common interval-endpoint abbreviations: `lo = √((c−E)/C)`, `hi = √((c+E)/C)`.
  set lo : ℝ := Real.sqrt ((c - E) / C) with hlo
  set hi : ℝ := Real.sqrt ((c + E) / C) with hhi
  have hlonn : 0 ≤ lo := Real.sqrt_nonneg _
  have hhinn : 0 ≤ hi := Real.sqrt_nonneg _
  have hlohi : lo ≤ hi := by
    rw [hlo, hhi]
    apply Real.sqrt_le_sqrt
    gcongr
    linarith
  -- The single-interval length bound `hi − lo ≤ E/√(C(c−E))`.
  have hlen : hi - lo ≤ E / Real.sqrt (C * (c - E)) := sqrt_band_length_le hC hE hcE
  have hlenpos : 0 ≤ E / Real.sqrt (C * (c - E)) := by positivity
  -- Every `v ∈ F` has `v² ∈ [(c−E)/C, (c+E)/C]`, i.e. `lo ≤ |v| ≤ hi`.
  have habsv : ∀ v ∈ F, lo ≤ |v| ∧ |v| ≤ hi := by
    intro v hv
    have hb := hband v hv
    rw [abs_le] at hb
    obtain ⟨hb1, hb2⟩ := hb
    -- `c − E ≤ C v² ≤ c + E`, so `(c−E)/C ≤ v² ≤ (c+E)/C`.
    have hv2lo : (c - E) / C ≤ v ^ 2 := by
      rw [div_le_iff₀ hC]; nlinarith [hb1]
    have hv2hi : v ^ 2 ≤ (c + E) / C := by
      rw [le_div_iff₀ hC]; nlinarith [hb2]
    have habs2 : |v| ^ 2 = v ^ 2 := by rw [sq_abs]
    constructor
    · -- lo = √((c−E)/C) ≤ |v|, since (lo)² ≤ |v|² and both nonneg.
      rw [hlo]
      rw [show |v| = Real.sqrt (|v| ^ 2) from (Real.sqrt_sq (abs_nonneg v)).symm]
      apply Real.sqrt_le_sqrt
      rw [habs2]; exact hv2lo
    · rw [hhi]
      rw [show |v| = Real.sqrt (|v| ^ 2) from (Real.sqrt_sq (abs_nonneg v)).symm]
      apply Real.sqrt_le_sqrt
      rw [habs2]; exact hv2hi
  -- Split `F` into nonnegative and negative parts.
  set Fp : Finset ℝ := F.filter (fun v => 0 ≤ v) with hFp
  set Fn : Finset ℝ := F.filter (fun v => ¬ (0 ≤ v)) with hFn
  have hsplit : F.card = Fp.card + Fn.card := by
    rw [hFp, hFn]
    exact (Finset.card_filter_add_card_filter_not (s := F) (fun v => 0 ≤ v)).symm
  -- Positive branch: `v ∈ [lo, hi]`.
  have hcardp : (Fp.card : ℝ) ≤ 1 + ℓ₁ * (hi - lo) := by
    apply interval_lattice_count hℓ₁ hlohi
    · intro v hv; exact hlat v (Finset.mem_of_mem_filter v hv)
    · intro v hv
      rw [hFp, Finset.mem_filter] at hv
      obtain ⟨hvF, hvnn⟩ := hv
      have := habsv v hvF
      rw [abs_of_nonneg hvnn] at this
      exact this
  -- Negative branch: `v ∈ [−hi, −lo]`.
  have hcardn : (Fn.card : ℝ) ≤ 1 + ℓ₁ * (-lo - -hi) := by
    apply interval_lattice_count hℓ₁ (by linarith : -hi ≤ -lo)
    · intro v hv; exact hlat v (Finset.mem_of_mem_filter v hv)
    · intro v hv
      rw [hFn, Finset.mem_filter] at hv
      obtain ⟨hvF, hvneg⟩ := hv
      have hvlt : v < 0 := lt_of_not_ge hvneg
      have := habsv v hvF
      rw [abs_of_neg hvlt] at this
      obtain ⟨h1, h2⟩ := this
      constructor <;> linarith
  -- Combine: each branch ≤ 1 + ℓ₁(hi−lo) ≤ 1 + ℓ₁·E/√(C(c−E)).
  have hcombp : (Fp.card : ℝ) ≤ 1 + ℓ₁ * (E / Real.sqrt (C * (c - E))) := by
    refine le_trans hcardp ?_
    have : ℓ₁ * (hi - lo) ≤ ℓ₁ * (E / Real.sqrt (C * (c - E))) :=
      mul_le_mul_of_nonneg_left hlen hℓ₁.le
    linarith
  have hcombn : (Fn.card : ℝ) ≤ 1 + ℓ₁ * (E / Real.sqrt (C * (c - E))) := by
    refine le_trans hcardn ?_
    have hle : (-lo - -hi) = hi - lo := by ring
    rw [hle]
    have : ℓ₁ * (hi - lo) ≤ ℓ₁ * (E / Real.sqrt (C * (c - E))) :=
      mul_le_mul_of_nonneg_left hlen hℓ₁.le
    linarith
  have hcardR : (F.card : ℝ) = (Fp.card : ℝ) + (Fn.card : ℝ) := by
    rw [hsplit]; push_cast; ring
  rw [hcardR]
  have : (Fp.card : ℝ) + (Fn.card : ℝ)
      ≤ (1 + ℓ₁ * (E / Real.sqrt (C * (c - E))))
        + (1 + ℓ₁ * (E / Real.sqrt (C * (c - E)))) := by
    linarith [hcombp, hcombn]
  refine le_trans this ?_
  have heq : (1 + ℓ₁ * (E / Real.sqrt (C * (c - E))))
        + (1 + ℓ₁ * (E / Real.sqrt (C * (c - E))))
      = 2 + 2 * ℓ₁ * E / Real.sqrt (C * (c - E)) := by ring
  rw [heq]

end Squarefree
