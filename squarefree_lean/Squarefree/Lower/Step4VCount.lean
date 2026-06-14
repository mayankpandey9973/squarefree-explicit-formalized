import Squarefree.Lower.DefectScales

/-!
# §5 Step-4 admissible-`v` count at a fixed `s`-scale (writeup 1060–1064)

For a fixed nonzero `s`, the admissible `v` live in `ℓ₁⁻¹ℤ` (spacing `1/ℓ₁`) and obey
`|v| ≍ V_s`.  Confining them to `|v| ≤ Vbnd` (with `Vbnd ≍ V_s`) and using the spacing
`1/ℓ₁` gives the writeup-1064 count

  `#{admissible v} ≪ 1 + ℓ₁·Vbnd`   (`≪ 1 + ℓ₁V_s`).

This is the genuinely-new **lattice-point count** of the §5 Step-4 large-defect argument.
`v ∈ ℓ₁⁻¹ℤ` means `v = m/ℓ₁` for an integer `m = ℓ₁v`; the confinement `|v| ≤ Vbnd` becomes
`|m| ≤ ℓ₁·Vbnd`, so the number of distinct admissible `v` is bounded by the number of integers
`m` in `[-⌊ℓ₁Vbnd⌋, ⌊ℓ₁Vbnd⌋]`, which is `≤ 2·ℓ₁·Vbnd + 1`.

The statement is phrased over an abstract finite set `Vset` of reals together with the witness
data: each `v ∈ Vset` carries an integer `mOf v` with `(mOf v : ℝ) = ℓ₁·v` (the `ℓ₁⁻¹ℤ`
membership) and `|v| ≤ Vbnd` (the scale confinement).  `mOf` need not be injective a priori —
distinctness of the `v`'s already forces distinctness of the `m`'s since `v = m/ℓ₁`.
-/

open Finset

namespace Squarefree

/-- **§5 Step-4 admissible-`v` count** (writeup 1060–1064).  A finite set `Vset` of reals, each
of the form `v = (mOf v)/ℓ₁` with `mOf v ∈ ℤ` (the `ℓ₁⁻¹ℤ` lattice) and `|v| ≤ Vbnd` (the
`V_s`-scale confinement), has cardinality `≤ 2·ℓ₁·Vbnd + 1`. -/
theorem step4_v_count (ℓ₁ Vbnd : ℝ) (hℓ1 : 0 < ℓ₁) (hVbnd : 0 ≤ Vbnd)
    (Vset : Finset ℝ) (mOf : ℝ → ℤ)
    (hlat : ∀ v ∈ Vset, (mOf v : ℝ) = ℓ₁ * v)
    (hconf : ∀ v ∈ Vset, |v| ≤ Vbnd) :
    (Vset.card : ℝ) ≤ 2 * ℓ₁ * Vbnd + 1 := by
  classical
  -- The integer window `[-⌊ℓ₁Vbnd⌋, ⌊ℓ₁Vbnd⌋]` capturing every `mOf v`.
  set M : ℤ := ⌊ℓ₁ * Vbnd⌋ with hMdef
  -- `mOf` restricted to `Vset` is injective (since `v = (mOf v)/ℓ₁`).
  have hinj : Set.InjOn mOf (Vset : Set ℝ) := by
    intro x hx y hy hxy
    have ex := hlat x hx
    have ey := hlat y hy
    have : ℓ₁ * x = ℓ₁ * y := by rw [← ex, ← ey, hxy]
    exact mul_left_cancel₀ (ne_of_gt hℓ1) this
  -- every `mOf v` lands in `Icc (-M) M`
  have hmem : ∀ v ∈ Vset, mOf v ∈ Finset.Icc (-M) M := by
    intro v hv
    have hlatv := hlat v hv
    have hconfv := hconf v hv
    -- `|mOf v| = ℓ₁·|v| ≤ ℓ₁·Vbnd`, so `(mOf v : ℝ) ∈ [-ℓ₁Vbnd, ℓ₁Vbnd]`.
    have habs : |(mOf v : ℝ)| ≤ ℓ₁ * Vbnd := by
      rw [hlatv, abs_mul, abs_of_pos hℓ1]
      exact mul_le_mul_of_nonneg_left hconfv hℓ1.le
    rw [abs_le] at habs
    rw [Finset.mem_Icc]
    constructor
    · -- `-M ≤ mOf v ⟺ -(mOf v) ≤ M = ⌊ℓ₁Vbnd⌋`, via `-(mOf v) ≤ ℓ₁Vbnd` and `Int.le_floor`.
      have hneg : -(mOf v) ≤ M := by
        rw [hMdef]
        refine Int.le_floor.mpr ?_
        push_cast
        linarith [habs.1]
      linarith [hneg]
    · -- `mOf v ≤ M` : `(mOf v : ℝ) ≤ ℓ₁Vbnd`, and `mOf v ≤ ⌊ℓ₁Vbnd⌋ = M` since `mOf v` is an int
      have h2 : (mOf v : ℝ) ≤ ℓ₁ * Vbnd := habs.2
      exact Int.le_floor.mpr h2
  -- card `Vset` ≤ card `Icc (-M) M` via the injective image
  have hcardle : Vset.card ≤ (Finset.Icc (-M) M).card := by
    have himg : Vset.image mOf ⊆ Finset.Icc (-M) M := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨v, hv, rfl⟩ := hm
      exact hmem v hv
    calc Vset.card = (Vset.image mOf).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc (-M) M).card := Finset.card_le_card himg
  -- card `Icc (-M) M` = (M + 1 - (-M)).toNat = (2M + 1).toNat
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact Int.floor_nonneg.mpr (by positivity)
  have hcardIcc : (Finset.Icc (-M) M).card = (2 * M + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  -- (2M+1).toNat = 2M+1 (since 2M+1 ≥ 1 > 0), so card `Vset` ≤ 2M+1 ≤ 2ℓ₁Vbnd+1
  have h2Mpos : (0 : ℤ) ≤ 2 * M + 1 := by linarith [hMnn]
  have hcardZ : (Vset.card : ℤ) ≤ 2 * M + 1 := by
    have := hcardle
    rw [hcardIcc] at this
    have hcast : ((2 * M + 1).toNat : ℤ) = 2 * M + 1 := Int.toNat_of_nonneg h2Mpos
    calc (Vset.card : ℤ) ≤ ((2 * M + 1).toNat : ℤ) := by exact_mod_cast this
      _ = 2 * M + 1 := hcast
  -- finally `M = ⌊ℓ₁Vbnd⌋ ≤ ℓ₁Vbnd`
  have hMle : (M : ℝ) ≤ ℓ₁ * Vbnd := Int.floor_le _
  have hcardR : (Vset.card : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast hcardZ
  calc (Vset.card : ℝ) ≤ 2 * (M : ℝ) + 1 := hcardR
    _ ≤ 2 * (ℓ₁ * Vbnd) + 1 := by linarith [hMle]
    _ = 2 * ℓ₁ * Vbnd + 1 := by ring

end Squarefree
