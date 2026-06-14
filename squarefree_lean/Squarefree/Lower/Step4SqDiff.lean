import Mathlib

/-!
# §5 Step-4 large-defect `v`-band — TWO-POINT square-difference count (writeup 1058)

This is the CORRECT vehicle for the sharp (`∝1/√n`) large-defect `v`-band, replacing the
absolute-band `vband_card_le` (`|C·v²−c|≤E`, which forces `E≲err` — an `|s|`-scale wall, since
the per-point residual `Sigma_closed_parabola_sharp` is `≍|s|`).

For a fixed nonzero `s`, the admissible defects `v∈ℓ₁⁻¹ℤ` (each with `|v|≥Vlo≍V_s` and
`round Σ_s(v)=s`) satisfy the **pairwise** square-difference bound

  `|v²−v'²| ≤ diam`  (writeup 1058: `|v²−v'²|≪(E+err)/C`),

where `diam` is the FIXED band-VARIATION budget — the variation of the cubic/`p₂`/coefficient-drift
correction across the band, NOT its absolute (`≍|s|`) size.  Combined with the lower pin `|v|≥Vlo`,
the same-sign diameter in `v` is `≤ diam/(2·Vlo)` (since `|v−v'|=|v²−v'²|/(|v|+|v'|)`), so each
sign holds `≤ 1+ℓ₁·diam/Vlo` lattice points and

  `#F ≤ 2 + 2·ℓ₁·diam/Vlo`.

The `diam` budget is supplied by the caller (the two-point parabola/variation analysis); this file
is the purely combinatorial lattice-count kernel that converts it into the `1/√n`-band card.
-/

open Real Finset

namespace Squarefree

/-- A finite set of `ℓ₁⁻¹ℤ`-lattice points contained in a real interval `[a, b]` has at most
`1 + ℓ₁·(b − a)` elements.  (Self-contained copy of the `Step4Band.lean` private helper.) -/
private theorem sqdiff_interval_lattice_count {ℓ₁ a b : ℝ} (hℓ₁ : 0 < ℓ₁) (hab : a ≤ b)
    (G : Finset ℝ)
    (hlat : ∀ v ∈ G, ∃ k : ℤ, v = (k : ℝ) / ℓ₁)
    (hin : ∀ v ∈ G, a ≤ v ∧ v ≤ b) :
    (G.card : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
  classical
  set mOf : ℝ → ℤ := fun v => ⌊ℓ₁ * v⌋ with hmdef
  have hexact : ∀ v ∈ G, (mOf v : ℝ) = ℓ₁ * v := by
    intro v hv
    obtain ⟨k, rfl⟩ := hlat v hv
    have : ℓ₁ * ((k : ℝ) / ℓ₁) = (k : ℝ) := by field_simp
    rw [hmdef]; simp only; rw [this, Int.floor_intCast]
  have hinj : Set.InjOn mOf (G : Set ℝ) := by
    intro x hx y hy hxy
    have ex := hexact x hx
    have ey := hexact y hy
    have : ℓ₁ * x = ℓ₁ * y := by rw [← ex, ← ey, hxy]
    exact mul_left_cancel₀ (ne_of_gt hℓ₁) this
  set m₀ : ℤ := ⌈ℓ₁ * a⌉ with hm0
  set m₁ : ℤ := ⌊ℓ₁ * b⌋ with hm1
  have hmem : ∀ v ∈ G, mOf v ∈ Finset.Icc m₀ m₁ := by
    intro v hv
    have he := hexact v hv
    obtain ⟨hav, hvb⟩ := hin v hv
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [hm0]; refine Int.ceil_le.mpr ?_
      rw [he]; exact mul_le_mul_of_nonneg_left hav hℓ₁.le
    · rw [hm1]; refine Int.le_floor.mpr ?_
      rw [he]; exact mul_le_mul_of_nonneg_left hvb hℓ₁.le
  have hcardle : G.card ≤ (Finset.Icc m₀ m₁).card := by
    have himg : G.image mOf ⊆ Finset.Icc m₀ m₁ := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨v, hv, rfl⟩ := hm
      exact hmem v hv
    calc G.card = (G.image mOf).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc m₀ m₁).card := Finset.card_le_card himg
  have hcardIcc : (Finset.Icc m₀ m₁).card = (m₁ + 1 - m₀).toNat := by rw [Int.card_Icc]
  have hm0le : ℓ₁ * a ≤ (m₀ : ℝ) := by rw [hm0]; exact Int.le_ceil _
  have hm1le : (m₁ : ℝ) ≤ ℓ₁ * b := by rw [hm1]; exact Int.floor_le _
  have htoNat : ((m₁ + 1 - m₀).toNat : ℝ) ≤ (m₁ : ℝ) + 1 - (m₀ : ℝ) ∨
      ((m₁ + 1 - m₀).toNat : ℝ) = 0 := by
    rcases le_or_gt (0 : ℤ) (m₁ + 1 - m₀) with hle | hlt
    · left
      have h2 : ((m₁ + 1 - m₀).toNat : ℤ) = m₁ + 1 - m₀ := Int.toNat_of_nonneg hle
      have : ((m₁ + 1 - m₀).toNat : ℝ) = (m₁ : ℝ) + 1 - (m₀ : ℝ) := by
        push_cast at h2 ⊢; exact_mod_cast h2
      rw [this]
    · right
      have : (m₁ + 1 - m₀).toNat = 0 := Int.toNat_of_nonpos (by linarith)
      rw [this]; simp
  have hcardR : (G.card : ℝ) ≤ ((m₁ + 1 - m₀).toNat : ℝ) := by
    have : (G.card : ℝ) ≤ ((Finset.Icc m₀ m₁).card : ℝ) := by exact_mod_cast hcardle
    rwa [hcardIcc] at this
  rcases htoNat with h | h
  · have hle1 : (G.card : ℝ) ≤ (m₁ : ℝ) + 1 - (m₀ : ℝ) := le_trans hcardR h
    have hlin : (m₁ : ℝ) + 1 - (m₀ : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
      have : ℓ₁ * (b - a) = ℓ₁ * b - ℓ₁ * a := by ring
      linarith [hm0le, hm1le]
    linarith
  · have hle0 : (G.card : ℝ) ≤ 0 := le_trans hcardR (le_of_eq h)
    have hcnn : (0 : ℝ) ≤ G.card := by positivity
    have hrhs : (0 : ℝ) ≤ 1 + ℓ₁ * (b - a) := by
      have : 0 ≤ ℓ₁ * (b - a) := mul_nonneg hℓ₁.le (by linarith)
      linarith
    linarith

/-- A finite set `G` of `ℓ₁⁻¹ℤ`-lattice points, all **nonnegative** and pinned `Vlo ≤ v`, with the
pairwise square-difference budget `|v²−v'²| ≤ diam`, has `≤ 1 + ℓ₁·diam/Vlo` elements: any two lie
within `|v−v'| = |v²−v'²|/(v+v') ≤ diam/(2·Vlo)` of each other, so `G` sits in an interval of length
`diam/Vlo`. -/
private theorem sqdiff_nonneg_band_card_le {ℓ₁ Vlo diam : ℝ}
    (hℓ₁ : 0 < ℓ₁) (hVlo : 0 < Vlo) (hdiam : 0 ≤ diam)
    (G : Finset ℝ)
    (hlat : ∀ v ∈ G, ∃ k : ℤ, v = (k : ℝ) / ℓ₁)
    (hpin : ∀ v ∈ G, Vlo ≤ v)
    (hpair : ∀ v ∈ G, ∀ v' ∈ G, |v ^ 2 - v' ^ 2| ≤ diam) :
    (G.card : ℝ) ≤ 1 + ℓ₁ * (diam / Vlo) := by
  classical
  have hhalf_nn : 0 ≤ diam / (2 * Vlo) := by positivity
  rcases G.eq_empty_or_nonempty with hE | ⟨v₀, hv₀⟩
  · subst hE; simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ ℓ₁ * (diam / Vlo) := by positivity
    linarith
  · -- reference point `v₀`; every `v ∈ G` is within `diam/(2Vlo)` of it.
    set h2 : ℝ := diam / (2 * Vlo) with hh2
    have hv0pin : Vlo ≤ v₀ := hpin v₀ hv₀
    have hbnd : ∀ v ∈ G, |v - v₀| ≤ h2 := by
      intro v hv
      have hvpin : Vlo ≤ v := hpin v hv
      have hsumpos : 0 < v + v₀ := by linarith
      have h2sum : 2 * Vlo ≤ v + v₀ := by linarith
      have hkey : |v - v₀| * (v + v₀) = |v ^ 2 - v₀ ^ 2| := by
        rw [← abs_of_pos hsumpos, ← abs_mul]; ring_nf
      have hle : |v - v₀| * (v + v₀) ≤ diam := by
        rw [hkey]; exact hpair v hv v₀ hv₀
      have hdiv : |v - v₀| ≤ diam / (v + v₀) := (le_div_iff₀ hsumpos).mpr hle
      refine le_trans hdiv ?_
      rw [hh2]; gcongr
    -- so `G ⊆ [v₀ − h2, v₀ + h2]`, an interval of length `2·h2 = diam/Vlo`.
    have hcard := sqdiff_interval_lattice_count (ℓ₁ := ℓ₁) (a := v₀ - h2) (b := v₀ + h2)
      hℓ₁ (by linarith) G hlat (by
        intro v hv
        have := hbnd v hv
        rw [abs_le] at this
        constructor <;> linarith [this.1, this.2])
    refine le_trans hcard (le_of_eq ?_)
    have hlen : (v₀ + h2) - (v₀ - h2) = diam / Vlo := by
      rw [hh2]; field_simp; ring
    rw [hlen]

/-- **§5 Step-4 band confinement EXPOSURE (writeup 1058).**  The interval `sqdiff_nonneg_band_card_le`
silently confines `F` to.  For a finite set `F` of **nonnegative**, `Vlo`-pinned reals with the
pairwise square-difference budget `|v²−v'²| ≤ diam`, every `v ∈ F` lies within the half-width
`diam/(2·Vlo)` of any chosen reference `v₀ ∈ F`:

  `|v − v₀| ≤ diam/(2·Vlo)`.

This is the recentered form the §5 Step-4 fibre `hconf` (`|vOf n r| ≤ Vbnd n`, `vOf := vval − v₀`,
`Vbnd := diam/(2·Vlo)`) consumes; the same-sign restriction is the caller's `b₀<0` sign split. -/
theorem sqdiff_band_confine {Vlo diam : ℝ}
    (hVlo : 0 < Vlo) (hdiam : 0 ≤ diam)
    (F : Finset ℝ)
    (hpin : ∀ v ∈ F, Vlo ≤ v)
    (hpair : ∀ v ∈ F, ∀ v' ∈ F, |v ^ 2 - v' ^ 2| ≤ diam)
    {v₀ : ℝ} (hv₀ : v₀ ∈ F) :
    ∀ v ∈ F, |v - v₀| ≤ diam / (2 * Vlo) := by
  intro v hv
  have hvpin : Vlo ≤ v := hpin v hv
  have hv0pin : Vlo ≤ v₀ := hpin v₀ hv₀
  have hsumpos : 0 < v + v₀ := by linarith
  have h2sum : 2 * Vlo ≤ v + v₀ := by linarith
  have h2Vlo : (0:ℝ) < 2 * Vlo := by linarith
  have hkey : |v - v₀| * (v + v₀) = |v ^ 2 - v₀ ^ 2| := by
    rw [← abs_of_pos hsumpos, ← abs_mul]; ring_nf
  have hle : |v - v₀| * (v + v₀) ≤ diam := by
    rw [hkey]; exact hpair v hv v₀ hv₀
  have hdiv : |v - v₀| ≤ diam / (v + v₀) := (le_div_iff₀ hsumpos).mpr hle
  refine le_trans hdiv ?_
  gcongr

/-- **§5 Step-4 large-defect `v`-band TWO-POINT count (writeup 1058).**  A finite set `F` of
`ℓ₁⁻¹ℤ`-lattice defects, each pinned `Vlo ≤ |v|` (the `|v|≍V_s` lower pin), satisfying the pairwise
square-difference budget `|v²−v'²| ≤ diam` (the FIXED band-variation budget `≍(E+err)/C`), has
`#F ≤ 2 + 2·ℓ₁·diam/Vlo`.  This is the SHARP `1/√n` band (`N_s−1 ≍ ℓ₁·diam/Vlo`); the `diam`
budget is supplied by the caller's two-point parabola/variation analysis. -/
theorem sqdiff_band_card_le {ℓ₁ Vlo diam : ℝ}
    (hℓ₁ : 0 < ℓ₁) (hVlo : 0 < Vlo) (hdiam : 0 ≤ diam)
    (F : Finset ℝ)
    (hlat : ∀ v ∈ F, ∃ k : ℤ, v = (k : ℝ) / ℓ₁)
    (hpin : ∀ v ∈ F, Vlo ≤ |v|)
    (hpair : ∀ v ∈ F, ∀ v' ∈ F, |v ^ 2 - v' ^ 2| ≤ diam) :
    (F.card : ℝ) ≤ 2 + 2 * ℓ₁ * diam / Vlo := by
  classical
  -- split into nonnegative / negative parts.
  set Fp : Finset ℝ := F.filter (fun v => 0 ≤ v) with hFp
  set Fn : Finset ℝ := F.filter (fun v => ¬ (0 ≤ v)) with hFn
  have hsplit : F.card = Fp.card + Fn.card := by
    rw [hFp, hFn]
    exact (Finset.card_filter_add_card_filter_not (s := F) (fun v => 0 ≤ v)).symm
  -- nonnegative branch.
  have hcardp : (Fp.card : ℝ) ≤ 1 + ℓ₁ * (diam / Vlo) := by
    apply sqdiff_nonneg_band_card_le hℓ₁ hVlo hdiam Fp
    · intro v hv; exact hlat v (Finset.mem_of_mem_filter v hv)
    · intro v hv
      rw [hFp, Finset.mem_filter] at hv
      obtain ⟨hvF, hvnn⟩ := hv
      have := hpin v hvF; rwa [abs_of_nonneg hvnn] at this
    · intro v hv v' hv'
      exact hpair v (Finset.mem_of_mem_filter v hv) v' (Finset.mem_of_mem_filter v' hv')
  -- negative branch: reflect `v ↦ −v` (preserves lattice / pin / pairwise, makes it nonnegative).
  set Fnr : Finset ℝ := Fn.image (fun v => -v) with hFnr
  have hneg_inj : Function.Injective (fun v : ℝ => -v) := fun x y h => by simpa using h
  have hcardn : (Fn.card : ℝ) ≤ 1 + ℓ₁ * (diam / Vlo) := by
    have hcardeq : Fn.card = Fnr.card := (Finset.card_image_of_injective Fn hneg_inj).symm
    rw [hcardeq]
    apply sqdiff_nonneg_band_card_le hℓ₁ hVlo hdiam Fnr
    · intro w hw
      rw [hFnr, Finset.mem_image] at hw
      obtain ⟨v, hvF, rfl⟩ := hw
      obtain ⟨k, hk⟩ := hlat v (Finset.mem_of_mem_filter v hvF)
      exact ⟨-k, by rw [hk]; push_cast; ring⟩
    · intro w hw
      rw [hFnr, Finset.mem_image] at hw
      obtain ⟨v, hvF, rfl⟩ := hw
      rw [hFn, Finset.mem_filter] at hvF
      obtain ⟨hvmem, hvneg⟩ := hvF
      have hvlt : v < 0 := lt_of_not_ge hvneg
      have := hpin v hvmem; rw [abs_of_neg hvlt] at this; linarith
    · intro w hw w' hw'
      rw [hFnr, Finset.mem_image] at hw hw'
      obtain ⟨v, hvF, rfl⟩ := hw
      obtain ⟨v', hvF', rfl⟩ := hw'
      have := hpair v (Finset.mem_of_mem_filter v hvF) v' (Finset.mem_of_mem_filter v' hvF')
      simpa [neg_pow] using this
  -- combine.
  have hcardR : (F.card : ℝ) = (Fp.card : ℝ) + (Fn.card : ℝ) := by
    rw [hsplit]; push_cast; ring
  rw [hcardR]
  have hsum : (Fp.card : ℝ) + (Fn.card : ℝ)
      ≤ (1 + ℓ₁ * (diam / Vlo)) + (1 + ℓ₁ * (diam / Vlo)) := by linarith
  refine le_trans hsum (le_of_eq ?_)
  field_simp; ring

end Squarefree
