import Squarefree.Lower.Step2BandCal
import Squarefree.Lower.Step2Model
import Squarefree.Lower.Step2Curvature
import Squarefree.Lower.Step2Curvature3

/-!
# §5 Step-2 per-band integer count (narrow-band tiling, one band)

For a single narrow band `[r₀,r₁]` (band scale `N = r₀`, width `λ = (51/50)²`) inside the §5
window `[(1/72)S.R, 16 S.R]`, this file packages the per-band integer count of near-`φ_f`-integers
into the absolute shape

  `#(F ∩ band) ≤ C_band · (S.R·(δ + √(δ/T₀)) + T₀ + 1)`,

with `T₀ = |f|·S.D⁴/(P.X·S.A)` and `C_band` an ABSOLUTE constant.  The engine is the
`N`-parametric `step2_subset_count_cal` (band scale `N := r₀`), fed by:
* the Part-A calibration `phif_band_calibration` (`hd1`/`hlower` at scale `r₀`),
* the bridge `T_band ≍ T₀` (`phif_deriv_lb`/`phif_deriv_ub` + `phif_deriv_band_compare`),
* `phif_contDiffOn` (smoothness) and a window-generic monotonicity of `φ_f'`.

`C_band` is reported in the final `Ra_step2_count`; here each band contributes the same shape.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **Window-generic monotonicity of `φ_f'`.**  `φ_f''` is sign-definite throughout the §5 window
(sign of `f`, `phif_iteratedDeriv2_sign`), so `deriv φ_f` is `MonotoneOn`/`AntitoneOn` on any
subinterval `[r₀,r₁]` with `(1/72)S.R ≤ r₀` and `r₁+ℓ₁ ≤ 16S.R`.  (The `Step2Curvature3` version is
hardwired to `S.R ≤ r₀`, `r₁ ≤ 3S.R`; this one only needs the window facts.) -/
private theorem phif_deriv_mono_window {a ℓ₁ ℓ₂ f r₀ r₁ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r₀) (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hfne : f ≠ 0)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  -- every `x` in the window satisfies the `phif_iteratedDeriv2_sign` window hyps
  have hwin_pt : ∀ x ∈ Set.Icc r₀ r₁,
      (1/72) * S.R ≤ x ∧ x + ℓ₁ ≤ 16 * S.R ∧ 0 < x ∧ 0 < x + ℓ₁ := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := Set.mem_Icc.mp hx
    have hx72 : (1/72) * S.R ≤ x := le_trans hr_lo hxl
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx72
    refine ⟨hx72, by linarith [hxr, hwin], hx0, by linarith⟩
  have hcont : ContinuousOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁) := by
    intro x hx
    obtain ⟨_, _, hx0, hxl0⟩ := hwin_pt x hx
    exact (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 (ne_of_gt hℓ1)).continuousAt.continuousWithinAt
  have hderivOn : DifferentiableOn ℝ (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s))
      (interior (Set.Icc r₀ r₁)) := by
    intro x hx
    have hx' : x ∈ Set.Icc r₀ r₁ := interior_subset hx
    obtain ⟨_, _, hx0, hxl0⟩ := hwin_pt x hx'
    exact (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 (ne_of_gt hℓ1)).differentiableAt.differentiableWithinAt
  have hsign : ∀ x ∈ Set.Icc r₀ r₁,
      0 < f * deriv (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x := by
    intro x hx
    obtain ⟨hxl, hxr, hx0, hxl0⟩ := hwin_pt x hx
    have hd2 : deriv (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x
        = iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) x :=
      (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
        ha0 hx0 hxl0 (ne_of_gt hℓ1)).deriv
    rw [hd2]
    have hbd := phif_iteratedDeriv2_sign (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hxl hxr hflarge
    have hpos : 0 < (1 / 10 ^ 16) * (f ^ 2 * S.D ^ 4 / (P.X * S.A * S.R ^ 2)) := by
      have hf2 : 0 < f ^ 2 := by positivity
      have hXpos := P.X_pos
      have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
      have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
      positivity
    linarith [hbd, hpos]
  rcases lt_or_gt_of_ne hfne with hf_neg | hf_pos
  · right
    apply antitoneOn_of_deriv_nonpos (convex_Icc r₀ r₁) hcont hderivOn
    intro x hx
    have hx' : x ∈ Set.Icc r₀ r₁ := interior_subset hx
    have := hsign x hx'
    nlinarith [this, hf_neg]
  · left
    apply monotoneOn_of_deriv_nonneg (convex_Icc r₀ r₁) hcont hderivOn
    intro x hx
    have hx' : x ∈ Set.Icc r₀ r₁ := interior_subset hx
    have := hsign x hx'
    nlinarith [this, hf_pos]

/-- **`Mmag(r₀) ≍ T₀/R` bridge.**  From `phif_deriv_band_compare` (`|φ_f'| ≍ Mmag`) and the
two-sided derivative bounds `phif_deriv_lb`/`phif_deriv_ub` (`|φ_f'| ≍ T₀/R`, with the genuine
`10¹⁴`/`10⁵⁰` constants), the pointwise f-part magnitude is two-sidedly comparable to `T₀/R`:
`(1/10⁵¹)·T₀/R ≤ Mmag(r₀) ≤ 10¹⁵·T₀/R`, with `T₀ = |f|·D⁴/(XA)`.  ABSOLUTE constants. -/
private theorem Mmag_bridge {a ℓ₁ ℓ₂ f r₀ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r₀) (hrl_hi : r₀ + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    Mmag (P := P) a f r₀ ≤ 10 ^ 15 * (|f| * S.D ^ 4 / (P.X * S.A) / S.R)
      ∧ (1 / 10 ^ 51) * (|f| * S.D ^ 4 / (P.X * S.A) / S.R) ≤ Mmag (P := P) a f r₀ := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0pos : 0 < r₀ := lt_of_lt_of_le (by positivity) hr_lo
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by
    have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
    have hℓ2 : 0 < ℓ₂ := by linarith
    have := P.G_pos; have := S.Ω_pos; positivity) hflarge
  have hfne : f ≠ 0 := by intro h; rw [h, abs_zero] at hfabs_pos; exact lt_irrefl _ hfabs_pos
  have hMpos : 0 < Mmag (P := P) a f r₀ := Mmag_pos ha0 hr0pos hfne
  -- weaken `f`-large from 10⁹⁰ to 10⁵⁵
  have hflarge55 : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f| := by
    have hLnn : 0 ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) := by
      have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
      have hℓ2 : 0 < ℓ₂ := by linarith
      have := P.G_pos; have := S.Ω_pos; positivity
    nlinarith [hflarge, hLnn]
  -- band_compare at r₀
  obtain ⟨hcmp_up, hcmp_lo⟩ := phif_deriv_band_compare (P := P) (S := S) (a := a)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r₀) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hflarge
  -- derivative two-sided
  have hub := phif_deriv_ub (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r₀)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hflarge55
  have hlb := phif_deriv_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r₀)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hsmall hflarge55
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hXpos : 0 < P.X := P.X_pos
  set D := |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r₀| with hD_def
  set T0R := |f| * S.D ^ 4 / (P.X * S.A) / S.R with hT0R_def
  have hT0R_pos : 0 < T0R := by rw [hT0R_def]; positivity
  -- hub : D ≤ T0R·10¹⁴  (rewrite |f|D⁴/(XA)·10¹⁴/R = 10¹⁴·T0R)
  have hub' : D ≤ 10 ^ 14 * T0R := by
    rw [hD_def]; rw [show |f| * S.D ^ 4 / (P.X * S.A) * 10 ^ 14 / S.R = 10 ^ 14 * T0R by
      rw [hT0R_def]; ring] at hub; exact hub
  -- hlb : T0R/10⁵⁰ ≤ D
  have hlb' : (1 / 10 ^ 50) * T0R ≤ D := by
    rw [hD_def]; rw [show |f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50)
      = (1 / 10 ^ 50) * T0R by rw [hT0R_def]; field_simp] at hlb; exact hlb
  constructor
  · -- Mmag ≤ |φ'|/(1-10⁻¹⁰) ≤ 2·10¹⁴·T0R ≤ 10¹⁵·T0R
    have h1 : (1 - 1 / 10 ^ 10) * Mmag (P := P) a f r₀ ≤ D := hcmp_lo
    nlinarith [h1, hub', hMpos, hT0R_pos, hMpos.le]
  · -- Mmag ≥ |φ'|/(1+10⁻¹⁰) ≥ (1/2)·T0R/10⁵⁰ ≥ T0R/10⁵¹
    have h2 : D ≤ (1 + 1 / 10 ^ 10) * Mmag (P := P) a f r₀ := hcmp_up
    nlinarith [h2, hlb', hMpos, hT0R_pos]

/-- **Per-band integer count** (one narrow band of the tiling).  For a narrow band `[r₀,r₁]` with
`S.R ≤ r₀`, `r₀ < r₁`, `r₁ ≤ (51/50)²·r₀`, `r₁+ℓ₁ ≤ 16·S.R`, in the `f`-large window, the count of
band members `r` near a `φ_f`-integer (`distInt(φ_f r) ≤ δ`, `δ > 0`) is bounded by the absolute
shape `≤ 10³¹·(S.R·(δ+√(δ/T₀)) + T₀ + 1)`, with `T₀ = |f|·S.D⁴/(P.X·S.A)`.  Engine:
`step2_subset_count_cal` (band scale `N := r₀`) fed by `phif_band_calibration` (Part A),
`phif_contDiffOn`, `phif_deriv_mono_window`, and the `Mmag_bridge`. -/
theorem step2_band_count {a ℓ₁ ℓ₂ f r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hℓ1_lo : 1 ≤ ℓ₁)
    (hr_band_lo : (1/72) * S.R ≤ r₀) (hr0r1 : r₀ < r₁)
    (hnarrow : r₁ ≤ (51 / 50) ^ 2 * r₀) (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hδ : 0 < δ)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|)
    (𝒯 : Finset ℕ)
    (hsubT : ∀ r ∈ 𝒯, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    (𝒯.card : ℝ) ≤ 10 ^ 31 * (S.R * (δ + Real.sqrt (δ / (|f| * S.D ^ 4 / (P.X * S.A))))
        + (|f| * S.D ^ 4 / (P.X * S.A)) + 1) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0pos : 0 < r₀ := lt_of_lt_of_le (by positivity) hr_band_lo
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hXpos : 0 < P.X := P.X_pos
  have hr_lo72 : (1/72) * S.R ≤ r₀ := hr_band_lo
  have hr0win : r₀ + ℓ₁ ≤ 16 * S.R := by linarith [hr0r1, hwin]
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by
    have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
    have hℓ2 : 0 < ℓ₂ := by linarith
    have := P.G_pos; have := S.Ω_pos; positivity) hflarge
  have hfne : f ≠ 0 := by intro h; rw [h, abs_zero] at hfabs_pos; exact lt_irrefl _ hfabs_pos
  -- `T₀ = |f|·D⁴/(XA) > 0`
  set T₀ : ℝ := |f| * S.D ^ 4 / (P.X * S.A) with hT0_def
  have hT0_pos : 0 < T₀ := by rw [hT0_def]; positivity
  -- the Part-A calibration: a single `T_band` discharging hd1/hlower at scale r₀.
  obtain ⟨T_band, hTb_pos, ⟨hTb_lo, hTb_hi⟩, hd1, hlower⟩ := phif_band_calibration (P := P) (S := S)
    (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r₀ := r₀) (r₁ := r₁)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_band_lo hnarrow hr0r1.le hwin hflarge
  -- the Mmag bridge ⟹ two-sided `T_band ≍ T₀`.
  obtain ⟨hMup, hMlo⟩ := Mmag_bridge (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    (r₀ := r₀) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo72 hr0win hsmall hflarge
  set M0 : ℝ := Mmag (P := P) a f r₀ with hM0_def
  have hM0_pos : 0 < M0 := Mmag_pos ha0 hr0pos hfne
  -- `T₀/R = T0R`; from Mmag bridge: T0R/10⁵¹ ≤ M0 ≤ 10¹⁵·T0R
  set T0R : ℝ := T₀ / S.R with hT0R_def
  have hT0R_pos : 0 < T0R := by rw [hT0R_def]; positivity
  have hMup' : M0 ≤ 10 ^ 15 * T0R := by rw [hM0_def, hT0R_def, hT0_def]; exact hMup
  have hMlo' : (1 / 10 ^ 51) * T0R ≤ M0 := by rw [hM0_def, hT0R_def, hT0_def]; exact hMlo
  -- T_band upper:  T_band ≤ 2·r₀·M0 ≤ 2·16R·10¹⁵·(T₀/R) = 32·10¹⁵·T₀ ≤ 10¹⁸·T₀
  have hr0_16R : r₀ ≤ 16 * S.R := by linarith [hr0r1, hwin, hℓ1.le]
  have hTb_le_T0 : T_band ≤ 10 ^ 18 * T₀ := by
    have h1 : T_band ≤ 2 * (r₀ * M0) := by rw [hM0_def]; exact hTb_hi
    have h2 : r₀ * M0 ≤ (16 * S.R) * (10 ^ 15 * T0R) :=
      mul_le_mul hr0_16R hMup' hM0_pos.le (by positivity)
    have hRcancel : (16 * S.R) * (10 ^ 15 * T0R) = 16 * 10 ^ 15 * T₀ := by
      rw [hT0R_def]; field_simp
    rw [hRcancel] at h2
    nlinarith [h1, h2, hT0_pos]
  -- T_band lower:  T_band ≥ r₀·M0 ≥ (R/72)·(T0R/10⁵¹) = T₀/(72·10⁵¹) ≥ T₀/10⁵³
  have hr0_R72 : S.R / 72 ≤ r₀ := by linarith [hr_lo72]
  have hTb_ge_T0 : (1 / 10 ^ 53) * T₀ ≤ T_band := by
    have h1 : r₀ * M0 ≤ T_band := by rw [hM0_def]; exact hTb_lo
    have h2 : (S.R / 72) * ((1 / 10 ^ 51) * T0R) ≤ r₀ * M0 :=
      mul_le_mul hr0_R72 hMlo' (by positivity) hr0pos.le
    have hRcancel : (S.R / 72) * ((1 / 10 ^ 51) * T0R) = (1 / (72 * 10 ^ 51)) * T₀ := by
      rw [hT0R_def]; field_simp
    rw [hRcancel] at h2
    have h3 : (1 / 10 ^ 53) * T₀ ≤ (1 / (72 * 10 ^ 51)) * T₀ := by
      apply mul_le_mul_of_nonneg_right _ hT0_pos.le; norm_num
    linarith [h1, h2, h3]
  -- smoothness on the open window
  have hcdO : ContDiffOn ℝ 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) (Set.Ioo (r₀ - 1) (r₁ + 1)) := by
    have hr0m1 : 0 < r₀ - 1 := by
      have hRbig : (10:ℝ) ^ 33 ≤ S.R := by nlinarith [hsmall, hℓ1_lo]
      -- r₀ ≥ (1/72)·S.R ≥ 10³³/72 > 1
      nlinarith [hr_band_lo, hRbig]
    exact (phif_contDiffOn hXpos ha0 hr0m1 hℓ1.le).mono Set.Ioo_subset_Icc_self
  -- monotonicity of φ_f' on the band
  have hmono := phif_deriv_mono_window (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    (r₀ := r₀) (r₁ := r₁) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo72 hwin hfne hflarge
  -- per-band count from the N-parametric engine (band scale N := r₀)
  have hr1_3r0 : r₁ ≤ 3 * r₀ := le_trans hnarrow (by nlinarith [hr0pos])
  have hcount := step2_subset_count_cal (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    (r₀ := r₀) (r₁ := r₁) (δ := δ) (T := T_band) (N := r₀)
    hr0pos (le_refl _) hr1_3r0 hδ hTb_pos hr0r1 hcdO hd1 hlower hmono 𝒯 hsubT
  -- Now convert  112·(r₀(δ+√(δ/T_band)) + T_band + 1)  ≤  10³¹·(R(δ+√(δ/T₀)) + T₀ + 1)
  refine le_trans hcount ?_
  -- √(δ/T_band) ≤ 10²⁷·√(δ/T₀):  δ/T_band ≤ 10⁵³·(δ/T₀)
  have hsqrt_le : Real.sqrt (δ / T_band) ≤ 10 ^ 27 * Real.sqrt (δ / T₀) := by
    have hT0_le : T₀ ≤ 10 ^ 53 * T_band := by nlinarith [hTb_ge_T0, hTb_pos]
    have hdiv : δ / T_band ≤ 10 ^ 53 * (δ / T₀) := by
      rw [div_le_iff₀ hTb_pos]
      -- goal: δ ≤ 10^53 * (δ/T₀) * T_band
      have hkey : (δ / T₀) * T₀ ≤ (δ / T₀) * (10 ^ 53 * T_band) :=
        mul_le_mul_of_nonneg_left hT0_le (by positivity)
      have heq : (δ / T₀) * T₀ = δ := by field_simp
      rw [heq] at hkey
      nlinarith [hkey]
    calc Real.sqrt (δ / T_band) ≤ Real.sqrt (10 ^ 53 * (δ / T₀)) := Real.sqrt_le_sqrt hdiv
      _ = Real.sqrt (10 ^ 53) * Real.sqrt (δ / T₀) := by
            rw [Real.sqrt_mul (by positivity)]
      _ ≤ 10 ^ 27 * Real.sqrt (δ / T₀) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            rw [show (10:ℝ) ^ 27 = Real.sqrt ((10 ^ 27) ^ 2) by
              rw [Real.sqrt_sq (by positivity)]]
            apply Real.sqrt_le_sqrt; norm_num
  -- assemble.  let q := R(δ+√(δ/T₀)) + T₀ + 1 ≥ 0.
  have hsqnn : 0 ≤ Real.sqrt (δ / T₀) := Real.sqrt_nonneg _
  set q : ℝ := S.R * (δ + Real.sqrt (δ / T₀)) + T₀ + 1 with hq_def
  have hq_nn : 0 ≤ q := by rw [hq_def]; nlinarith [hRpos.le, hδ.le, hT0_pos.le, hsqnn]
  -- 112·(r₀(δ+√(δ/T_band)) + T_band + 1)
  --   ≤ 112·(16R·δ + 16R·10²⁷√(δ/T₀) + 10¹⁸·T₀ + 1)
  --   ≤ 10³¹·(R(δ+√(δ/T₀)) + T₀ + 1)
  have hband_term : r₀ * (δ + Real.sqrt (δ / T_band)) + T_band + 1
      ≤ 16 * S.R * δ + 16 * S.R * (10 ^ 27 * Real.sqrt (δ / T₀)) + 10 ^ 18 * T₀ + 1 := by
    have ht1 : r₀ * (δ + Real.sqrt (δ / T_band))
        ≤ 16 * S.R * δ + 16 * S.R * (10 ^ 27 * Real.sqrt (δ / T₀)) := by
      have hsq_band_nn : 0 ≤ Real.sqrt (δ / T_band) := Real.sqrt_nonneg _
      have hexpand : r₀ * (δ + Real.sqrt (δ / T_band))
          = r₀ * δ + r₀ * Real.sqrt (δ / T_band) := by ring
      rw [hexpand]
      have hA : r₀ * δ ≤ 16 * S.R * δ := by
        apply mul_le_mul_of_nonneg_right hr0_16R hδ.le
      have hB : r₀ * Real.sqrt (δ / T_band) ≤ 16 * S.R * (10 ^ 27 * Real.sqrt (δ / T₀)) := by
        apply mul_le_mul hr0_16R hsqrt_le hsq_band_nn (by positivity)
      linarith [hA, hB]
    linarith [ht1, hTb_le_T0]
  -- 112·(16Rδ + 16R·10²⁷√(δ/T₀) + 10¹⁸T₀ + 1) ≤ 10³¹·q, since q = R(δ+√(δ/T₀))+T₀+1.
  have hRsqnn : 0 ≤ S.R * Real.sqrt (δ / T₀) := mul_nonneg hRpos.le hsqnn
  have hRδnn : 0 ≤ S.R * δ := mul_nonneg hRpos.le hδ.le
  have hfinal_const :
      112 * (16 * S.R * δ + 16 * S.R * (10 ^ 27 * Real.sqrt (δ / T₀)) + 10 ^ 18 * T₀ + 1)
        ≤ 10 ^ 31 * q := by
    rw [hq_def]
    nlinarith [hRsqnn, hRδnn, hT0_pos.le, hRpos.le, hδ.le, hsqnn]
  calc 112 * (r₀ * (δ + Real.sqrt (δ / T_band)) + T_band + 1)
      ≤ 112 * (16 * S.R * δ + 16 * S.R * (10 ^ 27 * Real.sqrt (δ / T₀)) + 10 ^ 18 * T₀ + 1) := by
        apply mul_le_mul_of_nonneg_left hband_term (by norm_num)
    _ ≤ 10 ^ 31 * q := hfinal_const

end Squarefree
