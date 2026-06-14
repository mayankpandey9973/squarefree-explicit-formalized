import Squarefree.Lower.Step2BandCurv

/-!
# §5 Step-2 single-`T` band calibration (`phif_band_calibration`)

The bands engine `step2_subset_count_cal` (`Step2Model.lean`) needs, over a band `[r₀,r₁]`, a
*single* variation scale `T` with both
* `hd1`   : `∀ x ∈ [r₀,r₁], |φ_f'(x)| ≤ T/R`,
* `hlower`: `∀ x ∈ [r₀,r₁], T/R ≤ |φ_f'(x)| + R·|φ_f''(x)|`.

The absolute lemmas (`phif_deriv_ub : |φ_f'| ≤ 10¹⁴·T₀/R`, `phif_curvature_lower :
(1/10¹⁶)·T₀/R ≤ …`) have a `~10³⁰` constant gap rooted in the `10⁶` two-sided slack of
`dtilde_d1_bounds`, so no single `T = c·T₀` discharges both.  This file repairs that with a
**band-relative** calibration: the scale `T_band := R·μ⁸·(1+10⁻¹⁰)·Mmag(r₀)` is built from the
pointwise f-part magnitude `Mmag(x) = (4/(6Xa))·|f|·d̃³|d̃'|` at the band's left endpoint, where
the band ratio of `Mmag` is an ABSOLUTE `O(1)` factor `μ⁸` for a narrow band `r₁ ≤ μ²·r₀`.

Mechanism, all with ABSOLUTE constants (see `Step2BandBase`/`Step2BandCurv` for the layers):
1. **f-part dominance** (`phif_deriv_band_compare`): `|φ_f'(x)| ∈ [(1−10⁻¹⁰)Mmag, (1+10⁻¹⁰)Mmag]`.
2. **Pointwise curvature** (`phif_iter2_band_lb`): `R·|φ_f''(x)| ≥ (½−10⁻⁹)Mmag` — the f-part
   `R(12d̃²d̃'²+4d̃³d̃'') ≥ ½·4d̃³|d̃'|` plus a `≤10⁻⁹·Mmag` `b̃²`-noise.
3. **Band ratio** (`Pimag_band_ub`): `Mmag x ≤ μ⁸·Mmag x'` over the band.

The calibration closes both: with `μ = 51/50` (so band width `λ := μ² = 2601/2500 ≈ 1.0404`) the
swing `μ⁸ = (51/50)⁸ ≈ 1.1717` and `μ¹⁶ ≈ 1.373`; `(1−10⁻¹⁰)+(½−10⁻⁹) = 3/2−…` gives
`|φ_f'|+R|φ_f''| ≥ (3/2−10⁻⁹)·Mmag(x) ≥ (3/2−10⁻⁹)/μ⁸·Mmag(r₀) ≥ μ⁸(1+10⁻¹⁰)·Mmag(r₀) = T/R`,
valid since `μ¹⁶·(1+10⁻¹⁰) ≤ 3/2−10⁻⁹`.  **Band width `λ = (51/50)² ≈ 1.0404`**; the absolute
calibration ratio is `c_u/c_l = μ¹⁶ ≈ 1.373 ≤ 3/2`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

variable {P : Globals} {S : Scale P}

/-- Band ratio of `Mmag` (inherits `Pimag_band_ub`): `Mmag x ≤ μ⁸·Mmag x'`. -/
private theorem Mmag_band_ub {a f r₀ r₁ x x' μ : ℝ} (ha0 : 0 < a)
    (hr0pos : 0 < r₀) (hband : r₁ ≤ μ ^ 2 * r₀) (hμ : 1 ≤ μ)
    (hx : x ∈ Set.Icc r₀ r₁) (hx' : x' ∈ Set.Icc r₀ r₁) :
    Mmag (P := P) a f x ≤ μ ^ 8 * Mmag (P := P) a f x' := by
  have hPi := Pimag_band_ub (P := P) (a := a) ha0 hr0pos hband hμ hx hx'
  unfold Mmag
  have hcoef : 0 ≤ 4 / (6 * P.X * a) * |f| := by have := P.X_pos; positivity
  calc 4 / (6 * P.X * a) * |f| * Pimag (P := P) a x
      ≤ 4 / (6 * P.X * a) * |f| * (μ ^ 8 * Pimag (P := P) a x') :=
        mul_le_mul_of_nonneg_left hPi hcoef
    _ = μ ^ 8 * (4 / (6 * P.X * a) * |f| * Pimag (P := P) a x') := by ring

/-- **§5 Step-2 single-`T` band calibration at band scale `N = r₀`.**  For a fixed §5 window value
`a`, an `f`-large phase shift (`hflarge : 10⁹⁰·L ≤ |f|`, `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵)`), and a NARROW
band `[r₀,r₁]` with `S.R ≤ r₀`, `r₁ ≤ (51/50)²·r₀` (band width `λ = (51/50)² ≈ 1.0404`), and the
full-window facts `r₁+ℓ₁ ≤ 16·S.R`, there is a scale `T_band > 0` discharging both bands inputs
over `[r₀,r₁]`, normalized by the band scale `N = r₀`:
* `hd1`    : `|φ_f'(x)| ≤ T_band/r₀`,
* `hlower` : `T_band/r₀ ≤ |φ_f'(x)| + r₀·|φ_f''(x)|`.

The scale is `T_band = r₀·(51/50)⁸·(1+10⁻¹⁰)·Mmag(r₀) ≍ |f|·D⁴/(XA)`; the absolute calibration
ratio (the `c_u/c_l` margin) is `(51/50)¹⁶ ≈ 1.373 ≤ 3/2`, an ABSOLUTE `O(1)` constant.  The
constraint `r₁ ≤ 3·r₀` is automatic from `r₁ ≤ (51/50)²·r₀ ≤ 3·r₀`. -/
theorem phif_band_calibration {a ℓ₁ ℓ₂ f r₀ r₁ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_band_lo : (1/72) * S.R ≤ r₀)
    (hnarrow : r₁ ≤ (51 / 50) ^ 2 * r₀) (hr0r1 : r₀ ≤ r₁)
    (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    ∃ T_band : ℝ, 0 < T_band
      ∧ (r₀ * Mmag (P := P) a f r₀ ≤ T_band
          ∧ T_band ≤ 2 * (r₀ * Mmag (P := P) a f r₀))
      ∧ (∀ x ∈ Set.Icc r₀ r₁, |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| ≤ T_band / r₀)
      ∧ (∀ x ∈ Set.Icc r₀ r₁, T_band / r₀ ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
            + r₀ * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0pos : 0 < r₀ := lt_of_lt_of_le (by positivity) hr_band_lo
  -- `r₁ ≤ 3·r₀` automatic from the narrow-band ratio
  have hr_band_hi3 : r₁ ≤ 3 * r₀ := le_trans hnarrow (by nlinarith [hr0pos])
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) := by
    have : 0 < ℓ₂ - ℓ₁ := by linarith
    have : 0 < ℓ₂ := by linarith
    positivity
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by positivity) hflarge
  have hfne : f ≠ 0 := by intro h; rw [h, abs_zero] at hfabs_pos; exact lt_irrefl _ hfabs_pos
  set μ : ℝ := 51 / 50 with hμ_def
  have hμ1 : (1:ℝ) ≤ μ := by rw [hμ_def]; norm_num
  have hμ8_pos : (0:ℝ) < μ ^ 8 := by rw [hμ_def]; positivity
  -- the calibration scale (normalized by the band scale `N = r₀`)
  set T_band : ℝ := r₀ * (μ ^ 8 * ((1 + 1 / 10 ^ 10) * Mmag (P := P) a f r₀)) with hT_def
  have hr0mem : r₀ ∈ Set.Icc r₀ r₁ := ⟨le_refl _, hr0r1⟩
  have hM0_pos : 0 < Mmag (P := P) a f r₀ := Mmag_pos ha0 hr0pos hfne
  have hTpos : 0 < T_band := by rw [hT_def]; positivity
  -- two-sided bound `r₀·Mmag(r₀) ≤ T_band ≤ 2·r₀·Mmag(r₀)`  (μ⁸(1+10⁻¹⁰) ∈ [1,2])
  have hTbounds : r₀ * Mmag (P := P) a f r₀ ≤ T_band
      ∧ T_band ≤ 2 * (r₀ * Mmag (P := P) a f r₀) := by
    have hcoef_lo : (1:ℝ) ≤ μ ^ 8 * (1 + 1 / 10 ^ 10) := by rw [hμ_def]; norm_num
    have hcoef_hi : μ ^ 8 * (1 + 1 / 10 ^ 10) ≤ 2 := by rw [hμ_def]; norm_num
    have hrM_nn : 0 ≤ r₀ * Mmag (P := P) a f r₀ := by positivity
    constructor
    · have : r₀ * Mmag (P := P) a f r₀ ≤ (μ ^ 8 * (1 + 1 / 10 ^ 10)) * (r₀ * Mmag (P := P) a f r₀) :=
        le_mul_of_one_le_left hrM_nn hcoef_lo
      rw [hT_def]; nlinarith [this]
    · have : (μ ^ 8 * (1 + 1 / 10 ^ 10)) * (r₀ * Mmag (P := P) a f r₀)
          ≤ 2 * (r₀ * Mmag (P := P) a f r₀) := mul_le_mul_of_nonneg_right hcoef_hi hrM_nn
      rw [hT_def]; nlinarith [this]
  refine ⟨T_band, hTpos, hTbounds, ?_, ?_⟩
  · -- hd1
    intro x hx
    have hxl := hx.1
    have hxr := hx.2
    have hxlo : r₀ ≤ x := hxl
    have hxhi : x ≤ 3 * r₀ := le_trans hxr hr_band_hi3
    have hx72 : (1/72) * S.R ≤ x := le_trans hr_band_lo hxl
    have hxwin : x + ℓ₁ ≤ 16 * S.R := by linarith [hxr, hwin]
    obtain ⟨hup, _⟩ := phif_deriv_band_compare (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      (f := f) (r := x) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hx72 hxwin hflarge
    -- Mmag x ≤ μ⁸·Mmag r₀
    have hMband := Mmag_band_ub (P := P) (a := a) (f := f) ha0 hr0pos hnarrow hμ1
      hx hr0mem
    have hT_over_R : T_band / r₀ = μ ^ 8 * ((1 + 1 / 10 ^ 10) * Mmag (P := P) a f r₀) := by
      rw [hT_def]; field_simp
    rw [hT_over_R]
    calc |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
        ≤ (1 + 1 / 10 ^ 10) * Mmag (P := P) a f x := hup
      _ ≤ (1 + 1 / 10 ^ 10) * (μ ^ 8 * Mmag (P := P) a f r₀) := by
            apply mul_le_mul_of_nonneg_left hMband (by norm_num)
      _ = μ ^ 8 * ((1 + 1 / 10 ^ 10) * Mmag (P := P) a f r₀) := by ring
  · -- hlower
    intro x hx
    have hxl := hx.1
    have hxr := hx.2
    have hxlo : r₀ ≤ x := hxl
    have hxhi : x ≤ 3 * r₀ := le_trans hxr hr_band_hi3
    have hx72 : (1/72) * S.R ≤ x := le_trans hr_band_lo hxl
    have hxwin : x + ℓ₁ ≤ 16 * S.R := by linarith [hxr, hwin]
    obtain ⟨_, hlow⟩ := phif_deriv_band_compare (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      (f := f) (r := x) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hx72 hxwin hflarge
    have hcurv := phif_iter2_band_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      (r := x) (N := r₀) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_band_lo hxlo hxhi hxwin hflarge
    -- Mmag r₀ ≤ μ⁸·Mmag x
    have hMband := Mmag_band_ub (P := P) (a := a) (f := f) ha0 hr0pos hnarrow hμ1
      hr0mem hx
    have hMx_pos : 0 < Mmag (P := P) a f x := Mmag_pos ha0 (lt_of_lt_of_le hr0pos hxl) hfne
    have hμ8_pos : 0 < μ ^ 8 := by rw [hμ_def]; positivity
    have hT_over_R : T_band / r₀ = μ ^ 8 * ((1 + 1 / 10 ^ 10) * Mmag (P := P) a f r₀) := by
      rw [hT_def]; field_simp
    rw [hT_over_R]
    -- |φ_f'| + r₀|φ_f''| ≥ (3/2 - 2·10⁻⁹)·Mmag x ≥ (3/2-2·10⁻⁹)/μ⁸·Mmag r₀ ≥ μ⁸(1+10⁻¹⁰)·Mmag r₀
    have hsum_lb : (1 / 2 - 1 / 10 ^ 9 + (1 - 1 / 10 ^ 10)) * Mmag (P := P) a f x
        ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
          + r₀ * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| := by
      have h1 : (1 - 1 / 10 ^ 10) * Mmag (P := P) a f x
          ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| := hlow
      have h2 : (1 / 2 - 1 / 10 ^ 9) * Mmag (P := P) a f x
          ≤ r₀ * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| := hcurv
      nlinarith [h1, h2]
    refine le_trans ?_ hsum_lb
    -- μ⁸(1+10⁻¹⁰)·Mmag r₀ ≤ (3/2-2·10⁻⁹)·Mmag x.  Use Mmag r₀ ≤ μ⁸·Mmag x and μ¹⁶(1+10⁻¹⁰) ≤ 3/2-2·10⁻⁹.
    have hkey : μ ^ 8 * ((1 + 1 / 10 ^ 10) * Mmag (P := P) a f r₀)
        ≤ μ ^ 8 * ((1 + 1 / 10 ^ 10) * (μ ^ 8 * Mmag (P := P) a f x)) := by
      apply mul_le_mul_of_nonneg_left _ hμ8_pos.le
      apply mul_le_mul_of_nonneg_left hMband (by norm_num)
    refine le_trans hkey ?_
    -- μ⁸·(1+10⁻¹⁰)·μ⁸·Mmag x = μ¹⁶(1+10⁻¹⁰)·Mmag x ≤ (3/2-2·10⁻⁹)·Mmag x
    have hcoef : μ ^ 8 * ((1 + 1 / 10 ^ 10) * μ ^ 8) ≤ (1 / 2 - 1 / 10 ^ 9 + (1 - 1 / 10 ^ 10)) := by
      rw [hμ_def]; norm_num
    calc μ ^ 8 * ((1 + 1 / 10 ^ 10) * (μ ^ 8 * Mmag (P := P) a f x))
        = (μ ^ 8 * ((1 + 1 / 10 ^ 10) * μ ^ 8)) * Mmag (P := P) a f x := by ring
      _ ≤ (1 / 2 - 1 / 10 ^ 9 + (1 - 1 / 10 ^ 10)) * Mmag (P := P) a f x :=
            mul_le_mul_of_nonneg_right hcoef hMx_pos.le

end Squarefree
