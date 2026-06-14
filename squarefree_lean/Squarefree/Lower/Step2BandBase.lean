import Squarefree.Lower.DefectBandLocal
import Squarefree.Lower.Step2Curvature
import Squarefree.Lower.Step2Curvature3

/-!
# §5 Step-2 band calibration — base layer (`Mmag`, band ratio, f-part dominance)

This is the base layer for the single-`T` Step-2 band calibration (`phif_band_calibration`,
in `Step2BandCal`).  It provides:

* `Mmag a f r := (4/(6Xa))·|f|·Pimag a r` — the pointwise **f-part magnitude** of `|φ_f'|`,
  where `Pimag a r := d̃(r)³·|d̃'(r)|`.
* `Pimag_band_ub` — over a narrow band `[r₀,r₁]` with `r₁ ≤ μ²·r₀`, the f-part magnitude
  varies by an ABSOLUTE factor `≤ μ⁸`: `Pimag a x ≤ μ⁸·Pimag a x'`.
* `phif_deriv_band_compare` — **f-part dominance for `φ_f'`**: under `hflarge : 10⁹⁰·L ≤ |f|`,
  the `b̃²`-part is `≤ 10⁻¹⁰·Mmag`, so `|φ_f'(x)| ∈ [(1−10⁻¹⁰)·Mmag, (1+10⁻¹⁰)·Mmag]`.

All constants are ABSOLUTE (no `X`-growth), `b̃²`-smallness driven by `|f| ≥ 10⁹⁰·L`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

variable {P : Globals} {S : Scale P}

/-- **Tight `λ`-root comparison.**  If `d, d' > 0` solve `d(d+a)=w`, `d'(d'+a)=w'`, `μ ≥ 1` and
`w ≤ μ·w'`, then `d ≤ μ·d'`.  (Linear in `μ`, via `d'+a ≤ d+a` when `d > μd' ≥ d'`.) -/
private theorem root_le_of_prod_le_lam {a d d' w w' μ : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hd' : 0 < d') (hμ : 1 ≤ μ)
    (hprod : d * (d + a) = w) (hprod' : d' * (d' + a) = w')
    (hww : w ≤ μ * w') : d ≤ μ * d' := by
  rcases le_or_gt d (μ * d') with h | h
  · exact h
  · have hda : 0 < d + a := by linarith
    have hd'_le_d : d' ≤ d := by nlinarith [hd'.le, hμ, h]
    have hkey : d * (d + a) ≤ μ * d' * (d + a) := by
      rw [hprod]
      calc w ≤ μ * w' := hww
        _ = μ * (d' * (d' + a)) := by rw [hprod']
        _ ≤ μ * (d' * (d + a)) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              apply mul_le_mul_of_nonneg_left _ hd'.le
              linarith
        _ = μ * d' * (d + a) := by ring
    have := le_of_mul_le_mul_right hkey hda
    linarith

/-- **`√λ`-band ratio of `d̃`.**  For fixed `a > 0`, `r, r' > 0` with `r' ≤ μ²·r` and `μ ≥ 1`,
`d̃(r) ≤ μ·d̃(r')`.  (`d̃` decreasing in `r`: smaller `r` ⟹ larger `d̃`; the product identity
`d̃(d̃+a)=√(Xa³/r)` gives `w(r) ≤ μ·w(r')` from `Xa³/r ≤ μ²·Xa³/r'`.) -/
private theorem dtilde_le_mu {a r r' μ : ℝ} (ha0 : 0 < a)
    (hr : 0 < r) (hr' : 0 < r') (hμ : 1 ≤ μ) (hband : r' ≤ μ ^ 2 * r) :
    dtilde P.X r a ≤ μ * dtilde P.X r' a := by
  have hXpos : 0 < P.X := P.X_pos
  set d := dtilde P.X r a with hd_def
  set d' := dtilde P.X r' a with hd'_def
  have hdpos : 0 < d := dtilde_pos hXpos ha0 hr
  have hd'pos : 0 < d' := dtilde_pos hXpos ha0 hr'
  set w := Real.sqrt (P.X * a ^ 3 / r) with hw_def
  set w' := Real.sqrt (P.X * a ^ 3 / r') with hw'_def
  have hprod : d * (d + a) = w := dtilde_prod hXpos ha0 hr
  have hprod' : d' * (d' + a) = w' := dtilde_prod hXpos ha0 hr'
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw'pos : 0 < w' := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = P.X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  have hw'sq : w' ^ 2 = P.X * a ^ 3 / r' := Real.sq_sqrt (by positivity)
  -- `w² = Xa³/r ≤ μ²·Xa³/r' = μ²·w'²`  (since `r ≤ μ² r'` ⟹ `1/r ≤ μ²/r'`)
  have hXa3 : 0 < P.X * a ^ 3 := by positivity
  have hrne : r ≠ 0 := ne_of_gt hr
  have hr'ne : r' ≠ 0 := ne_of_gt hr'
  have hw2_le : w ^ 2 ≤ μ ^ 2 * w' ^ 2 := by
    rw [hwsq, hw'sq]
    -- `Xa³/r ≤ μ²·(Xa³/r')`  ⟺  `Xa³·r' ≤ μ²·Xa³·r`  (from `r' ≤ μ²·r`)
    rw [div_le_iff₀ hr, mul_comm (μ ^ 2), mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hr']
    nlinarith [hXa3, hband]
  -- hence `w ≤ μ·w'`  (both nonneg, `μ > 0`)
  have hμpos : 0 < μ := lt_of_lt_of_le one_pos hμ
  have hww : w ≤ μ * w' := by
    nlinarith [hw2_le, hwpos, hw'pos, hμpos, mul_pos hμpos hw'pos]
  exact root_le_of_prod_le_lam ha0 hdpos hd'pos hμ hprod hprod' hww

/-- The pointwise f-part magnitude `Π(r) := d̃(r)⁴·(d̃(r)+a)/(2r(a+2 d̃(r)))`, equal to
`d̃(r)³·|d̃'(r)|` (so `|φ_f'|`'s f-part is `(4/(6Xa))·|f|·Π`). -/
noncomputable def Pimag (a r : ℝ) : ℝ :=
  dtilde P.X r a ^ 4 * (dtilde P.X r a + a) / (2 * r * (a + 2 * dtilde P.X r a))

theorem Pimag_pos {a r : ℝ} (ha0 : 0 < a) (hr : 0 < r) : 0 < Pimag (P := P) a r := by
  have hdpos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr
  unfold Pimag; positivity

/-- `Pimag` equals `d̃³·|d̃'|`. -/
theorem Pimag_eq_d3_d1abs {a r : ℝ} (ha0 : 0 < a) (hr : 0 < r) :
    Pimag (P := P) a r
      = dtilde P.X r a ^ 3 * |deriv (fun s => dtilde P.X s a) r| := by
  have hdpos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr
  have hda : 0 < dtilde P.X r a + a := by linarith
  have hda2 : 0 < a + 2 * dtilde P.X r a := by linarith
  have hderiv : deriv (fun s => dtilde P.X s a) r
      = - dtilde P.X r a * (dtilde P.X r a + a) / (2 * r * (a + 2 * dtilde P.X r a)) :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hr).deriv
  rw [hderiv]
  have : - dtilde P.X r a * (dtilde P.X r a + a) / (2 * r * (a + 2 * dtilde P.X r a))
      = - (dtilde P.X r a * (dtilde P.X r a + a) / (2 * r * (a + 2 * dtilde P.X r a))) := by ring
  rw [this, abs_neg, abs_of_pos (by positivity)]
  unfold Pimag
  rw [mul_div_assoc']
  ring_nf

/-- **Band ratio of `Pimag`** (`= d̃³|d̃'|`).  For `x, x' ∈ [r₀,r₁]`, `r₁ ≤ μ²·r₀`, `μ ≥ 1`,
`0 < r₀`, the magnitude varies by `≤ μ⁸`: `Pimag x ≤ μ⁸ · Pimag x'`.  ABSOLUTE constant. -/
theorem Pimag_band_ub {a r₀ r₁ x x' μ : ℝ} (ha0 : 0 < a)
    (hr0pos : 0 < r₀) (hband : r₁ ≤ μ ^ 2 * r₀) (hμ : 1 ≤ μ)
    (hx : x ∈ Set.Icc r₀ r₁) (hx' : x' ∈ Set.Icc r₀ r₁) :
    Pimag (P := P) a x ≤ μ ^ 8 * Pimag (P := P) a x' := by
  obtain ⟨hxl, hxr⟩ := hx
  obtain ⟨hx'l, hx'r⟩ := hx'
  have hxpos : 0 < x := lt_of_lt_of_le hr0pos hxl
  have hx'pos : 0 < x' := lt_of_lt_of_le hr0pos hx'l
  have hμpos : 0 < μ := lt_of_lt_of_le one_pos hμ
  -- both directions: x' ≤ μ²x and x ≤ μ²x'
  have hx'_le : x' ≤ μ ^ 2 * x := by
    have : x' ≤ r₁ := hx'r
    have h2 : r₁ ≤ μ ^ 2 * r₀ := hband
    have h3 : μ ^ 2 * r₀ ≤ μ ^ 2 * x := by
      apply mul_le_mul_of_nonneg_left hxl (by positivity)
    linarith
  have hx_le : x ≤ μ ^ 2 * x' := by
    have : x ≤ r₁ := hxr
    have h2 : r₁ ≤ μ ^ 2 * r₀ := hband
    have h3 : μ ^ 2 * r₀ ≤ μ ^ 2 * x' := by
      apply mul_le_mul_of_nonneg_left hx'l (by positivity)
    linarith
  -- d̃ bounds both ways
  set d := dtilde P.X x a with hd_def
  set d' := dtilde P.X x' a with hd'_def
  have hdpos : 0 < d := dtilde_pos P.X_pos ha0 hxpos
  have hd'pos : 0 < d' := dtilde_pos P.X_pos ha0 hx'pos
  have hd_le : d ≤ μ * d' := dtilde_le_mu ha0 hxpos hx'pos hμ hx'_le
  have hd'_le : d' ≤ μ * d := dtilde_le_mu ha0 hx'pos hxpos hμ hx_le
  -- closed forms of Pimag at x, x'
  have hPx : Pimag (P := P) a x = d ^ 4 * (d + a) / (2 * x * (a + 2 * d)) := rfl
  have hPx' : Pimag (P := P) a x' = d' ^ 4 * (d' + a) / (2 * x' * (a + 2 * d')) := rfl
  rw [hPx, hPx']
  -- numerator ≤ μ⁵ · num', denom factors: 2x' ≤ μ²·(2x)... use cross-multiplication.
  rw [div_le_iff₀ (by positivity), mul_comm (μ ^ 8), mul_assoc, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  -- goal: (d⁴(d+a))·(2x'(a+2d')) ≤ μ⁸·(d'⁴(d'+a))·(2x(a+2d))
  -- bound each factor: d⁴ ≤ μ⁴d'⁴, (d+a) ≤ μ(d'+a), x' ≤ μ²x, (a+2d') ≤ μ(a+2d)
  have hμa : a ≤ μ * a := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ μ - 1) ha0.le]
  have hb1 : d ^ 4 ≤ μ ^ 4 * d' ^ 4 := by
    have : d ^ 4 ≤ (μ * d') ^ 4 := pow_le_pow_left₀ hdpos.le hd_le 4
    calc d ^ 4 ≤ (μ * d') ^ 4 := this
      _ = μ ^ 4 * d' ^ 4 := by ring
  have hb2 : d + a ≤ μ * (d' + a) := by nlinarith [hd_le, hμa]
  have hb3 : a + 2 * d' ≤ μ * (a + 2 * d) := by nlinarith [hd'_le, hμa]
  have hb4 : 2 * x' ≤ μ ^ 2 * (2 * x) := by nlinarith [hx'_le]
  -- nonneg of factors
  have hn1 : (0:ℝ) ≤ d ^ 4 := by positivity
  have hn2 : (0:ℝ) ≤ d + a := by linarith
  have hn3 : (0:ℝ) ≤ 2 * x' := by positivity
  have hn4 : (0:ℝ) ≤ a + 2 * d' := by linarith
  -- product of the four bounds
  have hP : (d ^ 4 * (d + a)) * (2 * x' * (a + 2 * d'))
      ≤ (μ ^ 4 * d' ^ 4 * (μ * (d' + a))) * (μ ^ 2 * (2 * x) * (μ * (a + 2 * d))) := by
    apply mul_le_mul
    · exact mul_le_mul hb1 hb2 hn2 (by positivity)
    · exact mul_le_mul hb4 hb3 hn4 (by positivity)
    · positivity
    · positivity
  calc (d ^ 4 * (d + a)) * (2 * x' * (a + 2 * d'))
      ≤ (μ ^ 4 * d' ^ 4 * (μ * (d' + a))) * (μ ^ 2 * (2 * x) * (μ * (a + 2 * d))) := hP
    _ = d' ^ 4 * (d' + a) * (μ ^ 8 * (2 * x * (a + 2 * d))) := by ring

/-- The pointwise f-part magnitude of `φ_f'`: `Mmag(r) = (4/(6Xa))·|f|·Pimag(r)`.  This equals
`|c3·f|` where `c3 = 4d̃³d̃'/(6Xa)` is the leading coefficient of `φ_f'`. -/
noncomputable def Mmag (a f r : ℝ) : ℝ :=
  4 / (6 * P.X * a) * |f| * Pimag (P := P) a r

theorem Mmag_pos {a f r : ℝ} (ha0 : 0 < a) (hr : 0 < r) (hf : f ≠ 0) :
    0 < Mmag (P := P) a f r := by
  have hXpos : 0 < P.X := P.X_pos
  have hPi : 0 < Pimag (P := P) a r := Pimag_pos ha0 hr
  have hfabs : 0 < |f| := abs_pos.mpr hf
  unfold Mmag; positivity

/-- **f-part dominance for `φ_f'`.**  In the §5 `f`-large window the `b̃²`-part of `φ_f'` is
`≤ 10⁻¹⁰·Mmag`, so `|φ_f'(x)| ∈ [(1-10⁻¹⁰)·Mmag, (1+10⁻¹⁰)·Mmag]`.  The `b̃²`-part is the noise
`c3·φ + c4·φ1`; its smallness is governed by `|f| ≥ 10⁹⁰·L`.  ABSOLUTE constant `10⁻¹⁰`. -/
theorem phif_deriv_band_compare {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| ≤ (1 + 1 / 10 ^ 10) * Mmag (P := P) a f r
      ∧ (1 - 1 / 10 ^ 10) * Mmag (P := P) a f r ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  -- the L-large hypothesis
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by positivity) hflarge
  have hfne : f ≠ 0 := by intro h; rw [h, abs_zero] at hfabs_pos; exact lt_irrefl _ hfabs_pos
  -- closed-form value of φ_f'
  have hPD := phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r)
    ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  have hd_pos : 0 < d := dtilde_pos hXpos ha0 hr0
  set d1 := deriv (fun s => dtilde P.X s a) r with hd1_def
  set φ := phi P.X a ℓ₁ ℓ₂ r with hφ_def
  set φ1 := deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r with hφ1_def
  set c3 := 4 * d ^ 3 * d1 / (6 * P.X * a) with hc3_def
  set c4 := d ^ 4 / (6 * P.X * a) with hc4_def
  -- φ_f' = c3·f + (c3·φ + c4·φ1) = c3·f + noise
  have hval_eq : c3 * (f + φ) + c4 * φ1 = c3 * f + (c3 * φ + c4 * φ1) := by ring
  rw [hval_eq]
  -- |c3·f| = Mmag
  have hMmag_eq : Mmag (P := P) a f r = |c3 * f| := by
    rw [abs_mul]
    have h6Xa : (0:ℝ) < 6 * P.X * a := by positivity
    have hc3_abs : |c3| = 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
      rw [hc3_def, abs_div, abs_of_pos h6Xa, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (pow_pos hd_pos 3)]
    rw [hc3_abs]
    have hPi : Pimag (P := P) a r = d ^ 3 * |d1| := by
      rw [hd1_def]; exact Pimag_eq_d3_d1abs ha0 hr0
    unfold Mmag
    rw [hPi]; ring
  -- the φ-magnitude bounds
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- |c3| as a positive quantity, and Mmag = |c3|·|f|
  have h6Xa : (0:ℝ) < 6 * P.X * a := by positivity
  -- |d1| closed form (positive value)
  have hd1_abs : |d1| = d * (d + a) / (2 * r * (a + 2 * d)) := by
    rw [hd1_def]
    have := (dtilde_r_hasDerivAt hXpos ha0 hr0).deriv
    rw [this]
    have heq : - d * (d + a) / (2 * r * (a + 2 * d))
        = - (d * (d + a) / (2 * r * (a + 2 * d))) := by ring
    rw [heq, abs_neg, abs_of_pos (by positivity)]
  have hd1abs_pos : 0 < |d1| := by rw [hd1_abs]; positivity
  have hc3_abs : |c3| = 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
    rw [hc3_def, abs_div, abs_of_pos h6Xa, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (pow_pos hd_pos 3)]
  have hc3_pos : 0 < |c3| := by rw [hc3_abs]; positivity
  have hMmag_c3 : Mmag (P := P) a f r = |c3| * |f| := by rw [hMmag_eq, abs_mul]
  have hc4_pos : 0 < c4 := by rw [hc4_def]; positivity
  -- noise bound:  |c3·φ + c4·φ1| ≤ 10⁻¹⁰·Mmag
  have hnoise : |c3 * φ + c4 * φ1| ≤ (1 / 10 ^ 10) * Mmag (P := P) a f r := by
    have htri : |c3 * φ + c4 * φ1| ≤ |c3 * φ| + |c4 * φ1| := abs_add_le _ _
    -- term A: |c3·φ| = |c3|·φ ≤ 10⁻⁷⁰·|c3|·|f|
    have hφ_le : φ ≤ (1 / 10 ^ 70) * |f| := by
      have h1 : φ ≤ 10 ^ 20 * L := hphi_ub
      have h2 : (10:ℝ) ^ 90 * L ≤ |f| := hflarge
      nlinarith [h1, h2, hLpos]
    have htermA : |c3 * φ| ≤ (1 / 10 ^ 70) * (|c3| * |f|) := by
      rw [abs_mul, abs_of_nonneg hphi_nn]
      calc |c3| * φ ≤ |c3| * ((1 / 10 ^ 70) * |f|) :=
            mul_le_mul_of_nonneg_left hφ_le hc3_pos.le
        _ = (1 / 10 ^ 70) * (|c3| * |f|) := by ring
    -- term B: |c4·φ1| = c4·|φ1|.  c4 = (d/(4|d1|))·|c3|, and d/|d1| ≤ 12R.
    have hd_over_d1 : d / |d1| ≤ 64 * S.R := by
      rw [div_le_iff₀ hd1abs_pos, hd1_abs, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      -- d·(2r(a+2d)) ≤ 64R·d(d+a).  Use `r ≤ 16R` (so `16R - r ≥ 0`) times `d(a+2d) > 0`.
      have hda2pos : 0 < d * (a + 2 * d) := by positivity
      nlinarith [mul_nonneg (by linarith [hr_hi] : (0:ℝ) ≤ 16 * S.R - r) hda2pos.le,
        mul_pos (mul_pos hRpos hd_pos) ha0, hd_pos, ha0]
    have hc4_eq : c4 = d / (4 * |d1|) * |c3| := by
      rw [hc3_abs, hc4_def, hd1_abs]
      have hd1ne : (0:ℝ) < d * (d + a) / (2 * r * (a + 2 * d)) := by positivity
      field_simp
    have hφ1_le : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
      rw [hφ1_def, hL_def]
      calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
          ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
        _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
    have hφ1_le_f : |φ1| ≤ (10 ^ 35 / 10 ^ 90) * (|f| / S.R) := by
      have h2 : (10:ℝ) ^ 90 * L ≤ |f| := hflarge
      have hLf : L ≤ |f| / 10 ^ 90 := by rw [le_div_iff₀ (by norm_num)]; linarith [h2]
      calc |φ1| ≤ 10 ^ 35 * (L / S.R) := hφ1_le
        _ ≤ 10 ^ 35 * ((|f| / 10 ^ 90) / S.R) := by
              gcongr
        _ = (10 ^ 35 / 10 ^ 90) * (|f| / S.R) := by ring
    have htermB : |c4 * φ1| ≤ (1 / 10 ^ 50) * (|c3| * |f|) := by
      rw [abs_mul, abs_of_pos hc4_pos, hc4_eq]
      -- (d/(4|d1|)·|c3|)·|φ1| ≤ (12R/4)·|c3|·(10⁻⁵⁵|f|/R)
      have hd4d1 : d / (4 * |d1|) ≤ 16 * S.R := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hd1abs_pos] at hd_over_d1
        nlinarith [hd_over_d1]
      have hstep : d / (4 * |d1|) * |c3| * |φ1|
          ≤ (16 * S.R) * |c3| * ((10 ^ 35 / 10 ^ 90) * (|f| / S.R)) := by
        apply mul_le_mul (mul_le_mul hd4d1 (le_refl _) hc3_pos.le (by positivity)) hφ1_le_f
          (abs_nonneg _) (by positivity)
      refine le_trans hstep ?_
      have hRne : S.R ≠ 0 := ne_of_gt hRpos
      have heqB : (16 * S.R) * |c3| * ((10 ^ 35 / 10 ^ 90) * (|f| / S.R))
          = (16 * 10 ^ 35 / 10 ^ 90) * (|c3| * |f|) := by field_simp
      rw [heqB]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      norm_num
    rw [hMmag_c3]
    calc |c3 * φ + c4 * φ1| ≤ |c3 * φ| + |c4 * φ1| := htri
      _ ≤ (1 / 10 ^ 70) * (|c3| * |f|) + (1 / 10 ^ 50) * (|c3| * |f|) := by
            linarith [htermA, htermB]
      _ ≤ (1 / 10 ^ 10) * (|c3| * |f|) := by
            have hposm : 0 ≤ |c3| * |f| := by positivity
            nlinarith [hposm]
  rw [hMmag_eq] at hnoise ⊢
  -- triangle bounds
  have htri_up : |c3 * f + (c3 * φ + c4 * φ1)| ≤ |c3 * f| + |c3 * φ + c4 * φ1| := abs_add_le _ _
  have htri_lo : |c3 * f| - |c3 * φ + c4 * φ1| ≤ |c3 * f + (c3 * φ + c4 * φ1)| := by
    have hsplit : |c3 * f| ≤ |c3 * f + (c3 * φ + c4 * φ1)| + |c3 * φ + c4 * φ1| := by
      calc |c3 * f| = |(c3 * f + (c3 * φ + c4 * φ1)) + (-(c3 * φ + c4 * φ1))| := by ring_nf
        _ ≤ |c3 * f + (c3 * φ + c4 * φ1)| + |(-(c3 * φ + c4 * φ1))| := abs_add_le _ _
        _ = |c3 * f + (c3 * φ + c4 * φ1)| + |c3 * φ + c4 * φ1| := by rw [abs_neg]
    linarith
  constructor
  · linarith [htri_up, hnoise]
  · linarith [htri_lo, hnoise]

end Squarefree
