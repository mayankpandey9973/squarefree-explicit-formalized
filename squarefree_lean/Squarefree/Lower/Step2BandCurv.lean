import Squarefree.Lower.Step2BandBase
import Squarefree.Lower.Step2Curvature2

/-!
# §5 Step-2 band calibration — curvature layer (`phif_iter2_band_lb`)

Band-local curvature lower bound for the §5 Step-2 phase `φ_f`, supporting `phif_band_calibration`
(in `Step2BandCal`).  The `f`-part of `R·φ_f''` is `R·(12 d̃²d̃'² + 4 d̃³ d̃'')·|f|/(6Xa)`; the
closed-form fact `R·(12 d̃²d̃'² + 4 d̃³ d̃'') ≥ ½·4 d̃³|d̃'|` (over the band `r ∈ [R,3R]`) plus a
`≤ 10⁻⁹·Mmag` `b̃²`-noise (governed by `|f| ≥ 10⁹⁰·L`) give

* `phif_iter2_band_lb` : `(½ − 10⁻⁹)·Mmag(r) ≤ R·|φ_f''(r)|`,

with `Mmag(r) = (4/(6Xa))·|f|·d̃³|d̃'|` the f-part magnitude (`Step2BandBase`).  ABSOLUTE constants.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

variable {P : Globals} {S : Scale P}

/-- **Pointwise f-part curvature** (closed forms), at band scale `N`.  Abbreviating `d = d̃(r)`,
`d1abs = |d̃'(r)|`, `d2 = d̃''(r) > 0` (so `N·d2/|d1| ≍ 1`), over `r ≤ 3·N` the curvature numerator
dominates: `N·(12 d²·d1abs² + 4 d³·d2) ≥ ½·(4 d³·d1abs)`.  ABSOLUTE constant.  The algebra only
uses `r ≤ 3·N` (`N` in place of the global `S.R`). -/
private theorem curv_fpart_lb {a r N : ℝ} (ha0 : 0 < a)
    (hNpos : 0 < N) (hrpos : 0 < r) (hr_hi : r ≤ 3 * N) :
    let d := dtilde P.X r a
    let d1abs := d * (d + a) / (2 * r * (a + 2 * d))
    let d2 := d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3)
    N * (12 * d ^ 2 * d1abs ^ 2 + 4 * d ^ 3 * d2) ≥ (1/2) * (4 * d ^ 3 * d1abs) := by
  intro d d1abs d2
  have hdpos : 0 < d := dtilde_pos P.X_pos ha0 hrpos
  have hda : 0 < a + 2 * d := by positivity
  have e1 : d1abs = d * (d + a) / (2 * r * (a + 2 * d)) := rfl
  have e2 : d2 = d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
      / (4 * r ^ 2 * (a + 2 * d) ^ 3) := rfl
  rw [e1, e2, ge_iff_le, ← sub_nonneg]
  have key : N * (12 * d ^ 2 * (d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
        + 4 * d ^ 3 * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
          / (4 * r ^ 2 * (a + 2 * d) ^ 3)))
      - 1 / 2 * (4 * d ^ 3 * (d * (d + a) / (2 * r * (a + 2 * d))))
      = (d ^ 4 * (d + a) / (r ^ 2 * (a + 2 * d) ^ 3))
        * (N * (3 * (d + a) * (a + 2 * d) + (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2))
            - r * (a + 2 * d) ^ 2) := by
    field_simp; ring
  rw [key]
  apply mul_nonneg
  · positivity
  · -- N·(...) ≥ r·(a+2d)²;  use `r ≤ 3 N`, `(...) ≥ 3·(a+2d)²`
    have hbound : 3 * (d + a) * (a + 2 * d) + (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
        ≥ 3 * (a + 2 * d) ^ 2 := by
      nlinarith [sq_nonneg a, sq_nonneg d, sq_nonneg (a + d), mul_pos ha0 hdpos]
    nlinarith [hbound, hr_hi, hNpos, sq_nonneg (a + 2 * d), mul_pos ha0 hdpos,
      mul_nonneg hNpos.le (sq_nonneg (a + 2 * d))]

/-- **Pointwise f-part curvature, upper companion**, at band scale `N`.
`N·(12 d²·d1abs² + 4 d³·d2) ≤ 12·(d³·d1abs)` for `N ≤ r`.  Used to bound the `N·E1·φ` noise.
ABSOLUTE constant. -/
private theorem curv_fpart_ub {a r N : ℝ} (ha0 : 0 < a)
    (hNpos : 0 < N) (hN_le_r : N ≤ r) :
    let d := dtilde P.X r a
    let d1abs := d * (d + a) / (2 * r * (a + 2 * d))
    let d2 := d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3)
    N * (12 * d ^ 2 * d1abs ^ 2 + 4 * d ^ 3 * d2) ≤ 12 * (d ^ 3 * d1abs) := by
  intro d d1abs d2
  have hrpos : 0 < r := lt_of_lt_of_le hNpos hN_le_r
  have hdpos : 0 < d := dtilde_pos P.X_pos ha0 hrpos
  have hda : 0 < a + 2 * d := by positivity
  have e1 : d1abs = d * (d + a) / (2 * r * (a + 2 * d)) := rfl
  have e2 : d2 = d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
      / (4 * r ^ 2 * (a + 2 * d) ^ 3) := rfl
  rw [e1, e2, ← sub_nonneg]
  have key : 12 * (d ^ 3 * (d * (d + a) / (2 * r * (a + 2 * d))))
      - N * (12 * d ^ 2 * (d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
        + 4 * d ^ 3 * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
          / (4 * r ^ 2 * (a + 2 * d) ^ 3)))
      = (d ^ 4 * (d + a) / (r ^ 2 * (a + 2 * d) ^ 3))
        * (6 * r * (a + 2 * d) ^ 2
            - N * (3 * (d + a) * (a + 2 * d) + (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2))) := by
    field_simp; ring
  rw [key]
  apply mul_nonneg
  · positivity
  · -- 6 r (a+2d)² ≥ N·(3(d+a)(a+2d) + (3a²+10ad+10d²));  r ≥ N, (...) = 6a²+19ad+16d² ≤ 6(a+2d)²
    have hbound : 3 * (d + a) * (a + 2 * d) + (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
        ≤ 6 * (a + 2 * d) ^ 2 := by
      nlinarith [sq_nonneg a, sq_nonneg d, mul_pos ha0 hdpos]
    nlinarith [hbound, hN_le_r, hNpos, sq_nonneg (a + 2 * d), mul_pos ha0 hdpos,
      mul_nonneg hNpos.le (sq_nonneg (a + 2 * d))]

/-- **Band-local curvature lower bound at band scale `N`** (`N·|φ_f''| ≳ Mmag`).  Over a band point
`r` with `N ≤ r ≤ 3·N`, `S.R ≤ N`, and full-window facts `(1/72)S.R ≤ r`, `r+ℓ₁ ≤ 16R`,
`f`-large, the `f`-part of `N·φ_f''` is `≥ ½·Mmag` (by `curv_fpart_lb`) and the `b̃²`-noise is
`≤ 10⁻⁹·Mmag`, giving `(½−10⁻⁹)·Mmag ≤ N·|φ_f''(r)|`.  ABSOLUTE constant.  The curvature
normalization scale is `N`; the window facts and `hflarge` still refer to the global `S.R`. -/
theorem phif_iter2_band_lb {a ℓ₁ ℓ₂ f r N : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hRN : (1/72) * S.R ≤ N) (hr_band_lo : N ≤ r) (hr_band_hi : r ≤ 3 * N) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    (1 / 2 - 1 / 10 ^ 9) * Mmag (P := P) a f r ≤ N * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hRN
  have hr0 : 0 < r := lt_of_lt_of_le hNpos hr_band_lo
  have hr_lo72 : (1/72) * S.R ≤ r := le_trans hRN hr_band_lo
  have hrl : 0 < r + ℓ₁ := by linarith
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by positivity) hflarge
  have hfne : f ≠ 0 := by intro h; rw [h, abs_zero] at hfabs_pos; exact lt_irrefl _ hfabs_pos
  -- closed form of φ_f''
  rw [phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) ha0 hr0 hrl hℓne]
  set d := dtilde P.X r a with hd_def
  have hd_pos : 0 < d := dtilde_pos hXpos ha0 hr0
  set d1 := deriv (fun u => dtilde P.X u a) r with hd1_def
  set d2 := iteratedDeriv 2 (fun u => dtilde P.X u a) r with hd2_def
  set φ := phi P.X a ℓ₁ ℓ₂ r with hφ_def
  set φ1 := deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r with hφ1_def
  set φ2 := iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r with hφ2_def
  have h6Xa : (0:ℝ) < 6 * P.X * a := by positivity
  -- closed forms of d1 (neg), |d1|, and d2 (pos)
  have hd1_val : d1 = - d * (d + a) / (2 * r * (a + 2 * d)) := by
    rw [hd1_def]; exact (dtilde_r_hasDerivAt hXpos ha0 hr0).deriv
  have hd1_abs : |d1| = d * (d + a) / (2 * r * (a + 2 * d)) := by
    rw [hd1_val]
    have heq : - d * (d + a) / (2 * r * (a + 2 * d))
        = - (d * (d + a) / (2 * r * (a + 2 * d))) := by ring
    rw [heq, abs_neg, abs_of_pos (by positivity)]
  have hd1abs_pos : 0 < |d1| := by rw [hd1_abs]; positivity
  have hd2_val : d2 = d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
      / (4 * r ^ 2 * (a + 2 * d) ^ 3) := by
    rw [hd2_def]; exact dtilde_r_iteratedDeriv2 hXpos ha0 hr0
  have hd2_pos : 0 < d2 := by rw [hd2_val]; positivity
  -- Mmag = (4/(6Xa))·|f|·(d³|d1|)
  have hMmag_val : Mmag (P := P) a f r = 4 / (6 * P.X * a) * |f| * (d ^ 3 * |d1|) := by
    unfold Mmag
    rw [Pimag_eq_d3_d1abs ha0 hr0]
  -- E1 (>0), E2, E3 coefficients
  set E1 := (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * P.X * a) with hE1_def
  set E2 := (8 * d ^ 3 * d1) / (6 * P.X * a) with hE2_def
  set E3 := d ^ 4 / (6 * P.X * a) with hE3_def
  -- the explicit value matches E1·(f+φ) + E2·φ1 + E3·φ2
  show (1 / 2 - 1 / 10 ^ 9) * Mmag (P := P) a f r
    ≤ N * |E1 * (f + φ) + E2 * φ1 + E3 * φ2|
  -- E1 > 0
  have hE1_pos : 0 < E1 := by
    rw [hE1_def]; apply div_pos _ h6Xa
    have hp : 0 < 4 * d ^ 3 * d2 := by positivity
    nlinarith [sq_nonneg d1, sq_nonneg d, hp]
  -- value = E1·f + noise,  noise = E1·φ + E2·φ1 + E3·φ2
  have hval_eq : E1 * (f + φ) + E2 * φ1 + E3 * φ2 = E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2) := by ring
  rw [hval_eq]
  -- |E1·f + noise| ≥ |E1·f| - |noise|
  have htri : |E1 * f| - |E1 * φ + E2 * φ1 + E3 * φ2| ≤ |E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2)| := by
    have hsplit : |E1 * f| ≤ |E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2)| + |E1 * φ + E2 * φ1 + E3 * φ2| := by
      calc |E1 * f| = |(E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2)) + (-(E1 * φ + E2 * φ1 + E3 * φ2))| := by ring_nf
        _ ≤ |E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2)| + |(-(E1 * φ + E2 * φ1 + E3 * φ2))| := abs_add_le _ _
        _ = |E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2)| + |E1 * φ + E2 * φ1 + E3 * φ2| := by rw [abs_neg]
    linarith
  -- main:  N·|E1·f| ≥ ½·Mmag
  have hmain : (1 / 2) * Mmag (P := P) a f r ≤ N * |E1 * f| := by
    rw [abs_mul, abs_of_pos hE1_pos, hMmag_val]
    have hcurv := curv_fpart_lb (P := P) (a := a) (r := r) (N := N) ha0 hNpos hr0 hr_band_hi
    simp only at hcurv
    -- hcurv : N·(12 d²·d1abs² + 4 d³·d2closed) ≥ ½·4 d³·d1abs, with d1abs := |d1|, d2closed := d2
    rw [← hd1_abs, ← hd2_val] at hcurv
    -- now hcurv : N·(12 d²|d1|² + 4 d³ d2) ≥ ½·4 d³|d1|
    rw [sq_abs] at hcurv
    -- key inequality after cancelling the positive factor (4/(6Xa))·|f|
    have hcancel : (1 / 2) * (4 / (6 * P.X * a) * |f| * (d ^ 3 * |d1|))
        = (4 / (6 * P.X * a) * |f|) * (2 * d ^ 3 * |d1|) / 4 := by ring
    have hRE1 : N * E1 * |f|
        = (4 / (6 * P.X * a) * |f|) * (N * (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2)) / 4 := by
      rw [hE1_def]; field_simp
    rw [show N * (E1 * |f|) = N * E1 * |f| by ring, hRE1, hcancel]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    -- 2 d³|d1| ≤ N·(12 d²d1² + 4 d³ d2);  this is hcurv (½·4d³|d1| = 2d³|d1|)
    nlinarith [hcurv]
  -- φ-magnitude bounds
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo72 hrl_hi
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo72 hrl_hi
  have hphi''_ub := phi_iteratedDeriv2_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo72 hrl_hi
  -- Mmag/|f| = (4/(6Xa))·d³|d1| =: m0 > 0
  set m0 := 4 / (6 * P.X * a) * (d ^ 3 * |d1|) with hm0_def
  have hm0_pos : 0 < m0 := by rw [hm0_def]; have := pow_pos hd_pos 3; positivity
  have hMmag_m0 : Mmag (P := P) a f r = |f| * m0 := by rw [hMmag_val, hm0_def]; ring
  -- N ≤ 16R  (window: r ≤ 16R)
  have hr_hi16 : r ≤ 16 * S.R := by linarith
  have hN16 : N ≤ 16 * S.R := le_trans hr_band_lo hr_hi16
  -- d/|d1| ≤ 4r ≤ 12N  (band; r ≤ 3N).  Here `d/|d1| = 2r(a+2d)/(d+a) ≤ 4r`.
  have hd_over_d1 : d ≤ 12 * N * |d1| := by
    rw [hd1_abs, ← mul_div_assoc]
    rw [le_div_iff₀ (by positivity)]
    -- goal: d·(2r(a+2d)) ≤ 12N·(d(d+a)).  Use 2r(a+2d) ≤ 12N(d+a) (r≤3N, a+2d≤2(d+a)).
    have hkey : 2 * r * (a + 2 * d) ≤ 12 * N * (d + a) := by
      nlinarith [mul_nonneg (by linarith [hr_band_hi] : (0:ℝ) ≤ 3 * N - r) (by positivity : (0:ℝ) ≤ a + 2 * d),
        mul_nonneg hNpos.le ha0.le, ha0.le, hd_pos.le, mul_pos hNpos hd_pos]
    nlinarith [mul_le_mul_of_nonneg_left hkey hd_pos.le, hd_pos, mul_pos hNpos hd_pos]
  -- noise:  N·|noise| ≤ 10⁻⁹·Mmag
  have hnoise : N * |E1 * φ + E2 * φ1 + E3 * φ2| ≤ (1 / 10 ^ 9) * Mmag (P := P) a f r := by
    have htri3 : |E1 * φ + E2 * φ1 + E3 * φ2| ≤ |E1 * φ| + |E2 * φ1| + |E3 * φ2| := by
      calc |E1 * φ + E2 * φ1 + E3 * φ2| ≤ |E1 * φ + E2 * φ1| + |E3 * φ2| := abs_add_le _ _
        _ ≤ (|E1 * φ| + |E2 * φ1|) + |E3 * φ2| := by linarith [abs_add_le (E1 * φ) (E2 * φ1)]
        _ = |E1 * φ| + |E2 * φ1| + |E3 * φ2| := by ring
    -- (A) N·|E1·φ| ≤ 3·10⁻⁷⁰·Mmag
    have hRE1_ub : N * E1 ≤ 3 * m0 := by
      have hcurv := curv_fpart_ub (P := P) (a := a) (r := r) (N := N) ha0 hNpos hr_band_lo
      simp only at hcurv
      rw [← hd1_abs, ← hd2_val, sq_abs] at hcurv
      -- both sides /(6Xa);  N·E1 = N(12d²d1²+4d³d2)/(6Xa), 3m0 = 12d³|d1|/(6Xa)
      have hE1form : N * E1 = N * (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * P.X * a) := by
        rw [hE1_def]; ring
      have hm0form : 3 * m0 = 12 * (d ^ 3 * |d1|) / (6 * P.X * a) := by
        rw [hm0_def]; ring
      rw [hE1form, hm0form]
      apply div_le_div_of_nonneg_right (by linarith [hcurv]) h6Xa.le
    have htermA : N * |E1 * φ| ≤ (3 / 10 ^ 70) * Mmag (P := P) a f r := by
      rw [abs_mul, abs_of_pos hE1_pos, abs_of_nonneg hphi_nn, ← mul_assoc]
      have hφ_le : φ ≤ (1 / 10 ^ 70) * |f| := by
        have h1 : φ ≤ 10 ^ 20 * L := hphi_ub
        nlinarith [h1, hflarge, hLpos]
      rw [hMmag_m0]
      calc N * E1 * φ ≤ (3 * m0) * ((1 / 10 ^ 70) * |f|) :=
            mul_le_mul hRE1_ub hφ_le hphi_nn (by positivity)
        _ = (3 / 10 ^ 70) * (|f| * m0) := by ring
    -- (B) R·|E2·φ1| ≤ 2·10⁻⁵⁵·Mmag
    have hE2_abs : |E2| = 2 * m0 := by
      rw [hE2_def, hm0_def, abs_div, abs_of_pos h6Xa, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 8), abs_of_pos (pow_pos hd_pos 3)]
      field_simp; ring
    have htermB : N * |E2 * φ1| ≤ (32 / 10 ^ 55) * Mmag (P := P) a f r := by
      rw [abs_mul, hE2_abs]
      -- N·|φ1| ≤ 16·S.R·|φ1| ≤ 16·(1/10⁵⁵)·|f|
      have hφ1_abs_nn : 0 ≤ |φ1| := abs_nonneg _
      have hφ1_le : N * |φ1| ≤ (16 / 10 ^ 55) * |f| := by
        have hb : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
          rw [hφ1_def, hL_def]
          calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
              ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
            _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
        have hRφ1 : S.R * |φ1| ≤ 10 ^ 35 * L := by
          have := mul_le_mul_of_nonneg_left hb hRpos.le
          rw [show S.R * (10 ^ 35 * (L / S.R)) = 10 ^ 35 * L by field_simp] at this
          linarith [this]
        have hNφ1 : N * |φ1| ≤ 16 * (S.R * |φ1|) := by
          have := mul_le_mul_of_nonneg_right hN16 hφ1_abs_nn
          calc N * |φ1| ≤ 16 * S.R * |φ1| := this
            _ = 16 * (S.R * |φ1|) := by ring
        -- N|φ1| ≤ 16 S.R|φ1| ≤ 16·10³⁵ L ≤ 16·10⁻⁵⁵|f|  (10⁹⁰ L ≤ |f|)
        have hchain : N * |φ1| ≤ 16 * (10 ^ 35 * L) := by
          calc N * |φ1| ≤ 16 * (S.R * |φ1|) := hNφ1
            _ ≤ 16 * (10 ^ 35 * L) := by linarith [hRφ1]
        have hLf : (10:ℝ) ^ 35 * L ≤ (1 / 10 ^ 55) * |f| := by
          rw [show (1 / 10 ^ 55 : ℝ) * |f| = 10 ^ 35 * (|f| / 10 ^ 90) by ring]
          have : L ≤ |f| / 10 ^ 90 := by rw [le_div_iff₀ (by norm_num)]; linarith [hflarge]
          nlinarith [this]
        calc N * |φ1| ≤ 16 * (10 ^ 35 * L) := hchain
          _ ≤ 16 * ((1 / 10 ^ 55) * |f|) := by linarith [hLf]
          _ = (16 / 10 ^ 55) * |f| := by ring
      rw [hMmag_m0]
      calc N * (2 * m0 * |φ1|) = (2 * m0) * (N * |φ1|) := by ring
        _ ≤ (2 * m0) * ((16 / 10 ^ 55) * |f|) :=
              mul_le_mul_of_nonneg_left hφ1_le (by positivity)
        _ = (32 / 10 ^ 55) * (|f| * m0) := by ring
    -- (C) N·|E3·φ2| ≤ 768·10⁻⁴⁰·Mmag
    have htermC : N * |E3 * φ2| ≤ (768 / 10 ^ 40) * Mmag (P := P) a f r := by
      rw [abs_mul, abs_of_pos (by rw [hE3_def]; positivity)]
      -- E3 = d⁴/(6Xa);  N·E3 = (Nd/(4|d1|))·(4d³|d1|/(6Xa)) = (Nd/(4|d1|))·m0
      have hRE3 : N * E3 = (N * d / (4 * |d1|)) * m0 := by
        rw [hE3_def, hm0_def]; field_simp
      -- Nd/(4|d1|) ≤ 3N²  (from d ≤ 12N|d1|)
      have hRd4d1 : N * d / (4 * |d1|) ≤ 3 * N ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have h := mul_le_mul_of_nonneg_left hd_over_d1 hNpos.le
        calc N * d ≤ N * (12 * N * |d1|) := h
          _ = 3 * N ^ 2 * (4 * |d1|) := by ring
      -- 3N² ≤ 768·S.R²  (N ≤ 16S.R)
      have hN2 : (3:ℝ) * N ^ 2 ≤ 768 * S.R ^ 2 := by
        have hNsq : N ^ 2 ≤ (16 * S.R) ^ 2 := by
          apply pow_le_pow_left₀ hNpos.le hN16
        nlinarith [hNsq]
      have hφ2_le : |φ2| ≤ (1 / 10 ^ 40) * (|f| / S.R ^ 2) := by
        have hb : |φ2| ≤ 10 ^ 50 * (L / S.R ^ 2) := by
          rw [hφ2_def, hL_def]
          calc |iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r|
              ≤ 10 ^ 50 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R ^ 2)) := hphi''_ub
            _ = 10 ^ 50 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R ^ 2) := by rw [div_div]
        have hLf : L ≤ |f| / 10 ^ 90 := by rw [le_div_iff₀ (by norm_num)]; linarith [hflarge]
        calc |φ2| ≤ 10 ^ 50 * (L / S.R ^ 2) := hb
          _ ≤ 10 ^ 50 * ((|f| / 10 ^ 90) / S.R ^ 2) := by gcongr
          _ = (1 / 10 ^ 40) * (|f| / S.R ^ 2) := by ring
      rw [show N * (E3 * |φ2|) = (N * E3) * |φ2| by ring, hRE3, hMmag_m0]
      have hC : N * d / (4 * |d1|) * m0 ≤ 768 * S.R ^ 2 * m0 :=
        mul_le_mul_of_nonneg_right (le_trans hRd4d1 hN2) hm0_pos.le
      calc (N * d / (4 * |d1|) * m0) * |φ2|
          ≤ (768 * S.R ^ 2 * m0) * ((1 / 10 ^ 40) * (|f| / S.R ^ 2)) := by
            apply mul_le_mul hC hφ2_le (abs_nonneg _) (by positivity)
        _ = (768 / 10 ^ 40) * (|f| * m0) * (S.R ^ 2 / S.R ^ 2) := by ring
        _ = (768 / 10 ^ 40) * (|f| * m0) := by
              rw [div_self (by positivity : (S.R:ℝ) ^ 2 ≠ 0)]; ring
    -- combine the three
    have hMnn : 0 ≤ Mmag (P := P) a f r := (Mmag_pos ha0 hr0 hfne).le
    calc N * |E1 * φ + E2 * φ1 + E3 * φ2|
        ≤ N * (|E1 * φ| + |E2 * φ1| + |E3 * φ2|) := by
          apply mul_le_mul_of_nonneg_left htri3 hNpos.le
      _ = N * |E1 * φ| + N * |E2 * φ1| + N * |E3 * φ2| := by ring
      _ ≤ (3 / 10 ^ 70) * Mmag (P := P) a f r + (32 / 10 ^ 55) * Mmag (P := P) a f r
            + (768 / 10 ^ 40) * Mmag (P := P) a f r := by linarith [htermA, htermB, htermC]
      _ = (3 / 10 ^ 70 + 32 / 10 ^ 55 + 768 / 10 ^ 40) * Mmag (P := P) a f r := by ring
      _ ≤ (1 / 10 ^ 9) * Mmag (P := P) a f r := by
            apply mul_le_mul_of_nonneg_right _ hMnn
            norm_num
  -- combine
  have hfinal : (1 / 2 - 1 / 10 ^ 9) * Mmag (P := P) a f r
      ≤ N * |E1 * f| - N * |E1 * φ + E2 * φ1 + E3 * φ2| := by
    have : N * |E1 * f| - N * |E1 * φ + E2 * φ1 + E3 * φ2|
        ≥ (1 / 2) * Mmag (P := P) a f r - (1 / 10 ^ 9) * Mmag (P := P) a f r := by
      linarith [hmain, hnoise]
    have heq : (1 / 2) * Mmag (P := P) a f r - (1 / 10 ^ 9) * Mmag (P := P) a f r
        = (1 / 2 - 1 / 10 ^ 9) * Mmag (P := P) a f r := by ring
    linarith [this, heq.le, heq.ge]
  calc (1 / 2 - 1 / 10 ^ 9) * Mmag (P := P) a f r
      ≤ N * |E1 * f| - N * |E1 * φ + E2 * φ1 + E3 * φ2| := hfinal
    _ = N * (|E1 * f| - |E1 * φ + E2 * φ1 + E3 * φ2|) := by ring
    _ ≤ N * |E1 * f + (E1 * φ + E2 * φ1 + E3 * φ2)| := by
          apply mul_le_mul_of_nonneg_left htri hNpos.le

end Squarefree
