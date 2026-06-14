import Squarefree.Lower.Step4Phase

/-!
# §5 Step-4 smooth phase `φ_v` derivative UPPER bound (writeup 1073–1077)

`phiv_deriv_ub` is the matching upper-bound companion of `phiv_deriv_lb` (`Step4Phase.lean`).
Both scale as `T/R`, giving the two-sided `|φ_v'| ≍ T/R` of writeup line 1075.

Mechanism: `phiv_hasDerivAt` writes `φ_v' = VTERM − φ'`, where
`VTERM = (-24)·ℓ₁·X·a·v·d̃'/d̃⁵` is the exact derivative of the `6ℓ₁Xav/d̃⁴` piece and
`φ' = (b̃²-piece)'` is the Step-1 phase derivative.  The triangle inequality gives
`|φ_v'| ≤ |VTERM| + |φ'|`; `|VTERM|` is reported exactly via `|d̃'|`, and `|φ'|` is bounded by
`10³⁵·ℓ₂(ℓ₂−ℓ₁)/R` using `phi_deriv_ub` (which gives `10³⁵·ℓ₁ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵R)`) together with
the regime fact `ℓ₁ ≤ GΩ⁵`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **§5 Step-4 phase derivative upper bound (v-large).**  `|φ_v'|` splits, via `phiv_hasDerivAt`,
into the exact `6ℓ₁Xav/d̃⁴`-derivative `24ℓ₁Xa|v|·|d̃'|/d̃⁵` plus the Step-1 phase derivative
`|φ'| ≤ 10³⁵·ℓ₂(ℓ₂−ℓ₁)/R`.  Together with `phiv_deriv_lb` this gives `|φ_v'| ≍ T/R`. -/
theorem phiv_deriv_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ v r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hℓ1GΩ : ℓ₁ ≤ P.G * S.Ω ^ 5) :
    |deriv (fun ρ => phiv P.X a ℓ₁ ℓ₂ v ρ) r|
      ≤ 24 * ℓ₁ * P.X * a * |v| * |deriv (fun s => dtilde P.X s a) r| / dtilde P.X r a ^ 5
        + 10 ^ 35 * (ℓ₂ * (ℓ₂ - ℓ₁)) / S.R := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hvabs_nn : (0:ℝ) ≤ |v| := abs_nonneg _
  -- d̃ positivity
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  -- |φ'| ≤ 10³⁵·ℓ₁ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵R)
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- rewrite the derivative via phiv_hasDerivAt
  have hPD := phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := r)
    ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun s => dtilde P.X s a) r with hd1_def
  set φ1 := deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r with hφ1_def
  -- value = VTERM − φ1,  VTERM = -24ℓ₁Xav·d1/d⁵
  set VTERM := (-24) * ℓ₁ * P.X * a * v * d1 / d ^ 5 with hVTERM_def
  -- triangle: |VTERM − φ1| ≤ |VTERM| + |φ1|
  have htri : |VTERM - φ1| ≤ |VTERM| + |φ1| := abs_sub _ _
  refine le_trans htri ?_
  -- positivity helpers
  have hd5_pos : 0 < d ^ 5 := by positivity
  have h24pref_pos : 0 < 24 * ℓ₁ * P.X * a := by positivity
  -- |VTERM| = 24ℓ₁Xa|v|·|d1|/d⁵  (matches the first target term)
  have hVTERM_abs : |VTERM| = 24 * ℓ₁ * P.X * a * |v| * |d1| / d ^ 5 := by
    rw [hVTERM_def, abs_div, abs_of_pos hd5_pos]
    rw [show ((-24) * ℓ₁ * P.X * a * v * d1)
        = -((24 * ℓ₁ * P.X * a) * v * d1) by ring, abs_neg]
    rw [abs_mul, abs_mul, abs_of_pos h24pref_pos]
  -- |φ1| ≤ 10³⁵·ℓ₂(ℓ₂−ℓ₁)/R  (drop the ℓ₁/(GΩ⁵) ≤ 1 factor)
  have hphi1 : |φ1| ≤ 10 ^ 35 * (ℓ₂ * (ℓ₂ - ℓ₁)) / S.R := by
    refine le_trans hphi'_ub ?_
    -- 10³⁵·ℓ₁ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵R) ≤ 10³⁵·ℓ₂(ℓ₂−ℓ₁)/R  since ℓ₁ ≤ GΩ⁵
    have hlhs : 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R))
        = (10 ^ 35 * (ℓ₂ * (ℓ₂ - ℓ₁)) / S.R) * (ℓ₁ / (P.G * S.Ω ^ 5)) := by
      field_simp
    rw [hlhs]
    -- (target)·(ℓ₁/(GΩ⁵)) ≤ (target)·1 = target  since ℓ₁/(GΩ⁵) ≤ 1
    have htgt_nn : (0:ℝ) ≤ 10 ^ 35 * (ℓ₂ * (ℓ₂ - ℓ₁)) / S.R := by positivity
    have hfrac_le1 : ℓ₁ / (P.G * S.Ω ^ 5) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hℓ1GΩ
    nlinarith [mul_le_mul_of_nonneg_left hfrac_le1 htgt_nn]
  -- assemble
  rw [hVTERM_abs]
  linarith [hphi1]

/-- **§5 Step-4 phase derivative UPPER bound, scalar form (v-large).**  `|φ_v'| ≤ 10¹³·W` with
`W = ℓ₁Xa|v|/(D⁴R)`.  This is the matching companion of `phiv_deriv_lb`'s `10⁻⁵⁰·W` LOWER bound,
so over a confined interval the variation `|φ_v'|·|I_s|` is controlled by `W·|I_s|`.  The two
together give `|φ_v'| ≍ W ≍ T/R`. -/
theorem phiv_deriv_ub_scale {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ v r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hvlarge : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |v|) :
    |deriv (fun ρ => phiv P.X a ℓ₁ ℓ₂ v ρ) r|
      ≤ 10 ^ 13 * (ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R)) := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hvabs_nn : (0:ℝ) ≤ |v| := abs_nonneg _
  -- the L-scale and the W-scale
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  set W := ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R) with hW_def
  have hWnn : (0:ℝ) ≤ W := by rw [hW_def]; positivity
  -- B·R = D
  have hBR : S.B * S.R = S.D := by rw [Scale.B_eq_D_div_R]; field_simp
  have hWR : ℓ₁ * P.X * a * |v| / S.D ^ 4 = W * S.R := by rw [hW_def]; field_simp
  -- the v-large hypothesis rearranged: 10⁴⁷·L ≤ W·R
  have hkey : (10:ℝ) ^ 47 * L ≤ W * S.R := by
    have hcoef_pos : 0 < ℓ₁ * P.X * a / S.D ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hvlarge hcoef_pos.le
    have hLHS : (ℓ₁ * P.X * a / S.D ^ 4)
        * ((10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)))
        = 10 ^ 47 * L := by
      rw [hL_def]; field_simp
    have hRHS : (ℓ₁ * P.X * a / S.D ^ 4) * |v| = ℓ₁ * P.X * a * |v| / S.D ^ 4 := by ring
    rw [hLHS, hRHS, hWR] at hmul; exact hmul
  -- d̃ window and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  obtain ⟨hd1_lo, hd1_hi⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- |φ'| ≤ 10³⁵·L/R
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- rewrite the derivative via phiv_hasDerivAt
  have hPD := phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := r)
    ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun s => dtilde P.X s a) r with hd1_def
  set φ1 := deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r with hφ1_def
  set VTERM := (-24) * ℓ₁ * P.X * a * v * d1 / d ^ 5 with hVTERM_def
  have htri : |VTERM - φ1| ≤ |VTERM| + |φ1| := abs_sub _ _
  refine le_trans htri ?_
  have hd5_pos : 0 < d ^ 5 := by positivity
  have h24pref_pos : 0 < 24 * ℓ₁ * P.X * a := by positivity
  have hVTERM_abs : |VTERM| = 24 * ℓ₁ * P.X * a * |v| * |d1| / d ^ 5 := by
    rw [hVTERM_def, abs_div, abs_of_pos hd5_pos]
    rw [show ((-24) * ℓ₁ * P.X * a * v * d1)
        = -((24 * ℓ₁ * P.X * a) * v * d1) by ring, abs_neg]
    rw [abs_mul, abs_mul, abs_of_pos h24pref_pos]
  -- ===== |VTERM| ≤ (24·10⁶/10⁵)·W  (numerator |d1| ≤ 10⁶·B, denom d⁵ ≥ (D/10)⁵) =====
  have hVTERM_le : |VTERM| ≤ (24 * 10 ^ 6 * 10 ^ 5) * W := by
    rw [hVTERM_abs]
    have hnum_hi : 24 * ℓ₁ * P.X * a * |v| * |d1|
        ≤ 24 * ℓ₁ * P.X * a * |v| * (1000000 * S.B) :=
      mul_le_mul_of_nonneg_left hd1_hi (by positivity)
    have hd5_lo : (S.D / 10) ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ (by positivity) hd_lo 5
    have hd105_pos : 0 < (S.D / 10) ^ 5 := by positivity
    have hstep : 24 * ℓ₁ * P.X * a * |v| * |d1| / d ^ 5
        ≤ 24 * ℓ₁ * P.X * a * |v| * (1000000 * S.B) / (S.D / 10) ^ 5 :=
      div_le_div₀ (by positivity) hnum_hi hd105_pos hd5_lo
    refine le_trans hstep ?_
    have hreq : 24 * ℓ₁ * P.X * a * |v| * (1000000 * S.B) / (S.D / 10) ^ 5
        = (24 * 1000000 * 10 ^ 5) * (ℓ₁ * P.X * a * |v| * S.B / S.D ^ 5) := by
      field_simp
    rw [hreq]
    have hWB : ℓ₁ * P.X * a * |v| * S.B / S.D ^ 5 = W := by
      rw [hW_def, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (ℓ₁ * P.X * a * |v| * S.D ^ 4) * hBR
    rw [hWB]
    apply mul_le_mul_of_nonneg_right _ hWnn; norm_num
  -- ===== |φ1| ≤ 10⁻¹²·W  (from 10⁴⁷·L ≤ W·R) =====
  have hphi1 : |φ1| ≤ (1 / 10 ^ 12) * W := by
    have hphi1L : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
      rw [hφ1_def, hL_def]
      calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
          ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
        _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
    refine le_trans hphi1L ?_
    have hL_le : L ≤ W * S.R / 10 ^ 47 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hkey]
    calc 10 ^ 35 * (L / S.R)
        ≤ 10 ^ 35 * ((W * S.R / 10 ^ 47) / S.R) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply div_le_div_of_nonneg_right hL_le hRpos.le
      _ = (1 / 10 ^ 12) * W := by field_simp
  -- ===== combine =====
  calc |VTERM| + |φ1|
      ≤ (24 * 10 ^ 6 * 10 ^ 5) * W + (1 / 10 ^ 12) * W := by linarith [hVTERM_le, hphi1]
    _ ≤ 10 ^ 13 * (ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R)) := by
        rw [← hW_def]; nlinarith [hWnn]

end Squarefree
