import Squarefree.Lower.Step1Phase

/-!
# §5 Step-4 smooth phase `φ_v`

The §5 Step-4 smooth phase (writeup 1067)

  `φ_v(r) = 6ℓ₁·X·a·v/d̃ₐ(r)⁴ − φ(r)`,

where `φ = phi X a ℓ₁ ℓ₂` is the Step-1 phase.  This file gives its definition, its
derivative (reusing `phi_hasDerivAt` and the chain rule for `d̃⁴`), and — in the `v`-large
regime — the magnitude bound `|φ_v| ≤ 10⁵·ℓ₁Xa|v|/D⁴` and the derivative lower bound
`|φ_v'| ≥ ℓ₁Xa|v|/(D⁴·R·10⁵⁰)` (≍ T/R).  Mirrors `Step23Phase.lean`'s `φ_f` work.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- §5 Step-4 smooth phase `φ_v(r) = 6ℓ₁Xav/d̃ₐ(r)⁴ − φ(r)` (writeup 1067). -/
noncomputable def phiv (X a ℓ₁ ℓ₂ v r : ℝ) : ℝ :=
  6 * ℓ₁ * X * a * v / (dtilde X r a) ^ 4 - phi X a ℓ₁ ℓ₂ r

/-- Derivative of `φ_v`. -/
theorem phiv_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ v r : ℝ} (ha0 : 0 < a) (hr0 : 0 < r)
    (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => phiv P.X a ℓ₁ ℓ₂ v s)
      ( (-24) * ℓ₁ * P.X * a * v * deriv (fun s => dtilde P.X s a) r / (dtilde P.X r a) ^ 5
        - deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r ) r := by
  have hd0 : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  -- derivative of `d̃`
  have hd : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun s => dtilde P.X s a) r) r :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hr0).differentiableAt.hasDerivAt
  -- derivative of `d̃⁴`
  have hd4 : HasDerivAt (fun s => (dtilde P.X s a) ^ 4)
      (4 * (dtilde P.X r a) ^ 3 * deriv (fun s => dtilde P.X s a) r) r := by
    simpa using hd.pow 4
  -- derivative of `(d̃⁴)⁻¹`
  have hinv : HasDerivAt (fun s => ((dtilde P.X s a) ^ 4)⁻¹)
      (-(4 * (dtilde P.X r a) ^ 3 * deriv (fun s => dtilde P.X s a) r)
        / ((dtilde P.X r a) ^ 4) ^ 2) r :=
    hd4.inv (pow_ne_zero 4 hd0)
  -- derivative of the first term `6ℓ₁Xav · (d̃⁴)⁻¹`
  have hfirst : HasDerivAt (fun s => (6 * ℓ₁ * P.X * a * v) * ((dtilde P.X s a) ^ 4)⁻¹)
      ((6 * ℓ₁ * P.X * a * v)
        * (-(4 * (dtilde P.X r a) ^ 3 * deriv (fun s => dtilde P.X s a) r)
            / ((dtilde P.X r a) ^ 4) ^ 2)) r :=
    hinv.const_mul (6 * ℓ₁ * P.X * a * v)
  -- derivative of `φ`
  have hphi : HasDerivAt (fun s => phi P.X a ℓ₁ ℓ₂ s) (deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r) r :=
    (phi_hasDerivAt ha0 hr0 hrl hℓne).differentiableAt.hasDerivAt
  -- combine: `φ_v = first - φ`
  have hsub := hfirst.sub hphi
  -- rewrite `phiv` so the first term matches `(…)·(d̃⁴)⁻¹`
  have hphiv_eq : (fun s => phiv P.X a ℓ₁ ℓ₂ v s)
      = fun s => (6 * ℓ₁ * P.X * a * v) * ((dtilde P.X s a) ^ 4)⁻¹ - phi P.X a ℓ₁ ℓ₂ s := by
    funext s; simp only [phiv]; rw [div_eq_mul_inv]
  rw [hphiv_eq]
  convert hsub using 1
  -- reconcile the value of the first term's derivative
  rw [sub_left_inj]
  field_simp
  ring

/-- §5 Step-4 phase magnitude (v-large regime): `|φ_v| ≤ 10⁵·ℓ₁Xa|v|/D⁴`. -/
theorem phiv_abs_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ v r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hvlarge : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |v|) :
    |phiv P.X a ℓ₁ ℓ₂ v r| ≤ 10 ^ 5 * (ℓ₁ * P.X * a * |v| / S.D ^ 4) := by
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
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hvabs_nn : (0:ℝ) ≤ |v| := abs_nonneg _
  -- the L-scale `L = ℓ₁·(ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵))`
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  -- the v-large hypothesis rearranged:  10⁴⁷·L ≤ ℓ₁·X·a·|v|/D⁴
  have hkey : (10:ℝ) ^ 47 * L ≤ ℓ₁ * P.X * a * |v| / S.D ^ 4 := by
    -- hvlarge: 10⁴⁷·(ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵))·(D⁴/(Xa)) ≤ |v|
    -- multiply both sides by ℓ₁·X·a/D⁴ > 0
    have hcoef_pos : 0 < ℓ₁ * P.X * a / S.D ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hvlarge hcoef_pos.le
    -- LHS = 10⁴⁷·L,  RHS = ℓ₁·X·a·|v|/D⁴
    have hLHS : (ℓ₁ * P.X * a / S.D ^ 4)
        * ((10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)))
        = 10 ^ 47 * L := by
      rw [hL_def]; field_simp
    have hRHS : (ℓ₁ * P.X * a / S.D ^ 4) * |v| = ℓ₁ * P.X * a * |v| / S.D ^ 4 := by ring
    rw [hLHS, hRHS] at hmul; exact hmul
  -- d̃ window and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  set d := dtilde P.X r a with hd_def
  have hd4_pos : 0 < d ^ 4 := by positivity
  -- |φ_v| ≤ |6ℓ₁Xav/d⁴| + |φ|
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- |φ| ≤ 10²⁰·L  (rewrite ℓ₁ℓ₂(ℓ₂−ℓ₁) = ℓ₁·ℓ₂·(ℓ₂−ℓ₁) so the L-scale matches)
  have hphiL : phi P.X a ℓ₁ ℓ₂ r ≤ 10 ^ 20 * L := by
    rw [hL_def]; exact hphi_ub
  -- |6ℓ₁Xav/d⁴| = 6ℓ₁Xa|v|/d⁴
  have hpref_pos : 0 < 6 * ℓ₁ * P.X * a := by positivity
  have hterm_abs : |6 * ℓ₁ * P.X * a * v / d ^ 4| = 6 * ℓ₁ * P.X * a * |v| / d ^ 4 := by
    rw [abs_div, abs_of_pos hd4_pos, abs_mul, abs_of_pos hpref_pos]
  -- first term ≤ 6·10⁴·ℓ₁Xa|v|/D⁴  (since d ≥ D/10)
  have hterm_le : 6 * ℓ₁ * P.X * a * |v| / d ^ 4
      ≤ 6 * 10 ^ 4 * (ℓ₁ * P.X * a * |v| / S.D ^ 4) := by
    have hd4_lo : (S.D / 10) ^ 4 ≤ d ^ 4 := pow_le_pow_left₀ (by positivity) hd_lo 4
    have hnum_nn : (0:ℝ) ≤ 6 * ℓ₁ * P.X * a * |v| := by positivity
    have hDpow_pos : 0 < (S.D / 10) ^ 4 := by positivity
    calc 6 * ℓ₁ * P.X * a * |v| / d ^ 4
        ≤ 6 * ℓ₁ * P.X * a * |v| / (S.D / 10) ^ 4 := by
          apply div_le_div_of_nonneg_left hnum_nn hDpow_pos hd4_lo
      _ = 6 * 10 ^ 4 * (ℓ₁ * P.X * a * |v| / S.D ^ 4) := by ring
  -- |φ| ≤ ℓ₁Xa|v|/D⁴  (since 10²⁰·L ≤ 10⁴⁷·L ≤ ℓ₁Xa|v|/D⁴)
  have hphi_le : phi P.X a ℓ₁ ℓ₂ r ≤ ℓ₁ * P.X * a * |v| / S.D ^ 4 := by
    have h2047 : (10:ℝ) ^ 20 * L ≤ 10 ^ 47 * L := by
      apply mul_le_mul_of_nonneg_right _ hLpos.le; norm_num
    linarith [hphiL, h2047, hkey]
  -- assemble
  have hsplit : |phiv P.X a ℓ₁ ℓ₂ v r|
      ≤ 6 * ℓ₁ * P.X * a * |v| / d ^ 4 + phi P.X a ℓ₁ ℓ₂ r := by
    calc |phiv P.X a ℓ₁ ℓ₂ v r|
        = |6 * ℓ₁ * P.X * a * v / d ^ 4 - phi P.X a ℓ₁ ℓ₂ r| := by rw [phiv, hd_def]
      _ ≤ |6 * ℓ₁ * P.X * a * v / d ^ 4| + |phi P.X a ℓ₁ ℓ₂ r| := abs_sub _ _
      _ = 6 * ℓ₁ * P.X * a * |v| / d ^ 4 + phi P.X a ℓ₁ ℓ₂ r := by
          rw [hterm_abs, abs_of_nonneg hphi_nn]
  calc |phiv P.X a ℓ₁ ℓ₂ v r|
      ≤ 6 * ℓ₁ * P.X * a * |v| / d ^ 4 + phi P.X a ℓ₁ ℓ₂ r := hsplit
    _ ≤ 6 * 10 ^ 4 * (ℓ₁ * P.X * a * |v| / S.D ^ 4)
          + ℓ₁ * P.X * a * |v| / S.D ^ 4 := by linarith [hterm_le, hphi_le]
    _ ≤ 10 ^ 5 * (ℓ₁ * P.X * a * |v| / S.D ^ 4) := by
        have hWnn : (0:ℝ) ≤ ℓ₁ * P.X * a * |v| / S.D ^ 4 := by positivity
        nlinarith [hWnn]

/-- §5 Step-4 phase derivative lower bound (v-large): `|φ_v'| ≥ ℓ₁Xa|v|/(D⁴R·10⁵⁰)` (≍ T/R). -/
theorem phiv_deriv_lb {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ v r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hvlarge : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |v|) :
    ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R * 10 ^ 50)
      ≤ |deriv (fun s => phiv P.X a ℓ₁ ℓ₂ v s) r| := by
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
  -- the L-scale and the W'-scale
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  set W := ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R) with hW_def
  have hWnn : (0:ℝ) ≤ W := by rw [hW_def]; positivity
  -- B = D/R, i.e. B·R = D
  have hBR : S.B * S.R = S.D := by rw [Scale.B_eq_D_div_R]; field_simp
  -- the v-large hypothesis rearranged: 10⁴⁷·L ≤ ℓ₁·X·a·|v|/D⁴ = W·R
  have hWR : ℓ₁ * P.X * a * |v| / S.D ^ 4 = W * S.R := by rw [hW_def]; field_simp
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
  -- d̃' window
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
  -- value = VTERM - φ1,  VTERM = -24ℓ₁Xav·d1/d⁵
  set VTERM := (-24) * ℓ₁ * P.X * a * v * d1 / d ^ 5 with hVTERM_def
  -- reverse triangle: |VTERM - φ1| ≥ |VTERM| - |φ1|
  have htri : |VTERM| - |φ1| ≤ |VTERM - φ1| := by
    have := abs_sub_abs_le_abs_sub VTERM φ1
    linarith [this]
  refine le_trans ?_ htri
  -- positivity helpers
  have hd5_pos : 0 < d ^ 5 := by positivity
  have h24pref_pos : 0 < 24 * ℓ₁ * P.X * a := by positivity
  -- |VTERM| = 24ℓ₁Xa|v|·|d1|/d⁵
  have hVTERM_abs : |VTERM| = 24 * ℓ₁ * P.X * a * |v| * |d1| / d ^ 5 := by
    rw [hVTERM_def, abs_div, abs_of_pos hd5_pos]
    rw [show ((-24) * ℓ₁ * P.X * a * v * d1)
        = -((24 * ℓ₁ * P.X * a) * v * d1) by ring, abs_neg]
    rw [abs_mul, abs_mul, abs_of_pos h24pref_pos]
  -- ============ Main term lower bound:  10⁻¹¹·W ≤ |VTERM| ============
  -- |VTERM| ≥ 24ℓ₁Xa|v|·(B/10⁶)/(18D)⁵
  have hmain : (1 / 10 ^ 11) * W ≤ |VTERM| := by
    rw [hVTERM_abs]
    -- numerator monotone:  24ℓ₁Xa|v|·(B/10⁶) ≤ 24ℓ₁Xa|v|·|d1|
    have hnum_lo : 24 * ℓ₁ * P.X * a * |v| * (S.B / 1000000)
        ≤ 24 * ℓ₁ * P.X * a * |v| * |d1| := by
      apply mul_le_mul_of_nonneg_left hd1_lo (by positivity)
    -- denominator:  d⁵ ≤ (18D)⁵
    have hd5_le : d ^ 5 ≤ (18 * S.D) ^ 5 := pow_le_pow_left₀ hd_pos.le hd_hi 5
    have hd185_pos : 0 < (18 * S.D) ^ 5 := by positivity
    have hstep : 24 * ℓ₁ * P.X * a * |v| * (S.B / 1000000) / (18 * S.D) ^ 5
        ≤ 24 * ℓ₁ * P.X * a * |v| * |d1| / d ^ 5 :=
      div_le_div₀ (by positivity) hnum_lo hd5_pos hd5_le
    refine le_trans ?_ hstep
    -- 10⁻¹¹·W ≤ 24ℓ₁Xa|v|·(B/10⁶)/(18D)⁵
    -- use B·R = D:  (B/D⁵) appears; W = ℓ₁Xa|v|/(D⁴R)
    have hreq : 24 * ℓ₁ * P.X * a * |v| * (S.B / 1000000) / (18 * S.D) ^ 5
        = (24 / (1000000 * 18 ^ 5)) * (ℓ₁ * P.X * a * |v| * S.B / S.D ^ 5) := by
      field_simp
    rw [hreq]
    -- ℓ₁Xa|v|·B/D⁵ = W  (since B = D/R, so B/D⁵ = 1/(R·D⁴))
    have hWB : ℓ₁ * P.X * a * |v| * S.B / S.D ^ 5 = W := by
      rw [hW_def, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (ℓ₁ * P.X * a * |v| * S.D ^ 4) * hBR
    rw [hWB]
    apply mul_le_mul_of_nonneg_right _ hWnn
    norm_num
  -- ============ Noise upper bound:  |φ1| ≤ (1/2)·10⁻¹¹·W ============
  -- |φ1| ≤ 10³⁵·L/R,  and 10⁴⁷·L ≤ W·R, so 10³⁵·L ≤ 10⁻¹²·W·R, /R: 10³⁵·L/R ≤ 10⁻¹²·W
  have hnoise : |φ1| ≤ (1 / 2) * (1 / 10 ^ 11) * W := by
    -- |φ1| ≤ 10³⁵·(L/R)
    have hphi1 : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
      rw [hφ1_def, hL_def]
      calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
          ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
        _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
    refine le_trans hphi1 ?_
    -- 10³⁵·(L/R) ≤ (1/2)·10⁻¹¹·W
    -- from hkey:  10⁴⁷·L ≤ W·R, i.e. L ≤ W·R/10⁴⁷
    have hL_le : L ≤ W * S.R / 10 ^ 47 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hkey]
    have hRpos' : (0:ℝ) < S.R := hRpos
    calc 10 ^ 35 * (L / S.R)
        ≤ 10 ^ 35 * ((W * S.R / 10 ^ 47) / S.R) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply div_le_div_of_nonneg_right hL_le hRpos'.le
      _ = (1 / 10 ^ 12) * W := by field_simp
      _ ≤ (1 / 2) * (1 / 10 ^ 11) * W := by
          apply mul_le_mul_of_nonneg_right _ hWnn; norm_num
  -- ============ Combine ============
  -- target = ℓ₁Xa|v|/(D⁴R·10⁵⁰) = 10⁻⁵⁰·W
  have htgt_eq : ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R * 10 ^ 50) = (1 / 10 ^ 50) * W := by
    rw [hW_def]; field_simp
  rw [htgt_eq]
  -- |VTERM| - |φ1| ≥ 10⁻¹¹·W - (1/2)·10⁻¹¹·W = (1/2)·10⁻¹¹·W ≥ 10⁻⁵⁰·W
  have hhalf : (1 / 2) * (1 / 10 ^ 11) * W ≤ |VTERM| - |φ1| := by
    linarith [hmain, hnoise]
  have hsmall50 : (1 / 10 ^ 50) * W ≤ (1 / 2) * (1 / 10 ^ 11) * W := by
    apply mul_le_mul_of_nonneg_right _ hWnn; norm_num
  linarith [hhalf, hsmall50]

end Squarefree
