import Squarefree.Lower.Step1Phase

/-!
# §5 Steps-2&3 shared smooth phase `φ_f`

The §5 Steps-2&3 shared smooth phase (writeup 898)

  `φ_f(r) = (d̃ₐ(r)⁴/(6Xa))·(f + 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa·b̃ₐ(r)²/d̃ₐ(r)⁵)`.

The inner sum's second term is exactly the Step-1 phase `φ = phi X a ℓ₁ ℓ₂`, so

  `φ_f = (d̃⁴/(6Xa))·(f + φ)`.

This file gives its definition and its derivative, reusing `phi_hasDerivAt`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- The §5 Steps-2&3 shared smooth phase `φ_f(r) = (d̃ₐ(r)⁴/(6Xa))·(f + φ(r))` (writeup 898),
where `φ = phi X a ℓ₁ ℓ₂` is the Step-1 phase. -/
noncomputable def phif (X a ℓ₁ ℓ₂ f r : ℝ) : ℝ :=
  (dtilde X r a) ^ 4 / (6 * X * a) * (f + phi X a ℓ₁ ℓ₂ r)

/-- Derivative of `φ_f`, via the product rule (reusing `phi_hasDerivAt`). -/
theorem phif_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ} (ha0 : 0 < a) (hr0 : 0 < r)
    (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => phif P.X a ℓ₁ ℓ₂ f s)
      ( (4 * (dtilde P.X r a) ^ 3 * deriv (fun s => dtilde P.X s a) r) / (6 * P.X * a)
          * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (dtilde P.X r a) ^ 4 / (6 * P.X * a) * deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r ) r := by
  -- nonvanishing of the constant `6·X·a`
  have hXa : (6 : ℝ) * P.X * a ≠ 0 := by
    have hX := P.X_pos; positivity
  -- derivative of `d̃`
  have hd : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun s => dtilde P.X s a) r) r :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hr0).differentiableAt.hasDerivAt
  -- derivative of `d̃⁴`
  have hd4 : HasDerivAt (fun s => (dtilde P.X s a) ^ 4)
      (4 * (dtilde P.X r a) ^ 3 * deriv (fun s => dtilde P.X s a) r) r := by
    simpa using hd.pow 4
  -- derivative of `f + φ`
  have hg : HasDerivAt (fun s => f + phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r) r :=
    (((phi_hasDerivAt ha0 hr0 hrl hℓne).differentiableAt.hasDerivAt).const_add f)
  -- product rule then divide by the constant
  have hprod : HasDerivAt (fun s => (dtilde P.X s a) ^ 4 * (f + phi P.X a ℓ₁ ℓ₂ s))
      ((4 * (dtilde P.X r a) ^ 3 * deriv (fun s => dtilde P.X s a) r) * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (dtilde P.X r a) ^ 4 * deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r) r := hd4.mul hg
  have hfinal := hprod.div_const (6 * P.X * a)
  -- rewrite `phif` as the divided product, and reconcile derivative values
  have hphif_eq : (fun s => phif P.X a ℓ₁ ℓ₂ f s)
      = fun s => (dtilde P.X s a) ^ 4 * (f + phi P.X a ℓ₁ ℓ₂ s) / (6 * P.X * a) := by
    funext s; simp only [phif]; ring
  rw [hphif_eq]
  convert hfinal using 1
  field_simp

/-- §5 Step-3 phase magnitude: in the `f`-large regime, `|φ_f| ≤ 10⁶·|f|·D⁴/(XA)` (≍ T). -/
theorem phif_abs_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    |phif P.X a ℓ₁ ℓ₂ f r| ≤ 10 ^ 6 * (|f| * S.D ^ 4 / (P.X * S.A)) := by
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
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) := by positivity
  -- d̃ bounds and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  set d := dtilde P.X r a with hd_def
  -- the prefactor c := d⁴/(6Xa) > 0
  have hc_pos : 0 < d ^ 4 / (6 * P.X * a) := by positivity
  -- |phif| = c · |f + phi|
  have habs_eq : |phif P.X a ℓ₁ ℓ₂ f r| = d ^ 4 / (6 * P.X * a) * |f + phi P.X a ℓ₁ ℓ₂ r| := by
    rw [phif, hd_def, abs_mul, abs_of_pos hc_pos]
  rw [habs_eq]
  -- |φ| ≤ 10²⁰·L
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- |f + φ| ≤ 2·|f|  (since |φ| ≤ 10²⁰·L ≤ 10⁵⁵·L ≤ |f|)
  have hphi_le_f : phi P.X a ℓ₁ ℓ₂ r ≤ |f| := by
    have h1 : phi P.X a ℓ₁ ℓ₂ r ≤ 10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := hphi_ub
    have h2 : (10:ℝ) ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5))
        ≤ 10 ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := by
      apply mul_le_mul_of_nonneg_right _ hLpos.le; norm_num
    linarith
  have hfphi : |f + phi P.X a ℓ₁ ℓ₂ r| ≤ 2 * |f| := by
    calc |f + phi P.X a ℓ₁ ℓ₂ r| ≤ |f| + |phi P.X a ℓ₁ ℓ₂ r| := abs_add_le _ _
      _ = |f| + phi P.X a ℓ₁ ℓ₂ r := by rw [abs_of_nonneg hphi_nn]
      _ ≤ |f| + |f| := by linarith
      _ = 2 * |f| := by ring
  -- prefactor bound: c = d⁴/(6Xa) ≤ (18D)⁴/(6X·(A/5))
  have hc_le : d ^ 4 / (6 * P.X * a) ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hd_pos.le hd_hi 4) (by positivity)
    have : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
      apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
    linarith
  -- combine
  have hfabs_nn : (0:ℝ) ≤ |f| := abs_nonneg _
  calc d ^ 4 / (6 * P.X * a) * |f + phi P.X a ℓ₁ ℓ₂ r|
      ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) * (2 * |f|) := by
        apply mul_le_mul hc_le hfphi (abs_nonneg _) (by positivity)
    _ = (18 ^ 4 * 5 / 3) * (|f| * S.D ^ 4 / (P.X * S.A)) := by
        field_simp; ring
    _ ≤ 10 ^ 6 * (|f| * S.D ^ 4 / (P.X * S.A)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        norm_num

/-- §5 Step-3 phase derivative lower bound: in the `f`-large regime the `f`-term dominates,
giving `|φ_f'| ≥ |f|·D⁴/(XA·R·10⁵⁰)` (≍ T/R). -/
theorem phif_deriv_lb {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hflarge : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    |f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50)
      ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
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
  -- the L-scale
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  -- the W-scale W = D⁴/(XAR)
  set W := S.D ^ 4 / (P.X * S.A * S.R) with hW_def
  have hWpos : 0 < W := by rw [hW_def]; positivity
  -- B = D/R, i.e. B·R = D
  have hBR : S.B * S.R = S.D := by
    rw [Scale.B_eq_D_div_R]; field_simp
  -- D³·B/(XA) = W  (since B·R = D, so D³·B = D⁴/R, /(XA) = D⁴/(XAR) = W)
  have hDB : S.D ^ 3 * S.B / (P.X * S.A) = W := by
    rw [hW_def, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S.D ^ 3 * P.X * S.A) * hBR
  -- D⁴/(XA) = W·R
  have hD4 : S.D ^ 4 / (P.X * S.A) = W * S.R := by
    rw [hW_def]; field_simp
  -- d̃ bounds and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  -- d̃' bounds
  obtain ⟨hd1_lo, hd1_hi⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- |φ| ≤ 10²⁰·L
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- |φ'| ≤ 10³⁵·L/R
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- rewrite the derivative via phif_hasDerivAt
  have hPD := phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r)
    ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun s => dtilde P.X s a) r with hd1_def
  set φ := phi P.X a ℓ₁ ℓ₂ r with hφ_def
  set φ1 := deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r with hφ1_def
  -- abbreviate the coefficients
  set c3 := 4 * d ^ 3 * d1 / (6 * P.X * a) with hc3_def
  set c4 := d ^ 4 / (6 * P.X * a) with hc4_def
  -- the value is c3·(f + φ) + c4·φ1 = c3·f + (c3·φ + c4·φ1)
  have hval_eq : c3 * (f + φ) + c4 * φ1 = c3 * f + (c3 * φ + c4 * φ1) := by ring
  rw [hval_eq]
  -- |c3·f + noise| ≥ |c3·f| - |noise| ≥ |c3·f| - |c3·φ| - |c4·φ1|
  have htri : |c3 * f| - (|c3 * φ| + |c4 * φ1|)
      ≤ |c3 * f + (c3 * φ + c4 * φ1)| := by
    -- |c3·f| = |(c3·f + noise) - noise| ≤ |c3·f + noise| + |noise|
    have hsplit : |c3 * f| ≤ |c3 * f + (c3 * φ + c4 * φ1)| + |c3 * φ + c4 * φ1| := by
      calc |c3 * f| = |(c3 * f + (c3 * φ + c4 * φ1)) + (-(c3 * φ + c4 * φ1))| := by ring_nf
        _ ≤ |c3 * f + (c3 * φ + c4 * φ1)| + |(-(c3 * φ + c4 * φ1))| := abs_add_le _ _
        _ = |c3 * f + (c3 * φ + c4 * φ1)| + |c3 * φ + c4 * φ1| := by rw [abs_neg]
    have h2 : |c3 * φ + c4 * φ1| ≤ |c3 * φ| + |c4 * φ1| := abs_add_le _ _
    linarith
  refine le_trans ?_ htri
  -- positivity helpers
  have hfabs_nn : (0:ℝ) ≤ |f| := abs_nonneg _
  have hd3_pos : 0 < d ^ 3 := by positivity
  have hd4_pos : 0 < d ^ 4 := by positivity
  have h6Xa_pos : 0 < 6 * P.X * a := by positivity
  -- |c3| = 4·d³·|d1|/(6Xa)
  have hc3_abs : |c3| = 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
    rw [hc3_def, abs_div, abs_of_pos h6Xa_pos, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4),
        abs_of_pos hd3_pos]
  -- |c4| = d⁴/(6Xa) = c4 (it's positive)
  have hc4_pos : 0 < c4 := by rw [hc4_def]; positivity
  -- ============ Main term lower bound:  10⁻¹¹·W·|f| ≤ |c3·f| ============
  have hmain : (1 / 10 ^ 11) * W * |f| ≤ |c3 * f| := by
    rw [abs_mul]
    rw [hc3_abs]
    -- |c3| ≥ 10⁻¹¹·W : reduce 4·d³·|d1|/(6Xa) ≥ 4·(D/10)³·(B/10⁶)/(6X·11A)
    have hnum_lo : 4 * (S.D / 10) ^ 3 * (S.B / 1000000) ≤ 4 * d ^ 3 * |d1| := by
      have hp1 : (S.D / 10) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (by positivity) hd_lo 3
      have h1 : 4 * (S.D / 10) ^ 3 ≤ 4 * d ^ 3 := by linarith [hp1]
      have h2 : (0:ℝ) ≤ 4 * (S.D / 10) ^ 3 := by positivity
      exact mul_le_mul h1 hd1_lo (by positivity) (le_trans h2 h1)
    have hden_le : 6 * P.X * a ≤ 6 * P.X * (11 * S.A) := by
      apply mul_le_mul_of_nonneg_left ha_hi (by positivity)
    have hdiv_lo : 4 * (S.D / 10) ^ 3 * (S.B / 1000000) / (6 * P.X * (11 * S.A))
        ≤ 4 * d ^ 3 * |d1| / (6 * P.X * a) :=
      div_le_div₀ (by positivity) hnum_lo h6Xa_pos hden_le
    have hc3lo : (1 / 10 ^ 11) * W ≤ 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
      refine le_trans ?_ hdiv_lo
      -- 10⁻¹¹·W ≤ 4·(D/10)³·(B/10⁶)/(6X·11A)
      have hreq : 4 * (S.D / 10) ^ 3 * (S.B / 1000000) / (6 * P.X * (11 * S.A))
          = (4 / (1000 * 1000000 * 66)) * (S.D ^ 3 * S.B / (P.X * S.A)) := by
        field_simp
        ring
      rw [hreq, hDB]
      apply mul_le_mul_of_nonneg_right _ hWpos.le
      norm_num
    have : (1 / 10 ^ 11) * W * |f| ≤ (4 * d ^ 3 * |d1| / (6 * P.X * a)) * |f| := by
      apply mul_le_mul_of_nonneg_right hc3lo hfabs_nn
    linarith
  -- ============ Noise A upper bound:  |c3·φ| ≤ 10³¹·W·L ============
  have hnoiseA : |c3 * φ| ≤ 10 ^ 31 * W * L := by
    rw [abs_mul, hc3_abs, abs_of_nonneg hphi_nn]
    -- |c3| ≤ (4·18³·10⁶·5/6)·W  and φ ≤ 10²⁰·L
    have hc3hi : 4 * d ^ 3 * |d1| / (6 * P.X * a) ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6) * W := by
      have hnum_hi : 4 * d ^ 3 * |d1| ≤ 4 * (18 * S.D) ^ 3 * (1000000 * S.B) := by
        have hp1 : d ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hd_pos.le hd_hi 3
        have h1 : 4 * d ^ 3 ≤ 4 * (18 * S.D) ^ 3 := by linarith [hp1]
        have h2 : (0:ℝ) ≤ 4 * d ^ 3 := by positivity
        exact mul_le_mul h1 hd1_hi (abs_nonneg _) (le_trans h2 h1)
      have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
        apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
      have hstep : 4 * d ^ 3 * |d1| / (6 * P.X * a)
          ≤ 4 * (18 * S.D) ^ 3 * (1000000 * S.B) / (6 * P.X * (S.A / 5)) :=
        div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
      refine le_trans hstep ?_
      have hreq : 4 * (18 * S.D) ^ 3 * (1000000 * S.B) / (6 * P.X * (S.A / 5))
          = (4 * 18 ^ 3 * 1000000 * 5 / 6) * (S.D ^ 3 * S.B / (P.X * S.A)) := by
        field_simp
      rw [hreq, hDB]
    have hphiL : φ ≤ 10 ^ 20 * L := hphi_ub
    calc 4 * d ^ 3 * |d1| / (6 * P.X * a) * φ
        ≤ ((4 * 18 ^ 3 * 1000000 * 5 / 6) * W) * (10 ^ 20 * L) := by
          apply mul_le_mul hc3hi hphiL hphi_nn (by positivity)
      _ ≤ 10 ^ 31 * W * L := by
          rw [show ((4 * 18 ^ 3 * 1000000 * 5 / 6) * W) * (10 ^ 20 * L)
              = ((4 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 20) * (W * L) by ring,
              show (10:ℝ) ^ 31 * W * L = 10 ^ 31 * (W * L) by ring]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          norm_num
  -- ============ Noise B upper bound:  |c4·φ1| ≤ 10⁴⁰·W·L ============
  have hnoiseB : |c4 * φ1| ≤ 10 ^ 40 * W * L := by
    rw [abs_mul, abs_of_pos hc4_pos]
    -- c4 = d⁴/(6Xa) ≤ (18D)⁴/(6X·(A/5)) = (18⁴·5/6)·D⁴/(XA) = (18⁴·5/6)·W·R
    have hc4hi : c4 ≤ (18 ^ 4 * 5 / 6) * (W * S.R) := by
      rw [hc4_def]
      have hnum_hi : d ^ 4 ≤ (18 * S.D) ^ 4 := pow_le_pow_left₀ hd_pos.le hd_hi 4
      have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
        apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
      have hstep : d ^ 4 / (6 * P.X * a) ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) :=
        div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
      refine le_trans hstep ?_
      have hreq : (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5))
          = (18 ^ 4 * 5 / 6) * (S.D ^ 4 / (P.X * S.A)) := by
        field_simp
      rw [hreq, hD4]
    -- |φ1| ≤ 10³⁵·L/R
    have hphi1 : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
      have h := hphi'_ub
      rw [hφ1_def]
      rw [hL_def]
      calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
          ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := h
        _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by
            rw [div_div]
    calc c4 * |φ1|
        ≤ ((18 ^ 4 * 5 / 6) * (W * S.R)) * (10 ^ 35 * (L / S.R)) := by
          apply mul_le_mul hc4hi hphi1 (abs_nonneg _) (by positivity)
      _ = ((18 ^ 4 * 5 / 6) * 10 ^ 35) * (W * L) := by
          field_simp
      _ ≤ 10 ^ 40 * W * L := by
          rw [show (10:ℝ) ^ 40 * W * L = 10 ^ 40 * (W * L) by ring]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          norm_num
  -- ============ Combine ============
  -- L ≤ 10⁻⁵⁵·|f|  (from hflarge)
  have hL_le : L ≤ (1 / 10 ^ 55) * |f| := by
    have hf55 : (10:ℝ) ^ 55 * L ≤ |f| := hflarge
    nlinarith [hf55]
  -- target = W·|f|·10⁻⁵⁰
  have htgt_eq : |f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50) = (1 / 10 ^ 50) * (W * |f|) := by
    rw [hW_def]; field_simp
  rw [htgt_eq]
  -- |c3·f| - (|c3·φ| + |c4·φ1|) ≥ 10⁻¹¹·W·|f| - (10³¹·W·L + 10⁴⁰·W·L)
  have hnoise_bd : |c3 * φ| + |c4 * φ1| ≤ (10 ^ 31 + 10 ^ 40) * W * L := by
    have : (10:ℝ) ^ 31 * W * L + 10 ^ 40 * W * L = (10 ^ 31 + 10 ^ 40) * W * L := by ring
    linarith [hnoiseA, hnoiseB]
  -- (10³¹+10⁴⁰)·W·L ≤ (1/2)·10⁻¹¹·W·|f|
  have hnoise_small : (10 ^ 31 + 10 ^ 40) * W * L ≤ (1 / 2) * (1 / 10 ^ 11) * W * |f| := by
    have hWL : (10 ^ 31 + 10 ^ 40) * W * L ≤ (10 ^ 31 + 10 ^ 40) * W * ((1 / 10 ^ 55) * |f|) := by
      apply mul_le_mul_of_nonneg_left hL_le (by positivity)
    refine le_trans hWL ?_
    rw [show ((10:ℝ) ^ 31 + 10 ^ 40) * W * ((1 / 10 ^ 55) * |f|)
        = ((10 ^ 31 + 10 ^ 40) * (1 / 10 ^ 55)) * (W * |f|) by ring,
        show (1:ℝ) / 2 * (1 / 10 ^ 11) * W * |f| = ((1/2) * (1/10^11)) * (W * |f|) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    norm_num
  -- assemble
  have : (1 / 10 ^ 50) * (W * |f|) ≤ (1 / 10 ^ 11) * W * |f| - (10 ^ 31 + 10 ^ 40) * W * L := by
    have hhalf : (1 / 2) * (1 / 10 ^ 11) * W * |f| ≤ (1 / 10 ^ 11) * W * |f|
        - (10 ^ 31 + 10 ^ 40) * W * L := by linarith [hnoise_small]
    have hsmall50 : (1 / 10 ^ 50) * (W * |f|) ≤ (1 / 2) * (1 / 10 ^ 11) * W * |f| := by
      rw [show (1:ℝ) / 2 * (1 / 10 ^ 11) * W * |f| = ((1/2) * (1/10^11)) * (W * |f|) by ring,
          show (1:ℝ) / 10 ^ 50 * (W * |f|) = (1 / 10 ^ 50) * (W * |f|) by ring]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      norm_num
    linarith
  linarith [hmain, hnoise_bd, this]

end Squarefree
