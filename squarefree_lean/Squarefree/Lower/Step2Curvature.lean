import Squarefree.Lower.Step23Phase
import Squarefree.Lower.DefectBounds

/-!
# §5 Step-2 BANDS analytic facts about the phase `φ_f`

The BANDS count step `step2_subset_count` (`Step2Bands.lean`) defers four analytic facts about
`φ_f := phif P.X a ℓ₁ ℓ₂ f` on a band window `[r₀,r₁] ⊆ [S.R, 3·S.R]`.  This file proves the
two *tractable* ones (the smoothness and the derivative upper bound), reusing the `d̃` (dtilde)
derivative machinery from `DefectDeriv`/`Step23Phase`.

* `phif_contDiffOn` — `ContDiffOn ℝ 2 φ_f (Icc r₀ r₁)`.  (Note: the *global* `ContDiff ℝ 2 φ_f`
  is **false** — `φ_f` has poles where `d̃` vanishes / `s ≤ 0` — so `step2_subset_count`/
  `bands_count_mono` should be restated with `ContDiffOn`.)

* `phif_deriv_ub` — the derivative upper bound `|φ_f'| ≤ 10¹⁴·T₀/R` with `T₀ := |f|·D⁴/(XA)`.
  This is the `f`-large companion of `phif_deriv_lb` (`Step23Phase`).  The constant `10¹⁴` is
  genuine: with the *bare* `T₀` the bound `|φ_f'| ≤ T₀/R` is **false** (off by an absolute
  constant), so the bands variation scale must absorb it.

The remaining two facts (`hmono`, `hlower`) require the **second derivative** `φ_f''` and a sign
analysis of it; that machinery (a 2nd derivative of the `b̃²/d̃⁵` term) does not yet exist — see
the module note at the end.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **`φ_f` is `C²` on the band window.**  On `[r₀,r₁]` with `0 < r₀` (so `d̃(s) > 0` and `d̃` is
`C²` at `s` and at `s+ℓ₁`), the phase `φ_f = (d̃⁴/(6Xa))·(f + 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa·b̃²/d̃⁵)` is `C²`.
This is the `ContDiffOn` form of the `hcd` hypothesis of `step2_subset_count`. -/
theorem phif_contDiffOn {X a ℓ₁ ℓ₂ f r₀ r₁ : ℝ} (hX : 0 < X) (ha : 0 < a)
    (hr₀ : 0 < r₀) (hℓ : 0 ≤ ℓ₁) :
    ContDiffOn ℝ 2 (fun s => phif X a ℓ₁ ℓ₂ f s) (Set.Icc r₀ r₁) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ (Set.mem_Icc.mp hx).1
  have hxℓpos : 0 < x + ℓ₁ := by linarith
  -- `d̃` is `C²` at `x` and at `x + ℓ₁`
  have hd : ContDiffAt ℝ 2 (fun s => dtilde X s a) x := dtilde_contDiffAt_r hX ha hxpos
  have hdℓ : ContDiffAt ℝ 2 (fun s => dtilde X (s + ℓ₁) a) x := by
    have hshift : ContDiffAt ℝ 2 (fun s : ℝ => s + ℓ₁) x := by fun_prop
    exact (dtilde_contDiffAt_r hX ha hxℓpos).comp x hshift
  have hdne : dtilde X x a ≠ 0 := ne_of_gt (dtilde_pos hX ha hxpos)
  -- `b̃(s) = (d̃(s+ℓ₁) − d̃(s))/ℓ₁` is `C²` at `x`
  have hbt : ContDiffAt ℝ 2 (fun s => bt X a ℓ₁ s) x := by
    have : ContDiffAt ℝ 2 (fun s => (dtilde X (s + ℓ₁) a - dtilde X s a) / ℓ₁) x :=
      (hdℓ.sub hd).div_const ℓ₁
    simpa only [bt] using this
  -- `φ(s) = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa·b̃²/d̃⁵` is `C²` at `x`
  have hphi : ContDiffAt ℝ 2 (fun s => phi X a ℓ₁ ℓ₂ s) x := by
    have hnum : ContDiffAt ℝ 2
        (fun s => 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * (bt X a ℓ₁ s) ^ 2) x := by
      exact (contDiffAt_const).mul (hbt.pow 2)
    have hden : ContDiffAt ℝ 2 (fun s => (dtilde X s a) ^ 5) x := hd.pow 5
    have : ContDiffAt ℝ 2
        (fun s => 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * (bt X a ℓ₁ s) ^ 2 / (dtilde X s a) ^ 5) x :=
      hnum.div hden (pow_ne_zero 5 hdne)
    simpa only [phi] using this
  -- `φ_f(s) = (d̃⁴/(6Xa))·(f + φ(s))` is `C²` at `x`
  have hpref : ContDiffAt ℝ 2 (fun s => (dtilde X s a) ^ 4 / (6 * X * a)) x :=
    (hd.pow 4).div_const (6 * X * a)
  have hfphi : ContDiffAt ℝ 2 (fun s => f + phi X a ℓ₁ ℓ₂ s) x :=
    (contDiffAt_const).add hphi
  have : ContDiffAt ℝ 2
      (fun s => (dtilde X s a) ^ 4 / (6 * X * a) * (f + phi X a ℓ₁ ℓ₂ s)) x := hpref.mul hfphi
  have hfin : ContDiffAt ℝ 2 (fun s => phif X a ℓ₁ ℓ₂ f s) x := by
    simpa only [phif] using this
  exact hfin.contDiffWithinAt

/-- **§5 Step-2 phase derivative upper bound.**  In the `f`-large regime the `f`-term dominates,
giving `|φ_f'(r)| ≤ 10¹⁴·|f|·D⁴/(XA·R)` (`≍ T/R`).  This is the upper-bound companion of
`phif_deriv_lb`.  NOTE: the constant `10¹⁴` is genuine; with the bare scale `|f|·D⁴/(XA)` the
hypothesis `hd1` of `step2_subset_count` (`|φ_f'| ≤ T/R` with `T = |f|·D⁴/(XA)`) is **false**.  The
bands variation scale must therefore be taken as `T = 10¹⁴·|f|·D⁴/(XA)` (still `≍` the writeup's
line-917 `T` in the `f`-large regime, where the `f`-monomial dominates the `max`). -/
theorem phif_deriv_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r|
      ≤ |f| * S.D ^ 4 / (P.X * S.A) * 10 ^ 14 / S.R := by
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
  -- B·R = D
  have hBR : S.B * S.R = S.D := by rw [Scale.B_eq_D_div_R]; field_simp
  -- D³·B/(XA) = W
  have hDB : S.D ^ 3 * S.B / (P.X * S.A) = W := by
    rw [hW_def, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S.D ^ 3 * P.X * S.A) * hBR
  -- D⁴/(XA) = W·R
  have hD4 : S.D ^ 4 / (P.X * S.A) = W * S.R := by rw [hW_def]; field_simp
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
  set c3 := 4 * d ^ 3 * d1 / (6 * P.X * a) with hc3_def
  set c4 := d ^ 4 / (6 * P.X * a) with hc4_def
  -- the value is c3·(f + φ) + c4·φ1
  -- |value| ≤ |c3|·|f+φ| + |c4|·|φ1| ≤ |c3|·2|f| + |c4|·|φ1|
  have hfabs_nn : (0:ℝ) ≤ |f| := abs_nonneg _
  have hd3_pos : 0 < d ^ 3 := by positivity
  have hd4_pos : 0 < d ^ 4 := by positivity
  have h6Xa_pos : 0 < 6 * P.X * a := by positivity
  -- |c3| = 4·d³·|d1|/(6Xa)
  have hc3_abs : |c3| = 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
    rw [hc3_def, abs_div, abs_of_pos h6Xa_pos, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos hd3_pos]
  have hc4_pos : 0 < c4 := by rw [hc4_def]; positivity
  -- |f + φ| ≤ 2|f|
  have hphi_le_f : φ ≤ |f| := by
    have h1 : φ ≤ 10 ^ 20 * L := by rw [hL_def]; exact hphi_ub
    have h2 : (10:ℝ) ^ 20 * L ≤ 10 ^ 55 * L := by
      apply mul_le_mul_of_nonneg_right _ hLpos.le; norm_num
    have h3 : (10:ℝ) ^ 55 * L ≤ |f| := hflarge
    linarith
  have hfphi : |f + φ| ≤ 2 * |f| := by
    calc |f + φ| ≤ |f| + |φ| := abs_add_le _ _
      _ = |f| + φ := by rw [abs_of_nonneg hphi_nn]
      _ ≤ |f| + |f| := by linarith
      _ = 2 * |f| := by ring
  -- triangle inequality on the derivative value
  have htri : |c3 * (f + φ) + c4 * φ1| ≤ |c3| * |f + φ| + c4 * |φ1| := by
    calc |c3 * (f + φ) + c4 * φ1| ≤ |c3 * (f + φ)| + |c4 * φ1| := abs_add_le _ _
      _ = |c3| * |f + φ| + |c4| * |φ1| := by rw [abs_mul, abs_mul]
      _ = |c3| * |f + φ| + c4 * |φ1| := by rw [abs_of_pos hc4_pos]
  refine le_trans htri ?_
  -- ============ term 1:  |c3|·|f+φ| ≤ (4·18³·10⁶·5/6·2)·W·|f| ============
  have hc3hi : |c3| ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6) * W := by
    rw [hc3_abs]
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
  have hterm1 : |c3| * |f + φ| ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6 * 2) * (W * |f|) := by
    calc |c3| * |f + φ|
        ≤ ((4 * 18 ^ 3 * 1000000 * 5 / 6) * W) * (2 * |f|) :=
          mul_le_mul hc3hi hfphi (abs_nonneg _) (by positivity)
      _ = (4 * 18 ^ 3 * 1000000 * 5 / 6 * 2) * (W * |f|) := by ring
  -- ============ term 2:  c4·|φ1| ≤ 10⁴⁰·W·L ============
  have hterm2 : c4 * |φ1| ≤ 10 ^ 40 * (W * L) := by
    have hc4hi : c4 ≤ (18 ^ 4 * 5 / 6) * (W * S.R) := by
      rw [hc4_def]
      have hnum_hi : d ^ 4 ≤ (18 * S.D) ^ 4 := pow_le_pow_left₀ hd_pos.le hd_hi 4
      have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
        apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
      have hstep : d ^ 4 / (6 * P.X * a) ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) :=
        div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
      refine le_trans hstep ?_
      have hreq : (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5))
          = (18 ^ 4 * 5 / 6) * (S.D ^ 4 / (P.X * S.A)) := by field_simp
      rw [hreq, hD4]
    have hphi1 : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
      rw [hφ1_def, hL_def]
      calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
          ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
        _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
    calc c4 * |φ1|
        ≤ ((18 ^ 4 * 5 / 6) * (W * S.R)) * (10 ^ 35 * (L / S.R)) :=
          mul_le_mul hc4hi hphi1 (abs_nonneg _) (by positivity)
      _ = ((18 ^ 4 * 5 / 6) * 10 ^ 35) * (W * L) := by field_simp
      _ ≤ 10 ^ 40 * (W * L) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  -- ============ combine:  L ≤ 10⁻⁵⁵·|f| ============
  have hL_le : L ≤ (1 / 10 ^ 55) * |f| := by
    have hf55 : (10:ℝ) ^ 55 * L ≤ |f| := hflarge
    nlinarith [hf55]
  -- target = W·|f|·10¹⁴
  have htgt_eq : |f| * S.D ^ 4 / (P.X * S.A) * 10 ^ 14 / S.R = 10 ^ 14 * (W * |f|) := by
    rw [hW_def]; field_simp
  rw [htgt_eq]
  -- term2 ≤ 10⁴⁰·W·(10⁻⁵⁵|f|) = 10⁻¹⁵·W·|f|
  have hterm2' : c4 * |φ1| ≤ (1 / 10 ^ 15) * (W * |f|) := by
    refine le_trans hterm2 ?_
    have hWL : (10:ℝ) ^ 40 * (W * L) ≤ 10 ^ 40 * (W * ((1 / 10 ^ 55) * |f|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left hL_le hWpos.le
    refine le_trans hWL ?_
    rw [show (10:ℝ) ^ 40 * (W * ((1 / 10 ^ 55) * |f|)) = (10 ^ 40 * (1 / 10 ^ 55)) * (W * |f|) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  -- assemble: term1 + term2 ≤ (const)·W·|f| ≤ 10¹⁴·W·|f|
  have hconst : (4 * 18 ^ 3 * 1000000 * 5 / 6 * 2) + (1 / 10 ^ 15) ≤ (10:ℝ) ^ 14 := by norm_num
  calc |c3| * |f + φ| + c4 * |φ1|
      ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6 * 2) * (W * |f|) + (1 / 10 ^ 15) * (W * |f|) :=
        add_le_add hterm1 hterm2'
    _ = ((4 * 18 ^ 3 * 1000000 * 5 / 6 * 2) + (1 / 10 ^ 15)) * (W * |f|) := by ring
    _ ≤ 10 ^ 14 * (W * |f|) := by
        apply mul_le_mul_of_nonneg_right hconst (by positivity)

end Squarefree
