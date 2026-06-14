import Squarefree.Lower.Step4Combine
import Squarefree.Lower.UpsilonMag
import Squarefree.Lower.DefectBounds
import Squarefree.Lower.Step4ConfinementAux

/-!
# §5 Step-4 closed-form `r`-derivative `Σ_s'(r)` (writeup 1047–1052)

This file is the §5 Step-4 analogue of `Step4Phase`'s `phiv_hasDerivAt` / `phiv_deriv_lb`, but
for the leading cubic/quartic closed form

  `Σ_closed(d,b₀) = (Xa/d⁵)·((−4 + 10a/d)·(P₁ + P₂/d))`   (= `Lval X a d b₀ v ℓ₁ ℓ₂`),

viewed as a function of `r` through `d = d̃ₐ(r)` (holding `a, b₀, v` fixed, exactly as
`leading_abs_ge` does).  We give:

* `Sigma_closed_hasDerivAt` — the `r`-derivative via the chain rule through `d̃ₐ`
  (mirrors `phiv_hasDerivAt`: `dtilde_r_hasDerivAt`, `.inv`, `.pow`, product rule);
* `Sigma_closed_deriv_lb` — the lower bound `|s|/(C·R) ≤ |Σ_s'(ρ)|` via reverse-triangle
  dominance of the leading monomial `20·Xa·P₁·d̃'/d⁶` over the `10a/d`/`P₂/d` remainders
  (mirrors `phiv_deriv_lb`).  The leading magnitude reuses the `leading_abs_ge` ingredients
  (`|P₁| ≥ |v|³/2`, the `(Xa/d⁵)` prefactor lower bound, `|d̃'| ≍ B`, `B = D/R`).
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

variable {P : Globals} {S : Scale P}

/-- `Σ_closed` and `Lval` are the same expression (argument order differs). -/
theorem Sigma_closed_eq_Lval (X a b₀ v d ℓ₁ ℓ₂ : ℝ) :
    Sigma_closed X a b₀ v d ℓ₁ ℓ₂ = Lval X a d b₀ v ℓ₁ ℓ₂ := rfl

/-- The `d`-derivative of `Σ_closed` as a one-variable function of `d`.  The value is the explicit
expression `D5(X,a,b₀,v,d,ℓ₁,ℓ₂)`; we record it abstractly through this `HasDerivAt`. -/
private theorem sigma_d_hasDerivAt {X a b₀ v ℓ₁ ℓ₂ d : ℝ} (hd : d ≠ 0) :
    HasDerivAt (fun t => Sigma_closed X a b₀ v t ℓ₁ ℓ₂)
      ( X * a *
        ( ((-(10 * a / d ^ 2)) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
            + (-4 + 10 * a / d) * (-(Ptwo b₀ v ℓ₁ ℓ₂ / d ^ 2))) * d⁻¹ ^ 5
          + (-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
              * (-(5 * d⁻¹ ^ 4 * d⁻¹ ^ 2))) ) d := by
  -- u(d) = -4 + 10a/d,  u' = -10a/d²
  have hinvd : HasDerivAt (fun t => t⁻¹) (-(d⁻¹ ^ 2)) d := by
    simpa using hasDerivAt_inv hd
  have hu : HasDerivAt (fun t => -4 + 10 * a * t⁻¹) (10 * a * (-(d⁻¹ ^ 2))) d := by
    have := (hinvd.const_mul (10 * a))
    simpa using (this.const_add (-4 : ℝ))
  -- w(d) = P₁ + P₂/d,  w' = -P₂/d²
  have hw : HasDerivAt (fun t => Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ * t⁻¹)
      (Ptwo b₀ v ℓ₁ ℓ₂ * (-(d⁻¹ ^ 2))) d := by
    have := (hinvd.const_mul (Ptwo b₀ v ℓ₁ ℓ₂))
    simpa using (this.const_add (Pone b₀ v ℓ₁ ℓ₂))
  -- p(d) = (d⁻¹)⁵,  p' = 5(d⁻¹)⁴·(-(d⁻¹)²)
  have hp : HasDerivAt (fun t => (t⁻¹ : ℝ) ^ 5)
      (5 * (d⁻¹) ^ 4 * (-(d⁻¹ ^ 2))) d := by
    have h5 := hinvd.pow 5
    convert h5 using 2
  -- product u·w
  have huw := hu.mul hw
  -- product (u·w)·p
  have huwp := huw.mul hp
  -- constant factor X·a
  have hfull := huwp.const_mul (X * a)
  -- reconcile the function shape and the derivative value
  convert hfull using 1
  · funext t
    simp only [Sigma_closed, div_eq_mul_inv, Pi.mul_apply]
    ring
  · -- the derivative value matches after rewriting `10a/d`, `P₂/d`, `d⁻¹^k` consistently
    simp only [div_eq_mul_inv, Pi.mul_apply]
    ring

/-- **§5 Step-4 closed-form `r`-derivative** (writeup 1047).  The chain rule through `d̃ₐ` gives
the `r`-derivative of `r ↦ Σ_closed(d̃ₐ(r))` as `(dΣ/dd)·d̃ₐ'(r)`.  The leading monomial of the
returned value is `20·Xa·P₁·d̃'/d⁶`. -/
theorem Sigma_closed_hasDerivAt {a b₀ v ℓ₁ ℓ₂ r : ℝ} (ha0 : 0 < a) (hr0 : 0 < r) :
    HasDerivAt (fun s => Sigma_closed P.X a b₀ v (dtilde P.X s a) ℓ₁ ℓ₂)
      ( ( P.X * a *
          ( ((-(10 * a / (dtilde P.X r a) ^ 2))
                * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / (dtilde P.X r a))
              + (-4 + 10 * a / (dtilde P.X r a))
                  * (-(Ptwo b₀ v ℓ₁ ℓ₂ / (dtilde P.X r a) ^ 2)))
              * (dtilde P.X r a)⁻¹ ^ 5
            + (-4 + 10 * a / (dtilde P.X r a))
                * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / (dtilde P.X r a))
                * (-(5 * (dtilde P.X r a)⁻¹ ^ 4 * (dtilde P.X r a)⁻¹ ^ 2))) )
        * deriv (fun s => dtilde P.X s a) r ) r := by
  have hd0 : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  -- inner derivative `d̃ₐ'`
  have hd : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun s => dtilde P.X s a) r) r :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hr0).differentiableAt.hasDerivAt
  -- outer derivative `dΣ/dd` at `d̃ₐ(r)`
  have hg := sigma_d_hasDerivAt (X := P.X) (a := a) (b₀ := b₀) (v := v)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (d := dtilde P.X r a) hd0
  -- chain rule
  exact hg.comp r hd

/-- **§5 Step-4 closed-form derivative lower bound** (writeup 1052, `|Σ_s'(ρ)| ≍ |s|/R`).  In the
large-defect range, the `r`-derivative of `Σ_closed(d̃ₐ(r))` obeys
`|Lval| / (10⁶·R) ≤ |Σ_s'(ρ)|`; with `|Lval| ≥ 1` (`leading_abs_ge`) this is the `1/R` floor that
the MVT interval confinement (`Step4Confine`) needs.  Mirrors `phiv_deriv_lb`: reverse-triangle
dominance of the leading `−5Σ/d` over the `O(a/d)`-smaller correction. -/
theorem Sigma_closed_deriv_lb {a : ℝ} {ℓ₁ ℓ₂ b₀ v r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hdwin : S.D ≤ dtilde P.X r a ∧ dtilde P.X r a ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 55 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hVcut : V₂ P S ≤ |v|) :
    |Lval P.X a (dtilde P.X r a) b₀ v ℓ₁ ℓ₂| / (10 ^ 6 * S.R)
      ≤ |deriv (fun s => Sigma_closed P.X a b₀ v (dtilde P.X s a) ℓ₁ ℓ₂) r| := by
  -- scale positivity
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  -- window facts
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ12R : ℓ₁ < ℓ₂ := hℓ12
  -- `d = d̃ₐ(r)` confined to the dyadic window `D ≤ d ≤ 2D` (supplied by `hdwin`; in the MVT
  -- application the points lie where `Σ_s ≈ s`, forcing this dyadic constraint).
  obtain ⟨hd_lo, hd_hi⟩ := hdwin
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  set d := dtilde P.X r a with hd_def
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  -- regime: Δ²U⁵ ≤ HΩ³ (same chain as in `leading_abs_ge`)
  have hGU5Ω3 : (1 : ℝ) ≤ P.G * P.U ^ 5 * S.Ω ^ 3 := by
    have hU2Ω : P.U ≤ P.U ^ 2 / S.Ω := by
      rw [le_div_iff₀ hΩpos]; nlinarith [hΩU, hUpos.le, hU1]
    have hfactor : P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) = P.G * P.U ^ 5 * S.Ω ^ 3 := by
      field_simp
    have hchain : (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) := by
      calc (1 : ℝ) ≤ P.U := hU1
        _ ≤ P.U ^ 2 / S.Ω := hU2Ω
        _ = 1 * (P.U ^ 2 / S.Ω) := by ring
        _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) :=
            mul_le_mul_of_nonneg_right hband (by positivity)
    rwa [hfactor] at hchain
  have hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 := by
    have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
      (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
    have hstep : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3) ≤ P.H * S.Ω ^ 3 := by
      have heq : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3)
          = (P.G * P.U ^ 10 * S.Δ ^ 2) * S.Ω ^ 3 := by ring
      rw [heq]; exact mul_le_mul_of_nonneg_right hHbig (by positivity)
    have hle : S.Δ ^ 2 * P.U ^ 5 ≤ S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3) := by
      nlinarith [hGU5Ω3, mul_pos (by positivity : (0:ℝ) < S.Δ ^ 2) (by positivity : (0:ℝ) < P.U ^ 5)]
    linarith [hle, hstep]
  have hd2D : d ≤ 2 * S.D := hd_hi
  have hdD : S.D ≤ d := hd_lo
  -- scale identities
  have ha_hi' : a ≤ 11 * (S.Δ * S.Ω) := by have : S.A = S.Δ * S.Ω := rfl; rwa [this] at ha_hi
  have ha_lo' : S.Δ * S.Ω / 5 ≤ a := by have : S.A = S.Δ * S.Ω := rfl; rwa [this] at ha_lo
  -- ===== reverse-triangle ingredients =====
  -- a/d ≤ 1/5  (⟸ 55Ω ≤ H, a ≤ 11A = 11ΔΩ, d ≥ D = HΔ)
  have hdD' : P.H * S.Δ ≤ d := by have : S.D = P.H * S.Δ := rfl; rwa [← this]
  have had : a / d ≤ 1 / 5 := by
    rw [div_le_div_iff₀ hd_pos (by norm_num)]
    have h55 : 55 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by
      have := mul_le_mul_of_nonneg_right hΩH hΔpos.le; nlinarith [this]
    nlinarith [ha_hi', hdD', h55]
  have had0 : 0 ≤ a / d := by positivity
  -- bracket `u = −4 + 10a/d ∈ [−4,−2]`, so `|u| ≥ 2`
  have hbracket : 2 ≤ |(-4 + 10 * a / d)| := by
    have h10ad : 10 * a / d = 10 * (a / d) := by ring
    rw [h10ad, abs_of_nonpos (by nlinarith [had, had0])]
    nlinarith [had, had0]
  -- ===== sharp V₂-dominance:  |P₂|/d ≤ 2T ≤ |P₁+P₂/d| =====
  have hℓ1pos' : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos' hℓ12
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v| :=
    vlo_of_vcut (P := P) (S := S) hℓ1 hℓ12 hℓ2W hb0 hVcut (S.D_half_of_win hdD) hd_pos hG1 hU1 hUbig
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  have hres : |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d
      - 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2| ≤ (1 / 10 ^ 50) * T :=
    psum_resid_le_sharp (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hVcut (S.D_half_of_win hdD) hd_pos hReg
      hG1 hU1 hUbig hDeW
  have hMabs : |3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2| = 3 * T := by
    rw [hTdef, show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
        = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  have hPsum_ge : 2 * T ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| := by
    have htri := abs_sub_abs_le_abs_sub (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2)
      (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
    rw [hMabs, abs_sub_comm] at htri
    linarith [hres, htri]
  have hP2d : |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ 2 * T :=
    ptwo_div_le_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo (S.D_half_of_win hdD) hd_pos
      hReg hG1 hU1 hUbig hDeW
  -- abbreviate the polynomial core `w = P₁ + P₂/d` and the bracket `u`
  set w := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hw_def
  set u := (-4 + 10 * a / d) with hu_def
  have hw_nn : 0 ≤ |w| := abs_nonneg _
  have hu_nn : 0 ≤ |u| := abs_nonneg _
  set K := P.X * a / d ^ 5 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  -- |Σ| = K·|u|·|w|
  have hSabs : |Lval P.X a d b₀ v ℓ₁ ℓ₂| = K * (|u| * |w|) := by
    rw [hK_def, Lval, hu_def, hw_def, abs_mul, abs_mul, abs_of_pos (by positivity)]
  set Sm := |Lval P.X a d b₀ v ℓ₁ ℓ₂| with hSm_def
  have hSm_nn : 0 ≤ Sm := abs_nonneg _
  have hSm_val : Sm = K * (|u| * |w|) := hSabs
  -- ===== |dSig| ≥ 3·Sm/d : the reverse-triangle dominance of `−5Σ/d` =====
  -- abbreviate the d-derivative value Dval
  set Dval : ℝ :=
    P.X * a *
      ( ((-(10 * a / d ^ 2)) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
          + (-4 + 10 * a / d) * (-(Ptwo b₀ v ℓ₁ ℓ₂ / d ^ 2))) * d⁻¹ ^ 5
        + (-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
            * (-(5 * d⁻¹ ^ 4 * d⁻¹ ^ 2))) with hDval_def
  -- the algebraic split  Dval = −5·Ssig/d + K·(u'·w + u·w')
  -- where Ssig = K·u·w (the signed Σ_closed), u' = −10a/d², w' = −P₂/d²
  set Ssig := K * (u * w) with hSsig_def
  set up := -(10 * a / d ^ 2) with hup_def
  set wp := -(Ptwo b₀ v ℓ₁ ℓ₂ / d ^ 2) with hwp_def
  have hDval_split : Dval = -5 * Ssig / d + K * (up * w + u * wp) := by
    rw [hDval_def, hSsig_def, hK_def, hup_def, hwp_def, hu_def, hw_def]
    field_simp
    ring
  -- |Ssig| = Sm
  have hSsig_abs : |Ssig| = Sm := by
    rw [hSsig_def, hSm_val, abs_mul, abs_of_pos hK_pos, abs_mul]
  -- the two pointwise comparisons
  have h10adu : 10 * a / d ≤ |u| := by
    have : 10 * a / d ≤ 2 := by rw [show 10 * a / d = 10 * (a/d) by ring]; nlinarith [had]
    linarith [hbracket]
  have hP2w : |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ |w| := le_trans hP2d hPsum_ge
  clear hres hMabs
  -- correction term 1:  K·|u'|·|w| ≤ K·|u|·|w|/d = Sm/d
  have hup_abs : |up| = 10 * a / d ^ 2 := by
    rw [hup_def, abs_neg, abs_of_pos (by positivity)]
  have hd2_pos : (0:ℝ) < d ^ 2 := by positivity
  have hwp_abs : |wp| = |Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2 := by
    rw [hwp_def, abs_neg, abs_div, abs_of_pos hd2_pos]
  -- (10a/d²)·|w| ≤ |u|·|w|/d
  have hcmp1 : (10 * a / d ^ 2) * |w| ≤ |u| * |w| / d := by
    have hstep : (10 * a / d) * |w| ≤ |u| * |w| := mul_le_mul_of_nonneg_right h10adu hw_nn
    have hL : (10 * a / d ^ 2) * |w| = ((10 * a / d) * |w|) / d := by
      rw [eq_div_iff (ne_of_gt hd_pos)]; field_simp
    rw [hL]
    gcongr
  -- |u|·(|P₂|/d²) ≤ |u|·|w|/d
  have hcmp2 : |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2) ≤ |u| * |w| / d := by
    have hstep : |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d) ≤ |u| * |w| := mul_le_mul_of_nonneg_left hP2w hu_nn
    have hL : |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2) = (|u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d)) / d := by
      rw [eq_div_iff (ne_of_gt hd_pos)]; field_simp
    rw [hL]
    gcongr
  -- bound the correction:  |K·(u'w + uw')| ≤ 2·Sm/d
  have hcorr : |K * (up * w + u * wp)| ≤ 2 * Sm / d := by
    rw [abs_mul, abs_of_pos hK_pos]
    have htri : |up * w + u * wp| ≤ |up| * |w| + |u| * |wp| := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_left htri hK_pos.le) ?_
    rw [hup_abs, hwp_abs]
    -- K·((10a/d²)|w| + |u|(|P₂|/d²)) ≤ K·(|u||w|/d + |u||w|/d) = 2·Sm/d
    have hsum : (10 * a / d ^ 2) * |w| + |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2)
        ≤ |u| * |w| / d + |u| * |w| / d := add_le_add hcmp1 hcmp2
    calc K * ((10 * a / d ^ 2) * |w| + |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2))
        ≤ K * (|u| * |w| / d + |u| * |w| / d) :=
          mul_le_mul_of_nonneg_left hsum hK_pos.le
      _ = 2 * (K * (|u| * |w|)) / d := by ring
      _ = 2 * Sm / d := by rw [← hSm_val]
  -- ===== |Dval| ≥ 3·Sm/d : reverse triangle on Dval = −5Σ/d + correction =====
  have hDlb : 3 * Sm / d ≤ |Dval| := by
    -- |Dval| ≥ |−5Ssig/d| − |correction| = 5Sm/d − |corr| ≥ 5Sm/d − 2Sm/d
    have hmain_abs : |(-5 * Ssig / d)| = 5 * Sm / d := by
      rw [show (-5 * Ssig / d) = -(5 * Ssig / d) by ring, abs_neg, abs_div,
        abs_of_pos hd_pos, abs_mul, show |(5:ℝ)| = 5 by norm_num, hSsig_abs]
    have htriangle : |(-5 * Ssig / d)| ≤ |Dval| + |K * (up * w + u * wp)| := by
      have hM : (-5 * Ssig / d) = Dval - K * (up * w + u * wp) := by rw [hDval_split]; ring
      rw [hM]; exact abs_sub _ _
    rw [hmain_abs] at htriangle
    have harith : 5 * Sm / d - 2 * Sm / d = 3 * Sm / d := by ring
    linarith [htriangle, hcorr, harith]
  -- ===== chain through `d̃ₐ'` =====
  -- |d̃ₐ'(r)| ≥ B/10⁶
  obtain ⟨hd1_lo, _⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  set d1 := deriv (fun s => dtilde P.X s a) r with hd1_def
  have hd1_abs_lo : S.B / 1000000 ≤ |d1| := hd1_lo
  -- the derivative value of `Σ_closed ∘ d̃` is `Dval · d1`
  have hPD := Sigma_closed_hasDerivAt (P := P) (a := a) (b₀ := b₀) (v := v)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r) ha0 hr0
  have hderiv_eq : deriv (fun s => Sigma_closed P.X a b₀ v (dtilde P.X s a) ℓ₁ ℓ₂) r
      = Dval * d1 := by
    rw [hPD.deriv]
  rw [hderiv_eq, abs_mul]
  -- |Dval·d1| ≥ (3Sm/d)·(B/10⁶), and reduce to the target Sm/(10⁶ R)
  have hgoal : Sm / (10 ^ 6 * S.R) ≤ (3 * Sm / d) * (S.B / 1000000) := by
    -- RHS = 3·Sm·B/(d·10⁶);  LHS = Sm/(10⁶·R).  Need 3B/d ≥ 1/R ⟺ d ≤ 3BR = 3D.
    have hBR : S.B * S.R = S.D := by rw [Scale.B_eq_D_div_R]; field_simp
    have hd3BR : d ≤ 3 * (S.B * S.R) := by rw [hBR]; linarith [hd2D, hDpos]
    have hRHS_eq : (3 * Sm / d) * (S.B / 1000000) = 3 * Sm * S.B / (d * 1000000) := by ring
    have hLHS_eq : Sm / (10 ^ 6 * S.R) = Sm / (1000000 * S.R) := by norm_num
    rw [hRHS_eq, hLHS_eq, div_le_div_iff₀ (by positivity) (by positivity)]
    -- Sm·(d·10⁶) ≤ 3·Sm·B·(10⁶·R)  ⟸  Sm·d ≤ 3·Sm·(B·R)
    have hkey : Sm * d ≤ 3 * Sm * (S.B * S.R) := by
      rw [show 3 * Sm * (S.B * S.R) = Sm * (3 * (S.B * S.R)) by ring]
      exact mul_le_mul_of_nonneg_left hd3BR hSm_nn
    nlinarith [hkey, hSm_nn, mul_pos hd_pos (by positivity : (0:ℝ) < 1000000),
      mul_pos hBpos hRpos]
  refine le_trans hgoal ?_
  exact mul_le_mul hDlb hd1_abs_lo (by positivity) (abs_nonneg _)

end Squarefree
