import Squarefree.Lower.Step4Deriv
import Squarefree.Lower.Step4Confine

/-!
# §5 Step-4 `Σ_closed` `d`-smoothing (Blocker B, writeup 1042–1059)

`Sigma_closed_d_smoothing` is the second-difference analogue of `phi_d_replace`: it bridges the
INTEGER witness `d = dStar r` (where `sigma_s_extract_from_witness` lands) to the SMOOTH
`d̃ₐ(r) = dtilde P.X r a` (where `step4_confine_two` lives), holding `a, b₀, v, ℓ₁, ℓ₂` fixed:

```
|Σ_closed(d₂) − Σ_closed(d₁)| ≤ (7·M/D)·|d₂ − d₁|,   M = 10⁸⁵·G⁵U³⁵/Ω⁸,
```

for any two window points `d₁,d₂ ∈ [D,2D]`.

The mechanism is the mean value theorem in `d` (mirroring `step4_confine_two`'s MVT in `r`),
using the derivative UPPER bound `|dΣ/dd| ≤ 7|Σ|/d ≤ 7M/D` (the upper analogue of
`Sigma_closed_deriv_lb`'s `|dΣ/dd| ≥ 3|Σ|/d`, via the SAME identity
`Dval = −5Σ/d + correction`, `|correction| ≤ 2|Σ|/d`), the magnitude cap `|Σ| ≤ M`
(`leading_abs_le`), and the floor `d ≥ D` on the whole `[d₁,d₂]` segment (convex, both endpoints
in `[D,2D]`).

With `|d̃ₐ − dStar| ≤ 10¹²·Δ/(GΩ³)` (the `dtilde_close` witness) and `D = HΔ`, the resulting
slack `δ' = 7·M·10¹²·Δ/(GΩ³·HΔ)` is `≪ UpsT` (the near-integer tolerance), so it is absorbed
and `step4_confine_two` may be applied at the smooth `d̃ₐ` points.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

variable {P : Globals} {S : Scale P}

/-- The `d`-derivative of `Σ_closed` as a one-variable function of `d` (local copy of the
private `sigma_d_hasDerivAt` of `Step4Deriv.lean`, exposing the explicit `Dval` derivative). -/
private theorem sigma_d_hasDerivAt' {X a b₀ v ℓ₁ ℓ₂ d : ℝ} (hd : d ≠ 0) :
    HasDerivAt (fun t => Sigma_closed X a b₀ v t ℓ₁ ℓ₂)
      ( X * a *
        ( ((-(10 * a / d ^ 2)) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
            + (-4 + 10 * a / d) * (-(Ptwo b₀ v ℓ₁ ℓ₂ / d ^ 2))) * d⁻¹ ^ 5
          + (-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
              * (-(5 * d⁻¹ ^ 4 * d⁻¹ ^ 2))) ) d := by
  have hinvd : HasDerivAt (fun t => t⁻¹) (-(d⁻¹ ^ 2)) d := by
    simpa using hasDerivAt_inv hd
  have hu : HasDerivAt (fun t => -4 + 10 * a * t⁻¹) (10 * a * (-(d⁻¹ ^ 2))) d := by
    have := (hinvd.const_mul (10 * a))
    simpa using (this.const_add (-4 : ℝ))
  have hw : HasDerivAt (fun t => Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ * t⁻¹)
      (Ptwo b₀ v ℓ₁ ℓ₂ * (-(d⁻¹ ^ 2))) d := by
    have := (hinvd.const_mul (Ptwo b₀ v ℓ₁ ℓ₂))
    simpa using (this.const_add (Pone b₀ v ℓ₁ ℓ₂))
  have hp : HasDerivAt (fun t => (t⁻¹ : ℝ) ^ 5)
      (5 * (d⁻¹) ^ 4 * (-(d⁻¹ ^ 2))) d := by
    have h5 := hinvd.pow 5
    convert h5 using 2
  have huw := hu.mul hw
  have huwp := huw.mul hp
  have hfull := huwp.const_mul (X * a)
  convert hfull using 1
  · funext t
    simp only [Sigma_closed, div_eq_mul_inv, Pi.mul_apply]
    ring
  · simp only [div_eq_mul_inv, Pi.mul_apply]
    ring

/-- **§5 Step-4 `Σ_closed` `d`-derivative UPPER bound** (writeup 1047, upper analogue of
`Sigma_closed_deriv_lb`).  At a window point `d ∈ [D,2D]` in the large-defect range, the pure-`d`
derivative of `Σ_closed` obeys `|dΣ/dd| ≤ 7·|Σ|/d`.  Same `Dval = −5Σ/d + correction`,
`|correction| ≤ 2|Σ|/d` split as the lower bound, but assembled by the (forward) triangle
inequality `|Dval| ≤ 5|Σ|/d + 2|Σ|/d`. -/
private theorem sigma_d_deriv_ub {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D * (1 - 1/10 ^ 9) ≤ d ∧ d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 60 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hVcut : V₂ P S ≤ |v|) :
    |deriv (fun t => Sigma_closed P.X a b₀ v t ℓ₁ ℓ₂) d|
      ≤ 167 / 24 * |Lval P.X a d b₀ v ℓ₁ ℓ₂| / d := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  obtain ⟨hd_lo, hd_hi⟩ := hdwin
  have hd_pos : 0 < d := S.D_pos_of_eps hd_lo
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  -- regime: Δ²U⁵ ≤ HΩ³
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
  -- scale identities (same as `Sigma_closed_deriv_lb`)
  have ha_hi' : a ≤ 11 * (S.Δ * S.Ω) := by have : S.A = S.Δ * S.Ω := rfl; rwa [this] at ha_hi
  have hdD' : P.H * S.Δ * (1 - 1/10 ^ 9) ≤ d := by
    have : S.D = P.H * S.Δ := rfl; rwa [← this]
  -- a/d ≤ 23/120
  have had : a / d ≤ 23 / 120 := by
    rw [div_le_div_iff₀ hd_pos (by norm_num)]
    have h60 : 60 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by
      have := mul_le_mul_of_nonneg_right hΩH hΔpos.le; nlinarith [this]
    nlinarith [ha_hi', hdD', h60]
  have had0 : 0 ≤ a / d := by positivity
  -- bracket
  have hbracket : 2 ≤ |(-4 + 10 * a / d)| := by
    have h10ad : 10 * a / d = 10 * (a / d) := by ring
    rw [h10ad, abs_of_nonpos (by nlinarith [had, had0])]
    nlinarith [had, had0]
  -- ===== sharp V₂-dominance:  |P₂|/d ≤ 2T ≤ |P₁+P₂/d| =====
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v| :=
    vlo_of_vcut (P := P) (S := S) hℓ1 hℓ12 hℓ2W hb0 hVcut (S.D_half_of_eps hd_lo) hd_pos hG1 hU1 hUbig
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  have hres : |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d
      - 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2| ≤ (1 / 10 ^ 50) * T :=
    psum_resid_le_sharp (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hVcut (S.D_half_of_eps hd_lo) hd_pos hReg
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
    ptwo_div_le_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo (S.D_half_of_eps hd_lo)
      hd_pos hReg hG1 hU1 hUbig hDeW
  set w := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hw_def
  set u := (-4 + 10 * a / d) with hu_def
  have hw_nn : 0 ≤ |w| := abs_nonneg _
  have hu_nn : 0 ≤ |u| := abs_nonneg _
  set K := P.X * a / d ^ 5 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  have hSabs : |Lval P.X a d b₀ v ℓ₁ ℓ₂| = K * (|u| * |w|) := by
    rw [hK_def, Lval, hu_def, hw_def, abs_mul, abs_mul, abs_of_pos (by positivity)]
  set Sm := |Lval P.X a d b₀ v ℓ₁ ℓ₂| with hSm_def
  have hSm_nn : 0 ≤ Sm := abs_nonneg _
  have hSm_val : Sm = K * (|u| * |w|) := hSabs
  -- the d-derivative value Dval
  set Dval : ℝ :=
    P.X * a *
      ( ((-(10 * a / d ^ 2)) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
          + (-4 + 10 * a / d) * (-(Ptwo b₀ v ℓ₁ ℓ₂ / d ^ 2))) * d⁻¹ ^ 5
        + (-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d)
            * (-(5 * d⁻¹ ^ 4 * d⁻¹ ^ 2))) with hDval_def
  set Ssig := K * (u * w) with hSsig_def
  set up := -(10 * a / d ^ 2) with hup_def
  set wp := -(Ptwo b₀ v ℓ₁ ℓ₂ / d ^ 2) with hwp_def
  have hDval_split : Dval = -5 * Ssig / d + K * (up * w + u * wp) := by
    rw [hDval_def, hSsig_def, hK_def, hup_def, hwp_def, hu_def, hw_def]
    field_simp
    ring
  have hSsig_abs : |Ssig| = Sm := by
    rw [hSsig_def, hSm_val, abs_mul, abs_of_pos hK_pos, abs_mul]
  have h10adu : 10 * a / d ≤ 23 / 24 * |u| := by
    have h1' : 10 * a / d ≤ 23 / 12 := by
      rw [show 10 * a / d = 10 * (a/d) by ring]; nlinarith [had]
    nlinarith [hbracket, h1']
  have hP2w : |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ |w| := le_trans hP2d hPsum_ge
  clear hres hMabs
  have hup_abs : |up| = 10 * a / d ^ 2 := by
    rw [hup_def, abs_neg, abs_of_pos (by positivity)]
  have hd2_pos : (0:ℝ) < d ^ 2 := by positivity
  have hwp_abs : |wp| = |Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2 := by
    rw [hwp_def, abs_neg, abs_div, abs_of_pos hd2_pos]
  have hcmp1 : (10 * a / d ^ 2) * |w| ≤ 23 / 24 * (|u| * |w| / d) := by
    have hstep : (10 * a / d) * |w| ≤ 23 / 24 * |u| * |w| := by
      nlinarith [mul_le_mul_of_nonneg_right h10adu hw_nn]
    have hL : (10 * a / d ^ 2) * |w| = ((10 * a / d) * |w|) / d := by
      rw [eq_div_iff (ne_of_gt hd_pos)]; field_simp
    rw [hL, show 23 / 24 * (|u| * |w| / d) = (23 / 24 * |u| * |w|) / d by ring]
    gcongr
  have hcmp2 : |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2) ≤ |u| * |w| / d := by
    have hstep : |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d) ≤ |u| * |w| := mul_le_mul_of_nonneg_left hP2w hu_nn
    have hL : |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2) = (|u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d)) / d := by
      rw [eq_div_iff (ne_of_gt hd_pos)]; field_simp
    rw [hL]; gcongr
  have hcorr : |K * (up * w + u * wp)| ≤ 47 / 24 * Sm / d := by
    rw [abs_mul, abs_of_pos hK_pos]
    have htri : |up * w + u * wp| ≤ |up| * |w| + |u| * |wp| := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_left htri hK_pos.le) ?_
    rw [hup_abs, hwp_abs]
    have hsum : (10 * a / d ^ 2) * |w| + |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2)
        ≤ 23 / 24 * (|u| * |w| / d) + |u| * |w| / d := add_le_add hcmp1 hcmp2
    calc K * ((10 * a / d ^ 2) * |w| + |u| * (|Ptwo b₀ v ℓ₁ ℓ₂| / d ^ 2))
        ≤ K * (23 / 24 * (|u| * |w| / d) + |u| * |w| / d) :=
          mul_le_mul_of_nonneg_left hsum hK_pos.le
      _ = 47 / 24 * (K * (|u| * |w|)) / d := by ring
      _ = 47 / 24 * Sm / d := by rw [← hSm_val]
  -- ===== |Dval| ≤ 7·Sm/d : forward triangle on Dval = −5Σ/d + correction =====
  have hDub : |Dval| ≤ 167 / 24 * Sm / d := by
    have hmain_abs : |(-5 * Ssig / d)| = 5 * Sm / d := by
      rw [show (-5 * Ssig / d) = -(5 * Ssig / d) by ring, abs_neg, abs_div,
        abs_of_pos hd_pos, abs_mul, show |(5:ℝ)| = 5 by norm_num, hSsig_abs]
    have htriangle : |Dval| ≤ |(-5 * Ssig / d)| + |K * (up * w + u * wp)| := by
      have hM : Dval = (-5 * Ssig / d) + K * (up * w + u * wp) := hDval_split
      rw [hM]; exact abs_add_le _ _
    rw [hmain_abs] at htriangle
    have hsum_eq : 5 * Sm / d + 47 / 24 * Sm / d = 167 / 24 * Sm / d := by ring
    linarith [htriangle, hcorr, hsum_eq]
  -- the deriv equals Dval
  have hPD := sigma_d_hasDerivAt' (X := P.X) (a := a) (b₀ := b₀) (v := v)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (d := d) hd_ne
  have hderiv_eq : deriv (fun t => Sigma_closed P.X a b₀ v t ℓ₁ ℓ₂) d = Dval := by
    rw [hPD.deriv]
  rw [hderiv_eq]
  exact hDub

/-- **§5 Step-4 `Σ_closed` `d`-smoothing** (Blocker B, writeup 1042–1059).  For any two window
points `d₁,d₂ ∈ [D,2D]` (in the large-defect range, `a,b₀,v,ℓ₁,ℓ₂` fixed), the closed form is
Lipschitz in `d` with constant `7·M/D`:

```
|Σ_closed(d₂) − Σ_closed(d₁)| ≤ (7·M/D)·|d₂ − d₁|,   M = 10⁸⁵·G⁵U³⁵/Ω⁸.
```

MVT in `d` (`exists_hasDerivAt_eq_slope`) over the convex segment `[min d₁ d₂, max d₁ d₂] ⊆ [D,2D]`,
the derivative cap `|dΣ/dd| ≤ 7|Σ|/d ≤ 7M/D` (`sigma_d_deriv_ub` + `leading_abs_le` + `d ≥ D`). -/
theorem Sigma_closed_d_smoothing {a : ℝ} {ℓ₁ ℓ₂ b₀ v d₁ d₂ : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin1 : S.D * (1 - 1/10 ^ 9) ≤ d₁ ∧ d₁ ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hdwin2 : S.D * (1 - 1/10 ^ 9) ≤ d₂ ∧ d₂ ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hAD : 10 * S.A ≤ S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 60 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hVcut : V₂ P S ≤ |v|) :
    |Sigma_closed P.X a b₀ v d₂ ℓ₁ ℓ₂ - Sigma_closed P.X a b₀ v d₁ ℓ₁ ℓ₂|
      ≤ 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D * |d₂ - d₁| := by
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  set M : ℝ := 10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) with hM_def
  set L : ℝ := 7 * M / S.D with hL_def
  have hL_nn : 0 ≤ L := by rw [hL_def, hM_def]; positivity
  -- the smooth curve and its uniform Lipschitz constant `L` on the window `[D,2D]`
  set Φ : ℝ → ℝ := fun t => Sigma_closed P.X a b₀ v t ℓ₁ ℓ₂ with hΦ_def
  -- the convex window set
  set I : Set ℝ := Set.Icc (S.D * (1 - 1/10 ^ 9)) (2 * S.D * (1 + 1/10 ^ 9)) with hI_def
  have hconvex : Convex ℝ I := convex_Icc _ _
  have hd1I : d₁ ∈ I := ⟨hdwin1.1, hdwin1.2⟩
  have hd2I : d₂ ∈ I := ⟨hdwin2.1, hdwin2.2⟩
  -- per-point derivative bound `|Φ'(t)| ≤ L` on the window
  have hderiv_bd : ∀ t ∈ I, ‖deriv Φ t‖ ≤ L := by
    intro t ht
    obtain ⟨htlo, hthi⟩ := ht
    have htpos : 0 < t := S.D_pos_of_eps htlo
    have hub := sigma_d_deriv_ub (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      (b₀ := b₀) (v := v) (d := t) ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W ⟨htlo, hthi⟩
      hb0 hb0lo hv h1 hband hG1 hU1 hΩU hUbig hΩH hDeW hVcut
    have hMbd := leading_abs_le (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      (b₀ := b₀) (v := v) (d := t) hAD ha0 ha_lo ha_hi (lt_of_lt_of_le one_pos hℓ1) hℓ12 hℓ2W
      ⟨htlo, hthi⟩ hb0 hv h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
    -- `|Φ'(t)| ≤ 7|Lval|/t ≤ 7M/D = L`
    rw [Real.norm_eq_abs]
    refine le_trans hub ?_
    rw [hL_def]
    have hLval_nn : 0 ≤ |Lval P.X a t b₀ v ℓ₁ ℓ₂| := abs_nonneg _
    -- (167/24)·|Lval|/t ≤ 7·M/D  since |Lval| ≤ M, t ≥ D(1−ε), 167/24 ≤ 7(1−ε)
    rw [div_le_div_iff₀ htpos hDpos]
    have hM_nn : (0:ℝ) ≤ M := by rw [hM_def]; positivity
    have h1' : 167 / 24 * |Lval P.X a t b₀ v ℓ₁ ℓ₂| * S.D ≤ 167 / 24 * M * S.D :=
      mul_le_mul_of_nonneg_right (by linarith [hMbd]) hDpos.le
    have h2' : M * (S.D * (1 - 1/10 ^ 9)) ≤ M * t :=
      mul_le_mul_of_nonneg_left htlo hM_nn
    nlinarith [h1', h2', mul_nonneg hM_nn hDpos.le]
  -- differentiability of `Φ` on `I` (pure-`d` HasDerivAt at every window point, `d > 0`)
  have hdiff : ∀ t ∈ I, HasDerivAt Φ (deriv Φ t) t := by
    intro t ht
    have htpos : 0 < t := S.D_pos_of_eps ht.1
    have hPD := sigma_d_hasDerivAt' (X := P.X) (a := a) (b₀ := b₀) (v := v)
      (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (d := t) (ne_of_gt htpos)
    exact hPD.deriv ▸ hPD
  have hdiffOn : DifferentiableOn ℝ Φ I :=
    fun t ht => (hdiff t ht).differentiableAt.differentiableWithinAt
  -- mathlib's convex MVT: `‖Φ d₂ − Φ d₁‖ ≤ L · ‖d₂ − d₁‖`
  have hMVT := hconvex.norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hdiff t ht).differentiableAt) hderiv_bd hd2I hd1I
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hMVT
  rw [abs_sub_comm (Φ d₁) (Φ d₂), abs_sub_comm d₁ d₂] at hMVT
  -- reconcile `L · |d₂ − d₁|` with the target
  calc |Sigma_closed P.X a b₀ v d₂ ℓ₁ ℓ₂ - Sigma_closed P.X a b₀ v d₁ ℓ₁ ℓ₂|
      = |Φ d₂ - Φ d₁| := by rw [hΦ_def]
    _ ≤ L * |d₂ - d₁| := hMVT
    _ = 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D * |d₂ - d₁| := by
        rw [hL_def, hM_def]

end Squarefree
