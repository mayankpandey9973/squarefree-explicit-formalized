import Squarefree.Lower.Sec7RaResidual
import Squarefree.Lower.Sec7DtildeWide
import Squarefree.Bracket.Sec7FInverse

/-!
# §7 residual composition helpers

Reusable composition estimates for the `f₃` residual route.
-/

open Classical Filter Real
open scoped Topology

namespace Squarefree

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-- The one-variable `f₃` residual after subtracting the square-root principal term. -/
noncomputable def sec7_ra_rho3Fun (X a j : ℝ) : ℝ → ℝ :=
  fun d => dBreve X a (Ffun X a d + j) - Real.sqrt (d * (d + a))

/-- Normalized `d/D` target where the shifted inverse branch stays in the §7 `t` window. -/
noncomputable def sec7_ra_rho3Target (P : Globals) (S : Scale P) (a : ℝ) : Set ℝ :=
  Set.Icc (dBreve P.X a (300 * S.F) / S.D) (dBreve P.X a (S.F / 500) / S.D)

/-- `dtilde` is smooth in the `r` variable away from `r = 0`. -/
theorem sec7_ra_dtilde_r_contDiffAt {n : WithTop ℕ∞} {X r a : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ n (fun y => dtilde X y a) r := by
  have hinner_arg : ContDiffAt ℝ n (fun y : ℝ => X * a ^ 3 / y) r := by
    exact (contDiffAt_const (c := X * a ^ 3)).div contDiffAt_id (ne_of_gt hr)
  have hinner : ContDiffAt ℝ n (fun y : ℝ => Real.sqrt (X * a ^ 3 / y)) r := by
    refine ContDiffAt.sqrt hinner_arg ?_
    exact ne_of_gt (by positivity : 0 < X * a ^ 3 / r)
  have hrad : ContDiffAt ℝ n
      (fun y : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / y)) r := by
    fun_prop (disch := assumption)
  have houter : ContDiffAt ℝ n
      (fun y : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / y))) r := by
    refine ContDiffAt.sqrt hrad ?_
    have : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have : ContDiffAt ℝ n
      (fun y : ℝ => (-a + Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / y))) / 2) r := by
    fun_prop (disch := assumption)
  simpa [dtilde] using this

theorem sec7_ra_F_pos {P : Globals} (S : Scale P) : 0 < S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.F
  positivity

theorem sec7_ra_R3X_div_A5_eq_F4 {P : Globals} (S : Scale P) :
    S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hG := P.G_pos
  rw [Scale.R, Scale.A, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

theorem sec7_ra_ftil_F_factor {P : Globals} (S : Scale P) :
    P.H / S.A ^ 2 * (S.R * S.Δ) = S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.A Scale.R Scale.F
  field_simp

theorem sec7_ra_R_mono_nat {P : Globals} (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
  rw [OnStripAux.R_mono P S, Real.rpow_one,
    show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]]

theorem sec7_ra_le_of_fourth {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  exact le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hb h

theorem sec7_ra_Ffun_strictAntiOn_pos {X a : ℝ} (hX : 0 < X) (ha : 0 < a) :
    StrictAntiOn (fun d => Ffun X a d) (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro d hd
    have hd0 : 0 < d := by simpa using hd
    exact (Ffun_contDiffAt4 (X := X) (a := a) (d := d)
      (ne_of_gt hd0) (by positivity)).continuousAt.continuousWithinAt
  · intro d hd
    have hd0 : 0 < d := by simpa using hd
    have hda : d + a ≠ 0 := by positivity
    rw [Ffun_deriv_d X a d (ne_of_gt hd0) hda]
    rw [Ffun_deriv1_factor X a d (ne_of_gt hd0) hda]
    have hnum : 0 < 2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by positivity
    have hden : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
    rw [show -2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
          (d ^ 3 * (d + a) ^ 3)
        = -(2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
          (d ^ 3 * (d + a) ^ 3)) by ring]
    exact neg_neg_of_pos (div_pos hnum hden)

theorem sec7_ra_F_large_const {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    (10:ℝ) ^ 100 * (sec7_cJ + 1) ≤ S.F := by
  have hF : 0 < S.F := sec7_ra_F_pos S
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hΩ : 0 < S.Ω := S.Ω_pos
  have hC : 0 < sec7_envC2 := sec7_envC2_pos
  have hn6 : sec7_envC2 * S.Ω ^ 4 ≤ P.H * S.x := by
    have hW30 : (1:ℝ) ≤ W ^ 30 := one_le_pow₀ hW
    have h0 : 0 ≤ sec7_envC2 * S.Ω ^ 4 :=
      mul_nonneg hC.le (pow_nonneg hΩ.le 4)
    calc
      sec7_envC2 * S.Ω ^ 4 ≤ sec7_envC2 * S.Ω ^ 4 * W ^ 30 :=
        le_mul_of_one_le_right h0 hW30
      _ = sec7_envC2 * (W ^ 30 * S.Ω ^ 4) := by ring
      _ ≤ P.H * S.x := Env.n6
  have hn6div : sec7_envC2 ≤ P.H * S.x / S.Ω ^ 4 := by
    rw [le_div_iff₀ (by positivity : 0 < S.Ω ^ 4)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hn6
  have hn7 : sec7_envC2 ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := by
    have hW54 : (1:ℝ) ≤ W ^ 54 := one_le_pow₀ hW
    have h0 : 0 ≤ sec7_envC2 := hC.le
    calc
      sec7_envC2 ≤ sec7_envC2 * W ^ 54 :=
        le_mul_of_one_le_right h0 hW54
      _ ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := Env.n7
  have hF4 : sec7_envC2 ^ 4 ≤ S.F ^ 4 := by
    calc
      sec7_envC2 ^ 4 = sec7_envC2 ^ 3 * sec7_envC2 := by ring
      _ ≤ (P.H * S.x / S.Ω ^ 4) ^ 3 *
          (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) := by
            exact mul_le_mul (pow_le_pow_left₀ hC.le hn6div 3) hn7
              hC.le
              (pow_nonneg
                (div_nonneg (mul_nonneg P.H_pos.le (OnStripAux.x_pos P S).le)
                  (pow_nonneg hΩ.le 4)) 3)
      _ = S.F ^ 4 := by
            rw [Scale.F_eq_H_x_G_Ω]
            field_simp [hΩ.ne']
  have hK0 : 0 ≤ (10:ℝ) ^ 100 * (sec7_cJ + 1) := by
    have := sec7_cJ_pos
    positivity
  have hKleC : (10:ℝ) ^ 100 * (sec7_cJ + 1) ≤ sec7_envC2 := by
    norm_num [sec7_cJ, sec7_envC2]
  have hK4 : ((10:ℝ) ^ 100 * (sec7_cJ + 1)) ^ 4 ≤ S.F ^ 4 :=
    le_trans (pow_le_pow_left₀ hK0 hKleC 4) hF4
  exact sec7_ra_le_of_fourth hK0 hF.le hK4

theorem sec7_ra_HA2_large {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    (10:ℝ) ^ 100 * sec7_cJ * (P.H / S.A ^ 2) ≤ S.F := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hlog0 : 0 ≤ Real.log P.X := Real.log_nonneg hsd.hX
  have hlog1 : (1:ℝ) ≤ 1 + Real.log P.X := by linarith
  have hR : 0 < S.R := sec7_R_pos S
  have hΔ : 0 < S.Δ := S.Δ_pos
  have hΩ : 0 < S.Ω := S.Ω_pos
  have hA : 0 < S.A := by
    unfold Scale.A
    positivity
  have hHA : 0 ≤ P.H / S.A ^ 2 := div_nonneg P.H_pos.le (sq_nonneg S.A)
  have hRlarge : sec7_envC ≤ S.R := by
    calc
      sec7_envC ≤ sec7_envC * W ^ 8 := by
        exact le_mul_of_one_le_right sec7_envC_pos.le (one_le_pow₀ hW)
      _ ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 8)) hlog1
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := Env.tc4
      _ = S.R := sec7_ra_R_mono_nat S
  have hΔlarge_sq : sec7_envC ≤ S.Δ ^ 2 := by
    have htc9x : sec7_envC * S.x ≤ P.H := by
      have hW16 : (1:ℝ) ≤ W ^ 16 := one_le_pow₀ hW
      have hL2 : (1:ℝ) ≤ (1 + Real.log P.X) ^ 2 := by
        have hs := (sq_le_sq₀ zero_le_one
          (by linarith : 0 ≤ 1 + Real.log P.X)).mpr hlog1
        simpa using hs
      calc
        sec7_envC * S.x ≤ sec7_envC * (W ^ 16 * S.x) := by
          have hxW : S.x ≤ W ^ 16 * S.x :=
            le_mul_of_one_le_left (OnStripAux.x_pos P S).le hW16
          exact mul_le_mul_of_nonneg_left hxW sec7_envC_pos.le
        _ ≤ sec7_envC * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2 := by
          exact le_mul_of_one_le_right
            (mul_nonneg sec7_envC_pos.le
              (mul_nonneg (pow_nonneg hW0 16) (OnStripAux.x_pos P S).le)) hL2
        _ ≤ P.H := Env.tc9
    have hmul : sec7_envC * P.H ≤ P.H * S.Δ ^ 2 := by
      have htc9x' : sec7_envC * (P.H / S.Δ ^ 2) ≤ P.H := by
        simpa [Scale.x] using htc9x
      have hstep := mul_le_mul_of_nonneg_right htc9x' (pow_nonneg hΔ.le 2)
      calc
        sec7_envC * P.H = sec7_envC * (P.H / S.Δ ^ 2) * S.Δ ^ 2 := by
          field_simp [hΔ.ne']
        _ ≤ P.H * S.Δ ^ 2 := hstep
    exact le_of_mul_le_mul_left (by simpa [mul_comm] using hmul) P.H_pos
  have hΔlarge : 1 ≤ S.Δ := by
    have h1 : (1:ℝ) ≤ S.Δ ^ 2 := le_trans (by norm_num [sec7_envC]) hΔlarge_sq
    exact (sq_le_sq₀ zero_le_one hΔ.le).mp (by simpa using h1)
  have hRDlarge : (10:ℝ) ^ 100 * sec7_cJ ≤ S.R * S.Δ := by
    calc
      (10:ℝ) ^ 100 * sec7_cJ ≤ sec7_envC := by
        norm_num [sec7_cJ, sec7_envC]
      _ ≤ S.R := hRlarge
      _ ≤ S.R * S.Δ := by
        exact le_mul_of_one_le_right hR.le hΔlarge
  calc
    (10:ℝ) ^ 100 * sec7_cJ * (P.H / S.A ^ 2)
        ≤ (S.R * S.Δ) * (P.H / S.A ^ 2) := by
          exact mul_le_mul_of_nonneg_right hRDlarge hHA
    _ = S.F := by
          rw [← sec7_ra_ftil_F_factor S]
          ring

theorem sec7_ra_shift_error_bound_zero {P : Globals} {S : Scale P} {W : ℝ}
    {j : ℤ} (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) (hj : sec7_jBand P S j) :
    |(j : ℝ)| ≤ S.F / 1000 := by
  have hF : 0 < S.F := sec7_ra_F_pos S
  have hpow : (0:ℝ) < (10:ℝ) ^ 100 := by positivity
  have hlarge0 := sec7_ra_F_large_const (P := P) (S := S) (W := W) Env hW
  have hlargeHA := sec7_ra_HA2_large (P := P) (S := S) (W := W) Env hW c₀ Cu hsd
  have hsmall0 : sec7_cJ + 1 ≤ S.F / (10:ℝ) ^ 100 := by
    rw [le_div_iff₀ hpow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlarge0
  have hsmallJ : sec7_cJ ≤ S.F / (10:ℝ) ^ 100 := by
    have hJle : sec7_cJ ≤ sec7_cJ + 1 := by linarith
    exact le_trans hJle hsmall0
  have hsmallHA : sec7_cJ * (P.H / S.A ^ 2) ≤ S.F / (10:ℝ) ^ 100 := by
    rw [le_div_iff₀ hpow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlargeHA
  have hj_abs : |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := by
    rw [← Int.cast_abs]
    simpa [sec7_jBand] using hj
  have hj_split : |(j : ℝ)| ≤ sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := by
    calc
      |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := hj_abs
      _ = sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := by ring
  have hc : (2:ℝ) / (10:ℝ) ^ 100 ≤ 1 / 1000 := by norm_num
  calc
    |(j : ℝ)| ≤ sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := hj_split
    _ ≤ S.F / (10:ℝ) ^ 100 + S.F / (10:ℝ) ^ 100 := add_le_add hsmallJ hsmallHA
    _ ≤ S.F / 1000 := by nlinarith

theorem sec7_ra_X_tenth_large {P : Globals}
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) :
    (10 : ℝ) ^ 60 ≤ P.X ^ (1 / 10 : ℝ) := by
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16777216) hX24 10
  calc
    (10 : ℝ) ^ 60 ≤ (16777216 : ℝ) ^ 10 := by norm_num
    _ ≤ (P.X ^ (1 / 100 : ℝ)) ^ 10 := hpow
    _ = P.X ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_natCast (P.X ^ (1 / 100 : ℝ)) 10,
        ← Real.rpow_mul P.X_pos.le]
      congr 1
      norm_num

theorem sec7_ra_X_tenth_split {P : Globals} :
    P.X ^ (1 / 10 : ℝ) = P.G ^ (1 / 10 : ℝ) * P.H ^ (1 / 2 : ℝ) := by
  have hG : 0 ≤ P.G := P.G_pos.le
  have hH : 0 ≤ P.H ^ 5 := pow_nonneg P.H_pos.le 5
  rw [P.X_eq_G_mul_H_pow_five]
  rw [Real.mul_rpow hG hH]
  rw [show P.H ^ 5 = P.H ^ (5 : ℕ) by rfl]
  rw [← Real.rpow_natCast P.H 5, ← Real.rpow_mul P.H_pos.le]
  congr 1
  norm_num

theorem sec7_ra_GHΩx_large {P : Globals} {S : Scale P} {c₀ Cu : ℝ}
    (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) :
    (10 : ℝ) ^ 60 ≤ P.G * P.H * S.Ω * S.x := by
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1 / 100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hbud' := hbud
  unfold OnStripAux.Budget at hbud'
  have hmono :
      (1 : ℝ) < P.H ^ (1 / 2 : ℝ) * S.x ^ (1 : ℝ) *
          P.G ^ (9 / 10 : ℝ) * S.Ω ^ (1 : ℝ) := by
    exact OnStripAux.one_lt_mono P S c₀ Cu hsd hXgt
      (1 / 2 : ℝ) (1 : ℝ) (9 / 10 : ℝ) (1 : ℝ)
      (by
        unfold OnStripAux.ratioExp
        norm_num
        nlinarith [hbud', hg0, hu0.le, hsd.hCu])
  have hprod :
      P.X ^ (1 / 10 : ℝ) *
          (P.H ^ (1 / 2 : ℝ) * S.x ^ (1 : ℝ) *
            P.G ^ (9 / 10 : ℝ) * S.Ω ^ (1 : ℝ))
        = P.G * P.H * S.Ω * S.x := by
    rw [sec7_ra_X_tenth_split, Real.rpow_one, Real.rpow_one]
    rw [show P.G ^ (1 / 10 : ℝ) * P.H ^ (1 / 2 : ℝ) *
          (P.H ^ (1 / 2 : ℝ) * S.x * P.G ^ (9 / 10 : ℝ) * S.Ω)
        = (P.G ^ (1 / 10 : ℝ) * P.G ^ (9 / 10 : ℝ)) *
            (P.H ^ (1 / 2 : ℝ) * P.H ^ (1 / 2 : ℝ)) * S.Ω * S.x by ring]
    rw [← Real.rpow_add P.G_pos, ← Real.rpow_add P.H_pos]
    norm_num
  have hlt :
      P.X ^ (1 / 10 : ℝ) < P.G * P.H * S.Ω * S.x := by
    have hx10pos : 0 < P.X ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos P.X_pos _
    have hmul := mul_lt_mul_of_pos_left hmono hx10pos
    calc
      P.X ^ (1 / 10 : ℝ)
          < P.X ^ (1 / 10 : ℝ) *
              (P.H ^ (1 / 2 : ℝ) * S.x * P.G ^ (9 / 10 : ℝ) * S.Ω) := by
            simpa [Real.rpow_one] using hmul
      _ = P.G * P.H * S.Ω * S.x := by
            simpa [Real.rpow_one] using hprod
  exact le_trans (sec7_ra_X_tenth_large (P := P) hX24) (le_of_lt hlt)

theorem sec7_ra_GHΩ3_large {P : Globals} {S : Scale P} {c₀ Cu : ℝ}
    (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) :
    (10 : ℝ) ^ 60 ≤ P.G * P.H * S.Ω ^ 3 := by
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1 / 100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hbud' := hbud
  unfold OnStripAux.Budget at hbud'
  have hmono :
      (1 : ℝ) < P.H ^ (1 / 2 : ℝ) * S.x ^ (0 : ℝ) *
          P.G ^ (9 / 10 : ℝ) * S.Ω ^ (3 : ℝ) := by
    exact OnStripAux.one_lt_mono P S c₀ Cu hsd hXgt
      (1 / 2 : ℝ) (0 : ℝ) (9 / 10 : ℝ) (3 : ℝ)
      (by
        unfold OnStripAux.ratioExp
        norm_num
        nlinarith [hbud', hg0, hu0.le, hsd.hCu])
  have hΩ3 : S.Ω ^ (3 : ℝ) = S.Ω ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hprod :
      P.X ^ (1 / 10 : ℝ) *
          (P.H ^ (1 / 2 : ℝ) * S.x ^ (0 : ℝ) *
            P.G ^ (9 / 10 : ℝ) * S.Ω ^ (3 : ℝ))
        = P.G * P.H * S.Ω ^ 3 := by
    rw [sec7_ra_X_tenth_split, Real.rpow_zero, hΩ3]
    rw [show P.G ^ (1 / 10 : ℝ) * P.H ^ (1 / 2 : ℝ) *
          (P.H ^ (1 / 2 : ℝ) * 1 * P.G ^ (9 / 10 : ℝ) * S.Ω ^ 3)
        = (P.G ^ (1 / 10 : ℝ) * P.G ^ (9 / 10 : ℝ)) *
            (P.H ^ (1 / 2 : ℝ) * P.H ^ (1 / 2 : ℝ)) * S.Ω ^ 3 by ring]
    rw [← Real.rpow_add P.G_pos, ← Real.rpow_add P.H_pos]
    norm_num
  have hlt :
      P.X ^ (1 / 10 : ℝ) < P.G * P.H * S.Ω ^ 3 := by
    have hx10pos : 0 < P.X ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos P.X_pos _
    have hmul := mul_lt_mul_of_pos_left hmono hx10pos
    calc
      P.X ^ (1 / 10 : ℝ)
          < P.X ^ (1 / 10 : ℝ) *
              (P.H ^ (1 / 2 : ℝ) * S.x ^ (0 : ℝ) *
                P.G ^ (9 / 10 : ℝ) * S.Ω ^ (3 : ℝ)) := by
            simpa using hmul
      _ = P.G * P.H * S.Ω ^ 3 := hprod
  exact le_trans (sec7_ra_X_tenth_large (P := P) hX24) (le_of_lt hlt)

theorem sec7_ra_rho3Target_uniqueDiffOn {P : Globals} {S : Scale P} {a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) :
    UniqueDiffOn ℝ (sec7_ra_rho3Target P S a) := by
  have ha0 : 0 < a := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    linarith
  have hFpos : 0 < S.F := sec7_ra_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := 300 * S.F)
      hAD ha_lo ha_hi ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := S.F / 500)
      hAD ha_lo ha_hi ht_lo
  set q_hi : ℝ := dBreve P.X a (300 * S.F)
  set q_lo : ℝ := dBreve P.X a (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hq_order : q_hi < q_lo := by
    by_contra hnot
    have hle : q_lo ≤ q_hi := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hanti := sec7_ra_Ffun_strictAntiOn_pos (X := P.X) (a := a) P.X_pos ha0
      have hval := hanti (by simpa using hqlo_pos) (by simpa using hqhi_pos) hlt
      change Ffun P.X a q_hi < Ffun P.X a q_lo at hval
      rw [himg_hi, himg_lo] at hval
      nlinarith
    · have heqF : 300 * S.F = S.F / 500 := by
        rw [← himg_hi, ← himg_lo]
        rw [heq]
      nlinarith [hFpos, heqF]
  have hDpos : 0 < S.D := S.D_pos
  have htarget_order :
      dBreve P.X a (300 * S.F) / S.D < dBreve P.X a (S.F / 500) / S.D := by
    simpa [q_hi, q_lo] using div_lt_div_of_pos_right hq_order hDpos
  simpa [sec7_ra_rho3Target] using uniqueDiffOn_Icc htarget_order

/-- Normalized `dtilde/S.D` is `C⁶` on the wide §7 window. -/
theorem sec7_ra_ftilde_contDiffOn_wide {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} (ha : 0 < a) (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) :
    ContDiffOn ℝ 6 (fun s => dtilde P.X s (a : ℝ) / S.D) (sec7_rWinWide S W) := by
  intro r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hRpos : 0 < S.R := sec7_R_pos S
  have hr0 : 0 < r := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 107 / 18000) hRpos) hr_lo
  exact ((sec7_ra_dtilde_r_contDiffAt (n := 6) (X := P.X) (a := (a : ℝ))
    P.X_pos haR hr0).div_const S.D).contDiffWithinAt

/-- The normalized wide image lies in `(0, ∞)`. -/
theorem sec7_ra_ftilde_mapsTo_Ioi_wide {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) :
    Set.MapsTo (fun s => dtilde P.X s (a : ℝ) / S.D)
      (sec7_rWinWide S W) (Set.Ioi 0) := by
  intro r hr
  obtain ⟨hd_lo, _hd_ge, _hd_hi⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hD20 : 0 < S.D / 20 := div_pos S.D_pos (by norm_num)
  exact div_pos (lt_of_lt_of_le hD20 hd_lo) S.D_pos

/-- Derivative bounds for normalized `dtilde/S.D` on the wide window. -/
theorem sec7_ra_ftilde_FDeriv_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) {i : ℕ} (hi₁ : 1 ≤ i) (hi₆ : i ≤ 6) :
    ‖iteratedFDerivWithin ℝ i (fun s => dtilde P.X s (a : ℝ) / S.D)
        (sec7_rWinWide S W) r‖ ≤ ((10 ^ 3 : ℝ) / S.R) ^ i := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have hopen : IsOpen (sec7_rWinWide S W) := by
    simpa [sec7_rWinWide] using (isOpen_Ioo : IsOpen (Set.Ioo
      (S.R / 144 - 6 * (W + W ^ 2 + W ^ 4))
      (40 * S.R + 6 * (W + W ^ 2 + W ^ 4))))
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  rw [(iteratedDerivWithin_of_isOpen (𝕜 := ℝ) (n := i)
    (f := fun s => dtilde P.X s (a : ℝ) / S.D) hopen) hr]
  rw [Real.norm_eq_abs, iteratedDeriv_div_const, abs_div, abs_of_pos hDpos]
  interval_cases i
  · have hdt := sec7_ra_dtilde_wide_d1 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 1 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt1 * (S.D / S.R)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 1 := by
            norm_num [sec7_ra_Cdt1]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
  · have hdt := sec7_ra_dtilde_wide_d2 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 2 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt2 * (S.D / S.R ^ 2)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 2 := by
            norm_num [sec7_ra_Cdt2]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d3 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 3 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt3 * (S.D / S.R ^ 3)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 3 := by
            norm_num [sec7_ra_Cdt3]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d4 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 4 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt4 * (S.D / S.R ^ 4)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 4 := by
            norm_num [sec7_ra_Cdt4]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d5 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 5 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt5 * (S.D / S.R ^ 5)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 5 := by
            norm_num [sec7_ra_Cdt5]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d6 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 6 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt6 * (S.D / S.R ^ 6)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 6 := by
            norm_num [sec7_ra_Cdt6]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring

/-- On the wide §7 `r` core, `Ffun(dtilde)` stays in the `F`-scale window. -/
theorem sec7_ra_ftil_scale {P : Globals} {S : Scale P} {r : ℝ} {a : ℤ}
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hrlo : (107 / 18000 : ℝ) * S.R ≤ r)
    (hrhi : r ≤ (40001 / 1000 : ℝ) * S.R) :
    S.F / 500 ≤ Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) ∧
      Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) ≤ 300 * S.F := by
  have hR : 0 < S.R := sec7_R_pos S
  have hF : 0 < S.F := sec7_ra_F_pos S
  have hA : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have hX : 0 < P.X := P.X_pos
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hr0 : 0 < r := by
    have hbase : 0 < (107 / 18000 : ℝ) * S.R :=
      mul_pos (by norm_num) hR
    exact lt_of_lt_of_le hbase hrlo
  have hclosed := ftil_closed (X := P.X) (r := r) (a := (a : ℝ)) hX haR hr0
  have hftil_eq :
      Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) =
        r * Real.sqrt ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) /
          (a : ℝ) ^ 2 := by
    simpa using hclosed
  have hq_nonneg : 0 ≤ P.X * (a : ℝ) ^ 3 / r := by positivity
  have hrad_nonneg :
      0 ≤ (a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by positivity
  have hftil_nonneg : 0 ≤ Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) := by
    rw [hftil_eq]
    positivity
  have hclosed_low :
      16 * P.X * r ^ 3 / (a : ℝ) ^ 5
        ≤ (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ^ 4 := by
    rw [hftil_eq]
    calc
      16 * P.X * r ^ 3 / (a : ℝ) ^ 5
          = r ^ 4 * (4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 /
              (a : ℝ) ^ 8 := by
            rw [show (4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 =
                16 * (P.X * (a : ℝ) ^ 3 / r) by
                  rw [mul_pow, Real.sq_sqrt hq_nonneg]
                  ring]
            field_simp [ne_of_gt hr0, ne_of_gt haR]
      _ ≤ r ^ 4 *
            (((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) /
              (a : ℝ) ^ 8 := by
            have hterm_nonneg :
                0 ≤ 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by positivity
            have hrad_ge :
                4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) ≤
                  (a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by
              nlinarith [sq_nonneg (a : ℝ)]
            have hsq := pow_le_pow_left₀ hterm_nonneg hrad_ge 2
            gcongr
      _ = (r * Real.sqrt
              ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) /
            (a : ℝ) ^ 2) ^ 4 := by
            rw [div_pow, mul_pow,
              show Real.sqrt
                  ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 by
                  rw [show Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                    (Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) ^ 2
                    by ring, Real.sq_sqrt hrad_nonneg]]
            ring
  have hconst_low :
      (1 : ℝ) / 500 ^ 4 ≤
        16 * ((107 / 18000 : ℝ) ^ 3) / 11 ^ 5 := by
    norm_num
  have hscale_low :
      (S.F / 500) ^ 4 ≤ 16 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
    have hr3 :
        ((107 / 18000 : ℝ) * S.R) ^ 3 ≤ r ^ 3 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ (107 / 18000 : ℝ) * S.R) hrlo 3
    have ha5 : (a : ℝ) ^ 5 ≤ (11 * S.A) ^ 5 :=
      pow_le_pow_left₀ haR.le ha_hi 5
    have hnum :
        16 * P.X * (((107 / 18000 : ℝ) * S.R) ^ 3) ≤
          16 * P.X * r ^ 3 := by
      gcongr
    have hdenpos : 0 < (a : ℝ) ^ 5 := pow_pos haR 5
    calc
      (S.F / 500) ^ 4
          = (1 / (500:ℝ) ^ 4) * (S.R ^ 3 * P.X / S.A ^ 5) := by
            rw [sec7_ra_R3X_div_A5_eq_F4 S]
            ring
      _ ≤ (16 * ((107 / 18000 : ℝ) ^ 3) / 11 ^ 5) *
            (S.R ^ 3 * P.X / S.A ^ 5) := by
            exact mul_le_mul_of_nonneg_right hconst_low (by positivity)
      _ = 16 * P.X * (((107 / 18000 : ℝ) * S.R) ^ 3) / (11 * S.A) ^ 5 := by
            field_simp [ne_of_gt hA]
      _ ≤ 16 * P.X * r ^ 3 / (11 * S.A) ^ 5 := by
            exact div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 16 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
            exact div_le_div_of_nonneg_left (by positivity) hdenpos ha5
  have hlow4 :
      (S.F / 500) ^ 4 ≤ (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ^ 4 :=
    le_trans hscale_low hclosed_low
  have hlow :
      S.F / 500 ≤ Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) :=
    sec7_ra_le_of_fourth (by positivity) hftil_nonneg hlow4
  have hΩH : 10 * S.Ω ≤ P.H := sec7_dtilde_wide_AD_omega_le hAD
  have hΩle : S.Ω ≤ P.H / 10 := by nlinarith
  have hΩ4 : S.Ω ^ 4 ≤ (P.H / 10) ^ 4 :=
    pow_le_pow_left₀ S.Ω_pos.le hΩle 4
  have harX : (a : ℝ) * r ≤ P.X := by
    have hstep :
        (a : ℝ) * r ≤ (11 * S.A) * ((40001 / 1000 : ℝ) * S.R) := by
      exact mul_le_mul ha_hi hrhi hr0.le (by positivity)
    calc
      (a : ℝ) * r ≤ (11 * S.A) * ((40001 / 1000 : ℝ) * S.R) := hstep
      _ = (11 * (40001 / 1000 : ℝ)) * (P.H * P.G * S.Ω ^ 4) := by
            unfold Scale.A Scale.R
            field_simp [S.Δ_pos.ne']
      _ ≤ (11 * (40001 / 1000 : ℝ)) * (P.H * P.G * (P.H / 10) ^ 4) := by
            have hmid :
                P.H * P.G * S.Ω ^ 4 ≤ P.H * P.G * (P.H / 10) ^ 4 := by
              exact mul_le_mul_of_nonneg_left hΩ4
                (mul_nonneg P.H_pos.le P.G_pos.le)
            exact mul_le_mul_of_nonneg_left hmid (by norm_num)
      _ ≤ P.X := by
            rw [P.X_eq_G_mul_H_pow_five]
            have hc : (11 * (40001 / 1000 : ℝ)) / 10 ^ 4 ≤ 1 := by norm_num
            calc
              (11 * (40001 / 1000 : ℝ)) * (P.H * P.G * (P.H / 10) ^ 4)
                  = ((11 * (40001 / 1000 : ℝ)) / 10 ^ 4) *
                      (P.G * P.H ^ 5) := by ring_nf
              _ ≤ 1 * (P.G * P.H ^ 5) := by
                    exact mul_le_mul_of_nonneg_right hc
                      (mul_nonneg P.G_pos.le (pow_nonneg P.H_pos.le 5))
              _ = P.G * P.H ^ 5 := by ring
  have ha2_sq_le : ((a : ℝ) ^ 2) ^ 2 ≤ P.X * (a : ℝ) ^ 3 / r := by
    rw [le_div_iff₀ hr0]
    calc
      ((a : ℝ) ^ 2) ^ 2 * r = (a : ℝ) ^ 3 * ((a : ℝ) * r) := by ring
      _ ≤ (a : ℝ) ^ 3 * P.X := by
            exact mul_le_mul_of_nonneg_left harX (by positivity)
      _ = P.X * (a : ℝ) ^ 3 := by ring
  have ha2_le_sqrt :
      (a : ℝ) ^ 2 ≤ Real.sqrt (P.X * (a : ℝ) ^ 3 / r) :=
    Real.le_sqrt_of_sq_le ha2_sq_le
  have hrad_le :
      (a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) ≤
        5 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by
    nlinarith
  have hclosed_hi :
      (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ^ 4 ≤
        25 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
    rw [hftil_eq]
    calc
      (r * Real.sqrt
              ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) /
            (a : ℝ) ^ 2) ^ 4
          = r ^ 4 *
              (((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) /
                (a : ℝ) ^ 8 := by
            rw [div_pow, mul_pow,
              show Real.sqrt
                  ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 by
                  rw [show Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                    (Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) ^ 2
                    by ring, Real.sq_sqrt hrad_nonneg]]
            ring
      _ ≤ r ^ 4 * (5 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 /
            (a : ℝ) ^ 8 := by
            have hsq := pow_le_pow_left₀ hrad_nonneg hrad_le 2
            gcongr
      _ = 25 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
            rw [show (5 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 =
                25 * (P.X * (a : ℝ) ^ 3 / r) by
                  rw [mul_pow, Real.sq_sqrt hq_nonneg]
                  ring]
            field_simp [ne_of_gt hr0, ne_of_gt haR]
  have hconst_hi :
      25 * ((40001 / 1000 : ℝ) ^ 3) * 5 ^ 5 ≤ 300 ^ 4 := by
    norm_num
  have hscale_hi :
      25 * P.X * r ^ 3 / (a : ℝ) ^ 5 ≤ (300 * S.F) ^ 4 := by
    have hr3 : r ^ 3 ≤ ((40001 / 1000 : ℝ) * S.R) ^ 3 :=
      pow_le_pow_left₀ hr0.le hrhi 3
    have ha5 : (S.A / 5) ^ 5 ≤ (a : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ S.A / 5) ha_lo 5
    have hnum :
        25 * P.X * r ^ 3 ≤
          25 * P.X * (((40001 / 1000 : ℝ) * S.R) ^ 3) := by
      gcongr
    have hdenposa : 0 < (a : ℝ) ^ 5 := pow_pos haR 5
    have hdenposlo : 0 < (S.A / 5) ^ 5 := by positivity
    calc
      25 * P.X * r ^ 3 / (a : ℝ) ^ 5
          ≤ 25 * P.X * (((40001 / 1000 : ℝ) * S.R) ^ 3) / (a : ℝ) ^ 5 := by
            exact div_le_div_of_nonneg_right hnum hdenposa.le
      _ ≤ 25 * P.X * (((40001 / 1000 : ℝ) * S.R) ^ 3) / (S.A / 5) ^ 5 := by
            exact div_le_div_of_nonneg_left (by positivity) hdenposlo ha5
      _ = (25 * ((40001 / 1000 : ℝ) ^ 3) * 5 ^ 5) *
            (S.R ^ 3 * P.X / S.A ^ 5) := by
            field_simp [ne_of_gt hA]
      _ ≤ 300 ^ 4 * (S.R ^ 3 * P.X / S.A ^ 5) := by
            exact mul_le_mul_of_nonneg_right hconst_hi (by positivity)
      _ = (300 * S.F) ^ 4 := by
            rw [sec7_ra_R3X_div_A5_eq_F4 S]
            ring
  have hhi4 :
      (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ^ 4 ≤ (300 * S.F) ^ 4 :=
    le_trans hclosed_hi hscale_hi
  have hhi :
      Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) ≤ 300 * S.F :=
    sec7_ra_le_of_fourth hftil_nonneg (by positivity) hhi4
  exact ⟨hlow, hhi⟩

/-- The normalized wide image lies in the `ρ₃` target interval. -/
theorem sec7_ra_ftilde_mapsTo_rho3Target {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) :
    Set.MapsTo (fun s => dtilde P.X s (a : ℝ) / S.D)
      (sec7_rWinWide S W) (sec7_ra_rho3Target P S (a : ℝ)) := by
  intro r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  have ha_lo_w : S.A / 5 ≤ (a : ℝ) := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    nlinarith
  have ha_hi_w : (a : ℝ) ≤ 11 * S.A := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    nlinarith
  obtain ⟨hr_lo, hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_ra_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD ha_lo_w ha_hi_w hr_lo hr_hi
  have hFpos : 0 < S.F := sec7_ra_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := 300 * S.F)
      hAD ha_lo_w ha_hi_w ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := S.F / 500)
      hAD ha_lo_w ha_hi_w ht_lo
  set d : ℝ := dtilde P.X r (a : ℝ)
  set q_hi : ℝ := dBreve P.X (a : ℝ) (300 * S.F)
  set q_lo : ℝ := dBreve P.X (a : ℝ) (S.F / 500)
  have hr0 : 0 < r := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 107 / 18000) (sec7_R_pos S)) hr_lo
  have hdpos : 0 < d := by
    dsimp [d]
    exact dtilde_pos P.X_pos haR hr0
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hFd : Ffun P.X (a : ℝ) d =
      Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) := by
    simp [d]
  have hanti := sec7_ra_Ffun_strictAntiOn_pos (X := P.X) (a := (a : ℝ)) P.X_pos haR
  have hleft_d : q_hi ≤ d := by
    by_contra hnot
    have hlt : d < q_hi := lt_of_not_ge hnot
    have hval := hanti (by simpa using hdpos) (by simpa using hqhi_pos) hlt
    change Ffun P.X (a : ℝ) q_hi < Ffun P.X (a : ℝ) d at hval
    rw [himg_hi, hFd] at hval
    nlinarith
  have hright_d : d ≤ q_lo := by
    by_contra hnot
    have hlt : q_lo < d := lt_of_not_ge hnot
    have hval := hanti (by simpa using hqlo_pos) (by simpa using hdpos) hlt
    change Ffun P.X (a : ℝ) d < Ffun P.X (a : ℝ) q_lo at hval
    rw [hFd, himg_lo] at hval
    nlinarith
  constructor
  · simpa [sec7_ra_rho3Target, d, q_hi] using
      div_le_div_of_nonneg_right hleft_d hDpos.le
  · simpa [sec7_ra_rho3Target, d, q_lo] using
      div_le_div_of_nonneg_right hright_d hDpos.le

/-- The normalized `ρ₃(Du)` residual is `C⁵` on the target interval. -/
theorem sec7_ra_gtilde3_contDiffOn_target {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 6
      (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
      (sec7_ra_rho3Target P S (a : ℝ)) := by
  intro u hu
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  have ha_lo_w : S.A / 5 ≤ (a : ℝ) := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    nlinarith
  have ha_hi_w : (a : ℝ) ≤ 11 * S.A := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    nlinarith
  have hFpos : 0 < S.F := sec7_ra_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := 300 * S.F)
      hAD ha_lo_w ha_hi_w ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := S.F / 500)
      hAD ha_lo_w ha_hi_w ht_lo
  set q_hi : ℝ := dBreve P.X (a : ℝ) (300 * S.F)
  set q_lo : ℝ := dBreve P.X (a : ℝ) (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have huI : dBreve P.X (a : ℝ) (300 * S.F) / S.D ≤ u ∧
      u ≤ dBreve P.X (a : ℝ) (S.F / 500) / S.D := by
    simpa [sec7_ra_rho3Target] using hu
  have hu_pos : 0 < u := by
    have hqdiv : 0 < dBreve P.X (a : ℝ) (300 * S.F) / S.D := by
      simpa [q_hi] using div_pos hqhi_pos hDpos
    exact lt_of_lt_of_le hqdiv huI.1
  have hdu_pos : 0 < S.D * u := mul_pos hDpos hu_pos
  have hqhi_le_du : q_hi ≤ S.D * u := by
    have h := mul_le_mul_of_nonneg_right huI.1 hDpos.le
    field_simp [ne_of_gt hDpos] at h
    simpa [q_hi, mul_comm] using h
  have hdu_le_qlo : S.D * u ≤ q_lo := by
    have h := mul_le_mul_of_nonneg_right huI.2 hDpos.le
    field_simp [ne_of_gt hDpos] at h
    simpa [q_lo, mul_comm] using h
  have hanti := sec7_ra_Ffun_strictAntiOn_pos (X := P.X) (a := (a : ℝ)) P.X_pos haR
  have hFdu_hi : Ffun P.X (a : ℝ) (S.D * u) ≤ 300 * S.F := by
    rcases lt_or_eq_of_le hqhi_le_du with hlt | heq
    · have hval := hanti (by simpa using hqhi_pos) (by simpa using hdu_pos) hlt
      change Ffun P.X (a : ℝ) (S.D * u) < Ffun P.X (a : ℝ) q_hi at hval
      rw [himg_hi] at hval
      exact le_of_lt hval
    · rw [← heq]
      simpa [q_hi] using himg_hi.le
  have hFdu_lo : S.F / 500 ≤ Ffun P.X (a : ℝ) (S.D * u) := by
    rcases lt_or_eq_of_le hdu_le_qlo with hlt | heq
    · have hval := hanti (by simpa using hdu_pos) (by simpa using hqlo_pos) hlt
      change Ffun P.X (a : ℝ) q_lo < Ffun P.X (a : ℝ) (S.D * u) at hval
      rw [himg_lo] at hval
      exact le_of_lt hval
    · rw [heq]
      simpa [q_lo] using himg_lo.ge
  have hshift := sec7_ra_shift_error_bound_zero (P := P) (S := S) (W := W)
    (j := j) Env hW c₀ Cu hsd hj
  have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
    have hjlo' : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le (j : ℝ)
    nlinarith
  have hjhi : (j : ℝ) ≤ S.F / 1000 := by
    have hjhi' : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
    nlinarith
  have htWin : Ffun P.X (a : ℝ) (S.D * u) + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  set t : ℝ := Ffun P.X (a : ℝ) (S.D * u) + (j : ℝ)
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo_w ha_hi_w (by simpa [t] using htWin)
  have hdb :=
    sec7_ra_dBreve_contDiffAt6_Ffun_public (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR dBreve_pos
  have hdb_at : ContDiffAt ℝ 6 (dBreve P.X (a : ℝ)) t := by
    simpa [himg] using hdb
  have hlin : ContDiffAt ℝ 6 (fun y : ℝ => S.D * y) u :=
    contDiffAt_const.mul contDiffAt_id
  have hFbase : ContDiffAt ℝ 6 (fun d : ℝ => Ffun P.X (a : ℝ) d) (S.D * u) :=
    Ffun_contDiffAt6 (X := P.X) (a := (a : ℝ)) (d := S.D * u)
      (ne_of_gt hdu_pos) (by positivity)
  have hFarg : ContDiffAt ℝ 6 (fun y : ℝ => Ffun P.X (a : ℝ) (S.D * y)) u :=
    hFbase.comp u hlin
  have harg : ContDiffAt ℝ 6
      (fun y : ℝ => Ffun P.X (a : ℝ) (S.D * y) + (j : ℝ)) u :=
    hFarg.add contDiffAt_const
  have hB : ContDiffAt ℝ 6
      (fun y : ℝ => dBreve P.X (a : ℝ)
        (Ffun P.X (a : ℝ) (S.D * y) + (j : ℝ))) u := by
    simpa [t] using hdb_at.comp u harg
  have hrad : ContDiffAt ℝ 6
      (fun y : ℝ => (S.D * y) * (S.D * y + (a : ℝ))) u :=
    hlin.mul (hlin.add contDiffAt_const)
  have hsqrt : ContDiffAt ℝ 6
      (fun y : ℝ => Real.sqrt ((S.D * y) * (S.D * y + (a : ℝ)))) u := by
    refine ContDiffAt.sqrt hrad ?_
    positivity
  have hmain := hB.sub hsqrt
  simpa [sec7_ra_rho3Fun, mul_assoc] using hmain.contDiffWithinAt

end Squarefree
