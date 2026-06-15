import Squarefree.Lower.DefectDeriv5
import Squarefree.Bracket.Sec7Defs
import Squarefree.Opt.OnStripAux

/-!
# §7 wide-window bounds for `dtilde`

This file contains §7-local facts for `dtilde P.X r a` on the full wide aperture
`sec7_rWinWide`.  The older §5 derivative bounds are intentionally left unchanged: their
window is narrower and several §5 files depend on their exact statement.
-/

open Classical Filter Real
open scoped Topology

namespace Squarefree

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

private theorem sec7_dtilde_wide_shift_margin {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    2000 * (W + W ^ 2 + W ^ 4) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hlog : (1 : ℝ) ≤ 1 + Real.log P.X := by
    have := Real.log_nonneg hsd.hX
    linarith
  have hRform :
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
    rw [OnStripAux.R_mono P S, Real.rpow_one,
      show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have henv : sec7_envC * W ^ 8 ≤ S.R := by
    calc
      sec7_envC * W ^ 8
          ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
            exact le_mul_of_one_le_right (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 8)) hlog
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
            simpa only [Real.rpow_one, show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
              rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]] using Env.tc4
      _ = S.R := hRform
  have hW14 : W ≤ W ^ 4 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW24 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW48 : W ^ 4 ≤ W ^ 8 := pow_le_pow_right₀ hW (by omega)
  have hsum : W + W ^ 2 + W ^ 4 ≤ 3 * W ^ 4 := by linarith
  have h2000 : 2000 * (W + W ^ 2 + W ^ 4) ≤ 6000 * W ^ 8 := by
    calc
      2000 * (W + W ^ 2 + W ^ 4) ≤ 2000 * (3 * W ^ 4) := by gcongr
      _ = 6000 * W ^ 4 := by ring
      _ ≤ 6000 * W ^ 8 := by gcongr
  have hC : (6000 : ℝ) * W ^ 8 ≤ sec7_envC * W ^ 8 := by
    gcongr
    norm_num [sec7_envC]
  exact le_trans (le_trans h2000 hC) henv

private theorem sec7_dtilde_wide_shift_margin_strong {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    6000 * (W + W ^ 2 + W ^ 4) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hlog : (1 : ℝ) ≤ 1 + Real.log P.X := by
    have := Real.log_nonneg hsd.hX
    linarith
  have hRform :
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
    rw [OnStripAux.R_mono P S, Real.rpow_one,
      show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have henv : sec7_envC * W ^ 8 ≤ S.R := by
    calc
      sec7_envC * W ^ 8
          ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
            exact le_mul_of_one_le_right (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 8)) hlog
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
            simpa only [Real.rpow_one, show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
              rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]] using Env.tc4
      _ = S.R := hRform
  have hW14 : W ≤ W ^ 4 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW24 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW48 : W ^ 4 ≤ W ^ 8 := pow_le_pow_right₀ hW (by omega)
  have hsum : W + W ^ 2 + W ^ 4 ≤ 3 * W ^ 4 := by linarith
  have h6000 : 6000 * (W + W ^ 2 + W ^ 4) ≤ 18000 * W ^ 8 := by
    calc
      6000 * (W + W ^ 2 + W ^ 4) ≤ 6000 * (3 * W ^ 4) := by gcongr
      _ = 18000 * W ^ 4 := by ring
      _ ≤ 18000 * W ^ 8 := by gcongr
  have hC : (18000 : ℝ) * W ^ 8 ≤ sec7_envC * W ^ 8 := by
    gcongr
    norm_num [sec7_envC]
  exact le_trans (le_trans h6000 hC) henv

theorem sec7_dtilde_wide_rWinWide_core {P : Globals} {S : Scale P} {W r : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) (hr : r ∈ sec7_rWinWide S W) :
    (107 / 18000 : ℝ) * S.R ≤ r ∧ r ≤ (40001 / 1000 : ℝ) * S.R := by
  have hR : 0 < S.R := sec7_R_pos S
  have hs := sec7_dtilde_wide_shift_margin_strong Env hW c₀ Cu hsd
  simp only [sec7_rWinWide, Set.mem_Ioo] at hr
  constructor <;> nlinarith

theorem sec7_dtilde_wide_AD_omega_le {P : Globals} {S : Scale P}
    (hAD : 10 * S.A ≤ S.D) : 10 * S.Ω ≤ P.H := by
  have hΔ : 0 < S.Δ := S.Δ_pos
  have hAD' : 10 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by
    simpa [Scale.A, Scale.D, mul_assoc, mul_left_comm, mul_comm] using hAD
  have hAD'' : S.Δ * (10 * S.Ω) ≤ S.Δ * P.H := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hAD'
  exact le_of_mul_le_mul_left hAD'' hΔ

/-- Wide-window image for the §7 residual composition:
`D/20 ≤ dtilde ≤ 40D`, and the band variable satisfies `a ≤ dtilde`. -/
theorem sec7_ra_dtilde_wide_image {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    S.D / 20 ≤ dtilde P.X r (a : ℝ)
      ∧ (a : ℝ) ≤ dtilde P.X r (a : ℝ)
      ∧ dtilde P.X r (a : ℝ) ≤ 40 * S.D := by
  set X := P.X with hXdef
  set D := S.D with hDdef
  set R := S.R with hRdef
  set A := S.A with hAdef
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < X := by rw [hXdef]; exact P.X_pos
  have hDeq : D = P.H * S.Δ := rfl
  have hAeq : A = S.Δ * S.Ω := rfl
  have hReq : R = P.H * P.G * S.Ω ^ 3 / S.Δ := rfl
  have hDpos : 0 < D := by rw [hDeq]; positivity
  have hApos : 0 < A := by rw [hAeq]; positivity
  have hRpos : 0 < R := by rw [hReq]; positivity
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  have hRDX : X * A ^ 3 / R = D ^ 4 := by
    rw [hReq, hDeq, hAeq, hXdef, P.X_eq_G_mul_H_pow_five]
    field_simp
  set d := dtilde X r (a : ℝ) with hddef
  have hdpos : 0 < d := dtilde_pos hXpos haR hr0
  set w := Real.sqrt (X * (a : ℝ) ^ 3 / r) with hwdef
  have hprod : d * (d + (a : ℝ)) = w := dtilde_prod hXpos haR hr0
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = X * (a : ℝ) ^ 3 / r := Real.sq_sqrt (by positivity)
  have ha3_hi : (a : ℝ) ^ 3 ≤ (2 * A) ^ 3 := by
    have : (a : ℝ) ≤ 2 * A := by simpa [hAdef] using ha_hi
    exact pow_le_pow_left₀ haR.le this 3
  have ha3_lo : A ^ 3 ≤ (a : ℝ) ^ 3 := by
    have : A ≤ (a : ℝ) := by simpa [hAdef] using ha_lo
    exact pow_le_pow_left₀ hApos.le this 3
  have hXA3 : X * A ^ 3 = D ^ 4 * R := by
    rw [← hRDX]
    field_simp [ne_of_gt hRpos]
  have hw2_hi : w ^ 2 ≤ 500000 * D ^ 4 := by
    rw [hwsq]
    have hnum : X * (a : ℝ) ^ 3 ≤ X * (2 * A) ^ 3 :=
      mul_le_mul_of_nonneg_left ha3_hi hXpos.le
    have hstep : X * (a : ℝ) ^ 3 / r ≤
        X * (2 * A) ^ 3 / ((107 / 18000 : ℝ) * R) := by
      exact div_le_div₀ (by positivity : 0 ≤ X * (2 * A) ^ 3) hnum
        (by positivity : 0 < (107 / 18000 : ℝ) * R)
        (by simpa [hRdef] using hr_lo)
    refine hstep.trans ?_
    rw [div_le_iff₀ (by positivity : 0 < (107 / 18000 : ℝ) * R)]
    nlinarith [hXA3, hRpos, pow_pos hDpos 4]
  have hd2_lt_w : d ^ 2 < w := by
    have : d ^ 2 < d * (d + (a : ℝ)) := by nlinarith [hdpos, haR]
    linarith [hprod, this]
  have hw_le : w ≤ 800 * D ^ 2 := by
    nlinarith [hw2_hi, sq_nonneg (w - 800 * D ^ 2), hwpos, hDpos,
      pow_pos hDpos 2, mul_pos hwpos hwpos]
  have hd_upper : d ≤ 40 * D := by
    nlinarith [hd2_lt_w, hw_le, sq_nonneg (d - 40 * D), hdpos, hDpos,
      pow_pos hDpos 2, mul_pos hdpos hdpos]
  have hd_ge_a : (a : ℝ) ≤ d := by
    by_contra hcon
    rw [not_le] at hcon
    have hw_lt : w < 2 * (a : ℝ) ^ 2 := by
      have : d * (d + (a : ℝ)) < (a : ℝ) * (2 * (a : ℝ)) := by
        nlinarith [hdpos, haR, hcon]
      nlinarith [hprod, this]
    have hw2_lt : w ^ 2 < 4 * (a : ℝ) ^ 4 := by
      nlinarith [hw_lt, hwpos, haR, sq_nonneg (a : ℝ), mul_pos haR haR]
    rw [hwsq] at hw2_lt
    have hXar : X < 4 * (a : ℝ) * r := by
      have hcross : X * (a : ℝ) ^ 3 < 4 * (a : ℝ) ^ 4 * r := by
        have := (div_lt_iff₀ hr0).mp hw2_lt
        linarith [this]
      have ha3pos : 0 < (a : ℝ) ^ 3 := by positivity
      nlinarith [hcross, ha3pos, haR]
    have hbound : 4 * (a : ℝ) * r ≤ 400 * (A * R) := by
      have haA : (a : ℝ) ≤ 2 * A := by simpa [hAdef] using ha_hi
      have hrR : r ≤ (40001 / 1000 : ℝ) * R := by simpa [hRdef] using hr_hi
      have hmul := mul_le_mul haA hrR hr0.le (by positivity : 0 ≤ 2 * A)
      nlinarith [hmul, hApos, hRpos]
    have hHge : 10 * S.Ω ≤ P.H := sec7_dtilde_wide_AD_omega_le hAD
    have hAR : A * R = P.H * P.G * S.Ω ^ 4 := by
      rw [hAeq, hReq]
      field_simp [ne_of_gt hΔpos]
    have h400 : 400 * (A * R) < X := by
      rw [hAR, hXdef, P.X_eq_G_mul_H_pow_five]
      have hH4 : (400 : ℝ) * S.Ω ^ 4 < P.H ^ 4 := by
        have hmono : (10 * S.Ω) ^ 4 ≤ P.H ^ 4 :=
          pow_le_pow_left₀ (by positivity) hHge 4
        nlinarith [hmono, pow_pos hΩpos 4]
      have hfac : 0 < P.G * P.H := by positivity
      nlinarith [mul_lt_mul_of_pos_left hH4 hfac, hfac]
    linarith
  have hw2_lo : D ^ 4 / 100 ≤ w ^ 2 := by
    rw [hwsq]
    have hnum : X * A ^ 3 ≤ X * (a : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left ha3_lo hXpos.le
    have hrR : r ≤ (40001 / 1000 : ℝ) * R := by simpa [hRdef] using hr_hi
    have hstep : X * A ^ 3 / ((40001 / 1000 : ℝ) * R) ≤
        X * (a : ℝ) ^ 3 / r := by
      apply div_le_div₀ (by positivity) hnum hr0 hrR
    refine le_trans ?_ hstep
    rw [le_div_iff₀ (by positivity : 0 < (40001 / 1000 : ℝ) * R)]
    nlinarith [hXA3, hRpos, pow_pos hDpos 4]
  have hw_ge : D ^ 2 / 10 ≤ w := by
    nlinarith [hw2_lo, sq_nonneg (w - D ^ 2 / 10), hwpos, hDpos,
      pow_pos hDpos 2, mul_pos hwpos hwpos]
  have hw_le_2d2 : w ≤ 2 * d ^ 2 := by
    have : d * (d + (a : ℝ)) ≤ 2 * d ^ 2 := by nlinarith [hdpos, hd_ge_a]
    linarith [hprod, this]
  have hd_lower : D / 20 ≤ d := by
    nlinarith [hw_le_2d2, hw_ge, sq_nonneg (d - D / 20), hdpos, hDpos,
      pow_pos hDpos 2, mul_pos hdpos hdpos]
  simpa [hDdef, hXdef, hddef] using ⟨hd_lower, hd_ge_a, hd_upper⟩

def sec7_ra_Cdt1 : ℝ := 10 ^ 3
def sec7_ra_Cdt2 : ℝ := 10 ^ 6
def sec7_ra_Cdt3 : ℝ := 10 ^ 9
def sec7_ra_Cdt4 : ℝ := 10 ^ 12
def sec7_ra_Cdt5 : ℝ := 10 ^ 15

private theorem sec7_ra_wide_r_bounds {P : Globals} {S : Scale P} {W r : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) {c₀ Cu : ℝ}
    (hsd : OnStripAux.StripData P S c₀ Cu) (hr : r ∈ sec7_rWinWide S W) :
    S.R / 200 ≤ r ∧ r ≤ 41 * S.R := by
  have hR : 0 < S.R := sec7_R_pos S
  obtain ⟨hr_lo, hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  constructor
  · nlinarith [hr_lo, hR]
  · nlinarith [hr_hi, hR]

private theorem sec7_ra_dtilde_wide_d_upper_sharp {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    dtilde P.X r (a : ℝ) ≤ 7 * S.D := by
  set X := P.X with hXdef
  set D := S.D with hDdef
  set R := S.R with hRdef
  set A := S.A with hAdef
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < X := by rw [hXdef]; exact P.X_pos
  have hDeq : D = P.H * S.Δ := rfl
  have hAeq : A = S.Δ * S.Ω := rfl
  have hReq : R = P.H * P.G * S.Ω ^ 3 / S.Δ := rfl
  have hDpos : 0 < D := by rw [hDeq]; positivity
  have hApos : 0 < A := by rw [hAeq]; positivity
  have hRpos : 0 < R := by rw [hReq]; positivity
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  have hRDX : X * A ^ 3 / R = D ^ 4 := by
    rw [hReq, hDeq, hAeq, hXdef, P.X_eq_G_mul_H_pow_five]
    field_simp
  set d := dtilde X r (a : ℝ) with hddef
  have hdpos : 0 < d := dtilde_pos hXpos haR hr0
  set w := Real.sqrt (X * (a : ℝ) ^ 3 / r) with hwdef
  have hprod : d * (d + (a : ℝ)) = w := dtilde_prod hXpos haR hr0
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = X * (a : ℝ) ^ 3 / r := Real.sq_sqrt (by positivity)
  have ha3_hi : (a : ℝ) ^ 3 ≤ (2 * A) ^ 3 := by
    have : (a : ℝ) ≤ 2 * A := by simpa [hAdef] using ha_hi
    exact pow_le_pow_left₀ haR.le this 3
  have hXA3 : X * A ^ 3 = D ^ 4 * R := by
    rw [← hRDX]
    field_simp [ne_of_gt hRpos]
  have hw2_hi : w ^ 2 ≤ 1400 * D ^ 4 := by
    rw [hwsq]
    have hnum : X * (a : ℝ) ^ 3 ≤ X * (2 * A) ^ 3 :=
      mul_le_mul_of_nonneg_left ha3_hi hXpos.le
    have hstep : X * (a : ℝ) ^ 3 / r ≤
        X * (2 * A) ^ 3 / ((107 / 18000 : ℝ) * R) := by
      exact div_le_div₀ (by positivity : 0 ≤ X * (2 * A) ^ 3) hnum
        (by positivity : 0 < (107 / 18000 : ℝ) * R)
        (by simpa [hRdef] using hr_lo)
    refine hstep.trans ?_
    rw [div_le_iff₀ (by positivity : 0 < (107 / 18000 : ℝ) * R)]
    nlinarith [hXA3, hRpos, pow_pos hDpos 4]
  have hd2_lt_w : d ^ 2 < w := by
    have : d ^ 2 < d * (d + (a : ℝ)) := by nlinarith [hdpos, haR]
    linarith [hprod, this]
  have hw_le : w ≤ 49 * D ^ 2 := by
    nlinarith [hw2_hi, sq_nonneg (w - 49 * D ^ 2), hwpos, hDpos,
      pow_pos hDpos 2, mul_pos hwpos hwpos]
  have hd_upper : d ≤ 7 * D := by
    nlinarith [hd2_lt_w, hw_le, sq_nonneg (d - 7 * D), hdpos, hDpos,
      pow_pos hDpos 2, mul_pos hdpos hdpos]
  simpa [hDdef, hXdef, hddef] using hd_upper

/-- Wide-window first derivative bound for `dtilde`. -/
theorem sec7_ra_dtilde_wide_d1 {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    |iteratedDeriv 1 (fun s => dtilde P.X s (a : ℝ)) r|
      ≤ sec7_ra_Cdt1 * (S.D / S.R) := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
  have hd_sharp : d ≤ 7 * S.D := by
    simpa [hd_def] using
      sec7_ra_dtilde_wide_d_upper_sharp (P := P) (S := S) (W := W)
        (a := a) (r := r) ha ha_hi Env hW hsd hr
  have hdpos : 0 < d := dtilde_pos P.X_pos haR hr0
  rw [iteratedDeriv_one]
  have hderiv : deriv (fun s => dtilde P.X s (a : ℝ)) r =
      - d * (d + (a : ℝ)) / (2 * r * ((a : ℝ) + 2 * d)) := by
    simpa [hd_def] using (dtilde_r_hasDerivAt P.X_pos haR hr0).deriv
  rw [hderiv]
  set Num := d * (d + (a : ℝ)) with hNum_def
  set Den := 2 * r * ((a : ℝ) + 2 * d) with hDen_def
  have hDen_pos : 0 < Den := by rw [hDen_def]; positivity
  have habs : |- d * (d + (a : ℝ)) / (2 * r * ((a : ℝ) + 2 * d))| = Num / Den := by
    rw [hNum_def, hDen_def]
    have hnumpos : 0 < d * (d + (a : ℝ)) := by positivity
    have hdenpos : 0 < 2 * r * ((a : ℝ) + 2 * d) := by positivity
    rw [show - d * (d + (a : ℝ)) / (2 * r * ((a : ℝ) + 2 * d))
        = - (d * (d + (a : ℝ)) / (2 * r * ((a : ℝ) + 2 * d))) by ring,
      abs_neg, abs_of_pos (div_pos hnumpos hdenpos)]
  rw [habs]
  have hNum_hi : Num ≤ 2 * d ^ 2 := by
    rw [hNum_def]
    nlinarith [hd_ge_a, hdpos]
  have hDen_lo : 4 * r * d ≤ Den := by
    rw [hDen_def]
    nlinarith [haR, hdpos, hr0]
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt1 * (S.D / S.R) := by
    unfold sec7_ra_Cdt1
    positivity
  have hstep :
      sec7_ra_Cdt1 * (S.D / S.R) * (4 * r * d)
        ≤ sec7_ra_Cdt1 * (S.D / S.R) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have hmain : 2 * d ^ 2 ≤ sec7_ra_Cdt1 * (S.D / S.R) * (4 * r * d) := by
    unfold sec7_ra_Cdt1
    field_simp [ne_of_gt hRpos]
    nlinarith [hd_sharp, hr_lo, hdpos, hDpos, hRpos]
  exact le_trans hNum_hi (le_trans hmain hstep)

/-- Wide-window second derivative bound for `dtilde`. -/
theorem sec7_ra_dtilde_wide_d2 {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    |iteratedDeriv 2 (fun s => dtilde P.X s (a : ℝ)) r|
      ≤ sec7_ra_Cdt2 * (S.D / S.R ^ 2) := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
  have hd_sharp : d ≤ 7 * S.D := by
    simpa [hd_def] using
      sec7_ra_dtilde_wide_d_upper_sharp (P := P) (S := S) (W := W)
        (a := a) (r := r) ha ha_hi Env hW hsd hr
  have hdpos : 0 < d := dtilde_pos P.X_pos haR hr0
  rw [dtilde_r_iteratedDeriv2 P.X_pos haR hr0]
  set Poly := 3 * (a : ℝ) ^ 2 + 10 * (a : ℝ) * d + 10 * d ^ 2 with hPoly_def
  set Num := d * (d + (a : ℝ)) * Poly with hNum_def
  set Den := 4 * r ^ 2 * ((a : ℝ) + 2 * d) ^ 3 with hDen_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  have hDen_pos : 0 < Den := by rw [hDen_def]; positivity
  have hmatch :
      |d * (d + (a : ℝ)) * (3 * (a : ℝ) ^ 2 + 10 * (a : ℝ) * d + 10 * d ^ 2)
          / (4 * r ^ 2 * ((a : ℝ) + 2 * d) ^ 3)| = Num / Den := by
    rw [hNum_def, hDen_def, hPoly_def]
    exact abs_of_pos (div_pos (by positivity) (by positivity))
  rw [hmatch]
  have hf1 : d * (d + (a : ℝ)) ≤ 2 * d ^ 2 := by
    nlinarith [hd_ge_a, hdpos]
  have hf2 : Poly ≤ 23 * d ^ 2 := by
    rw [hPoly_def]
    have hp1 : 3 * (a : ℝ) ^ 2 ≤ 3 * d ^ 2 := by gcongr
    have hp2 : 10 * (a : ℝ) * d ≤ 10 * d ^ 2 := by
      calc 10 * (a : ℝ) * d ≤ 10 * d * d := by gcongr
        _ = 10 * d ^ 2 := by ring
    nlinarith [hp1, hp2]
  have hNum_hi : Num ≤ 46 * d ^ 4 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hf2 (le_of_lt hPoly_pos)
      (by positivity : (0:ℝ) ≤ 2 * d ^ 2)
    calc d * (d + (a : ℝ)) * Poly
        ≤ (2 * d ^ 2) * (23 * d ^ 2) := hmul
      _ = 46 * d ^ 4 := by ring
  have hs_lo_d : 2 * d ≤ (a : ℝ) + 2 * d := by nlinarith [haR]
  have hpow3_lo_d : (2 * d) ^ 3 ≤ ((a : ℝ) + 2 * d) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * d) hs_lo_d 3
  have hDen_lo : 32 * r ^ 2 * d ^ 3 ≤ Den := by
    rw [hDen_def]
    calc 32 * r ^ 2 * d ^ 3 = 4 * r ^ 2 * (2 * d) ^ 3 := by ring
      _ ≤ 4 * r ^ 2 * ((a : ℝ) + 2 * d) ^ 3 := by gcongr
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt2 * (S.D / S.R ^ 2) := by
    unfold sec7_ra_Cdt2
    positivity
  have hstep :
      sec7_ra_Cdt2 * (S.D / S.R ^ 2) * (32 * r ^ 2 * d ^ 3)
        ≤ sec7_ra_Cdt2 * (S.D / S.R ^ 2) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have hr2_lo : ((107 / 18000 : ℝ) * S.R) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (107 / 18000 : ℝ) * S.R) hr_lo 2
  have hd4_le : d ^ 4 ≤ (7 * S.D) * d ^ 3 := by
    calc d ^ 4 = d * d ^ 3 := by ring
      _ ≤ (7 * S.D) * d ^ 3 :=
        mul_le_mul_of_nonneg_right hd_sharp (pow_nonneg hdpos.le 3)
  have hmain :
      46 * d ^ 4 ≤ sec7_ra_Cdt2 * (S.D / S.R ^ 2) * (32 * r ^ 2 * d ^ 3) := by
    unfold sec7_ra_Cdt2
    field_simp [ne_of_gt hRpos]
    nlinarith [hd4_le, hr2_lo, hdpos, hDpos, hRpos]
  exact le_trans hNum_hi (le_trans hmain hstep)

/-- Wide-window third derivative bound for `dtilde`. -/
theorem sec7_ra_dtilde_wide_d3 {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    |iteratedDeriv 3 (fun s => dtilde P.X s (a : ℝ)) r|
      ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
  have hd_sharp : d ≤ 7 * S.D := by
    simpa [hd_def] using
      sec7_ra_dtilde_wide_d_upper_sharp (P := P) (S := S) (W := W)
        (a := a) (r := r) ha ha_hi Env hW hsd hr
  have hdpos : 0 < d := dtilde_pos P.X_pos haR hr0
  rw [dtilde_r_iteratedDeriv3 P.X_pos haR hr0]
  set Poly := 5 * (a : ℝ) ^ 4 + 34 * (a : ℝ) ^ 3 * d + 94 * (a : ℝ) ^ 2 * d ^ 2
      + 120 * (a : ℝ) * d ^ 3 + 60 * d ^ 4 with hPoly_def
  set Num := 3 * d * (d + (a : ℝ)) * Poly with hNum_def
  set Den := 8 * r ^ 3 * ((a : ℝ) + 2 * d) ^ 5 with hDen_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  have hDen_pos : 0 < Den := by rw [hDen_def]; positivity
  have habs :
      |-3 * d * (d + (a : ℝ)) * Poly / Den| = Num / Den := by
    rw [abs_div, hNum_def]
    rw [abs_of_pos hDen_pos]
    congr 1
    have hmul_pos : 0 < 3 * d * (d + (a : ℝ)) * Poly := by positivity
    rw [abs_of_neg (show -3 * d * (d + (a : ℝ)) * Poly < 0 by
      nlinarith [hmul_pos])]
    ring
  have hmatch :
      (-3 * d * (d + (a : ℝ))
        * (5 * (a : ℝ) ^ 4 + 34 * (a : ℝ) ^ 3 * d + 94 * (a : ℝ) ^ 2 * d ^ 2
             + 120 * (a : ℝ) * d ^ 3 + 60 * d ^ 4)
        / (8 * r ^ 3 * ((a : ℝ) + 2 * d) ^ 5))
        = -3 * d * (d + (a : ℝ)) * Poly / Den := by
    rw [hPoly_def, hDen_def]
  rw [hmatch, habs]
  have hf1 : 3 * d * (d + (a : ℝ)) ≤ 6 * d ^ 2 := by
    nlinarith [hd_ge_a, hdpos]
  have hPoly_le_d : Poly ≤ 313 * d ^ 4 := by
    rw [hPoly_def]
    have hp1 : 5 * (a : ℝ) ^ 4 ≤ 5 * d ^ 4 := by gcongr
    have hp2 : 34 * (a : ℝ) ^ 3 * d ≤ 34 * d ^ 4 := by
      calc 34 * (a : ℝ) ^ 3 * d ≤ 34 * d ^ 3 * d := by gcongr
        _ = 34 * d ^ 4 := by ring
    have hp3 : 94 * (a : ℝ) ^ 2 * d ^ 2 ≤ 94 * d ^ 4 := by
      calc 94 * (a : ℝ) ^ 2 * d ^ 2 ≤ 94 * d ^ 2 * d ^ 2 := by gcongr
        _ = 94 * d ^ 4 := by ring
    have hp4 : 120 * (a : ℝ) * d ^ 3 ≤ 120 * d ^ 4 := by
      calc 120 * (a : ℝ) * d ^ 3 ≤ 120 * d * d ^ 3 := by gcongr
        _ = 120 * d ^ 4 := by ring
    nlinarith [hp1, hp2, hp3, hp4]
  have hNum_hi : Num ≤ 1878 * d ^ 6 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hPoly_le_d (by positivity : (0:ℝ) ≤ Poly)
      (by positivity : (0:ℝ) ≤ 6 * d ^ 2)
    calc 3 * d * (d + (a : ℝ)) * Poly
        ≤ (6 * d ^ 2) * (313 * d ^ 4) := hmul
      _ = 1878 * d ^ 6 := by ring
  have hs_lo_d : 2 * d ≤ (a : ℝ) + 2 * d := by nlinarith [haR]
  have hpow5_lo_d : (2 * d) ^ 5 ≤ ((a : ℝ) + 2 * d) ^ 5 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * d) hs_lo_d 5
  have hDen_lo : 256 * r ^ 3 * d ^ 5 ≤ Den := by
    rw [hDen_def]
    calc 256 * r ^ 3 * d ^ 5 = 8 * r ^ 3 * (2 * d) ^ 5 := by ring
      _ ≤ 8 * r ^ 3 * ((a : ℝ) + 2 * d) ^ 5 := by gcongr
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) := by
    unfold sec7_ra_Cdt3
    positivity
  have hstep :
      sec7_ra_Cdt3 * (S.D / S.R ^ 3) * (256 * r ^ 3 * d ^ 5)
        ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have hr169 : S.R / 169 ≤ r := by nlinarith [hr_lo, hRpos]
  have hR3_le : S.R ^ 3 ≤ (169 : ℝ) ^ 3 * r ^ 3 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.R / 169) hr169 3
    rw [show (S.R / 169) ^ 3 = S.R ^ 3 / (169 : ℝ) ^ 3 by ring] at hpow
    rw [div_le_iff₀ (by norm_num : 0 < (169 : ℝ) ^ 3)] at hpow
    nlinarith
  have hmain :
      1878 * d ^ 6 ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) * (256 * r ^ 3 * d ^ 5) := by
    unfold sec7_ra_Cdt3
    field_simp [ne_of_gt hRpos]
    calc
      1878 * d * S.R ^ 3
          ≤ 1878 * (7 * S.D) * S.R ^ 3 := by gcongr
      _ ≤ 1878 * (7 * S.D) * ((169 : ℝ) ^ 3 * r ^ 3) := by gcongr
      _ ≤ (10 ^ 9 : ℝ) * S.D * 256 * r ^ 3 := by
        calc
          1878 * (7 * S.D) * ((169 : ℝ) ^ 3 * r ^ 3)
              = (1878 * 7 * (169 : ℝ) ^ 3) * (S.D * r ^ 3) := by ring
          _ ≤ ((10 ^ 9 : ℝ) * 256) * (S.D * r ^ 3) := by
            have hcoef : 1878 * 7 * (169 : ℝ) ^ 3 ≤ (10 ^ 9 : ℝ) * 256 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
          _ = (10 ^ 9 : ℝ) * S.D * 256 * r ^ 3 := by ring
  exact le_trans hNum_hi (le_trans hmain hstep)

/-- Wide-window fourth derivative bound for `dtilde`. -/
theorem sec7_ra_dtilde_wide_d4 {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    |iteratedDeriv 4 (fun s => dtilde P.X s (a : ℝ)) r|
      ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
  have hd_sharp : d ≤ 7 * S.D := by
    simpa [hd_def] using
      sec7_ra_dtilde_wide_d_upper_sharp (P := P) (S := S) (W := W)
        (a := a) (r := r) ha ha_hi Env hW hsd hr
  have hdpos : 0 < d := dtilde_pos P.X_pos haR hr0
  rw [dtilde_r_iteratedDeriv4 P.X_pos haR hr0]
  set Poly := 35 * (a : ℝ) ^ 6 + 362 * (a : ℝ) ^ 5 * d + 1650 * (a : ℝ) ^ 4 * d ^ 2
      + 4136 * (a : ℝ) ^ 3 * d ^ 3 + 5968 * (a : ℝ) ^ 2 * d ^ 4
      + 4680 * (a : ℝ) * d ^ 5 + 1560 * d ^ 6 with hPoly_def
  set Num := 3 * d * (d + (a : ℝ)) * Poly with hNum_def
  set Den := 16 * r ^ 4 * ((a : ℝ) + 2 * d) ^ 7 with hDen_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  have hDen_pos : 0 < Den := by rw [hDen_def]; positivity
  have habs : |3 * d * (d + (a : ℝ)) * Poly / Den| = Num / Den := by
    rw [hNum_def]
    exact abs_of_pos (div_pos (by positivity) hDen_pos)
  have hmatch :
      (3 * d * (d + (a : ℝ))
        * (35 * (a : ℝ) ^ 6 + 362 * (a : ℝ) ^ 5 * d + 1650 * (a : ℝ) ^ 4 * d ^ 2
           + 4136 * (a : ℝ) ^ 3 * d ^ 3 + 5968 * (a : ℝ) ^ 2 * d ^ 4
           + 4680 * (a : ℝ) * d ^ 5 + 1560 * d ^ 6)
        / (16 * r ^ 4 * ((a : ℝ) + 2 * d) ^ 7))
        = 3 * d * (d + (a : ℝ)) * Poly / Den := by
    rw [hPoly_def, hDen_def]
  rw [hmatch, habs]
  have hf1 : 3 * d * (d + (a : ℝ)) ≤ 6 * d ^ 2 := by
    nlinarith [hd_ge_a, hdpos]
  have hPoly_le_d : Poly ≤ 18391 * d ^ 6 := by
    rw [hPoly_def]
    have hp1 : 35 * (a : ℝ) ^ 6 ≤ 35 * d ^ 6 := by gcongr
    have hp2 : 362 * (a : ℝ) ^ 5 * d ≤ 362 * d ^ 6 := by
      calc 362 * (a : ℝ) ^ 5 * d ≤ 362 * d ^ 5 * d := by gcongr
        _ = 362 * d ^ 6 := by ring
    have hp3 : 1650 * (a : ℝ) ^ 4 * d ^ 2 ≤ 1650 * d ^ 6 := by
      calc 1650 * (a : ℝ) ^ 4 * d ^ 2 ≤ 1650 * d ^ 4 * d ^ 2 := by gcongr
        _ = 1650 * d ^ 6 := by ring
    have hp4 : 4136 * (a : ℝ) ^ 3 * d ^ 3 ≤ 4136 * d ^ 6 := by
      calc 4136 * (a : ℝ) ^ 3 * d ^ 3 ≤ 4136 * d ^ 3 * d ^ 3 := by gcongr
        _ = 4136 * d ^ 6 := by ring
    have hp5 : 5968 * (a : ℝ) ^ 2 * d ^ 4 ≤ 5968 * d ^ 6 := by
      calc 5968 * (a : ℝ) ^ 2 * d ^ 4 ≤ 5968 * d ^ 2 * d ^ 4 := by gcongr
        _ = 5968 * d ^ 6 := by ring
    have hp6 : 4680 * (a : ℝ) * d ^ 5 ≤ 4680 * d ^ 6 := by
      calc 4680 * (a : ℝ) * d ^ 5 ≤ 4680 * d * d ^ 5 := by gcongr
        _ = 4680 * d ^ 6 := by ring
    nlinarith [hp1, hp2, hp3, hp4, hp5, hp6]
  have hNum_hi : Num ≤ 110346 * d ^ 8 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hPoly_le_d (by positivity : (0:ℝ) ≤ Poly)
      (by positivity : (0:ℝ) ≤ 6 * d ^ 2)
    calc 3 * d * (d + (a : ℝ)) * Poly
        ≤ (6 * d ^ 2) * (18391 * d ^ 6) := hmul
      _ = 110346 * d ^ 8 := by ring
  have hs_lo_d : 2 * d ≤ (a : ℝ) + 2 * d := by nlinarith [haR]
  have hpow7_lo_d : (2 * d) ^ 7 ≤ ((a : ℝ) + 2 * d) ^ 7 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * d) hs_lo_d 7
  have hDen_lo : 2048 * r ^ 4 * d ^ 7 ≤ Den := by
    rw [hDen_def]
    calc 2048 * r ^ 4 * d ^ 7 = 16 * r ^ 4 * (2 * d) ^ 7 := by ring
      _ ≤ 16 * r ^ 4 * ((a : ℝ) + 2 * d) ^ 7 := by gcongr
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) := by
    unfold sec7_ra_Cdt4
    positivity
  have hstep :
      sec7_ra_Cdt4 * (S.D / S.R ^ 4) * (2048 * r ^ 4 * d ^ 7)
        ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have hr169 : S.R / 169 ≤ r := by nlinarith [hr_lo, hRpos]
  have hR4_le : S.R ^ 4 ≤ (169 : ℝ) ^ 4 * r ^ 4 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.R / 169) hr169 4
    rw [show (S.R / 169) ^ 4 = S.R ^ 4 / (169 : ℝ) ^ 4 by ring] at hpow
    rw [div_le_iff₀ (by norm_num : 0 < (169 : ℝ) ^ 4)] at hpow
    nlinarith
  have hmain :
      110346 * d ^ 8 ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) * (2048 * r ^ 4 * d ^ 7) := by
    unfold sec7_ra_Cdt4
    field_simp [ne_of_gt hRpos]
    calc
      110346 * d * S.R ^ 4
          ≤ 110346 * (7 * S.D) * S.R ^ 4 := by gcongr
      _ ≤ 110346 * (7 * S.D) * ((169 : ℝ) ^ 4 * r ^ 4) := by gcongr
      _ ≤ (10 ^ 12 : ℝ) * S.D * 2048 * r ^ 4 := by
        calc
          110346 * (7 * S.D) * ((169 : ℝ) ^ 4 * r ^ 4)
              = (110346 * 7 * (169 : ℝ) ^ 4) * (S.D * r ^ 4) := by ring
          _ ≤ ((10 ^ 12 : ℝ) * 2048) * (S.D * r ^ 4) := by
            have hcoef : 110346 * 7 * (169 : ℝ) ^ 4 ≤ (10 ^ 12 : ℝ) * 2048 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
          _ = (10 ^ 12 : ℝ) * S.D * 2048 * r ^ 4 := by ring
  exact le_trans hNum_hi (le_trans hmain hstep)

/-- Wide-window fifth derivative bound for `dtilde`. -/
theorem sec7_ra_dtilde_wide_d5 {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    |iteratedDeriv 5 (fun s => dtilde P.X s (a : ℝ)) r|
      ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hr_lo, _hr_hi⟩ :=
    sec7_dtilde_wide_rWinWide_core (P := P) (S := S) (W := W) (r := r)
      Env hW c₀ Cu hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < (107 / 18000 : ℝ) * S.R) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
  have hd_sharp : d ≤ 7 * S.D := by
    simpa [hd_def] using
      sec7_ra_dtilde_wide_d_upper_sharp (P := P) (S := S) (W := W)
        (a := a) (r := r) ha ha_hi Env hW hsd hr
  have hdpos : 0 < d := dtilde_pos P.X_pos haR hr0
  rw [dtilde_r_iteratedDeriv5 P.X_pos haR hr0]
  set Poly := 63 * (a : ℝ) ^ 8 + 878 * (a : ℝ) ^ 7 * d + 5594 * (a : ℝ) ^ 6 * d ^ 2
      + 20904 * (a : ℝ) ^ 5 * d ^ 3 + 49740 * (a : ℝ) ^ 4 * d ^ 4
      + 76848 * (a : ℝ) ^ 3 * d ^ 5 + 75120 * (a : ℝ) ^ 2 * d ^ 6
      + 42432 * (a : ℝ) * d ^ 7 + 10608 * d ^ 8 with hPoly_def
  set Num := 15 * d * (d + (a : ℝ)) * Poly with hNum_def
  set Den := 32 * r ^ 5 * ((a : ℝ) + 2 * d) ^ 9 with hDen_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  have hDen_pos : 0 < Den := by rw [hDen_def]; positivity
  have habs :
      |-15 * d * (d + (a : ℝ)) * Poly / Den| = Num / Den := by
    rw [abs_div, hNum_def]
    rw [abs_of_pos hDen_pos]
    congr 1
    have hmul_pos : 0 < 15 * d * (d + (a : ℝ)) * Poly := by positivity
    rw [abs_of_neg (show -15 * d * (d + (a : ℝ)) * Poly < 0 by
      nlinarith [hmul_pos])]
    ring
  have hmatch :
      (-15 * d * (d + (a : ℝ))
        * (63 * (a : ℝ) ^ 8 + 878 * (a : ℝ) ^ 7 * d + 5594 * (a : ℝ) ^ 6 * d ^ 2
           + 20904 * (a : ℝ) ^ 5 * d ^ 3 + 49740 * (a : ℝ) ^ 4 * d ^ 4
           + 76848 * (a : ℝ) ^ 3 * d ^ 5 + 75120 * (a : ℝ) ^ 2 * d ^ 6
           + 42432 * (a : ℝ) * d ^ 7 + 10608 * d ^ 8)
        / (32 * r ^ 5 * ((a : ℝ) + 2 * d) ^ 9))
        = -15 * d * (d + (a : ℝ)) * Poly / Den := by
    rw [hPoly_def, hDen_def]
  rw [hmatch, habs]
  have hf1 : 15 * d * (d + (a : ℝ)) ≤ 30 * d ^ 2 := by
    nlinarith [hd_ge_a, hdpos]
  have hPoly_le_d : Poly ≤ 282187 * d ^ 8 := by
    rw [hPoly_def]
    have hp1 : 63 * (a : ℝ) ^ 8 ≤ 63 * d ^ 8 := by gcongr
    have hp2 : 878 * (a : ℝ) ^ 7 * d ≤ 878 * d ^ 8 := by
      calc 878 * (a : ℝ) ^ 7 * d ≤ 878 * d ^ 7 * d := by gcongr
        _ = 878 * d ^ 8 := by ring
    have hp3 : 5594 * (a : ℝ) ^ 6 * d ^ 2 ≤ 5594 * d ^ 8 := by
      calc 5594 * (a : ℝ) ^ 6 * d ^ 2 ≤ 5594 * d ^ 6 * d ^ 2 := by gcongr
        _ = 5594 * d ^ 8 := by ring
    have hp4 : 20904 * (a : ℝ) ^ 5 * d ^ 3 ≤ 20904 * d ^ 8 := by
      calc 20904 * (a : ℝ) ^ 5 * d ^ 3 ≤ 20904 * d ^ 5 * d ^ 3 := by gcongr
        _ = 20904 * d ^ 8 := by ring
    have hp5 : 49740 * (a : ℝ) ^ 4 * d ^ 4 ≤ 49740 * d ^ 8 := by
      calc 49740 * (a : ℝ) ^ 4 * d ^ 4 ≤ 49740 * d ^ 4 * d ^ 4 := by gcongr
        _ = 49740 * d ^ 8 := by ring
    have hp6 : 76848 * (a : ℝ) ^ 3 * d ^ 5 ≤ 76848 * d ^ 8 := by
      calc 76848 * (a : ℝ) ^ 3 * d ^ 5 ≤ 76848 * d ^ 3 * d ^ 5 := by gcongr
        _ = 76848 * d ^ 8 := by ring
    have hp7 : 75120 * (a : ℝ) ^ 2 * d ^ 6 ≤ 75120 * d ^ 8 := by
      calc 75120 * (a : ℝ) ^ 2 * d ^ 6 ≤ 75120 * d ^ 2 * d ^ 6 := by gcongr
        _ = 75120 * d ^ 8 := by ring
    have hp8 : 42432 * (a : ℝ) * d ^ 7 ≤ 42432 * d ^ 8 := by
      calc 42432 * (a : ℝ) * d ^ 7 ≤ 42432 * d * d ^ 7 := by gcongr
        _ = 42432 * d ^ 8 := by ring
    nlinarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8]
  have hNum_hi : Num ≤ 8465610 * d ^ 10 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hPoly_le_d (by positivity : (0:ℝ) ≤ Poly)
      (by positivity : (0:ℝ) ≤ 30 * d ^ 2)
    calc 15 * d * (d + (a : ℝ)) * Poly
        ≤ (30 * d ^ 2) * (282187 * d ^ 8) := hmul
      _ = 8465610 * d ^ 10 := by ring
  have hs_lo_d : 2 * d ≤ (a : ℝ) + 2 * d := by nlinarith [haR]
  have hpow9_lo_d : (2 * d) ^ 9 ≤ ((a : ℝ) + 2 * d) ^ 9 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * d) hs_lo_d 9
  have hDen_lo : 16384 * r ^ 5 * d ^ 9 ≤ Den := by
    rw [hDen_def]
    calc 16384 * r ^ 5 * d ^ 9 = 32 * r ^ 5 * (2 * d) ^ 9 := by ring
      _ ≤ 32 * r ^ 5 * ((a : ℝ) + 2 * d) ^ 9 := by gcongr
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) := by
    unfold sec7_ra_Cdt5
    positivity
  have hstep :
      sec7_ra_Cdt5 * (S.D / S.R ^ 5) * (16384 * r ^ 5 * d ^ 9)
        ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have hr169 : S.R / 169 ≤ r := by nlinarith [hr_lo, hRpos]
  have hR5_le : S.R ^ 5 ≤ (169 : ℝ) ^ 5 * r ^ 5 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.R / 169) hr169 5
    rw [show (S.R / 169) ^ 5 = S.R ^ 5 / (169 : ℝ) ^ 5 by ring] at hpow
    rw [div_le_iff₀ (by norm_num : 0 < (169 : ℝ) ^ 5)] at hpow
    nlinarith
  have hmain :
      8465610 * d ^ 10 ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) * (16384 * r ^ 5 * d ^ 9) := by
    unfold sec7_ra_Cdt5
    field_simp [ne_of_gt hRpos]
    calc
      8465610 * d * S.R ^ 5
          ≤ 8465610 * (7 * S.D) * S.R ^ 5 := by gcongr
      _ ≤ 8465610 * (7 * S.D) * ((169 : ℝ) ^ 5 * r ^ 5) := by gcongr
      _ ≤ (10 ^ 15 : ℝ) * S.D * 16384 * r ^ 5 := by
        calc
          8465610 * (7 * S.D) * ((169 : ℝ) ^ 5 * r ^ 5)
              = (8465610 * 7 * (169 : ℝ) ^ 5) * (S.D * r ^ 5) := by ring
          _ ≤ ((10 ^ 15 : ℝ) * 16384) * (S.D * r ^ 5) := by
            have hcoef : 8465610 * 7 * (169 : ℝ) ^ 5 ≤ (10 ^ 15 : ℝ) * 16384 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
          _ = (10 ^ 15 : ℝ) * S.D * 16384 * r ^ 5 := by ring
  exact le_trans hNum_hi (le_trans hmain hstep)

end Squarefree
