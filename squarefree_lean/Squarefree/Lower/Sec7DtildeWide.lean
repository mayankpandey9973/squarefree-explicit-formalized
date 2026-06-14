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

def sec7_ra_Cdt1 : ℝ := 10 ^ 10
def sec7_ra_Cdt2 : ℝ := 10 ^ 20
def sec7_ra_Cdt3 : ℝ := 10 ^ 30
def sec7_ra_Cdt4 : ℝ := 10 ^ 40
def sec7_ra_Cdt5 : ℝ := 10 ^ 50

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
  obtain ⟨hr_lo, _hr_hi⟩ := sec7_ra_wide_r_bounds (P := P) (S := S) (W := W)
    (r := r) Env hW hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < S.R / 200) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
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
  have hNum_hi : Num ≤ 3200 * S.D ^ 2 := by
    rw [hNum_def]
    nlinarith [hd_hi, hd_ge_a, hdpos, hDpos]
  have hDen_lo : S.R * S.D / 1000 ≤ Den := by
    rw [hDen_def]
    have hs_lo : S.D / 10 ≤ (a : ℝ) + 2 * d := by nlinarith [hd_lo, haR]
    nlinarith [hr_lo, hs_lo, hRpos, hDpos, hr0]
  rw [div_le_iff₀ hDen_pos]
  field_simp [ne_of_gt hRpos]
  norm_num [sec7_ra_Cdt1]
  nlinarith [hNum_hi, hDen_lo, hDpos, hRpos]

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
  obtain ⟨hr_lo, _hr_hi⟩ := sec7_ra_wide_r_bounds (P := P) (S := S) (W := W)
    (r := r) Env hW hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < S.R / 200) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
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
  have hf1 : d * (d + (a : ℝ)) ≤ 3200 * S.D ^ 2 := by
    nlinarith [hd_hi, hd_ge_a, hdpos, hDpos]
  have hf2 : Poly ≤ 36800 * S.D ^ 2 := by
    rw [hPoly_def]
    nlinarith [hd_hi, hd_ge_a, hdpos, hDpos, haR]
  have hNum_hi : Num ≤ 120000000 * S.D ^ 4 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hf2 (le_of_lt hPoly_pos)
      (by positivity : (0:ℝ) ≤ 3200 * S.D ^ 2)
    calc d * (d + (a : ℝ)) * Poly
        ≤ (3200 * S.D ^ 2) * (36800 * S.D ^ 2) := hmul
      _ ≤ 120000000 * S.D ^ 4 := by nlinarith [pow_pos hDpos 4]
  have hr2_lo : S.R ^ 2 / 40000 ≤ r ^ 2 := by nlinarith [hr_lo, hr0, hRpos]
  have hs_lo : S.D / 10 ≤ (a : ℝ) + 2 * d := by nlinarith [hd_lo, haR]
  have hpow3_lo : S.D ^ 3 / 1000 ≤ ((a : ℝ) + 2 * d) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 10) hs_lo 3
    calc S.D ^ 3 / 1000 = (S.D / 10) ^ 3 := by ring
      _ ≤ ((a : ℝ) + 2 * d) ^ 3 := this
  have hDen_lo : S.R ^ 2 * S.D ^ 3 / 10000000 ≤ Den := by
    rw [hDen_def]
    have hmul := mul_le_mul hr2_lo hpow3_lo (by positivity) (by positivity)
    calc S.R ^ 2 * S.D ^ 3 / 10000000
        ≤ 4 * ((S.R ^ 2 / 40000) * (S.D ^ 3 / 1000)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith [mul_pos (pow_pos hRpos 2) (pow_pos hDpos 3)]
      _ ≤ 4 * (r ^ 2 * ((a : ℝ) + 2 * d) ^ 3) := by nlinarith [hmul]
      _ = 4 * r ^ 2 * ((a : ℝ) + 2 * d) ^ 3 := by ring
  rw [div_le_iff₀ hDen_pos]
  field_simp [ne_of_gt hRpos]
  norm_num [sec7_ra_Cdt2]
  nlinarith [hNum_hi, hDen_lo, hDpos, hRpos]

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
  obtain ⟨hr_lo, _hr_hi⟩ := sec7_ra_wide_r_bounds (P := P) (S := S) (W := W)
    (r := r) Env hW hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < S.R / 200) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
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
  have hf1 : 3 * d * (d + (a : ℝ)) ≤ 9600 * S.D ^ 2 := by
    nlinarith [hd_hi, hd_ge_a, hdpos, hDpos]
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
  have hd4_hi : d ^ 4 ≤ (40 * S.D) ^ 4 :=
    pow_le_pow_left₀ hdpos.le hd_hi 4
  have hf2 : Poly ≤ 802000000 * S.D ^ 4 := by
    nlinarith [hPoly_le_d, hd4_hi, pow_pos hDpos 4]
  have hNum_hi : Num ≤ 8000000000000 * S.D ^ 6 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hf2 (by positivity : (0:ℝ) ≤ Poly)
      (by positivity : (0:ℝ) ≤ 9600 * S.D ^ 2)
    calc 3 * d * (d + (a : ℝ)) * Poly
        ≤ (9600 * S.D ^ 2) * (802000000 * S.D ^ 4) := hmul
      _ ≤ 8000000000000 * S.D ^ 6 := by nlinarith [pow_pos hDpos 6]
  have hr3_lo : S.R ^ 3 / 8000000 ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.R / 200) hr_lo 3
    calc S.R ^ 3 / 8000000 = (S.R / 200) ^ 3 := by ring
      _ ≤ r ^ 3 := this
  have hs_lo : S.D / 10 ≤ (a : ℝ) + 2 * d := by nlinarith [hd_lo, haR]
  have hpow5_lo : S.D ^ 5 / 100000 ≤ ((a : ℝ) + 2 * d) ^ 5 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 10) hs_lo 5
    calc S.D ^ 5 / 100000 = (S.D / 10) ^ 5 := by ring
      _ ≤ ((a : ℝ) + 2 * d) ^ 5 := this
  have hDen_lo : S.R ^ 3 * S.D ^ 5 / 100000000000 ≤ Den := by
    rw [hDen_def]
    have hmul := mul_le_mul hr3_lo hpow5_lo (by positivity) (by positivity)
    calc S.R ^ 3 * S.D ^ 5 / 100000000000
        ≤ 8 * ((S.R ^ 3 / 8000000) * (S.D ^ 5 / 100000)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith [mul_pos (pow_pos hRpos 3) (pow_pos hDpos 5)]
      _ ≤ 8 * (r ^ 3 * ((a : ℝ) + 2 * d) ^ 5) := by nlinarith [hmul]
      _ = 8 * r ^ 3 * ((a : ℝ) + 2 * d) ^ 5 := by ring
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) := by
    unfold sec7_ra_Cdt3
    positivity
  have hstep :
      sec7_ra_Cdt3 * (S.D / S.R ^ 3) *
          (S.R ^ 3 * S.D ^ 5 / 100000000000)
        ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have heq :
      sec7_ra_Cdt3 * (S.D / S.R ^ 3) *
          (S.R ^ 3 * S.D ^ 5 / 100000000000)
        = 10000000000000000000 * S.D ^ 6 := by
    norm_num [sec7_ra_Cdt3]
    field_simp [ne_of_gt hRpos]
    ring
  have hle : (8000000000000 : ℝ) * S.D ^ 6 ≤
      10000000000000000000 * S.D ^ 6 := by
    nlinarith [pow_pos hDpos 6]
  calc Num ≤ 8000000000000 * S.D ^ 6 := hNum_hi
    _ ≤ 10000000000000000000 * S.D ^ 6 := hle
    _ = sec7_ra_Cdt3 * (S.D / S.R ^ 3) *
          (S.R ^ 3 * S.D ^ 5 / 100000000000) := by rw [heq]
    _ ≤ sec7_ra_Cdt3 * (S.D / S.R ^ 3) * Den := hstep

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
  obtain ⟨hr_lo, _hr_hi⟩ := sec7_ra_wide_r_bounds (P := P) (S := S) (W := W)
    (r := r) Env hW hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < S.R / 200) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
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
  have hf1 : 3 * d * (d + (a : ℝ)) ≤ 9600 * S.D ^ 2 := by
    nlinarith [hd_hi, hd_ge_a, hdpos, hDpos]
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
  have hd6_hi : d ^ 6 ≤ (40 * S.D) ^ 6 :=
    pow_le_pow_left₀ hdpos.le hd_hi 6
  have hf2 : Poly ≤ 80000000000000 * S.D ^ 6 := by
    nlinarith [hPoly_le_d, hd6_hi, pow_pos hDpos 6]
  have hNum_hi : Num ≤ 800000000000000000 * S.D ^ 8 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hf2 (by positivity : (0:ℝ) ≤ Poly)
      (by positivity : (0:ℝ) ≤ 9600 * S.D ^ 2)
    calc 3 * d * (d + (a : ℝ)) * Poly
        ≤ (9600 * S.D ^ 2) * (80000000000000 * S.D ^ 6) := hmul
      _ ≤ 800000000000000000 * S.D ^ 8 := by nlinarith [pow_pos hDpos 8]
  have hr4_lo : S.R ^ 4 / 1600000000 ≤ r ^ 4 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.R / 200) hr_lo 4
    calc S.R ^ 4 / 1600000000 = (S.R / 200) ^ 4 := by ring
      _ ≤ r ^ 4 := this
  have hs_lo : S.D / 10 ≤ (a : ℝ) + 2 * d := by nlinarith [hd_lo, haR]
  have hpow7_lo : S.D ^ 7 / 10000000 ≤ ((a : ℝ) + 2 * d) ^ 7 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 10) hs_lo 7
    calc S.D ^ 7 / 10000000 = (S.D / 10) ^ 7 := by ring
      _ ≤ ((a : ℝ) + 2 * d) ^ 7 := this
  have hDen_lo : S.R ^ 4 * S.D ^ 7 / 1000000000000000 ≤ Den := by
    rw [hDen_def]
    have hmul := mul_le_mul hr4_lo hpow7_lo (by positivity) (by positivity)
    calc S.R ^ 4 * S.D ^ 7 / 1000000000000000
        ≤ 16 * ((S.R ^ 4 / 1600000000) * (S.D ^ 7 / 10000000)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith [mul_pos (pow_pos hRpos 4) (pow_pos hDpos 7)]
      _ ≤ 16 * (r ^ 4 * ((a : ℝ) + 2 * d) ^ 7) := by nlinarith [hmul]
      _ = 16 * r ^ 4 * ((a : ℝ) + 2 * d) ^ 7 := by ring
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) := by
    unfold sec7_ra_Cdt4
    positivity
  have hstep :
      sec7_ra_Cdt4 * (S.D / S.R ^ 4) *
          (S.R ^ 4 * S.D ^ 7 / 1000000000000000)
        ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have heq :
      sec7_ra_Cdt4 * (S.D / S.R ^ 4) *
          (S.R ^ 4 * S.D ^ 7 / 1000000000000000)
        = 10000000000000000000000000 * S.D ^ 8 := by
    norm_num [sec7_ra_Cdt4]
    field_simp [ne_of_gt hRpos]
    ring
  have hle : (800000000000000000 : ℝ) * S.D ^ 8 ≤
      10000000000000000000000000 * S.D ^ 8 := by
    nlinarith [pow_pos hDpos 8]
  calc Num ≤ 800000000000000000 * S.D ^ 8 := hNum_hi
    _ ≤ 10000000000000000000000000 * S.D ^ 8 := hle
    _ = sec7_ra_Cdt4 * (S.D / S.R ^ 4) *
          (S.R ^ 4 * S.D ^ 7 / 1000000000000000) := by rw [heq]
    _ ≤ sec7_ra_Cdt4 * (S.D / S.R ^ 4) * Den := hstep

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
  obtain ⟨hr_lo, _hr_hi⟩ := sec7_ra_wide_r_bounds (P := P) (S := S) (W := W)
    (r := r) Env hW hsd hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < S.R / 200) hr_lo
  set d := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hd_lo0, hd_ge_a0, hd_hi0⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hd_lo : S.D / 20 ≤ d := by simpa [hd_def] using hd_lo0
  have hd_ge_a : (a : ℝ) ≤ d := by simpa [hd_def] using hd_ge_a0
  have hd_hi : d ≤ 40 * S.D := by simpa [hd_def] using hd_hi0
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
  have hf1 : 15 * d * (d + (a : ℝ)) ≤ 48000 * S.D ^ 2 := by
    nlinarith [hd_hi, hd_ge_a, hdpos, hDpos]
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
  have hd8_hi : d ^ 8 ≤ (40 * S.D) ^ 8 :=
    pow_le_pow_left₀ hdpos.le hd_hi 8
  have hf2 : Poly ≤ 2000000000000000000 * S.D ^ 8 := by
    nlinarith [hPoly_le_d, hd8_hi, pow_pos hDpos 8]
  have hNum_hi : Num ≤ 100000000000000000000000 * S.D ^ 10 := by
    rw [hNum_def]
    have hmul := mul_le_mul hf1 hf2 (by positivity : (0:ℝ) ≤ Poly)
      (by positivity : (0:ℝ) ≤ 48000 * S.D ^ 2)
    calc 15 * d * (d + (a : ℝ)) * Poly
        ≤ (48000 * S.D ^ 2) * (2000000000000000000 * S.D ^ 8) := hmul
      _ ≤ 100000000000000000000000 * S.D ^ 10 := by nlinarith [pow_pos hDpos 10]
  have hr5_lo : S.R ^ 5 / 320000000000 ≤ r ^ 5 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.R / 200) hr_lo 5
    calc S.R ^ 5 / 320000000000 = (S.R / 200) ^ 5 := by ring
      _ ≤ r ^ 5 := this
  have hs_lo : S.D / 10 ≤ (a : ℝ) + 2 * d := by nlinarith [hd_lo, haR]
  have hpow9_lo : S.D ^ 9 / 1000000000 ≤ ((a : ℝ) + 2 * d) ^ 9 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 10) hs_lo 9
    calc S.D ^ 9 / 1000000000 = (S.D / 10) ^ 9 := by ring
      _ ≤ ((a : ℝ) + 2 * d) ^ 9 := this
  have hDen_lo : S.R ^ 5 * S.D ^ 9 / 10000000000000000000 ≤ Den := by
    rw [hDen_def]
    have hmul := mul_le_mul hr5_lo hpow9_lo (by positivity) (by positivity)
    calc S.R ^ 5 * S.D ^ 9 / 10000000000000000000
        ≤ 32 * ((S.R ^ 5 / 320000000000) * (S.D ^ 9 / 1000000000)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith [mul_pos (pow_pos hRpos 5) (pow_pos hDpos 9)]
      _ ≤ 32 * (r ^ 5 * ((a : ℝ) + 2 * d) ^ 9) := by nlinarith [hmul]
      _ = 32 * r ^ 5 * ((a : ℝ) + 2 * d) ^ 9 := by ring
  rw [div_le_iff₀ hDen_pos]
  have hmul_nonneg : 0 ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) := by
    unfold sec7_ra_Cdt5
    positivity
  have hstep :
      sec7_ra_Cdt5 * (S.D / S.R ^ 5) *
          (S.R ^ 5 * S.D ^ 9 / 10000000000000000000)
        ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) * Den :=
    mul_le_mul_of_nonneg_left hDen_lo hmul_nonneg
  have heq :
      sec7_ra_Cdt5 * (S.D / S.R ^ 5) *
          (S.R ^ 5 * S.D ^ 9 / 10000000000000000000)
        = 10000000000000000000000000000000 * S.D ^ 10 := by
    norm_num [sec7_ra_Cdt5]
    field_simp [ne_of_gt hRpos]
    ring
  have hle : (100000000000000000000000 : ℝ) * S.D ^ 10 ≤
      10000000000000000000000000000000 * S.D ^ 10 := by
    nlinarith [pow_pos hDpos 10]
  calc Num ≤ 100000000000000000000000 * S.D ^ 10 := hNum_hi
    _ ≤ 10000000000000000000000000000000 * S.D ^ 10 := hle
    _ = sec7_ra_Cdt5 * (S.D / S.R ^ 5) *
          (S.R ^ 5 * S.D ^ 9 / 10000000000000000000) := by rw [heq]
    _ ≤ sec7_ra_Cdt5 * (S.D / S.R ^ 5) * Den := hstep

end Squarefree
