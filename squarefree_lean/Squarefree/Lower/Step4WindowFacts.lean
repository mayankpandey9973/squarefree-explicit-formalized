import Squarefree.Lower.DefectClose
import Squarefree.Lower.Step4BandPay
import Squarefree.Lower.Step4Confine
import Squarefree.Lower.Step4Capstone

/-!
# §5 Step-4 per-r window-bundle facts (writeup facts 16–23)

Producers for the per-`r` window bundle: the discrete-defect slope lower bound
(`dstar_slope_lo`), the ε-form `d̃`-window (`dtilde_eps_window`), monotone decrease and
placement of the witness defects (`dstar_decreasing`, `dstar_placement`), and the regime
smallness `step4ErrU ≤ 1/4` (`errB_quarter`) discharging the capstone budget.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

variable {P : Globals} {S : Scale P}

/-- Twice the `dtilde_close` tolerance is at most `B/(2·10⁶)` (margin `≥ 10²⁹`, from
`Δ ≥ 10¹⁵·G⁴U²⁰ ≥ 10⁴⁸`). -/
private theorem two_tol_le (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    2 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) ≤ S.B / 2000000 := by
  have hGΩ : (0:ℝ) < P.G * S.Ω ^ 3 := by have := P.G_pos; have := S.Ω_pos; positivity
  have hU20 : (10:ℝ) ^ 33 ≤ P.U ^ 20 := by
    calc (10:ℝ) ^ 33 ≤ P.U := hUbig
      _ = P.U ^ 1 := (pow_one _).symm
      _ ≤ P.U ^ 20 := pow_le_pow_right₀ hU1 (by norm_num)
  have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
  have hΔbig : (10:ℝ) ^ 48 ≤ S.Δ := by
    have h := mul_le_mul hG4 hU20 (by positivity) (by linarith)
    calc (10:ℝ) ^ 48 = 10 ^ 15 * (1 * 10 ^ 33) := by norm_num
      _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by nlinarith [h]
      _ ≤ S.Δ := hDeW
  have key : 4 * 10 ^ 18 * S.Δ ≤ S.Δ ^ 2 := by nlinarith [hΔbig, S.Δ_pos]
  have lhs_eq : 2 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
      = 2 * 1000000000000 * S.Δ / (P.G * S.Ω ^ 3) := by ring
  rw [lhs_eq, Scale.B, div_div, div_le_div_iff₀ hGΩ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right key hGΩ.le]

/-- Discrete slope vs `b̃`: if `d₁ ≈ d̃(r)`, `d₂ ≈ d̃(r+ℓ)` within `tol` and `ℓ ≥ 1`, then
`|(d₂−d₁)/ℓ − b̃ₐ(r)| ≤ 2·tol`. -/
private theorem slope_bt_close {a r ℓ d₁ d₂ tol : ℝ} (hℓ1 : 1 ≤ ℓ) (htol : 0 ≤ tol)
    (h1c : |d₁ - dtilde P.X r a| ≤ tol) (h2c : |d₂ - dtilde P.X (r + ℓ) a| ≤ tol) :
    |(d₂ - d₁) / ℓ - bt P.X a ℓ r| ≤ 2 * tol := by
  have hℓpos : (0:ℝ) < ℓ := lt_of_lt_of_le one_pos hℓ1
  have heq : (d₂ - d₁) / ℓ - bt P.X a ℓ r
      = ((d₂ - dtilde P.X (r + ℓ) a) - (d₁ - dtilde P.X r a)) / ℓ := by
    rw [bt]; field_simp; ring
  rw [heq, abs_div, abs_of_pos hℓpos]
  have hnum : |(d₂ - dtilde P.X (r + ℓ) a) - (d₁ - dtilde P.X r a)| ≤ 2 * tol := by
    calc |(d₂ - dtilde P.X (r + ℓ) a) - (d₁ - dtilde P.X r a)|
        ≤ |d₂ - dtilde P.X (r + ℓ) a| + |d₁ - dtilde P.X r a| := abs_sub _ _
      _ ≤ tol + tol := add_le_add h2c h1c
      _ = 2 * tol := by ring
  rw [div_le_iff₀ hℓpos]
  nlinarith [abs_nonneg ((d₂ - dtilde P.X (r + ℓ) a) - (d₁ - dtilde P.X r a))]

/-- **Fact 23 (slope lower bound).**  Two `RaWitness`-style defects `d₁` at `r`, `d₂` at
`r+ℓ₁` have discrete slope `|(d₂−d₁)/ℓ₁| ≥ B/(2·10⁶)`. -/
theorem dstar_slope_lo {a : ℤ} {r ℓ₁ : ℕ} {d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ : 0 < ℓ₁)
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hrl_hi : (r : ℝ) + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hd1D : S.D ≤ (d₁ : ℝ)) (hd1_2D : (d₁ : ℝ) ≤ 2 * S.D)
    (hd2D : S.D ≤ (d₂ : ℝ)) (hd2_2D : (d₂ : ℝ) ≤ 2 * S.D)
    (hrd1 : |Rfun P.X (a : ℝ) (d₁ : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hrd2 : |Rfun P.X (a : ℝ) (d₂ : ℝ) - ((r : ℝ) + (ℓ₁ : ℝ))| ≤ 14 * P.H / S.D)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    S.B / 2000000 ≤ |((d₂ : ℝ) - (d₁ : ℝ)) / (ℓ₁ : ℝ)| := by
  have hℓ1 : (1:ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ
  have hℓpos : (0:ℝ) < (ℓ₁ : ℝ) := lt_of_lt_of_le one_pos hℓ1
  have hr_hi : (r : ℝ) ≤ 16 * S.R := by linarith
  have hrl_lo : (1/72) * S.R ≤ (r : ℝ) + (ℓ₁ : ℝ) := by linarith
  have haR : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have htol0 : (0:ℝ) ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
    have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hc1 := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
    hd1D hd1_2D hrd1
  have hc2 := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hrl_lo hrl_hi
    hd2D hd2_2D hrd2
  obtain ⟨_, hbt_lo, _⟩ := bt_abs_bounds (P := P) (S := S) (a := (a:ℝ)) (ℓ := (ℓ₁:ℝ))
    (r := (r:ℝ)) hAD haR hℓpos ha_lo ha_hi hr_lo hrl_hi
  have hdiff := slope_bt_close (P := P) hℓ1 htol0 hc1 hc2
  have h2tol := two_tol_le (P := P) (S := S) hG1 hU1 hUbig hDeW
  -- `|s| ≥ |b̃| − |s − b̃| ≥ B/10⁶ − B/(2·10⁶) = B/(2·10⁶)`
  have htri : |bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ)|
      ≤ |((d₂:ℝ) - (d₁:ℝ)) / (ℓ₁:ℝ)|
        + |((d₂:ℝ) - (d₁:ℝ)) / (ℓ₁:ℝ) - bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ)| := by
    have h := abs_sub_abs_le_abs_sub (bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ))
      (((d₂:ℝ) - (d₁:ℝ)) / (ℓ₁:ℝ))
    have h2 : |bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ) - ((d₂:ℝ) - (d₁:ℝ)) / (ℓ₁:ℝ)|
        = |((d₂:ℝ) - (d₁:ℝ)) / (ℓ₁:ℝ) - bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ)| := abs_sub_comm _ _
    linarith [h, h2.le]
  have hB6 : S.B / 1000000 - S.B / 2000000 = S.B / 2000000 := by ring
  linarith [htri, hbt_lo, hdiff, h2tol]

/-- **Fact 22 (ε-form `d̃`-window).**  A `RaWitness` defect `d ∈ [D,2D]` at `r` pins
`d̃ₐ(r)` to `[D(1−10⁻⁹), 2D(1+10⁻⁹)]`. -/
theorem dtilde_eps_window {a : ℤ} {r d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hrd : |Rfun P.X (a : ℝ) d - r| ≤ 14 * P.H / S.D)
    (hG1 : 1 ≤ P.G) (hΔ1 : 1 ≤ S.Δ) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3) :
    S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X r (a : ℝ)
      ∧ dtilde P.X r (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9) := by
  have hDpos : (0:ℝ) < S.D := by rw [Scale.D]; have := P.H_pos; have := S.Δ_pos; positivity
  have hclose := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi hdD hd2D hrd
  -- `tol ≤ D/10⁹`:  `10¹²·Δ/(GΩ³) ≤ HΔ/10⁹ ⟸ 10²¹ ≤ G·HΩ³`, `HΩ³ ≥ Δ²U⁵ ≥ 10¹⁶⁵`
  have htolD : 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) ≤ S.D / 10 ^ 9 := by
    have hGΩ : (0:ℝ) < P.G * S.Ω ^ 3 := by have := P.G_pos; have := S.Ω_pos; positivity
    have hU5 : (10:ℝ) ^ 165 ≤ P.U ^ 5 := by
      calc (10:ℝ) ^ 165 = ((10:ℝ) ^ 33) ^ 5 := by norm_num
        _ ≤ P.U ^ 5 := pow_le_pow_left₀ (by positivity) hUbig 5
    have hΔ2 : (1:ℝ) ≤ S.Δ ^ 2 := one_le_pow₀ hΔ1
    have hHΩ : (10:ℝ) ^ 165 ≤ P.H * S.Ω ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hΔ2 (pow_pos P.U_pos 5).le
      calc (10:ℝ) ^ 165 ≤ S.Δ ^ 2 * P.U ^ 5 := by nlinarith [h, hU5]
        _ ≤ P.H * S.Ω ^ 3 := hReg
    have lhs_eq : 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
        = 1000000000000 * S.Δ / (P.G * S.Ω ^ 3) := by ring
    rw [lhs_eq, Scale.D, div_le_div_iff₀ hGΩ (by norm_num : (0:ℝ) < 10 ^ 9)]
    have hkey := mul_le_mul_of_nonneg_right hHΩ S.Δ_pos.le
    have hG : P.H * S.Ω ^ 3 * S.Δ ≤ P.H * S.Δ * (P.G * S.Ω ^ 3) := by
      nlinarith [mul_le_mul_of_nonneg_right hG1
        (show (0:ℝ) ≤ P.H * S.Ω ^ 3 * S.Δ by positivity)]
    nlinarith [hkey, hG]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hclose
  constructor
  · nlinarith [hlo, htolD, hdD, hDpos]
  · nlinarith [hhi, htolD, hd2D, hDpos]

/-- **Facts 16–18 (defect decrease).**  The witness defects decrease along `r`: with `d₁` at
`r` and `d₂` at `r+ℓ₁`, `d₂ − d₁ ≤ 0`. -/
theorem dstar_decreasing {a : ℤ} {r ℓ₁ : ℕ} {d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ : 0 < ℓ₁)
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hrl_hi : (r : ℝ) + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hd1D : S.D ≤ (d₁ : ℝ)) (hd1_2D : (d₁ : ℝ) ≤ 2 * S.D)
    (hd2D : S.D ≤ (d₂ : ℝ)) (hd2_2D : (d₂ : ℝ) ≤ 2 * S.D)
    (hrd1 : |Rfun P.X (a : ℝ) (d₁ : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hrd2 : |Rfun P.X (a : ℝ) (d₂ : ℝ) - ((r : ℝ) + (ℓ₁ : ℝ))| ≤ 14 * P.H / S.D)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    d₂ - d₁ ≤ 0 := by
  have hℓ1 : (1:ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ
  have hℓpos : (0:ℝ) < (ℓ₁ : ℝ) := lt_of_lt_of_le one_pos hℓ1
  have hr_hi : (r : ℝ) ≤ 16 * S.R := by linarith
  have hrl_lo : (1/72) * S.R ≤ (r : ℝ) + (ℓ₁ : ℝ) := by linarith
  have haR : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hBpos : (0:ℝ) < S.B := by
    rw [Scale.B]; have := S.Δ_pos; have := P.G_pos; have := S.Ω_pos; positivity
  have htol0 : (0:ℝ) ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
    have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hc1 := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
    hd1D hd1_2D hrd1
  have hc2 := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hrl_lo hrl_hi
    hd2D hd2_2D hrd2
  obtain ⟨hsign, hbt_lo, _⟩ := bt_abs_bounds (P := P) (S := S) (a := (a:ℝ)) (ℓ := (ℓ₁:ℝ))
    (r := (r:ℝ)) hAD haR hℓpos ha_lo ha_hi hr_lo hrl_hi
  have hdiff := slope_bt_close (P := P) hℓ1 htol0 hc1 hc2
  have h2tol := two_tol_le (P := P) (S := S) hG1 hU1 hUbig hDeW
  -- `b̃ ≤ −B/10⁶`, so the slope `s ≤ b̃ + 2tol ≤ −B/(2·10⁶) < 0`
  have hbt_neg : bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ) ≤ -(S.B / 1000000) := by
    have habs : |bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ)| = -bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ) :=
      abs_of_neg hsign
    linarith [hbt_lo, habs.symm.le, habs.le]
  have hslope : ((d₂:ℝ) - (d₁:ℝ)) / (ℓ₁:ℝ) < 0 := by
    have h := (abs_le.mp hdiff).2
    linarith [h, hbt_neg, h2tol, hBpos]
  have hnum : ((d₂:ℝ) - (d₁:ℝ)) < 0 := by
    by_contra hcon
    push Not at hcon
    exact absurd (div_nonneg hcon hℓpos.le) (not_le.mpr hslope)
  have : ((d₂ - d₁ : ℤ) : ℝ) < 0 := by push_cast; linarith
  exact le_of_lt (by exact_mod_cast this)

/-- Placement budget: `11A + (2·tol + 10⁶·W·B) ≤ D` in the regime (each piece `≤ D/3`). -/
private theorem placement_budget (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hΩU : S.Ω ≤ P.U) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    11 * S.A + (2 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
      + 130000000 * (P.G * P.U ^ 5) * S.B) ≤ S.D := by
  have hHpos := P.H_pos; have hGpos := P.G_pos; have hUpos := P.U_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hΔ2 : (1:ℝ) ≤ S.Δ ^ 2 := one_le_pow₀ hΔ1
  have hH2 : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := (le_div_iff₀ (pow_pos hΔpos 2)).mp h1
  have hU5 : P.U ≤ P.U ^ 5 := by
    calc P.U = P.U ^ 1 := (pow_one _).symm
      _ ≤ P.U ^ 5 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU2_10 : P.U ^ 2 ≤ P.U ^ 10 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU10Δ2H : P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
    nlinarith [hH2, mul_le_mul_of_nonneg_right hG1
      (show (0:ℝ) ≤ P.U ^ 10 * S.Δ ^ 2 by positivity)]
  have hU10H : P.U ^ 10 ≤ P.H := by nlinarith [hU10Δ2H, hΔ2, pow_pos hUpos 10]
  -- piece 1:  `33Ω ≤ H`
  have h33U : 33 * P.U ≤ P.U ^ 2 := by nlinarith [hUbig, hUpos]
  have piece1 : 33 * S.Ω ≤ P.H := by
    have : 33 * S.Ω ≤ 33 * P.U := by linarith
    linarith [this, h33U, hU2_10, hU10H]
  have piece1' : 3 * (11 * (S.Δ * S.Ω)) ≤ P.H * S.Δ := by
    nlinarith [mul_le_mul_of_nonneg_right piece1 hΔpos.le]
  -- piece 2:  `3·10⁶·U⁵·Δ² ≤ H ≤ HΔ`
  have h3e6 : (3:ℝ) * 1000000 ≤ P.U ^ 5 := le_trans (by norm_num) (le_trans hUbig hU5)
  have c1 : 3 * 1000000 * P.U ^ 5 ≤ P.U ^ 10 := by
    nlinarith [mul_le_mul_of_nonneg_right h3e6 (pow_pos hUpos 5).le]
  have e1 : 130000000 * (P.G * P.U ^ 5) * S.B
      = 130000000 * P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 := by
    rw [Scale.B]; field_simp
  have hpay3 := band_pay3 (P := P) (S := S) hband hΩU
  have hΩ3pos : (0:ℝ) < S.Ω ^ 3 := pow_pos hΩpos 3
  have hb2 : 130000000 * P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3
      ≤ 130000000 * P.G * P.U ^ 9 * S.Δ ^ 2 := by
    rw [div_le_iff₀ hΩ3pos]
    calc 130000000 * P.U ^ 5 * S.Δ ^ 2
        = (130000000 * P.U ^ 5 * S.Δ ^ 2) * 1 := (mul_one _).symm
      _ ≤ (130000000 * P.U ^ 5 * S.Δ ^ 2) * (P.G * P.U ^ 4 * S.Ω ^ 3) :=
          mul_le_mul_of_nonneg_left hpay3 (by positivity)
      _ = 130000000 * P.G * P.U ^ 9 * S.Δ ^ 2 * S.Ω ^ 3 := by ring
  have piece2 : 3 * (130000000 * P.G * P.U ^ 9 * S.Δ ^ 2) ≤ P.H * S.Δ := by
    have ha : 3 * (130000000 * P.U ^ 9) ≤ P.U ^ 10 := by
      have h3e6' : (3:ℝ) * 130000000 ≤ P.U := le_trans (by norm_num) hUbig
      nlinarith [h3e6', pow_pos hUpos 9]
    have hb : P.H ≤ P.H * S.Δ := by nlinarith [hHpos, hΔ1]
    have hc : 3 * (130000000 * P.G * P.U ^ 9 * S.Δ ^ 2) ≤ P.G * P.U ^ 10 * S.Δ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right ha
        (show (0:ℝ) ≤ P.G * S.Δ ^ 2 by positivity)]
    linarith [hc, hH2, hb]
  -- piece 3:  `6·10¹²·Δ·U⁴ ≤ HΔ`  (tol pays `1/(GΩ³) ≤ U⁴`)
  have htolp : S.Δ / (P.G * S.Ω ^ 3) ≤ S.Δ * P.U ^ 4 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < P.G * S.Ω ^ 3)]
    calc S.Δ = S.Δ * 1 := (mul_one _).symm
      _ ≤ S.Δ * (P.G * P.U ^ 4 * S.Ω ^ 3) := mul_le_mul_of_nonneg_left hpay3 hΔpos.le
      _ = S.Δ * P.U ^ 4 * (P.G * S.Ω ^ 3) := by ring
  have piece3 : 3 * (2 * (1000000000000 * (S.Δ * P.U ^ 4))) ≤ P.H * S.Δ := by
    have h6 : (6:ℝ) * 1000000000000 * P.U ^ 4 ≤ P.H := by
      have h6a : (6:ℝ) * 1000000000000 ≤ P.U := le_trans (by norm_num) hUbig
      have h6b : 6 * 1000000000000 * P.U ^ 4 ≤ P.U ^ 5 := by
        nlinarith [h6a, pow_pos hUpos 4]
      have h6c : P.U ^ 5 ≤ P.U ^ 10 := pow_le_pow_right₀ hU1 (by norm_num)
      linarith [h6b, h6c, hU10H]
    nlinarith [hΔpos, h6]
  rw [Scale.D, Scale.A, e1]
  linarith [piece1', piece2, piece3, hb2, htolp]

/-- **Facts 19–21 (placement).**  With `d₁` at `r`, `d₂` at `r+ℓ₁` and `ℓ₁ ≤ G·U⁵`:
`a + (d₁ − d₂) ≤ d₂`. -/
theorem dstar_placement {a : ℤ} {r ℓ₁ : ℕ} {d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ : 0 < ℓ₁) (hℓW : (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hrl_hi : (r : ℝ) + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hd1D : S.D ≤ (d₁ : ℝ)) (hd1_2D : (d₁ : ℝ) ≤ 2 * S.D)
    (hd2D : S.D ≤ (d₂ : ℝ)) (hd2_2D : (d₂ : ℝ) ≤ 2 * S.D)
    (hrd1 : |Rfun P.X (a : ℝ) (d₁ : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hrd2 : |Rfun P.X (a : ℝ) (d₂ : ℝ) - ((r : ℝ) + (ℓ₁ : ℝ))| ≤ 14 * P.H / S.D)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hΩU : S.Ω ≤ P.U) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    (a : ℝ) + ((d₁ : ℝ) - (d₂ : ℝ)) ≤ (d₂ : ℝ) := by
  have hℓ1 : (1:ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ
  have hℓpos : (0:ℝ) < (ℓ₁ : ℝ) := lt_of_lt_of_le one_pos hℓ1
  have hr_hi : (r : ℝ) ≤ 16 * S.R := by linarith
  have hrl_lo : (1/72) * S.R ≤ (r : ℝ) + (ℓ₁ : ℝ) := by linarith
  have haR : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hBpos : (0:ℝ) < S.B := by
    rw [Scale.B]; have := S.Δ_pos; have := P.G_pos; have := S.Ω_pos; positivity
  have hc1 := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
    hd1D hd1_2D hrd1
  have hc2 := dtilde_close (P := P) (S := S) hAD ha0 ha_lo ha_hi hrl_lo hrl_hi
    hd2D hd2_2D hrd2
  obtain ⟨_, _, hbt_hi⟩ := bt_abs_bounds (P := P) (S := S) (a := (a:ℝ)) (ℓ := (ℓ₁:ℝ))
    (r := (r:ℝ)) hAD haR hℓpos ha_lo ha_hi hr_lo hrl_hi
  -- `d̃(r+ℓ) − d̃(r) = ℓ·b̃`
  have hbtid : dtilde P.X ((r:ℝ) + (ℓ₁:ℝ)) (a:ℝ) - dtilde P.X (r:ℝ) (a:ℝ)
      = (ℓ₁:ℝ) * bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ) := by
    rw [bt]; field_simp
  -- `|ℓ·b̃| ≤ W·10⁶·B`
  have hlb : |(ℓ₁:ℝ) * bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ)|
      ≤ (130 * (P.G * P.U ^ 5)) * (1000000 * S.B) := by
    rw [abs_mul, abs_of_pos hℓpos]
    exact mul_le_mul hℓW hbt_hi (abs_nonneg _)
      (le_trans hℓpos.le hℓW)
  -- triangle: `d₁ − d₂ ≤ 2·tol + W·10⁶·B`
  have hd12 : (d₁ : ℝ) - (d₂ : ℝ)
      ≤ 2 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        + 130000000 * (P.G * P.U ^ 5) * S.B := by
    have hid : (d₁ : ℝ) - (d₂ : ℝ)
        = ((d₁:ℝ) - dtilde P.X (r:ℝ) (a:ℝ))
          - ((d₂:ℝ) - dtilde P.X ((r:ℝ) + (ℓ₁:ℝ)) (a:ℝ))
          - ((ℓ₁:ℝ) * bt P.X (a:ℝ) (ℓ₁:ℝ) (r:ℝ)) := by
      rw [← hbtid]; ring
    have t1 := (abs_le.mp hc1).2
    have t2 := (abs_le.mp hc2).1
    have t3 := (abs_le.mp hlb).1
    rw [hid]; nlinarith [t1, t2, t3]
  have hbud := placement_budget (P := P) (S := S) h1 hΩU hband hG1 hU1 hΔ1 hUbig
  linarith [ha_hi, hd12, hbud, hd2D]

/-- Convenience: the ε-form `d̃`-window of `dtilde_eps_window` at the three points
`r`, `r+ℓ₁`, `r+ℓ₂` simultaneously (`ℓ₁ ≤ ℓ₂`). -/
theorem dtilde_eps_window_pair {a : ℤ} {r ℓ₁ ℓ₂ : ℕ} {d dℓ₁ dℓ₂ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ12 : ℓ₁ ≤ ℓ₂)
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hr2_hi : (r : ℝ) + (ℓ₂ : ℝ) ≤ 16 * S.R)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hd1D : S.D ≤ dℓ₁) (hd1_2D : dℓ₁ ≤ 2 * S.D)
    (hd2D' : S.D ≤ dℓ₂) (hd2_2D' : dℓ₂ ≤ 2 * S.D)
    (hrd : |Rfun P.X (a : ℝ) d - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hrd1 : |Rfun P.X (a : ℝ) dℓ₁ - ((r : ℝ) + (ℓ₁ : ℝ))| ≤ 14 * P.H / S.D)
    (hrd2 : |Rfun P.X (a : ℝ) dℓ₂ - ((r : ℝ) + (ℓ₂ : ℝ))| ≤ 14 * P.H / S.D)
    (hG1 : 1 ≤ P.G) (hΔ1 : 1 ≤ S.Δ) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3) :
    (S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X (r : ℝ) (a : ℝ)
        ∧ dtilde P.X (r : ℝ) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9))
      ∧ (S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X ((r : ℝ) + (ℓ₁ : ℝ)) (a : ℝ)
        ∧ dtilde P.X ((r : ℝ) + (ℓ₁ : ℝ)) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9))
      ∧ (S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X ((r : ℝ) + (ℓ₂ : ℝ)) (a : ℝ)
        ∧ dtilde P.X ((r : ℝ) + (ℓ₂ : ℝ)) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9)) := by
  have hl1 : (0:ℝ) ≤ (ℓ₁ : ℝ) := Nat.cast_nonneg _
  have hl12 : (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hr_hi : (r : ℝ) ≤ 16 * S.R := by linarith
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + (ℓ₁ : ℝ) := by linarith
  have hr1_hi : (r : ℝ) + (ℓ₁ : ℝ) ≤ 16 * S.R := by linarith
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + (ℓ₂ : ℝ) := by linarith
  exact ⟨dtilde_eps_window hAD ha0 ha_lo ha_hi hr_lo hr_hi hdD hd2D hrd
      hG1 hΔ1 hUbig hReg,
    dtilde_eps_window hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1D hd1_2D hrd1
      hG1 hΔ1 hUbig hReg,
    dtilde_eps_window hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2D' hd2_2D' hrd2
      hG1 hΔ1 hUbig hReg⟩

/-- `H ≥ 10³⁰·G⁹·U⁵⁰` from `h1` (`H ≥ G·U¹⁰·Δ²`) and `hDeW` (`Δ ≥ 10¹⁵·G⁴·U²⁰`). -/
private theorem H_lower (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    10 ^ 30 * (P.G ^ 9 * P.U ^ 50) ≤ P.H := by
  have hH2 : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := (le_div_iff₀ (pow_pos S.Δ_pos 2)).mp h1
  have hΔsq : (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 ≤ S.Δ ^ 2 :=
    pow_le_pow_left₀ (by have := P.G_pos; have := P.U_pos; positivity) hDeW 2
  calc 10 ^ 30 * (P.G ^ 9 * P.U ^ 50)
      ≤ 10 ^ 54 * (P.G ^ 9 * P.U ^ 50) := by
        have := P.G_pos; have := P.U_pos
        nlinarith [mul_pos (pow_pos P.G_pos 9) (pow_pos P.U_pos 50)]
    _ = P.G * P.U ^ 10 * (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 := by ring
    _ ≤ P.G * P.U ^ 10 * S.Δ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hΔsq
          (by have := P.G_pos; have := P.U_pos; positivity)
    _ ≤ P.H := hH2

set_option exponentiation.threshold 600 in
/-- **Capstone budget.**  In the regime (`h1`, `hDeW`, `hHbig`, `U ≥ 10³³`), the uniform
near-integer budget satisfies `step4ErrU ≤ 1/4` — discharging the capstone's `hbud`. -/
theorem errB_quarter (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14) :
    step4ErrU P S ≤ 1 / 4 := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  -- term 1: `45·W⁴/Δ ≤ 1/20`
  have hW4 : P.Wval ^ 4 = P.G ^ 4 * P.U ^ 20 := by unfold Globals.Wval; ring
  have ht1 : 10 ^ 11 * P.Wval ^ 4 / S.Δ ≤ 1 / 20 := by
    rw [hW4, div_le_iff₀ hΔpos]
    nlinarith [hDeW, pow_pos hGpos 4, pow_pos hUpos 20]
  -- term 2: `10¹¹⁰·UpsT ≤ 1/100`
  have ht2 : 10 ^ 119 * UpsT P S ≤ 1 / 100 := by
    unfold UpsT
    have hDn : (0:ℝ) < P.H ^ 2 * S.Ω ^ 14 := by positivity
    rw [show (10:ℝ) ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
        = 10 ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) / (P.H ^ 2 * S.Ω ^ 14) by ring,
      div_le_iff₀ hDn]
    nlinarith [hHbig, pow_pos hΔpos 4, pow_pos hGpos 5, pow_pos hUpos 45]
  -- term 3: `7·10⁹⁷·G⁴U³⁵/(HΩ¹¹) ≤ 1/100`
  have hHlo := H_lower (P := P) (S := S) h1 hDeW
  have ht3 : 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
      * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) ≤ 1 / 100 := by
    have e3 : 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
        * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        = 7 * 10 ^ 106 * (P.G ^ 4 * P.U ^ 35) / (P.H * S.Ω ^ 11) := by
      rw [Scale.D]; field_simp; ring
    have hU15 : (10:ℝ) ^ 495 ≤ P.U ^ 15 := by
      calc (10:ℝ) ^ 495 = ((10:ℝ) ^ 33) ^ 15 := by norm_num
        _ ≤ P.U ^ 15 := pow_le_pow_left₀ (by positivity) hUbig 15
    have hG5 : (1:ℝ) ≤ P.G ^ 5 := one_le_pow₀ hG1
    have hGU15 : (10:ℝ) ^ 495 ≤ P.G ^ 5 * P.U ^ 15 := by
      nlinarith [hU15, mul_le_mul_of_nonneg_right hG5 (pow_pos hUpos 15).le]
    have hpay11 := band_pay11 (P := P) (S := S) hband hΩU
    have hcore : 7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35) * (P.G ^ 3 * P.U ^ 10)
        ≤ 10 ^ 30 * (P.G ^ 9 * P.U ^ 50) := by
      have hU5c : (7:ℝ) * 10 ^ 78 ≤ P.U ^ 5 := by
        calc (7:ℝ) * 10 ^ 78 ≤ (10:ℝ) ^ 79 := by norm_num
          _ ≤ (10:ℝ) ^ 165 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ = ((10:ℝ) ^ 33) ^ 5 := by rw [← pow_mul]
          _ ≤ P.U ^ 5 := pow_le_pow_left₀ (by norm_num) hUbig 5
      have hG79 : P.G ^ 7 ≤ P.G ^ 9 := pow_le_pow_right₀ hG1 (by norm_num)
      calc 7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35) * (P.G ^ 3 * P.U ^ 10)
          = 10 ^ 30 * (7 * 10 ^ 78) * (P.G ^ 7 * P.U ^ 45) := by ring
        _ ≤ 10 ^ 30 * P.U ^ 5 * (P.G ^ 7 * P.U ^ 45) := by
            gcongr 10 ^ 30 * ?_ * (P.G ^ 7 * P.U ^ 45)
        _ = 10 ^ 30 * (P.G ^ 7 * P.U ^ 50) := by ring
        _ ≤ 10 ^ 30 * (P.G ^ 9 * P.U ^ 50) := by gcongr 10 ^ 30 * (?_ * P.U ^ 50)
    have hmain : 7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35) ≤ P.H * S.Ω ^ 11 := by
      calc 7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35)
          = (7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35)) * 1 := (mul_one _).symm
        _ ≤ (7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35)) * (P.G ^ 3 * P.U ^ 10 * S.Ω ^ 11) :=
            mul_le_mul_of_nonneg_left hpay11 (by positivity)
        _ = (7 * 10 ^ 108 * (P.G ^ 4 * P.U ^ 35) * (P.G ^ 3 * P.U ^ 10)) * S.Ω ^ 11 := by
            ring
        _ ≤ (10 ^ 30 * (P.G ^ 9 * P.U ^ 50)) * S.Ω ^ 11 :=
            mul_le_mul_of_nonneg_right hcore (by positivity)
        _ ≤ P.H * S.Ω ^ 11 := mul_le_mul_of_nonneg_right hHlo (by positivity)
    rw [e3, div_le_iff₀ (by positivity : (0:ℝ) < P.H * S.Ω ^ 11)]
    linarith [hmain]
  unfold step4ErrU
  linarith [ht1, ht2, ht3]

end Squarefree
