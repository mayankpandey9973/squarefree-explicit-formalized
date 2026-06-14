import Squarefree.Lower.Step4Band5
import Squarefree.Lower.Step4BandPay

/-!
# §5 Step-4 hybrid E-part fit, A-half: core monomial budgets
Window/monomial core lemmas (`window`, `coreA/B/F/P4`, `chat`, `Δ`-floors) backing the
`Step4FitEA` summand fits. Public only for intra-family use by `Step4FitEA`/`Step4FitEACap`.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- TRUE-ℓ window monomial budget: `ℓ₁^i·ℓ₂^j·(ℓ₂-ℓ₁) ≤ 130^(i+j+1)·W^i·W^j·W` for
`W = G·U⁵` and the two-sided window `ℓ ≤ 130·W`. -/
theorem step4_fitEA_window (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5)) (i j : ℕ) :
    ℓ₁ ^ i * ℓ₂ ^ j * (ℓ₂ - ℓ₁)
      ≤ 130 ^ (i + j + 1)
          * ((P.G * P.U ^ 5) ^ i * (P.G * P.U ^ 5) ^ j * (P.G * P.U ^ 5)) := by
  have h0₁ : (0:ℝ) ≤ ℓ₁ := le_trans zero_le_one hℓ1lo
  have h0₂ : (0:ℝ) ≤ ℓ₂ := by linarith
  have hd0 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hdW : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hWnn : (0:ℝ) ≤ 130 * (P.G * P.U ^ 5) := le_trans h0₁ hℓ1W
  calc ℓ₁ ^ i * ℓ₂ ^ j * (ℓ₂ - ℓ₁)
      ≤ (130 * (P.G * P.U ^ 5)) ^ i * (130 * (P.G * P.U ^ 5)) ^ j
          * (130 * (P.G * P.U ^ 5)) := by
        refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ h0₁ hℓ1W i)
          (pow_le_pow_left₀ h0₂ hℓ2W j) (pow_nonneg h0₂ j) (pow_nonneg hWnn i)) hdW hd0 ?_
        exact mul_nonneg (pow_nonneg hWnn i) (pow_nonneg hWnn j)
    _ = 130 ^ (i + j + 1)
          * ((P.G * P.U ^ 5) ^ i * (P.G * P.U ^ 5) ^ j * (P.G * P.U ^ 5)) := by
        rw [mul_pow, mul_pow, pow_add, pow_add, pow_one]
        ring

/-- A-core: the g₁-piece monomial fraction fits `C²·H·G¹⁵·U⁷⁵/(Δ²·Ω¹³)`. -/
theorem step4_fitEA_coreA
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (C : ℝ) (hC : 1 ≤ C) (W : ℝ) (hW : W ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25)) :
    22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40 * W / (S.Δ ^ 2 * S.Ω ^ 9)
      ≤ C ^ 2 * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hU3 : (10:ℝ) ^ 95 ≤ P.U ^ 3 := by
    calc (10:ℝ) ^ 95 ≤ (10:ℝ) ^ 99 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((10:ℝ) ^ 33) ^ 3 := by rw [← pow_mul]
      _ ≤ P.U ^ 3 := pow_le_pow_left₀ (by norm_num) hUbig 3
  have hstep : 22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40 * W / (S.Δ ^ 2 * S.Ω ^ 9)
      ≤ 22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40 * (10 ^ 11 * (P.G ^ 5 * P.U ^ 25))
          / (S.Δ ^ 2 * S.Ω ^ 9) := by
    gcongr 22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40 * ?_ / (S.Δ ^ 2 * S.Ω ^ 9)
  refine le_trans hstep ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ (le_of_lt hΩpos) hΩU 4
  calc 22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40 * (10 ^ 11 * (P.G ^ 5 * P.U ^ 25))
        * (S.Δ ^ 2 * S.Ω ^ 13)
      = (22 * 10 ^ 93) * S.Ω ^ 4 * (C * P.H * P.G ^ 11 * P.U ^ 65 * (S.Δ ^ 2 * S.Ω ^ 9)) := by
        ring
    _ ≤ P.U ^ 3 * P.U ^ 4 * (C * P.H * P.G ^ 11 * P.U ^ 65 * (S.Δ ^ 2 * S.Ω ^ 9)) := by
        have h22 : (22:ℝ) * 10 ^ 93 ≤ (10:ℝ) ^ 95 := by norm_num
        gcongr ?_ * ?_ * (C * P.H * P.G ^ 11 * P.U ^ 65 * (S.Δ ^ 2 * S.Ω ^ 9))
        exact le_trans h22 hU3
    _ = C * P.H * P.G ^ 11 * P.U ^ 72 * (S.Δ ^ 2 * S.Ω ^ 9) := by ring
    _ ≤ C ^ 2 * P.H * P.G ^ 15 * P.U ^ 75 * (S.Δ ^ 2 * S.Ω ^ 9) := by
        have hCsq : C ≤ C ^ 2 := by nlinarith
        have hG' : P.G ^ 11 ≤ P.G ^ 15 := pow_le_pow_right₀ hG1 (by norm_num)
        have hU' : P.U ^ 72 ≤ P.U ^ 75 := pow_le_pow_right₀ (le_trans (by norm_num) hUbig)
          (by norm_num)
        gcongr ?_ * P.H * ?_ * ?_ * (S.Δ ^ 2 * S.Ω ^ 9)

/-- B-core: the Ω⁻¹²-type monomial fraction (g₂-piece and T2) fits
`C²·H·G¹⁵·U⁷⁵/(Δ²·Ω¹³)`, via `h1` once. -/
theorem step4_fitEA_coreB
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (C : ℝ) (hC : 1 ≤ C) (K W : ℝ) (hK : K ≤ (10:ℝ) ^ 97)
    (hW0 : 0 ≤ W) (hW : W ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35)) :
    K * C * P.G ^ 5 * P.U ^ 40 * W / S.Ω ^ 12
      ≤ C ^ 2 * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hU4 : (10:ℝ) ^ 112 ≤ P.U ^ 4 := by
    calc (10:ℝ) ^ 112 ≤ (10:ℝ) ^ 132 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((10:ℝ) ^ 33) ^ 4 := by rw [← pow_mul]
      _ ≤ P.U ^ 4 := pow_le_pow_left₀ (by norm_num) hUbig 4
  have hH' : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
    rw [← le_div_iff₀ (by positivity)]; exact h1
  have hstep : K * C * P.G ^ 5 * P.U ^ 40 * W / S.Ω ^ 12
      ≤ 10 ^ 97 * C * P.G ^ 5 * P.U ^ 40 * (10 ^ 15 * (P.G ^ 7 * P.U ^ 35)) / S.Ω ^ 12 := by
    gcongr ?_ * C * P.G ^ 5 * P.U ^ 40 * ?_ / S.Ω ^ 12
  refine le_trans hstep ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 10 ^ 97 * C * P.G ^ 5 * P.U ^ 40 * (10 ^ 15 * (P.G ^ 7 * P.U ^ 35))
        * (S.Δ ^ 2 * S.Ω ^ 13)
      = (10:ℝ) ^ 112 * S.Ω * (C * P.G ^ 12 * P.U ^ 75 * S.Δ ^ 2 * S.Ω ^ 12) := by ring
    _ ≤ P.U ^ 4 * P.U * (C * P.G ^ 12 * P.U ^ 75 * S.Δ ^ 2 * S.Ω ^ 12) := by
        gcongr ?_ * ?_ * (C * P.G ^ 12 * P.U ^ 75 * S.Δ ^ 2 * S.Ω ^ 12)
    _ = (P.G * P.U ^ 10 * S.Δ ^ 2) * (C * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 12) := by ring
    _ ≤ P.H * (C * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 12) := by
        gcongr ?_ * (C * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 12)
    _ = C * P.H * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 12 := by ring
    _ ≤ C ^ 2 * P.H * P.G ^ 15 * P.U ^ 75 * S.Ω ^ 12 := by
        have hCsq : C ≤ C ^ 2 := by nlinarith
        have hG' : P.G ^ 11 ≤ P.G ^ 15 := pow_le_pow_right₀ hG1 (by norm_num)
        have hU' : P.U ^ 70 ≤ P.U ^ 75 := pow_le_pow_right₀ (le_trans (by norm_num) hUbig)
          (by norm_num)
        gcongr ?_ * P.H * ?_ * ?_ * S.Ω ^ 12


/-- The `a`-cancellation in the flat `Ecap4` summand:
`(a/D)²·(Cref·(A/a)²) = 3·ℓ₁ℓ₂(ℓ₂−ℓ₁)/D²` for `a ≠ 0`. -/
theorem step4_fitEA_chat {a : ℝ} (ha : a ≠ 0) (ℓ₁ ℓ₂ : ℝ) :
    (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
      = 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / S.D ^ 2 := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  rw [show Cref P S ℓ₁ ℓ₂ = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (S.Δ ^ 2 * S.Ω ^ 2) from rfl,
    show S.A = S.Δ * S.Ω from rfl, show S.D = P.H * S.Δ from rfl]
  field_simp

/-- `hDeW` with the `G⁴`-factor dropped: `10¹⁵·U²⁰ ≤ Δ`. -/
theorem step4_fitEA_dewU
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) (hG1 : 1 ≤ P.G) :
    10 ^ 15 * P.U ^ 20 ≤ S.Δ := by
  have hUpos := P.U_pos
  have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
  nlinarith [pow_pos hUpos 20, pow_nonneg hUpos.le 20]

/-- Absolute `Δ`-floor from `hDeW` and `U ≥ 10³³`: `10⁴⁸ ≤ Δ`. -/
theorem step4_fitEA_dewBig
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) (hG1 : 1 ≤ P.G)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    (10:ℝ) ^ 48 ≤ S.Δ := by
  have hU1 : (1:ℝ) ≤ P.U := le_trans (by norm_num) hUbig
  have hU20 : (10:ℝ) ^ 33 ≤ P.U ^ 20 :=
    le_trans hUbig (le_self_pow₀ hU1 (by norm_num))
  calc (10:ℝ) ^ 48 = 10 ^ 15 * (10:ℝ) ^ 33 := by norm_num
    _ ≤ 10 ^ 15 * P.U ^ 20 := by gcongr 10 ^ 15 * ?_
    _ ≤ S.Δ := step4_fitEA_dewU hDeW hG1

/-- F-core: the flat `Ecap4a` summand monomial fraction fits the `C¹`-block, via `h1`
twice (on `H²`), the FULL `Δ³ ≥ 10⁴⁵G¹²U⁶⁰` floor, and the band pay `Ω⁻⁶ ≤ G²U⁸`. -/
theorem step4_fitEA_coreF
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (C : ℝ) (hC : 0 ≤ C) (W : ℝ) (hW : W ≤ 10 ^ 24 * (P.G ^ 11 * P.U ^ 55)) :
    528 * 10 ^ 101 * C * P.U ^ 40 * P.G ^ 5 * W / (S.Δ * P.H * S.Ω ^ 19)
      ≤ C * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hH' : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
    rw [← le_div_iff₀ (by positivity)]; exact h1
  have hpay := band_pay6 (P := P) (S := S) hband hΩU
  have hG1315 : P.G ^ 13 ≤ P.G ^ 15 := pow_le_pow_right₀ hG1 (by norm_num)
  have hKfit3 : 528 * 10 ^ 125 * (P.G ^ 3 * P.U ^ 8) ≤ S.Δ ^ 3 := by
    have hU52 : (10:ℝ) ^ 47 ≤ P.U ^ 52 := by
      calc (10:ℝ) ^ 47 ≤ (10:ℝ) ^ 1716 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 52 := by rw [← pow_mul]
        _ ≤ P.U ^ 52 := pow_le_pow_left₀ (by norm_num) hUbig 52
    have hΔ3 : 10 ^ 81 * (P.G ^ 12 * P.U ^ 60) ≤ S.Δ ^ 3 := by
      calc (10:ℝ) ^ 81 * (P.G ^ 12 * P.U ^ 60)
          = (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 3 := by ring
        _ ≤ S.Δ ^ 3 := pow_le_pow_left₀ (by positivity) hDeW 3
    calc 528 * 10 ^ 125 * (P.G ^ 3 * P.U ^ 8)
        ≤ 10 ^ 81 * 10 ^ 47 * (P.G ^ 3 * P.U ^ 8) := by
          have h59 : (528:ℝ) * 10 ^ 125 ≤ 10 ^ 81 * 10 ^ 47 := by norm_num
          exact mul_le_mul_of_nonneg_right h59 (by positivity)
      _ ≤ 10 ^ 81 * P.U ^ 52 * (P.G ^ 3 * P.U ^ 8) := by
          gcongr 10 ^ 81 * ?_ * (P.G ^ 3 * P.U ^ 8)
      _ = 10 ^ 81 * (P.G ^ 3 * P.U ^ 60) := by ring
      _ ≤ 10 ^ 81 * (P.G ^ 12 * P.U ^ 60) := by
          have hG312 : P.G ^ 3 ≤ P.G ^ 12 := pow_le_pow_right₀ hG1 (by norm_num)
          gcongr 10 ^ 81 * (?_ * P.U ^ 60)
      _ ≤ S.Δ ^ 3 := hΔ3
  have hstep : 528 * 10 ^ 101 * C * P.U ^ 40 * P.G ^ 5 * W / (S.Δ * P.H * S.Ω ^ 19)
      ≤ 528 * 10 ^ 101 * C * P.U ^ 40 * P.G ^ 5 * (10 ^ 24 * (P.G ^ 11 * P.U ^ 55))
          / (S.Δ * P.H * S.Ω ^ 19) := by
    gcongr 528 * 10 ^ 101 * C * P.U ^ 40 * P.G ^ 5 * ?_ / (S.Δ * P.H * S.Ω ^ 19)
  refine le_trans hstep ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 528 * 10 ^ 101 * C * P.U ^ 40 * P.G ^ 5 * (10 ^ 24 * (P.G ^ 11 * P.U ^ 55))
        * (S.Δ ^ 2 * S.Ω ^ 13)
      = (528 * 10 ^ 125 * (C * P.G ^ 16 * P.U ^ 95 * S.Δ ^ 2 * S.Ω ^ 13)) * 1 := by ring
    _ ≤ (528 * 10 ^ 125 * (C * P.G ^ 16 * P.U ^ 95 * S.Δ ^ 2 * S.Ω ^ 13))
          * (P.G ^ 2 * P.U ^ 8 * S.Ω ^ 6) :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
    _ = (528 * 10 ^ 125 * (P.G ^ 3 * P.U ^ 8))
          * (C * P.G ^ 15 * P.U ^ 95 * S.Δ ^ 2 * S.Ω ^ 19) := by ring
    _ ≤ S.Δ ^ 3 * (C * P.G ^ 15 * P.U ^ 95 * S.Δ ^ 2 * S.Ω ^ 19) :=
        mul_le_mul_of_nonneg_right hKfit3 (by positivity)
    _ = (P.G * P.U ^ 10 * S.Δ ^ 2)
          * ((P.G * P.U ^ 10 * S.Δ ^ 2) * (C * P.G ^ 13 * P.U ^ 75 * S.Δ * S.Ω ^ 19)) := by
        ring
    _ ≤ P.H * ((P.G * P.U ^ 10 * S.Δ ^ 2)
          * (C * P.G ^ 13 * P.U ^ 75 * S.Δ * S.Ω ^ 19)) :=
        mul_le_mul_of_nonneg_right hH' (by positivity)
    _ ≤ P.H * (P.H * (C * P.G ^ 13 * P.U ^ 75 * S.Δ * S.Ω ^ 19)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hH' (by positivity)) hHpos.le
    _ = C * P.H * P.G ^ 13 * P.U ^ 75 * (S.Δ * P.H * S.Ω ^ 19) := by ring
    _ ≤ C * P.H * P.G ^ 15 * P.U ^ 75 * (S.Δ * P.H * S.Ω ^ 19) := by
        gcongr C * P.H * ?_ * P.U ^ 75 * (S.Δ * P.H * S.Ω ^ 19)

/-- P4-core: the capped `p₂` degree-4 summand monomial fraction fits the `C¹`-block,
via `h1` once, `hDeW` twice, and the band pay `Ω⁻¹¹ ≤ G³U¹⁰`. -/
theorem step4_fitEA_coreP4
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (C : ℝ) (hC : 0 ≤ C) (W : ℝ) (hW : W ≤ 2 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50)) :
    1694 * 10 ^ 141 * C * P.G ^ 6 * P.U ^ 50 * W / (S.Δ ^ 2 * S.Ω ^ 24)
      ≤ C * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hH' : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
    rw [← le_div_iff₀ (by positivity)]; exact h1
  have hpay := band_pay11 (P := P) (S := S) hband hΩU
  have hH54 : 10 ^ 54 * (P.G ^ 9 * P.U ^ 50) ≤ P.H := by
    have hΔ2 : (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 ≤ S.Δ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hDeW 2
    calc (10:ℝ) ^ 54 * (P.G ^ 9 * P.U ^ 50)
        = (P.G * P.U ^ 10) * (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 := by ring
      _ ≤ (P.G * P.U ^ 10) * S.Δ ^ 2 := mul_le_mul_of_nonneg_left hΔ2 (by positivity)
      _ = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
      _ ≤ P.H := hH'
  have hscal : 3388 * 10 ^ 163 * (P.G ^ 4 * P.U ^ 35) ≤ P.H := by
    have hU15 : (3388:ℝ) * 10 ^ 109 ≤ P.U ^ 15 := by
      calc (3388:ℝ) * 10 ^ 109 ≤ (10:ℝ) ^ 113 := by norm_num
        _ ≤ (10:ℝ) ^ 495 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 15 := by rw [← pow_mul]
        _ ≤ P.U ^ 15 := pow_le_pow_left₀ (by norm_num) hUbig 15
    have hG49 : P.G ^ 4 ≤ P.G ^ 9 := pow_le_pow_right₀ hG1 (by norm_num)
    calc 3388 * 10 ^ 163 * (P.G ^ 4 * P.U ^ 35)
        = 10 ^ 54 * (3388 * 10 ^ 109) * (P.G ^ 4 * P.U ^ 35) := by ring
      _ ≤ 10 ^ 54 * P.U ^ 15 * (P.G ^ 4 * P.U ^ 35) := by
          gcongr 10 ^ 54 * ?_ * (P.G ^ 4 * P.U ^ 35)
      _ = 10 ^ 54 * (P.G ^ 4 * P.U ^ 50) := by ring
      _ ≤ 10 ^ 54 * (P.G ^ 9 * P.U ^ 50) := by
          gcongr 10 ^ 54 * (?_ * P.U ^ 50)
      _ ≤ P.H := hH54
  have hstep : 1694 * 10 ^ 141 * C * P.G ^ 6 * P.U ^ 50 * W / (S.Δ ^ 2 * S.Ω ^ 24)
      ≤ 1694 * 10 ^ 141 * C * P.G ^ 6 * P.U ^ 50 * (2 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50))
          / (S.Δ ^ 2 * S.Ω ^ 24) := by
    gcongr 1694 * 10 ^ 141 * C * P.G ^ 6 * P.U ^ 50 * ?_ / (S.Δ ^ 2 * S.Ω ^ 24)
  refine le_trans hstep ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1694 * 10 ^ 141 * C * P.G ^ 6 * P.U ^ 50 * (2 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50))
        * (S.Δ ^ 2 * S.Ω ^ 13)
      = (3388 * 10 ^ 163 * (C * P.G ^ 16 * P.U ^ 100 * S.Δ ^ 2 * S.Ω ^ 13)) * 1 := by ring
    _ ≤ (3388 * 10 ^ 163 * (C * P.G ^ 16 * P.U ^ 100 * S.Δ ^ 2 * S.Ω ^ 13))
          * (P.G ^ 3 * P.U ^ 10 * S.Ω ^ 11) :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
    _ = (3388 * 10 ^ 163 * (P.G ^ 4 * P.U ^ 35))
          * (C * P.G ^ 15 * P.U ^ 75 * S.Δ ^ 2 * S.Ω ^ 24) := by ring
    _ ≤ P.H * (C * P.G ^ 15 * P.U ^ 75 * S.Δ ^ 2 * S.Ω ^ 24) :=
        mul_le_mul_of_nonneg_right hscal (by positivity)
    _ = C * P.H * P.G ^ 15 * P.U ^ 75 * (S.Δ ^ 2 * S.Ω ^ 24) := by ring

end Squarefree
