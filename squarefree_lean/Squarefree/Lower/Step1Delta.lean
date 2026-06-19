import Squarefree.Lower.DefectScales
import Squarefree.Params

/-!
# §5 Step-1: uniform bound on `δ_eff`

The per-`r` "effective defect" appearing on the RHS of `phi_norm_le_v0`
(the near-integer term + the `E`-bound term + the §5 replacement term) is bounded
by a single clean uniform scale `δ_unif := 10^60·(1/Δ)·G³·U¹⁵/Ω⁵`.

The constant `10^60` is intentionally loose — the honest scale is
`(1/Δ)·G³·U¹⁵/Ω⁵`, a factor `U⁵` above the writeup's loose `(1/Δ)·G³·U¹⁰/Ω⁵`,
absorbed downstream in the Step-5 combine.

Each of the three summands is bounded by `(10^60/3)·δ_unif` in its own private
lemma, then `delta_eff_le` adds the three.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 800000

variable {P : Globals} {S : Scale P}

/-- Abbreviation: `δ_unif := (1/Δ)·G³·U¹⁵/Ω⁵` (without the loose `10^60`). -/
private noncomputable def δunif (P : Globals) (S : Scale P) : ℝ :=
  (1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5

private theorem δunif_pos : 0 < δunif P S := by
  have := P.G_pos; have := P.U_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold δunif; positivity

private theorem δunif_eq : δunif P S = P.G^3 * P.U^15 / (S.Δ * S.Ω^5) := by
  have := S.Δ_pos; have := S.Ω_pos
  unfold δunif; field_simp

/-- `1 ≤ H` from the regime hypothesis `G·U^10 ≤ H/Δ²`. -/
private theorem one_le_H (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) : 1 ≤ P.H := by
  have hΔ := S.Δ_pos; have hH := P.H_pos
  have hU10 : (1:ℝ) ≤ P.U^10 := one_le_pow₀ hU1
  have hGU : (1:ℝ) ≤ P.G * P.U^10 := one_le_mul_of_one_le_of_one_le hG1 hU10
  have hHdiv : (1:ℝ) ≤ P.H / S.Δ^2 := le_trans hGU h1
  rw [le_div_iff₀ (by positivity)] at hHdiv
  have hΔ2 : (1:ℝ) ≤ S.Δ^2 := one_le_pow₀ hΔ1
  nlinarith [hHdiv, hΔ2, hH]

/-- `A ≤ (G·U⁵)·B` (the §5 width bound), using `Ω ≤ U`. -/
private theorem A_le_W_B (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U) :
    S.A ≤ (P.G * P.U ^ 5) * S.B := by
  have hG := P.G_pos; have hU := P.U_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 5 * S.Δ := by
    have a1 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ hΩ.le hΩU 4
    have a2 : P.U ^ 4 ≤ P.U ^ 5 := by
      have := pow_le_pow_right₀ hU1 (by norm_num : 4 ≤ 5); simpa using this
    nlinarith [pow_pos hU 5, hΔ1, a1, a2]
  have hWB : (P.G * P.U ^ 5) * S.B = P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 := by
    unfold Scale.B; field_simp
  rw [hWB]
  unfold Scale.A
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hΩ4, hΔ, hΩ, mul_pos hΔ hΩ]

/-- **Term 3** (the §5 replacement term). -/
private theorem term3_le (hU1 : 1 ≤ P.U) :
    (10:ℝ)^45 * ((1/S.Δ) * P.G^3 * P.U^10 / S.Ω^5)
      ≤ ((10:ℝ)^60/3) * δunif P S := by
  have hG := P.G_pos; have hU := P.U_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [δunif_eq]
  have lhs_eq : (10:ℝ)^45 * ((1/S.Δ) * P.G^3 * P.U^10 / S.Ω^5)
      = ((10:ℝ)^45 * P.G^3 * P.U^10) / (S.Δ * S.Ω^5) := by field_simp
  have rhs_eq : ((10:ℝ)^60/3) * (P.G^3 * P.U^15 / (S.Δ * S.Ω^5))
      = (((10:ℝ)^60/3) * P.G^3 * P.U^15) / (S.Δ * S.Ω^5) := by ring
  rw [lhs_eq, rhs_eq]
  have hUU : P.U^10 ≤ P.U^15 := by
    have := pow_le_pow_right₀ hU1 (by norm_num : 10 ≤ 15); simpa using this
  gcongr ?_ / _
  nlinarith [pow_pos hG 3, pow_pos hU 15, pow_pos hU 10, hUU, pow_pos hG 3]

/-- **Term 1** (the near-integer term). -/
private theorem term1_le {ℓ₁ ℓ₂ d d₁ d₂ : ℝ}
    (hℓ1n : 0 ≤ ℓ₁) (hℓ2n : 0 ≤ ℓ₂) (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5))
    (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5)) (hd_lo : S.D ≤ d) (hd1pos : S.D ≤ d₁)
    (hd2pos : S.D ≤ d₂)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U) :
    (ℓ₁ * (2*P.H/d^2 + 2*P.H/d₂^2) + ℓ₂ * (2*P.H/d^2 + 2*P.H/d₁^2))
      ≤ ((10:ℝ)^60/3) * δunif P S := by
  have hH := P.H_pos; have hG := P.G_pos; have hU := P.U_pos
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hD : 0 < S.D := by unfold Scale.D; positivity
  have hdpos : 0 < d := lt_of_lt_of_le hD hd_lo
  have hd1 : 0 < d₁ := lt_of_lt_of_le hD hd1pos
  have hd2 : 0 < d₂ := lt_of_lt_of_le hD hd2pos
  set W : ℝ := 130 * (P.G * P.U ^ 5) with hW
  -- Each `2H/(·)² ≤ 2H/D²`.
  have hbd : ∀ e : ℝ, S.D ≤ e → 0 < e → 2*P.H/e^2 ≤ 2*P.H/S.D^2 := by
    intro e he hep
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [hep, hD, he]
  have b_d  := hbd d hd_lo hdpos
  have b_d1 := hbd d₁ hd1pos hd1
  have b_d2 := hbd d₂ hd2pos hd2
  have step1 : (ℓ₁ * (2*P.H/d^2 + 2*P.H/d₂^2) + ℓ₂ * (2*P.H/d^2 + 2*P.H/d₁^2))
      ≤ ℓ₁ * (2*P.H/S.D^2 + 2*P.H/S.D^2) + ℓ₂ * (2*P.H/S.D^2 + 2*P.H/S.D^2) := by
    have e1 : 2*P.H/d^2 + 2*P.H/d₂^2 ≤ 2*P.H/S.D^2 + 2*P.H/S.D^2 := by linarith
    have e2 : 2*P.H/d^2 + 2*P.H/d₁^2 ≤ 2*P.H/S.D^2 + 2*P.H/S.D^2 := by linarith
    have m1 := mul_le_mul_of_nonneg_left e1 hℓ1n
    have m2 := mul_le_mul_of_nonneg_left e2 hℓ2n
    linarith
  have step2 : ℓ₁ * (2*P.H/S.D^2 + 2*P.H/S.D^2) + ℓ₂ * (2*P.H/S.D^2 + 2*P.H/S.D^2)
      ≤ 8 * W * (P.H / S.D^2) := by
    have hrw : 2*P.H/S.D^2 = 2 * (P.H/S.D^2) := by ring
    rw [hrw]
    have hHsq : 0 ≤ P.H/S.D^2 := by positivity
    nlinarith [hℓ1W, hℓ2W, hHsq, mul_nonneg hℓ1n hHsq, mul_nonneg hℓ2n hHsq]
  have step3 : 8 * W * (P.H / S.D^2) ≤ ((10:ℝ)^60/3) * δunif P S := by
    have hDsq : S.D^2 = P.H^2 * S.Δ^2 := by unfold Scale.D; ring
    have lhs_eq : 8 * W * (P.H / S.D^2) = (8 * W * P.H) / (P.H^2 * S.Δ^2) := by
      rw [hDsq]; ring
    have rhs_eq : ((10:ℝ)^60/3) * δunif P S
        = (((10:ℝ)^60/3) * P.G^3 * P.U^15) / (S.Δ * S.Ω^5) := by
      rw [δunif_eq]; ring
    rw [lhs_eq, hW, rhs_eq, div_le_div_iff₀ (by positivity) (by positivity)]
    -- 8·(G U⁵)·H·(Δ Ω⁵) ≤ (10^60/3)·G³U¹⁵·(H²Δ²)
    have hΩ5 : S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩ.le hΩU 5
    have hG2 : (1:ℝ) ≤ P.G^2 := one_le_pow₀ hG1
    have hU5 : (1:ℝ) ≤ P.U^5 := one_le_pow₀ hU1
    have hH1 : (1:ℝ) ≤ P.H := one_le_H h1 hG1 hU1 hΔ1
    have hfac : (1:ℝ) ≤ P.G^2 * P.U^5 * P.H * S.Δ :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hG2 hU5) hH1) hΔ1
    have hg0 : (0:ℝ) ≤ P.G * P.U^10 * P.H * S.Δ := by positivity
    have hbig : (1040:ℝ) * (P.G * P.U^10 * P.H * S.Δ)
        ≤ ((10:ℝ)^60/3) * P.G^3 * P.U^15 * (P.H^2 * S.Δ^2) := by
      have key : ((10:ℝ)^60/3) * P.G^3 * P.U^15 * (P.H^2 * S.Δ^2)
          = (((10:ℝ)^60/3) * (P.G^2 * P.U^5 * P.H * S.Δ))
            * (P.G * P.U^10 * P.H * S.Δ) := by ring
      rw [key]
      have hcoef : (1040:ℝ) ≤ ((10:ℝ)^60/3) * (P.G^2 * P.U^5 * P.H * S.Δ) := by
        calc (1040:ℝ) ≤ (10:ℝ)^60/3 := by norm_num
          _ = ((10:ℝ)^60/3) * 1 := by ring
          _ ≤ ((10:ℝ)^60/3) * (P.G^2 * P.U^5 * P.H * S.Δ) := by
              apply mul_le_mul_of_nonneg_left hfac (by norm_num)
      calc (1040:ℝ) * (P.G * P.U^10 * P.H * S.Δ)
          = 1040 * (P.G * P.U^10 * P.H * S.Δ) := by ring
        _ ≤ (((10:ℝ)^60/3) * (P.G^2 * P.U^5 * P.H * S.Δ)) * (P.G * P.U^10 * P.H * S.Δ) :=
            mul_le_mul_of_nonneg_right hcoef hg0
    calc (8 * (130 * (P.G * P.U ^ 5)) * P.H) * (S.Δ * S.Ω^5)
        ≤ (8 * (130 * (P.G * P.U ^ 5)) * P.H) * (S.Δ * P.U^5) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left hΩ5 (by positivity)
      _ = 1040 * (P.G * P.U^10 * P.H * S.Δ) := by ring
      _ ≤ ((10:ℝ)^60/3) * P.G^3 * P.U^15 * (P.H^2 * S.Δ^2) := hbig
  linarith [step1, step2, step3]

/-- **Term 2** (the `E`-bound term). -/
private theorem term2_le {a ℓ₁ ℓ₂ d b₀ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hℓ1n : 0 ≤ ℓ₁) (hℓ2n : 0 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5)) (hd_lo : S.D ≤ d)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U) :
    400 * P.X * a * |b₀| * ℓ₁ * ℓ₂ * ((a + ℓ₂*|b₀|)^2 + (a + ℓ₁*|b₀|)^2) / d^6
      ≤ ((10:ℝ)^60/3) * δunif P S := by
  have hH := P.H_pos; have hG := P.G_pos; have hU := P.U_pos
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hX := P.X_pos
  have hD : 0 < S.D := by unfold Scale.D; positivity
  have hA : 0 < S.A := by unfold Scale.A; positivity
  have hB : 0 < S.B := by unfold Scale.B; positivity
  have hR : 0 < S.R := by unfold Scale.R; positivity
  have hb0n : 0 ≤ |b₀| := abs_nonneg _
  set W : ℝ := 130 * (P.G * P.U ^ 5) with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  -- `a + ℓ_i|b₀| ≤ M := 4e12·(W·B)`.
  have hAWB : S.A ≤ W * S.B := by
    refine le_trans (A_le_W_B hU1 hΔ1 hΩU) ?_
    rw [hW]
    have hBnn : (0:ℝ) ≤ S.B := by
      have := S.Δ_pos; have := P.G_pos; have := S.Ω_pos
      unfold Scale.B; positivity
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ P.G * P.U ^ 5) hBnn]
  have habℓ : ∀ ℓ : ℝ, ℓ ≤ W → 0 ≤ ℓ → a + ℓ * |b₀| ≤ 4000000000000 * (W * S.B) := by
    intro ℓ hℓW hℓn
    have e1 : a ≤ 11 * (W * S.B) := le_trans ha_hi (by nlinarith [hAWB, hA])
    have e2 : ℓ * |b₀| ≤ W * (3000000000000 * S.B) :=
      mul_le_mul hℓW hb0 hb0n hWpos.le
    nlinarith [e1, e2]
  have hab1 := habℓ ℓ₁ hℓ1W hℓ1n
  have hab2 := habℓ ℓ₂ hℓ2W hℓ2n
  have hab1n : 0 ≤ a + ℓ₁ * |b₀| := by positivity
  have hab2n : 0 ≤ a + ℓ₂ * |b₀| := by positivity
  set M : ℝ := 4000000000000 * (W * S.B) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hsq1 : (a + ℓ₁*|b₀|)^2 ≤ M^2 := by
    have := mul_le_mul hab1 hab1 hab1n hMpos.le; nlinarith [this]
  have hsq2 : (a + ℓ₂*|b₀|)^2 ≤ M^2 := by
    have := mul_le_mul hab2 hab2 hab2n hMpos.le; nlinarith [this]
  have hsqsum : (a + ℓ₂*|b₀|)^2 + (a + ℓ₁*|b₀|)^2 ≤ 2 * M^2 := by linarith
  -- Numerator bound:  400·X·a·|b₀|·ℓ₁·ℓ₂·(sum) ≤ N.
  set N : ℝ := 400 * P.X * (11*S.A) * (3000000000000 * S.B) * W * W * (2 * M^2)
    with hN
  have hnum : 400 * P.X * a * |b₀| * ℓ₁ * ℓ₂
      * ((a + ℓ₂*|b₀|)^2 + (a + ℓ₁*|b₀|)^2) ≤ N := by
    rw [hN]
    gcongr 400 * P.X * ?_ * ?_ * ?_ * ?_ * ?_
  -- Divide by d⁶ ≥ D⁶ > 0.
  have hD6 : 0 < S.D^6 := by positivity
  have hNpos : 0 ≤ N := by rw [hN]; positivity
  have hdiv1 : 400 * P.X * a * |b₀| * ℓ₁ * ℓ₂
        * ((a + ℓ₂*|b₀|)^2 + (a + ℓ₁*|b₀|)^2) / d^6 ≤ N / S.D^6 := by
    apply div_le_div₀ hNpos hnum hD6
    exact pow_le_pow_left₀ hD.le hd_lo 6
  refine le_trans hdiv1 ?_
  -- `N/D⁶ = C₀·(X·A·B³/D⁶)·W⁴ = C₀·W⁴/(G·Ω⁵·R)`, then bound.
  have hNeq : N / S.D^6
      = (400 * 11 * 3000000000000 * 2 * (4000000000000^2))
        * (P.X * S.A * S.B^3 / S.D^6) * W^4 := by
    rw [hN, hM]; ring
  rw [hNeq, defect_XAB3_div_D6' S]
  have hWdef : W^4 = 285610000 * (P.G^4 * P.U^20) := by rw [hW]; ring
  have hRdef : S.R = P.H * P.G * S.Ω ^ 3 / S.Δ := rfl
  have lhs_eq : (400 * 11 * 3000000000000 * 2 * (4000000000000^2))
        * (1 / (P.G * S.Ω^5 * S.R)) * W^4
      = ((400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000) * P.G^2 * P.U^20 * S.Δ)
        / (P.H * S.Ω^8) := by
    rw [hRdef, hWdef]; field_simp; try ring
  rw [lhs_eq, δunif_eq]
  have rhs_eq : ((10:ℝ)^60/3) * (P.G^3 * P.U^15 / (S.Δ * S.Ω^5))
      = (((10:ℝ)^60/3) * P.G^3 * P.U^15) / (S.Δ * S.Ω^5) := by ring
  rw [rhs_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  -- Cross goal:  (C₀·G²·U²⁰·Δ)·(Δ·Ω⁵) ≤ ((10^60/3)·G³·U¹⁵)·(H·Ω⁸).
  -- i.e.  C₀·G²·U²⁰·Δ²·Ω⁵ ≤ (10^60/3)·G³·U¹⁵·H·Ω⁸.
  -- From h1:  G·U^10·Δ² ≤ H.
  have hh1 : P.G * P.U^10 * S.Δ^2 ≤ P.H := by
    have hx := h1
    rw [le_div_iff₀ (by positivity)] at hx
    linarith [hx]
  -- From band & Ω ≤ U:  1 ≤ G·U⁴·Ω³  (since G·U³·Ω⁴ = G·U³·Ω³·Ω ≤ G·U⁴·Ω³).
  have hbandΩ : (1:ℝ) ≤ P.G * P.U^4 * S.Ω^3 := by
    have hstep : P.G * P.U^3 * S.Ω^4 ≤ P.G * P.U^4 * S.Ω^3 := by
      have : S.Ω^4 = S.Ω^3 * S.Ω := by ring
      nlinarith [hΩU, pow_pos hΩ 3, mul_pos (mul_pos hG (pow_pos hU 3)) (pow_pos hΩ 3),
        pow_pos hU 3]
    linarith [hband, hstep]
  have hCpos : (0:ℝ) < 400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 := by norm_num
  have hCle : (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 : ℝ) ≤ (10:ℝ)^60/3 := by
    norm_num
  -- stepA: LHS = C₀·Ω⁵·(G·U¹⁰)·(G·U¹⁰·Δ²) ≤ C₀·Ω⁵·(G·U¹⁰)·H.
  have stepA : (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 * P.G^2
          * P.U^20 * S.Δ)
        * (S.Δ * S.Ω^5)
      ≤ (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000)
        * (S.Ω^5 * (P.G * P.U^10)) * P.H := by
    have e : (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 * P.G^2
            * P.U^20 * S.Δ)
          * (S.Δ * S.Ω^5)
        = ((400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000)
          * (S.Ω^5 * (P.G * P.U^10))) * (P.G * P.U^10 * S.Δ^2) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left hh1 (by positivity)
  -- stepB: C₀·Ω⁵·(G·U¹⁰)·H ≤ (10^60/3)·G³·U¹⁵·H·Ω⁸.
  have stepB : (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000)
        * (S.Ω^5 * (P.G * P.U^10)) * P.H
      ≤ (((10:ℝ)^60/3) * P.G^3 * P.U^15) * (P.H * S.Ω^8) := by
    -- coefficient bound:  C₀ ≤ (10^60/3)·(G·U·(G·U⁴·Ω³)).
    have hcoef : (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 : ℝ)
        ≤ ((10:ℝ)^60/3) * (P.G * P.U * (P.G * P.U^4 * S.Ω^3)) := by
      have hGU1 : (1:ℝ) ≤ P.G * P.U := one_le_mul_of_one_le_of_one_le hG1 hU1
      have hbig : (1:ℝ) ≤ P.G * P.U * (P.G * P.U^4 * S.Ω^3) := by
        nlinarith [hGU1, hbandΩ, mul_pos hG hU,
          mul_pos (mul_pos hG (pow_pos hU 4)) (pow_pos hΩ 3)]
      calc (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 : ℝ)
          ≤ (10:ℝ)^60/3 := hCle
        _ = ((10:ℝ)^60/3) * 1 := by ring
        _ ≤ ((10:ℝ)^60/3) * (P.G * P.U * (P.G * P.U^4 * S.Ω^3)) :=
            mul_le_mul_of_nonneg_left hbig (by norm_num)
    -- assemble:  RHS = ((10^60/3)·(G·U·(G·U⁴·Ω³))) · (Ω⁵·(G·U¹⁰)·H).
    have efactR : (((10:ℝ)^60/3) * P.G^3 * P.U^15) * (P.H * S.Ω^8)
        = (((10:ℝ)^60/3) * (P.G * P.U * (P.G * P.U^4 * S.Ω^3)))
          * (S.Ω^5 * (P.G * P.U^10) * P.H) := by ring
    have efactL : (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 : ℝ)
          * (S.Ω^5 * (P.G * P.U^10)) * P.H
        = (400 * 11 * 3000000000000 * 2 * (4000000000000^2) * 285610000 : ℝ)
          * (S.Ω^5 * (P.G * P.U^10) * P.H) := by ring
    rw [efactR, efactL]
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  linarith [stepA, stepB]

/-- The per-`r` effective defect (the `phi_norm_le_v0` RHS) is bounded by the clean
uniform scale `δ_unif := 10^60·(1/Δ)·G³·U¹⁵/Ω⁵`.  Constant loose by design. -/
theorem delta_eff_le {a : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ b₀ : ℝ}
    (ha_hi : a ≤ 11 * S.A) (ha0 : 0 < a)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (hdwin : S.D ≤ d ∧ d ≤ 2*S.D) (hd1pos : S.D ≤ d₁) (hd2pos : S.D ≤ d₂)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U) :
    (ℓ₁ * (2*P.H/d^2 + 2*P.H/d₂^2) + ℓ₂ * (2*P.H/d^2 + 2*P.H/d₁^2))
      + 400 * P.X * a * |b₀| * ℓ₁ * ℓ₂ * ((a + ℓ₂*|b₀|)^2 + (a + ℓ₁*|b₀|)^2) / d^6
      + (10:ℝ)^45 * ((1/S.Δ) * P.G^3 * P.U^10 / S.Ω^5)
    ≤ (10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5) := by
  obtain ⟨hd_lo, hd_hi⟩ := hdwin
  have hℓ1n : 0 ≤ ℓ₁ := hℓ1.le
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have hℓ2n : 0 ≤ ℓ₂ := hℓ2.le
  have hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_of_lt (lt_of_lt_of_le hℓ12 hℓ2W)
  have hT1 := term1_le hℓ1n hℓ2n hℓ1W hℓ2W hd_lo hd1pos hd2pos h1 hG1 hU1 hΔ1 hΩU
  have hT2 := term2_le ha0 ha_hi hℓ1n hℓ2n hℓ1W hℓ2W hd_lo hb0 h1 hband hG1 hU1 hΔ1 hΩU
  have hT3 := term3_le (P := P) (S := S) hU1
  -- Combine.  3·(10^60/3)·δ_unif = 10^60·δ_unif = RHS.
  have hRHS : (10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5) = (10:ℝ)^60 * δunif P S := rfl
  have hsum : ((10:ℝ)^60/3) * δunif P S + ((10:ℝ)^60/3) * δunif P S
      + ((10:ℝ)^60/3) * δunif P S = (10:ℝ)^60 * δunif P S := by ring
  rw [hRHS]
  linarith [hT1, hT2, hT3, hsum]

end Squarefree
