import Squarefree.Lower.Step4FitEA

/-!
# §5 Step-4 hybrid E-part fit, A-half: capped summand and `cE`-fit
The `Ecap4` flat/degree-4 capped pieces, the `m`-reduction, and the full A-half
`cEhyb` fit `step4_fit_cE_A` assembled from the `Step4FitEA` `T1'`/`T2'` budgets.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}


/-- Flat `Ecap4` piece: `(480·a·L·ℓ₁²·Vmax²/D²)·b·m` fits one `C¹`-block (fraction form). -/
private theorem step4_fitEA_capFlat
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12)
    (hm0 : 0 ≤ m) (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (480 * a * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2 * (Vmax P S) ^ 2 / S.D ^ 2) * b * m
      ≤ C * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hd0 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hL0 : (0:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_nonneg (mul_nonneg hℓ1pos.le hℓ2pos.le) hd0
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  rw [show Vmax P S = 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) from rfl,
    show S.D = P.H * S.Δ from rfl, hb]
  have hmul0 : 0 ≤ 480 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
      * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL0) (by positivity))
      (by positivity)) (by positivity)
  have hcoef : 480 * a * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2
      ≤ 11 * (S.Δ * S.Ω) * (480 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2) := by
    calc 480 * a * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
          * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2
        = a * (480 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
          * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2) := by ring
      _ ≤ 11 * (S.Δ * S.Ω) * (480 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
          * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2) :=
          mul_le_mul_of_nonneg_right ha' hmul0
  have hprod : (480 * a * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2)
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) * m
      ≤ 11 * (S.Δ * S.Ω) * (480 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2)
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
        * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity)) hm hm0
      (mul_nonneg (mul_nonneg (by positivity) hmul0) (by positivity))
  refine le_trans hprod ?_
  have hsplit : 11 * (S.Δ * S.Ω) * (480 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 2 / (P.H * S.Δ) ^ 2)
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
        * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12)
      = 528 * 10 ^ 101 * C * P.U ^ 40 * P.G ^ 5
        * (ℓ₁ ^ 7 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * (ℓ₂ - ℓ₁)) / (S.Δ * P.H * S.Ω ^ 19) := by
    field_simp
    ring
  rw [hsplit]
  have hdW : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hWf : ℓ₁ ^ 7 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * (ℓ₂ - ℓ₁) ≤ 10 ^ 24 * (P.G ^ 11 * P.U ^ 55) := by
    calc ℓ₁ ^ 7 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * (ℓ₂ - ℓ₁)
        ≤ (130 ^ (7 + 2 + 1)
              * ((P.G * P.U ^ 5) ^ 7 * (P.G * P.U ^ 5) ^ 2 * (P.G * P.U ^ 5)))
            * (130 * (P.G * P.U ^ 5)) :=
          mul_le_mul (step4_fitEA_window ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W 7 2) hdW hd0
            (by positivity)
      _ = 130 ^ 11 * (P.G ^ 11 * P.U ^ 55) := by ring
      _ ≤ 10 ^ 24 * (P.G ^ 11 * P.U ^ 55) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  exact step4_fitEA_coreF h1 hDeW hG1 hU1 hΩU hband hUbig C hCnn _ hWf

/-- Degree-4 capped `p₂` piece: `(1540·a·(GΩ/Δ⁴)·ℓ₁³(2ℓ₂−ℓ₁)·Vmax⁴/D)·b·m` fits one
`C¹`-block (fraction form). -/
private theorem step4_fitEA_capP4
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12)
    (hm0 : 0 ≤ m) (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (1540 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (Vmax P S) ^ 4 / S.D)
        * b * m
      ≤ C * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hd0 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h2ℓ0 : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hGne : P.G ≠ 0 := ne_of_gt hGpos
  have hLm0 : (0:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h2ℓ0
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  rw [show Vmax P S = 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) from rfl,
    show S.D = P.H * S.Δ from rfl, hb]
  have hmul0 : 0 ≤ 1540 * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
      * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hLm0)
      (by positivity)) (by positivity)
  have hcoef : 1540 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ)
      ≤ 11 * (S.Δ * S.Ω) * (1540 * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ)) := by
    calc 1540 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
          * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ)
        = a * (1540 * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
          * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha' hmul0
  have hprod : (1540 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) * m
      ≤ 11 * (S.Δ * S.Ω) * (1540 * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
        * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity)) hm hm0
      (mul_nonneg (mul_nonneg (by positivity) hmul0) (by positivity))
  refine le_trans hprod ?_
  have hsplit : 11 * (S.Δ * S.Ω) * (1540 * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
        * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ^ 4 / (P.H * S.Δ))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
        * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12)
      = 1694 * 10 ^ 141 * C * P.G ^ 6 * P.U ^ 50
        * (ℓ₁ ^ 7 * ℓ₂ * (ℓ₂ - ℓ₁) * (2 * ℓ₂ - ℓ₁)) / (S.Δ ^ 2 * S.Ω ^ 24) := by
    field_simp
    ring
  rw [hsplit]
  have h2W : 2 * ℓ₂ - ℓ₁ ≤ 260 * (P.G * P.U ^ 5) := by linarith
  have hWp : ℓ₁ ^ 7 * ℓ₂ * (ℓ₂ - ℓ₁) * (2 * ℓ₂ - ℓ₁)
      ≤ 2 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50) := by
    calc ℓ₁ ^ 7 * ℓ₂ * (ℓ₂ - ℓ₁) * (2 * ℓ₂ - ℓ₁)
        ≤ (130 ^ (7 + 1 + 1)
              * ((P.G * P.U ^ 5) ^ 7 * (P.G * P.U ^ 5) ^ 1 * (P.G * P.U ^ 5)))
            * (260 * (P.G * P.U ^ 5)) := by
          refine mul_le_mul ?_ h2W h2ℓ0 (by positivity)
          have := step4_fitEA_window ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W 7 1
          calc ℓ₁ ^ 7 * ℓ₂ * (ℓ₂ - ℓ₁) = ℓ₁ ^ 7 * ℓ₂ ^ 1 * (ℓ₂ - ℓ₁) := by ring
            _ ≤ _ := this
      _ = 2 * 130 ^ 10 * (P.G ^ 10 * P.U ^ 50) := by ring
      _ ≤ 2 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  exact step4_fitEA_coreP4 h1 hDeW hG1 hU1 hΩU hband hUbig C hCnn _ hWp

/-- **Hybrid fit, capped summand, `C¹` form.** The `Ecap4`-summand product
`(4a·Ecap4a)·b·m` fits two `C¹·(H/Δ)`-blocks (flat + p₄), for the SHARP `m`-cap
`m ≤ 10⁶⁰·C·ℓ₁³·L·U¹⁵/Ω¹²` (the genuine `(N√N)/√L` budget; the padded `U²⁵/Ω⁸` form
is too weak for the tight degree-3 piece). -/
theorem step4_fitEA_cap
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12)
    (hm0 : 0 ≤ m)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (4 * a * Ecap4a P S a ℓ₁ ℓ₂) * b * m
      ≤ 2 * (C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))) := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  have hane : a ≠ 0 := ne_of_gt ha0
  have hchat : (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
      = 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / S.D ^ 2 := step4_fitEA_chat hane ℓ₁ ℓ₂
  have hexp : (4 * a * Ecap4a P S a ℓ₁ ℓ₂) * b * m
      = (480 * a * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ℓ₁ ^ 2 * (Vmax P S) ^ 2 / S.D ^ 2) * b * m
        + (1540 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
            * (Vmax P S) ^ 4 / S.D) * b * m := by
    simp only [Ecap4a]
    linear_combination (160 * a * (ℓ₁ * Vmax P S) ^ 2 * b * m) * hchat
  rw [hexp]
  have hF := step4_fitEA_capFlat h1 hDeW hG1 hU1 hΩU hband hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12
    hℓ1W hℓ2W m C hC hm hm0 a ha_hi b hb
  have hP4 := step4_fitEA_capP4 h1 hDeW hG1 hU1 hΩU hband hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12
    hℓ1W hℓ2W m C hC hm hm0 a ha_hi b hb
  refine le_trans (add_le_add hF hP4) (le_of_eq ?_)
  field_simp
  ring

/-- SHARP `m`-reduction: `(N·√N)/√L ≤ 10⁶⁰·C·ℓ₁³·L·U¹⁵/Ω¹²` from the `N`-cap
`N ≤ C·ℓ₁²·L·U¹⁰/Ω⁸`, spending `√C ≤ 10⁶⁰` (technique of `step4_fit_cubic_B`). -/
private theorem step4_fitEA_mred
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNcap : (N:ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8) :
    (N:ℝ) * Real.sqrt (N:ℝ) / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
      ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12 := by
  have hUpos := P.U_pos
  have hΩpos := S.Ω_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hL0 : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_pos (mul_pos hℓ1pos hℓ2pos) (by linarith)
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  set s : ℝ := Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hL0
  have hss : s * s = ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := Real.mul_self_sqrt hL0.le
  have hCs : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hCnn
  have hkey : (Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) ^ 2
      = C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8 := by
    calc (Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) ^ 2
        = (Real.sqrt C * Real.sqrt C) * ℓ₁ ^ 2 * (s * s) * P.U ^ 10 / S.Ω ^ 8 := by
          field_simp
      _ = C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8 := by rw [hCs, hss]
  have hsqN : Real.sqrt (N:ℝ) ≤ Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := by
    calc Real.sqrt (N:ℝ)
        ≤ Real.sqrt (C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8) :=
          Real.sqrt_le_sqrt hNcap
      _ = Real.sqrt ((Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) ^ 2) := by rw [hkey]
      _ = Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := Real.sqrt_sq (by positivity)
  have hsqC : Real.sqrt C ≤ (10:ℝ) ^ 60 := by
    calc Real.sqrt C ≤ Real.sqrt ((10:ℝ) ^ 120) := Real.sqrt_le_sqrt hCcap
      _ = Real.sqrt (((10:ℝ) ^ 60) ^ 2) := by rw [← pow_mul]
      _ = (10:ℝ) ^ 60 := Real.sqrt_sq (by positivity)
  have hsqN' : Real.sqrt (N:ℝ) ≤ 10 ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := by
    refine le_trans hsqN ?_
    gcongr ?_ * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4
  have hNs : (N:ℝ) * Real.sqrt (N:ℝ)
      ≤ (C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
        * (10 ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) :=
    mul_le_mul hNcap hsqN' (Real.sqrt_nonneg _) (by positivity)
  rw [div_le_iff₀ hspos]
  refine le_trans hNs (le_of_eq ?_)
  field_simp

/-- **§5 Step-4 hybrid `cE`-fit, A-half.** The full `cEhyb` coefficient times `b·N√N`
fits eight `C¹·(H/Δ)·t`-blocks: `T1 ≤ 2`, `T2 ≤ 1`, capped summand `≤ 2`, total `5 ≤ 8`. -/
theorem step4_fit_cE_A
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNcap : (N:ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (a gap : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
        + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    cEhyb P S a ℓ₁ ℓ₂ gap * b * ((N:ℝ) * Real.sqrt (N:ℝ))
      ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hL0 : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_pos (mul_pos hℓ1pos hℓ2pos) (by linarith)
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hΩpos := S.Ω_pos
  have hsL : 0 < Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := Real.sqrt_pos.mpr hL0
  have hsLne : Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≠ 0 := ne_of_gt hsL
  set m : ℝ := (N:ℝ) * Real.sqrt (N:ℝ) / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) with hmdef
  have hm0 : 0 ≤ m :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _)) hsL.le
  have hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 / S.Ω ^ 12 :=
    step4_fitEA_mred N ℓ₁ ℓ₂ hℓ1lo hℓ12 C hC hCcap hNcap
  have hX0 : 0 ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)) hL0.le
  have hmpad : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 := by
    refine le_trans hm ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpay : (1:ℝ) ≤ P.G * P.U ^ 10 * S.Ω ^ 4 := by
      calc (1:ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
        _ = P.G * P.U ^ 3 * S.Ω ^ 4 * 1 := (mul_one _).symm
        _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * P.U ^ 7 :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ hU1) (by positivity)
        _ = P.G * P.U ^ 10 * S.Ω ^ 4 := by ring
    calc 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 * S.Ω ^ 8
        = (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 * S.Ω ^ 8) * 1 :=
          (mul_one _).symm
      _ ≤ (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 15 * S.Ω ^ 8)
            * (P.G * P.U ^ 10 * S.Ω ^ 4) := by
          exact mul_le_mul_of_nonneg_left hpay
            (mul_nonneg (mul_nonneg hX0 (by positivity)) (by positivity))
      _ = 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 * S.Ω ^ 12 := by
          ring
  have hsplitE : cEhyb P S a ℓ₁ ℓ₂ gap * b * ((N:ℝ) * Real.sqrt (N:ℝ))
      = (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * m
        + (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)) * b * m
        + (4 * a * Ecap4a P S a ℓ₁ ℓ₂) * b * m := by
    rw [hmdef]
    simp only [cEhyb]
    field_simp
  rw [hsplitE]
  have hT1 := step4_fitEA_T1' h1 hG1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W m C hC
    hmpad hm0 a ha_hi gap hgap0 hgap b hb
  have hT2 := step4_fitEA_T2' h1 hG1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W m C hC
    hmpad hm0 a ha_hi b hb
  have hCap := step4_fitEA_cap h1 hDeW hG1 hU1 hΩU hband hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W
    hℓ2W m C hC hm hm0 a ha0 ha_hi b hb
  have hblock0 : 0 ≤ C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by
    have := P.H_pos; have := S.Δ_pos; have := P.G_pos; have := P.U_pos
    positivity
  have htot := add_le_add (add_le_add hT1 hT2) hCap
  refine le_trans htot ?_
  linarith only [hblock0]

end Squarefree
