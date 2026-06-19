import Squarefree.Params

/-!
# §5 scale (defect) identities

Six exact algebraic scale identities used in §5 of the writeup
(`explicit_writeup.md`, lines 676–1225). Each is a pure-algebra rewrite of the
derived `Scale.*` quantities (`A = ΔΩ`, `B = Δ²/(G·Ω³)`, `D = HΔ`) using the
global relation `X = G·H⁵`. All six are sympy-verified true; here we just supply
the Lean proofs. They are public — downstream §5 modules consume them.
-/

namespace Squarefree

variable {P : Globals} (S : Scale P)

theorem defect_XAB_div_D5 :
    P.X * S.A * S.B / S.D ^ 5 = 1 / (S.Δ ^ 2 * S.Ω ^ 2) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.B Scale.D
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

theorem defect_XAB3_div_D6 :
    P.X * S.A * S.B ^ 3 / S.D ^ 6 = S.Δ / (P.H * P.G ^ 2 * S.Ω ^ 8) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.B Scale.D
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

theorem defect_D4_div_XA :
    S.D ^ 4 / (P.X * S.A) = S.Δ ^ 3 / (P.H * P.G * S.Ω) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.D
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

theorem defect_B2_div_D :
    S.B ^ 2 / S.D = S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.B Scale.D
  field_simp

theorem defect_D5_div_XAB :
    S.D ^ 5 / (P.X * S.A * S.B) = S.Δ ^ 2 * S.Ω ^ 2 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.B Scale.D
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

theorem defect_XAB2_div_D5 :
    P.X * S.A * S.B ^ 2 / S.D ^ 5 = 1 / (P.G * S.Ω ^ 5) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.B Scale.D
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

/-- `X·A·B/D⁴ = R/(G·Ω⁵)` (used for the §5 Step-1 phase-derivative scale `|φ'| ≍ L/R`). -/
theorem defect_XAB_div_D4 :
    P.X * S.A * S.B / S.D ^ 4 = S.R / (P.G * S.Ω ^ 5) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.B Scale.D Scale.R
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

/-- `X·A·B³/D⁶ = 1/(G·Ω⁵·R)` (= `Δ/(H·G²·Ω⁸)`); used for the §5 Step-1 phase-derivative
upper bound `|φ'| ≤ C·L/R`. -/
theorem defect_XAB3_div_D6' :
    P.X * S.A * S.B ^ 3 / S.D ^ 6 = 1 / (P.G * S.Ω ^ 5 * S.R) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.B Scale.D Scale.R
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

/-- §5 regime smallness `R ≥ U·W` (`W = G·U⁵`), i.e. the `W/R` smallness of writeup
798–800 in multiplicative form. From `h1 : G·U¹⁰ ≤ H/Δ²`, the band `1 ≤ G·U³·Ω⁴`, and
`Ω ≤ U`, `1 ≤ Δ`, `1 ≤ U`. Used to discharge both `10³³ℓ₁ ≤ R` and the Taylor window
bound in the Step-1 modeling. -/
theorem U_mul_W_le_R
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hΩU : S.Ω ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hU1 : 1 ≤ P.U) :
    P.U * P.Wval ≤ S.R := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hU0 : (0:ℝ) < P.U := lt_of_lt_of_le one_pos hU1
  -- `H ≥ G·U¹⁰·Δ²`.
  have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
    (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
  -- the factor `G·U⁴·Δ·Ω³ ≥ 1`.
  have hUDΩ : S.Ω ≤ P.U * S.Δ := by
    nlinarith [mul_nonneg hU0.le (show (0:ℝ) ≤ S.Δ - 1 by linarith), hΩU]
  have hfac : (1:ℝ) ≤ P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3 := by
    have h2 : P.G * P.U ^ 3 * S.Ω ^ 4 ≤ P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 3 by positivity)
        (show (0:ℝ) ≤ P.U * S.Δ - S.Ω by linarith)]
    linarith
  -- conclude `U·W = G·U⁶ ≤ R = H·G·Ω³/Δ`.
  unfold Scale.R Globals.Wval
  rw [le_div_iff₀ hΔ]
  calc P.U * (P.G * P.U ^ 5) * S.Δ
      = (P.G * P.U ^ 6 * S.Δ) * 1 := by ring
    _ ≤ (P.G * P.U ^ 6 * S.Δ) * (P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (P.G * P.U ^ 10 * S.Δ ^ 2) * (P.G * S.Ω ^ 3) := by ring
    _ ≤ P.H * (P.G * S.Ω ^ 3) := mul_le_mul_of_nonneg_right hHbig (by positivity)
    _ = P.H * P.G * S.Ω ^ 3 := by ring

/-- 130-strengthened `U·W ≤ R` (for the relaxed pair-cap `ℓ ≤ 130·W` window chains):
`130·U·W ≤ R`, using `(G·U⁴·Δ·Ω³)⁴ = (G·U³·Ω⁴)³·(G·Δ⁴)·U⁷ ≥ U⁷ ≥ 130⁴`. -/
theorem U_mul_W130_le_R
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (_hΩU : S.Ω ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hU1 : 1 ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U) (hG1 : 1 ≤ P.G) :
    130 * (P.U * P.Wval) ≤ S.R := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hU0 : (0:ℝ) < P.U := lt_of_lt_of_le one_pos hU1
  have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
    (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
  have hfac : (130:ℝ) ≤ P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3 := by
    have hb3 : (1:ℝ) ≤ (P.G * P.U ^ 3 * S.Ω ^ 4) ^ 3 := one_le_pow₀ hband
    have hU7 : (130:ℝ) ^ 4 ≤ P.U ^ 7 := by
      calc (130:ℝ) ^ 4 ≤ (10:ℝ) ^ 231 := by norm_num
        _ = ((10:ℝ) ^ 33) ^ 7 := by rw [← pow_mul]
        _ ≤ P.U ^ 7 := pow_le_pow_left₀ (by positivity) hUbig 7
    have hGd : (1:ℝ) ≤ P.G * S.Δ ^ 4 := by
      have h4 := one_le_pow₀ (n := 4) hΔ1
      nlinarith [h4, hG1]
    have hkey : (130:ℝ) ^ 4 ≤ (P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3) ^ 4 := by
      have hid : (P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3) ^ 4
          = (P.G * P.U ^ 3 * S.Ω ^ 4) ^ 3 * (P.G * S.Δ ^ 4) * P.U ^ 7 := by ring
      rw [hid]
      calc (130:ℝ) ^ 4 ≤ P.U ^ 7 := hU7
        _ = 1 * 1 * P.U ^ 7 := by ring
        _ ≤ (P.G * P.U ^ 3 * S.Ω ^ 4) ^ 3 * (P.G * S.Δ ^ 4) * P.U ^ 7 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul hb3 hGd (by norm_num) (by positivity)
    have hQnn : (0:ℝ) ≤ P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3 := by positivity
    exact le_of_pow_le_pow_left₀ (by norm_num) hQnn hkey
  unfold Scale.R Globals.Wval
  rw [le_div_iff₀ hΔ]
  calc 130 * (P.U * (P.G * P.U ^ 5)) * S.Δ
      = (P.G * P.U ^ 6 * S.Δ) * 130 := by ring
    _ ≤ (P.G * P.U ^ 6 * S.Δ) * (P.G * P.U ^ 4 * S.Δ * S.Ω ^ 3) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (P.G * P.U ^ 10 * S.Δ ^ 2) * (P.G * S.Ω ^ 3) := by ring
    _ ≤ P.H * (P.G * S.Ω ^ 3) := mul_le_mul_of_nonneg_right hHbig (by positivity)
    _ = P.H * P.G * S.Ω ^ 3 := by ring

end Squarefree
