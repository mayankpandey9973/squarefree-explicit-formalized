import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Global parameters and scale identities (layer L0)

`Globals` carries `X, g, u` with `H = X^{(1-g)/5}`, `G = X^g`, `U = X^u`.
A `Scale` carries the dyadic data `Δ, Ω` and derives `D, A, x, F, R, B, T₁, T₂, T₃`.
The scale identities (verified in `math_audit.md` §3/§5/§7) are proved here once, so that
section proofs may cite them rather than re-deriving rpow algebra.  See `formalization_plan.md` §2.
-/

namespace Squarefree

/-- Global parameters of the problem. -/
structure Globals where
  X : ℝ
  g : ℝ
  u : ℝ
  X_pos : 0 < X

namespace Globals
variable (P : Globals)

/-- `H = X^{(1-g)/5}`. -/
noncomputable def H : ℝ := P.X ^ ((1 - P.g) / 5)
/-- `G = X^g`. -/
noncomputable def G : ℝ := P.X ^ P.g
/-- `U = X^u`. -/
noncomputable def U : ℝ := P.X ^ P.u

theorem H_pos : 0 < P.H := Real.rpow_pos_of_pos P.X_pos _
theorem G_pos : 0 < P.G := Real.rpow_pos_of_pos P.X_pos _
theorem U_pos : 0 < P.U := Real.rpow_pos_of_pos P.X_pos _

/-- The defining identity `X = G · H^5`. -/
theorem X_eq_G_mul_H_pow_five : P.X = P.G * P.H ^ 5 := by
  rw [H, G, ← Real.rpow_natCast (P.X ^ ((1 - P.g) / 5)) 5,
    ← Real.rpow_mul P.X_pos.le, ← Real.rpow_add P.X_pos]
  rw [show P.g + (1 - P.g) / 5 * (5 : ℕ) = (1 : ℝ) by push_cast; ring, Real.rpow_one]

/-- `W ≍ G·U⁵` — the §5/§7 bottleneck scale. -/
noncomputable def Wval (P : Globals) : ℝ := P.G * P.U ^ 5

end Globals

/-- A dyadic scale: `Δ` (so `D = HΔ`) and `Ω` (so `A = ΔΩ`). -/
structure Scale (P : Globals) where
  Δ : ℝ
  Ω : ℝ
  Δ_pos : 0 < Δ
  Ω_pos : 0 < Ω

namespace Scale
variable {P : Globals} (S : Scale P)

/-- `D = H·Δ`. -/
noncomputable def D : ℝ := P.H * S.Δ
/-- `A = Δ·Ω`. -/
noncomputable def A : ℝ := S.Δ * S.Ω
/-- `x = H/Δ²`. -/
noncomputable def x : ℝ := P.H / S.Δ ^ 2
/-- `F = H²·G·Ω/Δ²`. -/
noncomputable def F : ℝ := P.H ^ 2 * P.G * S.Ω / S.Δ ^ 2
/-- `R = H·G·Ω³/Δ`. -/
noncomputable def R : ℝ := P.H * P.G * S.Ω ^ 3 / S.Δ
/-- `B = Δ²/(G·Ω³)`. -/
noncomputable def B : ℝ := S.Δ ^ 2 / (P.G * S.Ω ^ 3)
/-- `T₃ = H·Δ`. -/
noncomputable def T₃ : ℝ := P.H * S.Δ
/-- `T₂ = F`. -/
noncomputable def T₂ : ℝ := S.F
/-- `T₁ = H·Δ/F`. -/
noncomputable def T₁ : ℝ := P.H * S.Δ / S.F

/-- `F > 0` (since `H, G, Ω, Δ > 0`). -/
private theorem F_pos : 0 < S.F := by
  have := P.H_pos; have := P.G_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold Scale.F
  positivity

/-- `R` agrees with its writeup definition `X·A³/(Δ⁴·H⁴)`. -/
theorem R_eq_orig : S.R = P.X * S.A ^ 3 / (S.Δ ^ 4 * P.H ^ 4) := by
  have hH := P.H_pos; have hΔ := S.Δ_pos
  unfold Scale.R Scale.A
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp
/-- `B = D/R`. -/
theorem B_eq_D_div_R : S.B = S.D / S.R := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.B Scale.D Scale.R
  field_simp
/-- `F = H·x·G·Ω`. -/
theorem F_eq_H_x_G_Ω : S.F = P.H * S.x * P.G * S.Ω := by
  have hΔ := S.Δ_pos
  unfold Scale.F Scale.x
  field_simp
/-- `T₁·T₂ = T₃`. -/
theorem T₁_mul_T₂_eq_T₃ : S.T₁ * S.T₂ = S.T₃ := by
  have hF := S.F_pos
  unfold Scale.T₁ Scale.T₂ Scale.T₃
  field_simp

end Scale
end Squarefree
