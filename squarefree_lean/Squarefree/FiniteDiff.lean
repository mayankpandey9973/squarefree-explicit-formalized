import Mathlib.Data.Real.Basic

/-!
# Finite-difference operator (layer L0)

The mixed forward differences used by Lemmas 2.1 and §7.  Integral/Taylor representations
(`Δ_{h₁,h₂,h₃} f = h₁h₂h₃ ∫ f''' …`) are added as needed (M2/M4).
-/

namespace Squarefree.FiniteDiff

/-- First forward difference `(Δ_h f)(x) = f(x + h) - f(x)`. -/
def diff1 (h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (x + h) - f x

/-- Mixed third forward difference `Δ_{h₁,h₂,h₃} = Δ_{h₁} ∘ Δ_{h₂} ∘ Δ_{h₃}`. -/
def diff3 (h₁ h₂ h₃ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  diff1 h₁ (diff1 h₂ (diff1 h₃ f))

end Squarefree.FiniteDiff
