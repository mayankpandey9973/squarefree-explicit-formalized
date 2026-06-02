import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Asymptotic `≲` calculus (absolute constants)

`a ≲ b` means `a ≤ C * b` for some absolute constant `C > 0`.  This hides all the
"constant × constant is a constant" bookkeeping so that section proofs never re-derive it.
Keystone of layer L0 — see `CLAUDE.md` §0/§7 and `formalization_plan.md` §2.
-/

namespace Squarefree.Asymp

/-- `a ≲ b`: there is an absolute constant `C > 0` with `a ≤ C * b`. -/
def Lesssim (a b : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ a ≤ C * b

@[inherit_doc] scoped infix:50 " ≲ " => Lesssim

theorem lesssim_refl (a : ℝ) : a ≲ a :=
  ⟨1, one_pos, le_of_eq (one_mul a).symm⟩

theorem lesssim_trans {a b c : ℝ} (hab : a ≲ b) (hbc : b ≲ c) : a ≲ c := by
  obtain ⟨C₁, hC₁, h₁⟩ := hab
  obtain ⟨C₂, hC₂, h₂⟩ := hbc
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  calc a ≤ C₁ * b := h₁
    _ ≤ C₁ * (C₂ * c) := mul_le_mul_of_nonneg_left h₂ hC₁.le
    _ = C₁ * C₂ * c := by ring

end Squarefree.Asymp
