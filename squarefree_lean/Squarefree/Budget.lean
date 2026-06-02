import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Squarefree.Params

/-!
# The `X^{O(u)}` budget lemma (layer L0 keystone)

TODO (M1): the single reusable lemma encoding the writeup's convention — a positive quantity
bounded by `C · X^{C·u + α(g)}` with `α(g) < 0` and `u ≤ c(g)` is `≤ X^{-c} ≤ U⁻¹` (hence
`≤ H/U` after the `H` factor).  Every "this term is `O(U⁻¹)`, drop it" step in §2/§5/§6/§8/§9
is one application of this.  The precise statement is designed against `Globals`/`Asymp` once
the project builds.
-/

namespace Squarefree.Budget

open Squarefree

/-- Core budget primitive: for `X ≥ 1`, any quantity equal to `X^e` with `e ≤ -u` is `≤ U⁻¹`. -/
theorem rpow_le_Uinv (P : Globals) (hX : 1 ≤ P.X) {e : ℝ} (he : e ≤ -P.u) :
    P.X ^ e ≤ (P.U)⁻¹ := by
  rw [Globals.U, ← Real.rpow_neg P.X_pos.le]
  exact Real.rpow_le_rpow_of_exponent_le hX he

/-- Exponent budget: if `α < 0`, `c ≥ 0`, `u ≤ -α/(c+1)`, then `α + c·u ≤ -u`. -/
theorem exponent_budget {α c u : ℝ} (hα : α < 0) (hc : 0 ≤ c) (hu : u ≤ -α / (c + 1)) :
    α + c * u ≤ -u := by
  have hc1 : 0 < c + 1 := by linarith
  rw [le_div_iff₀ hc1] at hu
  nlinarith [hu, hα]

end Squarefree.Budget
