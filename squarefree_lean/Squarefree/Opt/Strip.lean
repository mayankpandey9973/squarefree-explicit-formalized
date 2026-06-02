import Squarefree.Params
import Squarefree.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §8 strip optimum: Prop 8.1 (layer L?)

Faithful `sorry`-stubbed statement of Prop 8.1 from `../explicit_writeup.md` (lines 2012–2018).
This elaborates but is not yet proved; the `sorry` is tagged `STUB: <name>`.
See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree

/-- **Prop 8.1** (writeup 2012–2018): if `x` is OUTSIDE the unresolved strip then
`#𝒟[D,2D] ≪ H/U`. Edges use one absolute budget constant `C`. -/
theorem prop_8_1 (P : Globals) (S : Scale P) (hg0 : 0 < P.g) (hg1 : P.g < 2 / 18977)
    (hΔ : P.X ^ (1/100 : ℝ) ≤ S.Δ) (D : ℝ) (hD : 0 < D) :
    ∃ (C cU : ℝ), 0 < C ∧ 0 < cU ∧ (P.u ≤ cU →
      ( S.x ≤ P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(C * P.u))
        ∨ P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (C * P.u) ≤ S.x ) →
      (dCard P.X P.H D : ℝ) ≤ C * P.H / P.U) := by
  sorry -- STUB: prop_8_1

end Squarefree
