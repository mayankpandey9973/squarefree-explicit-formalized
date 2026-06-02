import Squarefree.Params
import Squarefree.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §2 short-Δ regime: Prop 2.4 (layer L?)

Faithful `sorry`-stubbed statement of Prop 2.4 from `../explicit_writeup.md` (lines 209–241).
This elaborates but is not yet proved; the `sorry` is tagged `STUB: <name>`. See `CLAUDE.md`
§3/§4.
-/

open Classical Finset

namespace Squarefree

/-- **Prop 2.4** (writeup 209–241): `Δ = D/H ≤ X^{1/100}` ⇒ `#𝒟[D,2D] ≪ H/U`. -/
theorem prop_2_4 (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℝ, 0 < D → D ≤ X ^ ((1 - g) / 5) * X ^ (1 / 100 : ℝ) →
        (dCard X (X ^ ((1 - g) / 5)) D : ℝ) ≤ C * X ^ ((1 - g) / 5) / X ^ u := by
  sorry -- STUB: prop_2_4

end Squarefree
