import Squarefree.Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §6 regime upper bound: Prop 6.1 (layer L?)

Faithful `sorry`-stubbed statement of Prop 6.1 from `../explicit_writeup.md` (lines 1230–1236).
This elaborates but is not yet proved; the `sorry` is tagged `STUB: <name>`.
See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree

/-- **Prop 6.1** (writeup 1230–1236); `x = H/Δ²` is `S.x`; the single `C` is both the `≪`
constant and the absolute `X^{O(u)}` budget constant. -/
theorem prop_6_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P) (RaOf : ℤ → Finset ℕ),
      (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) ≤
        C * P.H * P.X ^ (C * P.u) *
          ( S.x * P.G * S.Ω ^ 2
          + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
          + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
  sorry -- STUB: prop_6_1

end Squarefree
