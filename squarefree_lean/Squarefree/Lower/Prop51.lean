import Squarefree.Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §5 lower-bound input: Prop 5.1 (layer L?)

Faithful `sorry`-stubbed statement of Prop 5.1 from `../explicit_writeup.md` (lines 731–741).
This elaborates but is not yet proved; the `sorry` is tagged `STUB: <name>`.
See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree

/-- **Prop 5.1** (writeup 731–741). `Ra` is the §3 set `ℛ_a` (cardinality `#ℛ_a`). -/
theorem prop_5_1 (P : Globals) (S : Scale P) (a : ℤ) (ha : 0 < a) (Ra : Finset ℕ)
    (hHΔ : ∃ c : ℝ, 0 < c ∧ c * (P.G * P.U ^ 10) ≤ P.H / S.Δ ^ 2)
    (hΔ : ∃ c : ℝ, 0 < c ∧ c * (P.G ^ 2 * P.U ^ 5) ≤ S.Δ)
    (hpop : ∃ c : ℝ, 0 < c ∧ c * (S.R / P.Wval) ≤ (Ra.card : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ (Ra.card : ℝ) ≤
      C * (P.H / S.Δ) *
        ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
        + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
        + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 ) := by
  sorry -- STUB: prop_5_1

end Squarefree
