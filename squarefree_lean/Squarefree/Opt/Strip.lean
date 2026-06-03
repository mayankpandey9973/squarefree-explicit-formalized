import Squarefree.Structure.DaSpacing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §8/§9 per-Ω-scale block bound `𝐃(Ω) ≪ H/U`

The core §5–§9 per-scale result, at the `DBlock` (= `𝐃(Ω) = Σ_{a∼A} #𝒟_a`) level. For a scale
`S` with `Ω` in the band `[c·G^{-1/4}U^{-3/4}, U]` (the lower edge makes Prop 3.2's fiber factor
`1+Ω^{-8/3}G^{-2/3} ≤ X^{O(u)}`), `𝐃(Ω) ≤ C·H/U`. Proof (strip dichotomy, internal): off the
unresolved strip use `prop_5_1`/`prop_6_1`; on the strip use `prop_7_3` (W = W_{≠0}) with the
`18977g+15315u<2` optimization. Below the band, `dblock_small_omega` is the trivial Prop 3.2 bound.

Replaces the old `prop_8_1` (wrong granularity — `dCard` — and missing the band lower-edge
hypothesis; subsumed by `dblock_bound` + `a_decomposition`).
-/

open Classical Finset

namespace Squarefree

/-- **§8/§9 per-Ω block bound.** For `Ω` in the band `[c·G^{-1/4}U^{-3/4}, U]`, `𝐃(Ω) ≪ H/U`.
Strip dichotomy is internal (off-strip: Props 5.1/6.1; on-strip: Prop 7.3 + `18977g+15315u<2`). -/
theorem dblock_bound (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ 18977 * g + 15315 * u < 2 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (∃ c : ℝ, 0 < c ∧ c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) →
        S.Ω ≤ P.U →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  sorry -- STUB: dblock_bound

/-- Small-Ω block bound (below the band): the trivial Prop 3.2 bound `#𝒟_a ≪ #ℛ_a`, no §5/§6/§7. -/
theorem dblock_small_omega (P : Globals) (S : Scale P)
    (hX : 1 ≤ P.X) (hΔ : 1 ≤ S.Δ)
    (hΩsmall : ∃ c : ℝ, 0 < c ∧ S.Ω ≤ c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)))
    (D : ℝ) (hD : 0 < D) (hDeq : D = S.D) :
    ∃ C : ℝ, 0 < C ∧ DBlock P S D ≤ C * P.H / P.U := by
  sorry -- STUB: dblock_small_omega

end Squarefree
