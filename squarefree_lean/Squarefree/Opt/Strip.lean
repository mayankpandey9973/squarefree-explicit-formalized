import Squarefree.Opt.StripAux
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §8/§9 per-Ω-scale block bound `𝐃(Ω) ≪ H/U`

The core §5–§9 per-scale result, at the `DBlock` (= `𝐃(Ω) = Σ_{a∼A} #𝒟_a`) level.

The dichotomy is split by `Ω` against `c₀·G^{-1/4}U^{-3/4}` for a fixed absolute `c₀` chosen by
`dblock_bound` (the writeup's `Ω ≫ G^{-1/4}U^{-3/4}` threshold, line 406):
* `dblock_bound`     — `Ω ≥ c₀·G^{-1/4}U^{-3/4}` (the band): the lower edge makes Prop 3.2's
  fiber factor `1+Ω^{-8/3}G^{-2/3} ≤ X^{O(u)}`. Strip dichotomy internal (off-strip Props 5.1/6.1;
  on-strip Prop 7.3 + `18977g+15315u<2`).
* `dblock_small_omega` — `Ω ≤ c₀·G^{-1/4}U^{-3/4}` (below the band): the trivial Prop 3.2 bound
  (writeup lines 400–406), no §5/§6/§7. Works for any `c₀`, with `C` depending on `c₀`.

Both carry the Nair–Roth regime hypotheses that `a_decomposition`'s sum range supplies:
`64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A` (every gap in the block is super-threshold) and `2A ≤ D`.
These are exactly `prop_3_2_fiber`'s per-`a` hypotheses lifted to the block scale `A`.

`c₀` is in the existential prefix (chosen by the lemma), NOT a per-application `∃` — the latter
would make the band hypothesis vacuous. Replaces the old `prop_8_1` (`dCard` granularity, no band).
-/

open Classical Finset

namespace Squarefree

/-- **§8/§9 per-Ω block bound.** For `Ω` in the band `[c₀·G^{-1/4}U^{-3/4}, U]` (with `c₀` chosen
here), `𝐃(Ω) ≪ H/U`. Strip dichotomy internal (off-strip: Props 5.1/6.1; on-strip: Prop 7.3 +
`18977g+15315u<2`). The regime hypotheses `64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A`, `2A ≤ D` are supplied by
`a_decomposition`'s sum range. -/
theorem dblock_bound (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ 18977 * g + 15315 * u < 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  sorry -- STUB: dblock_bound

/-- Small-Ω block bound (below the band): the trivial Prop 3.2 bound (writeup 400–406), no §5/§6/§7.
Uniform (absolute) `C`, valid for any band constant `c₀` (with `C` depending on `c₀`). The regime
hypotheses match `dblock_bound`'s, so the two compose over `a_decomposition`'s sum. -/
theorem dblock_small_omega (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), 1 ≤ P.X →
      ∀ (S : Scale P), 1 ≤ S.Δ →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  sorry -- STUB: dblock_small_omega

end Squarefree
