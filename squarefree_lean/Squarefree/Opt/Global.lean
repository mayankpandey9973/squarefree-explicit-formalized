import Squarefree.Opt.Strip

/-!
# §9 on-strip case + the merged per-Ω block bound

`dblock_on_strip` is the §9 core (writeup 2083–2221): on the unresolved strip,
`𝐃(Ω) ≪ H/U` via Prop 7.3 with `W = W_{≠0}` (the largest admissible envelope, = the `e14`
monomial `H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}`) and the optimization `18977g+15315u<2` (the `e14`
constraint is the unique binding one: `840·(9.3) = 18977g+15315u−2`). It needs the full
`prop_3_2` (carrying `dStar`/`inDa`, gated by a `dtil = R_a⁻¹` right-inverse on the band).

`dblock_bound` is the merger: it picks shared `u, C, c₀, Cu`, splits on `S.x` against the strip
edges, and dispatches to `dblock_off_strip` (`Opt/Strip.lean`) / `dblock_on_strip`.
-/

open Classical Finset

namespace Squarefree

/-- **On-strip case** of `dblock_bound` (§9 core, writeup 2083–2221). Shared params `u, c₀, Cu`.
On the strip `G^{-2}Ω^{-11/2}X^{-Cu·u} ≤ x ≤ G^{17}Ω^{-26}X^{Cu·u}`, `𝐃(Ω) ≪ H/U` via Prop 7.3 with
`W = W_{≠0}` and `18977g+15315u<2`. (The prover may add a `Cu`-upper-bound / `u`-budget hypothesis;
the merger must respect it alongside `dblock_off_strip`'s `Cu ≥ (3/2)C6+232`.) -/
theorem dblock_on_strip (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18977)
    (u : ℝ) (hu0 : 0 < u) (hopt : 18977 * g + 15315 * u < 2) (hu2 : u ≤ 1 / 100)
    (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (Cu : ℝ) (hCu : 1 ≤ Cu) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)) ≤ S.x →
        S.x ≤ P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) →
        ∀ D : ℝ, 0 < D → D = S.D → DBlock P S D ≤ C * P.H / P.U := by
  sorry -- STUB: dblock_on_strip

/-- **§8/§9 per-Ω block bound** (merger). For `Ω` in the band `[c₀·G^{-1/4}U^{-3/4}, U]`,
`𝐃(Ω) ≪ H/U`. Picks shared `u, C, c₀, Cu`, splits `S.x` against the strip edges, and dispatches to
`dblock_off_strip` / `dblock_on_strip`. The regime hypotheses `64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A`, `2A ≤ D`
are supplied by `a_decomposition`'s sum range. -/
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

end Squarefree
