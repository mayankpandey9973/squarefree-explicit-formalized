import Mathlib

/-!
# Top of the proof spine — main statements

Faithful `sorry`-stubbed statements of the paper's headline results, kept verbatim from
`../explicit_writeup.md` lines 4–26 (Theorem) and 2241–2255 (Thm 10.1). These elaborate but
are not yet proved; each `sorry` is tagged `STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree

/-- `dCard X H D = #{ d ∈ (D, 2D] ∩ ℤ : ∃ m : ℤ, X ≤ m·d² ≤ X + H }` — the count `#𝒟[D,2D]`. -/
noncomputable def dCard (X H D : ℝ) : ℕ :=
  ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
    (fun d => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)).card

/-- §1 key estimate: every dyadic scale `H/U ≪ D ≪ X^{1/2}` has `#𝒟[D,2D] ≪ H/U`. -/
theorem key_dyadic_estimate (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℝ, X ^ ((1 - g) / 5) / X ^ u ≤ D → D ≤ X ^ (1/2 : ℝ) →
        (dCard X (X ^ ((1 - g) / 5)) D : ℝ) ≤ C * X ^ ((1 - g) / 5) / X ^ u := by
  sorry -- STUB: key_dyadic_estimate

/-- Main analytic theorem (§Theorem): `∑_{X≤n≤X+H} μ²(n) = 6/π² · H + O(H/U)`. -/
theorem squarefree_count_short_interval (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      |(∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + X ^ ((1 - g) / 5)⌋,
            (if Squarefree n.toNat then (1 : ℝ) else 0))
          - 6 / Real.pi ^ 2 * X ^ ((1 - g) / 5)|
        ≤ C * X ^ ((1 - g) / 5) / X ^ u := by
  sorry -- STUB: squarefree_count_short_interval

/-- Theorem 10.1: a squarefree number in `[X, X + X^{1/5 − 2/94885 + ε}]` for large `X`. -/
theorem theorem_10_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, Squarefree n ∧ (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + X ^ (1/5 - 2/94885 + ε : ℝ) := by
  sorry -- STUB: theorem_10_1

end Squarefree
