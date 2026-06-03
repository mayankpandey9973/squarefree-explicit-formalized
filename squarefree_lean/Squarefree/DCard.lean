import Mathlib

/-!
# `dCard` — the dyadic counting function (low-level definition)

`dCard X H D = #{ d ∈ (D, 2D] ∩ ℤ : ∃ m, X ≤ m·d² ≤ X + H }`, the count `#𝒟[D,2D]`.

This definition is split out of `Main.lean` so that the structural layer (`§3 ADecomp`,
`§2 ShortDelta`, the `Opt` block bounds) can depend on it *without* depending on the
proof-spine module `Main`, which in turn imports those layers to assemble
`key_dyadic_estimate`.  See `CLAUDE.md` §0/§1 (break import cycles, keep `Main` lean).
-/

open Classical Finset

namespace Squarefree

/-- `dCard X H D = #{ d ∈ (D, 2D] ∩ ℤ : ∃ m : ℤ, X ≤ m·d² ≤ X + H }` — the count `#𝒟[D,2D]`. -/
noncomputable def dCard (X H D : ℝ) : ℕ :=
  ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
    (fun d => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)).card

end Squarefree
