import Mathlib

/-!
# §5 trivial interval-count helper

`card_le_of_real_ub`: any `Finset ℕ` whose elements are all `≤ B` (as reals) has
`#T ≤ B + 1`.  This is the trivial "the count is at most the interval length" bound,
used in the §5 count scale-reductions: when the smooth variation `L` is small, the loose
`preimage_count`/`bands_count` product RHS is replaced by this trivial bound (which is `≤`
the target term in that regime).
-/

namespace Squarefree

open Finset

/-- A `Finset ℕ` whose every element is `≤ B` (in `ℝ`) has card `≤ B + 1`. -/
theorem card_le_of_real_ub {T : Finset ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ r ∈ T, (r : ℝ) ≤ B) :
    (T.card : ℝ) ≤ B + 1 := by
  -- `T ⊆ Finset.Iic ⌊B⌋₊`, which has card `⌊B⌋₊ + 1`.
  have hsub : T ⊆ Finset.Iic ⌊B⌋₊ := by
    intro r hr
    rw [Finset.mem_Iic, Nat.le_floor_iff hB]
    exact hT r hr
  have hcard : T.card ≤ ⌊B⌋₊ + 1 := by
    calc T.card ≤ (Finset.Iic ⌊B⌋₊).card := Finset.card_le_card hsub
      _ = ⌊B⌋₊ + 1 := by rw [Nat.card_Iic]
  calc (T.card : ℝ) ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊B⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ B + 1 := by
        have : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
        linarith

end Squarefree
