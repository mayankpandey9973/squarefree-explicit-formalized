import Squarefree.Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

/-!
# §2/§4 preimage counting (Lemma 4.1 / 2.3)

Faithful `sorry`-stubbed statement of the preimage-count lemma from `../explicit_writeup.md`
(lines 196–207, 413–421). This elaborates but is not yet proved; the `sorry` is tagged
`STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree.Counting

/-- Distance from a real to the nearest integer, `‖t‖`. -/
noncomputable def distInt (t : ℝ) : ℝ := |t - round t|

/-- **Lemma 4.1 / 2.3** (writeup 196–207, 413–421): an `F`-expanding map of total variation
`≤ V` is within `δ` of an integer at `≤ (V+2)(2δ/F+1)` integer points. -/
theorem preimage_count (a b V F δ : ℝ) (φ : ℝ → ℝ) (hF : 0 < F) (hδ : 0 ≤ δ)
    (hexp : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, F * |x - y| ≤ |φ x - φ y|)
    (hvar : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |φ x - φ y| ≤ V) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun n => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (V + 2) * (2 * δ / F + 1) := by
  sorry -- STUB: preimage_count

end Squarefree.Counting
