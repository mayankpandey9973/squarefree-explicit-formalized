import Squarefree.Counting.Preimage
import Mathlib

/-!
# §4 integer points near a curve (Prop 4.3)

Faithful `sorry`-stubbed statement of the integer-points-near-a-curve proposition from
`../explicit_writeup.md` (lines 463–469). This elaborates but is not yet proved; the `sorry`
is tagged `STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree.Counting

/-- **Prop 4.3** (writeup 463–469): integer points near a curve, `|F''| ≍ 1` normalized to
`1 ≤ |F''| ≤ 2` on `[1/2, 5/2]`; count over `(N,2N]`. -/
theorem nearCurve_count : ∃ C : ℝ, 0 < C ∧
    ∀ (N T δ : ℝ) (F : ℝ → ℝ),
      1 < N → 1 < T → 0 < δ → δ < 1 → ContDiff ℝ 2 F →
      (∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), 1 ≤ |iteratedDeriv 2 F x|) →
      (∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), |iteratedDeriv 2 F x| ≤ 2) →
      (((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter
          (fun n => distInt (T * F ((n : ℝ) / N)) ≤ δ)).card : ℝ)
        ≤ C * ((N * T) ^ (1/3 : ℝ) + N * δ
               + N * Real.sqrt (δ / T) * Real.log (2 + N * Real.sqrt (δ / T)) + 1) := by
  sorry -- STUB: nearCurve_count

end Squarefree.Geometry
