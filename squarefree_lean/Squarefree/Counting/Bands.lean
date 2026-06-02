import Squarefree.Counting.Preimage
import Mathlib

/-!
# §4 derivative-band counting (Lemma 4.2)

Faithful `sorry`-stubbed statement of the derivative-band counting lemma from
`../explicit_writeup.md` (lines 426–436). This elaborates but is not yet proved; the `sorry`
is tagged `STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree.Counting

/-- **Lemma 4.2** (writeup 426–436): derivative-band counting. `O(1) zeros` of `φ'`, `φ''`
encoded as finiteness (to be tightened to a uniform bound when proved). -/
theorem bands_count (N T δ a b : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hI : Set.Icc a b ⊆ Set.Icc N (3 * N)) (hφ : ContDiff ℝ 2 φ)
    (hhi : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ T / N)
    (hlo : ∀ x ∈ Set.Icc a b, T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hz1 : (Set.Icc a b ∩ {x | deriv φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite) :
    ∃ C : ℝ, 0 < C ∧
      (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun n => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ C * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  sorry -- STUB: bands_count

end Squarefree.Counting
