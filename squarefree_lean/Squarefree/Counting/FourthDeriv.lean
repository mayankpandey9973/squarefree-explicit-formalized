import Squarefree.Counting.Preimage
import Mathlib

/-!
# §2 fourth-derivative counting (Lemma 2.1)

Faithful `sorry`-stubbed statement of the 4th-derivative counting lemma from
`../explicit_writeup.md` (lines 84–94). This elaborates but is not yet proved; the `sorry`
is tagged `STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree.Counting

/-- **Lemma 2.1** (writeup 84–94): 4th-derivative counting via 3-fold differencing.
`|f⁽⁴⁾| ≍ Λ` is normalized to `Λ ≤ |f⁽⁴⁾| ≤ 2Λ` on `[N,3N]`; count over `(N,2N]`. -/
theorem fourthDeriv_count (N Λ δ : ℝ) (f : ℝ → ℝ)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1/4) (hΛ : 0 < Λ) (hf : ContDiff ℝ 4 f)
    (hlo : ∀ x ∈ Set.Icc N (3 * N), Λ ≤ |iteratedDeriv 4 f x|)
    (hhi : ∀ x ∈ Set.Icc N (3 * N), |iteratedDeriv 4 f x| ≤ 2 * Λ) :
    ∃ C : ℝ, 0 < C ∧
      (((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
               + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
  sorry -- STUB: fourthDeriv_count

end Squarefree.Counting
