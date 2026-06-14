import Squarefree.Structure.ADecompAux
import Squarefree.Counting.Preimage

/-!
# §5 𝒬 near-integer (writeup 777–781)

`distInt`-arithmetic (distance to the nearest integer is bounded by the distance to any
integer, subadditive on differences, scales under integer multiplication) plus the
near-integer property of a difference of two `Ffun`-values at `𝒟_a`-witnesses.

`distInt t = |t - round t|` is `Squarefree.Counting.distInt`.  All `round` facts come from
mathlib's `round_le (x : ℝ) (z : ℤ) : |x - round x| ≤ |x - z|`.
-/

namespace Squarefree

open Squarefree.Counting

/-- `distInt` is bounded by the distance to ANY integer. -/
theorem distInt_le_intDist (t : ℝ) (n : ℤ) : distInt t ≤ |t - (n : ℝ)| := by
  simpa only [distInt] using round_le t n

/-- `distInt` subadditive on differences. -/
theorem distInt_sub_le (x y : ℝ) : distInt (x - y) ≤ distInt x + distInt y := by
  refine le_trans (distInt_le_intDist (x - y) (round x - round y)) ?_
  have e : (x - y) - ((round x - round y : ℤ) : ℝ) = (x - round x) - (y - round y) := by
    push_cast; ring
  rw [e]
  refine le_trans (abs_sub _ _) ?_
  simp only [distInt, le_refl]

/-- `distInt (n·x) ≤ |n|·distInt x` for integer `n`. -/
theorem distInt_intMul_le (n : ℤ) (x : ℝ) :
    distInt ((n : ℝ) * x) ≤ |(n : ℝ)| * distInt x := by
  refine le_trans (distInt_le_intDist ((n : ℝ) * x) (n * round x)) ?_
  have e : (n : ℝ) * x - ((n * round x : ℤ) : ℝ) = (n : ℝ) * (x - round x) := by
    push_cast; ring
  rw [e, abs_mul]
  simp only [distInt, le_refl]

/-- **Near-integer of an `Ffun` difference**: if `d, d'` are both `𝒟_a`-witnesses then
`F_a(d) − F_a(d')` is within `2H/d² + 2H/d'²` of an integer. -/
theorem ffun_diff_near_int {X H : ℝ} {a d d' : ℤ}
    (hX : 0 < X) (hd : 0 < (d : ℝ)) (hd' : 0 < (d' : ℝ)) (ha : 0 < a)
    (hin : inDa X H a d) (hin' : inDa X H a d') :
    distInt (Ffun X (a : ℝ) (d : ℝ) - Ffun X (a : ℝ) (d' : ℝ))
      ≤ 2 * H / (d : ℝ) ^ 2 + 2 * H / (d' : ℝ) ^ 2 := by
  refine le_trans (distInt_sub_le _ _) ?_
  exact add_le_add (inDa_distInt_Ffun hX hd ha hin) (inDa_distInt_Ffun hX hd' ha hin')

/-- **Near-integer of the §5 defect `𝒬`** (writeup 777–781). Since `d₂ = d_a^*(r+ℓ₂)`,
`d₁ = d_a^*(r+ℓ₁)`, `d = d_a^*(r)` are all `𝒟_a`-witnesses, the combination
`𝒬 = ℓ₁(F_a(d)−F_a(d₂)) − ℓ₂(F_a(d)−F_a(d₁))` is near-integer. This is `v`-independent
(it only uses `inDa` of the three points), so it serves both the `v=0` and `v≠0` ranges. -/
theorem Q_distInt_le {X H : ℝ} {a d d₁ d₂ ℓ₁ ℓ₂ : ℤ}
    (hX : 0 < X) (ha : 0 < a)
    (hdpos : 0 < (d : ℝ)) (hd1pos : 0 < (d₁ : ℝ)) (hd2pos : 0 < (d₂ : ℝ))
    (hℓ1pos : 0 ≤ ℓ₁) (hℓ2pos : 0 ≤ ℓ₂)
    (hin : inDa X H a d) (hin1 : inDa X H a d₁) (hin2 : inDa X H a d₂) :
    distInt ((ℓ₁ : ℝ) * (Ffun X (a : ℝ) (d : ℝ) - Ffun X (a : ℝ) (d₂ : ℝ))
             - (ℓ₂ : ℝ) * (Ffun X (a : ℝ) (d : ℝ) - Ffun X (a : ℝ) (d₁ : ℝ)))
      ≤ (ℓ₁ : ℝ) * (2 * H / (d : ℝ) ^ 2 + 2 * H / (d₂ : ℝ) ^ 2)
        + (ℓ₂ : ℝ) * (2 * H / (d : ℝ) ^ 2 + 2 * H / (d₁ : ℝ) ^ 2) := by
  have hℓ1R : (0 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1pos
  have hℓ2R : (0 : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast hℓ2pos
  refine le_trans (distInt_sub_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (distInt_intMul_le ℓ₁ _) ?_
    rw [abs_of_nonneg hℓ1R]
    exact mul_le_mul_of_nonneg_left
      (ffun_diff_near_int hX hdpos hd2pos ha hin hin2) hℓ1R
  · refine le_trans (distInt_intMul_le ℓ₂ _) ?_
    rw [abs_of_nonneg hℓ2R]
    exact mul_le_mul_of_nonneg_left
      (ffun_diff_near_int hX hdpos hd1pos ha hin hin1) hℓ2R

end Squarefree
