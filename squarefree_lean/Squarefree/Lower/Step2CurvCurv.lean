import Squarefree.Lower.Step2Curvature3
import Squarefree.Lower.DefectDeriv4

/-!
# §5 Step-2 curvature lower bound (`f`-free Wronskian branch) — algebraic core

This file develops the `f`-independent curvature lower bound `phif_curvature_lower_curv`
(writeup line 917, second branch):

  `c · (T_curv / R) ≤ |φ_f'(r)| + R · |φ_f''(r)|`   for **all** `f`,

with `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D` and `c` an absolute positive constant.

The proof eliminates `f` via the Wronskian-type combination
`𝒲 := ψ''·φ_f' − ψ'·φ_f''` of `φ_f = ψ·(f + φ)`, `ψ = d̃⁴/(6Xa)`.  Writing `p = d̃'(r)`,
`q = d̃''(r)`, `s4 = d̃'''(r)`, one has the `f`-free identity
`𝒲 = (4 d̃⁶/(6Xa)²)·B_act`, `B_act := φ'·(5p²−d q) + d·p·φ''`.

This module supplies the two **algebraic bookends**:

* `smooth_wronskian_numerator_eq` / `_neg` — piece **(A)**: with `φ',φ''` replaced by their
  *smooth* versions (`b̃ → d̃'`), the numerator `p·(5p⁴−10p²q d+2p s4 d²)` has the closed form
  `−d⁵(a+d)³(5a⁴+44a³d+169a²d²+280a d³+180 d⁴)/(32 r⁵(a+2d)⁷)`, sign-definite (sympy-verified).
* `lp_duality_lower` — piece **(C, core)**: the elementary LP-duality inequality turning a lower
  bound on `|𝒲|` and `|ψ'| ≤ C R |ψ''|` into `|φ_f'| + R|φ_f''| ≥ |𝒲|/(C|ψ''|)`.
-/

namespace Squarefree

open Real

/-- **Piece (A), closed form.**  With the closed forms `p = d̃' = −d(d+a)/(2r(a+2d))`,
`q = d̃'' = d(d+a)(3a²+10a d+10 d²)/(4r²(a+2d)³)`,
`s4 = d̃''' = −3 d(d+a)(5a⁴+34a³d+94a²d²+120a d³+60 d⁴)/(8r³(a+2d)⁵)`, the *smooth* Wronskian
numerator `p·(5p⁴ − 10 p² q d + 2 p s4 d²)` has the closed product form. (sympy-verified.) -/
theorem smooth_wronskian_numerator_eq (a d r : ℝ) (hr : r ≠ 0) :
    (-d * (d + a) / (2 * r * (a + 2 * d)))
        * (5 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 4
           - 10 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
               * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
                  / (4 * r ^ 2 * (a + 2 * d) ^ 3)) * d
           + 2 * (-d * (d + a) / (2 * r * (a + 2 * d)))
               * (-3 * d * (d + a)
                  * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3
                     + 60 * d ^ 4) / (8 * r ^ 3 * (a + 2 * d) ^ 5)) * d ^ 2)
      = -d ^ 5 * (a + d) ^ 3
          * (5 * a ^ 4 + 44 * a ^ 3 * d + 169 * a ^ 2 * d ^ 2 + 280 * a * d ^ 3 + 180 * d ^ 4)
        / (32 * r ^ 5 * (a + 2 * d) ^ 7) := by
  field_simp
  ring

/-- **Piece (A), sign + magnitude.**  For `a, d, r > 0`, the smooth Wronskian numerator is
strictly negative, equal in magnitude to the explicit all-positive closed form.  This is the
`|B_s| > 0` fact (the leading factor `K/d⁶ > 0` is supplied by the caller). -/
theorem smooth_wronskian_numerator_neg {a d r : ℝ} (ha : 0 < a) (hd : 0 < d) (hr : 0 < r) :
    (-d * (d + a) / (2 * r * (a + 2 * d)))
        * (5 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 4
           - 10 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
               * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
                  / (4 * r ^ 2 * (a + 2 * d) ^ 3)) * d
           + 2 * (-d * (d + a) / (2 * r * (a + 2 * d)))
               * (-3 * d * (d + a)
                  * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3
                     + 60 * d ^ 4) / (8 * r ^ 3 * (a + 2 * d) ^ 5)) * d ^ 2)
      = -(d ^ 5 * (a + d) ^ 3
          * (5 * a ^ 4 + 44 * a ^ 3 * d + 169 * a ^ 2 * d ^ 2 + 280 * a * d ^ 3 + 180 * d ^ 4)
        / (32 * r ^ 5 * (a + 2 * d) ^ 7))
    ∧ 0 < d ^ 5 * (a + d) ^ 3
          * (5 * a ^ 4 + 44 * a ^ 3 * d + 169 * a ^ 2 * d ^ 2 + 280 * a * d ^ 3 + 180 * d ^ 4)
        / (32 * r ^ 5 * (a + 2 * d) ^ 7) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  refine ⟨?_, by positivity⟩
  rw [smooth_wronskian_numerator_eq a d r hr']
  ring

/-- **Piece (C), core: LP-duality.**  Let `𝒲 = ψ''·D1 − ψ'·D2` (with `D1 = φ_f'`, `D2 = φ_f''`
the actual derivatives).  Given `R ≥ 0`, `C ≥ 1`, and the derivative-ratio bound
`|ψ'| ≤ C·R·|ψ''|`, the LP-dual estimate `|𝒲| ≤ C·|ψ''|·(|D1| + R·|D2|)` holds.  Dividing by
`C·|ψ''|` yields `|φ_f'| + R·|φ_f''| ≥ |𝒲|/(C|ψ''|)`, the curvature lower bound's engine. -/
theorem lp_duality_lower {W ψ' ψ'' D1 D2 C R : ℝ}
    (hC : 1 ≤ C) (hWdef : W = ψ'' * D1 - ψ' * D2)
    (hψ' : |ψ'| ≤ C * R * |ψ''|) :
    |W| ≤ C * |ψ''| * (|D1| + R * |D2|) := by
  have habs : |W| ≤ |ψ''| * |D1| + |ψ'| * |D2| := by
    rw [hWdef]
    calc |ψ'' * D1 - ψ' * D2|
        ≤ |ψ'' * D1| + |ψ' * D2| := abs_sub _ _
      _ = |ψ''| * |D1| + |ψ'| * |D2| := by rw [abs_mul, abs_mul]
  have hψ''nn : 0 ≤ |ψ''| := abs_nonneg _
  have hD1nn : 0 ≤ |D1| := abs_nonneg _
  have hD2nn : 0 ≤ |D2| := abs_nonneg _
  -- `|ψ'|·|D2| ≤ C·R·|ψ''|·|D2|`
  have hterm2 : |ψ'| * |D2| ≤ C * R * |ψ''| * |D2| := by
    exact mul_le_mul_of_nonneg_right hψ' hD2nn
  -- `|ψ''|·|D1| ≤ C·|ψ''|·|D1|`  (since `C ≥ 1`)
  have hterm1 : |ψ''| * |D1| ≤ C * |ψ''| * |D1| := by
    have : |ψ''| * |D1| * 1 ≤ |ψ''| * |D1| * C :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    nlinarith [this]
  have hsum : |ψ''| * |D1| + |ψ'| * |D2| ≤ C * |ψ''| * (|D1| + R * |D2|) := by
    have hexp : C * |ψ''| * (|D1| + R * |D2|) = C * |ψ''| * |D1| + C * R * |ψ''| * |D2| := by
      ring
    rw [hexp]; linarith [hterm1, hterm2]
  exact le_trans habs hsum

end Squarefree
