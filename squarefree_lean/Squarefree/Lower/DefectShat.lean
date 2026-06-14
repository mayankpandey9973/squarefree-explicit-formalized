import Squarefree.Structure.ADecompAux
import Squarefree.Structure.DaSpacing
import Mathlib

/-!
# §5 large-defect range: the corrected second difference `Ŝ_{a,b}` (writeup 752–775)

The §5 Step-4 (large-defect) range is organized around the *corrected* mixed second
difference

  `Ŝ_{a,b}(d) := S_{a,b}(d) − (R_a(d) − R_a(d+b))`,

where (writeup 752)

  `S_{a,b}(d) = −(b−a)X/d² + (b+a)X/(d+a)² − (b+a)X/(d+b)² + (b−a)X/(d+a+b)²`,

and `R_a(d) = −(2d−a)X/d² + (2d+3a)X/(d+a)²` is Roth's quantity (here `Rfun`).

This file is the **first brick** of the `Ŝ`/`Υ` Taylor-expansion chain that Step 4 needs
(the analogue of `Ffun_factor` / `Fab` for the small-defect Step 3): it gives the closed-form
factorization of `S_{a,b}(d)` (writeup 299, sympy-verified) and pins the definitional unfolding
of `Ŝ_{a,b}`.

The downstream pieces — still to be built — are the order-5 Taylor expansion
`Ŝ_{a,b}(d) = (X/d⁵)(−4ab³ + (10ab⁴+10a²b³)/d + O(…))` (writeup 766), the `Υ→p₁,p₂` cubic/quartic
collection (writeup 1011–1030), and the per-`(s,v)` count.  See the scoping notes in
`formalization_plan.md` §5.
-/

namespace Squarefree

open Real

/-- The §5 mixed second difference `S_{a,b}(d)` (writeup 752):
`S_{a,b}(d) = −(b−a)X/d² + (b+a)X/(d+a)² − (b+a)X/(d+b)² + (b−a)X/(d+a+b)²`. -/
noncomputable def Sfun (X a b d : ℝ) : ℝ :=
  -(b - a) * X / d ^ 2 + (b + a) * X / (d + a) ^ 2
    - (b + a) * X / (d + b) ^ 2 + (b - a) * X / (d + a + b) ^ 2

/-- The §5 corrected mixed second difference `Ŝ_{a,b}(d)` (writeup 755):
`Ŝ_{a,b}(d) = S_{a,b}(d) − (R_a(d) − R_a(d+b))`. -/
noncomputable def Shat (X a b d : ℝ) : ℝ :=
  Sfun X a b d - (Rfun X a d - Rfun X a (d + b))

/-- **Exact factorization of `S_{a,b}(d)`** (writeup 299, sympy-verified). The 4-term combination
collapses to a single rational function with the degree-2 numerator
`a·b·(a−b)·(a+b)·(a+b+2d)·(ab+2ad+2bd+2d²)`. -/
theorem Sfun_factor {X a b d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) (hdb : d + b ≠ 0)
    (hdab : d + a + b ≠ 0) :
    Sfun X a b d =
      X * a * b * (a - b) * (a + b) * (a + b + 2 * d)
        * (a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2)
        / (d ^ 2 * (d + a) ^ 2 * (d + b) ^ 2 * (d + a + b) ^ 2) := by
  unfold Sfun
  field_simp
  ring

/-- Definitional unfolding of `Ŝ_{a,b}(d)` into the eight `X/(·)²` atoms (the `S_{a,b}` four
terms minus the two `R_a` corrections), each of the form `c·X/(d+x)²`.  This is the form on
which the order-5 Taylor remainder of `1/(d+x)²` is applied in the downstream expansion. -/
theorem Shat_unfold (X a b d : ℝ) :
    Shat X a b d =
      (-(b - a) * X / d ^ 2 + (b + a) * X / (d + a) ^ 2
        - (b + a) * X / (d + b) ^ 2 + (b - a) * X / (d + a + b) ^ 2)
      - ((-(2 * d - a) * X / d ^ 2 + (2 * d + 3 * a) * X / (d + a) ^ 2)
        - (-(2 * (d + b) - a) * X / (d + b) ^ 2
            + (2 * (d + b) + 3 * a) * X / ((d + b) + a) ^ 2)) := by
  unfold Shat Sfun Rfun
  rfl

/-- **Reflection identity** (sympy-verified): `Ŝ_{a,b}(d) = −Ŝ_{a,−b}(d+b)`.  Both `Sfun` and
the `Rfun`-correction are antisymmetric under `(b,d) ↦ (−b, d+b)` (the four spacing points
`{d, d+a, d+b, d+a+b}` are preserved as a set).  This lets the `b ≥ 0` near-integer brick be
re-used for the `b ≤ 0` shifts arising from the decreasing `d̃ₐ`-spacings. -/
theorem Shat_reflect (X a b d : ℝ) :
    Shat X a b d = - Shat X a (-b) (d + b) := by
  unfold Shat Sfun Rfun
  ring

end Squarefree
