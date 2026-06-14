import Mathlib

/-!
# §5 Step-4 — perturbed-quadratic square-difference bound (pure ℝ algebra)

This file packages the algebraic bridge from a near-quadratic Sigma shell to a
square-difference diameter, used by the large-defect `v`-band count.

Two pure real-arithmetic lemmas:

* `abs_sq_sub_le_of_abs_mul_sq_sub_center_le` — the un-perturbed shell: if
  `|C·x² − s| ≤ E` and `|C·y² − s| ≤ E` with `0 < C`, then `|x² − y²| ≤ 2E/C`.

* `abs_sq_sub_le_of_perturbed_quadratic_shell` — the perturbed version, where the
  non-quadratic part of the phase splits into a same-sign Lipschitz part
  (`θ·C·|x²−y²|`) and an additive part `E0`.  With `θ ≤ 1/2` the Lipschitz part is
  absorbed, giving `|x² − y²| ≤ (4·eta + 2·E0)/C`.

For the §5 additive route the perturbation (cubic + p₂ + drift sizes) enters as the
additive `E0`; the Lipschitz slope `θ` may then be taken `0` (the hypothesis
`htheta : θ ≤ 1/2` is satisfied).  Both forms are kept here so the downstream agent
can pick the slope it needs.
-/

namespace Squarefree

/-- If two real numbers have their quadratic images under a positive scalar within
`E` of the same center, their squares differ by at most `2E/C`.

Pure algebra: `|x²−y²| = |Cx²−Cy²|/C ≤ (|Cx²−s|+|Cy²−s|)/C ≤ 2E/C`. -/
theorem abs_sq_sub_le_of_abs_mul_sq_sub_center_le
    {C E x y center : ℝ}
    (hC : 0 < C)
    (hx : |C * x ^ (2 : ℕ) - center| ≤ E)
    (hy : |C * y ^ (2 : ℕ) - center| ≤ E) :
    |x ^ (2 : ℕ) - y ^ (2 : ℕ)| ≤ 2 * E / C := by
  have htri :
      |C * x ^ (2 : ℕ) - C * y ^ (2 : ℕ)| ≤ 2 * E := by
    calc
      |C * x ^ (2 : ℕ) - C * y ^ (2 : ℕ)|
          = |(C * x ^ (2 : ℕ) - center) +
              (center - C * y ^ (2 : ℕ))| := by ring_nf
      _ ≤ |C * x ^ (2 : ℕ) - center| +
            |center - C * y ^ (2 : ℕ)| := abs_add_le _ _
      _ = |C * x ^ (2 : ℕ) - center| +
            |C * y ^ (2 : ℕ) - center| := by rw [abs_sub_comm center]
      _ ≤ E + E := add_le_add hx hy
      _ = 2 * E := by ring
  have hfact :
      C * x ^ (2 : ℕ) - C * y ^ (2 : ℕ) =
        C * (x ^ (2 : ℕ) - y ^ (2 : ℕ)) := by
    ring
  have hmul :
      C * |x ^ (2 : ℕ) - y ^ (2 : ℕ)| ≤ 2 * E := by
    have habs :
        |C * x ^ (2 : ℕ) - C * y ^ (2 : ℕ)| =
          C * |x ^ (2 : ℕ) - y ^ (2 : ℕ)| := by
      rw [hfact, abs_mul, abs_of_pos hC]
    simpa [habs] using htri
  rw [le_div_iff₀ hC]
  simpa [mul_comm] using hmul

/-- Square-difference control for a quadratic phase with a same-sign Lipschitz
perturbation.

`ex`, `ey` are the non-quadratic perturbations: the phase is `C·x² + ex` (resp.
`C·y² + ey`), each within `eta` of the common `center`.  The perturbation
difference splits into a same-sign Lipschitz part `θ·C·|x²−y²|` and an additive
part `E0`.  If `θ ≤ 1/2`, the Lipschitz part is absorbed and

  `|x² − y²| ≤ (4·eta + 2·E0)/C`. -/
theorem abs_sq_sub_le_of_perturbed_quadratic_shell
    {C theta eta E0 x y center ex ey : ℝ}
    (hC : 0 < C)
    (htheta : theta ≤ (1 / 2 : ℝ))
    (hx : |(C * x ^ (2 : ℕ) + ex) - center| ≤ eta)
    (hy : |(C * y ^ (2 : ℕ) + ey) - center| ≤ eta)
    (hpert :
      |ex - ey| ≤ theta * C * |x ^ (2 : ℕ) - y ^ (2 : ℕ)| + E0) :
    |x ^ (2 : ℕ) - y ^ (2 : ℕ)| ≤ (4 * eta + 2 * E0) / C := by
  let Dsq : ℝ := |x ^ (2 : ℕ) - y ^ (2 : ℕ)|
  have htri :
      |(C * x ^ (2 : ℕ) + ex) -
          (C * y ^ (2 : ℕ) + ey)| ≤ 2 * eta := by
    calc
      |(C * x ^ (2 : ℕ) + ex) -
          (C * y ^ (2 : ℕ) + ey)|
          =
        |((C * x ^ (2 : ℕ) + ex) - center) +
          (center - (C * y ^ (2 : ℕ) + ey))| := by ring_nf
      _ ≤ |(C * x ^ (2 : ℕ) + ex) - center| +
            |center - (C * y ^ (2 : ℕ) + ey)| := abs_add_le _ _
      _ = |(C * x ^ (2 : ℕ) + ex) - center| +
            |(C * y ^ (2 : ℕ) + ey) - center| := by
              rw [abs_sub_comm center]
      _ ≤ eta + eta := add_le_add hx hy
      _ = 2 * eta := by ring
  have hmain :
      C * Dsq ≤ 2 * eta + (theta * C * Dsq + E0) := by
    have hCdiff :
        |C * (x ^ (2 : ℕ) - y ^ (2 : ℕ))| =
          C * Dsq := by
      dsimp [Dsq]
      rw [abs_mul, abs_of_pos hC]
    calc
      C * Dsq
          = |C * (x ^ (2 : ℕ) - y ^ (2 : ℕ))| := hCdiff.symm
      _ =
          |((C * x ^ (2 : ℕ) + ex) -
              (C * y ^ (2 : ℕ) + ey)) - (ex - ey)| := by
            congr 1
            ring
      _ ≤
          |(C * x ^ (2 : ℕ) + ex) -
              (C * y ^ (2 : ℕ) + ey)| + |ex - ey| := by
            calc
              |((C * x ^ (2 : ℕ) + ex) -
                  (C * y ^ (2 : ℕ) + ey)) - (ex - ey)|
                  =
                |((C * x ^ (2 : ℕ) + ex) -
                    (C * y ^ (2 : ℕ) + ey)) + (-(ex - ey))| := by
                    rw [sub_eq_add_neg]
              _ ≤
                |(C * x ^ (2 : ℕ) + ex) -
                    (C * y ^ (2 : ℕ) + ey)| + |-(ex - ey)| :=
                  abs_add_le _ _
              _ =
                |(C * x ^ (2 : ℕ) + ex) -
                    (C * y ^ (2 : ℕ) + ey)| + |ex - ey| := by rw [abs_neg]
      _ ≤ 2 * eta + (theta * C * Dsq + E0) := add_le_add htri hpert
  have hCD :
      C * Dsq ≤ 4 * eta + 2 * E0 := by
    have hCD_nonneg : 0 ≤ C * Dsq := by
      exact mul_nonneg hC.le (abs_nonneg _)
    have htheta_mul :
        theta * (C * Dsq) ≤ (1 / 2 : ℝ) * (C * Dsq) :=
      mul_le_mul_of_nonneg_right htheta hCD_nonneg
    nlinarith [hmain, htheta_mul]
  rw [le_div_iff₀ hC]
  simpa [Dsq, mul_comm, mul_left_comm, mul_assoc] using hCD

end Squarefree
