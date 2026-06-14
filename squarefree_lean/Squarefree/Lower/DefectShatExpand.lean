import Squarefree.Lower.DefectShat
import Mathlib

/-!
# §5 order-5 Taylor expansion of the corrected second difference `Ŝ_{a,b}` (writeup 766)

The §5 Step-4 analogue of `Fab_expand`: the corrected mixed second difference satisfies

  `Ŝ_{a,b}(d) = (X/d⁵)(−4ab³) + (X/d⁶)(10ab⁴+10a²b³) + O(X(ab⁵+a²b⁴+a³b³)/d⁷)`,

valid in the window `4(a+|b|) ≤ d`.  Route B (exact rational): `Sfun_factor` + an exact
field identity express `Ŝ − leading` as `−X·a·b³·P(a,b,d) / [d⁶(d+a)²(d+b)²(d+a+b)²]`
(`Shat_error_eq`, sympy-verified — the `a³b` `1/d⁵`-lead cancels against `R_a`); the window
then bounds the homogeneous degree-7 numerator `P` and pins the denominator `≍ d¹²`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- The degree-7 (homogeneous in `a,b,d`) numerator polynomial `P` of the error
`Ŝ − leading`, after pulling out the common factor `−X·a·b³`. -/
private def Pshat (a b d : ℝ) : ℝ :=
  10*a^5*b^2 + 20*a^5*b*d + 10*a^5*d^2 + 30*a^4*b^3 + 96*a^4*b^2*d + 102*a^4*b*d^2
    + 36*a^4*d^3 + 30*a^3*b^4 + 152*a^3*b^3*d + 258*a^3*b^2*d^2 + 180*a^3*b*d^3
    + 45*a^3*d^4 + 10*a^2*b^5 + 96*a^2*b^4*d + 258*a^2*b^3*d^2 + 284*a^2*b^2*d^3
    + 130*a^2*b*d^4 + 20*a^2*d^5 + 20*a*b^5*d + 102*a*b^4*d^2 + 180*a*b^3*d^3
    + 129*a*b^2*d^4 + 30*a*b*d^5 + 10*b^5*d^2 + 36*b^4*d^3 + 44*b^3*d^4 + 18*b^2*d^5

/-- **Exact rational identity for the §5 order-5 error** (sympy-verified).
`Ŝ_{a,b}(d) − (leading)` equals `−X·a·b³·P(a,b,d) / [d⁶(d+a)²(d+b)²(d+a+b)²]`. -/
private theorem Shat_error_eq {X a b d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) (hdb : d + b ≠ 0)
    (hdab : d + a + b ≠ 0) :
    Shat X a b d - (X * (-4*a*b^3) / d^5 + X * (10*a*b^4 + 10*a^2*b^3) / d^6)
      = (-X * a * b^3 * Pshat a b d)
        / (d^6 * (d + a)^2 * (d + b)^2 * (d + a + b)^2) := by
  have hdba : (d + b) + a ≠ 0 := by rw [show (d + b) + a = d + a + b by ring]; exact hdab
  simp only [Shat, Sfun, Rfun, Pshat]
  field_simp
  ring

/-- Generic monomial bound: `a^p·B^q·d^r ≤ d^(p+q+r)` for `0 ≤ a,B ≤ d`. -/
private theorem monoLe {a B d : ℝ} (hca : 0 ≤ a) (hcd : 0 ≤ B) (had : a ≤ d) (hBd : B ≤ d)
    (p q r : ℕ) : a ^ p * B ^ q * d ^ r ≤ d ^ (p + q + r) := by
  have hd : 0 ≤ d := le_trans hca had
  calc a ^ p * B ^ q * d ^ r ≤ d ^ p * d ^ q * d ^ r := by gcongr
    _ = d ^ (p + q + r) := by rw [pow_add, pow_add]

/-- `|a^i·b^j·d^k| ≤ a^i·|b|^j·d^k` for `0 ≤ a, 0 ≤ d`. -/
private theorem absMono {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (b : ℝ) (i j k : ℕ) :
    |a ^ i * b ^ j * d ^ k| ≤ a ^ i * |b| ^ j * d ^ k := by
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_of_nonneg ha, abs_of_nonneg hd]

/-- Window magnitude bound on `P` (all variables nonneg, `a, B ≤ d`):
`P(a,B,d) ≤ 2336·(a²+aB+B²)·d⁵`. -/
private theorem Pshat_le {a B d : ℝ} (hca : 0 ≤ a) (hcd : 0 ≤ B) (had : a ≤ d) (hBd : B ≤ d) :
    Pshat a B d ≤ 2336 * (a ^ 2 + a * B + B ^ 2) * d ^ 5 := by
  have hd0 : 0 ≤ d := le_trans hca had
  set s : ℝ := a ^ 2 + a * B + B ^ 2 with hs
  have hs0 : 0 ≤ s := by simp only [hs]; positivity
  have h0 : a^5*B^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 3 2 0
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 3 * B ^ 2 * d ^ 0 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 3) (pow_nonneg hcd 2)) (pow_nonneg hd0 0)
    calc a^5*B^2 = a^2 * (a ^ 3 * B ^ 2 * d ^ 0) := by ring
      _ ≤ s * d ^ (3 + 2 + 0) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h1 : a^5*B*d ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 3 1 1
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 3 * B ^ 1 * d ^ 1 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 3) (pow_nonneg hcd 1)) (pow_nonneg hd0 1)
    calc a^5*B*d = a^2 * (a ^ 3 * B ^ 1 * d ^ 1) := by ring
      _ ≤ s * d ^ (3 + 1 + 1) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h2 : a^5*d^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 3 0 2
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 3 * B ^ 0 * d ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 3) (pow_nonneg hcd 0)) (pow_nonneg hd0 2)
    calc a^5*d^2 = a^2 * (a ^ 3 * B ^ 0 * d ^ 2) := by ring
      _ ≤ s * d ^ (3 + 0 + 2) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h3 : a^4*B^3 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 2 3 0
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 2 * B ^ 3 * d ^ 0 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 2) (pow_nonneg hcd 3)) (pow_nonneg hd0 0)
    calc a^4*B^3 = a^2 * (a ^ 2 * B ^ 3 * d ^ 0) := by ring
      _ ≤ s * d ^ (2 + 3 + 0) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h4 : a^4*B^2*d ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 2 2 1
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 2 * B ^ 2 * d ^ 1 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 2) (pow_nonneg hcd 2)) (pow_nonneg hd0 1)
    calc a^4*B^2*d = a^2 * (a ^ 2 * B ^ 2 * d ^ 1) := by ring
      _ ≤ s * d ^ (2 + 2 + 1) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h5 : a^4*B*d^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 2 1 2
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 2 * B ^ 1 * d ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 2) (pow_nonneg hcd 1)) (pow_nonneg hd0 2)
    calc a^4*B*d^2 = a^2 * (a ^ 2 * B ^ 1 * d ^ 2) := by ring
      _ ≤ s * d ^ (2 + 1 + 2) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h6 : a^4*d^3 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 2 0 3
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 2 * B ^ 0 * d ^ 3 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 2) (pow_nonneg hcd 0)) (pow_nonneg hd0 3)
    calc a^4*d^3 = a^2 * (a ^ 2 * B ^ 0 * d ^ 3) := by ring
      _ ≤ s * d ^ (2 + 0 + 3) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h7 : a^3*B^4 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 1 4 0
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 1 * B ^ 4 * d ^ 0 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 1) (pow_nonneg hcd 4)) (pow_nonneg hd0 0)
    calc a^3*B^4 = a^2 * (a ^ 1 * B ^ 4 * d ^ 0) := by ring
      _ ≤ s * d ^ (1 + 4 + 0) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h8 : a^3*B^3*d ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 1 3 1
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 1 * B ^ 3 * d ^ 1 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 1) (pow_nonneg hcd 3)) (pow_nonneg hd0 1)
    calc a^3*B^3*d = a^2 * (a ^ 1 * B ^ 3 * d ^ 1) := by ring
      _ ≤ s * d ^ (1 + 3 + 1) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h9 : a^3*B^2*d^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 1 2 2
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 1 * B ^ 2 * d ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 1) (pow_nonneg hcd 2)) (pow_nonneg hd0 2)
    calc a^3*B^2*d^2 = a^2 * (a ^ 1 * B ^ 2 * d ^ 2) := by ring
      _ ≤ s * d ^ (1 + 2 + 2) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h10 : a^3*B*d^3 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 1 1 3
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 1 * B ^ 1 * d ^ 3 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 1) (pow_nonneg hcd 1)) (pow_nonneg hd0 3)
    calc a^3*B*d^3 = a^2 * (a ^ 1 * B ^ 1 * d ^ 3) := by ring
      _ ≤ s * d ^ (1 + 1 + 3) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h11 : a^3*d^4 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 1 0 4
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 1 * B ^ 0 * d ^ 4 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 1) (pow_nonneg hcd 0)) (pow_nonneg hd0 4)
    calc a^3*d^4 = a^2 * (a ^ 1 * B ^ 0 * d ^ 4) := by ring
      _ ≤ s * d ^ (1 + 0 + 4) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h12 : a^2*B^5 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 5 0
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 5 * d ^ 0 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 5)) (pow_nonneg hd0 0)
    calc a^2*B^5 = a^2 * (a ^ 0 * B ^ 5 * d ^ 0) := by ring
      _ ≤ s * d ^ (0 + 5 + 0) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h13 : a^2*B^4*d ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 4 1
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 4 * d ^ 1 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 4)) (pow_nonneg hd0 1)
    calc a^2*B^4*d = a^2 * (a ^ 0 * B ^ 4 * d ^ 1) := by ring
      _ ≤ s * d ^ (0 + 4 + 1) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h14 : a^2*B^3*d^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 3 2
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 3 * d ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 3)) (pow_nonneg hd0 2)
    calc a^2*B^3*d^2 = a^2 * (a ^ 0 * B ^ 3 * d ^ 2) := by ring
      _ ≤ s * d ^ (0 + 3 + 2) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h15 : a^2*B^2*d^3 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 2 3
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 2 * d ^ 3 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 2)) (pow_nonneg hd0 3)
    calc a^2*B^2*d^3 = a^2 * (a ^ 0 * B ^ 2 * d ^ 3) := by ring
      _ ≤ s * d ^ (0 + 2 + 3) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h16 : a^2*B*d^4 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 1 4
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 1 * d ^ 4 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 1)) (pow_nonneg hd0 4)
    calc a^2*B*d^4 = a^2 * (a ^ 0 * B ^ 1 * d ^ 4) := by ring
      _ ≤ s * d ^ (0 + 1 + 4) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h17 : a^2*d^5 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 0 5
    have hc : a^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 0 * d ^ 5 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 0)) (pow_nonneg hd0 5)
    calc a^2*d^5 = a^2 * (a ^ 0 * B ^ 0 * d ^ 5) := by ring
      _ ≤ s * d ^ (0 + 0 + 5) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h18 : a*B^5*d ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 4 1
    have hc : a*B ≤ s := by nlinarith [sq_nonneg (a-B)]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 4 * d ^ 1 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 4)) (pow_nonneg hd0 1)
    calc a*B^5*d = a*B * (a ^ 0 * B ^ 4 * d ^ 1) := by ring
      _ ≤ s * d ^ (0 + 4 + 1) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h19 : a*B^4*d^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 3 2
    have hc : a*B ≤ s := by nlinarith [sq_nonneg (a-B)]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 3 * d ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 3)) (pow_nonneg hd0 2)
    calc a*B^4*d^2 = a*B * (a ^ 0 * B ^ 3 * d ^ 2) := by ring
      _ ≤ s * d ^ (0 + 3 + 2) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h20 : a*B^3*d^3 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 2 3
    have hc : a*B ≤ s := by nlinarith [sq_nonneg (a-B)]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 2 * d ^ 3 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 2)) (pow_nonneg hd0 3)
    calc a*B^3*d^3 = a*B * (a ^ 0 * B ^ 2 * d ^ 3) := by ring
      _ ≤ s * d ^ (0 + 2 + 3) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h21 : a*B^2*d^4 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 1 4
    have hc : a*B ≤ s := by nlinarith [sq_nonneg (a-B)]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 1 * d ^ 4 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 1)) (pow_nonneg hd0 4)
    calc a*B^2*d^4 = a*B * (a ^ 0 * B ^ 1 * d ^ 4) := by ring
      _ ≤ s * d ^ (0 + 1 + 4) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h22 : a*B*d^5 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 0 5
    have hc : a*B ≤ s := by nlinarith [sq_nonneg (a-B)]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 0 * d ^ 5 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 0)) (pow_nonneg hd0 5)
    calc a*B*d^5 = a*B * (a ^ 0 * B ^ 0 * d ^ 5) := by ring
      _ ≤ s * d ^ (0 + 0 + 5) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h23 : B^5*d^2 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 3 2
    have hc : B^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 3 * d ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 3)) (pow_nonneg hd0 2)
    calc B^5*d^2 = B^2 * (a ^ 0 * B ^ 3 * d ^ 2) := by ring
      _ ≤ s * d ^ (0 + 3 + 2) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h24 : B^4*d^3 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 2 3
    have hc : B^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 2 * d ^ 3 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 2)) (pow_nonneg hd0 3)
    calc B^4*d^3 = B^2 * (a ^ 0 * B ^ 2 * d ^ 3) := by ring
      _ ≤ s * d ^ (0 + 2 + 3) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h25 : B^3*d^4 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 1 4
    have hc : B^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 1 * d ^ 4 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 1)) (pow_nonneg hd0 4)
    calc B^3*d^4 = B^2 * (a ^ 0 * B ^ 1 * d ^ 4) := by ring
      _ ≤ s * d ^ (0 + 1 + 4) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have h26 : B^2*d^5 ≤ s * d ^ 5 := by
    have hl := monoLe hca hcd had hBd 0 0 5
    have hc : B^2 ≤ s := by nlinarith [mul_nonneg hca hcd]
    have hpL : (0:ℝ) ≤ a ^ 0 * B ^ 0 * d ^ 5 :=
      mul_nonneg (mul_nonneg (pow_nonneg hca 0) (pow_nonneg hcd 0)) (pow_nonneg hd0 5)
    calc B^2*d^5 = B^2 * (a ^ 0 * B ^ 0 * d ^ 5) := by ring
      _ ≤ s * d ^ (0 + 0 + 5) := mul_le_mul hc hl hpL hs0
      _ = s * d ^ 5 := by norm_num
  have hexp : Pshat a B d = 10 * (a^5*B^2) + 20 * (a^5*B*d) + 10 * (a^5*d^2) + 30 * (a^4*B^3) + 96 * (a^4*B^2*d) + 102 * (a^4*B*d^2) + 36 * (a^4*d^3) + 30 * (a^3*B^4) + 152 * (a^3*B^3*d) + 258 * (a^3*B^2*d^2) + 180 * (a^3*B*d^3) + 45 * (a^3*d^4) + 10 * (a^2*B^5) + 96 * (a^2*B^4*d) + 258 * (a^2*B^3*d^2) + 284 * (a^2*B^2*d^3) + 130 * (a^2*B*d^4) + 20 * (a^2*d^5) + 20 * (a*B^5*d) + 102 * (a*B^4*d^2) + 180 * (a*B^3*d^3) + 129 * (a*B^2*d^4) + 30 * (a*B*d^5) + 10 * (B^5*d^2) + 36 * (B^4*d^3) + 44 * (B^3*d^4) + 18 * (B^2*d^5) := by
    simp only [Pshat]; ring
  rw [hexp]; simp only [hs]; nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]

/-- Signed magnitude bound: `|P(a,b,d)| ≤ 2336·(a²+a|b|+|b|²)·d⁵`. -/
private theorem Pshat_abs_le {a b d : ℝ} (hca : 0 ≤ a) (hd0 : 0 ≤ d) (had : a ≤ d)
    (hbd : |b| ≤ d) : |Pshat a b d| ≤ 2336 * (a ^ 2 + a * |b| + |b| ^ 2) * d ^ 5 := by
  have htri : |Pshat a b d| ≤ Pshat a |b| d := by
    have g0 := absMono hca hd0 b 5 2 0
    have g1 := absMono hca hd0 b 5 1 1
    have g2 := absMono hca hd0 b 5 0 2
    have g3 := absMono hca hd0 b 4 3 0
    have g4 := absMono hca hd0 b 4 2 1
    have g5 := absMono hca hd0 b 4 1 2
    have g6 := absMono hca hd0 b 4 0 3
    have g7 := absMono hca hd0 b 3 4 0
    have g8 := absMono hca hd0 b 3 3 1
    have g9 := absMono hca hd0 b 3 2 2
    have g10 := absMono hca hd0 b 3 1 3
    have g11 := absMono hca hd0 b 3 0 4
    have g12 := absMono hca hd0 b 2 5 0
    have g13 := absMono hca hd0 b 2 4 1
    have g14 := absMono hca hd0 b 2 3 2
    have g15 := absMono hca hd0 b 2 2 3
    have g16 := absMono hca hd0 b 2 1 4
    have g17 := absMono hca hd0 b 2 0 5
    have g18 := absMono hca hd0 b 1 5 1
    have g19 := absMono hca hd0 b 1 4 2
    have g20 := absMono hca hd0 b 1 3 3
    have g21 := absMono hca hd0 b 1 2 4
    have g22 := absMono hca hd0 b 1 1 5
    have g23 := absMono hca hd0 b 0 5 2
    have g24 := absMono hca hd0 b 0 4 3
    have g25 := absMono hca hd0 b 0 3 4
    have g26 := absMono hca hd0 b 0 2 5
    rw [abs_le] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26
    simp only [Pshat]; rw [abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [(g0).1, (g0).2, (g1).1, (g1).2, (g2).1, (g2).2, (g3).1, (g3).2, (g4).1, (g4).2, (g5).1, (g5).2, (g6).1, (g6).2, (g7).1, (g7).2, (g8).1, (g8).2, (g9).1, (g9).2, (g10).1, (g10).2, (g11).1, (g11).2, (g12).1, (g12).2, (g13).1, (g13).2, (g14).1, (g14).2, (g15).1, (g15).2, (g16).1, (g16).2, (g17).1, (g17).2, (g18).1, (g18).2, (g19).1, (g19).2, (g20).1, (g20).2, (g21).1, (g21).2, (g22).1, (g22).2, (g23).1, (g23).2, (g24).1, (g24).2, (g25).1, (g25).2, (g26).1, (g26).2]
    · nlinarith [(g0).1, (g0).2, (g1).1, (g1).2, (g2).1, (g2).2, (g3).1, (g3).2, (g4).1, (g4).2, (g5).1, (g5).2, (g6).1, (g6).2, (g7).1, (g7).2, (g8).1, (g8).2, (g9).1, (g9).2, (g10).1, (g10).2, (g11).1, (g11).2, (g12).1, (g12).2, (g13).1, (g13).2, (g14).1, (g14).2, (g15).1, (g15).2, (g16).1, (g16).2, (g17).1, (g17).2, (g18).1, (g18).2, (g19).1, (g19).2, (g20).1, (g20).2, (g21).1, (g21).2, (g22).1, (g22).2, (g23).1, (g23).2, (g24).1, (g24).2, (g25).1, (g25).2, (g26).1, (g26).2]
  exact le_trans htri (Pshat_le hca (abs_nonneg b) had hbd)

/-- **§5 order-5 expansion of `Ŝ_{a,b}`** (writeup 766). The corrected mixed second difference
`Shat X a b d` agrees with its order-5 Taylor leading part
`(X/d⁵)(−4ab³) + (X/d⁶)(10ab⁴+10a²b³)` up to `O(X(a|b|⁵+a²|b|⁴+a³|b|³)/d⁷)`, valid for
`b ≠ 0` of either sign in the window `4(a+|b|) ≤ d`.  (Constant `10⁴`; the algebra yields
`2336·256/81 < 7383`.) -/
theorem Shat_expand {X a b d : ℝ} (hX : 0 < X) (ha : 0 < a) (hb : b ≠ 0) (hd : 0 < d)
    (hab : 4 * (a + |b|) ≤ d) :
    |Shat X a b d - (X * (-4*a*b^3) / d^5 + X * (10*a*b^4 + 10*a^2*b^3) / d^6)|
      ≤ 10^4 * X * (a*|b|^5 + a^2*|b|^4 + a^3*|b|^3) / d^7 := by
  -- window unpacking
  have hbnn : 0 ≤ |b| := abs_nonneg b
  have had4 : a ≤ d / 4 := by linarith [hbnn]
  have hbd4 : |b| ≤ d / 4 := by linarith [ha.le]
  have hbpair := abs_le.mp (by linarith [hbd4] : |b| ≤ d / 4)
  have hblo : -(d / 4) ≤ b := hbpair.1
  have hbhi : b ≤ d / 4 := hbpair.2
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hda : d + a ≠ 0 := by positivity
  have hdb : d + b ≠ 0 := ne_of_gt (by linarith [hblo])
  have hdab : d + a + b ≠ 0 := ne_of_gt (by linarith [hblo, ha])
  -- the exact rational identity
  rw [Shat_error_eq hd0 hda hdb hdab]
  -- numerator/denominator
  set DenE : ℝ := d^6 * (d + a)^2 * (d + b)^2 * (d + a + b)^2 with hDen
  have hDenpos : 0 < DenE := by
    have h2 : (0:ℝ) < (d + a)^2 := by positivity
    have h3 : (0:ℝ) < (d + b)^2 := pow_pos (by linarith [hblo]) 2
    have h4 : (0:ℝ) < (d + a + b)^2 := pow_pos (by linarith [hblo, ha]) 2
    have h1 : (0:ℝ) < d^6 := by positivity
    simp only [hDen]; positivity
  rw [abs_div, abs_of_pos hDenpos]
  -- bound numerator: |−X a b³ P| = X·a·|b|³·|P| ≤ X·a·|b|³·2336(a²+a|b|+|b|²)·d⁵
  have hPbound : |Pshat a b d| ≤ 2336 * (a ^ 2 + a * |b| + |b| ^ 2) * d ^ 5 :=
    Pshat_abs_le ha.le hd.le (by linarith) (by linarith [hbd4])
  have hnumabs : |(-X * a * b^3 * Pshat a b d)|
      = X * a * |b|^3 * |Pshat a b d| := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hX, abs_of_pos ha,
        abs_pow]
  rw [hnumabs]
  -- denominator lower bound: DenE ≥ (81/256) d^12
  have hDenlb : (81/256) * d^12 ≤ DenE := by
    have e1 : d^2 ≤ (d+a)^2 := by nlinarith [hd.le, ha.le]
    have e2 : (3*d/4)^2 ≤ (d+b)^2 := by nlinarith [hd.le, hblo]
    have e3 : (3*d/4)^2 ≤ (d+a+b)^2 := by nlinarith [hd.le, hblo, ha.le]
    have hd6 : (0:ℝ) ≤ d^6 := by positivity
    simp only [hDen]
    calc (81/256) * d^12 = d^6 * d^2 * (3*d/4)^2 * (3*d/4)^2 := by ring
      _ ≤ d^6 * (d+a)^2 * (d+b)^2 * (d+a+b)^2 := by gcongr
  -- combine: num/DenE ≤ num/((81/256)d^12) ≤ 10^4 X (...)/d^7
  have hnumnn : 0 ≤ X * a * |b|^3 * |Pshat a b d| := by positivity
  have hPshatnn : 0 ≤ |Pshat a b d| := abs_nonneg _
  have hd12 : (0:ℝ) < (81/256) * d^12 := by positivity
  have hnumle : X * a * |b|^3 * |Pshat a b d|
      ≤ X * a * |b|^3 * (2336 * (a^2 + a*|b| + |b|^2) * d^5) :=
    mul_le_mul_of_nonneg_left hPbound (by positivity)
  calc X * a * |b|^3 * |Pshat a b d| / DenE
      ≤ X * a * |b|^3 * (2336 * (a^2 + a*|b| + |b|^2) * d^5) / ((81/256) * d^12) := by
        gcongr
    _ ≤ 10^4 * X * (a*|b|^5 + a^2*|b|^4 + a^3*|b|^3) / d^7 := by
        rw [div_le_div_iff₀ hd12 (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg ha.le (pow_nonneg hbnn 3))
          (by positivity : (0:ℝ) ≤ a^2 + a*|b| + |b|^2), hX.le, hd.le,
          pow_nonneg hd.le 5, pow_nonneg hd.le 7, pow_nonneg hd.le 12,
          mul_nonneg ha.le (pow_nonneg hbnn 3), sq_nonneg d]

end Squarefree
