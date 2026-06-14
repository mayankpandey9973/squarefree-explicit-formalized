import Squarefree.Lower.Step2CurvCurv2

/-!
# §5 Step-2 `χ''` positivity — algebraic helpers

Pure-algebra lemmas supporting `chi_iteratedDeriv2_pos` (`Step2ChiPos`):

* `chi2_poly` — the product-rule cleared form of `χ''` (`(K/(6Xa))·N_act/d⁶`).
* `smooth_chi2_eq` — the sign-definite closed form of the smooth numerator `N_s` (sympy-verified).
* `Ncorr_chi_alg` — the finite-difference correction expansion `N_act − N_s`.
* `chi_correction_abstract` — the §5-band correction bound `|N_act − N_s| ≤ B⁷R³/(2·10²⁷)`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

/-- **Product-rule cleared form of `χ''`** (sympy-verified).  Substituting the closed forms
`φ = K b²/d⁵`, `φ' = K b(2 b' d − 5 b d̃')/d⁶`, `φ'' = K(…)/d⁶` into the product rule
`χ'' = ψ''φ + 2ψ'φ' + ψφ''` collapses to `(K/(6Xa))·N_act/d⁶` with the four-monomial numerator
`N_act = (2d³d1² − d⁴d2)b² − 4d⁴d1·b·bp + 2d⁵·bp² + 2d⁵·b·bd`. -/
lemma chi2_poly (X a d d1 d2 b bp bd K : ℝ) (hd : d ≠ 0) :
    (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a) * (0 + K * b ^ 2 / d ^ 5)
      + (8 * d ^ 3 * d1) / (6 * X * a) * (K * b * (2 * bp * d - 5 * b * d1) / d ^ 6)
      + d ^ 4 / (6 * X * a)
          * (K * (bp * (2 * bp * d - 5 * b * d1)
              + b * (2 * bd * d - 3 * bp * d1 - 5 * b * d2)
              - 6 * b * (2 * bp * d - 5 * b * d1) * d1 / d) / d ^ 6)
      = K / (6 * X * a)
          * ((2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * b ^ 2 - 4 * d ^ 4 * d1 * b * bp
              + 2 * d ^ 5 * bp ^ 2 + 2 * d ^ 5 * b * bd) / d ^ 6 := by
  field_simp
  ring

/-- **Smooth numerator closed form** (sympy-verified, all-positive).  With `d1 = d̃'`, `d2 = d̃''`,
`s4 = d̃'''` at their closed forms, the smooth numerator
`N_s = 2d³d1⁴ − 5d⁴d1²d2 + 2d⁵d2² + 2d⁵d1 s4` factors as
`d⁷(a+d)²(35a⁴+241a³d+680a²d²+894ad³+468d⁴)/(16r⁴(a+2d)⁶)`. -/
lemma smooth_chi2_eq (a d r : ℝ) (hr : r ≠ 0) (had2 : a + 2 * d ≠ 0) :
    2 * d ^ 3 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 4
        - 5 * d ^ 4 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
            * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3))
        + 2 * d ^ 5
            * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
                / (4 * r ^ 2 * (a + 2 * d) ^ 3)) ^ 2
        + 2 * d ^ 5 * (-d * (d + a) / (2 * r * (a + 2 * d)))
            * (-3 * d * (d + a)
                * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
                / (8 * r ^ 3 * (a + 2 * d) ^ 5))
      = d ^ 7 * (a + d) ^ 2
          * (35 * a ^ 4 + 241 * a ^ 3 * d + 680 * a ^ 2 * d ^ 2 + 894 * a * d ^ 3 + 468 * d ^ 4)
        / (16 * r ^ 4 * (a + 2 * d) ^ 6) := by
  field_simp
  ring

/-- **Finite-difference correction expansion** (sympy-verified).  Substituting `b = d1+ε₁`,
`bp = d2+ε₂`, `bd = s4+ε₃` into `N_act` and subtracting the smooth `N_s` gives a 7-group
polynomial, each group carrying an `ε`. -/
lemma Ncorr_chi_alg (d d1 d2 s4 e1 e2 e3 : ℝ) :
    ((2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * (d1 + e1) ^ 2
        - 4 * d ^ 4 * d1 * (d1 + e1) * (d2 + e2) + 2 * d ^ 5 * (d2 + e2) ^ 2
        + 2 * d ^ 5 * (d1 + e1) * (s4 + e3))
      - (2 * d ^ 3 * d1 ^ 4 - 5 * d ^ 4 * d1 ^ 2 * d2 + 2 * d ^ 5 * d2 ^ 2 + 2 * d ^ 5 * d1 * s4)
      = (4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4) * e1
        + (-4 * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2) * e2
        + 2 * d ^ 5 * d1 * e3
        + (2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * e1 ^ 2
        + 2 * d ^ 5 * e2 ^ 2
        - 4 * d ^ 4 * d1 * e1 * e2
        + 2 * d ^ 5 * e1 * e3 := by
  ring

/-- **The finite-difference correction bound** (abstract).  Given the §5 scale bounds on the atoms
`d, d1, d2, s4` and the finite-difference errors `e1, e2, e3` (each `≤ ℓ₁·sup`), the correction
polynomial `N_act − N_s` is `≤ B⁷R³/(2·10²⁷)`.  Each monomial carries a factor `ℓ₁/R`, and
`hsmall : 10⁷⁸·ℓ₁ ≤ R` makes the total negligible against the smooth scale `B⁷R³/10²⁷`. -/
lemma chi_correction_abstract {d d1 d2 s4 e1 e2 e3 B R l1 : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hl1 : 0 < l1)
    (hd_hi : |d| ≤ 18 * (B * R))
    (hd1 : |d1| ≤ 10 ^ 6 * B)
    (hd2 : |d2| ≤ 10 ^ 13 * (B / R))
    (hs4 : |s4| ≤ 10 ^ 19 * (B / R ^ 2))
    (he1 : |e1| ≤ l1 * (10 ^ 13 * (B / R)))
    (he2 : |e2| ≤ l1 * (10 ^ 19 * (B / R ^ 2)))
    (he3 : |e3| ≤ l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
    (hsmall : 10 ^ 78 * l1 ≤ R) :
    |(4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4) * e1
        + (-4 * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2) * e2
        + 2 * d ^ 5 * d1 * e3
        + (2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * e1 ^ 2
        + 2 * d ^ 5 * e2 ^ 2
        - 4 * d ^ 4 * d1 * e1 * e2
        + 2 * d ^ 5 * e1 * e3|
      ≤ B ^ 7 * R ^ 3 / (2 * 10 ^ 27) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hl1R : l1 ≤ R := by nlinarith [hsmall, hl1]
  -- folding `ℓ₁²B⁷R ≤ ℓ₁B⁷R²`
  have hsq : l1 ^ 2 * B ^ 7 * R ≤ l1 * B ^ 7 * R ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hl1.le (pow_pos hB 7).le) hR.le)
      (sub_nonneg.mpr hl1R)]
  -- coefficient bounds
  have hcA : |4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4| ≤ 10 ^ 26 * (B ^ 6 * R ^ 3) := by
    have h1 : |4 * d ^ 3 * d1 ^ 3| ≤ 4 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 3 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(4:ℝ)| = 4 from by norm_num]; gcongr
    have h2 : |6 * d ^ 4 * d1 * d2| ≤ 6 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, show |(6:ℝ)| = 6 from by norm_num]; gcongr
    have h3 : |2 * d ^ 5 * s4| ≤ 2 * (18 * (B * R)) ^ 5 * (10 ^ 19 * (B / R ^ 2)) := by
      rw [abs_mul, abs_mul, abs_pow, show |(2:ℝ)| = 2 from by norm_num]; gcongr
    have e1' : 4 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 3 = 23328 * 10 ^ 18 * (B ^ 6 * R ^ 3) := by
      ring
    have e2' : 6 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 13 * (B / R))
        = 629856 * 10 ^ 19 * (B ^ 6 * R ^ 3) := by field_simp; ring
    have e3' : 2 * (18 * (B * R)) ^ 5 * (10 ^ 19 * (B / R ^ 2))
        = 3779136 * 10 ^ 19 * (B ^ 6 * R ^ 3) := by field_simp; ring
    calc |4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4|
        ≤ |4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2| + |2 * d ^ 5 * s4| := abs_add_le _ _
      _ ≤ (|4 * d ^ 3 * d1 ^ 3| + |6 * d ^ 4 * d1 * d2|) + |2 * d ^ 5 * s4| := by
          gcongr; exact abs_sub _ _
      _ ≤ 23328 * 10 ^ 18 * (B ^ 6 * R ^ 3) + 629856 * 10 ^ 19 * (B ^ 6 * R ^ 3)
            + 3779136 * 10 ^ 19 * (B ^ 6 * R ^ 3) := by rw [← e1', ← e2', ← e3']; linarith
      _ ≤ 10 ^ 26 * (B ^ 6 * R ^ 3) := by nlinarith [mul_pos (pow_pos hB 6) (pow_pos hR 3)]
  have hcB : |(-4) * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2| ≤ 10 ^ 20 * (B ^ 6 * R ^ 4) := by
    have h1 : |(-4) * d ^ 4 * d1 ^ 2| ≤ 4 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(-4:ℝ)| = 4 from by norm_num]; gcongr
    have h2 : |4 * d ^ 5 * d2| ≤ 4 * (18 * (B * R)) ^ 5 * (10 ^ 13 * (B / R)) := by
      rw [abs_mul, abs_mul, abs_pow, show |(4:ℝ)| = 4 from by norm_num]; gcongr
    have e1' : 4 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) ^ 2 = 419904 * 10 ^ 12 * (B ^ 6 * R ^ 4) := by
      ring
    have e2' : 4 * (18 * (B * R)) ^ 5 * (10 ^ 13 * (B / R)) = 7558272 * 10 ^ 13 * (B ^ 6 * R ^ 4) := by
      field_simp; ring
    calc |(-4) * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2|
        ≤ |(-4) * d ^ 4 * d1 ^ 2| + |4 * d ^ 5 * d2| := abs_add_le _ _
      _ ≤ 419904 * 10 ^ 12 * (B ^ 6 * R ^ 4) + 7558272 * 10 ^ 13 * (B ^ 6 * R ^ 4) := by
          rw [← e1', ← e2']; linarith
      _ ≤ 10 ^ 20 * (B ^ 6 * R ^ 4) := by nlinarith [mul_pos (pow_pos hB 6) (pow_pos hR 4)]
  have hcD : |2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2| ≤ 2 * 10 ^ 18 * (B ^ 5 * R ^ 3) := by
    have h1 : |2 * d ^ 3 * d1 ^ 2| ≤ 2 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(2:ℝ)| = 2 from by norm_num]; gcongr
    have h2 : |d ^ 4 * d2| ≤ (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) := by
      rw [abs_mul, abs_pow]; gcongr
    have e1' : 2 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 = 11664 * 10 ^ 12 * (B ^ 5 * R ^ 3) := by
      ring
    have e2' : (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) = 104976 * 10 ^ 13 * (B ^ 5 * R ^ 3) := by
      field_simp; ring
    calc |2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2|
        ≤ |2 * d ^ 3 * d1 ^ 2| + |d ^ 4 * d2| := abs_sub _ _
      _ ≤ 11664 * 10 ^ 12 * (B ^ 5 * R ^ 3) + 104976 * 10 ^ 13 * (B ^ 5 * R ^ 3) := by
          rw [← e1', ← e2']; linarith
      _ ≤ 2 * 10 ^ 18 * (B ^ 5 * R ^ 3) := by nlinarith [mul_pos (pow_pos hB 5) (pow_pos hR 3)]
  -- name the 7 signed groups
  set T1 := (4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4) * e1 with hT1
  set T2 := (-4 * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2) * e2 with hT2
  set T3 := 2 * d ^ 5 * d1 * e3 with hT3
  set T4 := (2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * e1 ^ 2 with hT4
  set T5 := 2 * d ^ 5 * e2 ^ 2 with hT5
  set T6 := 4 * d ^ 4 * d1 * e1 * e2 with hT6
  set T7 := 2 * d ^ 5 * e1 * e3 with hT7
  -- per-group magnitude bounds (each `≤ Kᵢ·ℓ₁B⁷R²`)
  have hT1bd : |T1| ≤ 10 ^ 39 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT1, abs_mul]
    calc |4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4| * |e1|
        ≤ 10 ^ 26 * (B ^ 6 * R ^ 3) * (l1 * (10 ^ 13 * (B / R))) :=
          mul_le_mul hcA he1 (abs_nonneg _) (by positivity)
      _ = 10 ^ 39 * (l1 * B ^ 7 * R ^ 2) := by field_simp
  have hT2bd : |T2| ≤ 10 ^ 39 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT2, abs_mul]
    have hcB' : |(-4 : ℝ) * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2| ≤ 10 ^ 20 * (B ^ 6 * R ^ 4) := hcB
    calc |(-4) * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2| * |e2|
        ≤ 10 ^ 20 * (B ^ 6 * R ^ 4) * (l1 * (10 ^ 19 * (B / R ^ 2))) :=
          mul_le_mul hcB' he2 (abs_nonneg _) (by positivity)
      _ = 10 ^ 39 * (l1 * B ^ 7 * R ^ 2) := by field_simp
  have hT3bd : |T3| ≤ 10 ^ 38 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT3]
    calc |2 * d ^ 5 * d1 * e3|
        ≤ 2 * (18 * (B * R)) ^ 5 * (10 ^ 6 * B) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, show |(2:ℝ)| = 2 from by norm_num]; gcongr
      _ = 75582720 * 10 ^ 30 * (l1 * B ^ 7 * R ^ 2) := by field_simp; ring
      _ ≤ 10 ^ 38 * (l1 * B ^ 7 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  have hT4bd : |T4| ≤ 2 * 10 ^ 44 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT4, abs_mul, abs_pow]
    calc |2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2| * |e1| ^ 2
        ≤ 2 * 10 ^ 18 * (B ^ 5 * R ^ 3) * (l1 * (10 ^ 13 * (B / R))) ^ 2 := by
          gcongr
      _ = 2 * 10 ^ 44 * (l1 ^ 2 * B ^ 7 * R) := by field_simp
      _ ≤ 2 * 10 ^ 44 * (l1 * B ^ 7 * R ^ 2) := mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hT5bd : |T5| ≤ 4 * 10 ^ 44 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT5]
    calc |2 * d ^ 5 * e2 ^ 2|
        ≤ 2 * (18 * (B * R)) ^ 5 * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2 := by
          rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(2:ℝ)| = 2 from by norm_num]; gcongr
      _ = 3779136 * 10 ^ 38 * (l1 ^ 2 * B ^ 7 * R) := by field_simp; ring
      _ ≤ 3779136 * 10 ^ 38 * (l1 * B ^ 7 * R ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 4 * 10 ^ 44 * (l1 * B ^ 7 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  have hT6bd : |T6| ≤ 5 * 10 ^ 43 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT6]
    calc |4 * d ^ 4 * d1 * e1 * e2|
        ≤ 4 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (l1 * (10 ^ 13 * (B / R)))
            * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, show |(4:ℝ)| = 4 from by norm_num]; gcongr
      _ = 419904 * 10 ^ 38 * (l1 ^ 2 * B ^ 7 * R) := by field_simp; ring
      _ ≤ 419904 * 10 ^ 38 * (l1 * B ^ 7 * R ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 5 * 10 ^ 43 * (l1 * B ^ 7 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  have hT7bd : |T7| ≤ 8 * 10 ^ 44 * (l1 * B ^ 7 * R ^ 2) := by
    rw [hT7]
    calc |2 * d ^ 5 * e1 * e3|
        ≤ 2 * (18 * (B * R)) ^ 5 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, show |(2:ℝ)| = 2 from by norm_num]; gcongr
      _ = 7558272 * 10 ^ 38 * (l1 ^ 2 * B ^ 7 * R) := by field_simp; ring
      _ ≤ 7558272 * 10 ^ 38 * (l1 * B ^ 7 * R ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 8 * 10 ^ 44 * (l1 * B ^ 7 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  -- triangle inequality on the 7 signed groups
  have htri : |T1 + T2 + T3 + T4 + T5 - T6 + T7|
      ≤ |T1| + |T2| + |T3| + |T4| + |T5| + |T6| + |T7| := by
    have s1 := abs_add_le (T1 + T2 + T3 + T4 + T5 - T6) T7
    have s2 := abs_sub (T1 + T2 + T3 + T4 + T5) T6
    have s3 := abs_add_le (T1 + T2 + T3 + T4) T5
    have s4' := abs_add_le (T1 + T2 + T3) T4
    have s5 := abs_add_le (T1 + T2) T3
    have s6 := abs_add_le T1 T2
    linarith [s1, s2, s3, s4', s5, s6]
  have hXnn : (0:ℝ) ≤ l1 * B ^ 7 * R ^ 2 := by positivity
  have hfin : (10 : ℝ) ^ 46 * (l1 * B ^ 7 * R ^ 2) ≤ B ^ 7 * R ^ 3 / (2 * 10 ^ 27) := by
    rw [le_div_iff₀ (by positivity)]
    have h2l1 : 2 * 10 ^ 73 * l1 ≤ R := by nlinarith [hsmall, hl1]
    nlinarith [mul_nonneg (mul_pos (pow_pos hB 7) (pow_pos hR 2)).le (sub_nonneg.mpr h2l1)]
  -- the goal's polynomial equals `T1+T2+T3+T4+T5-T6+T7`
  have heq : (4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4) * e1
        + (-4 * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2) * e2 + 2 * d ^ 5 * d1 * e3
        + (2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * e1 ^ 2 + 2 * d ^ 5 * e2 ^ 2
        - 4 * d ^ 4 * d1 * e1 * e2 + 2 * d ^ 5 * e1 * e3
      = T1 + T2 + T3 + T4 + T5 - T6 + T7 := by
    rw [hT1, hT2, hT3, hT4, hT5, hT6, hT7]
  rw [heq]
  calc |T1 + T2 + T3 + T4 + T5 - T6 + T7|
      ≤ |T1| + |T2| + |T3| + |T4| + |T5| + |T6| + |T7| := htri
    _ ≤ (10 ^ 39 + 10 ^ 39 + 10 ^ 38 + 2 * 10 ^ 44 + 4 * 10 ^ 44 + 5 * 10 ^ 43 + 8 * 10 ^ 44)
          * (l1 * B ^ 7 * R ^ 2) := by
        nlinarith [hT1bd, hT2bd, hT3bd, hT4bd, hT5bd, hT6bd, hT7bd, hXnn]
    _ ≤ (10 : ℝ) ^ 46 * (l1 * B ^ 7 * R ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hXnn; norm_num
    _ ≤ B ^ 7 * R ^ 3 / (2 * 10 ^ 27) := hfin

end Squarefree
