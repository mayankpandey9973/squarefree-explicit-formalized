import Squarefree.Lower.Step2D2ZeroAux

/-!
# §5 Step-2 φ″-zero count — the finite-difference correction bound for `W₂`

Order-2 analogue of `chi_correction_abstract` with the four errors `ε₁..ε₄`.  The 37-monomial
correction `W2num_act − W2num_s` (from `Ncorr_w2_alg`) is bounded by `B⁷/(2·10⁴²)` on the §5
band.  Because `W₂ ≍ B⁷` (no `R³` cushion), the smallness threshold is `10¹¹⁰·ℓ₁ ≤ R`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

/-- **Finite-difference correction bound for `W2num`** (order-2 analogue of
`chi_correction_abstract`).  Given the §5 atom/error magnitude bounds and `10¹¹⁰·ℓ₁ ≤ R`, the
37-group correction polynomial is `≤ B⁷/(2·10⁴²)` (half the smooth magnitude `B⁷/10⁴²`). -/
lemma w2_correction_abstract {d d1 d2 s4 d4 e1 e2 e3 e4 B R l1 : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hl1 : 0 < l1)
    (h_d : |d| ≤ 18 * (B * R))
    (h_d1 : |d1| ≤ 10 ^ 6 * B)
    (h_d2 : |d2| ≤ 10 ^ 13 * (B / R))
    (h_s4 : |s4| ≤ 10 ^ 19 * (B / R ^ 2))
    (h_d4 : |d4| ≤ 2 * 10 ^ 25 * (B / R ^ 3))
    (h_e1 : |e1| ≤ l1 * (10 ^ 13 * (B / R)))
    (h_e2 : |e2| ≤ l1 * (10 ^ 19 * (B / R ^ 2)))
    (h_e3 : |e3| ≤ l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
    (h_e4 : |e4| ≤ l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
    (hsmall : 10 ^ 110 * l1 ≤ R) :
    |8 * d ^ 4 * d1 * d2 * e4
        - 8 * d ^ 4 * d1 * s4 * e3
        + 24 * d ^ 4 * d2 ^ 2 * e3
        + 8 * d ^ 4 * d2 * d4 * e1
        + 8 * d ^ 4 * d2 * e1 * e4
        + 24 * d ^ 4 * d2 * e2 * e3
        + 8 * d ^ 4 * d2 * s4 * e2
        - 8 * d ^ 4 * s4 * e1 * e3
        - 8 * d ^ 4 * s4 ^ 2 * e1
        - 8 * d ^ 4 * s4 * e2 ^ 2
        + 24 * d ^ 3 * d1 ^ 3 * e4
        - 24 * d ^ 3 * d1 ^ 2 * d2 * e3
        + 24 * d ^ 3 * d1 ^ 2 * d4 * e1
        + 24 * d ^ 3 * d1 ^ 2 * e1 * e4
        + 72 * d ^ 3 * d1 ^ 2 * e2 * e3
        + 88 * d ^ 3 * d1 ^ 2 * s4 * e2
        - 216 * d ^ 3 * d1 * d2 ^ 2 * e2
        - 96 * d ^ 3 * d1 * d2 * e1 * e3
        - 80 * d ^ 3 * d1 * d2 * s4 * e1
        - 96 * d ^ 3 * d1 * d2 * e2 ^ 2
        + 16 * d ^ 3 * d1 * s4 * e1 * e2
        - 24 * d ^ 3 * d2 ^ 3 * e1
        - 24 * d ^ 3 * d2 ^ 2 * e1 * e2
        - 120 * d ^ 2 * d1 ^ 4 * e3
        - 120 * d ^ 2 * d1 ^ 3 * d2 * e2
        - 120 * d ^ 2 * d1 ^ 3 * e1 * e3
        - 160 * d ^ 2 * d1 ^ 3 * s4 * e1
        - 120 * d ^ 2 * d1 ^ 3 * e2 ^ 2
        + 240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1
        + 120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2
        - 20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2
        + 60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2
        + 240 * d * d1 ^ 5 * e2
        + 240 * d * d1 ^ 4 * d2 * e1
        + 240 * d * d1 ^ 4 * e1 * e2
        - 240 * d1 ^ 6 * e1
        - 120 * d1 ^ 5 * e1 ^ 2|
      ≤ B ^ 7 / (2 * 10 ^ 42) := by
  have hRne : R ≠ 0 := hR.ne'
  have hb0 : |8 * d ^ 4 * d1 * d2 * e4| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb1 : |8 * d ^ 4 * d1 * s4 * e3| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb2 : |24 * d ^ 4 * d2 ^ 2 * e3| ≤ 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb3 : |8 * d ^ 4 * d2 * d4 * e1| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb4 : |8 * d ^ 4 * d2 * e1 * e4| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb5 : |24 * d ^ 4 * d2 * e2 * e3| ≤ 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb6 : |8 * d ^ 4 * d2 * s4 * e2| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb7 : |8 * d ^ 4 * s4 * e1 * e3| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb8 : |8 * d ^ 4 * s4 ^ 2 * e1| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb9 : |8 * d ^ 4 * s4 * e2 ^ 2| ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2 := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb10 : |24 * d ^ 3 * d1 ^ 3 * e4| ≤ 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 3 * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb11 : |24 * d ^ 3 * d1 ^ 2 * d2 * e3| ≤ 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb12 : |24 * d ^ 3 * d1 ^ 2 * d4 * e1| ≤ 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb13 : |24 * d ^ 3 * d1 ^ 2 * e1 * e4| ≤ 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb14 : |72 * d ^ 3 * d1 ^ 2 * e2 * e3| ≤ 72 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb15 : |88 * d ^ 3 * d1 ^ 2 * s4 * e2| ≤ 88 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb16 : |216 * d ^ 3 * d1 * d2 ^ 2 * e2| ≤ 216 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb17 : |96 * d ^ 3 * d1 * d2 * e1 * e3| ≤ 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb18 : |80 * d ^ 3 * d1 * d2 * s4 * e1| ≤ 80 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb19 : |96 * d ^ 3 * d1 * d2 * e2 ^ 2| ≤ 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2 := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb20 : |16 * d ^ 3 * d1 * s4 * e1 * e2| ≤ 16 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb21 : |24 * d ^ 3 * d2 ^ 3 * e1| ≤ 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 3 * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb22 : |24 * d ^ 3 * d2 ^ 2 * e1 * e2| ≤ 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb23 : |120 * d ^ 2 * d1 ^ 4 * e3| ≤ 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 4 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb24 : |120 * d ^ 2 * d1 ^ 3 * d2 * e2| ≤ 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb25 : |120 * d ^ 2 * d1 ^ 3 * e1 * e3| ≤ 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb26 : |160 * d ^ 2 * d1 ^ 3 * s4 * e1| ≤ 160 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb27 : |120 * d ^ 2 * d1 ^ 3 * e2 ^ 2| ≤ 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2 := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb28 : |240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1| ≤ 240 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb29 : |120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2| ≤ 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb30 : |20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2| ≤ 20 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) ^ 2 := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb31 : |60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2| ≤ 60 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) ^ 2 := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb32 : |240 * d * d1 ^ 5 * e2| ≤ 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb33 : |240 * d * d1 ^ 4 * d2 * e1| ≤ 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb34 : |240 * d * d1 ^ 4 * e1 * e2| ≤ 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb35 : |240 * d1 ^ 6 * e1| ≤ 240 * (10 ^ 6 * B) ^ 6 * (l1 * (10 ^ 13 * (B / R))) := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have hb36 : |120 * d1 ^ 5 * e1 ^ 2| ≤ 120 * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 13 * (B / R))) ^ 2 := by
    simp only [abs_mul, abs_pow]; gcongr <;> first | norm_num | positivity
  have htri : |8 * d ^ 4 * d1 * d2 * e4
        - 8 * d ^ 4 * d1 * s4 * e3
        + 24 * d ^ 4 * d2 ^ 2 * e3
        + 8 * d ^ 4 * d2 * d4 * e1
        + 8 * d ^ 4 * d2 * e1 * e4
        + 24 * d ^ 4 * d2 * e2 * e3
        + 8 * d ^ 4 * d2 * s4 * e2
        - 8 * d ^ 4 * s4 * e1 * e3
        - 8 * d ^ 4 * s4 ^ 2 * e1
        - 8 * d ^ 4 * s4 * e2 ^ 2
        + 24 * d ^ 3 * d1 ^ 3 * e4
        - 24 * d ^ 3 * d1 ^ 2 * d2 * e3
        + 24 * d ^ 3 * d1 ^ 2 * d4 * e1
        + 24 * d ^ 3 * d1 ^ 2 * e1 * e4
        + 72 * d ^ 3 * d1 ^ 2 * e2 * e3
        + 88 * d ^ 3 * d1 ^ 2 * s4 * e2
        - 216 * d ^ 3 * d1 * d2 ^ 2 * e2
        - 96 * d ^ 3 * d1 * d2 * e1 * e3
        - 80 * d ^ 3 * d1 * d2 * s4 * e1
        - 96 * d ^ 3 * d1 * d2 * e2 ^ 2
        + 16 * d ^ 3 * d1 * s4 * e1 * e2
        - 24 * d ^ 3 * d2 ^ 3 * e1
        - 24 * d ^ 3 * d2 ^ 2 * e1 * e2
        - 120 * d ^ 2 * d1 ^ 4 * e3
        - 120 * d ^ 2 * d1 ^ 3 * d2 * e2
        - 120 * d ^ 2 * d1 ^ 3 * e1 * e3
        - 160 * d ^ 2 * d1 ^ 3 * s4 * e1
        - 120 * d ^ 2 * d1 ^ 3 * e2 ^ 2
        + 240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1
        + 120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2
        - 20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2
        + 60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2
        + 240 * d * d1 ^ 5 * e2
        + 240 * d * d1 ^ 4 * d2 * e1
        + 240 * d * d1 ^ 4 * e1 * e2
        - 240 * d1 ^ 6 * e1
        - 120 * d1 ^ 5 * e1 ^ 2|
      ≤ |8 * d ^ 4 * d1 * d2 * e4|
        + |8 * d ^ 4 * d1 * s4 * e3|
        + |24 * d ^ 4 * d2 ^ 2 * e3|
        + |8 * d ^ 4 * d2 * d4 * e1|
        + |8 * d ^ 4 * d2 * e1 * e4|
        + |24 * d ^ 4 * d2 * e2 * e3|
        + |8 * d ^ 4 * d2 * s4 * e2|
        + |8 * d ^ 4 * s4 * e1 * e3|
        + |8 * d ^ 4 * s4 ^ 2 * e1|
        + |8 * d ^ 4 * s4 * e2 ^ 2|
        + |24 * d ^ 3 * d1 ^ 3 * e4|
        + |24 * d ^ 3 * d1 ^ 2 * d2 * e3|
        + |24 * d ^ 3 * d1 ^ 2 * d4 * e1|
        + |24 * d ^ 3 * d1 ^ 2 * e1 * e4|
        + |72 * d ^ 3 * d1 ^ 2 * e2 * e3|
        + |88 * d ^ 3 * d1 ^ 2 * s4 * e2|
        + |216 * d ^ 3 * d1 * d2 ^ 2 * e2|
        + |96 * d ^ 3 * d1 * d2 * e1 * e3|
        + |80 * d ^ 3 * d1 * d2 * s4 * e1|
        + |96 * d ^ 3 * d1 * d2 * e2 ^ 2|
        + |16 * d ^ 3 * d1 * s4 * e1 * e2|
        + |24 * d ^ 3 * d2 ^ 3 * e1|
        + |24 * d ^ 3 * d2 ^ 2 * e1 * e2|
        + |120 * d ^ 2 * d1 ^ 4 * e3|
        + |120 * d ^ 2 * d1 ^ 3 * d2 * e2|
        + |120 * d ^ 2 * d1 ^ 3 * e1 * e3|
        + |160 * d ^ 2 * d1 ^ 3 * s4 * e1|
        + |120 * d ^ 2 * d1 ^ 3 * e2 ^ 2|
        + |240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1|
        + |120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2|
        + |20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2|
        + |60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2|
        + |240 * d * d1 ^ 5 * e2|
        + |240 * d * d1 ^ 4 * d2 * e1|
        + |240 * d * d1 ^ 4 * e1 * e2|
        + |240 * d1 ^ 6 * e1|
        + |120 * d1 ^ 5 * e1 ^ 2| := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [le_abs_self (8 * d ^ 4 * d1 * d2 * e4), le_abs_self (8 * d ^ 4 * d1 * s4 * e3), le_abs_self (24 * d ^ 4 * d2 ^ 2 * e3), le_abs_self (8 * d ^ 4 * d2 * d4 * e1), le_abs_self (8 * d ^ 4 * d2 * e1 * e4), le_abs_self (24 * d ^ 4 * d2 * e2 * e3), le_abs_self (8 * d ^ 4 * d2 * s4 * e2), le_abs_self (8 * d ^ 4 * s4 * e1 * e3), le_abs_self (8 * d ^ 4 * s4 ^ 2 * e1), le_abs_self (8 * d ^ 4 * s4 * e2 ^ 2), le_abs_self (24 * d ^ 3 * d1 ^ 3 * e4), le_abs_self (24 * d ^ 3 * d1 ^ 2 * d2 * e3), le_abs_self (24 * d ^ 3 * d1 ^ 2 * d4 * e1), le_abs_self (24 * d ^ 3 * d1 ^ 2 * e1 * e4), le_abs_self (72 * d ^ 3 * d1 ^ 2 * e2 * e3), le_abs_self (88 * d ^ 3 * d1 ^ 2 * s4 * e2), le_abs_self (216 * d ^ 3 * d1 * d2 ^ 2 * e2), le_abs_self (96 * d ^ 3 * d1 * d2 * e1 * e3), le_abs_self (80 * d ^ 3 * d1 * d2 * s4 * e1), le_abs_self (96 * d ^ 3 * d1 * d2 * e2 ^ 2), le_abs_self (16 * d ^ 3 * d1 * s4 * e1 * e2), le_abs_self (24 * d ^ 3 * d2 ^ 3 * e1), le_abs_self (24 * d ^ 3 * d2 ^ 2 * e1 * e2), le_abs_self (120 * d ^ 2 * d1 ^ 4 * e3), le_abs_self (120 * d ^ 2 * d1 ^ 3 * d2 * e2), le_abs_self (120 * d ^ 2 * d1 ^ 3 * e1 * e3), le_abs_self (160 * d ^ 2 * d1 ^ 3 * s4 * e1), le_abs_self (120 * d ^ 2 * d1 ^ 3 * e2 ^ 2), le_abs_self (240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1), le_abs_self (120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2), le_abs_self (20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2), le_abs_self (60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2), le_abs_self (240 * d * d1 ^ 5 * e2), le_abs_self (240 * d * d1 ^ 4 * d2 * e1), le_abs_self (240 * d * d1 ^ 4 * e1 * e2), le_abs_self (240 * d1 ^ 6 * e1), le_abs_self (120 * d1 ^ 5 * e1 ^ 2), neg_abs_le (8 * d ^ 4 * d1 * d2 * e4), neg_abs_le (8 * d ^ 4 * d1 * s4 * e3), neg_abs_le (24 * d ^ 4 * d2 ^ 2 * e3), neg_abs_le (8 * d ^ 4 * d2 * d4 * e1), neg_abs_le (8 * d ^ 4 * d2 * e1 * e4), neg_abs_le (24 * d ^ 4 * d2 * e2 * e3), neg_abs_le (8 * d ^ 4 * d2 * s4 * e2), neg_abs_le (8 * d ^ 4 * s4 * e1 * e3), neg_abs_le (8 * d ^ 4 * s4 ^ 2 * e1), neg_abs_le (8 * d ^ 4 * s4 * e2 ^ 2), neg_abs_le (24 * d ^ 3 * d1 ^ 3 * e4), neg_abs_le (24 * d ^ 3 * d1 ^ 2 * d2 * e3), neg_abs_le (24 * d ^ 3 * d1 ^ 2 * d4 * e1), neg_abs_le (24 * d ^ 3 * d1 ^ 2 * e1 * e4), neg_abs_le (72 * d ^ 3 * d1 ^ 2 * e2 * e3), neg_abs_le (88 * d ^ 3 * d1 ^ 2 * s4 * e2), neg_abs_le (216 * d ^ 3 * d1 * d2 ^ 2 * e2), neg_abs_le (96 * d ^ 3 * d1 * d2 * e1 * e3), neg_abs_le (80 * d ^ 3 * d1 * d2 * s4 * e1), neg_abs_le (96 * d ^ 3 * d1 * d2 * e2 ^ 2), neg_abs_le (16 * d ^ 3 * d1 * s4 * e1 * e2), neg_abs_le (24 * d ^ 3 * d2 ^ 3 * e1), neg_abs_le (24 * d ^ 3 * d2 ^ 2 * e1 * e2), neg_abs_le (120 * d ^ 2 * d1 ^ 4 * e3), neg_abs_le (120 * d ^ 2 * d1 ^ 3 * d2 * e2), neg_abs_le (120 * d ^ 2 * d1 ^ 3 * e1 * e3), neg_abs_le (160 * d ^ 2 * d1 ^ 3 * s4 * e1), neg_abs_le (120 * d ^ 2 * d1 ^ 3 * e2 ^ 2), neg_abs_le (240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1), neg_abs_le (120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2), neg_abs_le (20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2), neg_abs_le (60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2), neg_abs_le (240 * d * d1 ^ 5 * e2), neg_abs_le (240 * d * d1 ^ 4 * d2 * e1), neg_abs_le (240 * d * d1 ^ 4 * e1 * e2), neg_abs_le (240 * d1 ^ 6 * e1), neg_abs_le (120 * d1 ^ 5 * e1 ^ 2)]
    · linarith [le_abs_self (8 * d ^ 4 * d1 * d2 * e4), le_abs_self (8 * d ^ 4 * d1 * s4 * e3), le_abs_self (24 * d ^ 4 * d2 ^ 2 * e3), le_abs_self (8 * d ^ 4 * d2 * d4 * e1), le_abs_self (8 * d ^ 4 * d2 * e1 * e4), le_abs_self (24 * d ^ 4 * d2 * e2 * e3), le_abs_self (8 * d ^ 4 * d2 * s4 * e2), le_abs_self (8 * d ^ 4 * s4 * e1 * e3), le_abs_self (8 * d ^ 4 * s4 ^ 2 * e1), le_abs_self (8 * d ^ 4 * s4 * e2 ^ 2), le_abs_self (24 * d ^ 3 * d1 ^ 3 * e4), le_abs_self (24 * d ^ 3 * d1 ^ 2 * d2 * e3), le_abs_self (24 * d ^ 3 * d1 ^ 2 * d4 * e1), le_abs_self (24 * d ^ 3 * d1 ^ 2 * e1 * e4), le_abs_self (72 * d ^ 3 * d1 ^ 2 * e2 * e3), le_abs_self (88 * d ^ 3 * d1 ^ 2 * s4 * e2), le_abs_self (216 * d ^ 3 * d1 * d2 ^ 2 * e2), le_abs_self (96 * d ^ 3 * d1 * d2 * e1 * e3), le_abs_self (80 * d ^ 3 * d1 * d2 * s4 * e1), le_abs_self (96 * d ^ 3 * d1 * d2 * e2 ^ 2), le_abs_self (16 * d ^ 3 * d1 * s4 * e1 * e2), le_abs_self (24 * d ^ 3 * d2 ^ 3 * e1), le_abs_self (24 * d ^ 3 * d2 ^ 2 * e1 * e2), le_abs_self (120 * d ^ 2 * d1 ^ 4 * e3), le_abs_self (120 * d ^ 2 * d1 ^ 3 * d2 * e2), le_abs_self (120 * d ^ 2 * d1 ^ 3 * e1 * e3), le_abs_self (160 * d ^ 2 * d1 ^ 3 * s4 * e1), le_abs_self (120 * d ^ 2 * d1 ^ 3 * e2 ^ 2), le_abs_self (240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1), le_abs_self (120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2), le_abs_self (20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2), le_abs_self (60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2), le_abs_self (240 * d * d1 ^ 5 * e2), le_abs_self (240 * d * d1 ^ 4 * d2 * e1), le_abs_self (240 * d * d1 ^ 4 * e1 * e2), le_abs_self (240 * d1 ^ 6 * e1), le_abs_self (120 * d1 ^ 5 * e1 ^ 2), neg_abs_le (8 * d ^ 4 * d1 * d2 * e4), neg_abs_le (8 * d ^ 4 * d1 * s4 * e3), neg_abs_le (24 * d ^ 4 * d2 ^ 2 * e3), neg_abs_le (8 * d ^ 4 * d2 * d4 * e1), neg_abs_le (8 * d ^ 4 * d2 * e1 * e4), neg_abs_le (24 * d ^ 4 * d2 * e2 * e3), neg_abs_le (8 * d ^ 4 * d2 * s4 * e2), neg_abs_le (8 * d ^ 4 * s4 * e1 * e3), neg_abs_le (8 * d ^ 4 * s4 ^ 2 * e1), neg_abs_le (8 * d ^ 4 * s4 * e2 ^ 2), neg_abs_le (24 * d ^ 3 * d1 ^ 3 * e4), neg_abs_le (24 * d ^ 3 * d1 ^ 2 * d2 * e3), neg_abs_le (24 * d ^ 3 * d1 ^ 2 * d4 * e1), neg_abs_le (24 * d ^ 3 * d1 ^ 2 * e1 * e4), neg_abs_le (72 * d ^ 3 * d1 ^ 2 * e2 * e3), neg_abs_le (88 * d ^ 3 * d1 ^ 2 * s4 * e2), neg_abs_le (216 * d ^ 3 * d1 * d2 ^ 2 * e2), neg_abs_le (96 * d ^ 3 * d1 * d2 * e1 * e3), neg_abs_le (80 * d ^ 3 * d1 * d2 * s4 * e1), neg_abs_le (96 * d ^ 3 * d1 * d2 * e2 ^ 2), neg_abs_le (16 * d ^ 3 * d1 * s4 * e1 * e2), neg_abs_le (24 * d ^ 3 * d2 ^ 3 * e1), neg_abs_le (24 * d ^ 3 * d2 ^ 2 * e1 * e2), neg_abs_le (120 * d ^ 2 * d1 ^ 4 * e3), neg_abs_le (120 * d ^ 2 * d1 ^ 3 * d2 * e2), neg_abs_le (120 * d ^ 2 * d1 ^ 3 * e1 * e3), neg_abs_le (160 * d ^ 2 * d1 ^ 3 * s4 * e1), neg_abs_le (120 * d ^ 2 * d1 ^ 3 * e2 ^ 2), neg_abs_le (240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1), neg_abs_le (120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2), neg_abs_le (20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2), neg_abs_le (60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2), neg_abs_le (240 * d * d1 ^ 5 * e2), neg_abs_le (240 * d * d1 ^ 4 * d2 * e1), neg_abs_le (240 * d * d1 ^ 4 * e1 * e2), neg_abs_le (240 * d1 ^ 6 * e1), neg_abs_le (120 * d1 ^ 5 * e1 ^ 2)]
  have hSbd : |8 * d ^ 4 * d1 * d2 * e4|
        + |8 * d ^ 4 * d1 * s4 * e3|
        + |24 * d ^ 4 * d2 ^ 2 * e3|
        + |8 * d ^ 4 * d2 * d4 * e1|
        + |8 * d ^ 4 * d2 * e1 * e4|
        + |24 * d ^ 4 * d2 * e2 * e3|
        + |8 * d ^ 4 * d2 * s4 * e2|
        + |8 * d ^ 4 * s4 * e1 * e3|
        + |8 * d ^ 4 * s4 ^ 2 * e1|
        + |8 * d ^ 4 * s4 * e2 ^ 2|
        + |24 * d ^ 3 * d1 ^ 3 * e4|
        + |24 * d ^ 3 * d1 ^ 2 * d2 * e3|
        + |24 * d ^ 3 * d1 ^ 2 * d4 * e1|
        + |24 * d ^ 3 * d1 ^ 2 * e1 * e4|
        + |72 * d ^ 3 * d1 ^ 2 * e2 * e3|
        + |88 * d ^ 3 * d1 ^ 2 * s4 * e2|
        + |216 * d ^ 3 * d1 * d2 ^ 2 * e2|
        + |96 * d ^ 3 * d1 * d2 * e1 * e3|
        + |80 * d ^ 3 * d1 * d2 * s4 * e1|
        + |96 * d ^ 3 * d1 * d2 * e2 ^ 2|
        + |16 * d ^ 3 * d1 * s4 * e1 * e2|
        + |24 * d ^ 3 * d2 ^ 3 * e1|
        + |24 * d ^ 3 * d2 ^ 2 * e1 * e2|
        + |120 * d ^ 2 * d1 ^ 4 * e3|
        + |120 * d ^ 2 * d1 ^ 3 * d2 * e2|
        + |120 * d ^ 2 * d1 ^ 3 * e1 * e3|
        + |160 * d ^ 2 * d1 ^ 3 * s4 * e1|
        + |120 * d ^ 2 * d1 ^ 3 * e2 ^ 2|
        + |240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1|
        + |120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2|
        + |20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2|
        + |60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2|
        + |240 * d * d1 ^ 5 * e2|
        + |240 * d * d1 ^ 4 * d2 * e1|
        + |240 * d * d1 ^ 4 * e1 * e2|
        + |240 * d1 ^ 6 * e1|
        + |120 * d1 ^ 5 * e1 ^ 2|
      ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) ^ 2 * (l1 * (10 ^ 13 * (B / R)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 3 * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 72 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 88 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 216 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 80 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R)))
        + 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 16 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 3 * (l1 * (10 ^ 13 * (B / R)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 4 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 160 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 240 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 20 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) ^ 2
        + 60 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) ^ 2
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R)))
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 240 * (10 ^ 6 * B) ^ 6 * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 13 * (B / R))) ^ 2 := by
    linarith [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31, hb32, hb33, hb34, hb35, hb36]
  have hcomb : 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) ^ 2 * (l1 * (10 ^ 13 * (B / R)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 3 * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 72 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 88 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 216 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 80 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R)))
        + 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 16 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 3 * (l1 * (10 ^ 13 * (B / R)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 4 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 160 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 240 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 20 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) ^ 2
        + 60 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) ^ 2
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R)))
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 240 * (10 ^ 6 * B) ^ 6 * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 13 * (B / R))) ^ 2
      = (21970653527040000000000000000000000000000000000000000000000 : ℝ) * (l1 * B ^ 7 / R) + 111899368070400000000000000000000000000000000000000000000000000000 * (l1 ^ 2 * B ^ 7 / R ^ 2) := by
    field_simp; ring
  have hQ1b : l1 * B ^ 7 / R ≤ B ^ 7 / 10 ^ 110 := by
    rw [div_le_div_iff₀ hR (by positivity)]
    have key := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hB.le 7)
    calc l1 * B ^ 7 * 10 ^ 110 = 10 ^ 110 * l1 * B ^ 7 := by ring
      _ ≤ R * B ^ 7 := key
      _ = B ^ 7 * R := by ring
  have hQ2b : l1 ^ 2 * B ^ 7 / R ^ 2 ≤ B ^ 7 / 10 ^ 220 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key0 := mul_le_mul hsmall hsmall (by positivity) hR.le
    have key := mul_le_mul_of_nonneg_right key0 (pow_nonneg hB.le 7)
    calc l1 ^ 2 * B ^ 7 * 10 ^ 220 = 10 ^ 110 * l1 * (10 ^ 110 * l1) * B ^ 7 := by ring
      _ ≤ R * R * B ^ 7 := key
      _ = B ^ 7 * R ^ 2 := by ring
  have hcoef : (21970653527040000000000000000000000000000000000000000000000 : ℝ) / 10 ^ 110 + 111899368070400000000000000000000000000000000000000000000000000000 / 10 ^ 220 ≤ 1 / (2 * 10 ^ 42) := by norm_num
  have hfinal : (21970653527040000000000000000000000000000000000000000000000 : ℝ) * (l1 * B ^ 7 / R) + 111899368070400000000000000000000000000000000000000000000000000000 * (l1 ^ 2 * B ^ 7 / R ^ 2)
      ≤ B ^ 7 / (2 * 10 ^ 42) := by
    have t1 := mul_le_mul_of_nonneg_left hQ1b (show (0:ℝ) ≤ 21970653527040000000000000000000000000000000000000000000000 by norm_num)
    have t2 := mul_le_mul_of_nonneg_left hQ2b (show (0:ℝ) ≤ 111899368070400000000000000000000000000000000000000000000000000000 by norm_num)
    have hcoef2 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hB.le 7)
    calc (21970653527040000000000000000000000000000000000000000000000 : ℝ) * (l1 * B ^ 7 / R) + 111899368070400000000000000000000000000000000000000000000000000000 * (l1 ^ 2 * B ^ 7 / R ^ 2)
        ≤ 21970653527040000000000000000000000000000000000000000000000 * (B ^ 7 / 10 ^ 110) + 111899368070400000000000000000000000000000000000000000000000000000 * (B ^ 7 / 10 ^ 220) := by
          gcongr
      _ = (21970653527040000000000000000000000000000000000000000000000 / 10 ^ 110 + 111899368070400000000000000000000000000000000000000000000000000000 / 10 ^ 220) * B ^ 7 := by ring
      _ ≤ (1 / (2 * 10 ^ 42)) * B ^ 7 := hcoef2
      _ = B ^ 7 / (2 * 10 ^ 42) := by ring
  calc |8 * d ^ 4 * d1 * d2 * e4
        - 8 * d ^ 4 * d1 * s4 * e3
        + 24 * d ^ 4 * d2 ^ 2 * e3
        + 8 * d ^ 4 * d2 * d4 * e1
        + 8 * d ^ 4 * d2 * e1 * e4
        + 24 * d ^ 4 * d2 * e2 * e3
        + 8 * d ^ 4 * d2 * s4 * e2
        - 8 * d ^ 4 * s4 * e1 * e3
        - 8 * d ^ 4 * s4 ^ 2 * e1
        - 8 * d ^ 4 * s4 * e2 ^ 2
        + 24 * d ^ 3 * d1 ^ 3 * e4
        - 24 * d ^ 3 * d1 ^ 2 * d2 * e3
        + 24 * d ^ 3 * d1 ^ 2 * d4 * e1
        + 24 * d ^ 3 * d1 ^ 2 * e1 * e4
        + 72 * d ^ 3 * d1 ^ 2 * e2 * e3
        + 88 * d ^ 3 * d1 ^ 2 * s4 * e2
        - 216 * d ^ 3 * d1 * d2 ^ 2 * e2
        - 96 * d ^ 3 * d1 * d2 * e1 * e3
        - 80 * d ^ 3 * d1 * d2 * s4 * e1
        - 96 * d ^ 3 * d1 * d2 * e2 ^ 2
        + 16 * d ^ 3 * d1 * s4 * e1 * e2
        - 24 * d ^ 3 * d2 ^ 3 * e1
        - 24 * d ^ 3 * d2 ^ 2 * e1 * e2
        - 120 * d ^ 2 * d1 ^ 4 * e3
        - 120 * d ^ 2 * d1 ^ 3 * d2 * e2
        - 120 * d ^ 2 * d1 ^ 3 * e1 * e3
        - 160 * d ^ 2 * d1 ^ 3 * s4 * e1
        - 120 * d ^ 2 * d1 ^ 3 * e2 ^ 2
        + 240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1
        + 120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2
        - 20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2
        + 60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2
        + 240 * d * d1 ^ 5 * e2
        + 240 * d * d1 ^ 4 * d2 * e1
        + 240 * d * d1 ^ 4 * e1 * e2
        - 240 * d1 ^ 6 * e1
        - 120 * d1 ^ 5 * e1 ^ 2|
      ≤ |8 * d ^ 4 * d1 * d2 * e4|
        + |8 * d ^ 4 * d1 * s4 * e3|
        + |24 * d ^ 4 * d2 ^ 2 * e3|
        + |8 * d ^ 4 * d2 * d4 * e1|
        + |8 * d ^ 4 * d2 * e1 * e4|
        + |24 * d ^ 4 * d2 * e2 * e3|
        + |8 * d ^ 4 * d2 * s4 * e2|
        + |8 * d ^ 4 * s4 * e1 * e3|
        + |8 * d ^ 4 * s4 ^ 2 * e1|
        + |8 * d ^ 4 * s4 * e2 ^ 2|
        + |24 * d ^ 3 * d1 ^ 3 * e4|
        + |24 * d ^ 3 * d1 ^ 2 * d2 * e3|
        + |24 * d ^ 3 * d1 ^ 2 * d4 * e1|
        + |24 * d ^ 3 * d1 ^ 2 * e1 * e4|
        + |72 * d ^ 3 * d1 ^ 2 * e2 * e3|
        + |88 * d ^ 3 * d1 ^ 2 * s4 * e2|
        + |216 * d ^ 3 * d1 * d2 ^ 2 * e2|
        + |96 * d ^ 3 * d1 * d2 * e1 * e3|
        + |80 * d ^ 3 * d1 * d2 * s4 * e1|
        + |96 * d ^ 3 * d1 * d2 * e2 ^ 2|
        + |16 * d ^ 3 * d1 * s4 * e1 * e2|
        + |24 * d ^ 3 * d2 ^ 3 * e1|
        + |24 * d ^ 3 * d2 ^ 2 * e1 * e2|
        + |120 * d ^ 2 * d1 ^ 4 * e3|
        + |120 * d ^ 2 * d1 ^ 3 * d2 * e2|
        + |120 * d ^ 2 * d1 ^ 3 * e1 * e3|
        + |160 * d ^ 2 * d1 ^ 3 * s4 * e1|
        + |120 * d ^ 2 * d1 ^ 3 * e2 ^ 2|
        + |240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1|
        + |120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2|
        + |20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2|
        + |60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2|
        + |240 * d * d1 ^ 5 * e2|
        + |240 * d * d1 ^ 4 * d2 * e1|
        + |240 * d * d1 ^ 4 * e1 * e2|
        + |240 * d1 ^ 6 * e1|
        + |120 * d1 ^ 5 * e1 ^ 2| := htri
    _ ≤ 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 24 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) ^ 2 * (l1 * (10 ^ 13 * (B / R)))
        + 8 * (18 * (B * R)) ^ 4 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 3 * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (2 * 10 ^ 25 * (B / R ^ 3)) * (l1 * (10 ^ 13 * (B / R)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (118098 * 10 ^ 28 * (B / R ^ 4)))
        + 72 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 88 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 216 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 80 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R)))
        + 96 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 16 * (18 * (B * R)) ^ 3 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 3 * (l1 * (10 ^ 13 * (B / R)))
        + 24 * (18 * (B * R)) ^ 3 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 4 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
        + 160 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2
        + 240 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 20 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (10 ^ 19 * (B / R ^ 2)) * (l1 * (10 ^ 13 * (B / R))) ^ 2
        + 60 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (10 ^ 13 * (B / R)) ^ 2 * (l1 * (10 ^ 13 * (B / R))) ^ 2
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (10 ^ 13 * (B / R)) * (l1 * (10 ^ 13 * (B / R)))
        + 240 * (18 * (B * R)) * (10 ^ 6 * B) ^ 4 * (l1 * (10 ^ 13 * (B / R))) * (l1 * (10 ^ 19 * (B / R ^ 2)))
        + 240 * (10 ^ 6 * B) ^ 6 * (l1 * (10 ^ 13 * (B / R)))
        + 120 * (10 ^ 6 * B) ^ 5 * (l1 * (10 ^ 13 * (B / R))) ^ 2 := hSbd
    _ = (21970653527040000000000000000000000000000000000000000000000 : ℝ) * (l1 * B ^ 7 / R) + 111899368070400000000000000000000000000000000000000000000000000000 * (l1 ^ 2 * B ^ 7 / R ^ 2) := hcomb
    _ ≤ B ^ 7 / (2 * 10 ^ 42) := hfinal

end Squarefree
