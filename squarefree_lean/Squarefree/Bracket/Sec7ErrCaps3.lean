import Squarefree.Bracket.Sec7ErrPieces

/-!
# §7 N11 order-3 banked numeric caps (Φ″ endgame)

The `m = 3` siblings of `sec7E_cap{1,2,5,9,17}` (Sec7ErrPieces): the falling-factorial
caps `|aprod α k|·(2cWin)^{k-α}` over `k ≤ 3`.  The `k ≤ 2` cases reuse the existing caps;
the `k = 3` case is discharged directly (integer exponents) or via the quarter-power helper
`sec7_rpow_quarter_le`.  The cap ceilings are loosened to round powers of ten so the order-3
monomial bounds collapse cleanly into the `errScale` slots.
-/

open Classical Real

namespace Squarefree

theorem sec7E_cap1_3 : ∀ k ≤ 3,
    |sec7_aprod (-(1:ℝ)) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(1:ℝ))) ≤ (10 ^ 14 : ℝ) := by
  intro k hk
  interval_cases k
  · exact le_trans (sec7E_cap1 0 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap1 1 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap1 2 (by norm_num)) (by norm_num)
  · have he : ((3:ℕ):ℝ) - (-(1:ℝ)) = ((4:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]

theorem sec7E_cap2_3 : ∀ k ≤ 3,
    |sec7_aprod (-(2:ℝ)) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(2:ℝ))) ≤ (10 ^ 18 : ℝ) := by
  intro k hk
  interval_cases k
  · exact le_trans (sec7E_cap2 0 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap2 1 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap2 2 (by norm_num)) (by norm_num)
  · have he : ((3:ℕ):ℝ) - (-(2:ℝ)) = ((5:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]

theorem sec7E_cap5_3 : ∀ k ≤ 3,
    |sec7_aprod (-(5:ℝ)/4) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(5:ℝ)/4)) ≤ (2 * 10 ^ 15 : ℝ) := by
  intro k hk
  interval_cases k
  · exact le_trans (sec7E_cap5 0 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap5 1 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap5 2 (by norm_num)) (by norm_num)
  · have he : ((3:ℕ):ℝ) - (-(5:ℝ)/4) = ((17:ℕ):ℝ) / 4 := by norm_num
    rw [he]
    have h1 := sec7_rpow_quarter_le (q := 17) (b := 15 * 10 ^ 13)
      (by norm_num) (by norm_num [sec7_cWin])
    calc |sec7_aprod (-(5:ℝ)/4) 3| * (2 * sec7_cWin) ^ (((17:ℕ):ℝ) / 4)
        ≤ (585 / 64) * (15 * 10 ^ 13) := by
          apply mul_le_mul _ h1 (Real.rpow_nonneg (by norm_num [sec7_cWin]) _) (by norm_num)
          norm_num [sec7_aprod]
      _ ≤ 2 * 10 ^ 15 := by norm_num

theorem sec7E_cap9_3 : ∀ k ≤ 3,
    |sec7_aprod (-(9:ℝ)/4) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(9:ℝ)/4)) ≤ (10 ^ 19 : ℝ) := by
  intro k hk
  interval_cases k
  · exact le_trans (sec7E_cap9 0 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap9 1 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap9 2 (by norm_num)) (by norm_num)
  · have he : ((3:ℕ):ℝ) - (-(9:ℝ)/4) = ((21:ℕ):ℝ) / 4 := by norm_num
    rw [he]
    have h1 := sec7_rpow_quarter_le (q := 21) (b := 25 * 10 ^ 16)
      (by norm_num) (by norm_num [sec7_cWin])
    calc |sec7_aprod (-(9:ℝ)/4) 3| * (2 * sec7_cWin) ^ (((21:ℕ):ℝ) / 4)
        ≤ (1989 / 64) * (25 * 10 ^ 16) := by
          apply mul_le_mul _ h1 (Real.rpow_nonneg (by norm_num [sec7_cWin]) _) (by norm_num)
          norm_num [sec7_aprod]
      _ ≤ 10 ^ 19 := by norm_num

theorem sec7E_cap17_3 : ∀ k ≤ 3,
    |sec7_aprod (-(17:ℝ)/4) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(17:ℝ)/4)) ≤
      (2 * 10 ^ 26 : ℝ) := by
  intro k hk
  interval_cases k
  · exact le_trans (sec7E_cap17 0 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap17 1 (by norm_num)) (by norm_num)
  · exact le_trans (sec7E_cap17 2 (by norm_num)) (by norm_num)
  · have he : ((3:ℕ):ℝ) - (-(17:ℝ)/4) = ((29:ℕ):ℝ) / 4 := by norm_num
    rw [he]
    have h1 := sec7_rpow_quarter_le (q := 29) (b := 10 ^ 24)
      (by norm_num) (by norm_num [sec7_cWin])
    calc |sec7_aprod (-(17:ℝ)/4) 3| * (2 * sec7_cWin) ^ (((29:ℕ):ℝ) / 4)
        ≤ (8925 / 64) * (10 ^ 24) := by
          apply mul_le_mul _ h1 (Real.rpow_nonneg (by norm_num [sec7_cWin]) _) (by norm_num)
          norm_num [sec7_aprod]
      _ ≤ 2 * 10 ^ 26 := by norm_num

end Squarefree
