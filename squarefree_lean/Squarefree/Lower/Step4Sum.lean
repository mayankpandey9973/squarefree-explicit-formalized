import Mathlib

/-!
# §5 Step 4 elementary `s`-sum bounds (writeup 1100–1106)

The three pure summation facts used in §5 Step 4:
`Σ_{1≤s≤N} √s ≤ N·√N` and `Σ_{1≤s≤N} 1/√s ≤ 2√N` (the count `Σ 1 = N` is `Nat.card_Icc`).
Sums are over `Finset.Icc 1 N` with `N : ℕ`, real-valued.
-/

namespace Squarefree

open Real Finset

/-- `Σ_{1≤s≤N} √s ≤ N·√N` (each term `≤ √N`). -/
theorem sum_sqrt_le (N : ℕ) :
    ∑ s ∈ Finset.Icc 1 N, Real.sqrt (s : ℝ) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
  have hterm : ∀ s ∈ Finset.Icc 1 N, Real.sqrt (s : ℝ) ≤ Real.sqrt (N : ℝ) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    exact Real.sqrt_le_sqrt (by exact_mod_cast hs.2)
  calc ∑ s ∈ Finset.Icc 1 N, Real.sqrt (s : ℝ)
      ≤ ∑ _s ∈ Finset.Icc 1 N, Real.sqrt (N : ℝ) := Finset.sum_le_sum hterm
    _ = (Finset.Icc 1 N).card • Real.sqrt (N : ℝ) := by rw [Finset.sum_const]
    _ = (N : ℝ) * Real.sqrt (N : ℝ) := by
          rw [Nat.card_Icc, nsmul_eq_mul]
          push_cast
          ring

/-- Per-term telescoping bound: for `s ≥ 1`, `1/√s ≤ 2·(√s − √(s−1))`. -/
private theorem inv_sqrt_le_two_sub (s : ℕ) (hs : 1 ≤ s) :
    (1 : ℝ) / Real.sqrt (s : ℝ) ≤ 2 * (Real.sqrt (s : ℝ) - Real.sqrt ((s : ℝ) - 1)) := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := le_trans zero_le_one hs1
  have hsm0 : (0 : ℝ) ≤ (s : ℝ) - 1 := by linarith
  have hsqs_pos : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by linarith)
  set a := Real.sqrt (s : ℝ) with ha
  set b := Real.sqrt ((s : ℝ) - 1) with hb
  have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  -- (a - b)(a + b) = s - (s-1) = 1
  have key : (a - b) * (a + b) = 1 := by
    have h1 : a * a = (s : ℝ) := Real.mul_self_sqrt hs0
    have h2 : b * b = (s : ℝ) - 1 := Real.mul_self_sqrt hsm0
    nlinarith [h1, h2]
  -- a + b ≤ 2a
  have hsum_le : a + b ≤ 2 * a := by linarith
  have hsum_pos : 0 < a + b := by linarith
  -- 2*(a-b) = 2/(a+b) (from key), and 1/a ≤ 2/(a+b) since a+b ≤ 2a.
  have hdiff : 2 * (a - b) = 2 / (a + b) := by
    rw [eq_div_iff (ne_of_gt hsum_pos)]
    nlinarith [key]
  rw [hdiff, div_le_div_iff₀ hsqs_pos hsum_pos]
  nlinarith [hsum_le, hsqs_pos]

/-- `Σ_{1≤s≤N} 1/√s ≤ 2√N` (telescoping `1/√s ≤ 2(√s − √(s−1))`). -/
theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ s ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (s : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))]
      have hstep : (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)
          ≤ 2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (((n + 1 : ℕ) : ℝ) - 1)) :=
        inv_sqrt_le_two_sub (n + 1) (Nat.le_add_left 1 n)
      have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
      have hcast2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hstep
      calc ∑ s ∈ Finset.Icc 1 n, (1 : ℝ) / Real.sqrt (s : ℝ)
            + (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)
          ≤ 2 * Real.sqrt (n : ℝ)
            + 2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) :=
            add_le_add ih hstep
        _ = 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by ring

/-- Gauss-sum bound over `Icc 1 N`: `∑_{n=1}^N n ≤ N²` (in `ℝ`). -/
private lemma gauss_sum_Icc_le_sq (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    push_cast
    nlinarith [ih, hk]

/-- `Σ_{1≤n≤N} 1/n ≤ N` (each term `1/n ≤ 1`). -/
theorem sum_inv_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ (N : ℝ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    rw [div_le_one (by linarith)]; exact hn1
  calc ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)
      ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- Step-4 **FAITHFUL** s-sum bound: the `c₀ + cm/√n + cp/n` weight summed over `1 ≤ n ≤ N`
is controlled by `c₀ N + cm·2√N + cp N` (`Σ1 = N`, `Σ1/√n ≤ 2√N`, `Σ1/n ≤ N`). -/
theorem step4_ssum_inv (c₀ cm cp : ℝ) (_h0 : 0 ≤ c₀) (hm : 0 ≤ cm) (hp : 0 ≤ cp) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (c₀ + cm / Real.sqrt (n:ℝ) + cp / (n:ℝ)))
      ≤ c₀ * (N:ℝ) + cm * (2 * Real.sqrt (N:ℝ)) + cp * (N:ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hp0 : (∑ _n ∈ Finset.Icc 1 N, c₀) = c₀ * (N:ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hpm : (∑ n ∈ Finset.Icc 1 N, cm / Real.sqrt (n:ℝ)) ≤ cm * (2 * Real.sqrt (N:ℝ)) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, cm / Real.sqrt (n:ℝ))
        = cm * ∑ n ∈ Finset.Icc 1 N, (1:ℝ) / Real.sqrt (n:ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => (mul_one_div _ _).symm)
    rw [hrw]; exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) hm
  have hpp : (∑ n ∈ Finset.Icc 1 N, cp / (n:ℝ)) ≤ cp * (N:ℝ) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, cp / (n:ℝ))
        = cp * ∑ n ∈ Finset.Icc 1 N, (1:ℝ) / (n:ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => (mul_one_div _ _).symm)
    rw [hrw]; exact mul_le_mul_of_nonneg_left (sum_inv_le N) hp
  rw [hp0]; linarith [hpm, hpp]

/-- Step-4 s-sum bound: the affine-plus-√-plus-reciprocal-√ weight summed over `1 ≤ n ≤ N`
is controlled by `c₃ N² + c₁ (N·√N) + c₀ N + cm · 2√N`. -/
theorem step4_ssum (c₃ c₁ c₀ cm : ℝ) (h3 : 0 ≤ c₃) (h1 : 0 ≤ c₁) (_h0 : 0 ≤ c₀)
    (hm : 0 ≤ cm) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (c₃ * (n:ℝ) + c₁ * Real.sqrt (n:ℝ) + c₀ + cm / Real.sqrt (n:ℝ)))
      ≤ c₃ * (N:ℝ)^2 + c₁ * ((N:ℝ) * Real.sqrt (N:ℝ)) + c₀ * (N:ℝ)
        + cm * (2 * Real.sqrt (N:ℝ)) := by
  -- split the sum into four pieces
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Piece 1: ∑ c₃*n = c₃ * ∑ n ≤ c₃ * N²
  have hp1 : (∑ n ∈ Finset.Icc 1 N, c₃ * (n:ℝ)) ≤ c₃ * (N:ℝ)^2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (gauss_sum_Icc_le_sq N) h3
  -- Piece 2: ∑ c₁*√n = c₁ * ∑ √n ≤ c₁ * (N·√N)
  have hp2 : (∑ n ∈ Finset.Icc 1 N, c₁ * Real.sqrt (n:ℝ))
      ≤ c₁ * ((N:ℝ) * Real.sqrt (N:ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_sqrt_le N) h1
  -- Piece 3: ∑ c₀ = c₀ * N
  have hp3 : (∑ _n ∈ Finset.Icc 1 N, c₀) = c₀ * (N:ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring
  -- Piece 4: ∑ cm/√n = cm * ∑ (1/√n) ≤ cm * 2√N
  have hp4 : (∑ n ∈ Finset.Icc 1 N, cm / Real.sqrt (n:ℝ))
      ≤ cm * (2 * Real.sqrt (N:ℝ)) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, cm / Real.sqrt (n:ℝ))
        = cm * ∑ n ∈ Finset.Icc 1 N, (1:ℝ) / Real.sqrt (n:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_one_div]
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) hm
  rw [hp3]
  linarith [hp1, hp2, hp4]

end Squarefree
