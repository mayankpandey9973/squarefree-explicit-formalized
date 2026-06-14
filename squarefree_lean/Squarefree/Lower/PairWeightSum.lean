import Mathlib

/-!
# Pair-weight sum bound (§ lower bound, elementary)

`pair_weight_sum`: a purely arithmetic estimate
`∑_{1≤ℓ₁,ℓ₂≤W} [ℓ₁<ℓ₂] / (ℓ₁ ℓ₂ (ℓ₂−ℓ₁)) ≤ 4 W`.

Proof is elementary: drop the `(ℓ₂−ℓ₁) ≥ 1` factor to bound each term by `1/(ℓ₁ℓ₂)`,
factor the double sum as the square of the harmonic sum `H_W = ∑_{ℓ=1}^W 1/ℓ`, and use the
harmonic bound `H_W ≤ 2√W` (proved here by `√`-telescoping). Then `H_W² ≤ 4W`.
-/

namespace Squarefree

open Finset

/-- Per-term reciprocal bound used for the harmonic telescope:
for `i ≥ 1`, `1/i ≤ 2(√i − √(i−1))`. -/
private lemma recip_le_sqrt_telescope (i : ℕ) (hi : 1 ≤ i) :
    (1 : ℝ) / i ≤ 2 * (Real.sqrt i - Real.sqrt (i - 1)) := by
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hipos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le one_pos hi1
  have hi1nonneg : (0 : ℝ) ≤ (i : ℝ) - 1 := by linarith
  set a := Real.sqrt i with ha
  set b := Real.sqrt ((i : ℝ) - 1) with hb
  have ha2 : a ^ 2 = (i : ℝ) := Real.sq_sqrt (le_of_lt hipos)
  have hb2 : b ^ 2 = (i : ℝ) - 1 := Real.sq_sqrt hi1nonneg
  have hanonneg : 0 ≤ a := Real.sqrt_nonneg _
  have hbnonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hapos : 0 < a := by
    have h2 : (0 : ℝ) < a ^ 2 := by rw [ha2]; exact hipos
    nlinarith [hanonneg]
  -- a^2 - b^2 = 1
  have hdiff : a ^ 2 - b ^ 2 = 1 := by rw [ha2, hb2]; ring
  -- b ≤ a  (since i-1 ≤ i)
  have hba : b ≤ a := by
    rw [ha, hb]; exact Real.sqrt_le_sqrt (by linarith)
  have hsum_le : a + b ≤ 2 * a := by linarith
  -- (a-b)(a+b) = 1
  have hab1 : (a - b) * (a + b) = 1 := by nlinarith [hdiff]
  -- 1/(2a) ≤ a - b
  have key : (1 : ℝ) / (2 * a) ≤ a - b := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hab1, hsum_le, hapos, hba]
  -- a = √i ≤ i  (since i ≥ 1, a² = i ≤ i² = (a²)²)
  have hai : a ≤ (i : ℝ) := by
    have h1 : a ^ 2 ≤ (i : ℝ) ^ 2 := by rw [ha2]; nlinarith [hi1]
    nlinarith [hanonneg, hipos, h1]
  -- 1/i ≤ 1/a
  have hrecip : (1 : ℝ) / i ≤ 1 / a := by
    apply div_le_div_of_nonneg_left (by norm_num) hapos hai
  -- 1/a ≤ 1/(2a) * 2 ... we want 1/i ≤ 2(a-b). Note 1/a = 2 * (1/(2a)).
  have h2a : (1 : ℝ) / a = 2 * (1 / (2 * a)) := by
    field_simp
  calc (1 : ℝ) / i ≤ 1 / a := hrecip
    _ = 2 * (1 / (2 * a)) := h2a
    _ ≤ 2 * (a - b) := by linarith [key]

/-- Harmonic upper bound: `∑_{ℓ=1}^W 1/ℓ ≤ 2√W`. -/
private lemma harmonic_le_two_sqrt (W : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 W, (1 : ℝ) / ℓ) ≤ 2 * Real.sqrt W := by
  -- reindex Icc 1 W to range W via i ↦ i+1
  have hreindex :
      (∑ ℓ ∈ Finset.Icc 1 W, (1 : ℝ) / ℓ)
        = ∑ i ∈ Finset.range W, (1 : ℝ) / (i + 1) := by
    rw [← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast; ring
  rw [hreindex]
  -- termwise: 1/(i+1) ≤ 2(√(i+1) - √i)
  have hterm : ∀ i ∈ Finset.range W,
      (1 : ℝ) / (i + 1) ≤ 2 * (Real.sqrt (i + 1) - Real.sqrt i) := by
    intro i _
    have h := recip_le_sqrt_telescope (i + 1) (Nat.le_add_left 1 i)
    have e2 : ((i + 1 : ℕ) : ℝ) - 1 = (i : ℝ) := by push_cast; ring
    have e1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [e2, e1] at h
    exact h
  have hsum_le :
      (∑ i ∈ Finset.range W, (1 : ℝ) / (i + 1))
        ≤ ∑ i ∈ Finset.range W, 2 * (Real.sqrt (i + 1) - Real.sqrt i) :=
    Finset.sum_le_sum hterm
  refine le_trans hsum_le ?_
  -- telescope: ∑ 2(√(i+1) - √i) = 2√W
  have htel :
      (∑ i ∈ Finset.range W, 2 * (Real.sqrt (i + 1) - Real.sqrt i))
        = 2 * Real.sqrt W := by
    have hcongr :
        (∑ i ∈ Finset.range W, 2 * (Real.sqrt (i + 1) - Real.sqrt i))
          = ∑ i ∈ Finset.range W,
              ((fun n : ℕ => 2 * Real.sqrt n) (i + 1) - (fun n : ℕ => 2 * Real.sqrt n) i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only
      push_cast
      ring
    rw [hcongr, Finset.sum_range_sub (fun n : ℕ => 2 * Real.sqrt n) W]
    simp [Real.sqrt_zero]
  rw [htel]

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

/-- Step-3 f-sum bound: the affine-plus-reciprocal weight summed over `1 ≤ n ≤ N`
is controlled by `κ N² + ρ N + (ρ/κ) · 2√N`. -/
theorem step3_fsum_half (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (κ * (n:ℝ) + ρ + ρ / (κ * (n:ℝ))))
      ≤ κ * (N:ℝ)^2 + ρ * (N:ℝ) + (ρ / κ) * (2 * Real.sqrt (N:ℝ)) := by
  -- split the sum into three pieces
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Piece 1: ∑ κ*n = κ * ∑ n ≤ κ * N²
  have h1 : (∑ n ∈ Finset.Icc 1 N, κ * (n:ℝ)) ≤ κ * (N:ℝ)^2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (gauss_sum_Icc_le_sq N) (le_of_lt hκ)
  -- Piece 2: ∑ ρ = ρ * N
  have h2 : (∑ _n ∈ Finset.Icc 1 N, ρ) = ρ * (N:ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  -- Piece 3: ∑ ρ/(κ*n) = (ρ/κ) * ∑ 1/n ≤ (ρ/κ) * 2√N
  have h3 : (∑ n ∈ Finset.Icc 1 N, ρ / (κ * (n:ℝ)))
      ≤ (ρ / κ) * (2 * Real.sqrt (N:ℝ)) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, ρ / (κ * (n:ℝ)))
        = (ρ / κ) * ∑ n ∈ Finset.Icc 1 N, (1:ℝ) / (n:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
      rw [div_mul_div_comm, mul_one]
    rw [hrw]
    have hρκ : (0 : ℝ) ≤ ρ / κ := div_nonneg hρ (le_of_lt hκ)
    exact mul_le_mul_of_nonneg_left (harmonic_le_two_sqrt N) hρκ
  rw [h2]
  linarith [h1, h3]

/-- Harmonic upper bound (log form): `∑_{n=1}^N 1/n ≤ log N + 1`.
Proved from mathlib's `harmonic_le_one_add_log` (`harmonic N ≤ 1 + log N`) plus
`harmonic_eq_sum_Icc` (`harmonic N = ∑_{1≤i≤N} i⁻¹`). -/
private lemma harmonic_le_log_add_one (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ≤ Real.log (N : ℝ) + 1 := by
  have hsum : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ))
      = ((harmonic N : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [one_div]
  rw [hsum]
  have h := harmonic_le_one_add_log N
  linarith

/-- Step-3 f-sum bound (log form): the affine-plus-reciprocal weight summed over `1 ≤ n ≤ N`
is controlled by `κ N² + ρ N + (ρ/κ) · (log N + 1)`. -/
theorem step3_fsum_half_log (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (κ * (n:ℝ) + ρ + ρ / (κ * (n:ℝ))))
      ≤ κ * (N:ℝ)^2 + ρ * (N:ℝ) + (ρ / κ) * (Real.log (N:ℝ) + 1) := by
  -- split the sum into three pieces
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Piece 1: ∑ κ*n = κ * ∑ n ≤ κ * N²
  have h1 : (∑ n ∈ Finset.Icc 1 N, κ * (n:ℝ)) ≤ κ * (N:ℝ)^2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (gauss_sum_Icc_le_sq N) (le_of_lt hκ)
  -- Piece 2: ∑ ρ = ρ * N
  have h2 : (∑ _n ∈ Finset.Icc 1 N, ρ) = ρ * (N:ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  -- Piece 3: ∑ ρ/(κ*n) = (ρ/κ) * ∑ 1/n ≤ (ρ/κ) * (log N + 1)
  have h3 : (∑ n ∈ Finset.Icc 1 N, ρ / (κ * (n:ℝ)))
      ≤ (ρ / κ) * (Real.log (N:ℝ) + 1) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, ρ / (κ * (n:ℝ)))
        = (ρ / κ) * ∑ n ∈ Finset.Icc 1 N, (1:ℝ) / (n:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
      rw [div_mul_div_comm, mul_one]
    rw [hrw]
    have hρκ : (0 : ℝ) ≤ ρ / κ := div_nonneg hρ (le_of_lt hκ)
    exact mul_le_mul_of_nonneg_left (harmonic_le_log_add_one N) hρκ
  rw [h2]
  linarith [h1, h3]

/-- Pair-weight sum bound: the `if`-guarded reciprocal sum is at most `4 W`. -/
theorem pair_weight_sum (W : ℕ) :
    (∑ p ∈ Finset.Icc 1 W ×ˢ Finset.Icc 1 W,
       (if p.1 < p.2 then (1:ℝ) / ((p.1 : ℝ) * (p.2 : ℝ) * ((p.2 : ℝ) - (p.1 : ℝ))) else 0))
      ≤ 4 * (W : ℝ) := by
  -- Step 1+2: bound each guarded term by 1/(ℓ₁ ℓ₂)
  have hbound :
      (∑ p ∈ Finset.Icc 1 W ×ˢ Finset.Icc 1 W,
         (if p.1 < p.2 then (1:ℝ) / ((p.1 : ℝ) * (p.2 : ℝ) * ((p.2 : ℝ) - (p.1 : ℝ))) else 0))
        ≤ ∑ p ∈ Finset.Icc 1 W ×ˢ Finset.Icc 1 W,
            (1 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨h11, _⟩, ⟨h21, _⟩⟩ := hp
    have hp1pos : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast h11
    have hp2pos : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast h21
    have hrhs_nonneg : (0 : ℝ) ≤ 1 / ((p.1 : ℝ) * (p.2 : ℝ)) := by positivity
    by_cases hlt : p.1 < p.2
    · simp only [hlt, if_true]
      have hdiff1 : (1 : ℝ) ≤ (p.2 : ℝ) - (p.1 : ℝ) := by
        have : (p.1 : ℝ) + 1 ≤ (p.2 : ℝ) := by exact_mod_cast hlt
        linarith
      have hdiffpos : (0 : ℝ) < (p.2 : ℝ) - (p.1 : ℝ) := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (p.1 : ℝ) * (p.2 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) * ((p.2 : ℝ) - (p.1 : ℝ)) := by
        nlinarith [mul_pos hp1pos hp2pos, hdiff1]
      linarith
    · simp only [hlt, if_false]
      exact hrhs_nonneg
  refine le_trans hbound ?_
  -- Step 3: factor as (∑ 1/ℓ)²
  have hfactor :
      (∑ p ∈ Finset.Icc 1 W ×ˢ Finset.Icc 1 W, (1 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)))
        = (∑ ℓ ∈ Finset.Icc 1 W, (1 : ℝ) / ℓ) ^ 2 := by
    rw [Finset.sum_product]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [div_mul_div_comm, one_mul]
  rw [hfactor]
  -- Step 4+5: harmonic ≤ 2√W, square, (√W)² = W
  have hH := harmonic_le_two_sqrt W
  have hHnonneg : (0 : ℝ) ≤ ∑ ℓ ∈ Finset.Icc 1 W, (1 : ℝ) / ℓ := by
    apply Finset.sum_nonneg
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.1
    positivity
  have hsqW : (Real.sqrt W) ^ 2 = (W : ℝ) := Real.sq_sqrt (by positivity)
  calc (∑ ℓ ∈ Finset.Icc 1 W, (1 : ℝ) / ℓ) ^ 2
      ≤ (2 * Real.sqrt W) ^ 2 := by
        apply pow_le_pow_left₀ hHnonneg hH
    _ = 4 * ((Real.sqrt W) ^ 2) := by ring
    _ = 4 * (W : ℝ) := by rw [hsqW]

end Squarefree
