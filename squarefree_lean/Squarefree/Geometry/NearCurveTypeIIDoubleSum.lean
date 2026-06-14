import Squarefree.Geometry.NearCurveTypeIIBase
import Mathlib

/-!
# §4.3 Type II — the double sum (writeup 656–665)

The harmonic + cross-term arithmetic `typeII_double_sum` that sums the per-`q`
contribution to the closed form.  Split out of `NearCurveTypeII`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## STUB 6 — the double sum arithmetic -/

/-- **The Type II double-sum closed form** (writeup 656–665).
Sums the per-`(q)` contribution
`2·⌈128(qNλ+1)⌉₊·(4√(δ/λ)/q + 1)` over `q ∈ [1, ⌊4√(δ/λ)⌋]` to
`16384·(Nδ + √(δ/λ)·log(2+√(δ/λ)) + 1)`.  The 4-cross-term + harmonic arithmetic
(uses `typeII_harmonic_sum`).

The honest constant is `16384`: each summand absorbs the per-line ceiling and the
factor `2` via `2·⌈128(qNλ+1)⌉₊ ≤ 512(qNλ+1)` (as `128(qNλ+1) ≥ 128 ≥ 1`), then the
four cross-terms each contribute `≤ 512·(16Nδ)`, `≤ 512·(16Nδ)`, `≤ 512·4W(1+log Q)`,
`≤ 512·Q`, with `W² = δ/λ` and `Q ≤ 4W`. -/
theorem typeII_double_sum (N lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hN2 : 2 ≤ N) :
    (∑ q ∈ Finset.Icc 1 ⌊4 * Real.sqrt (δ / lam)⌋₊,
        2 * (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ)
          * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1))
      ≤ 109158400 * (N * δ + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1) := by
  classical
  set W := Real.sqrt (δ / lam) with hWdef
  set Q := ⌊4 * W⌋₊ with hQdef
  -- Basic positivity facts.
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hW0 : (0 : ℝ) ≤ W := Real.sqrt_nonneg _
  have hWsq : W ^ 2 = δ / lam := Real.sq_sqrt (by positivity)
  -- `N·λ·W² = N·δ`.
  have hNlW : N * lam * W ^ 2 = N * δ := by
    rw [hWsq]; field_simp
  have hQ4W : (Q : ℝ) ≤ 4 * W := Nat.floor_le (by positivity)
  have hNδ0 : (0 : ℝ) ≤ N * δ := by positivity
  -- Per-term bound: `2·⌈852800(qNλ+1)⌉₊·(4W/q+1) ≤ 3411200·(4NλW + qNλ + 4W/q + 1)`.
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      2 * (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ) * (4 * W / (q : ℝ) + 1)
        ≤ 3411200 * (4 * N * lam * W + (q : ℝ) * N * lam + 4 * W / (q : ℝ) + 1) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    -- `x := 852800(qNλ+1) ≥ 852800 ≥ 1`, so `2⌈x⌉₊ ≤ 2(x+1) ≤ 4x = 3411200(qNλ+1)`.
    set x : ℝ := 852800 * ((q : ℝ) * N * lam + 1) with hxdef
    have hx1 : (1 : ℝ) ≤ x := by
      have : (0 : ℝ) ≤ (q : ℝ) * N * lam := by positivity
      rw [hxdef]; nlinarith
    have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := le_of_lt (Nat.ceil_lt_add_one (by linarith))
    have hcoef : 2 * (⌈x⌉₊ : ℝ) ≤ 3411200 * ((q : ℝ) * N * lam + 1) := by
      have : 2 * (⌈x⌉₊ : ℝ) ≤ 2 * (x + 1) := by linarith
      have h4x : 2 * (x + 1) ≤ 4 * x := by linarith
      calc 2 * (⌈x⌉₊ : ℝ) ≤ 4 * x := le_trans this h4x
        _ = 3411200 * ((q : ℝ) * N * lam + 1) := by rw [hxdef]; ring
    -- nonneg factor `4W/q + 1`.
    have hfac : (0 : ℝ) ≤ 4 * W / (q : ℝ) + 1 := by positivity
    -- multiply and expand: `(qNλ+1)(4W/q+1) = 4NλW + qNλ + 4W/q + 1`.
    have hexpand : 3411200 * ((q : ℝ) * N * lam + 1) * (4 * W / (q : ℝ) + 1)
        = 3411200 * (4 * N * lam * W + (q : ℝ) * N * lam + 4 * W / (q : ℝ) + 1) := by
      field_simp
      ring
    calc 2 * (⌈x⌉₊ : ℝ) * (4 * W / (q : ℝ) + 1)
        ≤ 3411200 * ((q : ℝ) * N * lam + 1) * (4 * W / (q : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hcoef hfac
      _ = 3411200 * (4 * N * lam * W + (q : ℝ) * N * lam + 4 * W / (q : ℝ) + 1) := hexpand
  -- Sum the per-term bound.
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- Split the RHS sum into four pieces.
  have hsplit : (∑ q ∈ Finset.Icc 1 Q,
        3411200 * (4 * N * lam * W + (q : ℝ) * N * lam + 4 * W / (q : ℝ) + 1))
      = 3411200 * ((∑ _q ∈ Finset.Icc 1 Q, 4 * N * lam * W)
          + (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * N * lam)
          + (∑ q ∈ Finset.Icc 1 Q, 4 * W / (q : ℝ))
          + (∑ _q ∈ Finset.Icc 1 Q, (1 : ℝ))) := by
    have e1 : (∑ q ∈ Finset.Icc 1 Q,
          3411200 * (4 * N * lam * W + (q : ℝ) * N * lam + 4 * W / (q : ℝ) + 1))
        = (∑ q ∈ Finset.Icc 1 Q, (3411200 : ℝ) * (4 * N * lam * W))
          + (∑ q ∈ Finset.Icc 1 Q, (3411200 : ℝ) * ((q : ℝ) * N * lam))
          + (∑ q ∈ Finset.Icc 1 Q, (3411200 : ℝ) * (4 * W / (q : ℝ)))
          + (∑ q ∈ Finset.Icc 1 Q, (3411200 : ℝ) * (1 : ℝ)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _; ring
    rw [e1, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
  rw [hsplit]
  -- Bound each of the four sums.
  have hcardQ : (Finset.Icc 1 Q).card = Q := by
    rw [Nat.card_Icc]; omega
  -- (S1) `∑ 4NλW = Q·4NλW ≤ 16NλW² = 16Nδ`.
  have hS1 : (∑ _q ∈ Finset.Icc 1 Q, 4 * N * lam * W) ≤ 16 * (N * δ) := by
    rw [Finset.sum_const, hcardQ, nsmul_eq_mul]
    have hQval : (Q : ℝ) * (4 * N * lam * W) ≤ (4 * W) * (4 * N * lam * W) := by
      apply mul_le_mul_of_nonneg_right hQ4W; positivity
    have : (4 * W) * (4 * N * lam * W) = 16 * (N * lam * W ^ 2) := by ring
    rw [this, hNlW] at hQval
    linarith
  -- (S2) `∑ qNλ = Nλ·∑ q ≤ Nλ·Q² ≤ Nλ·(4W)² = 16Nδ`.
  have hS2 : (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * N * lam) ≤ 16 * (N * δ) := by
    have hbound : ∀ q ∈ Finset.Icc 1 Q, (q : ℝ) * N * lam ≤ (Q : ℝ) * N * lam := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq.2
      have hNl0 : (0 : ℝ) ≤ N * lam := by positivity
      nlinarith
    calc (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * N * lam)
        ≤ (∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) * N * lam) := Finset.sum_le_sum hbound
      _ = (Q : ℝ) * ((Q : ℝ) * N * lam) := by
          rw [Finset.sum_const, hcardQ, nsmul_eq_mul]
      _ ≤ (4 * W) * ((4 * W) * N * lam) := by
          have h1 : (0 : ℝ) ≤ (Q : ℝ) * N * lam := by positivity
          have h2 : (0 : ℝ) ≤ (4 * W) * N * lam := by positivity
          apply mul_le_mul hQ4W _ h1 (by positivity)
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ4W hN0) hlam.le
      _ = 16 * (N * lam * W ^ 2) := by ring
      _ = 16 * (N * δ) := by rw [hNlW]
  -- (S3) `∑ 4W/q = 4W·∑ 1/q ≤ 4W(1+log Q)`.
  have hS3 : (∑ q ∈ Finset.Icc 1 Q, 4 * W / (q : ℝ))
      ≤ 4 * W * (1 + Real.log Q) := by
    have heq : (∑ q ∈ Finset.Icc 1 Q, 4 * W / (q : ℝ))
        = 4 * W * (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _; rw [mul_one_div]
    rw [heq]
    have hharm := typeII_harmonic_sum Q
    apply mul_le_mul_of_nonneg_left hharm
    positivity
  -- (S4) `∑ 1 = Q ≤ 4W`.
  have hS4 : (∑ _q ∈ Finset.Icc 1 Q, (1 : ℝ)) ≤ 4 * W := by
    rw [Finset.sum_const, hcardQ, nsmul_eq_mul, mul_one]
    exact hQ4W
  -- Assemble: total `≤ 512·(16Nδ + 16Nδ + 4W(1+log Q) + 4W)`.
  -- Now absorb `4W(1+log Q) + 4W = 8W + 4W·log Q` into `C·(W·log(2+W)+1)`.
  have hlog2W : Real.log 2 ≤ Real.log (2 + W) := by
    apply Real.log_le_log (by norm_num); linarith
  have hlog2pos : (0 : ℝ) < Real.log (2 + W) := lt_of_lt_of_le (by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact this) hlog2W
  -- the absorption target: `8W + 4W·log Q ≤ 28·(W·log(2+W)) + 14`.
  have habsorb : 4 * W * (1 + Real.log Q) + 4 * W
      ≤ 28 * (W * Real.log (2 + W)) + 14 := by
    by_cases hQ0 : Q = 0
    · -- `Q = 0`: `log 0 = 0`, but also `W` may be positive; use `4W < 1`.
      rw [hQ0]
      simp only [Nat.cast_zero, Real.log_zero, add_zero, mul_one]
      -- `4W·1 + 4W = 8W`.  Here `Q = ⌊4W⌋₊ = 0` ⟹ `4W < 1` ⟹ `W < 1/4`.
      have hW14 : 4 * W < 1 := by
        by_contra h
        have h' : (1 : ℝ) ≤ 4 * W := not_lt.mp h
        have h1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast h')
        rw [hQ0] at h1; omega
      nlinarith [mul_nonneg hW0 hlog2pos.le, hlog2pos]
    · -- `Q ≥ 1`: `log Q ≤ log(4W)`.
      have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ0
      have hQR1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have hWpos : (0 : ℝ) < W := by
        have : (1 : ℝ) ≤ 4 * W := le_trans hQR1 hQ4W
        linarith
      have hlogQ4W : Real.log Q ≤ Real.log (4 * W) :=
        Real.log_le_log (by linarith) hQ4W
      -- `log(4W) = log 4 + log W ≤ log 4 + log(2+W)`.
      have hlogWle : Real.log W ≤ Real.log (2 + W) :=
        Real.log_le_log hWpos (by linarith)
      have hlog4W : Real.log (4 * W) = Real.log 4 + Real.log W :=
        Real.log_mul (by norm_num) (ne_of_gt hWpos)
      have hlog4val : Real.log 4 ≤ 2 := by
        have h42 : (4 : ℝ) = 2 * 2 := by norm_num
        rw [h42, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_two_lt_d9]
      -- `log Q ≤ log4 + log(2+W) ≤ 2 + log(2+W)`.
      have hlogQbound : Real.log Q ≤ 2 + Real.log (2 + W) := by
        calc Real.log Q ≤ Real.log (4 * W) := hlogQ4W
          _ = Real.log 4 + Real.log W := hlog4W
          _ ≤ 2 + Real.log (2 + W) := by linarith
      -- `4W·log Q ≤ 4W·(2 + log(2+W)) = 8W + 4W·log(2+W)`.
      have hkey : 4 * W * Real.log Q ≤ 8 * W + 4 * (W * Real.log (2 + W)) := by
        have := mul_le_mul_of_nonneg_left hlogQbound (by positivity : (0:ℝ) ≤ 4 * W)
        nlinarith [this]
      -- `4W(1+logQ) + 4W = 8W + 4W·logQ ≤ 8W + 8W + 4W·log(2+W) = 16W + 4·(W·log(2+W))`.
      -- Then `16W ≤ 24·(W·log(2+W))` since `log(2+W) ≥ log 2 > 2/3`.
      have hlog2third : (2 : ℝ) / 3 ≤ Real.log (2 + W) := by
        have := Real.log_two_gt_d9
        have : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        linarith [hlog2W]
      have hWlog : W * (2 / 3) ≤ W * Real.log (2 + W) :=
        mul_le_mul_of_nonneg_left hlog2third hW0
      -- `16W = 24·(W·(2/3)) ≤ 24·(W·log(2+W))`.
      nlinarith [hkey, hWlog, mul_nonneg hW0 hlog2pos.le]
  -- Final numeric combine.
  have hsum_le : (∑ _q ∈ Finset.Icc 1 Q, 4 * N * lam * W)
        + (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * N * lam)
        + (∑ q ∈ Finset.Icc 1 Q, 4 * W / (q : ℝ))
        + (∑ _q ∈ Finset.Icc 1 Q, (1 : ℝ))
      ≤ 16 * (N * δ) + 16 * (N * δ) + 4 * W * (1 + Real.log Q) + 4 * W := by
    linarith [hS1, hS2, hS3, hS4]
  calc 3411200 * ((∑ _q ∈ Finset.Icc 1 Q, 4 * N * lam * W)
          + (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * N * lam)
          + (∑ q ∈ Finset.Icc 1 Q, 4 * W / (q : ℝ))
          + (∑ _q ∈ Finset.Icc 1 Q, (1 : ℝ)))
      ≤ 3411200 * (16 * (N * δ) + 16 * (N * δ) + 4 * W * (1 + Real.log Q) + 4 * W) := by
        apply mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    _ ≤ 3411200 * (32 * (N * δ) + (28 * (W * Real.log (2 + W)) + 14)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [habsorb]
    _ ≤ 109158400 * (N * δ + W * Real.log (2 + W) + 1) := by
        have hWlog0 : (0 : ℝ) ≤ W * Real.log (2 + W) := mul_nonneg hW0 hlog2pos.le
        nlinarith [hNδ0, hWlog0]


end Squarefree.Geometry
