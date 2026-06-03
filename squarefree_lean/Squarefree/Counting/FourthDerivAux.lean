import Squarefree.FiniteDiff
import Squarefree.Counting.Preimage
import Mathlib

/-!
# §2 fourth-derivative counting — calculus helpers (Aux for Lemma 2.1)

The calculus crux of `Squarefree.Counting.fourthDeriv_count` (writeup lines 96–194, step 4):
the third forward difference `g = Δ_{h₁,h₂,h₃} f` has derivative `Δ_{h₁,h₂,h₃} f'`, and the
third forward difference of a `C³` function equals (by iterated mean value theorem)
`h₁h₂h₃` times its third derivative at an interior point.  Combined with `Λ ≤ |f⁗| ≤ 2Λ`,
this makes `g` an `(h₁h₂h₃·Λ)`-expanding map of variation `≤ 2(h₁h₂h₃·Λ)N` on `[N,2N]`,
ready for `preimage_count`.

All helpers are `private`; the only export is `expanding_and_variation`.
-/

open Squarefree.FiniteDiff Set Real

namespace Squarefree.Counting

/-- **Final combine of Lemma 2.1** (writeup 175–186).  The preimage-count product bound
(with variation coefficient `K ≥ 1` carried by the upper bound `|f⁗| ≤ K·Λ`), together with
`P ≤ C·Ñ⁷/M⁷` and `P ≥ 1`, yields the combined inequality fed to `four_case_bound`.  The
budget multiplier picks up a factor `K`. -/
theorem final_combine {M N Λ δ P Ñ K : ℝ}
    (hM : 0 < M) (hN : 1 ≤ N) (hΛ : 0 < Λ) (hδ : 0 < δ) (hδ1 : δ < 1) (hK : 1 ≤ K)
    (hÑpos : 0 < Ñ) (hÑ2N : Ñ ≤ 2 * N) (hP1 : 1 ≤ P)
    (hPbd : P ≤ 8192000 * Ñ ^ 7 / M ^ 7)
    (hub : M ^ 8 ≤ (16 * Ñ) ^ 7 * ((K * (P * Λ) * N + 16 * δ + 1) * (16 * δ / (P * Λ) + 1))) :
    M ^ 8 ≤ (2 ^ 70 * K) * (N ^ 7 + Λ * N ^ 15 / M ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ) := by
  set Q : ℝ := P * Λ with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hM7 : 0 < M ^ 7 := by positivity
  have hNpos : 0 < N := by linarith
  have hδ0 : (0:ℝ) ≤ δ := le_of_lt hδ
  have hK0 : (0:ℝ) ≤ K := by linarith
  -- product expansion ≤ linear bound (uses δ < 1 and K ≥ 1).
  have hprod : (K * Q * N + 16 * δ + 1) * (16 * δ / Q + 1)
      ≤ K * Q * N + 32 * K * N * δ + 272 * δ / Q + 1 := by
    have hexpand : (K * Q * N + 16 * δ + 1) * (16 * δ / Q + 1)
        = K * Q * N + 16 * K * N * δ + 256 * δ ^ 2 / Q + 16 * δ + 16 * δ / Q + 1 := by
      field_simp; ring
    rw [hexpand]
    have hδsq : 256 * δ ^ 2 / Q ≤ 256 * δ / Q := by
      gcongr; nlinarith [hδ1, hδ0]
    have hKN1 : (1:ℝ) ≤ K * N := by nlinarith [hN, hK]
    have h16δ : 16 * δ ≤ 16 * K * N * δ := by nlinarith [hKN1, hδ0]
    -- 32*K*N*δ = 16*K*N*δ + 16*K*N*δ ≥ 16*K*N*δ + 16*δ
    have e272 : K * Q * N + 32 * K * N * δ + 272 * δ / Q + 1
        = K * Q * N + 16 * K * N * δ + 16 * K * N * δ + 256 * δ / Q + 16 * δ / Q + 1 := by
      rw [show (272:ℝ) * δ / Q = 256 * δ / Q + 16 * δ / Q from by ring]; ring
    rw [e272]; linarith [hδsq, h16δ]
  -- (16Ñ)⁷ ≤ 2^35 N⁷
  have hÑ7bd : (16 * Ñ) ^ 7 ≤ 2 ^ 35 * N ^ 7 := by
    have h1 : (16 * Ñ) ^ 7 ≤ (32 * N) ^ 7 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_pow]; norm_num [show (32:ℝ) = 2^5 from by norm_num, ← pow_mul]
  have hÑ7pos : 0 < (16 * Ñ) ^ 7 := by positivity
  have hÑ7nn : (0:ℝ) ≤ (16 * Ñ) ^ 7 := le_of_lt hÑ7pos
  -- bound each of the 4 terms by 2^70·K · (a budget term)
  -- (A) constant: (16Ñ)⁷·1 ≤ 2^70·K·N⁷  (K ≥ 1)
  have hA : (16 * Ñ) ^ 7 * 1 ≤ (2 ^ 70 * K) * N ^ 7 := by
    rw [mul_one]; refine le_trans hÑ7bd ?_
    have hstep : (2:ℝ) ^ 35 * N ^ 7 ≤ 2 ^ 70 * N ^ 7 := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity); norm_num
    refine le_trans hstep ?_
    have : (2:ℝ) ^ 70 * N ^ 7 = 2 ^ 70 * 1 * N ^ 7 := by ring
    rw [this, show (2:ℝ) ^ 70 * K * N ^ 7 = 2 ^ 70 * K * N ^ 7 from rfl]
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    apply mul_le_mul_of_nonneg_left hK (by positivity)
  -- (B) K·QN: (16Ñ)⁷·(K·QN) ≤ 2^70·K·ΛN¹⁵/M⁷
  have hB : (16 * Ñ) ^ 7 * (K * Q * N) ≤ (2 ^ 70 * K) * (Λ * N ^ 15 / M ^ 7) := by
    have hQval : Q ≤ 8192000 * Ñ ^ 7 / M ^ 7 * Λ := by
      rw [hQdef]; apply mul_le_mul_of_nonneg_right hPbd (le_of_lt hΛ)
    -- first the K-free bound (16Ñ)⁷·(QN) ≤ 2^70·ΛN¹⁵/M⁷
    have hBfree : (16 * Ñ) ^ 7 * (Q * N) ≤ 2 ^ 70 * (Λ * N ^ 15 / M ^ 7) := by
      have hstep : (16 * Ñ) ^ 7 * (Q * N)
          ≤ (16 * Ñ) ^ 7 * ((8192000 * Ñ ^ 7 / M ^ 7 * Λ) * N) := by
        apply mul_le_mul_of_nonneg_left ?_ hÑ7nn
        apply mul_le_mul_of_nonneg_right hQval (le_of_lt hNpos)
      refine le_trans hstep ?_
      have hexp : (16 * Ñ) ^ 7 * ((8192000 * Ñ ^ 7 / M ^ 7 * Λ) * N)
          = (16 ^ 7 * 8192000 * (Ñ ^ 14) * (Λ * N)) / M ^ 7 := by
        field_simp
      have hRrw : 2 ^ 70 * (Λ * N ^ 15 / M ^ 7) = (2 ^ 70 * (Λ * N ^ 15)) / M ^ 7 := by ring
      rw [hexp, hRrw, div_le_div_iff_of_pos_right hM7]
      have hÑ14 : Ñ ^ 14 ≤ 2 ^ 14 * N ^ 14 := by
        have : Ñ ^ 14 ≤ (2 * N) ^ 14 := by apply pow_le_pow_left₀ (le_of_lt hÑpos) hÑ2N
        refine le_trans this (le_of_eq ?_); rw [mul_pow]
      have hcoef : (16:ℝ) ^ 7 * 8192000 ≤ 2 ^ 52 := by norm_num
      have hLNnn : (0:ℝ) ≤ Λ * N := by positivity
      calc 16 ^ 7 * 8192000 * Ñ ^ 14 * (Λ * N)
          ≤ 2 ^ 52 * (2 ^ 14 * N ^ 14) * (Λ * N) := by
            apply mul_le_mul_of_nonneg_right ?_ hLNnn
            apply mul_le_mul hcoef hÑ14 (by positivity) (by positivity)
        _ = 2 ^ 66 * (Λ * N ^ 15) := by ring
        _ ≤ 2 ^ 70 * (Λ * N ^ 15) := by
            apply mul_le_mul_of_nonneg_right ?_ (by positivity); norm_num
    -- multiply both sides by K
    have hlhs : (16 * Ñ) ^ 7 * (K * Q * N) = K * ((16 * Ñ) ^ 7 * (Q * N)) := by ring
    have hrhs : (2 ^ 70 * K) * (Λ * N ^ 15 / M ^ 7) = K * (2 ^ 70 * (Λ * N ^ 15 / M ^ 7)) := by
      ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_left hBfree hK0
  -- (C) 32·K·Nδ: (16Ñ)⁷·(32·K·Nδ) ≤ 2^70·K·N⁸δ
  have hC : (16 * Ñ) ^ 7 * (32 * K * N * δ) ≤ (2 ^ 70 * K) * (N ^ 8 * δ) := by
    have hstep : (16 * Ñ) ^ 7 * (32 * K * N * δ) ≤ 2 ^ 35 * N ^ 7 * (32 * K * N * δ) := by
      apply mul_le_mul_of_nonneg_right hÑ7bd (by positivity)
    refine le_trans hstep ?_
    have hrw : 2 ^ 35 * N ^ 7 * (32 * K * N * δ) = (2 ^ 35 * 32 * K) * (N ^ 8 * δ) := by ring
    rw [hrw]
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (2:ℝ) ^ 35 * 32 * K = (2 ^ 35 * 32) * K := by ring
    rw [this, show (2:ℝ) ^ 70 * K = (2 ^ 70) * K from rfl]
    apply mul_le_mul_of_nonneg_right ?_ hK0; norm_num
  -- (D) 272δ/Q ≤ 272δ/Λ (Q ≥ Λ), (16Ñ)⁷·272δ/Λ ≤ 2^70·K·N⁷δ/Λ
  have hQΛ : Λ ≤ Q := by
    rw [hQdef]; calc Λ = 1 * Λ := by ring
      _ ≤ P * Λ := mul_le_mul_of_nonneg_right hP1 (le_of_lt hΛ)
  have hD : (16 * Ñ) ^ 7 * (272 * δ / Q) ≤ (2 ^ 70 * K) * (N ^ 7 * δ / Λ) := by
    have hdq : 272 * δ / Q ≤ 272 * δ / Λ := by
      apply div_le_div_of_nonneg_left (by positivity) hΛ hQΛ
    have hstep : (16 * Ñ) ^ 7 * (272 * δ / Q) ≤ 2 ^ 35 * N ^ 7 * (272 * δ / Λ) := by
      apply mul_le_mul hÑ7bd hdq (by positivity) (by positivity)
    refine le_trans hstep ?_
    have hrw : 2 ^ 35 * N ^ 7 * (272 * δ / Λ) = (2 ^ 35 * 272) * (N ^ 7 * δ / Λ) := by
      rw [mul_div_assoc]; ring
    rw [hrw]
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [show (2:ℝ) ^ 70 * K = (2 ^ 70) * K from rfl]
    calc (2:ℝ) ^ 35 * 272 ≤ 2 ^ 70 := by norm_num
      _ = 2 ^ 70 * 1 := by ring
      _ ≤ 2 ^ 70 * K := by apply mul_le_mul_of_nonneg_left hK (by positivity)
  -- combine
  have hfin : (16 * Ñ) ^ 7 * (K * Q * N + 32 * K * N * δ + 272 * δ / Q + 1)
      ≤ (2 ^ 70 * K) * (N ^ 7 + Λ * N ^ 15 / M ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ) := by
    have hexpand : (16 * Ñ) ^ 7 * (K * Q * N + 32 * K * N * δ + 272 * δ / Q + 1)
        = (16 * Ñ) ^ 7 * (K * Q * N) + (16 * Ñ) ^ 7 * (32 * K * N * δ)
          + (16 * Ñ) ^ 7 * (272 * δ / Q) + (16 * Ñ) ^ 7 * 1 := by ring
    rw [hexpand]
    have hRexpand : (2 ^ 70 * K) * (N ^ 7 + Λ * N ^ 15 / M ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ)
        = (2 ^ 70 * K) * (Λ * N ^ 15 / M ^ 7) + (2 ^ 70 * K) * (N ^ 8 * δ)
          + (2 ^ 70 * K) * (N ^ 7 * δ / Λ) + (2 ^ 70 * K) * N ^ 7 := by ring
    rw [hRexpand]
    exact add_le_add (add_le_add (add_le_add hB hC) hD) hA
  refine le_trans hub ?_
  refine le_trans ?_ hfin
  apply mul_le_mul_of_nonneg_left hprod hÑ7nn

/-- `M^k ≤ B ⇒ M ≤ B^(1/k)` (nonnegative reals, `k ≠ 0`). -/
private theorem root_bound {M B : ℝ} {k : ℕ} (hM : 0 ≤ M) (_hB : 0 ≤ B) (hk : k ≠ 0)
    (h : M ^ k ≤ B) : M ≤ B ^ ((k : ℝ)⁻¹) := by
  have hMk : (0:ℝ) ≤ M ^ k := by positivity
  calc M = (M ^ k) ^ ((k:ℝ)⁻¹) := (pow_rpow_inv_natCast hM hk).symm
    _ ≤ B ^ ((k:ℝ)⁻¹) := Real.rpow_le_rpow hMk h (by positivity)

/-- **Four-case arithmetic of Lemma 2.1** (writeup 180–193).  The combined bound
`M⁸ ≤ K(N⁷ + ΛN¹⁵/M⁷ + N⁸δ + N⁷δ/Λ)` gives the four-term estimate on `M`. -/
theorem four_case_bound (K : ℝ) (hK : 1 ≤ K) :
    ∀ M N Λ δ : ℝ, 0 < M → 1 ≤ N → 0 < Λ → 0 < δ →
      M ^ 8 ≤ K * (N ^ 7 + Λ * N ^ 15 / M ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ) →
      M ≤ ((4*K) ^ (1/8 : ℝ) + (4*K) ^ (1/15 : ℝ)) *
          (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
             + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
  intro M N Λ δ hM hN hΛ hδ hbound
  have hM7 : (0:ℝ) < M ^ 7 := by positivity
  have hNpos : (0:ℝ) < N := by linarith
  have hK0 : (0:ℝ) < 4 * K := by linarith
  have w0 : (0:ℝ) ≤ N ^ 7 := by positivity
  have x0 : (0:ℝ) ≤ Λ * N ^ 15 / M ^ 7 := by positivity
  have y0 : (0:ℝ) ≤ N ^ 8 * δ := by positivity
  have z0 : (0:ℝ) ≤ N ^ 7 * δ / Λ := by positivity
  set w := N ^ 7
  set x := Λ * N ^ 15 / M ^ 7
  set y := N ^ 8 * δ
  set z := N ^ 7 * δ / Λ
  have four : M ^ 8 ≤ 4 * K * w ∨ M ^ 8 ≤ 4 * K * x ∨ M ^ 8 ≤ 4 * K * y ∨ M ^ 8 ≤ 4 * K * z := by
    by_contra h
    push_neg at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    nlinarith [hbound]
  have t1 : (0:ℝ) ≤ N ^ (7/8 : ℝ) := by positivity
  have t2 : (0:ℝ) ≤ N * δ ^ (1/8 : ℝ) := by positivity
  have t3 : (0:ℝ) ≤ N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) := by positivity
  have t4 : (0:ℝ) ≤ Λ ^ (1/15 : ℝ) * N := by positivity
  have hc8 : (0:ℝ) ≤ (4*K) ^ (1/8 : ℝ) := by positivity
  have hc15 : (0:ℝ) ≤ (4*K) ^ (1/15 : ℝ) := by positivity
  set C := (4*K) ^ (1/8 : ℝ) + (4*K) ^ (1/15 : ℝ) with hC
  have hCpos : 0 < C := by positivity
  rcases four with hcase | hcase | hcase | hcase
  · have hb := root_bound (le_of_lt hM) (by positivity) (k := 8) (by norm_num)
      (show M ^ 8 ≤ 4 * K * N ^ 7 from hcase)
    rw [show (((8:ℕ):ℝ)⁻¹) = (1/8 : ℝ) by norm_num] at hb
    have heq : (4 * K * N ^ 7) ^ (1/8 : ℝ) = (4*K) ^ (1/8 : ℝ) * N ^ (7/8 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hN78 : (N ^ 7) ^ (1/8 : ℝ) = N ^ (7/8 : ℝ) := by
        rw [← Real.rpow_natCast N 7, ← Real.rpow_mul (le_of_lt hNpos)]; norm_num
      rw [hN78]
    rw [heq] at hb
    calc M ≤ (4*K) ^ (1/8 : ℝ) * N ^ (7/8 : ℝ) := hb
      _ ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
            + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
          have h1 : (4*K) ^ (1/8 : ℝ) ≤ C := by rw [hC]; linarith
          refine le_trans (mul_le_mul_of_nonneg_right h1 t1) ?_
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos); nlinarith [t2, t3, t4, t1]
  · have hclear : M ^ 15 ≤ 4 * K * Λ * N ^ 15 := by
      have : M ^ 8 * M ^ 7 ≤ 4 * K * (Λ * N ^ 15 / M ^ 7) * M ^ 7 :=
        mul_le_mul_of_nonneg_right hcase (le_of_lt hM7)
      have hrw : 4 * K * (Λ * N ^ 15 / M ^ 7) * M ^ 7 = 4 * K * Λ * N ^ 15 := by field_simp
      have hrw2 : M ^ 8 * M ^ 7 = M ^ 15 := by ring
      rw [hrw, hrw2] at this; exact this
    have hb := root_bound (le_of_lt hM) (by positivity) (k := 15) (by norm_num) hclear
    rw [show (((15:ℕ):ℝ)⁻¹) = (1/15 : ℝ) by norm_num] at hb
    have heq : (4 * K * Λ * N ^ 15) ^ (1/15 : ℝ)
        = (4*K) ^ (1/15 : ℝ) * (Λ ^ (1/15 : ℝ) * N) := by
      rw [show 4 * K * Λ * N ^ 15 = (4 * K) * (Λ * N ^ 15) by ring,
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt hΛ) (by positivity)]
      have hN15 : (N ^ 15) ^ (1/15 : ℝ) = N := by
        rw [← Real.rpow_natCast N 15, ← Real.rpow_mul (le_of_lt hNpos)]; norm_num
      rw [hN15]
    rw [heq] at hb
    calc M ≤ (4*K) ^ (1/15 : ℝ) * (Λ ^ (1/15 : ℝ) * N) := hb
      _ ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
            + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
          have h1 : (4*K) ^ (1/15 : ℝ) ≤ C := by rw [hC]; linarith
          refine le_trans (mul_le_mul_of_nonneg_right h1 t4) ?_
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos); nlinarith [t1, t2, t3, t4]
  · have hb := root_bound (le_of_lt hM) (by positivity) (k := 8) (by norm_num)
      (show M ^ 8 ≤ 4 * K * (N ^ 8 * δ) from hcase)
    rw [show (((8:ℕ):ℝ)⁻¹) = (1/8 : ℝ) by norm_num] at hb
    have heq : (4 * K * (N ^ 8 * δ)) ^ (1/8 : ℝ)
        = (4*K) ^ (1/8 : ℝ) * (N * δ ^ (1/8 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (le_of_lt hδ)]
      have hN8 : (N ^ 8) ^ (1/8 : ℝ) = N := by
        rw [← Real.rpow_natCast N 8, ← Real.rpow_mul (le_of_lt hNpos)]; norm_num
      rw [hN8]
    rw [heq] at hb
    calc M ≤ (4*K) ^ (1/8 : ℝ) * (N * δ ^ (1/8 : ℝ)) := hb
      _ ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
            + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
          have h1 : (4*K) ^ (1/8 : ℝ) ≤ C := by rw [hC]; linarith
          refine le_trans (mul_le_mul_of_nonneg_right h1 t2) ?_
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos); nlinarith [t1, t2, t3, t4]
  · have hb := root_bound (le_of_lt hM) (by positivity) (k := 8) (by norm_num)
      (show M ^ 8 ≤ 4 * K * (N ^ 7 * δ / Λ) from hcase)
    rw [show (((8:ℕ):ℝ)⁻¹) = (1/8 : ℝ) by norm_num] at hb
    have heq : (4 * K * (N ^ 7 * δ / Λ)) ^ (1/8 : ℝ)
        = (4*K) ^ (1/8 : ℝ) * (N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ)) := by
      rw [show 4 * K * (N ^ 7 * δ / Λ) = (4 * K) * (N ^ 7 * (δ / Λ)) by ring,
        Real.mul_rpow (x := 4*K) (y := N ^ 7 * (δ / Λ)) (by positivity) (by positivity),
        Real.mul_rpow (x := N ^ 7) (y := δ / Λ) (by positivity) (by positivity)]
      have hN78 : (N ^ 7) ^ (1/8 : ℝ) = N ^ (7/8 : ℝ) := by
        rw [← Real.rpow_natCast N 7, ← Real.rpow_mul (le_of_lt hNpos)]; norm_num
      rw [hN78]
    rw [heq] at hb
    calc M ≤ (4*K) ^ (1/8 : ℝ) * (N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ)) := hb
      _ ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
            + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
          have h1 : (4*K) ^ (1/8 : ℝ) ≤ C := by rw [hC]; linarith
          refine le_trans (mul_le_mul_of_nonneg_right h1 t3) ?_
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos); nlinarith [t1, t2, t3, t4]

/-- `‖a+b‖ ≤ ‖a‖ + ‖b‖` for distance-to-integer. -/
private theorem distInt_add_le (a b : ℝ) : distInt (a + b) ≤ distInt a + distInt b := by
  have h := round_le (a + b) (round a + round b)
  simp only [distInt]
  refine le_trans h ?_
  have e : (a + b) - ((round a + round b : ℤ) : ℝ) = (a - round a) + (b - round b) := by
    push_cast; ring
  rw [e]; exact abs_add_le _ _

/-- `‖a-b‖ ≤ ‖a‖ + ‖b‖` for distance-to-integer. -/
private theorem distInt_sub_le (a b : ℝ) : distInt (a - b) ≤ distInt a + distInt b := by
  have h := round_le (a - b) (round a - round b)
  simp only [distInt]
  refine le_trans h ?_
  have e : (a - b) - ((round a - round b : ℤ) : ℝ) = (a - round a) - (b - round b) := by
    push_cast; ring
  rw [e]; exact abs_sub _ _

/-- If all 8 corners of `f` are within `δ` of `ℤ`, the third difference is within `8δ`. -/
theorem distInt_diff3_le {f : ℝ → ℝ} {n h₁ h₂ h₃ δ : ℝ}
    (c000 : distInt (f n) ≤ δ) (c001 : distInt (f (n + h₃)) ≤ δ)
    (c010 : distInt (f (n + h₂)) ≤ δ) (c011 : distInt (f (n + h₂ + h₃)) ≤ δ)
    (c100 : distInt (f (n + h₁)) ≤ δ) (c101 : distInt (f (n + h₁ + h₃)) ≤ δ)
    (c110 : distInt (f (n + h₁ + h₂)) ≤ δ) (c111 : distInt (f (n + h₁ + h₂ + h₃)) ≤ δ) :
    distInt (diff3 h₁ h₂ h₃ f n) ≤ 8 * δ := by
  have hexp : diff3 h₁ h₂ h₃ f n =
      f (n + h₁ + h₂ + h₃) - f (n + h₁ + h₂) - f (n + h₁ + h₃) + f (n + h₁)
      - f (n + h₂ + h₃) + f (n + h₂) + f (n + h₃) - f n := by
    simp only [diff3, diff1]; ring_nf
  rw [hexp]
  have step :=
    (distInt_sub_le _ (f n)).trans <|
      add_le_add
        ((distInt_add_le _ (f (n + h₃))).trans <|
          add_le_add
            ((distInt_add_le _ (f (n + h₂))).trans <|
              add_le_add
                ((distInt_sub_le _ (f (n + h₂ + h₃))).trans <|
                  add_le_add
                    ((distInt_add_le _ (f (n + h₁))).trans <|
                      add_le_add
                        ((distInt_sub_le _ (f (n + h₁ + h₃))).trans <|
                          add_le_add
                            ((distInt_sub_le _ (f (n + h₁ + h₂))).trans <|
                              add_le_add c111 c110)
                            c101)
                        c100)
                    c011)
                c010)
            c001)
        c000
  calc distInt (f (n + h₁ + h₂ + h₃) - f (n + h₁ + h₂) - f (n + h₁ + h₃) + f (n + h₁)
        - f (n + h₂ + h₃) + f (n + h₂) + f (n + h₃) - f n)
      ≤ δ + δ + δ + δ + δ + δ + δ + δ := step
    _ = 8 * δ := by ring

/-- Derivative of a first forward difference is the first forward difference of the derivative. -/
private theorem hasDerivAt_diff1 {ψ ψ' : ℝ → ℝ} {h x : ℝ}
    (hx : HasDerivAt ψ (ψ' x) x) (hxh : HasDerivAt ψ (ψ' (x + h)) (x + h)) :
    HasDerivAt (diff1 h ψ) (diff1 h ψ' x) x := by
  simp only [diff1]
  have h1 : HasDerivAt (fun y => ψ (y + h)) (ψ' (x + h)) x := by
    have := hxh.comp x (hasDerivAt_id x |>.add_const h)
    simpa using this
  exact h1.sub hx

/-- Single-step mean value form: `Δ_h ψ (ξ) = h · ψ'(c)` for some `c ∈ (ξ, ξ+h)`. -/
private theorem diff1_mvt {ψ ψ' : ℝ → ℝ} {ξ h : ℝ} (hh : 0 < h)
    (hd : ∀ t ∈ Icc ξ (ξ + h), HasDerivAt ψ (ψ' t) t) :
    ∃ c ∈ Ioo ξ (ξ + h), diff1 h ψ ξ = h * ψ' c := by
  have hab : ξ < ξ + h := by linarith
  have hcont : ContinuousOn ψ (Icc ξ (ξ + h)) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt (s := Icc ξ (ξ + h))
  have hderiv : ∀ t ∈ Ioo ξ (ξ + h), HasDerivAt ψ (ψ' t) t :=
    fun t ht => hd t (Ioo_subset_Icc_self ht)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' hab hcont hderiv
  refine ⟨c, hc, ?_⟩
  simp only [diff1]; rw [hslope]
  have : ξ + h - ξ = h := by ring
  rw [this]; field_simp

/-- **Iterated mean value form of the third difference.**  Given a chain `fᵢ' = fᵢ₊₁` on
`Icc ξ s` (with `ξ + h₁ + h₂ + h₃ ≤ s`), the third forward difference of `f₁` equals
`h₁h₂h₃ · f₄(ζ)` for some `ζ ∈ Icc ξ s`. -/
private theorem diff3_eq_mul {f₁ f₂ f₃ f₄ : ℝ → ℝ} {ξ h₁ h₂ h₃ s : ℝ}
    (h1 : 0 < h₁) (h2 : 0 < h₂) (h3 : 0 < h₃)
    (hs : ξ + h₁ + h₂ + h₃ ≤ s)
    (hd1 : ∀ t ∈ Icc ξ s, HasDerivAt f₁ (f₂ t) t)
    (hd2 : ∀ t ∈ Icc ξ s, HasDerivAt f₂ (f₃ t) t)
    (hd3 : ∀ t ∈ Icc ξ s, HasDerivAt f₃ (f₄ t) t) :
    ∃ ζ ∈ Icc ξ s, diff3 h₁ h₂ h₃ f₁ ξ = (h₁ * h₂ * h₃) * f₄ ζ := by
  set Φ₁ : ℝ → ℝ := diff1 h₂ (diff1 h₃ f₁) with hΦ₁
  set Φ₁' : ℝ → ℝ := diff1 h₂ (diff1 h₃ f₂) with hΦ₁'
  have hderivΦ₁ : ∀ t ∈ Icc ξ (ξ + h₁), HasDerivAt Φ₁ (Φ₁' t) t := by
    intro t ht
    rw [hΦ₁, hΦ₁']
    have key : ∀ u, ξ ≤ u → u + h₃ ≤ s →
        HasDerivAt (diff1 h₃ f₁) (diff1 h₃ f₂ u) u := by
      intro u hu1 hu2
      exact hasDerivAt_diff1 (hd1 u ⟨hu1, by linarith⟩) (hd1 (u + h₃) ⟨by linarith, by linarith⟩)
    obtain ⟨ht1, ht2⟩ := ht
    exact hasDerivAt_diff1 (key t ht1 (by linarith)) (key (t + h₂) (by linarith) (by linarith))
  obtain ⟨c₁, hc₁, e₁⟩ := diff1_mvt h1 hderivΦ₁
  have step1 : diff3 h₁ h₂ h₃ f₁ ξ = h₁ * Φ₁' c₁ := by
    rw [show diff3 h₁ h₂ h₃ f₁ = diff1 h₁ Φ₁ from rfl]; exact e₁
  have hderivΨ : ∀ t ∈ Icc c₁ (c₁ + h₂), HasDerivAt (diff1 h₃ f₂) (diff1 h₃ f₃ t) t := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hc₁ub : c₁ ≤ ξ + h₁ := le_of_lt hc₁.2
    exact hasDerivAt_diff1 (hd2 t ⟨by linarith [hc₁.1], by linarith⟩)
      (hd2 (t + h₃) ⟨by linarith [hc₁.1], by linarith⟩)
  obtain ⟨c₂, hc₂, e₂⟩ := diff1_mvt h2 hderivΨ
  have step2 : Φ₁' c₁ = h₂ * (diff1 h₃ f₃) c₂ := by rw [hΦ₁']; exact e₂
  have hderivf₃ : ∀ t ∈ Icc c₂ (c₂ + h₃), HasDerivAt f₃ (f₄ t) t := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hb₂ : c₂ ≤ c₁ + h₂ := le_of_lt hc₂.2
    have hb₁ : c₁ ≤ ξ + h₁ := le_of_lt hc₁.2
    exact hd3 t ⟨by linarith [hc₁.1, hc₂.1], by linarith⟩
  obtain ⟨c₃, hc₃, e₃⟩ := diff1_mvt h3 hderivf₃
  refine ⟨c₃, ⟨by linarith [hc₁.1, hc₂.1, hc₃.1], ?_⟩, ?_⟩
  · have a3 : c₃ < c₂ + h₃ := hc₃.2
    have a2 : c₂ < c₁ + h₂ := hc₂.2
    have a1 : c₁ < ξ + h₁ := hc₁.2
    linarith
  · rw [step1, step2, e₃]; ring

/-- From `ContDiffOn ℝ 4 f` on an open interval, `iteratedDeriv k f` differentiates to
`iteratedDeriv (k+1) f` at every interior point, for `k ≤ 3`. -/
private theorem hasDerivAt_iteratedDeriv_of_contDiffOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiffOn ℝ 4 f (Ioo a b)) {k : ℕ} (hk : k < 4) :
    ∀ x ∈ Ioo a b, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hopen : IsOpen (Ioo a b) := isOpen_Ioo
  intro x hx
  have hdw : DifferentiableOn ℝ (iteratedDerivWithin k f (Ioo a b)) (Ioo a b) :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) hopen.uniqueDiffOn
  have heq : EqOn (iteratedDerivWithin k f (Ioo a b)) (iteratedDeriv k f) (Ioo a b) :=
    fun y hy => iteratedDerivWithin_of_isOpen hopen hy
  have hdiffAt : DifferentiableAt ℝ (iteratedDeriv k f) x :=
    ((hdw x hx).differentiableAt (hopen.mem_nhds hx)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) heq.symm)
  rw [iteratedDeriv_succ]
  exact hdiffAt.hasDerivAt

/-- Derivative of the third forward difference is the third forward difference of the
derivative. -/
private theorem hasDerivAt_diff3 {f₀ f₁ : ℝ → ℝ} {h₁ h₂ h₃ x : ℝ}
    (h1 : 0 ≤ h₁) (h2 : 0 ≤ h₂) (h3 : 0 ≤ h₃)
    (hd : ∀ t ∈ Icc x (x + h₁ + h₂ + h₃), HasDerivAt f₀ (f₁ t) t) :
    HasDerivAt (diff3 h₁ h₂ h₃ f₀) (diff3 h₁ h₂ h₃ f₁ x) x := by
  have d3 : ∀ u, x ≤ u → u + h₃ ≤ x + h₁ + h₂ + h₃ →
      HasDerivAt (diff1 h₃ f₀) (diff1 h₃ f₁ u) u := by
    intro u hu1 hu2
    exact hasDerivAt_diff1 (hd u ⟨hu1, by linarith⟩) (hd (u + h₃) ⟨by linarith, by linarith⟩)
  have d2 : ∀ u, x ≤ u → u + h₂ ≤ x + h₁ + h₂ →
      HasDerivAt (diff1 h₂ (diff1 h₃ f₀)) (diff1 h₂ (diff1 h₃ f₁) u) u := by
    intro u hu1 hu2
    exact hasDerivAt_diff1 (d3 u hu1 (by linarith)) (d3 (u + h₂) (by linarith) (by linarith))
  exact hasDerivAt_diff1 (d2 x le_rfl (by linarith)) (d2 (x + h₁) (by linarith) (by linarith))

/-- **Calculus crux of Lemma 2.1.**  With `1 ≤ hᵢ`, `h₁+h₂+h₃ ≤ N`, `f` of class `C⁴` on the
open interval `(0, 4N)`, `1 ≤ K` and `Λ ≤ |f⁗| ≤ K·Λ` on `[N,3N]`, the third forward
difference `g = Δ_{h₁,h₂,h₃} f` is `(h₁h₂h₃·Λ)`-expanding on `[N,2N]` with total variation
`≤ K·(h₁h₂h₃·Λ)·N`. -/
theorem expanding_and_variation
    {N Λ K h₁ h₂ h₃ : ℝ} {f : ℝ → ℝ}
    (_hN : 2 ≤ N) (hΛ : 0 < Λ) (_hK : 1 ≤ K)
    (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hh3 : 1 ≤ h₃) (hsum : h₁ + h₂ + h₃ ≤ N)
    (hf : ContDiffOn ℝ 4 f (Ioo 0 (4 * N)))
    (hlb : ∀ x ∈ Icc N (3 * N), Λ ≤ |iteratedDeriv 4 f x|)
    (hub : ∀ x ∈ Icc N (3 * N), |iteratedDeriv 4 f x| ≤ K * Λ) :
    (∀ x ∈ Icc N (2 * N), ∀ y ∈ Icc N (2 * N),
        (h₁ * h₂ * h₃ * Λ) * |x - y| ≤ |diff3 h₁ h₂ h₃ f x - diff3 h₁ h₂ h₃ f y|) ∧
    (∀ x ∈ Icc N (2 * N), ∀ y ∈ Icc N (2 * N),
        |diff3 h₁ h₂ h₃ f x - diff3 h₁ h₂ h₃ f y| ≤ K * (h₁ * h₂ * h₃ * Λ) * N) := by
  have h1pos : (0:ℝ) < h₁ := by linarith
  have h2pos : (0:ℝ) < h₂ := by linarith
  have h3pos : (0:ℝ) < h₃ := by linarith
  have hNpos : (0:ℝ) < N := by linarith
  have hP : (0:ℝ) < h₁ * h₂ * h₃ := by positivity
  set g := diff3 h₁ h₂ h₃ f with hg
  set g' := fun ξ => diff3 h₁ h₂ h₃ (iteratedDeriv 1 f) ξ with hg'
  -- `f = iteratedDeriv 0 f`, so `g` differentiates to `g'` at interior points of `(N, 2N)`.
  -- We package the "slope bound" first, then derive both conclusions.
  -- For x ≠ y in [N,2N], the slope of g is P·f⁗(ζ) for some ζ ∈ [N,3N].
  -- Key sub-claim: pointwise derivative of g on (0, 4N - (h₁+h₂+h₃)).
  have hf0 : ∀ t ∈ Ioo (0:ℝ) (4 * N), HasDerivAt f (iteratedDeriv 1 f t) t := by
    intro t ht
    have := hasDerivAt_iteratedDeriv_of_contDiffOn hf (k := 0) (by norm_num) t ht
    simpa [iteratedDeriv_zero] using this
  have hf1 : ∀ t ∈ Ioo (0:ℝ) (4 * N), HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f t) t :=
    fun t ht => hasDerivAt_iteratedDeriv_of_contDiffOn hf (k := 1) (by norm_num) t ht
  have hf2 : ∀ t ∈ Ioo (0:ℝ) (4 * N), HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t :=
    fun t ht => hasDerivAt_iteratedDeriv_of_contDiffOn hf (k := 2) (by norm_num) t ht
  have hf3 : ∀ t ∈ Ioo (0:ℝ) (4 * N), HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    fun t ht => hasDerivAt_iteratedDeriv_of_contDiffOn hf (k := 3) (by norm_num) t ht
  -- The crucial slope inequality, packaged for both conclusions.
  have key : ∀ x ∈ Icc N (2 * N), ∀ y ∈ Icc N (2 * N), y < x →
      ∃ ζ ∈ Icc N (3 * N), g x - g y = (h₁ * h₂ * h₃) * iteratedDeriv 4 f ζ * (x - y) := by
    intro x hx y hy hyx
    obtain ⟨hxlo, hxhi⟩ := hx
    obtain ⟨hylo, hyhi⟩ := hy
    -- g has derivative g' on (y, x) ⊆ (N, 2N) ⊆ (0, 4N).
    have hsub : Ioo y x ⊆ Ioo (0:ℝ) (4 * N) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hgderiv : ∀ t ∈ Ioo y x, HasDerivAt g (g' t) t := by
      intro t ht
      have htmem : t ∈ Ioo (0:ℝ) (4 * N) := hsub ht
      apply hasDerivAt_diff3 (le_of_lt h1pos) (le_of_lt h2pos) (le_of_lt h3pos)
      intro u hu
      -- u ∈ [t, t + h₁+h₂+h₃]; t > y ≥ N > 0 and t + sum ≤ x + N ≤ 3N < 4N
      have hulo : (0:ℝ) < u := by
        have : N ≤ t := le_of_lt (lt_of_le_of_lt hylo ht.1)
        linarith [hu.1]
      have huhi : u < 4 * N := by
        have : t < x := ht.2
        have hu2 : u ≤ t + h₁ + h₂ + h₃ := hu.2
        linarith
      exact hf0 u ⟨hulo, huhi⟩
    have hcont : ContinuousOn g (Icc y x) := by
      intro t ht
      obtain ⟨htlo, hthi⟩ := ht
      have hderiv_t : HasDerivAt g (g' t) t := by
        apply hasDerivAt_diff3 (le_of_lt h1pos) (le_of_lt h2pos) (le_of_lt h3pos)
        intro u hu
        have hulo : (0:ℝ) < u := by linarith [hu.1, hylo]
        have huhi : u < 4 * N := by
          have hu2 : u ≤ t + h₁ + h₂ + h₃ := hu.2
          linarith [hxhi]
        exact hf0 u ⟨hulo, huhi⟩
      exact hderiv_t.continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g g' hyx hcont hgderiv
    -- now express g' ξ = diff3 of f' = P·f⁗(ζ)
    have hξmem : ξ ∈ Ioo (0:ℝ) (4 * N) := hsub hξ
    -- apply diff3_eq_mul to f₁ = f', with s = ξ + h₁+h₂+h₃
    have hξx : ξ < x := hξ.2
    have hdchain1 : ∀ t ∈ Icc ξ (ξ + h₁ + h₂ + h₃),
        HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f t) t := by
      intro t ht
      have h0 : (0:ℝ) < t := by linarith [ht.1, hξmem.1]
      have h4 : t < 4 * N := by have ht2 := ht.2; linarith
      exact hf1 t ⟨h0, h4⟩
    have hdchain2 : ∀ t ∈ Icc ξ (ξ + h₁ + h₂ + h₃),
        HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t := by
      intro t ht
      have h0 : (0:ℝ) < t := by linarith [ht.1, hξmem.1]
      have h4 : t < 4 * N := by have ht2 := ht.2; linarith
      exact hf2 t ⟨h0, h4⟩
    have hdchain3 : ∀ t ∈ Icc ξ (ξ + h₁ + h₂ + h₃),
        HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t := by
      intro t ht
      have h0 : (0:ℝ) < t := by linarith [ht.1, hξmem.1]
      have h4 : t < 4 * N := by have ht2 := ht.2; linarith
      exact hf3 t ⟨h0, h4⟩
    obtain ⟨ζ, hζ, hζeq⟩ := diff3_eq_mul h1pos h2pos h3pos (le_refl (ξ + h₁ + h₂ + h₃))
      hdchain1 hdchain2 hdchain3
    -- ζ ∈ [ξ, ξ+h₁+h₂+h₃] ⊆ [N, 3N]
    have hζN : ζ ∈ Icc N (3 * N) := by
      refine ⟨?_, ?_⟩
      · have : N ≤ ξ := le_of_lt (lt_of_le_of_lt hylo hξ.1)
        linarith [hζ.1]
      · have hξx : ξ < x := hξ.2
        have : ζ ≤ ξ + h₁ + h₂ + h₃ := hζ.2
        linarith [hxhi]
    refine ⟨ζ, hζN, ?_⟩
    -- g x - g y = g' ξ * (x - y), and g' ξ = diff3 h₁h₂h₃ (f') ξ = P·f⁗(ζ)
    have hxyne : x - y ≠ 0 := by linarith
    have hgx : g x - g y = g' ξ * (x - y) := by
      rw [hslope]; field_simp
    have hg'ξ : g' ξ = (h₁ * h₂ * h₃) * iteratedDeriv 4 f ζ := hζeq
    rw [hgx, hg'ξ]
  -- Now derive both conclusions from `key`.
  -- helper: turn `key` into an absolute-value identity for arbitrary `x,y`.
  have keyabs : ∀ x ∈ Icc N (2 * N), ∀ y ∈ Icc N (2 * N),
      ∃ ζ ∈ Icc N (3 * N),
        |diff3 h₁ h₂ h₃ f x - diff3 h₁ h₂ h₃ f y|
          = (h₁ * h₂ * h₃) * |iteratedDeriv 4 f ζ| * |x - y| := by
    intro x hx y hy
    rcases lt_trichotomy y x with hyx | hyx | hyx
    · obtain ⟨ζ, hζ, heq⟩ := key x hx y hy hyx
      exact ⟨ζ, hζ, by rw [hg] at heq; rw [heq, abs_mul, abs_mul, abs_of_pos hP]⟩
    · refine ⟨N, ?_, ?_⟩
      · exact ⟨le_rfl, by linarith⟩
      · subst hyx; simp
    · obtain ⟨ζ, hζ, heq⟩ := key y hy x hx hyx
      refine ⟨ζ, hζ, ?_⟩
      have heq' : diff3 h₁ h₂ h₃ f x - diff3 h₁ h₂ h₃ f y
          = (h₁ * h₂ * h₃) * iteratedDeriv 4 f ζ * (x - y) := by
        rw [hg] at heq; linarith [heq]
      rw [heq', abs_mul, abs_mul, abs_of_pos hP]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨ζ, hζ, heq⟩ := keyabs x hx y hy
    rw [heq]
    have hf4lb : Λ ≤ |iteratedDeriv 4 f ζ| := hlb ζ hζ
    have habsxy : (0:ℝ) ≤ |x - y| := abs_nonneg _
    nlinarith [mul_pos (mul_pos h1pos h2pos) h3pos, hf4lb, habsxy,
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt h1pos) (le_of_lt h2pos)) (le_of_lt h3pos)) habsxy]
  · intro x hx y hy
    have hxy_le : |x - y| ≤ N := by
      obtain ⟨hxlo, hxhi⟩ := hx; obtain ⟨hylo, hyhi⟩ := hy
      rw [abs_le]; constructor <;> linarith
    obtain ⟨ζ, hζ, heq⟩ := keyabs x hx y hy
    rw [heq]
    have hf4ub : |iteratedDeriv 4 f ζ| ≤ K * Λ := hub ζ hζ
    have habsxy : (0:ℝ) ≤ |x - y| := abs_nonneg _
    have hP' : (0:ℝ) ≤ h₁ * h₂ * h₃ := le_of_lt hP
    have hNnn : (0:ℝ) ≤ N := by linarith
    have hKΛnn : (0:ℝ) ≤ K * Λ := by positivity
    calc h₁ * h₂ * h₃ * |iteratedDeriv 4 f ζ| * |x - y|
        ≤ h₁ * h₂ * h₃ * (K * Λ) * N := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hf4ub hP') hxy_le habsxy
          positivity
      _ = K * (h₁ * h₂ * h₃ * Λ) * N := by ring

end Squarefree.Counting
