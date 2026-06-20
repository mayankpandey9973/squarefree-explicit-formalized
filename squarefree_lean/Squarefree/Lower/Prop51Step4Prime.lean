import Squarefree.Lower.Step4Sum
import Squarefree.Lower.DefectScales

/-!
# §5 Step-4 per-pair s-sum assembly — FAITHFUL (sharp `1/√n` band, writeup 1085–1156)

This module derives the §5 Step-4 analytic s-sum (writeup 1085–1156) in its **writeup-sharp** form.

## The fix vs. the premature `+√n` form

The faithful per-`s`-fibre weight pairs the **BARE** smooth count `Rδ = (H/Δ²)G⁵U¹⁵/Ω²` (writeup
1120) with the **SHARP** near-integer band v-count `(1 + ev/√n)`, where `ev = err·ΔΩ/√L` and
`N_s − 1 ≍ ev/√n` (writeup 1124).  The dominant s-sum is therefore `Σ_{n≤N}(ev/√n)·Rδ`, controlled
by `Σ_{n≤N} n^{−1/2} ≤ 2√N ≍ S^{1/2}` (writeup 1126).  The earlier `weight4'` instead paired the
crude `(1 + vc√n)` count (`∝ +√n`) with the smoothed coefficients `Rδ·err`, summing `Σ n^{+1/2} ≍
S^{3/2}` — an over-count of exactly `S = G⁵U³⁵/Ω⁸ = G·U⁵`, i.e. the conclusion was `U⁵` too big.

Both forms have the SAME dominant coefficient `Rδ·err·vc`; only the n-power of the dominant term
(and hence the s-sum) differs.  The sharp form lands on the writeup monomials (U-exponents 75/90).
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 400000

/-- The TRUE-ℓ Step-4 s-sum integrand, **FAITHFUL form** (writeup 1090–1126): the BARE smooth count
`b = Rδ = (H/Δ²)G⁵U¹⁵/Ω²` (n-free) times the SHARP near-integer band v-count `(1 + ev/√n)` plus the
`δ/(T/R)` correction `dc/√n` in the count factor.  Concretely `(1 + ev/√n)·(b + dc/√n)`, where
`ev = err·vc = err·ΔΩ/√L` is the band coefficient (`N_s − 1 ≍ ev/√n`, writeup 1124) and
`dc = (G⁴U¹⁵/Ω⁴)√L`.

The n-dependence of the v-count is `+1/√n` (NOT `+√n`): the dominant s-sum is `Σ (ev/√n)·b ≍ b·ev·S^{1/2}`
(`Σ_{n≤N} n^{−1/2} ≤ 2√N`, writeup 1126), an honest factor `S = GU⁵` below the premature `+√n` form. -/
noncomputable def weight4' (b ev dc : ℝ) (n : ℝ) : ℝ :=
  (1 + ev / Real.sqrt n) * (b + dc / Real.sqrt n)

/-- **§5 Step-4 per-pair s-sum collapse (FAITHFUL, sharp `1/√n` band).**  The bare-`Rδ` × sharp-band
s-sum, with the ℓ-data kept TRUE through the sum and collapsed `ℓ ≤ W` only *afterwards*, is
`≤ 16·C·(H/Δ)·(t6' + t7')` with the SHARP monomials `t6' = G¹⁵U⁷⁵/(ΔΩ¹³)`, `t7' = Δ²G¹⁵U⁹⁰/(HΩ²⁷)`.

The absolute constant `C ≥ 1` on the s-cap `N ≤ C·ℓ₁²·L·U¹⁰/Ω⁸` enters only as `C` (the `1/√n` sum
contributes `√C ≤ C`) and folds into the leading constant `16·C`.

The TRUE-ℓ coefficients (writeup 1109/1118/1120/1124):
* `b = Rδ = H·G⁵·U¹⁵/(Δ²·Ω²)` (bare smooth count, n-free),
* `ev = err·ΔΩ/√L`, `err = G⁴U²⁰/Δ + (Δ⁴/H²)G⁵U⁴⁵/Ω¹⁴`, `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)`  (`N_s−1 = ev/√n`),
* `dc = (G⁴U¹⁵/Ω⁴)·√L`  (`δ/(T/R) = dc/√n`). -/
theorem ra_step4_ssum_collapse'
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (_hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ)
    (ℓ₁ L : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hLlo : 1 ≤ L)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hLW3 : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3)
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
    (b ev dc : ℝ)
    (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
    (hev : ev = (P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
                  * (S.Δ * S.Ω) / Real.sqrt L)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt L) :
    (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ))
      ≤ 16 * C * (P.H / S.Δ) *
          ( P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27) ) := by
  -- positivity facts
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hLlo
  have hCnn : 0 ≤ C := le_trans zero_le_one hC
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  -- nonnegativity (proved while `Real.sqrt L` is still visible to `positivity`)
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hevnn : 0 ≤ ev := by rw [hev]; positivity
  have hdcnn : 0 ≤ dc := by rw [hdc]; positivity
  have hcmnn : 0 ≤ dc + ev * b := by positivity
  have hcpnn : 0 ≤ ev * dc := by positivity
  -- ============ Phase 1: bound the sum by `b·N + (dc+ev·b)·2√N + ev·dc·N` ============
  have hint : ∀ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ)
      = b + (dc + ev * b) / Real.sqrt (n : ℝ) + (ev * dc) / (n : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hsqne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
    have htt : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnpos.le
    rw [weight4',
      show (ev * dc) / (n : ℝ)
        = (ev * dc) / (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) by rw [htt]]
    field_simp
    ring
  rw [Finset.sum_congr rfl hint]
  refine le_trans (step4_ssum_inv b (dc + ev * b) (ev * dc) hcmnn hcpnn N) ?_
  -- ============ Phase 2: collapse the cap into the sharp monomials ============
  set sL : ℝ := Real.sqrt L with hsL
  have hsLpos : 0 < sL := by rw [hsL]; exact Real.sqrt_pos.mpr hLpos
  have hsLne : sL ≠ 0 := ne_of_gt hsLpos
  have hsLmul : sL * sL = L := by rw [hsL, Real.mul_self_sqrt hLpos.le]
  set Scap : ℝ := ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8 with hScap
  have hScap_nn : 0 ≤ Scap := by rw [hScap]; positivity
  have hNC : (N : ℝ) ≤ C * Scap := by rw [hScap]; exact le_trans hNcap (le_of_eq (by ring))
  -- `√Scap = ℓ₁·sL·U⁵/Ω⁴`
  have hsqrtScap : Real.sqrt Scap = ℓ₁ * sL * P.U ^ 5 / S.Ω ^ 4 := by
    have heq : Scap = (ℓ₁ * sL * P.U ^ 5 / S.Ω ^ 4) ^ 2 := by
      have hsL2 : sL ^ 2 = L := by rw [pow_two]; exact hsLmul
      rw [hScap, div_pow, mul_pow, mul_pow, hsL2]; ring
    rw [heq, Real.sqrt_sq (by positivity)]
  -- `√N ≤ C·√Scap`
  have hsqrtNC : Real.sqrt (N : ℝ) ≤ C * Real.sqrt Scap := by
    have hsC1 : (1 : ℝ) ≤ Real.sqrt C := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt hC
    have hsCle : Real.sqrt C ≤ C := by
      have := mul_le_mul_of_nonneg_right hsC1 (Real.sqrt_nonneg C)
      rwa [one_mul, Real.mul_self_sqrt hCnn] at this
    calc Real.sqrt (N : ℝ) ≤ Real.sqrt (C * Scap) := Real.sqrt_le_sqrt hNC
      _ = Real.sqrt C * Real.sqrt Scap := Real.sqrt_mul hCnn Scap
      _ ≤ C * Real.sqrt Scap := mul_le_mul_of_nonneg_right hsCle (Real.sqrt_nonneg _)
  -- pull `C` out of all three pieces
  have hkey : b * (N : ℝ) + (dc + ev * b) * (2 * Real.sqrt (N : ℝ)) + ev * dc * (N : ℝ)
      ≤ C * (b * Scap) + C * ((dc + ev * b) * (2 * Real.sqrt Scap)) + C * (ev * dc * Scap) := by
    have t1 : b * (N : ℝ) ≤ C * (b * Scap) := by
      calc b * (N : ℝ) ≤ b * (C * Scap) := mul_le_mul_of_nonneg_left hNC hbnn
        _ = C * (b * Scap) := by ring
    have t2 : (dc + ev * b) * (2 * Real.sqrt (N : ℝ))
        ≤ C * ((dc + ev * b) * (2 * Real.sqrt Scap)) := by
      have h2N : 2 * Real.sqrt (N : ℝ) ≤ 2 * (C * Real.sqrt Scap) := by linarith [hsqrtNC]
      calc (dc + ev * b) * (2 * Real.sqrt (N : ℝ))
          ≤ (dc + ev * b) * (2 * (C * Real.sqrt Scap)) := mul_le_mul_of_nonneg_left h2N hcmnn
        _ = C * ((dc + ev * b) * (2 * Real.sqrt Scap)) := by ring
    have t3 : ev * dc * (N : ℝ) ≤ C * (ev * dc * Scap) := by
      calc ev * dc * (N : ℝ) ≤ ev * dc * (C * Scap) := mul_le_mul_of_nonneg_left hNC hcpnn
        _ = C * (ev * dc * Scap) := by ring
    linarith [t1, t2, t3]
  refine le_trans hkey ?_
  set HDt6 : ℝ := P.H * P.G ^ 14 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) with hHDt6
  set HDt7 : ℝ := S.Δ * P.G ^ 14 * P.U ^ 90 / S.Ω ^ 27 with hHDt7
  have hHDt6nn : 0 ≤ HDt6 := by rw [hHDt6]; positivity
  have hHDt7nn : 0 ≤ HDt7 := by rw [hHDt7]; positivity
  have hRHS : 16 * C * (P.H / S.Δ) * (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
        + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27))
      = C * (16 * HDt6 + 16 * HDt7) := by
    rw [hHDt6, hHDt7]; field_simp; try ring
  rw [hRHS]
  -- the C-free collapse
  have hfree : b * Scap + (dc + ev * b) * (2 * Real.sqrt Scap) + ev * dc * Scap
      ≤ 16 * HDt6 + 16 * HDt7 := by
    -- sqrt eliminations (writeup 1109/1118): keep everything sqrt-free henceforth
    have hdcsL : dc * sL = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * L := by
      rw [hdc, mul_assoc, hsLmul]
    have hevsL : ev * sL
        = (P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
            * (S.Δ * S.Ω) := by rw [hev]; field_simp
    have hevdc : ev * dc
        = (P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
            * (S.Δ * S.Ω) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4) := by
      have hrearr : ev * dc = (ev * sL) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4) := by
        rw [hdc]; ring
      rw [hrearr, hevsL]
    -- the regime fact `Δ²·G·U¹⁰ ≤ H`
    have hHbig : S.Δ ^ 2 * P.G * P.U ^ 10 ≤ P.H := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
      calc S.Δ ^ 2 * P.G * P.U ^ 10 = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
        _ ≤ P.H := h
    have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
    have hLnn : 0 ≤ L := hLpos.le
    have hU2 : (2 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
    have hΩ_le : ∀ k : ℕ, S.Ω ^ k ≤ P.U ^ k := fun k => pow_le_pow_left₀ hΩpos.le hΩU k
    -- the six explicit ℓ-monomials (`lC = ℓ₁²L`, `lB = ℓ₁L`, plain `ℓ₁`)
    set lC : ℝ := ℓ₁ ^ 2 * L with hlC
    set lB : ℝ := ℓ₁ * L with hlB
    have hlCnn : 0 ≤ lC := by rw [hlC]; positivity
    have hlBnn : 0 ≤ lB := by rw [hlB]; positivity
    -- the three pieces, sqrt-eliminated, as explicit ℓ-monomial sums
    have hbScap : b * Scap = lC * (P.H * P.G ^ 5 * P.U ^ 25 / (S.Δ ^ 2 * S.Ω ^ 10)) := by
      rw [hb, hScap, hlC]; field_simp; try ring
    have hpiece2 : (dc + ev * b) * (2 * Real.sqrt Scap)
        = lB * (2 * (P.G ^ 4 * P.U ^ 20 / S.Ω ^ 8))
          + ℓ₁ * (2 * (P.H * P.G ^ 9 * P.U ^ 40 / (S.Δ ^ 2 * S.Ω ^ 5)))
          + ℓ₁ * (2 * (S.Δ ^ 3 * P.G ^ 10 * P.U ^ 65 / (P.H * S.Ω ^ 19))) := by
      rw [hsqrtScap]
      have expand : (dc + ev * b) * (2 * (ℓ₁ * sL * P.U ^ 5 / S.Ω ^ 4))
          = 2 * (ℓ₁ * P.U ^ 5 / S.Ω ^ 4) * (dc * sL)
            + 2 * (ℓ₁ * P.U ^ 5 / S.Ω ^ 4) * ((ev * sL) * b) := by ring
      rw [expand, hdcsL, hevsL, hb, hlB]; field_simp; try ring
    have hpiece4 : ev * dc * Scap
        = lC * (P.G ^ 8 * P.U ^ 45 / S.Ω ^ 11)
          + lC * (S.Δ ^ 5 * P.G ^ 9 * P.U ^ 70 / (P.H ^ 2 * S.Ω ^ 25)) := by
      rw [hevdc, hScap, hlC]; field_simp; try ring
    rw [hbScap, hpiece2, hpiece4]
    -- W-collapse bounds
    have hWpos : 0 < P.G * P.U ^ 5 := by positivity
    have hcollC : lC ≤ 130 ^ 5 * (P.G * P.U ^ 5) ^ 5 := by
      rw [hlC]
      calc ℓ₁ ^ 2 * L ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * L :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hℓ1nn hℓ1W 2) hLnn
        _ ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) :=
            mul_le_mul_of_nonneg_left hLW3 (by positivity)
        _ = 130 ^ 5 * (P.G * P.U ^ 5) ^ 5 := by ring
    have hcollB : lB ≤ 130 ^ 4 * (P.G * P.U ^ 5) ^ 4 := by
      rw [hlB]
      calc ℓ₁ * L ≤ (130 * (P.G * P.U ^ 5)) * L := mul_le_mul_of_nonneg_right hℓ1W hLnn
        _ ≤ (130 * (P.G * P.U ^ 5)) * (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) :=
            mul_le_mul_of_nonneg_left hLW3 (by positivity)
        _ = 130 ^ 4 * (P.G * P.U ^ 5) ^ 4 := by ring
    -- the regime power facts
    have hU17k : (130 : ℝ) ^ 5 ≤ P.U := le_trans (by norm_num) hUbig
    have R1 : 130 ^ 5 * S.Ω ^ 3 ≤ P.G ^ 4 * P.U ^ 25 := by
      calc (130:ℝ) ^ 5 * S.Ω ^ 3 ≤ 130 ^ 5 * P.U ^ 3 :=
            mul_le_mul_of_nonneg_left (hΩ_le 3) (by positivity)
        _ ≤ P.U * P.U ^ 3 := mul_le_mul_of_nonneg_right hU17k (by positivity)
        _ = P.U ^ 4 := by ring
        _ ≤ P.U ^ 25 := pow_le_pow_right₀ hU1 (by norm_num)
        _ ≤ P.G ^ 4 * P.U ^ 25 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hG1)
    have R2 : 2 * 130 ^ 4 * S.Ω ^ 19 ≤ S.Δ * P.G ^ 6 * P.U ^ 50 := by
      calc (2:ℝ) * 130 ^ 4 * S.Ω ^ 19 ≤ 2 * 130 ^ 4 * P.U ^ 19 :=
            mul_le_mul_of_nonneg_left (hΩ_le 19) (by positivity)
        _ ≤ P.U * P.U ^ 19 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) hU17k) (by positivity)
        _ = P.U ^ 20 := by ring
        _ ≤ P.U ^ 50 := pow_le_pow_right₀ hU1 (by norm_num)
        _ ≤ S.Δ * P.G ^ 6 * P.U ^ 50 := by
            have h17 : (1 : ℝ) ≤ S.Δ * P.G ^ 6 := by
              have := mul_le_mul hΔ1 (one_le_pow₀ hG1 (n := 6)) zero_le_one (le_trans zero_le_one hΔ1)
              simpa using this
            calc P.U ^ 50 = 1 * P.U ^ 50 := (one_mul _).symm
              _ ≤ (S.Δ * P.G ^ 6) * P.U ^ 50 := mul_le_mul_of_nonneg_right h17 (by positivity)
              _ = S.Δ * P.G ^ 6 * P.U ^ 50 := by ring
    have R3 : 260 * S.Ω ^ 8 ≤ P.G ^ 4 * P.U ^ 30 := by
      calc 260 * S.Ω ^ 8 ≤ 260 * P.U ^ 8 :=
            mul_le_mul_of_nonneg_left (hΩ_le 8) (by positivity)
        _ ≤ P.U * P.U ^ 8 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) hU17k) (by positivity)
        _ = P.U ^ 9 := by ring
        _ ≤ P.U ^ 30 := pow_le_pow_right₀ hU1 (by norm_num)
        _ ≤ P.G ^ 4 * P.U ^ 30 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hG1)
    have R4 : 260 * S.Δ ^ 2 * S.Ω ^ 8 ≤ P.H * P.G ^ 3 * P.U ^ 20 := by
      have hf1 := mul_le_mul_of_nonneg_left R3 (by positivity : (0:ℝ) ≤ S.Δ ^ 2)
      have hf2 := mul_le_mul_of_nonneg_right hHbig (by positivity : (0:ℝ) ≤ P.G ^ 3 * P.U ^ 20)
      calc 260 * S.Δ ^ 2 * S.Ω ^ 8 = S.Δ ^ 2 * (260 * S.Ω ^ 8) := by ring
        _ ≤ S.Δ ^ 2 * (P.G ^ 4 * P.U ^ 30) := hf1
        _ = (S.Δ ^ 2 * P.G * P.U ^ 10) * (P.G ^ 3 * P.U ^ 20) := by ring
        _ ≤ P.H * (P.G ^ 3 * P.U ^ 20) := hf2
        _ = P.H * P.G ^ 3 * P.U ^ 20 := by ring
    have R5 : 130 ^ 5 * S.Ω ^ 16 ≤ S.Δ * P.G * P.U ^ 20 := by
      calc (130:ℝ) ^ 5 * S.Ω ^ 16 ≤ 130 ^ 5 * P.U ^ 16 :=
            mul_le_mul_of_nonneg_left (hΩ_le 16) (by positivity)
        _ ≤ P.U * P.U ^ 16 := mul_le_mul_of_nonneg_right hU17k (by positivity)
        _ = P.U ^ 17 := by ring
        _ ≤ P.U ^ 20 := pow_le_pow_right₀ hU1 (by norm_num)
        _ ≤ S.Δ * P.G * P.U ^ 20 := by
            have h12 : (1 : ℝ) ≤ S.Δ * P.G := by
              have := mul_le_mul hΔ1 hG1 zero_le_one (le_trans zero_le_one hΔ1)
              simpa using this
            calc P.U ^ 20 = 1 * P.U ^ 20 := (one_mul _).symm
              _ ≤ (S.Δ * P.G) * P.U ^ 20 := mul_le_mul_of_nonneg_right h12 (by positivity)
              _ = S.Δ * P.G * P.U ^ 20 := by ring
    have R6 : 130 ^ 5 * (S.Δ ^ 4 * P.U ^ 5 * S.Ω ^ 2) ≤ P.H ^ 2 := by
      have hHsq : (S.Δ ^ 2 * P.G * P.U ^ 10) ^ 2 ≤ P.H ^ 2 :=
        pow_le_pow_left₀ (by positivity) hHbig 2
      have hu : (130:ℝ) ^ 5 * P.U ^ 7 ≤ P.G ^ 2 * P.U ^ 20 := by
        calc (130:ℝ) ^ 5 * P.U ^ 7 ≤ P.U * P.U ^ 7 :=
              mul_le_mul_of_nonneg_right hU17k (by positivity)
          _ = P.U ^ 8 := by ring
          _ ≤ P.U ^ 20 := pow_le_pow_right₀ hU1 (by norm_num)
          _ ≤ P.G ^ 2 * P.U ^ 20 :=
              le_mul_of_one_le_left (by positivity) (one_le_pow₀ hG1)
      calc (130:ℝ) ^ 5 * (S.Δ ^ 4 * P.U ^ 5 * S.Ω ^ 2)
            ≤ 130 ^ 5 * (S.Δ ^ 4 * P.U ^ 5 * P.U ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hΩ_le 2) (by positivity : (0:ℝ) ≤ S.Δ ^ 4 * P.U ^ 5))
              (by positivity)
        _ = S.Δ ^ 4 * (130 ^ 5 * P.U ^ 7) := by ring
        _ ≤ S.Δ ^ 4 * (P.G ^ 2 * P.U ^ 20) := mul_le_mul_of_nonneg_left hu (by positivity)
        _ = (S.Δ ^ 2 * P.G * P.U ^ 10) ^ 2 := by ring
        _ ≤ P.H ^ 2 := hHsq
    -- the six collapsed-monomial bounds `Wᵈᵉᵍ·m̂ᵢ ≤ HDtⱼ`
    have hm1 : (130 ^ 5 * (P.G * P.U ^ 5) ^ 5)
          * (P.H * P.G ^ 5 * P.U ^ 25 / (S.Δ ^ 2 * S.Ω ^ 10)) ≤ HDt6 := by
      rw [hHDt6]
      have hrw : (130 ^ 5 * (P.G * P.U ^ 5) ^ 5) * (P.H * P.G ^ 5 * P.U ^ 25 / (S.Δ ^ 2 * S.Ω ^ 10))
          = 130 ^ 5 * (P.H * P.G ^ 10 * P.U ^ 50) / (S.Δ ^ 2 * S.Ω ^ 10) := by field_simp; try ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hf := mul_le_mul_of_nonneg_left R1 (by positivity : (0:ℝ) ≤ P.H * P.G ^ 10 * P.U ^ 50 * S.Δ ^ 2 * S.Ω ^ 10)
      calc (130:ℝ) ^ 5 * (P.H * P.G ^ 10 * P.U ^ 50) * (S.Δ ^ 2 * S.Ω ^ 13)
          = (P.H * P.G ^ 10 * P.U ^ 50 * S.Δ ^ 2 * S.Ω ^ 10) * (130 ^ 5 * S.Ω ^ 3) := by ring
        _ ≤ (P.H * P.G ^ 10 * P.U ^ 50 * S.Δ ^ 2 * S.Ω ^ 10) * (P.G ^ 4 * P.U ^ 25) := hf
        _ = P.H * P.G ^ 14 * P.U ^ 75 * (S.Δ ^ 2 * S.Ω ^ 10) := by ring
    have hm2 : (130 ^ 4 * (P.G * P.U ^ 5) ^ 4) * (2 * (P.G ^ 4 * P.U ^ 20 / S.Ω ^ 8)) ≤ HDt7 := by
      rw [hHDt7]
      have hrw : ((130:ℝ) ^ 4 * (P.G * P.U ^ 5) ^ 4) * (2 * (P.G ^ 4 * P.U ^ 20 / S.Ω ^ 8))
          = 2 * 130 ^ 4 * P.G ^ 8 * P.U ^ 40 / S.Ω ^ 8 := by field_simp; try ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hf := mul_le_mul_of_nonneg_left R2 (by positivity : (0:ℝ) ≤ P.G ^ 8 * P.U ^ 40 * S.Ω ^ 8)
      calc (2:ℝ) * 130 ^ 4 * P.G ^ 8 * P.U ^ 40 * S.Ω ^ 27
          = (P.G ^ 8 * P.U ^ 40 * S.Ω ^ 8) * (2 * 130 ^ 4 * S.Ω ^ 19) := by ring
        _ ≤ (P.G ^ 8 * P.U ^ 40 * S.Ω ^ 8) * (S.Δ * P.G ^ 6 * P.U ^ 50) := hf
        _ = S.Δ * P.G ^ 14 * P.U ^ 90 * S.Ω ^ 8 := by ring
    have hm3 : (130 * (P.G * P.U ^ 5))
          * (2 * (P.H * P.G ^ 9 * P.U ^ 40 / (S.Δ ^ 2 * S.Ω ^ 5))) ≤ HDt6 := by
      rw [hHDt6]
      have hrw : (130 * (P.G * P.U ^ 5)) * (2 * (P.H * P.G ^ 9 * P.U ^ 40 / (S.Δ ^ 2 * S.Ω ^ 5)))
          = 260 * P.H * P.G ^ 10 * P.U ^ 45 / (S.Δ ^ 2 * S.Ω ^ 5) := by field_simp; try ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hf := mul_le_mul_of_nonneg_left R3 (by positivity : (0:ℝ) ≤ P.H * P.G ^ 10 * P.U ^ 45 * S.Δ ^ 2 * S.Ω ^ 5)
      calc 260 * P.H * P.G ^ 10 * P.U ^ 45 * (S.Δ ^ 2 * S.Ω ^ 13)
          = (P.H * P.G ^ 10 * P.U ^ 45 * S.Δ ^ 2 * S.Ω ^ 5) * (260 * S.Ω ^ 8) := by ring
        _ ≤ (P.H * P.G ^ 10 * P.U ^ 45 * S.Δ ^ 2 * S.Ω ^ 5) * (P.G ^ 4 * P.U ^ 30) := hf
        _ = P.H * P.G ^ 14 * P.U ^ 75 * (S.Δ ^ 2 * S.Ω ^ 5) := by ring
    have hm4 : (130 * (P.G * P.U ^ 5))
          * (2 * (S.Δ ^ 3 * P.G ^ 10 * P.U ^ 65 / (P.H * S.Ω ^ 19))) ≤ HDt7 := by
      rw [hHDt7]
      have hrw : (130 * (P.G * P.U ^ 5)) * (2 * (S.Δ ^ 3 * P.G ^ 10 * P.U ^ 65 / (P.H * S.Ω ^ 19)))
          = 260 * S.Δ ^ 3 * P.G ^ 11 * P.U ^ 70 / (P.H * S.Ω ^ 19) := by field_simp; try ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hf := mul_le_mul_of_nonneg_left R4 (by positivity : (0:ℝ) ≤ S.Δ * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 19)
      calc 260 * S.Δ ^ 3 * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 27
          = (S.Δ * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 19) * (260 * S.Δ ^ 2 * S.Ω ^ 8) := by ring
        _ ≤ (S.Δ * P.G ^ 11 * P.U ^ 70 * S.Ω ^ 19) * (P.H * P.G ^ 3 * P.U ^ 20) := hf
        _ = S.Δ * P.G ^ 14 * P.U ^ 90 * (P.H * S.Ω ^ 19) := by ring
    have hm5 : (130 ^ 5 * (P.G * P.U ^ 5) ^ 5) * (P.G ^ 8 * P.U ^ 45 / S.Ω ^ 11) ≤ HDt7 := by
      rw [hHDt7]
      have hrw : ((130:ℝ) ^ 5 * (P.G * P.U ^ 5) ^ 5) * (P.G ^ 8 * P.U ^ 45 / S.Ω ^ 11)
          = 130 ^ 5 * (P.G ^ 13 * P.U ^ 70) / S.Ω ^ 11 := by field_simp; try ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hf := mul_le_mul_of_nonneg_left R5 (by positivity : (0:ℝ) ≤ P.G ^ 13 * P.U ^ 70 * S.Ω ^ 11)
      calc (130:ℝ) ^ 5 * (P.G ^ 13 * P.U ^ 70) * S.Ω ^ 27
          = (P.G ^ 13 * P.U ^ 70 * S.Ω ^ 11) * (130 ^ 5 * S.Ω ^ 16) := by ring
        _ ≤ (P.G ^ 13 * P.U ^ 70 * S.Ω ^ 11) * (S.Δ * P.G * P.U ^ 20) := hf
        _ = S.Δ * P.G ^ 14 * P.U ^ 90 * S.Ω ^ 11 := by ring
    have hm6 : (130 ^ 5 * (P.G * P.U ^ 5) ^ 5)
          * (S.Δ ^ 5 * P.G ^ 9 * P.U ^ 70 / (P.H ^ 2 * S.Ω ^ 25)) ≤ HDt7 := by
      rw [hHDt7]
      have hrw : ((130:ℝ) ^ 5 * (P.G * P.U ^ 5) ^ 5) * (S.Δ ^ 5 * P.G ^ 9 * P.U ^ 70 / (P.H ^ 2 * S.Ω ^ 25))
          = 130 ^ 5 * (S.Δ ^ 5 * P.G ^ 14 * P.U ^ 95) / (P.H ^ 2 * S.Ω ^ 25) := by field_simp; try ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hf := mul_le_mul_of_nonneg_left R6 (by positivity : (0:ℝ) ≤ S.Δ * P.G ^ 14 * P.U ^ 90 * S.Ω ^ 25)
      calc (130:ℝ) ^ 5 * (S.Δ ^ 5 * P.G ^ 14 * P.U ^ 95) * S.Ω ^ 27
          = (S.Δ * P.G ^ 14 * P.U ^ 90 * S.Ω ^ 25) * (130 ^ 5 * (S.Δ ^ 4 * P.U ^ 5 * S.Ω ^ 2)) := by ring
        _ ≤ (S.Δ * P.G ^ 14 * P.U ^ 90 * S.Ω ^ 25) * P.H ^ 2 := hf
        _ = S.Δ * P.G ^ 14 * P.U ^ 90 * (P.H ^ 2 * S.Ω ^ 25) := by ring
    -- assemble: each `lᵢ·m̂ᵢ ≤ Wᵈᵉᵍ·m̂ᵢ ≤ HDtⱼ`
    have hm1hat : 0 ≤ P.H * P.G ^ 5 * P.U ^ 25 / (S.Δ ^ 2 * S.Ω ^ 10) := by positivity
    have hm2hat : 0 ≤ 2 * (P.G ^ 4 * P.U ^ 20 / S.Ω ^ 8) := by positivity
    have hm3hat : 0 ≤ 2 * (P.H * P.G ^ 9 * P.U ^ 40 / (S.Δ ^ 2 * S.Ω ^ 5)) := by positivity
    have hm4hat : 0 ≤ 2 * (S.Δ ^ 3 * P.G ^ 10 * P.U ^ 65 / (P.H * S.Ω ^ 19)) := by positivity
    have hm5hat : 0 ≤ P.G ^ 8 * P.U ^ 45 / S.Ω ^ 11 := by positivity
    have hm6hat : 0 ≤ S.Δ ^ 5 * P.G ^ 9 * P.U ^ 70 / (P.H ^ 2 * S.Ω ^ 25) := by positivity
    have b1 : lC * (P.H * P.G ^ 5 * P.U ^ 25 / (S.Δ ^ 2 * S.Ω ^ 10)) ≤ HDt6 :=
      le_trans (mul_le_mul_of_nonneg_right hcollC hm1hat) hm1
    have b2 : lB * (2 * (P.G ^ 4 * P.U ^ 20 / S.Ω ^ 8)) ≤ HDt7 :=
      le_trans (mul_le_mul_of_nonneg_right hcollB hm2hat) hm2
    have b3 : ℓ₁ * (2 * (P.H * P.G ^ 9 * P.U ^ 40 / (S.Δ ^ 2 * S.Ω ^ 5))) ≤ HDt6 :=
      le_trans (mul_le_mul_of_nonneg_right hℓ1W hm3hat) hm3
    have b4 : ℓ₁ * (2 * (S.Δ ^ 3 * P.G ^ 10 * P.U ^ 65 / (P.H * S.Ω ^ 19))) ≤ HDt7 :=
      le_trans (mul_le_mul_of_nonneg_right hℓ1W hm4hat) hm4
    have b5 : lC * (P.G ^ 8 * P.U ^ 45 / S.Ω ^ 11) ≤ HDt7 :=
      le_trans (mul_le_mul_of_nonneg_right hcollC hm5hat) hm5
    have b6 : lC * (S.Δ ^ 5 * P.G ^ 9 * P.U ^ 70 / (P.H ^ 2 * S.Ω ^ 25)) ≤ HDt7 :=
      le_trans (mul_le_mul_of_nonneg_right hcollC hm6hat) hm6
    have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5) b6
    linarith [hsum, hHDt6nn, hHDt7nn]
  calc C * (b * Scap) + C * ((dc + ev * b) * (2 * Real.sqrt Scap)) + C * (ev * dc * Scap)
      = C * (b * Scap + (dc + ev * b) * (2 * Real.sqrt Scap) + ev * dc * Scap) := by ring
    _ ≤ C * (16 * HDt6 + 16 * HDt7) := mul_le_mul_of_nonneg_left hfree hCnn

end Squarefree
