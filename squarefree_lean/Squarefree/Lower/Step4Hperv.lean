import Squarefree.Lower.Step4PervCard
import Squarefree.Lower.Step4BandPay

/-!
# §5 Step-4 per-`(s,v)` r-count `hperv` — FAITHFUL bare `Rδ` count (writeup 1064–1088)

`step4_hperv` is the per-`(s,v)`-fibre `φ_v`-window count: for a fixed admissible `(s,v)`
(equivalently a fixed lattice point `m = ℓ₁v`, here the `w := v`-value), the positions `r` in
the s₄ fibre lying in the comparable window `[r₀,r₁] ⊆ [R/72, 16R]` with the per-`r` near-integer
witness `distInt(φ_v(r)) ≤ δ` number at most

```
Cv := 10²⁰⁰·(b + dc/√n),   b = Rδ = H·G⁵U¹⁵/(Δ²Ω²),   dc/√n = G⁴U¹⁵/Ω⁴·√L/√n.
```

This is the **FAITHFUL `1/√n` band** count (md 1086–1088): `#{r:‖φ_v‖≤δ} ≪ Rδ + δ/(T/R)`.
Unlike the tight-`I_s` route (`step4_perv_count`, whose leading `|I_s|·δ = (s1+s2)` is the
premature `+√n` form summing to `S^{3/2}`), the leading term here is the bare `R·δ = b`, obtained
over the comparable window `len = r₁−r₀ ≤ 16R` (the `v`-band has already constrained `v`; we do
*not* localize `r` through `Σ_s`, md 1050).

`perv_countR` is the abstract analytic core (the `W`-cancelled count algebra over `len ≤ 16R`);
`step4_hperv` threads it through the counting injection `step4_perv_card_le`.
-/

open Squarefree.Counting

namespace Squarefree


/-- A small-constant power bound: `c·10^k ≤ 10¹⁹⁹` whenever `c ≤ 10²` and `2+k ≤ 199`. -/
private theorem hperv_cle {c : ℝ} {k : ℕ} (hc2 : c ≤ 10 ^ 2)
    (hk : 2 + k ≤ 199) : c * 10 ^ k ≤ 10 ^ 199 := by
  calc c * 10 ^ k ≤ 10 ^ 2 * 10 ^ k := by gcongr
    _ = 10 ^ (2 + k) := by rw [← pow_add]
    _ ≤ 10 ^ 199 := pow_le_pow_right₀ (by norm_num) hk

/-- **§5 Step-4 per-`(s,v)` r-count algebra (FAITHFUL bare `Rδ`).**  The abstract
comparable-window count value `(10¹³·W·len + 2δ + 1)(2δ/(W/10⁵⁰) + 1)` (`W` the `φ_v`-slope
scale, `len ≤ 16R`, `δ` the witness defect) is `≤ 10²⁰⁰·(b + dc/√n)` with `b = H·G⁵U¹⁵/(Δ²Ω²)`
and `dc/√n = G⁴U¹⁵/Ω⁴·√Lr/√n`.

Mechanism: the leading `MQ` term `W`-cancels to `2·10⁶³·len·δ ≤ const·R·δ = const·b`; the
variation `M = 10¹³·W·len ≤ const·(Ws·R) ≤ const·b` (`√n ≤ √N` cap); `δ ≤ ½` collapses `2δQ ≤ Q`;
and `Q ≍ δ/Ws → dc/√n`.  No `δ·dc` sub-bound is needed (the FAITHFUL route's win). -/
private theorem perv_countR {P : Globals} {S : Scale P} {ℓ₁ Lr W δ len n : ℝ}
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hδhalf : δ ≤ 1 / 2)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (_hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hℓ1lo : 1 ≤ ℓ₁) (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5))
    (hLrlo : 1 ≤ Lr)
    (hδ : δ = 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5))
    (hn1 : 1 ≤ n) (hnN : n ≤ 10 ^ 57 * ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8)
    (hWpos : 0 < W)
    (hWhi : W ≤ 10 ^ 9 * (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt Lr)))
    (hWlo : Real.sqrt n / (S.Δ * S.Ω * Real.sqrt Lr) ≤ 10 ^ 9 * W)
    (hlen0 : 0 ≤ len) (hlenR : len ≤ 16 * S.R) :
    (10 ^ 13 * W * len + 2 * δ + 1) * (2 * δ / (W / 10 ^ 50) + 1)
      ≤ 10 ^ 200 * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)
          + P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt Lr / Real.sqrt n) := by
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hLrpos : 0 < Lr := lt_of_lt_of_le one_pos hLrlo
  have hsqLr : 0 < Real.sqrt Lr := Real.sqrt_pos.mpr hLrpos
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn1
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hΩne := hΩpos.ne'
  have hΔne := hΔpos.ne'
  have hsqLrne := hsqLr.ne'
  have hsqnne := hsqn.ne'
  set b : ℝ := P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2) with hb_def
  set DC : ℝ := P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt Lr / Real.sqrt n with hDC_def
  have hbpos : 0 < b := by rw [hb_def]; positivity
  have hDCpos : 0 < DC := by rw [hDC_def]; positivity
  set Ws : ℝ := Real.sqrt n / (S.Δ * S.Ω * Real.sqrt Lr) with hWs_def
  have hWspos : 0 < Ws := by rw [hWs_def]; positivity
  -- ℓ₁ ≤ G⁴U¹⁰
  have hG3U5 : (1:ℝ) ≤ P.G ^ 3 * P.U ^ 5 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hG1) (one_le_pow₀ hU1)
  have hℓ1G4 : ℓ₁ ≤ P.G ^ 4 * P.U ^ 10 := by
    refine le_trans hℓ1W ?_
    have h130 : (130:ℝ) ≤ P.G ^ 3 * P.U ^ 5 := by
      have hU5 : (130:ℝ) ≤ P.U ^ 5 := by
        calc (130:ℝ) ≤ 10 ^ 33 := by norm_num
          _ ≤ P.U := hUbig
          _ ≤ P.U ^ 5 := by nlinarith only [one_le_pow₀ (n := 4) hU1, hUpos]
      nlinarith only [hU5, one_le_pow₀ (n := 3) hG1, pow_pos hUpos 5]
    have hkey := mul_le_mul_of_nonneg_right h130
      (le_of_lt (mul_pos hGpos (pow_pos hUpos 5)))
    linarith [hkey]
  -- H ≥ Δ²GU¹⁰
  have hHlo : S.Δ ^ 2 * P.G * P.U ^ 10 ≤ P.H := by
    rw [le_div_iff₀ (by positivity)] at h1; linarith [h1]
  have hΔGU6 : (1:ℝ) ≤ S.Δ * P.G * P.U ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hΔ1 hG1)
      (one_le_pow₀ hU1)
  have hΔU4H : S.Δ * P.U ^ 4 ≤ P.H := by
    nlinarith only [hHlo, mul_le_mul_of_nonneg_left hΔGU6
      (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 4)]
  have hΔHGΩ : S.Δ ≤ P.H * P.G * S.Ω ^ 3 := by
    have hpay3 := band_pay3 (P := P) (S := S) hband hΩU
    calc S.Δ = S.Δ * 1 := (mul_one _).symm
      _ ≤ S.Δ * (P.G * P.U ^ 4 * S.Ω ^ 3) := mul_le_mul_of_nonneg_left hpay3 hΔpos.le
      _ = (S.Δ * P.U ^ 4) * (P.G * S.Ω ^ 3) := by ring
      _ ≤ P.H * (P.G * S.Ω ^ 3) := mul_le_mul_of_nonneg_right hΔU4H (by positivity)
      _ = P.H * P.G * S.Ω ^ 3 := by ring
  -- √n ≤ √N = ℓ₁·√Lr·U⁵/Ω⁴
  have hsqN : Real.sqrt n ≤ 10 ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4) := by
    have hLrsq : Real.sqrt Lr ^ 2 = Lr := Real.sq_sqrt hLrpos.le
    have hb_nn : 0 ≤ 10 ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4) := by positivity
    have hXsq : (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4) ^ 2
        = ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8 := by
      rw [div_pow, mul_pow, mul_pow, hLrsq]; ring
    have hNle : 10 ^ 57 * ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8
        ≤ ((10:ℝ) ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4)) ^ 2 := by
      have hX : (0:ℝ) ≤ ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8 := by positivity
      calc 10 ^ 57 * ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8
          = 10 ^ 57 * (ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8) := by ring
        _ ≤ 10 ^ 58 * (ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8) := by nlinarith only [hX]
        _ = ((10:ℝ) ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4)) ^ 2 := by
            rw [mul_pow, hXsq, show ((10:ℝ) ^ 29) ^ 2 = 10 ^ 58 by norm_num]
    calc Real.sqrt n ≤ Real.sqrt (10 ^ 57 * ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8) :=
          Real.sqrt_le_sqrt hnN
      _ ≤ Real.sqrt (((10:ℝ) ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4)) ^ 2) :=
          Real.sqrt_le_sqrt hNle
      _ = 10 ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4) := Real.sqrt_sq hb_nn
  -- the δ-content single fraction
  have hcontent : (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5 = P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 5) := by
    field_simp
  -- R·δ = 10⁷⁰·b   (the bare `Rδ` identity)
  have hRδ : S.R * δ = 10 ^ 70 * b := by
    rw [hδ, Scale.R, hb_def]; field_simp
  -- Ws·R ≤ b   (variation cap via √n ≤ √N and ℓ₁ ≤ G⁴U¹⁰)
  have hWsR : Ws * S.R ≤ 10 ^ 29 * b := by
    have key : Ws * S.R = Real.sqrt n * (S.R / (S.Δ * S.Ω * Real.sqrt Lr)) := by
      rw [hWs_def]; ring
    rw [key]
    refine le_trans (mul_le_mul_of_nonneg_right hsqN (by positivity)) ?_
    have hprod : (10 ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4))
          * (S.R / (S.Δ * S.Ω * Real.sqrt Lr))
        = 10 ^ 29 * (P.H * P.G * ℓ₁ * P.U ^ 5 / (S.Δ ^ 2 * S.Ω ^ 2)) := by
      rw [Scale.R]; field_simp
    rw [hprod]
    have hold : P.H * P.G * ℓ₁ * P.U ^ 5 / (S.Δ ^ 2 * S.Ω ^ 2) ≤ b := by
      rw [hb_def, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right hℓ1G4
          (by positivity : (0:ℝ) ≤ P.H * P.G * P.U ^ 5 * (S.Δ ^ 2 * S.Ω ^ 2)),
        hHpos, hGpos, hΔpos, hΩpos, pow_pos hUpos 5]
    linarith [hold]
  -- δ/Ws = 10⁷⁰·DC   (exact)
  have hδWs : δ / Ws = 10 ^ 70 * DC := by
    rw [hδ, hWs_def, hDC_def]
    rw [div_div_eq_mul_div, div_eq_iff (by positivity)]; field_simp
  -- δ ≤ 10⁷⁰·b
  have hδb : δ ≤ 10 ^ 70 * b := by
    rw [hδ, hb_def, hcontent]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ (10:ℝ) ^ 70)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hΔHGΩ
        (by positivity : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 15 * (S.Δ * S.Ω ^ 2)),
      hHpos, hGpos, hΩpos, hΔpos, pow_pos hGpos 4, pow_pos hUpos 15]
  -- 2δ ≤ 1   (δ tiny: Δ ≥ 10¹⁵G⁴U²⁰, U ≥ 10³³)
  have h2δ1 : 2 * δ ≤ 1 := by linarith [hδhalf]
  -- δ/W ≤ 10⁹·(10⁷⁰·DC)
  have hinvW : 1 / W ≤ 10 ^ 9 / Ws := by
    rw [div_le_div_iff₀ hWpos hWspos]; linarith [hWlo]
  have hδW : δ / W ≤ 10 ^ 9 * (10 ^ 70 * DC) := by
    have hrw : δ / W = δ * (1 / W) := by ring
    rw [hrw]
    calc δ * (1 / W) ≤ δ * (10 ^ 9 / Ws) := mul_le_mul_of_nonneg_left hinvW hδpos.le
      _ = 10 ^ 9 * (δ / Ws) := by ring
      _ = 10 ^ 9 * (10 ^ 70 * DC) := by rw [hδWs]
  -- 1 ≤ 10⁷⁰·DC
  have hone : (1:ℝ) ≤ 10 ^ 70 * DC := by
    have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
    have hlow : S.Ω ^ 4 / (10 ^ 29 * (ℓ₁ * P.U ^ 5)) ≤ Real.sqrt Lr / Real.sqrt n := by
      rw [div_le_div_iff₀ (by positivity) hsqn]
      have hstep : S.Ω ^ 4 * Real.sqrt n
          ≤ S.Ω ^ 4 * (10 ^ 29 * (ℓ₁ * Real.sqrt Lr * P.U ^ 5 / S.Ω ^ 4)) :=
        mul_le_mul_of_nonneg_left hsqN (by positivity)
      refine le_trans hstep (le_of_eq ?_); field_simp
    have hdcge : P.G ^ 4 * P.U ^ 10 / (10 ^ 29 * ℓ₁) ≤ DC := by
      rw [hDC_def]
      have heqdc : P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt Lr / Real.sqrt n
          = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * (Real.sqrt Lr / Real.sqrt n) := by ring
      rw [heqdc]
      calc P.G ^ 4 * P.U ^ 10 / (10 ^ 29 * ℓ₁)
          = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * (S.Ω ^ 4 / (10 ^ 29 * (ℓ₁ * P.U ^ 5))) := by
            field_simp
        _ ≤ P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * (Real.sqrt Lr / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
    have hge : 10 ^ 70 * (P.G ^ 4 * P.U ^ 10 / (10 ^ 29 * ℓ₁)) ≤ 10 ^ 70 * DC :=
      mul_le_mul_of_nonneg_left hdcge (by positivity)
    refine le_trans ?_ hge
    rw [show (10:ℝ) ^ 70 * (P.G ^ 4 * P.U ^ 10 / (10 ^ 29 * ℓ₁))
          = 10 ^ 41 * (P.G ^ 4 * P.U ^ 10) / ℓ₁ by
        rw [show (10:ℝ) ^ 70 = 10 ^ 41 * 10 ^ 29 by norm_num]; field_simp,
        le_div_iff₀ hℓ1pos, one_mul]
    nlinarith only [hℓ1G4, (by positivity : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 10)]
  -- ===== ASSEMBLY =====
  set M : ℝ := 10 ^ 13 * W * len with hM_def
  set Q : ℝ := 2 * δ / (W / 10 ^ 50) with hQ_def
  have hQnn : 0 ≤ Q := by rw [hQ_def]; positivity
  have hQeq : Q = 2 * 10 ^ 50 * (δ / W) := by rw [hQ_def, div_div_eq_mul_div]; ring
  have hbDC_nn : 0 ≤ b + DC := by positivity
  have hble : b ≤ b + DC := by linarith [hDCpos]
  have hDCle : DC ≤ b + DC := by linarith [hbpos]
  -- T1 : M·Q ≤ 10¹⁹⁹·(b+DC)
  have hT1 : M * Q ≤ 10 ^ 199 * (b + DC) := by
    have hMQeq : M * Q = 2 * 10 ^ 63 * (len * δ) := by rw [hM_def, hQeq]; field_simp
    rw [hMQeq]
    have hlenδ : len * δ ≤ 16 * S.R * δ := mul_le_mul_of_nonneg_right hlenR hδpos.le
    refine le_trans (mul_le_mul_of_nonneg_left hlenδ (by norm_num : (0:ℝ) ≤ 2 * 10 ^ 63)) ?_
    rw [show (2:ℝ) * 10 ^ 63 * (16 * S.R * δ) = (2 * 16) * 10 ^ 63 * (S.R * δ) by ring, hRδ,
        show (2 * 16 : ℝ) * 10 ^ 63 * (10 ^ 70 * b) = 32 * 10 ^ 133 * b by
          rw [show (10:ℝ) ^ 133 = 10 ^ 63 * 10 ^ 70 by norm_num]; ring]
    calc 32 * 10 ^ 133 * b ≤ 10 ^ 199 * b :=
          mul_le_mul_of_nonneg_right (hperv_cle (by norm_num) (by norm_num)) hbpos.le
      _ ≤ 10 ^ 199 * (b + DC) := mul_le_mul_of_nonneg_left hble (by positivity)
  -- T2 : M ≤ 10¹⁹⁹·(b+DC)
  have hT2 : M ≤ 10 ^ 199 * (b + DC) := by
    rw [hM_def]
    have hWl : W * len ≤ (10 ^ 9 * Ws) * (16 * S.R) := mul_le_mul hWhi hlenR hlen0 (by positivity)
    have h22 : 10 ^ 13 * W * len ≤ (10 ^ 13 * 10 ^ 9 * 16) * (Ws * S.R) := by
      calc 10 ^ 13 * W * len = 10 ^ 13 * (W * len) := by ring
        _ ≤ 10 ^ 13 * ((10 ^ 9 * Ws) * (16 * S.R)) :=
            mul_le_mul_of_nonneg_left hWl (by norm_num)
        _ = (10 ^ 13 * 10 ^ 9 * 16) * (Ws * S.R) := by ring
    refine le_trans h22 ?_
    rw [show (10 ^ 13 * 10 ^ 9 * 16 : ℝ) = 16 * 10 ^ 22 by
        rw [show (10:ℝ) ^ 22 = 10 ^ 13 * 10 ^ 9 by norm_num]; ring]
    calc 16 * 10 ^ 22 * (Ws * S.R) ≤ 16 * 10 ^ 22 * (10 ^ 29 * b) :=
          mul_le_mul_of_nonneg_left hWsR (by norm_num)
      _ = 16 * 10 ^ 51 * b := by
          rw [show (10:ℝ) ^ 51 = 10 ^ 22 * 10 ^ 29 by norm_num]; ring
      _ ≤ 10 ^ 199 * b :=
          mul_le_mul_of_nonneg_right (hperv_cle (by norm_num) (by norm_num)) hbpos.le
      _ ≤ 10 ^ 199 * (b + DC) := mul_le_mul_of_nonneg_left hble (by positivity)
  -- Q ≤ 2·10¹²⁹·DC   (reused for T3, T5)
  have hQle : Q ≤ 2 * 10 ^ 129 * DC := by
    rw [hQeq]
    calc 2 * 10 ^ 50 * (δ / W) ≤ 2 * 10 ^ 50 * (10 ^ 9 * (10 ^ 70 * DC)) :=
          mul_le_mul_of_nonneg_left hδW (by positivity)
      _ = 2 * 10 ^ 129 * DC := by
          rw [show (10:ℝ) ^ 129 = 10 ^ 50 * (10 ^ 9 * 10 ^ 70) by norm_num]; ring
  have hT5 : Q ≤ 10 ^ 199 * (b + DC) := by
    refine le_trans hQle ?_
    calc 2 * 10 ^ 129 * DC ≤ 10 ^ 199 * DC :=
          mul_le_mul_of_nonneg_right (hperv_cle (by norm_num) (by norm_num)) hDCpos.le
      _ ≤ 10 ^ 199 * (b + DC) := mul_le_mul_of_nonneg_left hDCle (by positivity)
  -- T3 : 2δ·Q ≤ Q ≤ 10¹⁹⁹·(b+DC)   (δ ≤ ½)
  have hT3 : 2 * δ * Q ≤ 10 ^ 199 * (b + DC) := by
    have h : 2 * δ * Q ≤ 1 * Q := mul_le_mul_of_nonneg_right h2δ1 hQnn
    rw [one_mul] at h; exact le_trans h hT5
  -- T4 : 2δ ≤ 10¹⁹⁹·(b+DC)
  have hT4 : 2 * δ ≤ 10 ^ 199 * (b + DC) := by
    calc 2 * δ ≤ 2 * (10 ^ 70 * b) := by linarith [hδb]
      _ = 2 * 10 ^ 70 * b := by ring
      _ ≤ 10 ^ 199 * b :=
          mul_le_mul_of_nonneg_right (hperv_cle (by norm_num) (by norm_num)) hbpos.le
      _ ≤ 10 ^ 199 * (b + DC) := mul_le_mul_of_nonneg_left hble (by positivity)
  -- T6 : 1 ≤ 10¹⁹⁹·(b+DC)
  have hT6 : (1:ℝ) ≤ 10 ^ 199 * (b + DC) := by
    calc (1:ℝ) ≤ 10 ^ 70 * DC := hone
      _ ≤ 10 ^ 199 * DC :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by norm_num)) hDCpos.le
      _ ≤ 10 ^ 199 * (b + DC) := mul_le_mul_of_nonneg_left hDCle (by positivity)
  -- combine: product = MQ + M + 2δQ + 2δ + Q + 1 ≤ 6·10¹⁹⁹·(b+DC) ≤ 10²⁰⁰·(b+DC)
  have hexpand : (M + 2 * δ + 1) * (Q + 1)
      = M * Q + M + 2 * δ * Q + 2 * δ + Q + 1 := by ring
  rw [hexpand]
  have hsum : M * Q + M + 2 * δ * Q + 2 * δ + Q + 1 ≤ 6 * (10 ^ 199 * (b + DC)) := by
    linarith [hT1, hT2, hT3, hT4, hT5, hT6]
  refine le_trans hsum ?_
  rw [show (6:ℝ) * (10 ^ 199 * (b + DC)) = (6 * 10 ^ 199) * (b + DC) by ring]
  refine mul_le_mul_of_nonneg_right ?_ hbDC_nn
  have hp : (10:ℝ) ^ 200 = 10 ^ 199 * 10 := pow_succ 10 199
  rw [hp]; nlinarith only [pow_pos (show (0:ℝ) < 10 by norm_num) 199]

/-- **§5 Step-4 per-`(s,v)` r-count `hperv` (FAITHFUL bare `Rδ`, writeup 1086–1088).**  For a
fixed admissible `(s,v)` (the `w`-value, `|w|` large per the v-band), the positions `r ∈ Fib`
lying in the comparable window `[r₀,r₁] ⊆ [R/72, 16R]` with the per-`r` near-integer witness
`distInt(φ_v(r)) ≤ δ` number at most `Cv := 10²⁰⁰·(b + dc/√n)`, the bare `Rδ`-shape of the fibre-sum
route's `hCcol` (with `b = H·G⁵U¹⁵/(Δ²Ω²)`, `dc = G⁴U¹⁵/Ω⁴·√Lr`).

The window/near-integer witness `hFib` is supplied per `r` (e.g. via `phiv_distInt_from_witness`
threaded over the s₄ fibre); the `W ≍ Wstar` bridge `hWhi`/`hWlo` is the `|v| ≍ V_s` analytic
data from the v-band confinement (`W = ℓ₁·X·a·|w|/(D⁴·R)`). -/
theorem step4_hperv {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ w r₀ r₁ δ Lr n : ℝ}
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hδhalf : δ ≤ 1 / 2)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5))
    (hvlarge : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |w|)
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : δ = 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5))
    (hLrlo : 1 ≤ Lr) (hn1 : 1 ≤ n) (hnN : n ≤ 10 ^ 57 * ℓ₁ ^ 2 * Lr * P.U ^ 10 / S.Ω ^ 8)
    (hWhi : ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)
        ≤ 10 ^ 9 * (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt Lr)))
    (hWlo : Real.sqrt n / (S.Δ * S.Ω * Real.sqrt Lr)
        ≤ 10 ^ 9 * (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)))
    (Fib : Finset ℕ)
    (hFib : ∀ r ∈ Fib, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
        distInt (phiv P.X a ℓ₁ ℓ₂ w (r : ℝ)) ≤ δ) :
    (Fib.card : ℝ)
      ≤ 10 ^ 200 * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)
          + P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt Lr / Real.sqrt n) := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hGpos' : 0 < P.G := P.G_pos
  have hUpos' : 0 < P.U := P.U_pos
  have hΩpos' : 0 < S.Ω := S.Ω_pos
  have hΔpos' : 0 < S.Δ := S.Δ_pos
  have hHpos' : 0 < P.H := P.H_pos
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hcard := step4_perv_card_le hAD ha0 ha_lo ha_hi hℓ1pos hℓ12 hvlarge hr0_lo hr01 hr1_hi
    hδ0 Fib hFib
  refine le_trans hcard ?_
  -- derived positivity / window facts
  have hXpos : 0 < P.X := P.X_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hℓ21pos : 0 < ℓ₂ - ℓ₁ := by linarith [hℓ12]
  have hℓ2pos : 0 < ℓ₂ := by linarith [hℓ1pos, hℓ12]
  have hLHSpos : 0 < (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) := by
    apply mul_pos (mul_pos (by norm_num) (div_pos (mul_pos hℓ2pos hℓ21pos) (by positivity)))
    exact div_pos (by positivity) (mul_pos hXpos ha0)
  have hwpos : 0 < |w| := lt_of_lt_of_le hLHSpos hvlarge
  have hnum : 0 < ℓ₁ * P.X * a * |w| := mul_pos (mul_pos (mul_pos hℓ1pos hXpos) ha0) hwpos
  have hWpos : 0 < ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R) :=
    div_pos hnum (mul_pos (pow_pos hDpos 4) hRpos)
  have hlen0 : 0 ≤ r₁ - r₀ := by linarith [hr01]
  have hlenR : r₁ - r₀ ≤ 16 * S.R := by linarith [hr1_hi, hr0_lo, hℓ1pos, hRpos]
  rw [show ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R * 10 ^ 50)
      = (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) / 10 ^ 50 from by rw [div_div]]
  exact perv_countR (P := P) (S := S) (ℓ₁ := ℓ₁) (Lr := Lr)
    (W := ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) (δ := δ) (len := r₁ - r₀) (n := n)
    hG1 hU1 hUbig hΔ1 hH1 hΩU hband hδhalf h1 hDeW hℓ1lo hℓ1W hLrlo hδ hn1 hnN hWpos hWhi
    hWlo hlen0 hlenR

end Squarefree
