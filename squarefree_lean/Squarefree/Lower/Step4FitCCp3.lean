import Squarefree.Lower.Step4Band5
import Squarefree.Lower.Step4BandPay

/-!
# §5 Step-4 cC-slot fit: the re-slotted degree-3 cap piece

The `4a·Ecap4p3/√L` summand of `cChyb` (the `n`-free degree-3 cap piece, re-slotted out of
the `cE`-slot where its `√n`-weight overshoots the `t6'` block) fits HALF the `t7'` block
in each of the two constant-room products `cC·b·N` and `cC·dc·2√N`.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- Collapse of the re-slotted piece: `4a·Ecap4p3 = 924·10⁷³·a·ℓ₁³ℓ₂(3ℓ₂−2ℓ₁)·U¹⁵/(H·Ω¹¹)`. -/
private theorem cCp3_collapse (a ℓ₁ ℓ₂ : ℝ) :
    4 * a * Ecap4p3 P S ℓ₁ ℓ₂
      = 924 * 10 ^ 73 * a * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 11) := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  have hGne : P.G ≠ 0 := ne_of_gt P.G_pos
  rw [show Ecap4p3 P S ℓ₁ ℓ₂
      = 2 * (77 * (P.G * S.Ω / S.Δ ^ 4)
          * (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (3000000000000 * S.B)
              * (Vmax P S) ^ 3) / S.D) from rfl,
    show Vmax P S = 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) from rfl,
    show S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) from rfl,
    show S.D = P.H * S.Δ from rfl]
  field_simp
  ring

/-- The common window: `ℓ₁³ℓ₂(3ℓ₂−2ℓ₁) ≤ 3·130⁵·G⁵U²⁵ ≤ 3·10¹¹·G⁵U²⁵`. -/
private theorem cCp3_window {ℓ₁ ℓ₂ : ℝ} (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5)) :
    ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) ≤ 3 * 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have h3ℓ0 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have h3W : 3 * ℓ₂ - 2 * ℓ₁ ≤ 3 * (130 * (P.G * P.U ^ 5)) := by linarith
  have h3 : ℓ₁ ^ 3 ≤ (130 * (P.G * P.U ^ 5)) ^ 3 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 3
  calc ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)
      ≤ (130 * (P.G * P.U ^ 5)) ^ 3 * (130 * (P.G * P.U ^ 5))
          * (3 * (130 * (P.G * P.U ^ 5))) := by
        refine mul_le_mul (mul_le_mul h3 hℓ2W hℓ2pos.le (by positivity)) h3W h3ℓ0
          (by positivity)
    _ = 3 * 130 ^ 5 * (P.G ^ 5 * P.U ^ 25) := by ring
    _ ≤ 3 * 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- **cC-slot p₃-fit, E-block.** `(4a·Ecap4p3/√L)·b·N ≤ 4·C·(H/Δ)·t7'`. -/
theorem step4_fit_cCp3_E
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * b * (N : ℝ)
      ≤ 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hdpos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have h3ℓ0 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hA1 : (1:ℝ) ≤ ℓ₁ * ℓ₂ := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ₁ - 1) (by linarith : (0:ℝ) ≤ ℓ₂ - 1)]
  have hL1 : (1:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ₁ * ℓ₂ - 1)
      (by linarith : (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1)]
  have hsL1 : (1:ℝ) ≤ Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := Real.one_le_sqrt.mpr hL1
  have hE0 : (0:ℝ) ≤ Ecap4p3 P S ℓ₁ ℓ₂ := Ecap4p3_nonneg hℓ1lo hℓ12
  have hW0 : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) :=
    mul_nonneg (mul_nonneg (by positivity) hℓ2pos.le) h3ℓ0
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  -- drop the 1/√L (constant room: 1/√L ≤ 1)
  have hdrop : 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
      ≤ 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ :=
    div_le_self (by positivity) hsL1
  -- collapse and cap a ≤ 11ΔΩ
  have hQcap : 4 * a * Ecap4p3 P S ℓ₁ ℓ₂
      ≤ 10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 10) := by
    rw [cCp3_collapse]
    have h1' : 924 * 10 ^ 73 * a * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 11)
        ≤ 924 * 10 ^ 73 * (11 * (S.Δ * S.Ω)) * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 11) := by
      gcongr 924 * 10 ^ 73 * ?_ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
        / (P.H * S.Ω ^ 11)
    refine le_trans h1' (le_of_eq ?_)
    have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
    have hHne : P.H ≠ 0 := ne_of_gt hHpos
    field_simp
    ring
  -- triple product, collected
  have hQb0 : (0:ℝ) ≤ 10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
      / (P.H * S.Ω ^ 10) := by positivity
  have hstep : (4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * b * (N : ℝ)
      ≤ (10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
            / (P.H * S.Ω ^ 10))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8) := by
    rw [hb]
    exact mul_le_mul (mul_le_mul (le_trans hdrop hQcap) le_rfl (by positivity) hQb0)
      hNcap (Nat.cast_nonneg N) (by positivity)
  have heq : (10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
            / (P.H * S.Ω ^ 10))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
      = 10164 * 10 ^ 73 * C * P.G ^ 5 * P.U ^ 40
          * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))
          / (S.Δ * S.Ω ^ 20) := by
    have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
    have hHne : P.H ≠ 0 := ne_of_gt hHpos
    have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
    field_simp
  -- full 10-factor window
  have hwin : ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
      ≤ 3 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50) := by
    have hWp := cCp3_window (P := P) hℓ1lo hℓ12 hℓ1W hℓ2W
    have hrest : ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) := by
      have h2 : ℓ₁ ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 2
      have hd : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
      calc ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
          ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
              * (130 * (P.G * P.U ^ 5))) := by
            refine mul_le_mul h2 ?_ (by positivity) (by positivity)
            exact mul_le_mul (mul_le_mul hℓ1W hℓ2W hℓ2pos.le (by positivity)) hd hdpos.le
              (by positivity)
        _ = 130 ^ 5 * (P.G ^ 5 * P.U ^ 25) := by ring
        _ ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hrest0 : (0:ℝ) ≤ ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by positivity
    calc ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
        ≤ (3 * 10 ^ 11 * (P.G ^ 5 * P.U ^ 25)) * (10 ^ 11 * (P.G ^ 5 * P.U ^ 25)) :=
          mul_le_mul hWp hrest hrest0 (by positivity)
      _ = 3 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50) := by ring
  -- scalar + Δ²-floor cross comparison
  have hΔsq : 10 ^ 54 * (P.G ^ 8 * P.U ^ 40) ≤ S.Δ ^ 2 := by
    calc (10:ℝ) ^ 54 * (P.G ^ 8 * P.U ^ 40) = (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 := by ring
      _ ≤ S.Δ ^ 2 := pow_le_pow_left₀ (by positivity) hDeW 2
  have hΩ7 : S.Ω ^ 7 ≤ P.U ^ 7 := pow_le_pow_left₀ hΩpos.le hΩU 7
  have hsc : 30492 * 10 ^ 95 * P.U ^ 7 ≤ 4 * (10 ^ 54 * (P.G ^ 8 * P.U ^ 40)) := by
    have hU33 : (30492:ℝ) * 10 ^ 41 ≤ P.U ^ 33 := by
      calc (30492:ℝ) * 10 ^ 41 ≤ (10:ℝ) ^ 46 := by norm_num
        _ ≤ (10:ℝ) ^ 1089 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 33 := by rw [← pow_mul]
        _ ≤ P.U ^ 33 := pow_le_pow_left₀ (by norm_num) hUbig 33
    have hG8 : (1:ℝ) ≤ P.G ^ 8 := one_le_pow₀ hG1
    calc 30492 * 10 ^ 95 * P.U ^ 7 = 10 ^ 54 * (30492 * 10 ^ 41) * P.U ^ 7 := by ring
      _ ≤ 10 ^ 54 * P.U ^ 33 * P.U ^ 7 := by gcongr 10 ^ 54 * ?_ * P.U ^ 7
      _ = 10 ^ 54 * (1 * P.U ^ 40) := by ring
      _ ≤ 10 ^ 54 * (P.G ^ 8 * P.U ^ 40) := by gcongr 10 ^ 54 * (?_ * P.U ^ 40)
      _ ≤ 4 * (10 ^ 54 * (P.G ^ 8 * P.U ^ 40)) := by
          nlinarith [mul_pos (pow_pos hGpos 8) (pow_pos hUpos 40)]
  have hfin : 10164 * 10 ^ 73 * C * P.G ^ 5 * P.U ^ 40 * (3 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50))
        / (S.Δ * S.Ω ^ 20)
      ≤ 4 * C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 10164 * 10 ^ 73 * C * P.G ^ 5 * P.U ^ 40 * (3 * 10 ^ 22 * (P.G ^ 10 * P.U ^ 50))
          * S.Ω ^ 27
        = (30492 * 10 ^ 95 * S.Ω ^ 7) * (C * P.G ^ 15 * P.U ^ 90 * S.Ω ^ 20) := by ring
      _ ≤ (30492 * 10 ^ 95 * P.U ^ 7) * (C * P.G ^ 15 * P.U ^ 90 * S.Ω ^ 20) := by
          gcongr (30492 * 10 ^ 95 * ?_) * (C * P.G ^ 15 * P.U ^ 90 * S.Ω ^ 20)
      _ ≤ (4 * (10 ^ 54 * (P.G ^ 8 * P.U ^ 40))) * (C * P.G ^ 15 * P.U ^ 90 * S.Ω ^ 20) :=
          mul_le_mul_of_nonneg_right hsc (by positivity)
      _ ≤ (4 * S.Δ ^ 2) * (C * P.G ^ 15 * P.U ^ 90 * S.Ω ^ 20) := by
          have := mul_le_mul_of_nonneg_left hΔsq (by norm_num : (0:ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = 4 * C * S.Δ * P.G ^ 15 * P.U ^ 90 * (S.Δ * S.Ω ^ 20) := by ring
  -- assemble
  have htgt : 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27))
      = 4 * C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
    have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
    have hHne : P.H ≠ 0 := ne_of_gt hHpos
    have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
    field_simp
  rw [htgt]
  refine le_trans (hstep.trans (le_of_eq heq)) (le_trans ?_ hfin)
  gcongr 10164 * 10 ^ 73 * C * P.G ^ 5 * P.U ^ 40 * ?_ / (S.Δ * S.Ω ^ 20)

/-- **cC-slot p₃-fit, F-block.** `(4a·Ecap4p3/√L)·dc·2√N ≤ 4·C·(H/Δ)·t7'`. -/
theorem step4_fit_cCp3_F
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (dc : ℝ)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) :
    (4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * dc
        * (2 * Real.sqrt (N : ℝ))
      ≤ 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hdpos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have h3ℓ0 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hL0 : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  have hA1 : (1:ℝ) ≤ ℓ₁ * ℓ₂ := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ₁ - 1) (by linarith : (0:ℝ) ≤ ℓ₂ - 1)]
  have hL1 : (1:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ₁ * ℓ₂ - 1)
      (by linarith : (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1)]
  have hE0 : (0:ℝ) ≤ Ecap4p3 P S ℓ₁ ℓ₂ := Ecap4p3_nonneg hℓ1lo hℓ12
  have hW0 : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) :=
    mul_nonneg (mul_nonneg (by positivity) hℓ2pos.le) h3ℓ0
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  -- √L cancellation against dc
  have hsLpos : (0:ℝ) < Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := Real.sqrt_pos.mpr hL0
  have hcancel : (4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * dc
        * (2 * Real.sqrt (N : ℝ))
      = (4 * a * Ecap4p3 P S ℓ₁ ℓ₂) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4)
        * (2 * Real.sqrt (N : ℝ)) := by
    rw [hdc]
    have hs : Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≠ 0 := ne_of_gt hsLpos
    field_simp
  rw [hcancel]
  -- √N keep-net cap: 2√N ≤ 2·10⁶⁰·ℓ₁·L·U⁵/Ω⁴ (√L ≤ L)
  have hsqN : Real.sqrt (N : ℝ)
      ≤ 10 ^ 60 * ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4 := by
    have hCs : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hCnn
    have hss : Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
        = ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := Real.mul_self_sqrt hL0.le
    have hkey : (Real.sqrt C * ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4) ^ 2
        = C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8 := by
      calc (Real.sqrt C * ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4) ^ 2
          = (Real.sqrt C * Real.sqrt C) * ℓ₁ ^ 2
              * (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
              * P.U ^ 10 / S.Ω ^ 8 := by
            field_simp
        _ = C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8 := by rw [hCs, hss]
    have h1s : Real.sqrt (N : ℝ)
        ≤ Real.sqrt C * ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4 := by
      calc Real.sqrt (N : ℝ)
          ≤ Real.sqrt (C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8) :=
            Real.sqrt_le_sqrt hNcap
        _ = Real.sqrt ((Real.sqrt C * ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5
              / S.Ω ^ 4) ^ 2) := by rw [hkey]
        _ = Real.sqrt C * ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4 :=
            Real.sqrt_sq (by positivity)
    have hsqC : Real.sqrt C ≤ (10:ℝ) ^ 60 := by
      calc Real.sqrt C ≤ Real.sqrt ((10:ℝ) ^ 120) := Real.sqrt_le_sqrt hCcap
        _ = Real.sqrt (((10:ℝ) ^ 60) ^ 2) := by rw [← pow_mul]
        _ = (10:ℝ) ^ 60 := Real.sqrt_sq (by positivity)
    have hsl : Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) :=
      (Real.sqrt_le_left hL0.le).mpr
        (by nlinarith [mul_le_mul_of_nonneg_left hL1 hL0.le])
    calc Real.sqrt (N : ℝ)
        ≤ Real.sqrt C * ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4 := h1s
      _ ≤ 10 ^ 60 * ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4 := by
          gcongr ?_ * ℓ₁ * ?_ * P.U ^ 5 / S.Ω ^ 4
  -- collapse + a-cap + collect
  have hQcap : 4 * a * Ecap4p3 P S ℓ₁ ℓ₂
      ≤ 10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 10) := by
    rw [cCp3_collapse]
    have h1' : 924 * 10 ^ 73 * a * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 11)
        ≤ 924 * 10 ^ 73 * (11 * (S.Δ * S.Ω)) * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
          / (P.H * S.Ω ^ 11) := by
      gcongr 924 * 10 ^ 73 * ?_ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
        / (P.H * S.Ω ^ 11)
    refine le_trans h1' (le_of_eq ?_)
    have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
    have hHne : P.H ≠ 0 := ne_of_gt hHpos
    field_simp
    ring
  have hQcap0 : (0:ℝ) ≤ 10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
      / (P.H * S.Ω ^ 10) := by positivity
  have hstep : (4 * a * Ecap4p3 P S ℓ₁ ℓ₂) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4)
        * (2 * Real.sqrt (N : ℝ))
      ≤ (10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
            / (P.H * S.Ω ^ 10))
          * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4)
          * (2 * (10 ^ 60 * ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4)) := by
    refine mul_le_mul (mul_le_mul hQcap le_rfl (by positivity) hQcap0) ?_
      (by positivity) (by positivity)
    linarith [hsqN]
  have heq : (10164 * 10 ^ 73 * S.Δ * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * P.U ^ 15
            / (P.H * S.Ω ^ 10))
          * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4)
          * (2 * (10 ^ 60 * ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 5 / S.Ω ^ 4))
      = 20328 * 10 ^ 133 * S.Δ * P.G ^ 4 * P.U ^ 35
          * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))
          / (P.H * S.Ω ^ 18) := by
    have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
    have hHne : P.H ≠ 0 := ne_of_gt hHpos
    field_simp
    ring
  -- 9-factor window
  have hwin : ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
      ≤ 3 * 10 ^ 20 * (P.G ^ 9 * P.U ^ 45) := by
    have hWp := cCp3_window (P := P) hℓ1lo hℓ12 hℓ1W hℓ2W
    have hd : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
    have hrest : ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≤ 10 ^ 9 * (P.G ^ 4 * P.U ^ 20) := by
      calc ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
          ≤ (130 * (P.G * P.U ^ 5)) * ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
              * (130 * (P.G * P.U ^ 5))) := by
            refine mul_le_mul hℓ1W ?_ (by positivity) (by positivity)
            exact mul_le_mul (mul_le_mul hℓ1W hℓ2W hℓ2pos.le (by positivity)) hd hdpos.le
              (by positivity)
        _ = 130 ^ 4 * (P.G ^ 4 * P.U ^ 20) := by ring
        _ ≤ 10 ^ 9 * (P.G ^ 4 * P.U ^ 20) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hrest0 : (0:ℝ) ≤ ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by positivity
    calc ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * (ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
        ≤ (3 * 10 ^ 11 * (P.G ^ 5 * P.U ^ 25)) * (10 ^ 9 * (P.G ^ 4 * P.U ^ 20)) :=
          mul_le_mul hWp hrest hrest0 (by positivity)
      _ = 3 * 10 ^ 20 * (P.G ^ 9 * P.U ^ 45) := by ring
  -- final cross comparison: 60984·10¹³³·U⁸⁹ ≤ 4·U⁹⁰·H with H ≥ U¹⁰
  have hU10H : P.U ^ 10 ≤ P.H := by
    have hHcap : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := (le_div_iff₀ (by positivity)).mp h1
    have hGΔ2 : (1:ℝ) ≤ P.G * S.Δ ^ 2 := by
      nlinarith [one_le_pow₀ hΔ1 (n := 2), hG1]
    nlinarith [hHcap, pow_pos hUpos 10]
  have hΩ9 : S.Ω ^ 9 ≤ P.U ^ 9 := pow_le_pow_left₀ hΩpos.le hΩU 9
  have hfin : 20328 * 10 ^ 133 * S.Δ * P.G ^ 4 * P.U ^ 35
        * (3 * 10 ^ 20 * (P.G ^ 9 * P.U ^ 45)) / (P.H * S.Ω ^ 18)
      ≤ 4 * C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsc : 60984 * 10 ^ 153 * P.U ^ 9 ≤ 4 * P.U ^ 10 * P.H := by
      have hU11 : (60984:ℝ) * 10 ^ 153 ≤ P.U ^ 11 := by
        calc (60984:ℝ) * 10 ^ 153 ≤ (10:ℝ) ^ 158 := by norm_num
          _ ≤ (10:ℝ) ^ 363 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ = ((10:ℝ) ^ 33) ^ 11 := by rw [← pow_mul]
          _ ≤ P.U ^ 11 := pow_le_pow_left₀ (by norm_num) hUbig 11
      calc 60984 * 10 ^ 153 * P.U ^ 9 ≤ P.U ^ 11 * P.U ^ 9 :=
            mul_le_mul_of_nonneg_right hU11 (by positivity)
        _ = P.U ^ 10 * P.U ^ 10 := by ring
        _ ≤ P.U ^ 10 * P.H := mul_le_mul_of_nonneg_left hU10H (by positivity)
        _ ≤ 4 * P.U ^ 10 * P.H := by nlinarith [mul_pos (pow_pos hUpos 10) hHpos]
    calc 20328 * 10 ^ 133 * S.Δ * P.G ^ 4 * P.U ^ 35 * (3 * 10 ^ 20 * (P.G ^ 9 * P.U ^ 45))
          * S.Ω ^ 27
        = (60984 * 10 ^ 153 * S.Ω ^ 9) * (S.Δ * P.G ^ 13 * P.U ^ 80 * S.Ω ^ 18) := by ring
      _ ≤ (60984 * 10 ^ 153 * P.U ^ 9) * (S.Δ * P.G ^ 13 * P.U ^ 80 * S.Ω ^ 18) := by
          gcongr (60984 * 10 ^ 153 * ?_) * (S.Δ * P.G ^ 13 * P.U ^ 80 * S.Ω ^ 18)
      _ ≤ (4 * P.U ^ 10 * P.H) * (S.Δ * P.G ^ 13 * P.U ^ 80 * S.Ω ^ 18) :=
          mul_le_mul_of_nonneg_right hsc (by positivity)
      _ = 4 * 1 * S.Δ * P.G ^ 13 * P.U ^ 90 * (P.H * S.Ω ^ 18) := by ring
      _ ≤ 4 * C * S.Δ * P.G ^ 15 * P.U ^ 90 * (P.H * S.Ω ^ 18) := by
          have hG1315 : P.G ^ 13 ≤ P.G ^ 15 := pow_le_pow_right₀ hG1 (by norm_num)
          gcongr 4 * ?_ * S.Δ * ?_ * P.U ^ 90 * (P.H * S.Ω ^ 18)
  -- assemble
  have htgt : 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27))
      = 4 * C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
    have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
    have hHne : P.H ≠ 0 := ne_of_gt hHpos
    have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
    field_simp
  rw [htgt]
  refine le_trans (hstep.trans (le_of_eq heq)) (le_trans ?_ hfin)
  gcongr 20328 * 10 ^ 133 * S.Δ * P.G ^ 4 * P.U ^ 35 * ?_ / (P.H * S.Ω ^ 18)

end Squarefree
