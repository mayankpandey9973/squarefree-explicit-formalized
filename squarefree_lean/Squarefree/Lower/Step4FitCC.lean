import Squarefree.Lower.Step4Band5
import Squarefree.Lower.Step4FitCCp3

/-!
# §5 Step-4 cC-slot fit (constant-room budgets)

The two monomial-budget discharges feeding the `cC`-slot of the Step-4 five-slot band
collapse: the `cC·b·N` product and the `cC·dc·2√N` product both fit the `t7'` block
`8·C·(H/Δ)·Δ²G¹⁵U⁹⁰/(HΩ²⁷)`, for the hybrid constant coefficient `cChyb` (the `B³`-monomial
PLUS the re-slotted degree-3 cap piece `4a·Ecap4p3/√L`), the cap `a ≤ 11A`, the
`N ≤ C·ℓ₁²L·U¹⁰/Ω⁸` range cap, and the TRUE-ℓ windows `ℓᵢ ≤ GU⁵`.  Each of the two summands
fits 4 blocks (`step4_fit_cCM_*` + `step4_fit_cCp3_*`), summing to 8.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The `t7'` target block in monomial form: `4C·(H/Δ)·Δ²G¹⁵U⁹⁰/(HΩ²⁷) = 4C·ΔG¹⁵U⁹⁰/Ω²⁷`. -/
private theorem cC_target_eq4 (C : ℝ) :
    4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27))
      = 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 / S.Ω ^ 27 := by
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  field_simp

/-- Monomial cap for the `B³`-part of `cChyb` under `a ≤ 11A`:
`≤ 11·10⁴⁴·Δ³L/(G²HΩ⁶)`. -/
private theorem cChybM_le {a ℓ₁ ℓ₂ : ℝ} (ha_hi : a ≤ 11 * S.A)
    (hL : 0 ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) :
    10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D)
      ≤ 11 * 10 ^ 44 * S.Δ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / (P.G ^ 2 * P.H * S.Ω ^ 6) := by
  have hGpos := P.G_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hid : 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3
        / (S.Δ ^ 3 * S.D)
      = a * (10 ^ 44 * S.Δ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / (P.G ^ 2 * P.H * S.Ω ^ 7)) := by
    rw [show S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) from rfl, show S.D = P.H * S.Δ from rfl]
    field_simp
  rw [hid]
  calc a * (10 ^ 44 * S.Δ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / (P.G ^ 2 * P.H * S.Ω ^ 7))
      ≤ 11 * S.A * (10 ^ 44 * S.Δ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / (P.G ^ 2 * P.H * S.Ω ^ 7)) :=
        mul_le_mul_of_nonneg_right ha_hi (by positivity)
    _ = 11 * 10 ^ 44 * S.Δ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) / (P.G ^ 2 * P.H * S.Ω ^ 6) := by
        unfold Scale.A
        field_simp

/-- **cC-slot `B³`-monomial fit, E-block.** `M·b·N ≤ 4·C·(H/Δ)·t7'`. -/
private theorem step4_fit_cCM_E
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D))
        * b * (N : ℝ)
      ≤ 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hdpos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  set L : ℝ := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]; exact le_of_lt (mul_pos (mul_pos hℓ1pos hℓ2pos) hdpos)
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  -- step 1: cap the coefficient and bound the triple product factorwise
  have hcC : 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D)
      ≤ 11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6) := by
    rw [hLdef]; exact cChybM_le ha_hi (hLdef ▸ hLnn)
  have h12 : 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D) * b
      ≤ (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :=
    mul_le_mul hcC (le_of_eq hb) hbnn (by positivity)
  have hstep : 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D) * b * (N : ℝ)
      ≤ (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) :=
    mul_le_mul h12 hNcap (Nat.cast_nonneg N) (by positivity)
  -- step 2: simplify the product (H cancels)
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have heq : (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
        * (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
      = 11 * 10 ^ 44 * C * P.G ^ 3 * P.U ^ 25 * S.Δ * (ℓ₁ ^ 2 * L ^ 2) / S.Ω ^ 16 := by
    field_simp
  -- step 3: window budgets ℓ₁² ≤ (130·GU⁵)², L² ≤ (130³·G³U¹⁵)²; 130⁸ ≤ 10¹⁷
  have hdle : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hLW : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3 := by
    rw [hLdef]
    have h12m : ℓ₁ * ℓ₂ ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
      mul_le_mul hℓ1W hℓ2W (le_of_lt hℓ2pos) (by positivity)
    calc ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)
        ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
          mul_le_mul h12m hdle (by linarith) (by positivity)
      _ = 130 ^ 3 * (P.G * P.U ^ 5) ^ 3 := by ring
  have hwin : ℓ₁ ^ 2 * L ^ 2 ≤ 10 ^ 17 * (P.G ^ 8 * P.U ^ 40) := by
    have h1sq : ℓ₁ ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hℓ1pos) hℓ1W 2
    have hLsq : L ^ 2 ≤ (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) ^ 2 := pow_le_pow_left₀ hLnn hLW 2
    calc ℓ₁ ^ 2 * L ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) ^ 2 :=
          mul_le_mul h1sq hLsq (by positivity) (by positivity)
      _ = 130 ^ 8 * (P.G ^ 8 * P.U ^ 40) := by ring
      _ ≤ 10 ^ 17 * (P.G ^ 8 * P.U ^ 40) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  -- step 4: scalar budget 11·10⁴⁴·Ω¹¹ ≤ 4·G⁴·U²⁵
  have hΩ11 : S.Ω ^ 11 ≤ P.U ^ 11 := pow_le_pow_left₀ (le_of_lt hΩpos) hΩU 11
  have hU14 : (10:ℝ) ^ 462 ≤ P.U ^ 14 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10 ^ 33) hUbig 14
    calc (10:ℝ) ^ 462 = ((10:ℝ) ^ 33) ^ 14 := by rw [← pow_mul]
      _ ≤ P.U ^ 14 := h
  have hscalar : 11 * 10 ^ 61 * S.Ω ^ 11 ≤ 4 * P.G ^ 3 * P.U ^ 25 := by
    have h46 : (11:ℝ) * 10 ^ 61 ≤ (10:ℝ) ^ 462 := by
      calc (11:ℝ) * 10 ^ 61 ≤ 10 ^ 2 * 10 ^ 61 := by norm_num
        _ = (10:ℝ) ^ 63 := by rw [← pow_add]
        _ ≤ (10:ℝ) ^ 462 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hG4 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    calc 11 * 10 ^ 61 * S.Ω ^ 11 ≤ 11 * 10 ^ 61 * P.U ^ 11 :=
          mul_le_mul_of_nonneg_left hΩ11 (by norm_num)
      _ ≤ (10:ℝ) ^ 462 * P.U ^ 11 := mul_le_mul_of_nonneg_right h46 (by positivity)
      _ ≤ P.U ^ 14 * P.U ^ 11 := mul_le_mul_of_nonneg_right hU14 (by positivity)
      _ = 1 * P.U ^ 25 := by ring
      _ ≤ 4 * P.G ^ 3 * P.U ^ 25 := by
          have h4G : (1:ℝ) ≤ 4 * P.G ^ 3 := by linarith only [hG4]
          exact mul_le_mul_of_nonneg_right h4G (by positivity)
  -- step 5: cross-multiplied comparison
  have hfin : 11 * 10 ^ 44 * C * P.G ^ 3 * P.U ^ 25 * S.Δ
        * (10 ^ 17 * (P.G ^ 8 * P.U ^ 40)) / S.Ω ^ 16
      ≤ 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 / S.Ω ^ 27 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 11 * 10 ^ 44 * C * P.G ^ 3 * P.U ^ 25 * S.Δ * (10 ^ 17 * (P.G ^ 8 * P.U ^ 40))
          * S.Ω ^ 27
        = (11 * 10 ^ 61 * S.Ω ^ 11) * (C * P.G ^ 11 * P.U ^ 65 * S.Δ * S.Ω ^ 16) := by ring
      _ ≤ (4 * P.G ^ 3 * P.U ^ 25) * (C * P.G ^ 11 * P.U ^ 65 * S.Δ * S.Ω ^ 16) :=
          mul_le_mul_of_nonneg_right hscalar (by positivity)
      _ = 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 * S.Ω ^ 16 := by ring
  -- assemble
  calc 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D) * b * (N : ℝ)
      ≤ (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) := hstep
    _ = 11 * 10 ^ 44 * C * P.G ^ 3 * P.U ^ 25 * S.Δ * (ℓ₁ ^ 2 * L ^ 2) / S.Ω ^ 16 := heq
    _ ≤ 11 * 10 ^ 44 * C * P.G ^ 3 * P.U ^ 25 * S.Δ
          * (10 ^ 17 * (P.G ^ 8 * P.U ^ 40)) / S.Ω ^ 16 := by
        gcongr 11 * 10 ^ 44 * C * P.G ^ 3 * P.U ^ 25 * S.Δ * ?_ / S.Ω ^ 16
    _ ≤ 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 / S.Ω ^ 27 := hfin
    _ = 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) :=
        (cC_target_eq4 C).symm

/-- **cC-slot `B³`-monomial fit, F-block.** `M·dc·2√N ≤ 4·C·(H/Δ)·t7'` — keep-net form:
the `√(N-cap)` keeps its `Ω⁻⁴`, and the net `Ω⁻¹⁴` is padded by `Ω¹³ ≤ U¹³` only. -/
private theorem step4_fit_cCM_F
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (dc : ℝ)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) :
    (10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D))
        * dc * (2 * Real.sqrt (N : ℝ))
      ≤ 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hdpos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  set L : ℝ := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact mul_pos (mul_pos hℓ1pos hℓ2pos) hdpos
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hdcnn : 0 ≤ dc := by rw [hdc]; positivity
  -- abbreviate √L (opaque atom from here on)
  set s : ℝ := Real.sqrt L with hsdef
  have hsnn : 0 ≤ s := Real.sqrt_nonneg L
  have hss : s * s = L := Real.mul_self_sqrt hLnn
  -- step 1: cap the coefficient
  have hcC : 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D)
      ≤ 11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6) := by
    rw [hLdef]; exact cChybM_le ha_hi (hLdef ▸ hLnn)
  -- step 2: √ of the FULL N-cap (keep the Ω⁻⁴)
  have hkey : (Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) ^ 2
      = C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8 := by
    have hCs : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hCnn
    calc (Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) ^ 2
        = (Real.sqrt C * Real.sqrt C) * ℓ₁ ^ 2 * (s * s) * P.U ^ 10 / S.Ω ^ 8 := by
          field_simp
      _ = C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8 := by rw [hCs, hss]
  have hsqN : Real.sqrt (N : ℝ) ≤ Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := by
    calc Real.sqrt (N : ℝ) ≤ Real.sqrt (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) :=
          Real.sqrt_le_sqrt hNcap
      _ = Real.sqrt ((Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) ^ 2) := by rw [hkey]
      _ = Real.sqrt C * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := Real.sqrt_sq (by positivity)
  have hsqC : Real.sqrt C ≤ (10:ℝ) ^ 60 := by
    calc Real.sqrt C ≤ Real.sqrt ((10:ℝ) ^ 120) := Real.sqrt_le_sqrt hCcap
      _ = Real.sqrt (((10:ℝ) ^ 60) ^ 2) := by rw [← pow_mul]
      _ = (10:ℝ) ^ 60 := Real.sqrt_sq (by positivity)
  have hsqN' : Real.sqrt (N : ℝ) ≤ (10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := by
    refine le_trans hsqN ?_
    gcongr ?_ * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4
  have h2sq : 2 * Real.sqrt (N : ℝ) ≤ 2 * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) := by
    linarith
  -- step 3: bound the triple product factorwise
  have h12 : 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D) * dc
      ≤ (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
          * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s) :=
    mul_le_mul hcC (le_of_eq hdc) hdcnn (by positivity)
  have hmain : 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D) * dc
        * (2 * Real.sqrt (N : ℝ))
      ≤ (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
          * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s)
          * (2 * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4)) :=
    mul_le_mul h12 h2sq (by positivity) (by positivity)
  -- step 4: simplify the product (s·s = L cancels one √); net Ω-weight Ω⁻¹⁴
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have heqF : (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
        * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s)
        * (2 * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4))
      = 22 * 10 ^ 104 * S.Δ ^ 3 * P.G ^ 2 * P.U ^ 20 * (L ^ 2 * ℓ₁)
          / (P.H * S.Ω ^ 14) := by
    rw [← hss]
    field_simp
    ring
  -- step 5: window budget L²ℓ₁ ≤ 130⁷·G⁷U³⁵ ≤ 10¹⁵·G⁷U³⁵
  have hdle : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hLW : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3 := by
    rw [hLdef]
    have h12m : ℓ₁ * ℓ₂ ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
      mul_le_mul hℓ1W hℓ2W (le_of_lt hℓ2pos) (by positivity)
    calc ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)
        ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
          mul_le_mul h12m hdle (by linarith) (by positivity)
      _ = 130 ^ 3 * (P.G * P.U ^ 5) ^ 3 := by ring
  have hwinF : L ^ 2 * ℓ₁ ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35) := by
    have hLsq : L ^ 2 ≤ (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) ^ 2 := pow_le_pow_left₀ hLnn hLW 2
    calc L ^ 2 * ℓ₁ ≤ (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) ^ 2 * (130 * (P.G * P.U ^ 5)) :=
          mul_le_mul hLsq hℓ1W (le_of_lt hℓ1pos) (by positivity)
      _ = 130 ^ 7 * (P.G ^ 7 * P.U ^ 35) := by ring
      _ ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  -- step 6: scalar budget 22·10¹⁰⁴·Δ²Ω¹³ ≤ 4·G⁶U³⁵·H (Ω¹³ ≤ U¹³ pad only)
  have hU28 : (10:ℝ) ^ 924 ≤ P.U ^ 28 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10 ^ 33) hUbig 28
    calc (10:ℝ) ^ 924 = ((10:ℝ) ^ 33) ^ 28 := by rw [← pow_mul]
      _ ≤ P.U ^ 28 := h
  have h22 : (22:ℝ) * 10 ^ 119 ≤ P.U ^ 28 := by
    calc (22:ℝ) * 10 ^ 119 ≤ 10 ^ 2 * 10 ^ 119 := by norm_num
      _ = (10:ℝ) ^ 121 := by rw [← pow_add]
      _ ≤ (10:ℝ) ^ 924 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ ≤ P.U ^ 28 := hU28
  have hHcap : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := (le_div_iff₀ (by positivity)).mp h1
  have hUΔH : P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
    calc P.U ^ 10 * S.Δ ^ 2 = 1 * (P.U ^ 10 * S.Δ ^ 2) := (one_mul _).symm
      _ ≤ P.G * (P.U ^ 10 * S.Δ ^ 2) :=
          mul_le_mul_of_nonneg_right hG1 (by positivity)
      _ = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
      _ ≤ P.H := hHcap
  have hscalarF : 22 * 10 ^ 119 * (S.Δ ^ 2 * S.Ω ^ 13) ≤ 4 * P.G ^ 5 * P.U ^ 35 * P.H := by
    have hG6 : (1:ℝ) ≤ P.G ^ 5 := one_le_pow₀ hG1
    have hU3135 : P.U ^ 31 ≤ P.U ^ 35 := pow_le_pow_right₀ hU1 (by norm_num)
    calc 22 * 10 ^ 119 * (S.Δ ^ 2 * S.Ω ^ 13)
        ≤ P.U ^ 28 * (S.Δ ^ 2 * S.Ω ^ 13) :=
          mul_le_mul_of_nonneg_right h22 (by positivity)
      _ ≤ P.U ^ 28 * (S.Δ ^ 2 * P.U ^ 13) := by
          have hΩ13 : S.Ω ^ 13 ≤ P.U ^ 13 := pow_le_pow_left₀ (le_of_lt hΩpos) hΩU 13
          gcongr P.U ^ 28 * (S.Δ ^ 2 * ?_)
      _ = P.U ^ 31 * (P.U ^ 10 * S.Δ ^ 2) := by ring
      _ ≤ P.U ^ 31 * P.H := mul_le_mul_of_nonneg_left hUΔH (by positivity)
      _ ≤ P.U ^ 35 * P.H := mul_le_mul_of_nonneg_right hU3135 hHpos.le
      _ = 1 * (P.U ^ 35 * P.H) := (one_mul _).symm
      _ ≤ 4 * P.G ^ 5 * (P.U ^ 35 * P.H) := by
          have h4G : (1:ℝ) ≤ 4 * P.G ^ 5 := by linarith
          exact mul_le_mul_of_nonneg_right h4G (by positivity)
      _ = 4 * P.G ^ 5 * P.U ^ 35 * P.H := by ring
  -- step 7: cross-multiplied comparison
  have hfinF : 22 * 10 ^ 104 * S.Δ ^ 3 * P.G ^ 2 * P.U ^ 20
        * (10 ^ 15 * (P.G ^ 7 * P.U ^ 35)) / (P.H * S.Ω ^ 14)
      ≤ 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 / S.Ω ^ 27 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 22 * 10 ^ 104 * S.Δ ^ 3 * P.G ^ 2 * P.U ^ 20 * (10 ^ 15 * (P.G ^ 7 * P.U ^ 35))
          * S.Ω ^ 27
        = (22 * 10 ^ 119 * (S.Δ ^ 2 * S.Ω ^ 13)) * (S.Δ * P.G ^ 9 * P.U ^ 55 * S.Ω ^ 14) := by
          ring
      _ ≤ (4 * P.G ^ 5 * P.U ^ 35 * P.H) * (S.Δ * P.G ^ 9 * P.U ^ 55 * S.Ω ^ 14) :=
          mul_le_mul_of_nonneg_right hscalarF (by positivity)
      _ = 1 * (4 * S.Δ * P.G ^ 14 * P.U ^ 90 * (P.H * S.Ω ^ 14)) := by ring
      _ ≤ C * (4 * S.Δ * P.G ^ 14 * P.U ^ 90 * (P.H * S.Ω ^ 14)) :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ = 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 * (P.H * S.Ω ^ 14) := by ring
  -- assemble
  calc 10 ^ 44 * a * P.G * S.Ω ^ 2 * L * S.B ^ 3 / (S.Δ ^ 3 * S.D) * dc
        * (2 * Real.sqrt (N : ℝ))
      ≤ (11 * 10 ^ 44 * S.Δ ^ 3 * L / (P.G ^ 2 * P.H * S.Ω ^ 6))
          * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s)
          * (2 * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4)) := hmain
    _ = 22 * 10 ^ 104 * S.Δ ^ 3 * P.G ^ 2 * P.U ^ 20 * (L ^ 2 * ℓ₁)
          / (P.H * S.Ω ^ 14) := heqF
    _ ≤ 22 * 10 ^ 104 * S.Δ ^ 3 * P.G ^ 2 * P.U ^ 20 * (10 ^ 15 * (P.G ^ 7 * P.U ^ 35))
          / (P.H * S.Ω ^ 14) := by
        gcongr 22 * 10 ^ 104 * S.Δ ^ 3 * P.G ^ 2 * P.U ^ 20 * ?_ / (P.H * S.Ω ^ 14)
    _ ≤ 4 * C * S.Δ * P.G ^ 14 * P.U ^ 90 / S.Ω ^ 27 := hfinF
    _ = 4 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) :=
        (cC_target_eq4 C).symm

/-- **cC-slot fit, E-block.** `cC·b·N ≤ 8·C·(H/Δ)·t7'`: the `B³`-monomial part and the
re-slotted p₃ part each fit 4 blocks. -/
theorem step4_fit_cC_E
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    cChyb P S a ℓ₁ ℓ₂ * b * (N : ℝ)
      ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hsplit : cChyb P S a ℓ₁ ℓ₂ * b * (N : ℝ)
      = (10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D))
          * b * (N : ℝ)
        + (4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * b * (N : ℝ) := by
    rw [show cChyb P S a ℓ₁ ℓ₂
        = 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D)
          + 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) from rfl]
    ring
  rw [hsplit]
  have hM := step4_fit_cCM_E (P := P) (S := S) hG1 hU1 hΔ1 hH1 hΩU hUbig N ℓ₁ ℓ₂
    hℓ1lo hℓ12 hℓ1W hℓ2W C hC hNcap a ha_hi b hb
  have hQ := step4_fit_cCp3_E (P := P) (S := S) hG1 hU1 hΔ1 hH1 hΩU hUbig hDeW N ℓ₁ ℓ₂
    hℓ1lo hℓ12 hℓ1W hℓ2W C hC hNcap a ha0 ha_hi b hb
  linarith [hM, hQ]

/-- **cC-slot fit, F-block.** `cC·dc·2√N ≤ 8·C·(H/Δ)·t7'`: the `B³`-monomial part and the
re-slotted p₃ part each fit 4 blocks. -/
theorem step4_fit_cC_F
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
    cChyb P S a ℓ₁ ℓ₂ * dc * (2 * Real.sqrt (N : ℝ))
      ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hsplit : cChyb P S a ℓ₁ ℓ₂ * dc * (2 * Real.sqrt (N : ℝ))
      = (10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D))
          * dc * (2 * Real.sqrt (N : ℝ))
        + (4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * dc
            * (2 * Real.sqrt (N : ℝ)) := by
    rw [show cChyb P S a ℓ₁ ℓ₂
        = 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D)
          + 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) from rfl]
    ring
  rw [hsplit]
  have hM := step4_fit_cCM_F (P := P) (S := S) h1 hG1 hU1 hΔ1 hH1 hΩU hUbig N ℓ₁ ℓ₂
    hℓ1lo hℓ12 hℓ1W hℓ2W C hC hCcap hNcap a ha_hi dc hdc
  have hQ := step4_fit_cCp3_F (P := P) (S := S) h1 hG1 hU1 hΔ1 hH1 hΩU hUbig N ℓ₁ ℓ₂
    hℓ1lo hℓ12 hℓ1W hℓ2W C hC hCcap hNcap a ha0 ha_hi dc hdc
  linarith [hM, hQ]

end Squarefree
