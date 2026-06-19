import Squarefree.Lower.Step4SsumAdd

/-!
# §5 Step-4 cubic E-part fit (`E_cubic` confinement budgets)

The two monomial-budget discharges feeding the cubic-confinement variant of the Step-4
additive s-sum collapse: the `c_E·b·N²` product fits the `t6'` block and the
`c_E·dc·N√N` product fits the `t7'` block, for the cubic E-coefficient cap
`c_E ≤ 10¹⁸·G·Ω⁵/(ℓ₁L)`, the `N ≤ C·ℓ₁²L·U¹⁰/Ω⁸` range cap (`C ≤ 10¹²⁰`), and the
TRUE-ℓ windows `ℓ₁ ≤ GU⁵`, `L ≤ (GU⁵)³`.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **Cubic E-part fit, A-block.** `c_E·b·N² ≤ 8·C·(H/Δ)·t6'` for the cubic confinement
coefficient cap, the Step-4 range cap on `N`, and the TRUE-ℓ windows. -/
theorem step4_fit_cubic_A
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ) (ℓ₁ L : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hLlo : 1 ≤ L)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hLW3 : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3)
    (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
    (b cE₂ : ℝ)
    (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
    (hcE₂ : cE₂ ≤ 10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L)) :
    cE₂ * b * (N : ℝ) ^ 2
      ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le one_pos hLlo
  have hℓ1ne : ℓ₁ ≠ 0 := ne_of_gt hℓ1pos
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  -- step 1: square the N-cap
  have hN2 : ((N : ℝ)) ^ 2 ≤ (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg N) hNcap 2
  -- step 2: bound the triple product factorwise
  have hstep : cE₂ * b * (N : ℝ) ^ 2
      ≤ (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) ^ 2 := by
    have h12 : cE₂ * b ≤ (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :=
      mul_le_mul hcE₂ (le_of_eq hb) hbnn (by positivity)
    exact mul_le_mul h12 hN2 (by positivity) (by positivity)
  -- step 3: simplify the product (all denominators positive)
  have heq : (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
        * (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) ^ 2
      = 10 ^ 18 * C ^ 2 * P.H * P.G ^ 6 * P.U ^ 35 * (ℓ₁ ^ 3 * L)
          / (S.Δ ^ 2 * S.Ω ^ 13) := by
    field_simp
  -- step 4: ℓ₁³·L window budget (the `130⁶ ≤ 10¹³` window constant rides into the scalar)
  have hl3L : ℓ₁ ^ 3 * L ≤ 10 ^ 13 * (P.G ^ 6 * P.U ^ 30) := by
    have h13 : ℓ₁ ^ 3 ≤ (130 * (P.G * P.U ^ 5)) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hℓ1pos) hℓ1W 3
    calc ℓ₁ ^ 3 * L ≤ (130 * (P.G * P.U ^ 5)) ^ 3 * (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) :=
          mul_le_mul h13 hLW3 (le_of_lt hLpos) (by positivity)
      _ = 130 ^ 6 * (P.G ^ 6 * P.U ^ 30) := by ring
      _ ≤ 10 ^ 13 * (P.G ^ 6 * P.U ^ 30) := by
          nlinarith only [pow_pos hGpos 6, pow_pos hUpos 30]
  -- step 5: scalar budget 10¹⁸·C ≤ 8·G³·U¹⁰
  have hU10 : (10:ℝ) ^ 330 ≤ P.U ^ 10 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10 ^ 33) hUbig 10
    calc (10:ℝ) ^ 330 = ((10:ℝ) ^ 33) ^ 10 := by rw [← pow_mul]
      _ ≤ P.U ^ 10 := h
  have hscalar : (10:ℝ) ^ 31 * C ≤ 8 * P.G ^ 3 * P.U ^ 10 := by
    have hC138 : (10:ℝ) ^ 31 * C ≤ (10:ℝ) ^ 151 := by
      calc (10:ℝ) ^ 31 * C ≤ (10:ℝ) ^ 31 * (10:ℝ) ^ 120 :=
            mul_le_mul_of_nonneg_left hCcap (by positivity)
        _ = (10:ℝ) ^ 151 := by rw [← pow_add]
    have h138 : (10:ℝ) ^ 151 ≤ (10:ℝ) ^ 330 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    have hGU : (1:ℝ) * P.U ^ 10 ≤ P.G ^ 3 * P.U ^ 10 :=
      mul_le_mul_of_nonneg_right hG3 (le_of_lt (pow_pos hUpos 10))
    calc (10:ℝ) ^ 31 * C ≤ (10:ℝ) ^ 151 := hC138
      _ ≤ (10:ℝ) ^ 330 := h138
      _ ≤ P.U ^ 10 := hU10
      _ = 1 * P.U ^ 10 := (one_mul _).symm
      _ ≤ P.G ^ 3 * P.U ^ 10 := hGU
      _ ≤ 8 * (P.G ^ 3 * P.U ^ 10) :=
          le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = 8 * P.G ^ 3 * P.U ^ 10 := by ring
  -- assemble
  calc cE₂ * b * (N : ℝ) ^ 2
      ≤ (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8) ^ 2 := hstep
    _ = 10 ^ 18 * C ^ 2 * P.H * P.G ^ 6 * P.U ^ 35 * (ℓ₁ ^ 3 * L)
          / (S.Δ ^ 2 * S.Ω ^ 13) := heq
    _ ≤ 10 ^ 18 * C ^ 2 * P.H * P.G ^ 6 * P.U ^ 35 * (10 ^ 13 * (P.G ^ 6 * P.U ^ 30))
          / (S.Δ ^ 2 * S.Ω ^ 13) := by
        gcongr 10 ^ 18 * C ^ 2 * P.H * P.G ^ 6 * P.U ^ 35 * ?_ / (S.Δ ^ 2 * S.Ω ^ 13)
    _ = (10 ^ 31 * C) * (C * P.H * P.G ^ 12 * P.U ^ 65) / (S.Δ ^ 2 * S.Ω ^ 13) := by
        ring
    _ ≤ (8 * P.G ^ 3 * P.U ^ 10) * (C * P.H * P.G ^ 12 * P.U ^ 65)
          / (S.Δ ^ 2 * S.Ω ^ 13) := by
        gcongr ?_ * (C * P.H * P.G ^ 12 * P.U ^ 65) / (S.Δ ^ 2 * S.Ω ^ 13)
    _ = 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by
        field_simp

/-- **Cubic E-part fit, B-block.** `c_E·dc·N√N ≤ 8·C·(H/Δ)·t7'` for the cubic confinement
coefficient cap, the Step-4 range cap on `N`, and the TRUE-ℓ windows. -/
theorem step4_fit_cubic_B
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ) (ℓ₁ L : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hLlo : 1 ≤ L)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hLW3 : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3)
    (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
    (dc cE₂ : ℝ)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt L)
    (hcE₂ : cE₂ ≤ 10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L)) :
    cE₂ * dc * ((N : ℝ) * Real.sqrt (N : ℝ))
      ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le one_pos hLlo
  have hℓ1ne : ℓ₁ ≠ 0 := ne_of_gt hℓ1pos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hdcnn : 0 ≤ dc := by rw [hdc]; positivity
  -- abbreviate √L (opaque atom from here on)
  set s : ℝ := Real.sqrt L with hsdef
  have hsnn : 0 ≤ s := Real.sqrt_nonneg L
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hss : s * s = L := Real.mul_self_sqrt (le_of_lt hLpos)
  -- step 1: take square roots of the FULL N-cap (keep the Ω⁻⁴)
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
  -- step 2: √C ≤ 10⁶⁰
  have hsqC : Real.sqrt C ≤ (10:ℝ) ^ 60 := by
    calc Real.sqrt C ≤ Real.sqrt ((10:ℝ) ^ 120) := Real.sqrt_le_sqrt hCcap
      _ = Real.sqrt (((10:ℝ) ^ 60) ^ 2) := by rw [← pow_mul]
      _ = (10:ℝ) ^ 60 := Real.sqrt_sq (by positivity)
  have hsqN' : Real.sqrt (N : ℝ) ≤ (10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4 := by
    refine le_trans hsqN ?_
    gcongr ?_ * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4
  -- step 3: bound the quadruple product factorwise
  have hNsqN : (N : ℝ) * Real.sqrt (N : ℝ)
      ≤ (C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
          * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4) :=
    mul_le_mul hNcap hsqN' (Real.sqrt_nonneg _) (by positivity)
  have hmain : cE₂ * dc * ((N : ℝ) * Real.sqrt (N : ℝ))
      ≤ (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L)) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s)
          * ((C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
              * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4)) := by
    have h12 : cE₂ * dc ≤ (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L))
        * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s) :=
      mul_le_mul hcE₂ (le_of_eq hdc) hdcnn (by positivity)
    exact mul_le_mul h12 hNsqN (by positivity) (by positivity)
  -- step 4: simplify the product (√L·√L = L cancels the 1/L); net Ω-weight Ω⁻¹¹
  have heqB : (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L)) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s)
        * ((C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
            * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4))
      = 10 ^ 78 * C * P.G ^ 5 * P.U ^ 30 * (ℓ₁ ^ 2 * L) / S.Ω ^ 11 := by
    rw [← hss]
    field_simp
  -- step 5: window budgets ℓ₁² ≤ 130²·G²U¹⁰, L ≤ 130³·G³U¹⁵ (the `130⁵ ≤ 10¹¹` rides)
  have hl2L : ℓ₁ ^ 2 * L ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) := by
    have h12 : ℓ₁ ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hℓ1pos) hℓ1W 2
    calc ℓ₁ ^ 2 * L ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 ^ 3 * (P.G * P.U ^ 5) ^ 3) :=
          mul_le_mul h12 hLW3 (le_of_lt hLpos) (by positivity)
      _ = 130 ^ 5 * (P.G ^ 5 * P.U ^ 25) := by ring
      _ ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) := by
          nlinarith only [pow_pos hGpos 5, pow_pos hUpos 25]
  -- step 6: scalar budget 10⁸³·C·G¹⁰·U⁷¹ ≤ 8·C·Δ·G¹⁵·U⁹⁰ (U¹⁶ pad already spent)
  have hU8 : (10:ℝ) ^ 89 ≤ P.U ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10 ^ 33) hUbig 8
    calc (10:ℝ) ^ 89 ≤ (10:ℝ) ^ 264 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((10:ℝ) ^ 33) ^ 8 := by rw [← pow_mul]
      _ ≤ P.U ^ 8 := h
  have hfin : 10 ^ 89 * C * P.G ^ 10 * P.U ^ 71 ≤ 8 * C * S.Δ * P.G ^ 15 * P.U ^ 90 := by
    have hG1015 : P.G ^ 10 ≤ P.G ^ 15 := pow_le_pow_right₀ hG1 (by norm_num)
    have hU7990 : P.U ^ 79 ≤ P.U ^ 90 := pow_le_pow_right₀ hU1 (by norm_num)
    calc 10 ^ 89 * C * P.G ^ 10 * P.U ^ 71
        ≤ P.U ^ 8 * C * P.G ^ 10 * P.U ^ 71 := by gcongr ?_ * C * P.G ^ 10 * P.U ^ 71
      _ = C * P.G ^ 10 * P.U ^ 79 := by ring
      _ ≤ C * P.G ^ 15 * P.U ^ 90 := by gcongr C * ?_ * ?_
      _ = 1 * (C * P.G ^ 15 * P.U ^ 90) := (one_mul _).symm
      _ ≤ (8 * S.Δ) * (C * P.G ^ 15 * P.U ^ 90) := by
          have h8Δ : (1:ℝ) ≤ 8 * S.Δ := by linarith
          exact mul_le_mul_of_nonneg_right h8Δ (by positivity)
      _ = 8 * C * S.Δ * P.G ^ 15 * P.U ^ 90 := by ring
  -- step 7: keep-net cross-multiplied comparison — pad Ω¹⁶ ≤ U¹⁶ (hΩU only)
  have hΩ16 : S.Ω ^ 16 ≤ P.U ^ 16 := pow_le_pow_left₀ (le_of_lt hΩpos) hΩU 16
  have hcross : 10 ^ 89 * C * P.G ^ 10 * P.U ^ 55 / S.Ω ^ 11
      ≤ 8 * C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 10 ^ 89 * C * P.G ^ 10 * P.U ^ 55 * S.Ω ^ 27
        = (10 ^ 89 * C * P.G ^ 10 * P.U ^ 55 * S.Ω ^ 16) * S.Ω ^ 11 := by ring
      _ ≤ (10 ^ 89 * C * P.G ^ 10 * P.U ^ 55 * P.U ^ 16) * S.Ω ^ 11 := by
          gcongr (10 ^ 89 * C * P.G ^ 10 * P.U ^ 55 * ?_) * S.Ω ^ 11
      _ = (10 ^ 89 * C * P.G ^ 10 * P.U ^ 71) * S.Ω ^ 11 := by ring
      _ ≤ (8 * C * S.Δ * P.G ^ 15 * P.U ^ 90) * S.Ω ^ 11 :=
          mul_le_mul_of_nonneg_right hfin (by positivity)
  -- assemble
  calc cE₂ * dc * ((N : ℝ) * Real.sqrt (N : ℝ))
      ≤ (10 ^ 18 * P.G * S.Ω ^ 5 / (ℓ₁ * L)) * (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * s)
          * ((C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
              * ((10:ℝ) ^ 60 * ℓ₁ * s * P.U ^ 5 / S.Ω ^ 4)) :=
        hmain
    _ = 10 ^ 78 * C * P.G ^ 5 * P.U ^ 30 * (ℓ₁ ^ 2 * L) / S.Ω ^ 11 := heqB
    _ ≤ 10 ^ 78 * C * P.G ^ 5 * P.U ^ 30 * (10 ^ 11 * (P.G ^ 5 * P.U ^ 25)) / S.Ω ^ 11 := by
        gcongr 10 ^ 78 * C * P.G ^ 5 * P.U ^ 30 * ?_ / S.Ω ^ 11
    _ = 10 ^ 89 * C * P.G ^ 10 * P.U ^ 55 / S.Ω ^ 11 := by ring
    _ ≤ 8 * C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := hcross
    _ = 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
        field_simp

end Squarefree
