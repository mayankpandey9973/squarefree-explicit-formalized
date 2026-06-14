import Squarefree.Lower.Step4FitEACore

/-!
# §5 Step-4 hybrid E-part fit, A-half (`T1`/`T2` summand budgets)

The first two `cEhyb` summand-numerator products `Tᵢ·b·m` fit the `C²·(H/Δ)·t-block`
targets, for the abstract `(N·√N)/√L`-cap `m ≤ 10⁶⁰·C·ℓ₁³·L·U²⁵/Ω⁸`.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **Hybrid fit, T1 summand.** The gap-summand product `T1·b·m` fits twice the
`C²·(H/Δ)`-block, splitting the gap into its g₁/g₂ pieces. -/
theorem step4_fitEA_T1
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8)
    (hm0 : 0 ≤ m)
    (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (gap : ℝ) (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
        + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * m
      ≤ 2 * (C ^ 2 * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hd0 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hℓ1ne : ℓ₁ ≠ 0 := ne_of_gt hℓ1pos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hGne : P.G ≠ 0 := ne_of_gt hGpos
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  -- step 1: factorwise product bound
  have hcoef : 10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2
      ≤ 10 ^ 10 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3
          * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
             + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) / S.Δ ^ 2 := by
    have hag : a * gap ≤ 11 * (S.Δ * S.Ω)
        * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
           + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) :=
      mul_le_mul ha' hgap hgap0 (by positivity)
    calc 10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2
        = 10 ^ 10 * P.G * S.Ω ^ 3 * (a * gap) / S.Δ ^ 2 := by ring
      _ ≤ 10 ^ 10 * P.G * S.Ω ^ 3 * (11 * (S.Δ * S.Ω)
            * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
               + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))) / S.Δ ^ 2 := by
          gcongr 10 ^ 10 * P.G * S.Ω ^ 3 * ?_ / S.Δ ^ 2
      _ = 10 ^ 10 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3
            * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
               + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) / S.Δ ^ 2 := by ring
  have hprod : (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * m
      ≤ (10 ^ 10 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3
          * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
             + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) / S.Δ ^ 2)
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8) := by
    rw [hb]
    exact mul_le_mul (mul_le_mul hcoef le_rfl (by positivity) (by positivity)) hm hm0
      (by positivity)
  -- step 2: split into the two monomial pieces
  have hsplit : (10 ^ 10 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3
          * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
             + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) / S.Δ ^ 2)
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8)
      = 22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40
            * (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) / (S.Δ ^ 2 * S.Ω ^ 9)
        + 11 * 10 ^ 83 * C * P.G ^ 5 * P.U ^ 40
            * (ℓ₁ ^ 4 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) / S.Ω ^ 12 := by
    field_simp
    ring
  -- step 3: windows
  have hW1 : ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) := by
    calc ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) = ℓ₁ ^ 3 * ℓ₂ ^ 1 * (ℓ₂ - ℓ₁) := by ring
      _ ≤ 130 ^ (3 + 1 + 1)
            * ((P.G * P.U ^ 5) ^ 3 * (P.G * P.U ^ 5) ^ 1 * (P.G * P.U ^ 5)) :=
          step4_fitEA_window ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W 3 1
      _ = 130 ^ 5 * (P.G ^ 5 * P.U ^ 25) := by ring
      _ ≤ 10 ^ 11 * (P.G ^ 5 * P.U ^ 25) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hW2 : ℓ₁ ^ 4 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35) := by
    calc ℓ₁ ^ 4 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) = ℓ₁ ^ 5 * ℓ₂ ^ 1 * (ℓ₂ - ℓ₁) := by ring
      _ ≤ 130 ^ (5 + 1 + 1)
            * ((P.G * P.U ^ 5) ^ 5 * (P.G * P.U ^ 5) ^ 1 * (P.G * P.U ^ 5)) :=
          step4_fitEA_window ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W 5 1
      _ = 130 ^ 7 * (P.G ^ 7 * P.U ^ 35) := by ring
      _ ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hW20 : 0 ≤ ℓ₁ ^ 4 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) :=
    mul_nonneg (pow_nonneg hℓ1pos.le 4)
      (mul_nonneg (mul_nonneg hℓ1pos.le hℓ2pos.le) hd0)
  -- step 4: assemble
  calc (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * m
      ≤ (10 ^ 10 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3
          * (2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
             + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) / S.Δ ^ 2)
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8) := hprod
    _ = 22 * 10 ^ 82 * C * P.H * P.G ^ 6 * P.U ^ 40
            * (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) / (S.Δ ^ 2 * S.Ω ^ 9)
        + 11 * 10 ^ 83 * C * P.G ^ 5 * P.U ^ 40
            * (ℓ₁ ^ 4 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) / S.Ω ^ 12 := hsplit
    _ ≤ C ^ 2 * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13)
        + C ^ 2 * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) :=
        add_le_add (step4_fitEA_coreA hG1 hΩU hUbig C hC _ hW1)
          (step4_fitEA_coreB h1 hG1 hΩU hUbig C hC _ _ (by norm_num) hW20 hW2)
    _ = 2 * (C ^ 2 * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))) := by
        field_simp
        ring

/-- **Hybrid fit, T2 summand.** The `ℓ₂·B²/D`-summand product `T2·b·m` fits the
`C²·(H/Δ)`-block. -/
theorem step4_fitEA_T2
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8)
    (hm0 : 0 ≤ m)
    (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)) * b * m
      ≤ C ^ 2 * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hd0 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hCnn : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hℓ1ne : ℓ₁ ≠ 0 := ne_of_gt hℓ1pos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hGne : P.G ≠ 0 := ne_of_gt hGpos
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  rw [show S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) from rfl, show S.D = P.H * S.Δ from rfl, hb]
  -- step 1: factorwise product bound
  have hcoef : 10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) ^ 2
        / (S.Δ ^ 2 * (P.H * S.Δ))
      ≤ 10 ^ 35 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3 * ℓ₂
          * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) ^ 2 / (S.Δ ^ 2 * (P.H * S.Δ)) := by
    gcongr 10 ^ 35 * ?_ * P.G * S.Ω ^ 3 * ℓ₂ * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) ^ 2
      / (S.Δ ^ 2 * (P.H * S.Δ))
  have hprod : (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) ^ 2
        / (S.Δ ^ 2 * (P.H * S.Δ)))
        * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) * m
      ≤ (10 ^ 35 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3 * ℓ₂
          * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) ^ 2 / (S.Δ ^ 2 * (P.H * S.Δ)))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8) :=
    mul_le_mul (mul_le_mul hcoef le_rfl (by positivity) (by positivity)) hm hm0
      (by positivity)
  -- step 2: collapse to the single monomial piece
  have hsplit : (10 ^ 35 * (11 * (S.Δ * S.Ω)) * P.G * S.Ω ^ 3 * ℓ₂
          * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) ^ 2 / (S.Δ ^ 2 * (P.H * S.Δ)))
          * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          * (10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8)
      = 11 * 10 ^ 95 * C * P.G ^ 5 * P.U ^ 40
          * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) / S.Ω ^ 12 := by
    field_simp
  -- step 3: window
  have hW3 : ℓ₁ ^ 3 * ℓ₂ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35) := by
    calc ℓ₁ ^ 3 * ℓ₂ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) = ℓ₁ ^ 4 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) := by ring
      _ ≤ 130 ^ (4 + 2 + 1)
            * ((P.G * P.U ^ 5) ^ 4 * (P.G * P.U ^ 5) ^ 2 * (P.G * P.U ^ 5)) :=
          step4_fitEA_window ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W 4 2
      _ = 130 ^ 7 * (P.G ^ 7 * P.U ^ 35) := by ring
      _ ≤ 10 ^ 15 * (P.G ^ 7 * P.U ^ 35) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hW30 : 0 ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hℓ1pos.le 3) hℓ2pos.le)
      (mul_nonneg (mul_nonneg hℓ1pos.le hℓ2pos.le) hd0)
  -- step 4: assemble
  refine le_trans (le_trans hprod (le_of_eq hsplit)) (le_trans
    (step4_fitEA_coreB h1 hG1 hΩU hUbig C hC _ _ (by norm_num) hW30 hW3) (le_of_eq ?_))
  field_simp

/-- Target normalization: the `8·C·(H/Δ)·t`-block as a single fraction. -/
theorem step4_fitEA_target_eq (C : ℝ) :
    8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))
      = 8 * C * P.H * P.G ^ 15 * P.U ^ 75 / (S.Δ ^ 2 * S.Ω ^ 13) := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  field_simp

/-- `C² ≤ 10¹²⁰·C` for the Step-4 hybrid fit cap. -/
theorem step4_fitEA_csq (C : ℝ) (hC : 1 ≤ C) (hCcap : C ≤ (10:ℝ)^120) :
    C ^ 2 ≤ 10 ^ 120 * C := by nlinarith

/-- **Hybrid fit, T1 summand, `C¹` form.** The `m`-cap's `C` cancels 1:1 against the
target's `C` (scale `step4_fitEA_T1` at `C := 1`, `m := m/C`). -/
theorem step4_fitEA_T1'
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8)
    (hm0 : 0 ≤ m)
    (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (gap : ℝ) (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
        + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * m
      ≤ 2 * (C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))) := by
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hm' : m / C ≤ 10 ^ 60 * 1 * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 := by
    rw [div_le_iff₀ hCpos]
    calc m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 := hm
      _ = 10 ^ 60 * 1 * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 * C := by ring
  have hm0' : 0 ≤ m / C := div_nonneg hm0 hCpos.le
  have h := step4_fitEA_T1 h1 hG1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W (m / C) 1 le_rfl
    hm' hm0' a ha_hi gap hgap0 hgap b hb
  calc (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * m
      = C * ((10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2) * b * (m / C)) := by
        field_simp
    _ ≤ C * (2 * (1 ^ 2 * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))) :=
        mul_le_mul_of_nonneg_left h hCpos.le
    _ = 2 * (C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))) := by ring

/-- **Hybrid fit, T2 summand, `C¹` form.** Scale `step4_fitEA_T2` at `C := 1`, `m := m/C`. -/
theorem step4_fitEA_T2'
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (m C : ℝ) (hC : 1 ≤ C)
    (hm : m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8)
    (hm0 : 0 ≤ m)
    (a : ℝ) (ha_hi : a ≤ 11 * S.A)
    (b : ℝ) (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)) :
    (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)) * b * m
      ≤ C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hm' : m / C ≤ 10 ^ 60 * 1 * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 := by
    rw [div_le_iff₀ hCpos]
    calc m ≤ 10 ^ 60 * C * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 := hm
      _ = 10 ^ 60 * 1 * ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.G * P.U ^ 25 / S.Ω ^ 8 * C := by ring
  have hm0' : 0 ≤ m / C := div_nonneg hm0 hCpos.le
  have h := step4_fitEA_T2 h1 hG1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W (m / C) 1 le_rfl
    hm' hm0' a ha_hi b hb
  calc (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)) * b * m
      = C * ((10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)) * b * (m / C)) := by
        field_simp
    _ ≤ C * (1 ^ 2 * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13))) :=
        mul_le_mul_of_nonneg_left h hCpos.le
    _ = C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by ring

end Squarefree
