import Squarefree.Lower.Step23Delta
import Squarefree.Lower.DefectScales

/-!
# §5 Step-4 delta — the pref-free `Q_gen` error piece (writeup 1067, 1071)

`qgen_pieceV_le` is the **pref-free** analogue of `qgen_piece_le`: it bounds the raw
three-term `Q_gen_expand` remainder `E_Q` directly against the Step-4 budget
`δ = (1/Δ)G⁴U¹⁵/Ω⁵` (no `d̃⁴/6Xa` prefactor).  The cancellation `X·a/D⁵ = G/Δ⁵`,
`X·a/D⁶ = G/(HΔ⁶)` (with `a ≤ 11A`) and the regime fact `Δ²U⁶ ≤ HΩ³` collapse each `Ei`
to an absolute multiple of `δ`.  The constants are large but absolute.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000 in
/-- **Step-4 delta: the pref-free `Q_gen` error piece.** Raw `Q_gen_expand` remainder
`E_Q ≤ 10⁶⁶·δ`, `δ = (1/Δ)G⁴U¹⁵/Ω⁵`. -/
theorem qgen_pieceV_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1pos : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    12 * P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
        + 400 * P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
        + 400 * P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 / d ^ 6
      ≤ (10:ℝ) ^ 68 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  obtain ⟨hdD, hd2D⟩ := hdwin
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hd5 : S.D ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ hDpos.le hdD 5
  have hd6 : S.D ^ 6 ≤ d ^ 6 := pow_le_pow_left₀ hDpos.le hdD 6
  -- master scale M = U^5 Δ²/Ω³
  set M : ℝ := P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 with hM_def
  have hM_nonneg : 0 ≤ M := by rw [hM_def]; positivity
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans (le_of_lt hℓ12) hℓ2W'
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := le_trans hℓ1nn hℓ12.le
  have hℓ2pos : 0 < ℓ₂ := lt_of_lt_of_le hℓ1pos hℓ12.le
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- a ≤ 11A = 11ΔΩ  (TIGHT)
  have ha_A : (a : ℝ) ≤ 11 * (S.Δ * S.Ω) := by
    have : (11 : ℝ) * S.A = 11 * (S.Δ * S.Ω) := by unfold Scale.A; ring
    linarith [ha_hi, this]
  have ha_nn : 0 ≤ (a : ℝ) := haR.le
  -- ℓ₂|b₀| ≤ 3e12 M  and ℓ₁|b₀| ≤ 3e12 M
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
    have : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
    rw [this] at hb0; exact hb0
  have hℓ2b0_M : ℓ₂ * |b₀| ≤ 390000000000000 * M := by
    calc ℓ₂ * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
          mul_le_mul hℓ2W' hb0' hb0nn (by positivity)
      _ = 390000000000000 * M := by rw [hM_def]; field_simp; ring
  have hℓ1b0_M : ℓ₁ * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right hℓ12.le hb0nn) hℓ2b0_M
  -- a ≤ M  (lossy, for the (a+...) sum factors only)
  have ha_M : (a : ℝ) ≤ M := by
    rw [hM_def, le_div_iff₀ (by positivity)]
    have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ hΩpos.le hΩU 4
    have hUΔ : (11 : ℝ) ≤ P.U * S.Δ := by
      have : (11 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
      nlinarith [hΔ1, this, hUpos]
    have c1 : (a : ℝ) * S.Ω ^ 3 ≤ 11 * S.Δ * S.Ω ^ 4 := by
      have := mul_le_mul_of_nonneg_right ha_A (pow_nonneg hΩpos.le 3); nlinarith [this]
    have c2 : (11 : ℝ) * S.Δ * S.Ω ^ 4 ≤ 11 * S.Δ * P.U ^ 4 :=
      mul_le_mul_of_nonneg_left hΩ4 (by positivity)
    have c3 : (11 : ℝ) * S.Δ * P.U ^ 4 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hUΔ (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 4),
        hΔpos, hUpos]
    linarith [c1, c2, c3]
  have hv_M : |v| ≤ 10 ^ 20 * M := by
    rw [hM_def]
    refine le_trans hv ?_
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith [hΔ1, hΔpos]
    have hnum : S.Δ * P.U ^ 5 ≤ P.U ^ 5 * S.Δ ^ 2 := by nlinarith [hΔsq, pow_nonneg hUpos.le 5]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) (by norm_num)
  have hℓ2b0v_M : |ℓ₂ * b₀ + v| ≤ 2 * 10 ^ 20 * M := by
    calc |ℓ₂ * b₀ + v| ≤ |ℓ₂ * b₀| + |v| := abs_add_le _ _
      _ = ℓ₂ * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ2pos]
      _ ≤ 390000000000000 * M + 10 ^ 20 * M := by linarith [hℓ2b0_M, hv_M]
      _ ≤ 2 * 10 ^ 20 * M := by linarith [hM_nonneg]
  have hfac2sum : (a : ℝ) + |ℓ₂ * b₀ + v| ≤ 3 * 10 ^ 20 * M := by
    linarith [ha_M, hℓ2b0v_M, hM_nonneg]
  have hfac1 : (a : ℝ) + 2 * ℓ₂ * |b₀| + |v| ≤ 2 * 10 ^ 20 * M := by
    have h2 : 2 * ℓ₂ * |b₀| ≤ 2 * (390000000000000 * M) := by
      rw [show 2 * ℓ₂ * |b₀| = 2 * (ℓ₂ * |b₀|) by ring]; linarith [hℓ2b0_M]
    linarith [ha_M, h2, hv_M, hM_nonneg]
  have hfac3 : (a : ℝ) + ℓ₁ * |b₀| ≤ 400000000000000 * M := by
    linarith [ha_M, hℓ1b0_M, hM_nonneg]
  -- regime: Δ²U⁶ ≤ HΩ³
  have hkey : S.Δ ^ 2 * P.U ^ 6 ≤ P.H * S.Ω ^ 3 := by
    have hH1' : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1; linarith [this]
    have hUΩ : P.U ^ 3 * S.Ω ^ 4 ≤ P.U ^ 4 * S.Ω ^ 3 := by
      have hfac : P.U ^ 4 * S.Ω ^ 3 - P.U ^ 3 * S.Ω ^ 4
          = P.U ^ 3 * S.Ω ^ 3 * (P.U - S.Ω) := by ring
      nlinarith [hfac, pow_nonneg hUpos.le 3, pow_nonneg hΩpos.le 3, sub_nonneg.mpr hΩU,
        mul_nonneg (mul_nonneg (pow_nonneg hUpos.le 3) (pow_nonneg hΩpos.le 3))
          (sub_nonneg.mpr hΩU)]
    have hband4 : (1 : ℝ) ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := by
      have hb' : P.G * P.U ^ 3 * S.Ω ^ 4 ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := by
        nlinarith [hUΩ, hGpos.le, mul_le_mul_of_nonneg_left hUΩ hGpos.le]
      linarith [hband, hb']
    have hmid : S.Δ ^ 2 * P.U ^ 6 ≤ P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := by
      have hd6nn : (0:ℝ) ≤ S.Δ ^ 2 * P.U ^ 6 := by positivity
      have := mul_le_mul_of_nonneg_left hband4 hd6nn
      rw [mul_one] at this
      nlinarith [this]
    calc S.Δ ^ 2 * P.U ^ 6 ≤ P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := hmid
      _ ≤ P.H * S.Ω ^ 3 := by nlinarith [hH1', pow_nonneg hΩpos.le 3]
  -- scale identities for X·a / D^k  with a ≤ 11A
  -- X·A/D⁵ = X·A·B²/D⁵ / B² = (1/(GΩ⁵))/B²; B² = Δ⁴/(G²Ω⁶); so X·A/D⁵ = G/(Δ⁴)·... compute directly
  have hSDeq : S.D = P.H * S.Δ := rfl
  set δ4 : ℝ := (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5 with hδ4_def
  have hδ4_pos : 0 < δ4 := by rw [hδ4_def]; positivity
  -- ===== TERM 1 =====
  set E1 : ℝ := 12 * P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
    with hE1_def
  set E2 : ℝ :=
    400 * P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
    with hE2_def
  set E3 : ℝ :=
    400 * P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 / d ^ 6 with hE3_def
  -- TERM 1 bound: a·ℓ₁·|v|·(fac1) tight (a ≤ 11ΔΩ)
  have hT1 : E1 ≤ 10 ^ 68 * δ4 / 3 := by
    rw [hE1_def]
    -- numerator ≤ 12·X·(11ΔΩ)·(GU⁵)·(10²⁰ΔU⁵/Ω³)·(2·10²⁰M), denom ≥ D⁵
    have hnum : P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)
        ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
            * (2 * 10 ^ 20 * M) := by
      have q1 : P.X * (a : ℝ) ≤ P.X * (11 * (S.Δ * S.Ω)) :=
        mul_le_mul_of_nonneg_left ha_A hXpos.le
      have q2 : P.X * (a : ℝ) * ℓ₁ ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul q1 hℓ1W' hℓ1nn (by positivity)
      have q3 : P.X * (a : ℝ) * ℓ₁ * |v|
          ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) :=
        mul_le_mul q2 hv hvnn (by positivity)
      exact mul_le_mul q3 hfac1 (by positivity) (by positivity)
    have hnum12 : 12 * (P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|))
        ≤ 12 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5))
            * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M)) :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    have hstep : 12 * (P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)) / d ^ 5
        ≤ 12 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5))
            * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M)) / S.D ^ 5 :=
      div_le_div₀ (by positivity) hnum12 (by positivity) hd5
    rw [show 12 * P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
          = 12 * (P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)) / d ^ 5 by ring]
    refine le_trans hstep ?_
    -- collapse to a numeric multiple of G²U¹⁵/(ΔΩ⁵)
    have hcollapse : 12 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5))
            * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M)) / S.D ^ 5
        = (343200000000000000000000000000000000000000000 : ℝ) * (P.G ^ 2 * P.U ^ 15)
            / (S.Δ * S.Ω ^ 5) := by
      rw [hM_def, hSDeq, P.X_eq_G_mul_H_pow_five]
      field_simp
      ring
    rw [hcollapse, hδ4_def]
    rw [show (10:ℝ) ^ 68 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) / 3
          = 10 ^ 68 * P.G ^ 4 * P.U ^ 15 / (3 * (S.Δ * S.Ω ^ 5)) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- reduces to 2.64e42·G²·3 ≤ 10⁴⁹·G⁴; use G²≤G⁴ and 2.64e42·3 ≤ 10⁴⁹
    have hG24 : P.G ^ 2 ≤ P.G ^ 4 := by
      have : P.G ^ 2 * 1 ≤ P.G ^ 2 * P.G ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [hG1] : (1:ℝ) ≤ P.G ^ 2) (by positivity)
      nlinarith [this]
    have hfin : (343200000000000000000000000000000000000000000 : ℝ) * P.G ^ 2 * 3 ≤ 10 ^ 68 * P.G ^ 4 := by
      calc (343200000000000000000000000000000000000000000 : ℝ) * P.G ^ 2 * 3
          ≤ 10 ^ 68 * P.G ^ 2 := by nlinarith [hG24, pow_nonneg hGpos.le 2]
        _ ≤ 10 ^ 68 * P.G ^ 4 := by nlinarith [hG24]
    nlinarith [mul_le_mul_of_nonneg_right hfin
        (by positivity : (0:ℝ) ≤ P.U ^ 15 * (S.Δ * S.Ω ^ 5)),
      hGpos, hUpos, hΔpos, hΩpos]
  -- ===== TERM 2 =====
  have hT2 : E2 ≤ 10 ^ 68 * δ4 / 3 := by
    rw [hE2_def]
    have hnum : P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2
        ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2 := by
      have q1 : P.X * (a : ℝ) ≤ P.X * (11 * (S.Δ * S.Ω)) :=
        mul_le_mul_of_nonneg_left ha_A hXpos.le
      have q2 : P.X * (a : ℝ) * ℓ₁ ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul q1 hℓ1W' hℓ1nn (by positivity)
      have q3 : P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v|
          ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) :=
        mul_le_mul q2 hℓ2b0v_M (abs_nonneg _) (by positivity)
      have q4 : ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 ≤ (3 * 10 ^ 20 * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfac2sum 2
      exact mul_le_mul q3 q4 (by positivity) (by positivity)
    have hnum400 : 400 * (P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2)
        ≤ 400 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M)
            * (3 * 10 ^ 20 * M) ^ 2) := mul_le_mul_of_nonneg_left hnum (by norm_num)
    have hstep : 400 * (P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2) / d ^ 6
        ≤ 400 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M)
            * (3 * 10 ^ 20 * M) ^ 2) / S.D ^ 6 :=
      div_le_div₀ (by positivity) hnum400 (by positivity) hd6
    rw [show 400 * P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
          = 400 * (P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2) / d ^ 6 by ring]
    refine le_trans hstep ?_
    have hcollapse : 400 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M)
            * (3 * 10 ^ 20 * M) ^ 2) / S.D ^ 6
        = (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ)
            * (S.Δ * P.G ^ 2 * P.U ^ 20) / (P.H * S.Ω ^ 8) := by
      rw [hM_def, hSDeq, P.X_eq_G_mul_H_pow_five]; field_simp; ring
    rw [hcollapse]
    -- compare to 10⁶⁶·δ4/3 = 10⁶⁶·G⁴U¹⁵/(3ΔΩ⁵)
    rw [hδ4_def, show (10:ℝ) ^ 68 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) / 3
          = 10 ^ 68 * P.G ^ 4 * P.U ^ 15 / (3 * (S.Δ * S.Ω ^ 5)) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- reduce using hkey: Δ²U⁶ ≤ HΩ³
    have hG24 : P.G ^ 2 ≤ P.G ^ 4 := by nlinarith [hG1, sq_nonneg (P.G ^ 2 - 1), pow_nonneg hGpos.le 2]
    have hΩ3U3 : S.Ω ^ 3 ≤ P.U ^ 3 := pow_le_pow_left₀ hΩpos.le hΩU 3
    -- const·Δ·G²·U²⁰·(3ΔΩ⁵) ≤ 10⁶⁶·G⁴·U¹⁵·(HΩ⁸)
    -- i.e. 3·const·Δ²·U⁵·G² ≤ 10⁶⁶·G⁴·(HΩ³)  (after cancelling U¹⁵Ω⁵)
    have hcore : (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3
          * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2 ≤ 10 ^ 68 * P.G ^ 4 * (P.H * S.Ω ^ 3) := by
      have hc1 : (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3 ≤ 10 ^ 68 := by
        norm_num
      have hstepc : (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3
            * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2 ≤ 10 ^ 68 * (P.H * S.Ω ^ 3) * P.G ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc1 hkey (by positivity) (by norm_num))
          (by positivity)
      calc (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3
            * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2
          ≤ 10 ^ 68 * (P.H * S.Ω ^ 3) * P.G ^ 2 := hstepc
        _ ≤ 10 ^ 68 * (P.H * S.Ω ^ 3) * P.G ^ 4 :=
            mul_le_mul_of_nonneg_left hG24 (by positivity)
        _ = 10 ^ 68 * P.G ^ 4 * (P.H * S.Ω ^ 3) := by ring
    -- bridge: goal LHS = hcore_LHS · U¹⁴Ω⁵ ;  goal RHS ≥ hcore_RHS · U¹⁴Ω⁵
    have hbridge := mul_le_mul_of_nonneg_right hcore (by positivity : (0:ℝ) ≤ P.U ^ 14 * S.Ω ^ 5)
    have hU1415 : P.U ^ 14 ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
    calc (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ)
            * (S.Δ * P.G ^ 2 * P.U ^ 20) * (3 * (S.Δ * S.Ω ^ 5))
        = (10296000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3
            * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2 * (P.U ^ 14 * S.Ω ^ 5) := by ring
      _ ≤ 10 ^ 68 * P.G ^ 4 * (P.H * S.Ω ^ 3) * (P.U ^ 14 * S.Ω ^ 5) := hbridge
      _ = 10 ^ 68 * P.G ^ 4 * P.U ^ 14 * (P.H * S.Ω ^ 8) := by ring
      _ ≤ 10 ^ 68 * P.G ^ 4 * P.U ^ 15 * (P.H * S.Ω ^ 8) := by
          gcongr
  -- ===== TERM 3 =====
  have hT3 : E3 ≤ 10 ^ 68 * δ4 / 3 := by
    rw [hE3_def]
    have hnum : P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2
        ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
            * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) * (400000000000000 * M) ^ 2 := by
      have q1 : P.X * (a : ℝ) ≤ P.X * (11 * (S.Δ * S.Ω)) :=
        mul_le_mul_of_nonneg_left ha_A hXpos.le
      have q2 : P.X * (a : ℝ) * ℓ₂ ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul q1 hℓ2W' hℓ2nn (by positivity)
      have q3 : P.X * (a : ℝ) * ℓ₂ * ℓ₁
          ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul q2 hℓ1W' hℓ1nn (by positivity)
      have q4 : P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀|
          ≤ P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
              * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
        mul_le_mul q3 hb0' hb0nn (by positivity)
      have q5 : ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 ≤ (400000000000000 * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfac3 2
      exact mul_le_mul q4 q5 (by positivity) (by positivity)
    have hnum400 : 400 * (P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2)
        ≤ 400 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
            * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) * (400000000000000 * M) ^ 2) :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    have hstep : 400 * (P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2) / d ^ 6
        ≤ 400 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
            * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) * (400000000000000 * M) ^ 2) / S.D ^ 6 :=
      div_le_div₀ (by positivity) hnum400 (by positivity) hd6
    rw [show 400 * P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 / d ^ 6
          = 400 * (P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2) / d ^ 6 by ring]
    refine le_trans hstep ?_
    have hcollapse : 400 * (P.X * (11 * (S.Δ * S.Ω)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
            * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) * (400000000000000 * M) ^ 2) / S.D ^ 6
        = (35692800000000000000000000000000000000000000000000 : ℝ)
            * (S.Δ * P.G ^ 2 * P.U ^ 20) / (P.H * S.Ω ^ 8) := by
      rw [hM_def, hSDeq, P.X_eq_G_mul_H_pow_five]; field_simp; ring
    rw [hcollapse]
    rw [hδ4_def, show (10:ℝ) ^ 68 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) / 3
          = 10 ^ 68 * P.G ^ 4 * P.U ^ 15 / (3 * (S.Δ * S.Ω ^ 5)) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hG24 : P.G ^ 2 ≤ P.G ^ 4 := by nlinarith [hG1, sq_nonneg (P.G ^ 2 - 1), pow_nonneg hGpos.le 2]
    have hcore : (35692800000000000000000000000000000000000000000000 : ℝ) * 3
          * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2 ≤ 10 ^ 68 * P.G ^ 4 * (P.H * S.Ω ^ 3) := by
      have hc1 : (35692800000000000000000000000000000000000000000000 : ℝ) * 3 ≤ 10 ^ 68 := by norm_num
      have hstepc : (35692800000000000000000000000000000000000000000000 : ℝ) * 3
            * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2 ≤ 10 ^ 68 * (P.H * S.Ω ^ 3) * P.G ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc1 hkey (by positivity) (by norm_num))
          (by positivity)
      calc (35692800000000000000000000000000000000000000000000 : ℝ) * 3
            * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2
          ≤ 10 ^ 68 * (P.H * S.Ω ^ 3) * P.G ^ 2 := hstepc
        _ ≤ 10 ^ 68 * (P.H * S.Ω ^ 3) * P.G ^ 4 :=
            mul_le_mul_of_nonneg_left hG24 (by positivity)
        _ = 10 ^ 68 * P.G ^ 4 * (P.H * S.Ω ^ 3) := by ring
    have hbridge := mul_le_mul_of_nonneg_right hcore (by positivity : (0:ℝ) ≤ P.U ^ 14 * S.Ω ^ 5)
    have hU1415 : P.U ^ 14 ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
    calc (35692800000000000000000000000000000000000000000000 : ℝ)
            * (S.Δ * P.G ^ 2 * P.U ^ 20) * (3 * (S.Δ * S.Ω ^ 5))
        = (35692800000000000000000000000000000000000000000000 : ℝ) * 3
            * (S.Δ ^ 2 * P.U ^ 6) * P.G ^ 2 * (P.U ^ 14 * S.Ω ^ 5) := by ring
      _ ≤ 10 ^ 68 * P.G ^ 4 * (P.H * S.Ω ^ 3) * (P.U ^ 14 * S.Ω ^ 5) := hbridge
      _ = 10 ^ 68 * P.G ^ 4 * P.U ^ 14 * (P.H * S.Ω ^ 8) := by ring
      _ ≤ 10 ^ 68 * P.G ^ 4 * P.U ^ 15 * (P.H * S.Ω ^ 8) := by gcongr
  -- ===== ASSEMBLE =====
  rw [show (10:ℝ) ^ 68 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5)
        = 10 ^ 68 * δ4 / 3 + 10 ^ 68 * δ4 / 3 + 10 ^ 68 * δ4 / 3 by rw [hδ4_def]; ring]
  exact add_le_add (add_le_add hT1 hT2) hT3
