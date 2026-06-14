import Squarefree.Lower.Step23Delta

/-!
# §5 Steps 2/3 delta — the `Q_gen` error piece (writeup 884–903)

`qgen_piece_le` bounds the three-term `Q_gen_expand` remainder against `δ₂₃`.
Split out of `Step23Delta.lean` for file-size reasons; shares the same scale idioms
(`dtilde_asymp_D`, master scale `M = U⁵Δ²/Ω³`).
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000 in
/-- **Steps 2/3 delta: the `Q_gen` error piece** `(d̃⁴/6Xa)·E_Q ≤ δ₂₃`, where `E_Q` is the
three-term `Q_gen_expand` remainder. All inner factors are `≤ const·M` with the master scale
`M = U⁵Δ²/Ω³` (`a ≤ M`, `ℓ₂|b₀| ≤ 3·10¹²M`, `|v| ≤ M`), and `Δ²/(HΩ³) ≤ 1/U⁶` (from `h1`+band)
controls the two `d⁶` terms. -/
theorem qgen_piece_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hℓ1pos : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    (dtilde P.X r (a : ℝ)) ^ 4 / (6 * P.X * (a : ℝ))
        * ( 12 * P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
            + 400 * P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
            + 400 * P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 / d ^ 6 )
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
  -- positivity of scale quantities
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  -- d̃ ≍ D
  obtain ⟨hdt_lo, hdt_hi⟩ :=
    dtilde_asymp_D hAD (by exact_mod_cast ha0) hr0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  have hdt_pos : 0 < dt := lt_of_lt_of_le (by positivity) hdt_lo
  have hdt_nonneg : 0 ≤ dt := hdt_pos.le
  obtain ⟨hdD, hd2D⟩ := hdwin
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hX_ne : P.X ≠ 0 := ne_of_gt hXpos
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt haR
  -- d̃^4 ≤ 18^4 * S.D^4
  have hdt4 : dt ^ 4 ≤ 18 ^ 4 * S.D ^ 4 := by
    have := pow_le_pow_left₀ hdt_nonneg hdt_hi 4
    calc dt ^ 4 ≤ (18 * S.D) ^ 4 := this
      _ = 18 ^ 4 * S.D ^ 4 := by rw [mul_pow]
  have hdt4_nn : 0 ≤ dt ^ 4 := by positivity
  -- d^5 ≥ S.D^5, d^6 ≥ S.D^6
  have hd5 : S.D ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ hDpos.le hdD 5
  have hd6 : S.D ^ 6 ≤ d ^ 6 := pow_le_pow_left₀ hDpos.le hdD 6
  -- master scale M = U^5 Δ²/Ω³
  set M : ℝ := P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 with hM_def
  have hM_nonneg : 0 ≤ M := by rw [hM_def]; positivity
  -- ℓ₁, ℓ₂ ≤ G U^5
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans (le_of_lt hℓ12) hℓ2W'
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := le_trans hℓ1nn hℓ12.le
  have hℓ2pos : 0 < ℓ₂ := lt_of_lt_of_le hℓ1pos hℓ12.le
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- a ≤ M
  have ha_M : (a : ℝ) ≤ M := by
    have ha11 : (a : ℝ) ≤ 11 * (S.Δ * S.Ω) := by
      have : (11 : ℝ) * S.A = 11 * (S.Δ * S.Ω) := by unfold Scale.A; ring
      linarith [ha_hi, this]
    rw [hM_def]
    rw [le_div_iff₀ (by positivity)]
    -- 11*(Δ*Ω)*Ω³ ≤ U^5*Δ²  i.e.  11*Δ*Ω^4 ≤ U^5*Δ²  i.e. 11*Ω^4 ≤ U^5*Δ
    have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ hΩpos.le hΩU 4
    have hUΔ : (11 : ℝ) ≤ P.U * S.Δ := by
      have : (11 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
      nlinarith [hΔ1, this, hUpos]
    -- a*Ω³ ≤ 11ΔΩ⁴ ≤ 11ΔU⁴ ≤ U⁵Δ²
    have c1 : (a : ℝ) * S.Ω ^ 3 ≤ 11 * S.Δ * S.Ω ^ 4 := by
      have := mul_le_mul_of_nonneg_right ha11 (pow_nonneg hΩpos.le 3)
      nlinarith [this]
    have c2 : (11 : ℝ) * S.Δ * S.Ω ^ 4 ≤ 11 * S.Δ * P.U ^ 4 :=
      mul_le_mul_of_nonneg_left hΩ4 (by positivity)
    have c3 : (11 : ℝ) * S.Δ * P.U ^ 4 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      have hP4nn : (0:ℝ) ≤ P.U ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hUΔ (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 4),
        hΔpos, hUpos]
    linarith [c1, c2, c3]
  -- ℓ₂*|b₀| ≤ 3e12*M
  have hℓ2b0_M : ℓ₂ * |b₀| ≤ 390000000000000 * M := by
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      have : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
      rw [this] at hb0; exact hb0
    calc ℓ₂ * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
          mul_le_mul hℓ2W' hb0' hb0nn (by positivity)
      _ = 390000000000000 * M := by rw [hM_def]; field_simp; ring
  -- ℓ₁*|b₀| ≤ 3e12*M  (ℓ₁ ≤ ℓ₂)
  have hℓ1b0_M : ℓ₁ * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right hℓ12.le hb0nn) hℓ2b0_M
  -- |v| ≤ 10^20 * M  (Δ ≤ Δ²)
  have hv_M : |v| ≤ 10 ^ 20 * M := by
    rw [hM_def]
    refine le_trans hv ?_
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith [hΔ1, hΔpos]
    have hnum : S.Δ * P.U ^ 5 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith [hΔsq, pow_nonneg hUpos.le 5]
    have hbase : S.Δ * P.U ^ 5 / S.Ω ^ 3 ≤ P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    exact mul_le_mul_of_nonneg_left hbase (by norm_num)
  -- |ℓ₂*b₀+v| ≤ 2*10^20*M
  have hℓ2b0v_M : |ℓ₂ * b₀ + v| ≤ 2 * 10 ^ 20 * M := by
    calc |ℓ₂ * b₀ + v| ≤ |ℓ₂ * b₀| + |v| := abs_add_le _ _
      _ = ℓ₂ * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ2pos]
      _ ≤ 390000000000000 * M + 10 ^ 20 * M := by linarith [hℓ2b0_M, hv_M]
      _ ≤ 2 * 10 ^ 20 * M := by linarith [hM_nonneg]
  -- (a + 2ℓ₂|b₀| + |v|) ≤ 2*10^20*M
  have hfac1 : (a : ℝ) + 2 * ℓ₂ * |b₀| + |v| ≤ 2 * 10 ^ 20 * M := by
    have h2 : 2 * ℓ₂ * |b₀| ≤ 2 * (390000000000000 * M) := by
      have : 2 * ℓ₂ * |b₀| = 2 * (ℓ₂ * |b₀|) := by ring
      rw [this]; linarith [hℓ2b0_M]
    linarith [ha_M, h2, hv_M, hM_nonneg]
  -- (a + |ℓ₂b₀+v|) ≤ 3*10^20*M
  have hfac2 : (a : ℝ) + |ℓ₂ * b₀ + v| ≤ 3 * 10 ^ 20 * M := by
    linarith [ha_M, hℓ2b0v_M, hM_nonneg]
  -- (a + ℓ₁|b₀|) ≤ 4e12*M
  have hfac3 : (a : ℝ) + ℓ₁ * |b₀| ≤ 400000000000000 * M := by
    linarith [ha_M, hℓ1b0_M, hM_nonneg]
  -- key denominator fact: Δ² U^6 ≤ H Ω³
  have hkey : S.Δ ^ 2 * P.U ^ 6 ≤ P.H * S.Ω ^ 3 := by
    -- from h1: G U^10 Δ² ≤ H
    have hH1' : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
      linarith [this]
    -- band: G U^4 Ω³ ≥ G U^3 Ω^4 ≥ 1  (since U ≥ Ω)
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
    -- Δ² U^6 ≤ G U^10 Δ² Ω³ ≤ H Ω³
    have hmid : S.Δ ^ 2 * P.U ^ 6 ≤ P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := by
      -- (G U^4 Ω³ ≥ 1) ⟹ Δ²U^6 * (G U^4 Ω³) ≥ Δ²U^6
      have hd6nn : (0:ℝ) ≤ S.Δ ^ 2 * P.U ^ 6 := by positivity
      have := mul_le_mul_of_nonneg_left hband4 hd6nn
      have heq : S.Δ ^ 2 * P.U ^ 6 * (P.G * P.U ^ 4 * S.Ω ^ 3)
          = P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := by ring
      rw [mul_one] at this
      linarith [this, heq.le, heq.ge]
    calc S.Δ ^ 2 * P.U ^ 6 ≤ P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := hmid
      _ ≤ P.H * S.Ω ^ 3 := by nlinarith [hH1', pow_nonneg hΩpos.le 3]
  -- common positivity / abbreviation
  have hSDeq : S.D = P.H * S.Δ := rfl
  have hδ_pos : (0:ℝ) < S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by positivity
  -- ====================================================================
  -- TERM 1 : (dt^4/(6Xa)) * E1 ≤ δ₂₃/3
  -- ====================================================================
  set E1 : ℝ := 12 * P.X * (a : ℝ) * ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
    with hE1_def
  set E2 : ℝ :=
    400 * P.X * (a : ℝ) * ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
    with hE2_def
  set E3 : ℝ :=
    400 * P.X * (a : ℝ) * ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 / d ^ 6 with hE3_def
  -- cancellation: (dt^4/(6Xa))*E1 = 2*dt^4*ℓ₁*|v|*(fac1)/d^5
  have hT1eq : dt ^ 4 / (6 * P.X * (a : ℝ)) * E1
      = 2 * dt ^ 4 * (ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)) / d ^ 5 := by
    rw [hE1_def]; field_simp; ring
  have hT2eq : dt ^ 4 / (6 * P.X * (a : ℝ)) * E2
      = (400 / 6) * dt ^ 4
          * (ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2) / d ^ 6 := by
    rw [hE2_def]; field_simp
  have hT3eq : dt ^ 4 / (6 * P.X * (a : ℝ)) * E3
      = (400 / 6) * dt ^ 4
          * (ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2) / d ^ 6 := by
    rw [hE3_def]; field_simp
  -- TERM 1 scale bound
  have hT1 : dt ^ 4 / (6 * P.X * (a : ℝ)) * E1
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) / 3 := by
    rw [hT1eq]
    -- numerator ≤ : ℓ₁*|v|*(fac1) ≤ (G U^5)*(10^20·Δ U^5/Ω³)*(2·10^20 M)
    have hZ1 : ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)
        ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M) := by
      have s1 : ℓ₁ * |v| ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) :=
        mul_le_mul hℓ1W' hv hvnn (by positivity)
      have s2 : 0 ≤ (a : ℝ) + 2 * ℓ₂ * |b₀| + |v| := by positivity
      have s3 : 0 ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) := by positivity
      exact mul_le_mul s1 hfac1 s2 s3
    -- 2*dt^4*Z1/d^5 ≤ 2*(18^4 S.D^4)*Z1bound/S.D^5
    have hZ1_nn : 0 ≤ ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|) := by positivity
    have hnum_nn : 0 ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M) := by
      positivity
    have hstep : 2 * dt ^ 4 * (ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)) / d ^ 5
        ≤ 2 * (18 ^ 4 * S.D ^ 4)
            * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M)) / S.D ^ 5 := by
      apply div_le_div₀ (by positivity)
      · have a1 : 2 * dt ^ 4 ≤ 2 * (18 ^ 4 * S.D ^ 4) := by linarith [hdt4]
        have a2 : 0 ≤ 2 * (18 ^ 4 * S.D ^ 4) := by positivity
        calc 2 * dt ^ 4 * (ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|))
            ≤ 2 * (18 ^ 4 * S.D ^ 4) * (ℓ₁ * |v| * ((a : ℝ) + 2 * ℓ₂ * |b₀| + |v|)) :=
              mul_le_mul_of_nonneg_right a1 hZ1_nn
          _ ≤ 2 * (18 ^ 4 * S.D ^ 4)
              * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M)) :=
              mul_le_mul_of_nonneg_left hZ1 a2
      · positivity
      · exact hd5
    refine le_trans hstep ?_
    -- collapse the bound into an explicit single fraction
    have hBeq : 2 * (18 ^ 4 * S.D ^ 4)
            * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2 * 10 ^ 20 * M)) / S.D ^ 5
        = (545875200000000000000000000000000000000000000000 : ℝ) * (P.G * P.U ^ 15 * S.Δ ^ 2) / (P.H * S.Ω ^ 6) := by
      rw [hM_def, hSDeq]; field_simp; ring
    rw [hBeq]
    -- now clean fraction comparison: const*G*U^15*Δ²/(HΩ⁶) ≤ Δ²GU²⁰/(3HΩ⁶)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- reduces to const*U^15 ≤ U^20/3, i.e. 3*const ≤ U^5 (and 3*const ≤ 10^66 ≤ U^2·U^5...)
    have hkkey : (545875200000000000000000000000000000000000000000 : ℝ) * P.U ^ 15 * 3 ≤ P.U ^ 20 := by
      have hU5 : (1637625600000000000000000000000000000000000000000 : ℝ) ≤ P.U ^ 5 := by
        have h2 : ((10:ℝ) ^ 33) ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ (by norm_num) hUbig 5
        calc (1637625600000000000000000000000000000000000000000 : ℝ) ≤ ((10:ℝ) ^ 33) ^ 5 := by norm_num
          _ ≤ P.U ^ 5 := h2
      have hUsplit : P.U ^ 20 = P.U ^ 5 * P.U ^ 15 := by ring
      rw [hUsplit]
      have := mul_le_mul_of_nonneg_right hU5 (pow_nonneg hUpos.le 15)
      nlinarith [this, pow_pos hUpos 15]
    nlinarith [mul_le_mul_of_nonneg_right hkkey
        (by positivity : (0:ℝ) ≤ P.G * S.Δ ^ 2 * (P.H * S.Ω ^ 6)),
      hΔpos, hGpos, hHpos, hUpos, hΩpos]
  -- ====================================================================
  -- TERM 2 : (dt^4/(6Xa)) * E2 ≤ δ₂₃/3
  -- ====================================================================
  have hT2 : dt ^ 4 / (6 * P.X * (a : ℝ)) * E2
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) / 3 := by
    rw [hT2eq]
    have hZ2 : ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2
        ≤ (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2 := by
      have s1 : ℓ₁ * |ℓ₂ * b₀ + v| ≤ (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) :=
        mul_le_mul hℓ1W' hℓ2b0v_M (abs_nonneg _) (by positivity)
      have s2 : ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 ≤ (3 * 10 ^ 20 * M) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) hfac2
      have s3 : 0 ≤ ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 := by positivity
      have s4 : 0 ≤ (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) := by positivity
      exact mul_le_mul s1 s2 s3 s4
    have hZ2_nn : 0 ≤ ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2 := by positivity
    have hstep : (400 / 6) * dt ^ 4
          * (ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2) / d ^ 6
        ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4)
            * ((130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2) / S.D ^ 6 := by
      apply div_le_div₀ (by positivity)
      · have a1 : (400 / 6 : ℝ) * dt ^ 4 ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4) := by
          have : (0:ℝ) ≤ 400 / 6 := by norm_num
          nlinarith [hdt4, this]
        have a2 : 0 ≤ (400 / 6 : ℝ) * (18 ^ 4 * S.D ^ 4) := by positivity
        calc (400 / 6 : ℝ) * dt ^ 4 * (ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2)
            ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4)
                * (ℓ₁ * |ℓ₂ * b₀ + v| * ((a : ℝ) + |ℓ₂ * b₀ + v|) ^ 2) :=
              mul_le_mul_of_nonneg_right a1 hZ2_nn
          _ ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4)
                * ((130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2) :=
              mul_le_mul_of_nonneg_left hZ2 a2
      · positivity
      · exact hd6
    refine le_trans hstep ?_
    -- collapse into explicit single fraction
    have hBeq : (400 / 6) * (18 ^ 4 * S.D ^ 4)
            * ((130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2) / S.D ^ 6
        = (16376256000000000000000000000000000000000000000000000000000000000000000 : ℝ)
            * (P.G * P.U ^ 20 * S.Δ ^ 4) / (P.H ^ 2 * S.Ω ^ 9) := by
      rw [hM_def, hSDeq]; field_simp; ring
    rw [hBeq]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- reduces (via hkey: Δ²U^6 ≤ HΩ³) to 3*const*Δ² ≤ U^6*Δ² ≤ HΩ³ ⋅ (...)
    have hconst : (16376256000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3 ≤ P.U ^ 6 := by
      have : ((10:ℝ) ^ 33) ^ 6 ≤ P.U ^ 6 := pow_le_pow_left₀ (by norm_num) hUbig 6
      calc (16376256000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3
          ≤ ((10:ℝ) ^ 33) ^ 6 := by norm_num
        _ ≤ P.U ^ 6 := this
    -- 3*const*Δ² ≤ U^6*Δ² ≤ (HΩ³)  (hkey)
    have hstep2 : (16376256000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3 * S.Δ ^ 2 ≤ P.H * S.Ω ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_right hconst (by positivity : (0:ℝ) ≤ S.Δ ^ 2)
      calc (16376256000000000000000000000000000000000000000000000000000000000000000 : ℝ) * 3 * S.Δ ^ 2
          ≤ P.U ^ 6 * S.Δ ^ 2 := h1
        _ = S.Δ ^ 2 * P.U ^ 6 := by ring
        _ ≤ P.H * S.Ω ^ 3 := hkey
    nlinarith [mul_le_mul_of_nonneg_right hstep2
        (by positivity : (0:ℝ) ≤ P.G * P.U ^ 20 * S.Δ ^ 2 * (P.H * S.Ω ^ 6)),
      hΔpos, hGpos, hHpos, hUpos, hΩpos]
  -- ====================================================================
  -- TERM 3 : (dt^4/(6Xa)) * E3 ≤ δ₂₃/3
  -- ====================================================================
  have hT3 : dt ^ 4 / (6 * P.X * (a : ℝ)) * E3
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) / 3 := by
    rw [hT3eq]
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      have : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
      rw [this] at hb0; exact hb0
    have hZ3 : ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2
        ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
            * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) * (400000000000000 * M) ^ 2 := by
      have s12 : ℓ₂ * ℓ₁ ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul hℓ2W' hℓ1W' hℓ1nn (by positivity)
      have s12b : ℓ₂ * ℓ₁ * |b₀|
          ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
              * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) := by
        apply mul_le_mul s12 hb0' hb0nn (by positivity)
      have s3 : ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 ≤ (400000000000000 * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfac3 2
      have s3nn : 0 ≤ ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 := by positivity
      have s12bnn : 0 ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
          * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) := by positivity
      exact mul_le_mul s12b s3 s3nn s12bnn
    have hZ3_nn : 0 ≤ ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2 := by positivity
    have hstep : (400 / 6) * dt ^ 4 * (ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2) / d ^ 6
        ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4)
            * ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
                * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
                * (400000000000000 * M) ^ 2) / S.D ^ 6 := by
      apply div_le_div₀ (by positivity)
      · have a1 : (400 / 6 : ℝ) * dt ^ 4 ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4) := by
          nlinarith [hdt4]
        have a2 : 0 ≤ (400 / 6 : ℝ) * (18 ^ 4 * S.D ^ 4) := by positivity
        calc (400 / 6 : ℝ) * dt ^ 4 * (ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2)
            ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4)
                * (ℓ₂ * ℓ₁ * |b₀| * ((a : ℝ) + ℓ₁ * |b₀|) ^ 2) :=
              mul_le_mul_of_nonneg_right a1 hZ3_nn
          _ ≤ (400 / 6) * (18 ^ 4 * S.D ^ 4)
                * ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
                    * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
                    * (400000000000000 * M) ^ 2) :=
              mul_le_mul_of_nonneg_left hZ3 a2
      · positivity
      · exact hd6
    refine le_trans hstep ?_
    have hBeq : (400 / 6) * (18 ^ 4 * S.D ^ 4)
            * ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
                * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
                * (400000000000000 * M) ^ 2) / S.D ^ 6
        = (56771020800000000000000000000000000000000000000000000 : ℝ)
            * (P.G * P.U ^ 20 * S.Δ ^ 4) / (P.H ^ 2 * S.Ω ^ 9) := by
      rw [hM_def, hSDeq]; field_simp; ring
    rw [hBeq]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hconst : (56771020800000000000000000000000000000000000000000000 : ℝ) * 3 ≤ P.U ^ 6 := by
      have : ((10:ℝ) ^ 33) ^ 6 ≤ P.U ^ 6 := pow_le_pow_left₀ (by norm_num) hUbig 6
      calc (56771020800000000000000000000000000000000000000000000 : ℝ) * 3
          ≤ ((10:ℝ) ^ 33) ^ 6 := by norm_num
        _ ≤ P.U ^ 6 := this
    have hstep2 : (56771020800000000000000000000000000000000000000000000 : ℝ) * 3 * S.Δ ^ 2 ≤ P.H * S.Ω ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_right hconst (by positivity : (0:ℝ) ≤ S.Δ ^ 2)
      calc (56771020800000000000000000000000000000000000000000000 : ℝ) * 3 * S.Δ ^ 2
          ≤ P.U ^ 6 * S.Δ ^ 2 := h1
        _ = S.Δ ^ 2 * P.U ^ 6 := by ring
        _ ≤ P.H * S.Ω ^ 3 := hkey
    nlinarith [mul_le_mul_of_nonneg_right hstep2
        (by positivity : (0:ℝ) ≤ P.G * P.U ^ 20 * S.Δ ^ 2 * (P.H * S.Ω ^ 6)),
      hΔpos, hGpos, hHpos, hUpos, hΩpos]
  -- ====================================================================
  -- ASSEMBLE
  -- ====================================================================
  have hsum : dt ^ 4 / (6 * P.X * (a : ℝ)) * (E1 + E2 + E3)
      = dt ^ 4 / (6 * P.X * (a : ℝ)) * E1 + dt ^ 4 / (6 * P.X * (a : ℝ)) * E2
        + dt ^ 4 / (6 * P.X * (a : ℝ)) * E3 := by ring
  rw [hsum]
  have : S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) / 3
      + S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) / 3
      + S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) / 3
      = S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by ring
  linarith [hT1, hT2, hT3, this]

end Squarefree
