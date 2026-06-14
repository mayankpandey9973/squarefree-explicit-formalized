import Squarefree.Lower.DefectBounds

/-!
# §5 Step-1 phase monotonicity: scale bounds for `d̃‴` and the monotonicity quantity

Two window-arithmetic scale bounds on the defect inverse `d̃ₐ(r) = dtilde P.X r a`:

  * `|d̃‴(r)| ≤ C₃ · D/R³`              (`dtilde_d3_upper`),
  * `2·d̃″(r)·d̃(r) − 5·d̃′(r)² ≥ c_M · D²/R²`   (`dtilde_M_lower`).

These come from the closed forms in `DefectDeriv` and the `d̃`-window `D/10 ≤ d̃ ≤ 18D`
(`dtilde_asymp_D`).  We bound numerator and denominator separately, then combine via
`le_div_iff₀` / `div_le_iff₀`.  Constants are intentionally loose (internal, absorbed).
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **`|d̃‴(r)| ≤ C₃·D/R³`.**  In the §5 regime, the third `r`-derivative of `d̃ₐ` is
bounded in absolute value by `10¹⁹·(D/R³)`. -/
theorem dtilde_d3_upper {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    |iteratedDeriv 3 (fun s => dtilde P.X s a) r| ≤ 10000000000000000000 * (S.D / S.R ^ 3) := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  -- the defect-inverse window
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  set d := dtilde P.X r a with hd_def
  have ha_hiD : a ≤ (11/10) * S.D := by linarith
  -- closed form of the third derivative
  rw [dtilde_r_iteratedDeriv3 P.X_pos ha0 hr0]
  -- abbreviations
  set Poly := 5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4
    with hPoly_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  set Num3 := 3 * d * (d + a) * Poly with hNum3_def
  set Den3 := 8 * r ^ 3 * (a + 2 * d) ^ 5 with hDen3_def
  have hNum3_pos : 0 < Num3 := by rw [hNum3_def]; positivity
  have hDen3_pos : 0 < Den3 := by rw [hDen3_def]; positivity
  -- the iteratedDeriv value as written: `-3*d*(d+a)*Poly / (8 r³ (a+2d)⁵)`
  -- rewrite the messy form so the abs equals Num3/Den3
  have habs : |(-3 * d * (d + a) * Poly / Den3)| = Num3 / Den3 := by
    rw [abs_div, hNum3_def, hDen3_def]
    rw [abs_of_pos (show (0:ℝ) < 8 * r ^ 3 * (a + 2 * d) ^ 5 by positivity)]
    congr 1
    rw [abs_of_neg (show -3 * d * (d + a) * Poly < 0 by nlinarith [hPoly_pos, hd_pos, ha0])]
    ring
  -- match the goal's expression to `-3*d*(d+a)*Poly / Den3`
  have hmatch : (-3 * d * (d + a)
        * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
        / (8 * r ^ 3 * (a + 2 * d) ^ 5))
      = -3 * d * (d + a) * Poly / Den3 := by
    rw [hPoly_def, hDen3_def]
  rw [hmatch, habs]
  -- numerator upper bound: Num3 ≤ 10¹⁰ · D⁶
  -- factor 1: 3 d (d+a) ≤ 3 · 18D · 20D = 1080 D²
  have hf1 : 3 * d * (d + a) ≤ 1080 * S.D ^ 2 := by
    nlinarith [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  have hf1_nn : (0:ℝ) ≤ 3 * d * (d + a) := by positivity
  -- factor 2: Poly ≤ 8000000 · D⁴, bounded term by term (using a ≤ 1.1D, d ≤ 18D)
  have hf2 : Poly ≤ 8000000 * S.D ^ 4 := by
    rw [hPoly_def]
    have hp1 : 5 * a ^ 4 ≤ 5 * ((11/10) * S.D) ^ 4 := by
      have := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 4; nlinarith [this]
    have hp2 : 34 * a ^ 3 * d ≤ 34 * ((11/10) * S.D) ^ 3 * (18 * S.D) := by
      have h3 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 3
      nlinarith [h3, hd_hi, hDpos, pow_pos hDpos 3, ha0, hd_pos]
    have hp3 : 94 * a ^ 2 * d ^ 2 ≤ 94 * ((11/10) * S.D) ^ 2 * (18 * S.D) ^ 2 := by
      have h2 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 2
      have hd2 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 2
      nlinarith [h2, hd2, pow_pos hDpos 2]
    have hp4 : 120 * a * d ^ 3 ≤ 120 * ((11/10) * S.D) * (18 * S.D) ^ 3 := by
      have hd3 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 3
      nlinarith [ha_hiD, hd3, pow_pos hDpos 3, ha0, hd_pos]
    have hp5 : 60 * d ^ 4 ≤ 60 * (18 * S.D) ^ 4 := by
      have := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 4; nlinarith [this]
    nlinarith [hp1, hp2, hp3, hp4, hp5, pow_pos hDpos 4]
  have hNum3_hi : Num3 ≤ 9000000000 * S.D ^ 6 := by
    rw [hNum3_def]
    have hmul := mul_le_mul hf1 hf2 (le_of_lt hPoly_pos) (by positivity)
    calc 3 * d * (d + a) * Poly
        ≤ (1080 * S.D ^ 2) * (8000000 * S.D ^ 4) := hmul
      _ ≤ 9000000000 * S.D ^ 6 := by nlinarith [pow_pos hDpos 6]
  -- denominator lower bound: Den3 ≥ R³ D⁵ / 200000000
  -- r³ ≥ (R/72)³ = R³/373248
  have hr3_lo : S.R ^ 3 / 373248 ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (1/72) * S.R) hr_lo 3
    calc S.R ^ 3 / 373248 = ((1/72) * S.R) ^ 3 := by ring
      _ ≤ r ^ 3 := this
  -- (a+2d)⁵ ≥ (2d)⁵ ≥ (D/5)⁵ = D⁵/3125  (since a>0, 2d ≥ D/5)
  have h2d_lo : S.D / 5 ≤ a + 2 * d := by linarith
  have hpow5_lo : S.D ^ 5 / 3125 ≤ (a + 2 * d) ^ 5 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 5) h2d_lo 5
    calc S.D ^ 5 / 3125 = (S.D / 5) ^ 5 := by ring
      _ ≤ (a + 2 * d) ^ 5 := this
  have hDen3_lo : S.R ^ 3 * S.D ^ 5 / 200000000 ≤ Den3 := by
    rw [hDen3_def]
    have hmul := mul_le_mul hr3_lo hpow5_lo (by positivity) (by positivity)
    calc S.R ^ 3 * S.D ^ 5 / 200000000
        ≤ 8 * ((S.R ^ 3 / 373248) * (S.D ^ 5 / 3125)) := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith [mul_pos (pow_pos hRpos 3) (pow_pos hDpos 5)]
      _ ≤ 8 * (r ^ 3 * (a + 2 * d) ^ 5) := by nlinarith [hmul]
      _ = 8 * r ^ 3 * (a + 2 * d) ^ 5 := by ring
  -- combine: Num3/Den3 ≤ 10¹⁹ · D/R³
  rw [div_le_iff₀ hDen3_pos]
  -- 10¹⁹ · (D/R³) · Den3 ≥ 10¹⁹ · (D/R³) · (R³D⁵/2e8) = 5·10¹⁰ · D⁶ ≥ 10¹⁰ D⁶ ≥ Num3
  have hstep : 10000000000000000000 * (S.D / S.R ^ 3) * (S.R ^ 3 * S.D ^ 5 / 200000000)
      ≤ 10000000000000000000 * (S.D / S.R ^ 3) * Den3 :=
    mul_le_mul_of_nonneg_left hDen3_lo (by positivity)
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have heq : 10000000000000000000 * (S.D / S.R ^ 3) * (S.R ^ 3 * S.D ^ 5 / 200000000)
      = 50000000000 * S.D ^ 6 := by field_simp; ring
  have hle : (9000000000 : ℝ) * S.D ^ 6 ≤ 50000000000 * S.D ^ 6 := by
    nlinarith [pow_pos hDpos 6]
  calc Num3 ≤ 9000000000 * S.D ^ 6 := hNum3_hi
    _ ≤ 50000000000 * S.D ^ 6 := hle
    _ = 10000000000000000000 * (S.D / S.R ^ 3) * (S.R ^ 3 * S.D ^ 5 / 200000000) := by rw [heq]
    _ ≤ 10000000000000000000 * (S.D / S.R ^ 3) * Den3 := hstep

/-- **`M(r) := 2·d̃″(r)·d̃(r) − 5·d̃′(r)² ≥ c_M·D²/R²`.**  In the §5 regime, the Step-1
monotonicity quantity is bounded below by `D²/(10¹²·R²)`. -/
theorem dtilde_M_lower {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    S.D ^ 2 / (1000000000000 * S.R ^ 2)
      ≤ 2 * iteratedDeriv 2 (fun s => dtilde P.X s a) r * dtilde P.X r a
        - 5 * (deriv (fun s => dtilde P.X s a) r) ^ 2 := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  -- the defect-inverse window
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  set d := dtilde P.X r a with hd_def
  have ha_hiD : a ≤ (11/10) * S.D := by linarith
  -- rewrite the two derivatives to their closed forms
  rw [dtilde_r_iteratedDeriv2 P.X_pos ha0 hr0, (dtilde_r_hasDerivAt P.X_pos ha0 hr0).deriv]
  -- the LHS-expression equals the positive closed form via `dtilde_mono_leading`
  obtain ⟨hmono_eq, _hmono_pos⟩ := dtilde_mono_leading (X := P.X) (a := a) (r := r) P.X_pos ha0 hr0
  -- align the goal's expression with `dtilde_mono_leading`'s LHS
  have halign : 2 * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
          / (4 * r ^ 2 * (a + 2 * d) ^ 3)) * d
        - 5 * (- d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
      = d ^ 2 * (d + a) * (a ^ 2 + 5 * a * d + 10 * d ^ 2)
          / (4 * r ^ 2 * (a + 2 * d) ^ 3) := by
    have hsq : (- d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
        = (d * (d + a) / (2 * r * (a + 2 * d))) ^ 2 := by
      rw [show - d * (d + a) / (2 * r * (a + 2 * d))
            = - (d * (d + a) / (2 * r * (a + 2 * d))) by ring, neg_pow, pow_two]
      ring
    rw [hsq]; exact hmono_eq
  rw [halign]
  -- abbreviations for the positive closed form PF = NumM / DenM
  set NumM := d ^ 2 * (d + a) * (a ^ 2 + 5 * a * d + 10 * d ^ 2) with hNumM_def
  set DenM := 4 * r ^ 2 * (a + 2 * d) ^ 3 with hDenM_def
  have hNumM_pos : 0 < NumM := by rw [hNumM_def]; positivity
  have hDenM_pos : 0 < DenM := by rw [hDenM_def]; positivity
  -- numerator lower bound: NumM ≥ D⁵/10000
  -- d² ≥ D²/100 ; d+a ≥ d ≥ D/10 ; a²+5ad+10d² ≥ 10 d² ≥ D²/10
  have hNumM_lo : S.D ^ 5 / 10000 ≤ NumM := by
    rw [hNumM_def]
    have hg1 : S.D ^ 2 / 100 ≤ d ^ 2 := by nlinarith [hd_lo, hd_pos, hDpos]
    have hg2 : S.D / 10 ≤ d + a := by linarith
    have hg3 : S.D ^ 2 / 10 ≤ a ^ 2 + 5 * a * d + 10 * d ^ 2 := by
      nlinarith [hd_lo, hd_pos, ha0, hDpos]
    have hmul1 := mul_le_mul hg1 hg2 (by positivity) (by positivity : (0:ℝ) ≤ d ^ 2)
    have hmul2 := mul_le_mul hmul1 hg3 (by positivity)
      (by positivity : (0:ℝ) ≤ d ^ 2 * (d + a))
    calc S.D ^ 5 / 10000
        ≤ (S.D ^ 2 / 100) * (S.D / 10) * (S.D ^ 2 / 10) := by nlinarith [pow_pos hDpos 5]
      _ ≤ d ^ 2 * (d + a) * (a ^ 2 + 5 * a * d + 10 * d ^ 2) := hmul2
  -- denominator upper bound: DenM ≤ 60000000 R² D³
  -- r² ≤ 256 R² ; (a+2d)³ ≤ (38D)³ = 54872 D³
  have hr2_hi : r ^ 2 ≤ 256 * S.R ^ 2 := by nlinarith [hr_hi, hr0, hRpos]
  have hs_hi : a + 2 * d ≤ 38 * S.D := by linarith
  have hcube_hi : (a + 2 * d) ^ 3 ≤ 54872 * S.D ^ 3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ a + 2 * d) hs_hi 3
    calc (a + 2 * d) ^ 3 ≤ (38 * S.D) ^ 3 := this
      _ = 54872 * S.D ^ 3 := by ring
  have hDenM_hi : DenM ≤ 60000000 * S.R ^ 2 * S.D ^ 3 := by
    rw [hDenM_def]
    have hmul := mul_le_mul hr2_hi hcube_hi (by positivity)
      (by positivity : (0:ℝ) ≤ 256 * S.R ^ 2)
    calc 4 * r ^ 2 * (a + 2 * d) ^ 3 = 4 * (r ^ 2 * (a + 2 * d) ^ 3) := by ring
      _ ≤ 4 * ((256 * S.R ^ 2) * (54872 * S.D ^ 3)) := by nlinarith [hmul]
      _ ≤ 60000000 * S.R ^ 2 * S.D ^ 3 := by
          nlinarith [mul_pos (pow_pos hRpos 2) (pow_pos hDpos 3)]
  -- combine: NumM/DenM ≥ D²/(10¹² R²)
  rw [le_div_iff₀ hDenM_pos]
  -- D²/(10¹² R²) · DenM ≤ D²/(10¹² R²) · 60000000 R²D³ = 60000000 D⁵/10¹² ≤ D⁵/10000 ≤ NumM
  have hstep : S.D ^ 2 / (1000000000000 * S.R ^ 2) * DenM
      ≤ S.D ^ 2 / (1000000000000 * S.R ^ 2) * (60000000 * S.R ^ 2 * S.D ^ 3) :=
    mul_le_mul_of_nonneg_left hDenM_hi (by positivity)
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have heq : S.D ^ 2 / (1000000000000 * S.R ^ 2) * (60000000 * S.R ^ 2 * S.D ^ 3)
      = 60000000 * S.D ^ 5 / 1000000000000 := by field_simp
  have hle : (60000000 : ℝ) * S.D ^ 5 / 1000000000000 ≤ S.D ^ 5 / 10000 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith [pow_pos hDpos 5]
  calc S.D ^ 2 / (1000000000000 * S.R ^ 2) * DenM
      ≤ 60000000 * S.D ^ 5 / 1000000000000 := by rw [heq] at hstep; exact hstep
    _ ≤ S.D ^ 5 / 10000 := hle
    _ ≤ NumM := hNumM_lo

end Squarefree
