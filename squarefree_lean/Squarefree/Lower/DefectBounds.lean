import Squarefree.Lower.DefectDeriv
import Squarefree.Lower.DefectRegime

/-!
# §5 scale bounds for the defect-inverse derivatives `d̃ₐ'(r)` and `d̃ₐ''(r)`

In the §5 regime (`a ≍ A`, `r ≍ R`, `d̃ ≍ D`) we give two-sided absolute-constant scale
bounds for the first and second `r`-derivatives of `d̃ₐ(r) = dtilde P.X r a`:

  `|d̃ₐ'(r)| ≍ B = D/R`,      `d̃ₐ''(r) ≍ B/R = D/R²  (> 0)`.

The closed forms come from `DefectDeriv`; the `d̃`-window `D/10 ≤ d̃ ≤ 18D` from
`dtilde_asymp_D` (`DefectRegime`).  We bound numerator and denominator separately, then
combine via `le_div_iff₀` / `div_le_iff₀`.  Constants are intentionally loose.
-/

namespace Squarefree

open Real

/-- **`|d̃ₐ'(r)| ≍ B`.**  In the §5 regime, the first `r`-derivative of `d̃ₐ` satisfies
`B/1000000 ≤ |d̃ₐ'(r)| ≤ 1000000·B`, where `B = D/R`. -/
theorem dtilde_d1_bounds {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    S.B / 1000000 ≤ |deriv (fun s => dtilde P.X s a) r|
      ∧ |deriv (fun s => dtilde P.X s a) r| ≤ 1000000 * S.B := by
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
  -- `a` window in terms of `D`
  have ha_hiD : a ≤ (11/10) * S.D := by linarith
  -- closed form of the derivative; it is negative
  have hderiv : deriv (fun s => dtilde P.X s a) r
      = - d * (d + a) / (2 * r * (a + 2 * d)) := (dtilde_r_hasDerivAt P.X_pos ha0 hr0).deriv
  -- positive numerator / denominator
  set Num := d * (d + a) with hNum_def
  set Den := 2 * r * (a + 2 * d) with hDen_def
  have hNum_pos : 0 < Num := by rw [hNum_def]; positivity
  have hDen_pos : 0 < Den := by rw [hDen_def]; positivity
  -- `|deriv| = Num/Den`
  have habs : |deriv (fun s => dtilde P.X s a) r| = Num / Den := by
    rw [hderiv]
    have : - d * (d + a) / (2 * r * (a + 2 * d)) = - (Num / Den) := by
      rw [hNum_def, hDen_def]; ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
  rw [habs]
  -- numerator bounds
  have hNum_lo : S.D ^ 2 / 100 ≤ Num := by
    rw [hNum_def]; nlinarith only [hd_lo, ha0, hd_pos, hDpos]
  have hNum_hi : Num ≤ 360 * S.D ^ 2 := by
    rw [hNum_def]; nlinarith only [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  -- denominator bounds
  have hDen_lo : S.R * S.D / 180 ≤ Den := by
    rw [hDen_def]
    -- a + 2d ≥ 2(D/10) = D/5 ; r ≥ R/72
    have h1 : S.D / 5 ≤ a + 2 * d := by linarith
    have h2 : (1/72) * S.R ≤ r := hr_lo
    nlinarith only [h1, h2, hRpos, hDpos, ha0, hd_pos]
  have hDen_hi : Den ≤ 1300 * S.R * S.D := by
    rw [hDen_def]
    -- a + 2d ≤ 1.1D + 36D = 37.1D ≤ 38D ; r ≤ 16R
    have h1 : a + 2 * d ≤ 38 * S.D := by linarith
    have h2 : r ≤ 16 * S.R := hr_hi
    nlinarith only [h1, h2, hRpos, hDpos, ha0, hd_pos, hr0]
  -- combine: lower
  refine ⟨?_, ?_⟩
  · -- B/1000000 ≤ Num/Den
    rw [Scale.B_eq_D_div_R, le_div_iff₀ hDen_pos]
    -- (D/R)/1000000 * Den ≤ Num ; use Den ≤ 1300 R D and Num ≥ D²/100
    -- D/(1000000 R) * Den ≤ D/(1000000 R) * 1300 R D = 1300 D²/1000000 ≤ D²/100 ≤ Num
    have hstep : S.D / S.R / 1000000 * Den ≤ S.D / S.R / 1000000 * (1300 * S.R * S.D) :=
      mul_le_mul_of_nonneg_left hDen_hi (by positivity)
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    have heq : S.D / S.R / 1000000 * (1300 * S.R * S.D) = 1300 * S.D ^ 2 / 1000000 := by
      field_simp
    have hle : (1300 : ℝ) * S.D ^ 2 / 1000000 ≤ S.D ^ 2 / 100 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith [pow_pos hDpos 2]
    calc S.D / S.R / 1000000 * Den
        ≤ 1300 * S.D ^ 2 / 1000000 := by rw [heq] at hstep; exact hstep
      _ ≤ S.D ^ 2 / 100 := hle
      _ ≤ Num := hNum_lo
  · -- Num/Den ≤ 1000000 * B
    rw [Scale.B_eq_D_div_R, div_le_iff₀ hDen_pos]
    -- Num ≤ 1000000 * (D/R) * Den ; use Num ≤ 360 D² and Den ≥ R D/180
    have hstep : 1000000 * (S.D / S.R) * (S.R * S.D / 180)
        ≤ 1000000 * (S.D / S.R) * Den :=
      mul_le_mul_of_nonneg_left hDen_lo (by positivity)
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    have heq : 1000000 * (S.D / S.R) * (S.R * S.D / 180) = 1000000 * S.D ^ 2 / 180 := by
      field_simp
    have hle : (360 : ℝ) * S.D ^ 2 ≤ 1000000 * S.D ^ 2 / 180 := by
      rw [le_div_iff₀ (by norm_num)]; linarith [pow_pos hDpos 2]
    calc Num ≤ 360 * S.D ^ 2 := hNum_hi
      _ ≤ 1000000 * S.D ^ 2 / 180 := hle
      _ = 1000000 * (S.D / S.R) * (S.R * S.D / 180) := by rw [heq]
      _ ≤ 1000000 * (S.D / S.R) * Den := hstep

/-- **`d̃ₐ''(r) ≍ B/R` and `> 0`.**  In the §5 regime, the second `r`-derivative of `d̃ₐ`
is positive and satisfies `B/(R·10¹²) ≤ d̃ₐ''(r) ≤ 10¹³·(B/R)`, where `B/R = D/R²`. -/
theorem dtilde_d2_bounds {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    0 < iteratedDeriv 2 (fun s => dtilde P.X s a) r
      ∧ S.B / (S.R * 1000000000000) ≤ iteratedDeriv 2 (fun s => dtilde P.X s a) r
      ∧ iteratedDeriv 2 (fun s => dtilde P.X s a) r ≤ 10000000000000 * (S.B / S.R) := by
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
  -- closed form of the second derivative
  have hderiv : iteratedDeriv 2 (fun s => dtilde P.X s a) r
      = d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
        / (4 * r ^ 2 * (a + 2 * d) ^ 3) := dtilde_r_iteratedDeriv2 P.X_pos ha0 hr0
  set Num2 := d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) with hNum2_def
  set Den2 := 4 * r ^ 2 * (a + 2 * d) ^ 3 with hDen2_def
  have hNum2_pos : 0 < Num2 := by rw [hNum2_def]; positivity
  have hDen2_pos : 0 < Den2 := by rw [hDen2_def]; positivity
  -- positivity of the second derivative
  have hpos : 0 < iteratedDeriv 2 (fun s => dtilde P.X s a) r := by
    rw [hderiv]; exact div_pos hNum2_pos hDen2_pos
  -- the two factor bounds for the numerator
  -- factor 1: d(d+a)
  have hf1_lo : S.D ^ 2 / 100 ≤ d * (d + a) := by nlinarith [hd_lo, ha0, hd_pos, hDpos]
  have hf1_hi : d * (d + a) ≤ 360 * S.D ^ 2 := by
    nlinarith only [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  -- factor 2: 3a² + 10ad + 10d²
  have hf2_lo : S.D ^ 2 / 10 ≤ 3 * a ^ 2 + 10 * a * d + 10 * d ^ 2 := by
    nlinarith only [hd_lo, ha0, hd_pos, hDpos]
  have hf2_hi : 3 * a ^ 2 + 10 * a * d + 10 * d ^ 2 ≤ 3450 * S.D ^ 2 := by
    nlinarith only [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  -- numerator bounds via multiplication
  have hNum2_lo : S.D ^ 4 / 1000 ≤ Num2 := by
    rw [hNum2_def]
    have := mul_le_mul hf1_lo hf2_lo (by positivity) (by positivity)
    calc S.D ^ 4 / 1000 ≤ (S.D ^ 2 / 100) * (S.D ^ 2 / 10) := by nlinarith only [pow_pos hDpos 4]
      _ ≤ d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) := this
  have hNum2_hi : Num2 ≤ 1242000 * S.D ^ 4 := by
    rw [hNum2_def]
    have := mul_le_mul hf1_hi hf2_hi (by positivity) (by positivity : (0:ℝ) ≤ 360 * S.D ^ 2)
    calc d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
        ≤ (360 * S.D ^ 2) * (3450 * S.D ^ 2) := this
      _ ≤ 1242000 * S.D ^ 4 := by nlinarith only [pow_pos hDpos 4]
  -- denominator factor bounds
  -- r² ∈ [R²/5184, 256R²]
  have hr2_lo : S.R ^ 2 / 5184 ≤ r ^ 2 := by nlinarith only [hr_lo, hr0, hRpos]
  have hr2_hi : r ^ 2 ≤ 256 * S.R ^ 2 := by nlinarith only [hr_hi, hr0, hRpos]
  -- (a+2d)³ ∈ [D³/125, (38D)³]
  have hs_lo : S.D / 5 ≤ a + 2 * d := by linarith
  have hs_hi : a + 2 * d ≤ 38 * S.D := by linarith
  have hcube_lo : S.D ^ 3 / 125 ≤ (a + 2 * d) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 5) hs_lo 3
    calc S.D ^ 3 / 125 = (S.D / 5) ^ 3 := by ring
      _ ≤ (a + 2 * d) ^ 3 := this
  have hcube_hi : (a + 2 * d) ^ 3 ≤ 54872 * S.D ^ 3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ a + 2 * d) hs_hi 3
    calc (a + 2 * d) ^ 3 ≤ (38 * S.D) ^ 3 := this
      _ = 54872 * S.D ^ 3 := by ring
  -- Den2 = 4 r² (a+2d)³ bounds
  have hDen2_lo : S.R ^ 2 * S.D ^ 3 / 170000 ≤ Den2 := by
    rw [hDen2_def]
    have hmul := mul_le_mul hr2_lo hcube_lo (by positivity) (by positivity)
    calc S.R ^ 2 * S.D ^ 3 / 170000
        ≤ 4 * ((S.R ^ 2 / 5184) * (S.D ^ 3 / 125)) := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith only [mul_pos (pow_pos hRpos 2) (pow_pos hDpos 3)]
      _ ≤ 4 * (r ^ 2 * (a + 2 * d) ^ 3) := by nlinarith only [hmul]
      _ = 4 * r ^ 2 * (a + 2 * d) ^ 3 := by ring
  have hDen2_hi : Den2 ≤ 56200000 * S.R ^ 2 * S.D ^ 3 := by
    rw [hDen2_def]
    have hmul := mul_le_mul hr2_hi hcube_hi (by positivity)
      (by positivity : (0:ℝ) ≤ 256 * S.R ^ 2)
    calc 4 * r ^ 2 * (a + 2 * d) ^ 3 = 4 * (r ^ 2 * (a + 2 * d) ^ 3) := by ring
      _ ≤ 4 * ((256 * S.R ^ 2) * (54872 * S.D ^ 3)) := by nlinarith only [hmul]
      _ ≤ 56200000 * S.R ^ 2 * S.D ^ 3 := by
          nlinarith only [mul_pos (pow_pos hRpos 2) (pow_pos hDpos 3)]
  -- convert B/R to D/R²
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have hBR : S.B / S.R = S.D / S.R ^ 2 := by
    rw [Scale.B_eq_D_div_R]; field_simp
  refine ⟨hpos, ?_, ?_⟩
  · -- lower bound: B/(R·10¹²) ≤ Num2/Den2
    rw [hderiv, le_div_iff₀ hDen2_pos]
    -- B/(R·10¹²) = (D/R²)/10¹² = D/(R²·10¹²) ; multiply by Den2 ≤ 56200000 R²D³
    have hBR' : S.B / (S.R * 1000000000000) = S.D / (S.R ^ 2 * 1000000000000) := by
      rw [Scale.B_eq_D_div_R]; field_simp
    rw [hBR']
    have hstep : S.D / (S.R ^ 2 * 1000000000000) * Den2
        ≤ S.D / (S.R ^ 2 * 1000000000000) * (56200000 * S.R ^ 2 * S.D ^ 3) :=
      mul_le_mul_of_nonneg_left hDen2_hi (by positivity)
    have heq : S.D / (S.R ^ 2 * 1000000000000) * (56200000 * S.R ^ 2 * S.D ^ 3)
        = 56200000 * S.D ^ 4 / 1000000000000 := by field_simp
    have hle : (56200000 : ℝ) * S.D ^ 4 / 1000000000000 ≤ S.D ^ 4 / 1000 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith [pow_pos hDpos 4]
    calc S.D / (S.R ^ 2 * 1000000000000) * Den2
        ≤ 56200000 * S.D ^ 4 / 1000000000000 := by rw [heq] at hstep; exact hstep
      _ ≤ S.D ^ 4 / 1000 := hle
      _ ≤ Num2 := hNum2_lo
  · -- upper bound: Num2/Den2 ≤ 10¹³ * (B/R)
    rw [hderiv, div_le_iff₀ hDen2_pos, hBR]
    -- 10¹³ * (D/R²) ; Num2 ≤ 1242000 D⁴ , Den2 ≥ R²D³/170000
    have hstep : 10000000000000 * (S.D / S.R ^ 2) * (S.R ^ 2 * S.D ^ 3 / 170000)
        ≤ 10000000000000 * (S.D / S.R ^ 2) * Den2 :=
      mul_le_mul_of_nonneg_left hDen2_lo (by positivity)
    have heq : 10000000000000 * (S.D / S.R ^ 2) * (S.R ^ 2 * S.D ^ 3 / 170000)
        = 10000000000000 * S.D ^ 4 / 170000 := by field_simp
    have hle : (1242000 : ℝ) * S.D ^ 4 ≤ 10000000000000 * S.D ^ 4 / 170000 := by
      rw [le_div_iff₀ (by norm_num)]; linarith [pow_pos hDpos 4]
    calc Num2 ≤ 1242000 * S.D ^ 4 := hNum2_hi
      _ ≤ 10000000000000 * S.D ^ 4 / 170000 := hle
      _ = 10000000000000 * (S.D / S.R ^ 2) * (S.R ^ 2 * S.D ^ 3 / 170000) := by rw [heq]
      _ ≤ 10000000000000 * (S.D / S.R ^ 2) * Den2 := hstep

end Squarefree
