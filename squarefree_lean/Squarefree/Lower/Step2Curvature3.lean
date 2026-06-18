import Squarefree.Lower.Step2Curvature2

/-!
# §5 Step-2 BANDS: `φ_f''` bounds, sign-definiteness, and the `hmono`/`hlower` facts

Built on the second-derivative *infrastructure* of `Step2Curvature2` (the explicit values
`phi_iteratedDeriv2_eq`, `phif_iteratedDeriv2_eq`), this file supplies the analytic content that
discharges the two remaining deferred hypotheses of `step2_subset_count`:

* `phi_iteratedDeriv2_ub` — `|φ''| ≤ 10⁵⁰·L/R²` (the curvature scale of the Step-1 phase).
* `phif_iteratedDeriv2_sign` — `φ_f''` is sign-definite (sign of `f`) in the strongly `f`-large
  regime; the curvature input for monotonicity.
* `phif_deriv_monotoneOrAntitoneOn` — **`hmono`**: `deriv φ_f` is `MonotoneOn`/`AntitoneOn`.
* `phif_curvature_lower` — **`hlower`** (the faithful `≍` form of writeup line 924):
  `(1/10²⁰)·T₀/R ≤ |φ_f'| + R·|φ_f''|`, `T₀ = |f|·D⁴/(XA)`.  See the note there on why the
  *literal* bare-`T₀` hypothesis of `step2_subset_count` needs the constant-calibrated `T`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 400000

/-- **`|φ''|` upper bound at the `L/R²`-scale**: `|φ''| ≤ 10⁵⁰·L/R²`, `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵)`.
The §5 Step-2 second-derivative companion of `phi_deriv_ub`.  Each of the three product-rule
pieces of `φ'' = K·(b̃'·bracket + b̃·bracket' − 6 b̃·bracket·d̃'/d̃)/d̃⁶` is `≍ L/R²`. -/
theorem phi_iteratedDeriv2_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R) :
    |iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r|
      ≤ 10 ^ 50 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R ^ 2)) := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  -- d̃ bounds and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  -- B = D/R
  have hBeq : S.B = S.D / S.R := Scale.B_eq_D_div_R S
  -- the explicit value of φ''
  rw [phi_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne]
  -- abbreviations
  set f1 := fun t => deriv (fun u => dtilde P.X u a) t with hf1_def
  set f2 := fun t => iteratedDeriv 2 (fun u => dtilde P.X u a) t with hf2_def
  -- MVT helpers (on the positive ray)
  have hHD1 : ∀ x : ℝ, 0 < x → HasDerivAt f1 (f2 x) x := by
    intro x hx
    have h := dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := x) P.X_pos ha0 hx
    rw [hf1_def, hf2_def]; exact h
  have hHD2 : ∀ x : ℝ, 0 < x →
      HasDerivAt f2 (iteratedDeriv 3 (fun u => dtilde P.X u a) x) x := by
    intro x hx
    have h := dtilde_iteratedDeriv2_hasDerivAt (X := P.X) (a := a) (s := x) P.X_pos ha0 hx
    rw [hf2_def]; exact h
  have hCont1 : ∀ p q : ℝ, 0 < p → ContinuousOn f1 (Set.Icc p q) := by
    intro p q hp x hx
    exact (hHD1 x (lt_of_lt_of_le hp hx.1)).continuousAt.continuousWithinAt
  have hCont2 : ∀ p q : ℝ, 0 < p → ContinuousOn f2 (Set.Icc p q) := by
    intro p q hp x hx
    exact (hHD2 x (lt_of_lt_of_le hp hx.1)).continuousAt.continuousWithinAt
  -- bp := (f1 (r+ℓ₁) − f1 r)/ℓ₁ = f2 ξ ;  |bp| ≤ 10¹³·(B/R)
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope f1 f2 (show r < r + ℓ₁ by linarith)
      (hCont1 r (r + ℓ₁) hr0) (fun x hx => hHD1 x (lt_trans hr0 hx.1))
  have hsub : r + ℓ₁ - r = ℓ₁ := by ring
  rw [hsub] at hξ_eq
  have hξ_pos : 0 < ξ := lt_trans hr0 hξ_mem.1
  have hξ_lo : (1/72) * S.R ≤ ξ := le_of_lt (lt_of_le_of_lt hr_lo hξ_mem.1)
  have hξ_hi : ξ ≤ 16 * S.R := by linarith [hξ_mem.2, hrl_hi]
  have hbp_eq : (f1 (r + ℓ₁) - f1 r) / ℓ₁ = f2 ξ := by rw [← hξ_eq]
  obtain ⟨hf2ξ_pos, _, hf2ξ_ub⟩ := dtilde_d2_bounds (P := P) (S := S) (a := a) (r := ξ)
    hAD ha0 hξ_pos ha_lo ha_hi hξ_lo hξ_hi
  have hbp_ub : |(f1 (r + ℓ₁) - f1 r) / ℓ₁| ≤ 10 ^ 13 * (S.B / S.R) := by
    rw [hbp_eq, abs_of_pos hf2ξ_pos]
    calc f2 ξ ≤ 10000000000000 * (S.B / S.R) := by simpa only [hf2_def] using hf2ξ_ub
      _ = 10 ^ 13 * (S.B / S.R) := by norm_num
  -- bd := (f2 (r+ℓ₁) − f2 r)/ℓ₁ = f3 ζ ;  |bd| ≤ 10¹⁹·(D/R³)
  obtain ⟨ζ, hζ_mem, hζ_eq⟩ :=
    exists_hasDerivAt_eq_slope f2 (fun t => iteratedDeriv 3 (fun u => dtilde P.X u a) t)
      (show r < r + ℓ₁ by linarith)
      (hCont2 r (r + ℓ₁) hr0) (fun x hx => hHD2 x (lt_trans hr0 hx.1))
  rw [hsub] at hζ_eq
  have hζ_pos : 0 < ζ := lt_trans hr0 hζ_mem.1
  have hζ_lo : (1/72) * S.R ≤ ζ := le_of_lt (lt_of_le_of_lt hr_lo hζ_mem.1)
  have hζ_hi : ζ ≤ 16 * S.R := by linarith [hζ_mem.2, hrl_hi]
  have hbd_eq : (f2 (r + ℓ₁) - f2 r) / ℓ₁ = iteratedDeriv 3 (fun u => dtilde P.X u a) ζ := by
    rw [← hζ_eq]
  have hbd_ub : |(f2 (r + ℓ₁) - f2 r) / ℓ₁| ≤ 10 ^ 19 * (S.D / S.R ^ 3) := by
    rw [hbd_eq]
    calc |iteratedDeriv 3 (fun u => dtilde P.X u a) ζ|
        ≤ 10000000000000000000 * (S.D / S.R ^ 3) :=
          dtilde_d3_upper (P := P) (S := S) (a := a) (r := ζ) hAD ha0 hζ_pos ha_lo ha_hi hζ_lo hζ_hi
      _ = 10 ^ 19 * (S.D / S.R ^ 3) := by norm_num
  -- remaining scale bounds at `r`
  obtain ⟨_, _, hbt_hi⟩ := bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ₁) (r := r)
    hAD ha0 hℓ1 ha_lo ha_hi hr_lo hrl_hi
  obtain ⟨_, hf1r_hi⟩ := dtilde_d1_bounds (P := P) (S := S) (a := a) (r := r)
    hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hf1r_hi' : |f1 r| ≤ 1000000 * S.B := by simpa only [hf1_def] using hf1r_hi
  obtain ⟨hf2r_pos, _, hf2r_hi⟩ := dtilde_d2_bounds (P := P) (S := S) (a := a) (r := r)
    hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hf2r_hi' : |f2 r| ≤ 10000000000000 * (S.B / S.R) := by
    rw [hf2_def, abs_of_pos hf2r_pos]; simpa only [hf2_def] using hf2r_hi
  have hbracket_ub := phi_bracket_ub (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (r := r)
    hAD ha0 ha_lo ha_hi hℓ1 hr_lo hrl_hi
  -- name the symbolic atoms
  set d := dtilde P.X r a with hd_def
  set b := bt P.X a ℓ₁ r with hb_def
  set d1 := f1 r with hd1_def
  set d2 := f2 r with hd2_def
  set bp := (f1 (r + ℓ₁) - f1 r) / ℓ₁ with hbp_def
  set bd := (f2 (r + ℓ₁) - f2 r) / ℓ₁ with hbd_def
  set bracket := 2 * bp * d - 5 * b * d1 with hbracket_def
  -- collect absolute bounds (all nonneg RHS, in terms of B, D, R)
  have hd_lo' : S.D / 10 ≤ d := hd_lo
  have hd_hi' : d ≤ 18 * S.D := hd_hi
  have hb_abs : |b| ≤ 1000000 * S.B := hbt_hi
  have hbracket_abs : |bracket| ≤ 10 ^ 15 * S.B ^ 2 := by
    rw [hbracket_def, hbp_def, hb_def, hd_def, hd1_def, hf1_def]; exact hbracket_ub
  -- bracket'(r) := 2·bd·d − 3·bp·d1 − 5·b·d2
  set bracketd := 2 * bd * d - 3 * bp * d1 - 5 * b * d2 with hbracketd_def
  -- |bracketd| ≤ 2·(10¹⁹ D/R³)(18D) + 3·(10¹³ B/R)(10⁶ B) + 5·(10⁶ B)(10¹³ B/R)
  -- all ≍ B²/R = D²/R³;  use B = D/R to combine into a B² coefficient.
  -- We bound everything in terms of B and 1/R powers via B = D/R.
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  -- |d| ≤ 18 D = 18 B R
  have hd_abs : |d| ≤ 18 * S.B * S.R := by
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) hd_lo')]
    calc d ≤ 18 * S.D := hd_hi'
      _ = 18 * S.B * S.R := by rw [hBeq]; field_simp
  have hbp_abs : |bp| ≤ 10 ^ 13 * (S.B / S.R) := hbp_ub
  have hbd_abs : |bd| ≤ 10 ^ 19 * (S.D / S.R ^ 3) := hbd_ub
  have hd1_abs : |d1| ≤ 1000000 * S.B := hf1r_hi'
  have hd2_abs : |d2| ≤ 10000000000000 * (S.B / S.R) := hf2r_hi'
  -- D = B R
  have hD_eq : S.D = S.B * S.R := by rw [hBeq]; field_simp
  -- triangle bound on |bracketd| ≤ C_bracketd · B²/R
  have hbracketd_abs : |bracketd| ≤ (2 * 10 ^ 19 * 18 + 3 * 10 ^ 13 * 10 ^ 6
      + 5 * 10 ^ 6 * 10 ^ 13) * (S.B ^ 2 / S.R) := by
    have ht1 : |2 * bd * d| ≤ 2 * (10 ^ 19 * (S.D / S.R ^ 3)) * (18 * S.B * S.R) := by
      rw [abs_mul, abs_mul, show |(2:ℝ)| = 2 from abs_of_pos (by norm_num)]
      have := mul_le_mul (mul_le_mul_of_nonneg_left hbd_abs (by norm_num : (0:ℝ) ≤ 2))
        hd_abs (abs_nonneg _) (by positivity)
      calc 2 * |bd| * |d| = (2 * |bd|) * |d| := by ring
        _ ≤ (2 * (10 ^ 19 * (S.D / S.R ^ 3))) * (18 * S.B * S.R) := this
        _ = 2 * (10 ^ 19 * (S.D / S.R ^ 3)) * (18 * S.B * S.R) := by ring
    have ht2 : |3 * bp * d1| ≤ 3 * (10 ^ 13 * (S.B / S.R)) * (1000000 * S.B) := by
      rw [abs_mul, abs_mul, show |(3:ℝ)| = 3 from abs_of_pos (by norm_num)]
      have := mul_le_mul (mul_le_mul_of_nonneg_left hbp_abs (by norm_num : (0:ℝ) ≤ 3))
        hd1_abs (abs_nonneg _) (by positivity)
      calc 3 * |bp| * |d1| = (3 * |bp|) * |d1| := by ring
        _ ≤ (3 * (10 ^ 13 * (S.B / S.R))) * (1000000 * S.B) := this
        _ = 3 * (10 ^ 13 * (S.B / S.R)) * (1000000 * S.B) := by ring
    have ht3 : |5 * b * d2| ≤ 5 * (1000000 * S.B) * (10000000000000 * (S.B / S.R)) := by
      rw [abs_mul, abs_mul, show |(5:ℝ)| = 5 from abs_of_pos (by norm_num)]
      have := mul_le_mul (mul_le_mul_of_nonneg_left hb_abs (by norm_num : (0:ℝ) ≤ 5))
        hd2_abs (abs_nonneg _) (by positivity)
      calc 5 * |b| * |d2| = (5 * |b|) * |d2| := by ring
        _ ≤ (5 * (1000000 * S.B)) * (10000000000000 * (S.B / S.R)) := this
        _ = 5 * (1000000 * S.B) * (10000000000000 * (S.B / S.R)) := by ring
    have htri : |bracketd| ≤ |2 * bd * d| + |3 * bp * d1| + |5 * b * d2| := by
      rw [hbracketd_def]
      calc |2 * bd * d - 3 * bp * d1 - 5 * b * d2|
          ≤ |2 * bd * d - 3 * bp * d1| + |5 * b * d2| := abs_sub _ _
        _ ≤ (|2 * bd * d| + |3 * bp * d1|) + |5 * b * d2| := by
            have := abs_sub (2 * bd * d) (3 * bp * d1); linarith
        _ = |2 * bd * d| + |3 * bp * d1| + |5 * b * d2| := by ring
    -- the three RHS bounds all equal (coeff)·B²/R using D = B·R
    have heq1 : 2 * (10 ^ 19 * (S.D / S.R ^ 3)) * (18 * S.B * S.R)
        = (2 * 10 ^ 19 * 18) * (S.B ^ 2 / S.R) := by
      rw [hD_eq]; field_simp
    have heq2 : 3 * (10 ^ 13 * (S.B / S.R)) * (1000000 * S.B)
        = (3 * 10 ^ 13 * 10 ^ 6) * (S.B ^ 2 / S.R) := by field_simp; ring
    have heq3 : 5 * (1000000 * S.B) * (10000000000000 * (S.B / S.R))
        = (5 * 10 ^ 6 * 10 ^ 13) * (S.B ^ 2 / S.R) := by field_simp; ring
    rw [heq1] at ht1; rw [heq2] at ht2; rw [heq3] at ht3
    have hsum : (2 * 10 ^ 19 * 18) * (S.B ^ 2 / S.R) + (3 * 10 ^ 13 * 10 ^ 6) * (S.B ^ 2 / S.R)
        + (5 * 10 ^ 6 * 10 ^ 13) * (S.B ^ 2 / S.R)
        = (2 * 10 ^ 19 * 18 + 3 * 10 ^ 13 * 10 ^ 6 + 5 * 10 ^ 6 * 10 ^ 13) * (S.B ^ 2 / S.R) := by
      ring
    linarith [htri, ht1, ht2, ht3, hsum.ge, hsum.le]
  -- the value is `K · (bp·bracket + b·bracketd − 6·b·bracket·d1/d) / d⁶`
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hKpos : 0 < K := by rw [hK_def]; positivity
  -- fold the goal's value to the `K · inner / d⁶` shape
  set inner := bp * bracket + b * bracketd - 6 * b * bracket * d1 / d with hinner_def
  -- |inner| bound
  have hd_pos' : 0 < d := lt_of_lt_of_le (by positivity) hd_lo'
  have hdne : d ≠ 0 := ne_of_gt hd_pos'
  set Cbd := (2 * 10 ^ 19 * 18 + 3 * 10 ^ 13 * 10 ^ 6 + 5 * 10 ^ 6 * 10 ^ 13 : ℝ) with hCbd_def
  -- |bp·bracket| ≤ (10¹³ B/R)(10¹⁵ B²)
  have hP1 : |bp * bracket| ≤ (10 ^ 13 * (S.B / S.R)) * (10 ^ 15 * S.B ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hbp_abs hbracket_abs (abs_nonneg _) (by positivity)
  -- |b·bracketd| ≤ (10⁶ B)·Cbd·(B²/R)
  have hP2 : |b * bracketd| ≤ (1000000 * S.B) * (Cbd * (S.B ^ 2 / S.R)) := by
    rw [abs_mul]
    exact mul_le_mul hb_abs hbracketd_abs (abs_nonneg _) (by positivity)
  -- |6·b·bracket·d1/d| ≤ 6·(10⁶B)(10¹⁵B²)(10⁶B)/(D/10)
  have hP3 : |6 * b * bracket * d1 / d| ≤ 6 * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2)
      * (1000000 * S.B) / (S.D / 10) := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, show |(6:ℝ)| = 6 from abs_of_pos (by norm_num),
        abs_of_pos hd_pos']
    have hnum : (6:ℝ) * |b| * |bracket| * |d1|
        ≤ 6 * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) * (1000000 * S.B) := by
      have hbb : 6 * |b| ≤ 6 * (1000000 * S.B) :=
        mul_le_mul_of_nonneg_left hb_abs (by norm_num)
      have h12 : 6 * |b| * |bracket| ≤ 6 * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) :=
        mul_le_mul hbb hbracket_abs (abs_nonneg _) (by positivity)
      exact mul_le_mul h12 hd1_abs (abs_nonneg _) (by positivity)
    apply div_le_div₀ (by positivity) hnum (by positivity) hd_lo'
  -- |inner| ≤ sum of the three (all ≍ B³/R)
  have hinner_abs : |inner| ≤
      (10 ^ 13 * (S.B / S.R)) * (10 ^ 15 * S.B ^ 2)
      + (1000000 * S.B) * (Cbd * (S.B ^ 2 / S.R))
      + 6 * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) * (1000000 * S.B) / (S.D / 10) := by
    rw [hinner_def]
    calc |bp * bracket + b * bracketd - 6 * b * bracket * d1 / d|
        ≤ |bp * bracket + b * bracketd| + |6 * b * bracket * d1 / d| := abs_sub _ _
      _ ≤ (|bp * bracket| + |b * bracketd|) + |6 * b * bracket * d1 / d| := by
          have := abs_add_le (bp * bracket) (b * bracketd); linarith
      _ ≤ _ := by linarith [hP1, hP2, hP3]
  -- the three sum terms in terms of B³/R using D = B R
  have hbnd : (10 ^ 13 * (S.B / S.R)) * (10 ^ 15 * S.B ^ 2)
      + (1000000 * S.B) * (Cbd * (S.B ^ 2 / S.R))
      + 6 * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) * (1000000 * S.B) / (S.D / 10)
      ≤ (10 ^ 28 + 10 ^ 6 * Cbd + 6 * 10 ^ 28) * (S.B ^ 3 / S.R) := by
    have hT1 : (10 ^ 13 * (S.B / S.R)) * (10 ^ 15 * S.B ^ 2) = 10 ^ 28 * (S.B ^ 3 / S.R) := by
      field_simp
    have hT2 : (1000000 * S.B) * (Cbd * (S.B ^ 2 / S.R)) = 10 ^ 6 * Cbd * (S.B ^ 3 / S.R) := by
      field_simp; ring
    have hT3 : 6 * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) * (1000000 * S.B) / (S.D / 10)
        = 6 * 10 ^ 28 * (S.B ^ 3 / S.R) := by
      rw [hD_eq]; field_simp; ring
    rw [hT1, hT2, hT3]; apply le_of_eq; ring
  -- now bound |φ''| = K·|inner|/d⁶ ≤ K·(coeff·B³/R)/(D/10)⁶
  have hd6_lo : (S.D / 10) ^ 6 ≤ d ^ 6 := pow_le_pow_left₀ (by positivity) hd_lo' 6
  have hd6_pos : 0 < d ^ 6 := by positivity
  -- |value| = K·|inner|/d⁶
  have hval_abs : |K * inner / d ^ 6| = K * |inner| / d ^ 6 := by
    rw [abs_div, abs_mul, abs_of_pos hKpos, abs_of_pos hd6_pos]
  -- the goal value matches `K * inner / d^6`
  show |K * inner / d ^ 6| ≤ _
  rw [hval_abs]
  set Ccoef := (10 ^ 28 + 10 ^ 6 * Cbd + 6 * 10 ^ 28 : ℝ) with hCcoef_def
  have hCcoef_pos : 0 < Ccoef := by rw [hCcoef_def, hCbd_def]; norm_num
  -- numerator: K·|inner| ≤ K·(Ccoef·B³/R)
  have hnum_le : K * |inner| ≤ K * (Ccoef * (S.B ^ 3 / S.R)) :=
    mul_le_mul_of_nonneg_left (le_trans hinner_abs hbnd) hKpos.le
  -- assemble: K·|inner|/d⁶ ≤ K·(Ccoef B³/R)/(D/10)⁶
  have hstep : K * |inner| / d ^ 6
      ≤ K * (Ccoef * (S.B ^ 3 / S.R)) / (S.D / 10) ^ 6 :=
    div_le_div₀ (by positivity) hnum_le (by positivity) hd6_lo
  refine le_trans hstep ?_
  -- RHS = (Ccoef·10⁶) · K · B³/(D⁶·R), and K·X·a·B³/D⁶ → scale 11/(GΩ⁵R)
  -- rewrite to (12·Ccoef·10⁶)·ℓ₁ℓ₂(ℓ₂−ℓ₁)·(XaB³/D⁶)/R
  have hRHS_eq : K * (Ccoef * (S.B ^ 3 / S.R)) / (S.D / 10) ^ 6
      = (12 * Ccoef * 10 ^ 6 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
          * ((P.X * a * S.B ^ 3 / S.D ^ 6) / S.R) := by
    rw [hK_def]; field_simp
  rw [hRHS_eq]
  -- scale: X·a·B³/D⁶ ≤ 11·(1/(G·Ω⁵·R))
  have hsc : P.X * a * S.B ^ 3 / S.D ^ 6 ≤ 11 * (1 / (P.G * S.Ω ^ 5 * S.R)) := by
    have hbase := defect_XAB3_div_D6' S
    have hle : P.X * a * S.B ^ 3 / S.D ^ 6 ≤ P.X * (11 * S.A) * S.B ^ 3 / S.D ^ 6 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hfac : P.X * a * S.B ^ 3 = (P.X * S.B ^ 3) * a := by ring
      have hfac2 : P.X * (11 * S.A) * S.B ^ 3 = (P.X * S.B ^ 3) * (11 * S.A) := by ring
      rw [hfac, hfac2]
      exact mul_le_mul_of_nonneg_left ha_hi (by positivity)
    calc P.X * a * S.B ^ 3 / S.D ^ 6
        ≤ P.X * (11 * S.A) * S.B ^ 3 / S.D ^ 6 := hle
      _ = 11 * (P.X * S.A * S.B ^ 3 / S.D ^ 6) := by ring
      _ = 11 * (1 / (P.G * S.Ω ^ 5 * S.R)) := by rw [hbase]
  -- combine: replace the scale factor, then absorb the numeric coefficient
  have hLR_pos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R ^ 2) := by positivity
  have hstep_sc : (12 * Ccoef * 10 ^ 6 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
        * ((P.X * a * S.B ^ 3 / S.D ^ 6) / S.R)
      ≤ (12 * Ccoef * 10 ^ 6 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
          * ((11 * (1 / (P.G * S.Ω ^ 5 * S.R))) / S.R) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right hsc (by positivity)
  refine le_trans hstep_sc ?_
  -- the scaled term equals (12·Ccoef·10⁶·11)·L/R²
  have heq_sc : (12 * Ccoef * 10 ^ 6 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
          * ((11 * (1 / (P.G * S.Ω ^ 5 * S.R))) / S.R)
      = (12 * Ccoef * 10 ^ 6 * 11)
          * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R ^ 2)) := by
    field_simp
  rw [heq_sc]
  apply mul_le_mul_of_nonneg_right _ hLR_pos.le
  rw [hCcoef_def, hCbd_def]; norm_num

/-- **`φ_f''` is sign-definite (sign of `f`) on the §5 window** (in the strongly `f`-large
regime).  Concretely `f · φ_f''(r) ≥ c·f²·D⁴/(XA·R²) > 0`, with `c = 1/10²⁰`.  The dominant
`(d̃⁴)''·f/(6Xa)`-term carries the sign (`(d̃⁴)'' > 0`); the `φ'`/`φ''` noise terms are
negligible since `L ≤ 10⁻⁹⁰·|f|`.  This is the curvature input for `hmono`. -/
theorem phif_iteratedDeriv2_sign {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    (1 / 10 ^ 16) * (f ^ 2 * S.D ^ 4 / (P.X * S.A * S.R ^ 2))
      ≤ f * iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  -- the L-scale
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  -- W-scale W = D⁴/(XAR)
  set W := S.D ^ 4 / (P.X * S.A * S.R) with hW_def
  have hWpos : 0 < W := by rw [hW_def]; positivity
  have hBR : S.B * S.R = S.D := by rw [Scale.B_eq_D_div_R]; field_simp
  have hDB : S.D ^ 3 * S.B / (P.X * S.A) = W := by
    rw [hW_def, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S.D ^ 3 * P.X * S.A) * hBR
  have hD4 : S.D ^ 4 / (P.X * S.A) = W * S.R := by rw [hW_def]; field_simp
  -- d̃ bounds and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  -- d̃' bounds and d̃'' bounds
  obtain ⟨hd1_lo, hd1_hi⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  obtain ⟨hd2_pos, hd2_lo, hd2_hi⟩ := dtilde_d2_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- |φ| ≤ 10²⁰·L, |φ'| ≤ 10³⁵·L/R, |φ''| ≤ 10⁵⁰·L/R²
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  have hphi''_ub := phi_iteratedDeriv2_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- the explicit value of φ_f''
  rw [phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) ha0 hr0 hrl hℓne]
  -- abbreviations
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun u => dtilde P.X u a) r with hd1_def
  set d2 := iteratedDeriv 2 (fun u => dtilde P.X u a) r with hd2_def
  set φ := phi P.X a ℓ₁ ℓ₂ r with hφ_def
  set φ1 := deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r with hφ1_def
  set φ2 := iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r with hφ2_def
  -- positivity helpers
  have h6Xa_pos : 0 < 6 * P.X * a := by positivity
  have hfabs_nn : (0:ℝ) ≤ |f| := abs_nonneg _
  -- abbreviate the three coefficient terms.
  -- value = E1·(f+φ) + E2·φ1 + E3·φ2  with
  --   E1 = (12 d² d1² + 4 d³ d2)/(6Xa),  E2 = 8 d³ d1/(6Xa),  E3 = d⁴/(6Xa)
  set E1 := (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * P.X * a) with hE1_def
  set E2 := (8 * d ^ 3 * d1) / (6 * P.X * a) with hE2_def
  set E3 := d ^ 4 / (6 * P.X * a) with hE3_def
  -- f · value = E1·f·(f+φ) + f·(E2·φ1 + E3·φ2)
  -- show: lower bound on the main, upper bound on the noise
  -- E1 > 0 (since (d⁴)'' = 12 d²d1² + 4 d³ d2 > 0)
  have hE1_pos : 0 < E1 := by
    rw [hE1_def]; apply div_pos _ h6Xa_pos
    have : 0 < 4 * d ^ 3 * d2 := by
      have : (0:ℝ) < d ^ 3 := by positivity
      have hd2' : 0 < d2 := by rw [hd2_def]; exact hd2_pos
      positivity
    nlinarith only [sq_nonneg d1, sq_nonneg d, this]
  -- |φ| ≤ 10⁻⁹⁰·|f|·... ⇒ f·(f+φ) ≥ f²/2  (strong f-large)
  have hL_le90 : L ≤ (1 / 10 ^ 90) * |f| := by
    have hf90 : (10:ℝ) ^ 90 * L ≤ |f| := hflarge
    linarith only [hf90]
  have hφ_le : φ ≤ 10 ^ 20 * L := hphi_ub
  have hφ_small : φ ≤ (1 / 10 ^ 70) * |f| := by
    have : (10:ℝ) ^ 20 * L ≤ 10 ^ 20 * ((1 / 10 ^ 90) * |f|) :=
      mul_le_mul_of_nonneg_left hL_le90 (by norm_num)
    have h2 : (10:ℝ) ^ 20 * ((1 / 10 ^ 90) * |f|) = (1 / 10 ^ 70) * |f| := by ring
    linarith [hφ_le, this, h2.le, h2.ge]
  have hffφ : f ^ 2 / 2 ≤ f * (f + φ) := by
    have hfφ : f * (f + φ) = f ^ 2 + f * φ := by ring
    have hfφ_lb : f * φ ≥ - (|f| * φ) := by
      have := neg_abs_le (f * φ); rw [abs_mul] at this; rw [abs_of_nonneg hphi_nn] at this; linarith
    have hφf2 : |f| * φ ≤ f ^ 2 / 2 := by
      have h1 : |f| * φ ≤ |f| * ((1 / 10 ^ 70) * |f|) :=
        mul_le_mul_of_nonneg_left hφ_small hfabs_nn
      have h2 : |f| * ((1 / 10 ^ 70) * |f|) = (1 / 10 ^ 70) * |f| ^ 2 := by ring
      have h3 : |f| ^ 2 = f ^ 2 := sq_abs f
      linarith only [h1, h2.le, h2.ge, h3, sq_nonneg f]
    rw [hfφ]; linarith only [hfφ_lb, hφf2]
  -- MAIN: E1·f·(f+φ) ≥ (6/(66·10¹⁴))·W·f²
  -- TIGHTENED: lower-bound E1 through the `12 d̃²(d̃')²` term (no `10¹²` loss).
  -- `d̃ ≥ D/10` and `|d̃'| ≥ B/10⁶` give `12 d̃²(d̃')² ≥ 12·(D/10)²·(B/10⁶)² = 12 D²B²/10¹⁴`,
  -- and `D²B² = D⁴/R²` (since `B = D/R`), so `E1 ≥ (12/(66·10¹⁴))·W/R`.
  have hf2_nn : (0:ℝ) ≤ f ^ 2 := sq_nonneg f
  -- `D²B²/(XA) = W/R`:  `D²B² = D⁴/R²` and `D⁴/(XA) = W·R`.
  have hD2B2 : S.D ^ 2 * S.B ^ 2 / (P.X * S.A) = W / S.R := by
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    rw [hW_def, div_div, div_eq_div_iff (by positivity) (by positivity)]
    have hB : S.B = S.D / S.R := Scale.B_eq_D_div_R S
    rw [hB]; field_simp
  have hE1_lo : (12 / (66 * 10 ^ 14)) * (W / S.R) ≤ E1 := by
    rw [hE1_def]
    -- E1 ≥ 12 d²d1²/(6Xa) ≥ 12(D/10)²(B/10⁶)²/(6·11·XA)
    have hd2' : 0 < d2 := by rw [hd2_def]; exact hd2_pos
    -- `(d̃')² ≥ (B/10⁶)²` from `|d̃'| ≥ B/10⁶`
    have hd1abs_lo : S.B / 1000000 ≤ |d1| := by rw [hd1_def]; exact hd1_lo
    have hd1sq_lo : (S.B / 1000000) ^ 2 ≤ d1 ^ 2 := by
      calc (S.B / 1000000) ^ 2 ≤ |d1| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hd1abs_lo 2
        _ = d1 ^ 2 := sq_abs d1
    have hnum_lo : 12 * (S.D / 10) ^ 2 * (S.B / 1000000) ^ 2
        ≤ 12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2 := by
      have hp1 : (S.D / 10) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hd_lo 2
      have h1 : 12 * (S.D / 10) ^ 2 * (S.B / 1000000) ^ 2 ≤ 12 * d ^ 2 * d1 ^ 2 := by
        have hA : 12 * (S.D / 10) ^ 2 ≤ 12 * d ^ 2 := by linarith only [hp1]
        have hAnn : (0:ℝ) ≤ 12 * (S.D / 10) ^ 2 := by positivity
        have hBnn : (0:ℝ) ≤ (S.B / 1000000) ^ 2 := by positivity
        exact mul_le_mul hA hd1sq_lo hBnn (le_trans hAnn hA)
      have hpos2 : 0 < 4 * d ^ 3 * d2 := by
        have : (0:ℝ) < d ^ 3 := by positivity
        positivity
      linarith [h1, hpos2]
    have hden_le : 6 * P.X * a ≤ 6 * P.X * (11 * S.A) :=
      mul_le_mul_of_nonneg_left ha_hi (by positivity)
    have hdiv_lo : 12 * (S.D / 10) ^ 2 * (S.B / 1000000) ^ 2 / (6 * P.X * (11 * S.A))
        ≤ (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * P.X * a) :=
      div_le_div₀ (by positivity) hnum_lo h6Xa_pos hden_le
    refine le_trans ?_ hdiv_lo
    have hreq : 12 * (S.D / 10) ^ 2 * (S.B / 1000000) ^ 2 / (6 * P.X * (11 * S.A))
        = (12 / (66 * 10 ^ 14)) * (S.D ^ 2 * S.B ^ 2 / (P.X * S.A)) := by
      field_simp; ring
    rw [hreq, hD2B2]
  have hMain : (6 / (66 * 10 ^ 14)) * (W * f ^ 2 / S.R) ≤ E1 * (f * (f + φ)) := by
    have h1 : E1 * (f ^ 2 / 2) ≤ E1 * (f * (f + φ)) :=
      mul_le_mul_of_nonneg_left hffφ hE1_pos.le
    have h2 : (12 / (66 * 10 ^ 14)) * (W / S.R) * (f ^ 2 / 2) ≤ E1 * (f ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hE1_lo (by positivity)
    have h3 : (12 / (66 * 10 ^ 14)) * (W / S.R) * (f ^ 2 / 2)
        = (6 / (66 * 10 ^ 14)) * (W * f ^ 2 / S.R) := by ring
    linarith [h1, h2, h3.le, h3.ge]
  -- NOISE A: |f·E2·φ1| ≤ C₂·10⁻⁵⁵·W·f²/R
  have hE2_abs : |E2| ≤ (8 * 18 ^ 3 * 1000000 * 5 / 6) * W := by
    rw [hE2_def, abs_div, abs_of_pos h6Xa_pos, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 8), abs_of_pos (show (0:ℝ) < d ^ 3 by positivity)]
    have hnum_hi : 8 * d ^ 3 * |d1| ≤ 8 * (18 * S.D) ^ 3 * (1000000 * S.B) := by
      have hp1 : d ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hd_pos.le hd_hi 3
      have h1 : 8 * d ^ 3 ≤ 8 * (18 * S.D) ^ 3 := by linarith [hp1]
      exact mul_le_mul h1 hd1_hi (abs_nonneg _) (by positivity)
    have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a :=
      mul_le_mul_of_nonneg_left ha_lo (by positivity)
    have hstep : 8 * d ^ 3 * |d1| / (6 * P.X * a)
        ≤ 8 * (18 * S.D) ^ 3 * (1000000 * S.B) / (6 * P.X * (S.A / 5)) :=
      div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
    refine le_trans hstep ?_
    have hreq : 8 * (18 * S.D) ^ 3 * (1000000 * S.B) / (6 * P.X * (S.A / 5))
        = (8 * 18 ^ 3 * 1000000 * 5 / 6) * (S.D ^ 3 * S.B / (P.X * S.A)) := by field_simp
    rw [hreq, hDB]
  have hφ1_abs : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
    rw [hφ1_def, hL_def]
    calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
        ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
      _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
  have hNoiseA : |f * (E2 * φ1)| ≤ (8 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 35 * (1 / 10 ^ 90)
      * (W * f ^ 2 / S.R) := by
    rw [abs_mul, abs_mul]
    have hE2φ1 : |E2| * |φ1| ≤ ((8 * 18 ^ 3 * 1000000 * 5 / 6) * W) * (10 ^ 35 * (L / S.R)) :=
      mul_le_mul hE2_abs hφ1_abs (abs_nonneg _) (by positivity)
    have hLf : L ≤ (1 / 10 ^ 90) * |f| := hL_le90
    have hbound : |f| * (|E2| * |φ1|)
        ≤ |f| * (((8 * 18 ^ 3 * 1000000 * 5 / 6) * W) * (10 ^ 35 * ((1 / 10 ^ 90) * |f| / S.R))) := by
      apply mul_le_mul_of_nonneg_left _ hfabs_nn
      refine le_trans hE2φ1 ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right hLf (by positivity)
    refine le_trans hbound ?_
    apply le_of_eq
    have hf2 : |f| * |f| = f ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
    rw [show |f| * (((8 * 18 ^ 3 * 1000000 * 5 / 6) * W)
          * (10 ^ 35 * ((1 / 10 ^ 90) * |f| / S.R)))
        = (8 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 35 * (1 / 10 ^ 90) * (W * (|f| * |f|) / S.R) by ring,
        hf2]
  -- NOISE B: |f·E3·φ2| ≤ C₃·10⁻⁴⁰·W·f²/R
  have hE3_abs : |E3| ≤ (18 ^ 4 * 5 / 6) * (W * S.R) := by
    rw [hE3_def, abs_div, abs_of_pos h6Xa_pos, abs_of_pos (show (0:ℝ) < d ^ 4 by positivity)]
    have hnum_hi : d ^ 4 ≤ (18 * S.D) ^ 4 := pow_le_pow_left₀ hd_pos.le hd_hi 4
    have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a :=
      mul_le_mul_of_nonneg_left ha_lo (by positivity)
    have hstep : d ^ 4 / (6 * P.X * a) ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) :=
      div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
    refine le_trans hstep ?_
    have hreq : (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) = (18 ^ 4 * 5 / 6) * (S.D ^ 4 / (P.X * S.A)) := by
      field_simp
    rw [hreq, hD4]
  have hφ2_abs : |φ2| ≤ 10 ^ 50 * (L / S.R ^ 2) := by
    rw [hφ2_def, hL_def]
    calc |iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r|
        ≤ 10 ^ 50 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R ^ 2)) := hphi''_ub
      _ = 10 ^ 50 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R ^ 2) := by rw [div_div]
  have hNoiseB : |f * (E3 * φ2)| ≤ (18 ^ 4 * 5 / 6) * 10 ^ 50 * (1 / 10 ^ 90)
      * (W * f ^ 2 / S.R) := by
    rw [abs_mul, abs_mul]
    have hE3φ2 : |E3| * |φ2| ≤ ((18 ^ 4 * 5 / 6) * (W * S.R)) * (10 ^ 50 * (L / S.R ^ 2)) :=
      mul_le_mul hE3_abs hφ2_abs (abs_nonneg _) (by positivity)
    have hLf : L ≤ (1 / 10 ^ 90) * |f| := hL_le90
    have hbound : |f| * (|E3| * |φ2|)
        ≤ |f| * (((18 ^ 4 * 5 / 6) * (W * S.R)) * (10 ^ 50 * ((1 / 10 ^ 90) * |f| / S.R ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ hfabs_nn
      refine le_trans hE3φ2 ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right hLf (by positivity)
    refine le_trans hbound ?_
    apply le_of_eq
    have hf2 : |f| * |f| = f ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    rw [show |f| * (((18 ^ 4 * 5 / 6) * (W * S.R))
          * (10 ^ 50 * ((1 / 10 ^ 90) * |f| / S.R ^ 2)))
        = (18 ^ 4 * 5 / 6) * 10 ^ 50 * (1 / 10 ^ 90) * (W * (|f| * |f|)) * (S.R / S.R ^ 2) by ring,
        hf2]
    rw [show S.R / S.R ^ 2 = 1 / S.R by rw [sq]; field_simp]
    ring
  -- combine: f·value ≥ Main − NoiseA − NoiseB ≥ (1/10¹⁶)·W·f²/R
  have hWf2_nn : (0:ℝ) ≤ W * f ^ 2 / S.R := by positivity
  have htgt_eq : (1 / 10 ^ 16) * (f ^ 2 * S.D ^ 4 / (P.X * S.A * S.R ^ 2))
      = (1 / 10 ^ 16) * (W * f ^ 2 / S.R) := by rw [hW_def]; field_simp
  rw [htgt_eq]
  -- f·value = f·(E1·(f+φ)) + f·(E2·φ1) + f·(E3·φ2)
  have hexpand : f * (E1 * (f + φ) + E2 * φ1 + E3 * φ2)
      = E1 * (f * (f + φ)) + f * (E2 * φ1) + f * (E3 * φ2) := by ring
  rw [hexpand]
  have hNA := neg_abs_le (f * (E2 * φ1))
  have hNB := neg_abs_le (f * (E3 * φ2))
  -- numeric coefficient comparison (× the nonneg factor W·f²/R)
  have hcoef : (1 / 10 ^ 16 : ℝ)
      ≤ 6 / (66 * 10 ^ 14) - (8 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 35 * (1 / 10 ^ 90)
        - (18 ^ 4 * 5 / 6) * 10 ^ 50 * (1 / 10 ^ 90) := by norm_num
  have hcoef' : (1 / 10 ^ 16 : ℝ) * (W * f ^ 2 / S.R)
      ≤ (6 / (66 * 10 ^ 14) - (8 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 35 * (1 / 10 ^ 90)
        - (18 ^ 4 * 5 / 6) * 10 ^ 50 * (1 / 10 ^ 90)) * (W * f ^ 2 / S.R) :=
    mul_le_mul_of_nonneg_right hcoef hWf2_nn
  -- f·(E2·φ1) ≥ −|f·E2φ1| ≥ −(c_A·Wf²/R), similarly for E3
  have hA' : -((8 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 35 * (1 / 10 ^ 90) * (W * f ^ 2 / S.R))
      ≤ f * (E2 * φ1) := le_trans (by linarith [hNoiseA]) hNA
  have hB' : -((18 ^ 4 * 5 / 6) * 10 ^ 50 * (1 / 10 ^ 90) * (W * f ^ 2 / S.R))
      ≤ f * (E3 * φ2) := le_trans (by linarith [hNoiseB]) hNB
  linarith only [hMain, hA', hB', hcoef']

/-- **`deriv φ_f` is monotone or antitone on the band window** (`hmono` of `step2_subset_count`).
`φ_f''` is sign-definite (sign of `f`, `phif_iteratedDeriv2_sign`): if `f > 0` it is `> 0` so
`deriv φ_f` is `MonotoneOn`; if `f < 0` it is `< 0` so `deriv φ_f` is `AntitoneOn`. -/
theorem phif_deriv_monotoneOrAntitoneOn {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r₀ r₁ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_band_lo : S.R ≤ r₀) (hr_band_hi : r₁ ≤ 3 * S.R)
    (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hfne : f ≠ 0)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁) := by
  have _ := hr_band_hi  -- faithful signature binder; the window uses `hwin` instead
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hXpos : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  -- every `x` in the window satisfies the `phif_iteratedDeriv2_sign` window hyps
  have hwin_pt : ∀ x ∈ Set.Icc r₀ r₁,
      (1/72) * S.R ≤ x ∧ x + ℓ₁ ≤ 16 * S.R ∧ 0 < x ∧ 0 < x + ℓ₁ := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := Set.mem_Icc.mp hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos (le_trans hr_band_lo hxl)
    refine ⟨?_, ?_, hx0, by linarith⟩
    · nlinarith [hr_band_lo, hxl, hRpos]
    · linarith [hxr, hwin]
  -- `deriv φ_f` is differentiable on the window, with derivative `iteratedDeriv 2 φ_f`
  have hcont : ContinuousOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁) := by
    intro x hx
    obtain ⟨_, _, hx0, hxl0⟩ := hwin_pt x hx
    exact (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 (ne_of_gt hℓ1)).continuousAt.continuousWithinAt
  have hderivOn : DifferentiableOn ℝ (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s))
      (interior (Set.Icc r₀ r₁)) := by
    intro x hx
    have hx' : x ∈ Set.Icc r₀ r₁ := interior_subset hx
    obtain ⟨_, _, hx0, hxl0⟩ := hwin_pt x hx'
    exact (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 (ne_of_gt hℓ1)).differentiableAt.differentiableWithinAt
  -- the second derivative equals deriv (deriv φ_f), with sign of f
  have hsign : ∀ x ∈ Set.Icc r₀ r₁,
      0 < f * deriv (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x := by
    intro x hx
    obtain ⟨hxl, hxr, hx0, hxl0⟩ := hwin_pt x hx
    have hd2 : deriv (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x
        = iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) x :=
      (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
        ha0 hx0 hxl0 (ne_of_gt hℓ1)).deriv
    rw [hd2]
    have hbd := phif_iteratedDeriv2_sign (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hxl hxr hflarge
    have hpos : 0 < (1 / 10 ^ 16) * (f ^ 2 * S.D ^ 4 / (P.X * S.A * S.R ^ 2)) := by
      have hf2 : 0 < f ^ 2 := by positivity
      have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
      positivity
    linarith [hbd, hpos]
  -- split on the sign of f
  rcases lt_or_gt_of_ne hfne with hf_neg | hf_pos
  · -- f < 0  ⇒  deriv (deriv φ_f) ≤ 0  ⇒ AntitoneOn
    right
    apply antitoneOn_of_deriv_nonpos (convex_Icc r₀ r₁) hcont hderivOn
    intro x hx
    have hx' : x ∈ Set.Icc r₀ r₁ := interior_subset hx
    have := hsign x hx'
    nlinarith only [this, hf_neg]
  · -- f > 0  ⇒  deriv (deriv φ_f) ≥ 0  ⇒ MonotoneOn
    left
    apply monotoneOn_of_deriv_nonneg (convex_Icc r₀ r₁) hcont hderivOn
    intro x hx
    have hx' : x ∈ Set.Icc r₀ r₁ := interior_subset hx
    have := hsign x hx'
    nlinarith only [this, hf_pos]

/-- **`|φ_f''|` lower bound at the calibrated curvature scale** (the `T/(2N²) ≤ |φ''|` input of
`bands_count_mono_low`, with `N = R`, `T ≍ |f|D⁴/(XA)`).  Concretely
`(1/10¹⁶)·|f|·D⁴/(XA·R²) ≤ |φ_f''(r)|`, an **absolute** constant (no `X`-growth).  Follows from
`phif_iteratedDeriv2_sign` by dividing `f·φ_f'' ≥ (1/10¹⁶)·f²D⁴/(XAR²)` through `|f|`. -/
theorem phif_iteratedDeriv2_lb {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    (1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A)) / S.R ^ 2
      ≤ |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) := by
    have : 0 < ℓ₂ - ℓ₁ := by linarith
    have : 0 < ℓ₂ := by linarith
    positivity
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by positivity) hflarge
  -- the sign/size bound on f·φ_f''
  have hbd := phif_iteratedDeriv2_sign (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hflarge
  set φ2 := iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r with hφ2_def
  -- |f|·|φ_f''| = |f·φ_f''| ≥ f·φ_f'' ≥ (1/10¹⁶)·f²·D⁴/(XAR²)
  have hlb1 : (1 / 10 ^ 16) * (f ^ 2 * S.D ^ 4 / (P.X * S.A * S.R ^ 2)) ≤ |f| * |φ2| := by
    have h1 : f * φ2 ≤ |f * φ2| := le_abs_self _
    have h2 : |f * φ2| = |f| * |φ2| := abs_mul f φ2
    linarith [hbd, h1, h2.le, h2.ge]
  have hf2eq : f ^ 2 = |f| * |f| := by rw [← abs_mul, abs_mul_self, sq]
  -- divide through |f|: |φ_f''| ≥ (1/10¹⁶)·|f|·D⁴/(XAR²)
  have hφ2_lb : (1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A * S.R ^ 2)) ≤ |φ2| := by
    have hcancel : (1 / 10 ^ 16) * (f ^ 2 * S.D ^ 4 / (P.X * S.A * S.R ^ 2))
        = |f| * ((1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A * S.R ^ 2))) := by
      rw [hf2eq]; field_simp
    rw [hcancel] at hlb1
    exact le_of_mul_le_mul_left hlb1 hfabs_pos
  -- rewrite D⁴/(XAR²) = (D⁴/(XA))/R²
  have heq : (1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A * S.R ^ 2))
      = (1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A)) / S.R ^ 2 := by
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    have hXne : P.X ≠ 0 := ne_of_gt hXpos
    have hAne : S.A ≠ 0 := ne_of_gt hApos
    field_simp
  rw [hφ2_def, ← heq]; exact hφ2_lb

/-- **The §5 Step-2 curvature lower bound** (`hlower`, the faithful `≍` form of writeup line
924).  The variation scale `T₀ := |f|·D⁴/(XA)` satisfies `(1/10¹⁶)·T₀/R ≤ R·|φ_f''| ≤
|φ_f'| + R·|φ_f''|`, with the constant `1/10¹⁶` an **absolute** constant.  The dominant
`12 d̃²(d̃')²·f`-term gives `R·|φ_f''| ≳ T₀/R`.

NOTE on calibration: `R|φ_f''| ≍ T₀/R` only up to an absolute constant (`~10⁻¹⁶`); the bands
variation scale must be `T = c·|f|D⁴/(XA)` with the same `c` that calibrates `hd1`
(`phif_deriv_ub`: `|φ_f'| ≤ 10¹⁴·T₀/R`).  Since both constants here (`10¹⁴` and `10⁻¹⁶`) are
absolute and `X`-independent, a single calibrated `T` discharges `bands_count_mono`. -/
theorem phif_curvature_lower {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    (1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A)) / S.R
      ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r|
        + S.R * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  -- |φ_f''| lower bound (calibrated scale)
  have hφ2_lb := phif_iteratedDeriv2_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hflarge
  set φ2 := iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r with hφ2_def
  -- R·|φ_f''| ≥ (1/10¹⁶)·|f|·D⁴/(XA·R)  (multiply the R² bound by R)
  have hRφ2 : (1 / 10 ^ 16) * (|f| * S.D ^ 4 / (P.X * S.A)) / S.R ≤ S.R * |φ2| := by
    have h := mul_le_mul_of_nonneg_left hφ2_lb hRpos.le
    refine le_trans ?_ h
    apply le_of_eq
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    have hXne : P.X ≠ 0 := ne_of_gt hXpos
    have hAne : S.A ≠ 0 := ne_of_gt hApos
    field_simp
  -- add the nonneg |φ_f'| term
  have hd1_nn : 0 ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := abs_nonneg _
  rw [hφ2_def] at hRφ2 ⊢
  linarith [hRφ2, hd1_nn]

end Squarefree
