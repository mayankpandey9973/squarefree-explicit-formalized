import Squarefree.Lower.DefectMono
import Squarefree.Lower.DefectBt

/-!
# §5 Step 1 monotonicity core

The smooth Step-1 phase is `φ(r) = K·b̃(r)²/d̃(r)⁵` with `K = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa > 0` and
`b̃ < 0`, so `φ'(r) = K·b̃·d̃⁻⁶·(2·b̃'·d̃ − 5·b̃·d̃')` and `φ' < 0` reduces to the bracket
being positive. After clearing `ℓ₁ > 0` and applying the mean value theorem three times
to convert finite differences into interior derivatives, the bracket reduces to the exact
monotonicity quantity `M = 2·d̃″(r)·d̃(r) − 5·d̃′(r)²` up to an error controlled by `ℓ₁/R`.
The smallness hypothesis `10³³·ℓ₁ ≤ R` makes that error negligible against `M`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- §5 Step 1 monotonicity core: the bracket controlling the sign of `φ'` is bounded
below by `D²/(2·10¹²·R²) > 0`. -/
theorem phi_mono_core {P : Globals} {S : Scale P} {a ℓ₁ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓpos : 0 < ℓ₁)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R) :
    S.D ^ 2 / (2000000000000 * S.R ^ 2)
      ≤ 2 * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁)
              - deriv (fun s => dtilde P.X s a) r) / ℓ₁) * dtilde P.X r a
        - 5 * bt P.X a ℓ₁ r * deriv (fun s => dtilde P.X s a) r := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hr_hi16 : r ≤ 16 * S.R := by linarith
  have hrl0 : 0 < r + ℓ₁ := by linarith
  have hrll_lo : (1/72) * S.R ≤ r + ℓ₁ := by linarith
  set D := S.D with hD_def
  set R := S.R with hR_def
  -- abbreviations for the derivative functions
  -- d̃'  = deriv (fun s => dtilde P.X s a)
  -- d̃'' = iteratedDeriv 2 (fun s => dtilde P.X s a)
  -- d̃'''= iteratedDeriv 3 (fun s => dtilde P.X s a)
  set f0 := fun s => dtilde P.X s a with hf0_def
  set f1 := fun t => deriv (fun u => dtilde P.X u a) t with hf1_def
  set f2 := fun t => iteratedDeriv 2 (fun u => dtilde P.X u a) t with hf2_def
  set f3 := fun t => iteratedDeriv 3 (fun u => dtilde P.X u a) t with hf3_def
  -- interior derivative facts on the relevant intervals (all points are positive)
  -- HasDerivAt f0 (f1 x) x for x > 0
  have hHD0 : ∀ x : ℝ, 0 < x → HasDerivAt f0 (f1 x) x := by
    intro x hx
    have h := dtilde_r_hasDerivAt (X := P.X) (a := a) (r := x) P.X_pos ha0 hx
    have heq : f1 x = (- dtilde P.X x a * (dtilde P.X x a + a) / (2 * x * (a + 2 * dtilde P.X x a))) := by
      simp only [hf1_def]; exact h.deriv
    rw [hf0_def, heq]; exact h
  -- HasDerivAt f1 (f2 x) x for x > 0
  have hHD1 : ∀ x : ℝ, 0 < x → HasDerivAt f1 (f2 x) x := by
    intro x hx
    have h := dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := x) P.X_pos ha0 hx
    rw [hf1_def, hf2_def]; exact h
  -- HasDerivAt f2 (f3 x) x for x > 0
  have hHD2 : ∀ x : ℝ, 0 < x → HasDerivAt f2 (f3 x) x := by
    intro x hx
    have h := dtilde_iteratedDeriv2_hasDerivAt (X := P.X) (a := a) (s := x) P.X_pos ha0 hx
    rw [hf2_def, hf3_def]; exact h
  -- continuity (on any Icc inside the positive ray)
  have hCont0 : ∀ p q : ℝ, 0 < p → ContinuousOn f0 (Set.Icc p q) := by
    intro p q hp
    refine fun x hx => (hHD0 x ?_).continuousAt.continuousWithinAt
    exact lt_of_lt_of_le hp hx.1
  have hCont1 : ∀ p q : ℝ, 0 < p → ContinuousOn f1 (Set.Icc p q) := by
    intro p q hp
    refine fun x hx => (hHD1 x ?_).continuousAt.continuousWithinAt
    exact lt_of_lt_of_le hp hx.1
  have hCont2 : ∀ p q : ℝ, 0 < p → ContinuousOn f2 (Set.Icc p q) := by
    intro p q hp
    refine fun x hx => (hHD2 x ?_).continuousAt.continuousWithinAt
    exact lt_of_lt_of_le hp hx.1
  -- MVT 1: f0 over [r, r+ℓ₁]; slope = f1 η
  obtain ⟨η, hη_mem, hη_eq⟩ :=
    exists_hasDerivAt_eq_slope f0 f1 (show r < r + ℓ₁ by linarith)
      (hCont0 r (r + ℓ₁) hr0) (fun x hx => hHD0 x (lt_trans hr0 hx.1))
  -- (r+ℓ₁) - r = ℓ₁
  have hsub : r + ℓ₁ - r = ℓ₁ := by ring
  rw [hsub] at hη_eq
  -- so dtilde(r+ℓ₁) - dtilde(r) = ℓ₁ * f1 η
  have hD0 : dtilde P.X (r + ℓ₁) a - dtilde P.X r a = ℓ₁ * f1 η := by
    have : f1 η * ℓ₁ = (f0 (r + ℓ₁) - f0 r) := by
      rw [hη_eq]; field_simp
    simp only [hf0_def] at this
    linarith [this]
  -- MVT 2: f1 over [r, r+ℓ₁]; slope = f2 ξ
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope f1 f2 (show r < r + ℓ₁ by linarith)
      (hCont1 r (r + ℓ₁) hr0) (fun x hx => hHD1 x (lt_trans hr0 hx.1))
  rw [hsub] at hξ_eq
  -- so f1(r+ℓ₁) - f1 r = ℓ₁ * f2 ξ
  have hD1 : f1 (r + ℓ₁) - f1 r = ℓ₁ * f2 ξ := by
    have : f2 ξ * ℓ₁ = (f1 (r + ℓ₁) - f1 r) := by rw [hξ_eq]; field_simp
    linarith [this]
  -- restate the goal in terms of f1 and dtilde (definitional folds)
  show D ^ 2 / (2000000000000 * R ^ 2)
        ≤ 2 * ((f1 (r + ℓ₁) - f1 r) / ℓ₁) * dtilde P.X r a
        - 5 * ((dtilde P.X (r + ℓ₁) a - dtilde P.X r a) / ℓ₁) * f1 r
  -- substitute the two finite differences and cancel ℓ₁; reduces to bracket2 > 0
  rw [hD0, hD1]
  -- bracket2 := 2 * f2 ξ * d̃(r) - 5 * f1 η * f1 r
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓpos
  have hgoal_eq : 2 * (ℓ₁ * f2 ξ / ℓ₁) * dtilde P.X r a - 5 * (ℓ₁ * f1 η / ℓ₁) * f1 r
      = 2 * f2 ξ * dtilde P.X r a - 5 * f1 η * f1 r := by
    field_simp
  rw [hgoal_eq]
  -- it now suffices to prove bracket2 := 2*f2 ξ*d̃(r) - 5*f1 η*f1 r > 0
  set bracket2 := 2 * f2 ξ * dtilde P.X r a - 5 * f1 η * f1 r with hbracket2_def
  -- the exact monotonicity quantity M = 2·d̃″(r)·d̃(r) − 5·d̃′(r)²
  set M := 2 * f2 r * dtilde P.X r a - 5 * (f1 r) ^ 2 with hM_def
  -- lower bound for M
  have hM_lower : D ^ 2 / (1000000000000 * R ^ 2) ≤ M := by
    have h := dtilde_M_lower (P := P) (S := S) (a := a) (r := r)
      hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi16
    -- align: f2 r = iteratedDeriv 2 ..., f1 r = deriv ...
    simpa only [hM_def, hf2_def, hf1_def, hD_def, hR_def] using h
  -- window membership of ξ, η
  have hξ_lo : r < ξ := hξ_mem.1
  have hξ_hi : ξ < r + ℓ₁ := hξ_mem.2
  have hη_lo : r < η := hη_mem.1
  have hη_hi : η < r + ℓ₁ := hη_mem.2
  have hξ_pos : 0 < ξ := lt_trans hr0 hξ_lo
  have hη_pos : 0 < η := lt_trans hr0 hη_lo
  -- MVT 3a: f2 on [r, ξ] -> exists ζ ∈ Ioo r ξ, f3 ζ = (f2 ξ - f2 r)/(ξ - r)
  obtain ⟨ζ, hζ_mem, hζ_eq⟩ :=
    exists_hasDerivAt_eq_slope f2 f3 hξ_lo
      (hCont2 r ξ hr0) (fun x hx => hHD2 x (lt_trans hr0 hx.1))
  -- so f2 ξ - f2 r = f3 ζ * (ξ - r)
  have hξr_pos : 0 < ξ - r := by linarith
  have hD2 : f2 ξ - f2 r = f3 ζ * (ξ - r) := by
    have := hζ_eq
    field_simp at this ⊢
    linarith [this]
  -- MVT 3b: f1 on [r, η] -> exists ζ' ∈ Ioo r η, f2 ζ' = (f1 η - f1 r)/(η - r)
  obtain ⟨ζ', hζ'_mem, hζ'_eq⟩ :=
    exists_hasDerivAt_eq_slope f1 f2 hη_lo
      (hCont1 r η hr0) (fun x hx => hHD1 x (lt_trans hr0 hx.1))
  have hηr_pos : 0 < η - r := by linarith
  have hD3 : f1 η - f1 r = f2 ζ' * (η - r) := by
    have := hζ'_eq
    field_simp at this ⊢
    linarith [this]
  -- B = D/R
  have hB_eq : S.B = D / R := by rw [Scale.B_eq_D_div_R, hD_def, hR_def]
  -- window bounds for ζ and ζ'
  have hζ_lo : r < ζ := hζ_mem.1
  have hζ_hi : ζ < ξ := hζ_mem.2
  have hζ_pos : 0 < ζ := lt_trans hr0 hζ_lo
  have hζ_win_lo : (1/72) * R ≤ ζ := le_of_lt (lt_of_le_of_lt hr_lo hζ_lo)
  have hζ_win_hi : ζ ≤ 16 * R := by
    have : ζ < 16 * R := by linarith [hζ_hi, hξ_hi, hrl_hi]
    linarith
  have hζ'_lo : r < ζ' := hζ'_mem.1
  have hζ'_hi : ζ' < η := hζ'_mem.2
  have hζ'_pos : 0 < ζ' := lt_trans hr0 hζ'_lo
  have hζ'_win_lo : (1/72) * R ≤ ζ' := le_of_lt (lt_of_le_of_lt hr_lo hζ'_lo)
  have hζ'_win_hi : ζ' ≤ 16 * R := by
    have : ζ' < 16 * R := by linarith [hζ'_hi, hη_hi, hrl_hi]
    linarith
  -- bound |f3 ζ| ≤ 10^19 * (D/R^3)
  have hf3_bound : |f3 ζ| ≤ 10000000000000000000 * (D / R ^ 3) := by
    have h := dtilde_d3_upper (P := P) (S := S) (a := a) (r := ζ)
      hAD ha0 hζ_pos ha_lo ha_hi hζ_win_lo hζ_win_hi
    simpa only [hf3_def, hD_def, hR_def] using h
  -- bound f2 ζ' (positive) ≤ 10^13 * (D/R^2)
  have hf2'_pos_and_ub :
      0 < f2 ζ' ∧ f2 ζ' ≤ 10000000000000 * (D / R ^ 2) := by
    obtain ⟨hpos, _, hub⟩ := dtilde_d2_bounds (P := P) (S := S) (a := a) (r := ζ')
      hAD ha0 hζ'_pos ha_lo ha_hi hζ'_win_lo hζ'_win_hi
    refine ⟨by simpa only [hf2_def] using hpos, ?_⟩
    have hub' : iteratedDeriv 2 (fun s => dtilde P.X s a) ζ' ≤ 10000000000000 * (S.B / S.R) := hub
    rw [hB_eq] at hub'
    have hRpos2 : (0:ℝ) < R := hRpos
    have : D / R / R = D / R ^ 2 := by field_simp
    rw [this] at hub'
    simpa only [hf2_def] using hub'
  obtain ⟨hf2'_pos, hf2'_ub⟩ := hf2'_pos_and_ub
  -- bound dtilde P.X r a ≤ 18 * D
  have hd_ub : dtilde P.X r a ≤ 18 * D := by
    obtain ⟨_, hub⟩ := dtilde_asymp_D (P := P) (S := S) (a := a) (r := r)
      hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi16
    simpa only [hD_def] using hub
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  -- bound |f1 r| ≤ 10^6 * (D/R)
  have hf1_bound : |f1 r| ≤ 1000000 * (D / R) := by
    obtain ⟨_, hub⟩ := dtilde_d1_bounds (P := P) (S := S) (a := a) (r := r)
      hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi16
    rw [hB_eq] at hub
    simpa only [hf1_def] using hub
  -- the difference identity bracket2 - M
  have hdiff_eq : bracket2 - M
      = 2 * (f2 ξ - f2 r) * dtilde P.X r a - 5 * (f1 η - f1 r) * f1 r := by
    rw [hbracket2_def, hM_def]; ring
  -- |f2 ξ - f2 r| ≤ ℓ₁ * (10^19 * (D/R^3))
  have hξdiff_abs : |f2 ξ - f2 r| ≤ ℓ₁ * (10000000000000000000 * (D / R ^ 3)) := by
    rw [hD2, abs_mul, abs_of_pos hξr_pos]
    have hbound : ξ - r ≤ ℓ₁ := by linarith
    calc |f3 ζ| * (ξ - r) ≤ (10000000000000000000 * (D / R ^ 3)) * ℓ₁ := by
            apply mul_le_mul hf3_bound hbound (le_of_lt hξr_pos)
            positivity
      _ = ℓ₁ * (10000000000000000000 * (D / R ^ 3)) := by ring
  -- |f1 η - f1 r| ≤ ℓ₁ * (10^13 * (D/R^2))
  have hηdiff_abs : |f1 η - f1 r| ≤ ℓ₁ * (10000000000000 * (D / R ^ 2)) := by
    rw [hD3, abs_mul, abs_of_pos hηr_pos]
    have hbound : η - r ≤ ℓ₁ := by linarith
    have hf2'_abs : |f2 ζ'| ≤ 10000000000000 * (D / R ^ 2) := by
      rw [abs_of_pos hf2'_pos]; exact hf2'_ub
    calc |f2 ζ'| * (η - r) ≤ (10000000000000 * (D / R ^ 2)) * ℓ₁ := by
            apply mul_le_mul hf2'_abs hbound (le_of_lt hηr_pos)
            positivity
      _ = ℓ₁ * (10000000000000 * (D / R ^ 2)) := by ring
  -- perturbation bound: |bracket2 - M| ≤ 41*10^19 * ℓ₁ * D^2 / R^3
  have hf1r_abs := hf1_bound
  -- term-wise bounds
  have hT1 : 2 * |f2 ξ - f2 r| * dtilde P.X r a
      ≤ 2 * (ℓ₁ * (10000000000000000000 * (D / R ^ 3))) * (18 * D) := by
    have h1 : 2 * |f2 ξ - f2 r| ≤ 2 * (ℓ₁ * (10000000000000000000 * (D / R ^ 3))) := by
      linarith [hξdiff_abs]
    apply mul_le_mul h1 hd_ub (le_of_lt hd_pos)
    have : (0:ℝ) ≤ ℓ₁ := le_of_lt hℓpos
    positivity
  have hT2 : 5 * |f1 η - f1 r| * |f1 r|
      ≤ 5 * (ℓ₁ * (10000000000000 * (D / R ^ 2))) * (1000000 * (D / R)) := by
    have h1 : 5 * |f1 η - f1 r| ≤ 5 * (ℓ₁ * (10000000000000 * (D / R ^ 2))) := by
      linarith [hηdiff_abs]
    apply mul_le_mul h1 hf1r_abs (abs_nonneg _)
    have : (0:ℝ) ≤ ℓ₁ := le_of_lt hℓpos
    positivity
  have hpert : |bracket2 - M| ≤ 410000000000000000000 * ℓ₁ * D ^ 2 / R ^ 3 := by
    rw [hdiff_eq]
    have htri : |2 * (f2 ξ - f2 r) * dtilde P.X r a - 5 * (f1 η - f1 r) * f1 r|
        ≤ 2 * |f2 ξ - f2 r| * dtilde P.X r a + 5 * |f1 η - f1 r| * |f1 r| := by
      calc |2 * (f2 ξ - f2 r) * dtilde P.X r a - 5 * (f1 η - f1 r) * f1 r|
          ≤ |2 * (f2 ξ - f2 r) * dtilde P.X r a| + |5 * (f1 η - f1 r) * f1 r| :=
            abs_sub _ _
        _ = 2 * |f2 ξ - f2 r| * dtilde P.X r a + 5 * |f1 η - f1 r| * |f1 r| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            rw [abs_of_pos hd_pos, show |(2:ℝ)| = 2 from abs_of_pos (by norm_num),
                show |(5:ℝ)| = 5 from abs_of_pos (by norm_num)]
    have hsum : 2 * (ℓ₁ * (10000000000000000000 * (D / R ^ 3))) * (18 * D)
          + 5 * (ℓ₁ * (10000000000000 * (D / R ^ 2))) * (1000000 * (D / R))
        = 410000000000000000000 * ℓ₁ * D ^ 2 / R ^ 3 := by
      have hRne : R ≠ 0 := ne_of_gt hRpos
      field_simp
      norm_num
    calc |2 * (f2 ξ - f2 r) * dtilde P.X r a - 5 * (f1 η - f1 r) * f1 r|
        ≤ 2 * |f2 ξ - f2 r| * dtilde P.X r a + 5 * |f1 η - f1 r| * |f1 r| := htri
      _ ≤ 2 * (ℓ₁ * (10000000000000000000 * (D / R ^ 3))) * (18 * D)
          + 5 * (ℓ₁ * (10000000000000 * (D / R ^ 2))) * (1000000 * (D / R)) := by
            linarith [hT1, hT2]
      _ = 410000000000000000000 * ℓ₁ * D ^ 2 / R ^ 3 := hsum
  -- the perturbation is at most the half-floor D²/(2·10¹²·R²)
  have hkey : 410000000000000000000 * ℓ₁ * D ^ 2 / R ^ 3
      ≤ D ^ 2 / (2000000000000 * R ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- 41e19 * ℓ₁ * D² * (2e12 * R²) ≤ D² * R³
    -- ⟺ 82e31 * ℓ₁ * D² * R² ≤ D² * R³ ; cancel D²,R² > 0 ⟺ 82e31 * ℓ₁ ≤ R
    have hℓR : 820000000000000000000000000000000 * ℓ₁ ≤ R := by
      have h1 : (820000000000000000000000000000000 : ℝ) * ℓ₁
          ≤ 1000000000000000000000000000000000 * ℓ₁ := by
        have : (820000000000000000000000000000000 : ℝ)
            ≤ 1000000000000000000000000000000000 := by norm_num
        nlinarith [hℓpos]
      have h2 : (1000000000000000000000000000000000 : ℝ) * ℓ₁ ≤ R := by
        have : (1000000000000000000000000000000000 : ℝ) = (10:ℝ) ^ 33 := by norm_num
        rw [this]; exact hsmall
      linarith
    -- goal: 41e19 * ℓ₁ * D² * (2e12 * R²) ≤ D² * R³
    have hDR : 0 < D ^ 2 * R ^ 2 := by positivity
    have hstep : 410000000000000000000 * ℓ₁ * D ^ 2 * (2000000000000 * R ^ 2)
        = (820000000000000000000000000000000 * ℓ₁) * (D ^ 2 * R ^ 2) := by ring
    have hrhs : D ^ 2 * R ^ 3 = R * (D ^ 2 * R ^ 2) := by ring
    rw [hstep, hrhs]
    exact mul_le_mul_of_nonneg_right hℓR (le_of_lt hDR)
  -- |bracket2 - M| ≤ D²/(2·10¹²·R²)
  have hpert_le : |bracket2 - M| ≤ D ^ 2 / (2000000000000 * R ^ 2) :=
    le_trans hpert hkey
  -- conclude bracket2 ≥ D²/(2·10¹²·R²)
  -- from M - |bracket2 - M| ≤ bracket2 and the floors D²/(1e12 R²) - D²/(2e12 R²) = D²/(2e12 R²)
  have hfloor : D ^ 2 / (1000000000000 * R ^ 2) - D ^ 2 / (2000000000000 * R ^ 2)
      = D ^ 2 / (2000000000000 * R ^ 2) := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hge := neg_le_of_abs_le hpert_le
  -- bracket2 - M ≥ -D²/(2e12 R²)  ⟹  bracket2 ≥ M - D²/(2e12 R²) ≥ floor - half = half
  linarith [hge, hM_lower, hfloor]

/-- Upper bound on the §5 Step-1 phase bracket `2·b̃'·d̃ − 5·b̃·d̃'`: `|bracket| ≤ 10¹⁵·B²`.
(Companion to `phi_mono_core`'s lower bound; triangle inequality + one MVT, no smallness needed.) -/
theorem phi_bracket_ub {P : Globals} {S : Scale P} {a ℓ₁ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R) :
    |2 * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁)
            - deriv (fun s => dtilde P.X s a) r) / ℓ₁) * dtilde P.X r a
      - 5 * bt P.X a ℓ₁ r * deriv (fun s => dtilde P.X s a) r|
      ≤ 10 ^ 15 * S.B ^ 2 := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by
    unfold Scale.B; have := S.Δ_pos; have := P.G_pos; have := S.Ω_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hr_hi16 : r ≤ 16 * S.R := by linarith
  have hrl0 : 0 < r + ℓ₁ := by linarith
  -- abbreviations
  set f1 := fun t => deriv (fun u => dtilde P.X u a) t with hf1_def
  set f2 := fun t => iteratedDeriv 2 (fun u => dtilde P.X u a) t with hf2_def
  -- HasDerivAt f1 (f2 x) x for x > 0
  have hHD1 : ∀ x : ℝ, 0 < x → HasDerivAt f1 (f2 x) x := by
    intro x hx
    have h := dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := x) P.X_pos ha0 hx
    rw [hf1_def, hf2_def]; exact h
  have hCont1 : ∀ p q : ℝ, 0 < p → ContinuousOn f1 (Set.Icc p q) := by
    intro p q hp
    refine fun x hx => (hHD1 x ?_).continuousAt.continuousWithinAt
    exact lt_of_lt_of_le hp hx.1
  -- MVT on f1 over [r, r+ℓ₁]: slope = f2 ξ for some ξ ∈ Ioo r (r+ℓ₁)
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope f1 f2 (show r < r + ℓ₁ by linarith)
      (hCont1 r (r + ℓ₁) hr0) (fun x hx => hHD1 x (lt_trans hr0 hx.1))
  have hsub : r + ℓ₁ - r = ℓ₁ := by ring
  rw [hsub] at hξ_eq
  -- so (f1 (r+ℓ₁) - f1 r)/ℓ₁ = f2 ξ
  have hslope_eq : (f1 (r + ℓ₁) - f1 r) / ℓ₁ = f2 ξ := by
    rw [← hξ_eq]
  -- window membership of ξ
  have hξ_lo : r < ξ := hξ_mem.1
  have hξ_hi : ξ < r + ℓ₁ := hξ_mem.2
  have hξ_pos : 0 < ξ := lt_trans hr0 hξ_lo
  have hξ_win_lo : (1/72) * S.R ≤ ξ := le_of_lt (lt_of_le_of_lt hr_lo hξ_lo)
  have hξ_win_hi : ξ ≤ 16 * S.R := by linarith [hξ_hi, hrl_hi]
  -- f2 ξ positive and ≤ 10¹³·(B/R)
  obtain ⟨hf2pos, _, hf2ub⟩ := dtilde_d2_bounds (P := P) (S := S) (a := a) (r := ξ)
    hAD ha0 hξ_pos ha_lo ha_hi hξ_win_lo hξ_win_hi
  have hf2pos' : 0 < f2 ξ := by simpa only [hf2_def] using hf2pos
  have hf2ub' : f2 ξ ≤ 10000000000000 * (S.B / S.R) := by simpa only [hf2_def] using hf2ub
  -- |slope| = f2 ξ ≤ 10¹³·(B/R)
  have hslope_abs : |(f1 (r + ℓ₁) - f1 r) / ℓ₁| ≤ 10000000000000 * (S.B / S.R) := by
    rw [hslope_eq, abs_of_pos hf2pos']; exact hf2ub'
  -- d̃ bounds: |d̃| ≤ 18 D
  obtain ⟨_, hd_hi⟩ := dtilde_asymp_D (P := P) (S := S) (a := a) (r := r)
    hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi16
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  have hd_abs : |dtilde P.X r a| ≤ 18 * S.D := by rw [abs_of_pos hd_pos]; exact hd_hi
  -- |bt| ≤ 10⁶ B
  obtain ⟨_, _, hbt_hi⟩ := bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ₁) (r := r)
    hAD ha0 hℓ1 ha_lo ha_hi hr_lo hrl_hi
  -- |d̃'(r)| = |f1 r| ≤ 10⁶ B
  obtain ⟨_, hf1ub⟩ := dtilde_d1_bounds (P := P) (S := S) (a := a) (r := r)
    hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi16
  have hf1r_abs : |f1 r| ≤ 1000000 * S.B := by simpa only [hf1_def] using hf1ub
  -- fold the goal in terms of f1
  show |2 * ((f1 (r + ℓ₁) - f1 r) / ℓ₁) * dtilde P.X r a - 5 * bt P.X a ℓ₁ r * f1 r|
      ≤ 10 ^ 15 * S.B ^ 2
  set slope := (f1 (r + ℓ₁) - f1 r) / ℓ₁ with hslope_def
  -- term 1: |2·slope·d̃| ≤ 2·(10¹³ B/R)·(18 D)
  have hT1 : |2 * slope * dtilde P.X r a| ≤ 2 * (10000000000000 * (S.B / S.R)) * (18 * S.D) := by
    rw [abs_mul, abs_mul, show |(2:ℝ)| = 2 from abs_of_pos (by norm_num)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hslope_abs (by norm_num : (0:ℝ) ≤ 2))
      hd_abs (abs_nonneg _) (by positivity)
    calc 2 * |slope| * |dtilde P.X r a|
        = (2 * |slope|) * |dtilde P.X r a| := by ring
      _ ≤ (2 * (10000000000000 * (S.B / S.R))) * (18 * S.D) := h
      _ = 2 * (10000000000000 * (S.B / S.R)) * (18 * S.D) := by ring
  -- term 2: |5·bt·d̃'(r)| ≤ 5·(10⁶ B)·(10⁶ B)
  have hT2 : |5 * bt P.X a ℓ₁ r * f1 r| ≤ 5 * (1000000 * S.B) * (1000000 * S.B) := by
    rw [abs_mul, abs_mul, show |(5:ℝ)| = 5 from abs_of_pos (by norm_num)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hbt_hi (by norm_num : (0:ℝ) ≤ 5))
      hf1r_abs (abs_nonneg _) (by positivity)
    calc 5 * |bt P.X a ℓ₁ r| * |f1 r|
        = (5 * |bt P.X a ℓ₁ r|) * |f1 r| := by ring
      _ ≤ (5 * (1000000 * S.B)) * (1000000 * S.B) := h
      _ = 5 * (1000000 * S.B) * (1000000 * S.B) := by ring
  -- triangle inequality
  have htri : |2 * slope * dtilde P.X r a - 5 * bt P.X a ℓ₁ r * f1 r|
      ≤ |2 * slope * dtilde P.X r a| + |5 * bt P.X a ℓ₁ r * f1 r| := abs_sub _ _
  -- combine: bound ≤ 36·10¹³·(B·D/R) + 5·10¹²·B²
  have hcombine : 2 * (10000000000000 * (S.B / S.R)) * (18 * S.D)
      + 5 * (1000000 * S.B) * (1000000 * S.B) ≤ 10 ^ 15 * S.B ^ 2 := by
    -- B·D/R = B² since D/R = B
    have hBeq : S.B = S.D / S.R := Scale.B_eq_D_div_R S
    have hRne : S.R ≠ 0 := ne_of_gt hRpos
    have hkey : 2 * (10000000000000 * (S.B / S.R)) * (18 * S.D)
        = 36 * 10 ^ 13 * (S.B * (S.D / S.R)) := by ring
    rw [hkey, ← hBeq]
    -- 36·10¹³·B² + 5·10¹²·B² = 36.5·10¹³·B² ≤ 10¹⁵·B²
    nlinarith [sq_nonneg S.B, hBpos]
  linarith [htri, hT1, hT2, hcombine]

end Squarefree
