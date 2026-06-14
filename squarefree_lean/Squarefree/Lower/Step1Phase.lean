import Squarefree.Lower.Step1Mono
import Squarefree.Lower.DefectScales

/-!
# §5 Step-1 smooth phase `φ`

The §5 Step-1 smooth phase (writeup 836)

  `φ(r) = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)·X·a·b̃ₐ(r)²/d̃ₐ(r)⁵`,

its derivative `φ'(r)` in the factored form `K·b̃·(2·b̃'·d̃ − 5·b̃·d̃')/d̃⁶` with
`K = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa`, and the sign `φ'(r) < 0` (strict decrease), via the positive bracket
from `phi_mono_core`, `b̃ < 0` from `bt_abs_bounds`, and `K > 0`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- The §5 Step-1 smooth phase `φ(r) = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)·X·a·b̃ₐ(r)²/d̃ₐ(r)⁵` (writeup 836). -/
noncomputable def phi (X a ℓ₁ ℓ₂ r : ℝ) : ℝ :=
  12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * (bt X a ℓ₁ r) ^ 2 / (dtilde X r a) ^ 5

/-- Derivative of `φ`, in factored form `K·b̃·(bracket)/d̃⁶` where `K = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa`,
`bracket = 2·b̃'·d̃ − 5·b̃·d̃'` (the `phi_mono_core` quantity). -/
theorem phi_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ r : ℝ} (ha0 : 0 < a) (hr0 : 0 < r)
    (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => phi P.X a ℓ₁ ℓ₂ s)
      (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a * bt P.X a ℓ₁ r
        * (2 * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁)
                  - deriv (fun s => dtilde P.X s a) r) / ℓ₁) * dtilde P.X r a
            - 5 * bt P.X a ℓ₁ r * deriv (fun s => dtilde P.X s a) r)
        / (dtilde P.X r a) ^ 6) r := by
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  set btderiv := (deriv (fun s => dtilde P.X s a) (r + ℓ₁)
      - deriv (fun s => dtilde P.X s a) r) / ℓ₁ with hbtderiv_def
  -- derivative of `b̃`
  have hb : HasDerivAt (fun s => bt P.X a ℓ₁ s) btderiv r :=
    bt_hasDerivAt P.X_pos ha0 hr0 hrl hℓne
  -- derivative of `d̃`
  have hd : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun s => dtilde P.X s a) r) r :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hr0).differentiableAt.hasDerivAt
  -- numerator `K·b̃²`
  have hbsq : HasDerivAt (fun s => (bt P.X a ℓ₁ s) ^ 2)
      (2 * (bt P.X a ℓ₁ r) * btderiv) r := by
    have := hb.pow 2
    simpa using this
  have hnum : HasDerivAt (fun s => K * (bt P.X a ℓ₁ s) ^ 2)
      (K * (2 * (bt P.X a ℓ₁ r) * btderiv)) r := hbsq.const_mul K
  -- denominator `d̃⁵`
  have hden : HasDerivAt (fun s => (dtilde P.X s a) ^ 5)
      (5 * (dtilde P.X r a) ^ 4 * (deriv (fun s => dtilde P.X s a) r)) r := by
    have := hd.pow 5
    simpa using this
  have hd0 : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  have hdne : (dtilde P.X r a) ^ 5 ≠ 0 := pow_ne_zero 5 hd0
  -- quotient rule
  have hquot := hnum.div hden hdne
  -- rewrite `phi` as the quotient, and reconcile values
  have hphi_eq : (fun s => phi P.X a ℓ₁ ℓ₂ s)
      = fun s => (K * (bt P.X a ℓ₁ s) ^ 2) / (dtilde P.X s a) ^ 5 := by
    funext s; simp only [phi, hK_def]
  rw [hphi_eq]
  convert hquot using 1
  -- value reconciliation as rational functions
  rw [hbtderiv_def]
  field_simp

/-- `φ` is strictly decreasing on the §5 window: `φ'(r) < 0`. -/
theorem phi_deriv_neg {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R) :
    deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r < 0 := by
  -- scale positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  -- the derivative value, via `phi_hasDerivAt`
  have hPD := phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r) ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  -- factor pieces
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  set bracket := 2 * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁)
              - deriv (fun s => dtilde P.X s a) r) / ℓ₁) * dtilde P.X r a
            - 5 * bt P.X a ℓ₁ r * deriv (fun s => dtilde P.X s a) r with hbracket_def
  -- K > 0
  have hKpos : 0 < K := by
    rw [hK_def]
    have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
    have hℓ2 : 0 < ℓ₂ := by linarith
    have hX := P.X_pos
    positivity
  -- bracket > 0 (from phi_mono_core, ≥ D²/(2·10¹²·R²) > 0)
  have hbr_pos : 0 < bracket := by
    have h := phi_mono_core (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (r := r)
      hAD ha0 ha_lo ha_hi hℓ1 hr_lo hrl_hi hsmall
    have hfloor_pos : 0 < S.D ^ 2 / (2000000000000 * S.R ^ 2) := by positivity
    rw [hbracket_def]; linarith
  -- b̃ < 0
  have hbt_neg : bt P.X a ℓ₁ r < 0 :=
    (bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ₁) (r := r)
      hAD ha0 hℓ1 ha_lo ha_hi hr_lo hrl_hi).1
  -- d̃⁶ > 0
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  have hd6_pos : 0 < (dtilde P.X r a) ^ 6 := by positivity
  -- numerator K·b̃·bracket < 0
  have hnum_neg : K * bt P.X a ℓ₁ r * bracket < 0 := by
    have hKbr : 0 < K * bracket := mul_pos hKpos hbr_pos
    have : K * bt P.X a ℓ₁ r * bracket = (K * bracket) * bt P.X a ℓ₁ r := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hKbr hbt_neg
  exact div_neg_of_neg_of_pos hnum_neg hd6_pos

/-- `|φ|` upper bound at the `L`-scale `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵)` (writeup 845): `0 ≤ φ ≤ 10²⁰·L`. -/
theorem phi_abs_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R) :
    0 ≤ phi P.X a ℓ₁ ℓ₂ r
      ∧ phi P.X a ℓ₁ ℓ₂ r ≤ 10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  -- d̃ bounds
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  set d := dtilde P.X r a with hd_def
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hKpos : 0 < K := by rw [hK_def]; positivity
  -- bt bound
  obtain ⟨hbt_neg, hbt_lo, hbt_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ₁) (r := r)
      hAD ha0 hℓ1 ha_lo ha_hi hr_lo hrl_hi
  set bt0 := bt P.X a ℓ₁ r with hbt_def
  -- φ = K·bt²/d⁵
  have hphi_eq : phi P.X a ℓ₁ ℓ₂ r = K * bt0 ^ 2 / d ^ 5 := by
    rw [phi, hK_def, hbt_def, hd_def]
  -- first conjunct: φ ≥ 0
  have hnonneg : 0 ≤ phi P.X a ℓ₁ ℓ₂ r := by
    rw [hphi_eq]
    apply div_nonneg
    · exact mul_nonneg hKpos.le (sq_nonneg _)
    · positivity
  refine ⟨hnonneg, ?_⟩
  -- bt² = |bt|² ≤ (10⁶ B)²
  have hbtsq_le : bt0 ^ 2 ≤ 10 ^ 12 * S.B ^ 2 := by
    have h1 : bt0 ^ 2 = |bt0| ^ 2 := (sq_abs bt0).symm
    rw [h1]
    have h2 : |bt0| ^ 2 ≤ (1000000 * S.B) ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) hbt_hi
    calc |bt0| ^ 2 ≤ (1000000 * S.B) ^ 2 := h2
      _ = 10 ^ 12 * S.B ^ 2 := by ring
  -- d⁵ ≥ (D/10)⁵
  have hd5_lo : (S.D / 10) ^ 5 ≤ d ^ 5 := by
    apply pow_le_pow_left₀ (by positivity) hd_lo
  have hd5_pos : 0 < d ^ 5 := by positivity
  have hDpow_pos : 0 < (S.D / 10) ^ 5 := by positivity
  -- φ = K·bt²/d⁵ ≤ K·(10¹² B²)/(D⁵/10⁵)
  have step1 : phi P.X a ℓ₁ ℓ₂ r ≤ K * (10 ^ 12 * S.B ^ 2) / (S.D / 10) ^ 5 := by
    rw [hphi_eq]
    apply div_le_div₀ (by positivity) _ hDpow_pos hd5_lo
    exact mul_le_mul_of_nonneg_left hbtsq_le hKpos.le
  -- rewrite RHS of step1 = (12·10¹⁷ ℓ₁ℓ₂(ℓ₂−ℓ₁)) · (X·a·B²/D⁵)
  have hsimp : K * (10 ^ 12 * S.B ^ 2) / (S.D / 10) ^ 5
      = (12 * 10 ^ 17 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (P.X * a * S.B ^ 2 / S.D ^ 5) := by
    rw [hK_def]; field_simp
  -- scale: X·a·B²/D⁵ ≤ 11/(G·Ω⁵)
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hsc : P.X * a * S.B ^ 2 / S.D ^ 5 ≤ 11 / (P.G * S.Ω ^ 5) := by
    have hbase := defect_XAB2_div_D5 S
    have hle : P.X * a * S.B ^ 2 / S.D ^ 5 ≤ P.X * (11 * S.A) * S.B ^ 2 / S.D ^ 5 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hfac : P.X * a * S.B ^ 2 = (P.X * S.B ^ 2) * a := by ring
      have hfac2 : P.X * (11 * S.A) * S.B ^ 2 = (P.X * S.B ^ 2) * (11 * S.A) := by ring
      rw [hfac, hfac2]
      exact mul_le_mul_of_nonneg_left ha_hi (by positivity)
    calc P.X * a * S.B ^ 2 / S.D ^ 5
        ≤ P.X * (11 * S.A) * S.B ^ 2 / S.D ^ 5 := hle
      _ = 11 * (P.X * S.A * S.B ^ 2 / S.D ^ 5) := by ring
      _ = 11 * (1 / (P.G * S.Ω ^ 5)) := by rw [hbase]
      _ = 11 / (P.G * S.Ω ^ 5) := by ring
  -- combine
  calc phi P.X a ℓ₁ ℓ₂ r
      ≤ K * (10 ^ 12 * S.B ^ 2) / (S.D / 10) ^ 5 := step1
    _ = (12 * 10 ^ 17 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (P.X * a * S.B ^ 2 / S.D ^ 5) := hsimp
    _ ≤ (12 * 10 ^ 17 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (11 / (P.G * S.Ω ^ 5)) := by
        apply mul_le_mul_of_nonneg_left hsc (by positivity)
    _ ≤ 10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := by
        rw [div_eq_mul_one_div (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))]
        have hGΩ : 0 < P.G * S.Ω ^ 5 := by positivity
        rw [show (11:ℝ) / (P.G * S.Ω ^ 5) = 11 * (1 / (P.G * S.Ω ^ 5)) by ring]
        have key : (12 * 10 ^ 17 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (11 * (1 / (P.G * S.Ω ^ 5)))
            = (12 * 11 * 10 ^ 17) * ((ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (1 / (P.G * S.Ω ^ 5))) := by ring
        rw [key]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        norm_num

/-- `|φ'|` lower bound at the `L/R`-scale (writeup 849): `L/(R·10³⁰) ≤ |φ'|`. -/
theorem phi_deriv_lb {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R) :
    ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)
      ≤ |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r| := by
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
  -- d̃ bounds
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  -- rewrite the derivative via phi_hasDerivAt
  have hPD := phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r) ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hKpos : 0 < K := by rw [hK_def]; positivity
  set bracket := 2 * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁)
              - deriv (fun s => dtilde P.X s a) r) / ℓ₁) * dtilde P.X r a
            - 5 * bt P.X a ℓ₁ r * deriv (fun s => dtilde P.X s a) r with hbracket_def
  set bt0 := bt P.X a ℓ₁ r with hbt_def
  -- bracket ≥ D²/(2·10¹²·R²) > 0
  have hbr_lo : S.D ^ 2 / (2000000000000 * S.R ^ 2) ≤ bracket := by
    have h := phi_mono_core (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (r := r)
      hAD ha0 ha_lo ha_hi hℓ1 hr_lo hrl_hi hsmall
    rw [hbracket_def]; exact h
  have hbr_floor_pos : 0 < S.D ^ 2 / (2000000000000 * S.R ^ 2) := by positivity
  have hbr_pos : 0 < bracket := lt_of_lt_of_le hbr_floor_pos hbr_lo
  -- bt bounds
  obtain ⟨hbt_neg, hbt_lo, hbt_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ₁) (r := r)
      hAD ha0 hℓ1 ha_lo ha_hi hr_lo hrl_hi
  -- d̃⁶ > 0
  have hd6_pos : 0 < d ^ 6 := by positivity
  -- the value is K·bt·bracket/d⁶; compute its absolute value
  have habs_eq : |K * bt0 * bracket / d ^ 6| = K * |bt0| * bracket / d ^ 6 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hKpos, abs_of_pos hbr_pos,
        abs_of_pos hd6_pos]
  rw [habs_eq]
  -- lower bound: K·|bt|·bracket/d⁶ ≥ K·(B/10⁶)·(D²/(2·10¹²·R²))/(18D)⁶
  set floor := S.D ^ 2 / (2000000000000 * S.R ^ 2) with hfloor_def
  -- d⁶ ≤ (18 D)⁶
  have hd6_le : d ^ 6 ≤ (18 * S.D) ^ 6 := pow_le_pow_left₀ hd_pos.le hd_hi 6
  have hd18_pos : 0 < (18 * S.D) ^ 6 := by positivity
  -- numerator monotonicity: K·(B/10⁶)·floor ≤ K·|bt|·bracket
  have hnum_le : K * (S.B / 1000000) * floor ≤ K * |bt0| * bracket := by
    have h1 : K * (S.B / 1000000) ≤ K * |bt0| :=
      mul_le_mul_of_nonneg_left hbt_lo hKpos.le
    have h2 : 0 ≤ K * (S.B / 1000000) := by positivity
    exact mul_le_mul h1 hbr_lo hbr_floor_pos.le (le_trans h2 h1)
  -- assemble: K·(B/10⁶)·floor/(18D)⁶ ≤ K·|bt|·bracket/d⁶
  have hstep : K * (S.B / 1000000) * floor / (18 * S.D) ^ 6 ≤ K * |bt0| * bracket / d ^ 6 := by
    apply div_le_div₀ (by positivity) hnum_le hd6_pos hd6_le
  refine le_trans ?_ hstep
  -- Now reduce the explicit lower bound.
  -- LHS_target = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(G·Ω⁵·R·10³⁰)
  -- RHS = K·(B/10⁶)·floor/(18D)⁶
  -- scale: R/(5·G·Ω⁵) ≤ X·a·B/D⁴
  have hsc : S.R / (5 * P.G * S.Ω ^ 5) ≤ P.X * a * S.B / S.D ^ 4 := by
    have hbase := defect_XAB_div_D4 S
    have hle : P.X * (S.A / 5) * S.B / S.D ^ 4 ≤ P.X * a * S.B / S.D ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hfac : P.X * (S.A / 5) * S.B = (P.X * S.B) * (S.A / 5) := by ring
      have hfac2 : P.X * a * S.B = (P.X * S.B) * a := by ring
      rw [hfac, hfac2]
      exact mul_le_mul_of_nonneg_left ha_lo (by positivity)
    calc S.R / (5 * P.G * S.Ω ^ 5)
        = (1 / 5) * (S.R / (P.G * S.Ω ^ 5)) := by ring
      _ = (1 / 5) * (P.X * S.A * S.B / S.D ^ 4) := by rw [hbase]
      _ = P.X * (S.A / 5) * S.B / S.D ^ 4 := by ring
      _ ≤ P.X * a * S.B / S.D ^ 4 := hle
  -- Express RHS factoring out ℓ₁ℓ₂(ℓ₂−ℓ₁) and powers of D.
  -- RHS = ℓ₁ℓ₂(ℓ₂−ℓ₁) · c1 · (X·a·B/D⁴)/R²,  c1 = 12/(10⁶·2·10¹²·18⁶)
  have hrhs_eq : K * (S.B / 1000000) * floor / (18 * S.D) ^ 6
      = (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * ((12 / (1000000 * 2000000000000 * 18 ^ 6))
          * ((P.X * a * S.B / S.D ^ 4) / S.R ^ 2)) := by
    rw [hK_def, hfloor_def]
    field_simp
  rw [hrhs_eq]
  -- target = ℓ₁ℓ₂(ℓ₂−ℓ₁) · (1/(G·Ω⁵·R·10³⁰))
  have htgt_eq : ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)
      = (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (1 / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)) := by ring
  rw [htgt_eq]
  apply mul_le_mul_of_nonneg_left _ hLpos.le
  -- Now: 1/(G·Ω⁵·R·10³⁰) ≤ c1·((X·a·B/D⁴)/R²)
  -- Apply hsc: (X·a·B/D⁴)/R² ≥ (R/(5·G·Ω⁵))/R² = 1/(5·G·Ω⁵·R)
  set c1 := (12 : ℝ) / (1000000 * 2000000000000 * 18 ^ 6) with hc1_def
  have hc1_pos : 0 < c1 := by rw [hc1_def]; norm_num
  have hXaB_pos : 0 < P.X * a * S.B / S.D ^ 4 := by positivity
  have hstep2 : c1 * ((S.R / (5 * P.G * S.Ω ^ 5)) / S.R ^ 2)
      ≤ c1 * ((P.X * a * S.B / S.D ^ 4) / S.R ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hc1_pos.le
    apply div_le_div_of_nonneg_right hsc (by positivity)
  refine le_trans ?_ hstep2
  -- c1·((R/(5GΩ⁵))/R²) = c1/(5·G·Ω⁵·R) = (c1/5)·(1/(G·Ω⁵·R))
  have hreduce : c1 * ((S.R / (5 * P.G * S.Ω ^ 5)) / S.R ^ 2)
      = (c1 / 5) * (1 / (P.G * S.Ω ^ 5 * S.R)) := by
    field_simp
  rw [hreduce]
  -- target = 1/(G·Ω⁵·R·10³⁰) = (1/10³⁰)·(1/(G·Ω⁵·R))
  have htgt2 : (1 : ℝ) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)
      = (1 / 10 ^ 30) * (1 / (P.G * S.Ω ^ 5 * S.R)) := by
    rw [one_div_mul_eq_div]; ring
  rw [htgt2]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  -- numeric: 1/10³⁰ ≤ c1/5
  rw [hc1_def]
  norm_num

/-- `|φ'|` upper bound at the `L/R`-scale: `|φ'| ≤ 10³⁵·L/R`. -/
theorem phi_deriv_ub {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R) :
    |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
      ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := by
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
  -- d̃ bounds
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  -- rewrite the derivative via phi_hasDerivAt
  have hPD := phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r) ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hKpos : 0 < K := by rw [hK_def]; positivity
  set bracket := 2 * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁)
              - deriv (fun s => dtilde P.X s a) r) / ℓ₁) * dtilde P.X r a
            - 5 * bt P.X a ℓ₁ r * deriv (fun s => dtilde P.X s a) r with hbracket_def
  set bt0 := bt P.X a ℓ₁ r with hbt_def
  -- |bracket| ≤ 10¹⁵·B²  (phi_bracket_ub)
  have hbr_abs : |bracket| ≤ 10 ^ 15 * S.B ^ 2 := by
    have h := phi_bracket_ub (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (r := r)
      hAD ha0 ha_lo ha_hi hℓ1 hr_lo hrl_hi
    rw [hbracket_def]; exact h
  -- |bt| ≤ 10⁶·B  (bt_abs_bounds)
  obtain ⟨_, _, hbt_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ₁) (r := r)
      hAD ha0 hℓ1 ha_lo ha_hi hr_lo hrl_hi
  have hbt_abs : |bt0| ≤ 1000000 * S.B := by rw [hbt_def]; exact hbt_hi
  -- d̃⁶ ≥ (D/10)⁶ > 0
  have hd6_pos : 0 < d ^ 6 := by positivity
  have hd6_lo : (S.D / 10) ^ 6 ≤ d ^ 6 := pow_le_pow_left₀ (by positivity) hd_lo 6
  have hd6lo_pos : 0 < (S.D / 10) ^ 6 := by positivity
  -- |value| = K·|bt|·|bracket|/d⁶
  have habs_eq : |K * bt0 * bracket / d ^ 6| = K * |bt0| * |bracket| / d ^ 6 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hKpos, abs_of_pos hd6_pos]
  rw [habs_eq]
  -- numerator monotone: K·|bt|·|bracket| ≤ K·(10⁶ B)·(10¹⁵ B²)
  have hnum_le : K * |bt0| * |bracket| ≤ K * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) := by
    have h1 : K * |bt0| ≤ K * (1000000 * S.B) := mul_le_mul_of_nonneg_left hbt_abs hKpos.le
    have h2 : (0:ℝ) ≤ K * |bt0| := by positivity
    exact mul_le_mul h1 hbr_abs (abs_nonneg _) (le_trans h2 h1)
  -- assemble: K·|bt|·|bracket|/d⁶ ≤ K·(10⁶ B)·(10¹⁵ B²)/(D/10)⁶
  have hstep : K * |bt0| * |bracket| / d ^ 6
      ≤ K * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) / (S.D / 10) ^ 6 := by
    apply div_le_div₀ (by positivity) hnum_le hd6lo_pos hd6_lo
  refine le_trans hstep ?_
  -- RHS = (12·10²⁷ · ℓ₁ℓ₂(ℓ₂−ℓ₁)) · (X·a·B³/D⁶)
  have hRHS_eq : K * (1000000 * S.B) * (10 ^ 15 * S.B ^ 2) / (S.D / 10) ^ 6
      = (12 * 10 ^ 27 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (P.X * a * S.B ^ 3 / S.D ^ 6) := by
    rw [hK_def]; field_simp; ring
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
  -- combine
  calc (12 * 10 ^ 27 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (P.X * a * S.B ^ 3 / S.D ^ 6)
      ≤ (12 * 10 ^ 27 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (11 * (1 / (P.G * S.Ω ^ 5 * S.R))) := by
        apply mul_le_mul_of_nonneg_left hsc (by positivity)
    _ ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := by
        rw [div_eq_mul_one_div (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))]
        have key : (12 * 10 ^ 27 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) * (11 * (1 / (P.G * S.Ω ^ 5 * S.R)))
            = (12 * 11 * 10 ^ 27) * ((ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (1 / (P.G * S.Ω ^ 5 * S.R))) := by
          ring
        rw [key]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        norm_num

end Squarefree
