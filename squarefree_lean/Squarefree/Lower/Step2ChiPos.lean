import Squarefree.Lower.Step2ChiPosAux

/-!
# §5 Step-2 phase: positivity of `χ''` (the `χ = ψ·φ` part)

The §5 Step-2 phase's `χ`-part is `χ = ψ·φ` with `ψ = d̃⁴/(6Xa)` and `φ` the Step-1 phase
(`phi`); concretely `χ = phif X a ℓ₁ ℓ₂ 0` (the `f = 0` shared phase).  By the product rule
`χ'' = ψ''·φ + 2ψ'·φ' + ψ·φ''`, and the explicit closed forms of `ψ`, `φ` and their derivatives,

  `χ'' = (12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa / (6Xa))·N_act / d̃⁶`,

  `N_act = (2 d̃³ d̃'² − d̃⁴ d̃'')·b̃² − 4 d̃⁴ d̃'·b̃·b̃' + 2 d̃⁵·b̃'² + 2 d̃⁵·b̃·b̃''`,

with `b̃` the finite-difference defect derivative.  Replacing the finite differences by the smooth
derivatives (`b̃ → d̃'`, `b̃' → d̃''`, `b̃'' → d̃'''`) gives the smooth numerator `N_s`, which has the
sign-definite closed form (sympy-verified)

  `N_s = d̃⁷(a+d̃)²(35a⁴+241a³d̃+680a²d̃²+894ad̃³+468d̃⁴) / (16 r⁴ (a+2d̃)⁶) > 0`,

so that `χ_s'' = 2ℓ₁ℓ₂(ℓ₂−ℓ₁)·N_s/d̃⁶ > 0`.  The finite-difference correction `|N_act − N_s|`
is bounded by `½N_s` on the §5 band (where `ℓ₁ ≤ R·10⁻⁷⁸`), giving `χ'' > 0`.

This mirrors `phif_curvature_lower_curv` (pieces A + B): `smooth_chi2_eq` is the (A) closed form,
and `chi_correction_abstract` (+ `Ncorr_chi_alg`, reusing `fd_error_bound`) is the (B) correction.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

/-- The §5 Step-2 phase's `χ`-part: `χ = ψ·φ = (d̃⁴/(6Xa))·φ = phif X a ℓ₁ ℓ₂ 0`. -/
noncomputable def chi (X a ℓ₁ ℓ₂ r : ℝ) : ℝ := phif X a ℓ₁ ℓ₂ 0 r
/-- **The smooth numerator lower bound.**  `N_s = 2d̃³d̃'⁴ − 5d̃⁴d̃'²d̃'' + 2d̃⁵d̃''² + 2d̃⁵d̃'d̃'''`
equals the positive closed form `d̃⁷(a+d̃)²(35a⁴+241a³d̃+680a²d̃²+894ad̃³+468d̃⁴)/(16r⁴(a+2d̃)⁶)`
(`smooth_chi2_eq`), which on the §5 window is `≥ B⁷R³/10²⁷`. -/
private lemma Ns_chi_lower {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1 / 72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    S.B ^ 7 * S.R ^ 3 / 10 ^ 27
      ≤ 2 * dtilde P.X r a ^ 3 * (deriv (fun u => dtilde P.X u a) r) ^ 4
          - 5 * dtilde P.X r a ^ 4 * (deriv (fun u => dtilde P.X u a) r) ^ 2
              * iteratedDeriv 2 (fun u => dtilde P.X u a) r
          + 2 * dtilde P.X r a ^ 5 * (iteratedDeriv 2 (fun u => dtilde P.X u a) r) ^ 2
          + 2 * dtilde P.X r a ^ 5 * deriv (fun u => dtilde P.X u a) r
              * iteratedDeriv 3 (fun u => dtilde P.X u a) r := by
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by
    unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrne : r ≠ 0 := ne_of_gt hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  have hd1cf := (dtilde_r_hasDerivAt P.X_pos ha0 hr0).deriv
  have hd2cf := dtilde_r_iteratedDeriv2 P.X_pos ha0 hr0
  have hs4cf := dtilde_r_iteratedDeriv3 P.X_pos ha0 hr0
  have had2 : a + 2 * dtilde P.X r a ≠ 0 := ne_of_gt (by linarith [hd_pos, ha0])
  rw [hd1cf, hd2cf, hs4cf, smooth_chi2_eq a (dtilde P.X r a) r hrne had2]
  set d := dtilde P.X r a with hd_def
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  have hda : 0 < d + a := by linarith
  have ha2d : 0 < a + 2 * d := by linarith
  set Poly := 35 * a ^ 4 + 241 * a ^ 3 * d + 680 * a ^ 2 * d ^ 2 + 894 * a * d ^ 3 + 468 * d ^ 4
    with hPoly_def
  have h7 : (S.D / 10) ^ 7 ≤ d ^ 7 := pow_le_pow_left₀ (by positivity) hd_lo 7
  have h2 : (S.D / 10) ^ 2 ≤ (a + d) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hP4 : 468 * (S.D / 10) ^ 4 ≤ Poly := by
    have h4 : (S.D / 10) ^ 4 ≤ d ^ 4 := pow_le_pow_left₀ (by positivity) hd_lo 4
    rw [hPoly_def]
    nlinarith [h4, mul_nonneg (mul_nonneg ha0.le (pow_nonneg ha0.le 3)) hd_pos.le,
      pow_nonneg ha0.le 4, mul_nonneg (pow_nonneg ha0.le 2) (pow_nonneg hd_pos.le 2),
      mul_nonneg ha0.le (pow_nonneg hd_pos.le 3)]
  have hnum_lo : 468 * (S.D / 10) ^ 13 ≤ d ^ 7 * (a + d) ^ 2 * Poly := by
    have s1 : (S.D / 10) ^ 7 * (S.D / 10) ^ 2 ≤ d ^ 7 * (a + d) ^ 2 :=
      mul_le_mul h7 h2 (by positivity) (by positivity)
    have s2 : (S.D / 10) ^ 7 * (S.D / 10) ^ 2 * (468 * (S.D / 10) ^ 4)
        ≤ d ^ 7 * (a + d) ^ 2 * Poly :=
      mul_le_mul s1 hP4 (by positivity) (by positivity)
    calc 468 * (S.D / 10) ^ 13 = (S.D / 10) ^ 7 * (S.D / 10) ^ 2 * (468 * (S.D / 10) ^ 4) := by ring
      _ ≤ d ^ 7 * (a + d) ^ 2 * Poly := s2
  have ha2d_hi : a + 2 * d ≤ 38 * S.D := by linarith
  have hden_hi : 16 * r ^ 4 * (a + 2 * d) ^ 6 ≤ 16 * (16 * S.R) ^ 4 * (38 * S.D) ^ 6 := by
    have hr4 : r ^ 4 ≤ (16 * S.R) ^ 4 := pow_le_pow_left₀ hr0.le hr_hi 4
    have ha2d6 : (a + 2 * d) ^ 6 ≤ (38 * S.D) ^ 6 := pow_le_pow_left₀ ha2d.le ha2d_hi 6
    have s1 : 16 * r ^ 4 ≤ 16 * (16 * S.R) ^ 4 := by nlinarith [hr4]
    exact mul_le_mul s1 ha2d6 (by positivity) (by positivity)
  calc S.B ^ 7 * S.R ^ 3 / 10 ^ 27
      ≤ (468 * (S.D / 10) ^ 13) / (16 * (16 * S.R) ^ 4 * (38 * S.D) ^ 6) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), Scale.B_eq_D_div_R S]
        have eL : (S.D / S.R) ^ 7 * S.R ^ 3 * (16 * (16 * S.R) ^ 4 * (38 * S.D) ^ 6)
            = 16 ^ 5 * 38 ^ 6 * S.D ^ 13 := by field_simp
        have eR : 468 * (S.D / 10) ^ 13 * 10 ^ 27 = 468 * 10 ^ 14 * S.D ^ 13 := by
          field_simp
        rw [eL, eR]
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hDpos.le 13)
    _ ≤ (d ^ 7 * (a + d) ^ 2 * Poly) / (16 * r ^ 4 * (a + 2 * d) ^ 6) := by gcongr

/-- **§5 Step-2: `χ''` is positive on the band.**  The `χ`-part `χ = ψ·φ` of the Step-2 phase has
strictly positive curvature on the §5 window (`ℓ₁ ≤ R·10⁻⁷⁸`): `χ'' = (K/(6Xa))·N_act/d̃⁶` with
`N_act ≥ ½N_s > 0`, where `N_s` is the smooth numerator (`Ns_chi_lower`) and the finite-difference
correction `|N_act − N_s| ≤ ½N_s` (`chi_correction_abstract`). -/
theorem chi_iteratedDeriv2_pos {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1 / 72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 78 * ℓ₁ ≤ S.R) :
    0 < iteratedDeriv 2 (fun u => chi P.X a ℓ₁ ℓ₂ u) r := by
  -- scale positivity
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by
    unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have h6Xa : (6 : ℝ) * P.X * a ≠ 0 := by positivity
  have hBR : S.B = S.D / S.R := Scale.B_eq_D_div_R S
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- window predicate on `[r, r+ℓ₁]`
  have hwin : ∀ x ∈ Set.Icc r (r + ℓ₁), (1 / 72) * S.R ≤ x ∧ x ≤ 16 * S.R ∧ 0 < x := by
    intro x hx; obtain ⟨hxl, hxr⟩ := hx
    exact ⟨by linarith, by linarith, by linarith⟩
  have hD_BR : S.D = S.B * S.R := by rw [hBR]; field_simp
  have hconv3 : S.D / S.R ^ 3 = S.B / S.R ^ 2 := by rw [hBR]; field_simp
  have hconv4 : S.D / S.R ^ 4 = S.B / S.R ^ 3 := by rw [hBR]; field_simp
  -- closed-form derivative values (`χ'' = phif''` with `f = 0`, plus `φ, φ', φ''`)
  have hChi2eq := phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
    ha0 hr0 hrl hℓne
  have hφ1eq := (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).deriv
  have hφ2eq := phi_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have hφval : phi P.X a ℓ₁ ℓ₂ r
      = 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a * (bt P.X a ℓ₁ r) ^ 2 / (dtilde P.X r a) ^ 5 := by
    simp only [phi]
  -- smooth numerator lower bound
  have hNs_lb := Ns_chi_lower (P := P) (S := S) (a := a) (r := r) hAD ha0 ha_lo ha_hi hr_lo hr_hi
  -- ε bounds via the double-MVT
  have he1 : |bt P.X a ℓ₁ r - deriv (fun u => dtilde P.X u a) r|
      ≤ ℓ₁ * (10 ^ 13 * (S.B / S.R)) := by
    have key := fd_error_bound (f := fun s => dtilde P.X s a)
      (g := fun t => deriv (fun u => dtilde P.X u a) t)
      (h := fun t => iteratedDeriv 2 (fun u => dtilde P.X u a) t) (M := 10 ^ 13 * (S.B / S.R)) hℓ1
      (fun x hx => (dtilde_r_hasDerivAt hXpos ha0 (hwin x hx).2.2).differentiableAt.hasDerivAt)
      (fun x hx => dtilde_deriv_hasDerivAt hXpos ha0 (hwin x hx).2.2)
      (fun x hx => by
        obtain ⟨hxl, hxr, hxpos⟩ := hwin x hx
        obtain ⟨hp2, _, hub2⟩ := dtilde_d2_bounds hAD ha0 hxpos ha_lo ha_hi hxl hxr
        rw [abs_of_pos hp2, show (10:ℝ) ^ 13 = 10000000000000 by norm_num]; exact hub2)
    simpa [bt] using key
  have he2 : |(deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁
        - iteratedDeriv 2 (fun u => dtilde P.X u a) r| ≤ ℓ₁ * (10 ^ 19 * (S.B / S.R ^ 2)) := by
    have key := fd_error_bound (f := fun t => deriv (fun u => dtilde P.X u a) t)
      (g := fun t => iteratedDeriv 2 (fun u => dtilde P.X u a) t)
      (h := fun t => iteratedDeriv 3 (fun u => dtilde P.X u a) t)
      (M := 10 ^ 19 * (S.B / S.R ^ 2)) hℓ1
      (fun x hx => dtilde_deriv_hasDerivAt hXpos ha0 (hwin x hx).2.2)
      (fun x hx => dtilde_iteratedDeriv2_hasDerivAt hXpos ha0 (hwin x hx).2.2)
      (fun x hx => by
        obtain ⟨hxl, hxr, hxpos⟩ := hwin x hx
        have h := dtilde_d3_upper hAD ha0 hxpos ha_lo ha_hi hxl hxr
        rw [← hconv3, show (10:ℝ) ^ 19 = 10000000000000000000 by norm_num]; exact h)
    exact key
  have he3 : |(iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
          - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁
        - iteratedDeriv 3 (fun u => dtilde P.X u a) r| ≤ ℓ₁ * (2 * 10 ^ 25 * (S.B / S.R ^ 3)) := by
    have key := fd_error_bound (f := fun t => iteratedDeriv 2 (fun u => dtilde P.X u a) t)
      (g := fun t => iteratedDeriv 3 (fun u => dtilde P.X u a) t)
      (h := fun t => iteratedDeriv 4 (fun u => dtilde P.X u a) t)
      (M := 2 * 10 ^ 25 * (S.B / S.R ^ 3)) hℓ1
      (fun x hx => dtilde_iteratedDeriv2_hasDerivAt hXpos ha0 (hwin x hx).2.2)
      (fun x hx => dtilde_iteratedDeriv3_hasDerivAt hXpos ha0 (hwin x hx).2.2)
      (fun x hx => by
        obtain ⟨hxl, hxr, hxpos⟩ := hwin x hx
        have h := dtilde_d4_upper hAD ha0 hxpos ha_lo ha_hi hxl hxr
        rw [← hconv4, show (2:ℝ) * 10 ^ 25 = 20000000000000000000000000 by norm_num]; exact h)
    exact key
  -- atom magnitude bounds at `r`
  obtain ⟨hd1_lo, hd1_hi⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  obtain ⟨hd2_pos, _, hd2_hi⟩ := dtilde_d2_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hs4_hi : |iteratedDeriv 3 (fun u => dtilde P.X u a) r| ≤ 10 ^ 19 * (S.B / S.R ^ 2) := by
    rw [← hconv3, show (10:ℝ) ^ 19 = 10000000000000000000 by norm_num]
    exact dtilde_d3_upper hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- abbreviate the atoms
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun u => dtilde P.X u a) r with hd1_def
  set d2 := iteratedDeriv 2 (fun u => dtilde P.X u a) r with hd2_def
  set s4 := iteratedDeriv 3 (fun u => dtilde P.X u a) r with hs4_def
  set b := bt P.X a ℓ₁ r with hb_def
  set bp := (deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁
    with hbp_def
  set bd := (iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
    - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁ with hbd_def
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hdne : d ≠ 0 := ne_of_gt hd_pos
  set e1 := b - d1 with he1_def
  set e2 := bp - d2 with he2_def
  set e3 := bd - s4 with he3_def
  set Nact := (2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * b ^ 2 - 4 * d ^ 4 * d1 * b * bp
      + 2 * d ^ 5 * bp ^ 2 + 2 * d ^ 5 * b * bd with hNact_def
  set Ns := 2 * d ^ 3 * d1 ^ 4 - 5 * d ^ 4 * d1 ^ 2 * d2 + 2 * d ^ 5 * d2 ^ 2 + 2 * d ^ 5 * d1 * s4
    with hNs_def
  -- `χ'' = (K/(6Xa))·N_act/d⁶`
  have hChiVal : iteratedDeriv 2 (fun u => chi P.X a ℓ₁ ℓ₂ u) r = K / (6 * P.X * a) * Nact / d ^ 6 := by
    show iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) r = _
    rw [hChi2eq, hφval, hφ1eq, hφ2eq, hNact_def]
    exact chi2_poly P.X a d d1 d2 b bp bd K hdne
  -- correction expansion and bound
  have hcorr_eq : Nact - Ns = (4 * d ^ 3 * d1 ^ 3 - 6 * d ^ 4 * d1 * d2 + 2 * d ^ 5 * s4) * e1
      + (-4 * d ^ 4 * d1 ^ 2 + 4 * d ^ 5 * d2) * e2 + 2 * d ^ 5 * d1 * e3
      + (2 * d ^ 3 * d1 ^ 2 - d ^ 4 * d2) * e1 ^ 2 + 2 * d ^ 5 * e2 ^ 2
      - 4 * d ^ 4 * d1 * e1 * e2 + 2 * d ^ 5 * e1 * e3 := by
    have hb' : b = d1 + e1 := by rw [he1_def]; ring
    have hbp' : bp = d2 + e2 := by rw [he2_def]; ring
    have hbd' : bd = s4 + e3 := by rw [he3_def]; ring
    rw [hNact_def, hNs_def, hb', hbp', hbd']
    exact Ncorr_chi_alg d d1 d2 s4 e1 e2 e3
  have hcorr_bd : |Nact - Ns| ≤ S.B ^ 7 * S.R ^ 3 / (2 * 10 ^ 27) := by
    rw [hcorr_eq]
    refine chi_correction_abstract (B := S.B) (R := S.R) (l1 := ℓ₁)
      hRpos hBpos hℓ1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsmall
    · rw [abs_of_pos hd_pos]
      calc d ≤ 18 * S.D := hd_hi
        _ = 18 * (S.B * S.R) := by rw [hD_BR]
    · rw [show (10:ℝ) ^ 6 = 1000000 by norm_num]; exact hd1_hi
    · rw [abs_of_pos hd2_pos, show (10:ℝ) ^ 13 = 10000000000000 by norm_num]; exact hd2_hi
    · exact hs4_hi
    · rw [he1_def]; exact he1
    · rw [he2_def]; exact he2
    · rw [he3_def]; exact he3
  -- `N_act ≥ ½N_s > 0`
  have hNact_pos : 0 < Nact := by
    have hge := (abs_le.mp hcorr_bd).1
    have hpos : 0 < S.B ^ 7 * S.R ^ 3 / (2 * 10 ^ 27) := by positivity
    have harith : S.B ^ 7 * S.R ^ 3 / 10 ^ 27 - S.B ^ 7 * S.R ^ 3 / (2 * 10 ^ 27)
        = S.B ^ 7 * S.R ^ 3 / (2 * 10 ^ 27) := by ring
    linarith [hNs_lb, hge, hpos, harith]
  -- conclude
  rw [hChiVal]
  have hKpos : 0 < K := by rw [hK_def]; positivity
  apply div_pos
  · exact mul_pos (div_pos hKpos (by positivity)) hNact_pos
  · exact pow_pos hd_pos 6

end Squarefree
