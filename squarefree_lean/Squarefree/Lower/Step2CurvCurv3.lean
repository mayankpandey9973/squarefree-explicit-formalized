import Squarefree.Lower.Step2CurvCurv2

/-!
# §5 Step-2 curvature lower bound (`f`-free Wronskian branch) — assembly

This file finishes `phif_curvature_lower_curv`:

  `(1/10⁷⁰)·(T_curv/R) ≤ |φ_f'(r)| + R·|φ_f''(r)|`   for **all** `f`,

with `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`.  The mechanism is the `f`-free Wronskian
`𝒲 = ψ''·φ_f' − ψ'·φ_f'' = (4K/(6Xa)²)·Ñ_act` (`welim_poly`), whose magnitude is bounded
below by comparing `Ñ_act` to its smooth version `Ñ_s` (closed form of `Step2CurvCurv`)
through the finite-difference correction `|Ñ_act − Ñ_s| ≤ ½|Ñ_s|`.
-/

namespace Squarefree

open Real

/-- **The smooth numerator lower bound.**  `Ñ_s = −d̃'·(5d̃'⁴ − 10d̃'²d̃''d̃ + 2d̃'d̃'''d̃²)` equals the
positive closed form `d⁵(a+d)³(5a⁴+44a³d+169a²d²+280ad³+180d⁴)/(32r⁵(a+2d)⁷)` (`Step2CurvCurv`),
which on the §5 window is `≥ D⁵/(10²⁹R⁵)`. -/
private lemma Ns_lower {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1 / 72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    S.D ^ 5 / (10 ^ 29 * S.R ^ 5)
      ≤ |-(deriv (fun u => dtilde P.X u a) r
            * (5 * (deriv (fun u => dtilde P.X u a) r) ^ 4
               - 10 * (deriv (fun u => dtilde P.X u a) r) ^ 2
                   * iteratedDeriv 2 (fun u => dtilde P.X u a) r * dtilde P.X r a
               + 2 * (deriv (fun u => dtilde P.X u a) r)
                   * iteratedDeriv 3 (fun u => dtilde P.X u a) r * (dtilde P.X r a) ^ 2))| := by
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0 : 0 < r := by linarith [hr_lo, hRpos]
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  have hd1cf := (dtilde_r_hasDerivAt P.X_pos ha0 hr0).deriv
  have hd2cf := dtilde_r_iteratedDeriv2 P.X_pos ha0 hr0
  have hs4cf := dtilde_r_iteratedDeriv3 P.X_pos ha0 hr0
  rw [hd1cf, hd2cf, hs4cf]
  obtain ⟨heq, hpos⟩ := smooth_wronskian_numerator_neg ha0 hd_pos hr0
  rw [heq, neg_neg, abs_of_pos hpos]
  -- numeric lower bound on the positive closed form
  set d := dtilde P.X r a with hd_def
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  have hda : 0 < d + a := by linarith
  have ha2d : 0 < a + 2 * d := by linarith
  set Poly := 5 * a ^ 4 + 44 * a ^ 3 * d + 169 * a ^ 2 * d ^ 2 + 280 * a * d ^ 3 + 180 * d ^ 4
    with hPoly_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  have h5 : (S.D / 10) ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ (by positivity) hd_lo 5
  have h3 : (S.D / 10) ^ 3 ≤ (a + d) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hP4 : 180 * (S.D / 10) ^ 4 ≤ Poly := by
    have h4 : (S.D / 10) ^ 4 ≤ d ^ 4 := pow_le_pow_left₀ (by positivity) hd_lo 4
    rw [hPoly_def]
    nlinarith [h4, mul_nonneg (mul_nonneg ha0.le (pow_nonneg ha0.le 3)) hd_pos.le,
      pow_nonneg ha0.le 4, mul_nonneg (pow_nonneg ha0.le 2) (pow_nonneg hd_pos.le 2),
      mul_nonneg ha0.le (pow_nonneg hd_pos.le 3)]
  have hnum_lo : 180 * (S.D / 10) ^ 12 ≤ d ^ 5 * (a + d) ^ 3 * Poly := by
    have s1 : (S.D / 10) ^ 5 * (S.D / 10) ^ 3 ≤ d ^ 5 * (a + d) ^ 3 :=
      mul_le_mul h5 h3 (by positivity) (by positivity)
    have s2 : (S.D / 10) ^ 5 * (S.D / 10) ^ 3 * (180 * (S.D / 10) ^ 4)
        ≤ d ^ 5 * (a + d) ^ 3 * Poly :=
      mul_le_mul s1 hP4 (by positivity) (by positivity)
    calc 180 * (S.D / 10) ^ 12 = (S.D / 10) ^ 5 * (S.D / 10) ^ 3 * (180 * (S.D / 10) ^ 4) := by ring
      _ ≤ d ^ 5 * (a + d) ^ 3 * Poly := s2
  have ha2d_hi : a + 2 * d ≤ 38 * S.D := by linarith
  have hden_hi : 32 * r ^ 5 * (a + 2 * d) ^ 7 ≤ 32 * (16 * S.R) ^ 5 * (38 * S.D) ^ 7 := by
    have hr5 : r ^ 5 ≤ (16 * S.R) ^ 5 := pow_le_pow_left₀ hr0.le hr_hi 5
    have ha2d7 : (a + 2 * d) ^ 7 ≤ (38 * S.D) ^ 7 := pow_le_pow_left₀ ha2d.le ha2d_hi 7
    have s1 : 32 * r ^ 5 ≤ 32 * (16 * S.R) ^ 5 := by linarith [hr5]
    exact mul_le_mul s1 ha2d7 (by positivity) (by positivity)
  calc S.D ^ 5 / (10 ^ 29 * S.R ^ 5)
      ≤ (180 * (S.D / 10) ^ 12) / (32 * (16 * S.R) ^ 5 * (38 * S.D) ^ 7) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have eL : S.D ^ 5 * (32 * (16 * S.R) ^ 5 * (38 * S.D) ^ 7)
            = (32 * 16 ^ 5 * 38 ^ 7) * (S.D ^ 12 * S.R ^ 5) := by ring
        have eR : 180 * (S.D / 10) ^ 12 * (10 ^ 29 * S.R ^ 5)
            = 180 * 10 ^ 17 * (S.D ^ 12 * S.R ^ 5) := by ring
        rw [eL, eR]
        nlinarith only [mul_nonneg (pow_nonneg hDpos.le 12) (pow_nonneg hRpos.le 5)]
    _ ≤ (d ^ 5 * (a + d) ^ 3 * Poly) / (32 * r ^ 5 * (a + 2 * d) ^ 7) := by gcongr

/-- **§5 Step-2 curvature lower bound** (`f`-free Wronskian branch, writeup line 917, 2nd branch).
For **all** `f`, the variation scale `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D` satisfies
`(1/10⁷²)·(T_curv/R) ≤ |φ_f'(r)| + R·|φ_f''(r)|`, with `1/10⁷²` an absolute constant.  The proof
eliminates `f` via the Wronskian `𝒲 = ψ''·φ_f' − ψ'·φ_f'' = (4K/(6Xa)²)·Ñ_act`, bounds `|Ñ_act|`
below through the smooth comparison `|Ñ_act| ≥ ½|Ñ_s|`, and divides through `lp_duality_lower`. -/
theorem phif_curvature_lower_curv {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1 / 72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 78 * ℓ₁ ≤ S.R) :
    (1 / 10 ^ 72) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / S.R
      ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r|
        + S.R * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have h6Xa : (6 : ℝ) * P.X * a ≠ 0 := by positivity
  have hBR : S.B = S.D / S.R := Scale.B_eq_D_div_R S
  -- window facts
  have hr0 : 0 < r := by linarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hl1R : ℓ₁ ≤ S.R := by linarith [hsmall, hℓ1]
  -- d̃ positivity / bounds
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- the window predicate for points in `[r, r+ℓ₁]`
  have hwin : ∀ x ∈ Set.Icc r (r + ℓ₁), (1 / 72) * S.R ≤ x ∧ x ≤ 16 * S.R ∧ 0 < x := by
    intro x hx; obtain ⟨hxl, hxr⟩ := hx
    exact ⟨by linarith, by linarith, by linarith⟩
  have hD_BR : S.D = S.B * S.R := by rw [hBR]; field_simp
  have hconv3 : S.D / S.R ^ 3 = S.B / S.R ^ 2 := by rw [hBR]; ring
  have hconv4 : S.D / S.R ^ 4 = S.B / S.R ^ 3 := by rw [hBR]; ring
  -- closed-form derivative values
  have hD1eq := (phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    ha0 hr0 hrl hℓne).deriv
  have hD2eq := phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    ha0 hr0 hrl hℓne
  have hφ1eq := (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).deriv
  have hφ2eq := phi_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  -- smooth numerator lower bound (literal `Ñ_s`)
  have hNs_lb := Ns_lower (P := P) (S := S) (a := a) (r := r) hAD ha0 ha_lo ha_hi hr_lo hr_hi
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
  set φ := phi P.X a ℓ₁ ℓ₂ r with hφ_def
  set φ1 := deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r with hφ1_def
  set φ2 := iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r with hφ2_def
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  set D1 := deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r with hD1_def
  set D2 := iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r with hD2_def
  have hdne : d ≠ 0 := ne_of_gt hd_pos
  have hd6ne : d ^ 6 ≠ 0 := pow_ne_zero 6 hdne
  -- e := finite-difference errors
  set e1 := b - d1 with he1_def
  set e2 := bp - d2 with he2_def
  set e3 := bd - s4 with he3_def
  -- the actual Wronskian polynomial `Ñ_act` and its smooth version `Ñ_s`
  set Nact := (d * d2 - 5 * d1 ^ 2) * b * (2 * bp * d - 5 * b * d1)
      - d * d1 * (bp * (2 * bp * d - 5 * b * d1) + b * (2 * bd * d - 3 * bp * d1 - 5 * b * d2))
      + 6 * d1 ^ 2 * b * (2 * bp * d - 5 * b * d1) with hNact_def
  set Ns := -(d1 * (5 * d1 ^ 4 - 10 * d1 ^ 2 * d2 * d + 2 * d1 * s4 * d ^ 2)) with hNs_def
  -- the curvature scale atoms ψ', ψ'' = E1
  set ψ' := 4 * d ^ 3 * d1 / (6 * P.X * a) with hψ'_def
  set E1 := (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * P.X * a) with hE1_def
  -- Wronskian identity:  E1·D1 − ψ'·D2 = (4K/(6Xa)²)·Ñ_act  (closed forms `hφ*eq, hD*eq` are
  -- already in atom-form after the `set`s above)
  have hWval : E1 * D1 - ψ' * D2 = (4 * K / (6 * P.X * a) ^ 2) * Nact := by
    rw [hE1_def, hψ'_def, hD1eq, hD2eq, hNact_def]
    exact welim_poly P.X a d d1 d2 b bp bd φ φ1 φ2 f K h6Xa hd6ne hdne hφ1eq hφ2eq
  -- positivity of structural factors
  have hKpos : 0 < K := by rw [hK_def]; positivity
  have h4Kpos : 0 < 4 * K / (6 * P.X * a) ^ 2 := by rw [hK_def]; positivity
  have hE1pos : 0 < E1 := by
    rw [hE1_def]; apply div_pos _ (by positivity)
    have hd2pos : (0:ℝ) < d2 := hd2_pos
    have : (0:ℝ) < 4 * d ^ 3 * d2 := by positivity
    nlinarith only [sq_nonneg d1, pow_pos hd_pos 2, this]
  -- |Ñ_act| ≥ B⁵/(2·10²⁹)
  have hcorr_eq : Nact - Ns = (-5 * d1 ^ 3 * e1 ^ 2
      + 2 * d * (d * d2 + 5 * d1 ^ 2) * e1 * e2 - 2 * d ^ 2 * d1 * e1 * e3
      - 2 * (d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4) * e1
      - 2 * d ^ 2 * d1 * e2 ^ 2 + 2 * d * d1 * (5 * d1 ^ 2 - d * d2) * e2
      - 2 * d ^ 2 * d1 ^ 2 * e3) := by
    have hb' : b = d1 + e1 := by rw [he1_def]; ring
    have hbp' : bp = d2 + e2 := by rw [he2_def]; ring
    have hbd' : bd = s4 + e3 := by rw [he3_def]; ring
    rw [hNact_def, hNs_def, hb', hbp', hbd']
    exact Ncorr_alg d d1 d2 s4 e1 e2 e3
  have hcorr_bd : |Nact - Ns| ≤ S.B ^ 5 / (2 * 10 ^ 29) := by
    rw [hcorr_eq]
    refine correction_abstract (B := S.B) (R := S.R) (l1 := ℓ₁) hRpos hBpos hℓ1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsmall
    · rw [abs_of_pos hd_pos]
      calc d ≤ 18 * S.D := hd_hi
        _ = 18 * (S.B * S.R) := by rw [hD_BR]
    · rw [show (10:ℝ) ^ 6 = 1000000 by norm_num]; exact hd1_hi
    · rw [abs_of_pos hd2_pos, show (10:ℝ) ^ 13 = 10000000000000 by norm_num]; exact hd2_hi
    · exact hs4_hi
    · rw [he1_def]; exact he1
    · rw [he2_def]; exact he2
    · rw [he3_def]; exact he3
  have hLn_eq : S.D ^ 5 / (10 ^ 29 * S.R ^ 5) = S.B ^ 5 / 10 ^ 29 := by
    rw [hBR]; ring
  have hNact_lb : S.B ^ 5 / (2 * 10 ^ 29) ≤ |Nact| := by
    have h1 : |Ns| ≤ |Nact| + |Nact - Ns| := by
      have heq : Nact - (Nact - Ns) = Ns := by ring
      have hb := abs_sub Nact (Nact - Ns)
      rwa [heq] at hb
    have hNs_lb' : S.B ^ 5 / 10 ^ 29 ≤ |Ns| := by rw [← hLn_eq]; exact hNs_lb
    linarith [hNs_lb', hcorr_bd, h1]
  -- |𝒲| ≥ Wlo := (4K/(6Xa)²)·B⁵/(2·10²⁹)
  have hW_lo : (4 * K / (6 * P.X * a) ^ 2) * (S.B ^ 5 / (2 * 10 ^ 29)) ≤ |E1 * D1 - ψ' * D2| := by
    rw [hWval, abs_mul, abs_of_pos h4Kpos]
    exact mul_le_mul_of_nonneg_left hNact_lb h4Kpos.le
  -- E1 ≤ U_clean := 10¹⁸·D⁴/(R²·6Xa)
  have hd1abs_pos : 0 < |d1| := lt_of_lt_of_le (by positivity) hd1_lo
  have hRSB : S.R * S.B = S.D := by rw [hBR]; field_simp
  have hE1_U : E1 ≤ 10 ^ 18 * (S.D ^ 4 / S.R ^ 2) / (6 * P.X * a) := by
    rw [hE1_def]
    have hd1sq : d1 ^ 2 ≤ (1000000 * S.B) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg d1) hd1_hi 2; rwa [sq_abs] at h
    have hdsq : d ^ 2 ≤ (18 * S.D) ^ 2 := pow_le_pow_left₀ hd_pos.le hd_hi 2
    have hdcube : d ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hd_pos.le hd_hi 3
    have hnum : 12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2 ≤ 10 ^ 18 * (S.D ^ 4 / S.R ^ 2) := by
      have h12 : 12 * d ^ 2 * d1 ^ 2 ≤ 12 * ((18 * S.D) ^ 2 * (1000000 * S.B) ^ 2) := by
        have := mul_le_mul hdsq hd1sq (sq_nonneg d1) (by positivity); linarith
      have h4 : 4 * d ^ 3 * d2 ≤ 4 * ((18 * S.D) ^ 3 * (10000000000000 * (S.B / S.R))) := by
        have := mul_le_mul hdcube hd2_hi hd2_pos.le (by positivity); linarith
      have heq : 12 * ((18 * S.D) ^ 2 * (1000000 * S.B) ^ 2)
          + 4 * ((18 * S.D) ^ 3 * (10000000000000 * (S.B / S.R)))
          = 237168000000000000 * (S.D ^ 4 / S.R ^ 2) := by rw [hBR]; field_simp; ring
      have hcoef : 237168000000000000 * (S.D ^ 4 / S.R ^ 2) ≤ 10 ^ 18 * (S.D ^ 4 / S.R ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith [h12, h4, heq.le, heq.ge, hcoef]
    gcongr
  -- ψ' bound for `lp_duality_lower`
  have hkey : 4 * d ^ 3 * |d1| ≤ 10 ^ 24 * S.R * (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) := by
    have hd_le : d ≤ 3 * 10 ^ 24 * S.R * |d1| := by
      have h1 : 18 * S.D ≤ 3 * 10 ^ 24 * S.R * (S.B / 1000000) := by
        rw [show 3 * 10 ^ 24 * S.R * (S.B / 1000000) = 3 * 10 ^ 18 * (S.R * S.B) by ring, hRSB]
        linarith [hDpos]
      have h2 : 3 * 10 ^ 24 * S.R * (S.B / 1000000) ≤ 3 * 10 ^ 24 * S.R * |d1| := by gcongr
      linarith [hd_hi, h1, h2]
    have hprod : 4 * d ^ 2 * |d1| * d ≤ 4 * d ^ 2 * |d1| * (3 * 10 ^ 24 * S.R * |d1|) :=
      mul_le_mul_of_nonneg_left hd_le (by positivity)
    have hstep : 4 * d ^ 3 * |d1| ≤ 12 * 10 ^ 24 * S.R * d ^ 2 * |d1| ^ 2 := by
      nlinarith only [hprod]
    rw [sq_abs d1] at hstep
    have h0 : (0:ℝ) ≤ 10 ^ 24 * S.R * (4 * d ^ 3 * d2) := by positivity
    have hexp : 10 ^ 24 * S.R * (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2)
        = 12 * 10 ^ 24 * S.R * d ^ 2 * d1 ^ 2 + 10 ^ 24 * S.R * (4 * d ^ 3 * d2) := by ring
    rw [hexp]; linarith [hstep, h0]
  have hψ'_bound : |ψ'| ≤ 10 ^ 24 * S.R * |E1| := by
    rw [abs_of_pos hE1pos, hE1_def]
    have hψabs : |ψ'| = 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
      rw [hψ'_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < 6 * P.X * a), abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (show (0:ℝ) < d ^ 3 by positivity)]
    rw [hψabs, show 10 ^ 24 * S.R * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * P.X * a))
        = (10 ^ 24 * S.R * (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2)) / (6 * P.X * a) from by ring]
    gcongr
  -- lp-duality engine
  have hlp := lp_duality_lower (W := E1 * D1 - ψ' * D2) (ψ' := ψ') (ψ'' := E1) (D1 := D1) (D2 := D2)
    (C := 10 ^ 24) (R := S.R) hRpos.le (by norm_num) rfl hψ'_bound
  rw [abs_of_pos hE1pos] at hlp
  have hCEpos : (0:ℝ) < 10 ^ 24 * E1 := by positivity
  -- abbreviate the smooth Wronskian floor and the curvature ceiling
  set Wlo := (4 * K / (6 * P.X * a) ^ 2) * (S.B ^ 5 / (2 * 10 ^ 29)) with hWlo_def
  set Uc := 10 ^ 18 * (S.D ^ 4 / S.R ^ 2) / (6 * P.X * a) with hUc_def
  have hWlo_nn : 0 ≤ Wlo := by rw [hWlo_def]; positivity
  have hUcpos : 0 < Uc := by rw [hUc_def]; positivity
  -- chain: goalLHS ≤ Wlo/(10²⁴U) ≤ Wlo/(10²⁴E1) ≤ |𝒲|/(10²⁴E1) ≤ |D1|+R|D2|
  have step1 : |E1 * D1 - ψ' * D2| / (10 ^ 24 * E1) ≤ |D1| + S.R * |D2| := by
    rw [div_le_iff₀ hCEpos]
    calc |E1 * D1 - ψ' * D2| ≤ 10 ^ 24 * E1 * (|D1| + S.R * |D2|) := hlp
      _ = (|D1| + S.R * |D2|) * (10 ^ 24 * E1) := by ring
  have step2 : Wlo / (10 ^ 24 * E1) ≤ |E1 * D1 - ψ' * D2| / (10 ^ 24 * E1) := by
    gcongr
  have step3 : Wlo / (10 ^ 24 * Uc) ≤ Wlo / (10 ^ 24 * E1) := by
    gcongr
  have hscale : (1 / 10 ^ 72) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / S.R ≤ Wlo / (10 ^ 24 * Uc) := by
    have hgoal_nn : (0:ℝ) ≤ (1 / 10 ^ 72) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / S.R := by
      positivity
    have heq : Wlo / (10 ^ 24 * Uc)
        = 40 * ((1 / 10 ^ 72) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / S.R) := by
      rw [hWlo_def, hUc_def, hK_def, hBR]; field_simp; ring
    rw [heq]; linarith [hgoal_nn]
  linarith [hscale, step3, step2, step1]

end Squarefree
