import Squarefree.Lower.Step2D2ZeroBound
import Squarefree.Lower.Step2D2ZeroCorr
import Squarefree.Lower.Step2D2Split
import Squarefree.Lower.Step2Phi3Poly
import Squarefree.Lower.Step2ChiPos

/-!
# §5 Step-2 φ″-zero count — ratio monotonicity and the ≤2-piece split

This module finishes the §5 Step-2 φ″-zero count.  The zero set `{r : φ_f''(r) = 0}` is the graph
`f = m(r)` with `m = −χ''/ψ''` (`χ'' = iteratedDeriv 2 (phif … 0)`, `ψ'' = E1` the closed form).
By the quotient rule `m' = −(χ'''ψ'' − χ''ψ''')/(ψ'')² = −W₂/(ψ'')²` and `W₂ < 0` on the §5 band
(`Step2D2ZeroBound`/`Step2D2ZeroCorr`), so `m` is strictly monotone.  Feeding this into the abstract
`deriv_two_pieces_of_strictMono` (`Step2D2Split`) gives the ≤2-piece split `phif_d2_zero_le_one`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 6400000

/-- The closed-form second derivative `φ_f''` as a function of `s` (the `phif_iteratedDeriv2_eq`
right-hand side), used to transfer differentiability to `iteratedDeriv 2 φ_f`. -/
private noncomputable def F2 (P : Globals) (a ℓ₁ ℓ₂ f s : ℝ) : ℝ :=
  (12 * (dtilde P.X s a) ^ 2 * (deriv (fun u => dtilde P.X u a) s) ^ 2
        + 4 * (dtilde P.X s a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) s)
      / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ s)
    + (8 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a)
      * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s
    + (dtilde P.X s a) ^ 4 / (6 * P.X * a)
      * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s

/-- **`iteratedDeriv 2 φ_f` is differentiable, with derivative `iteratedDeriv 3 φ_f`.**  Builds the
third-derivative `HasDerivAt` of the §5 Steps-2&3 phase, kept symbolic.  (`phif_deriv_hasDerivAt`,
one order up.) -/
theorem phif_iteratedDeriv2_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) s)
      (iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r) r := by
  -- `iteratedDeriv 2 φ_f =ᶠ F2` near `r`
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ₁} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr0, hrl⟩
  have heq : iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) =ᶠ[nhds r]
      (fun s => F2 P a ℓ₁ ℓ₂ f s) := by
    refine Filter.eventuallyEq_of_mem hU ?_
    intro s hs
    rw [phif_iteratedDeriv2_eq ha0 hs.1 hs.2 hℓne]; rfl
  -- `F2` is differentiable at `r`
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt P.X_pos ha0 hr0; rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt P.X_pos ha0 hr0
  have hHD2 : HasDerivAt (fun s => iteratedDeriv 2 (fun u => dtilde P.X u a) s)
      (iteratedDeriv 3 (fun u => dtilde P.X u a) r) r :=
    dtilde_iteratedDeriv2_hasDerivAt P.X_pos ha0 hr0
  have hphi : HasDerivAt (fun s => phi P.X a ℓ₁ ℓ₂ s) (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    (phi_hasDerivAt (P := P) ha0 hr0 hrl hℓne).differentiableAt.hasDerivAt
  have hphi' : HasDerivAt (fun s => deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    phi_deriv_hasDerivAt (P := P) ha0 hr0 hrl hℓne
  have hphi'' : HasDerivAt (fun s => iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    phi_iteratedDeriv2_hasDerivAt (P := P) ha0 hr0 hrl hℓne
  have hd2 : HasDerivAt (fun s => (dtilde P.X s a) ^ 2) _ r := hHD0.pow 2
  have hd3 : HasDerivAt (fun s => (dtilde P.X s a) ^ 3) _ r := hHD0.pow 3
  have hd4 : HasDerivAt (fun s => (dtilde P.X s a) ^ 4) _ r := hHD0.pow 4
  have hd1sq : HasDerivAt (fun s => (deriv (fun u => dtilde P.X u a) s) ^ 2) _ r := hHD1.pow 2
  have hAnum : DifferentiableAt ℝ
      (fun s => 12 * (dtilde P.X s a) ^ 2 * (deriv (fun u => dtilde P.X u a) s) ^ 2
        + 4 * (dtilde P.X s a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) s) r :=
    (((hd2.const_mul 12).mul hd1sq).add ((hd3.const_mul 4).mul hHD2)).differentiableAt
  have hBnum : DifferentiableAt ℝ
      (fun s => 8 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) r :=
    ((hd3.const_mul 8).mul hHD1).differentiableAt
  have hFdiff : DifferentiableAt ℝ (fun s => F2 P a ℓ₁ ℓ₂ f s) r := by
    apply DifferentiableAt.add
    apply DifferentiableAt.add
    · exact (hAnum.div_const _).mul (hphi.differentiableAt.const_add f)
    · exact (hBnum.div_const _).mul hphi'.differentiableAt
    · exact (hd4.differentiableAt.div_const _).mul hphi''.differentiableAt
  have hdiff2 : DifferentiableAt ℝ (iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u)) r :=
    hFdiff.congr_of_eventuallyEq heq
  have hval : iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r
      = deriv (iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u)) r := by
    rw [iteratedDeriv_succ]
  rw [hval]
  exact hdiff2.hasDerivAt

/-- The closed-form curvature scale `ψ'' = (12 d̃²(d̃')² + 4 d̃³ d̃'')/(6Xa)`, as a function of `r`. -/
private noncomputable def E1f (P : Globals) (a r : ℝ) : ℝ :=
  (12 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
      + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r) / (6 * P.X * a)

/-- `ψ''` is differentiable with derivative `ψ''' = (24 d̃(d̃')³ + 36 d̃²d̃'d̃'' + 4 d̃³d̃''')/(6Xa)`. -/
private theorem E1f_hasDerivAt {P : Globals} {a r : ℝ} (ha0 : 0 < a) (hr0 : 0 < r) :
    HasDerivAt (fun s => E1f P a s)
      ((24 * dtilde P.X r a * (deriv (fun u => dtilde P.X u a) r) ^ 3
          + 36 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r
              * iteratedDeriv 2 (fun u => dtilde P.X u a) r
          + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 3 (fun u => dtilde P.X u a) r)
        / (6 * P.X * a)) r := by
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt P.X_pos ha0 hr0; rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt P.X_pos ha0 hr0
  have hHD2 : HasDerivAt (fun s => iteratedDeriv 2 (fun u => dtilde P.X u a) s)
      (iteratedDeriv 3 (fun u => dtilde P.X u a) r) r :=
    dtilde_iteratedDeriv2_hasDerivAt P.X_pos ha0 hr0
  have hd2 : HasDerivAt (fun s => (dtilde P.X s a) ^ 2)
      (2 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 2; simpa using this
  have hd3 : HasDerivAt (fun s => (dtilde P.X s a) ^ 3)
      (3 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 3; simpa using this
  have hd1sq : HasDerivAt (fun s => (deriv (fun u => dtilde P.X u a) s) ^ 2)
      (2 * deriv (fun u => dtilde P.X u a) r * iteratedDeriv 2 (fun u => dtilde P.X u a) r) r := by
    have := hHD1.pow 2; simpa using this
  have hnum := ((hd2.const_mul 12).mul hd1sq).add ((hd3.const_mul 4).mul hHD2)
  have hq := hnum.div_const (6 * P.X * a)
  have heq : (fun s => E1f P a s)
      = (fun s => (12 * (dtilde P.X s a) ^ 2 * (deriv (fun u => dtilde P.X u a) s) ^ 2
          + 4 * (dtilde P.X s a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) s) / (6 * P.X * a)) := by
    funext s; rw [E1f]
  rw [heq]
  convert hq using 1
  ring

/-- `ψ'' > 0` on the §5 band (`d̃ > 0`, `d̃'' > 0`). -/
private theorem E1f_pos {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1 / 72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    0 < E1f P a r := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  obtain ⟨hd2_pos, _, _⟩ := dtilde_d2_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  rw [E1f]
  apply div_pos _ (by have := P.X_pos; positivity)
  nlinarith [sq_nonneg (deriv (fun u => dtilde P.X u a) r), pow_pos hd_pos 2, pow_pos hd_pos 3,
    hd2_pos, mul_pos (pow_pos hd_pos 3) hd2_pos]

/-- **The `f`-free Wronskian `W₂ = χ'''·ψ'' − χ''·ψ''' < 0` on the §5 band.**  The numerator of
`deriv (χ''/ψ'')` (with `χ'' = iteratedDeriv 2 (phif … 0)`, `ψ'' = E1f`) is the `f`-free Wronskian.
Via `welim2_poly`/`w2_poly` it equals `(K/(6Xa)²)·W2num_act/d̃²`, with `W2num_act = W2num_s + corr`
where `W2num_s ≤ −B⁷/10⁴²` (`w2_smooth_upper`) and `|corr| ≤ B⁷/(2·10⁴²)` (`w2_correction_abstract`),
so `W2num_act < 0` and the Wronskian is negative. -/
private theorem W2_act_neg {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1 / 72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 110 * ℓ₁ ≤ S.R) :
    iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) r * E1f P a r
        - iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) r
          * ((24 * dtilde P.X r a * (deriv (fun u => dtilde P.X u a) r) ^ 3
              + 36 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r
                  * iteratedDeriv 2 (fun u => dtilde P.X u a) r
              + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 3 (fun u => dtilde P.X u a) r)
            / (6 * P.X * a)) < 0 := by
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by
    unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have h6Xa : (6 : ℝ) * P.X * a ≠ 0 := by positivity
  have hBR : S.B = S.D / S.R := Scale.B_eq_D_div_R S
  have hD_BR : S.D = S.B * S.R := by rw [hBR]; field_simp
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hconv3 : S.D / S.R ^ 3 = S.B / S.R ^ 2 := by rw [hBR]; field_simp
  have hconv4 : S.D / S.R ^ 4 = S.B / S.R ^ 3 := by rw [hBR]; field_simp
  have hconv5 : S.D / S.R ^ 5 = S.B / S.R ^ 4 := by rw [hBR]; field_simp
  have hsmall78 : (10 : ℝ) ^ 78 * ℓ₁ ≤ S.R := by nlinarith [hsmall, hℓ1, pow_pos (by norm_num : (0:ℝ) < 10) 78]
  have hwin : ∀ x ∈ Set.Icc r (r + ℓ₁), (1 / 72) * S.R ≤ x ∧ x ≤ 16 * S.R ∧ 0 < x := by
    intro x hx; obtain ⟨hxl, hxr⟩ := hx
    exact ⟨by linarith, by linarith, by linarith⟩
  -- closed-form derivative values
  have hChi2eq := phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
    ha0 hr0 hrl hℓne
  have hChi3eq := phif_iteratedDeriv3_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
    ha0 hr0 hrl hℓne
  have hφ1eq := (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).deriv
  have hφ2eq := phi_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have hφ3eq := phi3_poly (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have hφval : phi P.X a ℓ₁ ℓ₂ r
      = 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a * (bt P.X a ℓ₁ r) ^ 2 / (dtilde P.X r a) ^ 5 := by
    simp only [phi]
  -- ε bounds via double-MVT (mirror `chi_iteratedDeriv2_pos`, plus `ε₄`)
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
  have he4 : |(iteratedDeriv 3 (fun u => dtilde P.X u a) (r + ℓ₁)
          - iteratedDeriv 3 (fun u => dtilde P.X u a) r) / ℓ₁
        - iteratedDeriv 4 (fun u => dtilde P.X u a) r| ≤ ℓ₁ * (118098 * 10 ^ 28 * (S.B / S.R ^ 4)) := by
    have key := bt_iteratedDeriv3_fd_error (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (r := r)
      hAD ha0 ha_lo ha_hi hℓ1 hwin
    rw [hconv5] at key
    refine key.trans ?_
    apply mul_le_mul_of_nonneg_left _ hℓ1.le
    rw [show (118098 : ℝ) * 10 ^ 28 = 1180980000000000000000000000000000 by norm_num]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    norm_num
  -- atom magnitude bounds at `r`
  obtain ⟨hd1_lo, hd1_hi⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  obtain ⟨hd2_pos, _, hd2_hi⟩ := dtilde_d2_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hs4_hi : |iteratedDeriv 3 (fun u => dtilde P.X u a) r| ≤ 10 ^ 19 * (S.B / S.R ^ 2) := by
    rw [← hconv3, show (10:ℝ) ^ 19 = 10000000000000000000 by norm_num]
    exact dtilde_d3_upper hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd4_hi : |iteratedDeriv 4 (fun u => dtilde P.X u a) r| ≤ 2 * 10 ^ 25 * (S.B / S.R ^ 3) := by
    rw [← hconv4, show (2:ℝ) * 10 ^ 25 = 20000000000000000000000000 by norm_num]
    exact dtilde_d4_upper hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  -- abbreviate atoms
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun u => dtilde P.X u a) r with hd1_def
  set d2 := iteratedDeriv 2 (fun u => dtilde P.X u a) r with hd2_def
  set s4 := iteratedDeriv 3 (fun u => dtilde P.X u a) r with hs4_def
  set d4 := iteratedDeriv 4 (fun u => dtilde P.X u a) r with hd4_def
  set b := bt P.X a ℓ₁ r with hb_def
  set bp := (deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁
    with hbp_def
  set bd := (iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
    - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁ with hbd_def
  set bt3 := iteratedDeriv 3 (fun s => bt P.X a ℓ₁ s) r with hbt3_def
  have hbt3fd : bt3 = (iteratedDeriv 3 (fun u => dtilde P.X u a) (r + ℓ₁)
      - iteratedDeriv 3 (fun u => dtilde P.X u a) r) / ℓ₁ := by
    rw [hbt3_def]; exact bt_iteratedDeriv3 hXpos ha0 hr0 hrl hℓne
  have hbtp : deriv (fun s => bt P.X a ℓ₁ s) r = bp := by
    rw [hbp_def]; exact (bt_hasDerivAt hXpos ha0 hr0 hrl hℓne).deriv
  have hbtdd : iteratedDeriv 2 (fun s => bt P.X a ℓ₁ s) r = bd := by
    rw [hbd_def]; exact bt_iteratedDeriv2 hXpos ha0 hr0 hrl hℓne
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hdne : d ≠ 0 := ne_of_gt hd_pos
  set e1 := b - d1 with he1_def
  set e2 := bp - d2 with he2_def
  set e3 := bd - s4 with he3_def
  set e4 := bt3 - d4 with he4_def
  set Nact := -20 * b ^ 2 * d ^ 2 * d1 ^ 2 * s4 + 60 * b ^ 2 * d ^ 2 * d1 * d2 ^ 2
      - 120 * b ^ 2 * d1 ^ 5 - 8 * b * bd * d ^ 4 * s4 - 96 * b * bd * d ^ 3 * d1 * d2
      - 120 * b * bd * d ^ 2 * d1 ^ 3 + 16 * b * bp * d ^ 3 * d1 * s4
      - 24 * b * bp * d ^ 3 * d2 ^ 2 + 120 * b * bp * d ^ 2 * d1 ^ 2 * d2
      + 240 * b * bp * d * d1 ^ 4 + 8 * b * bt3 * d ^ 4 * d2 + 24 * b * bt3 * d ^ 3 * d1 ^ 2
      + 24 * bd * bp * d ^ 4 * d2 + 72 * bd * bp * d ^ 3 * d1 ^ 2 - 8 * bp ^ 2 * d ^ 4 * s4
      - 96 * bp ^ 2 * d ^ 3 * d1 * d2 - 120 * bp ^ 2 * d ^ 2 * d1 ^ 3 with hNact_def
  set Ns := 8 * d ^ 4 * d1 * d2 * d4 - 8 * d ^ 4 * d1 * s4 ^ 2 + 16 * d ^ 4 * d2 ^ 2 * s4
      + 24 * d ^ 3 * d1 ^ 3 * d4 - 8 * d ^ 3 * d1 ^ 2 * d2 * s4 - 120 * d ^ 3 * d1 * d2 ^ 3
      - 140 * d ^ 2 * d1 ^ 4 * s4 + 60 * d ^ 2 * d1 ^ 3 * d2 ^ 2 + 240 * d * d1 ^ 5 * d2
      - 120 * d1 ^ 7 with hNs_def
  -- the Wronskian numerator equals `(K/(6Xa)²)·Nact/d²`
  have hNumVal : iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) r * E1f P a r
      - iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) r
        * ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * P.X * a))
      = K / (6 * P.X * a) ^ 2 * Nact / d ^ 2 := by
    rw [hChi3eq, hChi2eq, E1f, hφval, hφ1eq, hφ2eq, hφ3eq, hbtp, hbtdd, hNact_def, hK_def]
    field_simp
    ring
  -- correction expansion and bound
  have hcorr_eq : Nact - Ns = 8 * d ^ 4 * d1 * d2 * e4
        - 8 * d ^ 4 * d1 * s4 * e3
        + 24 * d ^ 4 * d2 ^ 2 * e3
        + 8 * d ^ 4 * d2 * d4 * e1
        + 8 * d ^ 4 * d2 * e1 * e4
        + 24 * d ^ 4 * d2 * e2 * e3
        + 8 * d ^ 4 * d2 * s4 * e2
        - 8 * d ^ 4 * s4 * e1 * e3
        - 8 * d ^ 4 * s4 ^ 2 * e1
        - 8 * d ^ 4 * s4 * e2 ^ 2
        + 24 * d ^ 3 * d1 ^ 3 * e4
        - 24 * d ^ 3 * d1 ^ 2 * d2 * e3
        + 24 * d ^ 3 * d1 ^ 2 * d4 * e1
        + 24 * d ^ 3 * d1 ^ 2 * e1 * e4
        + 72 * d ^ 3 * d1 ^ 2 * e2 * e3
        + 88 * d ^ 3 * d1 ^ 2 * s4 * e2
        - 216 * d ^ 3 * d1 * d2 ^ 2 * e2
        - 96 * d ^ 3 * d1 * d2 * e1 * e3
        - 80 * d ^ 3 * d1 * d2 * s4 * e1
        - 96 * d ^ 3 * d1 * d2 * e2 ^ 2
        + 16 * d ^ 3 * d1 * s4 * e1 * e2
        - 24 * d ^ 3 * d2 ^ 3 * e1
        - 24 * d ^ 3 * d2 ^ 2 * e1 * e2
        - 120 * d ^ 2 * d1 ^ 4 * e3
        - 120 * d ^ 2 * d1 ^ 3 * d2 * e2
        - 120 * d ^ 2 * d1 ^ 3 * e1 * e3
        - 160 * d ^ 2 * d1 ^ 3 * s4 * e1
        - 120 * d ^ 2 * d1 ^ 3 * e2 ^ 2
        + 240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1
        + 120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2
        - 20 * d ^ 2 * d1 ^ 2 * s4 * e1 ^ 2
        + 60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2
        + 240 * d * d1 ^ 5 * e2
        + 240 * d * d1 ^ 4 * d2 * e1
        + 240 * d * d1 ^ 4 * e1 * e2
        - 240 * d1 ^ 6 * e1
        - 120 * d1 ^ 5 * e1 ^ 2 := by
    have hb' : b = d1 + e1 := by rw [he1_def]; ring
    have hbp' : bp = d2 + e2 := by rw [he2_def]; ring
    have hbd' : bd = s4 + e3 := by rw [he3_def]; ring
    have hbt3' : bt3 = d4 + e4 := by rw [he4_def]; ring
    rw [hNact_def, hNs_def, hb', hbp', hbd', hbt3']
    ring
  have hcorr_bd : |Nact - Ns| ≤ S.B ^ 7 / (2 * 10 ^ 42) := by
    rw [hcorr_eq]
    refine w2_correction_abstract (d := d) (d1 := d1) (d2 := d2) (s4 := s4) (d4 := d4)
      (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (B := S.B) (R := S.R) (l1 := ℓ₁)
      hRpos hBpos hℓ1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsmall
    · rw [abs_of_pos hd_pos]; calc d ≤ 18 * S.D := hd_hi
        _ = 18 * (S.B * S.R) := by rw [hD_BR]
    · rw [show (10:ℝ) ^ 6 = 1000000 by norm_num]; exact hd1_hi
    · rw [abs_of_pos hd2_pos, show (10:ℝ) ^ 13 = 10000000000000 by norm_num]; exact hd2_hi
    · exact hs4_hi
    · exact hd4_hi
    · rw [he1_def]; exact he1
    · rw [he2_def, hbp_def]; exact he2
    · rw [he3_def, hbd_def]; exact he3
    · rw [he4_def, hbt3fd]; exact he4
  have hNs_ub : Ns ≤ -(S.B ^ 7 / 10 ^ 42) := by
    rw [hNs_def]
    exact w2_smooth_upper (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
  -- `Nact < 0`
  have hNact_neg : Nact < 0 := by
    have hle := (abs_le.mp hcorr_bd).2
    have hpos : 0 < S.B ^ 7 / (2 * 10 ^ 42) := by positivity
    nlinarith [hNs_ub, hle, hpos]
  -- conclude
  rw [hNumVal]
  have hKpos : 0 < K := by rw [hK_def]; positivity
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (div_pos hKpos (by positivity)) hNact_neg
  · exact pow_pos hd_pos 2

/-- **The ratio `χ''/ψ'' = iteratedDeriv 2 (phif … 0) / E1f` is strictly antitone on the §5 band.**
By the quotient rule its derivative is `W₂/(ψ'')² < 0` (`W2_act_neg`). -/
private theorem phif_d2_ratio_strictAnti {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r₀ r₁ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1 / 72) * S.R ≤ r₀) (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 110 * ℓ₁ ≤ S.R) :
    StrictAntiOn (fun x => iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) x / E1f P a x)
      (Set.Icc r₀ r₁) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hwin_pt : ∀ x ∈ Set.Icc r₀ r₁,
      (1 / 72) * S.R ≤ x ∧ r₁ + ℓ₁ ≤ 16 * S.R ∧ 0 < x ∧ 0 < x + ℓ₁ ∧ x + ℓ₁ ≤ 16 * S.R := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := Set.mem_Icc.mp hx
    have hx72 : (1 / 72) * S.R ≤ x := le_trans hr_lo hxl
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx72
    exact ⟨hx72, hwin, hx0, by linarith, by linarith⟩
  refine strictAntiOn_of_deriv_neg (convex_Icc r₀ r₁) ?_ ?_
  · intro x hx
    obtain ⟨hx72, _, hx0, hxl0, _⟩ := hwin_pt x hx
    have hc := (phif_iteratedDeriv2_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
      ha0 hx0 hxl0 (ne_of_gt hℓ1)).continuousAt
    have hd := (E1f_hasDerivAt (P := P) (a := a) ha0 hx0).continuousAt
    have hne : E1f P a x ≠ 0 :=
      (E1f_pos (P := P) (S := S) hAD ha0 ha_lo ha_hi hx72 (by linarith [hxl0, hℓ1])).ne'
    exact (hc.div hd hne).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hxl, hxr⟩ := hx
    obtain ⟨hx72, _, hx0, hxl0, hxl16⟩ := hwin_pt x ⟨hxl.le, hxr.le⟩
    have hx16 : x ≤ 16 * S.R := by linarith [hℓ1.le]
    have hc := phif_iteratedDeriv2_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
      ha0 hx0 hxl0 (ne_of_gt hℓ1)
    have hd := E1f_hasDerivAt (P := P) (a := a) ha0 hx0
    have hne : E1f P a x ≠ 0 :=
      (E1f_pos (P := P) (S := S) hAD ha0 ha_lo ha_hi hx72 hx16).ne'
    have key : HasDerivAt (fun y => iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) y / E1f P a y)
        ((iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) x * E1f P a x
            - iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) x
              * ((24 * dtilde P.X x a * (deriv (fun u => dtilde P.X u a) x) ^ 3
                  + 36 * (dtilde P.X x a) ^ 2 * deriv (fun u => dtilde P.X u a) x
                      * iteratedDeriv 2 (fun u => dtilde P.X u a) x
                  + 4 * (dtilde P.X x a) ^ 3 * iteratedDeriv 3 (fun u => dtilde P.X u a) x)
                / (6 * P.X * a)))
          / E1f P a x ^ 2) x := hc.div hd hne
    rw [key.deriv]
    apply div_neg_of_neg_of_pos
    · exact W2_act_neg (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hx72 hxl16 hsmall
    · exact pow_pos (E1f_pos (P := P) (S := S) hAD ha0 ha_lo ha_hi hx72 hx16) 2

/-- **§5 Step-2 φ″-zero count: the ≤2-piece split.**  On a §5 band `[r₀,r₁]`, `deriv φ_f` is
monotone-up-then-down: there is a split point `z` with `deriv φ_f` `MonotoneOn [r₀,z]` and
`AntitoneOn [z,r₁]`.  (The zero locus `φ_f''=0` is the graph `f = m`, `m = −χ''/ψ''` strictly
monotone by `phif_d2_ratio_strictAnti`; feed into `deriv_two_pieces_of_strictMono`.) -/
theorem phif_d2_zero_le_one {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r₀ r₁ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr : r₀ ≤ r₁) (hr_lo : (1 / 72) * S.R ≤ r₀) (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 110 * ℓ₁ ≤ S.R) :
    ∃ z, z ∈ Set.Icc r₀ r₁ ∧
      MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ z) ∧
      AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc z r₁) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hwin_pt : ∀ x ∈ Set.Icc r₀ r₁,
      (1 / 72) * S.R ≤ x ∧ 0 < x ∧ 0 < x + ℓ₁ ∧ x ≤ 16 * S.R := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := Set.mem_Icc.mp hx
    have hx72 : (1 / 72) * S.R ≤ x := le_trans hr_lo hxl
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx72
    exact ⟨hx72, hx0, by linarith, by linarith [hℓ1.le]⟩
  -- the zero-locus function `m = −χ''/ψ''`
  set m := fun x => -(iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) x / E1f P a x) with hm_def
  -- `χ''/ψ''` strictly antitone, hence `m` strictly monotone and continuous
  have hAnti := phif_d2_ratio_strictAnti (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hwin hsmall
  have hm : StrictMonoOn m (Set.Icc r₀ r₁) := by
    intro p hp q hq hpq
    have := hAnti hp hq hpq
    simp only [hm_def]
    linarith
  have hratio_cont : ContinuousOn
      (fun x => iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) x / E1f P a x) (Set.Icc r₀ r₁) := by
    intro x hx
    obtain ⟨hx72, hx0, hxl0, hx16⟩ := hwin_pt x hx
    have hc := (phif_iteratedDeriv2_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
      ha0 hx0 hxl0 hℓne).continuousAt
    have hd := (E1f_hasDerivAt (P := P) (a := a) ha0 hx0).continuousAt
    have hne : E1f P a x ≠ 0 :=
      (E1f_pos (P := P) (S := S) hAD ha0 ha_lo ha_hi hx72 hx16).ne'
    exact (hc.div hd hne).continuousWithinAt
  have hmcont : ContinuousOn m (Set.Icc r₀ r₁) := hratio_cont.neg
  -- the C² data for `g = φ_f`
  have hcont : ContinuousOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁) := by
    intro x hx
    obtain ⟨_, hx0, hxl0, _⟩ := hwin_pt x hx
    exact (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 hℓne).continuousAt.continuousWithinAt
  have hdiff : ∀ x ∈ Set.Ioo r₀ r₁, DifferentiableAt ℝ (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x := by
    intro x hx
    obtain ⟨_, hx0, hxl0, _⟩ := hwin_pt x ⟨hx.1.le, hx.2.le⟩
    exact (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 hℓne).differentiableAt
  have hpos : ∀ x ∈ Set.Icc r₀ r₁, 0 < E1f P a x := by
    intro x hx
    obtain ⟨hx72, _, _, hx16⟩ := hwin_pt x hx
    exact E1f_pos (P := P) (S := S) hAD ha0 ha_lo ha_hi hx72 hx16
  have hg2 : ∀ x ∈ Set.Icc r₀ r₁,
      deriv (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x = E1f P a x * (f - m x) := by
    intro x hx
    obtain ⟨_, hx0, hxl0, _⟩ := hwin_pt x hx
    have hd2 : deriv (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) x
        = iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) x :=
      (phif_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
        ha0 hx0 hxl0 hℓne).deriv
    have hne : E1f P a x ≠ 0 := (hpos x hx).ne'
    -- `φ_f'' = χ'' + E1·f`, with `χ'' = φ_f''|₀`
    have hff := phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
      ha0 hx0 hxl0 hℓne
    have hf0 := phif_iteratedDeriv2_eq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := 0)
      ha0 hx0 hxl0 hℓne
    have hsplit : iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) x
        = iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ 0 u) x + E1f P a x * f := by
      rw [hff, hf0, E1f]; ring
    rw [hd2, hsplit, hm_def]
    field_simp
    ring
  obtain ⟨z, hz, hmono, hanti⟩ := deriv_two_pieces_of_strictMono (g := fun s => phif P.X a ℓ₁ ℓ₂ f s)
    (m := m) (ψ2 := fun x => E1f P a x) (f := f) hr hcont hdiff hpos hg2 hmcont hm
  exact ⟨z, hz, hmono, hanti⟩

end Squarefree
