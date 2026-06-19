import Squarefree.Lower.Step23Phase
import Squarefree.Counting.Preimage

/-!
# §5 Step-3 smooth phase preimage count (writeup 977)

Apply the preimage-count lemma (Lemma 4.1) to the §5 Step-3 phase `φ_f`, using that `φ_f`
is `F`-expanding (`|φ_f'| ≥ F`, from `phif_deriv_lb`) and bounded (`|φ_f| ≤ V`, from
`phif_abs_ub`) on the window `[r₀, r₁]`.  This is the analytic half of Step 3, a direct
analogue of `step1_smooth_count`.

Since `φ_f` is not sign-definite (it carries the parameter `f`, which may be negative), the
variation bound `|φ_f x − φ_f y| ≤ V` is obtained from the triangle inequality together with a
pointwise magnitude bound of constant `5·10⁵` (the true constant `174960` fits) — exactly half
the target constant `10⁶`, so that the doubled triangle bound matches the goal's `V`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- §5 Step-3 phase magnitude with the half-constant `5·10⁵` (true value `174960`): a sharpened
version of `phif_abs_ub`, used to obtain the `|φ_f x − φ_f y| ≤ V` variation bound via the
triangle inequality (`2·(5·10⁵) = 10⁶`). -/
private theorem phif_abs_ub_half {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hflarge : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|) :
    |phif P.X a ℓ₁ ℓ₂ f r| ≤ 5 * 10 ^ 5 * (|f| * S.D ^ 4 / (P.X * S.A)) := by
  -- scale positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) := by positivity
  -- d̃ bounds and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  set d := dtilde P.X r a with hd_def
  -- the prefactor c := d⁴/(6Xa) > 0
  have hc_pos : 0 < d ^ 4 / (6 * P.X * a) := by positivity
  -- |phif| = c · |f + phi|
  have habs_eq : |phif P.X a ℓ₁ ℓ₂ f r| = d ^ 4 / (6 * P.X * a) * |f + phi P.X a ℓ₁ ℓ₂ r| := by
    rw [phif, hd_def, abs_mul, abs_of_pos hc_pos]
  rw [habs_eq]
  -- |φ| ≤ 10²⁰·L
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  -- |f + φ| ≤ 2·|f|  (since |φ| ≤ 10²⁰·L ≤ 10⁵⁵·L ≤ |f|)
  have hphi_le_f : phi P.X a ℓ₁ ℓ₂ r ≤ |f| := by
    have h1 : phi P.X a ℓ₁ ℓ₂ r ≤ 10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := hphi_ub
    have h2 : (10:ℝ) ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5))
        ≤ 10 ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := by
      apply mul_le_mul_of_nonneg_right _ hLpos.le; norm_num
    linarith
  have hfphi : |f + phi P.X a ℓ₁ ℓ₂ r| ≤ 2 * |f| := by
    calc |f + phi P.X a ℓ₁ ℓ₂ r| ≤ |f| + |phi P.X a ℓ₁ ℓ₂ r| := abs_add_le _ _
      _ = |f| + phi P.X a ℓ₁ ℓ₂ r := by rw [abs_of_nonneg hphi_nn]
      _ ≤ |f| + |f| := by linarith
      _ = 2 * |f| := by ring
  -- prefactor bound: c = d⁴/(6Xa) ≤ (18D)⁴/(6X·(A/5))
  have hc_le : d ^ 4 / (6 * P.X * a) ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hd_pos.le hd_hi 4) (by positivity)
    have : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
      apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
    linarith
  -- combine: true constant is 18⁴·5/3 = 174960 ≤ 5·10⁵
  have hfabs_nn : (0:ℝ) ≤ |f| := abs_nonneg _
  calc d ^ 4 / (6 * P.X * a) * |f + phi P.X a ℓ₁ ℓ₂ r|
      ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) * (2 * |f|) := by
        apply mul_le_mul hc_le hfphi (abs_nonneg _) (by positivity)
    _ = (18 ^ 4 * 5 / 3) * (|f| * S.D ^ 4 / (P.X * S.A)) := by
        field_simp; ring
    _ ≤ 5 * 10 ^ 5 * (|f| * S.D ^ 4 / (P.X * S.A)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        norm_num

theorem step3_smooth_count {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hflarge : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|)
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : 0 ≤ δ) :
    (((Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
        (fun (n : ℤ) => Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (10 ^ 6 * (|f| * S.D ^ 4 / (P.X * S.A)) + 2 * δ + 1)
        * (2 * δ / (|f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50)) + 1) := by
  have _ := hr01
  -- abbreviations matching `preimage_count`
  set φ : ℝ → ℝ := fun s => phif P.X a ℓ₁ ℓ₂ f s with hφ_def
  set V : ℝ := 10 ^ 6 * (|f| * S.D ^ 4 / (P.X * S.A)) with hV_def
  set F : ℝ := |f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50) with hF_def
  -- positivity facts
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) := by positivity
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  -- `|f| > 0` from `hflarge`
  have hfpos : 0 < |f| := by
    have : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f| := hflarge
    have hlb : 0 < (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) := by positivity
    linarith
  -- `F > 0`
  have hF : 0 < F := by rw [hF_def]; positivity
  -- `V ≥ 0`
  have hV : 0 ≤ V := by rw [hV_def]; positivity
  -- window helpers
  have hwin_lo : ∀ z : ℝ, r₀ ≤ z → (1/72) * S.R ≤ z := fun z hz => le_trans hr0_lo hz
  have hwin_hi : ∀ z : ℝ, z ≤ r₁ → z + ℓ₁ ≤ 16 * S.R := fun z hz => by
    have : z + ℓ₁ ≤ r₁ + ℓ₁ := by linarith
    linarith [hr1_hi]
  have hwin_pos : ∀ z : ℝ, r₀ ≤ z → 0 < z := fun z hz => by
    have := hwin_lo z hz; nlinarith [hRpos]
  have hwin_posl : ∀ z : ℝ, r₀ ≤ z → 0 < z + ℓ₁ := fun z hz => by
    have := hwin_pos z hz; linarith
  -- The expanding bound for `x < y` (factored so we can reuse it after swapping).
  have key : ∀ x : ℝ, x ∈ Set.Icc r₀ r₁ → ∀ y : ℝ, y ∈ Set.Icc r₀ r₁ → x < y →
      F * |x - y| ≤ |φ x - φ y| := by
    intro x hx y hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    -- continuity on `[x, y]`
    have hcont : ContinuousOn φ (Set.Icc x y) := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := hz
      have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx)
      have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx)
      exact (phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := z)
        ha0 hz0 hzl hℓne).continuousAt.continuousWithinAt
    -- differentiability on `(x, y)`
    have hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt φ (deriv φ z) z := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := hz
      have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx.le)
      have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx.le)
      exact (phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := z)
        ha0 hz0 hzl hℓne).differentiableAt.hasDerivAt
    -- mean value theorem
    obtain ⟨ξ, hξ, hslope⟩ :=
      exists_hasDerivAt_eq_slope φ (fun z => deriv φ z) hxy hcont hderiv
    obtain ⟨hξx, hξy⟩ := hξ
    -- window hypotheses for `ξ`
    have hξ_lo : (1/72) * S.R ≤ ξ := hwin_lo ξ (le_trans hx0 hξx.le)
    have hξ_hi : ξ + ℓ₁ ≤ 16 * S.R := hwin_hi ξ (le_trans hξy.le hy1)
    -- `|φ' ξ| ≥ F`
    have hdlb : F ≤ |deriv φ ξ| :=
      phif_deriv_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := ξ)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hξ_lo hξ_hi hsmall hflarge
    -- `φ y - φ x = (deriv φ ξ) * (y - x)`
    have hyx : 0 < y - x := by linarith
    have hval : φ y - φ x = deriv φ ξ * (y - x) := by
      rw [hslope]; field_simp
    have hxyabs : |x - y| = y - x := by
      rw [abs_sub_comm]; exact abs_of_pos hyx
    have hφabs : |φ x - φ y| = |deriv φ ξ| * (y - x) := by
      rw [abs_sub_comm, hval, abs_mul, abs_of_pos hyx]
    rw [hxyabs, hφabs]
    apply mul_le_mul_of_nonneg_right hdlb hyx.le
  -- the expanding hypothesis for `preimage_count`
  have hexp : ∀ x ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc r₀ r₁, F * |x - y| ≤ |φ x - φ y| := by
    intro x hx y hy
    rcases lt_trichotomy x y with h | h | h
    · exact key x hx y hy h
    · subst h; simp
    · have := key y hy x hx h
      rwa [abs_sub_comm y x, abs_sub_comm (φ y) (φ x)] at this
  -- the variation hypothesis for `preimage_count`
  -- (φ_f not sign-definite ⇒ triangle: |φx − φy| ≤ |φx| + |φy| ≤ 2·(5·10⁵·…) = V)
  have hvar : ∀ x ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc r₀ r₁, |φ x - φ y| ≤ V := by
    intro x hx y hy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have hxub : |phif P.X a ℓ₁ ℓ₂ f x| ≤ 5 * 10 ^ 5 * (|f| * S.D ^ 4 / (P.X * S.A)) :=
      phif_abs_ub_half (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := x)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 (hwin_lo x hx0) (hwin_hi x hx1) hflarge
    have hyub : |phif P.X a ℓ₁ ℓ₂ f y| ≤ 5 * 10 ^ 5 * (|f| * S.D ^ 4 / (P.X * S.A)) :=
      phif_abs_ub_half (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := y)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 (hwin_lo y hy0) (hwin_hi y hy1) hflarge
    have htri : |φ x - φ y| ≤ |φ x| + |φ y| := abs_sub _ _
    simp only [hφ_def] at hxub hyub htri ⊢
    rw [hV_def]
    linarith
  -- apply the preimage count lemma
  exact Counting.preimage_count r₀ r₁ V F δ φ hF hδ hV hexp hvar

end Squarefree
