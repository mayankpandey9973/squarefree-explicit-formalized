import Squarefree.Lower.Step4PhivDeriv
import Squarefree.Counting.Preimage

/-!
# §5 Step-4 confined-interval smooth count (writeup 1085–1088)

`step4_smooth_count_conf` applies Lemma 4.1 (`preimage_count`) to `φ_v` over a *confined*
sub-interval `[r₀,r₁] ⊆ [R/72, 16R]` (the `Σ_s`-MVT confinement interval `I_s(v)`).  Unlike
`step4_smooth_count` (which uses the global magnitude `|φ_v| ≍ T` for the variation), here the
variation `V` is bounded by `phiv_deriv_ub_scale × (r₁−r₀)` (the matched derivative UB), so that
the leading `V·(2δ/F)` term scales as `|I_s|·δ` after the `W`-cancellation — exactly what the
`s1+s2` skeleton term needs (`step4_perv_count`, `Step4PervCount.lean`).
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **§5 Step-4 confined-interval smooth count.**  On `[r₀,r₁] ⊆ [R/72, 16R]` the count of
integer `r` with `‖φ_v(r)‖ ≤ δ` is `≤ (10¹³·W·(r₁−r₀) + 2δ + 1)(2δ/F + 1)`, with the variation
`V` bounded by `phiv_deriv_ub_scale × (r₁−r₀)` (NOT the global magnitude), so that the leading
`V·(2δ/F)` term scales as `|I_s|·δ` after the `W`-cancellation. -/
theorem step4_smooth_count_conf {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ v r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hvlarge : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |v|)
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : 0 ≤ δ) :
    (((Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
        (fun (n : ℤ) => Counting.distInt (phiv P.X a ℓ₁ ℓ₂ v (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (10 ^ 13 * (ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R)) * (r₁ - r₀) + 2 * δ + 1)
        * (2 * δ / (ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R * 10 ^ 50)) + 1) := by
  set φ : ℝ → ℝ := fun s => phiv P.X a ℓ₁ ℓ₂ v s with hφ_def
  set W : ℝ := ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R) with hW_def
  set V : ℝ := 10 ^ 13 * W * (r₁ - r₀) with hV_def
  set F : ℝ := ℓ₁ * P.X * a * |v| / (S.D ^ 4 * S.R * 10 ^ 50) with hF_def
  -- positivity
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hvpos : 0 < |v| := by
    have hlb : 0 < (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) := by
      positivity
    linarith [hvlarge]
  have hWpos : 0 < W := by rw [hW_def]; positivity
  have hF : 0 < F := by rw [hF_def]; positivity
  have hr01' : 0 ≤ r₁ - r₀ := by linarith
  have hVnn : 0 ≤ V := by rw [hV_def]; positivity
  -- window helpers
  have hwin_lo : ∀ z : ℝ, r₀ ≤ z → (1/72) * S.R ≤ z := fun z hz => le_trans hr0_lo hz
  have hwin_hi : ∀ z : ℝ, z ≤ r₁ → z + ℓ₁ ≤ 16 * S.R := fun z hz => by
    have : z + ℓ₁ ≤ r₁ + ℓ₁ := by linarith
    linarith [hr1_hi]
  have hwin_pos : ∀ z : ℝ, r₀ ≤ z → 0 < z := fun z hz => by
    have := hwin_lo z hz; nlinarith [hRpos]
  have hwin_posl : ∀ z : ℝ, r₀ ≤ z → 0 < z + ℓ₁ := fun z hz => by
    have := hwin_pos z hz; linarith
  -- expanding bound for `x < y`
  have key : ∀ x : ℝ, x ∈ Set.Icc r₀ r₁ → ∀ y : ℝ, y ∈ Set.Icc r₀ r₁ → x < y →
      F * |x - y| ≤ |φ x - φ y| := by
    intro x hx y hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have hcont : ContinuousOn φ (Set.Icc x y) := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := hz
      have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx)
      have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx)
      exact (phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := z)
        ha0 hz0 hzl hℓne).continuousAt.continuousWithinAt
    have hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt φ (deriv φ z) z := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := hz
      have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx.le)
      have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx.le)
      exact (phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := z)
        ha0 hz0 hzl hℓne).differentiableAt.hasDerivAt
    obtain ⟨ξ, hξ, hslope⟩ :=
      exists_hasDerivAt_eq_slope φ (fun z => deriv φ z) hxy hcont hderiv
    obtain ⟨hξx, hξy⟩ := hξ
    have hξ_lo : (1/72) * S.R ≤ ξ := hwin_lo ξ (le_trans hx0 hξx.le)
    have hξ_hi : ξ + ℓ₁ ≤ 16 * S.R := hwin_hi ξ (le_trans hξy.le hy1)
    have hdlb : F ≤ |deriv φ ξ| :=
      phiv_deriv_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := ξ)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hξ_lo hξ_hi hvlarge
    have hyx : 0 < y - x := by linarith
    have hval : φ y - φ x = deriv φ ξ * (y - x) := by rw [hslope]; field_simp
    have hxyabs : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_pos hyx
    have hφabs : |φ x - φ y| = |deriv φ ξ| * (y - x) := by
      rw [abs_sub_comm, hval, abs_mul, abs_of_pos hyx]
    rw [hxyabs, hφabs]
    apply mul_le_mul_of_nonneg_right hdlb hyx.le
  have hexp : ∀ x ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc r₀ r₁, F * |x - y| ≤ |φ x - φ y| := by
    intro x hx y hy
    rcases lt_trichotomy x y with h | h | h
    · exact key x hx y hy h
    · subst h; simp
    · have := key y hy x hx h
      rwa [abs_sub_comm y x, abs_sub_comm (φ y) (φ x)] at this
  -- variation bound via the derivative UB:  |φx − φy| ≤ V (= 10¹³·W·(r₁−r₀))
  have hvar : ∀ x ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc r₀ r₁, |φ x - φ y| ≤ V := by
    intro x hx y hy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    rcases lt_trichotomy x y with h | h | h
    · -- x < y : MVT gives |φx−φy| = |φ'(ξ)|·(y−x) ≤ 10¹³·W·(y−x) ≤ V
      have hcont : ContinuousOn φ (Set.Icc x y) := by
        intro z hz
        obtain ⟨hzx, hzy⟩ := hz
        have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx)
        have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx)
        exact (phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := z)
          ha0 hz0 hzl hℓne).continuousAt.continuousWithinAt
      have hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt φ (deriv φ z) z := by
        intro z hz
        obtain ⟨hzx, hzy⟩ := hz
        have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx.le)
        have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx.le)
        exact (phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := z)
          ha0 hz0 hzl hℓne).differentiableAt.hasDerivAt
      obtain ⟨ξ, hξ, hslope⟩ :=
        exists_hasDerivAt_eq_slope φ (fun z => deriv φ z) h hcont hderiv
      obtain ⟨hξx, hξy⟩ := hξ
      have hξ_lo : (1/72) * S.R ≤ ξ := hwin_lo ξ (le_trans hx0 hξx.le)
      have hξ_hi : ξ + ℓ₁ ≤ 16 * S.R := hwin_hi ξ (le_trans hξy.le hy1)
      have hdub : |deriv φ ξ| ≤ 10 ^ 13 * W :=
        phiv_deriv_ub_scale (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := ξ)
          hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hξ_lo hξ_hi hvlarge
      have hyx : 0 < y - x := by linarith
      have hval : φ y - φ x = deriv φ ξ * (y - x) := by rw [hslope]; field_simp
      have hφabs : |φ x - φ y| = |deriv φ ξ| * (y - x) := by
        rw [abs_sub_comm, hval, abs_mul, abs_of_pos hyx]
      rw [hφabs, hV_def]
      have hyx_le : y - x ≤ r₁ - r₀ := by linarith
      calc |deriv φ ξ| * (y - x)
          ≤ (10 ^ 13 * W) * (y - x) := mul_le_mul_of_nonneg_right hdub hyx.le
        _ ≤ (10 ^ 13 * W) * (r₁ - r₀) := by
            apply mul_le_mul_of_nonneg_left hyx_le (by positivity)
        _ = 10 ^ 13 * W * (r₁ - r₀) := by ring
    · subst h; simp [hVnn]
    · -- y < x : symmetric
      have hcont : ContinuousOn φ (Set.Icc y x) := by
        intro z hz
        obtain ⟨hzx, hzy⟩ := hz
        have hz0 : 0 < z := hwin_pos z (le_trans hy0 hzx)
        have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hy0 hzx)
        exact (phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := z)
          ha0 hz0 hzl hℓne).continuousAt.continuousWithinAt
      have hderiv : ∀ z ∈ Set.Ioo y x, HasDerivAt φ (deriv φ z) z := by
        intro z hz
        obtain ⟨hzx, hzy⟩ := hz
        have hz0 : 0 < z := hwin_pos z (le_trans hy0 hzx.le)
        have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hy0 hzx.le)
        exact (phiv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := z)
          ha0 hz0 hzl hℓne).differentiableAt.hasDerivAt
      obtain ⟨ξ, hξ, hslope⟩ :=
        exists_hasDerivAt_eq_slope φ (fun z => deriv φ z) h hcont hderiv
      obtain ⟨hξx, hξy⟩ := hξ
      have hξ_lo : (1/72) * S.R ≤ ξ := hwin_lo ξ (le_trans hy0 hξx.le)
      have hξ_hi : ξ + ℓ₁ ≤ 16 * S.R := hwin_hi ξ (le_trans hξy.le hx1)
      have hdub : |deriv φ ξ| ≤ 10 ^ 13 * W :=
        phiv_deriv_ub_scale (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (v := v) (r := ξ)
          hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hξ_lo hξ_hi hvlarge
      have hyx : 0 < x - y := by linarith
      have hval : φ x - φ y = deriv φ ξ * (x - y) := by rw [hslope]; field_simp
      have hφabs : |φ x - φ y| = |deriv φ ξ| * (x - y) := by
        rw [hval, abs_mul, abs_of_pos hyx]
      rw [hφabs, hV_def]
      have hyx_le : x - y ≤ r₁ - r₀ := by linarith
      calc |deriv φ ξ| * (x - y)
          ≤ (10 ^ 13 * W) * (x - y) := mul_le_mul_of_nonneg_right hdub hyx.le
        _ ≤ (10 ^ 13 * W) * (r₁ - r₀) := by
            apply mul_le_mul_of_nonneg_left hyx_le (by positivity)
        _ = 10 ^ 13 * W * (r₁ - r₀) := by ring
  -- apply the preimage count lemma
  have := Counting.preimage_count r₀ r₁ V F δ φ hF hδ hVnn hexp hvar
  -- unfold V, F, W back to the stated form
  rw [hV_def, hW_def, hF_def] at this
  convert this using 2

end Squarefree
