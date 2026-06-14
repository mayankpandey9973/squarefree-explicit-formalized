import Squarefree.Lower.Step1Phase
import Squarefree.Counting.Preimage

/-!
# §5 Step-1 smooth phase preimage count (writeup 852–855)

Apply the preimage-count lemma (Lemma 4.1) to the §5 Step-1 smooth phase `φ`, using that `φ`
is `F`-expanding (`|φ'| ≥ F`, from `phi_deriv_lb`) and bounded (`0 ≤ φ ≤ V`, from `phi_abs_ub`)
on the window `[r₀, r₁]`.  This is the analytic half of Step 1.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

theorem step1_smooth_count {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : 0 ≤ δ) :
    (((Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
        (fun (n : ℤ) => Counting.distInt (phi P.X a ℓ₁ ℓ₂ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) + 2 * δ + 1)
        * (2 * δ / (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)) + 1) := by
  -- abbreviations matching `preimage_count`
  set φ : ℝ → ℝ := fun s => phi P.X a ℓ₁ ℓ₂ s with hφ_def
  set V : ℝ := 10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) with hV_def
  set F : ℝ := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30) with hF_def
  -- positivity facts
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hLpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  -- `F > 0`
  have hF : 0 < F := by rw [hF_def]; positivity
  -- `V ≥ 0`
  have hV : 0 ≤ V := by rw [hV_def]; positivity
  -- window helper: a point `z ∈ [r₀, r₁]` satisfies the §5 window hypotheses.
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
      exact (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := z)
        ha0 hz0 hzl hℓne).continuousAt.continuousWithinAt
    -- differentiability on `(x, y)`
    have hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt φ (deriv φ z) z := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := hz
      have hz0 : 0 < z := hwin_pos z (le_trans hx0 hzx.le)
      have hzl : 0 < z + ℓ₁ := hwin_posl z (le_trans hx0 hzx.le)
      exact (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := z)
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
      phi_deriv_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := ξ)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hξ_lo hξ_hi hsmall
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
  have hvar : ∀ x ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc r₀ r₁, |φ x - φ y| ≤ V := by
    intro x hx y hy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    obtain ⟨hxlo, hxhi⟩ :=
      phi_abs_ub (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := x)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 (hwin_lo x hx0) (hwin_hi x hx1)
    obtain ⟨hylo, hyhi⟩ :=
      phi_abs_ub (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := y)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 (hwin_lo y hy0) (hwin_hi y hy1)
    rw [abs_le]
    constructor
    · simp only [hφ_def] at hxlo hxhi hylo hyhi ⊢; linarith
    · simp only [hφ_def] at hxlo hxhi hylo hyhi ⊢; linarith
  -- apply the preimage count lemma
  exact Counting.preimage_count r₀ r₁ V F δ φ hF hδ hV hexp hvar

end Squarefree
