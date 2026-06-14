import Squarefree.Lower.Step4Deriv

/-!
# §5 Step-4 MVT interval confinement (writeup 1055–1059)

For a fixed nonzero integer `s` and admissible `v`, the relevant `r`-values — those with
`Σ_closed(d̃ₐ(r)) ≈ s` — lie in an interval `I_s(v)` of length

  `|I_s(v)| ≤ 2·tol·10⁶·R`,  `tol` = the near-integer tolerance, `R = HGΩ³/Δ`  (writeup 1057).

This is the mean-value-theorem consequence of the derivative lower bound
`|Σ_s'(ρ)| ≥ |Lval| / (10⁶·R) ≥ 1/(10⁶·R)` (`Sigma_closed_deriv_lb`, since `|Lval| ≥ 1`).

The keystone is the **two-point confinement** `step4_confine_two`: any two admissible `r₁ ≤ r₂`
(both in the `r`-window with `d̃ₐ ∈ [D,2D]` and `Σ_closed` within `tol` of the *same* `s`) satisfy
`r₂ − r₁ ≤ 2·tol·10⁶·R`.  At the MVT midpoint `ξ ∈ (r₁,r₂)` the dyadic window `d̃ₐ(ξ) ∈ [D,2D]`
holds by strict antitonicity of `d̃ₐ` (`Sigma_closed_deriv_lb` needs it), so the derivative lower
bound applies and `|Σ(r₁)−Σ(r₂)| = |Σ'(ξ)|·(r₂−r₁) ≥ (r₂−r₁)/(10⁶R)`, while
`|Σ(r₁)−Σ(r₂)| ≤ 2·tol`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

variable {P : Globals} {S : Scale P}

/-- `d̃ₐ` is strictly antitone on `(0, ∞)` (its `r`-derivative is `< 0`). -/
theorem dtilde_strictAntiOn {a : ℝ} (ha0 : 0 < a) :
    StrictAntiOn (fun s => dtilde P.X s a) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · -- continuity on `(0,∞)`
    intro z hz
    have hz0 : 0 < z := hz
    exact (dtilde_r_hasDerivAt P.X_pos ha0 hz0).continuousAt.continuousWithinAt
  · -- derivative negative on the interior
    intro z hz
    rw [interior_Ioi] at hz
    have hz0 : 0 < z := hz
    rw [(dtilde_r_hasDerivAt P.X_pos ha0 hz0).deriv]
    have hd : 0 < dtilde P.X z a := dtilde_pos P.X_pos ha0 hz0
    apply div_neg_of_neg_of_pos
    · nlinarith [hd, ha0]
    · positivity

/-- **§5 Step-4 two-point MVT confinement** (writeup 1055–1057).  Two admissible `r₁ ≤ r₂` with
`d̃ₐ(rᵢ) ∈ [D,2D]` and `Σ_closed(d̃ₐ(rᵢ))` within `tol` of the same `s` satisfy
`r₂ − r₁ ≤ 2·tol·10⁶·R`. -/
theorem step4_confine_two {a : ℝ} {ℓ₁ ℓ₂ b₀ v s tol r₁ r₂ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 55 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v|)
    (hVcut : V₂ P S ≤ |v|)
    -- the two admissible points
    (hr1_lo : (1/72) * S.R ≤ r₁) (hr12 : r₁ ≤ r₂) (hr2_hi : r₂ ≤ 16 * S.R)
    (hdwin1 : S.D ≤ dtilde P.X r₁ a ∧ dtilde P.X r₁ a ≤ 2 * S.D)
    (hdwin2 : S.D ≤ dtilde P.X r₂ a ∧ dtilde P.X r₂ a ≤ 2 * S.D)
    (hs1 : |Sigma_closed P.X a b₀ v (dtilde P.X r₁ a) ℓ₁ ℓ₂ - s| ≤ tol)
    (hs2 : |Sigma_closed P.X a b₀ v (dtilde P.X r₂ a) ℓ₁ ℓ₂ - s| ≤ tol) :
    r₂ - r₁ ≤ 2 * tol * (10 ^ 6 * S.R) := by
  -- scale positivity
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hr0 : 0 < r₁ := lt_of_lt_of_le (by positivity) hr1_lo
  -- `tol ≥ 0` (it dominates an absolute value)
  have htol_nn : 0 ≤ tol := le_trans (abs_nonneg _) hs1
  -- abbreviate the curve `Σ ∘ d̃`
  set Φ : ℝ → ℝ := fun s => Sigma_closed P.X a b₀ v (dtilde P.X s a) ℓ₁ ℓ₂ with hΦ_def
  -- the easy case `r₁ = r₂`
  rcases eq_or_lt_of_le hr12 with heq | hlt
  · rw [heq]; simp; positivity
  -- the strict case `r₁ < r₂` : apply the MVT
  -- differentiability / continuity of `Φ` on `[r₁, r₂]`
  have hcont : ContinuousOn Φ (Set.Icc r₁ r₂) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hr0 hz.1
    exact (Sigma_closed_hasDerivAt (P := P) (a := a) (b₀ := b₀) (v := v)
      (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := z) ha0 hz0).continuousAt.continuousWithinAt
  have hderiv : ∀ z ∈ Set.Ioo r₁ r₂, HasDerivAt Φ (deriv Φ z) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hr0 hz.1.le
    exact (Sigma_closed_hasDerivAt (P := P) (a := a) (b₀ := b₀) (v := v)
      (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := z) ha0 hz0).differentiableAt.hasDerivAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope Φ (fun z => deriv Φ z) hlt hcont hderiv
  obtain ⟨hξ1, hξ2⟩ := hξ
  -- window for `ξ`
  have hξ0 : 0 < ξ := lt_trans hr0 hξ1
  have hξ_lo : (1/72) * S.R ≤ ξ := le_trans hr1_lo hξ1.le
  have hξ_hi : ξ ≤ 16 * S.R := le_trans hξ2.le hr2_hi
  -- `d̃ₐ(ξ) ∈ [D, 2D]` by strict antitonicity:  d̃(r₂) ≤ d̃(ξ) ≤ d̃(r₁), both endpoints in [D,2D]
  have hanti := dtilde_strictAntiOn (P := P) (a := a) ha0
  have hξ_in : ξ ∈ Set.Ioi (0:ℝ) := hξ0
  have hr1_in : r₁ ∈ Set.Ioi (0:ℝ) := hr0
  have hr2_in : r₂ ∈ Set.Ioi (0:ℝ) := lt_trans hr0 hlt
  have hd_ξ_lo : dtilde P.X r₂ a ≤ dtilde P.X ξ a := (hanti hξ_in hr2_in hξ2).le
  have hd_ξ_hi : dtilde P.X ξ a ≤ dtilde P.X r₁ a := (hanti hr1_in hξ_in hξ1).le
  have hdwinξ : S.D ≤ dtilde P.X ξ a ∧ dtilde P.X ξ a ≤ 2 * S.D :=
    ⟨le_trans hdwin2.1 hd_ξ_lo, le_trans hd_ξ_hi hdwin1.2⟩
  -- the derivative lower bound at `ξ`:  1/(10⁶R) ≤ |Lval|/(10⁶R) ≤ |Φ'(ξ)|
  have hLval1 : (1:ℝ) ≤ |Lval P.X a (dtilde P.X ξ a) b₀ v ℓ₁ ℓ₂| := by
    have hge := leading_abs_ge (S := S) (a := a) (b₀ := b₀) (v := v) (d := dtilde P.X ξ a)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hdwinξ hb0 hv h1 hband hG1 hU1 hΔ1 hH1
      hΩU hUbig hΩH hDeW hv2
    have hUpsTnn : 0 ≤ 10 ^ 119 * UpsT P S := by
      have : 0 ≤ UpsT P S := by rw [UpsT]; positivity
      positivity
    have : (1:ℝ) ≤ 1 + 10 ^ 119 * UpsT P S := by linarith [hUpsTnn]
    have hge' : 1 + 10 ^ 119 * UpsT P S ≤ |Lval P.X a (dtilde P.X ξ a) b₀ v ℓ₁ ℓ₂| := by
      simpa only [UpsT] using hge
    linarith [this, hge']
  have hdlb := Sigma_closed_deriv_lb (P := P) (S := S) (a := a) (b₀ := b₀) (v := v)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := ξ) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W hξ_lo hξ_hi
    hdwinξ hb0 hb0lo hv h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΩH hDeW hVcut
  -- `1/(10⁶R) ≤ |Lval|/(10⁶R)` so `1/(10⁶R) ≤ |Φ'(ξ)|`
  have hF_lo : 1 / (10 ^ 6 * S.R) ≤ |deriv Φ ξ| := by
    have hstep : (1:ℝ) / (10 ^ 6 * S.R)
        ≤ |Lval P.X a (dtilde P.X ξ a) b₀ v ℓ₁ ℓ₂| / (10 ^ 6 * S.R) := by
      apply div_le_div_of_nonneg_right hLval1 (by positivity)
    exact le_trans hstep hdlb
  -- `|Φ(r₁) − Φ(r₂)| = |Φ'(ξ)|·(r₂ − r₁) ≥ (r₂−r₁)/(10⁶R)`
  have hyx : 0 < r₂ - r₁ := by linarith
  have hval : Φ r₂ - Φ r₁ = deriv Φ ξ * (r₂ - r₁) := by rw [hslope]; field_simp
  have hΦdiff_abs : |Φ r₁ - Φ r₂| = |deriv Φ ξ| * (r₂ - r₁) := by
    rw [abs_sub_comm, hval, abs_mul, abs_of_pos hyx]
  -- variation bound `|Φ(r₁) − Φ(r₂)| ≤ 2·tol` from the two near-`s` facts
  have hvar : |Φ r₁ - Φ r₂| ≤ 2 * tol := by
    have htri : |Φ r₁ - Φ r₂|
        ≤ |Sigma_closed P.X a b₀ v (dtilde P.X r₁ a) ℓ₁ ℓ₂ - s|
          + |Sigma_closed P.X a b₀ v (dtilde P.X r₂ a) ℓ₁ ℓ₂ - s| := by
      rw [hΦ_def]
      have := abs_sub (Sigma_closed P.X a b₀ v (dtilde P.X r₁ a) ℓ₁ ℓ₂ - s)
        (Sigma_closed P.X a b₀ v (dtilde P.X r₂ a) ℓ₁ ℓ₂ - s)
      simpa using this
    linarith [htri, hs1, hs2]
  -- combine:  (r₂−r₁)/(10⁶R) ≤ |Φ'(ξ)|·(r₂−r₁) = |Φ(r₁)−Φ(r₂)| ≤ 2·tol
  have hlower : (r₂ - r₁) / (10 ^ 6 * S.R) ≤ |Φ r₁ - Φ r₂| := by
    rw [hΦdiff_abs]
    calc (r₂ - r₁) / (10 ^ 6 * S.R) = (1 / (10 ^ 6 * S.R)) * (r₂ - r₁) := by ring
      _ ≤ |deriv Φ ξ| * (r₂ - r₁) := mul_le_mul_of_nonneg_right hF_lo hyx.le
  -- so (r₂−r₁)/(10⁶R) ≤ 2·tol, i.e. r₂−r₁ ≤ 2·tol·10⁶R
  have hfin : (r₂ - r₁) / (10 ^ 6 * S.R) ≤ 2 * tol := le_trans hlower hvar
  rw [div_le_iff₀ (by positivity)] at hfin
  linarith [hfin]

end Squarefree
