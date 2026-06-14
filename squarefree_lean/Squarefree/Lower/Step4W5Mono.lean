import Squarefree.Lower.Step4Weight5
import Squarefree.Lower.Step4DiamHybrid

/-! # §5 Step-4 monotonicity for `weight5` / hybrid budgets -/

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- `weight5` is monotone in the band slot `ev` (for `n ≥ 0`). -/
theorem weight5_mono_ev {b ev ev' dc cE cE₂ cC n : ℝ}
    (hb : 0 ≤ b) (hdc : 0 ≤ dc) (hn : 0 ≤ n) (h : ev ≤ ev') :
    weight5 b ev dc cE cE₂ cC n ≤ weight5 b ev' dc cE cE₂ cC n := by
  unfold weight5
  rcases eq_or_lt_of_le (Real.sqrt_nonneg n) with h0 | h0
  · rw [← h0]; simp
  · gcongr

/-- Scaling the band slot `ev` by `k ≥ 1` scales `weight5` by at most `k`. -/
theorem weight5_ev_scale {k b ev dc cE cE₂ cC n : ℝ}
    (hk : 1 ≤ k) (hb : 0 ≤ b) (hdc : 0 ≤ dc) (hev : 0 ≤ ev)
    (hcE : 0 ≤ cE) (hcE₂ : 0 ≤ cE₂) (hcC : 0 ≤ cC) (hn : 0 ≤ n) :
    weight5 b (k * ev) dc cE cE₂ cC n ≤ k * weight5 b ev dc cE cE₂ cC n := by
  unfold weight5
  have hs : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hfac : (0:ℝ) ≤ b + dc / Real.sqrt n := by positivity
  have hfirst : 2 + k * ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC
      ≤ k * (2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC) := by
    rw [mul_div_assoc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg hcE hs),
      mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg hcE₂ hn),
      mul_nonneg (sub_nonneg.mpr hk) hcC]
  calc (2 + k * ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC)
        * (b + dc / Real.sqrt n)
      ≤ (k * (2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC))
        * (b + dc / Real.sqrt n) := mul_le_mul_of_nonneg_right hfirst hfac
    _ = k * ((2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC)
        * (b + dc / Real.sqrt n)) := by ring

/-- `Step4EcubV` is monotone in the fibre-local box `V` (on `0 ≤ V`). -/
theorem Step4EcubV_mono {ℓ₁ ℓ₂ V V' : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hV0 : 0 ≤ V) (hVV' : V ≤ V') :
    Step4EcubV P S ℓ₁ ℓ₂ V ≤ Step4EcubV P S ℓ₁ ℓ₂ V' := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hpref : (0:ℝ) ≤ 2 * (77 * (P.G * S.Ω / S.Δ ^ 4)) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) h2ℓ)
  unfold Step4EcubV
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV0 hVV' 3) hpref

/-- `Step4EremHyb` is monotone in the fibre-local box `V` (on `0 ≤ V`): the first term
is quadratic in `V`, the flat-drift term is `V`-free, the `p₂` term is `E0_p2_hyb_mono`. -/
theorem Step4EremHyb_mono {a ℓ₁ ℓ₂ gap V V' : ℝ}
    (ha0 : 0 < a) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hgap0 : 0 ≤ gap) (hV0 : 0 ≤ V) (hVV' : V ≤ V') :
    Step4EremHyb P S a ℓ₁ ℓ₂ gap V ≤ Step4EremHyb P S a ℓ₁ ℓ₂ gap V' := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hmid : (0:ℝ) ≤ 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h21
  have hpref1 : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap :=
    mul_nonneg (mul_nonneg (by positivity) hmid) hgap0
  have hsq : (ℓ₁ * V) ^ 2 ≤ (ℓ₁ * V') ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hℓ1pos.le hV0)
      (mul_le_mul_of_nonneg_left hVV' hℓ1pos.le) 2
  have ht1 := mul_le_mul_of_nonneg_left hsq hpref1
  have ht3 := E0_p2_hyb_mono (P := P) (S := S) hℓ1 hℓ12 hV0 hVV'
  unfold Step4EremHyb
  linarith

end Squarefree
