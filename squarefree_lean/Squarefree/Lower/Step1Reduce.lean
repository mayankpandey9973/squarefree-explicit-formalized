import Squarefree.Lower.DefectExpand
import Squarefree.Lower.DefectReplace
import Squarefree.Lower.QNearInt
import Squarefree.Lower.Step1Phase

/-!
# §5 Step-1 per-`r` reduction (writeup 819–840)

Pure chaining of three foundation lemmas:

* `phi_d_replace` — `|φ_d − φ| ≤ 10⁴⁰·δ` (smooth-phase replacement),
* `Q_v0_expand`   — `|𝒬 + φ_d| ≤ E` (defect Taylor expansion at `v = 0`),
* `ffun_diff_near_int` (+ `distInt` arithmetic) — `distInt 𝒬 ≤ (1st summand)`,

combined through the `distInt` triangle inequality `distInt φ ≤ distInt 𝒬 + |𝒬+φ_d| + |φ−φ_d|`.
-/

namespace Squarefree

open Squarefree.Counting

/-- `distInt (x + s) ≤ distInt x + |s|`: small triangle helper. -/
private theorem distInt_add_le_add_abs (x s : ℝ) :
    distInt (x + s) ≤ distInt x + |s| := by
  refine le_trans (distInt_le_intDist (x + s) (round x)) ?_
  have e : (x + s) - (round x : ℝ) = (x - round x) + s := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) ?_
  simp only [distInt, le_refl]

/-- `distInt (-x) = distInt x`. -/
private theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  refine le_antisymm ?_ ?_
  · refine le_trans (distInt_le_intDist (-x) (-round x)) ?_
    have e : (-x) - ((-round x : ℤ) : ℝ) = -(x - round x) := by push_cast; ring
    rw [e, abs_neg]; simp only [distInt, le_refl]
  · refine le_trans (distInt_le_intDist x (-round (-x))) ?_
    have e : x - ((-round (-x) : ℤ) : ℝ) = -((-x) - round (-x)) := by push_cast; ring
    rw [e, abs_neg]; simp only [distInt, le_refl]

/-- **§5 Step-1 per-`r` reduction** (writeup 819–840). -/
theorem phi_norm_le_v0 {P : Globals} {S : Scale P} {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hr_lo : (1/72) * S.R ≤ r) (hr1_hi : r + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hin : inDa P.X P.H a d) (hin1 : inDa P.X P.H a d₁) (hin2 : inDa P.X P.H a d₂)
    (hdpos : 0 < (d:ℝ)) (hd1pos : 0 < (d₁:ℝ)) (hd2pos : 0 < (d₂:ℝ))
    (hdwin : S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2*S.D) (hd1win : S.D ≤ (d₁:ℝ) ∧ (d₁:ℝ) ≤ 2*S.D)
    -- v = 0 :  ℓ₁(d₂−d) = ℓ₂(d₁−d)
    (hv0 : (ℓ₁:ℝ) * ((d₂:ℝ) - (d:ℝ)) = (ℓ₂:ℝ) * ((d₁:ℝ) - (d:ℝ)))
    -- discrete slope b₀ nonzero + window
    (hb0ne : (d₁:ℝ) ≠ (d:ℝ))
    (hwin : 4 * ((a:ℝ) + (ℓ₂:ℝ) * |((d₁:ℝ) - (d:ℝ))/(ℓ₁:ℝ)|) ≤ (d:ℝ))
    -- phi_d_replace closeness + regime
    (hd_close  : |(d:ℝ)  - dtilde P.X r (a:ℝ)|             ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hd1_close : |(d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) :
    Counting.distInt (phi P.X (a:ℝ) ℓ₁ ℓ₂ r)
      ≤ ((ℓ₁:ℝ) * (2*P.H/(d:ℝ)^2 + 2*P.H/(d₂:ℝ)^2) + (ℓ₂:ℝ) * (2*P.H/(d:ℝ)^2 + 2*P.H/(d₁:ℝ)^2))
        + 400 * P.X * (a:ℝ) * |((d₁:ℝ)-(d:ℝ))/(ℓ₁:ℝ)| * (ℓ₁:ℝ) * (ℓ₂:ℝ)
            * (((a:ℝ) + (ℓ₂:ℝ)*|((d₁:ℝ)-(d:ℝ))/(ℓ₁:ℝ)|)^2 + ((a:ℝ) + (ℓ₁:ℝ)*|((d₁:ℝ)-(d:ℝ))/(ℓ₁:ℝ)|)^2) / (d:ℝ)^6
        + (10:ℝ)^45 * ((1/S.Δ) * P.G^3 * P.U^10 / S.Ω^5) := by
  -- abbreviations
  set b₀ := ((d₁:ℝ) - (d:ℝ))/(ℓ₁:ℝ) with hb₀_def
  set φ := phi P.X (a:ℝ) ℓ₁ ℓ₂ r with hφ_def
  set φ_d := 12*(ℓ₁:ℝ)*(ℓ₂:ℝ)*((ℓ₂:ℝ)-(ℓ₁:ℝ))*P.X*(a:ℝ)*b₀^2/(d:ℝ)^5 with hφd_def
  set 𝒬 := (ℓ₁:ℝ)*Fab P.X (a:ℝ) ((ℓ₂:ℝ)*b₀) (d:ℝ)
             - (ℓ₂:ℝ)*Fab P.X (a:ℝ) ((ℓ₁:ℝ)*b₀) (d:ℝ) with h𝒬_def
  -- positivity / cast facts
  have hℓ1R : (0:ℝ) < (ℓ₁:ℝ) := by exact_mod_cast hℓ1
  have hℓ1ne : (ℓ₁:ℝ) ≠ 0 := ne_of_gt hℓ1R
  have hℓ12R : (ℓ₁:ℝ) < (ℓ₂:ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : (0:ℝ) < (ℓ₂:ℝ) := lt_trans hℓ1R hℓ12R
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha0
  have hb₀ne : b₀ ≠ 0 := by
    rw [hb₀_def]; exact div_ne_zero (sub_ne_zero.mpr hb0ne) hℓ1ne
  -- ===== A. |φ − φ_d| ≤ 10⁴⁰·δ via phi_d_replace =====
  have hA : |φ - φ_d| ≤ (10:ℝ)^45 * ((1/S.Δ) * P.G^3 * P.U^10 / S.Ω^5) := by
    have hrepl := phi_d_replace (P := P) (S := S) (a := a) (r := r)
      (ℓ₁ := (ℓ₁:ℝ)) (ℓ₂ := (ℓ₂:ℝ)) (d := (d:ℝ)) (d₁ := (d₁:ℝ))
      hAD ha0 ha_lo ha_hi hℓ1R (by exact_mod_cast hℓ1_lo) hℓ12R hℓ2W
      hr_lo hr1_hi hdwin hd1win hd_close hd1_close h1 hband hG1 hU1 hΔ1 hUH
    -- hrepl : |φ_d − φ| ≤ …  (with `((d₁-d)/ℓ₁)^2 = b₀^2`)
    have heq : |φ - φ_d|
        = |12*(ℓ₁:ℝ)*(ℓ₂:ℝ)*((ℓ₂:ℝ)-(ℓ₁:ℝ))*P.X*(a:ℝ)*(((d₁:ℝ)-(d:ℝ))/(ℓ₁:ℝ))^2/(d:ℝ)^5 - φ| := by
      rw [abs_sub_comm, hφd_def, hb₀_def]
    rw [heq]; exact hrepl
  -- ===== B. |𝒬 + φ_d| ≤ E_bound via Q_v0_expand =====
  have hB : |𝒬 + φ_d|
      ≤ 400 * P.X * (a:ℝ) * |b₀| * (ℓ₁:ℝ) * (ℓ₂:ℝ)
          * (((a:ℝ) + (ℓ₂:ℝ)*|b₀|)^2 + ((a:ℝ) + (ℓ₁:ℝ)*|b₀|)^2) / (d:ℝ)^6 := by
    have hexp := Q_v0_expand (X := P.X) (a := (a:ℝ)) (b₀ := b₀) (d := (d:ℝ))
      (ℓ₁ := (ℓ₁:ℝ)) (ℓ₂ := (ℓ₂:ℝ)) P.X_pos haR hb₀ne hdpos hℓ1R hℓ12R hwin
    -- hexp LHS = |𝒬 − (−φ_d)| = |𝒬 + φ_d|
    have hrw : 𝒬 + φ_d
        = ((ℓ₁:ℝ) * Fab P.X (a:ℝ) ((ℓ₂:ℝ) * b₀) (d:ℝ)
            - (ℓ₂:ℝ) * Fab P.X (a:ℝ) ((ℓ₁:ℝ) * b₀) (d:ℝ))
          - (-12 * (ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) * P.X * (a:ℝ) * b₀ ^ 2 / (d:ℝ) ^ 5) := by
      rw [h𝒬_def, hφd_def]; ring
    rw [hrw]; exact hexp
  -- ===== C. distInt 𝒬 ≤ (1st summand) via Ffun-near-integer =====
  -- v=0 rewrites:  d + ℓ₁·b₀ = d₁,  d + ℓ₂·b₀ = d₂
  have hℓ1b₀ : (ℓ₁:ℝ) * b₀ = (d₁:ℝ) - (d:ℝ) := by
    rw [hb₀_def]; field_simp
  have hℓ2b₀ : (ℓ₂:ℝ) * b₀ = (d₂:ℝ) - (d:ℝ) := by
    rw [hb₀_def]
    have : (ℓ₂:ℝ) * (((d₁:ℝ) - (d:ℝ))/(ℓ₁:ℝ)) = ((ℓ₂:ℝ) * ((d₁:ℝ) - (d:ℝ)))/(ℓ₁:ℝ) := by ring
    rw [this, ← hv0]; field_simp
  have hde1 : (d:ℝ) + (ℓ₁:ℝ) * b₀ = (d₁:ℝ) := by rw [hℓ1b₀]; ring
  have hde2 : (d:ℝ) + (ℓ₂:ℝ) * b₀ = (d₂:ℝ) := by rw [hℓ2b₀]; ring
  -- Fab → Ffun-difference form
  have hFab1 : Fab P.X (a:ℝ) ((ℓ₁:ℝ) * b₀) (d:ℝ)
      = Ffun P.X (a:ℝ) (d:ℝ) - Ffun P.X (a:ℝ) (d₁:ℝ) := by
    rw [Fab, hde1]
  have hFab2 : Fab P.X (a:ℝ) ((ℓ₂:ℝ) * b₀) (d:ℝ)
      = Ffun P.X (a:ℝ) (d:ℝ) - Ffun P.X (a:ℝ) (d₂:ℝ) := by
    rw [Fab, hde2]
  have h𝒬Ffun : 𝒬
      = (((ℓ₁:ℤ):ℝ)) * (Ffun P.X (a:ℝ) (d:ℝ) - Ffun P.X (a:ℝ) (d₂:ℝ))
        - (((ℓ₂:ℤ):ℝ)) * (Ffun P.X (a:ℝ) (d:ℝ) - Ffun P.X (a:ℝ) (d₁:ℝ)) := by
    rw [h𝒬_def, hFab1, hFab2]
  have hC : distInt 𝒬
      ≤ (ℓ₁:ℝ) * (2*P.H/(d:ℝ)^2 + 2*P.H/(d₂:ℝ)^2)
        + (ℓ₂:ℝ) * (2*P.H/(d:ℝ)^2 + 2*P.H/(d₁:ℝ)^2) := by
    rw [h𝒬Ffun]
    refine le_trans (distInt_sub_le _ _) ?_
    refine add_le_add ?_ ?_
    · refine le_trans (distInt_intMul_le ℓ₁ _) ?_
      have habs : |(((ℓ₁:ℤ):ℝ))| = (ℓ₁:ℝ) := by
        rw [abs_of_pos]; exact hℓ1R
      rw [habs]
      exact mul_le_mul_of_nonneg_left
        (ffun_diff_near_int P.X_pos hdpos hd2pos ha0 hin hin2) (le_of_lt hℓ1R)
    · refine le_trans (distInt_intMul_le ℓ₂ _) ?_
      have habs : |(((ℓ₂:ℤ):ℝ))| = (ℓ₂:ℝ) := by
        rw [abs_of_pos]; exact hℓ2R
      rw [habs]
      exact mul_le_mul_of_nonneg_left
        (ffun_diff_near_int P.X_pos hdpos hd1pos ha0 hin hin1) (le_of_lt hℓ2R)
  -- ===== triangle: distInt φ ≤ distInt 𝒬 + |𝒬+φ_d| + |φ−φ_d| =====
  have hstep1 : distInt (((-𝒬) + (𝒬 + φ_d)) + (φ - φ_d))
      ≤ distInt ((-𝒬) + (𝒬 + φ_d)) + |φ - φ_d| := distInt_add_le_add_abs _ _
  have hstep2 : distInt ((-𝒬) + (𝒬 + φ_d)) ≤ distInt (-𝒬) + |𝒬 + φ_d| :=
    distInt_add_le_add_abs _ _
  have hdiEq : distInt φ = distInt ((-𝒬) + (𝒬 + φ_d) + (φ - φ_d)) := by
    congr 1; ring
  have htri : distInt φ ≤ distInt 𝒬 + |𝒬 + φ_d| + |φ - φ_d| := by
    rw [hdiEq, ← distInt_neg 𝒬]
    linarith [hstep1, hstep2]
  -- ===== combine =====
  calc distInt φ ≤ distInt 𝒬 + |𝒬 + φ_d| + |φ - φ_d| := htri
    _ ≤ _ := by
        have habs_b₀ : |b₀| = |((d₁:ℝ)-(d:ℝ))/(ℓ₁:ℝ)| := by rw [hb₀_def]
        rw [habs_b₀] at hB
        linarith [hA, hB, hC]

end Squarefree
