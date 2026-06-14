import Squarefree.Lower.Step23Combine
import Squarefree.Lower.Step3VBound
import Squarefree.Lower.Step1Witness
import Squarefree.Lower.DefectClose

/-!
# §5 Steps 2/3 per-`r` bound from `RaWitness` data (writeup 877–903)

`phif_distInt_from_witness` is the v≠0 analogue of `phi_distInt_from_witness`: given the three
`D`-scale witnesses `d,d₁,d₂` (`RaWitness` shape) and an integer `f` within the `Q_distInt_le`
slack of `𝒬`, it produces `distInt(φ_f(r)) ≤ 4·δ₂₃`. It derives `phif_delta_le`'s hypotheses —
closeness (`dtilde_close`×3), the two discrete slopes (`bzero_le`×2), the Taylor windows
(`step1_window_bound`×2), and the defect bound (`v_defect_le`) — from the witness data.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 Steps 2/3 per-`r` bound from witnesses.** -/
theorem phif_distInt_from_witness {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ} {𝒬 : ℝ} {f : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (hr1_hi : r + (ℓ₁ : ℝ) ≤ 16 * S.R) (hr2_hi : r + (ℓ₂ : ℝ) ≤ 16 * S.R)
    (hin : inDa P.X P.H a d) (hin1 : inDa P.X P.H a d₁) (hin2 : inDa P.X P.H a d₂)
    (hdwin : S.D ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * S.D) (hd1win : S.D ≤ (d₁ : ℝ) ∧ (d₁ : ℝ) ≤ 2 * S.D)
    (hd2win : S.D ≤ (d₂ : ℝ) ∧ (d₂ : ℝ) ≤ 2 * S.D)
    (hRd  : |Rfun P.X (a : ℝ) (d : ℝ)  - r|             ≤ 14 * P.H / S.D)
    (hRd1 : |Rfun P.X (a : ℝ) (d₁ : ℝ) - (r + (ℓ₁ : ℝ))| ≤ 14 * P.H / S.D)
    (hRd2 : |Rfun P.X (a : ℝ) (d₂ : ℝ) - (r + (ℓ₂ : ℝ))| ≤ 14 * P.H / S.D)
    (hd1ned : (d₁ : ℝ) ≠ (d : ℝ)) (hd2ned : (d₂ : ℝ) ≠ (d : ℝ))
    (h𝒬 : 𝒬 = (ℓ₁ : ℝ) * Fab P.X (a : ℝ) ((d₂ : ℝ) - (d : ℝ)) (d : ℝ)
              - (ℓ₂ : ℝ) * Fab P.X (a : ℝ) ((d₁ : ℝ) - (d : ℝ)) (d : ℝ))
    (hf_near : |(f : ℝ) - 𝒬|
        ≤ (ℓ₁ : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₂ : ℝ) ^ 2)
          + (ℓ₂ : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₁ : ℝ) ^ 2))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) :
    Counting.distInt (phif P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) (f : ℝ) r)
      ≤ 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) := by
  -- ===== SETUP : casts and r-window helpers =====
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : (0 : ℝ) < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : (0 : ℝ) < (ℓ₂ : ℝ) := lt_trans hℓ1R hℓ12R
  have hℓ1_loR : (1 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1_lo
  have hℓ2_lo : (1 : ℤ) ≤ ℓ₂ := le_of_lt (lt_of_le_of_lt hℓ1_lo hℓ12)
  have hℓ1ne : (ℓ₁ : ℝ) ≠ 0 := ne_of_gt hℓ1R
  have hℓ2ne : (ℓ₂ : ℝ) ≠ 0 := ne_of_gt hℓ2R
  have hℓ1nn : (0 : ℝ) ≤ (ℓ₁ : ℝ) := le_of_lt hℓ1R
  have hℓ2nn : (0 : ℝ) ≤ (ℓ₂ : ℝ) := le_of_lt hℓ2R
  have hℓ1W : (ℓ₁ : ℝ) ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12R) hℓ2W
  have hr_hi16 : r ≤ 16 * S.R := le_trans (by linarith) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ r + (ℓ₁ : ℝ) := by linarith
  have hr2_lo : (1/72) * S.R ≤ r + (ℓ₂ : ℝ) := by linarith
  -- ===== STEP 1 : closeness ×3 via dtilde_close =====
  have hd_close : |(d : ℝ) - dtilde P.X r (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X (r + (ℓ₁ : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hd2_close : |(d₂ : ℝ) - dtilde P.X (r + (ℓ₂ : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2
  -- ===== STEP 2 : b₀ / b₀₂ bounds via bzero_le =====
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / (ℓ₁ : ℝ) with hb₀_def
  set v : ℝ := ((d₂ : ℝ) - (d : ℝ)) - (ℓ₂ : ℝ) * b₀ with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := r) (ℓ := (ℓ₁ : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
  have hb02 : |((d₂ : ℝ) - (d : ℝ)) / (ℓ₂ : ℝ)| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := r) (ℓ := (ℓ₂ : ℝ))
      (d := (d : ℝ)) (dℓ := (d₂ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ2R (by exact_mod_cast hℓ2_lo) hr_lo hr2_hi
      hd_close hd2_close hG1 hΔ1
  -- ===== STEP 3 : U * W ≤ R =====
  have hRUW : P.U * P.Wval ≤ S.R := U_mul_W_le_R (S := S) h1 hband hΩU hΔ1 hU1
  -- ===== STEP 4 : Taylor windows via step1_window_bound =====
  have hwin1 : 4 * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ≤ (d : ℝ) :=
    step1_window_bound (a := a) (ℓ₂ := ℓ₁) (b₀ := b₀) (dd := (d : ℝ))
      ha_hi hℓ1W hℓ1nn hb0 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin2' : 4 * ((a : ℝ) + (ℓ₂ : ℝ) * |((d₂ : ℝ) - (d : ℝ)) / (ℓ₂ : ℝ)|) ≤ (d : ℝ) :=
    step1_window_bound (a := a) (ℓ₂ := ℓ₂) (b₀ := ((d₂ : ℝ) - (d : ℝ)) / (ℓ₂ : ℝ))
      (dd := (d : ℝ)) ha_hi hℓ2W hℓ2nn hb02 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  -- ===== STEP 5 : definitional pinning =====
  have hb0def : (ℓ₁ : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ) := by
    rw [hb₀_def]; field_simp
  have hvdef : (ℓ₂ : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ) := by
    rw [hv_def]; ring
  -- massage hwin2' into the shape phif_delta_le wants
  have hwin2 : 4 * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ≤ (d : ℝ) := by
    have heq : |(ℓ₂ : ℝ) * b₀ + v| = (ℓ₂ : ℝ) * |((d₂ : ℝ) - (d : ℝ)) / (ℓ₂ : ℝ)| := by
      rw [hvdef, abs_div, abs_of_pos hℓ2R]
      field_simp
    rw [heq]; exact hwin2'
  -- ===== STEP 6 : v bound via v_defect_le =====
  have hvd := v_defect_le (P := P) (S := S) (a := a) (r := r) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (d := d) (d₁ := d₁) (d₂ := d₂)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ1_lo hℓ12 hℓ2W hr_lo hr2_hi
    hd_close hd1_close hd2_close h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hv_shape : v = ((d₂ : ℝ) - (d : ℝ)) - ((ℓ₂ : ℝ) / (ℓ₁ : ℝ)) * ((d₁ : ℝ) - (d : ℝ)) := by
    rw [hv_def, hb₀_def]; ring
  have hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    rw [hv_shape]
    refine le_trans hvd ?_
    have hnn : (0 : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by
      have := S.Δ_pos; have := P.U_pos; have := S.Ω_pos; positivity
    gcongr
    norm_num
  -- ===== STEP 7 : rewrite the given 𝒬 into phif_delta_le's shape =====
  have h𝒬' : 𝒬 = (ℓ₁ : ℝ) * Fab P.X (a : ℝ) ((ℓ₂ : ℝ) * b₀ + v) (d : ℝ)
              - (ℓ₂ : ℝ) * Fab P.X (a : ℝ) ((ℓ₁ : ℝ) * b₀) (d : ℝ) := by
    rw [h𝒬, hvdef, hb0def]
  -- ===== STEP 8 : finish =====
  exact phif_delta_le hAD ha0 ha_lo ha_hi hℓ1 hℓ1_lo hℓ12 hℓ2W hr_lo hr_hi16 hr1_hi
    hdwin hd1win hd2win hd_close hd1_close hb0def hvdef hb0 hv hd1ned hd2ned hwin2 hwin1
    h𝒬' hf_near h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg

end Squarefree
