import Squarefree.Lower.Step4Delta
import Squarefree.Lower.Step3VBound
import Squarefree.Lower.Step1Witness
import Squarefree.Lower.DefectClose
import Squarefree.Lower.Step3Model
import Squarefree.Lower.QNearInt
import Squarefree.Lower.Prop51Partition

/-!
# §5 Step-4 per-`r` `φ_v` near-integer bound from `dStar` witnesses (writeup 1067–1083)

`phiv_distInt_from_witness` is the §5 Step-4 analogue of `phif_distInt_from_witness`
(`Step3Witness.lean`): given the two `D`-scale witnesses `d = dStar r`, `d₁ = dStar (r+ℓ₁)`
(plus `d₂ = dStar (r+ℓ₂)` for the `Q_distInt_le` rounding cap) it threads the witness bundle
into `phiv_delta_le` (`Step4Delta.lean`), producing

```
distInt (phiv P.X a ℓ₁ ℓ₂ (vval P a dStar ℓ₁ ℓ₂ r) r) ≤ 10⁷⁰·(1/Δ)G⁴U¹⁵/Ω⁵.
```

It derives `phiv_delta_le`'s hypotheses — closeness (`dtilde_close`×2), the discrete slope
(`bzero_le`), the Taylor windows (`step1_window_bound`×2), and the defect bound (`v_defect_le`) —
from the witness data, EXACTLY as `phif_distInt_from_witness` does for the Step-3 phase, and
discharges `phiv_delta_le`'s `hf` disjunction via its second branch with `f := round (Qval r)`
through `Q_distInt_le` (the `Ffun`-difference near-integer keystone).
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **§5 Step-4 per-`r` `φ_v` near-integer bound from witnesses.** -/
theorem phiv_distInt_from_witness {a : ℤ} {ℓ₁ ℓ₂ r : ℕ} {dStar : ℕ → ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hr1_hi : (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
    (hr2_hi : (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
    (hinDa  : inDa P.X P.H a (dStar r))
    (hinDa1 : inDa P.X P.H a (dStar (r + ℓ₁)))
    (hinDa2 : inDa P.X P.H a (dStar (r + ℓ₂)))
    (hdwin : S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D)
    (hd1win : S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D)
    (hd2win : S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D)
    (hRd  : |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hRd1 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))|
        ≤ 14 * P.H / S.D)
    (hRd2 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))|
        ≤ 14 * P.H / S.D)
    (hd1ned : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ))
    (hℓ2bv_ne : (((ℓ₂ : ℤ) : ℝ)) * (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
        + vval P a dStar ℓ₁ ℓ₂ r ≠ 0)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) :
    distInt (phiv P.X (a : ℝ) ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) (vval P a dStar ℓ₁ ℓ₂ r) (r : ℝ))
      ≤ (10:ℝ) ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) := by
  -- ===== SETUP : casts and r-window helpers =====
  set d : ℤ := dStar r with hd_def
  set d₁ : ℤ := dStar (r + ℓ₁) with hd1_def
  set d₂ : ℤ := dStar (r + ℓ₂) with hd2_def
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1Z : (0 : ℤ) < (ℓ₁ : ℤ) := by exact_mod_cast hℓ1
  have hℓ12Z : (ℓ₁ : ℤ) < (ℓ₂ : ℤ) := by exact_mod_cast hℓ12
  have hℓ1_loZ : (1 : ℤ) ≤ (ℓ₁ : ℤ) := by exact_mod_cast hℓ1_lo
  have hℓ1R : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12Z
  have hℓ2R : (0 : ℝ) < ((ℓ₂ : ℤ) : ℝ) := lt_trans hℓ1R hℓ12R
  have hℓ1_loR : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1_loZ
  have hℓ2_lo : (1 : ℤ) ≤ (ℓ₂ : ℤ) := le_of_lt (lt_of_le_of_lt hℓ1_loZ hℓ12Z)
  have hℓ1nn : (0 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := le_of_lt hℓ1R
  have hℓ2nn : (0 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_of_lt hℓ2R
  have hℓ1W : ((ℓ₁ : ℤ) : ℝ) ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12R) hℓ2W
  have hr_hi16 : (r : ℝ) ≤ 16 * S.R := le_trans (by linarith) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by linarith
  -- ===== STEP 1 : closeness ×2 via dtilde_close =====
  have hd_close : |(d : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by linarith
  have hd2_close : |(d₂ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2
  -- ===== STEP 2 : b₀ / v =====
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / ((ℓ₁ : ℤ) : ℝ) with hb₀_def
  set v : ℝ := ((d₂ : ℝ) - (d : ℝ)) - ((ℓ₂ : ℤ) : ℝ) * b₀ with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₁ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
  have hb02 : |((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ)| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₂ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₂ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ2R (by exact_mod_cast hℓ2_lo) hr_lo hr2_hi
      hd_close hd2_close hG1 hΔ1
  -- ===== STEP 3 : U * W ≤ R =====
  have hRUW : P.U * P.Wval ≤ S.R := U_mul_W_le_R (S := S) h1 hband hΩU hΔ1 hU1
  -- ===== STEP 4 : Taylor windows via step1_window_bound =====
  have hwin1 : 4 * ((a : ℝ) + ((ℓ₁ : ℤ) : ℝ) * |b₀|) ≤ (d : ℝ) :=
    step1_window_bound (a := a) (ℓ₂ := (ℓ₁ : ℤ)) (b₀ := b₀) (dd := (d : ℝ))
      ha_hi hℓ1W hℓ1nn hb0 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin2' : 4 * ((a : ℝ) + ((ℓ₂ : ℤ) : ℝ) * |((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ)|)
      ≤ (d : ℝ) :=
    step1_window_bound (a := a) (ℓ₂ := (ℓ₂ : ℤ)) (b₀ := ((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ))
      (dd := (d : ℝ)) ha_hi hℓ2W hℓ2nn hb02 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  -- ===== STEP 5 : definitional pinning =====
  have hb0def : ((ℓ₁ : ℤ) : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ) := by rw [hb₀_def]; field_simp
  have hvdef : ((ℓ₂ : ℤ) : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ) := by rw [hv_def]; ring
  have hwin2 : 4 * ((a : ℝ) + |((ℓ₂ : ℤ) : ℝ) * b₀ + v|) ≤ (d : ℝ) := by
    have heq : |((ℓ₂ : ℤ) : ℝ) * b₀ + v|
        = ((ℓ₂ : ℤ) : ℝ) * |((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ)| := by
      rw [hvdef, abs_div, abs_of_pos hℓ2R]; field_simp
    rw [heq]; exact hwin2'
  have hwin1' : 4 * ((a : ℝ) + ((ℓ₁ : ℤ) : ℝ) * |b₀|) ≤ (d : ℝ) := hwin1
  -- ===== STEP 6 : v bound via v_defect_le =====
  have hvd := v_defect_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) (d := d) (d₁ := d₁) (d₂ := d₂)
    hAD ha0 ha_lo ha_hi hℓ1Z hℓ1_loZ hℓ12Z hℓ2W hr_lo hr2_hi
    hd_close hd1_close hd2_close h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hv_shape : v = ((d₂ : ℝ) - (d : ℝ))
      - (((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ)) * ((d₁ : ℝ) - (d : ℝ)) := by
    rw [hv_def, hb₀_def]; ring
  have hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    rw [hv_shape]
    refine le_trans hvd ?_
    have hnn : (0 : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by
      have := S.Δ_pos; have := P.U_pos; have := S.Ω_pos; positivity
    gcongr; norm_num
  -- the `vval`-shape identity
  have hvval_eq : vval P a dStar ℓ₁ ℓ₂ r = v := by
    rw [vval, hv_shape, hd_def, hd1_def, hd2_def]
  -- ===== STEP 7 : the rounding cap via Q_distInt_le (the `hf` second branch) =====
  set 𝒬 : ℝ := ((ℓ₁ : ℤ) : ℝ) * Fab P.X (a : ℝ) (((ℓ₂ : ℤ) : ℝ) * b₀ + v) (d : ℝ)
      - ((ℓ₂ : ℤ) : ℝ) * Fab P.X (a : ℝ) (((ℓ₁ : ℤ) : ℝ) * b₀) (d : ℝ) with h𝒬def
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le hDpos hdwin.1
  have hd1pos : 0 < (d₁ : ℝ) := lt_of_lt_of_le hDpos hd1win.1
  have hd2pos : 0 < (d₂ : ℝ) := lt_of_lt_of_le hDpos hd2win.1
  -- the near-integer cap for `Qval = 𝒬`
  have hQcap : distInt 𝒬 ≤ ((ℓ₁ : ℤ) : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₂ : ℝ) ^ 2)
      + ((ℓ₂ : ℤ) : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₁ : ℝ) ^ 2) := by
    have hQd := Q_distInt_le (X := P.X) (H := P.H) (a := a) (d := d) (d₁ := d₁) (d₂ := d₂)
      (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) P.X_pos ha0 hdpos hd1pos hd2pos
      (by exact_mod_cast hℓ1Z.le) (by exact_mod_cast hℓ2nn) hinDa hinDa1 hinDa2
    -- `Q_distInt_le`'s argument equals `𝒬` after expanding `Fab`
    have harg : ((ℓ₁ : ℤ) : ℝ) * (Ffun P.X (a : ℝ) (d : ℝ) - Ffun P.X (a : ℝ) (d₂ : ℝ))
          - ((ℓ₂ : ℤ) : ℝ) * (Ffun P.X (a : ℝ) (d : ℝ) - Ffun P.X (a : ℝ) (d₁ : ℝ)) = 𝒬 := by
      rw [h𝒬def, Fab, Fab, hvdef, hb0def]
      have e2 : (d : ℝ) + ((d₂ : ℝ) - (d : ℝ)) = (d₂ : ℝ) := by ring
      have e1 : (d : ℝ) + ((d₁ : ℝ) - (d : ℝ)) = (d₁ : ℝ) := by ring
      rw [e2, e1]
    rw [harg] at hQd
    exact hQd
  set f : ℤ := round 𝒬 with hf_def
  have hf : (f : ℝ) = 𝒬 ∨ |(f : ℝ) - 𝒬|
      ≤ ((ℓ₁ : ℤ) : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₂ : ℝ) ^ 2)
        + ((ℓ₂ : ℤ) : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₁ : ℝ) ^ 2) := by
    right
    have hdist : |(f : ℝ) - 𝒬| = distInt 𝒬 := by
      rw [hf_def, distInt, abs_sub_comm]
    rw [hdist]; exact hQcap
  -- ===== STEP 8 : finish via phiv_delta_le =====
  have hgoal := phiv_delta_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := ((ℓ₁ : ℤ) : ℝ)) (ℓ₂ := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v) (𝒬 := 𝒬)
    (d := (d : ℝ)) (d₁ := (d₁ : ℝ)) (d₂ := (d₂ : ℝ)) (f := f)
    hAD ha0 ha_lo ha_hi hr_lo hr1_hi hℓ1R hℓ1_loR hℓ12R hℓ2W hdwin hd1win hd2win
    hd_close hd1_close hb0def hv hb0 h𝒬def hf
    (by exact_mod_cast hd1ned) (by rw [hvval_eq] at hℓ2bv_ne; exact hℓ2bv_ne)
    hwin2 hwin1' h1 hΔreg hband hG1 hU1 hΔ1 hH1 hΩU hUbig hUH
  -- transport: `phiv ... v r = phiv ... (vval ...) r`
  rw [hvval_eq]
  exact hgoal

end Squarefree
