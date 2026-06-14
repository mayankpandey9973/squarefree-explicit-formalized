import Squarefree.Lower.Step23Reduce
import Squarefree.Lower.Step23Delta
import Squarefree.Lower.Step23DeltaQgen
import Squarefree.Lower.DefectExpandV
import Squarefree.Lower.DefectReplace

/-!
# §5 Steps 2/3 per-`r` reduction: the uniform δ₂₃ bound (writeup 884–903)

`phif_delta_le` is the v≠0 analogue of `phi_distInt_le_unif`: it combines the algebraic
reduction `phif_dist_le` with the four scaled delta pieces into the uniform near-integer
bound `distInt(φ_f) ≤ 4·δ₂₃`, `δ₂₃ = Δ²GU²⁰/(HΩ⁶)`, for any integer `f` within the
`Q_distInt_le` slack of `𝒬` (in practice `f = round 𝒬`).

The four `phif_dist_le` remainder terms are bounded by, in order:
`near_int_piece_le` (via `hf_near`), `qgen_piece_le` (via `Q_gen_expand`),
`replace_piece_le` (via `phi_d_replace`), `v_replace_le`.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **§5 Steps 2/3 per-`r` δ₂₃ bound.** -/
theorem phif_delta_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ} {b₀ v 𝒬 : ℝ} {f : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) (hr1_hi : r + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hdwin : S.D ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * S.D) (hd1win : S.D ≤ (d₁ : ℝ) ∧ (d₁ : ℝ) ≤ 2 * S.D)
    (hd2win : S.D ≤ (d₂ : ℝ) ∧ (d₂ : ℝ) ≤ 2 * S.D)
    (hd_close  : |(d : ℝ)  - dtilde P.X r (a : ℝ)|             ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hd1_close : |(d₁ : ℝ) - dtilde P.X (r + (ℓ₁ : ℝ)) (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    -- the discrete slope/defect, pinned to the witnesses
    (hb0def : (ℓ₁ : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ))
    (hvdef : (ℓ₂ : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ))
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hd1ned : (d₁ : ℝ) ≠ (d : ℝ)) (hd2ned : (d₂ : ℝ) ≠ (d : ℝ))
    -- Taylor windows for `Q_gen_expand`
    (hwin2 : 4 * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ≤ (d : ℝ))
    (hwin1 : 4 * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ≤ (d : ℝ))
    -- `𝒬` and the near-integer slack on `f`
    (h𝒬 : 𝒬 = (ℓ₁ : ℝ) * Fab P.X (a : ℝ) ((ℓ₂ : ℝ) * b₀ + v) (d : ℝ)
              - (ℓ₂ : ℝ) * Fab P.X (a : ℝ) ((ℓ₁ : ℝ) * b₀) (d : ℝ))
    (hf_near : |(f : ℝ) - 𝒬|
        ≤ (ℓ₁ : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₂ : ℝ) ^ 2)
          + (ℓ₂ : ℝ) * (2 * P.H / (d : ℝ) ^ 2 + 2 * P.H / (d₁ : ℝ) ^ 2))
    -- regime
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) :
    Counting.distInt (phif P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) (f : ℝ) r)
      ≤ 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) := by
  -- ===== casts =====
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : 0 < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ1_loR : (1 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1_lo
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hdRpos : 0 < (d : ℝ) := lt_of_lt_of_le hDpos hdwin.1
  have hℓ1W : (ℓ₁ : ℝ) ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12R) hℓ2W
  have hXpos : 0 < P.X := P.X_pos
  -- ===== the M witness and hM : ℓ₁ * v = (M : ℝ) =====
  set M : ℤ := ℓ₁ * (d₂ - d) - ℓ₂ * (d₁ - d) with hM_def
  have hM : (ℓ₁ : ℝ) * v = (M : ℝ) := by
    have hv' : v = ((d₂ : ℝ) - (d : ℝ)) - (ℓ₂ : ℝ) * b₀ := by linarith [hvdef]
    have : (ℓ₁ : ℝ) * v
        = (ℓ₁ : ℝ) * ((d₂ : ℝ) - (d : ℝ)) - (ℓ₂ : ℝ) * ((ℓ₁ : ℝ) * b₀) := by
      rw [hv']; ring
    rw [this, hb0def, hM_def]; push_cast; ring
  -- ===== STEP A : apply phif_dist_le =====
  have hreduce := phif_dist_le (P := P) (a := a) (r := r) (ℓ₁ := (ℓ₁ : ℝ))
    (ℓ₂ := (ℓ₂ : ℝ)) (b₀ := b₀) (v := v) (𝒬 := 𝒬) (f := (f : ℝ)) (d := (d : ℝ))
    (M := M) haR hdRpos hℓ1R hM h𝒬
  refine le_trans hreduce ?_
  -- prefactor (abbreviated)
  set PREF : ℝ := (dtilde P.X r (a : ℝ)) ^ 4 / (6 * P.X * (a : ℝ)) with hPREF_def
  have hPREF_nn : 0 ≤ PREF := by rw [hPREF_def]; positivity
  -- the four bound targets
  set PHID : ℝ := 12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)
      * b₀ ^ 2 / (d : ℝ) ^ 5 with hPHID_def
  set LEAD : ℝ := 6 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * v / (d : ℝ) ^ 4 - PHID with hLEAD_def
  -- ===== (b1) PREF * |f - 𝒬| ≤ δ₂₃ =====
  have b1 : PREF * |(f : ℝ) - 𝒬| ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
    refine le_trans (mul_le_mul_of_nonneg_left hf_near hPREF_nn) ?_
    exact near_int_piece_le (P := P) (S := S) (a := a) (r := r)
      (ℓ₁ := (ℓ₁ : ℝ)) (ℓ₂ := (ℓ₂ : ℝ)) (d := (d : ℝ)) (d₁ := (d₁ : ℝ)) (d₂ := (d₂ : ℝ))
      hAD ha0 ha_lo ha_hi hr_lo hr_hi hℓ1R hℓ12R hℓ2W hdwin.1 hd1win.1 hd2win.1
      hG1 hU1 hΔ1 hH1 hΩU hUbig
  -- ===== (b2) PREF * |𝒬 - LEAD| ≤ δ₂₃ =====
  have hℓ2bv : (ℓ₂ : ℝ) * b₀ + v ≠ 0 := by rw [hvdef]; exact sub_ne_zero.mpr hd2ned
  have hℓ1b₀ : (ℓ₁ : ℝ) * b₀ ≠ 0 := by rw [hb0def]; exact sub_ne_zero.mpr hd1ned
  have hQ := Q_gen_expand (X := P.X) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
    (ℓ₁ := (ℓ₁ : ℝ)) (ℓ₂ := (ℓ₂ : ℝ)) hXpos haR hdRpos hℓ1R hℓ12R hℓ2bv hℓ1b₀ hwin2 hwin1
  rw [← h𝒬, ← hPHID_def, ← hLEAD_def] at hQ
  have b2 : PREF * |𝒬 - LEAD| ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
    refine le_trans (mul_le_mul_of_nonneg_left hQ hPREF_nn) ?_
    exact qgen_piece_le (P := P) (S := S) (a := a) (r := r) (ℓ₁ := (ℓ₁ : ℝ))
      (ℓ₂ := (ℓ₂ : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
      hAD ha0 ha_lo ha_hi hr_lo hr_hi hℓ1R hℓ12R hℓ2W hdwin hb0 hv h1 hband
      hG1 hU1 hΔ1 hH1 hΩU hUbig
  -- ===== (b3) PREF * |phi - PHID| ≤ δ₂₃ =====
  have hℓ2W' : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hb0eq : b₀ = ((d₁ : ℝ) - (d : ℝ)) / (ℓ₁ : ℝ) := by
    field_simp; linarith [hb0def]
  have hR := phi_d_replace (P := P) (S := S) (a := a) (r := r) (ℓ₁ := (ℓ₁ : ℝ))
    (ℓ₂ := (ℓ₂ : ℝ)) (d := (d : ℝ)) (d₁ := (d₁ : ℝ)) hAD ha0 ha_lo ha_hi hℓ1R hℓ1_loR
    hℓ12R hℓ2W' hr_lo hr1_hi hdwin hd1win hd_close hd1_close h1 hband hG1 hU1 hΔ1 hUH
  -- replace ((d₁-d)/ℓ₁)^2 by b₀^2, giving |PHID - phi …| on the LHS
  rw [← hb0eq, ← hPHID_def] at hR
  have b3 : PREF * |phi P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) r - PHID|
      ≤ S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
    rw [abs_sub_comm]
    refine le_trans (mul_le_mul_of_nonneg_left hR hPREF_nn) ?_
    exact replace_piece_le (P := P) (S := S) (a := a) (r := r)
      hAD ha0 ha_lo ha_hi hr_lo hr_hi hG1 hU1 hΔ1 hΩU hUbig
  -- ===== (b4) v-term ≤ δ₂₃ =====
  have b4 : (ℓ₁ : ℝ) * |v| * |(dtilde P.X r (a : ℝ) / (d : ℝ)) ^ 4 - 1|
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) :=
    v_replace_le (P := P) (S := S) (a := a) (r := r) (ℓ₁ := (ℓ₁ : ℝ)) (v := v) (d := d)
      hAD ha0 ha_lo ha_hi hr_lo hr_hi hℓ1R hℓ1W hdwin hd_close hv hΔreg hG1 hU1 hΔ1 hUbig
  -- ===== STEP C : combine =====
  have hexp : PREF * (|(f : ℝ) - 𝒬| + |𝒬 - LEAD| + |phi P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) r - PHID|)
      = PREF * |(f : ℝ) - 𝒬| + PREF * |𝒬 - LEAD|
        + PREF * |phi P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) r - PHID| := by ring
  rw [hexp]
  -- pad the three old-δ₂₃ pieces with the extra `G ≥ 1` power
  have hGG : P.G ≤ P.G ^ 2 := by nlinarith [hG1]
  have hpad : S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6)
      ≤ S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
    have := P.H_pos; have := S.Ω_pos; have := S.Δ_pos
    gcongr
  linarith [b1, b2, b3, b4, hpad]

end Squarefree
