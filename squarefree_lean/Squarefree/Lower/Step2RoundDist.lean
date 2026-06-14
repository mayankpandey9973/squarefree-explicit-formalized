import Squarefree.Lower.Step3Witness
import Squarefree.Lower.Step2Model

/-!
# §5 Step-2 per-`r` near-integer bound from `dStar`-witnesses (regime-independent)

`phif_round_distInt` is the per-`r` extraction of `Ra_step2_count`'s `hFdist` block: given the
`dStar`-window witnesses at `r`, `r+ℓ₁`, `r+ℓ₂` and `round (Qval) = f`, the phase `φ_f` is within
`4·δ₂₃` of an integer.  It is `f`-INDEPENDENT (no `f`-largeness), so it feeds BOTH the `f`-large
band count (`Ra_step2_count`) and the curvature-regime count (`Ra_step2_count_curv`).
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **§5 Step-2 per-`r` δ₂₃ bound from witnesses.**  Mirrors `Ra_step2_count`'s `hFdist` derivation
for a single `r` with the three `dStar`-window facts. -/
theorem phif_round_distInt {a : ℤ} {ℓ₁ ℓ₂ : ℕ} {f : ℤ} {r : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    {dStar : ℕ → ℤ}
    (hin0 : inDa P.X P.H a (dStar r)) (hlo0 : S.D ≤ (dStar r : ℝ))
    (hhi0 : (dStar r : ℝ) ≤ 2 * S.D)
    (hRd0 : |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hwlo0 : (1/72) * S.R ≤ (r : ℝ))
    (hin1 : inDa P.X P.H a (dStar (r + ℓ₁))) (hlo1 : S.D ≤ (dStar (r + ℓ₁) : ℝ))
    (hhi1 : (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D)
    (hRd1 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))| ≤ 14 * P.H / S.D)
    (hwhi1 : (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
    (hin2 : inDa P.X P.H a (dStar (r + ℓ₂))) (hlo2 : S.D ≤ (dStar (r + ℓ₂) : ℝ))
    (hhi2 : (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D)
    (hRd2 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))| ≤ 14 * P.H / S.D)
    (hwhi2 : (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
    (hround : round (Qval P a dStar ℓ₁ ℓ₂ r) = f)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) :
    Counting.distInt (phif P.X (a : ℝ) ((ℓ₁:ℤ):ℝ) ((ℓ₂:ℤ):ℝ) (f:ℝ) (r : ℝ))
      ≤ 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) := by
  have hHpos := P.H_pos
  have hΔpos := S.Δ_pos
  have hUpos := P.U_pos
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
  have hcast2 : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
  have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
  have hd0pos : (0 : ℝ) < (dStar r : ℝ) := lt_of_lt_of_le hDpos hlo0
  have hd1pos : (0 : ℝ) < (dStar (r + ℓ₁) : ℝ) := lt_of_lt_of_le hDpos hlo1
  have hd2pos : (0 : ℝ) < (dStar (r + ℓ₂) : ℝ) := lt_of_lt_of_le hDpos hlo2
  have hΔbig : (28 : ℝ) < S.Δ := by
    have hU5 : P.U ≤ P.U ^ 5 := by
      nlinarith [pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ) ≤ (10:ℝ)^33) hUbig)
        (by norm_num : (1:ℕ) ≤ 5), hUpos]
    have hG2 : (1 : ℝ) ≤ P.G ^ 2 := by nlinarith [hG1]
    have : P.U ^ 5 ≤ P.G ^ 2 * P.U ^ 5 := by nlinarith [hG2, pow_pos hUpos 5]
    have h28 : (28 : ℝ) ≤ P.U := by nlinarith [hUbig]
    nlinarith [hΔreg, this, hU5, h28]
  have hd1ned : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ) := by
    intro hcontra
    rw [hcontra] at hRd1
    have htri : ((ℓ₁ : ℤ) : ℝ) ≤ 28 * P.H / S.D := by
      have hk := abs_sub_le ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))
        (Rfun P.X (a : ℝ) (dStar r : ℝ)) (r : ℝ)
      have habs1 : |(r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - Rfun P.X (a : ℝ) (dStar r : ℝ)|
          ≤ 14 * P.H / S.D := by rw [abs_sub_comm]; exact hRd1
      have heq : |(r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - (r : ℝ)| = ((ℓ₁ : ℤ) : ℝ) := by
        rw [show (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - (r : ℝ) = ((ℓ₁ : ℤ) : ℝ) by ring]
        exact abs_of_nonneg (by linarith [hℓ1R])
      rw [heq] at hk
      calc ((ℓ₁ : ℤ) : ℝ) ≤ 14 * P.H / S.D + 14 * P.H / S.D :=
            le_trans hk (by linarith [hRd0, habs1])
        _ = 28 * P.H / S.D := by ring
    have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
      rw [show S.D = P.H * S.Δ from rfl, mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
    rw [hsimp] at htri
    have hmul : ((ℓ₁ : ℤ) : ℝ) * S.Δ ≤ 28 := by rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
    have hge : S.Δ ≤ ((ℓ₁ : ℤ) : ℝ) * S.Δ := by
      have := mul_le_mul_of_nonneg_right hℓ1R (le_of_lt hΔpos); linarith [this]
    linarith [hmul, hge, hΔbig]
  have hd2ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ) := by
    have hℓ2R : (1 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := by
      have : (1:ℤ) ≤ (ℓ₂:ℤ) := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hℓ1 hℓ12))
      exact_mod_cast this
    intro hcontra
    rw [hcontra] at hRd2
    have htri : ((ℓ₂ : ℤ) : ℝ) ≤ 28 * P.H / S.D := by
      have hk := abs_sub_le ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))
        (Rfun P.X (a : ℝ) (dStar r : ℝ)) (r : ℝ)
      have habs2 : |(r : ℝ) + ((ℓ₂ : ℤ) : ℝ) - Rfun P.X (a : ℝ) (dStar r : ℝ)|
          ≤ 14 * P.H / S.D := by rw [abs_sub_comm]; exact hRd2
      have heq : |(r : ℝ) + ((ℓ₂ : ℤ) : ℝ) - (r : ℝ)| = ((ℓ₂ : ℤ) : ℝ) := by
        rw [show (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) - (r : ℝ) = ((ℓ₂ : ℤ) : ℝ) by ring]
        exact abs_of_nonneg (by linarith [hℓ2R])
      rw [heq] at hk
      calc ((ℓ₂ : ℤ) : ℝ) ≤ 14 * P.H / S.D + 14 * P.H / S.D :=
            le_trans hk (by linarith [hRd0, habs2])
        _ = 28 * P.H / S.D := by ring
    have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
      rw [show S.D = P.H * S.Δ from rfl, mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
    rw [hsimp] at htri
    have hmul : ((ℓ₂ : ℤ) : ℝ) * S.Δ ≤ 28 := by rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
    have hge : S.Δ ≤ ((ℓ₂ : ℤ) : ℝ) * S.Δ := by
      have := mul_le_mul_of_nonneg_right hℓ2R (le_of_lt hΔpos); linarith [this]
    linarith [hmul, hge, hΔbig]
  have h𝒬 : Qval P a dStar ℓ₁ ℓ₂ r
      = ((ℓ₁ : ℤ) : ℝ) * Fab P.X (a : ℝ) ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ)) (dStar r : ℝ)
        - ((ℓ₂ : ℤ) : ℝ) * Fab P.X (a : ℝ)
            ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) (dStar r : ℝ) := by
    simp only [Qval, Fab]
    rw [show (dStar r : ℝ) + ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ)) = (dStar (r + ℓ₂) : ℝ) by ring,
      show (dStar r : ℝ) + ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) = (dStar (r + ℓ₁) : ℝ) by ring]
    push_cast; ring
  have hf_near : |(f : ℝ) - Qval P a dStar ℓ₁ ℓ₂ r|
      ≤ ((ℓ₁ : ℤ) : ℝ) * (2 * P.H / (dStar r : ℝ) ^ 2 + 2 * P.H / (dStar (r + ℓ₂) : ℝ) ^ 2)
        + ((ℓ₂ : ℤ) : ℝ)
            * (2 * P.H / (dStar r : ℝ) ^ 2 + 2 * P.H / (dStar (r + ℓ₁) : ℝ) ^ 2) := by
    have heqd : |(f : ℝ) - Qval P a dStar ℓ₁ ℓ₂ r|
        = Counting.distInt (Qval P a dStar ℓ₁ ℓ₂ r) := by
      rw [Counting.distInt, abs_sub_comm, hround]
    rw [heqd, show Qval P a dStar ℓ₁ ℓ₂ r
        = ((ℓ₁:ℤ):ℝ) * (Ffun P.X (a:ℝ) (dStar r : ℝ) - Ffun P.X (a:ℝ) (dStar (r+ℓ₂) : ℝ))
          - ((ℓ₂:ℤ):ℝ)
              * (Ffun P.X (a:ℝ) (dStar r : ℝ) - Ffun P.X (a:ℝ) (dStar (r+ℓ₁) : ℝ)) by
      simp only [Qval]; push_cast; ring]
    exact Q_distInt_le (X := P.X) (H := P.H) (a := a)
      (d := dStar r) (d₁ := dStar (r + ℓ₁)) (d₂ := dStar (r + ℓ₂))
      (ℓ₁ := (ℓ₁:ℤ)) (ℓ₂ := (ℓ₂:ℤ))
      P.X_pos ha0 hd0pos hd1pos hd2pos (by exact_mod_cast (Nat.zero_le ℓ₁))
      (by exact_mod_cast (Nat.zero_le ℓ₂)) hin0 hin1 hin2
  exact phif_distInt_from_witness (P := P) (S := S) (a := a) (r := (r:ℝ))
    (ℓ₁ := (ℓ₁:ℤ)) (ℓ₂ := (ℓ₂:ℤ)) (d := dStar r) (d₁ := dStar (r + ℓ₁)) (d₂ := dStar (r + ℓ₂))
    (𝒬 := Qval P a dStar ℓ₁ ℓ₂ r) (f := f)
    hAD ha0 ha_lo ha_hi (by exact_mod_cast hℓ1) (by exact_mod_cast hℓ1)
    (by exact_mod_cast hℓ12) hℓ2W hwlo0 (by linarith [hwhi1]) (by linarith [hwhi2])
    hin0 hin1 hin2 ⟨hlo0, hhi0⟩ ⟨hlo1, hhi1⟩ ⟨hlo2, hhi2⟩
    hRd0 hRd1 hRd2
    hd1ned hd2ned h𝒬 hf_near
    h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg

end Squarefree
