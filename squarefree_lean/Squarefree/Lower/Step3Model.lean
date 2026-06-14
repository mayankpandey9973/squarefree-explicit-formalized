import Squarefree.Lower.Step3Witness
import Squarefree.Lower.Step3Count2
import Squarefree.Lower.QNearInt

/-!
# §5 Step-3 per-`f` count for the concrete triple set (writeup 975–984)

`Ra_step3_count`: for a fixed integer `f`, the set of triples `r ∈ Ra` (with `r+ℓ₁,r+ℓ₂ ∈ Ra`)
whose defect `𝒬(r)` rounds to `f` has card `≤ step3_smooth_count`'s bound (with `δ := 4·δ₂₃`).
Each such `r`: `hf_near` from `|round 𝒬(r) − 𝒬(r)| = distInt(𝒬(r)) ≤ Q_distInt_le`, then
`phif_distInt_from_witness` gives `distInt(φ_f(r)) ≤ 4·δ₂₃`, then `step3_subset_count`.
Non-degeneracy `d₁≠d, d₂≠d` is derived (no degenerate triples, as in `Ra_step1_v0_count`).
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- The defect `𝒬(r)` in `Ffun`-difference form, from a witness function `dStar`. -/
noncomputable def Qval (P : Globals) (a : ℤ) (dStar : ℕ → ℤ) (ℓ₁ ℓ₂ r : ℕ) : ℝ :=
  (ℓ₁ : ℝ) * (Ffun P.X (a : ℝ) (dStar r : ℝ) - Ffun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ))
    - (ℓ₂ : ℝ) * (Ffun P.X (a : ℝ) (dStar r : ℝ) - Ffun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ))

/-- **Step-3 per-`f` count.** -/
theorem Ra_step3_count {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    {f : ℤ}
    (hflarge : (10:ℝ) ^ 55 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
        / (P.G * S.Ω ^ 5)) ≤ |(f : ℝ)|)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ)
      ≤ (10 ^ 6 * (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A))
          + 2 * (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))) + 1)
        * (2 * (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)))
            / (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50)) + 1) := by
  -- positivity facts
  have hHpos := P.H_pos
  have hΔpos := S.Δ_pos
  have hUpos := P.U_pos
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  -- `S.Δ > 28`: from `Δ ≥ G²U⁵ ≥ U⁵ ≥ U ≥ 10^33`.
  have hΔbig : (28 : ℝ) < S.Δ := by
    have hU5 : P.U ≤ P.U ^ 5 := by
      nlinarith [pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ) ≤ (10:ℝ)^33) hUbig)
        (by norm_num : (1:ℕ) ≤ 5), hUpos]
    have hG2 : (1 : ℝ) ≤ P.G ^ 2 := by nlinarith [hG1]
    have : P.U ^ 5 ≤ P.G ^ 2 * P.U ^ 5 := by nlinarith [hG2, pow_pos hUpos 5]
    have h28 : (28 : ℝ) ≤ P.U := by nlinarith [hUbig]
    nlinarith [hΔreg, this, hU5, h28]
  -- abbreviation for the δ₃ bound
  set δ₃ : ℝ := 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) with hδ₃_def
  -- `hsmall : 10^33 * ℓ₁ ≤ S.R` (chain through Wval / U·W ≤ R)
  have hWpos : (0 : ℝ) < P.Wval := by rw [Globals.Wval]; have := P.G_pos; positivity
  have hℓ1W : ((ℓ₁ : ℤ) : ℝ) ≤ 130 * P.Wval := by
    have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
    linarith [hℓ2W, hℓ12R]
  have hRUW : 130 * (P.U * P.Wval) ≤ S.R :=
    U_mul_W130_le_R (S := S) h1 hband hΩU hΔ1 hU1 hUbig hG1
  have hsmall : (10:ℝ) ^ 33 * ((ℓ₁ : ℤ) : ℝ) ≤ S.R := by
    have hWnn : (0:ℝ) ≤ 130 * P.Wval := by
      rw [Globals.Wval]; have := P.G_pos; positivity
    calc (10:ℝ) ^ 33 * ((ℓ₁ : ℤ) : ℝ)
        ≤ (10:ℝ) ^ 33 * (130 * P.Wval) := by
          apply mul_le_mul_of_nonneg_left hℓ1W (by positivity)
      _ ≤ P.U * (130 * P.Wval) := mul_le_mul_of_nonneg_right hUbig hWnn
      _ = 130 * (P.U * P.Wval) := by ring
      _ ≤ S.R := hRUW
  -- `hδ : 0 ≤ δ₃`
  have hδ : 0 ≤ δ₃ := by
    rw [hδ₃_def]; have := S.Ω_pos; have := P.G_pos; positivity
  -- apply step3_subset_count.  RHS matches exactly with δ := δ₃.
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R0 : (0 : ℝ) < ((ℓ₁:ℤ):ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁:ℤ):ℝ) < ((ℓ₂:ℤ):ℝ) := by exact_mod_cast hℓ12
  refine step3_subset_count (a := (a:ℝ)) (ℓ₁ := ((ℓ₁:ℤ):ℝ)) (ℓ₂ := ((ℓ₂:ℤ):ℝ))
    (f := (f:ℝ)) (r₀ := (1/72) * S.R) (r₁ := 16 * S.R - ((ℓ₁:ℤ):ℝ)) (δ := δ₃)
    hAD ha0R ha_lo ha_hi hℓ1R0 hℓ12R hsmall hflarge
    (le_refl _) ?_ (le_of_eq (by ring)) hδ _ ?_
  · -- hr01 : (1/72)*S.R ≤ 16*S.R - ℓ₁
    have hRpos : (0 : ℝ) < S.R := by
      unfold Scale.R; have := P.G_pos; have := S.Ω_pos; positivity
    -- ℓ₁ ≤ R from hsmall (10^33·ℓ₁ ≤ R, 10^33 ≥ 1)
    have hℓ1leR : ((ℓ₁:ℤ):ℝ) ≤ S.R := by
      have hge : ((ℓ₁:ℤ):ℝ) ≤ (10:ℝ)^33 * ((ℓ₁:ℤ):ℝ) := by
        nlinarith [hℓ1R, (by norm_num : (1:ℝ) ≤ (10:ℝ)^33)]
      linarith [hsmall, hge]
    linarith [hℓ1leR, hRpos]
  · -- hT' : the filter satisfies the window + distInt bound
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1Ra, hr2Ra, hround⟩ := hr
    obtain ⟨hin0, hlo0, hhi0, hRd0, hwlo0, hwhi0⟩ := hdStar r hrRa
    obtain ⟨hin1, hlo1, hhi1, hRd1, hwlo1, hwhi1⟩ := hdStar (r + ℓ₁) hr1Ra
    obtain ⟨hin2, hlo2, hhi2, hRd2, hwlo2, hwhi2⟩ := hdStar (r + ℓ₂) hr2Ra
    -- cast facts for `r + ℓ₁`, `r + ℓ₂`
    have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
    have hcast2 : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast1] at hRd1 hwhi1 hwlo1
    rw [hcast2] at hRd2 hwhi2 hwlo2
    -- window components for step3_subset_count
    refine ⟨hwlo0, by linarith [hwhi1], ?_⟩
    -- positivity of d, d₁, d₂
    have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
    have hd0pos : (0 : ℝ) < (dStar r : ℝ) := lt_of_lt_of_le hDpos hlo0
    have hd1pos : (0 : ℝ) < (dStar (r + ℓ₁) : ℝ) := lt_of_lt_of_le hDpos hlo1
    have hd2pos : (0 : ℝ) < (dStar (r + ℓ₂) : ℝ) := lt_of_lt_of_le hDpos hlo2
    -- `hd1ned : (d₁:ℝ) ≠ (d:ℝ)` by the slack/Δ>28 contradiction
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
      have hDdef : S.D = P.H * S.Δ := rfl
      have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
        rw [hDdef, mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
      rw [hsimp] at htri
      have hmul : ((ℓ₁ : ℤ) : ℝ) * S.Δ ≤ 28 := by
        rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
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
      have hDdef : S.D = P.H * S.Δ := rfl
      have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
        rw [hDdef, mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
      rw [hsimp] at htri
      have hmul : ((ℓ₂ : ℤ) : ℝ) * S.Δ ≤ 28 := by
        rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
      have hge : S.Δ ≤ ((ℓ₂ : ℤ) : ℝ) * S.Δ := by
        have := mul_le_mul_of_nonneg_right hℓ2R (le_of_lt hΔpos); linarith [this]
      linarith [hmul, hge, hΔbig]
    -- the 𝒬 shape: Qval = ℓ₁·Fab(d₂-d, d) - ℓ₂·Fab(d₁-d, d)
    have h𝒬 : Qval P a dStar ℓ₁ ℓ₂ r
        = ((ℓ₁ : ℤ) : ℝ) * Fab P.X (a : ℝ) ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ)) (dStar r : ℝ)
          - ((ℓ₂ : ℤ) : ℝ) * Fab P.X (a : ℝ)
              ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) (dStar r : ℝ) := by
      simp only [Qval, Fab]
      have e2 : (dStar r : ℝ) + ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ)) = (dStar (r + ℓ₂) : ℝ) := by
        ring
      have e1 : (dStar r : ℝ) + ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) = (dStar (r + ℓ₁) : ℝ) := by
        ring
      rw [e2, e1]; push_cast; ring
    -- hf_near via round / Q_distInt_le
    have hf_near : |(f : ℝ) - Qval P a dStar ℓ₁ ℓ₂ r|
        ≤ ((ℓ₁ : ℤ) : ℝ) * (2 * P.H / (dStar r : ℝ) ^ 2 + 2 * P.H / (dStar (r + ℓ₂) : ℝ) ^ 2)
          + ((ℓ₂ : ℤ) : ℝ)
              * (2 * P.H / (dStar r : ℝ) ^ 2 + 2 * P.H / (dStar (r + ℓ₁) : ℝ) ^ 2) := by
      -- |f - Qval| = distInt(Qval) using round Qval = f
      have heqd : |(f : ℝ) - Qval P a dStar ℓ₁ ℓ₂ r|
          = Counting.distInt (Qval P a dStar ℓ₁ ℓ₂ r) := by
        rw [Counting.distInt, abs_sub_comm, hround]
      rw [heqd]
      -- Qval matches Q_distInt_le's argument
      have hQeq : Qval P a dStar ℓ₁ ℓ₂ r
          = ((ℓ₁:ℤ):ℝ) * (Ffun P.X (a:ℝ) (dStar r : ℝ) - Ffun P.X (a:ℝ) (dStar (r+ℓ₂) : ℝ))
            - ((ℓ₂:ℤ):ℝ)
                * (Ffun P.X (a:ℝ) (dStar r : ℝ) - Ffun P.X (a:ℝ) (dStar (r+ℓ₁) : ℝ)) := by
        simp only [Qval]; push_cast; ring
      rw [hQeq]
      exact Q_distInt_le (X := P.X) (H := P.H) (a := a)
        (d := dStar r) (d₁ := dStar (r + ℓ₁)) (d₂ := dStar (r + ℓ₂))
        (ℓ₁ := (ℓ₁:ℤ)) (ℓ₂ := (ℓ₂:ℤ))
        P.X_pos ha0 hd0pos hd1pos hd2pos (by exact_mod_cast (Nat.zero_le ℓ₁))
        (by exact_mod_cast (Nat.zero_le ℓ₂)) hin0 hin1 hin2
    -- finally apply phif_distInt_from_witness
    have hfinal := phif_distInt_from_witness (P := P) (S := S) (a := a) (r := (r:ℝ))
      (ℓ₁ := (ℓ₁:ℤ)) (ℓ₂ := (ℓ₂:ℤ)) (d := dStar r) (d₁ := dStar (r + ℓ₁)) (d₂ := dStar (r + ℓ₂))
      (𝒬 := Qval P a dStar ℓ₁ ℓ₂ r) (f := f)
      hAD ha0 ha_lo ha_hi (by exact_mod_cast hℓ1) (by exact_mod_cast hℓ1)
      (by exact_mod_cast hℓ12) hℓ2W hwlo0 (by linarith [hwhi1]) (by linarith [hwhi2])
      hin0 hin1 hin2 ⟨hlo0, hhi0⟩ ⟨hlo1, hhi1⟩ ⟨hlo2, hhi2⟩
      hRd0 hRd1 hRd2 hd1ned hd2ned h𝒬 hf_near
      h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg
    exact hfinal

end Squarefree
