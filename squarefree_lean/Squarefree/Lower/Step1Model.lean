import Squarefree.Lower.Step1Count3

/-!
# §5 Step-1 v=0 modeling: the count for the concrete `v=0` triple set (writeup 681–846)

`Ra_step1_v0_count` discharges `step1_v0_count`'s abstract `hT` for the concrete set

  `T₀ = {r ∈ Ra : r+ℓ₁∈Ra ∧ r+ℓ₂∈Ra ∧ v(r)=0}`,

where the discrete witnesses come from a function `dStar : ℕ → ℤ` satisfying the
`RaWitness` data on `Ra` (in `prop_5_1` this is `Classical.choose ∘ hwit`). The defect
`v(r) = d₂ − d − (ℓ₂/ℓ₁)(d₁−d)` (writeup 686/711) vanishes iff `ℓ₁(d₂−d)=ℓ₂(d₁−d)`.

The one non-`RaWitness` fact is `hb0ne : d₁ ≠ d`: if `d₁=d` then the two `R_a`-slacks
force `ℓ₁ ≤ 28H/D = 28/Δ`, contradicting `ℓ₁≥1` since `Δ ≥ G²U⁵ ≥ U⁵ ≫ 28`. So no
degenerate triple `d=d₁=d₂` survives, and `hb0ne` is automatic.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **Step-1 v=0 count for the concrete triple set.** -/
theorem Ra_step1_v0_count {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U) (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        (ℓ₁ : ℤ) * (dStar (r + ℓ₂) - dStar r) = (ℓ₂ : ℤ) * (dStar (r + ℓ₁) - dStar r))).card : ℝ)
      ≤ (10 ^ 20 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) / (P.G * S.Ω ^ 5))
          + 2 * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5)) + 1)
        * (2 * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5))
            / (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
                / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)) + 1) := by
  -- positivity facts
  have hHpos := P.H_pos
  have hΔpos := S.Δ_pos
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  -- `S.Δ > 28`: from `Δ ≥ G²U⁵ ≥ U⁵ ≥ U ≥ 10^33`.
  have hUpos := P.U_pos
  have hΔbig : (28 : ℝ) < S.Δ := by
    have hU5 : P.U ≤ P.U ^ 5 := by
      nlinarith [pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ) ≤ (10:ℝ)^33) hUbig) (by norm_num : (1:ℕ) ≤ 5), hUpos]
    have hG2 : (1 : ℝ) ≤ P.G ^ 2 := by nlinarith [hG1]
    have : P.U ^ 5 ≤ P.G ^ 2 * P.U ^ 5 := by nlinarith [hG2, pow_pos hUpos 5]
    have h28 : (28 : ℝ) ≤ P.U := by nlinarith [hUbig]
    nlinarith [hΔreg, this, hU5, h28]
  refine step1_v0_count hAD ha0 ha_lo ha_hi (by exact_mod_cast hℓ1)
    (by exact_mod_cast hℓ1) (by exact_mod_cast hℓ12) hℓ2W h1 hband hG1 hU1 hΔ1 hUH hΩU hUbig _ ?_
  -- discharge `hT`
  intro r hr
  rw [Finset.mem_filter] at hr
  obtain ⟨hrRa, hr1Ra, hr2Ra, hveq⟩ := hr
  refine ⟨dStar r, dStar (r + ℓ₁), dStar (r + ℓ₂), ?_⟩
  obtain ⟨hin0, hlo0, hhi0, hRd0, hwlo0, hwhi0⟩ := hdStar r hrRa
  obtain ⟨hin1, hlo1, hhi1, hRd1, hwlo1, hwhi1⟩ := hdStar (r + ℓ₁) hr1Ra
  obtain ⟨hin2, hlo2, hhi2, hRd2, hwlo2, hwhi2⟩ := hdStar (r + ℓ₂) hr2Ra
  -- cast facts for `r + ℓ₁`, `r + ℓ₂`
  have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
  have hcast2 : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
  rw [hcast1] at hRd1 hwhi1
  -- the v=0 equation cast to ℝ
  have hv0 : ((ℓ₁ : ℤ) : ℝ) * ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ))
      = ((ℓ₂ : ℤ) : ℝ) * ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) := by
    exact_mod_cast hveq
  -- `hb0ne : (dStar (r+ℓ₁) : ℝ) ≠ (dStar r : ℝ)`
  have hb0ne : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ) := by
    intro hcontra
    -- triangle inequality forces `ℓ₁ ≤ 28 H / D = 28/Δ`
    rw [hcontra] at hRd1
    -- |((r:ℝ)+ℓ₁) - r| ≤ 28 H / D
    have htri : ((ℓ₁ : ℤ) : ℝ) ≤ 28 * P.H / S.D := by
      have hk := abs_sub_le ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (Rfun P.X (a : ℝ) (dStar r : ℝ)) (r : ℝ)
      have habs0 : |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D := hRd0
      have habs1 : |(r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - Rfun P.X (a : ℝ) (dStar r : ℝ)| ≤ 14 * P.H / S.D := by
        rw [abs_sub_comm]; exact hRd1
      have heq : |(r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - (r : ℝ)| = ((ℓ₁ : ℤ) : ℝ) := by
        rw [show (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - (r : ℝ) = ((ℓ₁ : ℤ) : ℝ) by ring]
        exact abs_of_nonneg (by linarith [hℓ1R])
      rw [heq] at hk
      calc ((ℓ₁ : ℤ) : ℝ) ≤ 14 * P.H / S.D + 14 * P.H / S.D := le_trans hk (by linarith [habs0, habs1])
        _ = 28 * P.H / S.D := by ring
    -- `28 H / D = 28 / Δ` since `D = H Δ`
    have hDdef : S.D = P.H * S.Δ := rfl
    have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
      rw [hDdef]
      rw [mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
    rw [hsimp] at htri
    -- `ℓ₁ ≤ 28/Δ` with `ℓ₁ ≥ 1`, `Δ > 28` ⇒ contradiction
    have : ((ℓ₁ : ℤ) : ℝ) * S.Δ ≤ 28 := by
      rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
    nlinarith [hℓ1R, hΔbig, this, hΔpos]
  -- assemble
  exact ⟨hin0, hin1, hin2,
    ⟨hlo0, hhi0⟩, ⟨hlo1, hhi1⟩, ⟨hlo2, hhi2⟩,
    hRd0, hRd1, hv0, hb0ne, hwlo0, hwhi1⟩

end Squarefree
