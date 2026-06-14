import Squarefree.Lower.Prop51Partition
import Squarefree.Lower.Prop51Bridges
import Squarefree.Lower.Step4BandPay

/-!
# §5 assembly — the `dStar` witness choice and shared regime facts

`dStarOf` selects, via choice, the popular defect `d` witnessing `r ∈ ℛ_a` (the
`RaWitness` data, writeup §3).  `dStarOf_spec` exposes the witness bundle; the
`witness_*` lemmas package it into the `hdStar`/`hwin` shapes consumed by the four
§5 Step range lemmas.  `prop51_R_floor`, `prop51_hreg`, `prop51_Δ_floor` are the small
regime derivations shared by the per-pair assembly.
-/

open Classical Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- The choice function selecting the `RaWitness` defect for each `r` (and `0` off the
witnessed set). -/
noncomputable def dStarOf (P : Globals) (S : Scale P) (a : ℤ) : ℕ → ℤ :=
  fun r => if h : RaWitness P S a r then h.choose else 0

/-- The defining property of `dStarOf` on witnessed points. -/
theorem dStarOf_spec {a : ℤ} {r : ℕ} (h : RaWitness P S a r) :
    inDa P.X P.H a (dStarOf P S a r) ∧
      S.D ≤ (dStarOf P S a r : ℝ) ∧ (dStarOf P S a r : ℝ) ≤ 2 * S.D ∧
      |Rfun P.X (a : ℝ) (dStarOf P S a r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
      (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R := by
  unfold dStarOf
  rw [dif_pos h]
  exact h.choose_spec

/-- The `hdStar` bundle (Steps 1–3 shape) from the `RaWitness` hypothesis. -/
theorem witness_hdStar {a : ℤ} {Ra : Finset ℕ}
    (hRa : ∀ r ∈ Ra, RaWitness P S a r) :
    ∀ r ∈ Ra, inDa P.X P.H a (dStarOf P S a r) ∧
      S.D ≤ (dStarOf P S a r : ℝ) ∧ (dStarOf P S a r : ℝ) ≤ 2 * S.D ∧
      |Rfun P.X (a : ℝ) (dStarOf P S a r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
      (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R :=
  fun r hr => dStarOf_spec (hRa r hr)

/-- `Δ > 28` (for `dstar_ne_of_gap`), from `hDeW`. -/
theorem prop51_Δ28 (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) : (28 : ℝ) < S.Δ := by
  have h4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
  have h20 : (1:ℝ) ≤ P.U ^ 20 := one_le_pow₀ hU1
  nlinarith [h4, h20]

/-- The `hwin` bundle (Steps 2–3 shape) from the `RaWitness` hypothesis: window data at
`r+ℓ₁`, `r+ℓ₂` plus distinctness of the witness defects. -/
theorem witness_hwin {a : ℤ} {Ra : Finset ℕ} {ℓ₁ ℓ₂ : ℕ}
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hRa : ∀ r ∈ Ra, RaWitness P S a r) :
    ∀ r ∈ Ra, (r + ℓ₁ ∈ Ra) → (r + ℓ₂ ∈ Ra) →
      (S.D ≤ (dStarOf P S a (r + ℓ₁) : ℝ) ∧ (dStarOf P S a (r + ℓ₁) : ℝ) ≤ 2 * S.D) ∧
      (S.D ≤ (dStarOf P S a (r + ℓ₂) : ℝ) ∧ (dStarOf P S a (r + ℓ₂) : ℝ) ≤ 2 * S.D) ∧
      |Rfun P.X (a : ℝ) (dStarOf P S a (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))|
          ≤ 14 * P.H / S.D ∧
      |Rfun P.X (a : ℝ) (dStarOf P S a (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))|
          ≤ 14 * P.H / S.D ∧
      (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R ∧ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R ∧
      (dStarOf P S a (r + ℓ₁) : ℝ) ≠ (dStarOf P S a r : ℝ) ∧
      (dStarOf P S a (r + ℓ₂) : ℝ) ≠ (dStarOf P S a r : ℝ) := by
  intro r hr hr1 hr2
  obtain ⟨_, _, _, hRd, _, _⟩ := dStarOf_spec (hRa r hr)
  obtain ⟨_, hw1lo, hw1hi, hRd1, _, hhi1⟩ := dStarOf_spec (hRa (r + ℓ₁) hr1)
  obtain ⟨_, hw2lo, hw2hi, hRd2, _, hhi2⟩ := dStarOf_spec (hRa (r + ℓ₂) hr2)
  have hc1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
  have hc2 : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
  rw [hc1] at hRd1 hhi1
  rw [hc2] at hRd2 hhi2
  have hΔ28 := prop51_Δ28 (P := P) (S := S) hG1 hU1 hDeW
  have hgap1 : (1 : ℝ) ≤ |((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) - (r : ℝ)| := by
    have : ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) - (r : ℝ) = ((ℓ₁ : ℤ) : ℝ) := by ring
    rw [this, abs_of_nonneg (by positivity)]
    exact_mod_cast hℓ1
  have hgap2 : (1 : ℝ) ≤ |((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) - (r : ℝ)| := by
    have : ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) - (r : ℝ) = ((ℓ₂ : ℤ) : ℝ) := by ring
    rw [this, abs_of_nonneg (by positivity)]
    exact_mod_cast lt_trans hℓ1 hℓ12
  have hne1 : dStarOf P S a r ≠ dStarOf P S a (r + ℓ₁) :=
    dstar_ne_of_gap (S := S) hΔ28 hgap1 hRd hRd1
  have hne2 : dStarOf P S a r ≠ dStarOf P S a (r + ℓ₂) :=
    dstar_ne_of_gap (S := S) hΔ28 hgap2 hRd hRd2
  exact ⟨⟨hw1lo, hw1hi⟩, ⟨hw2lo, hw2hi⟩, hRd1, hRd2, hhi1, hhi2,
    by exact_mod_cast hne1.symm, by exact_mod_cast hne2.symm⟩

/-- `Δ ≥ 10⁹³` from `hDeW` + `U ≥ 10³³`. -/
theorem prop51_Δ_floor (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) : (10 : ℝ) ^ 93 ≤ S.Δ := by
  have hU2 : (10:ℝ) ^ 66 ≤ P.U ^ 2 := by
    calc (10:ℝ) ^ 66 = ((10:ℝ) ^ 33) ^ 2 := by rw [← pow_mul]
      _ ≤ P.U ^ 2 := pow_le_pow_left₀ (by positivity) hUbig 2
  have hU20 : (10:ℝ) ^ 66 ≤ P.U ^ 20 := by
    calc (10:ℝ) ^ 66 ≤ P.U ^ 2 := hU2
      _ ≤ P.U ^ 20 := pow_le_pow_right₀ hU1 (by norm_num)
  have h4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
  calc (10:ℝ) ^ 93 = 10 ^ 27 * (1 * 10 ^ 66) := by norm_num
    _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
        have := mul_le_mul h4 hU20 (by positivity) (by positivity)
        nlinarith [this]
    _ ≤ S.Δ := hDeW

/-- **The `R`-floor** `10¹¹³·G·U⁵ ≤ R`: the pair window `ℓ ≤ 130·W` is microscopic
against the `r`-range `≍ R`.  Covers `hsmall` (Step 2), the Markov `8W ≤ R`, and the
`r₀ ≤ r₁` window fact. -/
theorem prop51_R_floor (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hΩU : S.Ω ≤ P.U)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    10 ^ 113 * (P.G * P.U ^ 5) ≤ S.R := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hH : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := (le_div_iff₀ (by positivity)).mp h1
  have hpay3 : (1:ℝ) ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := band_pay3 (P := P) (S := S) hband hΩU
  have hΔ93 := prop51_Δ_floor (P := P) (S := S) hG1 hU1 hUbig hDeW
  have hUΔ : (10:ℝ) ^ 113 ≤ P.U * S.Δ := by
    have hU20' : (10:ℝ) ^ 20 ≤ P.U := le_trans (by norm_num) hUbig
    calc (10:ℝ) ^ 113 = 10 ^ 20 * 10 ^ 93 := by rw [← pow_add]
      _ ≤ P.U * S.Δ := mul_le_mul hU20' hΔ93 (by positivity) hUpos.le
  rw [Scale.R, le_div_iff₀ hΔpos]
  calc 10 ^ 113 * (P.G * P.U ^ 5) * S.Δ
      = 10 ^ 113 * (P.G * P.U ^ 5 * S.Δ) := by ring
    _ ≤ (P.U * S.Δ) * (P.G * P.U ^ 5 * S.Δ) :=
        mul_le_mul_of_nonneg_right hUΔ (by positivity)
    _ = 1 * (P.G * P.U ^ 6 * S.Δ ^ 2) := by ring
    _ ≤ (P.G * P.U ^ 4 * S.Ω ^ 3) * (P.G * P.U ^ 6 * S.Δ ^ 2) :=
        mul_le_mul_of_nonneg_right hpay3 (by positivity)
    _ = P.G * P.U ^ 10 * S.Δ ^ 2 * (P.G * S.Ω ^ 3) := by ring
    _ ≤ P.H * (P.G * S.Ω ^ 3) := mul_le_mul_of_nonneg_right hH (by positivity)
    _ = P.H * P.G * S.Ω ^ 3 := by ring

/-- The capstone regime fact `Δ²·U⁵ ≤ H·Ω³` from `hHbig` (squared comparison) + `Ω ≤ U`. -/
theorem prop51_hreg (hΩU : S.Ω ≤ P.U) (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14) :
    S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  -- squared form: `Δ⁴U¹⁰ ≤ H²Ω⁶`
  have hsq : (S.Δ ^ 2 * P.U ^ 5) ^ 2 ≤ (P.H * S.Ω ^ 3) ^ 2 := by
    have hΩ8 : S.Ω ^ 8 ≤ P.U ^ 8 := pow_le_pow_left₀ hΩpos.le hΩU 8
    have hG5 : (1:ℝ) ≤ P.G ^ 5 := one_le_pow₀ hG1
    have hU27 : (1:ℝ) ≤ P.U ^ 27 := one_le_pow₀ hU1
    -- `H²Ω⁶·U⁸ ≥ H²Ω¹⁴ ≥ 10¹²¹Δ⁴G⁵U⁴⁵ ≥ Δ⁴U¹⁰·U⁸`
    have key : P.H ^ 2 * S.Ω ^ 14 ≤ P.H ^ 2 * S.Ω ^ 6 * P.U ^ 8 := by
      have : S.Ω ^ 14 = S.Ω ^ 6 * S.Ω ^ 8 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hΩ8
        (show (0:ℝ) ≤ P.H ^ 2 * S.Ω ^ 6 by positivity)
      nlinarith [this]
    have low : S.Δ ^ 4 * P.U ^ 10 * P.U ^ 8 ≤ 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) := by
      have hU45 : P.U ^ 10 * P.U ^ 8 = P.U ^ 18 := by ring
      have h18 : P.U ^ 18 ≤ P.U ^ 45 := pow_le_pow_right₀ hU1 (by norm_num)
      have hc : S.Δ ^ 4 * P.U ^ 18 ≤ 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) := by
        nlinarith [mul_le_mul_of_nonneg_left h18 (show (0:ℝ) ≤ S.Δ ^ 4 by positivity),
          mul_le_mul_of_nonneg_left hG5 (show (0:ℝ) ≤ S.Δ ^ 4 * P.U ^ 45 by positivity),
          pow_pos hΔpos 4, pow_pos hUpos 45]
      calc S.Δ ^ 4 * P.U ^ 10 * P.U ^ 8 = S.Δ ^ 4 * P.U ^ 18 := by ring
        _ ≤ 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) := hc
    have hU8pos : (0:ℝ) < P.U ^ 8 := pow_pos hUpos 8
    have chain : (S.Δ ^ 2 * P.U ^ 5) ^ 2 * P.U ^ 8 ≤ (P.H * S.Ω ^ 3) ^ 2 * P.U ^ 8 := by
      calc (S.Δ ^ 2 * P.U ^ 5) ^ 2 * P.U ^ 8 = S.Δ ^ 4 * P.U ^ 10 * P.U ^ 8 := by ring
        _ ≤ 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) := low
        _ ≤ P.H ^ 2 * S.Ω ^ 14 := hHbig
        _ ≤ P.H ^ 2 * S.Ω ^ 6 * P.U ^ 8 := key
        _ = (P.H * S.Ω ^ 3) ^ 2 * P.U ^ 8 := by ring
    exact le_of_mul_le_mul_right chain hU8pos
  have hL : (0:ℝ) ≤ S.Δ ^ 2 * P.U ^ 5 := by positivity
  have hR : (0:ℝ) ≤ P.H * S.Ω ^ 3 := by positivity
  nlinarith [hsq, hL, hR]

/-- `10·A ≤ D` from `60·Ω ≤ H`. -/
theorem prop51_hAD (hΩH : 60 * S.Ω ≤ P.H) : 10 * S.A ≤ S.D := by
  have hΔpos := S.Δ_pos
  rw [Scale.A, Scale.D]
  nlinarith [hΩH, hΔpos, S.Ω_pos]

end Squarefree
