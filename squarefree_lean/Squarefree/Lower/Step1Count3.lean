import Squarefree.Lower.Step1Count2
import Squarefree.Lower.Step1Witness

/-!
# §5 Step-1 v=0 per-pair count (writeup 840–845)

`step1_v0_count`: for a fixed gap pair `(ℓ₁,ℓ₂)`, any finset `T` of starts of `v=0`
witnessed triples has
`#T ≤ step1_subset_count`'s bound with `δ := δ_unif = 10⁶⁰·(1/Δ)G³U¹⁵/Ω⁵`.

Each `r ∈ T` carries (via `hT`) the three `D`-scale witnesses `d,d₁,d₂` of its
triple; `phi_distInt_from_witness` turns those into `distInt(φ(r)) ≤ δ_unif`, and
`step1_subset_count` does the rest. The remaining work for `prop_5_1` is to build
`T` (and prove `hT`) from `RaWitness` + pigeonhole.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **Step-1 v=0 per-pair count.** -/
theorem step1_v0_count {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℤ}
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (T : Finset ℕ)
    (hT : ∀ r ∈ T, ∃ d d₁ d₂ : ℤ,
        inDa P.X P.H a d ∧ inDa P.X P.H a d₁ ∧ inDa P.X P.H a d₂ ∧
        (S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2*S.D) ∧ (S.D ≤ (d₁:ℝ) ∧ (d₁:ℝ) ≤ 2*S.D) ∧
        (S.D ≤ (d₂:ℝ) ∧ (d₂:ℝ) ≤ 2*S.D) ∧
        |Rfun P.X (a:ℝ) (d:ℝ) - (r:ℝ)| ≤ 14 * P.H / S.D ∧
        |Rfun P.X (a:ℝ) (d₁:ℝ) - ((r:ℝ) + (ℓ₁:ℝ))| ≤ 14 * P.H / S.D ∧
        (ℓ₁:ℝ) * ((d₂:ℝ) - (d:ℝ)) = (ℓ₂:ℝ) * ((d₁:ℝ) - (d:ℝ)) ∧
        (d₁:ℝ) ≠ (d:ℝ) ∧
        (1/72) * S.R ≤ (r:ℝ) ∧ (r:ℝ) + (ℓ₁:ℝ) ≤ 16 * S.R) :
    (T.card : ℝ) ≤
      (10 ^ 20 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) / (P.G * S.Ω ^ 5))
          + 2 * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5)) + 1)
        * (2 * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5))
            / ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)) + 1) := by
  -- positivity of R
  have hR : 0 < S.R := by rw [Scale.R]; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  -- real casts
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : (0 : ℝ) < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  -- `R ≥ U·W`, `W = G·U⁵`
  have hRUW : 130 * (P.U * P.Wval) ≤ S.R :=
    U_mul_W130_le_R (P := P) (S := S) h1 hband hΩU hΔ1 hU1 hUbig hG1
  have hWpos : (0 : ℝ) < P.Wval := by rw [Globals.Wval]; have := P.G_pos; positivity
  -- `(ℓ₁:ℝ) ≤ 130 * P.Wval`
  have hℓ1W : (ℓ₁ : ℝ) ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12R) hℓ2W
  -- `hsmall : 10^33 * ℓ₁ ≤ R`
  have hsmall : (10 : ℝ) ^ 33 * (ℓ₁ : ℝ) ≤ S.R := by
    calc (10 : ℝ) ^ 33 * (ℓ₁ : ℝ)
        ≤ (10 : ℝ) ^ 33 * (130 * P.Wval) := by
          apply mul_le_mul_of_nonneg_left hℓ1W (by positivity)
      _ ≤ P.U * (130 * P.Wval) := by
          apply mul_le_mul_of_nonneg_right hUbig (by positivity)
      _ = 130 * (P.U * P.Wval) := by ring
      _ ≤ S.R := hRUW
  -- `(ℓ₁:ℝ) ≤ R` (since 10^33 ≥ 1 and ℓ₁ ≥ 0)
  have hℓ1le_R : (ℓ₁ : ℝ) ≤ S.R := by nlinarith [hsmall, hℓ1R]
  -- window endpoints
  have hr01 : (1 / 72) * S.R ≤ 16 * S.R - (ℓ₁ : ℝ) := by nlinarith [hR, hℓ1le_R]
  have hr1_hi : (16 * S.R - (ℓ₁ : ℝ)) + (ℓ₁ : ℝ) ≤ 16 * S.R := by linarith
  -- δ ≥ 0
  have hδ : (0 : ℝ) ≤ (10 : ℝ) ^ 60 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 15 / S.Ω ^ 5) := by
    have := P.G_pos; have := P.U_pos; have := S.Δ_pos; have := S.Ω_pos; positivity
  -- per-element window + distInt bound
  have hT' : ∀ r ∈ T, (1 / 72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R - (ℓ₁ : ℝ) ∧
      Counting.distInt (phi P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) (r : ℝ))
        ≤ (10 : ℝ) ^ 60 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 15 / S.Ω ^ 5) := by
    intro r hr
    obtain ⟨d, d₁, d₂, hin, hin1, hin2, hdwin, hd1win, hd2win, hRd, hRd1, hv0, hbne, hrlo, hrhi⟩ :=
      hT r hr
    refine ⟨hrlo, by linarith [hℓ1R], ?_⟩
    exact phi_distInt_from_witness hAD ha0 ha_lo ha_hi hℓ1 hℓ1_lo hℓ12 hℓ2W hrlo hrhi
      hin hin1 hin2 hdwin hd1win hd2win hRd hRd1 hv0 hbne h1 hband hG1 hU1 hΔ1 hUH hΩU hUbig
  exact step1_subset_count hAD haR ha_lo ha_hi hℓ1R hℓ12R hsmall (le_refl _) hr01 hr1_hi hδ T hT'

end Squarefree
