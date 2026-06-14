import Squarefree.Lower.Prop51Partition
import Squarefree.Structure.DaSpacing

/-!
# §5 assembly bridges

Two small bridges for the §5 pair-sum assembly:
* `step1_filter_bridge` — the `vval = 0` filter is a subset of the ℤ-equation
  filter consumed by `Ra_step1_v0_perpair`.
* `dstar_distinct` / `dstar_ne_of_gap` — distinctness of `dStar` values from
  the `RaWitness` window `|Rfun − r| ≤ 14H/D` (triangle inequality, then
  `28/Δ < 1`).
-/

open Classical Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **Step-1 filter bridge**: the `vval = 0` fiber filter is at most the
ℤ-equation filter of `Ra_step1_v0_perpair`. -/
theorem step1_filter_bridge (Ra : Finset ℕ) (a : ℤ) (dStar : ℕ → ℤ)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) :
    (Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        vval P a dStar ℓ₁ ℓ₂ r = 0)).card
      ≤ (Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        (ℓ₁ : ℤ) * (dStar (r + ℓ₂) - dStar r)
          = (ℓ₂ : ℤ) * (dStar (r + ℓ₁) - dStar r))).card := by
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  obtain ⟨hrRa, h1, h2, hv⟩ := hr
  refine ⟨hrRa, h1, h2, ?_⟩
  unfold vval at hv
  have hℓ : ((ℓ₁ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hℓ1.ne'
  field_simp at hv
  have hZ : (dStar (r + ℓ₂) - dStar r) * (ℓ₁ : ℤ)
      - (ℓ₂ : ℤ) * (dStar (r + ℓ₁) - dStar r) = (ℓ₁ : ℤ) * 0 := by exact_mod_cast hv
  linear_combination hZ

/-- **Window distinctness, triangle step**: two `RaWitness`-style windows with the same
`d` force `|r' − r| ≤ 28H/D`. -/
theorem dstar_distinct {a : ℤ} {d₁ d₂ : ℤ} {r r' : ℝ}
    (h₁ : |Rfun P.X (a : ℝ) (d₁ : ℝ) - r| ≤ 14 * P.H / S.D)
    (h₂ : |Rfun P.X (a : ℝ) (d₂ : ℝ) - r'| ≤ 14 * P.H / S.D)
    (hd : d₁ = d₂) : |r' - r| ≤ 28 * P.H / S.D := by
  subst hd
  calc |r' - r|
      ≤ |r' - Rfun P.X (a : ℝ) (d₁ : ℝ)| + |Rfun P.X (a : ℝ) (d₁ : ℝ) - r| :=
        abs_sub_le _ _ _
    _ = |Rfun P.X (a : ℝ) (d₁ : ℝ) - r'| + |Rfun P.X (a : ℝ) (d₁ : ℝ) - r| := by
        rw [abs_sub_comm]
    _ ≤ 14 * P.H / S.D + 14 * P.H / S.D := add_le_add h₂ h₁
    _ = 28 * P.H / S.D := by ring

/-- **Distinctness corollary**: with `28 < Δ` (so `28H/D = 28/Δ < 1`), windows at
`r, r'` separated by `≥ 1` cannot share the same `d`. -/
theorem dstar_ne_of_gap {a : ℤ} {d₁ d₂ : ℤ} {r r' : ℝ}
    (hΔ : 28 < S.Δ) (hgap : 1 ≤ |r' - r|)
    (h₁ : |Rfun P.X (a : ℝ) (d₁ : ℝ) - r| ≤ 14 * P.H / S.D)
    (h₂ : |Rfun P.X (a : ℝ) (d₂ : ℝ) - r'| ≤ 14 * P.H / S.D) : d₁ ≠ d₂ := by
  intro hd
  have hbound := dstar_distinct (S := S) h₁ h₂ hd
  have hDval : 28 * P.H / S.D = 28 / S.Δ := by
    have hH : P.H ≠ 0 := P.H_pos.ne'
    have hΔ0 : S.Δ ≠ 0 := S.Δ_pos.ne'
    rw [Scale.D]
    field_simp
  have hlt : 28 / S.Δ < 1 := (div_lt_one S.Δ_pos).mpr (by linarith)
  rw [hDval] at hbound
  linarith

end Squarefree
