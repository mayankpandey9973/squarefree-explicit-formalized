import Squarefree.Lower.Step1Count

/-!
# §5 Step-1 subset → count step (writeup 852–855)

A subset `T ⊆ Ra` of "v=0 consecutive triples", whose every element `r` lies in the window
`[r₀, r₁]` and has `‖φ(r)‖ ≤ δ`, injects (ℕ → ℤ) into the smooth-count filter, so
`#T ≤ step1_smooth_count`.  This is a clean Finset-cardinality + injection argument.
-/

namespace Squarefree

open Squarefree.Counting

theorem step1_subset_count {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hr0_lo : (1/72) * S.R ≤ r₀) (_hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : 0 ≤ δ)
    (T : Finset ℕ)
    (hT : ∀ r ∈ T, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phi P.X a ℓ₁ ℓ₂ (r : ℝ)) ≤ δ) :
    (T.card : ℝ)
      ≤ (10 ^ 20 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) + 2 * δ + 1)
        * (2 * δ / (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30)) + 1) := by
  set Q : Finset ℤ := (Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
    (fun (n : ℤ) => Counting.distInt (phi P.X a ℓ₁ ℓ₂ (n : ℝ)) ≤ δ) with hQ_def
  -- the ℕ→ℤ cast is injective
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun a b h => by
    simpa using h
  -- `T.image (↑·) ⊆ Q`
  have hsubset : T.image (fun n : ℕ => (n : ℤ)) ⊆ Q := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hrT, rfl⟩ := hz
    obtain ⟨hlo, hhi, hdist⟩ := hT r hrT
    rw [hQ_def, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- ⌈r₀⌉ ≤ (r : ℤ)
      rw [Int.ceil_le]; push_cast; exact hlo
    · -- (r : ℤ) ≤ ⌊r₁⌋
      rw [Int.le_floor]; push_cast; exact hhi
    · -- distInt (phi … ((r:ℤ):ℝ)) ≤ δ
      have : ((r : ℤ) : ℝ) = (r : ℝ) := by push_cast; ring
      rw [this]; exact hdist
  -- card bound
  have hcard : T.card ≤ Q.card := by
    calc T.card = (T.image (fun n : ℕ => (n : ℤ))).card :=
          (Finset.card_image_of_injective T hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  calc (T.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := step1_smooth_count hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hsmall hr0_lo hr1_hi hδ

end Squarefree
