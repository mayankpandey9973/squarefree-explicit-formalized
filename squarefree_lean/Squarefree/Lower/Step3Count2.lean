import Squarefree.Lower.Step3Count

/-!
# §5 Step-3 subset → count step (writeup 975–984)

A subset `T` of Step-3 triples (`r` in the window `[r₀,r₁]` with `‖φ_f(r)‖ ≤ δ` for the
fixed integer `f`) injects (ℕ → ℤ) into the smooth-count filter, so
`#T ≤ step3_smooth_count`.  Direct analogue of `step1_subset_count` with `phif`/`step3_smooth_count`.
-/

namespace Squarefree

open Squarefree.Counting

theorem step3_subset_count {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hflarge : (10:ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|)
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : 0 ≤ δ)
    (T : Finset ℕ)
    (hT : ∀ r ∈ T, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    (T.card : ℝ)
      ≤ (10 ^ 6 * (|f| * S.D ^ 4 / (P.X * S.A)) + 2 * δ + 1)
        * (2 * δ / (|f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50)) + 1) := by
  set Q : Finset ℤ := (Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
    (fun (n : ℤ) => Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (n : ℝ)) ≤ δ) with hQ_def
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun a b h => by simpa using h
  have hsubset : T.image (fun n : ℕ => (n : ℤ)) ⊆ Q := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hrT, rfl⟩ := hz
    obtain ⟨hlo, hhi, hdist⟩ := hT r hrT
    rw [hQ_def, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Int.ceil_le]; push_cast; exact hlo
    · rw [Int.le_floor]; push_cast; exact hhi
    · have : ((r : ℤ) : ℝ) = (r : ℝ) := by push_cast; ring
      rw [this]; exact hdist
  have hcard : T.card ≤ Q.card := by
    calc T.card = (T.image (fun n : ℕ => (n : ℤ))).card :=
          (Finset.card_image_of_injective T hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  calc (T.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := step3_smooth_count hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hsmall hflarge
        hr0_lo hr01 hr1_hi hδ

end Squarefree
