import Squarefree.Lower.Step4SmoothConf

/-!
# §5 Step-4 per-`(s,v)`-fibre card injection (writeup 1085–1088)

`step4_perv_card_le` is the counting injection that turns a `(s,w)`-fibre's `Finset.card`
(a set of natural `r` confined to `[r₀,r₁]`, each with `distInt(φ_w(r)) ≤ δ`) into the smooth
count over the confined interval bounded by `step4_smooth_count_conf` (`Step4SmoothConf.lean`).

The fibre `Fib ⊆ ℕ` injects via `n ↦ (n : ℤ)` into

```
{ m ∈ Finset.Icc ⌈r₀⌉ ⌊r₁⌋ : distInt (φ_w m) ≤ δ },
```

whose card is bounded by `step4_smooth_count_conf`.  Each fibre element supplies its membership
`r₀ ≤ r ≤ r₁` and its per-`r` near-integer witness `distInt(φ_w r) ≤ δ` (the latter threaded by
`phiv_distInt_from_witness` in the downstream `Step4RangeFinal`), exactly mirroring
`step2_subset_count`'s `Step2Bands.lean` injection idiom.
-/

open Finset Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 1600000

/-- **§5 Step-4 per-`(s,v)`-fibre card injection.**  A finite set `Fib ⊆ ℕ` of admissible `r`,
each lying in the confined interval `[r₀,r₁] ⊆ [R/72, 16R]` and satisfying the per-`r` near-integer
witness `distInt(φ_w(r)) ≤ δ`, injects into `step4_smooth_count_conf`'s filtered `Finset.Icc`, so
its card is bounded by the confined smooth count
`(10¹³·W·(r₁−r₀) + 2δ + 1)(2δ/F + 1)`, `W = ℓ₁Xa|w|/(D⁴R)`, `F = W/10⁵⁰`. -/
theorem step4_perv_card_le {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ w r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hvlarge : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |w|)
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : 0 ≤ δ)
    (Fib : Finset ℕ)
    (hFib : ∀ r ∈ Fib, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
        distInt (phiv P.X a ℓ₁ ℓ₂ w (r : ℝ)) ≤ δ) :
    (Fib.card : ℝ)
      ≤ (10 ^ 13 * (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) * (r₁ - r₀) + 2 * δ + 1)
        * (2 * δ / (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R * 10 ^ 50)) + 1) := by
  classical
  -- the smooth-count filtered base over the confined interval `[r₀,r₁]`.
  set Q : Finset ℤ := (Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
    (fun (m : ℤ) => distInt (phiv P.X a ℓ₁ ℓ₂ w (m : ℝ)) ≤ δ) with hQ_def
  -- the fibre injects into `Q` via `n ↦ (n : ℤ)`.
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun x y h => by simpa using h
  have hsubset : Fib.image (fun n : ℕ => (n : ℤ)) ⊆ Q := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hrF, rfl⟩ := hz
    obtain ⟨hlo, hhi, hdist⟩ := hFib r hrF
    rw [hQ_def, Finset.mem_filter, Finset.mem_Icc]
    have hclo : ⌈r₀⌉ ≤ (r : ℤ) := by rw [Int.ceil_le]; push_cast; exact hlo
    have hchi : (r : ℤ) ≤ ⌊r₁⌋ := by rw [Int.le_floor]; push_cast; exact hhi
    refine ⟨⟨hclo, hchi⟩, ?_⟩
    have hcast : (((r : ℤ) : ℝ)) = (r : ℝ) := by push_cast; ring
    rw [hcast]; exact hdist
  have hcard : Fib.card ≤ Q.card := by
    calc Fib.card = (Fib.image (fun n : ℕ => (n : ℤ))).card :=
          (Finset.card_image_of_injective Fib hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  -- the confined smooth count bounds `Q.card`.
  have hsmooth := step4_smooth_count_conf (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (v := w) (r₀ := r₀) (r₁ := r₁) (δ := δ)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hvlarge hr0_lo hr01 hr1_hi hδ
  calc (Fib.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ ≤ (10 ^ 13 * (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) * (r₁ - r₀) + 2 * δ + 1)
        * (2 * δ / (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R * 10 ^ 50)) + 1) := hsmooth

end Squarefree
