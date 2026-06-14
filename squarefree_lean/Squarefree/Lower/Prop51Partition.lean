import Squarefree.Params
import Mathlib

/-!
# §5 the `v`-range partition of the per-pair fiber (writeup §5 step structure)

Structural backbone of the §5 `v`-range partition. `vval` is the per-`r` defect

```
v(r) = (d*(r+ℓ₂) − d*(r)) − (ℓ₂/ℓ₁)·(d*(r+ℓ₁) − d*(r)),
```

matching the `hVplus` argument of `Qval_abs_le_from_witness` (`Step3QWitness.lean`).

`fiber_le_sum_ranges` is the pure-Finset **cover** lemma: the card of the predicate-free
pair-fiber `{r ∈ Ra : r+ℓ₁ ∈ Ra ∧ r+ℓ₂ ∈ Ra}` is bounded by the sum of the four
`v`-range cards (`v=0`, `0<|v|≤V₁`, `V₁<|v|≤V₂`, `V₂<|v|`). The four predicates are a
total cover of the fiber by trichotomy on `v` versus `0, V₁, V₂`; no disjointness is needed
because the conclusion is a `≤` (the boundary cases at `V₁, V₂` are harmless). The
per-range bounds are deferred to the Step lemmas.
-/

namespace Squarefree

open Finset

variable {P : Globals} {S : Scale P}

/-- **§5 per-`r` defect** `v(r)`. Matches the `hVplus` argument of
`Qval_abs_le_from_witness`: the cast shape is
`(d*(r+ℓ₂) − d*(r)) − (ℓ₂/ℓ₁)·(d*(r+ℓ₁) − d*(r))`. -/
noncomputable def vval (P : Globals) (a : ℤ) (dStar : ℕ → ℤ) (ℓ₁ ℓ₂ r : ℕ) : ℝ :=
  ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ))
    - ((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ) * ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ))

/-- Chain of three `Finset.card_union_le` to bound the card of a 4-fold union by the sum of
the four cards. -/
private lemma card_union4_le {α : Type*} [DecidableEq α] (s₁ s₂ s₃ s₄ : Finset α) :
    (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card ≤ s₁.card + s₂.card + s₃.card + s₄.card := by
  calc (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card
      ≤ (s₁ ∪ s₂ ∪ s₃).card + s₄.card := Finset.card_union_le _ _
    _ ≤ ((s₁ ∪ s₂).card + s₃.card) + s₄.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((s₁.card + s₂.card) + s₃.card) + s₄.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _

/-- **§5 `v`-range cover.** The predicate-free pair-fiber is covered by the four `v`-ranges
`v=0`, `0<|v|≤V₁`, `V₁<|v|≤V₂`, `V₂<|v|`, so its card is `≤` the sum of the four range
cards. Pure structural cover; per-range bounds deferred to the Step lemmas. -/
theorem fiber_le_sum_ranges (Ra : Finset ℕ) (a : ℤ) (dStar : ℕ → ℤ) (ℓ₁ ℓ₂ : ℕ) (V₁ V₂ : ℝ) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra))).card : ℝ)
      ≤ ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ vval P a dStar ℓ₁ ℓ₂ r = 0)).card : ℝ)
        + ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ 0 < |vval P a dStar ℓ₁ ℓ₂ r| ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₁)).card : ℝ)
        + ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ V₁ < |vval P a dStar ℓ₁ ℓ₂ r| ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₂)).card : ℝ)
        + ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ V₂ < |vval P a dStar ℓ₁ ℓ₂ r|)).card : ℝ) := by
  classical
  set s₁ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ vval P a dStar ℓ₁ ℓ₂ r = 0) with hs₁
  set s₂ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ 0 < |vval P a dStar ℓ₁ ℓ₂ r| ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₁) with hs₂
  set s₃ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ V₁ < |vval P a dStar ℓ₁ ℓ₂ r| ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₂) with hs₃
  set s₄ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ V₂ < |vval P a dStar ℓ₁ ℓ₂ r|) with hs₄
  -- The predicate-free fiber is a subset of the union of the four ranges.
  have hsub : Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)) ⊆ s₁ ∪ s₂ ∪ s₃ ∪ s₄ := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1, hr2⟩ := hr
    set vr := vval P a dStar ℓ₁ ℓ₂ r with hvr
    -- trichotomy on vr vs 0, then |vr| vs V₁, V₂
    rcases eq_or_ne vr 0 with hv0 | hvne
    · -- v = 0 : s₁
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl ?_)))))
      rw [hs₁, Finset.mem_filter]
      exact ⟨hrRa, hr1, hr2, hv0⟩
    · have hpos : 0 < |vr| := abs_pos.mpr hvne
      rcases le_or_gt |vr| V₁ with hV1 | hV1
      · -- 0 < |v| ≤ V₁ : s₂
        refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr ?_)))))
        rw [hs₂, Finset.mem_filter]
        exact ⟨hrRa, hr1, hr2, hpos, hV1⟩
      · rcases le_or_gt |vr| V₂ with hV2 | hV2
        · -- V₁ < |v| ≤ V₂ : s₃
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
          rw [hs₃, Finset.mem_filter]
          exact ⟨hrRa, hr1, hr2, hV1, hV2⟩
        · -- V₂ < |v| : s₄
          refine Finset.mem_union.mpr (Or.inr ?_)
          rw [hs₄, Finset.mem_filter]
          exact ⟨hrRa, hr1, hr2, hV2⟩
  -- card of subset ≤ card of union ≤ sum of the four cards.
  have hcard : (Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra))).card
      ≤ s₁.card + s₂.card + s₃.card + s₄.card :=
    le_trans (Finset.card_le_card hsub) (card_union4_le s₁ s₂ s₃ s₄)
  have := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at this ⊢
  linarith

end Squarefree
