import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# §5 Step-2 φ″-zero count — abstract two-pieces splitting lemma

This is the *decoupled* final calculus step of the §5 Step-2 φ″-zero count.  It takes the
strict monotonicity of the zero-locus function `m` as a hypothesis, so it is independent of
the heavy Wronskian algebra (`Step2D2ZeroAux`).

Setup (instantiated by the count chain): on a band `[r₀,r₁]`, a C² function `g` (= `φ_f`) has
`g'' = ψ₂·(f − m)` with `ψ₂ > 0` and `m` strictly monotone.  Then `g''` is `+`-then-`−`
(since `f − m` decreases through `0`), so `g' = deriv g` is monotone-up-then-down.

Main result: `deriv_two_pieces_of_strictMono` — there is a split point `z ∈ [r₀,r₁]` with
`deriv g` `MonotoneOn [r₀,z]` and `AntitoneOn [z,r₁]`.  The split point is where `m` crosses
`f` (via the intermediate value theorem); if `m ≥ f` throughout then `z = r₀`, and if
`m ≤ f` throughout then `z = r₁`.
-/

open Set

namespace Squarefree

/-- Monotone piece: on `[a,b]`, if `g'' = ψ₂·(f − m) ≥ 0` (because `m ≤ f`) then `deriv g`
is monotone. -/
private lemma deriv_monotoneOn_of_le {g m ψ2 : ℝ → ℝ} {f a b : ℝ}
    (hcont : ContinuousOn (deriv g) (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv g) x)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < ψ2 x)
    (hg2 : ∀ x ∈ Set.Ioo a b, deriv (deriv g) x = ψ2 x * (f - m x))
    (hsign : ∀ x ∈ Set.Ioo a b, m x ≤ f) :
    MonotoneOn (deriv g) (Set.Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hdiff x hx).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [hg2 x hx]
    exact mul_nonneg (hpos x hx).le (by linarith [hsign x hx])

/-- Antitone piece: on `[a,b]`, if `g'' = ψ₂·(f − m) ≤ 0` (because `f ≤ m`) then `deriv g`
is antitone. -/
private lemma deriv_antitoneOn_of_ge {g m ψ2 : ℝ → ℝ} {f a b : ℝ}
    (hcont : ContinuousOn (deriv g) (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv g) x)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < ψ2 x)
    (hg2 : ∀ x ∈ Set.Ioo a b, deriv (deriv g) x = ψ2 x * (f - m x))
    (hsign : ∀ x ∈ Set.Ioo a b, f ≤ m x) :
    AntitoneOn (deriv g) (Set.Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hdiff x hx).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [hg2 x hx]
    exact mul_nonpos_of_nonneg_of_nonpos (hpos x hx).le (by linarith [hsign x hx])

/-- Assemble the two pieces from a split point `z ∈ [r₀,r₁]` with the sign data on each side. -/
private lemma deriv_two_pieces_assemble {g m ψ2 : ℝ → ℝ} {f r₀ r₁ z : ℝ}
    (hcont : ContinuousOn (deriv g) (Set.Icc r₀ r₁))
    (hdiff : ∀ x ∈ Set.Ioo r₀ r₁, DifferentiableAt ℝ (deriv g) x)
    (hpos : ∀ x ∈ Set.Icc r₀ r₁, 0 < ψ2 x)
    (hg2 : ∀ x ∈ Set.Icc r₀ r₁, deriv (deriv g) x = ψ2 x * (f - m x))
    (hz : z ∈ Set.Icc r₀ r₁)
    (hleft : ∀ x ∈ Set.Ioo r₀ z, m x ≤ f)
    (hright : ∀ x ∈ Set.Ioo z r₁, f ≤ m x) :
    ∃ w, w ∈ Set.Icc r₀ r₁ ∧ MonotoneOn (deriv g) (Set.Icc r₀ w) ∧
      AntitoneOn (deriv g) (Set.Icc w r₁) := by
  refine ⟨z, hz, ?_, ?_⟩
  · -- monotone on `[r₀,z]`
    refine deriv_monotoneOn_of_le
      (hcont.mono (Set.Icc_subset_Icc_right hz.2))
      (fun x hx => hdiff x (Set.Ioo_subset_Ioo_right hz.2 hx))
      (fun x hx => hpos x ⟨hx.1.le, le_trans hx.2.le hz.2⟩)
      (fun x hx => hg2 x ⟨hx.1.le, le_trans hx.2.le hz.2⟩)
      hleft
  · -- antitone on `[z,r₁]`
    refine deriv_antitoneOn_of_ge
      (hcont.mono (Set.Icc_subset_Icc_left hz.1))
      (fun x hx => hdiff x (Set.Ioo_subset_Ioo_left hz.1 hx))
      (fun x hx => hpos x ⟨le_trans hz.1 hx.1.le, hx.2.le⟩)
      (fun x hx => hg2 x ⟨le_trans hz.1 hx.1.le, hx.2.le⟩)
      hright

/-- **Abstract two-pieces lemma.**  Let `g` be `C²` on `[r₀,r₁]` (given here as continuity of
`deriv g` plus differentiability of `deriv g` on the interior), with second derivative
`deriv (deriv g) = ψ₂·(f − m)` where `ψ₂ > 0` and `m` is `StrictMonoOn [r₀,r₁]` and continuous.
Then there is a split point `z ∈ [r₀,r₁]` with `deriv g` monotone on `[r₀,z]` and antitone on
`[z,r₁]`.  (`z` is where `m` crosses `f`; if `m ≥ f` throughout then `z = r₀`, if `m ≤ f`
throughout then `z = r₁`.) -/
theorem deriv_two_pieces_of_strictMono {g m ψ2 : ℝ → ℝ} {f r₀ r₁ : ℝ}
    (hr : r₀ ≤ r₁)
    (hcont : ContinuousOn (deriv g) (Set.Icc r₀ r₁))
    (hdiff : ∀ x ∈ Set.Ioo r₀ r₁, DifferentiableAt ℝ (deriv g) x)
    (hpos : ∀ x ∈ Set.Icc r₀ r₁, 0 < ψ2 x)
    (hg2 : ∀ x ∈ Set.Icc r₀ r₁, deriv (deriv g) x = ψ2 x * (f - m x))
    (hmcont : ContinuousOn m (Set.Icc r₀ r₁))
    (hm : StrictMonoOn m (Set.Icc r₀ r₁)) :
    ∃ z, z ∈ Set.Icc r₀ r₁ ∧ MonotoneOn (deriv g) (Set.Icc r₀ z) ∧
      AntitoneOn (deriv g) (Set.Icc z r₁) := by
  have hr0mem : r₀ ∈ Set.Icc r₀ r₁ := ⟨le_refl _, hr⟩
  have hr1mem : r₁ ∈ Set.Icc r₀ r₁ := ⟨hr, le_refl _⟩
  rcases le_or_gt f (m r₀) with hA | hA
  · -- `f ≤ m r₀`: `m ≥ f` throughout, split at `z = r₀` (all antitone)
    refine deriv_two_pieces_assemble hcont hdiff hpos hg2 hr0mem ?_ ?_
    · intro x hx; exact absurd (hx.1.trans hx.2) (lt_irrefl _)
    · intro x hx
      have hxmem : x ∈ Set.Icc r₀ r₁ := ⟨hx.1.le, hx.2.le⟩
      exact hA.trans (hm hr0mem hxmem hx.1).le
  · rcases le_or_gt (m r₁) f with hB | hB
    · -- `m r₁ ≤ f`: `m ≤ f` throughout, split at `z = r₁` (all monotone)
      refine deriv_two_pieces_assemble hcont hdiff hpos hg2 hr1mem ?_ ?_
      · intro x hx
        have hxmem : x ∈ Set.Icc r₀ r₁ := ⟨hx.1.le, hx.2.le⟩
        exact (hm hxmem hr1mem hx.2).le.trans hB
      · intro x hx; exact absurd (hx.1.trans hx.2) (lt_irrefl _)
    · -- `m r₀ < f < m r₁`: interior crossing by IVT
      have hf_mem : f ∈ Set.Icc (m r₀) (m r₁) := ⟨hA.le, hB.le⟩
      obtain ⟨z, hz, hmz⟩ := intermediate_value_Icc hr hmcont hf_mem
      refine deriv_two_pieces_assemble hcont hdiff hpos hg2 hz ?_ ?_
      · intro x hx
        have hxmem : x ∈ Set.Icc r₀ r₁ := ⟨hx.1.le, le_trans hx.2.le hz.2⟩
        have := hm hxmem hz hx.2
        rw [hmz] at this
        exact this.le
      · intro x hx
        have hxmem : x ∈ Set.Icc r₀ r₁ := ⟨le_trans hz.1 hx.1.le, hx.2.le⟩
        have := hm hz hxmem hx.1
        rw [hmz] at this
        exact this.le

end Squarefree
