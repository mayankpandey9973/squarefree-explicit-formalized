import Squarefree.Geometry.NearCurveStrip
import Mathlib

/-!
# §4.3 Type I / Type II classification by the PROPER-ARC (component) span

This module supplies the **faithful** Type I / Type II split of the major set.
Stage 2 of the Type I redesign: a major point `n` is Type I iff its witness
line's **proper arc** (= maximal strip component, `properArc'` from
`NearCurveStrip`) is short, `properHi' − properLo' ≤ δ√(q/λ)`.

The previous classification (`NearCurveProof`, now removed) keyed Type I on a
*per-point witness span* `(b − a) ≤ δ√(q/λ)`.  But the Type I count is over the
line's proper arc (maximal strip component), whose span can be as large as
`4√(δ/λ)` even when a witness triple is short — a `√(δ/λ)` over-count.  Keying on
the **component span** makes `properArc'_span_typeI` definitional.

Import restructure (resolving the cycle): `typeISet` needs `properArc'`, which
lives in `NearCurveStrip`; so this file imports `NearCurveStrip`, and the
downstream packing / greedy / residual layers import *this* file for
`typeISet`/`typeIISet`.  `NearCurveStrip` itself imports only `NearCurveTypeI`
(basics + `arcDensity`) + `NearCurveAux`/mathlib — no cycle.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

/-! ## The component-keyed Type I predicate -/

/-- **`n` is Type I (proper-arc/component span)**: there is a small-denominator
witness line `D` on which `n` is the middle of a near-set collinear triple
`a < n < b` (the `OnMajorArc` witness structure), **and** `D`'s proper arc (the
maximal strip component, `properArc'`) is short:
`properHi' − properLo' ≤ δ√(q/λ)`.

This is the faithful Type I condition (writeup 585): the COMPONENT — not a single
witness triple — is what the Type I packing counts. -/
def OnTypeIArc (f : ℝ → ℝ) (N lam δ : ℝ) (n : ℤ) : Prop :=
  ∃ (D : MajorLine) (a b : ℤ),
    a ∈ nearSet f N δ ∧ b ∈ nearSet f N δ ∧ n ∈ nearSet f N δ ∧
    a < n ∧ n < b ∧ OnLine f D a ∧ OnLine f D n ∧ OnLine f D b ∧
    (D.denom : ℝ) ≤ denomCutoff / δ ∧
    ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ)) ≤ δ * Real.sqrt (D.denom / (256 * lam))

/-- **Type I set** (faithful): major points whose witness line's proper arc
(component) is short. -/
noncomputable def typeISet (f : ℝ → ℝ) (N lam δ : ℝ) : Finset ℤ :=
  (majorSet f N δ).filter (OnTypeIArc f N lam δ)

/-- **Type II set**: the remaining major points (proper arc long / no short
component witness). -/
noncomputable def typeIISet (f : ℝ → ℝ) (N lam δ : ℝ) : Finset ℤ :=
  (majorSet f N δ).filter (fun n => ¬ OnTypeIArc f N lam δ n)

/-- **Membership unfolding for `typeISet`.** -/
@[simp] theorem mem_typeISet {f : ℝ → ℝ} {N lam δ : ℝ} {n : ℤ} :
    n ∈ typeISet f N lam δ ↔
      n ∈ majorSet f N δ ∧ OnTypeIArc f N lam δ n := by
  simp only [typeISet, Finset.mem_filter]

/-- **Membership unfolding for `typeIISet`.** -/
@[simp] theorem mem_typeIISet {f : ℝ → ℝ} {N lam δ : ℝ} {n : ℤ} :
    n ∈ typeIISet f N lam δ ↔
      n ∈ majorSet f N δ ∧ ¬ OnTypeIArc f N lam δ n := by
  simp only [typeIISet, Finset.mem_filter]

/-! ## Partition lemma -/

/-- `#majorSet = #typeISet + #typeIISet` (partition by `OnTypeIArc`). -/
theorem majorSet_card_split (f : ℝ → ℝ) (N lam δ : ℝ) :
    (majorSet f N δ).card = (typeISet f N lam δ).card + (typeIISet f N lam δ).card := by
  classical
  rw [typeISet, typeIISet]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-! ## The proper-arc span bound for Type I points (DEFINITIONAL) -/

/-- **Proper-arc span for Type I points** (the redesign payoff, *definitional*):
for `n ∈ typeISet`, the witness line `D` has proper-arc span
`properHi' − properLo' ≤ δ√(q/λ)`.  This is exactly the `OnTypeIArc` filter
condition, recovered through `Finset.mem_filter`. -/
theorem properArc'_span_typeI {f : ℝ → ℝ} {N lam δ : ℝ} {n : ℤ}
    (hn : n ∈ typeISet f N lam δ) :
    ∃ (D : MajorLine) (a b : ℤ),
      a ∈ nearSet f N δ ∧ b ∈ nearSet f N δ ∧ n ∈ nearSet f N δ ∧
      a < n ∧ n < b ∧ OnLine f D a ∧ OnLine f D n ∧ OnLine f D b ∧
      (D.denom : ℝ) ≤ denomCutoff / δ ∧
      ((properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ))
        ≤ δ * Real.sqrt (D.denom / (256 * lam)) :=
  (mem_typeISet.mp hn).2

end Squarefree.Geometry
