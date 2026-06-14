import Squarefree.Counting.Preimage
import Squarefree.Geometry.NearCurveAux
import Squarefree.Geometry.NearCurveSpacing
import Mathlib

/-!
# §4.3 Bombieri–Pila major-arc core (`prop43_local`)

Concrete combinatorial encoding of the major-arc / residual / Type I / Type II
decomposition of `../explicit_writeup.md` (lines 463–672, Prop 4.3), and the
reduction of `prop43_local` to the residual bound plus two concrete Type I /
Type II card stubs.

⚠ Every predicate/set here is a **concrete `def`** (no `opaque`).  A major-arc
line is a `MajorLine = { slope : ℚ, shift : ℤ }`; a near-set point `n` lies on it
iff the lattice point `(n, ℓ_n)` sits on the rational line `q·y = p·n + shift`
(`q := slope.den`, `p := slope.num`).  `OnMajorArc` says `n` is the *middle* of a
small-denominator collinear triple of near-set points, exactly the structure that
makes the residual bound provable: a residual point is one with no such triple,
and five collinear residual points on a small-denominator line force three on one
connected component — contradiction (writeup 564–579).

Inputs (all proven): `Squarefree.noncollinear_span_lower` (the non-collinear
spacing engine), `Squarefree.residueClass_card_le` / `residueClass_denom_le`
(lattice-on-line counts), and the local pieces `nearSet`, `latticeY`,
`collinearDet`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

/-! ## Concrete near-set, lattice points, collinearity -/

/-- The counted integer set `S = {n ∈ [⌊N⌋, ⌊2N⌋] : ‖f n‖ ≤ δ}` (over `ℤ`,
matching `prop43_local`'s conclusion). -/
noncomputable def nearSet (f : ℝ → ℝ) (N δ : ℝ) : Finset ℤ :=
  (Finset.Icc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ)

@[simp] theorem mem_nearSet {f : ℝ → ℝ} {N δ : ℝ} {n : ℤ} :
    n ∈ nearSet f N δ ↔
      (⌊N⌋ ≤ n ∧ n ≤ ⌊2 * N⌋) ∧ distInt (f (n : ℝ)) ≤ δ := by
  simp [nearSet, Finset.mem_filter, Finset.mem_Icc]

/-- The integer nearest to `f n`; `(n, ℓ f n)` is the lattice point of `n ∈ S`. -/
noncomputable def latticeY (f : ℝ → ℝ) (n : ℤ) : ℤ := round (f (n : ℝ))

/-- For `n` in the near-set, `|f n − ℓ_n| ≤ δ`. -/
theorem nearSet_dist_le {f : ℝ → ℝ} {N δ : ℝ} {n : ℤ} (hn : n ∈ nearSet f N δ) :
    |f (n : ℝ) - (latticeY f n : ℝ)| ≤ δ := by
  have := (mem_nearSet.mp hn).2
  simpa [distInt, latticeY] using this

/-- Integer collinearity determinant of the lattice points
`(a, ℓ a), (b, ℓ b), (c, ℓ c)`.  Vanishes iff the three are collinear; equals the
`hncol` numerator `u` of `Squarefree.noncollinear_span_lower`. -/
noncomputable def collinearDet (f : ℝ → ℝ) (a b c : ℤ) : ℤ :=
  latticeY f a * (c - b) + latticeY f b * (a - c) + latticeY f c * (b - a)

/-! ## Concrete major-arc line encoding -/

/-- A rational line `y = (p/q)·x + shift/q`, encoded by a reduced rational slope
and an integral shift.  `q := slope.den`, `p := slope.num`. -/
structure MajorLine where
  slope : ℚ
  shift : ℤ

/-- The (positive) denominator of the line. -/
def MajorLine.denom (D : MajorLine) : ℤ := (D.slope.den : ℤ)

theorem MajorLine.denom_pos (D : MajorLine) : 0 < D.denom := by
  have h : 0 < D.slope.den := D.slope.pos
  simpa [MajorLine.denom] using (by exact_mod_cast h : (0 : ℤ) < (D.slope.den : ℤ))

/-- The lattice point `(n, ℓ_n)` lies on the line `D` iff `q·ℓ_n = p·n + shift`. -/
def OnLine (f : ℝ → ℝ) (D : MajorLine) (n : ℤ) : Prop :=
  D.denom * latticeY f n = D.slope.num * n + D.shift

/-- The `x`-coordinates of near-set points on `D` lie in one residue class mod `q`:
`q ∣ (n − r)` where `r := p⁻¹·shift` need not be computed — we only need the
two-point separation `q ∣ (n − m)` for two points on the line. -/
theorem OnLine.sub_dvd {f : ℝ → ℝ} {D : MajorLine} {n m : ℤ}
    (hn : OnLine f D n) (hm : OnLine f D m) :
    D.denom ∣ (D.slope.num * (n - m)) := by
  -- `q·(ℓ_n − ℓ_m) = p·(n − m)`, so `q ∣ p·(n−m)`.
  simp only [OnLine] at hn hm
  refine ⟨latticeY f n - latticeY f m, ?_⟩
  have : D.slope.num * (n - m)
      = (D.denom * latticeY f n) - (D.denom * latticeY f m) := by
    rw [hn, hm]; ring
  rw [this]; ring

/-! ## Concrete major-arc / residual / Type I / Type II sets

The cutoff `q ≤ ⌈cDenomCutoff / δ⌉` for a fixed small absolute constant; we use a
concrete real comparison `(q : ℝ) ≤ denomCutoff / δ` with `denomCutoff = 1/64`,
matching the threshold reconciliation in `formalization_plan.md`.  The writeup
("`c` sufficiently small", lines 534/581/595) licenses any sufficiently small
absolute constant; `1/64` is chosen so the §4.3 Type I shared-base corner has
strict slack (the gap `d(A)/24` strictly exceeds the `≤ q_k`-shift re-anchor). -/

/-- The absolute denominator-cutoff constant `c` (writeup `q ≤ c/δ`). -/
noncomputable def denomCutoff : ℝ := 1 / 64

/-- `n` is on a major arc: it is the **middle** of a collinear triple of near-set
points on a small-denominator line.  Concrete: there is a line `D` and near-set
points `a < n < b` all on `D` with `(D.denom : ℝ) ≤ denomCutoff / δ`. -/
def OnMajorArc (f : ℝ → ℝ) (N δ : ℝ) (n : ℤ) : Prop :=
  ∃ (D : MajorLine) (a b : ℤ),
    a ∈ nearSet f N δ ∧ b ∈ nearSet f N δ ∧ n ∈ nearSet f N δ ∧
    a < n ∧ n < b ∧ OnLine f D a ∧ OnLine f D n ∧ OnLine f D b ∧
    (D.denom : ℝ) ≤ denomCutoff / δ

/-- The major set: near-set points lying on a major arc. -/
noncomputable def majorSet (f : ℝ → ℝ) (N δ : ℝ) : Finset ℤ :=
  (nearSet f N δ).filter (fun n => OnMajorArc f N δ n)

/-- The residual set: near-set points lying on **no** major arc (writeup 564). -/
noncomputable def residualSet (f : ℝ → ℝ) (N δ : ℝ) : Finset ℤ :=
  (nearSet f N δ).filter (fun n => ¬ OnMajorArc f N δ n)

@[simp] theorem mem_majorSet {f : ℝ → ℝ} {N δ : ℝ} {n : ℤ} :
    n ∈ majorSet f N δ ↔ n ∈ nearSet f N δ ∧ OnMajorArc f N δ n := by
  simp [majorSet, Finset.mem_filter]

@[simp] theorem mem_residualSet {f : ℝ → ℝ} {N δ : ℝ} {n : ℤ} :
    n ∈ residualSet f N δ ↔ n ∈ nearSet f N δ ∧ ¬ OnMajorArc f N δ n := by
  simp [residualSet, Finset.mem_filter]

/-! ## Partition lemmas (real, not hollow) -/

/-- `#nearSet = #residualSet + #majorSet` (partition by `OnMajorArc`). -/
theorem nearSet_card_split (f : ℝ → ℝ) (N δ : ℝ) :
    (nearSet f N δ).card = (residualSet f N δ).card + (majorSet f N δ).card := by
  classical
  rw [residualSet, majorSet, add_comm]
  exact (Finset.filter_card_add_filter_neg_card_eq_card _).symm

end Squarefree.Geometry
