import Squarefree.Geometry.NearCurveTypeI
import Mathlib

/-!
# §4.3 UN-WINDOWED proper-arc (strip-component) machinery (writeup 529–532, 583–585)

This module builds the **un-windowed** parallel to the windowed carrier of
`NearCurveGreedy`: the line's *full* strip components (all near-set points on a
line `D`, with no witness-window restriction), the ≤2-component cover, and the
**universal span bound** `properHi' − properLo' ≤ 4√(δ/λ)`.

These are the foundation for the faithful Type-I line-keyed redesign.  The defs
carry a `'` to distinguish them from the windowed defs in `NearCurveGreedy`
(which stay untouched).

The genuine convex content lives in:

* `lineRes_convex_or_concave` (#1): from `|f''| ≥ λ > 0` and `f ∈ C²`, the
  residual `g = f − P_D` is `ConvexOn` *or* `ConcaveOn` on `[N/2, 5N/2]`
  (constant-sign second derivative);
* `properArc'_continuous_strip` (#4): on the monotone side of the discrete
  minimizer, `|g| ≤ δ` holds *throughout* the real span `[properLo', properHi']`;
* `properArc'_span_le` (#5): the universal span bound, via `majorArc_length_bound`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## The first/second derivative of the residual `g = f − P`

We use the *explicit* first-derivative function `g' = fun y => deriv f y − p/q`
(which matches `hasDerivAt_lineRes`), so the second derivative is literally
`iteratedDeriv 2 f` (`P` is affine). -/

/-- The explicit first derivative `g'(y) = deriv f y − p/q` of `g = lineRes f D`. -/
private noncomputable def lineRes' (f : ℝ → ℝ) (D : MajorLine) (y : ℝ) : ℝ :=
  deriv f y - (D.slope.num : ℝ) / (D.denom : ℝ)

private theorem hasDerivAt_lineRes' {D : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (lineRes f D) (lineRes' f D x) x :=
  hasDerivAt_lineRes (hasDerivAt_self_of_contDiff hf x)

/-- `g'` has derivative `iteratedDeriv 2 f x` everywhere (`P` affine). -/
private theorem hasDerivAt_lineRes'_deriv {D : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (lineRes' f D) (iteratedDeriv 2 f x) x :=
  (hasDerivAt_deriv_of_contDiff hf x).sub_const _

/-! ## Constant-sign second derivative ⟹ convex or concave -/

/-- **#1 — `lineRes` is convex or concave** (writeup: "`g'` is monotone").
From `f ∈ C²` and `λ ≤ |f''|` on `[N/2, 5N/2]` (so `f''` is continuous and never
zero, hence of constant sign by the intermediate value theorem), and the fact that
`(lineRes)'' = f''` (`P` affine), the residual `g = f − P_D` is `ConvexOn` or
`ConcaveOn` on `[N/2, 5N/2]`. -/
theorem lineRes_convex_or_concave {D : MajorLine}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) :
    ConvexOn ℝ (Set.Icc (N / 2) (5 * N / 2)) (lineRes f D) ∨
      ConcaveOn ℝ (Set.Icc (N / 2) (5 * N / 2)) (lineRes f D) := by
  classical
  set I := Set.Icc (N / 2) (5 * N / 2) with hI
  -- `f''` is continuous (from `f ∈ C²`).
  have hcont2 : Continuous (iteratedDeriv 2 f) := by
    have h0 : Continuous (deriv (deriv f)) := by
      simpa using (hf.iterate_deriv' 0 2).continuous
    have heq : iteratedDeriv 2 f = deriv (deriv f) := funext fun x => iteratedDeriv_two_eq
    rw [heq]; exact h0
  -- `f''` never vanishes on `I` (since `λ ≤ |f''|`, `λ > 0`).
  have hne : ∀ x ∈ I, iteratedDeriv 2 f x ≠ 0 := by
    intro x hx hzero
    have := hlower x hx
    rw [hzero, abs_zero] at this
    linarith
  -- `lineRes` is continuous on `I`.
  have hgcont : ContinuousOn (lineRes f D) I := by
    apply Continuous.continuousOn
    exact (hf.continuous).sub (by unfold lineVal; fun_prop)
  -- Constant-sign dichotomy on the connected (convex) set `I`.
  by_cases hpos : ∃ x ∈ I, 0 < iteratedDeriv 2 f x
  · -- positive somewhere ⟹ positive everywhere on `I` (no zero, IVT) ⟹ convex.
    left
    obtain ⟨x₀, hx₀I, hx₀pos⟩ := hpos
    have hall : ∀ x ∈ I, 0 < iteratedDeriv 2 f x := by
      intro x hxI
      rcases lt_trichotomy (iteratedDeriv 2 f x) 0 with hneg | hzero | hpos'
      · -- sign change between `x` and `x₀` would force a zero (IVT) — contradiction.
        exfalso
        have hsub : Set.uIcc x x₀ ⊆ I := Set.uIcc_subset_Icc hxI hx₀I
        have hcontOn : ContinuousOn (iteratedDeriv 2 f) (Set.uIcc x x₀) :=
          hcont2.continuousOn
        -- `0 ∈ [[f''(x), f''(x₀)]]` since one is `< 0` and the other `> 0`.
        have h0mem : (0 : ℝ) ∈ Set.uIcc (iteratedDeriv 2 f x) (iteratedDeriv 2 f x₀) := by
          rw [Set.mem_uIcc]; left; exact ⟨hneg.le, hx₀pos.le⟩
        obtain ⟨c, hcmem, hc0⟩ := intermediate_value_uIcc hcontOn h0mem
        exact hne c (hsub hcmem) hc0
      · exact absurd hzero (hne x hxI)
      · exact hpos'
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hgcont
      (f' := lineRes' f D) (f'' := iteratedDeriv 2 f) ?_ ?_ ?_
    · intro x _
      exact (hasDerivAt_lineRes' hf x).hasDerivWithinAt
    · intro x _
      exact (hasDerivAt_lineRes'_deriv hf x).hasDerivWithinAt
    · intro x hx
      exact (hall x (interior_subset hx)).le
  · -- not positive anywhere ⟹ (no zero) ⟹ negative everywhere ⟹ concave.
    right
    push_neg at hpos
    have hall : ∀ x ∈ I, iteratedDeriv 2 f x < 0 := by
      intro x hxI
      have h1 : iteratedDeriv 2 f x ≤ 0 := hpos x hxI
      exact lt_of_le_of_ne h1 (hne x hxI)
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) hgcont
      (f' := lineRes' f D) (f'' := iteratedDeriv 2 f) ?_ ?_ ?_
    · intro x _
      exact (hasDerivAt_lineRes' hf x).hasDerivWithinAt
    · intro x _
      exact (hasDerivAt_lineRes'_deriv hf x).hasDerivWithinAt
    · intro x hx
      exact (hall x (interior_subset hx)).le

/-- `lineRes f D ∈ C²` on all of `ℝ` (so `ContDiffOn` on any subset). -/
private theorem contDiff_lineRes {D : MajorLine} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (lineRes f D) := by
  have hP : ContDiff ℝ 2 (lineVal D) := by unfold lineVal; fun_prop
  exact hf.sub hP

/-! ## The un-windowed line carrier and its discrete minimizer -/

/-- **The un-windowed line carrier** of `D`: ALL near-set points on the line `D`
(no witness-window restriction).  This is the full strip-line intersection
`{m ∈ S : (m, ℓ_m) ∈ D}`. -/
noncomputable def lineCarrier' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : Finset ℤ :=
  (nearSet f N δ).filter (fun m => OnLine f D m)

theorem mem_lineCarrier' {D : MajorLine} {m : ℤ} :
    m ∈ lineCarrier' f N δ D ↔ m ∈ nearSet f N δ ∧ OnLine f D m := by
  simp only [lineCarrier', Finset.mem_filter]

/-- The **curvature sign** of the line `D` on the window `I = [N/2, 5N/2]`:
`+1` if the residual `g = lineRes f D` is `ConvexOn I`, else `-1`.  The signed
residual `lineSign' • g` is then `ConvexOn` under the curvature hypotheses
(convex stays convex; concave `× (-1)` becomes convex). -/
noncomputable def lineSign' (f : ℝ → ℝ) (N : ℝ) (D : MajorLine) : ℝ := by
  classical
  exact if ConvexOn ℝ (Set.Icc (N / 2) (5 * N / 2)) (lineRes f D) then 1 else -1

/-- **The curvature-keyed (continuous) split point** of the line `D` on the
curvature window `I = [N/2, 5N/2]`: a *minimizer* of the **convexified** residual
`lineSign' • g` on `I`.

This is the genuine fix over a discrete argmin: splitting always at the minimizer
of the *convexified* residual lands the proper arc on a monotone side regardless of
the curvature sign.  For convex `g` (`sign = +1`) this is the minimizer of `g`; for
concave `g` (`sign = -1`) it is the *maximizer* of `g` (= minimizer of `-g`).  With
a concave `g`, a discrete argmin sits at a carrier extreme and a side can bulge above
`δ` between lattice points — so the discrete split fails; the continuous extremum of
the convexified residual fixes it.

Total (default `N/2` when no minimizer exists), via classical choice. -/
noncomputable def lineSplit' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : ℝ := by
  classical
  exact
    if h : ∃ c ∈ Set.Icc (N / 2) (5 * N / 2),
        IsMinOn (fun x => lineSign' f N D * lineRes f D x)
          (Set.Icc (N / 2) (5 * N / 2)) c then
      h.choose
    else N / 2

/-- The convexified residual `lineSign' • g` is `ConvexOn` on `I` under the §4.3
curvature hypotheses (convex `g` keeps sign `+1`; concave `g` flips to `-1`). -/
theorem convexOn_signed_lineRes {D : MajorLine}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) :
    ConvexOn ℝ (Set.Icc (N / 2) (5 * N / 2))
      (fun x => lineSign' f N D * lineRes f D x) := by
  classical
  rcases lineRes_convex_or_concave hf hlam hlower with hcvx | hccv
  · have hsign : lineSign' f N D = 1 := by rw [lineSign', if_pos hcvx]
    simpa [hsign] using hcvx
  · by_cases hcvx : ConvexOn ℝ (Set.Icc (N / 2) (5 * N / 2)) (lineRes f D)
    · have hsign : lineSign' f N D = 1 := by rw [lineSign', if_pos hcvx]
      simpa [hsign] using hcvx
    · have hsign : lineSign' f N D = -1 := by rw [lineSign', if_neg hcvx]
      have heq : (fun x => lineSign' f N D * lineRes f D x)
          = -(lineRes f D) := by
        funext x; rw [hsign, Pi.neg_apply]; ring
      rw [heq]
      exact neg_convexOn_iff.mpr hccv

/-- **Split spec.**  Under the §4.3 curvature hypotheses, `lineSplit'` lies in the
window `I = [N/2, 5N/2]` and is a *minimizer* of the convexified residual on `I`. -/
theorem lineSplit'_isMinOn {D : MajorLine}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) :
    lineSplit' f N δ D ∈ Set.Icc (N / 2) (5 * N / 2) ∧
      IsMinOn (fun x => lineSign' f N D * lineRes f D x)
        (Set.Icc (N / 2) (5 * N / 2)) (lineSplit' f N δ D) := by
  classical
  set I := Set.Icc (N / 2) (5 * N / 2) with hIdef
  have hIne : I.Nonempty := ⟨N / 2, by rw [hIdef]; exact ⟨le_rfl, by linarith⟩⟩
  -- the convexified residual is continuous, hence attains a min on compact `I`.
  have hgcont : ContinuousOn (fun x => lineSign' f N D * lineRes f D x) I :=
    (continuousOn_const).mul (contDiff_lineRes hf).continuous.continuousOn
  have hex : ∃ c ∈ I, IsMinOn (fun x => lineSign' f N D * lineRes f D x) I c :=
    (isCompact_Icc).exists_isMinOn hIne hgcont
  have hval : lineSplit' f N δ D = hex.choose := by
    rw [lineSplit', dif_pos hex]
  rw [hval]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩

/-! ## The side-only half-runs and the proper arc -/

/-- **Side-only strip half-run** of the un-windowed carrier: the carrier points on
the `dir`-side of `x₀ := lineSplit'`.  For `dir = true` it is `{n ≤ x₀}`; for
`dir = false` it is `{x₀ ≤ n}`.  Side-only suffices for the `≤2`-component cover. -/
noncomputable def halfCarrier' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) (dir : Bool) :
    Finset ℤ :=
  (lineCarrier' f N δ D).filter
    (fun n => if dir then (n : ℝ) ≤ lineSplit' f N δ D
              else lineSplit' f N δ D ≤ (n : ℝ))

private theorem halfCarrier'_subset {D : MajorLine} (dir : Bool) :
    halfCarrier' f N δ D dir ⊆ lineCarrier' f N δ D :=
  Finset.filter_subset _ _

/-- The proper side: the half-run of larger cardinality. -/
noncomputable def properSide' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : Bool :=
  decide ((halfCarrier' f N δ D false).card ≤ (halfCarrier' f N δ D true).card)

/-- **The un-windowed proper major arc of the line `D`** (writeup 529–532): the
larger of the two side half-runs. -/
noncomputable def properArc' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : Finset ℤ :=
  halfCarrier' f N δ D (properSide' f N δ D)

/-- The left endpoint (least `x`-coordinate) of the proper arc (default `0`). -/
noncomputable def properLo' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : ℤ :=
  if h : (properArc' f N δ D).Nonempty then (properArc' f N δ D).min' h else 0

/-- The right endpoint (greatest `x`-coordinate) of the proper arc (default `0`). -/
noncomputable def properHi' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : ℤ :=
  if h : (properArc' f N δ D).Nonempty then (properArc' f N δ D).max' h else 0

/-- The proper-arc density `d(A) = (properHi' − properLo')/(qδ)`. -/
noncomputable def densArc' (f : ℝ → ℝ) (N δ : ℝ) (D : MajorLine) : ℝ :=
  arcDensity D δ (properLo' f N δ D) (properHi' f N δ D)

private theorem properArc'_subset_carrier {D : MajorLine} :
    properArc' f N δ D ⊆ lineCarrier' f N δ D :=
  halfCarrier'_subset _

/-- A point of the proper arc is a near-set point on `D` inside `[properLo', properHi']`. -/
theorem mem_properArc'_facts {D : MajorLine} {m : ℤ}
    (hm : m ∈ properArc' f N δ D) :
    m ∈ nearSet f N δ ∧ OnLine f D m ∧
      (properLo' f N δ D : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (properHi' f N δ D : ℝ) := by
  have hmc : m ∈ lineCarrier' f N δ D := properArc'_subset_carrier hm
  obtain ⟨hnear, hon⟩ := mem_lineCarrier'.mp hmc
  have hne : (properArc' f N δ D).Nonempty := ⟨m, hm⟩
  refine ⟨hnear, hon, ?_, ?_⟩
  · have : properLo' f N δ D = (properArc' f N δ D).min' hne := by
      simp only [properLo', hne, dif_pos]
    rw [this]; exact_mod_cast (properArc' f N δ D).min'_le m hm
  · have : properHi' f N δ D = (properArc' f N δ D).max' hne := by
      simp only [properHi', hne, dif_pos]
    rw [this]; exact_mod_cast (properArc' f N δ D).le_max' m hm

theorem properLo'_mem {D : MajorLine}
    (hne : (properArc' f N δ D).Nonempty) :
    properLo' f N δ D ∈ properArc' f N δ D := by
  have : properLo' f N δ D = (properArc' f N δ D).min' hne := by
    simp only [properLo', hne, dif_pos]
  rw [this]; exact (properArc' f N δ D).min'_mem hne

theorem properHi'_mem {D : MajorLine}
    (hne : (properArc' f N δ D).Nonempty) :
    properHi' f N δ D ∈ properArc' f N δ D := by
  have : properHi' f N δ D = (properArc' f N δ D).max' hne := by
    simp only [properHi', hne, dif_pos]
  rw [this]; exact (properArc' f N δ D).max'_mem hne

/-- **Proper-arc is convex (interval-like) within the carrier.**  The proper arc is
one *side* of the split point `lineSplit'` (the `halfCarrier'` filter is a single
one-sided comparison `≤`/`≥` against `lineSplit'`, hence convex).  So any carrier
point `x` (near-set on `D`) sandwiched between two proper-arc points `lo ≤ x ≤ hi`
is itself on the proper side, hence in the proper arc. -/
theorem mem_properArc'_of_between {D : MajorLine} {lo hi x : ℤ}
    (hlo : lo ∈ properArc' f N δ D) (hhi : hi ∈ properArc' f N δ D)
    (hxc : x ∈ lineCarrier' f N δ D) (hlx : lo ≤ x) (hxh : x ≤ hi) :
    x ∈ properArc' f N δ D := by
  -- Unfold the proper side filter for `lo`, `hi`, and the target.
  simp only [properArc', halfCarrier', Finset.mem_filter] at hlo hhi ⊢
  refine ⟨hxc, ?_⟩
  obtain ⟨_, hlo2⟩ := hlo
  obtain ⟨_, hhi2⟩ := hhi
  have hloR : (lo : ℝ) ≤ (x : ℝ) := by exact_mod_cast hlx
  have hxhR : (x : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hxh
  by_cases hps : properSide' f N δ D = true
  · -- `dir = true`: side `{n ≤ lineSplit'}`; `x ≤ hi ≤ lineSplit'`.
    rw [if_pos hps] at hhi2 ⊢
    exact le_trans hxhR hhi2
  · -- `dir = false`: side `{lineSplit' ≤ n}`; `lineSplit' ≤ lo ≤ x`.
    rw [if_neg hps] at hlo2 ⊢
    exact le_trans hlo2 hloR

/-! ## #2 — the ≤2-component cover (now trivial: side-only split) -/

/-- **#2 — The `≤2`-component cover.**  The un-windowed carrier is covered by the
two side half-runs `{n ≤ lineSplit'} ∪ {lineSplit' ≤ n}` — trivial by `le_or_gt`,
since the split is *side-only* (the convexity does not enter here; it enters in
`properArc'_continuous_strip`, #4). -/
theorem stripComp_cover' {D : MajorLine} :
    lineCarrier' f N δ D ⊆ halfCarrier' f N δ D true ∪ halfCarrier' f N δ D false := by
  intro m hm
  rw [Finset.mem_union]
  rcases le_or_gt (m : ℝ) (lineSplit' f N δ D) with hle | hlt
  · left; rw [halfCarrier', Finset.mem_filter]; exact ⟨hm, by simpa using hle⟩
  · right; rw [halfCarrier', Finset.mem_filter]; exact ⟨hm, by simpa using hlt.le⟩

private theorem halfCarrier'_card_le_properArc' {D : MajorLine} (dir : Bool) :
    (halfCarrier' f N δ D dir).card ≤ (properArc' f N δ D).card := by
  unfold properArc' properSide'
  by_cases hcmp : (halfCarrier' f N δ D false).card ≤ (halfCarrier' f N δ D true).card
  · rw [decide_eq_true hcmp]; cases dir
    · exact hcmp
    · exact le_rfl
  · rw [decide_eq_false hcmp]; push_neg at hcmp; cases dir
    · exact le_rfl
    · exact hcmp.le

/-! ## #3 — the carrier splits into ≤2 strip components -/

/-- **#3 — `#lineCarrier' ≤ 2·#properArc'`** (the writeup-532 factor 2), from the
`≤2`-component cover and the larger-half domination. -/
theorem lineCarrier'_card_le_two_properArc' {D : MajorLine} :
    (lineCarrier' f N δ D).card ≤ 2 * (properArc' f N δ D).card := by
  classical
  calc (lineCarrier' f N δ D).card
      ≤ (halfCarrier' f N δ D true ∪ halfCarrier' f N δ D false).card :=
        Finset.card_le_card stripComp_cover'
    _ ≤ (halfCarrier' f N δ D true).card + (halfCarrier' f N δ D false).card :=
        Finset.card_union_le _ _
    _ ≤ (properArc' f N δ D).card + (properArc' f N δ D).card :=
        Nat.add_le_add (halfCarrier'_card_le_properArc' true)
          (halfCarrier'_card_le_properArc' false)
    _ = 2 * (properArc' f N δ D).card := by ring

/-! ## Re-derived small helpers (private in `NearCurveGreedy`) -/

/-- A near-set point's `x`-coordinate lies in the curvature window `[N/2, 5N/2]`. -/
private theorem nearSet_coord_mem_Icc' {p : ℤ} (hN2 : 2 ≤ N) (hp : p ∈ nearSet f N δ) :
    (p : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := by
  rw [mem_nearSet] at hp
  obtain ⟨⟨hlo, hhi⟩, _⟩ := hp
  have hloR : (⌊N⌋ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo
  have hhiR : (p : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by exact_mod_cast hhi
  have hflo : N - 1 < (⌊N⌋ : ℝ) := by have := Int.sub_one_lt_floor N; linarith
  have hfhi : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
  constructor
  · linarith
  · linarith

/-- For an `OnLine` near-set point `p`, the line-residual is small: `|g(p)| ≤ δ`. -/
private theorem lineRes_le_of_onLine_nearSet' {D : MajorLine} {p : ℤ}
    (hp : p ∈ nearSet f N δ) (hon : OnLine f D p) :
    |lineRes f D (p : ℝ)| ≤ δ := by
  rw [lineRes, lineVal_eq_latticeY hon]
  exact nearSet_dist_le hp

/-! ## #4 — `|g| ≤ δ` on the real span of the proper arc

The genuine §4.3 content is that the proper arc lands on a **monotone** piece of
`g = lineRes f D` (a connected component of `{|g| ≤ δ}`, on which `g'` has fixed
sign).  We isolate the trivial "monotone between two `[−δ,δ]` endpoints stays in
`[−δ,δ]`" fact, and bridge to the proper arc through `properArc'_side_monotone`. -/

/-- **Monotone (or antitone) between two strip endpoints stays in the strip.**
If `g` is `MonotoneOn` *or* `AntitoneOn` on `[n, m]`, and `|g n|, |g m| ≤ d`, then
`|g x| ≤ d` for every `x ∈ [n, m]`.  (For monotone: `g n ≤ g x ≤ g m`; both ends in
`[−d, d]`.  Antitone is the mirror.)  This is the discrete-min split's payoff: a
side-half is one monotone piece. -/
private theorem monotone_between_abs_le {g : ℝ → ℝ} {n m d : ℝ} (hnm : n ≤ m)
    (hmono : MonotoneOn g (Set.Icc n m) ∨ AntitoneOn g (Set.Icc n m))
    (hgn : |g n| ≤ d) (hgm : |g m| ≤ d) :
    ∀ x ∈ Set.Icc n m, |g x| ≤ d := by
  intro x hx
  have hnmem : n ∈ Set.Icc n m := ⟨le_rfl, hnm⟩
  have hmmem : m ∈ Set.Icc n m := ⟨hnm, le_rfl⟩
  rw [abs_le] at hgn hgm ⊢
  rcases hmono with hmono | hanti
  · -- monotone: `g n ≤ g x ≤ g m`.
    have h1 : g n ≤ g x := hmono hnmem hx hx.1
    have h2 : g x ≤ g m := hmono hx hmmem hx.2
    exact ⟨le_trans hgn.1 h1, le_trans h2 hgm.2⟩
  · -- antitone: `g m ≤ g x ≤ g n`.
    have h1 : g x ≤ g n := hanti hnmem hx hx.1
    have h2 : g m ≤ g x := hanti hx hmmem hx.2
    exact ⟨le_trans hgm.1 h2, le_trans h1 hgn.2⟩

/-- **Right of a minimizer, a convex function is monotone.**  If `h` is `ConvexOn`
on a convex set `s` and `c ∈ s` is a minimizer (`IsMinOn h s c`), then `h` is
`MonotoneOn` on `s ∩ [c, ∞)`. -/
private theorem convexOn_monotoneOn_right {s : Set ℝ} {h : ℝ → ℝ} {c : ℝ}
    (hconv : ConvexOn ℝ s h) (hc : c ∈ s) (hmin : IsMinOn h s c) :
    MonotoneOn h (s ∩ Set.Ici c) := by
  intro u hu v hv huv
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact le_rfl
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hu.2) with hcu | hcu
  · -- `u = c`: minimizer ⟹ `h c ≤ h v`.
    rw [← hcu]; exact hmin hv.1
  · -- `c < u < v`: `u ∈ openSegment c v`, convexity from `h c ≤ h u` (min).
    have humem : u ∈ openSegment ℝ c v := by
      rw [openSegment_eq_Ioo (hcu.trans hlt)]; exact ⟨hcu, hlt⟩
    exact hconv.le_right_of_left_le hc hv.1 humem (hmin hu.1)

/-- **Left of a minimizer, a convex function is antitone.**  If `h` is `ConvexOn`
on a convex set `s` and `c ∈ s` is a minimizer, then `h` is `AntitoneOn` on
`s ∩ (∞, c]`. -/
private theorem convexOn_antitoneOn_left {s : Set ℝ} {h : ℝ → ℝ} {c : ℝ}
    (hconv : ConvexOn ℝ s h) (hc : c ∈ s) (hmin : IsMinOn h s c) :
    AntitoneOn h (s ∩ Set.Iic c) := by
  intro u hu v hv huv
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact le_rfl
  rcases eq_or_lt_of_le (Set.mem_Iic.mp hv.2) with hvc | hvc
  · -- `v = c`: minimizer ⟹ `h c ≤ h u`.
    rw [hvc]; exact hmin hu.1
  · -- `u < v < c`: `v ∈ openSegment u c`, convexity from `h c ≤ h v` (min).
    have hvmem : v ∈ openSegment ℝ u c := by
      rw [openSegment_eq_Ioo (hlt.trans hvc)]; exact ⟨hlt, hvc⟩
    -- use `le_left_of_right_le`: from `h c ≤ h v` deduce `h v ≤ h u`.
    exact hconv.le_left_of_right_le hu.1 hc hvmem (hmin hv.1)

/-- **The proper arc is a monotone piece** (§4.3, writeup 529–532).
Between any two same-side carrier points `n ≤ m` of `properArc' f N δ D`, the
residual `g = lineRes f D` is `MonotoneOn` *or* `AntitoneOn` on `[n, m]`.

PROOF: the curvature-keyed split `lineSplit'` is the minimizer of the *convexified*
residual `h = lineSign' • g` (`lineSplit'_isMinOn`); `h` is convex
(`convexOn_signed_lineRes`).  The proper arc is one side of `lineSplit'`, so
`[n, m] ⊆ I ∩ [c, ∞)` or `[n, m] ⊆ I ∩ (∞, c]`; on either, `h` is `MonotoneOn`
or `AntitoneOn` (`convexOn_monotoneOn_right`/`_left`).  Multiplying back by
`lineSign' = ±1` turns this into `MonotoneOn`-or-`AntitoneOn` of `g`. -/
private theorem properArc'_side_monotone {D : MajorLine}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    {n m : ℤ} (hn : n ∈ properArc' f N δ D) (hm : m ∈ properArc' f N δ D)
    (hnm : n ≤ m) :
    MonotoneOn (lineRes f D) (Set.Icc (n : ℝ) (m : ℝ)) ∨
      AntitoneOn (lineRes f D) (Set.Icc (n : ℝ) (m : ℝ)) := by
  classical
  set I := Set.Icc (N / 2) (5 * N / 2) with hIdef
  set c := lineSplit' f N δ D with hc
  set sgn := lineSign' f N D with hsgn
  set h := fun x => sgn * lineRes f D x with hh
  -- convexified residual is convex, split point is its minimizer in `I`.
  have hconv : ConvexOn ℝ I h := convexOn_signed_lineRes hf hlam hlower
  obtain ⟨hcI, hcmin⟩ := lineSplit'_isMinOn (δ := δ) (D := D) hf hlam hN2 hlower
  -- `n, m` are near-set coords ⟹ in `I`.
  obtain ⟨hnNear, _, _, _⟩ := mem_properArc'_facts hn
  obtain ⟨hmNear, _, _, _⟩ := mem_properArc'_facts hm
  have hnI : (n : ℝ) ∈ I := nearSet_coord_mem_Icc' hN2 hnNear
  have hmI : (m : ℝ) ∈ I := nearSet_coord_mem_Icc' hN2 hmNear
  -- `[n, m] ⊆ I` (window is an `Icc`, hence convex).
  have hsubI : Set.Icc (n : ℝ) (m : ℝ) ⊆ I := Set.Icc_subset_Icc hnI.1 hmI.2
  -- the proper arc is one side of `c`: all `≤ c` or all `≥ c`.
  -- Determine the side from `n, m`'s membership in `halfCarrier'`.
  have hside : ((m : ℝ) ≤ c) ∨ (c ≤ (n : ℝ)) := by
    -- `n, m ∈ properArc' = halfCarrier' (properSide')`, whose filter pins the side.
    have hnf : n ∈ halfCarrier' f N δ D (properSide' f N δ D) := hn
    have hmf : m ∈ halfCarrier' f N δ D (properSide' f N δ D) := hm
    rw [halfCarrier', Finset.mem_filter] at hnf hmf
    by_cases hsd : properSide' f N δ D = true
    · left
      have := hmf.2; rw [hsd, if_pos rfl] at this; exact this
    · right
      have hsd' : properSide' f N δ D = false := by
        cases hpr : properSide' f N δ D
        · rfl
        · exact absurd hpr hsd
      have := hnf.2; rw [hsd', if_neg (by decide)] at this; exact this
  -- helper: `h` mono/anti ⟹ `g` mono/anti (since `g = sgn⁻¹ • h` and `sgn = ±1`).
  have hsgn_cases : sgn = 1 ∨ sgn = -1 := by
    rw [hsgn, lineSign']; split <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hg_eq : ∀ x, lineRes f D x = sgn * h x := by
    intro x; rw [hh]
    rcases hsgn_cases with h1 | h1 <;> rw [h1] <;> ring
  -- transport mono/anti of `h` to `g` through the `sgn`-scaling.
  have transport : (MonotoneOn h (Set.Icc (n : ℝ) (m : ℝ)) ∨
        AntitoneOn h (Set.Icc (n : ℝ) (m : ℝ))) →
      (MonotoneOn (lineRes f D) (Set.Icc (n : ℝ) (m : ℝ)) ∨
        AntitoneOn (lineRes f D) (Set.Icc (n : ℝ) (m : ℝ))) := by
    intro hmono
    have hgfun : lineRes f D = fun x => sgn * h x := funext hg_eq
    rcases hsgn_cases with h1 | h1
    · -- sgn = 1: `g = h`.
      rw [hgfun]
      rcases hmono with hM | hA
      · left; simpa [h1] using hM
      · right; simpa [h1] using hA
    · -- sgn = -1: `g = -h`, so mono ↔ anti flip.
      rw [hgfun]
      rcases hmono with hM | hA
      · right
        intro u hu v hv huv
        have := hM hu hv huv
        rw [h1]; simp only [neg_one_mul]; exact neg_le_neg this
      · left
        intro u hu v hv huv
        have := hA hu hv huv
        rw [h1]; simp only [neg_one_mul]; exact neg_le_neg this
  apply transport
  rcases hside with hmc | hcn
  · -- `[n, m] ⊆ I ∩ (∞, c]`: `h` antitone.
    right
    have hsub : Set.Icc (n : ℝ) (m : ℝ) ⊆ I ∩ Set.Iic c := by
      intro x hx
      exact ⟨hsubI hx, le_trans hx.2 hmc⟩
    exact (convexOn_antitoneOn_left hconv hcI hcmin).mono hsub
  · -- `[n, m] ⊆ I ∩ [c, ∞)`: `h` monotone.
    left
    have hsub : Set.Icc (n : ℝ) (m : ℝ) ⊆ I ∩ Set.Ici c := by
      intro x hx
      exact ⟨hsubI hx, le_trans hcn hx.1⟩
    exact (convexOn_monotoneOn_right hconv hcI hcmin).mono hsub

/-- **#4 — `|g| ≤ δ` on the proper-arc real span.**  For carrier points `n ≤ m`
both in `properArc' f N δ D`, the residual `g = lineRes f D` stays in `[−δ, δ]` on
the *whole* real interval `[n, m]`.  PROOF: the endpoints are near-set points on
`D`, so `|g(n)|, |g(m)| ≤ δ`; `g` is monotone on the side (`properArc'_side_monotone`);
monotone between two `[−δ,δ]` endpoints stays in `[−δ,δ]` (`monotone_between_abs_le`). -/
theorem properArc'_continuous_strip {D : MajorLine}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    {n m : ℤ} (hn : n ∈ properArc' f N δ D) (hm : m ∈ properArc' f N δ D)
    (hnm : n ≤ m) :
    ∀ x ∈ Set.Icc (n : ℝ) (m : ℝ), |lineRes f D x| ≤ δ := by
  have hnR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  -- endpoints are near-set points on `D` ⟹ `|g| ≤ δ`.
  obtain ⟨hnNear, hnOn, _, _⟩ := mem_properArc'_facts hn
  obtain ⟨hmNear, hmOn, _, _⟩ := mem_properArc'_facts hm
  have hgn : |lineRes f D (n : ℝ)| ≤ δ := lineRes_le_of_onLine_nearSet' hnNear hnOn
  have hgm : |lineRes f D (m : ℝ)| ≤ δ := lineRes_le_of_onLine_nearSet' hmNear hmOn
  exact monotone_between_abs_le hnR
    (properArc'_side_monotone hf hlam hN2 hlower hn hm hnm) hgn hgm

/-! ## #5 — the universal proper-arc span bound `≤ 4√(δ/λ)` -/

/-- `iteratedDeriv 2 (lineRes f D) x = iteratedDeriv 2 f x` (`P` affine). -/
private theorem iteratedDeriv_two_lineRes {D : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    iteratedDeriv 2 (lineRes f D) x = iteratedDeriv 2 f x := by
  -- `deriv (lineRes f D) = lineRes' f D` everywhere.
  have hd1 : deriv (lineRes f D) = lineRes' f D :=
    funext fun y => (hasDerivAt_lineRes' hf y).deriv
  rw [iteratedDeriv_two_eq, hd1]
  exact (hasDerivAt_lineRes'_deriv hf x).deriv

/-- **#5 — the universal span bound** (writeup 529): the projected length of the
un-windowed proper major arc of `D` is `≤ 4√(δ/λ)`.  PROOF: apply
`majorArc_length_bound` to `g = lineRes f D` on `[properLo', properHi']` — its
`|g| ≤ δ` hypothesis is `properArc'_continuous_strip` (#4), its `|g''| ≥ λ` is the
curvature floor (`g'' = f''`), giving `λ·L² ≤ 16δ`, hence `L ≤ 4√(δ/λ)`. -/
theorem properArc'_span_le {D : MajorLine}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) :
    (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ) ≤ 4 * Real.sqrt (δ / lam) := by
  classical
  set lo := (properLo' f N δ D : ℝ) with hlo
  set hi := (properHi' f N δ D : ℝ) with hhi
  -- The sqrt bound target is nonnegative.
  have hsqrt_nn : (0 : ℝ) ≤ 4 * Real.sqrt (δ / lam) := by positivity
  by_cases hne : (properArc' f N δ D).Nonempty
  · -- nonempty: `lo = properLo' ≤ properHi' = hi`, both near-set coords.
    have hlomem := properLo'_mem hne
    have hhimem := properHi'_mem hne
    obtain ⟨hloNear, _, _, _⟩ := mem_properArc'_facts hlomem
    obtain ⟨hhiNear, _, _, _⟩ := mem_properArc'_facts hhimem
    -- `properLo' ≤ properHi'` (min' ≤ max').
    have hlohiZ : properLo' f N δ D ≤ properHi' f N δ D := by
      obtain ⟨_, _, _, h2⟩ := mem_properArc'_facts hlomem
      exact_mod_cast h2
    have hlohi : lo ≤ hi := by rw [hlo, hhi]; exact_mod_cast hlohiZ
    -- endpoint coords in the curvature window `[N/2, 5N/2]`.
    have hloIcc : lo ∈ Set.Icc (N / 2) (5 * N / 2) := nearSet_coord_mem_Icc' hN2 hloNear
    have hhiIcc : hi ∈ Set.Icc (N / 2) (5 * N / 2) := nearSet_coord_mem_Icc' hN2 hhiNear
    -- `[lo, hi] ⊆ [N/2, 5N/2]` (window is an Icc, hence convex).
    have hsub : Set.Icc lo hi ⊆ Set.Icc (N / 2) (5 * N / 2) :=
      Set.Icc_subset_Icc hloIcc.1 hhiIcc.2
    set L := hi - lo with hLdef
    have hLnn : 0 ≤ L := by rw [hLdef]; linarith
    rcases eq_or_lt_of_le hLnn with hL0 | hLpos
    · -- `L = 0`: span `= 0 ≤ 4√(δ/λ)`.
      linarith [hsqrt_nn, hL0]
    · -- `L > 0`: apply `majorArc_length_bound`.
      have hga : Set.Icc lo (lo + L) = Set.Icc lo hi := by rw [hLdef]; ring_nf
      -- `g ∈ C²` ⟹ `ContDiffOn`.
      have hgC2 : ContDiffOn ℝ 2 (lineRes f D) (Set.Icc lo (lo + L)) :=
        (contDiff_lineRes hf).contDiffOn
      -- `|g''| ≥ λ` on `[lo, lo+L]`.
      have hg2 : ∀ x ∈ Set.Icc lo (lo + L), lam ≤ |iteratedDeriv 2 (lineRes f D) x| := by
        intro x hx
        rw [hga] at hx
        rw [iteratedDeriv_two_lineRes hf]
        exact hlower x (hsub hx)
      -- `|g| ≤ δ` on `[lo, lo+L]` (= `[properLo', properHi']`), via #4.
      have hgδ : ∀ x ∈ Set.Icc lo (lo + L), |lineRes f D x| ≤ δ := by
        intro x hx
        rw [hga] at hx
        exact properArc'_continuous_strip hf hlam hN2 hlower hlomem hhimem hlohiZ x hx
      have hbound := majorArc_length_bound (g := lineRes f D) (a := lo) (L := L)
        (δ := δ) (Λlo := lam) hLpos hδ.le hgC2 hg2 hgδ
      -- `λ·L² ≤ 16δ ⟹ L ≤ 4√(δ/λ)`.  Goal is `L ≤ 4√(δ/λ)`.
      -- `L² ≤ 16δ/λ`, `L ≥ 0` ⟹ `L ≤ √(16δ/λ) = 4√(δ/λ)`.
      have hL2 : L ^ 2 ≤ 16 * (δ / lam) := by
        have h16 : 16 * (δ / lam) = 16 * δ / lam := by ring
        rw [h16, le_div_iff₀ hlam]
        nlinarith [hbound, hlam, hLnn]
      have hsqrt_eq : Real.sqrt (16 * (δ / lam)) = 4 * Real.sqrt (δ / lam) := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      calc L = Real.sqrt (L ^ 2) := (Real.sqrt_sq hLnn).symm
        _ ≤ Real.sqrt (16 * (δ / lam)) := Real.sqrt_le_sqrt hL2
        _ = 4 * Real.sqrt (δ / lam) := hsqrt_eq
  · -- empty: `properLo' = properHi' = 0`, span `= 0`.
    have hlo0 : properLo' f N δ D = 0 := by simp only [properLo', hne, dif_neg, not_false_iff]
    have hhi0 : properHi' f N δ D = 0 := by simp only [properHi', hne, dif_neg, not_false_iff]
    rw [hhi, hlo, hlo0, hhi0]
    simp only [Int.cast_zero, sub_zero]
    exact hsqrt_nn

end Squarefree.Geometry
