import Squarefree.Bracket.Sec7Defs
import Squarefree.Structure.FfunHighDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# §7 inverse defect map for `F_a`

This leaf builds the inverse map `dBreve = F_a⁻¹` used by the §7 phase package.  The
definition is global on `ℝ`, but the proved inverse and derivative facts are stated on the
positive `d`-window where `F_a` is strictly decreasing.  We avoid a quartic closed form for
the inverse: `dBreve` is the `invFun` of `F_a` restricted to positive `d`.
-/

open Classical Filter Real
open scoped Topology

namespace Squarefree

set_option maxHeartbeats 4000000

private instance : Nonempty {d : ℝ // 0 < d} := ⟨⟨1, by norm_num⟩⟩

/-! ## The `F_a` derivative tower as named scalar functions -/

private noncomputable def F₁ (X a d : ℝ) : ℝ :=
  -2 * X / d ^ 3 + 2 * X / (d + a) ^ 3

private noncomputable def F₂ (X a d : ℝ) : ℝ :=
  6 * X / d ^ 4 - 6 * X / (d + a) ^ 4

private noncomputable def F₃ (X a d : ℝ) : ℝ :=
  -24 * X / d ^ 5 + 24 * X / (d + a) ^ 5

private noncomputable def F₄ (X a d : ℝ) : ℝ :=
  120 * X / d ^ 6 - 120 * X / (d + a) ^ 6

private noncomputable def F₅ (X a d : ℝ) : ℝ :=
  -720 * X / d ^ 7 + 720 * X / (d + a) ^ 7

private theorem F₁_hasDerivAt {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => F₁ X a t) (F₂ X a d) d := by
  simpa [F₁, F₂] using Ffun_hasDerivAt2_d X a d hd hda

private theorem F₂_hasDerivAt {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => F₂ X a t) (F₃ X a d) d := by
  simpa [F₂, F₃] using Ffun_hasDerivAt3_d X a d hd hda

private theorem F₃_hasDerivAt {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => F₃ X a t) (F₄ X a d) d := by
  simpa [F₃, F₄] using Ffun_hasDerivAt4_d X a d hd hda

private theorem F₄_hasDerivAt {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => F₄ X a t) (F₅ X a d) d := by
  simpa [F₄, F₅] using Ffun_hasDerivAt5_d X a d hd hda

private theorem F₁_eq_deriv {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    F₁ X a d = deriv (fun t => Ffun X a t) d := by
  rw [Ffun_deriv_d X a d hd hda]
  rfl

private theorem F₁_neg {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    F₁ X a d < 0 := by
  have hda : d + a ≠ 0 := by positivity
  rw [F₁, Ffun_deriv1_factor X a d (ne_of_gt hd) hda]
  have hnum : 0 < 2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by positivity
  have hden : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
  rw [show -2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
        (d ^ 3 * (d + a) ^ 3)
      = -(2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
        (d ^ 3 * (d + a) ^ 3)) by ring]
  exact neg_neg_of_pos (div_pos hnum hden)

private theorem Ffun_strictAntiOn_pos {X a : ℝ} (hX : 0 < X) (ha : 0 < a) :
    StrictAntiOn (fun d => Ffun X a d) (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro d hd
    have hd0 : 0 < d := by simpa using hd
    exact (Ffun_contDiffAt4 (X := X) (a := a) (d := d)
      (ne_of_gt hd0) (by positivity)).continuousAt.continuousWithinAt
  · intro d hd
    have hd0 : 0 < d := by simpa using hd
    rw [← F₁_eq_deriv (X := X) (a := a) (d := d) (ne_of_gt hd0) (by positivity)]
    exact F₁_neg hX ha hd0

private theorem Ffun_posSubtype_injective {X a : ℝ} (hX : 0 < X) (ha : 0 < a) :
    Function.Injective (fun d : {d : ℝ // 0 < d} => Ffun X a d) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hltF := Ffun_strictAntiOn_pos hX ha x.property y.property hlt
    rw [hxy] at hltF
    exact (lt_irrefl _ hltF).elim
  · have hltF := Ffun_strictAntiOn_pos hX ha y.property x.property hgt
    rw [hxy] at hltF
    exact (lt_irrefl _ hltF).elim

/-! ## The inverse map -/

/-- The positive-branch inverse `d̆ₐ(t) = F_a⁻¹(t)`.

It is implemented as the inverse of `d ↦ Ffun X a d` on the positive subtype.  The value away
from the range of `F_a` is the arbitrary `Function.invFun` fallback; all API below is on
points `t = Ffun X a d` with `d > 0`. -/
noncomputable def dBreve (X a : ℝ) (t : ℝ) : ℝ :=
  (Function.invFun (fun d : {d : ℝ // 0 < d} => Ffun X a d) t).1

/-- The global `invFun` branch always returns a positive representative. -/
theorem dBreve_pos {X a t : ℝ} : 0 < dBreve X a t := by
  unfold dBreve
  exact (Function.invFun (fun d : {d : ℝ // 0 < d} => Ffun X a d) t).property

/-- First derivative of `dBreve`, in inverse-function form. -/
noncomputable def dBreve' (X a : ℝ) (t : ℝ) : ℝ :=
  (F₁ X a (dBreve X a t))⁻¹

/-- Second derivative of `dBreve`, in inverse-function form. -/
noncomputable def dBreve'' (X a : ℝ) (t : ℝ) : ℝ :=
  - F₂ X a (dBreve X a t) / (F₁ X a (dBreve X a t)) ^ 3

/-- Third derivative of `dBreve`, in inverse-function form. -/
noncomputable def dBreve''' (X a : ℝ) (t : ℝ) : ℝ :=
  3 * (F₂ X a (dBreve X a t)) ^ 2 / (F₁ X a (dBreve X a t)) ^ 5
    - F₃ X a (dBreve X a t) / (F₁ X a (dBreve X a t)) ^ 4

/-- Fourth derivative of `dBreve`, in inverse-function form. -/
noncomputable def dBreve'''' (X a : ℝ) (t : ℝ) : ℝ :=
  -15 * (F₂ X a (dBreve X a t)) ^ 3 / (F₁ X a (dBreve X a t)) ^ 7
    + 10 * F₂ X a (dBreve X a t) * F₃ X a (dBreve X a t) /
        (F₁ X a (dBreve X a t)) ^ 6
    - F₄ X a (dBreve X a t) / (F₁ X a (dBreve X a t)) ^ 5

/-- Fifth derivative of `dBreve`, in inverse-function form. -/
noncomputable def dBreve''''' (X a : ℝ) (t : ℝ) : ℝ :=
  105 * (F₂ X a (dBreve X a t)) ^ 4 / (F₁ X a (dBreve X a t)) ^ 9
    - 105 * (F₂ X a (dBreve X a t)) ^ 2 * F₃ X a (dBreve X a t) /
        (F₁ X a (dBreve X a t)) ^ 8
    + 10 * (F₃ X a (dBreve X a t)) ^ 2 / (F₁ X a (dBreve X a t)) ^ 7
    + 15 * F₂ X a (dBreve X a t) * F₄ X a (dBreve X a t) /
        (F₁ X a (dBreve X a t)) ^ 7
    - F₅ X a (dBreve X a t) / (F₁ X a (dBreve X a t)) ^ 6

/-- `dBreve` is a left inverse of `Ffun X a` on the positive branch. -/
theorem dBreve_spec {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve X a (Ffun X a d) = d := by
  unfold dBreve
  exact congrArg Subtype.val
    (Function.leftInverse_invFun (Ffun_posSubtype_injective hX ha) ⟨d, hd⟩)

/-- `dBreve` is a right inverse at every point known to be in the positive-branch range.

This is the range-level bridge for the global `invFun` definition.  Window-specific callers
still have to prove that their `t` lies in the range of `d ↦ Ffun X a d` on positive `d`. -/
theorem Ffun_dBreve_id_of_mem_range {X a t : ℝ}
    (ht : t ∈ Set.range (fun d : {d : ℝ // 0 < d} => Ffun X a d)) :
    Ffun X a (dBreve X a t) = t := by
  unfold dBreve
  simpa using
    (Function.invFun_eq (f := fun d : {d : ℝ // 0 < d} => Ffun X a d)
      (b := t) (by simpa [Set.mem_range] using ht))

/-- Image-point form of the right-inverse bridge. -/
theorem Ffun_dBreve_id_of_Ffun {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    Ffun X a (dBreve X a (Ffun X a d)) = Ffun X a d := by
  rw [dBreve_spec hX ha hd]

private theorem dBreve_eventually_left_inverse {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ x in 𝓝 d, dBreve X a (Ffun X a x) = x := by
  filter_upwards [eventually_gt_nhds hd] with x hx
  exact dBreve_spec hX ha hx

/-- `dBreve` has derivative `1/F_a'(d)` at `F_a(d)`. -/
theorem dBreve_hasDerivAt_Ffun {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (dBreve X a) (dBreve' X a (Ffun X a d)) (Ffun X a d) := by
  have hda : d + a ≠ 0 := by positivity
  have hf : HasDerivAt (fun t => Ffun X a t) (F₁ X a d) d := by
    simpa [F₁] using Ffun_hasDerivAt_d X a d (ne_of_gt hd) hda
  have hstrict : HasStrictDerivAt (fun t => Ffun X a t) (F₁ X a d) d :=
    (Ffun_contDiffAt4 (X := X) (a := a) (d := d) (ne_of_gt hd) hda).hasStrictDerivAt'
      hf (by norm_num : (4 : WithTop ℕ∞) ≠ 0)
  have hne : F₁ X a d ≠ 0 := ne_of_lt (F₁_neg hX ha hd)
  have hloc := dBreve_eventually_left_inverse hX ha hd
  have hderiv := (hstrict.to_local_left_inverse hne hloc).hasDerivAt
  rw [dBreve', dBreve_spec hX ha hd]
  exact hderiv

/-- The first inverse-derivative expression has derivative `dBreve''` at image points. -/
theorem dBreve_deriv1_hasDerivAt_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (dBreve' X a) (dBreve'' X a (Ffun X a d)) (Ffun X a d) := by
  set t0 := Ffun X a d with ht0
  set A := F₁ X a d with hA_def
  set B := F₂ X a d with hB_def
  have hda : d + a ≠ 0 := by positivity
  have hA_ne : A ≠ 0 := by
    rw [hA_def]
    exact ne_of_lt (F₁_neg hX ha hd)
  have hD : HasDerivAt (dBreve X a) A⁻¹ t0 := by
    have h := dBreve_hasDerivAt_Ffun hX ha hd
    rw [dBreve', dBreve_spec hX ha hd] at h
    simpa [ht0, hA_def] using h
  have hDval : dBreve X a t0 = d := by
    rw [ht0]
    exact dBreve_spec hX ha hd
  have hAcomp_ne : F₁ X a (dBreve X a t0) ≠ 0 := by
    rw [hDval, ← hA_def]
    exact hA_ne
  have hAcomp : HasDerivAt (fun t => F₁ X a (dBreve X a t)) (B * A⁻¹) t0 := by
    have hF₁ : HasDerivAt (fun t => F₁ X a t) B (dBreve X a t0) := by
      rw [hDval]
      simpa [hB_def] using F₁_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₁.comp t0 hD
  have hraw : HasDerivAt (dBreve' X a)
      (-(B * A⁻¹) / (F₁ X a (dBreve X a t0)) ^ 2) t0 := by
    simpa [dBreve'] using hAcomp.inv hAcomp_ne
  have hval : -(B * A⁻¹) / (F₁ X a (dBreve X a t0)) ^ 2 = dBreve'' X a t0 := by
    rw [dBreve'', ht0, dBreve_spec hX ha hd, hA_def, hB_def]
    field_simp [hA_ne]
  simpa [hval]
    using hraw

/-- The second inverse-derivative expression has derivative `dBreve'''` at image points. -/
theorem dBreve_deriv2_hasDerivAt_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (dBreve'' X a) (dBreve''' X a (Ffun X a d)) (Ffun X a d) := by
  set t0 := Ffun X a d with ht0
  set A := F₁ X a d with hA_def
  set B := F₂ X a d with hB_def
  set C := F₃ X a d with hC_def
  have hda : d + a ≠ 0 := by positivity
  have hA_ne : A ≠ 0 := by
    rw [hA_def]
    exact ne_of_lt (F₁_neg hX ha hd)
  have hDval : dBreve X a t0 = d := by
    rw [ht0]
    exact dBreve_spec hX ha hd
  have hD : HasDerivAt (dBreve X a) A⁻¹ t0 := by
    have h := dBreve_hasDerivAt_Ffun hX ha hd
    rw [dBreve', dBreve_spec hX ha hd] at h
    simpa [ht0, hA_def] using h
  have hAcomp : HasDerivAt (fun t => F₁ X a (dBreve X a t)) (B * A⁻¹) t0 := by
    have hF₁ : HasDerivAt (fun t => F₁ X a t) B (dBreve X a t0) := by
      rw [hDval]
      simpa [hB_def] using F₁_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₁.comp t0 hD
  have hBcomp : HasDerivAt (fun t => F₂ X a (dBreve X a t)) (C * A⁻¹) t0 := by
    have hF₂ : HasDerivAt (fun t => F₂ X a t) C (dBreve X a t0) := by
      rw [hDval]
      simpa [hC_def] using F₂_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₂.comp t0 hD
  have hnum : HasDerivAt (fun t => -F₂ X a (dBreve X a t)) (-(C * A⁻¹)) t0 :=
    hBcomp.neg
  have hden : HasDerivAt (fun t => (F₁ X a (dBreve X a t)) ^ 3)
      (3 * (F₁ X a (dBreve X a t0)) ^ 2 * (B * A⁻¹)) t0 := by
    simpa using hAcomp.pow 3
  have hden_ne : (F₁ X a (dBreve X a t0)) ^ 3 ≠ 0 := by
    rw [hDval, ← hA_def]
    exact pow_ne_zero 3 hA_ne
  have hraw : HasDerivAt (dBreve'' X a)
      (((-(C * A⁻¹)) * (F₁ X a (dBreve X a t0)) ^ 3
          - (-(F₂ X a (dBreve X a t0)))
            * (3 * (F₁ X a (dBreve X a t0)) ^ 2 * (B * A⁻¹))) /
        ((F₁ X a (dBreve X a t0)) ^ 3) ^ 2) t0 := by
    have hq := hnum.div hden hden_ne
    simpa [dBreve''] using hq
  have hval :
      ((-(C * A⁻¹ * (F₁ X a (dBreve X a t0)) ^ 3)
          + F₂ X a (dBreve X a t0)
            * (3 * (F₁ X a (dBreve X a t0)) ^ 2 * (B * A⁻¹))) /
        ((F₁ X a (dBreve X a t0)) ^ 3) ^ 2)
        = dBreve''' X a t0 := by
    rw [hDval, dBreve''', ht0, dBreve_spec hX ha hd, hA_def, hB_def, hC_def]
    field_simp [hA_ne]
    ring
  simpa [hval] using hraw

/-- The third inverse-derivative expression has derivative `dBreve''''` at image points. -/
theorem dBreve_deriv3_hasDerivAt_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (dBreve''' X a) (dBreve'''' X a (Ffun X a d)) (Ffun X a d) := by
  set t0 := Ffun X a d with ht0
  set A := F₁ X a d with hA_def
  set B := F₂ X a d with hB_def
  set C := F₃ X a d with hC_def
  set E := F₄ X a d with hE_def
  have hda : d + a ≠ 0 := by positivity
  have hA_ne : A ≠ 0 := by
    rw [hA_def]
    exact ne_of_lt (F₁_neg hX ha hd)
  have hDval : dBreve X a t0 = d := by
    rw [ht0]
    exact dBreve_spec hX ha hd
  have hD : HasDerivAt (dBreve X a) A⁻¹ t0 := by
    have h := dBreve_hasDerivAt_Ffun hX ha hd
    rw [dBreve', dBreve_spec hX ha hd] at h
    simpa [ht0, hA_def] using h
  have hAcomp : HasDerivAt (fun t => F₁ X a (dBreve X a t)) (B * A⁻¹) t0 := by
    have hF₁ : HasDerivAt (fun t => F₁ X a t) B (dBreve X a t0) := by
      rw [hDval]
      simpa [hB_def] using F₁_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₁.comp t0 hD
  have hBcomp : HasDerivAt (fun t => F₂ X a (dBreve X a t)) (C * A⁻¹) t0 := by
    have hF₂ : HasDerivAt (fun t => F₂ X a t) C (dBreve X a t0) := by
      rw [hDval]
      simpa [hC_def] using F₂_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₂.comp t0 hD
  have hCcomp : HasDerivAt (fun t => F₃ X a (dBreve X a t)) (E * A⁻¹) t0 := by
    have hF₃ : HasDerivAt (fun t => F₃ X a t) E (dBreve X a t0) := by
      rw [hDval]
      simpa [hE_def] using F₃_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₃.comp t0 hD
  have hA5_ne : (F₁ X a (dBreve X a t0)) ^ 5 ≠ 0 := by
    rw [hDval, ← hA_def]
    exact pow_ne_zero 5 hA_ne
  have hA4_ne : (F₁ X a (dBreve X a t0)) ^ 4 ≠ 0 := by
    rw [hDval, ← hA_def]
    exact pow_ne_zero 4 hA_ne
  have hBsq : HasDerivAt (fun t => (F₂ X a (dBreve X a t)) ^ 2)
      (2 * (F₂ X a (dBreve X a t0)) ^ 1 * (C * A⁻¹)) t0 := by
    simpa using hBcomp.pow 2
  have hnum1 : HasDerivAt (fun t => 3 * (F₂ X a (dBreve X a t)) ^ 2)
      (3 * (2 * (F₂ X a (dBreve X a t0)) ^ 1 * (C * A⁻¹))) t0 := by
    simpa using hBsq.const_mul 3
  have hden1 : HasDerivAt (fun t => (F₁ X a (dBreve X a t)) ^ 5)
      (5 * (F₁ X a (dBreve X a t0)) ^ 4 * (B * A⁻¹)) t0 := by
    simpa using hAcomp.pow 5
  have hterm1 := hnum1.div hden1 hA5_ne
  have hden2 : HasDerivAt (fun t => (F₁ X a (dBreve X a t)) ^ 4)
      (4 * (F₁ X a (dBreve X a t0)) ^ 3 * (B * A⁻¹)) t0 := by
    simpa using hAcomp.pow 4
  have hterm2 := hCcomp.div hden2 hA4_ne
  have hraw0 := hterm1.sub hterm2
  convert hraw0 using 1
  rw [hDval, dBreve'''', ht0, dBreve_spec hX ha hd, hA_def, hB_def, hC_def, hE_def]
  field_simp [hA_ne]
  ring

/-- The fourth inverse-derivative expression has derivative `dBreve'''''` at image points. -/
theorem dBreve_deriv4_hasDerivAt_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (dBreve'''' X a) (dBreve''''' X a (Ffun X a d)) (Ffun X a d) := by
  set t0 := Ffun X a d with ht0
  set A := F₁ X a d with hA_def
  set B := F₂ X a d with hB_def
  set C := F₃ X a d with hC_def
  set E := F₄ X a d with hE_def
  set G := F₅ X a d with hG_def
  have hda : d + a ≠ 0 := by positivity
  have hA_ne : A ≠ 0 := by
    rw [hA_def]
    exact ne_of_lt (F₁_neg hX ha hd)
  have hDval : dBreve X a t0 = d := by
    rw [ht0]
    exact dBreve_spec hX ha hd
  have hD : HasDerivAt (dBreve X a) A⁻¹ t0 := by
    have h := dBreve_hasDerivAt_Ffun hX ha hd
    rw [dBreve', dBreve_spec hX ha hd] at h
    simpa [ht0, hA_def] using h
  have hAcomp : HasDerivAt (fun t => F₁ X a (dBreve X a t)) (B * A⁻¹) t0 := by
    have hF₁ : HasDerivAt (fun t => F₁ X a t) B (dBreve X a t0) := by
      rw [hDval]
      simpa [hB_def] using F₁_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₁.comp t0 hD
  have hBcomp : HasDerivAt (fun t => F₂ X a (dBreve X a t)) (C * A⁻¹) t0 := by
    have hF₂ : HasDerivAt (fun t => F₂ X a t) C (dBreve X a t0) := by
      rw [hDval]
      simpa [hC_def] using F₂_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₂.comp t0 hD
  have hCcomp : HasDerivAt (fun t => F₃ X a (dBreve X a t)) (E * A⁻¹) t0 := by
    have hF₃ : HasDerivAt (fun t => F₃ X a t) E (dBreve X a t0) := by
      rw [hDval]
      simpa [hE_def] using F₃_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₃.comp t0 hD
  have hEcomp : HasDerivAt (fun t => F₄ X a (dBreve X a t)) (G * A⁻¹) t0 := by
    have hF₄ : HasDerivAt (fun t => F₄ X a t) G (dBreve X a t0) := by
      rw [hDval]
      simpa [hG_def] using F₄_hasDerivAt (X := X) (a := a) (d := d) (ne_of_gt hd) hda
    simpa using hF₄.comp t0 hD
  have hA7_ne : (F₁ X a (dBreve X a t0)) ^ 7 ≠ 0 := by
    rw [hDval, ← hA_def]
    exact pow_ne_zero 7 hA_ne
  have hA6_ne : (F₁ X a (dBreve X a t0)) ^ 6 ≠ 0 := by
    rw [hDval, ← hA_def]
    exact pow_ne_zero 6 hA_ne
  have hA5_ne : (F₁ X a (dBreve X a t0)) ^ 5 ≠ 0 := by
    rw [hDval, ← hA_def]
    exact pow_ne_zero 5 hA_ne
  have hBcube : HasDerivAt (fun t => (F₂ X a (dBreve X a t)) ^ 3)
      (3 * (F₂ X a (dBreve X a t0)) ^ 2 * (C * A⁻¹)) t0 := by
    simpa using hBcomp.pow 3
  have hnum1 : HasDerivAt (fun t => -15 * (F₂ X a (dBreve X a t)) ^ 3)
      (-15 * (3 * (F₂ X a (dBreve X a t0)) ^ 2 * (C * A⁻¹))) t0 := by
    simpa using hBcube.const_mul (-15)
  have hden1 : HasDerivAt (fun t => (F₁ X a (dBreve X a t)) ^ 7)
      (7 * (F₁ X a (dBreve X a t0)) ^ 6 * (B * A⁻¹)) t0 := by
    simpa using hAcomp.pow 7
  have hterm1 := hnum1.div hden1 hA7_ne
  have hBC : HasDerivAt
      (fun t => F₂ X a (dBreve X a t) * F₃ X a (dBreve X a t))
      ((C * A⁻¹) * F₃ X a (dBreve X a t0)
        + F₂ X a (dBreve X a t0) * (E * A⁻¹)) t0 := by
    simpa using hBcomp.mul hCcomp
  have hnum2 : HasDerivAt
      (fun t => 10 * (F₂ X a (dBreve X a t) * F₃ X a (dBreve X a t)))
      (10 * ((C * A⁻¹) * F₃ X a (dBreve X a t0)
        + F₂ X a (dBreve X a t0) * (E * A⁻¹))) t0 := by
    simpa using hBC.const_mul 10
  have hden2 : HasDerivAt (fun t => (F₁ X a (dBreve X a t)) ^ 6)
      (6 * (F₁ X a (dBreve X a t0)) ^ 5 * (B * A⁻¹)) t0 := by
    simpa using hAcomp.pow 6
  have hterm2 := hnum2.div hden2 hA6_ne
  have hden3 : HasDerivAt (fun t => (F₁ X a (dBreve X a t)) ^ 5)
      (5 * (F₁ X a (dBreve X a t0)) ^ 4 * (B * A⁻¹)) t0 := by
    simpa using hAcomp.pow 5
  have hterm3 := hEcomp.div hden3 hA5_ne
  have hraw0 := (hterm1.add hterm2).sub hterm3
  convert hraw0 using 1
  · funext t
    simp [dBreve'''']
    ring
  · rw [hDval, dBreve''''', ht0, dBreve_spec hX ha hd,
      hA_def, hB_def, hC_def, hE_def, hG_def]
    field_simp [hA_ne]
    ring

/-! ## Sympy-verified high-order closed forms -/

/-- Factored closed form for the third inverse derivative at image points.

Sympy check:
`3(F'')²/(F')⁵ - F'''/(F')⁴`
factors to the displayed expression after substituting the factored `F`-derivatives. -/
theorem dBreve_deriv3_factor_image {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve''' X a (Ffun X a d) =
      -3 * d ^ 7 * (d + a) ^ 7
        * (5 * a ^ 6 + 40 * a ^ 5 * d + 140 * a ^ 4 * d ^ 2
          + 284 * a ^ 3 * d ^ 3 + 352 * a ^ 2 * d ^ 4
          + 252 * a * d ^ 5 + 84 * d ^ 6)
        / (8 * X ^ 3 * a ^ 3 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 5) := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hP : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [dBreve''', dBreve_spec hX ha hd]
  unfold F₁ F₂ F₃
  rw [Ffun_deriv1_factor X a d hdne hda,
    Ffun_deriv2_factor X a d hdne hda,
    Ffun_deriv3_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hP]
  ring

/-- Factored closed form for the fourth inverse derivative at image points.

Sympy check:
`-15(F'')³/(F')⁷ + 10F''F'''/(F')⁶ - F''''/(F')⁵`
factors to the displayed expression after substituting the factored `F`-derivatives. -/
theorem dBreve_deriv4_factor_image {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve'''' X a (Ffun X a d) =
      15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d)
        * (7 * a ^ 8 + 70 * a ^ 7 * d + 322 * a ^ 6 * d ^ 2
          + 912 * a ^ 5 * d ^ 3 + 1728 * a ^ 4 * d ^ 4
          + 2232 * a ^ 3 * d ^ 5 + 1920 * a ^ 2 * d ^ 6
          + 1008 * a * d ^ 7 + 252 * d ^ 8)
        / (16 * X ^ 4 * a ^ 4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 7) := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hP : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [dBreve'''', dBreve_spec hX ha hd]
  unfold F₁ F₂ F₃ F₄
  rw [Ffun_deriv1_factor X a d hdne hda,
    Ffun_deriv2_factor X a d hdne hda,
    Ffun_deriv3_factor X a d hdne hda,
    Ffun_deriv4_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hP]
  ring

/-- Factored closed form for the fifth inverse derivative at image points.

Sympy check:
`105(F'')⁴/(F')⁹ - 105(F'')²F'''/(F')⁸ + 10(F''')²/(F')⁷
  + 15F''F''''/(F')⁷ - F'''''/(F')⁶`
factors to the displayed expression after substituting the factored `F`-derivatives. -/
theorem dBreve_deriv5_factor_image {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve''''' X a (Ffun X a d) =
      -45 * d ^ 11 * (d + a) ^ 11
        * (21 * a ^ 12 + 336 * a ^ 11 * d + 2520 * a ^ 10 * d ^ 2
          + 11852 * a ^ 9 * d ^ 3 + 39104 * a ^ 8 * d ^ 4
          + 95348 * a ^ 7 * d ^ 5 + 175964 * a ^ 6 * d ^ 6
          + 247424 * a ^ 5 * d ^ 7 + 262988 * a ^ 4 * d ^ 8
          + 206160 * a ^ 3 * d ^ 9 + 113304 * a ^ 2 * d ^ 10
          + 39312 * a * d ^ 11 + 6552 * d ^ 12)
        / (32 * X ^ 5 * a ^ 5 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 9) := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hP : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [dBreve''''', dBreve_spec hX ha hd]
  unfold F₁ F₂ F₃ F₄ F₅
  rw [Ffun_deriv1_factor X a d hdne hda,
    Ffun_deriv2_factor X a d hdne hda,
    Ffun_deriv3_factor X a d hdne hda,
    Ffun_deriv4_factor X a d hdne hda,
    Ffun_deriv5_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hP]
  ring

/-- Exact magnitude of the third inverse derivative at image points. -/
theorem dBreve_deriv3_abs_factor_image {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |dBreve''' X a (Ffun X a d)| =
      3 * d ^ 7 * (d + a) ^ 7
        * (5 * a ^ 6 + 40 * a ^ 5 * d + 140 * a ^ 4 * d ^ 2
          + 284 * a ^ 3 * d ^ 3 + 352 * a ^ 2 * d ^ 4
          + 252 * a * d ^ 5 + 84 * d ^ 6)
        / (8 * X ^ 3 * a ^ 3 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 5) := by
  rw [dBreve_deriv3_factor_image hX ha hd]
  rw [show -3 * d ^ 7 * (d + a) ^ 7
        * (5 * a ^ 6 + 40 * a ^ 5 * d + 140 * a ^ 4 * d ^ 2
          + 284 * a ^ 3 * d ^ 3 + 352 * a ^ 2 * d ^ 4
          + 252 * a * d ^ 5 + 84 * d ^ 6)
        / (8 * X ^ 3 * a ^ 3 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 5)
      = -(3 * d ^ 7 * (d + a) ^ 7
        * (5 * a ^ 6 + 40 * a ^ 5 * d + 140 * a ^ 4 * d ^ 2
          + 284 * a ^ 3 * d ^ 3 + 352 * a ^ 2 * d ^ 4
          + 252 * a * d ^ 5 + 84 * d ^ 6)
        / (8 * X ^ 3 * a ^ 3 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 5)) by ring]
  rw [abs_neg, abs_of_nonneg]
  positivity

/-- Exact magnitude of the fourth inverse derivative at image points. -/
theorem dBreve_deriv4_abs_factor_image {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |dBreve'''' X a (Ffun X a d)| =
      15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d)
        * (7 * a ^ 8 + 70 * a ^ 7 * d + 322 * a ^ 6 * d ^ 2
          + 912 * a ^ 5 * d ^ 3 + 1728 * a ^ 4 * d ^ 4
          + 2232 * a ^ 3 * d ^ 5 + 1920 * a ^ 2 * d ^ 6
          + 1008 * a * d ^ 7 + 252 * d ^ 8)
        / (16 * X ^ 4 * a ^ 4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 7) := by
  rw [dBreve_deriv4_factor_image hX ha hd, abs_of_nonneg]
  positivity

/-- Exact magnitude of the fifth inverse derivative at image points. -/
theorem dBreve_deriv5_abs_factor_image {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |dBreve''''' X a (Ffun X a d)| =
      45 * d ^ 11 * (d + a) ^ 11
        * (21 * a ^ 12 + 336 * a ^ 11 * d + 2520 * a ^ 10 * d ^ 2
          + 11852 * a ^ 9 * d ^ 3 + 39104 * a ^ 8 * d ^ 4
          + 95348 * a ^ 7 * d ^ 5 + 175964 * a ^ 6 * d ^ 6
          + 247424 * a ^ 5 * d ^ 7 + 262988 * a ^ 4 * d ^ 8
          + 206160 * a ^ 3 * d ^ 9 + 113304 * a ^ 2 * d ^ 10
          + 39312 * a * d ^ 11 + 6552 * d ^ 12)
        / (32 * X ^ 5 * a ^ 5 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 9) := by
  rw [dBreve_deriv5_factor_image hX ha hd]
  rw [show -45 * d ^ 11 * (d + a) ^ 11
        * (21 * a ^ 12 + 336 * a ^ 11 * d + 2520 * a ^ 10 * d ^ 2
          + 11852 * a ^ 9 * d ^ 3 + 39104 * a ^ 8 * d ^ 4
          + 95348 * a ^ 7 * d ^ 5 + 175964 * a ^ 6 * d ^ 6
          + 247424 * a ^ 5 * d ^ 7 + 262988 * a ^ 4 * d ^ 8
          + 206160 * a ^ 3 * d ^ 9 + 113304 * a ^ 2 * d ^ 10
          + 39312 * a * d ^ 11 + 6552 * d ^ 12)
        / (32 * X ^ 5 * a ^ 5 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 9)
      = -(45 * d ^ 11 * (d + a) ^ 11
        * (21 * a ^ 12 + 336 * a ^ 11 * d + 2520 * a ^ 10 * d ^ 2
          + 11852 * a ^ 9 * d ^ 3 + 39104 * a ^ 8 * d ^ 4
          + 95348 * a ^ 7 * d ^ 5 + 175964 * a ^ 6 * d ^ 6
          + 247424 * a ^ 5 * d ^ 7 + 262988 * a ^ 4 * d ^ 8
          + 206160 * a ^ 3 * d ^ 9 + 113304 * a ^ 2 * d ^ 10
          + 39312 * a * d ^ 11 + 6552 * d ^ 12)
        / (32 * X ^ 5 * a ^ 5 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 9)) by ring]
  rw [abs_neg, abs_of_nonneg]
  positivity

/-! ## Image-window scale bounds -/

private theorem XA_div_D3_eq_F {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 3 = S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem Ffun_mono_a {X d a b : ℝ} (hX : 0 < X) (hd : 0 < d)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Ffun X a d ≤ Ffun X b d := by
  have hda_pos : 0 < d + a := by positivity
  have hdb_pos : 0 < d + b := by nlinarith
  unfold Ffun
  have hp : (d + a) ^ 2 ≤ (d + b) ^ 2 :=
    pow_le_pow_left₀ hda_pos.le (by linarith) 2
  have hdiv : X / (d + b) ^ 2 ≤ X / (d + a) ^ 2 :=
    div_le_div_of_nonneg_left hX.le (pow_pos hda_pos 2) hp
  linarith

private theorem Ffun_thirtyD_le_tWin_lo {P : Globals} {S : Scale P} {a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) :
    Ffun P.X a (30 * S.D) ≤ S.F / sec7_cWin := by
  have hX : 0 < P.X := P.X_pos
  have hD : 0 < S.D := S.D_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hAleD : S.A ≤ S.D / 10 := by nlinarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < 30 * S.D := by positivity
  have hda : 30 * S.D + a ≠ 0 := by positivity
  calc Ffun P.X a (30 * S.D)
      = P.X * a * (a + 2 * (30 * S.D)) /
          ((30 * S.D) ^ 2 * (30 * S.D + a) ^ 2) := by
          rw [Ffun_factor' P.X a (30 * S.D) (ne_of_gt hd0) hda]
    _ ≤ P.X * a * (a + 2 * (30 * S.D)) /
          ((30 * S.D) ^ 2 * (30 * S.D) ^ 2) := by
          gcongr
          linarith
    _ ≤ P.X * (11 * S.A) * ((11 / 10 : ℝ) * S.D + 2 * (30 * S.D)) /
          ((30 * S.D) ^ 2 * (30 * S.D) ^ 2) := by
          gcongr
          nlinarith [ha_hi, hAleD]
    _ ≤ S.F / sec7_cWin := by
          rw [← XA_div_D3_eq_F S, sec7_cWin]
          field_simp [hD.ne']
          nlinarith [hX, hD, hApos, hAleD]

private theorem tWin_hi_le_Ffun_sixteenthD {P : Globals} {S : Scale P} {a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) :
    sec7_cWin * S.F ≤ Ffun P.X a (S.D / 16) := by
  have hX : 0 < P.X := P.X_pos
  have hD : 0 < S.D := S.D_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hAleD : S.A ≤ S.D / 10 := by nlinarith
  have hd0 : 0 < S.D / 16 := by positivity
  have hbase_le : Ffun P.X (S.A / 5) (S.D / 16) ≤ Ffun P.X a (S.D / 16) :=
    Ffun_mono_a P.X_pos hd0 (by positivity : 0 ≤ S.A / 5) ha_lo
  refine le_trans ?_ hbase_le
  have hda : S.D / 16 + S.A / 5 ≠ 0 := by positivity
  rw [Ffun_factor' P.X (S.A / 5) (S.D / 16) (ne_of_gt hd0) hda,
    ← XA_div_D3_eq_F S, sec7_cWin]
  field_simp [hD.ne']
  have hA2 : S.A ^ 2 ≤ (S.D / 10) ^ 2 := pow_le_pow_left₀ hApos.le hAleD 2
  have hADmul : S.A * S.D ≤ (S.D / 10) * S.D :=
    mul_le_mul_of_nonneg_right hAleD hD.le
  nlinarith [hX, hD, hApos, hAleD, hA2, hADmul]

/-- Points in the §7 `t`-window are represented by the positive inverse branch, with image
window `d̆(t) ∈ [D/16, 30D]`. -/
theorem dBreve_sec7_tWin_image {P : Globals} {S : Scale P} {a t : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (ht : t ∈ sec7_tWin S) :
    Ffun P.X a (dBreve P.X a t) = t ∧
      S.D / 16 ≤ dBreve P.X a t ∧ dBreve P.X a t ≤ 30 * S.D := by
  have hD : 0 < S.D := S.D_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hlohi : S.D / 16 ≤ 30 * S.D := by nlinarith
  have hcont : ContinuousOn (fun x => Ffun P.X a x) (Set.Icc (S.D / 16) (30 * S.D)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hx.1
    have hxa : x + a ≠ 0 := by positivity
    exact (Ffun_contDiffAt4 (X := P.X) (a := a) (d := x)
      (ne_of_gt hx0) hxa).continuousAt.continuousWithinAt
  have htIcc : t ∈ Set.Icc (Ffun P.X a (30 * S.D)) (Ffun P.X a (S.D / 16)) := by
    simp only [sec7_tWin, Set.mem_Icc] at ht
    exact ⟨le_trans (Ffun_thirtyD_le_tWin_lo hAD ha_lo ha_hi) ht.1,
      le_trans ht.2 (tWin_hi_le_Ffun_sixteenthD hAD ha_lo)⟩
  rcases intermediate_value_Icc' hlohi hcont htIcc with ⟨d, hdmem, hdt⟩
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hdmem.1
  have hdb : dBreve P.X a t = d := by
    rw [← hdt]
    exact dBreve_spec P.X_pos ha0 hd0
  rw [hdb]
  exact ⟨hdt, hdmem⟩

private theorem dBreve_deriv1_tnorm_identity {P : Globals} {S : Scale P} {a d : ℝ}
    (ha0 : 0 < a) (hd0 : 0 < d) :
    (Ffun P.X a d / S.F) *
        ((S.F * |dBreve' P.X a (Ffun P.X a d)|) / S.D) =
      (d + a) * (a + 2 * d) /
        (2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) * (d / S.D) := by
  have hD : 0 < S.D := S.D_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hF : 0 < S.F := by unfold Scale.F; positivity
  have hda : d + a ≠ 0 := by positivity
  have hX : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hQpos : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
  rw [dBreve', dBreve_spec P.X_pos ha0 hd0]
  unfold F₁
  rw [Ffun_deriv1_factor P.X a d (ne_of_gt hd0) hda,
    Ffun_factor' P.X a d (ne_of_gt hd0) hda]
  rw [show -2 * P.X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
        (d ^ 3 * (d + a) ^ 3) =
      -(2 * P.X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
        (d ^ 3 * (d + a) ^ 3)) by ring]
  rw [abs_inv, abs_neg, abs_of_pos]
  · rw [← XA_div_D3_eq_F S]
    field_simp [hD.ne', hF.ne', hX.ne', hApos.ne', ha0.ne', hd0.ne', hda, hQpos.ne']
  · positivity

private theorem dBreve_deriv2_abs_factor_image {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |dBreve'' X a (Ffun X a d)| =
      3 * d ^ 5 * (d + a) ^ 5 * (a + 2 * d) *
          (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
        (4 * X ^ 2 * a ^ 2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3) := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hQpos : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
  have hQne : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := ne_of_gt hQpos
  have hval : dBreve'' X a (Ffun X a d) =
      3 * d ^ 5 * (d + a) ^ 5 * (a + 2 * d) *
          (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
        (4 * X ^ 2 * a ^ 2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3) := by
    rw [dBreve'', dBreve_spec hX ha hd]
    unfold F₁ F₂
    rw [Ffun_deriv1_factor X a d hdne hda, Ffun_deriv2_factor X a d hdne hda]
    field_simp [hXne, hane, hdne, hda, hQne]
    ring
  rw [hval, abs_of_pos]
  positivity

private theorem dBreve_deriv2_tnorm_identity {P : Globals} {S : Scale P} {a d : ℝ}
    (ha0 : 0 < a) (hd0 : 0 < d) :
    (Ffun P.X a d / S.F) ^ 2 *
        ((S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d)|) / S.D) =
      (3 * (d + a) * (a + 2 * d) ^ 3 *
          (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
        (4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3)) * (d / S.D) := by
  have hD : 0 < S.D := S.D_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hF : 0 < S.F := by unfold Scale.F; positivity
  have hda : d + a ≠ 0 := by positivity
  have hX : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hQpos : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
  rw [dBreve_deriv2_abs_factor_image P.X_pos ha0 hd0,
    Ffun_factor' P.X a d (ne_of_gt hd0) hda, ← XA_div_D3_eq_F S]
  field_simp [hD.ne', hF.ne', hX.ne', hApos.ne', ha0.ne', hd0.ne', hda, hQpos.ne']

private theorem dBreve_deriv1_tnorm_factor_bounds {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    (1 / 3 : ℝ) ≤
        (d + a) * (a + 2 * d) /
          (2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) ∧
      (d + a) * (a + 2 * d) /
          (2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) ≤ (1 / 2 : ℝ) := by
  have hQ : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ (by positivity : 0 < 2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2))]
    nlinarith [mul_pos ha hd, sq_nonneg a, sq_nonneg d]
  · rw [div_le_iff₀ (by positivity : 0 < 2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2))]
    nlinarith [sq_nonneg d]

private theorem dBreve_deriv2_tnorm_factor_bounds {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    (4 / 9 : ℝ) ≤
        3 * (d + a) * (a + 2 * d) ^ 3 *
            (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
          (4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3) ∧
      3 * (d + a) * (a + 2 * d) ^ 3 *
            (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
          (4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3) ≤ (3 / 4 : ℝ) := by
  have hQ : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ (by positivity : 0 < 4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3)]
    have hdiff : 27 * ((d + a) * (a + 2 * d) ^ 3 *
          (a ^ 2 + 2 * a * d + 2 * d ^ 2)) -
        16 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3 =
        a * (11 * a ^ 5 + 99 * a ^ 4 * d + 342 * a ^ 3 * d ^ 2 +
          594 * a ^ 2 * d ^ 3 + 540 * a * d ^ 4 + 216 * d ^ 5) := by ring
    have hnon : 0 ≤ 27 * ((d + a) * (a + 2 * d) ^ 3 *
          (a ^ 2 + 2 * a * d + 2 * d ^ 2)) -
        16 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3 := by
      rw [hdiff]
      positivity
    nlinarith
  · rw [div_le_iff₀ (by positivity : 0 < 4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3)]
    have hdiff : (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3 -
        (d + a) * (a + 2 * d) ^ 3 * (a ^ 2 + 2 * a * d + 2 * d ^ 2) =
        d ^ 2 * (2 * a ^ 4 + 11 * a ^ 3 * d + 24 * a ^ 2 * d ^ 2 +
          25 * a * d ^ 3 + 11 * d ^ 4) := by ring
    have hnon : 0 ≤ (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3 -
        (d + a) * (a + 2 * d) ^ 3 * (a ^ 2 + 2 * a * d + 2 * d ^ 2) := by
      rw [hdiff]
      positivity
    nlinarith

/-- The §7 inverse-function scale bounds on the concrete `t ≍ F` window. -/
theorem dBreve_sec7_tWin_scale {P : Globals} {S : Scale P} {a t : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (ht : t ∈ sec7_tWin S) :
    (P.H * S.Δ ≤ sec7_cPh * (S.F * |dBreve' P.X a t|) ∧
      S.F * |dBreve' P.X a t| ≤ sec7_cPh * (P.H * S.Δ)) ∧
    (P.H * S.Δ ≤ sec7_cPh * (S.F ^ 2 * |dBreve'' P.X a t|) ∧
      S.F ^ 2 * |dBreve'' P.X a t| ≤ sec7_cPh * (P.H * S.Δ)) := by
  obtain ⟨hright, hd_lo, hd_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := t) hAD ha_lo ha_hi ht
  set d : ℝ := dBreve P.X a t with hd_def
  have hD : 0 < S.D := S.D_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hF : 0 < S.F := by unfold Scale.F; positivity
  have hDscale : P.H * S.Δ = S.D := rfl
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := by
    rw [hd_def]
    exact dBreve_pos
  have ht_bounds : S.F / sec7_cWin ≤ t ∧ t ≤ sec7_cWin * S.F := by
    simpa only [sec7_tWin, Set.mem_Icc] using ht
  set q : ℝ := t / S.F with hq_def
  set y : ℝ := d / S.D with hy_def
  set Y₁ : ℝ := S.F * |dBreve' P.X a t| with hY₁_def
  set R₁ : ℝ := Y₁ / S.D with hR₁_def
  set C₁ : ℝ :=
    (d + a) * (a + 2 * d) / (2 * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) with hC₁_def
  set Y₂ : ℝ := S.F ^ 2 * |dBreve'' P.X a t| with hY₂_def
  set R₂ : ℝ := Y₂ / S.D with hR₂_def
  set C₂ : ℝ :=
    3 * (d + a) * (a + 2 * d) ^ 3 * (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
      (4 * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ^ 3) with hC₂_def
  have hq_pos : 0 < q := by
    rw [hq_def]
    exact div_pos (lt_of_lt_of_le (div_pos hF sec7_cWin_pos) ht_bounds.1) hF
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hq_lo : (1 / 1000 : ℝ) ≤ q := by
    rw [hq_def]
    rw [le_div_iff₀ hF]
    calc (1 / 1000 : ℝ) * S.F
        = S.F / sec7_cWin := by norm_num [sec7_cWin]; ring
      _ ≤ t := ht_bounds.1
  have hq_hi : q ≤ (1000 : ℝ) := by
    rw [hq_def]
    rw [div_le_iff₀ hF]
    calc t
        ≤ sec7_cWin * S.F := ht_bounds.2
      _ = (1000 : ℝ) * S.F := by norm_num [sec7_cWin]
  have hy_lo : (1 / 16 : ℝ) ≤ y := by
    rw [hy_def]
    rw [le_div_iff₀ hD]
    calc (1 / 16 : ℝ) * S.D
        = S.D / 16 := by ring
      _ ≤ d := hd_lo
  have hy_hi : y ≤ (30 : ℝ) := by
    rw [hy_def, hd_def]
    rw [div_le_iff₀ hD]
    simpa using hd_hi
  have hy_nonneg : 0 ≤ y := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 16) hy_lo
  have hR₁_nonneg : 0 ≤ R₁ := by rw [hR₁_def, hY₁_def]; positivity
  have hR₂_nonneg : 0 ≤ R₂ := by rw [hR₂_def, hY₂_def]; positivity
  have hC₁_bounds : (1 / 3 : ℝ) ≤ C₁ ∧ C₁ ≤ (1 / 2 : ℝ) := by
    simpa [hC₁_def] using dBreve_deriv1_tnorm_factor_bounds ha0 hd0
  have hC₂_bounds : (4 / 9 : ℝ) ≤ C₂ ∧ C₂ ≤ (3 / 4 : ℝ) := by
    simpa [hC₂_def] using dBreve_deriv2_tnorm_factor_bounds ha0 hd0
  have hC₁_nonneg : 0 ≤ C₁ := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 3) hC₁_bounds.1
  have hC₂_nonneg : 0 ≤ C₂ := le_trans (by norm_num : (0 : ℝ) ≤ 4 / 9) hC₂_bounds.1
  have hnorm₁ : q * R₁ = C₁ * y := by
    have h := dBreve_deriv1_tnorm_identity (P := P) (S := S) (a := a) (d := d) ha0 hd0
    rw [hright] at h
    simpa [hq_def, hY₁_def, hR₁_def, hy_def, hC₁_def, hd_def] using h
  have hnorm₂ : q ^ 2 * R₂ = C₂ * y := by
    have h := dBreve_deriv2_tnorm_identity (P := P) (S := S) (a := a) (d := d) ha0 hd0
    rw [hright] at h
    simpa [hq_def, hY₂_def, hR₂_def, hy_def, hC₂_def, hd_def] using h
  have hR₁_lo : (1 / 48000 : ℝ) ≤ R₁ := by
    have hprod_lo : (1 / 48 : ℝ) ≤ q * R₁ := by
      rw [hnorm₁]
      calc (1 / 48 : ℝ)
          = (1 / 3 : ℝ) * (1 / 16 : ℝ) := by norm_num
        _ ≤ C₁ * y := mul_le_mul hC₁_bounds.1 hy_lo (by norm_num) hC₁_nonneg
    have hprod_hi : q * R₁ ≤ (1000 : ℝ) * R₁ :=
      mul_le_mul_of_nonneg_right hq_hi hR₁_nonneg
    nlinarith
  have hR₁_hi : R₁ ≤ (15000 : ℝ) := by
    have hprod_hi : q * R₁ ≤ (15 : ℝ) := by
      rw [hnorm₁]
      calc C₁ * y
          ≤ (1 / 2 : ℝ) * 30 := mul_le_mul hC₁_bounds.2 hy_hi hy_nonneg (by norm_num)
        _ = (15 : ℝ) := by norm_num
    have hprod_lo : (1 / 1000 : ℝ) * R₁ ≤ q * R₁ :=
      mul_le_mul_of_nonneg_right hq_lo hR₁_nonneg
    nlinarith
  have hq_sq_hi : q ^ 2 ≤ (1000000 : ℝ) := by
    have h := pow_le_pow_left₀ hq_nonneg hq_hi 2
    norm_num at h
    exact h
  have hq_sq_lo : (1 / 1000000 : ℝ) ≤ q ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 1000) hq_lo 2
    norm_num at h ⊢
    exact h
  have hR₂_lo : (1 / 36000000 : ℝ) ≤ R₂ := by
    have hprod_lo : (1 / 36 : ℝ) ≤ q ^ 2 * R₂ := by
      rw [hnorm₂]
      calc (1 / 36 : ℝ)
          = (4 / 9 : ℝ) * (1 / 16 : ℝ) := by norm_num
        _ ≤ C₂ * y := mul_le_mul hC₂_bounds.1 hy_lo (by norm_num) hC₂_nonneg
    have hprod_hi : q ^ 2 * R₂ ≤ (1000000 : ℝ) * R₂ :=
      mul_le_mul_of_nonneg_right hq_sq_hi hR₂_nonneg
    nlinarith
  have hR₂_hi : R₂ ≤ (22500000 : ℝ) := by
    have hprod_hi : q ^ 2 * R₂ ≤ (45 / 2 : ℝ) := by
      rw [hnorm₂]
      calc C₂ * y
          ≤ (3 / 4 : ℝ) * 30 := mul_le_mul hC₂_bounds.2 hy_hi hy_nonneg (by norm_num)
        _ = (45 / 2 : ℝ) := by norm_num
    have hprod_lo : (1 / 1000000 : ℝ) * R₂ ≤ q ^ 2 * R₂ :=
      mul_le_mul_of_nonneg_right hq_sq_lo hR₂_nonneg
    nlinarith
  have hY₁_lo : P.H * S.Δ ≤ sec7_cPh * Y₁ := by
    rw [hDscale]
    have hcPhR₁ : (1 : ℝ) ≤ sec7_cPh * R₁ := by
      nlinarith [hR₁_lo, show (48000 : ℝ) ≤ sec7_cPh by norm_num [sec7_cPh]]
    calc S.D
        = (1 : ℝ) * S.D := by ring
      _ ≤ (sec7_cPh * R₁) * S.D := mul_le_mul_of_nonneg_right hcPhR₁ hD.le
      _ = sec7_cPh * Y₁ := by
          rw [hR₁_def]
          field_simp [hD.ne']
  have hY₁_hi : Y₁ ≤ sec7_cPh * (P.H * S.Δ) := by
    rw [hDscale]
    calc Y₁
        = R₁ * S.D := by
          rw [hR₁_def]
          field_simp [hD.ne']
      _ ≤ (15000 : ℝ) * S.D := by gcongr
      _ ≤ sec7_cPh * S.D := by
          gcongr
          norm_num [sec7_cPh]
  have hY₂_lo : P.H * S.Δ ≤ sec7_cPh * Y₂ := by
    rw [hDscale]
    have hcPhR₂ : (1 : ℝ) ≤ sec7_cPh * R₂ := by
      nlinarith [hR₂_lo, show (36000000 : ℝ) ≤ sec7_cPh by norm_num [sec7_cPh]]
    calc S.D
        = (1 : ℝ) * S.D := by ring
      _ ≤ (sec7_cPh * R₂) * S.D := mul_le_mul_of_nonneg_right hcPhR₂ hD.le
      _ = sec7_cPh * Y₂ := by
          rw [hR₂_def]
          field_simp [hD.ne']
  have hY₂_hi : Y₂ ≤ sec7_cPh * (P.H * S.Δ) := by
    rw [hDscale]
    calc Y₂
        = R₂ * S.D := by
          rw [hR₂_def]
          field_simp [hD.ne']
      _ ≤ (22500000 : ℝ) * S.D := by gcongr
      _ ≤ sec7_cPh * S.D := by
          gcongr
          norm_num [sec7_cPh]
  simpa [hY₁_def, hY₂_def] using ⟨⟨hY₁_lo, hY₁_hi⟩, ⟨hY₂_lo, hY₂_hi⟩⟩

/-- First inverse-derivative scale on the wide image window:
`F·|d̆ₐ'(F_a(d))| ≍ HΔ`, with explicit constants. -/
theorem dBreve_deriv1_scale_wide_image {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (314 * 11 * 10 ^ 4) : ℝ) * (P.H * S.Δ) ≤
        S.F * |dBreve' P.X a (Ffun P.X a d)| ∧
      S.F * |dBreve' P.X a (Ffun P.X a d)| ≤
        (288 * 5 * 18 ^ 4 : ℝ) * (P.H * S.Δ) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  set A₁ := F₁ P.X a d with hA₁_def
  have hA₁_ne : A₁ ≠ 0 := by
    rw [hA₁_def]
    exact ne_of_lt (F₁_neg P.X_pos ha0 hd0)
  have hA₁_abs_pos : 0 < |A₁| := abs_pos.mpr hA₁_ne
  obtain ⟨hlo, hhi⟩ := Ffun_deriv1_scale_wide (P := P) (S := S) (a := a) (d := d)
    hAD ha_lo ha_hi hd_lo hd_hi
  have hAabs : |A₁| = |deriv (fun t => Ffun P.X a t) d| := by
    rw [hA₁_def, F₁_eq_deriv (X := P.X) (a := a) (d := d)
      (ne_of_gt hd0) (by positivity)]
  rw [← hAabs] at hlo hhi
  have hhiD : |A₁| * S.D ≤ (314 * 11 * 10 ^ 4 : ℝ) * S.F := by
    calc |A₁| * S.D
        ≤ ((314 * 11 * 10 ^ 4 : ℝ) * (S.F / S.D)) * S.D :=
            mul_le_mul_of_nonneg_right hhi hDpos.le
      _ = (314 * 11 * 10 ^ 4 : ℝ) * S.F := by field_simp [ne_of_gt hDpos]
  have hloD :
      (1 / (288 * 5 * 18 ^ 4) : ℝ) * S.F ≤ |A₁| * S.D := by
    calc (1 / (288 * 5 * 18 ^ 4) : ℝ) * S.F
        = ((1 / (288 * 5 * 18 ^ 4) : ℝ) * (S.F / S.D)) * S.D := by
            field_simp [ne_of_gt hDpos]
      _ ≤ |A₁| * S.D := mul_le_mul_of_nonneg_right hlo hDpos.le
  have hscale :
      S.F * |dBreve' P.X a (Ffun P.X a d)| = S.F / |A₁| := by
    rw [dBreve', dBreve_spec P.X_pos ha0 hd0, hA₁_def, abs_inv, div_eq_mul_inv]
  constructor
  · rw [hscale, show P.H * S.Δ = S.D by rfl]
    rw [le_div_iff₀ hA₁_abs_pos]
    nlinarith [hhiD]
  · rw [hscale, show P.H * S.Δ = S.D by rfl]
    rw [div_le_iff₀ hA₁_abs_pos]
    nlinarith [hloD]

/-- Second inverse-derivative scale on the wide image window:
`F²·|d̆ₐ''(F_a(d))| ≍ HΔ`.  The constant is deliberately generous; it is only a
phase-package comparability constant. -/
theorem dBreve_deriv2_scale_wide_image {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 40 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d)| ∧
      S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d)| ≤
        (10 ^ 40 : ℝ) * (P.H * S.Δ) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  set α : ℝ := 1 / (288 * 5 * 18 ^ 4) with hα_def
  set β : ℝ := 314 * 11 * 10 ^ 4 with hβ_def
  set γ : ℝ := 1 / (864 * 5 * 18 ^ 5) with hγ_def
  set δ : ℝ := 11310 * 11 * 10 ^ 5 with hδ_def
  have hαpos : 0 < α := by rw [hα_def]; norm_num
  have hβpos : 0 < β := by rw [hβ_def]; norm_num
  have hγpos : 0 < γ := by rw [hγ_def]; norm_num
  have hδpos : 0 < δ := by rw [hδ_def]; norm_num
  set A₁ := F₁ P.X a d with hA₁_def
  set B₂ := F₂ P.X a d with hB₂_def
  have hA₁_ne : A₁ ≠ 0 := by
    rw [hA₁_def]
    exact ne_of_lt (F₁_neg P.X_pos ha0 hd0)
  have hA₁_abs_pos : 0 < |A₁| := abs_pos.mpr hA₁_ne
  obtain ⟨hAlo, hAhi⟩ := Ffun_deriv1_scale_wide (P := P) (S := S) (a := a) (d := d)
    hAD ha_lo ha_hi hd_lo hd_hi
  obtain ⟨hBlo, hBhi⟩ := Ffun_deriv2_scale_wide (P := P) (S := S) (a := a) (d := d)
    hAD ha_lo ha_hi hd_lo hd_hi
  have hAabs : |A₁| = |deriv (fun t => Ffun P.X a t) d| := by
    rw [hA₁_def, F₁_eq_deriv (X := P.X) (a := a) (d := d)
      (ne_of_gt hd0) (by positivity)]
  have hBabs : |B₂| = |iteratedDeriv 2 (fun t => Ffun P.X a t) d| := by
    rw [hB₂_def, Ffun_iteratedDeriv2_d P.X a d (ne_of_gt hd0) (by positivity)]
    rfl
  rw [← hAabs] at hAlo hAhi
  rw [← hBabs] at hBlo hBhi
  have hAloD : α * S.F ≤ |A₁| * S.D := by
    calc α * S.F
        = (α * (S.F / S.D)) * S.D := by field_simp [ne_of_gt hDpos]
      _ ≤ |A₁| * S.D := by
        exact mul_le_mul_of_nonneg_right (by simpa [hα_def] using hAlo) hDpos.le
  have hAhiD : |A₁| * S.D ≤ β * S.F := by
    calc |A₁| * S.D
        ≤ (β * (S.F / S.D)) * S.D := by
            exact mul_le_mul_of_nonneg_right (by simpa [hβ_def] using hAhi) hDpos.le
      _ = β * S.F := by field_simp [ne_of_gt hDpos]
  have hBloD : γ * S.F ≤ |B₂| * S.D ^ 2 := by
    calc γ * S.F
        = (γ * (S.F / S.D ^ 2)) * S.D ^ 2 := by field_simp [ne_of_gt hDpos]
      _ ≤ |B₂| * S.D ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by simpa [hγ_def] using hBlo) (by positivity)
  have hBhiD : |B₂| * S.D ^ 2 ≤ δ * S.F := by
    calc |B₂| * S.D ^ 2
        ≤ (δ * (S.F / S.D ^ 2)) * S.D ^ 2 := by
            exact mul_le_mul_of_nonneg_right (by simpa [hδ_def] using hBhi) (by positivity)
      _ = δ * S.F := by field_simp [ne_of_gt hDpos]
  have hAhi_cube : |A₁| ^ 3 * S.D ^ 3 ≤ β ^ 3 * S.F ^ 3 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ |A₁| * S.D) hAhiD 3
    nlinarith [hp]
  have hAlo_cube : α ^ 3 * S.F ^ 3 ≤ |A₁| ^ 3 * S.D ^ 3 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ α * S.F) hAloD 3
    nlinarith [hp]
  have hBlo_div : γ * S.F ^ 3 / S.D ^ 2 ≤ S.F ^ 2 * |B₂| := by
    rw [div_le_iff₀ (by positivity : 0 < S.D ^ 2)]
    nlinarith [hBloD, hFpos]
  have hBhi_div : S.F ^ 2 * |B₂| ≤ δ * S.F ^ 3 / S.D ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < S.D ^ 2)]
    nlinarith [hBhiD, hFpos]
  have hAhi_div : S.D * |A₁| ^ 3 ≤ β ^ 3 * S.F ^ 3 / S.D ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < S.D ^ 2)]
    nlinarith [hAhi_cube]
  have hAlo_div : α ^ 3 * S.F ^ 3 / S.D ^ 2 ≤ S.D * |A₁| ^ 3 := by
    rw [div_le_iff₀ (by positivity : 0 < S.D ^ 2)]
    nlinarith [hAlo_cube]
  have hscale :
      S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d)| =
        S.F ^ 2 * |B₂| / |A₁| ^ 3 := by
    rw [dBreve'', dBreve_spec P.X_pos ha0 hd0, hA₁_def, hB₂_def]
    rw [abs_div, abs_neg, abs_pow, div_eq_mul_inv]
    ring
  constructor
  · rw [hscale, show P.H * S.Δ = S.D by rfl]
    rw [le_div_iff₀ (by positivity : 0 < |A₁| ^ 3)]
    have hnum : (1 / 10 ^ 40 : ℝ) * S.D * |A₁| ^ 3 ≤
        γ * S.F ^ 3 / S.D ^ 2 := by
      calc (1 / 10 ^ 40 : ℝ) * S.D * |A₁| ^ 3
          = (1 / 10 ^ 40 : ℝ) * (S.D * |A₁| ^ 3) := by ring
        _ ≤ (1 / 10 ^ 40 : ℝ) * (β ^ 3 * S.F ^ 3 / S.D ^ 2) := by
              exact mul_le_mul_of_nonneg_left hAhi_div (by positivity)
        _ = ((1 / 10 ^ 40 : ℝ) * β ^ 3) * (S.F ^ 3 / S.D ^ 2) := by ring
        _ ≤ γ * (S.F ^ 3 / S.D ^ 2) := by
              have hconst : (1 / 10 ^ 40 : ℝ) * β ^ 3 ≤ γ := by
                rw [hβ_def, hγ_def]
                norm_num
              exact mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = γ * S.F ^ 3 / S.D ^ 2 := by ring
    exact le_trans hnum hBlo_div
  · rw [hscale, show P.H * S.Δ = S.D by rfl]
    rw [div_le_iff₀ (by positivity : 0 < |A₁| ^ 3)]
    calc S.F ^ 2 * |B₂|
        ≤ δ * S.F ^ 3 / S.D ^ 2 := hBhi_div
      _ ≤ (10 ^ 40 : ℝ) * S.D * |A₁| ^ 3 := by
        have hconst : δ ≤ (10 ^ 40 : ℝ) * α ^ 3 := by
          rw [hδ_def, hα_def]
          norm_num
        calc δ * S.F ^ 3 / S.D ^ 2
            = δ * (S.F ^ 3 / S.D ^ 2) := by ring
          _ ≤ ((10 ^ 40 : ℝ) * α ^ 3) * (S.F ^ 3 / S.D ^ 2) := by
              exact mul_le_mul_of_nonneg_right hconst (by positivity)
          _ = (10 ^ 40 : ℝ) * (α ^ 3 * S.F ^ 3 / S.D ^ 2) := by ring
          _ ≤ (10 ^ 40 : ℝ) * (S.D * |A₁| ^ 3) := by
              exact mul_le_mul_of_nonneg_left hAlo_div (by positivity)
          _ = (10 ^ 40 : ℝ) * S.D * |A₁| ^ 3 := by ring

/-- Fifth inverse-derivative scale on the wide image window:
`F⁵·|d̆ₐ⁽⁵⁾(F_a(d))| ≍ HΔ`.  The constants are deliberately generous; this is an
additive grade-5 comparability lemma for the residual layer. -/
theorem dBreve_deriv5_scale_wide_image {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d) (hd_hi : d ≤ 30 * S.D) :
    (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 5 * |dBreve''''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 5 * |dBreve''''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hd_lo
  have ha_le_19d : a ≤ 19 * d := by nlinarith [ha_hi, hAD, hd_lo]
  set Q : ℝ :=
    21 * a ^ 12 + 336 * a ^ 11 * d + 2520 * a ^ 10 * d ^ 2
      + 11852 * a ^ 9 * d ^ 3 + 39104 * a ^ 8 * d ^ 4
      + 95348 * a ^ 7 * d ^ 5 + 175964 * a ^ 6 * d ^ 6
      + 247424 * a ^ 5 * d ^ 7 + 262988 * a ^ 4 * d ^ 8
      + 206160 * a ^ 3 * d ^ 9 + 113304 * a ^ 2 * d ^ 10
      + 39312 * a * d ^ 11 + 6552 * d ^ 12 with hQ_def
  set R : ℝ := a ^ 2 + 3 * a * d + 3 * d ^ 2 with hR_def
  have hQpos : 0 < Q := by
    rw [hQ_def]
    positivity
  have hRpos : 0 < R := by
    rw [hR_def]
    positivity
  have hnorm :
      (S.F ^ 5 * |dBreve''''' P.X a (Ffun P.X a d)|) / S.D =
        (45 / 32 : ℝ) * (S.A / a) ^ 5 * (d / S.D) ^ 16 *
          ((d + a) / d) ^ 11 * ((Q / d ^ 12) / ((R / d ^ 2) ^ 9)) := by
    rw [dBreve_deriv5_abs_factor_image P.X_pos ha0 hd0, ← XA_div_D3_eq_F S]
    rw [hQ_def, hR_def]
    field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd0.ne', hDpos.ne']
  have hSA_lo : (1 / 11 : ℝ) ≤ S.A / a := by
    rw [le_div_iff₀ ha0]
    nlinarith [ha_hi]
  have hSA_hi : S.A / a ≤ (5 : ℝ) := by
    rw [div_le_iff₀ ha0]
    nlinarith [ha_lo]
  have hSA_nonneg : 0 ≤ S.A / a := (div_pos hApos ha0).le
  have hSA5_lo : (1 / 11 : ℝ) ^ 5 ≤ (S.A / a) ^ 5 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 11) hSA_lo 5
  have hSA5_hi : (S.A / a) ^ 5 ≤ (5 : ℝ) ^ 5 :=
    pow_le_pow_left₀ hSA_nonneg hSA_hi 5
  have hy_lo : (1 / 16 : ℝ) ≤ d / S.D := by
    rw [le_div_iff₀ hDpos]
    calc (1 / 16 : ℝ) * S.D = S.D / 16 := by ring
      _ ≤ d := hd_lo
  have hy_hi : d / S.D ≤ (30 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    exact hd_hi
  have hy_nonneg : 0 ≤ d / S.D := (div_pos hd0 hDpos).le
  have hy16_lo : (1 / 16 : ℝ) ^ 16 ≤ (d / S.D) ^ 16 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 16) hy_lo 16
  have hy16_hi : (d / S.D) ^ 16 ≤ (30 : ℝ) ^ 16 :=
    pow_le_pow_left₀ hy_nonneg hy_hi 16
  have hda_lo : (1 : ℝ) ≤ (d + a) / d := by
    rw [le_div_iff₀ hd0]
    nlinarith [ha0]
  have hda_hi : (d + a) / d ≤ (20 : ℝ) := by
    rw [div_le_iff₀ hd0]
    nlinarith [ha_le_19d]
  have hda_nonneg : 0 ≤ (d + a) / d := by positivity
  have hda11_lo : (1 : ℝ) ^ 11 ≤ ((d + a) / d) ^ 11 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hda_lo 11
  have hda11_hi : ((d + a) / d) ^ 11 ≤ (20 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hda_nonneg hda_hi 11
  have hRlo_base : 3 * d ^ 2 ≤ R := by
    rw [hR_def]
    nlinarith [sq_nonneg a, mul_pos ha0 hd0]
  have hRhi_base : R ≤ 421 * d ^ 2 := by
    have ha2 : a ^ 2 ≤ (19 * d) ^ 2 := pow_le_pow_left₀ ha0.le ha_le_19d 2
    have had : a * d ≤ (19 * d) * d := mul_le_mul_of_nonneg_right ha_le_19d hd0.le
    rw [hR_def]
    nlinarith [ha2, had]
  have hRnorm_lo : (3 : ℝ) ≤ R / d ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < d ^ 2)]
    simpa using hRlo_base
  have hRnorm_hi : R / d ^ 2 ≤ (421 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < d ^ 2)]
    simpa using hRhi_base
  have hRnorm_pos : 0 < R / d ^ 2 := div_pos hRpos (pow_pos hd0 2)
  have hRpow_lo : (3 : ℝ) ^ 9 ≤ (R / d ^ 2) ^ 9 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hRnorm_lo 9
  have hRpow_hi : (R / d ^ 2) ^ 9 ≤ (421 : ℝ) ^ 9 :=
    pow_le_pow_left₀ hRnorm_pos.le hRnorm_hi 9
  have hQlo_base : 6552 * d ^ 12 ≤ Q := by
    rw [hQ_def]
    have h1 : 0 ≤ 21 * a ^ 12 := by positivity
    have h2 : 0 ≤ 336 * a ^ 11 * d := by positivity
    have h3 : 0 ≤ 2520 * a ^ 10 * d ^ 2 := by positivity
    have h4 : 0 ≤ 11852 * a ^ 9 * d ^ 3 := by positivity
    have h5 : 0 ≤ 39104 * a ^ 8 * d ^ 4 := by positivity
    have h6 : 0 ≤ 95348 * a ^ 7 * d ^ 5 := by positivity
    have h7 : 0 ≤ 175964 * a ^ 6 * d ^ 6 := by positivity
    have h8 : 0 ≤ 247424 * a ^ 5 * d ^ 7 := by positivity
    have h9 : 0 ≤ 262988 * a ^ 4 * d ^ 8 := by positivity
    have h10 : 0 ≤ 206160 * a ^ 3 * d ^ 9 := by positivity
    have h11 : 0 ≤ 113304 * a ^ 2 * d ^ 10 := by positivity
    have h12 : 0 ≤ 39312 * a * d ^ 11 := by positivity
    nlinarith
  have hQhi_base : Q ≤ (10 ^ 18 : ℝ) * d ^ 12 := by
    have hQmono : Q ≤
        21 * (19 * d) ^ 12 + 336 * (19 * d) ^ 11 * d
          + 2520 * (19 * d) ^ 10 * d ^ 2
          + 11852 * (19 * d) ^ 9 * d ^ 3
          + 39104 * (19 * d) ^ 8 * d ^ 4
          + 95348 * (19 * d) ^ 7 * d ^ 5
          + 175964 * (19 * d) ^ 6 * d ^ 6
          + 247424 * (19 * d) ^ 5 * d ^ 7
          + 262988 * (19 * d) ^ 4 * d ^ 8
          + 206160 * (19 * d) ^ 3 * d ^ 9
          + 113304 * (19 * d) ^ 2 * d ^ 10
          + 39312 * (19 * d) * d ^ 11 + 6552 * d ^ 12 := by
      rw [hQ_def]
      gcongr
    have hd12_nonneg : 0 ≤ d ^ 12 := by positivity
    nlinarith [hQmono, hd12_nonneg]
  have hQnorm_lo : (6552 : ℝ) ≤ Q / d ^ 12 := by
    rw [le_div_iff₀ (pow_pos hd0 12)]
    simpa using hQlo_base
  have hQnorm_hi : Q / d ^ 12 ≤ (10 ^ 18 : ℝ) := by
    rw [div_le_iff₀ (pow_pos hd0 12)]
    simpa using hQhi_base
  have hQnorm_nonneg : 0 ≤ Q / d ^ 12 := (div_pos hQpos (pow_pos hd0 12)).le
  have hquot_lo :
      (6552 : ℝ) / (421 : ℝ) ^ 9 ≤ (Q / d ^ 12) / ((R / d ^ 2) ^ 9) := by
    calc (6552 : ℝ) / (421 : ℝ) ^ 9
        ≤ (Q / d ^ 12) / (421 : ℝ) ^ 9 := by
            gcongr
      _ ≤ (Q / d ^ 12) / ((R / d ^ 2) ^ 9) := by
            exact div_le_div_of_nonneg_left hQnorm_nonneg (pow_pos hRnorm_pos 9) hRpow_hi
  have hquot_hi :
      (Q / d ^ 12) / ((R / d ^ 2) ^ 9) ≤ (10 ^ 18 : ℝ) / (3 : ℝ) ^ 9 := by
    calc (Q / d ^ 12) / ((R / d ^ 2) ^ 9)
        ≤ (10 ^ 18 : ℝ) / ((R / d ^ 2) ^ 9) := by
            gcongr
      _ ≤ (10 ^ 18 : ℝ) / (3 : ℝ) ^ 9 := by
            exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 10 ^ 18)
              (by norm_num : (0 : ℝ) < (3 : ℝ) ^ 9) hRpow_lo
  have hmain_lo :
      (1 / 10 ^ 100 : ℝ) ≤
        (45 / 32 : ℝ) * (S.A / a) ^ 5 * (d / S.D) ^ 16 *
          ((d + a) / d) ^ 11 * ((Q / d ^ 12) / ((R / d ^ 2) ^ 9)) := by
    have hconst : (1 / 10 ^ 100 : ℝ) ≤
        (45 / 32 : ℝ) * (1 / 11 : ℝ) ^ 5 * (1 / 16 : ℝ) ^ 16 *
          (1 : ℝ) ^ 11 * ((6552 : ℝ) / (421 : ℝ) ^ 9) := by
      norm_num
    calc (1 / 10 ^ 100 : ℝ)
        ≤ (45 / 32 : ℝ) * (1 / 11 : ℝ) ^ 5 * (1 / 16 : ℝ) ^ 16 *
          (1 : ℝ) ^ 11 * ((6552 : ℝ) / (421 : ℝ) ^ 9) := hconst
      _ ≤ (45 / 32 : ℝ) * (S.A / a) ^ 5 * (d / S.D) ^ 16 *
          ((d + a) / d) ^ 11 * ((Q / d ^ 12) / ((R / d ^ 2) ^ 9)) := by
            gcongr
  have hmain_hi :
      (45 / 32 : ℝ) * (S.A / a) ^ 5 * (d / S.D) ^ 16 *
          ((d + a) / d) ^ 11 * ((Q / d ^ 12) / ((R / d ^ 2) ^ 9)) ≤
        (10 ^ 100 : ℝ) := by
    have hconst :
        (45 / 32 : ℝ) * (5 : ℝ) ^ 5 * (30 : ℝ) ^ 16 *
            (20 : ℝ) ^ 11 * ((10 ^ 18 : ℝ) / (3 : ℝ) ^ 9) ≤
          (10 ^ 100 : ℝ) := by
      norm_num
    calc (45 / 32 : ℝ) * (S.A / a) ^ 5 * (d / S.D) ^ 16 *
          ((d + a) / d) ^ 11 * ((Q / d ^ 12) / ((R / d ^ 2) ^ 9))
        ≤ (45 / 32 : ℝ) * (5 : ℝ) ^ 5 * (30 : ℝ) ^ 16 *
            (20 : ℝ) ^ 11 * ((10 ^ 18 : ℝ) / (3 : ℝ) ^ 9) := by
            gcongr
      _ ≤ (10 ^ 100 : ℝ) := hconst
  constructor
  · rw [show P.H * S.Δ = S.D by rfl]
    rw [← le_div_iff₀ hDpos]
    rw [hnorm]
    exact hmain_lo
  · rw [show P.H * S.Δ = S.D by rfl]
    rw [← div_le_iff₀ hDpos]
    rw [hnorm]
    exact hmain_hi

end Squarefree
