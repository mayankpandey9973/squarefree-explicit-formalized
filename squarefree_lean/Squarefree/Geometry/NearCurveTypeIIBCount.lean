import Squarefree.Geometry.NearCurveTypeIISlope
import Squarefree.Geometry.NearCurveConvexArc
import Mathlib

/-!
# §4.3 Type II — convexity b-count (writeup 626–650, analytic crux)

The second-derivative / residual derivative helpers, the constant-sign convexity
lemma `deriv2_const_sign`, `signedRes_deriv2_eq_abs`, and the per-slope `b`-count
`typeII_b_count_per_slope`.  Split out of `NearCurveTypeII`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## §4.3 convex-arc application support (for `typeII_shift_loc`) -/

/-- `lineRes f D₀` has derivative `f'(x) − p/q` everywhere. -/
private theorem hasDerivAt_lineRes_pub {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (lineRes f D₀) (deriv f x - (D₀.slope.num : ℝ) / (D₀.denom : ℝ)) x :=
  hasDerivAt_lineRes (hasDerivAt_self_of_contDiff hf x)

/-- `deriv (lineRes f D₀) = fun x => f'(x) − p/q`. -/
private theorem deriv_lineRes_pub {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    deriv (lineRes f D₀) = fun x => deriv f x - (D₀.slope.num : ℝ) / (D₀.denom : ℝ) :=
  funext fun x => (hasDerivAt_lineRes_pub hf x).deriv

/-- `deriv (deriv (lineRes f D₀)) x = f''(x)` everywhere. -/
private theorem deriv_deriv_lineRes_pub {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (lineRes f D₀)) x = iteratedDeriv 2 f x := by
  rw [deriv_lineRes_pub hf]
  exact ((hasDerivAt_deriv_of_contDiff hf x).sub_const _).deriv

/-- `lineRes f D₀` is differentiable everywhere. -/
private theorem differentiable_lineRes_pub {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (lineRes f D₀) :=
  fun x => (hasDerivAt_lineRes_pub hf x).differentiableAt

/-- `deriv (lineRes f D₀)` is differentiable everywhere (`= f' − const`, `f ∈ C²`). -/
private theorem differentiable_deriv_lineRes_pub {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv (lineRes f D₀)) := by
  rw [deriv_lineRes_pub hf]
  have hf' : Differentiable ℝ (deriv f) :=
    fun x => (hasDerivAt_deriv_of_contDiff hf x).differentiableAt
  exact fun x => (hf' x).sub_const _

/-- `deriv (lineRes f D₀)` is continuous everywhere. -/
private theorem continuous_deriv_lineRes_pub {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (lineRes f D₀)) :=
  (differentiable_deriv_lineRes_pub hf).continuous

/-- The **signed residual** `H = sign·g` of the reference line `D₀`, the function fed to the
generic convex-arc lemma. -/
private noncomputable def signedRes (f : ℝ → ℝ) (N : ℝ) (D₀ : MajorLine) : ℝ → ℝ :=
  fun x => lineSign' f N D₀ * lineRes f D₀ x

/-- `H` has derivative `sign·(f'(x) − p/q)` everywhere. -/
private theorem hasDerivAt_signedRes {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (signedRes f N D₀)
      (lineSign' f N D₀ * (deriv f x - (D₀.slope.num : ℝ) / (D₀.denom : ℝ))) x := by
  have h := (hasDerivAt_lineRes (D := D₀) (hasDerivAt_self_of_contDiff hf x)).const_mul
    (lineSign' f N D₀)
  exact h

/-- `deriv H = fun x => sign·(f'(x) − p/q)`. -/
private theorem deriv_signedRes {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    deriv (signedRes f N D₀)
      = fun x => lineSign' f N D₀ * (deriv f x - (D₀.slope.num : ℝ) / (D₀.denom : ℝ)) :=
  funext fun x => (hasDerivAt_signedRes hf x).deriv

/-- `deriv (deriv H) x = sign·f''(x)` everywhere. -/
private theorem deriv_deriv_signedRes {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (signedRes f N D₀)) x = lineSign' f N D₀ * iteratedDeriv 2 f x := by
  rw [deriv_signedRes hf]
  have h : HasDerivAt (fun x => lineSign' f N D₀ * (deriv f x - (D₀.slope.num : ℝ)
      / (D₀.denom : ℝ))) (lineSign' f N D₀ * iteratedDeriv 2 f x) x := by
    have := ((hasDerivAt_deriv_of_contDiff hf x).sub_const
      ((D₀.slope.num : ℝ) / (D₀.denom : ℝ))).const_mul (lineSign' f N D₀)
    exact this
  exact h.deriv

/-- `H` is differentiable everywhere. -/
private theorem differentiable_signedRes {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (signedRes f N D₀) :=
  fun x => (hasDerivAt_signedRes hf x).differentiableAt

/-- `deriv H` is continuous everywhere (`f ∈ C²`). -/
private theorem continuous_deriv_signedRes {D₀ : MajorLine} (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (signedRes f N D₀)) := by
  rw [deriv_signedRes hf]
  have hf' : Continuous (deriv f) := by
    have h1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
    exact h1.continuous
  fun_prop

/-- **`f''` has constant sign on the curvature window** (the IVT dichotomy used in
`lineRes_convex_or_concave`): either `f'' > 0` throughout `I` or `f'' < 0` throughout. -/
private theorem deriv2_const_sign {hf : ContDiff ℝ 2 f}
    (hlam : 0 < lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) :
    (∀ x ∈ Set.Icc (N / 2) (5 * N / 2), 0 < iteratedDeriv 2 f x) ∨
      (∀ x ∈ Set.Icc (N / 2) (5 * N / 2), iteratedDeriv 2 f x < 0) := by
  classical
  set I := Set.Icc (N / 2) (5 * N / 2) with hI
  have hcont2 : Continuous (iteratedDeriv 2 f) := by
    have h0 : Continuous (deriv (deriv f)) := by
      simpa using (hf.iterate_deriv' 0 2).continuous
    have heq : iteratedDeriv 2 f = deriv (deriv f) := funext fun x => iteratedDeriv_two_eq
    rw [heq]; exact h0
  have hne : ∀ x ∈ I, iteratedDeriv 2 f x ≠ 0 := by
    intro x hx hzero
    have := hlower x hx; rw [hzero, abs_zero] at this; linarith
  by_cases hpos : ∃ x ∈ I, 0 < iteratedDeriv 2 f x
  · left
    obtain ⟨x₀, hx₀I, hx₀pos⟩ := hpos
    intro x hxI
    rcases lt_trichotomy (iteratedDeriv 2 f x) 0 with hneg | hzero | hpos'
    · exfalso
      have hsub : Set.uIcc x x₀ ⊆ I := Set.uIcc_subset_Icc hxI hx₀I
      have hcontOn : ContinuousOn (iteratedDeriv 2 f) (Set.uIcc x x₀) := hcont2.continuousOn
      have h0mem : (0 : ℝ) ∈ Set.uIcc (iteratedDeriv 2 f x) (iteratedDeriv 2 f x₀) := by
        rw [Set.mem_uIcc]; left; exact ⟨hneg.le, hx₀pos.le⟩
      obtain ⟨c, hcmem, hc0⟩ := intermediate_value_uIcc hcontOn h0mem
      exact hne c (hsub hcmem) hc0
    · exact absurd hzero (hne x hxI)
    · exact hpos'
  · right
    push Not at hpos
    intro x hxI
    exact lt_of_le_of_ne (hpos x hxI) (hne x hxI)

/-- **`H'' = |f''|` on the curvature window.**  The curvature sign `lineSign'` is `+1` exactly
when the residual is convex (i.e. `f'' > 0` on the window) and `−1` when concave (`f'' < 0`),
so the signed second derivative equals `|f''|`. -/
private theorem signedRes_deriv2_eq_abs {D₀ : MajorLine} (hf : ContDiff ℝ 2 f)
    (hlam : 0 < lam) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    {x : ℝ} (hx : x ∈ Set.Icc (N / 2) (5 * N / 2)) :
    deriv (deriv (signedRes f N D₀)) x = |iteratedDeriv 2 f x| := by
  classical
  rw [deriv_deriv_signedRes hf]
  set I := Set.Icc (N / 2) (5 * N / 2) with hI
  have hIab : (N / 2 : ℝ) < 5 * N / 2 := by linarith
  rcases deriv2_const_sign (f := f) (N := N) (lam := lam) (hf := hf) hlam hlower with
    hallpos | hallneg
  · -- `f'' > 0` everywhere ⟹ `lineRes` is `ConvexOn` ⟹ `lineSign' = 1`.
    have hcvx : ConvexOn ℝ I (lineRes f D₀) := by
      apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
        (differentiable_lineRes_pub hf).continuous.continuousOn
        (differentiable_lineRes_pub hf).differentiableOn
        ((differentiable_deriv_lineRes_pub hf).differentiableOn)
      intro y hy
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply,
        deriv_deriv_lineRes_pub hf]
      exact (hallpos y (interior_subset hy)).le
    have hsign : lineSign' f N D₀ = 1 := by rw [lineSign', ← hI, if_pos hcvx]
    rw [hsign, one_mul, abs_of_pos (hallpos x hx)]
  · -- `f'' < 0` everywhere ⟹ `lineRes` NOT `ConvexOn` ⟹ `lineSign' = -1`.
    have hncvx : ¬ ConvexOn ℝ I (lineRes f D₀) := by
      intro hcvx
      -- `ConvexOn` ⟹ `deriv (lineRes)` MonotoneOn `I`.
      have hmono : MonotoneOn (deriv (lineRes f D₀)) I :=
        hcvx.monotoneOn_deriv (fun y _ => (differentiable_lineRes_pub hf) y)
      -- `f'' < 0` ⟹ `deriv (lineRes)` StrictAntiOn `I`.
      have hanti : StrictAntiOn (deriv (lineRes f D₀)) I := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
          (continuous_deriv_lineRes_pub hf).continuousOn
        intro y hy
        rw [deriv_deriv_lineRes_pub hf]
        exact hallneg y (interior_subset hy)
      have hmemlo : (N / 2 : ℝ) ∈ I := ⟨le_rfl, hIab.le⟩
      have hmemhi : (5 * N / 2 : ℝ) ∈ I := ⟨hIab.le, le_rfl⟩
      have h1 := hmono hmemlo hmemhi hIab.le
      have h2 := hanti hmemlo hmemhi hIab
      linarith
    have hsign : lineSign' f N D₀ = -1 := by rw [lineSign', ← hI, if_neg hncvx]
    rw [hsign, abs_of_neg (hallneg x hx)]; ring

/-! ## STUB 6 — the b-count per slope (the convexity argmin) -/

/-- **Same-slope residual difference.**  If `D.slope = D₀.slope` (so equal `num` and `denom`),
the residuals of `D` and `D₀` differ by the constant `(D.shift − D₀.shift)/q`:
`lineRes f D x = lineRes f D₀ x − (D.shift − D₀.shift)/q`. -/
private theorem lineRes_same_slope {D D₀ : MajorLine} (hslope : D.slope = D₀.slope) (x : ℝ) :
    lineRes f D x
      = lineRes f D₀ x - ((D.shift : ℝ) - (D₀.shift : ℝ)) / (D.denom : ℝ) := by
  have hnum : D.slope.num = D₀.slope.num := by rw [hslope]
  have hden : D.denom = D₀.denom := by simp only [MajorLine.denom, hslope]
  have hqne : (D.denom : ℝ) ≠ 0 := by have := D.denom_pos; positivity
  rw [lineRes, lineRes, lineVal, lineVal, hnum, hden]
  field_simp
  ring

/-- **Shift-localization (the convexity argmin), writeup 624–642.**  For a fixed
denominator `q` and fixed slope `r/q = D₀.slope`, write `h(x) = f(x) − (r/q)x`; then
`h'' = f''`, so `λ ≤ |h''| ≤ 2λ` on `[N/2, 5N/2]`, hence (by IVT on the continuous
`h''`) `h` is convex *or* concave on the curvature window.  Let `x₀` be the argmin of
the convexified residual and `m := h(x₀)`.  Every Type II line `D` of slope `r/q` has a
long proper arc on which `|h − D.shift/q| ≤ δ`; the lower endpoint gives
`D.shift/q ≥ m − δ`, and the MVT + convex Taylor bound on the arc nearest `x₀` gives
`D.shift/q ≤ m + δ + 4/q`.  Thus all admissible `D.shift/q` lie in an interval of
half-width `δ + 2/q` about the center `c := m + 2/q`; equivalently, there is a real
`c` with `|D.shift − q·c| ≤ q·δ + 2` for all such `D`.

This packages the entire convex-argmin analysis as a single existential center, from
which the `≤ 6` count is pure integer-interval arithmetic. -/
private theorem typeII_shift_loc (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hδ : 0 < δ) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (q : ℤ) (D₀ : MajorLine) :
    ∃ c : ℝ, ∀ D ∈ (typeIILines f N lam δ).filter
        (fun D => D.denom = q ∧ D.slope = D₀.slope),
      |((D.shift : ℝ)) - (q : ℝ) * c| ≤ (q : ℝ) * δ + 512 := by
  classical
  set A : ℝ := N / 2 with hAdef
  set B : ℝ := 5 * N / 2 with hBdef
  set sgn : ℝ := lineSign' f N D₀ with hsgndef
  set H : ℝ → ℝ := signedRes f N D₀ with hHdef
  set x₀ : ℝ := lineSplit' f N δ D₀ with hx₀def
  set M : ℝ := H x₀ with hMdef
  -- `sgn = ±1`, in particular `sgn² = 1`.
  have hsgnsq : sgn * sgn = 1 := by
    rw [hsgndef, lineSign']; split_ifs <;> ring
  -- The common analytic hypotheses for the generic convex-arc lemma.
  have hAB : A ≤ B := by rw [hAdef, hBdef]; linarith
  have hHc : ContinuousOn H (Set.Icc A B) := by
    simp only [hHdef]
    exact (continuousOn_const.mul (differentiable_lineRes_pub hf).continuous.continuousOn)
  have hHd : ∀ x ∈ Set.Icc A B, DifferentiableAt ℝ H x := by
    intro x _; rw [hHdef]; exact differentiable_signedRes hf x
  have hHc' : ContinuousOn (deriv H) (Set.Icc A B) := by
    rw [hHdef]; exact (continuous_deriv_signedRes hf).continuousOn
  have hHd' : DifferentiableOn ℝ (deriv H) (Set.Ioo A B) := by
    rw [hHdef, deriv_signedRes hf]
    have hf' : Differentiable ℝ (deriv f) :=
      fun y => (hasDerivAt_deriv_of_contDiff hf y).differentiableAt
    exact (fun y _ => ((hf' y).sub_const _).const_mul sgn |>.differentiableWithinAt)
  have hconv : ConvexOn ℝ (Set.Icc A B) H := by
    simp only [hHdef, hAdef, hBdef]
    exact convexOn_signed_lineRes hf hlam hlower
  have hH'' : ∀ x ∈ Set.Ioo A B, lam ≤ deriv (deriv H) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (N / 2) (5 * N / 2) :=
      ⟨le_of_lt (by rw [← hAdef]; exact hx.1), le_of_lt (by rw [← hBdef]; exact hx.2)⟩
    rw [hHdef, signedRes_deriv2_eq_abs hf hlam hN2 hlower hxIcc]
    exact hlower x hxIcc
  obtain ⟨hx₀mem0, hx₀min0⟩ := lineSplit'_isMinOn (D := D₀) (δ := δ) hf hlam hN2 hlower
  have hx₀mem : x₀ ∈ Set.Icc A B := by rw [hx₀def, hAdef, hBdef]; exact hx₀mem0
  have hx₀min : IsMinOn H (Set.Icc A B) x₀ := by
    simp only [hHdef, hx₀def, hAdef, hBdef]; exact hx₀min0
  -- The localization center (depends only on `D₀`, `q`).
  refine ⟨(D₀.shift : ℝ) / (q : ℝ) + sgn * (M + 512 / (q : ℝ)), ?_⟩
  intro D hD
  rw [Finset.mem_filter] at hD
  obtain ⟨hDmem, hDq, hDslope⟩ := hD
  have hqpos : 0 < q := by rw [← hDq]; exact D.denom_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hqDR : ((D.denom : ℝ)) = (q : ℝ) := by rw [hDq]
  -- The proper arc of `D` is nonempty (≥2 points) and long.
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'II hDmem
  have hne : (properArc' f N δ D).Nonempty := Finset.card_pos.mp (by omega)
  set lo : ℤ := properLo' f N δ D with hlodef
  set hi : ℤ := properHi' f N δ D with hhidef
  have hlomem := properLo'_mem (D := D) hne
  have hhimem := properHi'_mem (D := D) hne
  rw [← hlodef] at hlomem; rw [← hhidef] at hhimem
  have hlohiZ : lo ≤ hi := by
    rw [hlodef, hhidef]
    exact_mod_cast properLo'_le_properHi' (f := f) (N := N) (δ := δ) (D := D)
  -- arc endpoints in `[A, B]` (near-set coords).
  obtain ⟨hloNear, _, _, _⟩ := mem_properArc'_facts hlomem
  obtain ⟨hhiNear, _, _, _⟩ := mem_properArc'_facts hhimem
  have hloIcc : (lo : ℝ) ∈ Set.Icc A B := by
    rw [hAdef, hBdef]; exact nearCoord_mem_Icc hN2 hloNear
  have hhiIcc : (hi : ℝ) ∈ Set.Icc A B := by
    rw [hAdef, hBdef]; exact nearCoord_mem_Icc hN2 hhiNear
  -- long-arc and `lo < hi` (tightened split `δ√(q/(256λ))`).
  have hlong0 : δ * Real.sqrt ((D.denom : ℝ) / (256 * lam)) < (hi : ℝ) - (lo : ℝ) :=
    typeII_longArc hDmem
  have hlong : δ * Real.sqrt ((q : ℝ) / (256 * lam)) < (hi : ℝ) - (lo : ℝ) := by
    rwa [hqDR] at hlong0
  have hWnn : (0 : ℝ) ≤ δ * Real.sqrt ((q : ℝ) / (256 * lam)) := by positivity
  have hlohiR : (lo : ℝ) < (hi : ℝ) := by linarith [hWnn, hlong]
  -- the strip condition for `D` transferred to `H`: `|H x − w| ≤ δ` on `[lo, hi]`.
  set w : ℝ := sgn * ((D.shift : ℝ) - (D₀.shift : ℝ)) / (q : ℝ) with hwdef
  have hstrip : ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), |H x - w| ≤ δ := by
    intro x hx
    have hgD : |lineRes f D x| ≤ δ :=
      properArc'_continuous_strip hf hlam hN2 hlower hlomem hhimem hlohiZ x hx
    -- `H x − w = sgn · lineRes f D x`.
    have hHxw : H x - w = sgn * lineRes f D x := by
      simp only [hHdef, signedRes, hwdef, ← hsgndef]
      rw [lineRes_same_slope (f := f) hDslope x, hqDR]
      ring
    rw [hHxw, abs_mul]
    have hsgnabs : |sgn| = 1 := by
      rw [hsgndef, lineSign']; split_ifs <;> simp
    rw [hsgnabs, one_mul]; exact hgD
  -- Apply the generic convex-arc lemma with split curvature `μ = 256λ`:
  -- `w ≤ M + δ + 4·(256λ/λ)/q = M + δ + 1024/q`.
  have hupper_w : w ≤ M + δ + 1024 / (q : ℝ) := by
    have h := convex_arc_height_le_min (mu := 256 * lam)
      hAB hHc hHd hHc' hHd' hconv hH'' hx₀mem hx₀min hMdef
      hloIcc hhiIcc hlohiR hstrip hlong hqR hlam (by linarith [hlam]) hδ
    have hratio : (256 : ℝ) * lam / lam = 256 := by
      field_simp
    rw [hratio] at h
    have hsimp : 4 * (256 : ℝ) / (q : ℝ) = 1024 / (q : ℝ) := by ring
    rwa [hsimp] at h
  -- Lower bound `M − δ ≤ w`:  `M = H x₀ ≤ H lo ≤ w + δ`.
  have hlower_w : M - δ ≤ w := by
    have hMlo : M ≤ H (lo : ℝ) := by rw [hMdef]; exact hx₀min hloIcc
    have hstrip_lo := hstrip (lo : ℝ) ⟨le_rfl, hlohiR.le⟩
    rw [abs_le] at hstrip_lo
    linarith [hMlo, hstrip_lo.2]
  -- Translate `w ∈ [M−δ, M+δ+1024/q]` to `|D.shift − q·c| ≤ qδ + 1024`.
  -- `(D.shift − D₀.shift)/q = sgn·w` and `D.shift − q·c = q·sgn·(w − (M + 512/q))`.
  set c : ℝ := (D₀.shift : ℝ) / (q : ℝ) + sgn * (M + 512 / (q : ℝ)) with hcdef
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  have hshift_eq : (D.shift : ℝ) - (q : ℝ) * c = (q : ℝ) * sgn * (w - (M + 512 / (q : ℝ))) := by
    -- LHS = D.shift − D₀.shift − q·sgn·(M+512/q);  RHS via `sgn² = 1` is the same.
    have hqc : (q : ℝ) * c = (D₀.shift : ℝ) + (q : ℝ) * sgn * (M + 512 / (q : ℝ)) := by
      rw [hcdef]; field_simp
    have hqsw : (q : ℝ) * sgn * w = ((D.shift : ℝ) - (D₀.shift : ℝ)) := by
      rw [hwdef]
      field_simp
      linear_combination ((D.shift : ℝ) - (D₀.shift : ℝ)) * hsgnsq
    rw [hqc, mul_sub, hqsw]; ring
  rw [hshift_eq, abs_mul]
  have hqsgn_abs : |(q : ℝ) * sgn| = (q : ℝ) := by
    rw [abs_mul]
    have hsgnabs : |sgn| = 1 := by rw [hsgndef, lineSign']; split_ifs <;> simp
    rw [hsgnabs, mul_one, abs_of_pos hqR]
  rw [hqsgn_abs]
  -- `|w − (M + 512/q)| ≤ δ + 512/q`, so `q·|…| ≤ qδ + 1024`.
  have h2q4q : (512 : ℝ) / (q : ℝ) + 512 / (q : ℝ) = 1024 / (q : ℝ) := by ring
  have hball : |w - (M + 512 / (q : ℝ))| ≤ δ + 512 / (q : ℝ) := by
    rw [abs_le]
    refine ⟨by linarith [hlower_w], by linarith [hupper_w, h2q4q]⟩
  calc (q : ℝ) * |w - (M + 512 / (q : ℝ))|
      ≤ (q : ℝ) * (δ + 512 / (q : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hball hqR.le
    _ = (q : ℝ) * δ + 512 := by
        rw [mul_add, mul_div_cancel₀ _ hqR.ne']

/-- **The b-count per slope** (writeup 624–642).  For fixed denominator `q` and fixed
slope `D₀.slope`, the number of Type II witness lines is `≤ 6`.

A `MajorLine` of slope `D₀.slope` is determined by its integer `shift`, so the filter
injects (via `D ↦ D.shift`) into the set of admissible shifts.  By `typeII_shift_loc`
every admissible shift lies in `[q·c − (qδ+2), q·c + (qδ+2)]`, an interval of length
`2(qδ + 2) ≤ 2·(1/64) + 4 < 5` (using `qδ ≤ denomCutoff = 1/64` for major lines), hence
contains `≤ 6` integers. -/
theorem typeII_b_count_per_slope (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hδ : 0 < δ) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (_hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    (q : ℤ) (D₀ : MajorLine) :
    ((typeIILines f N lam δ).filter
        (fun D => D.denom = q ∧ D.slope = D₀.slope)).card ≤ 1025 := by
  classical
  set S := (typeIILines f N lam δ).filter
      (fun D => D.denom = q ∧ D.slope = D₀.slope) with hSdef
  -- Empty case is trivial.
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · rw [hS0]; simp
  -- From a representative line, extract `q·δ ≤ 1/64` (major-line denominator cutoff).
  obtain ⟨D₁, hD₁S⟩ := hSne
  have hD₁mem : D₁ ∈ typeIILines f N lam δ := (Finset.mem_filter.mp hD₁S).1
  have hD₁q : D₁.denom = q := (Finset.mem_filter.mp hD₁S).2.1
  have hqpos : 0 < q := by rw [← hD₁q]; exact D₁.denom_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  -- The denominator cutoff `(q : ℝ) ≤ denomCutoff/δ = (1/64)/δ`, so `q·δ ≤ 1/64`.
  have hqcut : (q : ℝ) ≤ denomCutoff / δ := by
    obtain ⟨n, hn, hDn⟩ := mem_typeIILines.mp hD₁mem
    obtain ⟨a, b, _, _, _, _, _, _, _, _, hcut⟩ := witnessII_spec hn
    rw [hDn] at hcut
    have : ((D₁.denom : ℝ)) ≤ denomCutoff / δ := hcut
    rw [show ((D₁.denom : ℝ)) = (q : ℝ) by exact_mod_cast hD₁q] at this
    exact this
  have hqδ : (q : ℝ) * δ ≤ 1 / 64 := by
    have hcut' : denomCutoff / δ = (1 / 64) / δ := by rw [denomCutoff]
    rw [hcut'] at hqcut
    -- `q ≤ (1/64)/δ` over `δ > 0` gives `q·δ ≤ 1/64`.
    have hstep : (q : ℝ) * δ ≤ ((1 / 64) / δ) * δ :=
      mul_le_mul_of_nonneg_right hqcut hδ.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at hstep
  -- The localization center.
  obtain ⟨c, hloc⟩ := typeII_shift_loc hf hlam hδ hN2 hlower q D₀
  rw [← hSdef] at hloc
  -- Inject `D ↦ D.shift` into the integer interval of admissible shifts.
  set bLo : ℤ := ⌈(q : ℝ) * c - ((q : ℝ) * δ + 512)⌉ with hbLo
  set bHi : ℤ := ⌊(q : ℝ) * c + ((q : ℝ) * δ + 512)⌋ with hbHi
  have hmaps : Set.MapsTo (fun D : MajorLine => D.shift) (S : Set MajorLine)
      (Finset.Icc bLo bHi : Set ℤ) := by
    intro D hD
    have hDS : D ∈ S := hD
    have hb := hloc D hDS
    rw [abs_le] at hb
    simp only [Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rw [hbLo]
      refine Int.ceil_le.mpr ?_
      have : (q : ℝ) * c - ((q : ℝ) * δ + 512) ≤ (D.shift : ℝ) := by linarith [hb.1]
      exact_mod_cast this
    · rw [hbHi]
      refine Int.le_floor.mpr ?_
      have : (D.shift : ℝ) ≤ (q : ℝ) * c + ((q : ℝ) * δ + 512) := by linarith [hb.2]
      exact_mod_cast this
  have hinj : (S : Set MajorLine).InjOn (fun D : MajorLine => D.shift) := by
    intro D₂ hD₂ D₃ hD₃ hshift
    have h2 : D₂.slope = D₀.slope := (Finset.mem_filter.mp hD₂).2.2
    have h3 : D₃.slope = D₀.slope := (Finset.mem_filter.mp hD₃).2.2
    cases D₂; cases D₃
    simp_all
  have hcardle : S.card ≤ (Finset.Icc bLo bHi).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  -- Count integers in `[bLo, bHi]`: `bHi − bLo + 1 ≤ 6` since the real interval has
  -- length `2(qδ + 2) ≤ 2·(1/64) + 4 < 5`.
  have hIcc : (Finset.Icc bLo bHi).card = (bHi + 1 - bLo).toNat := Int.card_Icc _ _
  have hbnd : bHi + 1 - bLo ≤ 1025 := by
    have hfl : (bHi : ℝ) ≤ (q : ℝ) * c + ((q : ℝ) * δ + 512) := by
      rw [hbHi]; exact Int.floor_le _
    have hcl : (q : ℝ) * c - ((q : ℝ) * δ + 512) ≤ (bLo : ℝ) := by
      rw [hbLo]; exact Int.le_ceil _
    have hreal : (bHi : ℝ) - (bLo : ℝ) ≤ 2 * ((q : ℝ) * δ) + 1024 := by linarith
    have hreal' : (bHi : ℝ) - (bLo : ℝ) ≤ 2 * (1 / 64) + 1024 := by
      have : 2 * ((q : ℝ) * δ) ≤ 2 * (1 / 64) := by linarith [hqδ]
      linarith
    -- `bHi − bLo ≤ 1024.03... < 1025`, so `bHi − bLo ≤ 1024` as integers, `+1 ≤ 1025`.
    have hint : ((bHi - bLo : ℤ) : ℝ) ≤ 2 * (1 / 64) + 1024 := by push_cast; linarith
    have hle4 : (bHi - bLo : ℤ) ≤ 1024 := by
      by_contra hc
      have hge5 : (1025 : ℤ) ≤ bHi - bLo := by omega
      have : (1025 : ℝ) ≤ ((bHi - bLo : ℤ) : ℝ) := by exact_mod_cast hge5
      linarith
    omega
  calc S.card ≤ (Finset.Icc bLo bHi).card := hcardle
    _ = (bHi + 1 - bLo).toNat := hIcc
    _ ≤ 1025 := by omega


end Squarefree.Geometry
