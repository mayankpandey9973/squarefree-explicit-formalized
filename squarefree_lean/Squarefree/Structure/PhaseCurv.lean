import Squarefree.Structure.PhaseDeriv
import Mathlib

/-!
# §6 toolkit, Stage 3b: curvature bound for the phase `f̃ₐ(r)`

The §6 phase `f̃ₐ(r) = F_a(d̃ₐ(r)) = r·√(a² + 4√(X a³/r))/a²` (handle `ftil`, `PhaseDeriv`)
viewed as a function of `a`.  This module supplies the **second-`a`-derivative** data, which
is the curvature hypothesis `A²|∂²_a f̃ₐ| ≍ F` of Proposition 6.1 (writeup line 1255).

* `ftil_iteratedDeriv2`: the EXACT closed form
  `iteratedDeriv 2 (fun t => ftil X r t) a = r·(4a⁴ + 39a²w + 90w²)/(2a⁴D³)`
  where `w := √(X a³/r)` and `D := √(a²+4w)` (sympy-verified).
* `ftil_curv_bound`: the two-sided curvature bound over the window `[A/2, 5A/2]` under the
  regime `ρ ≥ 16` (i.e. `16a² ≤ 4√(X a³/r)`): there is `lam > 0` with
  `lam ≤ f̃'' ≤ 256·lam` everywhere on the window.

The second derivative is assembled from two `HasDerivAt` steps on the closed form, using the
square-variable technique (`w² = X a³/r`, `D² = a²+4w`) to discharge the nested `√` algebra.
-/

open Classical

namespace Squarefree

set_option maxHeartbeats 1000000

/-! ## First derivative of `ftil` -/

/-- Derivative of `t ↦ √(X t³/r)` at `a > 0`, in the clean form `3√(Xa³/r)/(2a)`. -/
private theorem hwfun_deriv (X r a : ℝ) (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    HasDerivAt (fun t => Real.sqrt (X * t ^ 3 / r))
      (3 * Real.sqrt (X * a ^ 3 / r) / (2 * a)) a := by
  have hraw : HasDerivAt (fun t => Real.sqrt (X * t ^ 3 / r))
      ((3 * X * a ^ 2 / r) / (2 * Real.sqrt (X * a ^ 3 / r))) a := by
    have hinner : HasDerivAt (fun t : ℝ => X * t ^ 3 / r) (3 * X * a ^ 2 / r) a := by
      have h : HasDerivAt (fun t : ℝ => X * t ^ 3 / r) ((X * (3 * a ^ 2)) / r) a := by
        simpa using ((hasDerivAt_pow 3 a).const_mul X).div_const r
      convert h using 1; ring
    have hpos : X * a ^ 3 / r ≠ 0 := by positivity
    have h := (Real.hasDerivAt_sqrt hpos).comp a hinner
    convert h using 1; ring
  convert hraw using 1
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hw : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  have key : X * a ^ 3 = w ^ 2 * r := by rw [hwsq]; field_simp
  have hr' : r ≠ 0 := ne_of_gt hr
  have ha' : a ≠ 0 := ne_of_gt ha
  have hw' : w ≠ 0 := ne_of_gt hw
  field_simp
  nlinarith [key]

/-- **First `a`-derivative of `f̃`.**  `f̃'(a) = −r(a²+5w)/(a³·D)`, `w=√(Xa³/r)`, `D=√(a²+4w)`. -/
private theorem ftil_deriv1 (X r a : ℝ) (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    HasDerivAt (fun t => ftil X r t)
      (-r * (a ^ 2 + 5 * Real.sqrt (X * a ^ 3 / r)) /
        (a ^ 3 * Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)))) a := by
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hDsq : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  have hrad : HasDerivAt (fun t => t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r))
      (2 * a + 6 * w / a) a := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
    have h2 := (hwfun_deriv X r a hX hr ha).const_mul 4
    rw [← hwdef] at h2
    have h := h1.add h2
    convert h using 1; field_simp; ring
  have hDpos' : a ^ 2 + 4 * w ≠ 0 := by positivity
  have hDderiv : HasDerivAt (fun t => Real.sqrt (t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r)))
      ((2 * a + 6 * w / a) / (2 * D)) a := by
    have h := (Real.hasDerivAt_sqrt hDpos').comp a hrad
    rw [← hDdef] at h
    convert h using 1; ring
  have hden : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
  have hnum := hDderiv.const_mul r
  have hq := hnum.div hden (pow_ne_zero 2 (ne_of_gt ha))
  rw [← hDdef] at hq
  -- `ftil` unfolds to `fun t => r*√(t²+4√(Xt³/r))/t²`
  have hfun : (fun t => ftil X r t)
      = fun t => r * Real.sqrt (t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r)) / t ^ 2 := by
    funext t; rfl
  rw [hfun]
  convert hq using 1
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have ha' : a ≠ 0 := ne_of_gt ha
  have hD' : D ≠ 0 := ne_of_gt hDpos
  field_simp
  nlinarith [hDsq, hwsq, sq_nonneg a, sq_nonneg w, sq_nonneg D]

/-- **First `a`-derivative of `f̃`** (public handle).  `f̃'(a) = −r(a²+5w)/(a³·D)`,
`w=√(Xa³/r)`, `D=√(a²+4w)`. -/
theorem ftil_hasDerivAt1 (X r a : ℝ) (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    HasDerivAt (fun t => ftil X r t)
      (-r * (a ^ 2 + 5 * Real.sqrt (X * a ^ 3 / r)) /
        (a ^ 3 * Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)))) a :=
  ftil_deriv1 X r a hX hr ha

/-! ## Second derivative of `ftil` (exact closed form) -/

/-- **Second `a`-derivative of `f̃`** (as the derivative of its first-derivative function):
`(d/dt) f̃'(t)|_a = r(4a⁴+39a²w+90w²)/(2a⁴D³)`, `w=√(Xa³/r)`, `D=√(a²+4w)`. -/
private theorem ftil_deriv2 (X r a : ℝ) (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    HasDerivAt (fun t => -r * (t ^ 2 + 5 * Real.sqrt (X * t ^ 3 / r)) /
        (t ^ 3 * Real.sqrt (t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r))))
      (r * (4 * a ^ 4 + 39 * a ^ 2 * Real.sqrt (X * a ^ 3 / r)
          + 90 * (Real.sqrt (X * a ^ 3 / r)) ^ 2) /
        (2 * a ^ 4 * (Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) ^ 3)) a := by
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hDsq : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  have hwf : HasDerivAt (fun t => Real.sqrt (X * t ^ 3 / r)) (3 * w / (2 * a)) a := by
    have h := hwfun_deriv X r a hX hr ha; rw [← hwdef] at h; exact h
  have hrad : HasDerivAt (fun t => t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r))
      (2 * a + 6 * w / a) a := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
    have h2 := hwf.const_mul 4
    have h := h1.add h2
    convert h using 1; field_simp; ring
  have hDpos' : a ^ 2 + 4 * w ≠ 0 := by positivity
  have hDf : HasDerivAt (fun t => Real.sqrt (t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r)))
      ((2 * a + 6 * w / a) / (2 * D)) a := by
    have h := (Real.hasDerivAt_sqrt hDpos').comp a hrad
    rw [← hDdef] at h
    convert h using 1; ring
  have hnum : HasDerivAt (fun t => -r * (t ^ 2 + 5 * Real.sqrt (X * t ^ 3 / r)))
      (-r * (2 * a + 5 * (3 * w / (2 * a)))) a := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
    have h2 := hwf.const_mul 5
    have h := (h1.add h2).const_mul (-r)
    convert h using 1
  have hden : HasDerivAt (fun t => t ^ 3 * Real.sqrt (t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r)))
      (3 * a ^ 2 * D + a ^ 3 * ((2 * a + 6 * w / a) / (2 * D))) a := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * a ^ 2) a := by simpa using hasDerivAt_pow 3 a
    have h := h1.mul hDf
    convert h using 1
  have hden_ne : a ^ 3 * D ≠ 0 := by positivity
  have hq := hnum.div hden hden_ne
  -- reduce raw quotient-rule output to the closed form via `D² = a²+4w`
  have hred : (-r * (2 * a + 5 * (3 * w / (2 * a))) * (a ^ 3 * D) -
        (-r * (a ^ 2 + 5 * w)) * (3 * a ^ 2 * D + a ^ 3 * ((2 * a + 6 * w / a) / (2 * D))))
        / (a ^ 3 * D) ^ 2
      = r * (4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2) / (2 * a ^ 4 * D ^ 3) := by
    have ha' : a ≠ 0 := ne_of_gt ha
    have hD' : D ≠ 0 := ne_of_gt hDpos
    field_simp
    nlinarith [hDsq, sq_nonneg a, sq_nonneg w, sq_nonneg D, mul_pos ha hwpos,
      mul_pos (mul_pos ha hwpos) hDpos]
  rw [hred] at hq
  -- `hq` now has exactly the target derivative value (matching `w`,`D` folds)
  exact hq

/-- **The EXACT second-derivative identity** (sympy-verified):
`iteratedDeriv 2 (fun t => ftil X r t) a = r·(4a⁴ + 39a²w + 90w²)/(2a⁴D³)`,
`w := √(X a³/r)`, `D := √(a²+4w)`.  All factors positive, so `f̃'' > 0`. -/
theorem ftil_iteratedDeriv2 {X r a : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    iteratedDeriv 2 (fun t => ftil X r t) a
      = r * (4 * a ^ 4 + 39 * a ^ 2 * Real.sqrt (X * a ^ 3 / r)
          + 90 * (Real.sqrt (X * a ^ 3 / r)) ^ 2) /
        (2 * a ^ 4 * (Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) ^ 3) := by
  have hL : iteratedDeriv 2 (fun t => ftil X r t) a
      = deriv (deriv (fun t => ftil X r t)) a := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hL]
  -- `deriv ftil =ᶠ[nhds a] f̃'-function` on the open set `{a' | 0 < a'}`
  have hee : deriv (fun t => ftil X r t)
      =ᶠ[nhds a] (fun t => -r * (t ^ 2 + 5 * Real.sqrt (X * t ^ 3 / r)) /
        (t ^ 3 * Real.sqrt (t ^ 2 + 4 * Real.sqrt (X * t ^ 3 / r)))) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds ha) ?_
    intro a' ha'
    exact (ftil_deriv1 X r a' hX hr ha').deriv
  rw [hee.deriv_eq]
  exact (ftil_deriv2 X r a hX hr ha).deriv

/-! ## Two-sided curvature bound -/

/-- The reference profile `M(a) := r·√(√(X a³/r))/a⁴` controlling `f̃''` up to absolute
constants.  Its fourth power is the clean rational `r³X/a¹³`. -/
private noncomputable def Mfun (X r a : ℝ) : ℝ :=
  r * Real.sqrt (Real.sqrt (X * a ^ 3 / r)) / a ^ 4

/-- `Mfun X r a > 0` for positive inputs. -/
private theorem Mfun_pos {X r a : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    0 < Mfun X r a := by
  have : 0 < Real.sqrt (Real.sqrt (X * a ^ 3 / r)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  unfold Mfun; positivity

/-- The fourth-power identity `(r·√(√(Xa³/r)))⁴ = X a³/r`, ie `v⁴ = X a³/r` for `v = √(√(Xa³/r))`. -/
private theorem v_pow4 {X r a : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a) :
    (Real.sqrt (Real.sqrt (X * a ^ 3 / r))) ^ 4 = X * a ^ 3 / r := by
  have h1 : (Real.sqrt (Real.sqrt (X * a ^ 3 / r))) ^ 2 = Real.sqrt (X * a ^ 3 / r) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : (Real.sqrt (X * a ^ 3 / r)) ^ 2 = X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  calc (Real.sqrt (Real.sqrt (X * a ^ 3 / r))) ^ 4
      = ((Real.sqrt (Real.sqrt (X * a ^ 3 / r))) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (X * a ^ 3 / r)) ^ 2 := by rw [h1]
    _ = X * a ^ 3 / r := h2

/-- **Upper f̃'' bound** at a window point under the regime: `f̃''(a) ≤ (25/4)·M(a)`. -/
private theorem ftil_dd_le {X r a : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a)
    (hreg : 16 * a ^ 2 ≤ 4 * Real.sqrt (X * a ^ 3 / r)) :
    iteratedDeriv 2 (fun t => ftil X r t) a ≤ (25 / 4) * Mfun X r a := by
  rw [ftil_iteratedDeriv2 hX hr ha]
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  set v := Real.sqrt w with hvdef
  have hvpos : 0 < v := Real.sqrt_pos.mpr hwpos
  have hv2 : v ^ 2 = w := Real.sq_sqrt hwpos.le
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  have hreg' : 4 * a ^ 2 ≤ w := by linarith
  -- D³ ≥ 8 w v
  have hD3lo : 8 * w * v ≤ D ^ 3 := by
    have hDge : 2 * v ≤ D := by
      nlinarith [sq_nonneg (D - 2 * v), hv2, hD2, hreg', mul_pos hwpos hvpos]
    have hD2ge : 4 * w ≤ D ^ 2 := by nlinarith [hD2, hreg', sq_nonneg a]
    nlinarith [hDge, hD2ge, mul_pos hwpos hvpos, hv2, hvpos.le, hwpos.le]
  have hMfun : Mfun X r a = r * v / a ^ 4 := by
    simp only [Mfun, ← hwdef, ← hvdef]
  rw [hMfun]
  -- bound the fraction
  have hstep : r * (4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2) / (2 * a ^ 4 * D ^ 3)
      ≤ r * (100 * w ^ 2) / (2 * a ^ 4 * (8 * w * v)) := by
    gcongr ?_ / ?_
    · have : 4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2 ≤ 100 * w ^ 2 := by
        nlinarith [hreg', sq_nonneg a, sq_nonneg w, mul_pos hwpos hwpos]
      exact mul_le_mul_of_nonneg_left this hr.le
    · exact mul_le_mul_of_nonneg_left hD3lo (by positivity)
  refine hstep.trans (le_of_eq ?_)
  have ha' : a ≠ 0 := ne_of_gt ha
  have hw' : w ≠ 0 := ne_of_gt hwpos
  have hv' : v ≠ 0 := ne_of_gt hvpos
  rw [show w = v ^ 2 from hv2.symm]; field_simp; ring

/-- **Lower f̃'' bound** at a window point under the regime: `5·M(a) ≤ f̃''(a)`. -/
private theorem ftil_dd_ge {X r a : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a)
    (hreg : 16 * a ^ 2 ≤ 4 * Real.sqrt (X * a ^ 3 / r)) :
    5 * Mfun X r a ≤ iteratedDeriv 2 (fun t => ftil X r t) a := by
  rw [ftil_iteratedDeriv2 hX hr ha]
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  set v := Real.sqrt w with hvdef
  have hvpos : 0 < v := Real.sqrt_pos.mpr hwpos
  have hv2 : v ^ 2 = w := Real.sq_sqrt hwpos.le
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  have hreg' : 4 * a ^ 2 ≤ w := by linarith
  have ha2 : a ^ 2 ≤ w / 4 := by linarith
  -- D³ ≤ 9 w v
  have hD3hi : D ^ 3 ≤ 9 * w * v := by
    have hD2le : D ^ 2 ≤ (441 / 100) * w := by nlinarith [hD2, ha2]
    have hD2le' : D ^ 2 ≤ (17 / 4) * w := by nlinarith [hD2, ha2]
    have hDle : D ≤ (21 / 10) * v := by
      nlinarith [hD2le, hv2, sq_nonneg ((21 / 10) * v - D), mul_pos hvpos hvpos]
    nlinarith [hDle, hD2le', mul_pos hwpos hvpos, hv2, hvpos.le, hwpos.le,
      mul_nonneg hvpos.le hwpos.le]
  have hMfun : Mfun X r a = r * v / a ^ 4 := by
    simp only [Mfun, ← hwdef, ← hvdef]
  rw [hMfun]
  have hstep : r * (90 * w ^ 2) / (2 * a ^ 4 * (9 * w * v))
      ≤ r * (4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2) / (2 * a ^ 4 * D ^ 3) := by
    gcongr ?_ / ?_
    · have : 90 * w ^ 2 ≤ 4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2 := by
        nlinarith [pow_pos ha 4, mul_nonneg (sq_nonneg a) hwpos.le]
      exact mul_le_mul_of_nonneg_left this hr.le
    · exact mul_le_mul_of_nonneg_left hD3hi (by positivity)
  refine le_of_eq ?_ |>.trans hstep
  have ha' : a ≠ 0 := ne_of_gt ha
  have hw' : w ≠ 0 := ne_of_gt hwpos
  have hv' : v ≠ 0 := ne_of_gt hvpos
  rw [show w = v ^ 2 from hv2.symm]; field_simp; ring

/-- **Monotonicity of `M`:** if `a ≤ a₀` (both positive) then `M(a₀) ≤ M(a)`. -/
private theorem Mfun_antitone {X r a a₀ : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a)
    (ha₀ : 0 < a₀) (hle : a ≤ a₀) : Mfun X r a₀ ≤ Mfun X r a := by
  set v := Real.sqrt (Real.sqrt (X * a ^ 3 / r)) with hvdef
  set v₀ := Real.sqrt (Real.sqrt (X * a₀ ^ 3 / r)) with hv0def
  have hva : v ^ 4 = X * a ^ 3 / r := v_pow4 hX hr ha
  have hv0a : v₀ ^ 4 = X * a₀ ^ 3 / r := v_pow4 hX hr ha₀
  have ha' : a ≠ 0 := ne_of_gt ha
  have ha0' : a₀ ≠ 0 := ne_of_gt ha₀
  have hr' : r ≠ 0 := ne_of_gt hr
  show r * v₀ / a₀ ^ 4 ≤ r * v / a ^ 4
  have hR : 0 ≤ r * v / a ^ 4 := by positivity
  have e1 : (r * v₀ / a₀ ^ 4) ^ 4 = r ^ 3 * X / a₀ ^ 13 := by
    rw [div_pow, mul_pow, hv0a]; field_simp
  have e2 : (r * v / a ^ 4) ^ 4 = r ^ 3 * X / a ^ 13 := by
    rw [div_pow, mul_pow, hva]; field_simp
  have h4 : (r * v₀ / a₀ ^ 4) ^ 4 ≤ (r * v / a ^ 4) ^ 4 := by
    rw [e1, e2]
    apply (div_le_div_iff_of_pos_left (by positivity) (by positivity) (by positivity)).mpr
    exact pow_le_pow_left₀ ha.le hle 13
  exact le_of_pow_le_pow_left₀ (by norm_num) hR h4

/-- **Ratio control of `M`:** for `a` in the window (`A/2 ≤ a`) and `a₀ = 5A/2`,
`M(a) ≤ (1024/5)·M(a₀)`. -/
private theorem Mfun_ratio {X r A a a₀ : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a)
    (ha₀ : 0 < a₀) (haL : A / 2 ≤ a) (ha0eq : a₀ = 5 * A / 2) :
    Mfun X r a ≤ (1024 / 5) * Mfun X r a₀ := by
  set v := Real.sqrt (Real.sqrt (X * a ^ 3 / r)) with hvdef
  set v₀ := Real.sqrt (Real.sqrt (X * a₀ ^ 3 / r)) with hv0def
  have hva : v ^ 4 = X * a ^ 3 / r := v_pow4 hX hr ha
  have hv0a : v₀ ^ 4 = X * a₀ ^ 3 / r := v_pow4 hX hr ha₀
  have ha' : a ≠ 0 := ne_of_gt ha
  have ha0' : a₀ ≠ 0 := ne_of_gt ha₀
  have hr' : r ≠ 0 := ne_of_gt hr
  show r * v / a ^ 4 ≤ (1024 / 5) * (r * v₀ / a₀ ^ 4)
  have hbig : 0 ≤ (1024 / 5) * (r * v₀ / a₀ ^ 4) := by positivity
  have e1 : (r * v / a ^ 4) ^ 4 = r ^ 3 * X / a ^ 13 := by
    rw [div_pow, mul_pow, hva]; field_simp
  have e2 : ((1024 / 5) * (r * v₀ / a₀ ^ 4)) ^ 4 = (1024 / 5) ^ 4 * (r ^ 3 * X / a₀ ^ 13) := by
    have hin : (r * v₀ / a₀ ^ 4) ^ 4 = r ^ 3 * X / a₀ ^ 13 := by
      rw [div_pow, mul_pow, hv0a]; field_simp
    rw [mul_pow, hin]
  have ha0le : a₀ ≤ 5 * a := by rw [ha0eq]; linarith
  have ha13key : a₀ ^ 13 ≤ (1024 / 5) ^ 4 * a ^ 13 := by
    calc a₀ ^ 13 ≤ (5 * a) ^ 13 := pow_le_pow_left₀ ha₀.le ha0le 13
      _ = 5 ^ 13 * a ^ 13 := by ring
      _ ≤ (1024 / 5) ^ 4 * a ^ 13 := by
          nlinarith [pow_pos ha 13, (by norm_num : (5 : ℝ) ^ 13 ≤ (1024 / 5) ^ 4)]
  have hrX : 0 < r ^ 3 * X := by positivity
  have h4 : (r * v / a ^ 4) ^ 4 ≤ ((1024 / 5) * (r * v₀ / a₀ ^ 4)) ^ 4 := by
    rw [e1, e2]
    have hrhs : (1024 / 5 : ℝ) ^ 4 * (r ^ 3 * X / a₀ ^ 13)
        = (r ^ 3 * X) * ((1024 / 5) ^ 4 / a₀ ^ 13) := by ring
    have hlhs : r ^ 3 * X / a ^ 13 = (r ^ 3 * X) * (1 / a ^ 13) := by ring
    rw [hrhs, hlhs]
    apply mul_le_mul_of_nonneg_left _ hrX.le
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact ha13key
  exact le_of_pow_le_pow_left₀ (by norm_num) hbig h4

/-- **§6 curvature bound** (writeup line 1255, `A²|∂²_a f̃ₐ| ≍ F`).
Over the window `[A/2, 5A/2]`, under the regime `ρ ≥ 16` (`16a² ≤ 4√(X a³/r)`), the
second `a`-derivative of the phase `f̃ₐ(r)` is two-sided with absolute ratio `≤ 256`. -/
theorem ftil_curv_bound {X r A : ℝ} (hX : 0 < X) (hr : 0 < r) (hA : 0 < A)
    (hreg : ∀ a ∈ Set.Icc (A / 2) (5 * A / 2), 16 * a ^ 2 ≤ 4 * Real.sqrt (X * a ^ 3 / r)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ a ∈ Set.Icc (A / 2) (5 * A / 2),
      lam ≤ iteratedDeriv 2 (fun t => ftil X r t) a ∧
      iteratedDeriv 2 (fun t => ftil X r t) a ≤ 256 * lam := by
  set a₀ := 5 * A / 2 with ha0def
  have ha₀ : 0 < a₀ := by rw [ha0def]; linarith
  have hlampos : 0 < 5 * Mfun X r a₀ := by
    have := Mfun_pos hX hr ha₀; positivity
  refine ⟨5 * Mfun X r a₀, hlampos, ?_⟩
  intro a ha
  obtain ⟨haL, haU⟩ := ha
  have hapos : 0 < a := by linarith
  have hreg_a : 16 * a ^ 2 ≤ 4 * Real.sqrt (X * a ^ 3 / r) := hreg a ⟨haL, haU⟩
  refine ⟨?_, ?_⟩
  · -- lam ≤ f''(a):  5 M(a₀) ≤ 5 M(a) ≤ f''(a)
    have h1 : Mfun X r a₀ ≤ Mfun X r a :=
      Mfun_antitone hX hr hapos ha₀ (by rw [ha0def]; linarith)
    have h2 : 5 * Mfun X r a ≤ iteratedDeriv 2 (fun t => ftil X r t) a :=
      ftil_dd_ge hX hr hapos hreg_a
    linarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 5)]
  · -- f''(a) ≤ 256 lam:  f''(a) ≤ (25/4) M(a) ≤ (25/4)(1024/5) M(a₀) = 1280 M(a₀) = 256 lam
    have h1 : iteratedDeriv 2 (fun t => ftil X r t) a ≤ (25 / 4) * Mfun X r a :=
      ftil_dd_le hX hr hapos hreg_a
    have h2 : Mfun X r a ≤ (1024 / 5) * Mfun X r a₀ :=
      Mfun_ratio hX hr hapos ha₀ haL ha0def
    have h3 : (25 / 4) * Mfun X r a ≤ (25 / 4) * ((1024 / 5) * Mfun X r a₀) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h4 : (25 / 4 : ℝ) * ((1024 / 5) * Mfun X r a₀) = 256 * (5 * Mfun X r a₀) := by ring
    linarith [h1, h3, h4.le]

end Squarefree
