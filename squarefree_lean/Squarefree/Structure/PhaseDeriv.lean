import Squarefree.Structure.ADecompAux
import Squarefree.Structure.DaSpacing
import Squarefree.Params
import Mathlib

/-!
# §6 toolkit, Stage 1: `F_a` / `R_a` derivative calculus

Pure analytic foundation reused by §5/§6/§7.  We provide, for the rational phase functions
`Ffun X a d = X/d² − X/(d+a)²` (= `F_a(d)`, `ADecompAux`) and
`Rfun X a d = −(2d−a)X/d² + (2d+3a)X/(d+a)²` (= `R_a(d)`, `DaSpacing`):

* closed-form factorizations (`Rfun_factor` lives in `FiberAux`/here, `Ffun_factor` in `ADecompAux`);
* first `d`-derivatives as `HasDerivAt` at a point (off the poles `d ≠ 0`, `d+a ≠ 0`);
* the second `d`-derivative of `Ffun` (as a `HasDerivAt` of its first-derivative function), and
  the `iteratedDeriv 2` value on the pole-free set;
* `ContDiffAt ℝ 2` smoothness of both phases away from poles;
* the fixed sign `R_a'(d) < 0` for `0 < a`, `0 < d`, `0 < X`, which makes `d̃_a = R_a^{-1}`
  well-defined (Stage 2).

The first-derivative `HasDerivAt` for `Ffun` is reused from `NearCurveBridge` only conceptually;
here we re-establish it self-containedly (so this foundational module does not depend on the
bridge) and additionally produce the `Rfun` derivative and second-order data.

`R'_formula`: `R_a'(d) = −2 X a³ (2d + a) / (d³ (d+a)³)`.
-/

open Classical

namespace Squarefree

set_option maxHeartbeats 1000000

/-! ## Factorizations -/

/-- Closed form of `R_a(d) = X a³/(d²(d+a)²)` (sympy-verified, writeup line 334).
A copy of `Squarefree.Rfun_factor` (`FiberAux`); restated here so this module is self-contained
without pulling in the fiber-counting layer. -/
theorem Rfun_factor' (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    Rfun X a d = X * a ^ 3 / (d ^ 2 * (d + a) ^ 2) := by
  unfold Rfun; field_simp; ring

/-- Closed form of `F_a(d) = X a (a + 2d)/(d²(d+a)²)` (sympy-verified).
Public restatement of the `private Ffun_factor` in `ADecompAux`. -/
theorem Ffun_factor' (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    Ffun X a d = X * a * (a + 2 * d) / (d ^ 2 * (d + a) ^ 2) := by
  unfold Ffun; field_simp; ring

/-! ## First derivatives -/

/-- `HasDerivAt` of `s ↦ X/s²` at `s ≠ 0`, derivative `−2X/s³`. -/
private theorem hasDerivAt_inv_sq (X s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t => X / t ^ 2) (-2 * X / s ^ 3) s := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s ^ 1) s := by
    simpa using (hasDerivAt_pow 2 s)
  have h := (hasDerivAt_const s X).div hpow (pow_ne_zero 2 hs)
  convert h using 1
  field_simp; ring

/-- `HasDerivAt` of `s ↦ X/(s+a)²` at points where `s+a ≠ 0`, derivative `−2X/(s+a)³`. -/
private theorem hasDerivAt_inv_sq_shift (X a s : ℝ) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => X / (t + a) ^ 2) (-2 * X / (s + a) ^ 3) s := by
  have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).add_const a
  have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 2) (2 * (s + a) ^ 1 * 1) s := by
    simpa using (hasDerivAt_pow 2 (s + a)).comp s hshift
  have h := (hasDerivAt_const s X).div hpow (pow_ne_zero 2 hsa)
  convert h using 1
  field_simp; ring

/-- **First `d`-derivative of `F_a`.** `F_a'(d) = −2X/d³ + 2X/(d+a)³` (off the poles). -/
theorem Ffun_hasDerivAt_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => Ffun X a t) (-2 * X / d ^ 3 + 2 * X / (d + a) ^ 3) d := by
  have h1 := hasDerivAt_inv_sq X d hd
  have h2 := hasDerivAt_inv_sq_shift X a d hda
  have h := h1.sub h2
  have hfun : (fun t => Ffun X a t) = (fun t => X / t ^ 2) - (fun t => X / (t + a) ^ 2) := by
    funext t; simp [Ffun, Pi.sub_apply]
  rw [hfun]; convert h using 1; ring

/-- The closed-form `R'_formula`: `R_a'(d) = −2 X a³ (2d + a)/(d³(d+a)³)` (off the poles). -/
theorem Rfun_hasDerivAt_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => Rfun X a t)
      (-2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3)) d := by
  -- Differentiate the unfolded `Rfun = −(2t−a)·X/t² + (2t+3a)·X/(t+a)²` via product/quotient rules.
  -- term 1: g₁(t) = −(2t−a)·X / t²
  have hpow2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * d ^ 1) d := by simpa using (hasDerivAt_pow 2 d)
  have hg1num : HasDerivAt (fun t : ℝ => -(2 * t - a) * X) (-(2) * X) d := by
    have hlin : HasDerivAt (fun t : ℝ => -(2 * t - a) * X) ((-(2 * 1 - 0)) * X) d := by
      have h := (((hasDerivAt_id d).const_mul (2:ℝ)).sub_const a).neg.mul_const X
      simpa using h
    simpa using hlin
  have hg1 : HasDerivAt (fun t : ℝ => -(2 * t - a) * X / t ^ 2)
      ((-(2) * X * d ^ 2 - -(2 * d - a) * X * (2 * d ^ 1)) / (d ^ 2) ^ 2) d :=
    hg1num.div hpow2 (pow_ne_zero 2 hd)
  -- term 2: g₂(t) = (2t+3a)·X / (t+a)²
  have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) d := by
    simpa using (hasDerivAt_id d).add_const a
  have hpow2s : HasDerivAt (fun t : ℝ => (t + a) ^ 2) (2 * (d + a) ^ 1 * 1) d := by
    simpa using (hasDerivAt_pow 2 (d + a)).comp d hshift
  have hg2num : HasDerivAt (fun t : ℝ => (2 * t + 3 * a) * X) ((2) * X) d := by
    have h := (((hasDerivAt_id d).const_mul (2:ℝ)).add_const (3 * a)).mul_const X
    simpa using h
  have hg2 : HasDerivAt (fun t : ℝ => (2 * t + 3 * a) * X / (t + a) ^ 2)
      (((2) * X * (d + a) ^ 2 - (2 * d + 3 * a) * X * (2 * (d + a) ^ 1 * 1)) / ((d + a) ^ 2) ^ 2) d :=
    hg2num.div hpow2s (pow_ne_zero 2 hda)
  have h := hg1.add hg2
  have hfun : (fun t => Rfun X a t)
      = (fun t : ℝ => -(2 * t - a) * X / t ^ 2) + (fun t : ℝ => (2 * t + 3 * a) * X / (t + a) ^ 2) := by
    funext t; simp [Rfun, Pi.add_apply]
  rw [hfun]
  convert h using 1
  field_simp; ring

/-! ## Second derivative of `F_a` -/

/-- `HasDerivAt` of `s ↦ −2X/s³` at `s ≠ 0`, derivative `6X/s⁴`. -/
private theorem hasDerivAt_neg2_inv_cube (X s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t => -2 * X / t ^ 3) (6 * X / s ^ 4) s := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 3) (3 * s ^ 2) s := by simpa using (hasDerivAt_pow 3 s)
  have h := (hasDerivAt_const s (-2 * X)).div hpow (pow_ne_zero 3 hs)
  convert h using 1
  field_simp; ring

/-- `HasDerivAt` of `s ↦ 2X/(s+a)³` at `s+a ≠ 0`, derivative `−6X/(s+a)⁴`. -/
private theorem hasDerivAt_2_inv_cube_shift (X a s : ℝ) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => 2 * X / (t + a) ^ 3) (-6 * X / (s + a) ^ 4) s := by
  have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).add_const a
  have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 3) (3 * (s + a) ^ 2 * 1) s := by
    simpa using (hasDerivAt_pow 3 (s + a)).comp s hshift
  have h := (hasDerivAt_const s (2 * X)).div hpow (pow_ne_zero 3 hsa)
  convert h using 1
  field_simp; ring

/-- **Second `d`-derivative of `F_a`** (as the derivative of its first-derivative function).
`(d/dt)(−2X/t³ + 2X/(t+a)³)|_{t=d} = 6X/d⁴ − 6X/(d+a)⁴`. -/
theorem Ffun_hasDerivAt2_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => -2 * X / t ^ 3 + 2 * X / (t + a) ^ 3)
      (6 * X / d ^ 4 - 6 * X / (d + a) ^ 4) d := by
  have h := (hasDerivAt_neg2_inv_cube X d hd).add (hasDerivAt_2_inv_cube_shift X a d hda)
  convert h using 1; ring

/-- The first derivative function `deriv (fun t => Ffun X a t)` agrees with the explicit
`fun t => −2X/t³ + 2X/(t+a)³` on a neighborhood of any pole-free point. -/
private theorem deriv_Ffun_eventuallyEq (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    deriv (fun t => Ffun X a t)
      =ᶠ[nhds d] (fun t => -2 * X / t ^ 3 + 2 * X / (t + a) ^ 3) := by
  -- on the open pole-free set, `deriv` equals the explicit first-derivative pointwise
  have hopen : IsOpen {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} :=
    (isOpen_ne.preimage continuous_id).inter (isOpen_ne.preimage (continuous_id.add continuous_const))
  have hmem : d ∈ {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} := ⟨hd, hda⟩
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
  intro t ht
  exact (Ffun_hasDerivAt_d X a t ht.1 ht.2).deriv

/-- **`iteratedDeriv 2` value of `F_a`** on the pole-free set:
`iteratedDeriv 2 (fun t => Ffun X a t) d = 6X/d⁴ − 6X/(d+a)⁴`. -/
theorem Ffun_iteratedDeriv2_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 2 (fun t => Ffun X a t) d = 6 * X / d ^ 4 - 6 * X / (d + a) ^ 4 := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- second deriv = deriv (deriv f); rewrite the inner `deriv f` to the explicit function
  rw [(deriv_Ffun_eventuallyEq X a d hd hda).deriv_eq]
  exact (Ffun_hasDerivAt2_d X a d hd hda).deriv

/-! ## Smoothness away from poles -/

/-- `Ffun X a` is `C²` (indeed `C^∞`) at any pole-free point. -/
theorem Ffun_contDiffAt {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ 2 (fun t => Ffun X a t) d := by
  have h1 : ContDiffAt ℝ 2 (fun t : ℝ => X / t ^ 2) d :=
    (contDiffAt_const).div (contDiffAt_id.pow 2) (pow_ne_zero 2 hd)
  have h2 : ContDiffAt ℝ 2 (fun t : ℝ => X / (t + a) ^ 2) d :=
    (contDiffAt_const).div ((contDiffAt_id.add contDiffAt_const).pow 2) (pow_ne_zero 2 hda)
  have h := h1.sub h2
  have hfun : (fun t => Ffun X a t) = (fun t : ℝ => X / t ^ 2) - (fun t : ℝ => X / (t + a) ^ 2) := by
    funext t; simp [Ffun, Pi.sub_apply]
  rw [hfun]; exact h

/-- `Rfun X a` is `C²` (indeed `C^∞`) at any pole-free point. -/
theorem Rfun_contDiffAt {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ 2 (fun t => Rfun X a t) d := by
  have hn1 : ContDiffAt ℝ 2 (fun t : ℝ => -(2 * t - a) * X) d := by fun_prop
  have hn2 : ContDiffAt ℝ 2 (fun t : ℝ => (2 * t + 3 * a) * X) d := by fun_prop
  have h1 : ContDiffAt ℝ 2 (fun t : ℝ => -(2 * t - a) * X / t ^ 2) d :=
    hn1.div (contDiffAt_id.pow 2) (pow_ne_zero 2 hd)
  have h2 : ContDiffAt ℝ 2 (fun t : ℝ => (2 * t + 3 * a) * X / (t + a) ^ 2) d :=
    hn2.div ((contDiffAt_id.add contDiffAt_const).pow 2) (pow_ne_zero 2 hda)
  have h := h1.add h2
  have hfun : (fun t => Rfun X a t)
      = (fun t : ℝ => -(2 * t - a) * X / t ^ 2) + (fun t : ℝ => (2 * t + 3 * a) * X / (t + a) ^ 2) := by
    funext t; simp [Rfun, Pi.add_apply]
  rw [hfun]; exact h

/-! ## Fixed sign of `R_a'` -/

/-- **`R_a'(d) < 0`** for `0 < a`, `0 < d`, `0 < X`: the closed form
`R_a'(d) = −2 X a³ (2d + a)/(d³(d+a)³)` is strictly negative, so `R_a` is strictly monotone
and `d̃_a = R_a^{-1}` is well-defined (Stage 2 input). -/
theorem Rfun_deriv_neg {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    -2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3) < 0 := by
  have hda : 0 < d + a := by linarith
  have hnum : 0 < 2 * X * a ^ 3 * (2 * d + a) := by positivity
  have hden : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
  rw [show -2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3)
        = -(2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3)) by ring]
  simpa using div_pos hnum hden

/-- The `d`-derivative of `R_a` is nonzero for `0 < a`, `0 < d`, `0 < X`, hence `R_a` is locally
invertible.  (Derivative value plus its strict sign.) -/
theorem Rfun_deriv_ne_zero {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (fun t => Rfun X a t)
        (-2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3)) d
      ∧ (-2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3)) ≠ 0 :=
  ⟨Rfun_hasDerivAt_d X a d (ne_of_gt hd) (by positivity),
    ne_of_lt (Rfun_deriv_neg hX ha hd)⟩

/-! ## `deriv` corollaries -/

/-- `deriv (fun t => Ffun X a t) d = −2X/d³ + 2X/(d+a)³`. -/
theorem Ffun_deriv_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    deriv (fun t => Ffun X a t) d = -2 * X / d ^ 3 + 2 * X / (d + a) ^ 3 :=
  (Ffun_hasDerivAt_d X a d hd hda).deriv

/-- `deriv (fun t => Rfun X a t) d = −2 X a³ (2d + a)/(d³(d+a)³)`. -/
theorem Rfun_deriv_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    deriv (fun t => Rfun X a t) d = -2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3) :=
  (Rfun_hasDerivAt_d X a d hd hda).deriv

/-! ## Stage 2: closed-form inverse `d̃ₐ(r)` of `R_a(·)`

Solving `R_a(d) = r` at fixed `a` (writeup line 339).  Since `R_a(d) = X a³/(d²(d+a)²)`,
setting `= r` gives `d(d+a) = √(X a³/r)`, hence the positive root
`d = (−a + √(a² + 4√(X a³/r)))/2`. -/

/-- The closed-form inverse `d̃ₐ(r) = R_a^{-1}(r)`: the positive root of `d(d+a) = √(X a³/r)`. -/
noncomputable def dtilde (X r a : ℝ) : ℝ :=
  (-a + Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) / 2

/-- **Positivity of `d̃ₐ(r)`.** -/
theorem dtilde_pos {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    0 < dtilde X r a := by
  have hw : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
  -- `√(a² + 4w) > a` since `a² + 4w > a²` and `a ≥ 0` (via `Real.lt_sqrt`).
  have hgt : a < Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) :=
    (Real.lt_sqrt ha.le).mpr (by nlinarith)
  unfold dtilde
  linarith

/-- **The key quadratic identity** `d̃ₐ(r) · (d̃ₐ(r) + a) = √(X a³/r)`. -/
theorem dtilde_prod {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    dtilde X r a * (dtilde X r a + a) = Real.sqrt (X * a ^ 3 / r) := by
  set w := Real.sqrt (X * a ^ 3 / r) with hw
  have hwnn : 0 ≤ w := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 + 4 * w) ^ 2 = a ^ 2 + 4 * w :=
    Real.sq_sqrt (by positivity)
  unfold dtilde
  -- with `s := √(a²+4w)`, `d = (−a+s)/2`, so `d(d+a) = (s²−a²)/4 = (4w)/4 = w`.
  set s := Real.sqrt (a ^ 2 + 4 * w) with hs
  field_simp
  nlinarith [hsq]

/-- **`d̃ₐ(r)` inverts `R_a`:** `R_a(d̃ₐ(r)) = r`. -/
theorem dtilde_spec {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    Rfun X a (dtilde X r a) = r := by
  have hd : 0 < dtilde X r a := dtilde_pos hX ha hr
  have hda : dtilde X r a + a ≠ 0 := by positivity
  have hprod := dtilde_prod hX ha hr
  have hwsq : Real.sqrt (X * a ^ 3 / r) ^ 2 = X * a ^ 3 / r :=
    Real.sq_sqrt (by positivity)
  rw [Rfun_factor' X a _ (ne_of_gt hd) hda]
  -- `d²(d+a)² = (d(d+a))² = (√(Xa³/r))² = Xa³/r`, so `Xa³/(Xa³/r) = r`.
  have hden : (dtilde X r a) ^ 2 * (dtilde X r a + a) ^ 2 = X * a ^ 3 / r := by
    rw [show (dtilde X r a) ^ 2 * (dtilde X r a + a) ^ 2
          = (dtilde X r a * (dtilde X r a + a)) ^ 2 by ring, hprod, hwsq]
  rw [hden]
  field_simp

/-- **`C²` smoothness of `a ↦ d̃ₐ(r)`** at `a` for `0 < X`, `0 < r`, `0 < a`. -/
theorem dtilde_contDiffAt {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 2 (fun a => dtilde X r a) a := by
  -- inner `√(X·a³/r)` is `C²` at `a` since `X·a³/r > 0 ≠ 0`.
  have hinner : ContDiffAt ℝ 2 (fun a : ℝ => Real.sqrt (X * a ^ 3 / r)) a := by
    refine ContDiffAt.sqrt ?_ (by positivity)
    fun_prop (disch := assumption)
  -- the radicand `a² + 4·inner` is `C²` and positive (so `≠ 0`), so outer `√` is `C²`.
  have hrad : ContDiffAt ℝ 2 (fun a : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) a := by
    fun_prop (disch := assumption)
  have houter : ContDiffAt ℝ 2
      (fun a : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) a := by
    refine ContDiffAt.sqrt hrad ?_
    have : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
    positivity
  -- finally compose with the affine `(−a + ·)/2`.
  have : ContDiffAt ℝ 2
      (fun a : ℝ => (-a + Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) / 2) a := by
    fun_prop (disch := assumption)
  simpa [dtilde] using this

/-! ## Stage 3a: closed form of the §6 phase `f̃ₐ(r) = F_a(d̃ₐ(r))`

Substituting the inverse `d̃ₐ(r)` into `F_a` collapses the rational phase to an affine
expression in `a + 2 d̃ₐ(r)`, which in turn equals a nested square root in `a`.  This sets up
the curvature stage (the `a`-derivatives of `f̃ₐ`). -/

/-- **`a + 2 d̃ₐ(r) = √(a² + 4√(X a³/r))`.**  Immediate from the definition of `d̃ₐ(r)`. -/
theorem dtilde_two_plus {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    a + 2 * dtilde X r a = Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) := by
  unfold dtilde; ring

/-- **Affine collapse of the phase:** `F_a(d̃ₐ(r)) = r · (a + 2 d̃ₐ(r)) / a²`.
Uses `Ffun_factor'` and `d̃ₐ(r)·(d̃ₐ(r)+a) = √(X a³/r)`, so the denominator
`d²(d+a)² = (√(X a³/r))² = X a³/r`. -/
theorem ftil_eq_aff {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    Ffun X a (dtilde X r a) = r * (a + 2 * dtilde X r a) / a ^ 2 := by
  have hd : 0 < dtilde X r a := dtilde_pos hX ha hr
  have hda : dtilde X r a + a ≠ 0 := by positivity
  have hprod := dtilde_prod hX ha hr
  have hwsq : Real.sqrt (X * a ^ 3 / r) ^ 2 = X * a ^ 3 / r :=
    Real.sq_sqrt (by positivity)
  rw [Ffun_factor' X a _ (ne_of_gt hd) hda]
  -- `d²(d+a)² = (d(d+a))² = (√(Xa³/r))² = Xa³/r`.
  have hden : (dtilde X r a) ^ 2 * (dtilde X r a + a) ^ 2 = X * a ^ 3 / r := by
    rw [show (dtilde X r a) ^ 2 * (dtilde X r a + a) ^ 2
          = (dtilde X r a * (dtilde X r a + a)) ^ 2 by ring, hprod, hwsq]
  rw [hden]
  -- `X a (a+2d)/(X a³/r) = r (a+2d)/a²`.
  rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Closed form of the §6 phase** `f̃ₐ(r) = F_a(d̃ₐ(r)) = r·√(a² + 4√(X a³/r))/a²`. -/
theorem ftil_closed {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    Ffun X a (dtilde X r a)
      = r * Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) / a ^ 2 := by
  rw [ftil_eq_aff hX ha hr, dtilde_two_plus hX ha hr]

/-- The §6 phase as a clean handle: `f̃ₐ(r) = r·√(a² + 4√(X a³/r))/a²`
(`= F_a(d̃ₐ(r))` for `0 < X, a, r` by `ftil_closed`). -/
noncomputable def ftil (X r a : ℝ) : ℝ :=
  r * Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) / a ^ 2

/-- `ftil` agrees with the phase `F_a(d̃ₐ(r))` for `0 < X, a, r`. -/
theorem ftil_eq_phase {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ftil X r a = Ffun X a (dtilde X r a) := (ftil_closed hX ha hr).symm

/-- **`C²` smoothness of `a ↦ f̃ₐ(r) = F_a(d̃ₐ(r))`** at `a` for `0 < X`, `0 < r`, `0 < a`.
Rewrite to the closed form on the open set `{a' | 0 < a'}` and reuse the nested-`√` pattern. -/
theorem ftil_contDiffAt {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 2 (fun a => Ffun X a (dtilde X r a)) a := by
  -- The closed form `ftil_closed` holds on the open set `{a' | 0 < a'}` which is a nhd of `a`.
  have heq : (fun a => Ffun X a (dtilde X r a))
      =ᶠ[nhds a] (fun a : ℝ => r * Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) / a ^ 2) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds ha) ?_
    intro a' ha'
    exact ftil_closed hX ha' hr
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  -- The closed form is `C²` at `a > 0` by the same nested-`√` + `a² ≠ 0` reasoning as `dtilde`.
  have hinner : ContDiffAt ℝ 2 (fun a : ℝ => Real.sqrt (X * a ^ 3 / r)) a := by
    refine ContDiffAt.sqrt ?_ (by positivity)
    fun_prop (disch := assumption)
  have hrad : ContDiffAt ℝ 2 (fun a : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) a := by
    fun_prop (disch := assumption)
  have houter : ContDiffAt ℝ 2
      (fun a : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) a := by
    refine ContDiffAt.sqrt hrad ?_
    have : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
    positivity
  exact (contDiffAt_const.mul houter).div (contDiffAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt ha))

end Squarefree
