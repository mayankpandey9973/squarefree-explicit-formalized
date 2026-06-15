import Squarefree.Structure.PhaseDeriv
import Mathlib

/-!
# Higher `d`-derivatives of `F_a`

This leaf extends `Structure/PhaseDeriv.lean` from the first two `d`-derivatives of
`Ffun X a d = X/d² - X/(d+a)²` to the third, fourth, and fifth derivatives.  It also records
closed absolute-value formulas and scale bounds on the wide inverse window used by the
forthcoming inverse-phase module.
-/

open Classical

namespace Squarefree

set_option maxHeartbeats 1000000

/-! ## Third, fourth, and fifth derivatives -/

/-- `HasDerivAt` of `s ↦ 6X/s⁴` at `s ≠ 0`, derivative `-24X/s⁵`. -/
private theorem hasDerivAt_6_inv_four (X s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t => 6 * X / t ^ 4) (-24 * X / s ^ 5) s := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 4) (4 * s ^ 3) s := by
    simpa using (hasDerivAt_pow 4 s)
  have h := (hasDerivAt_const s (6 * X)).div hpow (pow_ne_zero 4 hs)
  convert h using 1
  field_simp
  ring

/-- `HasDerivAt` of `s ↦ -6X/(s+a)⁴` at `s+a ≠ 0`, derivative `24X/(s+a)⁵`. -/
private theorem hasDerivAt_neg6_inv_four_shift (X a s : ℝ) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => -6 * X / (t + a) ^ 4) (24 * X / (s + a) ^ 5) s := by
  have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).add_const a
  have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 4) (4 * (s + a) ^ 3 * 1) s := by
    simpa using (hasDerivAt_pow 4 (s + a)).comp s hshift
  have h := (hasDerivAt_const s (-6 * X)).div hpow (pow_ne_zero 4 hsa)
  convert h using 1
  field_simp
  ring

/-- **Third `d`-derivative of `F_a`** (as the derivative of the second-derivative function).
`(d/dt)(6X/t⁴ - 6X/(t+a)⁴)|_{t=d} = -24X/d⁵ + 24X/(d+a)⁵`. -/
theorem Ffun_hasDerivAt3_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => 6 * X / t ^ 4 - 6 * X / (t + a) ^ 4)
      (-24 * X / d ^ 5 + 24 * X / (d + a) ^ 5) d := by
  have h := (hasDerivAt_6_inv_four X d hd).add
    (hasDerivAt_neg6_inv_four_shift X a d hda)
  have hfun : (fun t => 6 * X / t ^ 4 - 6 * X / (t + a) ^ 4)
      = (fun t => 6 * X / t ^ 4) + (fun t => -6 * X / (t + a) ^ 4) := by
    funext t
    simp only [Pi.add_apply, sub_eq_add_neg]
    ring
  rw [hfun]
  exact h

/-- `HasDerivAt` of `s ↦ -24X/s⁵` at `s ≠ 0`, derivative `120X/s⁶`. -/
private theorem hasDerivAt_neg24_inv_five (X s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t => -24 * X / t ^ 5) (120 * X / s ^ 6) s := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 5) (5 * s ^ 4) s := by
    simpa using (hasDerivAt_pow 5 s)
  have h := (hasDerivAt_const s (-24 * X)).div hpow (pow_ne_zero 5 hs)
  convert h using 1
  field_simp
  ring

/-- `HasDerivAt` of `s ↦ 24X/(s+a)⁵` at `s+a ≠ 0`, derivative `-120X/(s+a)⁶`. -/
private theorem hasDerivAt_24_inv_five_shift (X a s : ℝ) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => 24 * X / (t + a) ^ 5) (-120 * X / (s + a) ^ 6) s := by
  have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).add_const a
  have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 5) (5 * (s + a) ^ 4 * 1) s := by
    simpa using (hasDerivAt_pow 5 (s + a)).comp s hshift
  have h := (hasDerivAt_const s (24 * X)).div hpow (pow_ne_zero 5 hsa)
  convert h using 1
  field_simp
  ring

/-- **Fourth `d`-derivative of `F_a`** (as the derivative of the third-derivative function).
`(d/dt)(-24X/t⁵ + 24X/(t+a)⁵)|_{t=d} = 120X/d⁶ - 120X/(d+a)⁶`. -/
theorem Ffun_hasDerivAt4_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => -24 * X / t ^ 5 + 24 * X / (t + a) ^ 5)
      (120 * X / d ^ 6 - 120 * X / (d + a) ^ 6) d := by
  have h := (hasDerivAt_neg24_inv_five X d hd).add
    (hasDerivAt_24_inv_five_shift X a d hda)
  have hfun : (fun t => -24 * X / t ^ 5 + 24 * X / (t + a) ^ 5)
      = (fun t => -24 * X / t ^ 5) + (fun t => 24 * X / (t + a) ^ 5) := by
    funext t
    simp only [Pi.add_apply]
  rw [hfun]
  convert h using 1
  ring

/-- `HasDerivAt` of `s ↦ 120X/s⁶` at `s ≠ 0`, derivative `-720X/s⁷`. -/
private theorem hasDerivAt_120_inv_six (X s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t => 120 * X / t ^ 6) (-720 * X / s ^ 7) s := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 6) (6 * s ^ 5) s := by
    simpa using (hasDerivAt_pow 6 s)
  have h := (hasDerivAt_const s (120 * X)).div hpow (pow_ne_zero 6 hs)
  convert h using 1
  field_simp
  ring

/-- `HasDerivAt` of `s ↦ -120X/(s+a)⁶` at `s+a ≠ 0`, derivative
`720X/(s+a)⁷`. -/
private theorem hasDerivAt_neg120_inv_six_shift (X a s : ℝ) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => -120 * X / (t + a) ^ 6) (720 * X / (s + a) ^ 7) s := by
  have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).add_const a
  have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 6) (6 * (s + a) ^ 5 * 1) s := by
    simpa using (hasDerivAt_pow 6 (s + a)).comp s hshift
  have h := (hasDerivAt_const s (-120 * X)).div hpow (pow_ne_zero 6 hsa)
  convert h using 1
  field_simp
  ring

/-- **Fifth `d`-derivative of `F_a`** (as the derivative of the fourth-derivative
function).
`(d/dt)(120X/t⁶ - 120X/(t+a)⁶)|_{t=d} = -720X/d⁷ + 720X/(d+a)⁷`. -/
theorem Ffun_hasDerivAt5_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => 120 * X / t ^ 6 - 120 * X / (t + a) ^ 6)
      (-720 * X / d ^ 7 + 720 * X / (d + a) ^ 7) d := by
  have h := (hasDerivAt_120_inv_six X d hd).add
    (hasDerivAt_neg120_inv_six_shift X a d hda)
  have hfun : (fun t => 120 * X / t ^ 6 - 120 * X / (t + a) ^ 6)
      = (fun t => 120 * X / t ^ 6) + (fun t => -120 * X / (t + a) ^ 6) := by
    funext t
    simp only [Pi.add_apply, sub_eq_add_neg]
    ring
  rw [hfun]
  exact h

/-- **Sixth `d`-derivative of `F_a`** (as the derivative of the fifth-derivative
function).
`(d/dt)(-720X/t⁷ + 720X/(t+a)⁷)|_{t=d} = 5040X/d⁸ - 5040X/(d+a)⁸`. -/
theorem Ffun_hasDerivAt6_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (fun t => -720 * X / t ^ 7 + 720 * X / (t + a) ^ 7)
      (5040 * X / d ^ 8 - 5040 * X / (d + a) ^ 8) d := by
  have hleft : HasDerivAt (fun t => -720 * X / t ^ 7) (5040 * X / d ^ 8) d := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 7) (7 * d ^ 6) d := by
      simpa using (hasDerivAt_pow 7 d)
    have h := (hasDerivAt_const d (-720 * X)).div hpow (pow_ne_zero 7 hd)
    convert h using 1
    field_simp
    ring
  have hright : HasDerivAt (fun t => 720 * X / (t + a) ^ 7)
      (-5040 * X / (d + a) ^ 8) d := by
    have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) d := by
      simpa using (hasDerivAt_id d).add_const a
    have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 7)
        (7 * (d + a) ^ 6 * 1) d := by
      simpa using (hasDerivAt_pow 7 (d + a)).comp d hshift
    have h := (hasDerivAt_const d (720 * X)).div hpow (pow_ne_zero 7 hda)
    convert h using 1
    field_simp
    ring
  have h := hleft.add hright
  have hfun : (fun t => -720 * X / t ^ 7 + 720 * X / (t + a) ^ 7)
      = (fun t => -720 * X / t ^ 7) + (fun t => 720 * X / (t + a) ^ 7) := by
    funext t
    simp only [Pi.add_apply]
  rw [hfun]
  convert h using 1
  ring

/-! ## Iterated-derivative identities -/

/-- The second derivative function `iteratedDeriv 2 (fun t => Ffun X a t)` agrees locally
with the explicit second-derivative expression near any pole-free point. -/
private theorem iteratedDeriv2_Ffun_eventuallyEq (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 2 (fun t => Ffun X a t)
      =ᶠ[nhds d] (fun t => 6 * X / t ^ 4 - 6 * X / (t + a) ^ 4) := by
  have hopen : IsOpen {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} :=
    (isOpen_ne.preimage continuous_id).inter (isOpen_ne.preimage (continuous_id.add continuous_const))
  have hmem : d ∈ {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} := ⟨hd, hda⟩
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
  intro t ht
  exact Ffun_iteratedDeriv2_d X a t ht.1 ht.2

/-- **`iteratedDeriv 3` value of `F_a`** on the pole-free set:
`iteratedDeriv 3 (fun t => Ffun X a t) d = -24X/d⁵ + 24X/(d+a)⁵`. -/
theorem Ffun_iteratedDeriv3_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 3 (fun t => Ffun X a t) d =
      -24 * X / d ^ 5 + 24 * X / (d + a) ^ 5 := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ]
  rw [(iteratedDeriv2_Ffun_eventuallyEq X a d hd hda).deriv_eq]
  exact (Ffun_hasDerivAt3_d X a d hd hda).deriv

/-- The third derivative function `iteratedDeriv 3 (fun t => Ffun X a t)` agrees locally
with the explicit third-derivative expression near any pole-free point. -/
private theorem iteratedDeriv3_Ffun_eventuallyEq (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 3 (fun t => Ffun X a t)
      =ᶠ[nhds d] (fun t => -24 * X / t ^ 5 + 24 * X / (t + a) ^ 5) := by
  have hopen : IsOpen {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} :=
    (isOpen_ne.preimage continuous_id).inter (isOpen_ne.preimage (continuous_id.add continuous_const))
  have hmem : d ∈ {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} := ⟨hd, hda⟩
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
  intro t ht
  exact Ffun_iteratedDeriv3_d X a t ht.1 ht.2

/-- **`iteratedDeriv 4` value of `F_a`** on the pole-free set:
`iteratedDeriv 4 (fun t => Ffun X a t) d = 120X/d⁶ - 120X/(d+a)⁶`. -/
theorem Ffun_iteratedDeriv4_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 4 (fun t => Ffun X a t) d =
      120 * X / d ^ 6 - 120 * X / (d + a) ^ 6 := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ]
  rw [(iteratedDeriv3_Ffun_eventuallyEq X a d hd hda).deriv_eq]
  exact (Ffun_hasDerivAt4_d X a d hd hda).deriv

/-- The fourth derivative function `iteratedDeriv 4 (fun t => Ffun X a t)` agrees
locally with the explicit fourth-derivative expression near any pole-free point. -/
private theorem iteratedDeriv4_Ffun_eventuallyEq (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 4 (fun t => Ffun X a t)
      =ᶠ[nhds d] (fun t => 120 * X / t ^ 6 - 120 * X / (t + a) ^ 6) := by
  have hopen : IsOpen {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} :=
    (isOpen_ne.preimage continuous_id).inter (isOpen_ne.preimage (continuous_id.add continuous_const))
  have hmem : d ∈ {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} := ⟨hd, hda⟩
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
  intro t ht
  exact Ffun_iteratedDeriv4_d X a t ht.1 ht.2

/-- **`iteratedDeriv 5` value of `F_a`** on the pole-free set:
`iteratedDeriv 5 (fun t => Ffun X a t) d = -720X/d⁷ + 720X/(d+a)⁷`. -/
theorem Ffun_iteratedDeriv5_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 5 (fun t => Ffun X a t) d =
      -720 * X / d ^ 7 + 720 * X / (d + a) ^ 7 := by
  rw [show (5 : ℕ) = 4 + 1 by rfl, iteratedDeriv_succ]
  rw [(iteratedDeriv4_Ffun_eventuallyEq X a d hd hda).deriv_eq]
  exact (Ffun_hasDerivAt5_d X a d hd hda).deriv

/-- **`iteratedDeriv 6` value of `F_a`** on the pole-free set:
`iteratedDeriv 6 (fun t => Ffun X a t) d = 5040X/d⁸ - 5040X/(d+a)⁸`. -/
theorem Ffun_iteratedDeriv6_d (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    iteratedDeriv 6 (fun t => Ffun X a t) d =
      5040 * X / d ^ 8 - 5040 * X / (d + a) ^ 8 := by
  have hev : iteratedDeriv 5 (fun t => Ffun X a t)
      =ᶠ[nhds d] (fun t => -720 * X / t ^ 7 + 720 * X / (t + a) ^ 7) := by
    have hopen : IsOpen {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} :=
      (isOpen_ne.preimage continuous_id).inter (isOpen_ne.preimage (continuous_id.add continuous_const))
    have hmem : d ∈ {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} := ⟨hd, hda⟩
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
    intro t ht
    exact Ffun_iteratedDeriv5_d X a t ht.1 ht.2
  rw [show (6 : ℕ) = 5 + 1 by rfl, iteratedDeriv_succ]
  rw [hev.deriv_eq]
  exact (Ffun_hasDerivAt6_d X a d hd hda).deriv

/-! ## Smoothness away from poles -/

/-- `Ffun X a` is `C⁴` (indeed `C^∞`) at any pole-free point. -/
theorem Ffun_contDiffAt4 {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ 4 (fun t => Ffun X a t) d := by
  have h1 : ContDiffAt ℝ 4 (fun t : ℝ => X / t ^ 2) d :=
    (contDiffAt_const).div (contDiffAt_id.pow 2) (pow_ne_zero 2 hd)
  have h2 : ContDiffAt ℝ 4 (fun t : ℝ => X / (t + a) ^ 2) d :=
    (contDiffAt_const).div ((contDiffAt_id.add contDiffAt_const).pow 2) (pow_ne_zero 2 hda)
  have h := h1.sub h2
  have hfun : (fun t => Ffun X a t) = (fun t : ℝ => X / t ^ 2) - (fun t : ℝ => X / (t + a) ^ 2) := by
    funext t
    simp [Ffun, Pi.sub_apply]
  rw [hfun]
  exact h

/-- `Ffun X a` is `C⁵` (indeed `C^∞`) at any pole-free point. -/
theorem Ffun_contDiffAt5 {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ 5 (fun t => Ffun X a t) d := by
  have h1 : ContDiffAt ℝ 5 (fun t : ℝ => X / t ^ 2) d :=
    (contDiffAt_const).div (contDiffAt_id.pow 2) (pow_ne_zero 2 hd)
  have h2 : ContDiffAt ℝ 5 (fun t : ℝ => X / (t + a) ^ 2) d :=
    (contDiffAt_const).div ((contDiffAt_id.add contDiffAt_const).pow 2) (pow_ne_zero 2 hda)
  have h := h1.sub h2
  have hfun : (fun t => Ffun X a t) = (fun t : ℝ => X / t ^ 2) - (fun t : ℝ => X / (t + a) ^ 2) := by
    funext t
    simp [Ffun, Pi.sub_apply]
  rw [hfun]
  exact h

/-! ## Closed factored forms and exact magnitudes -/

/-- Factored first `d`-derivative:
`F_a'(d) = -2X a(a²+3ad+3d²)/(d³(d+a)³)`. -/
theorem Ffun_deriv1_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    -2 * X / d ^ 3 + 2 * X / (d + a) ^ 3 =
      -2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) / (d ^ 3 * (d + a) ^ 3) := by
  field_simp
  ring

/-- Factored second `d`-derivative:
`F_a''(d) = 6X a(a+2d)(a²+2ad+2d²)/(d⁴(d+a)⁴)`. -/
theorem Ffun_deriv2_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    6 * X / d ^ 4 - 6 * X / (d + a) ^ 4 =
      6 * X * a * (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
        (d ^ 4 * (d + a) ^ 4) := by
  field_simp
  ring

/-- Factored third `d`-derivative:
`F_a⁽³⁾(d) = -24X a(a⁴+5a³d+10a²d²+10ad³+5d⁴)/(d⁵(d+a)⁵)`. -/
theorem Ffun_deriv3_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    -24 * X / d ^ 5 + 24 * X / (d + a) ^ 5 =
      -24 * X * a *
        (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 + 5 * d ^ 4) /
          (d ^ 5 * (d + a) ^ 5) := by
  field_simp
  ring

/-- Factored fourth `d`-derivative:
`F_a⁽⁴⁾(d) = 120X a(a+2d)(a²+ad+d²)(a²+3ad+3d²)/(d⁶(d+a)⁶)`. -/
theorem Ffun_deriv4_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    120 * X / d ^ 6 - 120 * X / (d + a) ^ 6 =
      120 * X * a * (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) *
        (a ^ 2 + 3 * a * d + 3 * d ^ 2) / (d ^ 6 * (d + a) ^ 6) := by
  field_simp
  ring

/-- Factored fifth `d`-derivative:
`F_a⁽⁵⁾(d) = -720X a(a⁶+7a⁵d+21a⁴d²+35a³d³+35a²d⁴+21ad⁵+7d⁶)/(d⁷(d+a)⁷)`. -/
theorem Ffun_deriv5_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    -720 * X / d ^ 7 + 720 * X / (d + a) ^ 7 =
      -720 * X * a *
        (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
          + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6) /
          (d ^ 7 * (d + a) ^ 7) := by
  field_simp
  ring

/-- Factored sixth `d`-derivative:
`F_a⁽⁶⁾(d) = 5040X a(a⁷+8a⁶d+28a⁵d²+56a⁴d³+70a³d⁴+56a²d⁵+28ad⁶+8d⁷)/(d⁸(d+a)⁸)`. -/
theorem Ffun_deriv6_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    5040 * X / d ^ 8 - 5040 * X / (d + a) ^ 8 =
      5040 * X * a *
        (a ^ 7 + 8 * a ^ 6 * d + 28 * a ^ 5 * d ^ 2 + 56 * a ^ 4 * d ^ 3
          + 70 * a ^ 3 * d ^ 4 + 56 * a ^ 2 * d ^ 5 + 28 * a * d ^ 6
          + 8 * d ^ 7) / (d ^ 8 * (d + a) ^ 8) := by
  field_simp
  ring

/-- Exact magnitude of `F_a'(d)` at positive inputs. -/
theorem Ffun_deriv1_abs_eq {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |deriv (fun t => Ffun X a t) d| =
      2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) / (d ^ 3 * (d + a) ^ 3) := by
  have hda : d + a ≠ 0 := by positivity
  rw [Ffun_deriv_d X a d (ne_of_gt hd) hda, Ffun_deriv1_factor X a d (ne_of_gt hd) hda]
  rw [show -2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) / (d ^ 3 * (d + a) ^ 3)
      = -(2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) / (d ^ 3 * (d + a) ^ 3)) by ring]
  rw [abs_neg, abs_of_nonneg]
  positivity

/-- Exact magnitude of `F_a''(d)` at positive inputs. -/
theorem Ffun_deriv2_abs_eq {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |iteratedDeriv 2 (fun t => Ffun X a t) d| =
      6 * X * a * (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2) /
        (d ^ 4 * (d + a) ^ 4) := by
  have hda : d + a ≠ 0 := by positivity
  rw [Ffun_iteratedDeriv2_d X a d (ne_of_gt hd) hda,
    Ffun_deriv2_factor X a d (ne_of_gt hd) hda]
  rw [abs_of_nonneg]
  positivity

/-- Exact magnitude of `F_a⁽³⁾(d)` at positive inputs. -/
theorem Ffun_deriv3_abs_eq {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |iteratedDeriv 3 (fun t => Ffun X a t) d| =
      24 * X * a *
        (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 + 5 * d ^ 4) /
          (d ^ 5 * (d + a) ^ 5) := by
  have hda : d + a ≠ 0 := by positivity
  rw [Ffun_iteratedDeriv3_d X a d (ne_of_gt hd) hda,
    Ffun_deriv3_factor X a d (ne_of_gt hd) hda]
  rw [show -24 * X * a *
        (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 + 5 * d ^ 4) /
          (d ^ 5 * (d + a) ^ 5)
      = -(24 * X * a *
        (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 + 5 * d ^ 4) /
          (d ^ 5 * (d + a) ^ 5)) by ring]
  rw [abs_neg, abs_of_nonneg]
  positivity

/-- Exact magnitude of `F_a⁽⁴⁾(d)` at positive inputs. -/
theorem Ffun_deriv4_abs_eq {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |iteratedDeriv 4 (fun t => Ffun X a t) d| =
      120 * X * a * (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) *
        (a ^ 2 + 3 * a * d + 3 * d ^ 2) / (d ^ 6 * (d + a) ^ 6) := by
  have hda : d + a ≠ 0 := by positivity
  rw [Ffun_iteratedDeriv4_d X a d (ne_of_gt hd) hda,
    Ffun_deriv4_factor X a d (ne_of_gt hd) hda]
  rw [abs_of_nonneg]
  positivity

/-- Exact magnitude of `F_a⁽⁵⁾(d)` at positive inputs. -/
theorem Ffun_deriv5_abs_eq {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |iteratedDeriv 5 (fun t => Ffun X a t) d| =
      720 * X * a *
        (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
          + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6) /
          (d ^ 7 * (d + a) ^ 7) := by
  have hda : d + a ≠ 0 := by positivity
  rw [Ffun_iteratedDeriv5_d X a d (ne_of_gt hd) hda,
    Ffun_deriv5_factor X a d (ne_of_gt hd) hda]
  rw [show -720 * X * a *
        (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
          + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6) /
          (d ^ 7 * (d + a) ^ 7)
      = -(720 * X * a *
        (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
          + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6) /
          (d ^ 7 * (d + a) ^ 7)) by ring]
  rw [abs_neg, abs_of_nonneg]
  positivity

/-- Exact magnitude of `F_a⁽⁶⁾(d)` at positive inputs. -/
theorem Ffun_deriv6_abs_eq {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |iteratedDeriv 6 (fun t => Ffun X a t) d| =
      5040 * X * a *
        (a ^ 7 + 8 * a ^ 6 * d + 28 * a ^ 5 * d ^ 2 + 56 * a ^ 4 * d ^ 3
          + 70 * a ^ 3 * d ^ 4 + 56 * a ^ 2 * d ^ 5 + 28 * a * d ^ 6
          + 8 * d ^ 7) / (d ^ 8 * (d + a) ^ 8) := by
  have hda : d + a ≠ 0 := by positivity
  rw [Ffun_iteratedDeriv6_d X a d (ne_of_gt hd) hda,
    Ffun_deriv6_factor X a d (ne_of_gt hd) hda]
  rw [abs_of_nonneg]
  positivity

/-! ## Local magnitude bounds in the natural `X*a/d^(k+3)` scale -/

/-- Local two-sided first-derivative bound for `0 < a ≤ 11d`:
`|F_a'(d)| ≍ X a/d⁴`. -/
theorem Ffun_deriv1_abs_bounds {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (had : a ≤ 11 * d) :
    X * a / (288 * d ^ 4) ≤ |deriv (fun t => Ffun X a t) d| ∧
      |deriv (fun t => Ffun X a t) d| ≤ 314 * X * a / d ^ 4 := by
  rw [Ffun_deriv1_abs_eq hX ha hd]
  have hda_pos : 0 < d + a := by positivity
  have hden_pos : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
  have hPlo : 3 * d ^ 2 ≤ a ^ 2 + 3 * a * d + 3 * d ^ 2 := by
    nlinarith [sq_nonneg a, mul_pos ha hd]
  have hPhi : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≤ 157 * d ^ 2 := by
    nlinarith [had, ha, hd, sq_nonneg (a - 11 * d)]
  have hden_lo : d ^ 6 ≤ d ^ 3 * (d + a) ^ 3 := by
    have hpow : d ^ 3 ≤ (d + a) ^ 3 := pow_le_pow_left₀ hd.le (by linarith) 3
    nlinarith [hpow, pow_pos hd 3]
  have hden_hi : d ^ 3 * (d + a) ^ 3 ≤ 1728 * d ^ 6 := by
    have hda_le : d + a ≤ 12 * d := by linarith
    have hpow : (d + a) ^ 3 ≤ (12 * d) ^ 3 := pow_le_pow_left₀ hda_pos.le hda_le 3
    nlinarith [hpow, pow_pos hd 3]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 288 * d ^ 4) hden_pos]
    have h1 : X * a * (d ^ 3 * (d + a) ^ 3) ≤ X * a * (1728 * d ^ 6) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    have h2 : X * a * (1728 * d ^ 6) ≤
        2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) * (288 * d ^ 4) := by
      have hmul : (2 * X * a * (288 * d ^ 4)) * (3 * d ^ 2) ≤
          (2 * X * a * (288 * d ^ 4)) *
            (a ^ 2 + 3 * a * d + 3 * d ^ 2) :=
        mul_le_mul_of_nonneg_left hPlo (by positivity)
      nlinarith [hmul]
    linarith
  · rw [div_le_div_iff₀ hden_pos (by positivity : 0 < d ^ 4)]
    have h1 : 2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) * d ^ 4 ≤
        2 * X * a * (157 * d ^ 2) * d ^ 4 := by
      have hmul : (2 * X * a * d ^ 4) * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ≤
          (2 * X * a * d ^ 4) * (157 * d ^ 2) :=
        mul_le_mul_of_nonneg_left hPhi (by positivity)
      nlinarith [hmul]
    have h2 : 2 * X * a * (157 * d ^ 2) * d ^ 4 ≤
        314 * X * a * (d ^ 3 * (d + a) ^ 3) := by
      have hmul : (314 * X * a) * d ^ 6 ≤
          (314 * X * a) * (d ^ 3 * (d + a) ^ 3) :=
        mul_le_mul_of_nonneg_left hden_lo (by positivity)
      nlinarith [hmul]
    linarith

/-- Local two-sided second-derivative bound for `0 < a ≤ 11d`:
`|F_a''(d)| ≍ X a/d⁵`. -/
theorem Ffun_deriv2_abs_bounds {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (had : a ≤ 11 * d) :
    X * a / (864 * d ^ 5) ≤ |iteratedDeriv 2 (fun t => Ffun X a t) d| ∧
      |iteratedDeriv 2 (fun t => Ffun X a t) d| ≤ 11310 * X * a / d ^ 5 := by
  rw [Ffun_deriv2_abs_eq hX ha hd]
  have hda_pos : 0 < d + a := by positivity
  have hden_pos : 0 < d ^ 4 * (d + a) ^ 4 := by positivity
  set Q : ℝ := (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2)
  have hQlo : 4 * d ^ 3 ≤ Q := by
    have h1 : 2 * d ≤ a + 2 * d := by linarith
    have h2 : 2 * d ^ 2 ≤ a ^ 2 + 2 * a * d + 2 * d ^ 2 := by
      nlinarith [sq_nonneg a, mul_pos ha hd]
    have hmul : (2 * d) * (2 * d ^ 2) ≤
        (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith [hmul]
  have hQhi : Q ≤ 1885 * d ^ 3 := by
    have h1 : a + 2 * d ≤ 13 * d := by linarith
    have h2 : a ^ 2 + 2 * a * d + 2 * d ^ 2 ≤ 145 * d ^ 2 := by
      nlinarith [had, ha, hd, sq_nonneg (a - 11 * d)]
    have hmul : (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2) ≤
        (13 * d) * (145 * d ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith [hmul]
  have hden_lo : d ^ 8 ≤ d ^ 4 * (d + a) ^ 4 := by
    have hpow : d ^ 4 ≤ (d + a) ^ 4 := pow_le_pow_left₀ hd.le (by linarith) 4
    nlinarith [hpow, pow_pos hd 4]
  have hden_hi : d ^ 4 * (d + a) ^ 4 ≤ 20736 * d ^ 8 := by
    have hda_le : d + a ≤ 12 * d := by linarith
    have hpow : (d + a) ^ 4 ≤ (12 * d) ^ 4 := pow_le_pow_left₀ hda_pos.le hda_le 4
    nlinarith [hpow, pow_pos hd 4]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 864 * d ^ 5) hden_pos]
    have h1 : X * a * (d ^ 4 * (d + a) ^ 4) ≤ X * a * (20736 * d ^ 8) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    have h2 : X * a * (20736 * d ^ 8) ≤
        6 * X * a * Q * (864 * d ^ 5) := by
      have hmul : (6 * X * a * (864 * d ^ 5)) * (4 * d ^ 3) ≤
          (6 * X * a * (864 * d ^ 5)) * Q :=
        mul_le_mul_of_nonneg_left hQlo (by positivity)
      nlinarith [hmul]
    linarith
  · rw [div_le_div_iff₀ hden_pos (by positivity : 0 < d ^ 5)]
    have h1 : 6 * X * a * Q * d ^ 5 ≤ 6 * X * a * (1885 * d ^ 3) * d ^ 5 := by
      have hmul : (6 * X * a * d ^ 5) * Q ≤
          (6 * X * a * d ^ 5) * (1885 * d ^ 3) :=
        mul_le_mul_of_nonneg_left hQhi (by positivity)
      nlinarith [hmul]
    have h2 : 6 * X * a * (1885 * d ^ 3) * d ^ 5 ≤
        11310 * X * a * (d ^ 4 * (d + a) ^ 4) := by
      have hmul : (11310 * X * a) * d ^ 8 ≤
          (11310 * X * a) * (d ^ 4 * (d + a) ^ 4) :=
        mul_le_mul_of_nonneg_left hden_lo (by positivity)
      nlinarith [hmul]
    linarith

/-- Local two-sided third-derivative bound for `0 < a ≤ 11d`:
`|F_a⁽³⁾(d)| ≍ X a/d⁶`. -/
theorem Ffun_deriv3_abs_bounds {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (had : a ≤ 11 * d) :
    X * a / (2500 * d ^ 6) ≤ |iteratedDeriv 3 (fun t => Ffun X a t) d| ∧
      |iteratedDeriv 3 (fun t => Ffun X a t) d| ≤ 542904 * X * a / d ^ 6 := by
  rw [Ffun_deriv3_abs_eq hX ha hd]
  have hda_pos : 0 < d + a := by positivity
  have hden_pos : 0 < d ^ 5 * (d + a) ^ 5 := by positivity
  set Q : ℝ := a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 + 5 * d ^ 4
  have hQlo : 5 * d ^ 4 ≤ Q := by
    have h1 : 0 ≤ a ^ 4 := by positivity
    have h2 : 0 ≤ 5 * a ^ 3 * d := by positivity
    have h3 : 0 ≤ 10 * a ^ 2 * d ^ 2 := by positivity
    have h4 : 0 ≤ 10 * a * d ^ 3 := by positivity
    nlinarith
  have hQhi : Q ≤ 22621 * d ^ 4 := by
    have ha4 : a ^ 4 ≤ (11 * d) ^ 4 := pow_le_pow_left₀ ha.le had 4
    have ha3 : a ^ 3 ≤ (11 * d) ^ 3 := pow_le_pow_left₀ ha.le had 3
    have ha3d : a ^ 3 * d ≤ (11 * d) ^ 3 * d :=
      mul_le_mul_of_nonneg_right ha3 hd.le
    have ha2 : a ^ 2 ≤ (11 * d) ^ 2 := pow_le_pow_left₀ ha.le had 2
    have ha2d2 : a ^ 2 * d ^ 2 ≤ (11 * d) ^ 2 * d ^ 2 :=
      mul_le_mul_of_nonneg_right ha2 (by positivity)
    have had3 : a * d ^ 3 ≤ (11 * d) * d ^ 3 :=
      mul_le_mul_of_nonneg_right had (by positivity)
    nlinarith [ha4, ha3d, ha2d2, had3]
  have hden_lo : d ^ 10 ≤ d ^ 5 * (d + a) ^ 5 := by
    have hpow : d ^ 5 ≤ (d + a) ^ 5 := pow_le_pow_left₀ hd.le (by linarith) 5
    nlinarith [hpow, pow_pos hd 5]
  have hden_hi : d ^ 5 * (d + a) ^ 5 ≤ 248832 * d ^ 10 := by
    have hda_le : d + a ≤ 12 * d := by linarith
    have hpow : (d + a) ^ 5 ≤ (12 * d) ^ 5 := pow_le_pow_left₀ hda_pos.le hda_le 5
    nlinarith [hpow, pow_pos hd 5]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 2500 * d ^ 6) hden_pos]
    have h1 : X * a * (d ^ 5 * (d + a) ^ 5) ≤ X * a * (248832 * d ^ 10) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    have h2 : X * a * (248832 * d ^ 10) ≤ 24 * X * a * Q * (2500 * d ^ 6) := by
      have hmul : (24 * X * a * (2500 * d ^ 6)) * (5 * d ^ 4) ≤
          (24 * X * a * (2500 * d ^ 6)) * Q :=
        mul_le_mul_of_nonneg_left hQlo (by positivity)
      nlinarith [hmul]
    linarith
  · rw [div_le_div_iff₀ hden_pos (by positivity : 0 < d ^ 6)]
    have h1 : 24 * X * a * Q * d ^ 6 ≤ 24 * X * a * (22621 * d ^ 4) * d ^ 6 := by
      have hmul : (24 * X * a * d ^ 6) * Q ≤
          (24 * X * a * d ^ 6) * (22621 * d ^ 4) :=
        mul_le_mul_of_nonneg_left hQhi (by positivity)
      nlinarith [hmul]
    have h2 : 24 * X * a * (22621 * d ^ 4) * d ^ 6 ≤
        542904 * X * a * (d ^ 5 * (d + a) ^ 5) := by
      have hmul : (542904 * X * a) * d ^ 10 ≤
          (542904 * X * a) * (d ^ 5 * (d + a) ^ 5) :=
        mul_le_mul_of_nonneg_left hden_lo (by positivity)
      nlinarith [hmul]
    linarith

/-- Local two-sided fourth-derivative bound for `0 < a ≤ 11d`:
`|F_a⁽⁴⁾(d)| ≍ X a/d⁷`. -/
theorem Ffun_deriv4_abs_bounds {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (had : a ≤ 11 * d) :
    X * a / (5000 * d ^ 7) ≤ |iteratedDeriv 4 (fun t => Ffun X a t) d| ∧
      |iteratedDeriv 4 (fun t => Ffun X a t) d| ≤ 32574360 * X * a / d ^ 7 := by
  rw [Ffun_deriv4_abs_eq hX ha hd]
  have hda_pos : 0 < d + a := by positivity
  have hden_pos : 0 < d ^ 6 * (d + a) ^ 6 := by positivity
  set Q : ℝ := (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) * (a ^ 2 + 3 * a * d + 3 * d ^ 2)
  have hQlo : 6 * d ^ 5 ≤ Q := by
    have h1 : 2 * d ≤ a + 2 * d := by linarith
    have h2 : d ^ 2 ≤ a ^ 2 + a * d + d ^ 2 := by nlinarith [sq_nonneg a, mul_pos ha hd]
    have h3 : 3 * d ^ 2 ≤ a ^ 2 + 3 * a * d + 3 * d ^ 2 := by
      nlinarith [sq_nonneg a, mul_pos ha hd]
    have h12 : (2 * d) * d ^ 2 ≤ (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h123 : ((2 * d) * d ^ 2) * (3 * d ^ 2) ≤
        ((a + 2 * d) * (a ^ 2 + a * d + d ^ 2)) *
          (a ^ 2 + 3 * a * d + 3 * d ^ 2) :=
      mul_le_mul h12 h3 (by positivity) (by positivity)
    nlinarith [h123]
  have hQhi : Q ≤ 271453 * d ^ 5 := by
    have h1 : a + 2 * d ≤ 13 * d := by linarith
    have h2 : a ^ 2 + a * d + d ^ 2 ≤ 133 * d ^ 2 := by
      nlinarith [had, ha, hd, sq_nonneg (a - 11 * d)]
    have h3 : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≤ 157 * d ^ 2 := by
      nlinarith [had, ha, hd, sq_nonneg (a - 11 * d)]
    have h12 : (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) ≤ (13 * d) * (133 * d ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h123 : ((a + 2 * d) * (a ^ 2 + a * d + d ^ 2)) *
          (a ^ 2 + 3 * a * d + 3 * d ^ 2) ≤
        ((13 * d) * (133 * d ^ 2)) * (157 * d ^ 2) :=
      mul_le_mul h12 h3 (by positivity) (by positivity)
    nlinarith [h123]
  have hden_lo : d ^ 12 ≤ d ^ 6 * (d + a) ^ 6 := by
    have hpow : d ^ 6 ≤ (d + a) ^ 6 := pow_le_pow_left₀ hd.le (by linarith) 6
    nlinarith [hpow, pow_pos hd 6]
  have hden_hi : d ^ 6 * (d + a) ^ 6 ≤ 2985984 * d ^ 12 := by
    have hda_le : d + a ≤ 12 * d := by linarith
    have hpow : (d + a) ^ 6 ≤ (12 * d) ^ 6 := pow_le_pow_left₀ hda_pos.le hda_le 6
    nlinarith [hpow, pow_pos hd 6]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 5000 * d ^ 7) hden_pos]
    have h1 : X * a * (d ^ 6 * (d + a) ^ 6) ≤ X * a * (2985984 * d ^ 12) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    have h2 : X * a * (2985984 * d ^ 12) ≤ 120 * X * a * Q * (5000 * d ^ 7) := by
      have hmul : (120 * X * a * (5000 * d ^ 7)) * (6 * d ^ 5) ≤
          (120 * X * a * (5000 * d ^ 7)) * Q :=
        mul_le_mul_of_nonneg_left hQlo (by positivity)
      nlinarith [hmul]
    linarith
  · rw [div_le_div_iff₀ hden_pos (by positivity : 0 < d ^ 7)]
    have h1 : 120 * X * a * Q * d ^ 7 ≤ 120 * X * a * (271453 * d ^ 5) * d ^ 7 := by
      have hmul : (120 * X * a * d ^ 7) * Q ≤
          (120 * X * a * d ^ 7) * (271453 * d ^ 5) :=
        mul_le_mul_of_nonneg_left hQhi (by positivity)
      nlinarith [hmul]
    have h2 : 120 * X * a * (271453 * d ^ 5) * d ^ 7 ≤
        32574360 * X * a * (d ^ 6 * (d + a) ^ 6) := by
      have hmul : (32574360 * X * a) * d ^ 12 ≤
          (32574360 * X * a) * (d ^ 6 * (d + a) ^ 6) :=
        mul_le_mul_of_nonneg_left hden_lo (by positivity)
      nlinarith [hmul]
    linarith

/-- Local two-sided fifth-derivative bound for `0 < a ≤ 11d`:
`|F_a⁽⁵⁾(d)| ≍ X a/d⁸`. -/
theorem Ffun_deriv5_abs_bounds {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (had : a ≤ 11 * d) :
    X * a / (10000 * d ^ 8) ≤ |iteratedDeriv 5 (fun t => Ffun X a t) d| ∧
      |iteratedDeriv 5 (fun t => Ffun X a t) d| ≤ 2345354640 * X * a / d ^ 8 := by
  rw [Ffun_deriv5_abs_eq hX ha hd]
  have hda_pos : 0 < d + a := by positivity
  have hden_pos : 0 < d ^ 7 * (d + a) ^ 7 := by positivity
  set Q : ℝ := a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
          + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6
  have hQlo : 7 * d ^ 6 ≤ Q := by
    have h1 : 0 ≤ a ^ 6 := by positivity
    have h2 : 0 ≤ 7 * a ^ 5 * d := by positivity
    have h3 : 0 ≤ 21 * a ^ 4 * d ^ 2 := by positivity
    have h4 : 0 ≤ 35 * a ^ 3 * d ^ 3 := by positivity
    have h5 : 0 ≤ 35 * a ^ 2 * d ^ 4 := by positivity
    have h6 : 0 ≤ 21 * a * d ^ 5 := by positivity
    nlinarith
  have hQhi : Q ≤ 3257437 * d ^ 6 := by
    have ha6 : a ^ 6 ≤ (11 * d) ^ 6 := pow_le_pow_left₀ ha.le had 6
    have ha5 : a ^ 5 ≤ (11 * d) ^ 5 := pow_le_pow_left₀ ha.le had 5
    have ha5d : a ^ 5 * d ≤ (11 * d) ^ 5 * d :=
      mul_le_mul_of_nonneg_right ha5 hd.le
    have ha4 : a ^ 4 ≤ (11 * d) ^ 4 := pow_le_pow_left₀ ha.le had 4
    have ha4d2 : a ^ 4 * d ^ 2 ≤ (11 * d) ^ 4 * d ^ 2 :=
      mul_le_mul_of_nonneg_right ha4 (by positivity)
    have ha3 : a ^ 3 ≤ (11 * d) ^ 3 := pow_le_pow_left₀ ha.le had 3
    have ha3d3 : a ^ 3 * d ^ 3 ≤ (11 * d) ^ 3 * d ^ 3 :=
      mul_le_mul_of_nonneg_right ha3 (by positivity)
    have ha2 : a ^ 2 ≤ (11 * d) ^ 2 := pow_le_pow_left₀ ha.le had 2
    have ha2d4 : a ^ 2 * d ^ 4 ≤ (11 * d) ^ 2 * d ^ 4 :=
      mul_le_mul_of_nonneg_right ha2 (by positivity)
    have had5 : a * d ^ 5 ≤ (11 * d) * d ^ 5 :=
      mul_le_mul_of_nonneg_right had (by positivity)
    nlinarith [ha6, ha5d, ha4d2, ha3d3, ha2d4, had5]
  have hden_lo : d ^ 14 ≤ d ^ 7 * (d + a) ^ 7 := by
    have hpow : d ^ 7 ≤ (d + a) ^ 7 := pow_le_pow_left₀ hd.le (by linarith) 7
    nlinarith [hpow, pow_pos hd 7]
  have hden_hi : d ^ 7 * (d + a) ^ 7 ≤ 35831808 * d ^ 14 := by
    have hda_le : d + a ≤ 12 * d := by linarith
    have hpow : (d + a) ^ 7 ≤ (12 * d) ^ 7 := pow_le_pow_left₀ hda_pos.le hda_le 7
    nlinarith [hpow, pow_pos hd 7]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 10000 * d ^ 8) hden_pos]
    have h1 : X * a * (d ^ 7 * (d + a) ^ 7) ≤ X * a * (35831808 * d ^ 14) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    have h2 : X * a * (35831808 * d ^ 14) ≤ 720 * X * a * Q * (10000 * d ^ 8) := by
      have hmul : (720 * X * a * (10000 * d ^ 8)) * (7 * d ^ 6) ≤
          (720 * X * a * (10000 * d ^ 8)) * Q :=
        mul_le_mul_of_nonneg_left hQlo (by positivity)
      nlinarith [hmul]
    linarith
  · rw [div_le_div_iff₀ hden_pos (by positivity : 0 < d ^ 8)]
    have h1 : 720 * X * a * Q * d ^ 8 ≤ 720 * X * a * (3257437 * d ^ 6) * d ^ 8 := by
      have hmul : (720 * X * a * d ^ 8) * Q ≤
          (720 * X * a * d ^ 8) * (3257437 * d ^ 6) :=
        mul_le_mul_of_nonneg_left hQhi (by positivity)
      nlinarith [hmul]
    have h2 : 720 * X * a * (3257437 * d ^ 6) * d ^ 8 ≤
        2345354640 * X * a * (d ^ 7 * (d + a) ^ 7) := by
      have hmul : (2345354640 * X * a) * d ^ 14 ≤
          (2345354640 * X * a) * (d ^ 7 * (d + a) ^ 7) :=
        mul_le_mul_of_nonneg_left hden_lo (by positivity)
      nlinarith [hmul]
    linarith

/-- Local two-sided sixth-derivative bound for `0 < a ≤ 11d`:
`|F_a⁽⁶⁾(d)| ≍ X a/d⁹`. -/
theorem Ffun_deriv6_abs_bounds {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (had : a ≤ 11 * d) :
    X * a / (20000 * d ^ 9) ≤ |iteratedDeriv 6 (fun t => Ffun X a t) d| ∧
      |iteratedDeriv 6 (fun t => Ffun X a t) d| ≤ 197009794800 * X * a / d ^ 9 := by
  rw [Ffun_deriv6_abs_eq hX ha hd]
  have hda_pos : 0 < d + a := by positivity
  have hden_pos : 0 < d ^ 8 * (d + a) ^ 8 := by positivity
  set Q : ℝ := a ^ 7 + 8 * a ^ 6 * d + 28 * a ^ 5 * d ^ 2
    + 56 * a ^ 4 * d ^ 3 + 70 * a ^ 3 * d ^ 4 + 56 * a ^ 2 * d ^ 5
    + 28 * a * d ^ 6 + 8 * d ^ 7 with hQ_def
  have hQlo : 8 * d ^ 7 ≤ Q := by
    have h1 : 0 ≤ a ^ 7 := by positivity
    have h2 : 0 ≤ 8 * a ^ 6 * d := by positivity
    have h3 : 0 ≤ 28 * a ^ 5 * d ^ 2 := by positivity
    have h4 : 0 ≤ 56 * a ^ 4 * d ^ 3 := by positivity
    have h5 : 0 ≤ 70 * a ^ 3 * d ^ 4 := by positivity
    have h6 : 0 ≤ 56 * a ^ 2 * d ^ 5 := by positivity
    have h7 : 0 ≤ 28 * a * d ^ 6 := by positivity
    rw [hQ_def]
    nlinarith
  have hQhi : Q ≤ 39089245 * d ^ 7 := by
    have ha7 : a ^ 7 ≤ (11 * d) ^ 7 := pow_le_pow_left₀ ha.le had 7
    have ha6 : a ^ 6 ≤ (11 * d) ^ 6 := pow_le_pow_left₀ ha.le had 6
    have ha6d : a ^ 6 * d ≤ (11 * d) ^ 6 * d :=
      mul_le_mul_of_nonneg_right ha6 hd.le
    have ha5 : a ^ 5 ≤ (11 * d) ^ 5 := pow_le_pow_left₀ ha.le had 5
    have ha5d2 : a ^ 5 * d ^ 2 ≤ (11 * d) ^ 5 * d ^ 2 :=
      mul_le_mul_of_nonneg_right ha5 (by positivity)
    have ha4 : a ^ 4 ≤ (11 * d) ^ 4 := pow_le_pow_left₀ ha.le had 4
    have ha4d3 : a ^ 4 * d ^ 3 ≤ (11 * d) ^ 4 * d ^ 3 :=
      mul_le_mul_of_nonneg_right ha4 (by positivity)
    have ha3 : a ^ 3 ≤ (11 * d) ^ 3 := pow_le_pow_left₀ ha.le had 3
    have ha3d4 : a ^ 3 * d ^ 4 ≤ (11 * d) ^ 3 * d ^ 4 :=
      mul_le_mul_of_nonneg_right ha3 (by positivity)
    have ha2 : a ^ 2 ≤ (11 * d) ^ 2 := pow_le_pow_left₀ ha.le had 2
    have ha2d5 : a ^ 2 * d ^ 5 ≤ (11 * d) ^ 2 * d ^ 5 :=
      mul_le_mul_of_nonneg_right ha2 (by positivity)
    have had6 : a * d ^ 6 ≤ (11 * d) * d ^ 6 :=
      mul_le_mul_of_nonneg_right had (by positivity)
    rw [hQ_def]
    nlinarith [ha7, ha6d, ha5d2, ha4d3, ha3d4, ha2d5, had6]
  have hden_lo : d ^ 16 ≤ d ^ 8 * (d + a) ^ 8 := by
    have hpow : d ^ 8 ≤ (d + a) ^ 8 := pow_le_pow_left₀ hd.le (by linarith) 8
    nlinarith [hpow, pow_pos hd 8]
  have hden_hi : d ^ 8 * (d + a) ^ 8 ≤ 429981696 * d ^ 16 := by
    have hda_le : d + a ≤ 12 * d := by linarith
    have hpow : (d + a) ^ 8 ≤ (12 * d) ^ 8 := pow_le_pow_left₀ hda_pos.le hda_le 8
    nlinarith [hpow, pow_pos hd 8]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 20000 * d ^ 9) hden_pos]
    have h1 : X * a * (d ^ 8 * (d + a) ^ 8) ≤ X * a * (429981696 * d ^ 16) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    have h2 : X * a * (429981696 * d ^ 16) ≤ 5040 * X * a * Q * (20000 * d ^ 9) := by
      have hmul : (5040 * X * a * (20000 * d ^ 9)) * (8 * d ^ 7) ≤
          (5040 * X * a * (20000 * d ^ 9)) * Q :=
        mul_le_mul_of_nonneg_left hQlo (by positivity)
      nlinarith [hmul]
    linarith
  · rw [div_le_div_iff₀ hden_pos (by positivity : 0 < d ^ 9)]
    have h1 : 5040 * X * a * Q * d ^ 9 ≤
        5040 * X * a * (39089245 * d ^ 7) * d ^ 9 := by
      have hmul : (5040 * X * a * d ^ 9) * Q ≤
          (5040 * X * a * d ^ 9) * (39089245 * d ^ 7) :=
        mul_le_mul_of_nonneg_left hQhi (by positivity)
      nlinarith [hmul]
    have h2 : 5040 * X * a * (39089245 * d ^ 7) * d ^ 9 ≤
        197009794800 * X * a * (d ^ 8 * (d + a) ^ 8) := by
      have hmul : (197009794800 * X * a) * d ^ 16 ≤
          (197009794800 * X * a) * (d ^ 8 * (d + a) ^ 8) :=
        mul_le_mul_of_nonneg_left hden_lo (by positivity)
      nlinarith [hmul]
    linarith

/-! ## Wide-window scale bounds in the dyadic `F/D^k` scale -/

private theorem XA_div_D4_eq_F_div_D {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 4 = S.F / S.D := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem XA_div_D5_eq_F_div_D2 {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 5 = S.F / S.D ^ 2 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem XA_div_D6_eq_F_div_D3 {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 6 = S.F / S.D ^ 3 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem XA_div_D7_eq_F_div_D4 {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 7 = S.F / S.D ^ 4 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem XA_div_D8_eq_F_div_D5 {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 8 = S.F / S.D ^ 5 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

/-- Wide inverse-window first-derivative scale:
if `10A ≤ D`, `a ∈ [A/5,11A]`, and `d ∈ [D/10,18D]`, then
`|F_a'(d)| ≍ F/D` with explicit constants. -/
theorem Ffun_deriv1_scale_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (288 * 5 * 18 ^ 4) : ℝ) * (S.F / S.D) ≤
        |deriv (fun t => Ffun P.X a t) d| ∧
      |deriv (fun t => Ffun P.X a t) d| ≤
        (314 * 11 * 10 ^ 4 : ℝ) * (S.F / S.D) := by
  have hX := P.X_pos
  have hApos : 0 < S.A := by
    rw [show S.A = S.Δ * S.Ω from rfl]
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have had : a ≤ 11 * d := by nlinarith [ha_hi, hAD, hd_lo]
  obtain ⟨hloc, hloc_hi⟩ := Ffun_deriv1_abs_bounds hX ha0 hd0 had
  constructor
  · refine le_trans ?_ hloc
    rw [← XA_div_D4_eq_F_div_D S]
    rw [show (1 / (288 * 5 * 18 ^ 4) : ℝ) * (P.X * S.A / S.D ^ 4)
        = P.X * S.A / ((288 * 5 * 18 ^ 4) * S.D ^ 4) by field_simp]
    rw [div_le_div_iff₀ (by positivity : 0 < (288 * 5 * 18 ^ 4 : ℝ) * S.D ^ 4)
      (by positivity : 0 < 288 * d ^ 4)]
    have hd4 : d ^ 4 ≤ (18 * S.D) ^ 4 := pow_le_pow_left₀ hd0.le hd_hi 4
    have ha5 : S.A ≤ 5 * a := by linarith
    have hprod : S.A * d ^ 4 ≤ (5 * a) * (18 * S.D) ^ 4 :=
      mul_le_mul ha5 hd4 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]
  · refine le_trans hloc_hi ?_
    rw [← XA_div_D4_eq_F_div_D S]
    rw [show (314 * 11 * 10 ^ 4 : ℝ) * (P.X * S.A / S.D ^ 4)
        = (314 * 11 * 10 ^ 4) * P.X * S.A / S.D ^ 4 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 4) (by positivity : 0 < S.D ^ 4)]
    have hd4 : (S.D / 10) ^ 4 ≤ d ^ 4 := pow_le_pow_left₀ (by positivity) hd_lo 4
    have hD4 : S.D ^ 4 ≤ 10 ^ 4 * d ^ 4 := by nlinarith [hd4, hDpos]
    have hprod : a * S.D ^ 4 ≤ (11 * S.A) * (10 ^ 4 * d ^ 4) :=
      mul_le_mul ha_hi hD4 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]

/-- Wide inverse-window second-derivative scale:
if `10A ≤ D`, `a ∈ [A/5,11A]`, and `d ∈ [D/10,18D]`, then
`|F_a''(d)| ≍ F/D²` with explicit constants. -/
theorem Ffun_deriv2_scale_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (864 * 5 * 18 ^ 5) : ℝ) * (S.F / S.D ^ 2) ≤
        |iteratedDeriv 2 (fun t => Ffun P.X a t) d| ∧
      |iteratedDeriv 2 (fun t => Ffun P.X a t) d| ≤
        (11310 * 11 * 10 ^ 5 : ℝ) * (S.F / S.D ^ 2) := by
  have hX := P.X_pos
  have hApos : 0 < S.A := by
    rw [show S.A = S.Δ * S.Ω from rfl]
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have had : a ≤ 11 * d := by nlinarith [ha_hi, hAD, hd_lo]
  obtain ⟨hloc, hloc_hi⟩ := Ffun_deriv2_abs_bounds hX ha0 hd0 had
  constructor
  · refine le_trans ?_ hloc
    rw [← XA_div_D5_eq_F_div_D2 S]
    rw [show (1 / (864 * 5 * 18 ^ 5) : ℝ) * (P.X * S.A / S.D ^ 5)
        = P.X * S.A / ((864 * 5 * 18 ^ 5) * S.D ^ 5) by field_simp]
    rw [div_le_div_iff₀ (by positivity : 0 < (864 * 5 * 18 ^ 5 : ℝ) * S.D ^ 5)
      (by positivity : 0 < 864 * d ^ 5)]
    have hd5 : d ^ 5 ≤ (18 * S.D) ^ 5 := pow_le_pow_left₀ hd0.le hd_hi 5
    have ha5 : S.A ≤ 5 * a := by linarith
    have hprod : S.A * d ^ 5 ≤ (5 * a) * (18 * S.D) ^ 5 :=
      mul_le_mul ha5 hd5 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]
  · refine le_trans hloc_hi ?_
    rw [← XA_div_D5_eq_F_div_D2 S]
    rw [show (11310 * 11 * 10 ^ 5 : ℝ) * (P.X * S.A / S.D ^ 5)
        = (11310 * 11 * 10 ^ 5) * P.X * S.A / S.D ^ 5 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 5) (by positivity : 0 < S.D ^ 5)]
    have hd5 : (S.D / 10) ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ (by positivity) hd_lo 5
    have hD5 : S.D ^ 5 ≤ 10 ^ 5 * d ^ 5 := by nlinarith [hd5, hDpos]
    have hprod : a * S.D ^ 5 ≤ (11 * S.A) * (10 ^ 5 * d ^ 5) :=
      mul_le_mul ha_hi hD5 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]

/-- Wide inverse-window third-derivative scale:
if `10A ≤ D`, `a ∈ [A/5,11A]`, and `d ∈ [D/10,18D]`, then
`|F_a⁽³⁾(d)| ≍ F/D³` with explicit constants. -/
theorem Ffun_deriv3_scale_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (2500 * 5 * 18 ^ 6) : ℝ) * (S.F / S.D ^ 3) ≤
        |iteratedDeriv 3 (fun t => Ffun P.X a t) d| ∧
      |iteratedDeriv 3 (fun t => Ffun P.X a t) d| ≤
        (542904 * 11 * 10 ^ 6 : ℝ) * (S.F / S.D ^ 3) := by
  have hX := P.X_pos
  have hApos : 0 < S.A := by
    rw [show S.A = S.Δ * S.Ω from rfl]
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have had : a ≤ 11 * d := by nlinarith [ha_hi, hAD, hd_lo]
  obtain ⟨hloc, hloc_hi⟩ := Ffun_deriv3_abs_bounds hX ha0 hd0 had
  constructor
  · refine le_trans ?_ hloc
    rw [← XA_div_D6_eq_F_div_D3 S]
    rw [show (1 / (2500 * 5 * 18 ^ 6) : ℝ) * (P.X * S.A / S.D ^ 6)
        = P.X * S.A / ((2500 * 5 * 18 ^ 6) * S.D ^ 6) by field_simp]
    rw [div_le_div_iff₀ (by positivity : 0 < (2500 * 5 * 18 ^ 6 : ℝ) * S.D ^ 6)
      (by positivity : 0 < 2500 * d ^ 6)]
    have hd6 : d ^ 6 ≤ (18 * S.D) ^ 6 := pow_le_pow_left₀ hd0.le hd_hi 6
    have ha5 : S.A ≤ 5 * a := by linarith
    have hprod : S.A * d ^ 6 ≤ (5 * a) * (18 * S.D) ^ 6 :=
      mul_le_mul ha5 hd6 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]
  · refine le_trans hloc_hi ?_
    rw [← XA_div_D6_eq_F_div_D3 S]
    rw [show (542904 * 11 * 10 ^ 6 : ℝ) * (P.X * S.A / S.D ^ 6)
        = (542904 * 11 * 10 ^ 6) * P.X * S.A / S.D ^ 6 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 6) (by positivity : 0 < S.D ^ 6)]
    have hd6 : (S.D / 10) ^ 6 ≤ d ^ 6 := pow_le_pow_left₀ (by positivity) hd_lo 6
    have hD6 : S.D ^ 6 ≤ 10 ^ 6 * d ^ 6 := by nlinarith [hd6, hDpos]
    have hprod : a * S.D ^ 6 ≤ (11 * S.A) * (10 ^ 6 * d ^ 6) :=
      mul_le_mul ha_hi hD6 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]

/-- Wide inverse-window fourth-derivative scale:
if `10A ≤ D`, `a ∈ [A/5,11A]`, and `d ∈ [D/10,18D]`, then
`|F_a⁽⁴⁾(d)| ≍ F/D⁴` with explicit constants. -/
theorem Ffun_deriv4_scale_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (5000 * 5 * 18 ^ 7) : ℝ) * (S.F / S.D ^ 4) ≤
        |iteratedDeriv 4 (fun t => Ffun P.X a t) d| ∧
      |iteratedDeriv 4 (fun t => Ffun P.X a t) d| ≤
        (32574360 * 11 * 10 ^ 7 : ℝ) * (S.F / S.D ^ 4) := by
  have hX := P.X_pos
  have hApos : 0 < S.A := by
    rw [show S.A = S.Δ * S.Ω from rfl]
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have had : a ≤ 11 * d := by nlinarith [ha_hi, hAD, hd_lo]
  obtain ⟨hloc, hloc_hi⟩ := Ffun_deriv4_abs_bounds hX ha0 hd0 had
  constructor
  · refine le_trans ?_ hloc
    rw [← XA_div_D7_eq_F_div_D4 S]
    rw [show (1 / (5000 * 5 * 18 ^ 7) : ℝ) * (P.X * S.A / S.D ^ 7)
        = P.X * S.A / ((5000 * 5 * 18 ^ 7) * S.D ^ 7) by field_simp]
    rw [div_le_div_iff₀ (by positivity : 0 < (5000 * 5 * 18 ^ 7 : ℝ) * S.D ^ 7)
      (by positivity : 0 < 5000 * d ^ 7)]
    have hd7 : d ^ 7 ≤ (18 * S.D) ^ 7 := pow_le_pow_left₀ hd0.le hd_hi 7
    have ha5 : S.A ≤ 5 * a := by linarith
    have hprod : S.A * d ^ 7 ≤ (5 * a) * (18 * S.D) ^ 7 :=
      mul_le_mul ha5 hd7 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]
  · refine le_trans hloc_hi ?_
    rw [← XA_div_D7_eq_F_div_D4 S]
    rw [show (32574360 * 11 * 10 ^ 7 : ℝ) * (P.X * S.A / S.D ^ 7)
        = (32574360 * 11 * 10 ^ 7) * P.X * S.A / S.D ^ 7 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 7) (by positivity : 0 < S.D ^ 7)]
    have hd7 : (S.D / 10) ^ 7 ≤ d ^ 7 := pow_le_pow_left₀ (by positivity) hd_lo 7
    have hD7 : S.D ^ 7 ≤ 10 ^ 7 * d ^ 7 := by nlinarith [hd7, hDpos]
    have hprod : a * S.D ^ 7 ≤ (11 * S.A) * (10 ^ 7 * d ^ 7) :=
      mul_le_mul ha_hi hD7 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]

/-- Wide inverse-window fifth-derivative scale:
if `10A ≤ D`, `a ∈ [A/5,11A]`, and `d ∈ [D/10,18D]`, then
`|F_a⁽⁵⁾(d)| ≍ F/D⁵` with explicit constants. -/
theorem Ffun_deriv5_scale_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (10000 * 5 * 18 ^ 8) : ℝ) * (S.F / S.D ^ 5) ≤
        |iteratedDeriv 5 (fun t => Ffun P.X a t) d| ∧
      |iteratedDeriv 5 (fun t => Ffun P.X a t) d| ≤
        (2345354640 * 11 * 10 ^ 8 : ℝ) * (S.F / S.D ^ 5) := by
  have hX := P.X_pos
  have hApos : 0 < S.A := by
    rw [show S.A = S.Δ * S.Ω from rfl]
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have had : a ≤ 11 * d := by nlinarith [ha_hi, hAD, hd_lo]
  obtain ⟨hloc, hloc_hi⟩ := Ffun_deriv5_abs_bounds hX ha0 hd0 had
  constructor
  · refine le_trans ?_ hloc
    rw [← XA_div_D8_eq_F_div_D5 S]
    rw [show (1 / (10000 * 5 * 18 ^ 8) : ℝ) * (P.X * S.A / S.D ^ 8)
        = P.X * S.A / ((10000 * 5 * 18 ^ 8) * S.D ^ 8) by field_simp]
    rw [div_le_div_iff₀ (by positivity : 0 < (10000 * 5 * 18 ^ 8 : ℝ) * S.D ^ 8)
      (by positivity : 0 < 10000 * d ^ 8)]
    have hd8 : d ^ 8 ≤ (18 * S.D) ^ 8 := pow_le_pow_left₀ hd0.le hd_hi 8
    have ha5 : S.A ≤ 5 * a := by linarith
    have hprod : S.A * d ^ 8 ≤ (5 * a) * (18 * S.D) ^ 8 :=
      mul_le_mul ha5 hd8 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]
  · refine le_trans hloc_hi ?_
    rw [← XA_div_D8_eq_F_div_D5 S]
    rw [show (2345354640 * 11 * 10 ^ 8 : ℝ) * (P.X * S.A / S.D ^ 8)
        = (2345354640 * 11 * 10 ^ 8) * P.X * S.A / S.D ^ 8 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 8) (by positivity : 0 < S.D ^ 8)]
    have hd8 : (S.D / 10) ^ 8 ≤ d ^ 8 := pow_le_pow_left₀ (by positivity) hd_lo 8
    have hD8 : S.D ^ 8 ≤ 10 ^ 8 * d ^ 8 := by nlinarith [hd8, hDpos]
    have hprod : a * S.D ^ 8 ≤ (11 * S.A) * (10 ^ 8 * d ^ 8) :=
      mul_le_mul ha_hi hD8 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]

/-- Wide inverse-window sixth-derivative scale:
if `10A ≤ D`, `a ∈ [A/5,11A]`, and `d ∈ [D/10,18D]`, then
`|F_a⁽⁶⁾(d)| ≍ F/D⁶` with explicit constants. -/
theorem Ffun_deriv6_scale_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / (20000 * 5 * 18 ^ 9) : ℝ) * (S.F / S.D ^ 6) ≤
        |iteratedDeriv 6 (fun t => Ffun P.X a t) d| ∧
      |iteratedDeriv 6 (fun t => Ffun P.X a t) d| ≤
        (197009794800 * 11 * 10 ^ 9 : ℝ) * (S.F / S.D ^ 6) := by
  have hX := P.X_pos
  have hApos : 0 < S.A := by
    rw [show S.A = S.Δ * S.Ω from rfl]
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have had : a ≤ 11 * d := by nlinarith [ha_hi, hAD, hd_lo]
  have hXA : P.X * S.A / S.D ^ 9 = S.F / S.D ^ 6 := by
    have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
    rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
    field_simp
  obtain ⟨hloc, hloc_hi⟩ := Ffun_deriv6_abs_bounds hX ha0 hd0 had
  constructor
  · refine le_trans ?_ hloc
    rw [← hXA]
    rw [show (1 / (20000 * 5 * 18 ^ 9) : ℝ) * (P.X * S.A / S.D ^ 9)
        = P.X * S.A / ((20000 * 5 * 18 ^ 9) * S.D ^ 9) by field_simp]
    rw [div_le_div_iff₀ (by positivity : 0 < (20000 * 5 * 18 ^ 9 : ℝ) * S.D ^ 9)
      (by positivity : 0 < 20000 * d ^ 9)]
    have hd9 : d ^ 9 ≤ (18 * S.D) ^ 9 := pow_le_pow_left₀ hd0.le hd_hi 9
    have ha5 : S.A ≤ 5 * a := by linarith
    have hprod : S.A * d ^ 9 ≤ (5 * a) * (18 * S.D) ^ 9 :=
      mul_le_mul ha5 hd9 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]
  · refine le_trans hloc_hi ?_
    rw [← hXA]
    rw [show (197009794800 * 11 * 10 ^ 9 : ℝ) * (P.X * S.A / S.D ^ 9)
        = (197009794800 * 11 * 10 ^ 9) * P.X * S.A / S.D ^ 9 by ring]
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 9) (by positivity : 0 < S.D ^ 9)]
    have hd9 : (S.D / 10) ^ 9 ≤ d ^ 9 := pow_le_pow_left₀ (by positivity) hd_lo 9
    have hD9 : S.D ^ 9 ≤ 10 ^ 9 * d ^ 9 := by nlinarith [hd9, hDpos]
    have hprod : a * S.D ^ 9 ≤ (11 * S.A) * (10 ^ 9 * d ^ 9) :=
      mul_le_mul ha_hi hD9 (by positivity) (by positivity)
    nlinarith [hprod, hX, hApos, hDpos]

end Squarefree
