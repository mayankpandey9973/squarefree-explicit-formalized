import Squarefree.Structure.PhaseDeriv

/-!
# §5 derivative calculus, foundational lemma: the `r`-derivative of `d̃ₐ(r)`

The defect inverse `d̃ₐ(r) = R_a^{-1}(r)` (`dtilde`, `PhaseDeriv`) has, by the inverse
function theorem applied to `R_a`,

  `d̃ₐ'(r) = 1 / R_a'(d̃ₐ(r)) = − d̃(d̃+a) / (2 r (a + 2 d̃))`   (sympy-verified, writeup 676–725).

We obtain this via `HasDerivAt.of_local_left_inverse` (no re-differentiation of the nested
radical), then rewrite the inverse-derivative value to the clean closed form using
`dtilde_prod` and `dtilde_spec`.
-/

namespace Squarefree

open Real

/-- **The `r`-derivative of the defect inverse `d̃ₐ(r)`.**
By the inverse function theorem on `R_a` (whose closed `d`-derivative is `Rfun_hasDerivAt_d`),

  `d̃ₐ'(r) = − d̃ₐ(r)·(d̃ₐ(r)+a) / (2 r (a + 2 d̃ₐ(r)))`.

(sympy-verified `d̃'(r) = 1/R_a'(d̃) = −d̃(d̃+a)/(2r(a+2d̃))`, writeup 676–725.) -/
theorem dtilde_r_hasDerivAt {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun s => dtilde X s a)
      (- dtilde X r a * (dtilde X r a + a) / (2 * r * (a + 2 * dtilde X r a))) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have hda2 : 0 < a + 2 * d := by linarith
  -- The `d`-derivative value of `R_a` at `d`.
  set Rval := (-2 * X * a ^ 3 * (2 * d + a) / (d ^ 3 * (d + a) ^ 3)) with hRval_def
  -- `hf`: `R_a` has derivative `Rval` at `g r = d`.
  have hf : HasDerivAt (fun t => Rfun X a t) Rval d :=
    Rfun_hasDerivAt_d X a d (ne_of_gt hd) (by positivity)
  -- `hf'`: `Rval ≠ 0`.
  have hf' : Rval ≠ 0 := ne_of_lt (Rfun_deriv_neg hX ha hd)
  -- `hg`: `s ↦ d̃ₐ(s)` is continuous at `r`. Unfold `dtilde` and compose continuity of `√`,
  -- division, etc., on the neighbourhood `{s | 0 < s}`.
  have hg : ContinuousAt (fun s => dtilde X s a) r := by
    have hcont : ContinuousAt
        (fun s : ℝ => (-a + Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / s))) / 2) r := by
      have hinner : ContinuousAt (fun s : ℝ => Real.sqrt (X * a ^ 3 / s)) r :=
        Real.continuous_sqrt.continuousAt.comp
          ((continuousAt_const).div continuousAt_id (ne_of_gt hr))
      have hrad : ContinuousAt
          (fun s : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / s)) r :=
        continuousAt_const.add (continuousAt_const.mul hinner)
      have houter : ContinuousAt
          (fun s : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / s))) r :=
        Real.continuous_sqrt.continuousAt.comp hrad
      exact (continuousAt_const.add houter).div_const 2
    simpa only [dtilde] using hcont
  -- `hfg`: on a neighbourhood of `r`, `R_a (d̃ₐ s) = s`.
  have hfg : ∀ᶠ y in nhds r, (fun t => Rfun X a t) (dtilde X y a) = y := by
    filter_upwards [eventually_gt_nhds hr] with y hy
    exact dtilde_spec hX ha hy
  -- Inverse function theorem: `d̃ₐ` has derivative `Rval⁻¹` at `r`.
  have key : HasDerivAt (fun s => dtilde X s a) Rval⁻¹ r :=
    hf.of_local_left_inverse hg hf' hfg
  -- Rewrite `Rval⁻¹` to the clean closed form.
  have hval : Rval⁻¹ = - d * (d + a) / (2 * r * (a + 2 * d)) := by
    -- `r = X a³ / (d²(d+a)²)` via `dtilde_spec` + `Rfun_factor'`.
    have hr_eq : r = X * a ^ 3 / (d ^ 2 * (d + a) ^ 2) := by
      have hspec : Rfun X a d = r := dtilde_spec hX ha hr
      rw [Rfun_factor' X a d (ne_of_gt hd) (ne_of_gt hda)] at hspec
      linarith [hspec]
    rw [hRval_def, hr_eq]
    rw [inv_div]
    -- Now both sides are explicit rational functions of `X, a, d`; clear denominators.
    have hd3 : (0:ℝ) < d ^ 3 * (d + a) ^ 3 := by positivity
    have hden : (0:ℝ) < d ^ 2 * (d + a) ^ 2 := by positivity
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  rw [hval] at key
  exact key

/-- The first-derivative function `d̃ₐ'(s)` as a closed-form expression. Its value at `r`
equals the derivative produced by `dtilde_r_hasDerivAt`. -/
private noncomputable def dtil1 (X a s : ℝ) : ℝ :=
  - dtilde X s a * (dtilde X s a + a) / (2 * s * (a + 2 * dtilde X s a))

/-- **The second `r`-derivative of the defect inverse `d̃ₐ(r)`.**

  `d̃ₐ''(r) = d̃(d̃+a)(3a² + 10a d̃ + 10 d̃²) / (4 r² (a + 2 d̃)³)`.

(sympy-verified, writeup 720–725; this is `≍ Δ/R² > 0`.) -/
theorem dtil1_hasDerivAt {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun s => dtil1 X a s)
      ( dtilde X r a * (dtilde X r a + a)
        * (3 * a ^ 2 + 10 * a * dtilde X r a + 10 * dtilde X r a ^ 2)
        / (4 * r ^ 2 * (a + 2 * dtilde X r a) ^ 3) ) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have hda2 : 0 < a + 2 * d := by linarith
  -- Inner derivative `D'(r) = dtil1 X a r`.
  have hD : HasDerivAt (fun s => dtilde X s a) (dtil1 X a r) r := by
    have := dtilde_r_hasDerivAt hX ha hr
    convert this using 1
  set D' := dtil1 X a r with hD'_def
  -- Numerator `N(s) = - D(s) * (D(s) + a)`.
  have hN : HasDerivAt (fun s => - dtilde X s a * (dtilde X s a + a))
      ((- D') * (d + a) + (- d) * D') r := by
    exact (hD.neg).mul (hD.add_const a)
  -- Denominator `M(s) = 2*s*(a + 2*D(s))`.
  have hMid : HasDerivAt (fun s => (2:ℝ) * s) 2 r := by
    simpa using (hasDerivAt_id r).const_mul 2
  have hMin : HasDerivAt (fun s => a + 2 * dtilde X s a) (2 * D') r := by
    exact (hD.const_mul 2).const_add a
  have hM : HasDerivAt (fun s => (2:ℝ) * s * (a + 2 * dtilde X s a))
      (2 * (a + 2 * d) + (2 * r) * (2 * D')) r := by
    exact hMid.mul hMin
  -- Denominator value nonzero at `r`.
  have hMne : (2:ℝ) * r * (a + 2 * d) ≠ 0 := by positivity
  -- Quotient rule.
  have hderiv : HasDerivAt (fun s => dtil1 X a s)
      ( (((- D') * (d + a) + (- d) * D') * ((2:ℝ) * r * (a + 2 * d))
          - (- d * (d + a)) * (2 * (a + 2 * d) + (2 * r) * (2 * D')))
        / ((2:ℝ) * r * (a + 2 * d)) ^ 2 ) r := by
    have := hN.div hM hMne
    convert this using 1
  -- Substitute the explicit value of `D' = dtil1 X a r`.
  have hD'_val : D' = - d * (d + a) / (2 * r * (a + 2 * d)) := by
    simp only [hD'_def, dtil1, hd_def]
  -- Now `RAW = target`.  Substitute `D'` and simplify.
  have hval : (((- D') * (d + a) + (- d) * D') * ((2:ℝ) * r * (a + 2 * d))
          - (- d * (d + a)) * (2 * (a + 2 * d) + (2 * r) * (2 * D')))
        / ((2:ℝ) * r * (a + 2 * d)) ^ 2
      = d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
        / (4 * r ^ 2 * (a + 2 * d) ^ 3) := by
    rw [hD'_val]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hda2' : a + 2 * d ≠ 0 := ne_of_gt hda2
    field_simp
    ring
  rw [hval] at hderiv
  exact hderiv

/-- **The second `r`-derivative of `d̃ₐ` as an `iteratedDeriv`.** -/
theorem dtilde_r_iteratedDeriv2 {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    iteratedDeriv 2 (fun s => dtilde X s a) r
      = dtilde X r a * (dtilde X r a + a)
        * (3 * a ^ 2 + 10 * a * dtilde X r a + 10 * dtilde X r a ^ 2)
        / (4 * r ^ 2 * (a + 2 * dtilde X r a) ^ 3) := by
  have hL : iteratedDeriv 2 (fun s => dtilde X s a) r
      = deriv (deriv (fun s => dtilde X s a)) r := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hL]
  -- `deriv (fun s => dtilde X s a) =ᶠ[nhds r] dtil1 X a ·` on the open set `{s | 0 < s}`.
  have hee : deriv (fun s => dtilde X s a) =ᶠ[nhds r] (fun s => dtil1 X a s) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hr) ?_
    intro s hs
    have hs' : 0 < s := hs
    have := (dtilde_r_hasDerivAt hX ha hs').deriv
    rw [this]
    simp only [dtil1]
  rw [hee.deriv_eq]
  exact (dtil1_hasDerivAt hX ha hr).deriv

/-- **`d̃ₐ'` is differentiable with derivative `d̃ₐ''`.**  I.e. the function
`s ↦ deriv (d̃ₐ) s` has derivative `iteratedDeriv 2 d̃ₐ s` at `s` (for `s > 0`).  This exposes
the MVT-ready differentiability of the first derivative (used by §5 Step-1 monotonicity). -/
theorem dtilde_deriv_hasDerivAt {X a s : ℝ} (hX : 0 < X) (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun t => deriv (fun u => dtilde X u a) t)
      (iteratedDeriv 2 (fun u => dtilde X u a) s) s := by
  have hee : deriv (fun u => dtilde X u a) =ᶠ[nhds s] (fun t => dtil1 X a t) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hs) ?_
    intro t ht
    have ht' : 0 < t := ht
    have := (dtilde_r_hasDerivAt hX ha ht').deriv
    rw [this]
    simp only [dtil1]
  rw [dtilde_r_iteratedDeriv2 hX ha hs]
  exact (dtil1_hasDerivAt hX ha hs).congr_of_eventuallyEq hee

/-- The second-derivative function `d̃ₐ''(s)` as a closed-form expression. Its value at `r`
equals the derivative produced by `dtil1_hasDerivAt`. -/
private noncomputable def dtil2 (X a s : ℝ) : ℝ :=
  dtilde X s a * (dtilde X s a + a) * (3 * a ^ 2 + 10 * a * dtilde X s a + 10 * dtilde X s a ^ 2)
    / (4 * s ^ 2 * (a + 2 * dtilde X s a) ^ 3)

/-- **The third `r`-derivative of the defect inverse `d̃ₐ(r)`.**

  `d̃ₐ'''(r) = − 3 d̃(d̃+a)(5a⁴ + 34a³d̃ + 94a²d̃² + 120a d̃³ + 60 d̃⁴) / (8 r³ (a + 2 d̃)⁵)`.

(sympy-verified.) -/
theorem dtil2_hasDerivAt {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun s => dtil2 X a s)
      ( - 3 * dtilde X r a * (dtilde X r a + a)
          * (5 * a ^ 4 + 34 * a ^ 3 * dtilde X r a + 94 * a ^ 2 * dtilde X r a ^ 2
             + 120 * a * dtilde X r a ^ 3 + 60 * dtilde X r a ^ 4)
        / (8 * r ^ 3 * (a + 2 * dtilde X r a) ^ 5) ) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have hda2 : 0 < a + 2 * d := by linarith
  -- Inner derivative `D'(r) = dtil1 X a r`.
  have hD : HasDerivAt (fun s => dtilde X s a) (dtil1 X a r) r := by
    have := dtilde_r_hasDerivAt hX ha hr
    convert this using 1
  set D' := dtil1 X a r with hD'_def
  -- Numerator `N(s) = D(s)*(D(s)+a)*(3a² + 10a D(s) + 10 D(s)²)`.
  have hP : HasDerivAt (fun s => dtilde X s a * (dtilde X s a + a))
      (D' * (d + a) + d * D') r :=
    hD.mul (hD.add_const a)
  have hQ : HasDerivAt
      (fun s => 3 * a ^ 2 + 10 * a * dtilde X s a + 10 * dtilde X s a ^ 2)
      (10 * a * D' + 10 * (2 * d * D')) r := by
    have h1 : HasDerivAt (fun s => 10 * a * dtilde X s a) (10 * a * D') r := by
      have := hD.const_mul (10 * a)
      simpa [mul_assoc] using this
    have h2 : HasDerivAt (fun s => 10 * dtilde X s a ^ 2) (10 * (2 * d * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 2) (2 * d ^ 1 * D') r := by
        simpa using hD.pow 2
      have := hpow.const_mul 10
      simpa using this
    have := (((hasDerivAt_const r (3 * a ^ 2)).add h1).add h2)
    convert this using 1
    ring
  have hN : HasDerivAt
      (fun s => dtilde X s a * (dtilde X s a + a)
        * (3 * a ^ 2 + 10 * a * dtilde X s a + 10 * dtilde X s a ^ 2))
      ((D' * (d + a) + d * D') * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
        + (d * (d + a)) * (10 * a * D' + 10 * (2 * d * D'))) r :=
    hP.mul hQ
  -- Denominator `M(s) = 4*s²*(a + 2*D(s))³`.
  have hMid : HasDerivAt (fun s => (4:ℝ) * s ^ 2) (4 * (2 * r ^ 1)) r := by
    have := (hasDerivAt_pow 2 r).const_mul 4
    simpa using this
  have hMin : HasDerivAt (fun s => (a + 2 * dtilde X s a) ^ 3)
      (3 * (a + 2 * d) ^ 2 * (2 * D')) r := by
    have hbase : HasDerivAt (fun s => a + 2 * dtilde X s a) (2 * D') r :=
      (hD.const_mul 2).const_add a
    have := hbase.pow 3
    simpa using this
  have hM : HasDerivAt (fun s => (4:ℝ) * s ^ 2 * (a + 2 * dtilde X s a) ^ 3)
      ((4 * (2 * r ^ 1)) * (a + 2 * d) ^ 3
        + (4 * r ^ 2) * (3 * (a + 2 * d) ^ 2 * (2 * D'))) r :=
    hMid.mul hMin
  -- Denominator value nonzero at `r`.
  have hMne : (4:ℝ) * r ^ 2 * (a + 2 * d) ^ 3 ≠ 0 := by positivity
  -- Quotient rule.
  have hderiv : HasDerivAt (fun s => dtil2 X a s)
      ( ( ((D' * (d + a) + d * D') * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
            + (d * (d + a)) * (10 * a * D' + 10 * (2 * d * D')))
            * ((4:ℝ) * r ^ 2 * (a + 2 * d) ^ 3)
          - (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2))
            * ((4 * (2 * r ^ 1)) * (a + 2 * d) ^ 3
               + (4 * r ^ 2) * (3 * (a + 2 * d) ^ 2 * (2 * D'))))
        / ((4:ℝ) * r ^ 2 * (a + 2 * d) ^ 3) ^ 2 ) r := by
    have := hN.div hM hMne
    convert this using 1
  -- Substitute the explicit value of `D' = dtil1 X a r`.
  have hD'_val : D' = - d * (d + a) / (2 * r * (a + 2 * d)) := by
    simp only [hD'_def, dtil1, hd_def]
  -- Now `RAW = target`.  Substitute `D'` and simplify.
  have hval : ( ((D' * (d + a) + d * D') * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2)
            + (d * (d + a)) * (10 * a * D' + 10 * (2 * d * D')))
            * ((4:ℝ) * r ^ 2 * (a + 2 * d) ^ 3)
          - (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2))
            * ((4 * (2 * r ^ 1)) * (a + 2 * d) ^ 3
               + (4 * r ^ 2) * (3 * (a + 2 * d) ^ 2 * (2 * D'))))
        / ((4:ℝ) * r ^ 2 * (a + 2 * d) ^ 3) ^ 2
      = - 3 * d * (d + a)
          * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2
             + 120 * a * d ^ 3 + 60 * d ^ 4)
        / (8 * r ^ 3 * (a + 2 * d) ^ 5) := by
    rw [hD'_val]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hda2' : a + 2 * d ≠ 0 := ne_of_gt hda2
    field_simp
    ring
  rw [hval] at hderiv
  exact hderiv

/-- **The third `r`-derivative of `d̃ₐ` as an `iteratedDeriv`.** -/
theorem dtilde_r_iteratedDeriv3 {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    iteratedDeriv 3 (fun s => dtilde X s a) r
      = - 3 * dtilde X r a * (dtilde X r a + a)
          * (5*a^4 + 34*a^3*dtilde X r a + 94*a^2*dtilde X r a^2 + 120*a*dtilde X r a^3
             + 60*dtilde X r a^4)
        / (8 * r^3 * (a + 2*dtilde X r a)^5) := by
  have hL : iteratedDeriv 3 (fun s => dtilde X s a) r
      = deriv (iteratedDeriv 2 (fun s => dtilde X s a)) r := by
    rw [iteratedDeriv_succ]
  rw [hL]
  -- `iteratedDeriv 2 (fun s => dtilde X s a) =ᶠ[nhds r] dtil2 X a ·` on the open set `{s | 0 < s}`.
  have hee : iteratedDeriv 2 (fun s => dtilde X s a) =ᶠ[nhds r] (fun s => dtil2 X a s) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hr) ?_
    intro s hs
    have hs' : 0 < s := hs
    rw [dtilde_r_iteratedDeriv2 hX ha hs']
    simp only [dtil2]
  rw [hee.deriv_eq]
  exact (dtil2_hasDerivAt hX ha hr).deriv

/-- **`d̃ₐ''` is differentiable with derivative `d̃ₐ'''`.**  I.e. the function
`s ↦ iteratedDeriv 2 d̃ₐ s` has derivative `iteratedDeriv 3 d̃ₐ s` at `s` (for `s > 0`).
Exposes the MVT-ready differentiability of the second derivative (§5 Step-1 monotonicity). -/
theorem dtilde_iteratedDeriv2_hasDerivAt {X a s : ℝ} (hX : 0 < X) (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun t => iteratedDeriv 2 (fun u => dtilde X u a) t)
      (iteratedDeriv 3 (fun u => dtilde X u a) s) s := by
  have hee : iteratedDeriv 2 (fun u => dtilde X u a) =ᶠ[nhds s] (fun t => dtil2 X a t) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hs) ?_
    intro t ht
    have ht' : 0 < t := ht
    rw [dtilde_r_iteratedDeriv2 hX ha ht']
    simp only [dtil2]
  rw [dtilde_r_iteratedDeriv3 hX ha hs]
  exact (dtil2_hasDerivAt hX ha hs).congr_of_eventuallyEq hee

/-- **§5 Step-1 phase monotonicity, algebraic core.**

The Step-1 phase `φ = c·b̃²/d̃⁵` is monotone because the combination
`2·d̃''(r)·d̃(r) − 5·(d̃'(r))²` is exactly positive. Plugging in the closed forms
`d̃'(r) = −d̃(d̃+a)/(2r(a+2d̃))` and `d̃''(r) = d̃(d̃+a)(3a²+10a d̃+10 d̃²)/(4r²(a+2d̃)³)`,
this combination simplifies to `d̃²(d̃+a)(a²+5a d̃+10 d̃²)/(4r²(a+2d̃)³) > 0`.
(sympy-verified.) -/
theorem dtilde_mono_leading {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    2 * (dtilde X r a * (dtilde X r a + a)
          * (3 * a ^ 2 + 10 * a * dtilde X r a + 10 * dtilde X r a ^ 2)
          / (4 * r ^ 2 * (a + 2 * dtilde X r a) ^ 3)) * dtilde X r a
      - 5 * (dtilde X r a * (dtilde X r a + a) / (2 * r * (a + 2 * dtilde X r a))) ^ 2
    = dtilde X r a ^ 2 * (dtilde X r a + a)
        * (a ^ 2 + 5 * a * dtilde X r a + 10 * dtilde X r a ^ 2)
        / (4 * r ^ 2 * (a + 2 * dtilde X r a) ^ 3)
  ∧ 0 < dtilde X r a ^ 2 * (dtilde X r a + a)
        * (a ^ 2 + 5 * a * dtilde X r a + 10 * dtilde X r a ^ 2)
        / (4 * r ^ 2 * (a + 2 * dtilde X r a) ^ 3) := by
  have hd : 0 < dtilde X r a := dtilde_pos hX ha hr
  have h1 : (a + 2 * dtilde X r a) ≠ 0 := by positivity
  have h2 : r ≠ 0 := ne_of_gt hr
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · positivity

/-- **`d̃ₐ` is `C²` in `r`** (the `r`-variable analogue of `dtilde_contDiffAt`).  From the
closed form `(−a + √(a² + 4√(Xa³/r)))/2`; the only `r`-dependence is the inner `√(Xa³/r)`,
`C²` at `r > 0` since `r ≠ 0` and `Xa³/r > 0`. -/
theorem dtilde_contDiffAt_r {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 2 (fun s => dtilde X s a) r := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hinner : ContDiffAt ℝ 2 (fun s : ℝ => Real.sqrt (X * a ^ 3 / s)) r := by
    refine ContDiffAt.sqrt ?_ (by positivity)
    fun_prop (disch := assumption)
  have hrad : ContDiffAt ℝ 2 (fun s : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / s)) r := by
    fun_prop (disch := assumption)
  have houter : ContDiffAt ℝ 2
      (fun s : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / s))) r := by
    refine ContDiffAt.sqrt hrad ?_
    have : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hfin : ContDiffAt ℝ 2
      (fun s : ℝ => (-a + Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / s))) / 2) r := by
    fun_prop (disch := assumption)
  simpa [dtilde] using hfin

end Squarefree
