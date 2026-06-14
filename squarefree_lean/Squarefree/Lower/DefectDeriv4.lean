import Squarefree.Lower.DefectMono

/-!
# §5 derivative calculus: the 4th `r`-derivative of `d̃ₐ(r)`

Extends the `d̃ₐ` derivative tower (`DefectDeriv`, `DefectMono`) by one order.  From the closed
form of `d̃ₐ'''` and the chain rule `d̃ₐ'(r) = − d̃(d̃+a)/(2 r (a + 2 d̃))` we obtain

  `d̃ₐ''''(r) = 3 d̃(d̃+a)(35a⁶+362a⁵d̃+1650a⁴d̃²+4136a³d̃³+5968a²d̃⁴+4680a d̃⁵+1560 d̃⁶)
                / (16 r⁴ (a + 2 d̃)⁷)`   (sympy-verified; positive),

together with the scale bound `|d̃''''(r)| ≤ C₄ · D/R⁴` on the §5 band window.  This is the
gating prerequisite for the §5 Step-2 curvature bound.  We do *not* edit `DefectDeriv.lean`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 4000000

/-- The third-derivative function `d̃ₐ'''(s)` as a closed-form expression (matches the RHS of
`dtilde_r_iteratedDeriv3` with `s` in place of `r`). -/
private noncomputable def dtil3 (X a s : ℝ) : ℝ :=
  - 3 * dtilde X s a * (dtilde X s a + a)
    * (5*a^4 + 34*a^3*dtilde X s a + 94*a^2*dtilde X s a^2 + 120*a*dtilde X s a^3
       + 60*dtilde X s a^4)
  / (8 * s^3 * (a + 2*dtilde X s a)^5)

/-- **The derivative of the closed form `d̃ₐ'''` (i.e. `d̃ₐ''''` pointwise).**

  `d̃ₐ''''(r) = 3 d̃(d̃+a)(35a⁶+362a⁵d̃+1650a⁴d̃²+4136a³d̃³+5968a²d̃⁴+4680a d̃⁵+1560 d̃⁶)
                / (16 r⁴ (a + 2 d̃)⁷)`.

(sympy-verified by differentiating the `d̃'''` closed form under `d̃' = −d̃(d̃+a)/(2r(a+2d̃))`,
then `factor`; numerically validated against `dtilde` via `mpmath`.) -/
theorem dtil3_hasDerivAt {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun s => dtil3 X a s)
      ( 3 * dtilde X r a * (dtilde X r a + a)
          * (35 * a ^ 6 + 362 * a ^ 5 * dtilde X r a + 1650 * a ^ 4 * dtilde X r a ^ 2
             + 4136 * a ^ 3 * dtilde X r a ^ 3 + 5968 * a ^ 2 * dtilde X r a ^ 4
             + 4680 * a * dtilde X r a ^ 5 + 1560 * dtilde X r a ^ 6)
        / (16 * r ^ 4 * (a + 2 * dtilde X r a) ^ 7) ) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have hda2 : 0 < a + 2 * d := by linarith
  -- inner derivative `d̃'(r) = −d̃(d̃+a)/(2r(a+2d̃))`
  have hD : HasDerivAt (fun s => dtilde X s a) (- d * (d + a) / (2 * r * (a + 2 * d))) r :=
    dtilde_r_hasDerivAt hX ha hr
  set D' := - d * (d + a) / (2 * r * (a + 2 * d)) with hD'_def
  -- numerator first factor: `-3 d̃ (d̃+a)`
  have hP3 : HasDerivAt (fun s => -3 * dtilde X s a * (dtilde X s a + a))
      ((-3 * D') * (d + a) + (-3 * d) * D') r :=
    (hD.const_mul (-3)).mul (hD.add_const a)
  -- the degree-4 polynomial factor
  have hQ4 : HasDerivAt
      (fun s => 5 * a ^ 4 + 34 * a ^ 3 * dtilde X s a + 94 * a ^ 2 * dtilde X s a ^ 2
         + 120 * a * dtilde X s a ^ 3 + 60 * dtilde X s a ^ 4)
      (34 * a ^ 3 * D' + 94 * a ^ 2 * (2 * d * D') + 120 * a * (3 * d ^ 2 * D')
         + 60 * (4 * d ^ 3 * D')) r := by
    have h1 : HasDerivAt (fun s => 34 * a ^ 3 * dtilde X s a) (34 * a ^ 3 * D') r := by
      have := hD.const_mul (34 * a ^ 3); simpa [mul_assoc] using this
    have h2 : HasDerivAt (fun s => 94 * a ^ 2 * dtilde X s a ^ 2)
        (94 * a ^ 2 * (2 * d * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 2) (2 * d * D') r := by
        have := hD.pow 2; simpa using this
      have := hpow.const_mul (94 * a ^ 2); simpa [mul_assoc] using this
    have h3 : HasDerivAt (fun s => 120 * a * dtilde X s a ^ 3)
        (120 * a * (3 * d ^ 2 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 3) (3 * d ^ 2 * D') r := by
        have := hD.pow 3; simpa using this
      have := hpow.const_mul (120 * a); simpa [mul_assoc] using this
    have h4 : HasDerivAt (fun s => 60 * dtilde X s a ^ 4) (60 * (4 * d ^ 3 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 4) (4 * d ^ 3 * D') r := by
        have := hD.pow 4; simpa using this
      have := hpow.const_mul 60; simpa using this
    have := ((((hasDerivAt_const r (5 * a ^ 4)).add h1).add h2).add h3).add h4
    convert this using 1
    ring
  -- full numerator
  have hN : HasDerivAt
      (fun s => -3 * dtilde X s a * (dtilde X s a + a)
        * (5 * a ^ 4 + 34 * a ^ 3 * dtilde X s a + 94 * a ^ 2 * dtilde X s a ^ 2
           + 120 * a * dtilde X s a ^ 3 + 60 * dtilde X s a ^ 4))
      ( ((-3 * D') * (d + a) + (-3 * d) * D')
          * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
        + (-3 * d * (d + a))
          * (34 * a ^ 3 * D' + 94 * a ^ 2 * (2 * d * D') + 120 * a * (3 * d ^ 2 * D')
             + 60 * (4 * d ^ 3 * D')) ) r :=
    hP3.mul hQ4
  -- denominator `8 s³ (a + 2 d̃)⁵`
  have hMid : HasDerivAt (fun s => (8:ℝ) * s ^ 3) (8 * (3 * r ^ 2)) r := by
    have := (hasDerivAt_pow 3 r).const_mul 8; simpa using this
  have hMin : HasDerivAt (fun s => (a + 2 * dtilde X s a) ^ 5)
      (5 * (a + 2 * d) ^ 4 * (2 * D')) r := by
    have hbase : HasDerivAt (fun s => a + 2 * dtilde X s a) (2 * D') r :=
      (hD.const_mul 2).const_add a
    have := hbase.pow 5; simpa using this
  have hM : HasDerivAt (fun s => (8:ℝ) * s ^ 3 * (a + 2 * dtilde X s a) ^ 5)
      ((8 * (3 * r ^ 2)) * (a + 2 * d) ^ 5
        + (8 * r ^ 3) * (5 * (a + 2 * d) ^ 4 * (2 * D'))) r :=
    hMid.mul hMin
  have hMne : (8:ℝ) * r ^ 3 * (a + 2 * d) ^ 5 ≠ 0 := by positivity
  -- quotient rule (raw value)
  have hderiv : HasDerivAt (fun s => dtil3 X a s)
      ( ( (((-3 * D') * (d + a) + (-3 * d) * D')
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
            + (-3 * d * (d + a))
              * (34 * a ^ 3 * D' + 94 * a ^ 2 * (2 * d * D') + 120 * a * (3 * d ^ 2 * D')
                 + 60 * (4 * d ^ 3 * D')))
            * ((8:ℝ) * r ^ 3 * (a + 2 * d) ^ 5)
          - (-3 * d * (d + a)
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4))
            * ((8 * (3 * r ^ 2)) * (a + 2 * d) ^ 5
               + (8 * r ^ 3) * (5 * (a + 2 * d) ^ 4 * (2 * D'))) )
        / ((8:ℝ) * r ^ 3 * (a + 2 * d) ^ 5) ^ 2 ) r := by
    have := hN.div hM hMne
    convert this using 1
  -- substitute `D'` and simplify to the target closed form
  have hval : ( (((-3 * D') * (d + a) + (-3 * d) * D')
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
            + (-3 * d * (d + a))
              * (34 * a ^ 3 * D' + 94 * a ^ 2 * (2 * d * D') + 120 * a * (3 * d ^ 2 * D')
                 + 60 * (4 * d ^ 3 * D')))
            * ((8:ℝ) * r ^ 3 * (a + 2 * d) ^ 5)
          - (-3 * d * (d + a)
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4))
            * ((8 * (3 * r ^ 2)) * (a + 2 * d) ^ 5
               + (8 * r ^ 3) * (5 * (a + 2 * d) ^ 4 * (2 * D'))) )
        / ((8:ℝ) * r ^ 3 * (a + 2 * d) ^ 5) ^ 2
      = 3 * d * (d + a)
          * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
             + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
        / (16 * r ^ 4 * (a + 2 * d) ^ 7) := by
    rw [hD'_def]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hda2' : a + 2 * d ≠ 0 := ne_of_gt hda2
    field_simp
    ring
  rw [hval] at hderiv
  exact hderiv

/-- **The fourth `r`-derivative of `d̃ₐ` as an `iteratedDeriv`.** -/
theorem dtilde_r_iteratedDeriv4 {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    iteratedDeriv 4 (fun s => dtilde X s a) r
      = 3 * dtilde X r a * (dtilde X r a + a)
          * (35 * a ^ 6 + 362 * a ^ 5 * dtilde X r a + 1650 * a ^ 4 * dtilde X r a ^ 2
             + 4136 * a ^ 3 * dtilde X r a ^ 3 + 5968 * a ^ 2 * dtilde X r a ^ 4
             + 4680 * a * dtilde X r a ^ 5 + 1560 * dtilde X r a ^ 6)
        / (16 * r ^ 4 * (a + 2 * dtilde X r a) ^ 7) := by
  have hL : iteratedDeriv 4 (fun s => dtilde X s a) r
      = deriv (iteratedDeriv 3 (fun s => dtilde X s a)) r := by
    rw [iteratedDeriv_succ]
  rw [hL]
  -- `iteratedDeriv 3 d̃ =ᶠ[nhds r] dtil3 X a ·` on the open set `{s | 0 < s}`
  have hee : iteratedDeriv 3 (fun s => dtilde X s a) =ᶠ[nhds r] (fun s => dtil3 X a s) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hr) ?_
    intro s hs
    have hs' : 0 < s := hs
    rw [dtilde_r_iteratedDeriv3 hX ha hs']
    simp only [dtil3]
  rw [hee.deriv_eq]
  exact (dtil3_hasDerivAt hX ha hr).deriv

/-- **`d̃ₐ'''` is differentiable with derivative `d̃ₐ''''`.**  I.e. `s ↦ iteratedDeriv 3 d̃ₐ s`
has derivative `iteratedDeriv 4 d̃ₐ s` at `s > 0`.  Companion of `dtilde_iteratedDeriv2_hasDerivAt`,
needed for the §5 Step-2 curvature finite-difference (`ε₃`) bound. -/
theorem dtilde_iteratedDeriv3_hasDerivAt {X a s : ℝ} (hX : 0 < X) (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun t => iteratedDeriv 3 (fun u => dtilde X u a) t)
      (iteratedDeriv 4 (fun u => dtilde X u a) s) s := by
  have hee : iteratedDeriv 3 (fun u => dtilde X u a) =ᶠ[nhds s] (fun t => dtil3 X a t) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hs) ?_
    intro t ht
    have ht' : 0 < t := ht
    rw [dtilde_r_iteratedDeriv3 hX ha ht']
    simp only [dtil3]
  rw [dtilde_r_iteratedDeriv4 hX ha hs]
  exact (dtil3_hasDerivAt hX ha hs).congr_of_eventuallyEq hee

/-- **`|d̃''''(r)| ≤ C₄·D/R⁴`.**  In the §5 regime, the fourth `r`-derivative of `d̃ₐ` is
bounded in absolute value by `2·10²⁵·(D/R⁴)`. -/
theorem dtilde_d4_upper {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    |iteratedDeriv 4 (fun s => dtilde P.X s a) r|
      ≤ 20000000000000000000000000 * (S.D / S.R ^ 4) := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  -- the defect-inverse window
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  set d := dtilde P.X r a with hd_def
  have ha_hiD : a ≤ (11/10) * S.D := by linarith
  -- closed form of the fourth derivative
  rw [dtilde_r_iteratedDeriv4 P.X_pos ha0 hr0]
  -- abbreviations
  set Poly := 35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
      + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6 with hPoly_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  set Num4 := 3 * d * (d + a) * Poly with hNum4_def
  set Den4 := 16 * r ^ 4 * (a + 2 * d) ^ 7 with hDen4_def
  have hNum4_pos : 0 < Num4 := by rw [hNum4_def]; positivity
  have hDen4_pos : 0 < Den4 := by rw [hDen4_def]; positivity
  -- the closed form is positive, so its abs is `Num4 / Den4`
  have habs : |(3 * d * (d + a) * Poly / Den4)| = Num4 / Den4 := by
    rw [abs_of_pos (show (0:ℝ) < 3 * d * (d + a) * Poly / Den4 by
      rw [hDen4_def]; positivity)]
  have hmatch : (3 * d * (d + a)
        * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
           + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
        / (16 * r ^ 4 * (a + 2 * d) ^ 7))
      = 3 * d * (d + a) * Poly / Den4 := by
    rw [hPoly_def, hDen4_def]
  rw [hmatch, habs]
  -- numerator upper bound: `Num4 ≤ 8·10¹³ · D⁸`
  have hf1 : 3 * d * (d + a) ≤ 1080 * S.D ^ 2 := by
    nlinarith [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  have hf2 : Poly ≤ 70000000000 * S.D ^ 6 := by
    rw [hPoly_def]
    have hp1 : 35 * a ^ 6 ≤ 35 * ((11/10) * S.D) ^ 6 := by
      have := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 6; nlinarith [this]
    have hp2 : 362 * a ^ 5 * d ≤ 362 * ((11/10) * S.D) ^ 5 * (18 * S.D) := by
      have h5 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 5
      have := mul_le_mul h5 hd_hi (by positivity) (by positivity)
      nlinarith [this]
    have hp3 : 1650 * a ^ 4 * d ^ 2 ≤ 1650 * ((11/10) * S.D) ^ 4 * (18 * S.D) ^ 2 := by
      have h4 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 4
      have hd2 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 2
      have := mul_le_mul h4 hd2 (by positivity) (by positivity)
      nlinarith [this]
    have hp4 : 4136 * a ^ 3 * d ^ 3 ≤ 4136 * ((11/10) * S.D) ^ 3 * (18 * S.D) ^ 3 := by
      have h3 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 3
      have hd3 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 3
      have := mul_le_mul h3 hd3 (by positivity) (by positivity)
      nlinarith [this]
    have hp5 : 5968 * a ^ 2 * d ^ 4 ≤ 5968 * ((11/10) * S.D) ^ 2 * (18 * S.D) ^ 4 := by
      have h2 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 2
      have hd4 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 4
      have := mul_le_mul h2 hd4 (by positivity) (by positivity)
      nlinarith [this]
    have hp6 : 4680 * a * d ^ 5 ≤ 4680 * ((11/10) * S.D) * (18 * S.D) ^ 5 := by
      have hd5 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 5
      have := mul_le_mul ha_hiD hd5 (by positivity) (by positivity)
      nlinarith [this]
    have hp7 : 1560 * d ^ 6 ≤ 1560 * (18 * S.D) ^ 6 := by
      have := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 6; nlinarith [this]
    nlinarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, pow_pos hDpos 6]
  have hNum4_hi : Num4 ≤ 80000000000000 * S.D ^ 8 := by
    rw [hNum4_def]
    have hmul := mul_le_mul hf1 hf2 (le_of_lt hPoly_pos) (by positivity)
    calc 3 * d * (d + a) * Poly
        ≤ (1080 * S.D ^ 2) * (70000000000 * S.D ^ 6) := hmul
      _ ≤ 80000000000000 * S.D ^ 8 := by nlinarith [pow_pos hDpos 8]
  -- denominator lower bound: `Den4 ≥ R⁴ D⁷ / 2·10¹¹`
  have hr4_lo : S.R ^ 4 / 26873856 ≤ r ^ 4 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (1/72) * S.R) hr_lo 4
    calc S.R ^ 4 / 26873856 = ((1/72) * S.R) ^ 4 := by ring
      _ ≤ r ^ 4 := this
  have h2d_lo : S.D / 5 ≤ a + 2 * d := by linarith
  have hpow7_lo : S.D ^ 7 / 78125 ≤ (a + 2 * d) ^ 7 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 5) h2d_lo 7
    calc S.D ^ 7 / 78125 = (S.D / 5) ^ 7 := by ring
      _ ≤ (a + 2 * d) ^ 7 := this
  have hDen4_lo : S.R ^ 4 * S.D ^ 7 / 200000000000 ≤ Den4 := by
    rw [hDen4_def]
    have hmul := mul_le_mul hr4_lo hpow7_lo (by positivity) (by positivity)
    calc S.R ^ 4 * S.D ^ 7 / 200000000000
        ≤ 16 * ((S.R ^ 4 / 26873856) * (S.D ^ 7 / 78125)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith [mul_pos (pow_pos hRpos 4) (pow_pos hDpos 7)]
      _ ≤ 16 * (r ^ 4 * (a + 2 * d) ^ 7) := by nlinarith [hmul]
      _ = 16 * r ^ 4 * (a + 2 * d) ^ 7 := by ring
  -- combine
  rw [div_le_iff₀ hDen4_pos]
  have hstep : 20000000000000000000000000 * (S.D / S.R ^ 4)
        * (S.R ^ 4 * S.D ^ 7 / 200000000000)
      ≤ 20000000000000000000000000 * (S.D / S.R ^ 4) * Den4 :=
    mul_le_mul_of_nonneg_left hDen4_lo (by positivity)
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have heq : 20000000000000000000000000 * (S.D / S.R ^ 4)
        * (S.R ^ 4 * S.D ^ 7 / 200000000000)
      = 100000000000000 * S.D ^ 8 := by field_simp; ring
  have hle : (80000000000000 : ℝ) * S.D ^ 8 ≤ 100000000000000 * S.D ^ 8 := by
    nlinarith [pow_pos hDpos 8]
  calc Num4 ≤ 80000000000000 * S.D ^ 8 := hNum4_hi
    _ ≤ 100000000000000 * S.D ^ 8 := hle
    _ = 20000000000000000000000000 * (S.D / S.R ^ 4)
          * (S.R ^ 4 * S.D ^ 7 / 200000000000) := by rw [heq]
    _ ≤ 20000000000000000000000000 * (S.D / S.R ^ 4) * Den4 := hstep

end Squarefree
