import Squarefree.Lower.DefectDeriv4

/-!
# §5 derivative calculus: the 5th `r`-derivative of `d̃ₐ(r)`

Extends the `d̃ₐ` derivative tower (`DefectDeriv`, `DefectDeriv4`) by one more order.  From the
closed form of `d̃ₐ''''` and the chain rule `d̃ₐ'(r) = − d̃(d̃+a)/(2 r (a + 2 d̃))` we obtain

  `d̃ₐ⁽⁵⁾(r) = − 15 d̃(d̃+a)(63a⁸ + 878a⁷d̃ + 5594a⁶d̃² + 20904a⁵d̃³ + 49740a⁴d̃⁴
                + 76848a³d̃⁵ + 75120a²d̃⁶ + 42432a d̃⁷ + 10608 d̃⁸)
                / (32 r⁵ (a + 2 d̃)⁹)`   (sympy-verified; negative),

together with the scale bound `|d̃⁽⁵⁾(r)| ≤ C₅ · D/R⁵` on the §5 band window.  This is the
gating prerequisite for the §5 Step-2 φ″-zero count.  We do *not* edit `DefectDeriv.lean` or
`DefectDeriv4.lean`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 4000000

/-- The fourth-derivative function `d̃ₐ''''(s)` as a closed-form expression (matches the RHS of
`dtilde_r_iteratedDeriv4` with `s` in place of `r`). -/
private noncomputable def dtil4 (X a s : ℝ) : ℝ :=
  3 * dtilde X s a * (dtilde X s a + a)
    * (35 * a ^ 6 + 362 * a ^ 5 * dtilde X s a + 1650 * a ^ 4 * dtilde X s a ^ 2
       + 4136 * a ^ 3 * dtilde X s a ^ 3 + 5968 * a ^ 2 * dtilde X s a ^ 4
       + 4680 * a * dtilde X s a ^ 5 + 1560 * dtilde X s a ^ 6)
  / (16 * s ^ 4 * (a + 2 * dtilde X s a) ^ 7)

/-- **The derivative of the closed form `d̃ₐ''''` (i.e. `d̃ₐ⁽⁵⁾` pointwise).**

  `d̃ₐ⁽⁵⁾(r) = − 15 d̃(d̃+a)(63a⁸ + 878a⁷d̃ + 5594a⁶d̃² + 20904a⁵d̃³ + 49740a⁴d̃⁴
                + 76848a³d̃⁵ + 75120a²d̃⁶ + 42432a d̃⁷ + 10608 d̃⁸) / (32 r⁵ (a + 2 d̃)⁹)`.

(sympy-verified by differentiating the `d̃''''` closed form under `d̃' = −d̃(d̃+a)/(2r(a+2d̃))`,
then `factor`.) -/
theorem dtil4_hasDerivAt {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun s => dtil4 X a s)
      ( -15 * dtilde X r a * (dtilde X r a + a)
          * (63 * a ^ 8 + 878 * a ^ 7 * dtilde X r a + 5594 * a ^ 6 * dtilde X r a ^ 2
             + 20904 * a ^ 5 * dtilde X r a ^ 3 + 49740 * a ^ 4 * dtilde X r a ^ 4
             + 76848 * a ^ 3 * dtilde X r a ^ 5 + 75120 * a ^ 2 * dtilde X r a ^ 6
             + 42432 * a * dtilde X r a ^ 7 + 10608 * dtilde X r a ^ 8)
        / (32 * r ^ 5 * (a + 2 * dtilde X r a) ^ 9) ) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have hda2 : 0 < a + 2 * d := by linarith
  -- inner derivative `d̃'(r) = −d̃(d̃+a)/(2r(a+2d̃))`
  have hD : HasDerivAt (fun s => dtilde X s a) (- d * (d + a) / (2 * r * (a + 2 * d))) r :=
    dtilde_r_hasDerivAt hX ha hr
  set D' := - d * (d + a) / (2 * r * (a + 2 * d)) with hD'_def
  -- numerator first factor: `3 d̃ (d̃+a)`
  have hP4 : HasDerivAt (fun s => 3 * dtilde X s a * (dtilde X s a + a))
      ((3 * D') * (d + a) + (3 * d) * D') r :=
    (hD.const_mul 3).mul (hD.add_const a)
  -- the degree-6 polynomial factor
  have hQ6 : HasDerivAt
      (fun s => 35 * a ^ 6 + 362 * a ^ 5 * dtilde X s a + 1650 * a ^ 4 * dtilde X s a ^ 2
         + 4136 * a ^ 3 * dtilde X s a ^ 3 + 5968 * a ^ 2 * dtilde X s a ^ 4
         + 4680 * a * dtilde X s a ^ 5 + 1560 * dtilde X s a ^ 6)
      (362 * a ^ 5 * D' + 1650 * a ^ 4 * (2 * d * D') + 4136 * a ^ 3 * (3 * d ^ 2 * D')
         + 5968 * a ^ 2 * (4 * d ^ 3 * D') + 4680 * a * (5 * d ^ 4 * D')
         + 1560 * (6 * d ^ 5 * D')) r := by
    have h1 : HasDerivAt (fun s => 362 * a ^ 5 * dtilde X s a) (362 * a ^ 5 * D') r := by
      have := hD.const_mul (362 * a ^ 5); simpa [mul_assoc] using this
    have h2 : HasDerivAt (fun s => 1650 * a ^ 4 * dtilde X s a ^ 2)
        (1650 * a ^ 4 * (2 * d * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 2) (2 * d * D') r := by
        have := hD.pow 2; simpa using this
      have := hpow.const_mul (1650 * a ^ 4); simpa [mul_assoc] using this
    have h3 : HasDerivAt (fun s => 4136 * a ^ 3 * dtilde X s a ^ 3)
        (4136 * a ^ 3 * (3 * d ^ 2 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 3) (3 * d ^ 2 * D') r := by
        have := hD.pow 3; simpa using this
      have := hpow.const_mul (4136 * a ^ 3); simpa [mul_assoc] using this
    have h4 : HasDerivAt (fun s => 5968 * a ^ 2 * dtilde X s a ^ 4)
        (5968 * a ^ 2 * (4 * d ^ 3 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 4) (4 * d ^ 3 * D') r := by
        have := hD.pow 4; simpa using this
      have := hpow.const_mul (5968 * a ^ 2); simpa [mul_assoc] using this
    have h5 : HasDerivAt (fun s => 4680 * a * dtilde X s a ^ 5)
        (4680 * a * (5 * d ^ 4 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 5) (5 * d ^ 4 * D') r := by
        have := hD.pow 5; simpa using this
      have := hpow.const_mul (4680 * a); simpa [mul_assoc] using this
    have h6 : HasDerivAt (fun s => 1560 * dtilde X s a ^ 6) (1560 * (6 * d ^ 5 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 6) (6 * d ^ 5 * D') r := by
        have := hD.pow 6; simpa using this
      have := hpow.const_mul 1560; simpa using this
    have := ((((((hasDerivAt_const r (35 * a ^ 6)).add h1).add h2).add h3).add h4).add h5).add h6
    convert this using 1
    ring
  -- full numerator
  have hN : HasDerivAt
      (fun s => 3 * dtilde X s a * (dtilde X s a + a)
        * (35 * a ^ 6 + 362 * a ^ 5 * dtilde X s a + 1650 * a ^ 4 * dtilde X s a ^ 2
           + 4136 * a ^ 3 * dtilde X s a ^ 3 + 5968 * a ^ 2 * dtilde X s a ^ 4
           + 4680 * a * dtilde X s a ^ 5 + 1560 * dtilde X s a ^ 6))
      ( ((3 * D') * (d + a) + (3 * d) * D')
          * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
             + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
        + (3 * d * (d + a))
          * (362 * a ^ 5 * D' + 1650 * a ^ 4 * (2 * d * D') + 4136 * a ^ 3 * (3 * d ^ 2 * D')
             + 5968 * a ^ 2 * (4 * d ^ 3 * D') + 4680 * a * (5 * d ^ 4 * D')
             + 1560 * (6 * d ^ 5 * D')) ) r :=
    hP4.mul hQ6
  -- denominator `16 s⁴ (a + 2 d̃)⁷`
  have hMid : HasDerivAt (fun s => (16:ℝ) * s ^ 4) (16 * (4 * r ^ 3)) r := by
    have := (hasDerivAt_pow 4 r).const_mul 16; simpa using this
  have hMin : HasDerivAt (fun s => (a + 2 * dtilde X s a) ^ 7)
      (7 * (a + 2 * d) ^ 6 * (2 * D')) r := by
    have hbase : HasDerivAt (fun s => a + 2 * dtilde X s a) (2 * D') r :=
      (hD.const_mul 2).const_add a
    have := hbase.pow 7; simpa using this
  have hM : HasDerivAt (fun s => (16:ℝ) * s ^ 4 * (a + 2 * dtilde X s a) ^ 7)
      ((16 * (4 * r ^ 3)) * (a + 2 * d) ^ 7
        + (16 * r ^ 4) * (7 * (a + 2 * d) ^ 6 * (2 * D'))) r :=
    hMid.mul hMin
  have hMne : (16:ℝ) * r ^ 4 * (a + 2 * d) ^ 7 ≠ 0 := by positivity
  -- quotient rule (raw value)
  have hderiv : HasDerivAt (fun s => dtil4 X a s)
      ( ( ( ((3 * D') * (d + a) + (3 * d) * D')
              * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
                 + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
            + (3 * d * (d + a))
              * (362 * a ^ 5 * D' + 1650 * a ^ 4 * (2 * d * D') + 4136 * a ^ 3 * (3 * d ^ 2 * D')
                 + 5968 * a ^ 2 * (4 * d ^ 3 * D') + 4680 * a * (5 * d ^ 4 * D')
                 + 1560 * (6 * d ^ 5 * D')))
            * ((16:ℝ) * r ^ 4 * (a + 2 * d) ^ 7)
          - (3 * d * (d + a)
              * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
                 + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6))
            * ((16 * (4 * r ^ 3)) * (a + 2 * d) ^ 7
               + (16 * r ^ 4) * (7 * (a + 2 * d) ^ 6 * (2 * D'))) )
        / ((16:ℝ) * r ^ 4 * (a + 2 * d) ^ 7) ^ 2 ) r := by
    have := hN.div hM hMne
    convert this using 1
  -- substitute `D'` and simplify to the target closed form
  have hval : ( ( ((3 * D') * (d + a) + (3 * d) * D')
              * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
                 + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
            + (3 * d * (d + a))
              * (362 * a ^ 5 * D' + 1650 * a ^ 4 * (2 * d * D') + 4136 * a ^ 3 * (3 * d ^ 2 * D')
                 + 5968 * a ^ 2 * (4 * d ^ 3 * D') + 4680 * a * (5 * d ^ 4 * D')
                 + 1560 * (6 * d ^ 5 * D')))
            * ((16:ℝ) * r ^ 4 * (a + 2 * d) ^ 7)
          - (3 * d * (d + a)
              * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
                 + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6))
            * ((16 * (4 * r ^ 3)) * (a + 2 * d) ^ 7
               + (16 * r ^ 4) * (7 * (a + 2 * d) ^ 6 * (2 * D'))) )
        / ((16:ℝ) * r ^ 4 * (a + 2 * d) ^ 7) ^ 2
      = -15 * d * (d + a)
          * (63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
             + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
             + 42432 * a * d ^ 7 + 10608 * d ^ 8)
        / (32 * r ^ 5 * (a + 2 * d) ^ 9) := by
    rw [hD'_def]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hda2' : a + 2 * d ≠ 0 := ne_of_gt hda2
    field_simp
    ring
  rw [hval] at hderiv
  exact hderiv

/-- **The fifth `r`-derivative of `d̃ₐ` as an `iteratedDeriv`.** -/
theorem dtilde_r_iteratedDeriv5 {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    iteratedDeriv 5 (fun s => dtilde X s a) r
      = -15 * dtilde X r a * (dtilde X r a + a)
          * (63 * a ^ 8 + 878 * a ^ 7 * dtilde X r a + 5594 * a ^ 6 * dtilde X r a ^ 2
             + 20904 * a ^ 5 * dtilde X r a ^ 3 + 49740 * a ^ 4 * dtilde X r a ^ 4
             + 76848 * a ^ 3 * dtilde X r a ^ 5 + 75120 * a ^ 2 * dtilde X r a ^ 6
             + 42432 * a * dtilde X r a ^ 7 + 10608 * dtilde X r a ^ 8)
        / (32 * r ^ 5 * (a + 2 * dtilde X r a) ^ 9) := by
  have hL : iteratedDeriv 5 (fun s => dtilde X s a) r
      = deriv (iteratedDeriv 4 (fun s => dtilde X s a)) r := by
    rw [iteratedDeriv_succ]
  rw [hL]
  -- `iteratedDeriv 4 d̃ =ᶠ[nhds r] dtil4 X a ·` on the open set `{s | 0 < s}`
  have hee : iteratedDeriv 4 (fun s => dtilde X s a) =ᶠ[nhds r] (fun s => dtil4 X a s) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hr) ?_
    intro s hs
    have hs' : 0 < s := hs
    rw [dtilde_r_iteratedDeriv4 hX ha hs']
    simp only [dtil4]
  rw [hee.deriv_eq]
  exact (dtil4_hasDerivAt hX ha hr).deriv

/-- **`d̃ₐ''''` is differentiable with derivative `d̃ₐ⁽⁵⁾`.**  I.e. `s ↦ iteratedDeriv 4 d̃ₐ s`
has derivative `iteratedDeriv 5 d̃ₐ s` at `s > 0`.  Companion of `dtilde_iteratedDeriv3_hasDerivAt`,
needed for the §5 Step-2 φ″-zero count finite-difference bound. -/
theorem dtilde_iteratedDeriv4_hasDerivAt {X a s : ℝ} (hX : 0 < X) (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun t => iteratedDeriv 4 (fun u => dtilde X u a) t)
      (iteratedDeriv 5 (fun u => dtilde X u a) s) s := by
  have hee : iteratedDeriv 4 (fun u => dtilde X u a) =ᶠ[nhds s] (fun t => dtil4 X a t) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hs) ?_
    intro t ht
    have ht' : 0 < t := ht
    rw [dtilde_r_iteratedDeriv4 hX ha ht']
    simp only [dtil4]
  rw [dtilde_r_iteratedDeriv5 hX ha hs]
  exact (dtil4_hasDerivAt hX ha hs).congr_of_eventuallyEq hee

/-- **`|d̃⁽⁵⁾(r)| ≤ C₅·D/R⁵`.**  In the §5 regime, the fifth `r`-derivative of `d̃ₐ` is
bounded in absolute value by `(1.18098·10³²)·(D/R⁵)`. -/
theorem dtilde_d5_upper {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    |iteratedDeriv 5 (fun s => dtilde P.X s a) r|
      ≤ 118098000000000000000000000000000 * (S.D / S.R ^ 5) := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  -- the defect-inverse window
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  rw [dtilde_r_iteratedDeriv5 P.X_pos ha0 hr0]
  set d := dtilde P.X r a with hd_def
  have ha_hiD : a ≤ (11/10) * S.D := by linarith
  -- abbreviations
  set Poly := 63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
      + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
      + 42432 * a * d ^ 7 + 10608 * d ^ 8 with hPoly_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  set Num5 := 15 * d * (d + a) * Poly with hNum5_def
  set Den5 := 32 * r ^ 5 * (a + 2 * d) ^ 9 with hDen5_def
  have hNum5_pos : 0 < Num5 := by rw [hNum5_def]; positivity
  have hDen5_pos : 0 < Den5 := by rw [hDen5_def]; positivity
  -- the closed form is `−(Num5/Den5) < 0`, so its abs is `Num5 / Den5`
  have hmatch : (-15 * d * (d + a) * Poly / Den5) = -(Num5 / Den5) := by
    rw [hNum5_def]; ring
  rw [hmatch, abs_neg, abs_of_pos (div_pos hNum5_pos hDen5_pos)]
  -- numerator upper bound: `Num5 ≤ 7.8·10¹⁷ · D¹⁰`
  have hf1 : 15 * d * (d + a) ≤ 5200 * S.D ^ 2 := by
    nlinarith [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  have hf2 : Poly ≤ 150000000000000 * S.D ^ 8 := by
    rw [hPoly_def]
    have hp1 : 63 * a ^ 8 ≤ 63 * ((11/10) * S.D) ^ 8 := by
      have := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 8; nlinarith [this]
    have hp2 : 878 * a ^ 7 * d ≤ 878 * ((11/10) * S.D) ^ 7 * (18 * S.D) := by
      have h7 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 7
      have := mul_le_mul h7 hd_hi (by positivity) (by positivity)
      nlinarith [this]
    have hp3 : 5594 * a ^ 6 * d ^ 2 ≤ 5594 * ((11/10) * S.D) ^ 6 * (18 * S.D) ^ 2 := by
      have h6 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 6
      have hd2 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 2
      have := mul_le_mul h6 hd2 (by positivity) (by positivity)
      nlinarith [this]
    have hp4 : 20904 * a ^ 5 * d ^ 3 ≤ 20904 * ((11/10) * S.D) ^ 5 * (18 * S.D) ^ 3 := by
      have h5 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 5
      have hd3 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 3
      have := mul_le_mul h5 hd3 (by positivity) (by positivity)
      nlinarith [this]
    have hp5 : 49740 * a ^ 4 * d ^ 4 ≤ 49740 * ((11/10) * S.D) ^ 4 * (18 * S.D) ^ 4 := by
      have h4 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 4
      have hd4 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 4
      have := mul_le_mul h4 hd4 (by positivity) (by positivity)
      nlinarith [this]
    have hp6 : 76848 * a ^ 3 * d ^ 5 ≤ 76848 * ((11/10) * S.D) ^ 3 * (18 * S.D) ^ 5 := by
      have h3 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 3
      have hd5 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 5
      have := mul_le_mul h3 hd5 (by positivity) (by positivity)
      nlinarith [this]
    have hp7 : 75120 * a ^ 2 * d ^ 6 ≤ 75120 * ((11/10) * S.D) ^ 2 * (18 * S.D) ^ 6 := by
      have h2 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 2
      have hd6 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 6
      have := mul_le_mul h2 hd6 (by positivity) (by positivity)
      nlinarith [this]
    have hp8 : 42432 * a * d ^ 7 ≤ 42432 * ((11/10) * S.D) * (18 * S.D) ^ 7 := by
      have hd7 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 7
      have := mul_le_mul ha_hiD hd7 (by positivity) (by positivity)
      nlinarith [this]
    have hp9 : 10608 * d ^ 8 ≤ 10608 * (18 * S.D) ^ 8 := by
      have := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 8; nlinarith [this]
    nlinarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, pow_pos hDpos 8]
  have hNum5_hi : Num5 ≤ 780000000000000000 * S.D ^ 10 := by
    rw [hNum5_def]
    have hmul := mul_le_mul hf1 hf2 (le_of_lt hPoly_pos) (by positivity)
    calc 15 * d * (d + a) * Poly
        ≤ (5200 * S.D ^ 2) * (150000000000000 * S.D ^ 8) := hmul
      _ ≤ 780000000000000000 * S.D ^ 10 := by nlinarith [pow_pos hDpos 10]
  -- denominator lower bound: `Den5 ≥ R⁵ D⁹ / 1.18098·10¹⁴`
  have hr5_lo : S.R ^ 5 / 1934917632 ≤ r ^ 5 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (1/72) * S.R) hr_lo 5
    calc S.R ^ 5 / 1934917632 = ((1/72) * S.R) ^ 5 := by ring
      _ ≤ r ^ 5 := this
  have h2d_lo : S.D / 5 ≤ a + 2 * d := by linarith
  have hpow9_lo : S.D ^ 9 / 1953125 ≤ (a + 2 * d) ^ 9 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 5) h2d_lo 9
    calc S.D ^ 9 / 1953125 = (S.D / 5) ^ 9 := by ring
      _ ≤ (a + 2 * d) ^ 9 := this
  have hDen5_lo : S.R ^ 5 * S.D ^ 9 / 118098000000000 ≤ Den5 := by
    rw [hDen5_def]
    have hmul := mul_le_mul hr5_lo hpow9_lo (by positivity) (by positivity)
    calc S.R ^ 5 * S.D ^ 9 / 118098000000000
        ≤ 32 * ((S.R ^ 5 / 1934917632) * (S.D ^ 9 / 1953125)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith [mul_pos (pow_pos hRpos 5) (pow_pos hDpos 9)]
      _ ≤ 32 * (r ^ 5 * (a + 2 * d) ^ 9) := by nlinarith [hmul]
      _ = 32 * r ^ 5 * (a + 2 * d) ^ 9 := by ring
  -- combine
  rw [div_le_iff₀ hDen5_pos]
  have hstep : 118098000000000000000000000000000 * (S.D / S.R ^ 5)
        * (S.R ^ 5 * S.D ^ 9 / 118098000000000)
      ≤ 118098000000000000000000000000000 * (S.D / S.R ^ 5) * Den5 :=
    mul_le_mul_of_nonneg_left hDen5_lo (by positivity)
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have heq : 118098000000000000000000000000000 * (S.D / S.R ^ 5)
        * (S.R ^ 5 * S.D ^ 9 / 118098000000000)
      = 1000000000000000000 * S.D ^ 10 := by field_simp; ring
  have hle : (780000000000000000 : ℝ) * S.D ^ 10 ≤ 1000000000000000000 * S.D ^ 10 := by
    nlinarith [pow_pos hDpos 10]
  calc Num5 ≤ 780000000000000000 * S.D ^ 10 := hNum5_hi
    _ ≤ 1000000000000000000 * S.D ^ 10 := hle
    _ = 118098000000000000000000000000000 * (S.D / S.R ^ 5)
          * (S.R ^ 5 * S.D ^ 9 / 118098000000000) := by rw [heq]
    _ ≤ 118098000000000000000000000000000 * (S.D / S.R ^ 5) * Den5 := hstep

end Squarefree
