import Squarefree.Lower.DefectDeriv5

/-!
# §5 derivative calculus: the 6th `r`-derivative of `d̃ₐ(r)`

Extends the `d̃ₐ` derivative tower (`DefectDeriv`, `DefectDeriv4`, `DefectDeriv5`) by one more
order.  From the closed form of `d̃ₐ⁽⁵⁾` and the chain rule
`d̃ₐ'(r) = − d̃(d̃+a)/(2 r (a + 2 d̃))` we obtain

  `d̃ₐ⁽⁶⁾(r) = 45 d̃(d̃+a)(231a¹⁰ + 4058a⁹d̃ + 33274a⁸d̃² + 165416a⁷d̃³ + 548520a⁶d̃⁴
                + 1262872a⁵d̃⁵ + 2039656a⁴d̃⁶ + 2278528a³d̃⁷ + 1683472a²d̃⁸
                + 742560a d̃⁹ + 148512 d̃¹⁰) / (64 r⁶ (a + 2 d̃)¹¹)`  (sympy-verified; positive),

together with the scale bound `|d̃⁽⁶⁾(r)| ≤ C₆ · D/R⁶` on the §5 band window.  We do *not* edit
`DefectDeriv.lean`, `DefectDeriv4.lean`, or `DefectDeriv5.lean`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 400000

/-- The fifth-derivative function `d̃ₐ⁽⁵⁾(s)` as a closed-form expression (matches the RHS of
`dtilde_r_iteratedDeriv5` with `s` in place of `r`). -/
private noncomputable def dtil5 (X a s : ℝ) : ℝ :=
  -15 * dtilde X s a * (dtilde X s a + a)
    * (63 * a ^ 8 + 878 * a ^ 7 * dtilde X s a + 5594 * a ^ 6 * dtilde X s a ^ 2
       + 20904 * a ^ 5 * dtilde X s a ^ 3 + 49740 * a ^ 4 * dtilde X s a ^ 4
       + 76848 * a ^ 3 * dtilde X s a ^ 5 + 75120 * a ^ 2 * dtilde X s a ^ 6
       + 42432 * a * dtilde X s a ^ 7 + 10608 * dtilde X s a ^ 8)
  / (32 * s ^ 5 * (a + 2 * dtilde X s a) ^ 9)

/-- **The derivative of the closed form `d̃ₐ⁽⁵⁾` (i.e. `d̃ₐ⁽⁶⁾` pointwise).**

  `d̃ₐ⁽⁶⁾(r) = 45 d̃(d̃+a)(231a¹⁰ + 4058a⁹d̃ + 33274a⁸d̃² + 165416a⁷d̃³ + 548520a⁶d̃⁴
                + 1262872a⁵d̃⁵ + 2039656a⁴d̃⁶ + 2278528a³d̃⁷ + 1683472a²d̃⁸
                + 742560a d̃⁹ + 148512 d̃¹⁰) / (64 r⁶ (a + 2 d̃)¹¹)`.

(sympy-verified by differentiating the `d̃⁽⁵⁾` closed form under `d̃' = −d̃(d̃+a)/(2r(a+2d̃))`,
then `factor`.) -/
theorem dtil5_hasDerivAt {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun s => dtil5 X a s)
      ( 45 * dtilde X r a * (dtilde X r a + a)
          * (231 * a ^ 10 + 4058 * a ^ 9 * dtilde X r a + 33274 * a ^ 8 * dtilde X r a ^ 2
             + 165416 * a ^ 7 * dtilde X r a ^ 3 + 548520 * a ^ 6 * dtilde X r a ^ 4
             + 1262872 * a ^ 5 * dtilde X r a ^ 5 + 2039656 * a ^ 4 * dtilde X r a ^ 6
             + 2278528 * a ^ 3 * dtilde X r a ^ 7 + 1683472 * a ^ 2 * dtilde X r a ^ 8
             + 742560 * a * dtilde X r a ^ 9 + 148512 * dtilde X r a ^ 10)
        / (64 * r ^ 6 * (a + 2 * dtilde X r a) ^ 11) ) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have hda2 : 0 < a + 2 * d := by linarith
  -- inner derivative `d̃'(r) = −d̃(d̃+a)/(2r(a+2d̃))`
  have hD : HasDerivAt (fun s => dtilde X s a) (- d * (d + a) / (2 * r * (a + 2 * d))) r :=
    dtilde_r_hasDerivAt hX ha hr
  set D' := - d * (d + a) / (2 * r * (a + 2 * d)) with hD'_def
  -- numerator first factor: `-15 d̃ (d̃+a)`
  have hP5 : HasDerivAt (fun s => -15 * dtilde X s a * (dtilde X s a + a))
      ((-15 * D') * (d + a) + (-15 * d) * D') r :=
    (hD.const_mul (-15)).mul (hD.add_const a)
  -- the degree-8 polynomial factor
  have hQ8 : HasDerivAt
      (fun s => 63 * a ^ 8 + 878 * a ^ 7 * dtilde X s a + 5594 * a ^ 6 * dtilde X s a ^ 2
         + 20904 * a ^ 5 * dtilde X s a ^ 3 + 49740 * a ^ 4 * dtilde X s a ^ 4
         + 76848 * a ^ 3 * dtilde X s a ^ 5 + 75120 * a ^ 2 * dtilde X s a ^ 6
         + 42432 * a * dtilde X s a ^ 7 + 10608 * dtilde X s a ^ 8)
      (878 * a ^ 7 * D' + 5594 * a ^ 6 * (2 * d * D') + 20904 * a ^ 5 * (3 * d ^ 2 * D')
         + 49740 * a ^ 4 * (4 * d ^ 3 * D') + 76848 * a ^ 3 * (5 * d ^ 4 * D')
         + 75120 * a ^ 2 * (6 * d ^ 5 * D') + 42432 * a * (7 * d ^ 6 * D')
         + 10608 * (8 * d ^ 7 * D')) r := by
    have h1 : HasDerivAt (fun s => 878 * a ^ 7 * dtilde X s a) (878 * a ^ 7 * D') r := by
      have := hD.const_mul (878 * a ^ 7); simpa [mul_assoc] using this
    have h2 : HasDerivAt (fun s => 5594 * a ^ 6 * dtilde X s a ^ 2)
        (5594 * a ^ 6 * (2 * d * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 2) (2 * d * D') r := by
        have := hD.pow 2; simpa using this
      have := hpow.const_mul (5594 * a ^ 6); simpa [mul_assoc] using this
    have h3 : HasDerivAt (fun s => 20904 * a ^ 5 * dtilde X s a ^ 3)
        (20904 * a ^ 5 * (3 * d ^ 2 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 3) (3 * d ^ 2 * D') r := by
        have := hD.pow 3; simpa using this
      have := hpow.const_mul (20904 * a ^ 5); simpa [mul_assoc] using this
    have h4 : HasDerivAt (fun s => 49740 * a ^ 4 * dtilde X s a ^ 4)
        (49740 * a ^ 4 * (4 * d ^ 3 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 4) (4 * d ^ 3 * D') r := by
        have := hD.pow 4; simpa using this
      have := hpow.const_mul (49740 * a ^ 4); simpa [mul_assoc] using this
    have h5 : HasDerivAt (fun s => 76848 * a ^ 3 * dtilde X s a ^ 5)
        (76848 * a ^ 3 * (5 * d ^ 4 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 5) (5 * d ^ 4 * D') r := by
        have := hD.pow 5; simpa using this
      have := hpow.const_mul (76848 * a ^ 3); simpa [mul_assoc] using this
    have h6 : HasDerivAt (fun s => 75120 * a ^ 2 * dtilde X s a ^ 6)
        (75120 * a ^ 2 * (6 * d ^ 5 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 6) (6 * d ^ 5 * D') r := by
        have := hD.pow 6; simpa using this
      have := hpow.const_mul (75120 * a ^ 2); simpa [mul_assoc] using this
    have h7 : HasDerivAt (fun s => 42432 * a * dtilde X s a ^ 7)
        (42432 * a * (7 * d ^ 6 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 7) (7 * d ^ 6 * D') r := by
        have := hD.pow 7; simpa using this
      have := hpow.const_mul (42432 * a); simpa [mul_assoc] using this
    have h8 : HasDerivAt (fun s => 10608 * dtilde X s a ^ 8) (10608 * (8 * d ^ 7 * D')) r := by
      have hpow : HasDerivAt (fun s => dtilde X s a ^ 8) (8 * d ^ 7 * D') r := by
        have := hD.pow 8; simpa using this
      have := hpow.const_mul 10608; simpa using this
    have := ((((((((hasDerivAt_const r (63 * a ^ 8)).add h1).add h2).add h3).add h4).add h5).add
      h6).add h7).add h8
    convert this using 1
    ring
  -- full numerator
  have hN : HasDerivAt
      (fun s => -15 * dtilde X s a * (dtilde X s a + a)
        * (63 * a ^ 8 + 878 * a ^ 7 * dtilde X s a + 5594 * a ^ 6 * dtilde X s a ^ 2
           + 20904 * a ^ 5 * dtilde X s a ^ 3 + 49740 * a ^ 4 * dtilde X s a ^ 4
           + 76848 * a ^ 3 * dtilde X s a ^ 5 + 75120 * a ^ 2 * dtilde X s a ^ 6
           + 42432 * a * dtilde X s a ^ 7 + 10608 * dtilde X s a ^ 8))
      ( ((-15 * D') * (d + a) + (-15 * d) * D')
          * (63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
             + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
             + 42432 * a * d ^ 7 + 10608 * d ^ 8)
        + (-15 * d * (d + a))
          * (878 * a ^ 7 * D' + 5594 * a ^ 6 * (2 * d * D') + 20904 * a ^ 5 * (3 * d ^ 2 * D')
             + 49740 * a ^ 4 * (4 * d ^ 3 * D') + 76848 * a ^ 3 * (5 * d ^ 4 * D')
             + 75120 * a ^ 2 * (6 * d ^ 5 * D') + 42432 * a * (7 * d ^ 6 * D')
             + 10608 * (8 * d ^ 7 * D')) ) r :=
    hP5.mul hQ8
  -- denominator `32 s⁵ (a + 2 d̃)⁹`
  have hMid : HasDerivAt (fun s => (32:ℝ) * s ^ 5) (32 * (5 * r ^ 4)) r := by
    have := (hasDerivAt_pow 5 r).const_mul 32; simpa using this
  have hMin : HasDerivAt (fun s => (a + 2 * dtilde X s a) ^ 9)
      (9 * (a + 2 * d) ^ 8 * (2 * D')) r := by
    have hbase : HasDerivAt (fun s => a + 2 * dtilde X s a) (2 * D') r :=
      (hD.const_mul 2).const_add a
    have := hbase.pow 9; simpa using this
  have hM : HasDerivAt (fun s => (32:ℝ) * s ^ 5 * (a + 2 * dtilde X s a) ^ 9)
      ((32 * (5 * r ^ 4)) * (a + 2 * d) ^ 9
        + (32 * r ^ 5) * (9 * (a + 2 * d) ^ 8 * (2 * D'))) r :=
    hMid.mul hMin
  have hMne : (32:ℝ) * r ^ 5 * (a + 2 * d) ^ 9 ≠ 0 := by positivity
  -- quotient rule (raw value)
  have hderiv : HasDerivAt (fun s => dtil5 X a s)
      ( ( ( ((-15 * D') * (d + a) + (-15 * d) * D')
              * (63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
                 + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
                 + 42432 * a * d ^ 7 + 10608 * d ^ 8)
            + (-15 * d * (d + a))
              * (878 * a ^ 7 * D' + 5594 * a ^ 6 * (2 * d * D') + 20904 * a ^ 5 * (3 * d ^ 2 * D')
                 + 49740 * a ^ 4 * (4 * d ^ 3 * D') + 76848 * a ^ 3 * (5 * d ^ 4 * D')
                 + 75120 * a ^ 2 * (6 * d ^ 5 * D') + 42432 * a * (7 * d ^ 6 * D')
                 + 10608 * (8 * d ^ 7 * D')))
            * ((32:ℝ) * r ^ 5 * (a + 2 * d) ^ 9)
          - (-15 * d * (d + a)
              * (63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
                 + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
                 + 42432 * a * d ^ 7 + 10608 * d ^ 8))
            * ((32 * (5 * r ^ 4)) * (a + 2 * d) ^ 9
               + (32 * r ^ 5) * (9 * (a + 2 * d) ^ 8 * (2 * D'))) )
        / ((32:ℝ) * r ^ 5 * (a + 2 * d) ^ 9) ^ 2 ) r := by
    have := hN.div hM hMne
    convert this using 1
  -- substitute `D'` and simplify to the target closed form
  have hval : ( ( ((-15 * D') * (d + a) + (-15 * d) * D')
              * (63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
                 + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
                 + 42432 * a * d ^ 7 + 10608 * d ^ 8)
            + (-15 * d * (d + a))
              * (878 * a ^ 7 * D' + 5594 * a ^ 6 * (2 * d * D') + 20904 * a ^ 5 * (3 * d ^ 2 * D')
                 + 49740 * a ^ 4 * (4 * d ^ 3 * D') + 76848 * a ^ 3 * (5 * d ^ 4 * D')
                 + 75120 * a ^ 2 * (6 * d ^ 5 * D') + 42432 * a * (7 * d ^ 6 * D')
                 + 10608 * (8 * d ^ 7 * D')))
            * ((32:ℝ) * r ^ 5 * (a + 2 * d) ^ 9)
          - (-15 * d * (d + a)
              * (63 * a ^ 8 + 878 * a ^ 7 * d + 5594 * a ^ 6 * d ^ 2 + 20904 * a ^ 5 * d ^ 3
                 + 49740 * a ^ 4 * d ^ 4 + 76848 * a ^ 3 * d ^ 5 + 75120 * a ^ 2 * d ^ 6
                 + 42432 * a * d ^ 7 + 10608 * d ^ 8))
            * ((32 * (5 * r ^ 4)) * (a + 2 * d) ^ 9
               + (32 * r ^ 5) * (9 * (a + 2 * d) ^ 8 * (2 * D'))) )
        / ((32:ℝ) * r ^ 5 * (a + 2 * d) ^ 9) ^ 2
      = 45 * d * (d + a)
          * (231 * a ^ 10 + 4058 * a ^ 9 * d + 33274 * a ^ 8 * d ^ 2 + 165416 * a ^ 7 * d ^ 3
             + 548520 * a ^ 6 * d ^ 4 + 1262872 * a ^ 5 * d ^ 5 + 2039656 * a ^ 4 * d ^ 6
             + 2278528 * a ^ 3 * d ^ 7 + 1683472 * a ^ 2 * d ^ 8 + 742560 * a * d ^ 9
             + 148512 * d ^ 10)
        / (64 * r ^ 6 * (a + 2 * d) ^ 11) := by
    rw [hD'_def]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hda2' : a + 2 * d ≠ 0 := ne_of_gt hda2
    field_simp
    ring
  rw [hval] at hderiv
  exact hderiv

/-- **The sixth `r`-derivative of `d̃ₐ` as an `iteratedDeriv`.** -/
theorem dtilde_r_iteratedDeriv6 {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    iteratedDeriv 6 (fun s => dtilde X s a) r
      = 45 * dtilde X r a * (dtilde X r a + a)
          * (231 * a ^ 10 + 4058 * a ^ 9 * dtilde X r a + 33274 * a ^ 8 * dtilde X r a ^ 2
             + 165416 * a ^ 7 * dtilde X r a ^ 3 + 548520 * a ^ 6 * dtilde X r a ^ 4
             + 1262872 * a ^ 5 * dtilde X r a ^ 5 + 2039656 * a ^ 4 * dtilde X r a ^ 6
             + 2278528 * a ^ 3 * dtilde X r a ^ 7 + 1683472 * a ^ 2 * dtilde X r a ^ 8
             + 742560 * a * dtilde X r a ^ 9 + 148512 * dtilde X r a ^ 10)
        / (64 * r ^ 6 * (a + 2 * dtilde X r a) ^ 11) := by
  have hL : iteratedDeriv 6 (fun s => dtilde X s a) r
      = deriv (iteratedDeriv 5 (fun s => dtilde X s a)) r := by
    rw [iteratedDeriv_succ]
  rw [hL]
  -- `iteratedDeriv 5 d̃ =ᶠ[nhds r] dtil5 X a ·` on the open set `{s | 0 < s}`
  have hee : iteratedDeriv 5 (fun s => dtilde X s a) =ᶠ[nhds r] (fun s => dtil5 X a s) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hr) ?_
    intro s hs
    have hs' : 0 < s := hs
    rw [dtilde_r_iteratedDeriv5 hX ha hs']
    simp only [dtil5]
  rw [hee.deriv_eq]
  exact (dtil5_hasDerivAt hX ha hr).deriv

/-- **`d̃ₐ⁽⁵⁾` is differentiable with derivative `d̃ₐ⁽⁶⁾`.**  I.e. `s ↦ iteratedDeriv 5 d̃ₐ s`
has derivative `iteratedDeriv 6 d̃ₐ s` at `s > 0`.  Companion of `dtilde_iteratedDeriv4_hasDerivAt`. -/
theorem dtilde_iteratedDeriv5_hasDerivAt {X a s : ℝ} (hX : 0 < X) (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun t => iteratedDeriv 5 (fun u => dtilde X u a) t)
      (iteratedDeriv 6 (fun u => dtilde X u a) s) s := by
  have hee : iteratedDeriv 5 (fun u => dtilde X u a) =ᶠ[nhds s] (fun t => dtil5 X a t) := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_id).mem_nhds hs) ?_
    intro t ht
    have ht' : 0 < t := ht
    rw [dtilde_r_iteratedDeriv5 hX ha ht']
    simp only [dtil5]
  rw [dtilde_r_iteratedDeriv6 hX ha hs]
  exact (dtil5_hasDerivAt hX ha hs).congr_of_eventuallyEq hee

/-- **`|d̃⁽⁶⁾(r)| ≤ C₆·D/R⁶`.**  In the §5 regime, the sixth `r`-derivative of `d̃ₐ` is
bounded in absolute value by `C₆·(D/R⁶)` with `C₆ = 1.3817466·10³⁹`. -/
theorem dtilde_d6_upper {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    |iteratedDeriv 6 (fun s => dtilde P.X s a) r|
      ≤ 1381746600000000000000000000000000000000 * (S.D / S.R ^ 6) := by
  -- scale positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  -- the defect-inverse window
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  rw [dtilde_r_iteratedDeriv6 P.X_pos ha0 hr0]
  set d := dtilde P.X r a with hd_def
  have ha_hiD : a ≤ (11/10) * S.D := by linarith
  -- abbreviations
  set Poly := 231 * a ^ 10 + 4058 * a ^ 9 * d + 33274 * a ^ 8 * d ^ 2 + 165416 * a ^ 7 * d ^ 3
      + 548520 * a ^ 6 * d ^ 4 + 1262872 * a ^ 5 * d ^ 5 + 2039656 * a ^ 4 * d ^ 6
      + 2278528 * a ^ 3 * d ^ 7 + 1683472 * a ^ 2 * d ^ 8 + 742560 * a * d ^ 9
      + 148512 * d ^ 10 with hPoly_def
  have hPoly_pos : 0 < Poly := by rw [hPoly_def]; positivity
  set Num6 := 45 * d * (d + a) * Poly with hNum6_def
  set Den6 := 64 * r ^ 6 * (a + 2 * d) ^ 11 with hDen6_def
  have hNum6_pos : 0 < Num6 := by rw [hNum6_def]; positivity
  have hDen6_pos : 0 < Den6 := by rw [hDen6_def]; positivity
  -- the closed form is positive, so its abs is `Num6 / Den6`
  have habs : |(45 * d * (d + a) * Poly / Den6)| = Num6 / Den6 := by
    rw [abs_of_pos (show (0:ℝ) < 45 * d * (d + a) * Poly / Den6 by
      rw [hDen6_def]; positivity)]
  have hmatch : (45 * d * (d + a)
        * (231 * a ^ 10 + 4058 * a ^ 9 * d + 33274 * a ^ 8 * d ^ 2 + 165416 * a ^ 7 * d ^ 3
           + 548520 * a ^ 6 * d ^ 4 + 1262872 * a ^ 5 * d ^ 5 + 2039656 * a ^ 4 * d ^ 6
           + 2278528 * a ^ 3 * d ^ 7 + 1683472 * a ^ 2 * d ^ 8 + 742560 * a * d ^ 9
           + 148512 * d ^ 10)
        / (64 * r ^ 6 * (a + 2 * d) ^ 11))
      = 45 * d * (d + a) * Poly / Den6 := by
    rw [hPoly_def, hDen6_def]
  rw [hmatch, habs]
  -- numerator upper bound
  have hf1 : 45 * d * (d + a) ≤ 16000 * S.D ^ 2 := by
    nlinarith only [hd_hi, ha_hiD, hd_pos, ha0, hDpos]
  have hf2 : Poly ≤ 800000000000000000 * S.D ^ 10 := by
    rw [hPoly_def]
    have hp1 : 231 * a ^ 10 ≤ 231 * ((11/10) * S.D) ^ 10 := by
      have := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 10; nlinarith only [this]
    have hp2 : 4058 * a ^ 9 * d ≤ 4058 * ((11/10) * S.D) ^ 9 * (18 * S.D) := by
      have h9 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 9
      have := mul_le_mul h9 hd_hi (by positivity) (by positivity)
      nlinarith only [this]
    have hp3 : 33274 * a ^ 8 * d ^ 2 ≤ 33274 * ((11/10) * S.D) ^ 8 * (18 * S.D) ^ 2 := by
      have h8 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 8
      have hd2 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 2
      have := mul_le_mul h8 hd2 (by positivity) (by positivity)
      nlinarith only [this]
    have hp4 : 165416 * a ^ 7 * d ^ 3 ≤ 165416 * ((11/10) * S.D) ^ 7 * (18 * S.D) ^ 3 := by
      have h7 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 7
      have hd3 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 3
      have := mul_le_mul h7 hd3 (by positivity) (by positivity)
      nlinarith only [this]
    have hp5 : 548520 * a ^ 6 * d ^ 4 ≤ 548520 * ((11/10) * S.D) ^ 6 * (18 * S.D) ^ 4 := by
      have h6 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 6
      have hd4 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 4
      have := mul_le_mul h6 hd4 (by positivity) (by positivity)
      nlinarith only [this]
    have hp6 : 1262872 * a ^ 5 * d ^ 5 ≤ 1262872 * ((11/10) * S.D) ^ 5 * (18 * S.D) ^ 5 := by
      have h5 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 5
      have hd5 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 5
      have := mul_le_mul h5 hd5 (by positivity) (by positivity)
      nlinarith only [this]
    have hp7 : 2039656 * a ^ 4 * d ^ 6 ≤ 2039656 * ((11/10) * S.D) ^ 4 * (18 * S.D) ^ 6 := by
      have h4 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 4
      have hd6 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 6
      have := mul_le_mul h4 hd6 (by positivity) (by positivity)
      nlinarith only [this]
    have hp8 : 2278528 * a ^ 3 * d ^ 7 ≤ 2278528 * ((11/10) * S.D) ^ 3 * (18 * S.D) ^ 7 := by
      have h3 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 3
      have hd7 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 7
      have := mul_le_mul h3 hd7 (by positivity) (by positivity)
      nlinarith only [this]
    have hp9 : 1683472 * a ^ 2 * d ^ 8 ≤ 1683472 * ((11/10) * S.D) ^ 2 * (18 * S.D) ^ 8 := by
      have h2 := pow_le_pow_left₀ (le_of_lt ha0) ha_hiD 2
      have hd8 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 8
      have := mul_le_mul h2 hd8 (by positivity) (by positivity)
      nlinarith only [this]
    have hp10 : 742560 * a * d ^ 9 ≤ 742560 * ((11/10) * S.D) * (18 * S.D) ^ 9 := by
      have hd9 := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 9
      have := mul_le_mul ha_hiD hd9 (by positivity) (by positivity)
      nlinarith only [this]
    have hp11 : 148512 * d ^ 10 ≤ 148512 * (18 * S.D) ^ 10 := by
      have := pow_le_pow_left₀ (le_of_lt hd_pos) hd_hi 10; nlinarith only [this]
    nlinarith only [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, pow_pos hDpos 10]
  have hNum6_hi : Num6 ≤ 13000000000000000000000 * S.D ^ 12 := by
    rw [hNum6_def]
    have hmul := mul_le_mul hf1 hf2 (le_of_lt hPoly_pos) (by positivity)
    calc 45 * d * (d + a) * Poly
        ≤ (16000 * S.D ^ 2) * (800000000000000000 * S.D ^ 10) := hmul
      _ ≤ 13000000000000000000000 * S.D ^ 12 := by nlinarith only [pow_pos hDpos 12]
  -- denominator lower bound: `Den6 ≥ R⁶ D¹¹ / 1.062882·10¹⁷`
  have hr6_lo : S.R ^ 6 / 139314069504 ≤ r ^ 6 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (1/72) * S.R) hr_lo 6
    calc S.R ^ 6 / 139314069504 = ((1/72) * S.R) ^ 6 := by ring
      _ ≤ r ^ 6 := this
  have h2d_lo : S.D / 5 ≤ a + 2 * d := by linarith
  have hpow11_lo : S.D ^ 11 / 48828125 ≤ (a + 2 * d) ^ 11 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.D / 5) h2d_lo 11
    calc S.D ^ 11 / 48828125 = (S.D / 5) ^ 11 := by ring
      _ ≤ (a + 2 * d) ^ 11 := this
  have hDen6_lo : S.R ^ 6 * S.D ^ 11 / 106288200000000000 ≤ Den6 := by
    rw [hDen6_def]
    have hmul := mul_le_mul hr6_lo hpow11_lo (by positivity) (by positivity)
    calc S.R ^ 6 * S.D ^ 11 / 106288200000000000
        ≤ 64 * ((S.R ^ 6 / 139314069504) * (S.D ^ 11 / 48828125)) := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith only [mul_pos (pow_pos hRpos 6) (pow_pos hDpos 11)]
      _ ≤ 64 * (r ^ 6 * (a + 2 * d) ^ 11) := by nlinarith only [hmul]
      _ = 64 * r ^ 6 * (a + 2 * d) ^ 11 := by ring
  -- combine
  rw [div_le_iff₀ hDen6_pos]
  have hstep : 1381746600000000000000000000000000000000 * (S.D / S.R ^ 6)
        * (S.R ^ 6 * S.D ^ 11 / 106288200000000000)
      ≤ 1381746600000000000000000000000000000000 * (S.D / S.R ^ 6) * Den6 :=
    mul_le_mul_of_nonneg_left hDen6_lo (by positivity)
  have hRne : S.R ≠ 0 := ne_of_gt hRpos
  have heq : 1381746600000000000000000000000000000000 * (S.D / S.R ^ 6)
        * (S.R ^ 6 * S.D ^ 11 / 106288200000000000)
      = 13000000000000000000000 * S.D ^ 12 := by field_simp; ring
  calc Num6 ≤ 13000000000000000000000 * S.D ^ 12 := hNum6_hi
    _ = 1381746600000000000000000000000000000000 * (S.D / S.R ^ 6)
          * (S.R ^ 6 * S.D ^ 11 / 106288200000000000) := by rw [heq]
    _ ≤ 1381746600000000000000000000000000000000 * (S.D / S.R ^ 6) * Den6 := hstep

end Squarefree
