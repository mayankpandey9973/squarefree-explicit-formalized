import Squarefree.Lower.DefectShatExpand

/-!
# §5 Step-4: the `Υ` collection expansion (writeup 1006–1030)

The §5 Step-4 analogue of `Q_gen_expand`.  The three-term combination

  `Υ := ℓ₂²(ℓ₂−ℓ₁)²·Ŝ_{a,ℓ₁b₀}(d) − ℓ₁²(ℓ₂−ℓ₁)²·Ŝ_{a,ℓ₂b₀+v}(d)
        + ℓ₁²ℓ₂²·Ŝ_{a,(ℓ₂−ℓ₁)b₀+v}(d+ℓ₁b₀)`

expands, after collecting the order-5 / order-6 Taylor leads of all three `Ŝ` (with the third
re-centred from base `d+ℓ₁b₀` to base `d`), into the closed cubic/quartic form

  `(Xa/d⁵)·((−4+10a/d)·(P₁+P₂/d)) + O(·/d⁷)`.

The collection identity through orders `1/d⁵`, `1/d⁶` is *exact* (sympy-verified); the leftover
`R` is genuinely into `1/d⁷` and is absorbed, together with the three `Shat_expand` remainders
and the two base-point shift corrections (`rem5`, `rem6` of `1/(d+x)⁵`, `1/(d+x)⁶`), into the
explicit error term `ERR`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

/-- `|P₁(v)|` cubic part (writeup 1020). -/
noncomputable def Pone (b₀ v ℓ₁ ℓ₂ : ℝ) : ℝ :=
  3*ℓ₁^3*ℓ₂*(ℓ₂-ℓ₁)*b₀*v^2 + ℓ₁^3*(2*ℓ₂-ℓ₁)*v^3

/-- `P₂(v)` quartic part (writeup 1024). -/
noncomputable def Ptwo (b₀ v ℓ₁ ℓ₂ : ℝ) : ℝ :=
  -5*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)^2*b₀^3*v - 15*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)*b₀^2*v^2
    - 5*ℓ₁^3*ℓ₂*(3*ℓ₂-2*ℓ₁)*b₀*v^3 - (5/2)*ℓ₁^3*(2*ℓ₂-ℓ₁)*v^4

/-- The genuine `1/d⁷` residual of the collection identity (sympy-confirmed). Public so the
§5 Step-4 error-collection lemma (`UpsilonErr.lean`) can bound it. -/
noncomputable def Rres (X a b₀ v d ℓ₁ ℓ₂ : ℝ) : ℝ :=
  25*X*a^2*ℓ₁^3*v*(2*b₀^3*ℓ₁^2*ℓ₂^2 - 4*b₀^3*ℓ₁*ℓ₂^3 + 2*b₀^3*ℓ₂^4
    - 6*b₀^2*ℓ₁*ℓ₂^2*v + 6*b₀^2*ℓ₂^3*v - 4*b₀*ℓ₁*ℓ₂*v^2 + 6*b₀*ℓ₂^2*v^2
    - ℓ₁*v^3 + 2*ℓ₂*v^3) / d^7

/-- **Order-2 base-point shift remainder of `1/(d+x)⁵`.**
`|1/(d+x)⁵ − (1/d⁵)(1−5x/d)| ≤ 120·x²/d⁷` on the window `4|x| ≤ d`. -/
private theorem rem5_bound {d x : ℝ} (hd : 0 < d) (hx : 4 * |x| ≤ d) :
    |1 / (d + x) ^ 5 - (1 / d ^ 5) * (1 - 5 * x / d)| ≤ 120 * x ^ 2 / d ^ 7 := by
  have hpair := abs_le.mp (by linarith [hx] : |x| ≤ d / 4)
  have hxhi : x ≤ d / 4 := hpair.2
  have hxlo : -(d / 4) ≤ x := hpair.1
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdz : 0 < d + x := by linarith
  have hdz5 : (0:ℝ) < (d + x) ^ 5 := by positivity
  have hd7 : (0:ℝ) < d ^ 7 := by positivity
  have hden : (0:ℝ) < d ^ 6 * (d + x) ^ 5 := by positivity
  have hlo : 3 * d / 4 ≤ d + x := by linarith
  have hhi : d + x ≤ 5 * d / 4 := by linarith
  have h34 : (0:ℝ) ≤ 3 * d / 4 := by linarith
  have hpow_lo : (3 * d / 4) ^ 5 ≤ (d + x) ^ 5 := by gcongr
  have hpow_hi : (d + x) ^ 5 ≤ (5 * d / 4) ^ 5 := by gcongr
  -- LHS over common denom d⁶(d+x)⁵, numerator N5 = 15d⁴x²+40d³x³+45d²x⁴+24dx⁵+5x⁶ (sympy)
  have hrw : 1 / (d + x) ^ 5 - (1 / d ^ 5) * (1 - 5 * x / d)
      = (15*d^4*x^2 + 40*d^3*x^3 + 45*d^2*x^4 + 24*d*x^5 + 5*x^6)
        / (d ^ 6 * (d + x) ^ 5) := by
    field_simp
    ring
  rw [hrw, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hd7]
  -- N5 = x²·Q(x) with Q(x) = 15d⁴+40d³x+45d²x²+24dx³+5x⁴ ≥ 0 and ≤ (7221/256)d⁴ on the window.
  have hQnn : 0 ≤ 15*d^4 + 40*d^3*x + 45*d^2*x^2 + 24*d*x^3 + 5*x^4 := by
    nlinarith [hxlo, hxhi, hd, sq_nonneg x, mul_nonneg (sq_nonneg x) hd.le,
      mul_pos hd hd, mul_pos (mul_pos hd hd) hd, mul_pos (mul_pos (mul_pos hd hd) hd) hd]
  have hN5nn : 0 ≤ 15*d^4*x^2 + 40*d^3*x^3 + 45*d^2*x^4 + 24*d*x^5 + 5*x^6 := by
    nlinarith [mul_nonneg (sq_nonneg x) hQnn]
  rw [abs_of_nonneg hN5nn]
  -- Q(x) ≤ (7221/256)d⁴: the gap factors as
  -- (d−4x)·(3381d³+3284d²x+1616dx²+320x³)/256, both factors ≥ 0 on the window.
  have hcubnn : 0 ≤ 3381*d^3 + 3284*d^2*x + 1616*d*x^2 + 320*x^3 := by
    nlinarith [hxlo, hxhi, hd, sq_nonneg x, mul_nonneg (sq_nonneg x) hd.le,
      mul_pos hd hd, mul_pos (mul_pos hd hd) hd]
  have hQub : 15*d^4 + 40*d^3*x + 45*d^2*x^2 + 24*d*x^3 + 5*x^4 ≤ (7221/256) * d^4 := by
    nlinarith [mul_nonneg (by linarith [hxhi] : (0:ℝ) ≤ d - 4*x) hcubnn]
  have hN5ub : 15*d^4*x^2 + 40*d^3*x^3 + 45*d^2*x^4 + 24*d*x^5 + 5*x^6
      ≤ (7221/256) * d^4 * x^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hQub (sq_nonneg x)]
  calc (15*d^4*x^2 + 40*d^3*x^3 + 45*d^2*x^4 + 24*d*x^5 + 5*x^6) * d ^ 7
      ≤ ((7221/256) * d^4 * x^2) * d^7 := by gcongr
    _ ≤ 120 * x ^ 2 * (d ^ 6 * (d + x) ^ 5) := by
        nlinarith [hpow_lo, hd7, hd, sq_nonneg x, mul_nonneg (sq_nonneg x) hd7.le,
          mul_nonneg (sq_nonneg x) (mul_nonneg (pow_nonneg hd.le 6) (sub_nonneg.mpr hpow_lo))]

/-- **Order-1 base-point shift remainder of `1/(d+x)⁶`.**
`|1/(d+x)⁶ − 1/d⁶| ≤ 64·|x|/d⁷` on the window `4|x| ≤ d`. -/
private theorem rem6_bound {d x : ℝ} (hd : 0 < d) (hx : 4 * |x| ≤ d) :
    |1 / (d + x) ^ 6 - 1 / d ^ 6| ≤ 64 * |x| / d ^ 7 := by
  have hpair := abs_le.mp (by linarith [hx] : |x| ≤ d / 4)
  have hxhi : x ≤ d / 4 := hpair.2
  have hxlo : -(d / 4) ≤ x := hpair.1
  have habsx := abs_nonneg x
  have hxle := le_abs_self x
  have hxge := neg_abs_le x
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdz : 0 < d + x := by linarith
  have hdz6 : (0:ℝ) < (d + x) ^ 6 := by positivity
  have hd7 : (0:ℝ) < d ^ 7 := by positivity
  have hden : (0:ℝ) < d ^ 6 * (d + x) ^ 6 := by positivity
  have hlo : 3 * d / 4 ≤ d + x := by linarith
  have h34 : (0:ℝ) ≤ 3 * d / 4 := by linarith
  have hpow_lo : (3 * d / 4) ^ 6 ≤ (d + x) ^ 6 := by gcongr
  -- LHS over common denom d⁶(d+x)⁶, numerator N6 = -(6d⁵x+15d⁴x²+20d³x³+15d²x⁴+6dx⁵+x⁶) (sympy)
  have hrw : 1 / (d + x) ^ 6 - 1 / d ^ 6
      = (-(6*d^5*x + 15*d^4*x^2 + 20*d^3*x^3 + 15*d^2*x^4 + 6*d*x^5 + x^6))
        / (d ^ 6 * (d + x) ^ 6) := by
    field_simp
    ring
  rw [hrw, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hd7]
  -- N6 = −x·Q6(x), Q6 = 6d⁵+15d⁴x+20d³x²+15d²x³+6dx⁴+x⁵ ≥ 0 and ≤ (11529/1024)d⁵, so
  -- |N6| = |x|·Q6 ≤ (11529/1024)d⁵·|x|.
  -- with u = x+d/4 ≥ 0, Q6 = (7d+4u)(13d²+8du+16u²)(37d²+40du+16u²)/1024 ≥ 0.
  have hu : (0:ℝ) ≤ x + d/4 := by linarith
  have hQ6nn : 0 ≤ 6*d^5 + 15*d^4*x + 20*d^3*x^2 + 15*d^2*x^3 + 6*d*x^4 + x^5 := by
    nlinarith [hu, hd, mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu,
      mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu) hu,
      mul_pos hd hd, mul_pos (mul_pos hd hd) hd, mul_pos (mul_pos (mul_pos hd hd) hd) hd,
      mul_nonneg hu hd.le, mul_nonneg (mul_nonneg hu hu) hd.le,
      mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hd.le,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu) hd.le]
  have hN6abs : |-(6*d^5*x + 15*d^4*x^2 + 20*d^3*x^3 + 15*d^2*x^4 + 6*d*x^5 + x^6)|
      = |x| * (6*d^5 + 15*d^4*x + 20*d^3*x^2 + 15*d^2*x^3 + 6*d*x^4 + x^5) := by
    rw [show -(6*d^5*x + 15*d^4*x^2 + 20*d^3*x^3 + 15*d^2*x^4 + 6*d*x^5 + x^6)
          = (-x) * (6*d^5 + 15*d^4*x + 20*d^3*x^2 + 15*d^2*x^3 + 6*d*x^4 + x^5) by ring,
        abs_mul, abs_neg, abs_of_nonneg hQ6nn]
  rw [hN6abs]
  -- Q6 ≤ (11529/1024)d⁵: gap = (d−4x)·(5385d⁴+6180d³x+4240d²x²+1600dx³+256x⁴)/1024 ≥ 0.
  have hquartnn : 0 ≤ 5385*d^4 + 6180*d^3*x + 4240*d^2*x^2 + 1600*d*x^3 + 256*x^4 := by
    nlinarith [hxlo, hxhi, hd, sq_nonneg x, mul_nonneg (sq_nonneg x) hd.le,
      mul_pos hd hd, mul_pos (mul_pos hd hd) hd, mul_pos (mul_pos (mul_pos hd hd) hd) hd]
  have hQ6ub : 6*d^5 + 15*d^4*x + 20*d^3*x^2 + 15*d^2*x^3 + 6*d*x^4 + x^5
      ≤ (11529/1024) * d^5 := by
    nlinarith [mul_nonneg (by linarith [hxhi] : (0:ℝ) ≤ d - 4*x) hquartnn]
  calc |x| * (6*d^5 + 15*d^4*x + 20*d^3*x^2 + 15*d^2*x^3 + 6*d*x^4 + x^5) * d ^ 7
      ≤ |x| * ((11529/1024) * d^5) * d^7 := by
        gcongr
    _ ≤ 64 * |x| * (d ^ 6 * (d + x) ^ 6) := by
        nlinarith [hpow_lo, hd7, hd, habsx, mul_nonneg habsx hd7.le,
          mul_nonneg habsx (mul_nonneg (pow_nonneg hd.le 6) (sub_nonneg.mpr hpow_lo))]

/-- **§5 Step-4 `Υ` collection expansion** (writeup 1006–1030).  The three-term combination of
corrected mixed second differences `Ŝ` collects, after re-centring the third (base `d+ℓ₁b₀`) and
applying the order-5 expansion `Shat_expand` to all three, into the closed cubic/quartic form
`(Xa/d⁵)·((−4+10a/d)·(P₁+P₂/d))` up to an explicit `O(·/d⁷)` error `ERR`. -/
theorem Upsilon_expand {X a b₀ v d ℓ₁ ℓ₂ : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb1 : ℓ₁*b₀ ≠ 0) (hb2 : ℓ₂*b₀+v ≠ 0) (hb3 : (ℓ₂-ℓ₁)*b₀+v ≠ 0)
    (hwin : 4*(a + ℓ₂*|b₀| + |v|) ≤ d)              -- uniform Taylor window (terms 1,2)
    (hwin3 : 4*(a + |(ℓ₂-ℓ₁)*b₀+v|) ≤ d + ℓ₁*b₀)    -- window for the shifted base point (term 3)
    (hshift : 0 < d + ℓ₁*b₀) :
    |(ℓ₂^2*(ℓ₂-ℓ₁)^2 * Shat X a (ℓ₁*b₀) d
        - ℓ₁^2*(ℓ₂-ℓ₁)^2 * Shat X a (ℓ₂*b₀+v) d
        + ℓ₁^2*ℓ₂^2 * Shat X a ((ℓ₂-ℓ₁)*b₀+v) (d + ℓ₁*b₀))
      - (X*a/d^5) * ((-4 + 10*a/d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂/d))|
      ≤ ℓ₂^2*(ℓ₂-ℓ₁)^2
          * (10^4 * X * (a*|ℓ₁*b₀|^5 + a^2*|ℓ₁*b₀|^4 + a^3*|ℓ₁*b₀|^3) / d^7)
        + ℓ₁^2*(ℓ₂-ℓ₁)^2
          * (10^4 * X * (a*|ℓ₂*b₀+v|^5 + a^2*|ℓ₂*b₀+v|^4 + a^3*|ℓ₂*b₀+v|^3) / d^7)
        + ℓ₁^2*ℓ₂^2
          * (10^4 * X * (a*|(ℓ₂-ℓ₁)*b₀+v|^5 + a^2*|(ℓ₂-ℓ₁)*b₀+v|^4
              + a^3*|(ℓ₂-ℓ₁)*b₀+v|^3) / (d + ℓ₁*b₀)^7)
        + ℓ₁^2*ℓ₂^2
          * (|X*(-4*a*((ℓ₂-ℓ₁)*b₀+v)^3)| * (120 * (ℓ₁*b₀)^2 / d^7)
            + |X*(10*a*((ℓ₂-ℓ₁)*b₀+v)^4 + 10*a^2*((ℓ₂-ℓ₁)*b₀+v)^3)| * (64 * |ℓ₁*b₀| / d^7))
        + |Rres X a b₀ v d ℓ₁ ℓ₂| := by
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hb0nn : 0 ≤ |b₀| := abs_nonneg b₀
  have hvnn : 0 ≤ |v| := abs_nonneg v
  -- windows for terms 1 and 2 at base d (from the uniform window `hwin`)
  have habs1 : |ℓ₁ * b₀| = ℓ₁ * |b₀| := by rw [abs_mul, abs_of_pos hℓ1]
  have hwin1 : 4 * (a + |ℓ₁ * b₀|) ≤ d := by
    rw [habs1]; nlinarith [hwin, hb0nn, hvnn, hℓ12, hℓ1, mul_le_mul_of_nonneg_right hℓ12.le hb0nn]
  have hwin2 : 4 * (a + |ℓ₂ * b₀ + v|) ≤ d := by
    have h1 : |ℓ₂ * b₀ + v| ≤ ℓ₂ * |b₀| + |v| := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_pos hℓ2]
    linarith [hwin]
  -- the three Shat_expand estimates
  have hE1 := Shat_expand hX ha hb1 hd hwin1
  have hE2 := Shat_expand hX ha hb2 hd hwin2
  have hE3 := Shat_expand hX ha hb3 hshift hwin3
  rw [habs1] at hE1
  -- window for the base-point shift (4|ℓ₁b₀| ≤ d)
  have hxwin : 4 * |ℓ₁ * b₀| ≤ d := by
    rw [habs1]; nlinarith [hwin, hb0nn, hvnn, hℓ12, hℓ1, mul_le_mul_of_nonneg_right hℓ12.le hb0nn]
  -- abbreviations
  set b₁ : ℝ := ℓ₁ * b₀ with hb1def
  set b₂ : ℝ := ℓ₂ * b₀ + v with hb2def
  set b₃ : ℝ := (ℓ₂ - ℓ₁) * b₀ + v with hb3def
  set w₁ : ℝ := ℓ₂^2*(ℓ₂-ℓ₁)^2 with hw1def
  set w₂ : ℝ := ℓ₁^2*(ℓ₂-ℓ₁)^2 with hw2def
  set w₃ : ℝ := ℓ₁^2*ℓ₂^2 with hw3def
  -- the leading parts (base d for terms 1,2; base d+b₁ for term 3)
  set lead₁ : ℝ := X * (-4*a*b₁^3) / d^5 + X * (10*a*b₁^4 + 10*a^2*b₁^3) / d^6 with hlead1
  set lead₂ : ℝ := X * (-4*a*b₂^3) / d^5 + X * (10*a*b₂^4 + 10*a^2*b₂^3) / d^6 with hlead2
  set lead₃ : ℝ := X * (-4*a*b₃^3) / (d+b₁)^5
      + X * (10*a*b₃^4 + 10*a^2*b₃^3) / (d+b₁)^6 with hlead3
  -- the re-centred third lead (1/(d+b₁)^5 → (1/d^5)(1-5b₁/d), 1/(d+b₁)^6 → 1/d^6)
  set lead₃s : ℝ := X * (-4*a*b₃^3) * ((1/d^5)*(1 - 5*b₁/d))
      + X * (10*a*b₃^4 + 10*a^2*b₃^3) * (1/d^6) with hlead3s
  set target : ℝ :=
    (X*a/d^5) * ((-4 + 10*a/d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂/d)) with htgt
  -- THE COLLECTION IDENTITY (sympy-confirmed exact through 1/d⁵,1/d⁶; residual Rres into 1/d⁷)
  have hcoll : w₁ * lead₁ - w₂ * lead₂ + w₃ * lead₃s - target = Rres X a b₀ v d ℓ₁ ℓ₂ := by
    rw [hw1def, hw2def, hw3def, hlead1, hlead2, hlead3s, htgt, hb1def, hb2def, hb3def,
      Pone, Ptwo, Rres]
    field_simp
    ring
  -- the base-point shift correction for term 3
  have hshiftdiff : lead₃ - lead₃s
      = X*(-4*a*b₃^3) * (1/(d+b₁)^5 - (1/d^5)*(1 - 5*b₁/d))
        + X*(10*a*b₃^4 + 10*a^2*b₃^3) * (1/(d+b₁)^6 - 1/d^6) := by
    rw [hlead3, hlead3s]; ring
  -- master decomposition: Υ − target = w₁(Ŝ₁−lead₁) − w₂(Ŝ₂−lead₂) + w₃(Ŝ₃−lead₃)
  --   + w₃(lead₃−lead₃s) + Rres
  set S1 : ℝ := Shat X a b₁ d with hS1
  set S2 : ℝ := Shat X a b₂ d with hS2
  set S3 : ℝ := Shat X a b₃ (d+b₁) with hS3
  have hdecomp : (w₁ * S1 - w₂ * S2 + w₃ * S3) - target
      = (w₁ * (S1 - lead₁) - w₂ * (S2 - lead₂) + w₃ * (S3 - lead₃))
        + w₃ * (lead₃ - lead₃s) + Rres X a b₀ v d ℓ₁ ℓ₂ := by
    have := hcoll
    ring_nf
    ring_nf at this
    linarith [this]
  rw [hdecomp]
  -- triangle inequality across the five pieces
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) (le_refl _)) ?_
  -- bound each abs piece
  have hd7 : (0:ℝ) < d^7 := by positivity
  -- (a) the three Shat_expand remainders
  have hP1 : |w₁ * (S1 - lead₁)|
      ≤ w₁ * (10^4 * X * (a*|ℓ₁*b₀|^5 + a^2*|ℓ₁*b₀|^4 + a^3*|ℓ₁*b₀|^3) / d^7) := by
    rw [abs_mul, abs_of_nonneg (by rw [hw1def]; positivity : (0:ℝ) ≤ w₁)]
    refine mul_le_mul_of_nonneg_left ?_ (by rw [hw1def]; positivity)
    rw [habs1]; exact hE1
  have hP2 : |w₂ * (S2 - lead₂)|
      ≤ w₂ * (10^4 * X * (a*|ℓ₂*b₀+v|^5 + a^2*|ℓ₂*b₀+v|^4 + a^3*|ℓ₂*b₀+v|^3) / d^7) := by
    rw [abs_mul, abs_of_nonneg (by rw [hw2def]; positivity : (0:ℝ) ≤ w₂)]
    exact mul_le_mul_of_nonneg_left hE2 (by rw [hw2def]; positivity)
  have hP3 : |w₃ * (S3 - lead₃)|
      ≤ w₃ * (10^4 * X * (a*|(ℓ₂-ℓ₁)*b₀+v|^5 + a^2*|(ℓ₂-ℓ₁)*b₀+v|^4
          + a^3*|(ℓ₂-ℓ₁)*b₀+v|^3) / (d+ℓ₁*b₀)^7) := by
    rw [abs_mul, abs_of_nonneg (by rw [hw3def]; positivity : (0:ℝ) ≤ w₃)]
    refine mul_le_mul_of_nonneg_left ?_ (by rw [hw3def]; positivity)
    rw [hb3def, hb1def] at *; exact hE3
  -- (b) the base-point shift correction
  have hr5 := rem5_bound (x := b₁) hd (by rw [hb1def]; exact hxwin)
  have hr6 := rem6_bound (x := b₁) hd (by rw [hb1def]; exact hxwin)
  have hPshift : |w₃ * (lead₃ - lead₃s)|
      ≤ w₃ * (|X*(-4*a*((ℓ₂-ℓ₁)*b₀+v)^3)| * (120 * (ℓ₁*b₀)^2 / d^7)
          + |X*(10*a*((ℓ₂-ℓ₁)*b₀+v)^4 + 10*a^2*((ℓ₂-ℓ₁)*b₀+v)^3)| * (64 * |ℓ₁*b₀| / d^7)) := by
    rw [abs_mul, abs_of_nonneg (by rw [hw3def]; positivity : (0:ℝ) ≤ w₃)]
    refine mul_le_mul_of_nonneg_left ?_ (by rw [hw3def]; positivity)
    rw [hshiftdiff]
    refine le_trans (abs_add_le _ _) ?_
    have hsq : (ℓ₁ * b₀)^2 = b₁^2 := by rw [hb1def]
    refine add_le_add ?_ ?_
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hb1def, hb3def] at *
      calc |1/(d+b₁)^5 - (1/d^5)*(1 - 5*b₁/d)| ≤ 120 * b₁^2 / d^7 := hr5
        _ = 120 * (ℓ₁*b₀)^2 / d^7 := by rw [hb1def]
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hb1def, hb3def] at *
      calc |1/(d+b₁)^6 - 1/d^6| ≤ 64 * |b₁| / d^7 := hr6
        _ = 64 * |ℓ₁*b₀| / d^7 := by rw [hb1def]
  -- assemble
  calc |w₁ * (S1 - lead₁) - w₂ * (S2 - lead₂) + w₃ * (S3 - lead₃)| + |w₃ * (lead₃ - lead₃s)|
        + |Rres X a b₀ v d ℓ₁ ℓ₂|
      ≤ ((|w₁ * (S1 - lead₁)| + |w₂ * (S2 - lead₂)|) + |w₃ * (S3 - lead₃)|)
          + |w₃ * (lead₃ - lead₃s)| + |Rres X a b₀ v d ℓ₁ ℓ₂| := by
        gcongr
        refine le_trans (abs_add_le _ _) ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by
        gcongr

end Squarefree
