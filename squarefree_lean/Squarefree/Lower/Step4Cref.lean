import Squarefree.Params

/-!
# §5 Step-4 flat leading coefficient (writeup 1052; `r`-independent reference parabola)

The per-`r` bracket-included quadratic coefficient of the `Σ_closed` parabola (the coefficient
of `(ℓ₁v)²` subtracted in `Sigma_closed_parabola_sharp`) is

  `C'(r) = (Xa/d⁵)·(−4+10a/d)·3ℓ₁ℓ₂(ℓ₂−ℓ₁)b₀`   (`Cprime` below).

This is `r`-dependent (through `a`, `d`, `b₀`), which is exactly why the two-point
square-difference fails when phrased against `C'`.  The remedy is a **fixed `r`-independent
reference**

  `Cref = 3ℓ₁ℓ₂(ℓ₂−ℓ₁)/(Δ²Ω²)`   (`Cref` below),

and a bound on the per-`r` drift of `C'(r)` away from `Cref` that is *quadratically* small in
`t = a/d̃ ≍ A/D = Ω/H`.

## The flatness mechanism (sympy-exact, ported from attempt-1 `Sigma.lean:40,78`)

Substituting the first-derivative model `b̃ₐ(d) = b1Model X a d` (the value forced by
`ρ = Xa³/(d²(d+a)²)`) into `C'` produces

  `C'(b̃) = (3ℓ₁ℓ₂(ℓ₂−ℓ₁)/a²)·Cshape(a/d)`,   `Cshape t = ½·(1+t)³/(2+t)·(4−10t)`.

The shape has **no linear term**: `Cshape t = 1 − (9/2)t² + t³·rem(t)` (the `(1+t)³` factor's
`+2t` combines with `(4−10t)`'s `+4` as `2(2+t)`, cancelling the denominator), so on `0≤t≤1`,
`|Cshape t − 1| ≤ 20 t²` (`Cshape_abs_sub_one_le`).

## Normalization convention (for the downstream `D` agent)

`C'(r)` is the coefficient of `(ℓ₁v)²`.  The reference scale matched is

  `Cref · (A/a)² = 3ℓ₁ℓ₂(ℓ₂−ℓ₁)/a²`   (the geometric coefficient at the *actual* scale `a`),

and the drift bound (`Cref_drift_le`) is, with `b₀` set to the model slope `b1Model P.X a d`,

  `|C'(b̃) − Cref·(A/a)²| ≤ 20·(a/d)²·(Cref·(A/a)²)`,

i.e. a *relative* `O((a/d)²) = O((Ω/H)²)` drift.  Here `a ≍ A` makes the `(A/a)²` factor a
bounded (non-small) renormalization, while the `20(a/d)²` is the genuine flatness gain that feeds
the additive `E`-budget at scale `V_s` downstream.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

noncomputable section

/-- Remainder in the small-`t` expansion of the normalized leading `(ℓ₁v)²` coefficient shape.
`Cshape t = 1 − (9/2)t² + t³·CshapeRem t`. -/
private def CshapeRem (t : ℝ) : ℝ := -(10 * t + 17) / (2 * (2 + t))

/-- Normalized leading `(ℓ₁v)²` coefficient shape after writing `t = a/d`.  Up to the geometric
factor `3ℓ₁ℓ₂(ℓ₂−ℓ₁)/a²`, this is the bracket-included per-`r` quadratic coefficient obtained by
substituting the first-derivative model `b1Model` for `b₀`. -/
def Cshape (t : ℝ) : ℝ := (1 / 2 : ℝ) * (((1 + t) ^ 3 / (2 + t)) * (4 - 10 * t))

/-- Exact cancellation: the normalized shape has **no linear term** in `t`.  After subtracting the
constant value `1`, what remains is divisible by `t²`. -/
private theorem Cshape_sub_one_eq {t : ℝ} (ht : 2 + t ≠ 0) :
    Cshape t - 1 = t ^ 2 * (-(9 / 2 : ℝ) + t * CshapeRem t) := by
  unfold Cshape CshapeRem
  field_simp
  ring

/-- Quantitative flatness: on the small-parameter range `0 ≤ t ≤ 1`, the normalized shape departs
from its constant value `1` by at most `20·t²`.  This is the `r`-independence input: the per-`r`
coefficient is `Cref` up to a relative `O(t²)` drift. -/
theorem Cshape_abs_sub_one_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Cshape t - 1| ≤ 20 * t ^ 2 := by
  have ht2 : 2 + t ≠ 0 := by nlinarith
  have hshape := Cshape_sub_one_eq (t := t) ht2
  have hden_pos : 0 < 2 * (2 + t) := by positivity
  have hnum_nonneg : 0 ≤ 10 * t + 17 := by nlinarith
  have hrem_abs : |CshapeRem t| ≤ (27 / 4 : ℝ) := by
    have hrem_eq : |CshapeRem t| = (10 * t + 17) / (2 * (2 + t)) := by
      have hfrac_nonneg : 0 ≤ (10 * t + 17) / (2 * (2 + t)) :=
        div_nonneg hnum_nonneg hden_pos.le
      unfold CshapeRem
      rw [abs_of_nonpos]
      · ring
      · have hneg : -((10 * t + 17) / (2 * (2 + t))) ≤ 0 :=
          neg_nonpos.mpr hfrac_nonneg
        convert hneg using 1
        ring
    rw [hrem_eq, div_le_iff₀ hden_pos]
    nlinarith
  have hq : |-(9 / 2 : ℝ) + t * CshapeRem t| ≤ (12 : ℝ) := by
    calc
      |-(9 / 2 : ℝ) + t * CshapeRem t|
          ≤ |-(9 / 2 : ℝ)| + |t * CshapeRem t| := abs_add_le _ _
      _ = (9 / 2 : ℝ) + t * |CshapeRem t| := by
            rw [show |(-(9 / 2 : ℝ))| = (9 / 2 : ℝ) by norm_num, abs_mul, abs_of_nonneg ht0]
      _ ≤ (9 / 2 : ℝ) + t * (27 / 4 : ℝ) := by
            nlinarith [mul_le_mul_of_nonneg_left hrem_abs ht0]
      _ ≤ (12 : ℝ) := by nlinarith
  rw [hshape, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
  calc
    t ^ 2 * |-(9 / 2 : ℝ) + t * CshapeRem t|
        ≤ t ^ 2 * 12 := mul_le_mul_of_nonneg_left hq (pow_nonneg ht0 _)
    _ ≤ t ^ 2 * 20 := mul_le_mul_of_nonneg_left (by norm_num) (pow_nonneg ht0 _)
    _ = 20 * t ^ 2 := by ring

/-- Sharper form of `Cshape_abs_sub_one_le` (the proof's own intermediate constant `12`). -/
theorem Cshape_abs_sub_one_le12 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Cshape t - 1| ≤ 12 * t ^ 2 := by
  have ht2 : 2 + t ≠ 0 := by nlinarith
  have hshape := Cshape_sub_one_eq (t := t) ht2
  have hden_pos : 0 < 2 * (2 + t) := by positivity
  have hnum_nonneg : 0 ≤ 10 * t + 17 := by nlinarith
  have hrem_abs : |CshapeRem t| ≤ (27 / 4 : ℝ) := by
    have hrem_eq : |CshapeRem t| = (10 * t + 17) / (2 * (2 + t)) := by
      have hfrac_nonneg : 0 ≤ (10 * t + 17) / (2 * (2 + t)) :=
        div_nonneg hnum_nonneg hden_pos.le
      unfold CshapeRem
      rw [abs_of_nonpos]
      · ring
      · have hneg : -((10 * t + 17) / (2 * (2 + t))) ≤ 0 :=
          neg_nonpos.mpr hfrac_nonneg
        convert hneg using 1
        ring
    rw [hrem_eq, div_le_iff₀ hden_pos]
    nlinarith
  have hq : |-(9 / 2 : ℝ) + t * CshapeRem t| ≤ (12 : ℝ) := by
    calc
      |-(9 / 2 : ℝ) + t * CshapeRem t|
          ≤ |-(9 / 2 : ℝ)| + |t * CshapeRem t| := abs_add_le _ _
      _ = (9 / 2 : ℝ) + t * |CshapeRem t| := by
            rw [show |(-(9 / 2 : ℝ))| = (9 / 2 : ℝ) by norm_num, abs_mul, abs_of_nonneg ht0]
      _ ≤ (9 / 2 : ℝ) + t * (27 / 4 : ℝ) := by
            nlinarith [mul_le_mul_of_nonneg_left hrem_abs ht0]
      _ ≤ (12 : ℝ) := by nlinarith
  rw [hshape, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
  calc
    t ^ 2 * |-(9 / 2 : ℝ) + t * CshapeRem t|
        ≤ t ^ 2 * 12 := mul_le_mul_of_nonneg_left hq (pow_nonneg ht0 _)
    _ = 12 * t ^ 2 := by ring

/-- The first-derivative model for the secant slope `b₀`, expressed as a function of `d`.  This is
the value of `b₀` forced by differentiating `ρ = Xa³/(d²(d+a)²)` and solving (`largeDefectD1AtDModel`
in attempt-1).  Keeping it a standalone rational expression makes the flatness identity pure field
algebra. -/
def b1Model (X a d : ℝ) : ℝ :=
  -(d ^ 3 * (d + a) ^ 3) / (2 * X * a ^ 3 * (2 * d + a))

/-- The per-`r` **bracket-included** quadratic coefficient: the coefficient of `(ℓ₁v)²` subtracted
in `Sigma_closed_parabola_sharp`,
`C'(r) = (Xa/d⁵)·(−4+10a/d)·3ℓ₁ℓ₂(ℓ₂−ℓ₁)b₀`. -/
def Cprime (X a b₀ d ℓ₁ ℓ₂ : ℝ) : ℝ :=
  (X * a / d ^ 5) * (-4 + 10 * a / d) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀)

/-- **The `r`-independent reference parabola coefficient** (attempt-1 `largeDefectSigmaMainCoeffMd`).
`Cref = 3ℓ₁ℓ₂(ℓ₂−ℓ₁)/(Δ²Ω²)`; note `Δ²Ω² = A²`, so this is the geometric coefficient at the fixed
scale `A`, free of `a`, `d`, `b₀`, `X`. -/
def Cref (P : Globals) (S : Scale P) (ℓ₁ ℓ₂ : ℝ) : ℝ :=
  3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (S.Δ ^ 2 * S.Ω ^ 2)

/-- `Cref > 0` for `0 < ℓ₁ < ℓ₂`. -/
theorem Cref_pos {ℓ₁ ℓ₂ : ℝ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    0 < Cref P S ℓ₁ ℓ₂ := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have h21 : 0 < ℓ₂ - ℓ₁ := by linarith
  unfold Cref
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) hℓ1) hℓ2) h21)
    (mul_pos (pow_pos hΔ 2) (pow_pos hΩ 2))

/-- **The flatness identity** (port of `largeDefectSigmaQuadraticCoeffReal_d1Model_eq_shape`).
Substituting the first-derivative model `b1Model X a d` for `b₀` turns the per-`r` coefficient into
the geometric coefficient `3ℓ₁ℓ₂(ℓ₂−ℓ₁)/a²` times the normalized shape `Cshape (a/d)`. -/
theorem Cprime_b1Model_eq {X a d ℓ₁ ℓ₂ : ℝ}
    (hX : X ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) (h2da : 2 * d + a ≠ 0) :
    Cprime X a (b1Model X a d) d ℓ₁ ℓ₂
      = (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2) * Cshape (a / d) := by
  have h2t : 2 + a / d ≠ 0 := by
    intro h
    have hm : d * (2 + a / d) = 0 := by rw [h, mul_zero]
    have hrewrite : d * (2 + a / d) = 2 * d + a := by field_simp
    rw [hrewrite] at hm
    exact h2da hm
  unfold Cprime b1Model Cshape
  field_simp
  ring

/-- **Step-4 flat-coefficient drift bound** (writeup 1052 flatness piece).  With `b₀` set to the
first-derivative model slope `b1Model P.X a d`, the per-`r` bracket-included quadratic coefficient
`C'(r)` deviates from the fixed reference `Cref·(A/a)²` by at most a *relative* `20·(a/d)²`, where
`a/d ≍ A/D = Ω/H`.  This is the `r`-independent reference that the two-point square-difference
needs; the `(a/d)²` gain feeds the additive `E`-budget at scale `V_s` downstream. -/
theorem Cref_drift_le {a d ℓ₁ ℓ₂ : ℝ}
    (ha : 0 < a) (hd : 0 < d) (had : a ≤ d)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    |Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2|
      ≤ 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) := by
  have hX := P.X_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have h21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have h2da : 2 * d + a ≠ 0 := by positivity
  -- bridge: `Cref·(A/a)²` is the geometric coefficient at the actual scale `a`
  have hbridge : Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 := by
    unfold Cref Scale.A
    field_simp
  have hCgeom_pos : 0 < 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) hℓ1) hℓ2) h21) (pow_pos ha 2)
  -- the flatness identity and the shape bound on `t = a/d ∈ [0,1]`
  have hid := Cprime_b1Model_eq (X := P.X) (a := a) (d := d) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    hX.ne' ha.ne' hd.ne' h2da
  have ht0 : 0 ≤ a / d := (div_pos ha hd).le
  have ht1 : a / d ≤ 1 := (div_le_one hd).mpr had
  have hflat := Cshape_abs_sub_one_le ht0 ht1
  rw [hbridge, hid,
    show 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * Cshape (a / d)
        - 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2
      = (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2) * (Cshape (a / d) - 1) by ring,
    abs_mul, abs_of_pos hCgeom_pos]
  calc
    3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * |Cshape (a / d) - 1|
        ≤ 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * (20 * (a / d) ^ 2) :=
          mul_le_mul_of_nonneg_left hflat hCgeom_pos.le
    _ = 20 * (a / d) ^ 2 * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2) := by ring

/-- **`Cref`-drift through the ε-relaxed `D`-window**: with `d ≥ D(1−10⁻⁹)`, the flat drift is
still `≤ 20·(a/D)²·Ĉ₀` (the sharper internal constant `12` absorbs the window slack). -/
theorem Cref_drift_le_winD {a d ℓ₁ ℓ₂ : ℝ}
    (ha : 0 < a) (hd : 0 < d) (had : a ≤ d)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    |Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2|
      ≤ 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) := by
  have hX := P.X_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have h21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have h2da : 2 * d + a ≠ 0 := by positivity
  have hbridge : Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 := by
    unfold Cref Scale.A
    field_simp
  have hCgeom_pos : 0 < 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) hℓ1) hℓ2) h21) (pow_pos ha 2)
  have hid := Cprime_b1Model_eq (X := P.X) (a := a) (d := d) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    hX.ne' ha.ne' hd.ne' h2da
  have ht0 : 0 ≤ a / d := (div_pos ha hd).le
  have ht1 : a / d ≤ 1 := (div_le_one hd).mpr had
  have hflat := Cshape_abs_sub_one_le12 ht0 ht1
  -- window conversion : 12·(a/d)² ≤ 20·(a/D)²
  have hDeps : (0:ℝ) < S.D * (1 - 1/10 ^ 9) := by nlinarith [hDpos]
  have hsq : (a / d) ^ 2 ≤ (a / (S.D * (1 - 1/10 ^ 9))) ^ 2 :=
    pow_le_pow_left₀ ht0 (div_le_div_of_nonneg_left ha.le hDeps hdD) 2
  have hconv : 12 * (a / d) ^ 2 ≤ 20 * (a / S.D) ^ 2 := by
    have he : (a / (S.D * (1 - 1/10 ^ 9))) ^ 2
        = (a / S.D) ^ 2 * (1 / (1 - 1/10 ^ 9)) ^ 2 := by
      field_simp
    have hcc : (12:ℝ) * (1 / (1 - 1/10 ^ 9)) ^ 2 ≤ 20 := by norm_num
    nlinarith [hsq, he.le, he.ge, sq_nonneg (a / S.D), sq_nonneg (a / d)]
  rw [hbridge, hid,
    show 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * Cshape (a / d)
        - 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2
      = (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2) * (Cshape (a / d) - 1) by ring,
    abs_mul, abs_of_pos hCgeom_pos]
  calc
    3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * |Cshape (a / d) - 1|
        ≤ 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * (12 * (a / d) ^ 2) :=
          mul_le_mul_of_nonneg_left hflat hCgeom_pos.le
    _ ≤ 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 * (20 * (a / S.D) ^ 2) :=
          mul_le_mul_of_nonneg_left hconv hCgeom_pos.le
    _ = 20 * (a / S.D) ^ 2 * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2) := by ring

end

end Squarefree
