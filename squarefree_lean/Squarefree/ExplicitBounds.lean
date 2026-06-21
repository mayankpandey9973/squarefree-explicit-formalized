import Mathlib
import Squarefree.Upper.Regime
import Squarefree.DyadicAssembly
import Squarefree.MobiusAssembly
import Squarefree.Explicit

/-!
# Explicit numeric bound on the §6 spine constant `C6val`

This leaf file proves the single explicit estimate `C6val ≤ 10 ^ 20`, where
`C6val = max prop6lowF_C prop6highF_C` is the §6 constant assembled in
`Squarefree.Upper.Regime`.  The two branch constants contain `rpow`/`sqrt`/`log`
factors; each is bounded through small dedicated helper lemmas proved on clean goals
(quarter and cube root comparisons, square-root and log numerics) and then assembled.
-/

namespace Squarefree

open Real

/-- `x^{1/4} ≤ c` from `x ≤ c⁴` (clean rpow comparison). -/
private lemma rpow_quarter_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c ^ 4) :
    x ^ (1 / 4 : ℝ) ≤ c := by
  calc x ^ (1 / 4 : ℝ) ≤ (c ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
    _ = c := by
        rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast hc (by norm_num)

/-- `c ≤ x^{1/4}` from `c⁴ ≤ x` (clean rpow comparison). -/
private lemma le_rpow_quarter {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 4 ≤ x) :
    c ≤ x ^ (1 / 4 : ℝ) := by
  have hx : 0 ≤ x := le_trans (by positivity) h
  calc c = (c ^ 4) ^ (1 / 4 : ℝ) := by
            rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
            exact (Real.pow_rpow_inv_natCast hc (by norm_num)).symm
    _ ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- `x^{1/3} ≤ c` from `x ≤ c³` (clean rpow comparison). -/
private lemma rpow_third_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c ^ 3) :
    x ^ (1 / 3 : ℝ) ≤ c := by
  calc x ^ (1 / 3 : ℝ) ≤ (c ^ 3) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
    _ = c := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast hc (by norm_num)

/-! ### Sub-bounds on the individual constants. -/

private lemma Cval6_le : Cval6 ≤ 40 := by
  unfold Cval6
  exact rpow_quarter_le (by norm_num) (by norm_num) (by norm_num)

private lemma K0_le : K0 ≤ 10064704 := by unfold K0 C_ncmem; norm_num

private lemma pLo_ge : (1 / 2000 : ℝ) ≤ prop6ScaleLo := by
  unfold prop6ScaleLo
  exact le_rpow_quarter (by norm_num) (by norm_num)

private lemma cderiv6_ge : (1 / 60 : ℝ) ≤ cderiv6 := by
  have h17 : Real.sqrt 17 ≤ 21 / 5 := by
    rw [show (21 / 5 : ℝ) = Real.sqrt ((21 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h17pos : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have hfrac : (50 / 21 : ℝ) ≤ 10 / Real.sqrt 17 := by
    rw [le_div_iff₀ h17pos]; nlinarith [h17]
  have hZ : (3 / 400 : ℝ) ≤ ((1 / 72 : ℝ) ^ 3 * (1 / 2 : ℝ) ^ 9) ^ (1 / 4 : ℝ) :=
    le_rpow_quarter (by norm_num) (by norm_num)
  unfold cderiv6
  calc (1 / 60 : ℝ) ≤ (50 / 21) * (3 / 400) := by norm_num
    _ ≤ (10 / Real.sqrt 17) * ((1 / 72 : ℝ) ^ 3 * (1 / 2 : ℝ) ^ 9) ^ (1 / 4 : ℝ) :=
        mul_le_mul hfrac hZ (by norm_num) (le_trans (by norm_num) hfrac)

private lemma pHi_third_le : prop6ScaleHi ^ (1 / 3 : ℝ) ≤ 4 := by
  have hle : prop6ScaleHi ≤ 51 := by
    unfold prop6ScaleHi
    exact rpow_quarter_le (by norm_num) (by norm_num) (by norm_num)
  exact rpow_third_le prop6ScaleHi_pos.le (by norm_num) (by nlinarith [hle])

private lemma sqrt_inv_pLo_le : Real.sqrt (1 / prop6ScaleLo) ≤ 45 := by
  have h1 : 1 / prop6ScaleLo ≤ 2000 := by
    rw [div_le_iff₀ prop6ScaleLo_pos]; nlinarith [pLo_ge]
  calc Real.sqrt (1 / prop6ScaleLo) ≤ Real.sqrt (45 ^ 2) :=
        Real.sqrt_le_sqrt (le_trans h1 (by norm_num))
    _ = 45 := Real.sqrt_sq (by norm_num)

private lemma sqrt_K0_le : Real.sqrt K0 ≤ 3173 := by
  calc Real.sqrt K0 ≤ Real.sqrt (3173 ^ 2) := Real.sqrt_le_sqrt (le_trans K0_le (by norm_num))
    _ = 3173 := Real.sqrt_sq (by norm_num)

private lemma log_2sqrtK0_le : Real.log (2 + Real.sqrt K0) ≤ 9 := by
  have hb : 2 + Real.sqrt K0 ≤ 4096 := by linarith [sqrt_K0_le]
  have hpos : 0 < 2 + Real.sqrt K0 := by positivity
  calc Real.log (2 + Real.sqrt K0) ≤ Real.log 4096 := Real.log_le_log hpos hb
    _ ≤ 9 := by
        rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
        push_cast
        nlinarith [Real.log_two_lt_d9]

private lemma sqrt_K0_div_pLo_le : Real.sqrt (K0 / prop6ScaleLo) ≤ 142000 := by
  have hKpLo : K0 / prop6ScaleLo ≤ 20129408000 := by
    rw [div_le_iff₀ prop6ScaleLo_pos]; nlinarith [K0_le, pLo_ge]
  calc Real.sqrt (K0 / prop6ScaleLo) ≤ Real.sqrt (142000 ^ 2) :=
        Real.sqrt_le_sqrt (le_trans hKpLo (by norm_num))
    _ = 142000 := Real.sqrt_sq (by norm_num)

private lemma prop6CountConst_le : prop6CountConst = 109159296 := by
  unfold prop6CountConst Squarefree.Geometry.C_nearCurveCount Squarefree.Geometry.C_prop43local
  rw [max_eq_left (show (2 : ℝ) ≤ 109159296 by norm_num)]

/-! ### Assembling the two branch bounds. -/

private lemma prop6lowF_C_le : Prop61.prop6lowF_C ≤ (10 : ℝ) ^ 20 := by
  have hLo := pLo_ge
  have hLopos := prop6ScaleLo_pos
  -- the inner factor `B`
  have ht1 : 2 * Cval6 / prop6ScaleLo ≤ 160000 := by
    rw [div_le_iff₀ hLopos]; nlinarith [Cval6_le, hLo]
  have ht2 : 2 * K0 / (prop6ScaleLo * 16777216) ≤ 2400 := by
    rw [div_le_iff₀ (mul_pos hLopos (by norm_num))]; nlinarith [K0_le, hLo]
  have hBle : 2 * Cval6 / prop6ScaleLo + 2 * K0 / (prop6ScaleLo * 16777216) + 1 ≤ 163000 := by
    linarith [ht1, ht2]
  have hBnn : 0 ≤ 2 * Cval6 / prop6ScaleLo + 2 * K0 / (prop6ScaleLo * 16777216) + 1 := by
    have a1 : 0 ≤ 2 * Cval6 / prop6ScaleLo :=
      div_nonneg (mul_nonneg (by norm_num) Cval6_pos.le) hLopos.le
    have a2 : 0 ≤ 2 * K0 / (prop6ScaleLo * 16777216) :=
      div_nonneg (mul_nonneg (by norm_num) K0_pos.le) (mul_pos hLopos (by norm_num)).le
    linarith [a1, a2]
  have hP1le : 64 * K0 / cderiv6 ≤ 38648463360 := by
    rw [div_le_iff₀ cderiv6_pos]; nlinarith [K0_le, cderiv6_ge]
  have hP1nn : 0 ≤ 64 * K0 / cderiv6 :=
    div_nonneg (mul_nonneg (by norm_num) K0_pos.le) cderiv6_pos.le
  have hQnn : 0 ≤ Real.sqrt (1 / prop6ScaleLo) := Real.sqrt_nonneg _
  -- abstract `B` so the products are atomic for `nlinarith`
  unfold Prop61.prop6lowF_C
  set B := 2 * Cval6 / prop6ScaleLo + 2 * K0 / (prop6ScaleLo * 16777216) + 1 with hBdef
  have hm1 : B * (64 * K0 / cderiv6) ≤ 163000 * 38648463360 :=
    mul_le_mul hBle hP1le hP1nn (by norm_num)
  have hm2 : B * Real.sqrt (1 / prop6ScaleLo) ≤ 163000 * 45 :=
    mul_le_mul hBle sqrt_inv_pLo_le hQnn (by norm_num)
  calc B * (64 * K0 / cderiv6) + 32 * B * Real.sqrt (1 / prop6ScaleLo) + 1
      ≤ 163000 * 38648463360 + 32 * (163000 * 45) + 1 := by nlinarith [hm1, hm2]
    _ ≤ (10 : ℝ) ^ 20 := by norm_num

private lemma prop6highF_C_le : Prop61.prop6highF_C ≤ (10 : ℝ) ^ 20 := by
  have hLogHalf : Real.log (2 + Real.sqrt K0) + 1 / 2 ≤ 19 / 2 := by
    linarith [log_2sqrtK0_le]
  have hLogHalf_nn : 0 ≤ Real.log (2 + Real.sqrt K0) + 1 / 2 := by
    have : 0 ≤ Real.log (2 + Real.sqrt K0) :=
      Real.log_nonneg (by nlinarith [Real.sqrt_nonneg K0])
    linarith
  have hprod : Real.sqrt (K0 / prop6ScaleLo) * (Real.log (2 + Real.sqrt K0) + 1 / 2)
      ≤ 142000 * (19 / 2) :=
    mul_le_mul sqrt_K0_div_pLo_le hLogHalf hLogHalf_nn (by norm_num)
  have hInside : prop6ScaleHi ^ (1 / 3 : ℝ) + K0
      + Real.sqrt (K0 / prop6ScaleLo) * (Real.log (2 + Real.sqrt K0) + 1 / 2)
      + Real.sqrt (1 / prop6ScaleLo) + 1 ≤ 11500000 := by
    linarith [pHi_third_le, K0_le, hprod, sqrt_inv_pLo_le]
  calc Prop61.prop6highF_C ≤ 96 * 109159296 * 11500000 + 1 := by
        unfold Prop61.prop6highF_C
        rw [prop6CountConst_le]
        nlinarith [hInside]
    _ ≤ (10 : ℝ) ^ 20 := by norm_num

/-- **Explicit bound on the §6 spine constant.** `C6val = max prop6lowF_C prop6highF_C ≤ 10²⁰`. -/
theorem C6val_le : C6val ≤ 10 ^ 20 := by
  unfold C6val
  exact max_le prop6lowF_C_le prop6highF_C_le

/-! ### Downstream §2–§9 / dyadic-assembly constants. -/

/-- The Lemma 2.1 constant at `K = 729` is `≤ 1245`. -/
private lemma C_fourthDeriv_729_le : Counting.C_fourthDeriv 729 ≤ 1245 := by
  unfold Counting.C_fourthDeriv
  refine max_le ?_ (by norm_num)
  have h8 : (4 * (2 ^ 70 * 729) : ℝ) ^ (1 / 8 : ℝ) ≤ 1200 := by
    rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    calc (4 * (2 ^ 70 * 729) : ℝ) ^ (((8 : ℕ) : ℝ)⁻¹)
          ≤ ((1200 : ℝ) ^ (8 : ℕ)) ^ (((8 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by positivity)
      _ = 1200 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h15 : (4 * (2 ^ 70 * 729) : ℝ) ^ (1 / 15 : ℝ) ≤ 45 := by
    rw [show (1 / 15 : ℝ) = ((15 : ℕ) : ℝ)⁻¹ by norm_num]
    calc (4 * (2 ^ 70 * 729) : ℝ) ^ (((15 : ℕ) : ℝ)⁻¹)
          ≤ ((45 : ℝ) ^ (15 : ℕ)) ^ (((15 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by positivity)
      _ = 45 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  linarith [h8, h15]

/-- **Prop 2.4** explicit constant: `C_prop24 ≤ 10⁴`. -/
private lemma C_prop24_le : C_prop24 ≤ 10 ^ 4 := by
  unfold C_prop24
  have hC := C_fourthDeriv_729_le
  have hCnn : (0 : ℝ) ≤ Counting.C_fourthDeriv 729 := by
    unfold Counting.C_fourthDeriv; exact le_trans (by norm_num) (le_max_right _ _)
  have h7 : (7 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
    rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    calc (7 : ℝ) ^ (((8 : ℕ) : ℝ)⁻¹) ≤ ((2 : ℝ) ^ (8 : ℕ)) ^ (((8 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
      _ = 2 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h7nn : (0 : ℝ) ≤ (7 : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hmul : Counting.C_fourthDeriv 729 * (3 + 7 ^ (1 / 8 : ℝ)) ≤ 1245 * 5 :=
    mul_le_mul hC (by linarith [h7]) (by linarith [h7nn]) (by norm_num)
  linarith [hmul, (show (10 : ℝ) ^ 4 = 10000 by norm_num)]

/-- **Prop 7.3** explicit constant: `C_prop73 ≤ 10²⁴`. -/
private lemma C_prop73_le : C_prop73 ≤ 10 ^ 24 := by
  unfold C_prop73 C_prop71 sec7_cJ sec7_cCubeIn
  norm_num

/-- The small-`Ω` block constant at `c₀ = 1` is `≤ 10⁸`. -/
private lemma dblockSmallOmega_C_le : dblockSmallOmega_C 1 ≤ 10 ^ 8 := by
  have hid : (1 / 4 : ℝ) ^ (-8 / 3 : ℝ) = (65536 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (-8 / 3 : ℝ) = (-8) * (1 / 3) by ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    congr 1
    rw [show (-8 : ℝ) = ((-8 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hle : (1 / 4 : ℝ) ^ (-8 / 3 : ℝ) ≤ 41 := by
    rw [hid]; exact rpow_third_le (by norm_num) (by norm_num) (by norm_num)
  have key : dblockSmallOmega_C 1 = 181442 * (193 + (1 / 4 : ℝ) ^ (-8 / 3 : ℝ)) := by
    unfold dblockSmallOmega_C prop32fiber_C2 prop32fiber_C1 lemma31_c
    simp only [Real.one_rpow]
    ring
  rw [key]
  calc 181442 * (193 + (1 / 4 : ℝ) ^ (-8 / 3 : ℝ)) ≤ 181442 * (193 + 41) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith [hle]
    _ ≤ 10 ^ 8 := by norm_num

/-- The on-strip block constant at `c₀ = 1` is `≤ 10⁵⁵`. -/
private lemma dblockOnStrip_C_le : dblockOnStrip_C 1 ≤ 10 ^ 55 := by
  unfold dblockOnStrip_C prop32fiberD_C2 lemma31_c C_prop73 C_prop71 sec7_cJ sec7_cCubeIn
  rw [Real.one_rpow]
  norm_num

set_option exponentiation.threshold 1000 in
/-- Clean-goal numeric core for the off-strip block bound. -/
private lemma offStrip_numeric :
    (181442 : ℝ) * (6 * 10 ^ 20 + 12 * 10 ^ 415 + 4) ≤ 10 ^ 422 := by norm_num

set_option exponentiation.threshold 1000 in
/-- The off-strip block constant at `c₀ = 1` is `≤ 10⁴²²`. -/
private lemma dblockOffStrip_C_le : dblockOffStrip_C 1 ≤ 10 ^ 422 := by
  have hC6 : StripAux.C6 ≤ (10 : ℝ) ^ 20 := C6val_le
  have hC5 : StripAux.C5 ≤ (10 : ℝ) ^ 415 := le_of_eq rfl
  have key : dblockOffStrip_C 1 = 181442 * (6 * StripAux.C6 + 12 * StripAux.C5 + 4) := by
    unfold dblockOffStrip_C prop32fiberD_C2 lemma31_c
    simp only [Real.one_rpow]
    ring
  rw [key]
  calc 181442 * (6 * StripAux.C6 + 12 * StripAux.C5 + 4)
      ≤ 181442 * (6 * 10 ^ 20 + 12 * 10 ^ 415 + 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hC6, hC5]
    _ ≤ 10 ^ 422 := offStrip_numeric

/-- The merged per-Ω block constant is `≤ 10⁴²²` (uniformly in `g`). -/
private lemma dblockBound_C_le : ∀ g : ℝ, dblockBound_C g ≤ 10 ^ 422 := by
  intro g
  unfold dblockBound_C
  exact max_le dblockOffStrip_C_le
    (le_trans dblockOnStrip_C_le (pow_le_pow_right₀ (by norm_num) (by norm_num)))

set_option exponentiation.threshold 1000 in
/-- Clean-goal numeric core for the dyadic-assembly constant. -/
private lemma keyDyadic_numeric : (6 : ℝ) * 10 ^ 422 + 6 + 10 ^ 4 ≤ 10 ^ 423 := by norm_num

/-- **Key dyadic assembly** explicit constant: `keyDyadic_C g ≤ 10⁴²³` (uniformly in `g`). -/
private lemma keyDyadic_C_le : ∀ g : ℝ, keyDyadic_C g ≤ 10 ^ 423 := by
  intro g
  unfold keyDyadic_C dblockBound_c0
  have hmax : max (dblockBound_C g) (dblockSmallOmega_C 1) ≤ 10 ^ 422 :=
    max_le (dblockBound_C_le g)
      (le_trans dblockSmallOmega_C_le (pow_le_pow_right₀ (by norm_num) (by norm_num)))
  have h24 : C_prop24 ≤ 10 ^ 4 := C_prop24_le
  calc 6 * max (dblockBound_C g) (dblockSmallOmega_C 1) + 6 + C_prop24
      ≤ 6 * 10 ^ 422 + 6 + 10 ^ 4 := by gcongr
    _ ≤ 10 ^ 423 := keyDyadic_numeric

/-! ## Explicit `ε`-dependence of the squarefree-interval savings/constant

We set `ε' := min ε (1/90935)` and bound the `count_short_interval` savings exponent
`countSI_u (gEff ε)` from below by `ε'/10²⁵` and its constant `countSI_C (gEff ε)` from
above by `10⁴⁵⁰/ε'`.  Both go through the `gEff` algebraic identities. -/

/-- Definitional unfolding of `gEff`, used to feed `ring`. -/
private lemma gEff_eq (ε : ℝ) : gEff ε = 2 / 18187 - 5 * min ε (1 / 90935) := rfl

/-- Lower bound on the §2.4 dyadic-block savings exponent. -/
private lemma dblockBound_u_lower (ε : ℝ) (hε : 0 < ε) :
    min ε (1 / 90935) / 10 ^ 21 ≤ dblockBound_u (gEff ε) := by
  have hM0 : 0 < min ε (1 / 90935) := lt_min hε (by norm_num)
  have hMle : min ε (1 / 90935) ≤ 1 / 90935 := min_le_right _ _
  have hC6 : StripAux.C6 ≤ (10 : ℝ) ^ 20 := C6val_le
  have hC6pos : 0 < StripAux.C6 := StripAux.C6_pos
  -- numerator of the off-strip budget is `≥ 1/400`
  have hnum1 : (1 : ℝ) / 400 ≤ 1 / 200 - 20 * gEff ε := by
    have e : (1 : ℝ) / 200 - 20 * gEff ε
        = 1 / 200 - 40 / 18187 + 100 * min ε (1 / 90935) := by rw [gEff_eq]; ring
    rw [e]; linarith [hM0.le]
  -- the `2 - 18187 g` numerator equals `90935 ε'`
  have enum2 : (2 : ℝ) - 18187 * gEff ε = 90935 * min ε (1 / 90935) := by rw [gEff_eq]; ring
  have hd1 : (0 : ℝ) < StripAux.C6 + 100 := by linarith
  have hd2 : (0 : ℝ) < 18675 + 790 * ((3 / 2) * StripAux.C6 + 232) := by nlinarith
  -- off-strip branch
  have hT1 : 2 * min ε (1 / 90935) / 10 ^ 21
      ≤ (1 / 200 - 20 * gEff ε) / (StripAux.C6 + 100) := by
    rw [le_div_iff₀ hd1]
    calc 2 * min ε (1 / 90935) / 10 ^ 21 * (StripAux.C6 + 100)
        ≤ 2 * (1 / 90935) / 10 ^ 21 * (10 ^ 20 + 100) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right (by linarith [hMle]) (by norm_num)
          · linarith [hC6]
          · linarith
          · positivity
      _ ≤ 1 / 400 := by norm_num
      _ ≤ 1 / 200 - 20 * gEff ε := hnum1
  -- on-strip branch
  have hD2le : 2 * (18675 + 790 * ((3 / 2) * StripAux.C6 + 232)) / 10 ^ 21 ≤ 90935 := by
    calc 2 * (18675 + 790 * ((3 / 2) * StripAux.C6 + 232)) / 10 ^ 21
        ≤ 2 * (18675 + 790 * ((3 / 2) * (10 ^ 20) + 232)) / 10 ^ 21 :=
          div_le_div_of_nonneg_right (by linarith [hC6]) (by norm_num)
      _ ≤ 90935 := by norm_num
  have hT2 : 2 * min ε (1 / 90935) / 10 ^ 21
      ≤ (2 - 18187 * gEff ε) / (18675 + 790 * ((3 / 2) * StripAux.C6 + 232)) := by
    rw [le_div_iff₀ hd2, enum2]
    have heq : 2 * min ε (1 / 90935) / 10 ^ 21
          * (18675 + 790 * ((3 / 2) * StripAux.C6 + 232))
        = (2 * (18675 + 790 * ((3 / 2) * StripAux.C6 + 232)) / 10 ^ 21)
          * min ε (1 / 90935) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hD2le hM0.le
  -- cap branch
  have h100 : 2 * min ε (1 / 90935) / 10 ^ 21 ≤ 1 / 100 := by
    calc 2 * min ε (1 / 90935) / 10 ^ 21 ≤ 2 * (1 / 90935) / 10 ^ 21 :=
          div_le_div_of_nonneg_right (by linarith [hMle]) (by norm_num)
      _ ≤ 1 / 100 := by norm_num
  unfold dblockBound_u
  have hmin : 2 * min ε (1 / 90935) / 10 ^ 21
      ≤ min ((1 / 200 - 20 * gEff ε) / (StripAux.C6 + 100))
          (min ((2 - 18187 * gEff ε) / (18675 + 790 * ((3 / 2) * StripAux.C6 + 232))) (1 / 100)) :=
    le_min hT1 (le_min hT2 h100)
  linarith [hmin]

/-- Lower bound on the key-dyadic-assembly savings exponent. -/
private lemma keyDyadic_u_lower (ε : ℝ) (hε : 0 < ε) :
    min ε (1 / 90935) / 10 ^ 22 ≤ keyDyadic_u (gEff ε) := by
  have hM0 : 0 < min ε (1 / 90935) := lt_min hε (by norm_num)
  have hMle : min ε (1 / 90935) ≤ 1 / 90935 := min_le_right _ _
  have hdb : min ε (1 / 90935) / 10 ^ 21 ≤ dblockBound_u (gEff ε) := dblockBound_u_lower ε hε
  unfold keyDyadic_u
  apply le_min
  · have h1 : min ε (1 / 90935) / 10 ^ 22 ≤ (min ε (1 / 90935) / 10 ^ 21) / 2 := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hM0.le (by norm_num) (by norm_num)
    calc min ε (1 / 90935) / 10 ^ 22 ≤ (min ε (1 / 90935) / 10 ^ 21) / 2 := h1
      _ ≤ dblockBound_u (gEff ε) / 2 := by linarith [hdb]
  · calc min ε (1 / 90935) / 10 ^ 22 ≤ (1 / 90935) / 10 ^ 22 :=
          div_le_div_of_nonneg_right hMle (by norm_num)
      _ ≤ u_prop24 := by unfold u_prop24; norm_num

/-- **(B0)** Lower bound on the `count_short_interval` savings exponent in terms of `ε`. -/
lemma countSI_u_lower (ε : ℝ) (hε : 0 < ε) :
    min ε (1 / 90935) / 10 ^ 25 ≤ Mob.countSI_u (gEff ε) := by
  have hM0 : 0 < min ε (1 / 90935) := lt_min hε (by norm_num)
  have hMle : min ε (1 / 90935) ≤ 1 / 90935 := min_le_right _ _
  have hku : min ε (1 / 90935) / 10 ^ 22 ≤ keyDyadic_u (gEff ε) := keyDyadic_u_lower ε hε
  have h1g : (1 : ℝ) / 20 ≤ (1 - gEff ε) / 5 / 2 := by
    have e3 : (1 - gEff ε) / 5 / 2 = (1 - 2 / 18187 + 5 * min ε (1 / 90935)) / 10 := by
      rw [gEff_eq]; ring
    rw [e3]; linarith [hM0.le]
  unfold Mob.countSI_u
  have hmin2 : min ε (1 / 90935) / 10 ^ 22
      ≤ min (keyDyadic_u (gEff ε)) ((1 - gEff ε) / 5 / 2) := by
    apply le_min hku
    calc min ε (1 / 90935) / 10 ^ 22 ≤ (1 / 90935) / 10 ^ 22 :=
          div_le_div_of_nonneg_right hMle (by norm_num)
      _ ≤ 1 / 20 := by norm_num
      _ ≤ (1 - gEff ε) / 5 / 2 := h1g
  calc min ε (1 / 90935) / 10 ^ 25 ≤ (min ε (1 / 90935) / 10 ^ 22) / 2 := by
        rw [div_div]
        exact div_le_div_of_nonneg_left hM0.le (by norm_num) (by norm_num)
    _ ≤ min (keyDyadic_u (gEff ε)) ((1 - gEff ε) / 5 / 2) / 2 := by linarith [hmin2]

set_option exponentiation.threshold 1000 in
/-- Clean-goal numeric core for the `count_short_interval` constant upper bound. -/
private lemma countSI_C_numeric {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) :
    7 + ((10 ^ 423 + 1) * (1 + 10 ^ 23 / M) + 20 + 1) ≤ 10 ^ 450 / M := by
  have hMne : M ≠ 0 := ne_of_gt hM0
  rw [le_div_iff₀ hM0]
  have hrw : (7 + ((10 ^ 423 + 1) * (1 + 10 ^ 23 / M) + 20 + 1)) * M
      = 28 * M + (10 ^ 423 + 1) * M + (10 ^ 423 + 1) * 10 ^ 23 := by
    field_simp
    ring
  rw [hrw]
  have a1 : 28 * M ≤ 28 := by nlinarith [hM1]
  have a2 : (10 ^ 423 + 1) * M ≤ 10 ^ 423 + 1 := by
    nlinarith [hM1, (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 423 + 1)]
  have a3 : (28 : ℝ) + (10 ^ 423 + 1) + (10 ^ 423 + 1) * 10 ^ 23 ≤ 10 ^ 450 := by norm_num
  linarith [a1, a2, a3]

set_option exponentiation.threshold 1000 in
/-- **(B1)** Upper bound on the `count_short_interval` constant in terms of `ε`. -/
lemma countSI_C_upper (ε : ℝ) (hε : 0 < ε) :
    Mob.countSI_C (gEff ε) ≤ 10 ^ 450 / min ε (1 / 90935) := by
  have hM0 : 0 < min ε (1 / 90935) := lt_min hε (by norm_num)
  have hMle : min ε (1 / 90935) ≤ 1 / 90935 := min_le_right _ _
  have hMle1 : min ε (1 / 90935) ≤ 1 := le_trans hMle (by norm_num)
  have hku : min ε (1 / 90935) / 10 ^ 22 ≤ keyDyadic_u (gEff ε) := keyDyadic_u_lower ε hε
  have hkC : keyDyadic_C (gEff ε) ≤ 10 ^ 423 := keyDyadic_C_le (gEff ε)
  -- `countSI_u ≤ keyDyadic_u/2` and `keyDyadic_u ≤ 1/200`
  have hcu_le : Mob.countSI_u (gEff ε) ≤ keyDyadic_u (gEff ε) / 2 := by
    unfold Mob.countSI_u
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hku_le : keyDyadic_u (gEff ε) ≤ 1 / 200 := by
    unfold keyDyadic_u u_prop24; exact min_le_right _ _
  have hcu_400 : Mob.countSI_u (gEff ε) ≤ 1 / 400 := by linarith [hcu_le, hku_le]
  -- first inverse: `keyDyadic_u - countSI_u ≥ ε'/(2·10²²) > 0`
  have heqd : min ε (1 / 90935) / (2 * 10 ^ 22) = (min ε (1 / 90935) / 10 ^ 22) / 2 := by ring
  have ha : min ε (1 / 90935) / (2 * 10 ^ 22) ≤ keyDyadic_u (gEff ε) / 2 := by
    rw [heqd]; linarith [hku]
  have hsub_pos : min ε (1 / 90935) / (2 * 10 ^ 22)
      ≤ keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε) := by linarith [ha, hcu_le]
  have hsubpos2 : 0 < min ε (1 / 90935) / (2 * 10 ^ 22) := div_pos hM0 (by norm_num)
  have hpos : 0 < keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε) := lt_of_lt_of_le hsubpos2 hsub_pos
  have hlog : (1 : ℝ) ≤ 2 * Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogpos : (0 : ℝ) ≤ 2 * Real.log 2 := by linarith
  have hinv1 : (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹
      ≤ 2 * 10 ^ 22 / min ε (1 / 90935) := by
    rw [inv_eq_one_div]
    calc 1 / (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))
        ≤ 1 / (min ε (1 / 90935) / (2 * 10 ^ 22)) :=
          one_div_le_one_div_of_le hsubpos2 hsub_pos
      _ = 2 * 10 ^ 22 / min ε (1 / 90935) := by rw [one_div_div]
  have hA0 : 0 ≤ (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹ :=
    le_of_lt (inv_pos.mpr hpos)
  have hA : (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹ / (2 * Real.log 2)
      ≤ 10 ^ 23 / min ε (1 / 90935) := by
    calc (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹ / (2 * Real.log 2)
        ≤ (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹ := div_le_self hA0 hlog
      _ ≤ 2 * 10 ^ 22 / min ε (1 / 90935) := hinv1
      _ ≤ 10 ^ 23 / min ε (1 / 90935) :=
          div_le_div_of_nonneg_right (by norm_num) hM0.le
  have hA0' : 0 ≤ (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹ / (2 * Real.log 2) :=
    div_nonneg hA0 hlogpos
  -- second inverse: `(1-g)/5 - countSI_u ≥ 1/20`
  have h15 : (1 : ℝ) / 10 ≤ (1 - gEff ε) / 5 := by
    have e : (1 - gEff ε) / 5 = (1 - 2 / 18187 + 5 * min ε (1 / 90935)) / 5 := by
      rw [gEff_eq]; ring
    rw [e]; linarith [hM0.le]
  have hden2 : (1 : ℝ) / 20 ≤ (1 - gEff ε) / 5 - Mob.countSI_u (gEff ε) := by
    linarith [h15, hcu_400]
  have hden2pos : 0 < (1 - gEff ε) / 5 - Mob.countSI_u (gEff ε) := by linarith [hden2]
  have hB : ((1 - gEff ε) / 5 - Mob.countSI_u (gEff ε))⁻¹ / (2 * Real.log 2) ≤ 20 := by
    calc ((1 - gEff ε) / 5 - Mob.countSI_u (gEff ε))⁻¹ / (2 * Real.log 2)
        ≤ ((1 - gEff ε) / 5 - Mob.countSI_u (gEff ε))⁻¹ :=
          div_le_self (le_of_lt (inv_pos.mpr hden2pos)) hlog
      _ ≤ 20 := by
          rw [inv_eq_one_div]
          calc 1 / ((1 - gEff ε) / 5 - Mob.countSI_u (gEff ε))
              ≤ 1 / (1 / 20) := one_div_le_one_div_of_le (by norm_num) hden2
            _ = 20 := by norm_num
  -- assemble
  have hmul : (keyDyadic_C (gEff ε) + 1)
        * (1 + (keyDyadic_u (gEff ε) - Mob.countSI_u (gEff ε))⁻¹ / (2 * Real.log 2))
      ≤ (10 ^ 423 + 1) * (1 + 10 ^ 23 / min ε (1 / 90935)) := by
    apply mul_le_mul (by linarith [hkC]) (by linarith [hA]) (by linarith [hA0'])
    positivity
  unfold Mob.countSI_C
  refine le_trans ?_ (countSI_C_numeric hM0 hMle1)
  linarith [hmul, hB]

/-- `x^y ≤ exp B` for `x > 0` reduces to `log x · y ≤ B`. -/
private lemma rpow_le_exp_aux {x y B : ℝ} (hx : 0 < x) (h : Real.log x * y ≤ B) :
    x ^ y ≤ Real.exp B := by
  rw [Real.rpow_def_of_pos hx]; exact Real.exp_le_exp.mpr h

set_option maxHeartbeats 400000 in

/-- Loose upper bound on the §6 short-interval threshold `countSI_X0` in terms of the effective
parameter `gEff ε`.  Each of the (rpow) thresholds is bounded through `log`; the dominant ones
(`tU`, `Tlog`, `tbig`, `t1025`) absorb into the generous `exp (10²⁷/ε'²)` budget. -/
theorem countSI_X0_upper (ε : ℝ) (hε : 0 < ε) :
    Mob.countSI_X0 (gEff ε) ≤ Real.exp (10 ^ 27 / (min ε (1 / 90935)) ^ 2) := by
  set ε' := min ε (1 / 90935) with hε'def
  -- basic ε' facts
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'le : ε' ≤ 1 / 90935 := min_le_right _ _
  have hε'le1 : ε' ≤ 1 := le_trans hε'le (by norm_num)
  have htpos : 0 < ε'⁻¹ := inv_pos.mpr hε'pos
  have ht1 : (1 : ℝ) ≤ ε'⁻¹ := by simpa using inv_anti₀ hε'pos hε'le1
  -- budget rewrites and floors
  have hBt : (10 : ℝ) ^ 27 / ε' ^ 2 = 10 ^ 27 * ε'⁻¹ ^ 2 := by
    rw [inv_pow, div_eq_mul_inv]
  have hBge : (10 : ℝ) ^ 27 ≤ 10 ^ 27 / ε' ^ 2 := by
    rw [hBt]; nlinarith [ht1, sq_nonneg (ε'⁻¹ - 1)]
  have hexpge : (10 : ℝ) ^ 27 ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    have h := Real.add_one_le_exp (10 ^ 27 / ε' ^ 2 : ℝ); linarith [hBge, h]
  -- log numerics
  have hlog10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
  have hlog10nn : (0 : ℝ) ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num); linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2lb : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hloglog2 : -Real.log (Real.log 2) ≤ 1 := by
    rw [← Real.log_inv]
    have h1 : Real.log ((Real.log 2)⁻¹) ≤ (Real.log 2)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hlog2pos)
    have h2 : (Real.log 2)⁻¹ ≤ 2 := by
      have hh := inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) hlog2lb
      norm_num at hh; exact hh
    linarith
  unfold Mob.countSI_X0 keyDyadic_X0
  set u_b := dblockBound_u (gEff ε) with hubdef
  set a := (1 - gEff ε) / 5 with hadef
  -- algebraic identities of gEff and the band on a, u_b
  have hgeq : gEff ε = 2 / 18187 - 5 * ε' := by rw [hε'def]; exact gEff_eq ε
  have ha_lo : (1 : ℝ) / 10 ≤ a := by rw [hadef, hgeq]; linarith [hε'pos]
  have ha_hi : a ≤ (1 : ℝ) / 5 := by rw [hadef, hgeq]; linarith [hε'le]
  have hub_lo : ε' / 10 ^ 21 ≤ u_b := by rw [hubdef, hε'def]; exact dblockBound_u_lower ε hε
  have hub_pos : 0 < u_b := lt_of_lt_of_le (div_pos hε'pos (by norm_num)) hub_lo
  have hub_hi : u_b ≤ 1 / 200 := by
    rw [hubdef]; unfold dblockBound_u
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num)
  have hubinvt : u_b⁻¹ ≤ 10 ^ 21 * ε'⁻¹ := by
    have h := inv_anti₀ (div_pos hε'pos (by norm_num)) hub_lo
    rwa [inv_div, div_eq_mul_inv] at h
  have hneglogub : -Real.log u_b ≤ 189 + ε'⁻¹ := by
    rw [← Real.log_inv]
    calc Real.log (u_b⁻¹)
        ≤ Real.log (10 ^ 21 * ε'⁻¹) := Real.log_le_log (inv_pos.mpr hub_pos) hubinvt
      _ = 21 * Real.log 10 + Real.log (ε'⁻¹) := by
          rw [Real.log_mul (by norm_num) htpos.ne', Real.log_pow]; push_cast; ring
      _ ≤ 21 * 9 + (ε'⁻¹ - 1) := by
          have hle := Real.log_le_sub_one_of_pos htpos; linarith [hlog10, hle]
      _ ≤ 189 + ε'⁻¹ := by linarith
  -- leaf bounds
  have hX0 : X0_prop24 ≤ Real.exp (10 ^ 27 / ε' ^ 2) :=
    le_trans (by unfold X0_prop24; norm_num) hexpge
  have h8 : (8 : ℝ) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := le_trans (by norm_num) hexpge
  have hone : (1 : ℝ) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := le_trans (by norm_num) hexpge
  have htbig : (16777216 : ℝ) ^ ((1 / 100 : ℝ)⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by norm_num)
    rw [show ((1 / 100 : ℝ)⁻¹) = (100 : ℝ) by norm_num]
    have hl : Real.log 16777216 ≤ 16777216 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16777216 by norm_num); linarith
    calc Real.log 16777216 * 100 ≤ 16777216 * 100 := mul_le_mul_of_nonneg_right hl (by norm_num)
      _ ≤ 10 ^ 27 / ε' ^ 2 := le_trans (by norm_num) hBge
  have ht1025 : (1025 : ℝ) ^ (((1 : ℝ) / 100)⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by norm_num)
    rw [show (((1 : ℝ) / 100)⁻¹) = (100 : ℝ) by norm_num]
    have hl : Real.log 1025 ≤ 1025 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1025 by norm_num); linarith
    calc Real.log 1025 * 100 ≤ 1025 * 100 := mul_le_mul_of_nonneg_right hl (by norm_num)
      _ ≤ 10 ^ 27 / ε' ^ 2 := le_trans (by norm_num) hBge
  have ht8 : (8 : ℝ) ^ ((1 - (a + 1 / 2))⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by norm_num)
    have he : (1 - (a + 1 / 2))⁻¹ ≤ 4 := by
      have hd : (3 : ℝ) / 10 ≤ 1 - (a + 1 / 2) := by linarith [ha_hi]
      have hh := inv_anti₀ (show (0 : ℝ) < 3 / 10 by norm_num) hd
      rw [show ((3 : ℝ) / 10)⁻¹ = 10 / 3 by norm_num] at hh; linarith
    have henn : (0 : ℝ) ≤ (1 - (a + 1 / 2))⁻¹ := inv_nonneg.mpr (by linarith [ha_hi])
    calc Real.log 8 * (1 - (a + 1 / 2))⁻¹ ≤ 7 * 4 := mul_le_mul hlog8 he henn (by norm_num)
      _ ≤ 10 ^ 27 / ε' ^ 2 := le_trans (by norm_num) hBge
  have ht64 : (64 : ℝ) ^ ((1 + 1 / 50 - a)⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by norm_num)
    have he : (1 + 1 / 50 - a)⁻¹ ≤ 2 := by
      have hd : (1 : ℝ) / 2 ≤ 1 + 1 / 50 - a := by linarith [ha_hi]
      have hh := inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) hd
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at hh; linarith
    have henn : (0 : ℝ) ≤ (1 + 1 / 50 - a)⁻¹ := inv_nonneg.mpr (by linarith [ha_hi])
    have hl64 : Real.log 64 ≤ 64 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 64 by norm_num); linarith
    calc Real.log 64 * (1 + 1 / 50 - a)⁻¹ ≤ 64 * 2 := mul_le_mul hl64 he henn (by norm_num)
      _ ≤ 10 ^ 27 / ε' ^ 2 := le_trans (by norm_num) hBge
  have ht2 : (2 : ℝ) ^ ((a - u_b)⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by norm_num)
    have hd : (19 : ℝ) / 200 ≤ a - u_b := by linarith [ha_lo, hub_hi]
    have he : (a - u_b)⁻¹ ≤ 11 := by
      have hh := inv_anti₀ (show (0 : ℝ) < 19 / 200 by norm_num) hd
      rw [show ((19 : ℝ) / 200)⁻¹ = 200 / 19 by norm_num] at hh; linarith
    have henn : (0 : ℝ) ≤ (a - u_b)⁻¹ := inv_nonneg.mpr (by linarith [hd])
    calc Real.log 2 * (a - u_b)⁻¹ ≤ 1 * 11 := mul_le_mul hlog2 he henn (by norm_num)
      _ ≤ 10 ^ 27 / ε' ^ 2 := le_trans (by norm_num) hBge
  have hTlog : (8 / (u_b * Real.log 2)) ^ ((u_b / 4)⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (div_pos (by norm_num) (mul_pos hub_pos hlog2pos))
    rw [hBt]
    have hbase : Real.log (8 / (u_b * Real.log 2)) ≤ 198 + ε'⁻¹ := by
      rw [Real.log_div (by norm_num) (mul_pos hub_pos hlog2pos).ne',
          Real.log_mul hub_pos.ne' hlog2pos.ne']
      linarith [hlog8, hneglogub, hloglog2]
    have hy_le : (u_b / 4)⁻¹ ≤ 4 * 10 ^ 21 * ε'⁻¹ := by
      rw [inv_div, div_eq_mul_inv]; linarith [hubinvt]
    have hy_nn : (0 : ℝ) ≤ (u_b / 4)⁻¹ := inv_nonneg.mpr (div_pos hub_pos (by norm_num)).le
    have hprod : Real.log (8 / (u_b * Real.log 2)) * (u_b / 4)⁻¹
        ≤ (198 + ε'⁻¹) * (4 * 10 ^ 21 * ε'⁻¹) :=
      mul_le_mul hbase hy_le hy_nn (by linarith [htpos])
    nlinarith [hprod, ht1, htpos,
      mul_nonneg htpos.le (show (0 : ℝ) ≤ ε'⁻¹ - 1 by linarith [ht1])]
  have htU : ((10 : ℝ) ^ 33) ^ (u_b⁻¹) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by positivity)
    rw [Real.log_pow, hBt]; push_cast
    have h1 : (33 : ℝ) * Real.log 10 * u_b⁻¹ ≤ 297 * (10 ^ 21 * ε'⁻¹) :=
      mul_le_mul (by linarith [hlog10]) hubinvt (inv_nonneg.mpr hub_pos.le) (by norm_num)
    nlinarith [h1, ht1, htpos,
      mul_nonneg htpos.le (show (0 : ℝ) ≤ ε'⁻¹ - 1 by linarith [ht1])]
  have h2a : (2 : ℝ) ^ (2 / a) ≤ Real.exp (10 ^ 27 / ε' ^ 2) := by
    apply rpow_le_exp_aux (by norm_num)
    have hapos : 0 < a := by linarith [ha_lo]
    have he : 2 / a ≤ 20 := by rw [div_le_iff₀ hapos]; linarith [ha_lo]
    have henn : (0 : ℝ) ≤ 2 / a := div_nonneg (by norm_num) hapos.le
    calc Real.log 2 * (2 / a) ≤ 1 * 20 := mul_le_mul hlog2 he henn (by norm_num)
      _ ≤ 10 ^ 27 / ε' ^ 2 := le_trans (by norm_num) hBge
  exact max_le
    (max_le
      (max_le
        (max_le hX0 (max_le htbig (max_le ht8 (max_le ht1025
          (max_le ht64 (max_le ht2 (max_le hTlog h8)))))))
        htU)
      hone)
    h2a

/-- Positivity of the `count_short_interval` constant at the effective parameter `gEff ε`.
Re-proved inline (the dedicated lemma in `MobiusAssembly` is `private`). -/
private lemma countSI_C_pos_gEff (ε : ℝ) (hε : 0 < ε) : 0 < Mob.countSI_C (gEff ε) := by
  have hε'le : min ε (1 / 90935) ≤ 1 / 90935 := min_le_right _ _
  have hε'pos : 0 < min ε (1 / 90935) := lt_min hε (by norm_num)
  have hg : 0 < gEff ε := by rw [gEff_eq]; linarith [hε'le]
  have hg' : gEff ε < 2 / 18187 := by rw [gEff_eq]; linarith [hε'pos]
  set g := gEff ε with hgset
  have hCk : 0 < Squarefree.keyDyadic_C g := Squarefree.keyDyadic_C_pos g hg hg'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have huk : 0 < Squarefree.keyDyadic_u g := Squarefree.keyDyadic_u_pos g hg hg'
  have hduk : 0 < Squarefree.keyDyadic_u g - Mob.countSI_u g := by
    have h1 : Mob.countSI_u g < Squarefree.keyDyadic_u g := by
      unfold Mob.countSI_u
      have hm : min (Squarefree.keyDyadic_u g) ((1 - g) / 5 / 2) ≤ Squarefree.keyDyadic_u g :=
        min_le_left _ _
      linarith
    linarith
  have hdeu : 0 < (1 - g) / 5 - Mob.countSI_u g := by
    have h2 : Mob.countSI_u g < (1 - g) / 5 := by
      unfold Mob.countSI_u
      have hm : min (Squarefree.keyDyadic_u g) ((1 - g) / 5 / 2) ≤ (1 - g) / 5 / 2 :=
        min_le_right _ _
      linarith
    linarith
  unfold Mob.countSI_C
  have h1 : 0 ≤ (Squarefree.keyDyadic_C g + 1)
      * (1 + (Squarefree.keyDyadic_u g - Mob.countSI_u g)⁻¹ / (2 * Real.log 2)) := by positivity
  have h2 : 0 ≤ ((1 - g) / 5 - Mob.countSI_u g)⁻¹ / (2 * Real.log 2) := by positivity
  linarith

set_option exponentiation.threshold 1000 in
/-- **(B4)** Closed-form upper bound on the effective threshold `X0eff` in terms of `ε`.
All three branches of the `max` are absorbed into the generous `exp (10³²/ε'²)` budget. -/
theorem X0eff_upper (ε : ℝ) (hε : 0 < ε) :
    Squarefree.X0eff ε ≤ Real.exp (10 ^ 32 / (min ε (1 / 90935)) ^ 2) := by
  set ε' := min ε (1 / 90935) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'le : ε' ≤ 1 / 90935 := min_le_right _ _
  have hε'le1 : ε' ≤ 1 := le_trans hε'le (by norm_num)
  have htpos : 0 < ε'⁻¹ := inv_pos.mpr hε'pos
  have ht1 : (1 : ℝ) ≤ ε'⁻¹ := by simpa using inv_anti₀ hε'pos hε'le1
  -- budget rewrites
  have hBt31 : (10 : ℝ) ^ 31 / ε' ^ 2 = 10 ^ 31 * ε'⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  have hBt32 : (10 : ℝ) ^ 32 / ε' ^ 2 = 10 ^ 32 * ε'⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  have hlog10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
  -- reusable building blocks
  have hC_pos : 0 < Mob.countSI_C (gEff ε) := countSI_C_pos_gEff ε hε
  have hC_ub : Mob.countSI_C (gEff ε) ≤ 10 ^ 450 * ε'⁻¹ := by
    have h := countSI_C_upper ε hε
    rw [← hε'def, div_eq_mul_inv] at h; exact h
  have hcu_lb : ε' / 10 ^ 25 ≤ Mob.countSI_u (gEff ε) := by
    rw [hε'def]; exact countSI_u_lower ε hε
  have hcu_pos : 0 < Mob.countSI_u (gEff ε) :=
    lt_of_lt_of_le (div_pos hε'pos (by norm_num)) hcu_lb
  -- the `one` and `X0` branches
  have hone : (1 : ℝ) ≤ Real.exp (10 ^ 32 / ε' ^ 2) :=
    Real.one_le_exp (div_nonneg (by norm_num) (sq_nonneg ε'))
  have hA : Mob.countSI_X0 (gEff ε) ≤ Real.exp (10 ^ 32 / ε' ^ 2) := by
    have h := countSI_X0_upper ε hε
    rw [← hε'def] at h
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    gcongr <;> norm_num
  unfold Squarefree.X0eff
  set base := Mob.countSI_C (gEff ε) * Real.pi ^ 2 / 6 with hbasedef
  set e := 1 / Mob.countSI_u (gEff ε) with hedef
  -- the middle (rpow) branch
  have hbase_pos : 0 < base := by
    rw [hbasedef]; exact div_pos (mul_pos hC_pos (pow_pos Real.pi_pos 2)) (by norm_num)
  have hbase_ub : base ≤ 10 ^ 451 * ε'⁻¹ := by
    rw [hbasedef]
    have hpi2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hstep : Mob.countSI_C (gEff ε) * Real.pi ^ 2 ≤ 10 ^ 451 * ε'⁻¹ :=
      calc Mob.countSI_C (gEff ε) * Real.pi ^ 2
          ≤ Mob.countSI_C (gEff ε) * 10 := mul_le_mul_of_nonneg_left hpi2 hC_pos.le
        _ ≤ (10 ^ 450 * ε'⁻¹) * 10 := mul_le_mul_of_nonneg_right hC_ub (by norm_num)
        _ = 10 ^ 451 * ε'⁻¹ := by ring
    exact le_trans
      (div_le_self (mul_nonneg hC_pos.le (pow_nonneg Real.pi_pos.le 2)) (by norm_num)) hstep
  have hlogbase : Real.log base ≤ 4060 * ε'⁻¹ := by
    calc Real.log base
        ≤ Real.log (10 ^ 451 * ε'⁻¹) := Real.log_le_log hbase_pos hbase_ub
      _ = 451 * Real.log 10 + Real.log (ε'⁻¹) := by
          rw [Real.log_mul (by norm_num) htpos.ne', Real.log_pow]; push_cast; ring
      _ ≤ 451 * 9 + (ε'⁻¹ - 1) := by
          have hle := Real.log_le_sub_one_of_pos htpos; linarith [hlog10, hle]
      _ ≤ 4060 * ε'⁻¹ := by linarith [ht1]
  have he_pos : 0 < e := by rw [hedef]; exact one_div_pos.mpr hcu_pos
  have he_ub : e ≤ 10 ^ 25 * ε'⁻¹ := by
    rw [hedef, one_div]
    have h := inv_anti₀ (div_pos hε'pos (by norm_num)) hcu_lb
    rwa [inv_div, div_eq_mul_inv] at h
  have hprod : Real.log base * e ≤ 10 ^ 31 / ε' ^ 2 := by
    rw [hBt31]
    calc Real.log base * e
        ≤ (4060 * ε'⁻¹) * e := mul_le_mul_of_nonneg_right hlogbase he_pos.le
      _ ≤ (4060 * ε'⁻¹) * (10 ^ 25 * ε'⁻¹) :=
          mul_le_mul_of_nonneg_left he_ub (mul_nonneg (by norm_num) htpos.le)
      _ ≤ 10 ^ 31 * ε'⁻¹ ^ 2 := by nlinarith [sq_nonneg ε'⁻¹, htpos]
  have hbpe : base ^ e ≤ Real.exp (10 ^ 31 / ε' ^ 2) := rpow_le_exp_aux hbase_pos hprod
  have hfin : Real.exp (10 ^ 31 / ε' ^ 2) + 1 ≤ Real.exp (10 ^ 32 / ε' ^ 2) := by
    have h1 : (1 : ℝ) ≤ Real.exp (10 ^ 31 / ε' ^ 2) :=
      Real.one_le_exp (div_nonneg (by norm_num) (sq_nonneg ε'))
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have hpos : (0 : ℝ) ≤ Real.exp (10 ^ 31 / ε' ^ 2) := (Real.exp_pos _).le
    calc Real.exp (10 ^ 31 / ε' ^ 2) + 1
        ≤ Real.exp (10 ^ 31 / ε' ^ 2) + Real.exp (10 ^ 31 / ε' ^ 2) := by linarith [h1]
      _ = 2 * Real.exp (10 ^ 31 / ε' ^ 2) := by ring
      _ ≤ Real.exp 1 * Real.exp (10 ^ 31 / ε' ^ 2) := mul_le_mul_of_nonneg_right h2 hpos
      _ = Real.exp (1 + 10 ^ 31 / ε' ^ 2) := by rw [← Real.exp_add]
      _ ≤ Real.exp (10 ^ 32 / ε' ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [hBt31, hBt32]
          nlinarith [ht1, sq_nonneg (ε'⁻¹ - 1)]
  have hB : base ^ e + 1 ≤ Real.exp (10 ^ 32 / ε' ^ 2) := by
    calc base ^ e + 1 ≤ Real.exp (10 ^ 31 / ε' ^ 2) + 1 := by linarith [hbpe]
      _ ≤ Real.exp (10 ^ 32 / ε' ^ 2) := hfin
  exact max_le (max_le hA hB) hone

/-- **Effective Theorem 10.1 (clean threshold).**  For every `X ≥ exp(10³²/ε'²)` with
`ε' = min ε (1/90935)`, the interval `[X, X + X^{1/5 − 2/90935 + ε}]` contains a squarefree
number. -/
theorem theorem_10_1_effective_clean (ε : ℝ) (hε : 0 < ε) :
    ∀ X : ℝ, Real.exp (10 ^ 32 / (min ε (1 / 90935)) ^ 2) ≤ X →
      ∃ n : ℕ, Squarefree n ∧ (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + X ^ (1/5 - 2/90935 + ε : ℝ) := by
  intro X hX
  exact theorem_10_1_effective ε hε X (le_trans (X0eff_upper ε hε) hX)

/-- For `0 < ε ≤ 1/90935` the clean threshold simplifies to `exp(10³²/ε²)`. -/
theorem theorem_10_1_effective_clean' (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 90935) :
    ∀ X : ℝ, Real.exp (10 ^ 32 / ε ^ 2) ≤ X →
      ∃ n : ℕ, Squarefree n ∧ (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + X ^ (1/5 - 2/90935 + ε : ℝ) := by
  intro X hX
  apply theorem_10_1_effective_clean ε hε X
  rw [min_eq_left hε2]; exact hX

end Squarefree
