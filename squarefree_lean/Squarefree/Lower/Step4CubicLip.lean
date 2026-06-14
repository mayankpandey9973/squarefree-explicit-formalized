import Squarefree.Lower.Step4Magnitude
import Squarefree.Lower.Step4Cref

/-!
# §5 Step-4 large-defect cubic-term LIPSCHITZ θ-slope (writeup 1052–1058)

The §5 Step-4 closed form `Σ_closed = (Xa/d⁵)·((−4+10a/d)·(P₁+P₂/d))` has a genuine cubic-in-`v`
tail living inside `P₁`: the monomial `ℓ₁³(2ℓ₂−ℓ₁)v³` with `pref := (Xa/d⁵)(−4+10a/d)`.

Unlike the (now-unused) additive route `Step4CubicSize.lean`, this file ports the cubic as a
**Lipschitz θ-slope** of the perturbed-quadratic shell
(`abs_sq_sub_le_of_perturbed_quadratic_shell`, `Step4SqDiffShell.lean`).  The shell consumes the
non-quadratic perturbation difference `ex − ey` in the form `θ·Ĉ·|x²−y²| + E0`; the cubic tail,
within one fibre (common `pref`), is exactly a `θ·Ĉ·|v²−v'²|` slope — it **renormalizes the shell's
fixed coefficient `Ĉ` by the factor `θ` and contributes nothing to the band width** (no additive
`E0`).  The cross-fibre prefactor drift (different `pref` at the two points) is the only additive
remainder, and it is an `X`-power-small `E0` at the `V_box` cap.

## V_box / Ĉ conventions (match `Step4Diam`/`Step4Magnitude`)

* **box window** `hv : |v| ≤ V_box := 10²⁰·(Δ·U⁵/Ω³)` — the global `V_box`-scale window
  (`M = ΔU⁵/Ω³`), identical to the window threaded through `Step4Magnitude`/`Step4Diam`.
* **fixed reference coefficient** `Ĉ := Cref·(A/a)²·ℓ₁² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)/a² (> 0)`
  (`Step4Cref.Cref`), the `r`-independent leading `v²`-coefficient consumed by the shell.
* **prefactor magnitude** `|pref| ≤ 77·G·Ω/Δ⁴` (from `D⁵ = XΔ⁵/G`, `d ≥ D`, `a ≤ 11ΔΩ`,
  `|−4+10a/d| ≤ 7`; `Step4Magnitude.bracket_ad_small`).

## θ_cub (the slope) and its `≤ 1/2` collapse

The same-sign cube identity `|v³−v'³| = |v²+vv'+v'²|·|v−v'| ≤ 2·V_box·|v²−v'²|`
(both endpoints in the box, common sign) turns the cubic into the slope

  `|pref·ℓ₁³(2ℓ₂−ℓ₁)(v³−v'³)| ≤ (|pref|·ℓ₁³(2ℓ₂−ℓ₁)·2V_box)·|v²−v'²| =: θ_cub·Ĉ·|v²−v'²|`,

  `θ_cub = |pref|·ℓ₁³(2ℓ₂−ℓ₁)·2V_box / Ĉ = |pref|·(2ℓ₂−ℓ₁)·2V_box·a²/(3ℓ₂(ℓ₂−ℓ₁))`.

Killing the `ℓ`-ratio `(2ℓ₂−ℓ₁) ≤ 2ℓ₂(ℓ₂−ℓ₁)` and using `|pref| ≤ 77GΩ/Δ⁴`,
`V_box = 10²⁰ΔU⁵/Ω³`, `a² ≤ 121Δ²Ω²` collapses (via `Ω,Δ`-cancellation) to the clean negative
`X`-power `θ_cub ≤ (4/3)·77·121·10²⁰·G·U⁵/Δ ≤ 10²⁵·G·U⁵/Δ ≤ 1/2`, the last step by the regime
`Δ ≥ 10¹⁵G⁴U²⁰`, `U ≥ 10³³`.  So `cubic_lipschitz_le` packs the cubic into `θ = 1/2` of the shell's
`htheta : θ ≤ 1/2` slot.

## Cross-fibre drift (the additive `E0`)

`cubic_pref_drift_le` (pure algebra, abstract `Pmaj, V_box`): with `|pref|,|pref'| ≤ Pmaj` and
`|v'| ≤ V_box`, the residual `(pref − pref')·ℓ₁³(2ℓ₂−ℓ₁)·v'³` is bounded by
`ρ_drift := 2·Pmaj·ℓ₁³(2ℓ₂−ℓ₁)·V_box³`, an `X`-power-small additive `E0` (the cube-power budget;
instantiated `Pmaj = 77GΩ/Δ⁴`, `V_box = 10²⁰ΔU⁵/Ω³`).
-/

namespace Squarefree

open Real

/-- Same-sign cube-difference Lipschitz bound for nonnegative endpoints (port of attempt-1
`abs_cube_sub_cube_le_two_mul_bound_mul_abs_sq_sub_sq_nonneg`).  For `0 ≤ x, y ≤ V`,
`|x³−y³| ≤ 2V·|x²−y²|`. -/
private theorem abs_cube_sub_cube_le_box_nonneg {x y V : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxV : x ≤ V) (hyV : y ≤ V) :
    |x ^ 3 - y ^ 3| ≤ 2 * V * |x ^ 2 - y ^ 2| := by
  have hV0 : 0 ≤ V := le_trans hx0 hxV
  have hpoly_nonneg : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx0 hy0]
  have hx2 : x ^ 2 ≤ V * x := by nlinarith
  have hxy : x * y ≤ V * y := mul_le_mul_of_nonneg_right hxV hy0
  have hy2 : y ^ 2 ≤ V * y := by nlinarith
  have hpoly_le : x ^ 2 + x * y + y ^ 2 ≤ 2 * V * (x + y) := by
    nlinarith [mul_nonneg hV0 hx0]
  have hsum_nonneg : 0 ≤ x + y := add_nonneg hx0 hy0
  have hcube : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  have hsq : |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by
    rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) from by ring, abs_mul]
  calc |x ^ 3 - y ^ 3|
      = |(x - y) * (x ^ 2 + x * y + y ^ 2)| := by rw [hcube]
    _ = |x - y| * |x ^ 2 + x * y + y ^ 2| := abs_mul _ _
    _ ≤ |x - y| * (2 * V * (x + y)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg hpoly_nonneg]; exact hpoly_le
    _ = 2 * V * (|x - y| * |x + y|) := by rw [abs_of_nonneg hsum_nonneg]; ring
    _ = 2 * V * |x ^ 2 - y ^ 2| := by rw [hsq]

/-- Same-sign cube-difference Lipschitz bound: for `v, v'` of common sign (`0 ≤ v·v'`) both within
the box `|·| ≤ V`, `|v³−v'³| ≤ 2V·|v²−v'²|`. -/
private theorem abs_cube_sub_cube_le_box {v v' V : ℝ}
    (hsign : 0 ≤ v * v') (hv : |v| ≤ V) (hv' : |v'| ≤ V) :
    |v ^ 3 - v' ^ 3| ≤ 2 * V * |v ^ 2 - v' ^ 2| := by
  rcases mul_nonneg_iff.mp hsign with ⟨hv0, hv'0⟩ | ⟨hv0, hv'0⟩
  · have hvV : v ≤ V := by rwa [abs_of_nonneg hv0] at hv
    have hv'V : v' ≤ V := by rwa [abs_of_nonneg hv'0] at hv'
    exact abs_cube_sub_cube_le_box_nonneg hv0 hv'0 hvV hv'V
  · have hvV : -v ≤ V := by rwa [abs_of_nonpos hv0] at hv
    have hv'V : -v' ≤ V := by rwa [abs_of_nonpos hv'0] at hv'
    have h := abs_cube_sub_cube_le_box_nonneg
      (neg_nonneg.mpr hv0) (neg_nonneg.mpr hv'0) hvV hv'V
    have e1 : |(-v) ^ 3 - (-v') ^ 3| = |v ^ 3 - v' ^ 3| := by
      rw [show (-v) ^ 3 - (-v') ^ 3 = -(v ^ 3 - v' ^ 3) from by ring, abs_neg]
    have e2 : |(-v) ^ 2 - (-v') ^ 2| = |v ^ 2 - v' ^ 2| := by
      rw [show (-v) ^ 2 - (-v') ^ 2 = v ^ 2 - v' ^ 2 from by ring]
    rwa [e1, e2] at h

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **§5 Step-4 cubic-term LIPSCHITZ slope** (writeup 1052–1058, Lipschitz route).  For two
in-fibre points `v, v'` of common sign in the box `|·| ≤ 10²⁰·(Δ·U⁵/Ω³)`, sharing the single
prefactor `pref = (Xa/d⁵)(−4+10a/d)`, the cubic tail `pref·ℓ₁³(2ℓ₂−ℓ₁)(v³−v'³)` is a Lipschitz
slope `θ·Ĉ·|v²−v'²|` of the fixed reference coefficient `Ĉ = Cref·(A/a)²·ℓ₁²`, with the slope
already collapsed to `θ = 1/2` (the genuine slope is `θ_cub ≤ 10²⁵·G·U⁵/Δ ≤ 1/2`):

  `|pref·ℓ₁³(2ℓ₂−ℓ₁)(v³−v'³)| ≤ (1/2)·Ĉ·|v²−v'²|`.

This is the form the perturbed-quadratic shell's `htheta : θ ≤ 1/2` slot consumes; the cubic
renormalizes `Ĉ` and adds nothing to the band width. -/
theorem cubic_lipschitz_le
    {a v v' d ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hv' : |v'| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hsign : 0 ≤ v * v')
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |(P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (v ^ 3 - v' ^ 3))|
      ≤ (1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * |v ^ 2 - v' ^ 2| := by
  -- positivity scaffolding
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h2ℓpos : (0:ℝ) < 2 * ℓ₂ - ℓ₁ := by linarith
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hΔne : S.Δ ≠ 0 := hΔpos.ne'
  have hΩne : S.Ω ≠ 0 := hΩpos.ne'
  have hGne : P.G ≠ 0 := hGpos.ne'
  have hXne : P.X ≠ 0 := hXpos.ne'
  have ha_ne : a ≠ 0 := ha0.ne'
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  -- abbreviations
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set pref : ℝ := Q * (-4 + 10 * a / d) with hpref_def
  -- bracket bound : |−4+10a/d| ≤ 7
  obtain ⟨had0, hadhi⟩ := bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  -- scale identity D⁵ = XΔ⁵/G  and  Q ≤ 12GΩ/Δ⁴ (ε-window)
  have hD5 : S.D ^ 5 = P.X * S.Δ ^ 5 / P.G := by
    unfold Scale.D; rw [P.X_eq_G_mul_H_pow_five]; field_simp
  have hQle : Q ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
    have hd5ge : S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5 ≤ d ^ 5 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hdD 5
    calc Q = P.X * a / d ^ 5 := hQdef
      _ ≤ P.X * a / (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by gcongr
      _ = a * P.G / (S.Δ ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by rw [hD5]; field_simp
      _ ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right haA (by positivity : (0:ℝ) ≤ P.G * S.Δ ^ 4),
            hΔpos, hΩpos, hGpos, mul_pos (mul_pos hGpos (pow_pos hΔpos 5)) hΩpos]
  -- |pref| ≤ 77·G·Ω/Δ⁴
  have hprefbound : |pref| ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by
    rw [hpref_def, abs_mul, abs_of_pos hQpos]
    calc Q * |(-4 + 10 * a / d)|
        ≤ Q * 4 := mul_le_mul_of_nonneg_left hbr_hi hQpos.le
      _ ≤ (12 * P.G * S.Ω / S.Δ ^ 4) * 4 := mul_le_mul_of_nonneg_right hQle (by norm_num)
      _ = 48 * (P.G * S.Ω / S.Δ ^ 4) := by ring
      _ ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by
          have hnn : (0:ℝ) ≤ P.G * S.Ω / S.Δ ^ 4 := by positivity
          linarith
  -- regime collapse :  10²⁵·G·U⁵ ≤ Δ
  have hkey : (10:ℝ) ^ 25 * (P.G * P.U ^ 5) ≤ S.Δ := by
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    have hU15 : (10:ℝ) ^ 10 ≤ P.U ^ 15 := by
      calc (10:ℝ) ^ 10 ≤ (10:ℝ) ^ 33 := by norm_num
        _ ≤ P.U := hUbig
        _ = P.U ^ 1 := (pow_one _).symm
        _ ≤ P.U ^ 15 := pow_le_pow_right₀ (le_trans (by norm_num) hUbig) (by norm_num)
    have hcube_ineq : (10:ℝ) ^ 10 ≤ P.G ^ 3 * P.U ^ 15 := by
      nlinarith [hU15, mul_nonneg (by linarith [hG3] : (0:ℝ) ≤ P.G ^ 3 - 1) (pow_pos hUpos 15).le]
    have hbig : (10:ℝ) ^ 25 * (P.G * P.U ^ 5) ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
      nlinarith [mul_le_mul_of_nonneg_left hcube_ineq
        (by positivity : (0:ℝ) ≤ 10 ^ 15 * (P.G * P.U ^ 5)),
        (by positivity : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 20)]
    linarith [hbig, hDeW]
  -- a² ≤ 121Δ²Ω²
  have ha2 : a ^ 2 ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2) := by
    have hmul : a * a ≤ (11 * (S.Δ * S.Ω)) * (11 * (S.Δ * S.Ω)) :=
      mul_le_mul haA haA ha0.le (by positivity)
    nlinarith [hmul]
  -- ℓ-ratio :  2ℓ₂−ℓ₁ ≤ 2ℓ₂(ℓ₂−ℓ₁)
  have hlrat : (2 * ℓ₂ - ℓ₁) ≤ 2 * (ℓ₂ * (ℓ₂ - ℓ₁)) := by
    nlinarith [mul_nonneg hℓ2pos.le (by linarith [hℓ12'] : (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1), hℓ1pos.le]
  -- bridge :  Ĉ = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)/a²
  have hbridge : Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2 = 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 := by
    unfold Cref Scale.A; field_simp
  -- nonnegativity helpers
  have hℓnn : (0:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h2ℓpos.le
  have hLfac_nn : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_nonneg (mul_nonneg (by positivity) hℓ2pos.le) h21
  -- the ℓ-free scalar crux :  |pref|·4V_box·a² ≤ 3/2
  have hscalar : |pref| * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) * a ^ 2 ≤ 3 / 2 := by
    have h1' : |pref| * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
        ≤ (77 * (P.G * S.Ω / S.Δ ^ 4)) * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) :=
      mul_le_mul_of_nonneg_right hprefbound (by positivity)
    have hstep : |pref| * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) * a ^ 2
        ≤ (77 * (P.G * S.Ω / S.Δ ^ 4)) * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
            * (121 * (S.Δ ^ 2 * S.Ω ^ 2)) :=
      mul_le_mul h1' ha2 (by positivity) (by positivity)
    refine hstep.trans ?_
    have heq : (77 * (P.G * S.Ω / S.Δ ^ 4)) * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
          * (121 * (S.Δ ^ 2 * S.Ω ^ 2)) = 37268 * 10 ^ 20 * (P.G * P.U ^ 5) / S.Δ := by
      field_simp; ring
    rw [heq, div_le_iff₀ hΔpos]
    nlinarith [hkey, mul_nonneg hGpos.le (pow_nonneg hUpos.le 5)]
  -- the slope inequality :  |pref|·ℓ₁³(2ℓ₂−ℓ₁)·2V_box ≤ (1/2)·Ĉ
  have hslope : |pref| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (2 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
      ≤ (1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) := by
    calc |pref| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (2 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
        ≤ |pref| * (ℓ₁ ^ 3 * (2 * (ℓ₂ * (ℓ₂ - ℓ₁))))
            * (2 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hlrat (by positivity)
      _ = (|pref| * (4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) := by
          ring
      _ ≤ ((3 / 2) / a ^ 2) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) := by
          apply mul_le_mul_of_nonneg_right _ hLfac_nn
          rw [le_div_iff₀ (by positivity : (0:ℝ) < a ^ 2)]
          exact hscalar
      _ = (1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) := by rw [hbridge]; ring
  -- the same-sign cube difference
  have hcube := abs_cube_sub_cube_le_box hsign hv hv'
  -- assemble
  have hLHSeq : |pref * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (v ^ 3 - v' ^ 3))|
      = |pref| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * |v ^ 3 - v' ^ 3| := by
    rw [show pref * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (v ^ 3 - v' ^ 3))
          = (pref * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * (v ^ 3 - v' ^ 3) from by ring,
        abs_mul, abs_mul, abs_of_nonneg hℓnn]
  calc |pref * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (v ^ 3 - v' ^ 3))|
      = |pref| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * |v ^ 3 - v' ^ 3| := hLHSeq
    _ ≤ |pref| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
          * (2 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * |v ^ 2 - v' ^ 2|) :=
        mul_le_mul_of_nonneg_left hcube (mul_nonneg (abs_nonneg _) hℓnn)
    _ = (|pref| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (2 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))))
          * |v ^ 2 - v' ^ 2| := by ring
    _ ≤ ((1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2)) * |v ^ 2 - v' ^ 2| :=
        mul_le_mul_of_nonneg_right hslope (abs_nonneg _)
    _ = (1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * |v ^ 2 - v' ^ 2| := by ring

/-- **§5 Step-4 cubic cross-fibre prefactor drift** (writeup 1052–1058, additive `E0`).  When two
fibre points carry different prefactors `pref, pref'` (with common magnitude majorant
`|pref|,|pref'| ≤ Pmaj`), the cubic tail evaluated at the common box point `|v'| ≤ V` drifts by an
additive amount controlled by the cube-power budget

  `|(pref − pref')·ℓ₁³(2ℓ₂−ℓ₁)·v'³| ≤ 2·Pmaj·ℓ₁³(2ℓ₂−ℓ₁)·V³`.

Instantiated with `Pmaj = 77·G·Ω/Δ⁴` and `V = V_box = 10²⁰·(Δ·U⁵/Ω³)` this is the `X`-power-small
additive `E0` term the shell consumes alongside the Lipschitz slope. -/
theorem cubic_pref_drift_le
    {pref pref' Pmaj v' V ℓ₁ ℓ₂ : ℝ}
    (hpref : |pref| ≤ Pmaj) (hpref' : |pref'| ≤ Pmaj)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hv' : |v'| ≤ V) :
    |pref * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3) - pref' * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3)|
      ≤ 2 * Pmaj * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * V ^ 3 := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h2ℓpos : (0:ℝ) < 2 * ℓ₂ - ℓ₁ := by linarith
  have hℓnn : (0:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h2ℓpos.le
  have hPmaj0 : (0:ℝ) ≤ Pmaj := le_trans (abs_nonneg _) hpref
  have hdiff : |pref - pref'| ≤ 2 * Pmaj := by
    calc |pref - pref'| = |pref + -pref'| := by rw [sub_eq_add_neg]
      _ ≤ |pref| + |-pref'| := abs_add_le _ _
      _ = |pref| + |pref'| := by rw [abs_neg]
      _ ≤ Pmaj + Pmaj := add_le_add hpref hpref'
      _ = 2 * Pmaj := by ring
  have hv3 : |v' ^ 3| ≤ V ^ 3 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv' 3
  rw [show pref * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3) - pref' * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3)
        = (pref - pref') * ((ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v' ^ 3) from by ring,
      abs_mul, abs_mul, abs_of_nonneg hℓnn]
  calc |pref - pref'| * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v' ^ 3|)
      ≤ (2 * Pmaj) * ((ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * V ^ 3) := by
        apply mul_le_mul hdiff (mul_le_mul_of_nonneg_left hv3 hℓnn)
          (mul_nonneg hℓnn (abs_nonneg _)) (by positivity)
    _ = 2 * Pmaj * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * V ^ 3 := by ring

end Squarefree
