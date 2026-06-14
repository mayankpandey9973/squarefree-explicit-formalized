import Squarefree.Lower.Step4Magnitude

/-!
# §5 Step-4 large-defect cubic-term SIZE bound (additive route, writeup 1052–1064)

The §5 Step-4 closed form `Σ_closed = (Xa/d⁵)·((−4+10a/d)·(P₁+P₂/d))` has a genuine cubic-in-`v`
tail living inside `P₁ = Pone`: the monomial `ℓ₁³(2ℓ₂−ℓ₁)v³` (attempt-1
`largeDefectP1CubicTermReal`, identical coefficient).  Its full contribution to `Σ_closed` is

  `Cub := pref · ℓ₁³(2ℓ₂−ℓ₁) · v³`,    `pref := (Xa/d⁵)·(−4+10a/d)`.

This file ports the **additive SIZE** bound (not the Lipschitz/cube-difference form): on the band
box `|v| ≤ V_box` the cubic contribution is a clean negative-`X`-power fraction of `|s|`,

  `|Cub| ≤ (1/U¹⁴)·|s|`.

## V_box / |s| convention (must match the band-counting kernel)

* **box window** `hv : |v| ≤ 10²⁰·(Δ·U⁵/Ω³)` — the global `V_box`-scale window (`M = ΔU⁵/Ω³`),
  the band box enlarged to the §5 large-`v` range; identical to the window threaded through
  `Step4Magnitude`/`Step4Parabola`.
* **`|s|` pin** `hvpin_hi : ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v² ≤ 10⁶·(Δ²Ω²·|s|)` — the squared `|v| ≍ V_s` pin
  (`V_s² = Δ²Ω²|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁))`), in the form lower-bounding `|s|` by `ℓ₁³ℓ₂(ℓ₂−ℓ₁)v²`.

## Mechanism

Write `Q := Xa/d⁵`, `L := ℓ₁³ℓ₂(ℓ₂−ℓ₁)`.  Then
`|Cub| ≤ 7·Q·ℓ₁³(2ℓ₂−ℓ₁)·|v|³ ≤ 7·Q·(2L)·|v|³ = (L·v²)·(14·Q·|v|)`.  Two collapses:
* `14·Q·|v| ≤ 1/(U¹⁴·10⁶·Δ²Ω²)` via `Q ≤ 11GΩ/Δ⁴` (from `D⁵ = XΔ⁵/G`, `d ≥ D`, `a ≤ 11ΔΩ`),
  `|v| ≤ 10²⁰ΔU⁵/Ω³`, and the regime collapse `154·10²⁶·G·U¹⁹ ≤ Δ` (`Δ ≥ 10¹⁵G⁴U²⁰`, `U ≥ 10³³`);
* `L·v² ≤ 10⁶·Δ²Ω²|s|` (the pin), and `10⁶·Δ²Ω²·(1/(U¹⁴·10⁶·Δ²Ω²)) = 1/U¹⁴`.

`ρ_cub = 1/U¹⁴` is a clean negative `X`-power (the cubic is `≪ |s|`); the committee's heuristic
`ρ_cub = V_s/((ℓ₂−ℓ₁)·B)` is the same scale up to the `b₀`-free `V_box`/`V_s` enlargement.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **§5 Step-4 large-defect cubic-term SIZE bound** (additive route, writeup 1052–1064).  The
full cubic-in-`v` contribution `pref·ℓ₁³(2ℓ₂−ℓ₁)·v³` to `Σ_closed`
(`pref := (Xa/d⁵)(−4+10a/d)`) has magnitude a clean negative-`X`-power fraction of `|s|`:

  `|Cub| ≤ (1/U¹⁴)·|s|`,

on the band box `|v| ≤ 10²⁰·(Δ·U⁵/Ω³)`, with the `|v| ≍ V_s` pin `hvpin_hi` lower-bounding `|s|`
by `ℓ₁³ℓ₂(ℓ₂−ℓ₁)v²`.  Hypotheses reuse the `Step4Magnitude` set (minus the `b₀`/near-int data,
which the `b₀`-free cubic monomial does not touch). -/
theorem cubic_size_le
    {a : ℝ} {ℓ₁ ℓ₂ v d : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hdD : S.D ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hvpin_hi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2
        ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|)) :
    |(P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)|
      ≤ (1 / P.U ^ 14) * |(s : ℝ)| := by
  -- positivity / basic facts
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (1:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have h2ℓpos : (0:ℝ) < 2 * ℓ₂ - ℓ₁ := by linarith
  have hΔne : S.Δ ≠ 0 := hΔpos.ne'
  have hΩne : S.Ω ≠ 0 := hΩpos.ne'
  have hUne : P.U ≠ 0 := hUpos.ne'
  have hGne : P.G ≠ 0 := hGpos.ne'
  have hXne : P.X ≠ 0 := hXpos.ne'
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  -- abbreviations
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set L : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  -- bracket bound :  |−4 + 10a/d| ≤ 7
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi (S.D_eps_lo hdD) h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 7 := by rw [abs_le]; constructor <;> linarith
  -- scale identity :  D⁵ = X·Δ⁵/G
  have hD5 : S.D ^ 5 = P.X * S.Δ ^ 5 / P.G := by
    unfold Scale.D
    rw [P.X_eq_G_mul_H_pow_five]
    field_simp
  -- Q upper bound :  Q ≤ 11·G·Ω/Δ⁴
  have hQle : Q ≤ 11 * P.G * S.Ω / S.Δ ^ 4 := by
    rw [hQdef]
    have hd5ge : S.D ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ hDpos.le hdD 5
    have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
    calc P.X * a / d ^ 5 ≤ P.X * a / S.D ^ 5 := by gcongr
      _ = a * P.G / S.Δ ^ 5 := by rw [hD5]; field_simp
      _ ≤ 11 * P.G * S.Ω / S.Δ ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right haA (by positivity : (0:ℝ) ≤ P.G * S.Δ ^ 4),
            hΔpos, hΩpos, hGpos]
  -- regime collapse :  154·10²⁶·G·U¹⁹ ≤ Δ
  have hkey : 154 * 10 ^ 26 * P.G * P.U ^ 19 ≤ S.Δ := by
    have hGU : (154:ℝ) * 10 ^ 11 ≤ P.G ^ 3 * P.U := by
      have hge : (1:ℝ) * P.U ≤ P.G ^ 3 * P.U :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hG1) hUpos.le
      nlinarith [hUbig, hge, (by norm_num : (154:ℝ) * 10 ^ 11 ≤ (10:ℝ) ^ 33)]
    have hprod : 0 ≤ P.G * P.U ^ 19 * (10 ^ 15 * (P.G ^ 3 * P.U - 154 * 10 ^ 11)) := by
      apply mul_nonneg (by positivity)
      nlinarith [hGU]
    nlinarith [hDeW, hprod]
  -- key scalar collapse :  14·Q·|v| ≤ 1/(U¹⁴·10⁶·Δ²Ω²)
  have hQv : 14 * Q * |v| ≤ 1 / (P.U ^ 14 * 10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2) := by
    have h1' : Q * |v|
        ≤ (11 * P.G * S.Ω / S.Δ ^ 4) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) :=
      mul_le_mul hQle hv (abs_nonneg v) (by positivity)
    have hsimp : (11 * P.G * S.Ω / S.Δ ^ 4) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
        = 11 * 10 ^ 20 * P.G * P.U ^ 5 / (S.Δ ^ 3 * S.Ω ^ 2) := by field_simp
    rw [hsimp] at h1'
    have h3 : 14 * Q * |v| ≤ 14 * (11 * 10 ^ 20 * P.G * P.U ^ 5 / (S.Δ ^ 3 * S.Ω ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_left h1' (by norm_num : (0:ℝ) ≤ 14)]
    refine le_trans h3 ?_
    rw [show (14:ℝ) * (11 * 10 ^ 20 * P.G * P.U ^ 5 / (S.Δ ^ 3 * S.Ω ^ 2))
          = 154 * 10 ^ 20 * P.G * P.U ^ 5 / (S.Δ ^ 3 * S.Ω ^ 2) from by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2)]
  -- ℓ-ratio :  ℓ₁³(2ℓ₂−ℓ₁) ≤ 2·L
  have hℓb : ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) ≤ 2 * L := by
    rw [hLdef]
    have hineq : 2 * ℓ₂ - ℓ₁ ≤ 2 * ℓ₂ * (ℓ₂ - ℓ₁) := by
      nlinarith [h21, hℓ2pos, hℓ1pos, mul_nonneg hℓ2pos.le (by linarith [h21] : (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hineq (by positivity : (0:ℝ) ≤ ℓ₁ ^ 3)]
  -- abs of the cubic contribution
  have hQℓnn : (0:ℝ) ≤ Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) :=
    mul_nonneg hQpos.le (mul_nonneg (by positivity) h2ℓpos.le)
  have hCub_le : |Q * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)|
      ≤ 7 * (Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * |v| ^ 3) := by
    rw [show Q * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)
          = (-4 + 10 * a / d) * (Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 3) from by ring]
    rw [abs_mul]
    calc |(-4 + 10 * a / d)| * |Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 3|
        = |(-4 + 10 * a / d)| * (Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * |v| ^ 3) := by
          rw [abs_mul, abs_of_nonneg hQℓnn, abs_pow]
      _ ≤ 7 * (Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * |v| ^ 3) :=
          mul_le_mul_of_nonneg_right hbr_hi (mul_nonneg hQℓnn (by positivity))
  -- assemble
  have hident : 7 * (Q * (2 * L) * |v| ^ 3) = (L * |v| ^ 2) * (14 * Q * |v|) := by ring
  have hLv2nn : (0:ℝ) ≤ L * v ^ 2 := mul_nonneg hLpos.le (sq_nonneg v)
  have hρ'nn : (0:ℝ) ≤ 1 / (P.U ^ 14 * 10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2) := by positivity
  calc |Q * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)|
      ≤ 7 * (Q * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * |v| ^ 3) := hCub_le
    _ ≤ 7 * (Q * (2 * L) * |v| ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 7)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓb hQpos.le) (by positivity)
    _ = (L * v ^ 2) * (14 * Q * |v|) := by rw [hident, sq_abs]
    _ ≤ (L * v ^ 2) * (1 / (P.U ^ 14 * 10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2)) :=
        mul_le_mul_of_nonneg_left hQv hLv2nn
    _ ≤ (1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|))
          * (1 / (P.U ^ 14 * 10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2)) :=
        mul_le_mul_of_nonneg_right hvpin_hi hρ'nn
    _ = (1 / P.U ^ 14) * |(s : ℝ)| := by field_simp; ring

end Squarefree
