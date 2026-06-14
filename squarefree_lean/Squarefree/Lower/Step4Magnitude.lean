import Squarefree.Lower.UpsilonMagV2
import Squarefree.Lower.UpsilonErr
import Squarefree.Lower.Step4Combine
import Squarefree.Lower.DefectScales

/-!
# §5 Step-4 large-defect per-`s` magnitude + extraction (writeup 1025–1052)

This is the corrected first piece of the large-`v` build.  The earlier framing tried to
*extract* a nonzero `s` from a single floor `|v| ≥ V₂`; that has a gap, since `V₂` does not by
itself force `s ≠ 0`.  The fixed architecture **ranges over `s` as an input** and pins the
geometry by `|v| ≍ V_s` (writeup 1062), where

  `V_s² = D⁵|s|/(XAB·ℓ₁³ℓ₂(ℓ₂−ℓ₁)) = Δ²Ω²·|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁))`   (since `XAB/D⁵ = 1/(Δ²Ω²)`).

For a fixed admissible nonzero integer `s` and a `v` with `|v| ≍ V_s` lying in the
large-defect range (the cancellation-avoidance bound `hvlo`, writeup 1025–1031, which forces
the `p₁`-term to dominate), the closed cubic/quartic form `Σ_closed` of writeup 1047 has
magnitude `≍ |s|` and rounds to `s`:

  `(1/C)·|s| ≤ |Σ_closed| ≤ C·|s|`   and   `|Σ_closed − s| ≤ C·(E1 + NB)`,

with `E1 := 10¹¹⁰·UpsT`, `NB := 45·Wval⁴·H/D` (`= 45·G⁴U²⁰/Δ`) the writeup-1042 error scales.

## Mechanism
* **lower** (`Σ_closed ≥ |s|/C`): `psum_abs_ge_v2` (`|p₁+p₂/d| ≥ ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`) times the
  leading coefficient `Xa/d⁵·|−4+10a/d| ≥ 2·Xa/d⁵`, times the pin-lower `v² ≥ V_s²/C₁` and
  `|b₀| ≥ B/(2·10⁶)`, collapsed by `XAB/D⁵ = 1/(Δ²Ω²)`.
* **upper** (`Σ_closed ≤ C·|s|`): `psum_abs_le_v2` (`|p₁+p₂/d| ≤ 4·ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`) times
  the leading coefficient `≤ 7·Xa/d⁵`, times the pin-upper `v² ≤ C₁·V_s²` and `|b₀| ≤ 3·10¹²B`.
* **extraction**: `s = round Σ_closed` together with `distInt Σ_closed ≤ E1 + NB`
  (`Sigma_closed_near_int`) gives `|Σ_closed − s| ≤ E1 + NB`.

`hvlo` (the writeup-1025 cancellation-avoidance floor) is a genuine side hypothesis of the
large-defect range, supplied by the caller; it is *not* implied by `|v| ≍ V_s` alone (in the
small-`Ω` regime the `s = 1` configuration is simply empty), so it is threaded explicitly,
exactly as in `psum_abs_ge_v2`.
-/

namespace Squarefree

open Real Squarefree.Counting

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The large-defect leading bracket is genuinely `≍ −4`: under the §5 regime `a/d` is tiny
(`H ≫ Ω`), so `10·a/d ≤ 1/8`, hence `2 ≤ |−4 + 10a/d| ≤ 7`. -/
theorem bracket_ad_small {a d : ℝ} (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    0 ≤ 10 * a / d ∧ 10 * a / d ≤ 1 / 8 := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  -- H ≥ G·U¹⁰·Δ²  ≥ U¹⁰  (G,Δ ≥ 1)
  have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
    (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
  -- H ≥ 1000·Ω :  H ≥ U¹⁰ ≥ U⁹·Ω  (Ω ≤ U), and U⁹ ≥ 1000.
  have hHΩ : 1000 * S.Ω ≤ P.H := by
    have hU10 : P.U ^ 10 ≤ P.H := by
      have h1' : (1:ℝ) ≤ P.G * S.Δ ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hΔ1, hG1]
      nlinarith [hHbig, pow_pos hUpos 10, mul_le_mul_of_nonneg_left h1'
        (by positivity : (0:ℝ) ≤ P.U ^ 10)]
    have hU9 : (1000:ℝ) ≤ P.U ^ 9 := by
      calc (1000:ℝ) ≤ (10:ℝ) ^ 33 := by norm_num
        _ ≤ P.U := hUbig
        _ = P.U ^ 1 := by ring
        _ ≤ P.U ^ 9 := pow_le_pow_right₀ (le_trans (by norm_num) hUbig) (by norm_num)
    have hΩU9 : P.U ^ 10 = P.U ^ 9 * P.U := by ring
    calc 1000 * S.Ω ≤ P.U ^ 9 * P.U := by nlinarith [hU9, hΩU, pow_pos hUpos 9, hΩpos]
      _ = P.U ^ 10 := hΩU9.symm
      _ ≤ P.H := hU10
  -- a/d ≤ 11A/D = 11Ω/H ≤ 11/1000.  So 10a/d ≤ 0.11.
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  have hd_ge : P.H * S.Δ * (1 - 1/10 ^ 9) ≤ d := by unfold Scale.D at hdD; exact hdD
  have had : 10 * a / d ≤ 1 / 8 := by
    rw [div_le_iff₀ hd_pos]
    -- 10 a ≤ (1/8) d ;  10 a ≤ 110 ΔΩ ;  (1/8) d ≥ (1/8)(1−ε) HΔ ≥ 124.9 ΩΔ
    have hlo : (10:ℝ) * a ≤ 110 * (S.Δ * S.Ω) := by nlinarith [haA]
    have hhi : 110 * (S.Δ * S.Ω) ≤ 1 / 8 * d := by
      have hstep : 110 * (S.Δ * S.Ω) ≤ 1 / 8 * (P.H * S.Δ * (1 - 1/10 ^ 9)) := by
        nlinarith [mul_le_mul_of_nonneg_right hHΩ hΔpos.le, hΔpos, hΩpos, hHpos]
      nlinarith [hstep, mul_le_mul_of_nonneg_left hd_ge (by norm_num : (0:ℝ) ≤ 1/8)]
    linarith [hlo, hhi]
  have had0 : 0 ≤ 10 * a / d := by positivity
  exact ⟨had0, had⟩

/-- **§5 Step-4 large-defect per-`s` magnitude LOWER bound** (writeup 1025–1047).  The lower
half of `sigma_s_magnitude_extract`, isolated so the MVT confinement (`Step4Confinement`) can
apply it at the unknown MVT midpoint without the point-specific `round`/`distInt` inputs:

  `(1/10²¹)·|s| ≤ |Σ_closed|`.

Mechanism: `psum_abs_ge_v2` × the bracket lower `|−4+10a/d| ≥ 2`, then the pin-lower
`v² ≥ Δ²Ω²|s|/(10⁶L)`, `a ≥ A/5`, `|b₀| ≥ B/(2·10⁶)`, collapsed by `D⁵ = Δ²Ω²·XAB`. -/
theorem sigma_s_magnitude_lower
    {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hvpin_lo : S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|
        ≤ 1000000 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)) :
    (1 / (10 ^ 21 : ℝ)) * |(s : ℝ)| ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set L : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  have hsnn : 0 ≤ |(s : ℝ)| := abs_nonneg _
  have hSeq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ = Q * ((-4 + 10 * a / d) * P0) := by
    rw [Sigma_closed, hQdef, hP0def]
  have hSabs : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| = Q * (|(-4 + 10 * a / d)| * |P0|) := by
    rw [hSeq, abs_mul, abs_of_pos hQpos, abs_mul]
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi (S.D_eps_lo hdD) h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_lo : 2 ≤ |(-4 + 10 * a / d)| := by rw [le_abs]; right; linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  have hP0lo : L * |b₀| * v ^ 2 ≤ |P0| := by
    have := psum_abs_ge_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo
      (S.D_half_of_win hdD) hd_pos hReg hG1 hU1 hUbig hDeW
    rw [hLdef, hP0def]; exact this
  have hABID : S.D ^ 5 = S.Δ ^ 2 * S.Ω ^ 2 * (P.X * S.A * S.B) := by
    have h := defect_D5_div_XAB (P := P) S
    rw [div_eq_iff (by positivity : P.X * S.A * S.B ≠ 0)] at h
    linarith [h]
  have hd5pos : (0:ℝ) < d ^ 5 := by positivity
  have hstep1 : Q * (2 * (L * |b₀| * v ^ 2)) ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
    rw [hSabs]
    apply mul_le_mul_of_nonneg_left _ hQpos.le
    exact mul_le_mul hbr_lo hP0lo (by positivity) hbr_nn
  have hkey : |(s : ℝ)| * d ^ 5 ≤ 2 * 10 ^ 21 * (P.X * a * |b₀| * (L * v ^ 2)) := by
    have hn : 2 * 10 ^ 8 * (P.X * S.A * S.B * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|))
        ≤ 2 * 10 ^ 21 * (P.X * a * |b₀| * (L * v ^ 2)) := by
      have e1 : P.X * (S.A / 5) * (S.B / 2000000) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)| / 1000000)
          ≤ P.X * a * |b₀| * (L * v ^ 2) := by
        have hb1 : P.X * (S.A / 5) ≤ P.X * a := mul_le_mul_of_nonneg_left ha_lo hXpos.le
        have hb2 : P.X * (S.A / 5) * (S.B / 2000000) ≤ P.X * a * |b₀| :=
          mul_le_mul hb1 hb0lo (by positivity) (by positivity)
        have hb3 : S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)| / 1000000 ≤ L * v ^ 2 := by
          rw [div_le_iff₀ (by norm_num)]; linarith [hvpin_lo]
        exact mul_le_mul hb2 hb3 (by positivity) (by positivity)
      nlinarith [e1, mul_pos hXpos (mul_pos hApos hBpos)]
    have hd5le : d ^ 5 ≤ (2 * S.D) ^ 5 := pow_le_pow_left₀ hd_pos.le hd2D 5
    have hLHS : |(s:ℝ)| * d ^ 5 ≤ 2 * 10 ^ 8 * (P.X * S.A * S.B * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|)) := by
      have h32 : |(s:ℝ)| * d ^ 5 ≤ |(s:ℝ)| * (32 * S.D ^ 5) := by
        apply mul_le_mul_of_nonneg_left _ hsnn
        calc d ^ 5 ≤ (2 * S.D) ^ 5 := hd5le
          _ = 32 * S.D ^ 5 := by ring
      have h32' : |(s:ℝ)| * (32 * S.D ^ 5)
          = 32 * (S.Δ ^ 2 * S.Ω ^ 2 * (P.X * S.A * S.B)) * |(s:ℝ)| := by
        rw [hABID]; ring
      rw [h32'] at h32
      nlinarith [h32, mul_nonneg (mul_nonneg (mul_pos hXpos hApos).le hBpos.le)
        (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ S.Δ^2) (by positivity : (0:ℝ) ≤ S.Ω^2)) hsnn)]
    linarith [hLHS, hn]
  have hQform : (1 / (10 ^ 21 : ℝ)) * |(s : ℝ)| ≤ Q * (2 * (L * |b₀| * v ^ 2)) := by
    have hQexp : Q * (2 * (L * |b₀| * v ^ 2)) = 2 * (P.X * a * |b₀| * (L * v ^ 2)) / d ^ 5 := by
      rw [hQdef]; field_simp
    rw [hQexp, le_div_iff₀ hd5pos]
    have : (1 / (10 ^ 21 : ℝ)) * |(s:ℝ)| * d ^ 5 = (|(s:ℝ)| * d ^ 5) / 10 ^ 21 := by ring
    rw [this, div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 21)]
    nlinarith [hkey]
  linarith [hQform, hstep1]

/-- **§5 Step-4 large-defect per-`s` magnitude + extraction** (writeup 1025–1052).

For a fixed admissible nonzero integer `s` with `1 ≤ |s|` and a `v` pinned by `|v| ≍ V_s`
(the squared, denominator-cleared pin `hvpin_lo`/`hvpin_hi` with constant `C₁ = 10⁶`,
`V_s² = Δ²Ω²|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁))`), in the large-defect range (the cancellation-avoidance floor
`hvlo`, writeup 1025–1031), the closed cubic/quartic form `Σ_closed` has magnitude `≍ |s|` and
rounds to `s`:

  `(1/C)·|s| ≤ |Σ_closed| ≤ C·|s|`   and   `|Σ_closed − s| ≤ C·(E1 + NB)`,

with absolute `C = 10²¹`, `E1 = 10¹¹⁰·UpsT`, `NB = 45·Wval⁴·H/D`.  The extraction inputs
(`hround : s = round Σ_closed`, `hnear : distInt Σ_closed ≤ E1 + NB`) are discharged by the
caller via `Sigma_closed_near_int`. -/
theorem sigma_s_magnitude_extract
    {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hvpin_lo : S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|
        ≤ 1000000 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2))
    (hvpin_hi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2
        ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|))
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂))
    (hnear : distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
        ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 119 * UpsT P S) :
    (1 / (10 ^ 21 : ℝ)) * |(s : ℝ)| ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂|
      ∧ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ (10 ^ 21 : ℝ) * |(s : ℝ)|
      ∧ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)|
          ≤ (10 ^ 21 : ℝ) * (10 ^ 119 * UpsT P S + 10 ^ 11 * P.Wval ^ 4 * P.H / S.D) := by
  -- positivity of scales
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  -- abbreviations
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set L : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  have hsnn : 0 ≤ |(s : ℝ)| := abs_nonneg _
  -- Sigma_closed = Q * ((-4 + 10a/d) * P0) ;  |Sigma_closed| = Q * |-4+10a/d| * |P0|.
  have hSeq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ = Q * ((-4 + 10 * a / d) * P0) := by
    rw [Sigma_closed, hQdef, hP0def]
  have hSabs : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| = Q * (|(-4 + 10 * a / d)| * |P0|) := by
    rw [hSeq, abs_mul, abs_of_pos hQpos, abs_mul]
  -- bracket bounds : 10a/d ∈ [0, 1/8], so |-4+10a/d| ∈ [2, 7].
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi (S.D_eps_lo hdD) h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_lo : 2 ≤ |(-4 + 10 * a / d)| := by rw [le_abs]; right; linarith
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 7 := by rw [abs_le]; constructor <;> linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  -- magnitude P0 bounds
  have hP0lo : L * |b₀| * v ^ 2 ≤ |P0| := by
    have := psum_abs_ge_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo
      (S.D_half_of_win hdD) hd_pos hReg hG1 hU1 hUbig hDeW
    rw [hLdef, hP0def]
    calc ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2
        = ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 := rfl
      _ ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| := this
  have hP0hi : |P0| ≤ 4 * (L * |b₀| * v ^ 2) := by
    have := psum_abs_le_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo
      (S.D_half_of_win hdD) hd_pos hReg hG1 hU1 hUbig hDeW
    rw [hLdef, hP0def]; exact this
  have hP0nn : 0 ≤ |P0| := abs_nonneg _
  -- scale identity:  D⁵ = Δ²Ω²·X·A·B  (from defect_D5_div_XAB)
  have hABID : S.D ^ 5 = S.Δ ^ 2 * S.Ω ^ 2 * (P.X * S.A * S.B) := by
    have h := defect_D5_div_XAB (P := P) S
    rw [div_eq_iff (by positivity : P.X * S.A * S.B ≠ 0)] at h
    linarith [h]
  have hd5pos : (0:ℝ) < d ^ 5 := by positivity
  have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
  have hAval : S.A = S.Δ * S.Ω := rfl
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hLv2nn : 0 ≤ L * v ^ 2 := by positivity
  -- ===================== (1) LOWER BOUND :  (1/10²¹)·|s| ≤ |Σ_closed| =====================
  have hlower : (1 / (10 ^ 21 : ℝ)) * |(s : ℝ)| ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
    -- |Σ_closed| ≥ Q · (2 · (L|b₀|v²))
    have hstep1 : Q * (2 * (L * |b₀| * v ^ 2)) ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
      rw [hSabs]
      apply mul_le_mul_of_nonneg_left _ hQpos.le
      exact mul_le_mul hbr_lo hP0lo (by positivity) hbr_nn
    -- |s|·d⁵ ≤ 2·10²¹·X·a·|b₀|·(L·v²)
    have hkey : |(s : ℝ)| * d ^ 5 ≤ 2 * 10 ^ 21 * (P.X * a * |b₀| * (L * v ^ 2)) := by
      -- numerator lower bounds : a ≥ A/5, |b₀| ≥ B/2e6, L v² ≥ Δ²Ω²|s|/1e6
      have hn : 2 * 10 ^ 8 * (P.X * S.A * S.B * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|))
          ≤ 2 * 10 ^ 21 * (P.X * a * |b₀| * (L * v ^ 2)) := by
        have e1 : P.X * (S.A / 5) * (S.B / 2000000) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)| / 1000000)
            ≤ P.X * a * |b₀| * (L * v ^ 2) := by
          have hb1 : P.X * (S.A / 5) ≤ P.X * a :=
            mul_le_mul_of_nonneg_left ha_lo hXpos.le
          have hb2 : P.X * (S.A / 5) * (S.B / 2000000)
              ≤ P.X * a * |b₀| :=
            mul_le_mul hb1 hb0lo (by positivity) (by positivity)
          have hb3 : S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)| / 1000000 ≤ L * v ^ 2 := by
            rw [div_le_iff₀ (by norm_num)]; linarith [hvpin_lo]
          exact mul_le_mul hb2 hb3 (by positivity) (by positivity)
        nlinarith [e1, mul_pos hXpos (mul_pos hApos hBpos)]
      -- LHS |s|·d⁵ ≤ |s|·(2D)⁵ = 32·|s|·D⁵ = 32·|s|·(Δ²Ω²XAB) ≤ 2·10⁸·(…)
      have hd5le : d ^ 5 ≤ (2 * S.D) ^ 5 := by
        apply pow_le_pow_left₀ hd_pos.le hd2D
      have hLHS : |(s:ℝ)| * d ^ 5 ≤ 2 * 10 ^ 8 * (P.X * S.A * S.B * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|)) := by
        have h32 : |(s:ℝ)| * d ^ 5 ≤ |(s:ℝ)| * (32 * S.D ^ 5) := by
          apply mul_le_mul_of_nonneg_left _ hsnn
          calc d ^ 5 ≤ (2 * S.D) ^ 5 := hd5le
            _ = 32 * S.D ^ 5 := by ring
        have h32' : |(s:ℝ)| * (32 * S.D ^ 5)
            = 32 * (S.Δ ^ 2 * S.Ω ^ 2 * (P.X * S.A * S.B)) * |(s:ℝ)| := by
          rw [hABID]; ring
        rw [h32'] at h32
        nlinarith [h32, mul_nonneg (mul_nonneg (mul_pos hXpos hApos).le hBpos.le)
          (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ S.Δ^2) (by positivity : (0:ℝ) ≤ S.Ω^2)) hsnn)]
      linarith [hLHS, hn]
    -- convert |s|·d⁵ ≤ … into the Q-form and finish
    have hQform : (1 / (10 ^ 21 : ℝ)) * |(s : ℝ)| ≤ Q * (2 * (L * |b₀| * v ^ 2)) := by
      have hQexp : Q * (2 * (L * |b₀| * v ^ 2)) = 2 * (P.X * a * |b₀| * (L * v ^ 2)) / d ^ 5 := by
        rw [hQdef]; field_simp
      rw [hQexp, le_div_iff₀ hd5pos]
      have : (1 / (10 ^ 21 : ℝ)) * |(s:ℝ)| * d ^ 5 = (|(s:ℝ)| * d ^ 5) / 10 ^ 21 := by ring
      rw [this, div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 21)]
      nlinarith [hkey]
    linarith [hQform, hstep1]
  -- ===================== (2) UPPER BOUND :  |Σ_closed| ≤ 10²¹·|s| =====================
  have hupper : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ (10 ^ 21 : ℝ) * |(s : ℝ)| := by
    -- |Σ_closed| ≤ Q · (7 · (4 · (L|b₀|v²)))
    have hstep1 : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ Q * (7 * (4 * (L * |b₀| * v ^ 2))) := by
      rw [hSabs]
      apply mul_le_mul_of_nonneg_left _ hQpos.le
      exact mul_le_mul hbr_hi hP0hi hP0nn (by norm_num)
    -- Q · (28 · L|b₀|v²) = 28·X·a·|b₀|·(L·v²)/d⁵ ≤ 28·X·a·|b₀|·(L·v²)/D⁵
    have hQexp : Q * (7 * (4 * (L * |b₀| * v ^ 2)))
        = 28 * (P.X * a * |b₀| * (L * v ^ 2)) / d ^ 5 := by
      rw [hQdef]; field_simp; ring
    have hnum_nn : 0 ≤ 28 * (P.X * a * |b₀| * (L * v ^ 2)) := by positivity
    have hD5d5 : S.D ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ hDpos.le hdD 5
    have hd5D5 : 28 * (P.X * a * |b₀| * (L * v ^ 2)) / d ^ 5
        ≤ 28 * (P.X * a * |b₀| * (L * v ^ 2)) / S.D ^ 5 := by
      gcongr
    -- numerator upper bound :  28·X·a·|b₀|·(L v²) ≤ 924·10¹⁸·X·A·B·(Δ²Ω²|s|)
    have hnum : 28 * (P.X * a * |b₀| * (L * v ^ 2))
        ≤ 924 * 10 ^ 18 * (P.X * S.A * S.B * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|)) := by
      have e1 : P.X * a * |b₀| * (L * v ^ 2)
          ≤ P.X * (11 * S.A) * (3000000000000 * S.B)
              * (1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|)) := by
        have hb1 : P.X * a ≤ P.X * (11 * S.A) := mul_le_mul_of_nonneg_left ha_hi hXpos.le
        have hb2 : P.X * a * |b₀| ≤ P.X * (11 * S.A) * (3000000000000 * S.B) :=
          mul_le_mul hb1 hb0 hb0nn (by positivity)
        exact mul_le_mul hb2 hvpin_hi hLv2nn (by positivity)
      nlinarith [e1, mul_pos hXpos (mul_pos hApos hBpos)]
    -- D⁵ = Δ²Ω²·X·A·B, so the RHS/D⁵ = 924·10¹⁸·|s|
    have hcollapse : 924 * 10 ^ 18 * (P.X * S.A * S.B * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|)) / S.D ^ 5
        = 924 * 10 ^ 18 * |(s : ℝ)| := by
      rw [hABID]; field_simp
    have hfin : 28 * (P.X * a * |b₀| * (L * v ^ 2)) / S.D ^ 5 ≤ 924 * 10 ^ 18 * |(s : ℝ)| := by
      rw [← hcollapse]; gcongr
    have hconst : (924 : ℝ) * 10 ^ 18 * |(s:ℝ)| ≤ 10 ^ 21 * |(s : ℝ)| := by
      apply mul_le_mul_of_nonneg_right _ hsnn; norm_num
    calc |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂|
        ≤ Q * (7 * (4 * (L * |b₀| * v ^ 2))) := hstep1
      _ = 28 * (P.X * a * |b₀| * (L * v ^ 2)) / d ^ 5 := hQexp
      _ ≤ 28 * (P.X * a * |b₀| * (L * v ^ 2)) / S.D ^ 5 := hd5D5
      _ ≤ 924 * 10 ^ 18 * |(s : ℝ)| := hfin
      _ ≤ 10 ^ 21 * |(s : ℝ)| := hconst
  -- ===================== (3) EXTRACTION :  |Σ_closed − s| ≤ 10²¹·(E1 + NB) =====================
  have hextract : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)|
      ≤ (10 ^ 21 : ℝ) * (10 ^ 119 * UpsT P S + 10 ^ 11 * P.Wval ^ 4 * P.H / S.D) := by
    -- s = round Σ_closed, so |Σ_closed − s| = distInt Σ_closed ≤ NB + E1
    have hdist : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)|
        = distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) := by
      rw [distInt, hround]
    rw [hdist]
    have hEpos : 0 ≤ 10 ^ 119 * UpsT P S + 10 ^ 11 * P.Wval ^ 4 * P.H / S.D := by
      have : 0 ≤ UpsT P S := by rw [UpsT]; positivity
      have hW : 0 ≤ P.Wval := by rw [Globals.Wval]; positivity
      positivity
    calc distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
        ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 119 * UpsT P S := hnear
      _ = 10 ^ 119 * UpsT P S + 10 ^ 11 * P.Wval ^ 4 * P.H / S.D := by ring
      _ ≤ 10 ^ 21 * (10 ^ 119 * UpsT P S + 10 ^ 11 * P.Wval ^ 4 * P.H / S.D) := by
          apply le_mul_of_one_le_left hEpos; norm_num
  exact ⟨hlower, hupper, hextract⟩
