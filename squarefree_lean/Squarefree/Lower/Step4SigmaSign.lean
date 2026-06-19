import Squarefree.Lower.Step4Parabola

/-!
# §5 Step-4 sign of the extracted integer `s` (writeup 1052–1058)

`step4_fiber_extract` (`Step4Fiber.lean`) returns the nonzero integer `s = round(Σ_closed)` with
`1 ≤ |s| ≤ cap`, but **not** its sign.  The Step-4 assembly groups fibres by a uniform sign of
the square-difference, so it needs `s` pinned to one sign across the whole `b₀ < 0` (smooth-slope)
regime.  This file supplies that.

## The derived sign is `s > 0`

`Σ_closed = (Xa/d⁵)·(−4 + 10a/d)·(P₁ + P₂/d)`.  At the large-defect `v`-band, the SHARP parabola
`Sigma_closed_parabola_sharp` shows `Σ_closed` agrees with its leading quadratic
`LEAD := (Xa/d⁵)·(−4+10a/d)·(3ℓ₁ℓ₂(ℓ₂−ℓ₁)b₀)·(ℓ₁v)²` up to `(1/10²⁹)·|s|`.  Tracking the three
sign-bearing factors of `LEAD` under `b₀ < 0`:

* prefactor `Xa/d⁵ > 0`;
* bracket `−4 + 10a/d < 0` (the large-defect regime, `10a/d ≤ 1/8` via `bracket_ad_small`);
* coefficient `3ℓ₁ℓ₂(ℓ₂−ℓ₁)b₀ < 0` (since `b₀ < 0`);
* square `(ℓ₁v)² > 0`.

so `LEAD = (+)·(−)·(−)·(+) > 0`.  Equivalently the P-sum `P₁ + P₂/d ≈ 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)b₀v² < 0`, and
`Σ_closed = (prefactor +)·(bracket −)·(P-sum −) > 0`.  Since the residual is `≪ |s|` and the round
floor gives `|Σ_closed| ≥ ½|s| ≥ ½`, the leading term dominates and `Σ_closed > 0`, hence
`round(Σ_closed) = s > 0`.

(Note: this corrects the orchestrator's tentative `s < 0`; the algebra gives `s > 0`.  The assembly
only requires a *uniform* sign, which `s > 0` supplies.)
-/

namespace Squarefree

open Real Squarefree.Counting

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 sign of `Σ_closed` in the `b₀ < 0` regime.**  Under the smooth-slope regime
`b₀ < 0` and the large-defect `v`-band data of `Sigma_closed_parabola_sharp`, the closed form is
positive: `0 < Σ_closed`.  Same hypothesis set as `Sigma_closed_parabola_sharp` plus `b₀ < 0`. -/
theorem Sigma_closed_sign_pos
    {a b₀ v d ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hb0neg : b₀ < 0)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) :
    0 < Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ := by
  have hXpos : 0 < P.X := P.X_pos
  have hDpos : 0 < S.D := by unfold Scale.D; exact mul_pos P.H_pos S.Δ_pos
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  -- the SHARP parabola residual:  |Σ_closed − LEAD| ≤ (1/10²⁹)|s|
  have hsharp := Sigma_closed_parabola_sharp (P := P) (S := S) ha0 ha_hi hℓ1 hℓ12 hℓ12'
    hℓ2W hb0 hb0lo hv hvlo hVcut hdD hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hs1 hround
  set LEAD : ℝ := (P.X * a / d ^ 5) * (-4 + 10 * a / d)
      * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀) * (ℓ₁ * v) ^ 2 with hLEAD
  set sc : ℝ := Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ with hsc
  -- === LEAD > 0 : sign-bearing factor analysis ===
  obtain ⟨had0, hadhi⟩ := bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_neg : -4 + 10 * a / d < 0 := by linarith
  have hQ : 0 < P.X * a / d ^ 5 := div_pos (mul_pos hXpos ha0) (pow_pos hd_pos 5)
  have hcoef_pos3 : 0 < 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hℓ1pos) hℓ2pos) h21pos
  have hcoef_neg : 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ < 0 :=
    mul_neg_of_pos_of_neg hcoef_pos3 hb0neg
  -- v ≠ 0 from the lower band:  RHS of `hvlo` is > 0
  have hb0sq : 0 < b₀ ^ 2 := by rw [pow_two]; exact mul_pos_of_neg_of_neg hb0neg hb0neg
  have hrhs_pos : 0 < 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) := by
    have : 0 < ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d :=
      div_pos (mul_pos (mul_pos hℓ2pos h21pos) hb0sq) hd_pos
    linarith
  have hvpos : 0 < |v| := lt_of_lt_of_le hrhs_pos hvlo
  have hv_ne : v ≠ 0 := by
    intro h; rw [h, abs_zero] at hvpos; exact lt_irrefl 0 hvpos
  have hℓv_ne : ℓ₁ * v ≠ 0 := mul_ne_zero (ne_of_gt hℓ1pos) hv_ne
  have hsq_pos : 0 < (ℓ₁ * v) ^ 2 :=
    (sq_nonneg _).lt_of_ne (pow_ne_zero 2 hℓv_ne).symm
  have hLpos : 0 < LEAD := by
    rw [hLEAD]
    exact mul_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hQ hbr_neg) hcoef_neg) hsq_pos
  -- === round floor + residual domination ===
  have hhalf : |sc - (s : ℝ)| ≤ 1 / 2 := by rw [hround]; exact abs_sub_round sc
  have hSabs_ub : |sc| ≤ LEAD + |sc - LEAD| := by
    have h : sc = LEAD + (sc - LEAD) := by ring
    calc |sc| = |LEAD + (sc - LEAD)| := by rw [← h]
      _ ≤ |LEAD| + |sc - LEAD| := abs_add_le _ _
      _ = LEAD + |sc - LEAD| := by rw [abs_of_pos hLpos]
  have hSabs_lb : |(s : ℝ)| - 1 / 2 ≤ |sc| := by
    have h := abs_sub_abs_le_abs_sub (s : ℝ) sc
    rw [abs_sub_comm] at h
    linarith [h, hhalf]
  have hsharp8 : |sc - LEAD| ≤ (1 / 8) * |(s : ℝ)| :=
    le_trans hsharp (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))
  have hlow := (abs_le.mp hsharp8).1
  -- assemble : LEAD ≥ (7/8)|s| − 1/2, sc ≥ (3/4)|s| − 1/2 ≥ 1/4 > 0
  linarith [hSabs_lb, hSabs_ub, hsharp8, hlow, hs1]

/-- **§5 Step-4 sign of the extracted integer `s`.**  In the `b₀ < 0` regime, the integer
`s = round(Σ_closed)` returned by `step4_fiber_extract` satisfies `0 < s`.  (Hence `s = +|s|`, the
uniform positive sign the assembly groups on.)  Same hypotheses as `Sigma_closed_sign_pos`. -/
theorem round_Sigma_closed_pos
    {a b₀ v d ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (_ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hb0neg : b₀ < 0)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (_hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) :
    0 < s := by
  have hpos := Sigma_closed_sign_pos (P := P) (S := S) ha0 ha_hi hℓ1 hℓ12 hℓ12' hℓ2W
    hb0 hb0lo hb0neg hv hvlo hVcut hdD hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hs1 hround
  have hhalf : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)| ≤ 1 / 2 := by
    rw [hround]; exact abs_sub_round _
  have h2 := (abs_le.mp hhalf).2   -- Σ_closed − s ≤ 1/2
  have hsgt : (-1 / 2 : ℝ) < (s : ℝ) := by linarith [hpos, h2]
  have hpos_real : (0 : ℝ) < (s : ℝ) := by
    by_contra h
    rw [not_lt] at h     -- h : (s : ℝ) ≤ 0
    have hbnd : |(s : ℝ)| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hsgt, h]
    linarith [hs1, hbnd]
  exact_mod_cast hpos_real

end Squarefree
