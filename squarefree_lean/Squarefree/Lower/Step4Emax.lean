import Squarefree.Lower.Step4Diam

/-!
# §5 Step-4 perturbation collapse `E ≤ ρ·|s|` (writeup 1052–1064; additive route)

`Sigma_closed_diff_Cref_le` (`Step4Diam.lean`) bounds the deviation of the closed form `Σ_closed`
from the fixed model parabola `Ĉ·v²` by a symbolic four-term budget

  `E = E_recon + E_drift + E_cubic + E_p2`.

This file collapses that budget to a single clean **negative-`X`-power** majorant of `|s|`,

  `E ≤ ρ·|s|`,    `ρ = 231·10⁶/Δ  +  6·10⁷·Ω²/H²  +  1/U¹⁴  +  8316·10⁵⁷·ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²/(G²Ω⁸)`,

so the `E`-part of the §5 `s`-summation is `≪ RHS`.  The four collapses are:

* **`E_drift`, `E_recon`** — both `∝ (ℓ₁v)²`.  The pin `hvpin_hi` gives `ℓ₁³ℓ₂(ℓ₂−ℓ₁)v² ≤ 10⁶Δ²Ω²|s|`,
  and the `(A/a)²` renormalization cancels the explicit `a` (`E_drift = 60·ℓ₁³ℓ₂(ℓ₂−ℓ₁)v²/d²`,
  the `a²` of `(a/d)²` cancelling `1/a²`).  With `d ≥ D = HΔ`, `E_drift ≤ 6·10⁷·Ω²/H²·|s|`.  For
  `E_recon` the slope gap `gap ≤ Δ/(GΩ³)` plus `Q = Xa/d⁵ ≤ 11GΩ/Δ⁴` and the bracket `≤ 7` give
  `Q·7·gap ≤ 77/(Δ³Ω²)`, hence `E_recon ≤ 231·10⁶/Δ·|s|`.
* **`E_cubic = (1/U¹⁴)·|s|`** already (`ρ_cub = 1/U¹⁴`).
* **`E_p2`** — `Vx ≤ Bx` collapses the quartic majorant to `40·ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²·Bx³·Vx`; with
  `Bx = 3·10¹²·B` and `Vx ≤ V_box = 10²⁰ΔU⁵/Ω³` it is `s`-independent, and `|s| ≥ 1` lifts it to
  `≤ ρ_p2·|s|`, where the residual `Δ²U⁵/H ≤ Ω³` (regime `hReg`) collapses the scale to `1/(G²Ω⁸)`.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The quartic absolute majorant collapses, on the box `0 ≤ Vx ≤ Bx` with `1 ≤ ℓ₁`,
`ℓ₁+1 ≤ ℓ₂`, to a single `Bx³·Vx` monomial: `P2AbsMaj ≤ 40·ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²·Bx³·Vx`. -/
private theorem P2AbsMaj_collapse {ℓ₁ ℓ₂ Bx Vx : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hVx0 : 0 ≤ Vx) (hVxBx : Vx ≤ Bx) :
    P2AbsMaj ℓ₁ ℓ₂ Bx Vx ≤ 40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) * (Bx ^ 3 * Vx) := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ1nn : (0:ℝ) ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : (0:ℝ) ≤ ℓ₂ := hℓ2pos.le
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h21ge1 : (1:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hBx0 : 0 ≤ Bx := le_trans hVx0 hVxBx
  -- power collapses  Bx^iVx^j ≤ Bx³Vx  (i+j=4, j≥1) from Vx ≤ Bx
  have hp2 : Bx ^ 2 * Vx ^ 2 ≤ Bx ^ 3 * Vx := by
    nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hBx0 2) hVx0) (sub_nonneg.2 hVxBx)]
  have hp3 : Bx * Vx ^ 3 ≤ Bx ^ 3 * Vx := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hBx0 hVx0)
      (sub_nonneg.2 (pow_le_pow_left₀ hVx0 hVxBx 2))) (le_refl (0:ℝ)),
      mul_nonneg (mul_nonneg hBx0 hVx0) (sub_nonneg.2 (pow_le_pow_left₀ hVx0 hVxBx 2))]
  have hp4 : Vx ^ 4 ≤ Bx ^ 3 * Vx := by
    nlinarith [mul_nonneg hVx0 (sub_nonneg.2 (pow_le_pow_left₀ hVx0 hVxBx 3))]
  have hWnn : (0:ℝ) ≤ Bx ^ 3 * Vx := mul_nonneg (pow_nonneg hBx0 3) hVx0
  -- ℓ-coefficient nonnegs
  have hc1nn : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hc2nn : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) := by
    have := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 15 * ℓ₁ ^ 3) (by positivity : (0:ℝ) ≤ ℓ₂ ^ 2)) h21nn
    nlinarith [this]
  have hc3nn : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) := by
    have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 5 * ℓ₁ ^ 3) hℓ2nn) h32]
  have hc4nn : (0:ℝ) ≤ (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := by
    have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (5 / 2) * ℓ₁ ^ 3) h2ℓ]
  -- Step A: each monomial ≤ its ℓ-coeff times Bx³Vx
  have hm1 : 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * Bx ^ 3 * Vx
      ≤ (5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) * (Bx ^ 3 * Vx) := le_of_eq (by ring)
  have hm2 : 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * Bx ^ 2 * Vx ^ 2
      ≤ (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) * (Bx ^ 3 * Vx) := by
    calc 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * Bx ^ 2 * Vx ^ 2
        = (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) * (Bx ^ 2 * Vx ^ 2) := by ring
      _ ≤ (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) * (Bx ^ 3 * Vx) :=
          mul_le_mul_of_nonneg_left hp2 hc2nn
  have hm3 : 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * Bx * Vx ^ 3
      ≤ (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * (Bx ^ 3 * Vx) := by
    calc 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * Bx * Vx ^ 3
        = (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * (Bx * Vx ^ 3) := by ring
      _ ≤ (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * (Bx ^ 3 * Vx) :=
          mul_le_mul_of_nonneg_left hp3 hc3nn
  have hm4 : (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * Vx ^ 4
      ≤ ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (Bx ^ 3 * Vx) := by
    calc (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * Vx ^ 4
        = ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * Vx ^ 4 := by ring
      _ ≤ ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (Bx ^ 3 * Vx) :=
          mul_le_mul_of_nonneg_left hp4 hc4nn
  -- Step B: ℓ-bracket ≤ 40·base
  have hLpoly : (5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
        + (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))
        + (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))
        + ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))
      ≤ 40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hℓ1nn 3) (pow_nonneg hℓ2nn 2)) h21nn)
        (show (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1 by linarith),
      mul_nonneg (mul_nonneg (pow_nonneg hℓ1nn 3) (pow_nonneg hℓ2nn 2))
        (show (0:ℝ) ≤ (ℓ₂ - ℓ₁) ^ 2 - 1 by nlinarith [h21ge1]),
      mul_nonneg (pow_nonneg hℓ1nn 3)
        (show (0:ℝ) ≤ ℓ₂ * ((ℓ₂ - ℓ₁) ^ 2 - 1) by
          have : (0:ℝ) ≤ (ℓ₂ - ℓ₁) ^ 2 - 1 := by nlinarith [h21ge1]
          positivity),
      mul_nonneg (pow_nonneg hℓ1nn 3) hℓ1nn,
      mul_nonneg (pow_nonneg hℓ1nn 3) (mul_nonneg hℓ2nn (sq_nonneg (ℓ₂ - ℓ₁))),
      mul_nonneg (pow_nonneg hℓ1nn 3) hℓ2nn]
  -- assemble
  have hsum := add_le_add (add_le_add (add_le_add hm1 hm2) hm3) hm4
  have hLW : ((5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
        + (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))
        + (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))
        + ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * (Bx ^ 3 * Vx)
      ≤ (40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)) * (Bx ^ 3 * Vx) :=
    mul_le_mul_of_nonneg_right hLpoly hWnn
  calc P2AbsMaj ℓ₁ ℓ₂ Bx Vx
      = 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * Bx ^ 3 * Vx
        + 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * Bx ^ 2 * Vx ^ 2
        + 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * Bx * Vx ^ 3
        + (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * Vx ^ 4 := rfl
    _ ≤ ((5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) * (Bx ^ 3 * Vx)
          + (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) * (Bx ^ 3 * Vx)
          + (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * (Bx ^ 3 * Vx)
          + ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (Bx ^ 3 * Vx)) := hsum
    _ = ((5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
          + (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))
          + (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))
          + ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * (Bx ^ 3 * Vx) := by ring
    _ ≤ (40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)) * (Bx ^ 3 * Vx) := hLW
    _ = 40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) * (Bx ^ 3 * Vx) := by ring

/-- **§5 Step-4 perturbation collapse** (writeup 1052–1064).  The symbolic four-term budget `E` of
`Sigma_closed_diff_Cref_le` is dominated by a single clean negative-`X`-power majorant of `|s|`:

  `E ≤ ρ·|s|`,  `ρ = 231·10⁶/Δ + 6·10⁷·Ω²/H² + 1/U¹⁴ + 8316·10⁵⁷·ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²/(G²Ω⁸)`.

Hypotheses: the §5 band box (`Vx ≤ V_box`, the `|v|≍V_s` pin `hvpin_hi`), the `b₀`-box convention
`Bx = 3·10¹²·B`, the smooth-slope gap `gap ≤ Δ/(GΩ³)`, the nonzero near-integer `1 ≤ |s|`, and the
reusable Step-4 regime set. -/
theorem Step4_E_le_rho_s
    {a d v gap Bx Vx ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hdD : S.D ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hvpin_hi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2
        ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|))
    (hgap0 : 0 ≤ gap) (hgap : gap ≤ S.Δ / (P.G * S.Ω ^ 3))
    (hBx : Bx = 3000000000000 * S.B)
    (hVx0 : 0 ≤ Vx) (hvxbox : Vx ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hs1 : 1 ≤ |(s : ℝ)|) :
    (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)| * gap * (ℓ₁ * v) ^ 2
        + 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
        + (1 / P.U ^ 14) * |(s : ℝ)|
        + 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D)
      ≤ (231 * 10 ^ 6 / S.Δ
          + 6 * 10 ^ 7 * S.Ω ^ 2 / P.H ^ 2
          + 1 / P.U ^ 14
          + 8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 8))
        * |(s : ℝ)| := by
  -- positivity scaffolding
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
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hΔne : S.Δ ≠ 0 := hΔpos.ne'
  have hΩne : S.Ω ≠ 0 := hΩpos.ne'
  have hGne : P.G ≠ 0 := hGpos.ne'
  have hHne : P.H ≠ 0 := hHpos.ne'
  have hane : a ≠ 0 := ha0.ne'
  have hdne : d ≠ 0 := hd_pos.ne'
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  have hsnn : (0:ℝ) ≤ |(s:ℝ)| := abs_nonneg _
  -- bracket bound  |−4 + 10a/d| ≤ 7
  obtain ⟨_, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi (S.D_eps_lo hdD) h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr : |(-4 + 10 * a / d)| ≤ 7 := by rw [abs_le]; constructor <;> linarith
  -- Q ≤ 11GΩ/Δ⁴
  have hQle : P.X * a / d ^ 5 ≤ 11 * P.G * S.Ω / S.Δ ^ 4 := by
    have hD5 : S.D ^ 5 = P.X * S.Δ ^ 5 / P.G := by
      unfold Scale.D; rw [P.X_eq_G_mul_H_pow_five]; field_simp
    have hd5ge : S.D ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ hDpos.le hdD 5
    calc P.X * a / d ^ 5 ≤ P.X * a / S.D ^ 5 := by gcongr
      _ = a * P.G / S.Δ ^ 5 := by rw [hD5]; field_simp
      _ ≤ 11 * P.G * S.Ω / S.Δ ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right haA (by positivity : (0:ℝ) ≤ P.G * S.Δ ^ 4),
            hΔpos, hΩpos, hGpos]
  --==================  E_recon  ==================
  have hRecon : (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)|
        * gap * (ℓ₁ * v) ^ 2
      ≤ (231 * 10 ^ 6 / S.Δ) * |(s : ℝ)| := by
    have hform : (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)|
          * gap * (ℓ₁ * v) ^ 2
        = ((P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap)
            * (3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)) := by ring
    have hQbr : (P.X * a / d ^ 5) * |(-4 + 10 * a / d)| ≤ (11 * P.G * S.Ω / S.Δ ^ 4) * 7 :=
      mul_le_mul hQle hbr (abs_nonneg _) (by positivity)
    have hcoeff : (P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap ≤ 77 / (S.Δ ^ 3 * S.Ω ^ 2) := by
      have hstep : (P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap
          ≤ ((11 * P.G * S.Ω / S.Δ ^ 4) * 7) * (S.Δ / (P.G * S.Ω ^ 3)) :=
        mul_le_mul hQbr hgap hgap0 (by positivity)
      refine hstep.trans (le_of_eq ?_)
      field_simp; ring
    have hpin3 : 3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)
        ≤ 3 * (1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|)) :=
      mul_le_mul_of_nonneg_left hvpin_hi (by norm_num)
    have h3nn : (0:ℝ) ≤ 3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg
        (pow_nonneg hℓ1pos.le 3) hℓ2pos.le) h21nn) (sq_nonneg v))
    rw [hform]
    calc ((P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap) * (3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2))
        ≤ (77 / (S.Δ ^ 3 * S.Ω ^ 2)) * (3 * (1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|))) :=
          mul_le_mul hcoeff hpin3 h3nn (by positivity)
      _ = (231 * 10 ^ 6 / S.Δ) * |(s : ℝ)| := by field_simp; ring
  --==================  E_drift  ==================
  have hDrift : 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
      ≤ (6 * 10 ^ 7 * S.Ω ^ 2 / P.H ^ 2) * |(s : ℝ)| := by
    have hbridge : Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / a ^ 2 := by
      unfold Cref Scale.A; field_simp
    have heq : 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
        = 60 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) / d ^ 2 := by
      rw [hbridge]; field_simp; ring
    rw [heq]
    have hd2pos : (0:ℝ) < d ^ 2 := by positivity
    have hD2 : S.D ^ 2 = P.H ^ 2 * S.Δ ^ 2 := by unfold Scale.D; ring
    calc 60 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) / d ^ 2
        ≤ 60 * (1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|)) / d ^ 2 := by
          gcongr
      _ ≤ 60 * (1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|)) / S.D ^ 2 := by
          gcongr
      _ = (6 * 10 ^ 7 * S.Ω ^ 2 / P.H ^ 2) * |(s : ℝ)| := by rw [hD2]; field_simp; ring
  --==================  E_p2  ==================
  have hP2 : 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D)
      ≤ (8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 8)) * |(s : ℝ)| := by
    -- box facts:  Vx ≤ V_box ≤ B ≤ Bx
    have hkey : 10 ^ 20 * P.G * P.U ^ 5 ≤ S.Δ := by
      have hU15 : (10:ℝ) ^ 5 ≤ P.U ^ 15 := by
        have hstep := pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ) ≤ 10 ^ 33) hUbig)
          (show 1 ≤ 15 by norm_num)
        calc (10:ℝ) ^ 5 ≤ P.U := le_trans (by norm_num) hUbig
          _ = P.U ^ 1 := (pow_one _).symm
          _ ≤ P.U ^ 15 := hstep
      have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
      have hGU : (10:ℝ) ^ 5 ≤ P.G ^ 3 * P.U ^ 15 := by
        nlinarith [hU15, hG3, mul_nonneg (by linarith [hG3] : (0:ℝ) ≤ P.G ^ 3 - 1)
          (pow_nonneg hUpos.le 15)]
      nlinarith [hDeW, mul_le_mul_of_nonneg_left hGU (by positivity : (0:ℝ) ≤ 10 ^ 15 * P.G * P.U ^ 5)]
    have hVboxB : 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) ≤ S.B := by
      unfold Scale.B
      rw [le_div_iff₀ (by positivity : (0:ℝ) < P.G * S.Ω ^ 3)]
      have he : 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) * (P.G * S.Ω ^ 3)
          = 10 ^ 20 * P.G * P.U ^ 5 * S.Δ := by field_simp
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_right hkey hΔpos.le]
    have hVxBx : Vx ≤ Bx := by
      rw [hBx]
      have hBnn : (0:ℝ) ≤ S.B := by unfold Scale.B; positivity
      have : S.B ≤ 3000000000000 * S.B := by nlinarith [hBnn]
      linarith [hvxbox, hVboxB, this]
    have hcollapse := P2AbsMaj_collapse hℓ1 hℓ12 hℓ12' hVx0 hVxBx
    have hKnn : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) / S.D := by positivity
    have hℓbnn : (0:ℝ) ≤ 40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg
        (pow_nonneg hℓ1pos.le 3) (pow_nonneg hℓ2pos.le 2)) (pow_nonneg h21nn 2))
    have hBx3nn : (0:ℝ) ≤ Bx ^ 3 := by
      have : (0:ℝ) ≤ Bx := le_trans hVx0 hVxBx
      positivity
    have hΔU5H : S.Δ ^ 2 * P.U ^ 5 / P.H ≤ S.Ω ^ 3 :=
      (div_le_iff₀ hHpos).mpr (by rw [mul_comm (S.Ω ^ 3) P.H]; exact hReg)
    have hcoeffnn : (0:ℝ) ≤ 8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 11) :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg
        (pow_nonneg hℓ1pos.le 3) (pow_nonneg hℓ2pos.le 2)) (pow_nonneg h21nn 2))) (by positivity)
    have hρnn : (0:ℝ) ≤ 8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 8) :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg
        (pow_nonneg hℓ1pos.le 3) (pow_nonneg hℓ2pos.le 2)) (pow_nonneg h21nn 2))) (by positivity)
    calc 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D)
        = (77 * (P.G * S.Ω / S.Δ ^ 4) / S.D) * P2AbsMaj ℓ₁ ℓ₂ Bx Vx := by ring
      _ ≤ (77 * (P.G * S.Ω / S.Δ ^ 4) / S.D)
            * (40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) * (Bx ^ 3 * Vx)) :=
          mul_le_mul_of_nonneg_left hcollapse hKnn
      _ ≤ (77 * (P.G * S.Ω / S.Δ ^ 4) / S.D)
            * (40 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
              * (Bx ^ 3 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))) := by
          apply mul_le_mul_of_nonneg_left _ hKnn
          apply mul_le_mul_of_nonneg_left _ hℓbnn
          exact mul_le_mul_of_nonneg_left hvxbox hBx3nn
      _ = (8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 11))
            * (S.Δ ^ 2 * P.U ^ 5 / P.H) := by
          rw [hBx]; unfold Scale.B Scale.D; field_simp; ring
      _ ≤ (8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 11)) * S.Ω ^ 3 :=
          mul_le_mul_of_nonneg_left hΔU5H hcoeffnn
      _ = 8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 8) := by
          field_simp
      _ ≤ (8316 * 10 ^ 57 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) / (P.G ^ 2 * S.Ω ^ 8)) * |(s : ℝ)| :=
          le_mul_of_one_le_right hρnn hs1
  --==================  assemble  ==================
  refine le_trans (add_le_add (add_le_add (add_le_add hRecon hDrift)
    (le_refl ((1 / P.U ^ 14) * |(s : ℝ)|))) hP2) (le_of_eq ?_)
  ring

end Squarefree
