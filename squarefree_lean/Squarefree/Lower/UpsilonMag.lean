import Squarefree.Lower.DefectUpsilon
import Squarefree.Lower.DefectScales

/-!
# §5 Step-4: magnitude bounds for the leading term `Lval` (writeup 1029–1035)

The §5 Step-4 s-extraction (`Upsilon_s_extract`) needs two magnitude facts about the
leading cubic/quartic value

  `Lval := (Xa/d⁵)·((−4+10a/d)·(P₁ + P₂/d))`,

where `P₁ = Pone b₀ v ℓ₁ ℓ₂`, `P₂ = Ptwo b₀ v ℓ₁ ℓ₂` are the polynomials of `DefectUpsilon`.

* **`leading_abs_le`** (the upper bound, writeup 1035): under the per-`r` scale bounds
  (`a ≍ A`, `D ≤ d ≤ 2D`, `|b₀| ≤ 3·10¹²B`, `|v| ≤ 10²⁰·ΔU⁵/Ω³`, `ℓ ≤ W = GU⁵`),
  `|Lval| ≤ 10^k·(G⁵U³⁵/Ω⁸)`.

The dominant contribution is the `b₀v²`-piece of `P₁`, whose `(Xa/d⁵)`-weight is exactly
`G⁵U³⁵/Ω⁸`; every other monomial is smaller by a factor `≤ 1` under the §5 regime
(`Δ²U⁵/(HΩ³) ≤ 1`, `1/Δ ≤ 1`).  This is the same scale arithmetic as `qgen_piece_le`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

variable {P : Globals} {S : Scale P}

/-- The leading cubic/quartic value of `Upsilon_expand`. -/
noncomputable def Lval (X a d b₀ v ℓ₁ ℓ₂ : ℝ) : ℝ :=
  (X * a / d ^ 5) * ((-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d))

/-- **§5 Step-4 leading-term upper bound** (writeup 1035). -/
theorem leading_abs_le {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (_ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1pos : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D * (1 - 1/10 ^ 9) ≤ d ∧ d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    |Lval P.X a d b₀ v ℓ₁ ℓ₂|
      ≤ 10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by
  -- positivity of scales
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  obtain ⟨hdD, hd2D⟩ := hdwin
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  -- ℓ bounds
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2pos.le
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- a > 0
  have haR : 0 < a := ha0
  -- KEY regime fact: Δ²·U⁵ ≤ H·Ω³  (from h1 + band + Ω ≤ U)
  have hGU5Ω3 : (1 : ℝ) ≤ P.G * P.U ^ 5 * S.Ω ^ 3 := by
    have hU2Ω : P.U ≤ P.U ^ 2 / S.Ω := by
      rw [le_div_iff₀ hΩpos, pow_two]; exact mul_le_mul_of_nonneg_left hΩU hUpos.le
    have hfactor : P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) = P.G * P.U ^ 5 * S.Ω ^ 3 := by
      field_simp
    have hU2Ωpos : (0 : ℝ) ≤ P.U ^ 2 / S.Ω := by positivity
    have hchain : (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) := by
      calc (1 : ℝ) ≤ P.U := hU1
        _ ≤ P.U ^ 2 / S.Ω := hU2Ω
        _ = 1 * (P.U ^ 2 / S.Ω) := by ring
        _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) :=
            mul_le_mul_of_nonneg_right hband hU2Ωpos
    rwa [hfactor] at hchain
  have hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 := by
    -- H ≥ G U^10 Δ²
    have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
      (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
    -- Δ²U⁵ ≤ Δ²U¹⁰ = (GU¹⁰Δ²)·(1/G)·... use: Δ²U⁵·(GU⁵Ω³) ≤ GU¹⁰Δ²·Ω³ ≤ HΩ³
    have hstep : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3)
        ≤ P.H * S.Ω ^ 3 := by
      have heq : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3)
          = (P.G * P.U ^ 10 * S.Δ ^ 2) * S.Ω ^ 3 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hHbig (by positivity)
    -- Δ²U⁵ ≤ Δ²U⁵·(GU⁵Ω³)  since GU⁵Ω³ ≥ 1
    have hle : S.Δ ^ 2 * P.U ^ 5 ≤ S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3) :=
      le_mul_of_one_le_right (by positivity) hGU5Ω3
    linarith [hle, hstep]
  -- B and A in terms of Δ,Ω,G
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hAval : S.A = S.Δ * S.Ω := rfl
  -- explicit per-variable upper bounds
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by rw [hBval] at hb0; exact hb0
  have ha' : a ≤ 11 * (S.Δ * S.Ω) := by rw [hAval] at ha_hi; exact ha_hi
  -- abbreviation V := 10^20·ΔU⁵/Ω³  (upper for |v|)
  set Vu : ℝ := 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) with hVu_def
  have hVu_nn : 0 ≤ Vu := by rw [hVu_def]; positivity
  have hv' : |v| ≤ Vu := hv
  -- abbreviation Bu := 3·10¹²·Δ²/(GΩ³), Wu := G·U⁵
  set Bu : ℝ := 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) with hBu_def
  have hBu_nn : 0 ≤ Bu := by rw [hBu_def]; positivity
  set Wu : ℝ := 130 * (P.G * P.U ^ 5) with hWu_def
  have hWu_nn : 0 ≤ Wu := by rw [hWu_def]; positivity
  have hb0'' : |b₀| ≤ Bu := hb0'
  -- ============= bound |Pone| =============
  -- |Pone| ≤ 3 ℓ₁³ ℓ₂ (ℓ₂-ℓ₁) |b₀| |v|² + ℓ₁³ (2ℓ₂-ℓ₁) |v|³
  have hP1abs : |Pone b₀ v ℓ₁ ℓ₂|
      ≤ 3 * Wu ^ 3 * Wu * Wu * Bu * Vu ^ 2 + Wu ^ 3 * (2 * Wu) * Vu ^ 3 := by
    rw [Pone]
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · -- |3ℓ₁³ℓ₂(ℓ₂-ℓ₁)b₀v²| = 3ℓ₁³ℓ₂(ℓ₂-ℓ₁)·|b₀|·|v|²
      have hcoefnn : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) := by
        have : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
        positivity
      have heq : |3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2|
          = 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * |v| ^ 2 := by
        rw [show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
              = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) * b₀ * v ^ 2 by ring, abs_mul, abs_mul,
            abs_of_nonneg hcoefnn, abs_pow]
      rw [heq]
      have hcoef : 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) ≤ 3 * Wu ^ 3 * Wu * Wu := by
        have e1 : ℓ₁ ^ 3 ≤ Wu ^ 3 := by
          apply pow_le_pow_left₀ hℓ1nn; rw [hWu_def]; exact hℓ1W'
        have e2 : ℓ₂ ≤ Wu := by rw [hWu_def]; exact hℓ2W'
        have e3 : ℓ₂ - ℓ₁ ≤ Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
        have e3nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
        have s1 : 3 * ℓ₁ ^ 3 ≤ 3 * Wu ^ 3 := by linarith [e1]
        have s2 : 3 * ℓ₁ ^ 3 * ℓ₂ ≤ 3 * Wu ^ 3 * Wu :=
          mul_le_mul s1 e2 hℓ2nn (by positivity)
        calc 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) ≤ (3 * Wu ^ 3 * Wu) * Wu :=
              mul_le_mul s2 e3 e3nn (by positivity)
          _ = 3 * Wu ^ 3 * Wu * Wu := by ring
      calc 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * |v| ^ 2
          ≤ (3 * Wu ^ 3 * Wu * Wu) * Bu * Vu ^ 2 := by
            apply mul_le_mul (mul_le_mul hcoef hb0'' hb0nn (by positivity))
              (pow_le_pow_left₀ hvnn hv' 2) (by positivity) (by positivity)
        _ = 3 * Wu ^ 3 * Wu * Wu * Bu * Vu ^ 2 := by ring
    · -- |ℓ₁³(2ℓ₂-ℓ₁)v³| = ℓ₁³(2ℓ₂-ℓ₁)·|v|³
      have hcoefnn : (0:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := by
        have : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [hℓ12.le, hℓ1nn]
        positivity
      have heq : |ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3| = ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 3 := by
        rw [show ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 = (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 3 by ring,
          abs_mul, abs_of_nonneg hcoefnn, abs_pow]
      rw [heq]
      have hcoef : ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) ≤ Wu ^ 3 * (2 * Wu) := by
        have e1 : ℓ₁ ^ 3 ≤ Wu ^ 3 := by
          apply pow_le_pow_left₀ hℓ1nn; rw [hWu_def]; exact hℓ1W'
        have e2 : 2 * ℓ₂ - ℓ₁ ≤ 2 * Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
        have e2nn : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [hℓ12.le, hℓ1nn]
        exact mul_le_mul e1 e2 e2nn (by positivity)
      calc ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 3
          ≤ (Wu ^ 3 * (2 * Wu)) * Vu ^ 3 := by
            apply mul_le_mul hcoef (pow_le_pow_left₀ hvnn hv' 3) (by positivity) (by positivity)
        _ = Wu ^ 3 * (2 * Wu) * Vu ^ 3 := by ring
  -- shorthand for nonneg of (ℓ₂-ℓ₁), (3ℓ₂-2ℓ₁), (2ℓ₂-ℓ₁)
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h32nn : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith [hℓ12.le]
  have h2ℓ1nn : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [hℓ12.le, hℓ1nn]
  have hℓ13nn : (0:ℝ) ≤ ℓ₁ ^ 3 := by positivity
  have hWu3 : ℓ₁ ^ 3 ≤ Wu ^ 3 := by
    apply pow_le_pow_left₀ hℓ1nn; rw [hWu_def]; exact hℓ1W'
  have hℓ2Wu : ℓ₂ ≤ Wu := by rw [hWu_def]; exact hℓ2W'
  have h21Wu : ℓ₂ - ℓ₁ ≤ Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
  -- ============= bound |Ptwo| =============
  have hP2abs : |Ptwo b₀ v ℓ₁ ℓ₂|
      ≤ 5 * Wu ^ 7 * Bu ^ 3 * Vu + 15 * Wu ^ 6 * Bu ^ 2 * Vu ^ 2
        + 15 * Wu ^ 5 * Bu * Vu ^ 3 + 5 * Wu ^ 4 * Vu ^ 4 := by
    rw [Ptwo]
    -- expand the four-term abs via triangle inequality
    set q1 : ℝ := (-5)*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)^2*b₀^3*v with hq1
    set q2 : ℝ := (-(15*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)*b₀^2*v^2)) with hq2
    set q3 : ℝ := (-(5*ℓ₁^3*ℓ₂*(3*ℓ₂-2*ℓ₁)*b₀*v^3)) with hq3
    set q4 : ℝ := (-((5/2)*ℓ₁^3*(2*ℓ₂-ℓ₁)*v^4)) with hq4
    have hbody : -5*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)^2*b₀^3*v - 15*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)*b₀^2*v^2
        - 5*ℓ₁^3*ℓ₂*(3*ℓ₂-2*ℓ₁)*b₀*v^3 - (5/2)*ℓ₁^3*(2*ℓ₂-ℓ₁)*v^4
        = q1 + q2 + q3 + q4 := by rw [hq1, hq2, hq3, hq4]; ring
    rw [hbody]
    have htri : |q1 + q2 + q3 + q4| ≤ |q1| + |q2| + |q3| + |q4| := by
      calc |q1 + q2 + q3 + q4| ≤ |q1 + q2 + q3| + |q4| := abs_add_le _ _
        _ ≤ (|q1 + q2| + |q3|) + |q4| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|q1| + |q2|) + |q3|) + |q4| := by gcongr; exact abs_add_le _ _
        _ = |q1| + |q2| + |q3| + |q4| := by ring
    refine le_trans htri ?_
    -- now bound each abs term
    have t1 : |q1| ≤ 5 * Wu ^ 7 * Bu ^ 3 * Vu := by
      have hcnn : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
      have heq : |q1| = 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * |b₀| ^ 3 * |v| := by
        rw [hq1, show (-5) * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v
              = (-(5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)) * b₀ ^ 3 * v by ring,
            abs_mul, abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow]
      rw [heq]
      have hcoef : 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ 5 * Wu ^ 7 := by
        have a2 : ℓ₂ ^ 2 ≤ Wu ^ 2 := pow_le_pow_left₀ hℓ2nn hℓ2Wu 2
        have a3 : (ℓ₂ - ℓ₁) ^ 2 ≤ Wu ^ 2 := pow_le_pow_left₀ h21nn h21Wu 2
        calc 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
            = 5 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) := by ring
          _ ≤ 5 * (Wu ^ 3 * Wu ^ 2 * Wu ^ 2) := by gcongr
          _ = 5 * Wu ^ 7 := by ring
      calc 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * |b₀| ^ 3 * |v|
          ≤ (5 * Wu ^ 7) * Bu ^ 3 * Vu := by
            apply mul_le_mul (mul_le_mul hcoef (pow_le_pow_left₀ hb0nn hb0'' 3) (by positivity)
              (by positivity)) hv' hvnn (by positivity)
        _ = 5 * Wu ^ 7 * Bu ^ 3 * Vu := by ring
    have t2 : |q2| ≤ 15 * Wu ^ 6 * Bu ^ 2 * Vu ^ 2 := by
      have hcnn : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) := by positivity
      have heq : |q2| = 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * |b₀| ^ 2 * |v| ^ 2 := by
        rw [hq2, show -(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2)
              = (-(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))) * b₀ ^ 2 * v ^ 2 by ring,
            abs_mul, abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow, abs_pow]
      rw [heq]
      have hcoef : 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ≤ 15 * Wu ^ 6 := by
        have a2 : ℓ₂ ^ 2 ≤ Wu ^ 2 := pow_le_pow_left₀ hℓ2nn hℓ2Wu 2
        calc 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)
            = 15 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) := by ring
          _ ≤ 15 * (Wu ^ 3 * Wu ^ 2 * Wu) := by gcongr
          _ = 15 * Wu ^ 6 := by ring
      calc 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * |b₀| ^ 2 * |v| ^ 2
          ≤ (15 * Wu ^ 6) * Bu ^ 2 * Vu ^ 2 := by
            apply mul_le_mul (mul_le_mul hcoef (pow_le_pow_left₀ hb0nn hb0'' 2) (by positivity)
              (by positivity)) (pow_le_pow_left₀ hvnn hv' 2) (by positivity) (by positivity)
        _ = 15 * Wu ^ 6 * Bu ^ 2 * Vu ^ 2 := by ring
    have t3 : |q3| ≤ 15 * Wu ^ 5 * Bu * Vu ^ 3 := by
      have hcnn : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) := by positivity
      have heq : |q3| = 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * |b₀| * |v| ^ 3 := by
        rw [hq3, show -(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3)
              = (-(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))) * b₀ * v ^ 3 by ring,
            abs_mul, abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow]
      rw [heq]
      have hcoef : 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) ≤ 15 * Wu ^ 5 := by
        have a3 : 3 * ℓ₂ - 2 * ℓ₁ ≤ 3 * Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
        calc 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)
            = 5 * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) := by ring
          _ ≤ 5 * (Wu ^ 3 * Wu * (3 * Wu)) := by gcongr
          _ = 15 * Wu ^ 5 := by ring
      calc 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * |b₀| * |v| ^ 3
          ≤ (15 * Wu ^ 5) * Bu * Vu ^ 3 := by
            apply mul_le_mul (mul_le_mul hcoef hb0'' hb0nn (by positivity))
              (pow_le_pow_left₀ hvnn hv' 3) (by positivity) (by positivity)
        _ = 15 * Wu ^ 5 * Bu * Vu ^ 3 := by ring
    have t4 : |q4| ≤ 5 * Wu ^ 4 * Vu ^ 4 := by
      have hcnn : (0:ℝ) ≤ (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := by positivity
      have heq : |q4| = (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 4 := by
        rw [hq4, show -((5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4)
              = (-((5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * v ^ 4 by ring,
            abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow]
      rw [heq]
      have hcoef : (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) ≤ 5 * Wu ^ 4 := by
        have a2 : 2 * ℓ₂ - ℓ₁ ≤ 2 * Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
        calc (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)
            = (5/2) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) := by ring
          _ ≤ (5/2) * (Wu ^ 3 * (2 * Wu)) := by gcongr
          _ = 5 * Wu ^ 4 := by ring
      calc (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 4
          ≤ (5 * Wu ^ 4) * Vu ^ 4 := by
            apply mul_le_mul hcoef (pow_le_pow_left₀ hvnn hv' 4) (by positivity) (by positivity)
        _ = 5 * Wu ^ 4 * Vu ^ 4 := by ring
    linarith [t1, t2, t3, t4]
  -- ============= assemble |Lval| =============
  -- prefactor bound: X a / d⁵ ≤ 11·G·Ω/Δ⁴
  have hXval : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
  have hpre_pos : 0 < P.X * a / d ^ 5 := by positivity
  have hpre : P.X * a / d ^ 5 ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- X·a·Δ⁴ ≤ 12GΩ·d⁵, with d ≥ D(1−ε) = HΔ(1−ε)
    have hd5 : (P.H * S.Δ) ^ 5 * (1 - 1/10 ^ 9) ^ 5 ≤ d ^ 5 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
        (by rw [show P.H * S.Δ * (1 - 1/10 ^ 9) = S.D * (1 - 1/10 ^ 9) by rfl]; exact hdD)
    have haub : a ≤ 11 * (S.Δ * S.Ω) := ha'
    have h1112 : (11:ℝ) ≤ 12 * (1 - 1/10 ^ 9) ^ 5 := by norm_num
    calc P.X * a * S.Δ ^ 4
        ≤ P.X * (11 * (S.Δ * S.Ω)) * S.Δ ^ 4 := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haub (by positivity))
            (by positivity)
      _ = 11 * P.G * S.Ω * (P.H * S.Δ) ^ 5 := by rw [hXval]; ring
      _ ≤ 12 * P.G * S.Ω * ((P.H * S.Δ) ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by
          have hKnn : (0:ℝ) ≤ P.G * S.Ω * (P.H * S.Δ) ^ 5 := by positivity
          calc 11 * P.G * S.Ω * (P.H * S.Δ) ^ 5
              = 11 * (P.G * S.Ω * (P.H * S.Δ) ^ 5) := by ring
            _ ≤ (12 * (1 - 1/10 ^ 9) ^ 5) * (P.G * S.Ω * (P.H * S.Δ) ^ 5) :=
                mul_le_mul_of_nonneg_right h1112 hKnn
            _ = 12 * P.G * S.Ω * ((P.H * S.Δ) ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by ring
      _ ≤ 12 * P.G * S.Ω * d ^ 5 := by
          apply mul_le_mul_of_nonneg_left hd5 (by positivity)
  have hpre_ub_nn : (0:ℝ) ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by positivity
  -- |−4 + 10a/d| ≤ 7  (via the H ≥ 1000Ω route, robust to the ε-window)
  have hbracket : |(-4 + 10 * a / d)| ≤ 7 := by
    have hHbig2 : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
      (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
    have hU10H : P.U ^ 10 ≤ P.H := by
      have h1' : (1:ℝ) ≤ P.G * S.Δ ^ 2 := by
        have hΔ2 : (1:ℝ) ≤ S.Δ ^ 2 := one_le_pow₀ hΔ1
        calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ P.G * S.Δ ^ 2 := mul_le_mul hG1 hΔ2 zero_le_one hGpos.le
      calc P.U ^ 10 = P.U ^ 10 * 1 := (mul_one _).symm
        _ ≤ P.U ^ 10 * (P.G * S.Δ ^ 2) := mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
        _ ≤ P.H := hHbig2
    have hHΩ : 1000 * S.Ω ≤ P.H := by
      have hU9 : (1000:ℝ) ≤ P.U ^ 9 := by
        calc (1000:ℝ) ≤ (10:ℝ) ^ 33 := by norm_num
          _ ≤ P.U := hUbig
          _ = P.U ^ 1 := by ring
          _ ≤ P.U ^ 9 := pow_le_pow_right₀ (le_trans (by norm_num) hUbig) (by norm_num)
      calc 1000 * S.Ω ≤ P.U ^ 9 * P.U := mul_le_mul hU9 hΩU hΩpos.le (by positivity)
        _ = P.U ^ 10 := by ring
        _ ≤ P.H := hU10H
    have hd_ge : P.H * S.Δ * (1 - 1/10 ^ 9) ≤ d := by
      rw [show P.H * S.Δ * (1 - 1/10 ^ 9) = S.D * (1 - 1/10 ^ 9) by rfl]; exact hdD
    have had2 : 10 * a / d ≤ 11 := by
      rw [div_le_iff₀ hd_pos]
      linarith [ha', hd_ge, mul_le_mul_of_nonneg_right hHΩ hΔpos.le,
        mul_nonneg hHpos.le hΔpos.le]
    have had0 : 0 ≤ 10 * a / d := by positivity
    rw [abs_le]
    constructor <;> [linarith [had0]; linarith [had2]]
  -- Z1, Z2 abbreviations
  set Z1 : ℝ := 3 * Wu ^ 3 * Wu * Wu * Bu * Vu ^ 2 + Wu ^ 3 * (2 * Wu) * Vu ^ 3 with hZ1
  set Z2 : ℝ := 5 * Wu ^ 7 * Bu ^ 3 * Vu + 15 * Wu ^ 6 * Bu ^ 2 * Vu ^ 2
      + 15 * Wu ^ 5 * Bu * Vu ^ 3 + 5 * Wu ^ 4 * Vu ^ 4 with hZ2
  have hZ1_nn : 0 ≤ Z1 := by rw [hZ1]; positivity
  have hZ2_nn : 0 ≤ Z2 := by rw [hZ2]; positivity
  -- |P1 + P2/d| ≤ Z1 + Z2/d
  have hPsum : |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| ≤ Z1 + Z2 / d := by
    refine le_trans (abs_add_le _ _) ?_
    have h2 : |Ptwo b₀ v ℓ₁ ℓ₂ / d| ≤ Z2 / d := by
      rw [abs_div, abs_of_pos hd_pos]
      gcongr
    linarith [hP1abs, h2]
  have hPsum_nn : 0 ≤ Z1 + Z2 / d := by positivity
  -- |Lval| ≤ (X a/d⁵)·7·(Z1 + Z2/d)
  have hLval_eq : |Lval P.X a d b₀ v ℓ₁ ℓ₂|
      = (P.X * a / d ^ 5) * (|(-4 + 10 * a / d)| * |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d|) := by
    rw [Lval, abs_mul, abs_mul, abs_of_pos hpre_pos]
  rw [hLval_eq]
  have hstep1 : (P.X * a / d ^ 5)
        * (|(-4 + 10 * a / d)| * |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d|)
      ≤ (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * (Z1 + Z2 / d)) := by
    apply mul_le_mul hpre ?_ (by positivity) hpre_ub_nn
    apply mul_le_mul hbracket hPsum (by positivity) (by norm_num)
  refine le_trans hstep1 ?_
  -- now: (12GΩ/Δ⁴)·7·(Z1 + Z2/d) ≤ 10^85·G⁵U³⁵/Ω⁸
  rw [mul_add]
  -- Z1-piece: (12GΩ/Δ⁴)·7·Z1 = G⁵U³⁵·(c₁Δ + c₀)/(ΔΩ⁸) ≤ (10⁸⁵/2)·G⁵U³⁵/Ω⁸
  have hZ1piece : (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * Z1)
      ≤ (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by
    have heqv : (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * Z1)
        = (P.G ^ 5 * P.U ^ 35)
            * (280697508000000000000000000000000000000000000000000000000000000000 * S.Δ
              + 47982480000000000000000000000000000000000000000000000000000000000000000)
            / (S.Δ * S.Ω ^ 8) := by
      rw [hZ1, hWu_def, hBu_def, hVu_def]; field_simp; ring
    rw [heqv, div_le_iff₀ (by positivity : (0:ℝ) < S.Δ * S.Ω ^ 8)]
    -- RHS simplifies: (10⁸⁵/2)·(G⁵U³⁵/Ω⁸)·(Δ Ω⁸) = (10⁸⁵/2)·G⁵U³⁵·Δ
    have hRHSeq : (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) * (S.Δ * S.Ω ^ 8)
        = (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 * S.Δ) := by field_simp
    rw [hRHSeq]
    -- LHS = G⁵U³⁵·(c₁Δ+c₀) ≤ (10⁸⁵/2)·G⁵U³⁵·Δ  ⟸ (c₁Δ+c₀) ≤ (10⁸⁵/2)·Δ
    have hkey : (280697508000000000000000000000000000000000000000000000000000000000 * S.Δ
          + 47982480000000000000000000000000000000000000000000000000000000000000000)
        ≤ (10:ℝ) ^ 94 / 2 * S.Δ := by linarith [hΔ1]
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ P.G ^ 5 * P.U ^ 35)
    calc (P.G ^ 5 * P.U ^ 35)
          * (280697508000000000000000000000000000000000000000000000000000000000 * S.Δ
            + 47982480000000000000000000000000000000000000000000000000000000000000000)
        ≤ (P.G ^ 5 * P.U ^ 35) * ((10:ℝ) ^ 94 / 2 * S.Δ) := this
      _ = (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 * S.Δ) := by ring
  -- Z2-piece: (12GΩ/Δ⁴)·7·(9/8·Z2/D) ≤ (10⁸⁵/2)·G⁵U³⁵/Ω⁸
  have hZ2piece : (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * (Z2 / d))
      ≤ (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by
    -- step through d ≥ D(1−ε) : Z2/d ≤ (9/8)·Z2/D
    have hZ2d : Z2 / d ≤ 9 / 8 * (Z2 / S.D) := by
      have hD'pos : (0:ℝ) < S.D * (1 - 1/10 ^ 9) := mul_pos hDpos (by norm_num)
      have h1' : Z2 / d ≤ Z2 / (S.D * (1 - 1/10 ^ 9)) := by gcongr
      refine h1'.trans ?_
      rw [div_le_iff₀ hD'pos]
      have heq9 : 9 / 8 * (Z2 / S.D) * (S.D * (1 - 1/10 ^ 9))
          = 9 / 8 * (1 - 1/10 ^ 9) * Z2 := by field_simp
      rw [heq9]
      linarith [hZ2_nn]
    have hmul : (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * (Z2 / d))
        ≤ (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * (9 / 8 * (Z2 / S.D))) := by
      apply mul_le_mul_of_nonneg_left _ hpre_ub_nn
      linarith [hZ2d]
    refine le_trans hmul ?_
    -- exact value: G⁵U⁴⁰·(quartic in Δ)/(H·Δ³·Ω¹¹)
    have hSD : S.D = P.H * S.Δ := rfl
    have heqv : (12 * P.G * S.Ω / S.Δ ^ 4) * (7 * (9 / 8 * (Z2 / S.D)))
        = (P.G ^ 5 * P.U ^ 40)
            * (800514205627500000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 6
              + 615780158175000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 5
              + 157892348250000000000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 4
              + 13495072500000000000000000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 3)
            / (P.H * S.Δ ^ 4 * S.Ω ^ 11) := by
      rw [hZ2, hWu_def, hBu_def, hVu_def, hSD]; field_simp; ring
    rw [heqv, div_le_iff₀ (by positivity : (0:ℝ) < P.H * S.Δ ^ 4 * S.Ω ^ 11)]
    -- reduces to: G⁵U⁴⁰·(poly) ≤ (10⁸⁵/2)·(G⁵U³⁵/Ω⁸) · (H Δ⁴ Ω¹¹)
    -- poly ≤ C·Δ⁶ (Δ³,Δ⁴,Δ⁵ ≤ Δ⁶), and U⁵Δ⁶ = Δ⁴·(Δ²U⁵) ≤ Δ⁴·HΩ³
    have hΔ36 : S.Δ ^ 3 ≤ S.Δ ^ 6 := pow_le_pow_right₀ hΔ1 (by norm_num)
    have hΔ46 : S.Δ ^ 4 ≤ S.Δ ^ 6 := pow_le_pow_right₀ hΔ1 (by norm_num)
    have hΔ56 : S.Δ ^ 5 ≤ S.Δ ^ 6 := pow_le_pow_right₀ hΔ1 (by norm_num)
    have hΔ6nn : (0:ℝ) ≤ S.Δ ^ 6 := by positivity
    -- poly ≤ C·Δ⁶ with C = sum of constants ≤ 10⁸¹
    have hpoly : (800514205627500000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 6
          + 615780158175000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 5
          + 157892348250000000000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 4
          + 13495072500000000000000000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 3)
        ≤ (10:ℝ) ^ 92 * S.Δ ^ 6 := by
      have c1 : (800514205627500000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 6
          ≤ (800514205627500000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 6 := le_refl _
      have c2 : (615780158175000000000000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 5
          ≤ (615780158175000000000000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 6 :=
        mul_le_mul_of_nonneg_left hΔ56 (by norm_num)
      have c3 : (157892348250000000000000000000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 4
          ≤ (157892348250000000000000000000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 6 :=
        mul_le_mul_of_nonneg_left hΔ46 (by norm_num)
      have c4 : (13495072500000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 3
          ≤ (13495072500000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℝ) * S.Δ ^ 6 :=
        mul_le_mul_of_nonneg_left hΔ36 (by norm_num)
      have hconst : (800514205627500000000000000000000000000000000000000000000000000000000000000:ℝ)
          + 615780158175000000000000000000000000000000000000000000000000000000000000000000000
          + 157892348250000000000000000000000000000000000000000000000000000000000000000000000000000
          + 13495072500000000000000000000000000000000000000000000000000000000000000000000000000000000000
          ≤ (10:ℝ) ^ 92 := by norm_num
      have hcsum := mul_le_mul_of_nonneg_right hconst hΔ6nn
      linarith [c2, c3, c4, hcsum]
    -- U⁵·Δ⁶ ≤ Δ⁴·HΩ³   (from Δ²U⁵ ≤ HΩ³, multiply by Δ⁴)
    have hUΔ : P.U ^ 5 * S.Δ ^ 6 ≤ S.Δ ^ 4 * (P.H * S.Ω ^ 3) := by
      have hmul := mul_le_mul_of_nonneg_left hReg (by positivity : (0:ℝ) ≤ S.Δ ^ 4)
      have hl : S.Δ ^ 4 * (S.Δ ^ 2 * P.U ^ 5) = P.U ^ 5 * S.Δ ^ 6 := by ring
      rw [hl] at hmul
      exact hmul
    -- combine: G⁵U⁴⁰·poly ≤ G⁵U⁴⁰·10⁸¹Δ⁶ = 10⁸¹·G⁵U³⁵·(U⁵Δ⁶) ≤ 10⁸¹·G⁵U³⁵·Δ⁴HΩ³
    --   and RHS = (10⁸⁵/2)·G⁵U³⁵·HΔ⁴Ω³  (Ω¹¹/Ω⁸ = Ω³); 10⁸¹ ≤ 10⁸⁵/2
    have hG5U40 : P.G ^ 5 * P.U ^ 40 = P.G ^ 5 * P.U ^ 35 * P.U ^ 5 := by ring
    have hstep : (P.G ^ 5 * P.U ^ 40)
          * (800514205627500000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 6
            + 615780158175000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 5
            + 157892348250000000000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 4
            + 13495072500000000000000000000000000000000000000000000000000000000000000000000000000000000000 * S.Δ ^ 3)
        ≤ (P.G ^ 5 * P.U ^ 35) * ((10:ℝ) ^ 92 * (P.U ^ 5 * S.Δ ^ 6)) := by
      rw [hG5U40]
      have h1 := mul_le_mul_of_nonneg_left hpoly
        (by positivity : (0:ℝ) ≤ P.G ^ 5 * P.U ^ 35 * P.U ^ 5)
      refine le_trans h1 (le_of_eq ?_)
      ring
    refine le_trans hstep ?_
    have h2 : (P.G ^ 5 * P.U ^ 35) * ((10:ℝ) ^ 92 * (P.U ^ 5 * S.Δ ^ 6))
        ≤ (P.G ^ 5 * P.U ^ 35) * ((10:ℝ) ^ 92 * (S.Δ ^ 4 * (P.H * S.Ω ^ 3))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left hUΔ (by positivity)
    refine le_trans h2 ?_
    -- RHS = (10⁸⁵/2)·G⁵U³⁵·H·Δ⁴·Ω³ ; LHS = 10⁸¹·G⁵U³⁵·H·Δ⁴·Ω³ ; 10⁸¹ ≤ 10⁸⁵/2
    have hRHSeq : (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) * (P.H * S.Δ ^ 4 * S.Ω ^ 11)
        = (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 * (S.Δ ^ 4 * (P.H * S.Ω ^ 3))) := by
      field_simp
    rw [hRHSeq]
    have hmono_nn : (0:ℝ) ≤ P.G ^ 5 * P.U ^ 35 * (S.Δ ^ 4 * (P.H * S.Ω ^ 3)) := by positivity
    calc (P.G ^ 5 * P.U ^ 35) * ((10:ℝ) ^ 92 * (S.Δ ^ 4 * (P.H * S.Ω ^ 3)))
        = (10:ℝ) ^ 92 * (P.G ^ 5 * P.U ^ 35 * (S.Δ ^ 4 * (P.H * S.Ω ^ 3))) := by ring
      _ ≤ (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 * (S.Δ ^ 4 * (P.H * S.Ω ^ 3))) := by
          apply mul_le_mul_of_nonneg_right _ hmono_nn; norm_num
  -- combine
  have hsplit : (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
      + (10:ℝ) ^ 94 / 2 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
      = (10:ℝ) ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by ring
  linarith [hZ1piece, hZ2piece, hsplit]

/-- The §5 Step-4 leading-term scale chain: under the regime facts `hReg : Δ²U⁵ ≤ HΩ³`,
`hDeW : 10¹⁵·G⁴U²⁰ ≤ Δ`, `hUbig : 10³³ ≤ U`, and the threshold `hv2 : V₂ ≤ |v|`, the cubed
threshold `GΩ·|v|³/(320Δ⁴)` dominates `1 + 10¹¹⁰·UpsT`.  Factored out so the heartbeat-heavy
constant arithmetic gets its own budget. -/
private theorem leading_scale_chain {v : ℝ}
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v|) :
    1 + 10 ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
      ≤ P.G * S.Ω * |v| ^ 3 / (320 * S.Δ ^ 4) := by
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hHpos : 0 < P.H := P.H_pos
  -- |v|³ ≥ V₂³
  have hV2nn : (0:ℝ) ≤ 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) := by positivity
  have hv3ge : (2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3)) ^ 3 ≤ |v| ^ 3 :=
    pow_le_pow_left₀ hV2nn hv2 3
  have hstep : P.G * S.Ω * (2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3)) ^ 3 / (320 * S.Δ ^ 4)
      ≤ P.G * S.Ω * |v| ^ 3 / (320 * S.Δ ^ 4) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hv3ge (by positivity)
  refine le_trans ?_ hstep
  have hLHSval : P.G * S.Ω * (2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3)) ^ 3 / (320 * S.Δ ^ 4)
      = (40040325 * 10 ^ 36) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8) := by
    field_simp
    ring
  rw [hLHSval]
  have hHsq : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 := hReg
  have hUpsT : 10 ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
      ≤ (40040325 * 10 ^ 36 / 2) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8) := by
    rw [mul_div_assoc', mul_div_assoc',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hH2 : S.Δ ^ 4 * P.U ^ 10 ≤ P.H ^ 2 * S.Ω ^ 6 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * P.U ^ 5) hHsq 2
      calc S.Δ ^ 4 * P.U ^ 10 = (S.Δ ^ 2 * P.U ^ 5) ^ 2 := by ring
        _ ≤ (P.H * S.Ω ^ 3) ^ 2 := h
        _ = P.H ^ 2 * S.Ω ^ 6 := by ring
    have hΔ2 : (10:ℝ) ^ 30 * (P.G ^ 8 * P.U ^ 40) ≤ S.Δ ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) hDeW 2
      have hge : (10:ℝ) ^ 30 * (P.G ^ 8 * P.U ^ 40)
          ≤ (10 ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 := by
        have he : ((10:ℝ) ^ 27 * (P.G ^ 4 * P.U ^ 20)) ^ 2 = 10 ^ 54 * (P.G ^ 8 * P.U ^ 40) := by
          ring
        rw [he]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith [hge, h]
    -- literal-safe:  10¹¹⁰ ≤ U²⁰  (from U ≥ 10³³, keeping 10⁶⁶⁰ as a symbolic power)
    have hU110 : (10:ℝ) ^ 119 ≤ P.U ^ 20 := by
      have h1 : (10:ℝ) ^ 119 ≤ (10:ℝ) ^ 660 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      have h2 : ((10:ℝ) ^ 33) ^ 20 = (10:ℝ) ^ 660 := by rw [← pow_mul]
      have h3 : ((10:ℝ) ^ 33) ^ 20 ≤ P.U ^ 20 := pow_le_pow_left₀ (by positivity) hUbig 20
      calc (10:ℝ) ^ 119 ≤ (10:ℝ) ^ 660 := h1
        _ = ((10:ℝ) ^ 33) ^ 20 := h2.symm
        _ ≤ P.U ^ 20 := h3
    have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
    -- KEY:  10¹¹⁰·G⁴U²⁰ ≤ (c/2)·Δ².  Use Δ² ≥ 10³⁰(G⁴U²⁰)² and 10¹¹⁰ ≤ U²⁰ ≤ G⁴U²⁰.
    have hKey : (10:ℝ) ^ 119 * (P.G ^ 4 * P.U ^ 20) ≤ (40040325 * 10 ^ 36 / 2) * S.Δ ^ 2 := by
      have hA : (40040325 * 10 ^ 36 / 2 : ℝ) * (10 ^ 30 * (P.G ^ 8 * P.U ^ 40))
          ≤ (40040325 * 10 ^ 36 / 2) * S.Δ ^ 2 :=
        mul_le_mul_of_nonneg_left hΔ2 (by norm_num)
      refine le_trans ?_ hA
      -- 10¹¹⁰·G⁴U²⁰ ≤ (c/2)·10³⁰·G⁸U⁴⁰ ;  c/2·10³⁰ ≥ 1 and G⁴U²⁰ ≥ U²⁰ ≥ 10¹¹⁰.
      have hGU : (10:ℝ) ^ 119 ≤ P.G ^ 4 * P.U ^ 20 := by
        calc (10:ℝ) ^ 119 ≤ P.U ^ 20 := hU110
          _ = 1 * P.U ^ 20 := by ring
          _ ≤ P.G ^ 4 * P.U ^ 20 := mul_le_mul_of_nonneg_right hG4 (by positivity)
      have hc2 : (1:ℝ) ≤ (40040325 * 10 ^ 36 / 2) * 10 ^ 30 := by norm_num
      -- (c/2)·10³⁰·G⁸U⁴⁰ ≥ ((c/2)·10³⁰)·(G⁴U²⁰)·(10¹¹⁰) ≥ (10¹¹⁰)·(G⁴U²⁰)
      set W : ℝ := P.G ^ 4 * P.U ^ 20 with hWdef
      have hWnn : (0:ℝ) ≤ W := by rw [hWdef]; positivity
      have hfac : (40040325 * 10 ^ 36 / 2 : ℝ) * (10 ^ 30 * (P.G ^ 8 * P.U ^ 40))
          = (((40040325 * 10 ^ 36 / 2) * 10 ^ 30) * W) * W := by rw [hWdef]; ring
      rw [hfac]
      have hstep1 : (10:ℝ) ^ 119 * W ≤ W * W := mul_le_mul_of_nonneg_right hGU hWnn
      have hstep2 : W * W ≤ (((40040325 * 10 ^ 36 / 2) * 10 ^ 30) * W) * W := by
        apply mul_le_mul_of_nonneg_right _ hWnn
        calc W = 1 * W := by ring
          _ ≤ ((40040325 * 10 ^ 36 / 2) * 10 ^ 30) * W :=
              mul_le_mul_of_nonneg_right hc2 hWnn
      linarith [hstep1, hstep2]
    -- multiply hKey by Δ⁴·G·U²⁵·Ω⁸ (≥0) ; reach goal LHS, then trade Δ⁴U¹⁰ ≤ H²Ω⁶ via hH2.
    have hMul1 : (10:ℝ) ^ 119 * (P.G ^ 4 * P.U ^ 20) * (S.Δ ^ 4 * (P.G * P.U ^ 25 * S.Ω ^ 8))
        ≤ (40040325 * 10 ^ 36 / 2) * S.Δ ^ 2 * (S.Δ ^ 4 * (P.G * P.U ^ 25 * S.Ω ^ 8)) :=
      mul_le_mul_of_nonneg_right hKey (by positivity)
    have hL : (10:ℝ) ^ 119 * (P.G ^ 4 * P.U ^ 20) * (S.Δ ^ 4 * (P.G * P.U ^ 25 * S.Ω ^ 8))
        = 10 ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) * S.Ω ^ 8 := by ring
    rw [hL] at hMul1
    refine le_trans hMul1 ?_
    have hRfac : (40040325 * 10 ^ 36 / 2 : ℝ) * S.Δ ^ 2 * (S.Δ ^ 4 * (P.G * P.U ^ 25 * S.Ω ^ 8))
        = (40040325 * 10 ^ 36 / 2) * (P.G * P.U ^ 15 * S.Ω ^ 8) * (S.Δ ^ 4 * P.U ^ 10) * S.Δ ^ 2 := by
      ring
    rw [hRfac]
    have hTrade : (40040325 * 10 ^ 36 / 2 : ℝ) * (P.G * P.U ^ 15 * S.Ω ^ 8) * (S.Δ ^ 4 * P.U ^ 10) * S.Δ ^ 2
        ≤ (40040325 * 10 ^ 36 / 2) * (P.G * P.U ^ 15 * S.Ω ^ 8) * (P.H ^ 2 * S.Ω ^ 6) * S.Δ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left hH2 (by positivity)
    refine le_trans hTrade ?_
    apply le_of_eq; ring
  have hOne : (1:ℝ) ≤ (40040325 * 10 ^ 36 / 2) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    -- goal: 1·Ω⁸ ≤ (c/2)·(GΔ²U¹⁵).  Ω⁸ ≤ U⁸ ≤ U¹⁵ ≤ GΔ²U¹⁵ ≤ (c/2)·GΔ²U¹⁵.
    have hΩ8 : S.Ω ^ 8 ≤ P.U ^ 8 := pow_le_pow_left₀ hΩpos.le hΩU 8
    have hU815 : P.U ^ 8 ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
    have hGΔ : P.U ^ 15 ≤ P.G * S.Δ ^ 2 * P.U ^ 15 := by
      have h1 : (1:ℝ) ≤ P.G * S.Δ ^ 2 := by
        have hΔ2 : (1:ℝ) ≤ S.Δ ^ 2 := one_le_pow₀ hΔ1
        calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ P.G * S.Δ ^ 2 := mul_le_mul hG1 hΔ2 zero_le_one hGpos.le
      exact le_mul_of_one_le_left (by positivity) h1
    have hchain : S.Ω ^ 8 ≤ P.G * S.Δ ^ 2 * P.U ^ 15 := le_trans hΩ8 (le_trans hU815 hGΔ)
    have hc2 : (1:ℝ) ≤ (40040325 * 10 ^ 36 / 2) := by norm_num
    calc (1:ℝ) * S.Ω ^ 8 = S.Ω ^ 8 := by ring
      _ ≤ P.G * S.Δ ^ 2 * P.U ^ 15 := hchain
      _ = 1 * (P.G * S.Δ ^ 2 * P.U ^ 15) := by ring
      _ ≤ (40040325 * 10 ^ 36 / 2) * (P.G * S.Δ ^ 2 * P.U ^ 15) :=
          mul_le_mul_of_nonneg_right hc2 (by positivity)
  -- combine:  1 + 10¹¹⁰Y ≤ (c/2)X + (c/2)X = c·X   (the doubling is a ring identity)
  have hdouble : (40040325 * 10 ^ 36 / 2 : ℝ) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8)
      + (40040325 * 10 ^ 36 / 2) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8)
      = (40040325 * 10 ^ 36) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8) := by ring
  calc 1 + 10 ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
      ≤ (40040325 * 10 ^ 36 / 2) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8)
        + (40040325 * 10 ^ 36 / 2) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8) := by
        linarith [hUpsT, hOne]
    _ = (40040325 * 10 ^ 36) * (P.G * S.Δ ^ 2 * P.U ^ 15 / S.Ω ^ 8) := hdouble

/-- §5 Step-4: the quartic value `P₂`, divided by `d`, is `≤ |v|³/4` in the large-defect
range.  Factored out of `leading_abs_ge` so the term-by-term scale arithmetic gets its own
heartbeat budget.  The threshold `hv2`, the upper window `hv`, and the X-large fact `hDeW`
calibrate the four `P₂`-monomials against `(HΔ/16)|v|³`. -/
theorem ptwo_div_quarter {_a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hdD : S.D ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v|) :
    |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ |v| ^ 3 / 4 := by
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hHpos : 0 < P.H := P.H_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2pos.le
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h2ℓ1ge : (1:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [hℓ12.le]
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
    have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
    rw [hBval] at hb0; exact hb0
  -- ============= UPPER bound on |P₂| (with |v| in place of Vu) =============
  set Wu : ℝ := 130 * (P.G * P.U ^ 5) with hWu_def
  have hWu_nn : 0 ≤ Wu := by rw [hWu_def]; positivity
  set Bu : ℝ := 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) with hBu_def
  have hBu_nn : 0 ≤ Bu := by rw [hBu_def]; positivity
  have hb0'' : |b₀| ≤ Bu := hb0'
  have hℓ2Wu : ℓ₂ ≤ Wu := by rw [hWu_def]; exact hℓ2W'
  have hℓ1Wu : ℓ₁ ≤ Wu := by rw [hWu_def]; exact hℓ1W'
  have hWu3 : ℓ₁ ^ 3 ≤ Wu ^ 3 := pow_le_pow_left₀ hℓ1nn hℓ1Wu 3
  have h21Wu : ℓ₂ - ℓ₁ ≤ Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
  have hP2abs : |Ptwo b₀ v ℓ₁ ℓ₂|
      ≤ 5 * Wu ^ 7 * Bu ^ 3 * |v| + 15 * Wu ^ 6 * Bu ^ 2 * |v| ^ 2
        + 15 * Wu ^ 5 * Bu * |v| ^ 3 + 5 * Wu ^ 4 * |v| ^ 4 := by
    rw [Ptwo]
    set q1 : ℝ := (-5)*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)^2*b₀^3*v with hq1
    set q2 : ℝ := (-(15*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)*b₀^2*v^2)) with hq2
    set q3 : ℝ := (-(5*ℓ₁^3*ℓ₂*(3*ℓ₂-2*ℓ₁)*b₀*v^3)) with hq3
    set q4 : ℝ := (-((5/2)*ℓ₁^3*(2*ℓ₂-ℓ₁)*v^4)) with hq4
    have hbody : -5*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)^2*b₀^3*v - 15*ℓ₁^3*ℓ₂^2*(ℓ₂-ℓ₁)*b₀^2*v^2
        - 5*ℓ₁^3*ℓ₂*(3*ℓ₂-2*ℓ₁)*b₀*v^3 - (5/2)*ℓ₁^3*(2*ℓ₂-ℓ₁)*v^4
        = q1 + q2 + q3 + q4 := by rw [hq1, hq2, hq3, hq4]; ring
    rw [hbody]
    have htri : |q1 + q2 + q3 + q4| ≤ |q1| + |q2| + |q3| + |q4| := by
      calc |q1 + q2 + q3 + q4| ≤ |q1 + q2 + q3| + |q4| := abs_add_le _ _
        _ ≤ (|q1 + q2| + |q3|) + |q4| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|q1| + |q2|) + |q3|) + |q4| := by gcongr; exact abs_add_le _ _
        _ = |q1| + |q2| + |q3| + |q4| := by ring
    refine le_trans htri ?_
    have t1 : |q1| ≤ 5 * Wu ^ 7 * Bu ^ 3 * |v| := by
      have hcnn : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
      have heq : |q1| = 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * |b₀| ^ 3 * |v| := by
        rw [hq1, show (-5) * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v
              = (-(5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)) * b₀ ^ 3 * v by ring,
            abs_mul, abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow]
      rw [heq]
      have hcoef : 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ 5 * Wu ^ 7 := by
        have a2 : ℓ₂ ^ 2 ≤ Wu ^ 2 := pow_le_pow_left₀ hℓ2nn hℓ2Wu 2
        have a3 : (ℓ₂ - ℓ₁) ^ 2 ≤ Wu ^ 2 := pow_le_pow_left₀ h21nn h21Wu 2
        calc 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
            = 5 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) := by ring
          _ ≤ 5 * (Wu ^ 3 * Wu ^ 2 * Wu ^ 2) := by gcongr
          _ = 5 * Wu ^ 7 := by ring
      calc 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * |b₀| ^ 3 * |v|
          ≤ (5 * Wu ^ 7) * Bu ^ 3 * |v| := by
            apply mul_le_mul (mul_le_mul hcoef (pow_le_pow_left₀ hb0nn hb0'' 3) (by positivity)
              (by positivity)) (le_refl _) hvnn (by positivity)
        _ = 5 * Wu ^ 7 * Bu ^ 3 * |v| := by ring
    have t2 : |q2| ≤ 15 * Wu ^ 6 * Bu ^ 2 * |v| ^ 2 := by
      have hcnn : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) := by positivity
      have heq : |q2| = 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * |b₀| ^ 2 * |v| ^ 2 := by
        rw [hq2, show -(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2)
              = (-(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))) * b₀ ^ 2 * v ^ 2 by ring,
            abs_mul, abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow, abs_pow]
      rw [heq]
      have hcoef : 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ≤ 15 * Wu ^ 6 := by
        have a2 : ℓ₂ ^ 2 ≤ Wu ^ 2 := pow_le_pow_left₀ hℓ2nn hℓ2Wu 2
        calc 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)
            = 15 * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) := by ring
          _ ≤ 15 * (Wu ^ 3 * Wu ^ 2 * Wu) := by gcongr
          _ = 15 * Wu ^ 6 := by ring
      calc 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * |b₀| ^ 2 * |v| ^ 2
          ≤ (15 * Wu ^ 6) * Bu ^ 2 * |v| ^ 2 := by
            apply mul_le_mul (mul_le_mul hcoef (pow_le_pow_left₀ hb0nn hb0'' 2) (by positivity)
              (by positivity)) (le_refl _) (by positivity) (by positivity)
        _ = 15 * Wu ^ 6 * Bu ^ 2 * |v| ^ 2 := by ring
    have t3 : |q3| ≤ 15 * Wu ^ 5 * Bu * |v| ^ 3 := by
      have hcnn : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) := by
        have : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith [hℓ12.le]
        positivity
      have heq : |q3| = 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * |b₀| * |v| ^ 3 := by
        rw [hq3, show -(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3)
              = (-(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))) * b₀ * v ^ 3 by ring,
            abs_mul, abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow]
      rw [heq]
      have h32nn : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith [hℓ12.le]
      have hcoef : 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) ≤ 15 * Wu ^ 5 := by
        have a3 : 3 * ℓ₂ - 2 * ℓ₁ ≤ 3 * Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
        calc 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)
            = 5 * (ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) := by ring
          _ ≤ 5 * (Wu ^ 3 * Wu * (3 * Wu)) := by gcongr
          _ = 15 * Wu ^ 5 := by ring
      calc 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * |b₀| * |v| ^ 3
          ≤ (15 * Wu ^ 5) * Bu * |v| ^ 3 := by
            apply mul_le_mul (mul_le_mul hcoef hb0'' hb0nn (by positivity))
              (le_refl _) (by positivity) (by positivity)
        _ = 15 * Wu ^ 5 * Bu * |v| ^ 3 := by ring
    have t4 : |q4| ≤ 5 * Wu ^ 4 * |v| ^ 4 := by
      have hcnn : (0:ℝ) ≤ (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := by
        have : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [h2ℓ1ge]
        positivity
      have heq : |q4| = (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 4 := by
        rw [hq4, show -((5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4)
              = (-((5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * v ^ 4 by ring,
            abs_mul, abs_neg, abs_of_nonneg hcnn, abs_pow]
      rw [heq]
      have hcoef : (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) ≤ 5 * Wu ^ 4 := by
        have a2 : 2 * ℓ₂ - ℓ₁ ≤ 2 * Wu := by rw [hWu_def]; linarith [hℓ2W', hℓ1nn]
        calc (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)
            = (5/2) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) := by ring
          _ ≤ (5/2) * (Wu ^ 3 * (2 * Wu)) := by gcongr
          _ = 5 * Wu ^ 4 := by ring
      calc (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 4
          ≤ (5 * Wu ^ 4) * |v| ^ 4 := mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = 5 * Wu ^ 4 * |v| ^ 4 := by ring
    linarith [t1, t2, t3, t4]
  -- ============= STEP 3: |Ptwo|/d ≤ |v|³/4 =============
  -- Each of the four Z2-terms ≤ HΔ·|v|³/16, so |Ptwo| ≤ HΔ·|v|³/4 ≤ d·|v|³/4.
  have hv3nn : (0:ℝ) ≤ |v| ^ 3 := by positivity
  have hv_lo : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v| := hv2
  have hv_hi : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := hv
  -- HΔ ≥ Δ³U⁵/Ω³   (from hReg : Δ²U⁵ ≤ HΩ³)
  have hHΔlow : S.Δ ^ 3 * P.U ^ 5 / S.Ω ^ 3 ≤ P.H * S.Δ := by
    rw [div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hReg (by positivity : (0:ℝ) ≤ S.Δ)
    calc S.Δ ^ 3 * P.U ^ 5 = S.Δ * (S.Δ ^ 2 * P.U ^ 5) := by ring
      _ ≤ S.Δ * (P.H * S.Ω ^ 3) := h
      _ = P.H * S.Δ * S.Ω ^ 3 := by ring
  -- bound |Ptwo| ≤ HΔ·|v|³/4.  Work term by term against (HΔ/16)|v|³, using Wu=GU⁵, Bu=3e12Δ²/(GΩ³).
  have hPtwo_le : |Ptwo b₀ v ℓ₁ ℓ₂| ≤ (P.H * S.Δ) * |v| ^ 3 / 4 := by
    refine le_trans hP2abs ?_
    -- term-by-term: each ≤ (HΔ/16)·|v|³
    -- abbreviate the big-monomial in Δ,U,Ω that bounds W^k B^m and Δ³U⁵/Ω³ relations.
    have hΩ3pos : (0:ℝ) < S.Ω ^ 3 := by positivity
    -- T3 :  15 Wu⁵ Bu |v|³ ≤ (HΔ/16)|v|³.  Reduces to 240 G⁴U²⁰ ≤ Δ (hDeW), with HΔ≥Δ³U⁵/Ω³.
    have hT3 : 15 * Wu ^ 5 * Bu * |v| ^ 3 ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := by
      have hHΔΩ : S.Δ ^ 3 * P.U ^ 5 ≤ (P.H * S.Δ) * S.Ω ^ 3 := by
        rw [div_le_iff₀ hΩ3pos] at hHΔlow; linarith [hHΔlow]
      have hcoef : 15 * Wu ^ 5 * Bu ≤ (P.H * S.Δ) / 16 := by
        rw [hWu_def, hBu_def]
        have hval : 15 * (130 * (P.G * P.U ^ 5)) ^ 5 * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
            = 1670818500000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) / S.Ω ^ 3 := by
          field_simp; ring
        rw [hval, div_le_div_iff₀ hΩ3pos (by norm_num : (0:ℝ) < 16)]
        -- 45e12·G⁴U²⁵Δ²·16 ≤ HΔ·Ω³ : use HΔΩ³≥Δ³U⁵ and 10¹⁵G⁴U²⁰≤Δ (·U⁵Δ²)
        have hprod : (26733096000000000000000000 : ℝ) * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) ≤ S.Δ ^ 3 * P.U ^ 5 := by
          have h := mul_le_mul_of_nonneg_right hDeW (by positivity : (0:ℝ) ≤ P.U ^ 5 * S.Δ ^ 2)
          have hL : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) * (P.U ^ 5 * S.Δ ^ 2)
              = 1000000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) := by ring
          have hR : S.Δ * (P.U ^ 5 * S.Δ ^ 2) = S.Δ ^ 3 * P.U ^ 5 := by ring
          rw [hL, hR] at h
          have hc : (26733096000000000000000000 : ℝ) * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2)
              ≤ 1000000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          linarith [hc, h]
        linarith [hprod, hHΔΩ]
      calc 15 * Wu ^ 5 * Bu * |v| ^ 3 ≤ (P.H * S.Δ) / 16 * |v| ^ 3 :=
            mul_le_mul_of_nonneg_right hcoef hv3nn
        _ = (P.H * S.Δ) * |v| ^ 3 / 16 := by ring
    -- T4 :  5 Wu⁴ |v|⁴ ≤ (HΔ/16)|v|³.  |v|⁴=|v|³·|v|, |v|≤Vup. Reduces to 80 W⁴ Vup ≤ HΔ.
    have hT4 : 5 * Wu ^ 4 * |v| ^ 4 ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := by
      have hv4 : |v| ^ 4 = |v| ^ 3 * |v| := by ring
      rw [hv4]
      have hbound : 5 * Wu ^ 4 * (|v| ^ 3 * |v|) ≤ 5 * Wu ^ 4 * (|v| ^ 3 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv_hi hv3nn) (by positivity)
      refine le_trans hbound ?_
      have hHΔΩ : S.Δ ^ 3 * P.U ^ 5 ≤ (P.H * S.Δ) * S.Ω ^ 3 := by
        rw [div_le_iff₀ hΩ3pos] at hHΔlow; linarith [hHΔlow]
      have hcoef : 5 * Wu ^ 4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) ≤ (P.H * S.Δ) / 16 := by
        rw [hWu_def]
        have hval : 5 * (130 * (P.G * P.U ^ 5)) ^ 4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
            = 142805000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ) / S.Ω ^ 3 := by
          field_simp; ring
        rw [hval, div_le_div_iff₀ hΩ3pos (by norm_num : (0:ℝ) < 16)]
        -- 5e20·G⁴U²⁵Δ·16 ≤ HΔ·Ω³ ;  HΔΩ³≥Δ³U⁵ ; need 8e21 G⁴U²⁰≤Δ², from Δ²≥10³⁰G⁸U⁴⁰
        -- Δ ≥ 10¹⁵ G⁴U²⁰ and Δ³U⁵ ≥ (10¹⁵ G⁴U²⁰)·Δ²U⁵ ≥ 10¹⁵ G⁴U²⁰·(8e21 G⁴U⁵... ) — chain via two ·
        have hGU1 : (1:ℝ) ≤ P.G ^ 4 * P.U ^ 20 := by
          have h1 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
          have h2 : (1:ℝ) ≤ P.U ^ 20 := one_le_pow₀ hU1
          calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
            _ ≤ P.G ^ 4 * P.U ^ 20 := mul_le_mul h1 h2 zero_le_one (by positivity)
        -- step A: Δ² ≥ 10¹⁵ G⁴U²⁰ · Δ  (from Δ ≥ 10¹⁵ G⁴U²⁰)
        have hA : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) * S.Δ ≤ S.Δ ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hDeW hΔpos.le
          calc 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) * S.Δ ≤ S.Δ * S.Δ := h
            _ = S.Δ ^ 2 := by ring
        -- step B: Δ³U⁵ = Δ·Δ²·U⁵ ≥ Δ·(10¹⁵ G⁴U²⁰·Δ)·U⁵ = 10¹⁵ G⁴U²⁵·Δ²  (one factor Δ extra)
        have hkey : 2284880000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ)
            ≤ S.Δ ^ 3 * P.U ^ 5 := by
          have hB := mul_le_mul_of_nonneg_left hA
            (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 5)
          -- hB :  Δ·U⁵·(10¹⁵ G⁴U²⁰·Δ) ≤ Δ·U⁵·Δ²
          have hBL : S.Δ * P.U ^ 5 * (10 ^ 27 * (P.G ^ 4 * P.U ^ 20) * S.Δ)
              = 1000000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) := by ring
          have hBR : S.Δ * P.U ^ 5 * S.Δ ^ 2 = S.Δ ^ 3 * P.U ^ 5 := by ring
          rw [hBL, hBR] at hB
          -- 1e15 G⁴U²⁵Δ² ≤ Δ³U⁵ ; and 8e21 G⁴U²⁵Δ ≤ 1e15 G⁴U²⁵Δ²  (Δ ≥ 1e15 G⁴U²⁰ ≥ 8e6)
          have hΔge : 2284880000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ)
              ≤ 1000000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) := by
            have hΔbig : (8000000 : ℝ) ≤ S.Δ := by
              have hge : (10:ℝ) ^ 27 ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
                calc (10:ℝ) ^ 27 = 10 ^ 27 * 1 := (mul_one _).symm
                  _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) :=
                      mul_le_mul_of_nonneg_left hGU1 (by norm_num)
              calc (8000000:ℝ) ≤ (10:ℝ) ^ 27 := by norm_num
                _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := hge
                _ ≤ S.Δ := hDeW
            have hMnn : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 25 * S.Δ := by positivity
            have hcoef : (2284880000000000000000000000000:ℝ)
                ≤ 1000000000000000000000000000 * S.Δ := by linarith [hΔbig]
            calc 2284880000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ)
                = (P.G ^ 4 * P.U ^ 25 * S.Δ) * 2284880000000000000000000000000 := by ring
              _ ≤ (P.G ^ 4 * P.U ^ 25 * S.Δ) * (1000000000000000000000000000 * S.Δ) :=
                  mul_le_mul_of_nonneg_left hcoef hMnn
              _ = 1000000000000000000000000000 * (P.G ^ 4 * P.U ^ 25 * S.Δ ^ 2) := by ring
          linarith [hB, hΔge]
        linarith [hHΔΩ, hkey]
      calc 5 * Wu ^ 4 * (|v| ^ 3 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
          = (5 * Wu ^ 4 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) * |v| ^ 3 := by ring
        _ ≤ (P.H * S.Δ) / 16 * |v| ^ 3 := mul_le_mul_of_nonneg_right hcoef hv3nn
        _ = (P.H * S.Δ) * |v| ^ 3 / 16 := by ring
    -- T1, T2 : extra factors of Bu/|v| and Bu²/|v|² ; bounded by T3-type using |v| ≥ V₂.
    -- 5 Wu⁷ Bu³ |v| ≤ (HΔ/16)|v|³  ⟸  5 Wu⁷ Bu³ ≤ (HΔ/16)|v|²  and |v|²≥V₂². But cleaner:
    --   5 Wu⁷ Bu³ |v| = (Wu² Bu²/|v|²)·(5 Wu⁵ Bu |v|³); Wu²Bu²/|v|² ≤ 1.  Actually do directly.
    have hWuBu : Wu ^ 2 * Bu ^ 2 ≤ |v| ^ 2 := by
      -- Wu Bu = GU⁵·3e12Δ²/(GΩ³)=3e12 U⁵Δ²/Ω³ ≤ |v|/6 ≤ |v| ;  so Wu²Bu²≤|v|²
      have hWuBu1 : Wu * Bu = 390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) := by
        rw [hWu_def, hBu_def]; field_simp; ring
      have hle : Wu * Bu ≤ |v| := by
        rw [hWuBu1]
        calc 390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3)
            ≤ 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) := by
              rw [show S.Δ ^ 2 * P.U ^ 5 = P.U ^ 5 * S.Δ ^ 2 by ring]
              apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
          _ ≤ |v| := hv_lo
      have hWuBunn : (0:ℝ) ≤ Wu * Bu := by positivity
      calc Wu ^ 2 * Bu ^ 2 = (Wu * Bu) ^ 2 := by ring
        _ ≤ |v| ^ 2 := pow_le_pow_left₀ hWuBunn hle 2
    have hT1 : 5 * Wu ^ 7 * Bu ^ 3 * |v| ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := by
      -- 5 Wu⁷ Bu³ |v| = (Wu² Bu²)·(5 Wu⁵ Bu |v|) ≤ |v|²·(5 Wu⁵ Bu |v|) = 5 Wu⁵ Bu |v|³ ≤ T3 bound
      have hrw : 5 * Wu ^ 7 * Bu ^ 3 * |v| = (Wu ^ 2 * Bu ^ 2) * (5 * Wu ^ 5 * Bu * |v|) := by ring
      rw [hrw]
      calc (Wu ^ 2 * Bu ^ 2) * (5 * Wu ^ 5 * Bu * |v|)
          ≤ |v| ^ 2 * (5 * Wu ^ 5 * Bu * |v|) :=
            mul_le_mul_of_nonneg_right hWuBu (by positivity)
        _ = (15 * Wu ^ 5 * Bu * |v| ^ 3) / 3 := by ring
        _ ≤ ((P.H * S.Δ) * |v| ^ 3 / 16) / 3 := by
            gcongr
        _ ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := by
            have : (0:ℝ) ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := by positivity
            linarith
    have hT2 : 15 * Wu ^ 6 * Bu ^ 2 * |v| ^ 2 ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := by
      -- 15 Wu⁶ Bu² |v|² = (Wu Bu/|v|)·(15 Wu⁵ Bu |v|³); WuBu≤|v| ; so ≤ 15 Wu⁵ Bu |v|³ ≤ T3 bound
      have hrw : 15 * Wu ^ 6 * Bu ^ 2 * |v| ^ 2 = (Wu * Bu) * (15 * Wu ^ 5 * Bu * |v|) * |v| := by ring
      have hWuBu1 : Wu * Bu = 390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) := by
        rw [hWu_def, hBu_def]; field_simp; ring
      have hle : Wu * Bu ≤ |v| := by
        rw [hWuBu1]
        calc 390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3)
            ≤ 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) := by
              rw [show S.Δ ^ 2 * P.U ^ 5 = P.U ^ 5 * S.Δ ^ 2 by ring]
              apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
          _ ≤ |v| := hv_lo
      rw [hrw]
      calc (Wu * Bu) * (15 * Wu ^ 5 * Bu * |v|) * |v|
          ≤ |v| * (15 * Wu ^ 5 * Bu * |v|) * |v| := by
            apply mul_le_mul_of_nonneg_right _ hvnn
            apply mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 15 * Wu ^ 5 * Bu * |v| ^ 3 := by ring
        _ ≤ (P.H * S.Δ) * |v| ^ 3 / 16 := hT3
    -- sum the four:  |Ptwo bound| ≤ 4·(HΔ/16)|v|³ = (HΔ/4)|v|³
    have hsum : 5 * Wu ^ 7 * Bu ^ 3 * |v| + 15 * Wu ^ 6 * Bu ^ 2 * |v| ^ 2
        + 15 * Wu ^ 5 * Bu * |v| ^ 3 + 5 * Wu ^ 4 * |v| ^ 4
        ≤ (P.H * S.Δ) * |v| ^ 3 / 4 := by linarith [hT1, hT2, hT3, hT4]
    exact hsum
  -- |Ptwo|/d ≤ |v|³/4   (using d ≥ HΔ)
  have hP2d : |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ |v| ^ 3 / 4 := by
    have hdHΔ : P.H * S.Δ ≤ d := by have : S.D = P.H * S.Δ := rfl; rw [← this]; exact hdD
    have h1 : |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ ((P.H * S.Δ) * |v| ^ 3 / 4) / d := by
      gcongr
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ hd_pos (by norm_num : (0:ℝ) < 4)]
    -- (HΔ |v|³/4)·4 = HΔ|v|³ ≤ |v|³·d  ⟸ HΔ ≤ d
    have : (P.H * S.Δ) * |v| ^ 3 / 4 * 4 = (P.H * S.Δ) * |v| ^ 3 := by ring
    rw [this]
    calc (P.H * S.Δ) * |v| ^ 3 ≤ d * |v| ^ 3 :=
          mul_le_mul_of_nonneg_right hdHΔ hv3nn
      _ = |v| ^ 3 * d := by ring
  exact hP2d

/-- **`|P₁ + P₂/d| ≥ |v|³/4`** (the cubic dominance of `Upsilon_expand`'s polynomial core,
writeup 1029–1033).  Factored out of `leading_abs_ge` so the §5 Step-4 derivative lower bound
(`Sigma_closed_deriv_lb`) can reuse it.  Requires `S.D ≤ d` (lower window only). -/
theorem psum_abs_ge {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hdD : S.D ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v|) :
    |v| ^ 3 / 4 ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2pos.le
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h2ℓ1ge : (1:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [hℓ12.le]
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
    have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
    rw [hBval] at hb0; exact hb0
  -- 6(ℓ₂−ℓ₁)|b₀| ≤ |v|
  have hWB : 6 * (ℓ₂ - ℓ₁) * |b₀| ≤ |v| := by
    have hbW : (ℓ₂ - ℓ₁) * |b₀|
        ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) := by
      apply mul_le_mul _ hb0' hb0nn (by positivity)
      linarith [hℓ2W', hℓ1nn]
    have heq : (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
        = 390000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) := by field_simp; ring
    rw [heq] at hbW
    calc 6 * (ℓ₂ - ℓ₁) * |b₀| = 6 * ((ℓ₂ - ℓ₁) * |b₀|) := by ring
      _ ≤ 6 * (390000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3)) :=
          mul_le_mul_of_nonneg_left hbW (by norm_num)
      _ = 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) := by ring
      _ ≤ |v| := hv2
  -- |E| ≥ (2ℓ₂−ℓ₁)|v|/2
  have hEabs : (2 * ℓ₂ - ℓ₁) * |v| / 2 ≤ |3*ℓ₂*(ℓ₂-ℓ₁)*b₀ + (2*ℓ₂-ℓ₁)*v| := by
    have hlow : (2 * ℓ₂ - ℓ₁) * |v| - 3*ℓ₂*(ℓ₂-ℓ₁)*|b₀|
        ≤ |3*ℓ₂*(ℓ₂-ℓ₁)*b₀ + (2*ℓ₂-ℓ₁)*v| := by
      have h1 : |(2*ℓ₂-ℓ₁)*v| - |3*ℓ₂*(ℓ₂-ℓ₁)*b₀|
          ≤ |3*ℓ₂*(ℓ₂-ℓ₁)*b₀ + (2*ℓ₂-ℓ₁)*v| := by
        rw [show (3*ℓ₂*(ℓ₂-ℓ₁)*b₀ + (2*ℓ₂-ℓ₁)*v)
              = (2*ℓ₂-ℓ₁)*v - (-(3*ℓ₂*(ℓ₂-ℓ₁)*b₀)) by ring]
        have := abs_sub_abs_le_abs_sub ((2*ℓ₂-ℓ₁)*v) (-(3*ℓ₂*(ℓ₂-ℓ₁)*b₀))
        rwa [abs_neg] at this
      have hA : |(2*ℓ₂-ℓ₁)*v| = (2*ℓ₂-ℓ₁) * |v| := by
        rw [abs_mul, abs_of_nonneg (by linarith [h2ℓ1ge] : (0:ℝ) ≤ 2*ℓ₂-ℓ₁)]
      have hB : |3*ℓ₂*(ℓ₂-ℓ₁)*b₀| = 3*ℓ₂*(ℓ₂-ℓ₁)*|b₀| := by
        rw [show 3*ℓ₂*(ℓ₂-ℓ₁)*b₀ = (3*ℓ₂*(ℓ₂-ℓ₁))*b₀ by ring, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 3*ℓ₂*(ℓ₂-ℓ₁))]
      rw [hA, hB] at h1; exact h1
    have hhalf : 3*ℓ₂*(ℓ₂-ℓ₁)*|b₀| ≤ (2 * ℓ₂ - ℓ₁) * |v| / 2 := by
      have hkey : ℓ₂ * (6 * (ℓ₂ - ℓ₁) * |b₀|) ≤ (2*ℓ₂-ℓ₁) * |v| := by
        calc ℓ₂ * (6 * (ℓ₂ - ℓ₁) * |b₀|) ≤ ℓ₂ * |v| :=
              mul_le_mul_of_nonneg_left hWB hℓ2nn
          _ ≤ (2*ℓ₂-ℓ₁) * |v| := by
              apply mul_le_mul_of_nonneg_right _ hvnn; linarith
      linarith [hkey]
    linarith [hlow, hhalf]
  -- |P₁| ≥ |v|³/2
  have hP1ge : |v| ^ 3 / 2 ≤ |Pone b₀ v ℓ₁ ℓ₂| := by
    have hfac : Pone b₀ v ℓ₁ ℓ₂ = ℓ₁^3 * v^2 * (3*ℓ₂*(ℓ₂-ℓ₁)*b₀ + (2*ℓ₂-ℓ₁)*v) := by
      rw [Pone]; ring
    rw [hfac, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hℓ1nn]
    have hb : ℓ₁ ^ 3 * |v| ^ 2 * ((2 * ℓ₂ - ℓ₁) * |v| / 2)
        ≤ ℓ₁ ^ 3 * |v| ^ 2 * |3*ℓ₂*(ℓ₂-ℓ₁)*b₀ + (2*ℓ₂-ℓ₁)*v| :=
      mul_le_mul_of_nonneg_left hEabs (by positivity)
    have hc : |v| ^ 3 / 2 ≤ ℓ₁ ^ 3 * |v| ^ 2 * ((2 * ℓ₂ - ℓ₁) * |v| / 2) := by
      have hℓ13 : (1:ℝ) ≤ ℓ₁ ^ 3 := by
        calc (1:ℝ) = 1 ^ 3 := by norm_num
          _ ≤ ℓ₁ ^ 3 := by gcongr
      have hv3 : |v| ^ 2 * |v| = |v| ^ 3 := by ring
      have hstep : ℓ₁ ^ 3 * |v| ^ 2 * ((2 * ℓ₂ - ℓ₁) * |v| / 2)
          = (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * (|v| ^ 3 / 2) := by rw [← hv3]; ring
      rw [hstep]
      have hcoef : (1:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := by
        calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) :=
              mul_le_mul hℓ13 h2ℓ1ge zero_le_one (pow_nonneg hℓ1nn 3)
      have hvq : (0:ℝ) ≤ |v| ^ 3 / 2 := by positivity
      exact le_mul_of_one_le_left hvq hcoef
    linarith [hb, hc]
  -- |P₂|/d ≤ |v|³/4
  have hP2d : |Ptwo b₀ v ℓ₁ ℓ₂| / d ≤ |v| ^ 3 / 4 :=
    ptwo_div_quarter (_a := a) hℓ1 hℓ12 hℓ2W hb0 hv hdD hd_pos hReg hG1 hU1 hDeW hv2
  -- assemble
  have htri : |Pone b₀ v ℓ₁ ℓ₂| - |Ptwo b₀ v ℓ₁ ℓ₂ / d|
      ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| := by
    have hsplit : |Pone b₀ v ℓ₁ ℓ₂|
        ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| + |Ptwo b₀ v ℓ₁ ℓ₂ / d| := by
      have := abs_add_le (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d) (-(Ptwo b₀ v ℓ₁ ℓ₂ / d))
      simp only [add_neg_cancel_right, abs_neg] at this
      exact this
    linarith [hsplit]
  have hP2dabs : |Ptwo b₀ v ℓ₁ ℓ₂ / d| ≤ |v| ^ 3 / 4 := by
    rw [abs_div, abs_of_pos hd_pos]; exact hP2d
  linarith [htri, hP1ge, hP2dabs]

/-- **§5 Step-4 leading-term lower bound** (the `s ≠ 0` magnitude fact, writeup 1029–1033).

Under the per-`r` scale bounds, the X-large regime fact `hΩH : 55Ω ≤ H` (forcing the bracket
`−4+10a/d ∈ [−4,−2]`, so `|bracket| ≥ 2`), the X-large regime fact `hDeW : 180·G⁴U²⁰ ≤ Δ`, and
the large-defect threshold `hv2 : V₂ ≤ |v|` with `V₂ = 1.8·10¹³·Δ²U⁵/Ω³`, the leading value is
`≥ 1 + 10¹¹⁰·UpsT`.  The threshold `V₂ ≥ 2|v*|` (with `v* = −3ℓ₂(ℓ₂−ℓ₁)b₀/(2ℓ₂−ℓ₁)` the zero of
the `P₁`-bracket) forces the cubic `v³`-monomial of `P₁` to dominate, giving `|P₁| ≥ |v|³/2`; the
upper bound `|v| ≤ 10²⁰ΔU⁵/Ω³` together with `hDeW` controls `|P₂|/d ≤ |P₁|/2`. -/
theorem leading_abs_ge {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (_hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 55 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v|) :
    1 + 10 ^ 119 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
      ≤ |Lval P.X a d b₀ v ℓ₁ ℓ₂| := by
  -- positivity of scales
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  obtain ⟨hdD, hd2D⟩ := hdwin
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  -- ℓ basics
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2pos.le
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h2ℓ1ge : (1:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith [hℓ12.le]
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- scale identities
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hAval : S.A = S.Δ * S.Ω := rfl
  have hXval : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
  have hWval : P.Wval = P.G * P.U ^ 5 := rfl
  -- per-variable bounds
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by rw [hBval] at hb0; exact hb0
  have ha_lo' : S.Δ * S.Ω / 5 ≤ a := by rw [hAval] at ha_lo; exact ha_lo
  have ha_hi' : a ≤ 11 * (S.Δ * S.Ω) := by rw [hAval] at ha_hi; exact ha_hi
  -- ===== regime: Δ²U⁵ ≤ HΩ³ (same as in leading_abs_le) =====
  have hGU5Ω3 : (1 : ℝ) ≤ P.G * P.U ^ 5 * S.Ω ^ 3 := by
    have hU2Ω : P.U ≤ P.U ^ 2 / S.Ω := by
      rw [le_div_iff₀ hΩpos, pow_two]; exact mul_le_mul_of_nonneg_left hΩU hUpos.le
    have hfactor : P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) = P.G * P.U ^ 5 * S.Ω ^ 3 := by
      field_simp
    have hU2Ωpos : (0 : ℝ) ≤ P.U ^ 2 / S.Ω := by positivity
    have hchain : (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) := by
      calc (1 : ℝ) ≤ P.U := hU1
        _ ≤ P.U ^ 2 / S.Ω := hU2Ω
        _ = 1 * (P.U ^ 2 / S.Ω) := by ring
        _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) :=
            mul_le_mul_of_nonneg_right hband hU2Ωpos
    rwa [hfactor] at hchain
  have hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 := by
    have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
      (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
    have hstep : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3) ≤ P.H * S.Ω ^ 3 := by
      have heq : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3)
          = (P.G * P.U ^ 10 * S.Δ ^ 2) * S.Ω ^ 3 := by ring
      rw [heq]; exact mul_le_mul_of_nonneg_right hHbig (by positivity)
    have hle : S.Δ ^ 2 * P.U ^ 5 ≤ S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3) :=
      le_mul_of_one_le_right (by positivity) hGU5Ω3
    linarith [hle, hstep]
  -- ============= |P₁ + P₂/d| ≥ |v|³/4  (factored: psum_abs_ge) =============
  have hPsum_ge : |v| ^ 3 / 4 ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| :=
    psum_abs_ge (a := a) hℓ1 hℓ12 hℓ2W hb0 hv hdD hd_pos hReg hG1 hU1 hDeW hv2
  -- bracket lower:  |−4+10a/d| ≥ 2   (from 55Ω ≤ H ⟹ a/d ≤ 1/5 ⟹ 10a/d ≤ 2)
  have hbracket : 2 ≤ |(-4 + 10 * a / d)| := by
    have h10ad : 10 * a / d = 10 * (a / d) := by ring
    rw [h10ad]
    have had : a / d ≤ 1 / 5 := by
      rw [div_le_div_iff₀ hd_pos (by norm_num)]
      -- 5a ≤ d, with a ≤ 11A = 11ΔΩ and d ≥ D = HΔ ; 55ΔΩ ≤ HΔ from 55Ω ≤ H
      have hdD' : P.H * S.Δ ≤ d := by have : S.D = P.H * S.Δ := rfl; rw [← this]; exact hdD
      have h55 : 55 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by
        have h := mul_le_mul_of_nonneg_right hΩH hΔpos.le
        calc 55 * (S.Δ * S.Ω) = 55 * S.Ω * S.Δ := by ring
          _ ≤ P.H * S.Δ := h
      linarith [ha_hi', hdD', h55]
    have had0 : 0 ≤ a / d := by positivity
    rw [abs_of_nonpos (by linarith [had])]
    linarith [had]
  -- prefactor lower:  Xa/d⁵ ≥ GΩ/(160Δ⁴)   (a ≥ A/5 = ΔΩ/5, d ≤ 2D = 2HΔ, X = GH⁵)
  have hpre_pos : 0 < P.X * a / d ^ 5 := by positivity
  have hpre : P.G * S.Ω / (160 * S.Δ ^ 4) ≤ P.X * a / d ^ 5 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- GΩ·d⁵ ≤ Xa·160Δ⁴, with d ≤ 2HΔ, a ≥ ΔΩ/5, X = GH⁵
    have hd5 : d ^ 5 ≤ (2 * (P.H * S.Δ)) ^ 5 := by
      apply pow_le_pow_left₀ hd_pos.le
      have : S.D = P.H * S.Δ := rfl; rw [this] at hd2D; linarith [hd2D]
    have ha5 : S.Δ * S.Ω / 5 ≤ a := ha_lo'
    calc P.G * S.Ω * d ^ 5 ≤ P.G * S.Ω * (2 * (P.H * S.Δ)) ^ 5 :=
          mul_le_mul_of_nonneg_left hd5 (by positivity)
      _ = (P.G * P.H ^ 5) * (S.Δ * S.Ω / 5) * (160 * S.Δ ^ 4) := by ring
      _ ≤ (P.G * P.H ^ 5) * a * (160 * S.Δ ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left ha5 (by positivity)
      _ = P.X * a * (160 * S.Δ ^ 4) := by rw [hXval]
  -- |Lval| = (Xa/d⁵)·|bracket|·|Pone+Ptwo/d| ≥ (GΩ/160Δ⁴)·2·(|v|³/4)
  have hLval_eq : |Lval P.X a d b₀ v ℓ₁ ℓ₂|
      = (P.X * a / d ^ 5) * (|(-4 + 10 * a / d)| * |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d|) := by
    rw [Lval, abs_mul, abs_mul, abs_of_pos hpre_pos]
  have hLval_ge : (P.G * S.Ω / (160 * S.Δ ^ 4)) * (2 * (|v| ^ 3 / 4))
      ≤ |Lval P.X a d b₀ v ℓ₁ ℓ₂| := by
    rw [hLval_eq]
    apply mul_le_mul hpre _ (by positivity) hpre_pos.le
    apply mul_le_mul hbracket hPsum_ge (by positivity) (le_trans (by norm_num) hbracket)
  refine le_trans ?_ hLval_ge
  -- ============= STEP 5: scale chain (factored into leading_scale_chain) =============
  have hLHS_eq : (P.G * S.Ω / (160 * S.Δ ^ 4)) * (2 * (|v| ^ 3 / 4))
      = P.G * S.Ω * |v| ^ 3 / (320 * S.Δ ^ 4) := by ring
  rw [hLHS_eq]
  exact leading_scale_chain (S := S) hReg hG1 hU1 hΔ1 hΩU hUbig hDeW hv2

end Squarefree
