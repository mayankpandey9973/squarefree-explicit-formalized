import Squarefree.Lower.DefectUpsilon
import Squarefree.Lower.UpsilonErr
import Squarefree.Lower.UpsilonErrSharp
import Squarefree.Lower.UpsilonNearInt
import Squarefree.Lower.UpsilonNearIntNeg
import Squarefree.Lower.QNearInt

/-!
# §5 Step-4 per-`r` near-integer reduction (writeup 992–1083)

This file is the §5 Step-4 analogue of `Step23Combine.phif_delta_le`.  Where the Step-3
near-integer bound `distInt(φ_f) ≤ 4·δ₂₃` reduced through the first-difference combination
`𝒬` (`Q_gen_expand` + `Q_distInt_le`), the Step-4 bound reduces through the **second**-difference
collection `Υ` (writeup 992):

  `Υ := ℓ₂²(ℓ₂−ℓ₁)²·Ŝ_{a,ℓ₁b₀}(d) − ℓ₁²(ℓ₂−ℓ₁)²·Ŝ_{a,ℓ₂b₀+v}(d)
        + ℓ₁²ℓ₂²·Ŝ_{a,(ℓ₂−ℓ₁)b₀+v}(d+ℓ₁b₀)`,

whose closed form is the cubic/quartic `Σ_s` (writeup 1013, 1047):

  `Σ_closed(d,b₀) := (Xa/d⁵)·((−4 + 10a/d)·(P₁ + P₂/d))`.

## What this file proves (GREEN)

`Sigma_closed_near_int` (the keystone Step-4 near-integer ingredient): for the integer
witnesses `d,d',b₁,b₂,b₃` of `Υ`, the closed form `Σ_closed(d,b₀)` is near an integer,

  `distInt(Σ_closed(d, b₀)) ≤ 45·Wval⁴/Δ + 10¹¹⁰·UpsT`,

`UpsT = Δ⁴G⁵U⁴⁵/(H²Ω¹⁴)`.  This is exactly the writeup-1042 statement
`Σ_s = s + O(Δ⁴G⁵U⁴⁵/(H²Ω¹⁴) + G⁴U²⁰/Δ)` made precise (the `Wval⁴/Δ ≍ G⁴U²⁰/Δ` term is the
`Υ ∈ ℤ + O(W⁴/Δ)` slack of writeup 1001; the `10¹¹⁰·UpsT` term is the `Υ`-expansion error of
writeup 1013).  It is built from three already-proved pieces:

* `Upsilon_expand` — `|Υ_Ŝ − Σ_closed(d,b₀)| ≤ ERR` (the exact collection identity);
* `upsilon_err_le` — `ERR ≤ 10¹¹⁰·UpsT`;
* `Upsilon_near_int` — `distInt(Υ_Ŝ) ≤ 45·Wval⁴/Δ`.

It is the §5 Step-4 analogue of `Q_distInt_le` and is the per-`r` `δ_v`-tolerance feeding the
`step4_smooth_count` double sum.  The remaining link `φ_v = Σ_closed + O(δ_v)` (the
`d→d̃`, `b₀→b̃` smoothing, writeup 1071) is the Step-4 analogue of the `phif_dist_le` +
`v_replace_le` + `phi_d_replace` chain and is tracked separately.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- The §5 Step-4 closed form `Σ_closed(d,b₀) = (Xa/d⁵)·((−4 + 10a/d)·(P₁ + P₂/d))`
(writeup 1013, 1047), the cubic/quartic Taylor lead of the second-difference collection `Υ`. -/
noncomputable def Sigma_closed (X a b₀ v d ℓ₁ ℓ₂ : ℝ) : ℝ :=
  (X * a / d ^ 5) * ((-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d))

/-- **§5 Step-4 closed-form near-integer bound** (writeup 1042).  The cubic/quartic closed form
`Σ_closed(d,b₀)` of the second-difference collection `Υ` lies within
`45·Wval⁴/Δ + 10¹¹⁰·UpsT` of an integer, i.e.
`Σ_s = s + O(Δ⁴G⁵U⁴⁵/(H²Ω¹⁴) + G⁴U²⁰/Δ)`.

The hypotheses package, in order: the real `Υ`-expansion side conditions (positivity, Taylor
windows on the three corrected second differences, `b₀/v` windows, the `Δ ≥ G²U⁵`/`U`-large
regime) feeding `Upsilon_expand` + `upsilon_err_le`, together with the integer-witness `inD`
data feeding `Upsilon_near_int`.  The integer-witness/real-value coherence is supplied through
`hcoh`, which identifies the three real `b`-arguments and the two base points with the integer
combinations the `inD` brick recognises. -/
theorem Sigma_closed_near_int
    {a : ℝ} {b₀ v d ℓ₁ ℓ₂ : ℝ}
    {aℤ dℤ d'ℤ b₁ℤ b₂ℤ b₃ℤ ℓ₁ℤ ℓ₂ℤ : ℤ}
    -- real side (Upsilon_expand + upsilon_err_le)
    (hX : 0 < P.X) (ha : 0 < a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb1 : ℓ₁ * b₀ ≠ 0) (hb2 : ℓ₂ * b₀ + v ≠ 0) (hb3 : (ℓ₂ - ℓ₁) * b₀ + v ≠ 0)
    (hwin : 4 * (a + ℓ₂ * |b₀| + |v|) ≤ d)
    (hwin3 : 4 * (a + |(ℓ₂ - ℓ₁) * b₀ + v|) ≤ d + ℓ₁ * b₀)
    (hshiftpos : 0 < d + ℓ₁ * b₀)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hshift2 : d / 2 ≤ d + ℓ₁ * b₀)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    -- integer-witness coherence (Upsilon_near_int)
    (hacoh : a = (aℤ : ℝ)) (hdcoh : d = (dℤ : ℝ)) (hd'coh : d + ℓ₁ * b₀ = (d'ℤ : ℝ))
    (hℓ1coh : ℓ₁ = (ℓ₁ℤ : ℝ)) (hℓ2coh : ℓ₂ = (ℓ₂ℤ : ℝ))
    (hb1coh : ℓ₁ * b₀ = (b₁ℤ : ℝ)) (hb2coh : ℓ₂ * b₀ + v = (b₂ℤ : ℝ))
    (hb3coh : (ℓ₂ - ℓ₁) * b₀ + v = (b₃ℤ : ℝ))
    (haℤ : 0 ≤ aℤ) (hb1ℤ : 0 ≤ b₁ℤ) (hb2ℤ : 0 ≤ b₂ℤ) (hb3ℤ : 0 ≤ b₃ℤ)
    (hℓ1ℤ : 0 ≤ ℓ₁ℤ) (hℓ12ℤ : ℓ₁ℤ ≤ ℓ₂ℤ) (hℓ2Wℤ : (ℓ₂ℤ : ℝ) ≤ 130 * P.Wval)
    (hDd : S.D ≤ (dℤ : ℝ)) (hDd' : S.D ≤ (d'ℤ : ℝ))
    (hab1 : (aℤ : ℝ) + (b₁ℤ : ℝ) ≤ (dℤ : ℝ)) (hab2 : (aℤ : ℝ) + (b₂ℤ : ℝ) ≤ (dℤ : ℝ))
    (hab3 : (aℤ : ℝ) + (b₃ℤ : ℝ) ≤ (d'ℤ : ℝ))
    (hS1_0 : inD P.X P.H dℤ) (hS1_1 : inD P.X P.H (dℤ + aℤ))
    (hS1_2 : inD P.X P.H (dℤ + b₁ℤ)) (hS1_3 : inD P.X P.H (dℤ + aℤ + b₁ℤ))
    (hS2_2 : inD P.X P.H (dℤ + b₂ℤ)) (hS2_3 : inD P.X P.H (dℤ + aℤ + b₂ℤ))
    (hS3_0 : inD P.X P.H d'ℤ) (hS3_1 : inD P.X P.H (d'ℤ + aℤ))
    (hS3_2 : inD P.X P.H (d'ℤ + b₃ℤ)) (hS3_3 : inD P.X P.H (d'ℤ + aℤ + b₃ℤ)) :
    distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 119 * UpsT P S := by
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  -- ===== the integer-side Υ (combination of Ŝ at the integer witnesses) =====
  -- Abbreviate the real `Υ_Ŝ` (the Shat combination evaluated at the real arguments).
  set UpsShat : ℝ :=
    ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * Shat P.X a (ℓ₁ * b₀) d
      - ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * Shat P.X a (ℓ₂ * b₀ + v) d
      + ℓ₁ ^ 2 * ℓ₂ ^ 2 * Shat P.X a ((ℓ₂ - ℓ₁) * b₀ + v) (d + ℓ₁ * b₀) with hUpsShat_def
  -- ===== (A) distInt(Υ_Ŝ) ≤ 45·Wval⁴/Δ  via Upsilon_near_int (integer witnesses) =====
  -- The integer combination recognised by the brick, cast to ℝ.
  have hnear := Upsilon_near_int (P := P) S (a := aℤ) (d := dℤ) (d' := d'ℤ)
    (b₁ := b₁ℤ) (b₂ := b₂ℤ) (b₃ := b₃ℤ) (ℓ₁ := ℓ₁ℤ) (ℓ₂ := ℓ₂ℤ)
    haℤ hb1ℤ hb2ℤ hb3ℤ hℓ1ℤ hℓ12ℤ hℓ2Wℤ hDd hDd' hab1 hab2 hab3
    hS1_0 hS1_1 hS1_2 hS1_3 hS2_2 hS2_3 hS3_0 hS3_1 hS3_2 hS3_3
  -- rewrite the integer Υ to match `UpsShat` via the coherence equalities
  have hUpsShat_eq :
      (((ℓ₂ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ)) : ℝ) * Shat P.X (aℤ : ℝ) (b₁ℤ : ℝ) (dℤ : ℝ)
        - (((ℓ₁ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ)) : ℝ) * Shat P.X (aℤ : ℝ) (b₂ℤ : ℝ) (dℤ : ℝ)
        + (((ℓ₁ℤ ^ 2 * ℓ₂ℤ ^ 2 : ℤ)) : ℝ) * Shat P.X (aℤ : ℝ) (b₃ℤ : ℝ) (d'ℤ : ℝ)
      = UpsShat := by
    -- rewrite every real argument of the three `Shat`s back to the `b₀,v,d` expressions,
    -- then match the integer coefficients via `push_cast; ring`
    rw [hUpsShat_def, ← hacoh, ← hdcoh, ← hd'coh, ← hb1coh, ← hb2coh, ← hb3coh]
    rw [show ((ℓ₂ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ) : ℝ) = ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 by
          rw [hℓ1coh, hℓ2coh]; push_cast; ring,
        show ((ℓ₁ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ) : ℝ) = ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 by
          rw [hℓ1coh, hℓ2coh]; push_cast; ring,
        show ((ℓ₁ℤ ^ 2 * ℓ₂ℤ ^ 2 : ℤ) : ℝ) = ℓ₁ ^ 2 * ℓ₂ ^ 2 by
          rw [hℓ1coh, hℓ2coh]; push_cast; ring]
  rw [hUpsShat_eq] at hnear
  -- ===== (B) |Υ_Ŝ − Σ_closed(d,b₀)| ≤ ERR  via Upsilon_expand =====
  have hexp := Upsilon_expand (X := P.X) (a := a) (b₀ := b₀) (v := v) (d := d)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hX ha hd hℓ1R hℓ12 hb1 hb2 hb3 hwin hwin3 hshiftpos
  rw [← hUpsShat_def] at hexp
  -- the subtracted term in `Upsilon_expand` is exactly `Sigma_closed`
  have htgt_eq :
      (P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d))
        = Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ := by
    rw [Sigma_closed]
  rw [htgt_eq] at hexp
  -- ===== (C) ERR ≤ 10¹¹⁰·UpsT  via upsilon_err_le =====
  have herr := upsilon_err_le (P := P) (S := S) (a := a) (b₀ := b₀) (v := v) (d := d)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha ha_hi hℓ1 hℓ12 hℓ2W hdwin hb0 hv hshift2
    h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
  -- combine: |Υ_Ŝ − Σ_closed| ≤ 10¹¹⁰·UpsT
  have hexp' : |UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ 10 ^ 119 * UpsT P S :=
    le_trans hexp herr
  -- ===== assemble:  distInt(Σ_closed) ≤ distInt(Υ_Ŝ) + |Υ_Ŝ − Σ_closed| =====
  -- distInt(Σ) ≤ distInt(Υ) + distInt(Σ − Υ) ≤ distInt(Υ) + |Σ − Υ|
  -- `distInt` is symmetric under negation
  have hneg : ∀ x y : ℝ, distInt (x - y) = distInt (y - x) := by
    intro x y
    apply le_antisymm
    · refine le_trans (distInt_le_intDist _ (-round (y - x))) ?_
      have e : (x - y) - ((-round (y - x) : ℤ) : ℝ) = -((y - x) - (round (y - x) : ℝ)) := by
        push_cast; ring
      rw [e, abs_neg]; simp only [distInt, le_refl]
    · refine le_trans (distInt_le_intDist _ (-round (x - y))) ?_
      have e : (y - x) - ((-round (x - y) : ℤ) : ℝ) = -((x - y) - (round (x - y) : ℝ)) := by
        push_cast; ring
      rw [e, abs_neg]; simp only [distInt, le_refl]
  have hsub : distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      ≤ distInt UpsShat + distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - UpsShat) := by
    -- Σ = Υ − (Υ − Σ);  distInt(Υ − (Υ−Σ)) ≤ distInt Υ + distInt(Υ−Σ) = distInt Υ + distInt(Σ−Υ)
    have hSigeq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        = UpsShat - (UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) := by ring
    rw [hneg (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) UpsShat]
    calc distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
        = distInt (UpsShat - (UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) := by rw [← hSigeq]
      _ ≤ distInt UpsShat + distInt (UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) :=
          distInt_sub_le _ _
  have hSU : distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - UpsShat)
      ≤ |UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
    refine le_trans (distInt_le_intDist _ 0) ?_
    rw [Int.cast_zero, sub_zero, abs_sub_comm]
  calc distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      ≤ distInt UpsShat + distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - UpsShat) := hsub
    _ ≤ distInt UpsShat + |UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
        linarith [hSU]
    _ ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 119 * UpsT P S := by
        linarith [hnear, hexp']

/-- **§5 Step-4 closed-form near-integer bound, `b ≤ 0` form** (writeup 1042).  Mirror of
`Sigma_closed_near_int` for the genuine decreasing-`d̃ₐ` triples, where all three integer shifts
`bᵢℤ ≤ 0`.  The only change from the `b ≥ 0` form is that the integer-side `Υ` near-integer
bound is supplied by `Upsilon_near_int_neg` (the reflected keystone), so the sign hypotheses are
`bᵢℤ ≤ 0` and the placement/window hypotheses are the shifted form `S.D ≤ dᵢ+bᵢ`,
`aℤ + (−bᵢℤ) ≤ dᵢ+bᵢ` (each shifted point `dᵢ+bᵢ` is itself a `d*`-witness in `[D,2D]`).
This form also takes the SHARP `v_defect_le` window `|v| ≤ 3.9·10¹⁴·ΔU⁵/Ω³` and routes the
expansion error through `upsilon_err_le_sharp`, giving the sharpened tolerance
`distInt(Σ_closed) ≤ 10¹¹·Wval⁴·H/D + 10¹¹¹·UpsT` that the `step4_fiber_extract`
err-domination step needs. -/
theorem Sigma_closed_near_int_neg
    {a : ℝ} {b₀ v d ℓ₁ ℓ₂ : ℝ}
    {aℤ dℤ d'ℤ b₁ℤ b₂ℤ b₃ℤ ℓ₁ℤ ℓ₂ℤ : ℤ}
    -- real side (Upsilon_expand + upsilon_err_le)
    (hX : 0 < P.X) (ha : 0 < a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb1 : ℓ₁ * b₀ ≠ 0) (hb2 : ℓ₂ * b₀ + v ≠ 0) (hb3 : (ℓ₂ - ℓ₁) * b₀ + v ≠ 0)
    (hwin : 4 * (a + ℓ₂ * |b₀| + |v|) ≤ d)
    (hwin3 : 4 * (a + |(ℓ₂ - ℓ₁) * b₀ + v|) ≤ d + ℓ₁ * b₀)
    (hshiftpos : 0 < d + ℓ₁ * b₀)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 390000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hshift2 : d / 2 ≤ d + ℓ₁ * b₀)
    (_h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (_hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    -- integer-witness coherence (Upsilon_near_int_neg)
    (hacoh : a = (aℤ : ℝ)) (hdcoh : d = (dℤ : ℝ)) (hd'coh : d + ℓ₁ * b₀ = (d'ℤ : ℝ))
    (hℓ1coh : ℓ₁ = (ℓ₁ℤ : ℝ)) (hℓ2coh : ℓ₂ = (ℓ₂ℤ : ℝ))
    (hb1coh : ℓ₁ * b₀ = (b₁ℤ : ℝ)) (hb2coh : ℓ₂ * b₀ + v = (b₂ℤ : ℝ))
    (hb3coh : (ℓ₂ - ℓ₁) * b₀ + v = (b₃ℤ : ℝ))
    (haℤ : 0 ≤ aℤ) (hb1ℤ : b₁ℤ ≤ 0) (hb2ℤ : b₂ℤ ≤ 0) (hb3ℤ : b₃ℤ ≤ 0)
    (hℓ1ℤ : 0 ≤ ℓ₁ℤ) (hℓ12ℤ : ℓ₁ℤ ≤ ℓ₂ℤ) (hℓ2Wℤ : (ℓ₂ℤ : ℝ) ≤ 130 * P.Wval)
    -- the shifted base points `dᵢ+bᵢ` are `d*`-witnesses in `[D, 2D]`
    (hDd1 : S.D ≤ ((dℤ + b₁ℤ : ℤ) : ℝ)) (hDd2 : S.D ≤ ((dℤ + b₂ℤ : ℤ) : ℝ))
    (hDd3 : S.D ≤ ((d'ℤ + b₃ℤ : ℤ) : ℝ))
    (hab1 : (aℤ : ℝ) + ((-b₁ℤ : ℤ) : ℝ) ≤ ((dℤ + b₁ℤ : ℤ) : ℝ))
    (hab2 : (aℤ : ℝ) + ((-b₂ℤ : ℤ) : ℝ) ≤ ((dℤ + b₂ℤ : ℤ) : ℝ))
    (hab3 : (aℤ : ℝ) + ((-b₃ℤ : ℤ) : ℝ) ≤ ((d'ℤ + b₃ℤ : ℤ) : ℝ))
    (hS1_0 : inD P.X P.H dℤ) (hS1_1 : inD P.X P.H (dℤ + aℤ))
    (hS1_2 : inD P.X P.H (dℤ + b₁ℤ)) (hS1_3 : inD P.X P.H (dℤ + aℤ + b₁ℤ))
    (hS2_2 : inD P.X P.H (dℤ + b₂ℤ)) (hS2_3 : inD P.X P.H (dℤ + aℤ + b₂ℤ))
    (hS3_0 : inD P.X P.H d'ℤ) (hS3_1 : inD P.X P.H (d'ℤ + aℤ))
    (hS3_2 : inD P.X P.H (d'ℤ + b₃ℤ)) (hS3_3 : inD P.X P.H (d'ℤ + aℤ + b₃ℤ)) :
    distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 111 * UpsT P S := by
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  set UpsShat : ℝ :=
    ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * Shat P.X a (ℓ₁ * b₀) d
      - ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * Shat P.X a (ℓ₂ * b₀ + v) d
      + ℓ₁ ^ 2 * ℓ₂ ^ 2 * Shat P.X a ((ℓ₂ - ℓ₁) * b₀ + v) (d + ℓ₁ * b₀) with hUpsShat_def
  -- ===== (A) distInt(Υ_Ŝ) ≤ 45·Wval⁴/Δ via Upsilon_near_int_neg (b ≤ 0) =====
  have hnear := Upsilon_near_int_neg (P := P) S (a := aℤ) (d := dℤ) (d' := d'ℤ)
    (b₁ := b₁ℤ) (b₂ := b₂ℤ) (b₃ := b₃ℤ) (ℓ₁ := ℓ₁ℤ) (ℓ₂ := ℓ₂ℤ)
    haℤ hb1ℤ hb2ℤ hb3ℤ hℓ1ℤ hℓ12ℤ hℓ2Wℤ hDd1 hDd2 hDd3 hab1 hab2 hab3
    hS1_0 hS1_1 hS1_2 hS1_3 hS2_2 hS2_3 hS3_0 hS3_1 hS3_2 hS3_3
  have hUpsShat_eq :
      (((ℓ₂ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ)) : ℝ) * Shat P.X (aℤ : ℝ) (b₁ℤ : ℝ) (dℤ : ℝ)
        - (((ℓ₁ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ)) : ℝ) * Shat P.X (aℤ : ℝ) (b₂ℤ : ℝ) (dℤ : ℝ)
        + (((ℓ₁ℤ ^ 2 * ℓ₂ℤ ^ 2 : ℤ)) : ℝ) * Shat P.X (aℤ : ℝ) (b₃ℤ : ℝ) (d'ℤ : ℝ)
      = UpsShat := by
    rw [hUpsShat_def, ← hacoh, ← hdcoh, ← hd'coh, ← hb1coh, ← hb2coh, ← hb3coh]
    rw [show ((ℓ₂ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ) : ℝ) = ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 by
          rw [hℓ1coh, hℓ2coh]; push_cast; ring,
        show ((ℓ₁ℤ ^ 2 * (ℓ₂ℤ - ℓ₁ℤ) ^ 2 : ℤ) : ℝ) = ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 by
          rw [hℓ1coh, hℓ2coh]; push_cast; ring,
        show ((ℓ₁ℤ ^ 2 * ℓ₂ℤ ^ 2 : ℤ) : ℝ) = ℓ₁ ^ 2 * ℓ₂ ^ 2 by
          rw [hℓ1coh, hℓ2coh]; push_cast; ring]
  rw [hUpsShat_eq] at hnear
  -- ===== (B) |Υ_Ŝ − Σ_closed(d,b₀)| ≤ ERR via Upsilon_expand =====
  have hexp := Upsilon_expand (X := P.X) (a := a) (b₀ := b₀) (v := v) (d := d)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hX ha hd hℓ1R hℓ12 hb1 hb2 hb3 hwin hwin3 hshiftpos
  rw [← hUpsShat_def] at hexp
  have htgt_eq :
      (P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d))
        = Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ := by
    rw [Sigma_closed]
  rw [htgt_eq] at hexp
  -- ===== (C) ERR ≤ 10¹¹⁰·UpsT via upsilon_err_le =====
  have herr := upsilon_err_le_sharp (P := P) (S := S) (a := a) (b₀ := b₀) (v := v) (d := d)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha ha_hi hℓ1 hℓ12 hℓ2W hdwin hb0 hv hshift2
    hG1 hU1 hΔ1 hH1 hΩU hUbig
  have hexp' : |UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ 10 ^ 111 * UpsT P S :=
    le_trans hexp herr
  -- ===== assemble =====
  have hneg : ∀ x y : ℝ, distInt (x - y) = distInt (y - x) := by
    intro x y
    apply le_antisymm
    · refine le_trans (distInt_le_intDist _ (-round (y - x))) ?_
      have e : (x - y) - ((-round (y - x) : ℤ) : ℝ) = -((y - x) - (round (y - x) : ℝ)) := by
        push_cast; ring
      rw [e, abs_neg]; simp only [distInt, le_refl]
    · refine le_trans (distInt_le_intDist _ (-round (x - y))) ?_
      have e : (y - x) - ((-round (x - y) : ℤ) : ℝ) = -((x - y) - (round (x - y) : ℝ)) := by
        push_cast; ring
      rw [e, abs_neg]; simp only [distInt, le_refl]
  have hsub : distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      ≤ distInt UpsShat + distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - UpsShat) := by
    have hSigeq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        = UpsShat - (UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) := by ring
    rw [hneg (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) UpsShat]
    calc distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
        = distInt (UpsShat - (UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) := by rw [← hSigeq]
      _ ≤ distInt UpsShat + distInt (UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) :=
          distInt_sub_le _ _
  have hSU : distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - UpsShat)
      ≤ |UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
    refine le_trans (distInt_le_intDist _ 0) ?_
    rw [Int.cast_zero, sub_zero, abs_sub_comm]
  calc distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      ≤ distInt UpsShat + distInt (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - UpsShat) := hsub
    _ ≤ distInt UpsShat + |UpsShat - Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
        linarith [hSU]
    _ ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 111 * UpsT P S := by
        linarith [hnear, hexp']

end Squarefree
