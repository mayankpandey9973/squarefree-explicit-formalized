import Squarefree.Lower.Step4VsBand
import Squarefree.Lower.UpsilonMagV2

/-!
# §5 Step-4 `W`-bridge: from the `V_s` squared pin to the `step4_hperv` inputs (writeup 1086–1124)

`step4_hperv` (`Step4Hperv.lean`) consumes three analytic facts about the per-`(s,v)` value
`w` (`= vval r`, `|w| = |v|`) on an `s`-fibre of index `n` (`= |s|`):

* `hvlarge` — the absolute lower bound `10⁴⁷·(ℓ₂(ℓ₂−ℓ₁)/(GΩ⁵))·(D⁴/(Xa)) ≤ |w|`, and
* the two-sided `W ≍ √n/(ΔΩ√Lr)` bridge `hWhi`/`hWlo` (`W = ℓ₁Xa|w|/(D⁴R)`, factor `10⁹`).

This file derives all three from the `V_s` two-sided **squared pin** (`Vs_pin`, with `|s|` set to
`n`) plus the absolute defect lower bound `18·10¹²·Δ²U⁵/Ω³ ≤ |w|` (the `hv2` fibre fact) and the §5
regime.  The scale `Lr` is pinned to **`Lr = ℓ₁·ℓ₂·(ℓ₂−ℓ₁)`**: substituting the pin
`|w| ≍ ΔΩ·√(n/(ℓ₁³ℓ₂(ℓ₂−ℓ₁)))` into `W` and using the scale identities
`D=HΔ, R=HGΩ³/Δ, X=GH⁵` collapses (via `D⁸R² = X²(ΔΩ)⁶`) to
`W ≍ √n/(ΔΩ·√(ℓ₁ℓ₂(ℓ₂−ℓ₁)))`, i.e. `Lr = ℓ₁ℓ₂(ℓ₂−ℓ₁)`, with the residual constants
(`a ∈ [A/5,11A]`, `√(1/150)..√(10⁶)`) absorbed comfortably into `10⁹`.
-/

open Real

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000 in
/-- **§5 Step-4 `W`-bridge (writeup 1086–1124).**  From the `V_s` squared pin (with `|s|` set to the
fibre index `n`) and the absolute defect lower bound `hv2`, in the §5 regime, derive the three
`step4_hperv` inputs `hvlarge`/`hWhi`/`hWlo` with the scale `Lr = ℓ₁·ℓ₂·(ℓ₂−ℓ₁)`. -/
theorem step4_W_from_Vs {a w ℓ₁ ℓ₂ n : ℝ}
    (hG1 : 1 ≤ P.G) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hDeW : (10:ℝ) ^ 15 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (hn1 : 1 ≤ n)
    (hVcut : V₂ P S ≤ |w|)
    (hpin_lo : (1 / 150 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * n) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * w ^ 2)
    (hpin_hi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * w ^ 2 ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * n)) :
    ((10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * a)) ≤ |w|)
    ∧ (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)
        ≤ 10 ^ 9 * (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))))
    ∧ (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
        ≤ 10 ^ 9 * (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R))) := by
  have hGpos := P.G_pos; have hHpos := P.H_pos; have hUpos := P.U_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos; have hXpos := P.X_pos
  have hGne : P.G ≠ 0 := hGpos.ne'; have hHne : P.H ≠ 0 := hHpos.ne'
  have hΔne : S.Δ ≠ 0 := hΔpos.ne'; have hΩne : S.Ω ≠ 0 := hΩpos.ne'
  have hane : a ≠ 0 := ha0.ne'
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ21pos : 0 < ℓ₂ - ℓ₁ := by linarith
  have hDpos : 0 < S.D := by rw [show S.D = P.H * S.Δ from rfl]; positivity
  have hRpos : 0 < S.R := by rw [show S.R = P.H * P.G * S.Ω ^ 3 / S.Δ from rfl]; positivity
  have hLrpos : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  have hnpos : 0 < n := lt_of_lt_of_le one_pos hn1
  have hn_nn : (0:ℝ) ≤ n := hnpos.le
  have hLr_nn : (0:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := hLrpos.le
  have ha_lo2 : S.Δ * S.Ω / 5 ≤ a := ha_lo
  have ha_hi2 : a ≤ 11 * (S.Δ * S.Ω) := ha_hi
  -- the central scale identity `D⁸R² = X²(ΔΩ)⁶`
  have hid : S.D ^ 8 * S.R ^ 2 = P.X ^ 2 * (S.Δ * S.Ω) ^ 6 := by
    rw [show S.D = P.H * S.Δ from rfl, show S.R = P.H * P.G * S.Ω ^ 3 / S.Δ from rfl,
      P.X_eq_G_mul_H_pow_five]
    field_simp
  have hden_W_pos : 0 < S.D ^ 8 * S.R ^ 2 := by positivity
  have hden_T_pos : 0 < (S.Δ * S.Ω) ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by positivity
  -- `a²` window
  have hAAnn : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2 := by positivity
  have ha2hi : a ^ 2 ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2) := by nlinarith [ha_hi2, ha0, hΔpos, hΩpos]
  have ha2lo : S.Δ ^ 2 * S.Ω ^ 2 / 25 ≤ a ^ 2 := by
    nlinarith [ha_lo2, ha0, hΔpos, hΩpos, mul_pos hΔpos hΩpos]
  have hQw_nn : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * w ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hℓ1pos.le 3) hℓ2pos.le) hℓ21pos.le) (sq_nonneg w)
  refine ⟨?_, ?_, ?_⟩
  · -- hvlarge : reduce to the `V₂` floor via its first summand `T1 = (Δ³/H)·G^{5/2}U^{45/2}/Ω⁶`
    refine le_trans ?_ hVcut
    rw [show S.D ^ 4 / (P.X * a) = S.Δ ^ 4 / (P.G * P.H * a) from by
      rw [show S.D = P.H * S.Δ from rfl, P.X_eq_G_mul_H_pow_five]; field_simp]
    have hsqG : (1:ℝ) ≤ Real.sqrt P.G := by
      rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt hG1
    have hsqU : (1:ℝ) ≤ Real.sqrt P.U := by
      rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (le_trans (by norm_num) hUbig)
    -- `V₂ ≥ (Δ³·G²U²²)/(HΩ⁶)`  (drop the √-factors `≥ 1` and the second summand `≥ 0`)
    have hV2t1 : S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22) / (P.H * S.Ω ^ 6) ≤ V₂ P S := by
      rw [V₂]
      have hterm1 : S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22) / (P.H * S.Ω ^ 6)
          ≤ (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
              / S.Ω ^ 6 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hfac : (1:ℝ) ≤ Real.sqrt P.G * Real.sqrt P.U := by
          nlinarith [hsqG, hsqU, Real.sqrt_nonneg P.G, Real.sqrt_nonneg P.U]
        have hRHSeq : (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
              * (P.H * S.Ω ^ 6)
            = (S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22) * S.Ω ^ 6)
                * (Real.sqrt P.G * Real.sqrt P.U) := by
          field_simp [hHpos.ne']
          try ring
        rw [hRHSeq]
        exact le_mul_of_one_le_right (by positivity) hfac
      have hpos2 : 0 ≤ Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω) := by positivity
      linarith [hterm1, hpos2]
    refine le_trans ?_ hV2t1
    have hℓP : ℓ₂ * (ℓ₂ - ℓ₁) ≤ 16900 * (P.G * P.U ^ 5) ^ 2 := by
      have hb : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ2W, hℓ1]
      calc ℓ₂ * (ℓ₂ - ℓ₁) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
            mul_le_mul hℓ2W hb hℓ21pos.le (by positivity)
        _ = 16900 * (P.G * P.U ^ 5) ^ 2 := by ring
    have hU12 : (84500:ℝ) * 10 ^ 47 ≤ P.U ^ 12 := by
      calc (84500:ℝ) * 10 ^ 47 ≤ (10:ℝ) ^ 52 := by norm_num
        _ ≤ (10:ℝ) ^ 396 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 12 := by rw [← pow_mul]
        _ ≤ P.U ^ 12 := pow_le_pow_left₀ (by positivity) hUbig 12
    have hG2 : (1:ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
    -- the cross-multiplied polynomial inequality (margin `U¹² ≥ 5·10⁴⁷`)
    have hpoly : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁)) * S.Δ ^ 4 * (P.H * S.Ω ^ 6)
        ≤ S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22) * ((P.G * S.Ω ^ 5) * (P.G * P.H * a)) := by
      have step1 : (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁)) * S.Δ ^ 4 * (P.H * S.Ω ^ 6)
          ≤ (10:ℝ) ^ 47 * (16900 * (P.G * P.U ^ 5) ^ 2) * S.Δ ^ 4 * (P.H * S.Ω ^ 6) := by
        gcongr
      refine step1.trans ?_
      have step2 : S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22)
            * ((P.G * S.Ω ^ 5) * (P.G * P.H * (S.Δ * S.Ω / 5)))
          ≤ S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22) * ((P.G * S.Ω ^ 5) * (P.G * P.H * a)) := by
        gcongr
      refine le_trans ?_ step2
      have hcomb : (84500:ℝ) * 10 ^ 47 ≤ P.G ^ 2 * P.U ^ 12 := by
        nlinarith [hU12, hG2, pow_pos hUpos 12]
      nlinarith [mul_le_mul_of_nonneg_right hcomb
        (by positivity : (0:ℝ) ≤ P.G ^ 2 * P.U ^ 10 * S.Δ ^ 4 * (P.H * S.Ω ^ 6))]
    -- assemble the fraction inequality from `hpoly`
    rw [show (10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.Δ ^ 4 / (P.G * P.H * a))
        = ((10:ℝ) ^ 47 * (ℓ₂ * (ℓ₂ - ℓ₁)) * S.Δ ^ 4) / ((P.G * S.Ω ^ 5) * (P.G * P.H * a)) from by
        field_simp,
      show S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22) / (P.H * S.Ω ^ 6)
        = (S.Δ ^ 3 * (P.G ^ 2 * P.U ^ 22)) / (P.H * S.Ω ^ 6) from by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    exact hpoly
  · -- hWhi
    have hWsq : (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) ^ 2
        = ℓ₁ ^ 2 * P.X ^ 2 * a ^ 2 * w ^ 2 / (S.D ^ 8 * S.R ^ 2) := by
      rw [div_pow]; congr 1
      · rw [← sq_abs w]; ring
      · ring
    have hT2 : (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) ^ 2
        = n / ((S.Δ * S.Ω) ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hn_nn, Real.sq_sqrt hLr_nn]
    have hmid_hi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * a ^ 2 * w ^ 2 ≤ 10 ^ 18 * n * (S.Δ ^ 2 * S.Ω ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (by linarith [ha2hi] : (0:ℝ) ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2) - a ^ 2) hQw_nn,
        mul_nonneg (by positivity : (0:ℝ) ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2))
          (by linarith [hpin_hi] : (0:ℝ) ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * n)
            - ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * w ^ 2),
        mul_nonneg (mul_nonneg hAAnn hAAnn) hn_nn]
    have hcross_hi : ℓ₁ ^ 2 * P.X ^ 2 * a ^ 2 * w ^ 2 * ((S.Δ * S.Ω) ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
        ≤ 10 ^ 18 * n * (S.D ^ 8 * S.R ^ 2) := by
      rw [hid]
      nlinarith [mul_le_mul_of_nonneg_right hmid_hi
        (show (0:ℝ) ≤ P.X ^ 2 * (S.Δ * S.Ω) ^ 2 by positivity)]
    have hW_nn : (0:ℝ) ≤ ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hℓ1pos.le hXpos.le) ha0.le) (abs_nonneg _))
        (mul_pos (pow_pos hDpos 4) hRpos).le
    have hT_nn : (0:ℝ) ≤ Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) :=
      div_nonneg (Real.sqrt_nonneg _)
        (mul_pos (mul_pos hΔpos hΩpos) (Real.sqrt_pos.mpr hLrpos)).le
    have hRHS_nn : (0:ℝ) ≤ 10 ^ 9 * (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) :=
      mul_nonneg (by norm_num) hT_nn
    have key_hi : (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) ^ 2
        ≤ (10 ^ 9 * (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))) ^ 2 := by
      rw [hWsq, mul_pow, hT2, show ((10:ℝ) ^ 9) ^ 2 = 10 ^ 18 by norm_num, ← mul_div_assoc,
        div_le_div_iff₀ hden_W_pos hden_T_pos]
      exact hcross_hi
    have h := Real.sqrt_le_sqrt key_hi
    rwa [Real.sqrt_sq hW_nn, Real.sqrt_sq hRHS_nn] at h
  · -- hWlo
    have hWsq : (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) ^ 2
        = ℓ₁ ^ 2 * P.X ^ 2 * a ^ 2 * w ^ 2 / (S.D ^ 8 * S.R ^ 2) := by
      rw [div_pow]; congr 1
      · rw [← sq_abs w]; ring
      · ring
    have hT2 : (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) ^ 2
        = n / ((S.Δ * S.Ω) ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hn_nn, Real.sq_sqrt hLr_nn]
    have hmid_lo : n * (S.Δ ^ 2 * S.Ω ^ 2) ^ 2 ≤ 10 ^ 18 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) * a ^ 2 * w ^ 2 := by
      nlinarith [mul_nonneg (by linarith [ha2lo] : (0:ℝ) ≤ a ^ 2 - S.Δ ^ 2 * S.Ω ^ 2 / 25) hQw_nn,
        mul_nonneg (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2 / 25)
          (by linarith [hpin_lo] : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * w ^ 2
            - (1 / 150 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * n)),
        mul_nonneg (mul_nonneg hAAnn hAAnn) hn_nn]
    have hcross_lo : n * (S.D ^ 8 * S.R ^ 2)
        ≤ 10 ^ 18 * (ℓ₁ ^ 2 * P.X ^ 2 * a ^ 2 * w ^ 2)
            * ((S.Δ * S.Ω) ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by
      rw [hid]
      nlinarith [mul_le_mul_of_nonneg_right hmid_lo
        (show (0:ℝ) ≤ P.X ^ 2 * (S.Δ * S.Ω) ^ 2 by positivity)]
    have hW_nn : (0:ℝ) ≤ ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hℓ1pos.le hXpos.le) ha0.le) (abs_nonneg _))
        (mul_pos (pow_pos hDpos 4) hRpos).le
    have hT_nn : (0:ℝ) ≤ Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) :=
      div_nonneg (Real.sqrt_nonneg _)
        (mul_pos (mul_pos hΔpos hΩpos) (Real.sqrt_pos.mpr hLrpos)).le
    have hWRHS_nn : (0:ℝ) ≤ 10 ^ 9 * (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R)) :=
      mul_nonneg (by norm_num) hW_nn
    have key_lo : (Real.sqrt n / (S.Δ * S.Ω * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) ^ 2
        ≤ (10 ^ 9 * (ℓ₁ * P.X * a * |w| / (S.D ^ 4 * S.R))) ^ 2 := by
      rw [mul_pow, hWsq, hT2, show ((10:ℝ) ^ 9) ^ 2 = 10 ^ 18 by norm_num, ← mul_div_assoc,
        div_le_div_iff₀ hden_T_pos hden_W_pos]
      exact hcross_lo
    have h := Real.sqrt_le_sqrt key_lo
    rwa [Real.sqrt_sq hT_nn, Real.sqrt_sq hWRHS_nn] at h

end Squarefree
