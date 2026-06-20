import Squarefree.Opt.StripAux

/-!
# Large-`x` discharge of the Prop 5.1 AUDITED-FAITHFUL regime pack

Helper lemmas discharging, from the ambient context of `dblock_off_strip`'s large-`x`
branch (band lower edge `G^{-1/4}U^{-3/4} ≤ Ω`, `Ω ≤ U`, `Δ ≥ X^{1/100}`, the large-`x`
edge `G¹⁷Ω⁻²⁶X^{Cu·u} ≤ x`, the `u`-budget `100u + 20g ≤ 1/200`, and the threaded
`X`-largeness `10³³ ≤ U`), the regime-pack hypotheses of `prop_5_1` (regime ruling
2026-06-10): the band floor `1 ≤ GU³Ω⁴`, `U⁹ ≤ G⁷H²`, `10¹⁵·G⁴U²⁰ ≤ Δ`,
`10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴`, the Step-4 half-width budget `10⁷⁰·(1/Δ)G⁴U¹⁵/Ω⁵ ≤ 1/2`,
`60Ω ≤ H`, and the `N`-free log cap (the Step-3 `hlogcap` evaluated at the `hNenv` max cap).
-/

namespace Squarefree.StripAux

open Squarefree

/-- Band lower edge to the inverse fifth power: `1/Ω⁵ ≤ G^{5/4}·U^{15/4}`. -/
theorem inv_omega5_le (P : Globals) (S : Scale P)
    (hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω) :
    1 / S.Ω ^ 5 ≤ P.G ^ (5/4 : ℝ) * P.U ^ (15/4 : ℝ) := by
  have hG := P.G_pos; have hU := P.U_pos; have hΩ := S.Ω_pos
  have hb_pos : (0:ℝ) < P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) := by
    have := Real.rpow_pos_of_pos hG (-1/4 : ℝ)
    have := Real.rpow_pos_of_pos hU (-3/4 : ℝ)
    positivity
  have hb5 : (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ^ 5
      = P.G ^ (-5/4 : ℝ) * P.U ^ (-15/4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (P.G ^ (-1/4 : ℝ)) 5,
        ← Real.rpow_natCast (P.U ^ (-3/4 : ℝ)) 5,
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hU.le]
    norm_num
  have hΩ5 : P.G ^ (-5/4 : ℝ) * P.U ^ (-15/4 : ℝ) ≤ S.Ω ^ 5 := by
    rw [← hb5]; exact pow_le_pow_left₀ hb_pos.le hband6 5
  rw [div_le_iff₀ (by positivity)]
  have hid : (P.G ^ (5/4 : ℝ) * P.U ^ (15/4 : ℝ))
      * (P.G ^ (-5/4 : ℝ) * P.U ^ (-15/4 : ℝ)) = 1 := by
    rw [show (P.G ^ (5/4 : ℝ) * P.U ^ (15/4 : ℝ))
          * (P.G ^ (-5/4 : ℝ) * P.U ^ (-15/4 : ℝ))
        = (P.G ^ (5/4 : ℝ) * P.G ^ (-5/4 : ℝ)) * (P.U ^ (15/4 : ℝ) * P.U ^ (-15/4 : ℝ)) by ring,
      ← Real.rpow_add hG, ← Real.rpow_add hU]
    norm_num
  calc (1:ℝ) = (P.G ^ (5/4 : ℝ) * P.U ^ (15/4 : ℝ))
        * (P.G ^ (-5/4 : ℝ) * P.U ^ (-15/4 : ℝ)) := hid.symm
    _ ≤ (P.G ^ (5/4 : ℝ) * P.U ^ (15/4 : ℝ)) * S.Ω ^ 5 :=
        mul_le_mul_of_nonneg_left hΩ5 (by positivity)

/-- Band lower edge ⟹ the faithful band primitive `1 ≤ G·U³·Ω⁴`. -/
theorem regime_band_one (P : Globals) (S : Scale P)
    (hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω) :
    1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := by
  have hG := P.G_pos; have hU := P.U_pos; have hΩ := S.Ω_pos
  have hb_pos : (0:ℝ) < P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) := by
    have := Real.rpow_pos_of_pos hG (-1/4 : ℝ)
    have := Real.rpow_pos_of_pos hU (-3/4 : ℝ)
    positivity
  have hb4 : (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ^ 4
      = P.G ^ (-1 : ℝ) * P.U ^ (-3 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (P.G ^ (-1/4 : ℝ)) 4,
        ← Real.rpow_natCast (P.U ^ (-3/4 : ℝ)) 4,
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hU.le]
    norm_num
  have hΩ4 : P.G ^ (-1 : ℝ) * P.U ^ (-3 : ℝ) ≤ S.Ω ^ 4 := by
    rw [← hb4]; exact pow_le_pow_left₀ hb_pos.le hband6 4
  have e1 : P.G * P.G ^ (-1 : ℝ) = 1 := by
    nth_rewrite 1 [← Real.rpow_one P.G]
    rw [← Real.rpow_add hG]; norm_num
  have e2 : P.U ^ 3 * P.U ^ (-3 : ℝ) = 1 := by
    rw [← Real.rpow_natCast P.U 3, ← Real.rpow_add hU]; norm_num
  calc (1:ℝ) = (P.G * P.G ^ (-1 : ℝ)) * (P.U ^ 3 * P.U ^ (-3 : ℝ)) := by rw [e1, e2]; norm_num
    _ = P.G * P.U ^ 3 * (P.G ^ (-1 : ℝ) * P.U ^ (-3 : ℝ)) := by ring
    _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := mul_le_mul_of_nonneg_left hΩ4 (by positivity)

/-- Regime calibration `U⁹ ≤ G⁷·H²` from `u ≤ 1/100` (exponents: `9u ≤ 2/5 + 33g/5`). -/
theorem regime_UH (P : Globals) (hX : 1 ≤ P.X) (hg0 : 0 ≤ P.g) (hu2 : P.u ≤ 1/100) :
    P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2 := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hU9 : P.U ^ 9 = P.X ^ (P.u * 9) := by
    rw [Globals.U, ← Real.rpow_natCast (P.X ^ P.u) 9, ← Real.rpow_mul hX0.le]
    norm_num
  have hGH : P.G ^ 7 * P.H ^ 2 = P.X ^ (P.g * 7 + (1 - P.g) / 5 * 2) := by
    rw [Globals.G, Globals.H, ← Real.rpow_natCast (P.X ^ P.g) 7,
        ← Real.rpow_natCast (P.X ^ ((1 - P.g) / 5)) 2,
        ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    norm_num
  rw [hU9, hGH]
  apply Real.rpow_le_rpow_of_exponent_le hX
  linarith

/-- Regime calibration `10¹⁵·G⁴U²⁰ ≤ Δ` from the `u`-budget, `10³³ ≤ U` and `X^{1/100} ≤ Δ`. -/
theorem regime_DeW (P : Globals) (S : Scale P) (hX : 1 ≤ P.X) (hg0 : 0 ≤ P.g)
    (hu0 : 0 < P.u) (hbu : 100 * P.u + 20 * P.g ≤ 1/200)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U) (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ) :
    10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hU := P.U_pos
  have hGU : P.G ^ 4 * P.U ^ 20 = P.X ^ (P.g * 4 + P.u * 20) := by
    rw [Globals.G, Globals.U, ← Real.rpow_natCast (P.X ^ P.g) 4,
        ← Real.rpow_natCast (P.X ^ P.u) 20,
        ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    norm_num
  have h15 : (10:ℝ) ^ 27 ≤ P.U := le_trans (by norm_num) hUbig
  calc 10 ^ 27 * (P.G ^ 4 * P.U ^ 20)
      ≤ P.U * (P.G ^ 4 * P.U ^ 20) := by
        apply mul_le_mul_of_nonneg_right h15 (by positivity)
    _ = P.X ^ (P.u + (P.g * 4 + P.u * 20)) := by
        rw [hGU, Globals.U, ← Real.rpow_add hX0]
    _ ≤ P.X ^ (1/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ ≤ S.Δ := hΔlong

/-- `60Ω ≤ H` from `Ω ≤ U`, `10³³ ≤ U` and the exponent gap `2u ≤ (1-g)/5`. -/
theorem regime_omega_H (P : Globals) (S : Scale P) (hX : 1 ≤ P.X)
    (hg1 : P.g ≤ 1/4000) (hu2 : P.u ≤ 1/100) (hΩU : S.Ω ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U) : 60 * S.Ω ≤ P.H := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hU := P.U_pos
  have hHU : P.H = P.U * P.X ^ ((1 - P.g) / 5 - P.u) := by
    rw [Globals.H, Globals.U, ← Real.rpow_add hX0]
    congr 1; ring
  have hgap : P.u ≤ (1 - P.g) / 5 - P.u := by linarith
  have h60 : (60:ℝ) ≤ P.X ^ ((1 - P.g) / 5 - P.u) := by
    calc (60:ℝ) ≤ 10 ^ 33 := by norm_num
      _ ≤ P.U := hUbig
      _ = P.X ^ P.u := rfl
      _ ≤ P.X ^ ((1 - P.g) / 5 - P.u) := Real.rpow_le_rpow_of_exponent_le hX hgap
  calc 60 * S.Ω ≤ 60 * P.U := mul_le_mul_of_nonneg_left hΩU (by norm_num)
    _ ≤ P.X ^ ((1 - P.g) / 5 - P.u) * P.U := mul_le_mul_of_nonneg_right h60 hU.le
    _ = P.H := by rw [hHU]; ring

/-- `10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴` from the large-`x` edge (`Δ² ≤ H·G^{-17}Ω²⁶X^{-Cu·u}` via
`delta_sq_edge_le`), `Ω ≤ U`, `Cu ≥ 232` and `10³³ ≤ U`. -/
theorem regime_Hbig (P : Globals) (S : Scale P) (Cu : ℝ) (hCu : (232:ℝ) ≤ Cu)
    (hX : 1 ≤ P.X) (hu0 : 0 < P.u) (hG1 : 1 ≤ P.G) (hΩU : S.Ω ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hlarge : P.G ^ 16 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) ≤ S.x) :
    10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14 := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hU := P.U_pos; have hH := P.H_pos
  have hΔp := S.Δ_pos; have hΩ := S.Ω_pos
  -- the edge: Δ² ≤ H·(G^{-17}Ω²⁶X^{-Cu·u}), then weaken `G^{-17} ≤ G^{-5/2}`
  have hΔ2 := delta_sq_edge_le P S Cu hlarge
  have hΔ2' : S.Δ ^ 2 ≤ P.H * (P.G ^ (-5/2 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))) := by
    refine hΔ2.trans (mul_le_mul_of_nonneg_left ?_ hH.le)
    have hGw : P.G ^ (-16 : ℝ) ≤ P.G ^ (-5/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hG1 (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hGw (Real.rpow_nonneg hΩ.le _))
      (Real.rpow_nonneg hX0.le _)
  -- square it: Δ⁴ ≤ H²·(G^{-5}Ω⁵²X^{-2Cu·u})
  have hEsq : (P.G ^ (-5/2 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))) ^ 2
      = P.G ^ (-5 : ℝ) * S.Ω ^ (52 : ℝ) * P.X ^ (-(Cu * P.u) * 2) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (P.G ^ (-5/2 : ℝ)) 2,
        ← Real.rpow_natCast (S.Ω ^ (26 : ℝ)) 2, ← Real.rpow_natCast (P.X ^ (-(Cu * P.u))) 2,
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le, ← Real.rpow_mul hX0.le]
    norm_num
  have hΔ4 : S.Δ ^ 4 ≤ P.H ^ 2 * (P.G ^ (-5 : ℝ) * S.Ω ^ (52 : ℝ) * P.X ^ (-(Cu * P.u) * 2)) := by
    have h4 : S.Δ ^ 4 = (S.Δ ^ 2) ^ 2 := by ring
    rw [h4, ← hEsq, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hΔ2' 2
  -- the scalar smallness: 10¹¹²·Ω³⁸U⁴⁵X^{-2Cu·u} ≤ 1
  have hsmall : (10:ℝ) ^ 121 * (S.Ω ^ 38 * P.U ^ 45 * P.X ^ (-(Cu * P.u) * 2)) ≤ 1 := by
    have hΩ38 : S.Ω ^ 38 ≤ P.U ^ 38 := pow_le_pow_left₀ hΩ.le hΩU 38
    have hU83 : P.U ^ 38 * P.U ^ 45 = P.X ^ (P.u * 83) := by
      rw [Globals.U, ← pow_add, ← Real.rpow_natCast (P.X ^ P.u) 83, ← Real.rpow_mul hX0.le]
      norm_num
    have hexp : P.X ^ (P.u * 83) * P.X ^ (-(Cu * P.u) * 2) ≤ P.X ^ (P.u * (-381 : ℝ)) := by
      rw [← Real.rpow_add hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX
      linarith only [mul_le_mul_of_nonneg_left hCu hu0.le]
    have hXneg : P.X ^ (P.u * (-381 : ℝ)) ≤ ((10:ℝ) ^ 33) ^ (-381 : ℝ) := by
      rw [Real.rpow_mul hX0.le]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hUbig (by norm_num)
    have hconst : (10:ℝ) ^ 121 * ((10:ℝ) ^ 33) ^ (-381 : ℝ) ≤ 1 := by
      have he : ((10:ℝ) ^ 33) ^ (-381 : ℝ) = (((10:ℝ) ^ 33) ^ (381 : ℕ))⁻¹ := by
        rw [← Real.rpow_natCast ((10:ℝ) ^ 33) 381, ← Real.rpow_neg (by positivity)]
        norm_num
      rw [he, ← pow_mul, ← div_eq_mul_inv, div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    calc (10:ℝ) ^ 121 * (S.Ω ^ 38 * P.U ^ 45 * P.X ^ (-(Cu * P.u) * 2))
        ≤ (10:ℝ) ^ 121 * (P.U ^ 38 * P.U ^ 45 * P.X ^ (-(Cu * P.u) * 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hΩ38 (by positivity)) (Real.rpow_nonneg hX0.le _)
      _ = (10:ℝ) ^ 121 * (P.X ^ (P.u * 83) * P.X ^ (-(Cu * P.u) * 2)) := by rw [hU83]
      _ ≤ (10:ℝ) ^ 121 * ((10:ℝ) ^ 33) ^ (-381 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_trans hexp hXneg
      _ ≤ 1 := hconst
  -- assemble
  have hΩ52 : S.Ω ^ (52:ℝ) = S.Ω ^ 14 * S.Ω ^ 38 := by
    rw [← pow_add, ← Real.rpow_natCast S.Ω 52]
    norm_num
  have hG5 : P.G ^ (-5 : ℝ) * P.G ^ 5 = 1 := by
    rw [← Real.rpow_natCast P.G 5, ← Real.rpow_add hG]
    norm_num
  calc (10:ℝ) ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45)
      ≤ (10:ℝ) ^ 121 * (P.H ^ 2 * (P.G ^ (-5 : ℝ) * S.Ω ^ (52 : ℝ) * P.X ^ (-(Cu * P.u) * 2))
          * P.G ^ 5 * P.U ^ 45) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hΔ4 (by positivity)) (by positivity)
    _ = P.H ^ 2 * S.Ω ^ 14 * ((10:ℝ) ^ 121 * (S.Ω ^ 38 * P.U ^ 45 * P.X ^ (-(Cu * P.u) * 2)))
          * (P.G ^ (-5 : ℝ) * P.G ^ 5) := by
        rw [hΩ52]; ring
    _ = P.H ^ 2 * S.Ω ^ 14 * ((10:ℝ) ^ 121 * (S.Ω ^ 38 * P.U ^ 45
          * P.X ^ (-(Cu * P.u) * 2))) := by rw [hG5, mul_one]
    _ ≤ P.H ^ 2 * S.Ω ^ 14 * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = P.H ^ 2 * S.Ω ^ 14 := mul_one _

/-- Step-4 witness-defect half-width budget `10⁷⁰·(1/Δ)G⁴U¹⁵/Ω⁵ ≤ 1/2` (exact
`Step4Capstone` form) from the band lower edge, the `u`-budget, `10³³ ≤ U`, `X^{1/100} ≤ Δ`. -/
theorem regime_delta_bud (P : Globals) (S : Scale P)
    (hX : 1 ≤ P.X) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hbu : 100 * P.u + 20 * P.g ≤ 1/200)
    (hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ) :
    10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) ≤ 1 / 2 := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hU := P.U_pos; have hΩ := S.Ω_pos; have hΔp := S.Δ_pos
  have hinvΩ := inv_omega5_le P S hband6
  have hinvΔ : 1 / S.Δ ≤ P.X ^ (-(1/100) : ℝ) := by
    rw [Real.rpow_neg hX0.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hX0 _) hΔlong
  have hG4 : P.G ^ 4 = P.X ^ (P.g * 4) := by
    rw [Globals.G, ← Real.rpow_natCast (P.X ^ P.g) 4, ← Real.rpow_mul hX0.le]; norm_num
  have hU15 : P.U ^ 15 = P.X ^ (P.u * 15) := by
    rw [Globals.U, ← Real.rpow_natCast (P.X ^ P.u) 15, ← Real.rpow_mul hX0.le]; norm_num
  have hG54 : P.G ^ (5/4 : ℝ) = P.X ^ (P.g * (5/4)) := by
    rw [Globals.G, ← Real.rpow_mul hX0.le]
  have hU154 : P.U ^ (15/4 : ℝ) = P.X ^ (P.u * (15/4)) := by
    rw [Globals.U, ← Real.rpow_mul hX0.le]
  calc 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5)
      = 10 ^ 70 * ((1 / S.Δ) * (P.G ^ 4 * P.U ^ 15) * (1 / S.Ω ^ 5)) := by ring
    _ ≤ 10 ^ 70 * (P.X ^ (-(1/100) : ℝ) * (P.G ^ 4 * P.U ^ 15)
          * (P.G ^ (5/4 : ℝ) * P.U ^ (15/4 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hinvΔ (by positivity)) hinvΩ
          (by positivity) (by positivity)
    _ = 10 ^ 70 * P.X ^ (-(1/100) + (P.g * 4 + P.u * 15) + (P.g * (5/4) + P.u * (15/4)) : ℝ) := by
        rw [hG4, hU15, hG54, hU154, ← Real.rpow_add hX0, ← Real.rpow_add hX0,
            ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    _ ≤ 10 ^ 70 * P.X ^ (P.u * (-3) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hX
        linarith
    _ ≤ 10 ^ 70 * ((10:ℝ) ^ 33) ^ (-3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.rpow_mul hX0.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hUbig (by norm_num)
    _ ≤ 1 / 2 := by
        rw [show ((10:ℝ) ^ 33) ^ (-3 : ℝ) = (((10:ℝ) ^ 33) ^ (3 : ℕ))⁻¹ by
          rw [← Real.rpow_natCast ((10:ℝ) ^ 33) 3, ← Real.rpow_neg (by positivity)]; norm_num]
        rw [← pow_mul]
        norm_num

/-- The `N`-free log cap: the Step-3 `hlogcap` evaluated at the `hNenv` max cap
`10⁹⁰·(Na + Nb + Nc)`.  Each cap monomial is `≤ X`, so the argument is `≤ 3·10⁹⁰·X ≤ X²`,
and `log(X²) + 1 ≤ 3U ≤ U^{57/4} ≤ G³U¹⁵√Δ·Ω` via the band lower edge and `10³³ ≤ U`. -/
theorem regime_logcap (P : Globals) (S : Scale P)
    (hX : 1 ≤ P.X) (hg0 : 0 ≤ P.g) (hg1 : P.g ≤ 1/4000) (hu0 : 0 < P.u) (hu2 : P.u ≤ 1/100)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω) (hΩU : S.Ω ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hlog : Real.log P.X ≤ P.X ^ P.u) :
    Real.log (10 ^ 90 * (P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) / S.Ω ^ 5)
        + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5:ℝ)/2))
        + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) + 1
      ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have _ := hg0
  have hG := P.G_pos; have hU := P.U_pos; have hΩ := S.Ω_pos
  have hΔp := S.Δ_pos; have hH := P.H_pos
  have hinvΩ := inv_omega5_le P S hband6
  -- cap monomial 1: `Na ≤ X`
  have hNa : P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) / S.Ω ^ 5 ≤ P.X := by
    have h1 : P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) / S.Ω ^ 5
        ≤ P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) * (P.G ^ (5/4:ℝ) * P.U ^ (15/4:ℝ)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvΩ (by positivity)
    refine h1.trans ?_
    have hcoll : P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) * (P.G ^ (5/4:ℝ) * P.U ^ (15/4:ℝ))
        = P.X ^ (P.g * ((9:ℝ)/2 + 5/4) + P.u * ((55:ℝ)/2 + 15/4)) := by
      rw [show P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) * (P.G ^ (5/4:ℝ) * P.U ^ (15/4:ℝ))
            = (P.G ^ ((9:ℝ)/2) * P.G ^ (5/4:ℝ)) * (P.U ^ ((55:ℝ)/2) * P.U ^ (15/4:ℝ)) by ring,
          ← Real.rpow_add hG, ← Real.rpow_add hU, Globals.G, Globals.U,
          ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    rw [hcoll]
    calc P.X ^ (P.g * ((9:ℝ)/2 + 5/4) + P.u * ((55:ℝ)/2 + 15/4)) ≤ P.X ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX (by linarith only [hg1, hu2])
      _ = P.X := Real.rpow_one _
  -- cap monomial 2: `Nb ≤ X`
  have hNb : P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5:ℝ)/2) ≤ P.X := by
    have hΔ52 : (1:ℝ) ≤ S.Δ ^ ((5:ℝ)/2) := Real.one_le_rpow hΔ1 (by norm_num)
    have h1 : P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5:ℝ)/2)
        ≤ P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 := div_le_self (by positivity) hΔ52
    refine h1.trans ?_
    have hΩ2 : S.Ω ^ 2 ≤ P.U ^ 2 := pow_le_pow_left₀ hΩ.le hΩU 2
    have h2 : P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 ≤ P.H * P.G ^ 4 * P.U ^ 2 * P.U ^ 15 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΩ2 (by positivity)) (by positivity)
    refine h2.trans ?_
    have hcoll : P.H * P.G ^ 4 * P.U ^ 2 * P.U ^ 15
        = P.X ^ ((1 - P.g)/5 + P.g * 4 + P.u * 2 + P.u * 15) := by
      rw [Globals.H, Globals.G, Globals.U,
          ← Real.rpow_natCast (P.X ^ P.g) 4, ← Real.rpow_natCast (P.X ^ P.u) 2,
          ← Real.rpow_natCast (P.X ^ P.u) 15,
          ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
          ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
      norm_num
    rw [hcoll]
    calc P.X ^ ((1 - P.g)/5 + P.g * 4 + P.u * 2 + P.u * 15) ≤ P.X ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ = P.X := Real.rpow_one _
  -- cap monomial 3: `Nc ≤ X`
  have hNc : P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 ≤ P.X := by
    have h1 : P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5
        ≤ P.G ^ 2 * P.U ^ 15 * (P.G ^ (5/4:ℝ) * P.U ^ (15/4:ℝ)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvΩ (by positivity)
    refine h1.trans ?_
    have hcoll : P.G ^ 2 * P.U ^ 15 * (P.G ^ (5/4:ℝ) * P.U ^ (15/4:ℝ))
        = P.X ^ (P.g * (((2:ℕ):ℝ) + 5/4) + P.u * (((15:ℕ):ℝ) + 15/4)) := by
      rw [show P.G ^ 2 * P.U ^ 15 * (P.G ^ (5/4:ℝ) * P.U ^ (15/4:ℝ))
            = (P.G ^ 2 * P.G ^ (5/4:ℝ)) * (P.U ^ 15 * P.U ^ (15/4:ℝ)) by ring,
          ← Real.rpow_natCast P.G 2, ← Real.rpow_natCast P.U 15,
          ← Real.rpow_add hG, ← Real.rpow_add hU, Globals.G, Globals.U,
          ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    rw [hcoll]
    calc P.X ^ (P.g * (((2:ℕ):ℝ) + 5/4) + P.u * (((15:ℕ):ℝ) + 15/4)) ≤ P.X ^ (1:ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hX
          push_cast
          linarith only [hg1, hu2]
      _ = P.X := Real.rpow_one _
  -- the argument is ≤ X²
  set E : ℝ := 10 ^ 90 * (P.G ^ ((9:ℝ)/2) * P.U ^ ((55:ℝ)/2) / S.Ω ^ 5)
      + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5:ℝ)/2))
      + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) with hEdef
  have hEpos : (0:ℝ) < E := by
    rw [hEdef]
    have h2 : (0:ℝ) < S.Δ ^ ((5:ℝ)/2) := Real.rpow_pos_of_pos hΔp _
    have h3 : (0:ℝ) < P.G ^ ((9:ℝ)/2) := Real.rpow_pos_of_pos hG _
    have h4 : (0:ℝ) < P.U ^ ((55:ℝ)/2) := Real.rpow_pos_of_pos hU _
    positivity
  have h3X : (3:ℝ) * 10 ^ 90 ≤ P.X := by
    have h99 : (3:ℝ) * 10 ^ 90 ≤ ((10:ℝ) ^ 33) ^ (3:ℕ) := by norm_num
    have hU3 : ((10:ℝ) ^ 33) ^ (3:ℕ) ≤ P.U ^ (3:ℕ) := pow_le_pow_left₀ (by positivity) hUbig 3
    have hXu3 : P.U ^ (3:ℕ) = P.X ^ (P.u * 3) := by
      rw [Globals.U, ← Real.rpow_natCast (P.X ^ P.u) 3, ← Real.rpow_mul hX0.le]
      norm_num
    calc (3:ℝ) * 10 ^ 90 ≤ ((10:ℝ) ^ 33) ^ (3:ℕ) := h99
      _ ≤ P.U ^ (3:ℕ) := hU3
      _ = P.X ^ (P.u * 3) := hXu3
      _ ≤ P.X ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ = P.X := Real.rpow_one _
  have hEX2 : E ≤ P.X ^ (2:ℕ) := by
    rw [hEdef]
    have hsum := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hNa (by positivity : (0:ℝ) ≤ 10 ^ 90))
      (mul_le_mul_of_nonneg_left hNb (by positivity : (0:ℝ) ≤ 10 ^ 90)))
      (mul_le_mul_of_nonneg_left hNc (by positivity : (0:ℝ) ≤ 10 ^ 90))
    refine hsum.trans ?_
    rw [show (10:ℝ) ^ 90 * P.X + 10 ^ 90 * P.X + 10 ^ 90 * P.X = (3 * 10 ^ 90) * P.X by ring,
        pow_two]
    exact mul_le_mul_of_nonneg_right h3X hX0.le
  -- log of the argument
  have hlogE : Real.log E ≤ 2 * Real.log P.X := by
    have h := Real.log_le_log hEpos hEX2
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hXu1 : (1:ℝ) ≤ P.X ^ P.u := Real.one_le_rpow hX hu0.le
  have hLHS : Real.log E + 1 ≤ 3 * P.X ^ P.u := by
    have hlogX0 : 0 ≤ Real.log P.X := Real.log_nonneg hX
    linarith [hlogE, hlog, hXu1]
  -- the RHS dominates `U^{57/4}`
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt S.Δ := Real.one_le_sqrt.mpr hΔ1
  have hid : P.G ^ 3 * P.U ^ 15 * (P.G ^ (-1/4:ℝ) * P.U ^ (-3/4:ℝ))
      = P.G ^ ((11:ℝ)/4) * P.U ^ ((57:ℝ)/4) := by
    rw [show P.G ^ 3 * P.U ^ 15 * (P.G ^ (-1/4:ℝ) * P.U ^ (-3/4:ℝ))
          = (P.G ^ 3 * P.G ^ (-1/4:ℝ)) * (P.U ^ 15 * P.U ^ (-3/4:ℝ)) by ring,
        ← Real.rpow_natCast P.G 3, ← Real.rpow_natCast P.U 15,
        ← Real.rpow_add hG, ← Real.rpow_add hU]
    norm_num
  have hRHS : P.G ^ ((11:ℝ)/4) * P.U ^ ((57:ℝ)/4)
      ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω := by
    rw [← hid]
    calc P.G ^ 3 * P.U ^ 15 * (P.G ^ (-1/4:ℝ) * P.U ^ (-3/4:ℝ))
        ≤ P.G ^ 3 * P.U ^ 15 * S.Ω := mul_le_mul_of_nonneg_left hband6 (by positivity)
      _ ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω := by
          apply mul_le_mul_of_nonneg_right _ hΩ.le
          exact le_mul_of_one_le_right (by positivity) hsqrt1
  -- `3U ≤ U^{57/4}`
  have h3U : 3 * P.X ^ P.u ≤ P.U ^ ((57:ℝ)/4) := by
    have hU53 : (3:ℝ) ≤ P.U ^ ((53:ℝ)/4) := by
      calc (3:ℝ) ≤ 10 ^ 33 := by norm_num
        _ ≤ P.U := hUbig
        _ = P.U ^ (1:ℝ) := (Real.rpow_one _).symm
        _ ≤ P.U ^ ((53:ℝ)/4) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have hsplit : P.U ^ ((57:ℝ)/4) = P.U ^ ((53:ℝ)/4) * P.U := by
      rw [show ((57:ℝ)/4) = (53:ℝ)/4 + 1 by norm_num, Real.rpow_add hU, Real.rpow_one]
    rw [hsplit, show (3:ℝ) * P.X ^ P.u = 3 * P.U from rfl]
    exact mul_le_mul_of_nonneg_right hU53 hU.le
  -- chain
  calc Real.log E + 1 ≤ 3 * P.X ^ P.u := hLHS
    _ ≤ P.U ^ ((57:ℝ)/4) := h3U
    _ ≤ P.G ^ ((11:ℝ)/4) * P.U ^ ((57:ℝ)/4) :=
        le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hG1 (by norm_num))
    _ ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω := hRHS

end Squarefree.StripAux
