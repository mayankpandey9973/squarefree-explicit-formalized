import Squarefree.Structure.Fiber
import Squarefree.Lower.Prop51
import Squarefree.Upper.Regime
import Squarefree.Bracket.BoxSum
import Squarefree.Budget
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §8/§9 helper lemmas for `dblock_bound` (`Opt/Strip.lean`)

Reusable budget/exponent pieces for the per-Ω block bound:

* `fiber_factor_budget` — in the band `Ω ≥ c·G^{-1/4}U^{-3/4}`, the Prop 3.2 fiber factor
  `1 + (Δ/A)^{8/3}G^{-2/3} = 1 + Ω^{-8/3}G^{-2/3} ≤ (1+c^{-8/3})·X^{2u}`.
* `dblock_le_sum_Ra` — `𝐃(Ω) ≤ X^{O(u)} · Σ_{a∼A} #ℛ_a` from `prop_3_2_fiber`, providing the
  per-`a` set `RaOf a`.
* `xpow_*`/`rpow_mono_*` — small rpow-algebra wrappers used by the regime exponent budgets.

These keep `Opt/Strip.lean`'s elaboration small.  See `explicit_writeup.md` §8 (2020–2079),
§9 (2083–2221) and `math_audit.md` §8/§9.
-/

open Classical Finset

namespace Squarefree.StripAux

open Squarefree

/-- `(Δ/A)^{8/3} = Ω^{-8/3}` (since `A = ΔΩ`), as a positive rpow identity. -/
theorem deltaA_pow_eq (P : Globals) (S : Scale P) :
    (S.Δ / S.A) ^ (8/3 : ℝ) = S.Ω ^ (-8/3 : ℝ) := by
  have hΩ := S.Ω_pos
  have hΔ := S.Δ_pos
  have hAeq : S.Δ / S.A = S.Ω⁻¹ := by
    unfold Scale.A
    rw [inv_eq_one_div, div_eq_div_iff (by positivity) (ne_of_gt hΩ)]
    ring
  rw [hAeq, ← Real.rpow_neg_one S.Ω, ← Real.rpow_mul hΩ.le]
  congr 1
  norm_num

/-- `Ω^{-8/3}·G^{-2/3} ≤ c^{-8/3}·X^{2u}` in the band `c·G^{-1/4}U^{-3/4} ≤ Ω`. -/
theorem fiber_term_le (P : Globals) (S : Scale P) (c : ℝ) (hc : 0 < c)
    (hband : c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    S.Ω ^ (-8/3 : ℝ) * P.G ^ (-2/3 : ℝ) ≤ c ^ (-8/3 : ℝ) * P.X ^ (2 * P.u) := by
  have hΩ := S.Ω_pos
  have hG := P.G_pos
  have hU := P.U_pos
  have hX := P.X_pos
  -- lower bound is positive
  have hlb_pos : 0 < c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) := by
    have := Real.rpow_pos_of_pos hG (-1/4 : ℝ)
    have := Real.rpow_pos_of_pos hU (-3/4 : ℝ)
    positivity
  -- raise the band to the (8/3) power (positive exponent ⇒ monotone)
  have hpow : (c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) ^ (8/3 : ℝ) ≤ S.Ω ^ (8/3 : ℝ) :=
    Real.rpow_le_rpow hlb_pos.le hband (by norm_num)
  -- Ω^{-8/3} = (Ω^{8/3})⁻¹ ≤ (lb^{8/3})⁻¹
  have hΩneg : S.Ω ^ (-8/3 : ℝ) = (S.Ω ^ (8/3 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hΩ.le]; norm_num
  have hlbneg : (c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) ^ (8/3 : ℝ)
      = c ^ (8/3 : ℝ) * (P.G ^ (-2/3 : ℝ) * P.U ^ (-2 : ℝ)) := by
    rw [Real.mul_rpow hc.le (by positivity)]
    rw [Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hU.le _)]
    rw [← Real.rpow_mul hG.le, ← Real.rpow_mul hU.le]
    norm_num
  have hΩle : S.Ω ^ (-8/3 : ℝ) ≤ (c ^ (8/3 : ℝ) * (P.G ^ (-2/3 : ℝ) * P.U ^ (-2 : ℝ)))⁻¹ := by
    rw [hΩneg, ← hlbneg]
    exact inv_anti₀ (Real.rpow_pos_of_pos hlb_pos _) hpow
  -- multiply by G^{-2/3} > 0
  have hG23 : 0 < P.G ^ (-2/3 : ℝ) := Real.rpow_pos_of_pos hG _
  calc S.Ω ^ (-8/3 : ℝ) * P.G ^ (-2/3 : ℝ)
      ≤ (c ^ (8/3 : ℝ) * (P.G ^ (-2/3 : ℝ) * P.U ^ (-2 : ℝ)))⁻¹ * P.G ^ (-2/3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hΩle hG23.le
    _ = c ^ (-8/3 : ℝ) * P.X ^ (2 * P.u) := by
        rw [show c ^ (-8/3 : ℝ) = (c ^ (8/3 : ℝ))⁻¹ by rw [← Real.rpow_neg hc.le]; norm_num]
        have hUval : P.U ^ (-2 : ℝ) = (P.X ^ (2 * P.u))⁻¹ := by
          rw [Globals.U, ← Real.rpow_mul hX.le, ← Real.rpow_neg hX.le]
          congr 1; ring
        rw [hUval]
        field_simp

/-- **Fiber-factor budget.** In the band `c·G^{-1/4}U^{-3/4} ≤ Ω`, with `X ≥ 1`, `u > 0`,
`1 + (Δ/A)^{8/3}G^{-2/3} ≤ (1 + c^{-8/3})·X^{2u}`. -/
theorem fiber_factor_budget (P : Globals) (S : Scale P) (c : ℝ) (hc : 0 < c)
    (hX : 1 ≤ P.X) (hu : 0 < P.u)
    (hband : c * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)
      ≤ (1 + c ^ (-8/3 : ℝ)) * P.X ^ (2 * P.u) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hone : (1:ℝ) ≤ P.X ^ (2 * P.u) :=
    Real.one_le_rpow hX (by positivity)
  rw [deltaA_pow_eq]
  have hterm := fiber_term_le P S c hc hband
  have hc23 : 0 < c ^ (-8/3 : ℝ) := Real.rpow_pos_of_pos hc _
  calc 1 + S.Ω ^ (-8/3 : ℝ) * P.G ^ (-2/3 : ℝ)
      ≤ P.X ^ (2 * P.u) + c ^ (-8/3 : ℝ) * P.X ^ (2 * P.u) := by linarith [hterm, hone]
    _ = (1 + c ^ (-8/3 : ℝ)) * P.X ^ (2 * P.u) := by ring

end Squarefree.StripAux
