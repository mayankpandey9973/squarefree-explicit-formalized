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

/-! ### Small-Ω budget arithmetic for `dblock_small_omega`

Below we collect the per-monomial budget bounds used to discard the small-Ω block.
Throughout, `H/U = X^{(1-g)/5 - u}`, and every monomial of
`(A+1)(C₁R+1)(1+Ω^{-8/3}G^{-2/3})` is shown `≤ Cᵢ·H/U` with absolute `Cᵢ`. -/

/-- `H/U = X^{(1-g)/5 - u}`. -/
theorem H_div_U_eq (P : Globals) :
    P.H / P.U = P.X ^ ((1 - P.g) / 5 - P.u) := by
  have hX := P.X_pos
  rw [Globals.H, Globals.U, ← Real.rpow_sub hX]

/-- Master budget step: `q ≤ c·X^e` with `e ≤ (1-g)/5 - u` gives `q ≤ c·(H/U)`. -/
theorem term_le_HU (P : Globals) (hX : 1 ≤ P.X) {q c e : ℝ}
    (hc : 0 ≤ c) (he : e ≤ (1 - P.g) / 5 - P.u) (hq : q ≤ c * P.X ^ e) :
    q ≤ c * (P.H / P.U) := by
  rw [H_div_U_eq]
  refine hq.trans (mul_le_mul_of_nonneg_left ?_ hc)
  exact Real.rpow_le_rpow_of_exponent_le hX he

/-- The band edge in `X`-power form: `c₀·G^{-1/4}·U^{-3/4} = c₀·X^{-g/4 - 3u/4}`. -/
theorem band_eq_xpow (P : Globals) (c₀ : ℝ) :
    c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) = c₀ * P.X ^ (-P.g/4 - 3*P.u/4) := by
  have hX := P.X_pos
  rw [Globals.G, Globals.U, ← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le,
      ← Real.rpow_add hX]
  congr 2; ring

/-- Band upper bound in `X`-power form: `Ω ≤ c₀·X^{-g/4 - 3u/4}`. -/
theorem band_xpow (P : Globals) (S : Scale P) (c₀ : ℝ)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.Ω ≤ c₀ * P.X ^ (-P.g/4 - 3*P.u/4) := by
  rwa [band_eq_xpow] at hband

/-- Positive-power band bound: for `p ≥ 0`, `Ω^p ≤ c₀^p·X^{(-g/4 - 3u/4)·p}`. -/
theorem band_rpow (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀) {p : ℝ} (hp : 0 ≤ p)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.Ω ^ p ≤ c₀ ^ p * P.X ^ ((-P.g/4 - 3*P.u/4) * p) := by
  have hX := P.X_pos
  have hb := band_xpow P S c₀ hband
  calc S.Ω ^ p ≤ (c₀ * P.X ^ (-P.g/4 - 3*P.u/4)) ^ p :=
        Real.rpow_le_rpow S.Ω_pos.le hb hp
    _ = c₀ ^ p * P.X ^ ((-P.g/4 - 3*P.u/4) * p) := by
        rw [Real.mul_rpow hc₀.le (Real.rpow_nonneg hX.le _), ← Real.rpow_mul hX.le]

/-- The Nair–Roth Ω lower bound: `64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A = ΔΩ` with `Δ ≥ 1` gives
`Ω ≥ 64·(H⁴/X)^{1/3}`.  Used to upper-bound the bare `Ω^{-8/3}` term. -/
theorem omega_lb (P : Globals) (S : Scale P) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A) :
    (64 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.Ω := by
  have hΔ := S.Δ_pos
  have hH := P.H_pos
  have hX := P.X_pos
  have hy : (0:ℝ) ≤ (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  -- A = ΔΩ; 64 Δ^{4/3} y ≤ ΔΩ, and Δ^{4/3} = Δ·Δ^{1/3} ≥ Δ·1 = Δ, so 64 Δ y ≤ ΔΩ
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hΔ13 : (1:ℝ) ≤ S.Δ ^ (1/3 : ℝ) := Real.one_le_rpow hΔ1 (by norm_num)
  have hΔ43 : S.Δ * 1 ≤ S.Δ ^ (4/3 : ℝ) := by
    rw [show (4:ℝ)/3 = 1 + 1/3 by norm_num, Real.rpow_add hΔ, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hΔ13 hΔ.le
  have hstep : (64:ℝ) * S.Δ * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.Δ * S.Ω := by
    rw [← hAeq]
    calc (64:ℝ) * S.Δ * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)
        ≤ 64 * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := by
          have : (64:ℝ) * S.Δ ≤ 64 * S.Δ ^ (4/3 : ℝ) := by nlinarith [hΔ43]
          exact mul_le_mul_of_nonneg_right this hy
      _ ≤ S.A := hNR
  -- cancel Δ > 0
  have := le_of_mul_le_mul_left (by linarith [hstep] :
    S.Δ * ((64:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ≤ S.Δ * S.Ω) hΔ
  exact this

/-- The Nair–Roth Δ-ceiling: `64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A = ΔΩ` gives `Δ ≤ Ω³·X/(64³·H⁴)`. -/
theorem delta_ceiling (P : Globals) (S : Scale P) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A) :
    S.Δ ≤ S.Ω ^ 3 * P.X / ((64:ℝ) ^ 3 * P.H ^ 4) := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hX := P.X_pos
  -- cube both sides of the threshold; A³ = Δ³Ω³, and (64 Δ^{4/3} y^{1/3})³ = 64³ Δ⁴ (H⁴/X)
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  have hcube : ((64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ 3
      = (64:ℝ) ^ 3 * S.Δ ^ 4 * (P.H ^ 4 / P.X) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (S.Δ ^ (4/3:ℝ)) 3,
        ← Real.rpow_mul hΔ.le, ← Real.rpow_natCast ((P.H ^ 4 / P.X) ^ (1/3:ℝ)) 3,
        ← Real.rpow_mul (by positivity)]
    rw [show (4:ℝ)/3 * (3:ℕ) = (4:ℕ) by push_cast; ring, Real.rpow_natCast,
        show (1:ℝ)/3 * (3:ℕ) = (1:ℕ) by push_cast; ring, Real.rpow_natCast]
    ring
  have hAcube : S.A ^ 3 = S.Δ ^ 3 * S.Ω ^ 3 := by unfold Scale.A; ring
  have hmono : ((64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ 3 ≤ S.A ^ 3 :=
    pow_le_pow_left₀ (by positivity) hNR 3
  rw [hcube, hAcube] at hmono
  -- 64³ Δ⁴ H⁴/X ≤ Δ³ Ω³  ⟹  Δ ≤ Ω³ X /(64³ H⁴)
  rw [le_div_iff₀ (by positivity)]
  have hkey : (64:ℝ) ^ 3 * S.Δ ^ 4 * P.H ^ 4 ≤ S.Δ ^ 3 * S.Ω ^ 3 * P.X := by
    have e : (64:ℝ) ^ 3 * S.Δ ^ 4 * (P.H ^ 4 / P.X) * P.X = (64:ℝ) ^ 3 * S.Δ ^ 4 * P.H ^ 4 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hmono hX.le, e]
  -- cancel Δ³ > 0 from hkey : Δ³·(64³ΔH⁴) ≤ Δ³·(Ω³X)
  have hΔ3 : (0:ℝ) < S.Δ ^ 3 := by positivity
  have hkey' : S.Δ ^ 3 * (S.Δ * ((64:ℝ) ^ 3 * P.H ^ 4)) ≤ S.Δ ^ 3 * (S.Ω ^ 3 * P.X) := by
    nlinarith [hkey]
  have := le_of_mul_le_mul_left hkey' hΔ3
  nlinarith [this]

/-- `H·G·X^a = X^{(1-g)/5 + g + a}`. -/
private theorem HG_xpow (P : Globals) (a : ℝ) :
    P.H * P.G * P.X ^ a = P.X ^ ((1 - P.g) / 5 + P.g + a) := by
  have hX := P.X_pos
  rw [Globals.H, Globals.G, ← Real.rpow_add hX, ← Real.rpow_add hX]

/-- `H^4 · X^a = X^{4(1-g)/5 + a}` (the `1/X` and `H^{-4}` blocks). -/
private theorem H4_xpow (P : Globals) (a : ℝ) :
    P.H ^ 4 * P.X ^ a = P.X ^ (4 * ((1 - P.g) / 5) + a) := by
  have hX := P.X_pos
  rw [Globals.H, ← Real.rpow_natCast (P.X ^ ((1 - P.g)/5)) 4, ← Real.rpow_mul hX.le,
      ← Real.rpow_add hX]
  congr 1; push_cast; ring

/-- `Ω^(n:ℝ) = Ω^(n:ℕ)` helper to feed nat-power monomials into `band_rpow`. -/
private theorem rpow_ofNat_eq {x : ℝ} (n : ℕ) : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n

/-- **Term 1** `A·C₁R = C₁·H·G·Ω⁴ ≤ C₁c₀⁴·H/U`. Killed by the band edge alone (`exp = -3u`). -/
theorem term1_le (P : Globals) (S : Scale P) (c₀ : ℝ) (C₁ : ℝ) (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hu : 0 < P.u)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.A * (C₁ * S.R) ≤ (C₁ * c₀ ^ (4:ℝ)) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΔ := S.Δ_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ4 : S.Ω ^ (4:ℝ) = S.Ω ^ (4:ℕ) := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have heq : S.A * (C₁ * S.R) = C₁ * (P.H * P.G * S.Ω ^ (4:ℝ)) := by
    rw [hΩ4]; unfold Scale.A Scale.R
    field_simp; try ring
  rw [heq]
  refine term_le_HU P hX (c := C₁ * c₀ ^ (4:ℝ)) (e := (1 - P.g)/5 + P.g + (-P.g/4 - 3*P.u/4) * 4)
    (by positivity) ?_ ?_
  · -- exponent: (1-g)/5 + g + (-g/4-3u/4)*4 = (1-g)/5 - 3u ≤ (1-g)/5 - u
    have : (1 - P.g)/5 + P.g + (-P.g/4 - 3*P.u/4)*4 = (1 - P.g)/5 - 3*P.u := by ring
    rw [this]; linarith [hu]
  · -- C₁·(H·G·Ω⁴) ≤ C₁c₀⁴·X^{(1-g)/5+g+(-g/4-3u/4)*4}
    have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (4:ℝ)) hband
    have hHG : (0:ℝ) ≤ C₁ * (P.H * P.G) :=
      mul_nonneg hC₁.le (by positivity)
    calc C₁ * (P.H * P.G * S.Ω ^ (4:ℝ))
        = (C₁ * (P.H * P.G)) * S.Ω ^ (4:ℝ) := by ring
      _ ≤ (C₁ * (P.H * P.G)) * (c₀ ^ (4:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * 4)) :=
          mul_le_mul_of_nonneg_left hb hHG
      _ = (C₁ * c₀ ^ (4:ℝ)) * (P.H * P.G * P.X ^ ((-P.g/4 - 3*P.u/4) * 4)) := by ring
      _ = (C₁ * c₀ ^ (4:ℝ)) * P.X ^ ((1 - P.g)/5 + P.g + (-P.g/4 - 3*P.u/4) * 4) := by
          rw [HG_xpow]

/-- `G^k = X^{g·k}`. -/
private theorem G_xpow (P : Globals) (k : ℝ) : P.G ^ k = P.X ^ (P.g * k) := by
  rw [Globals.G, ← Real.rpow_mul P.X_pos.le]

/-- `(H⁴/X)^p = X^{(4(1-g)/5 - 1)·p}`. -/
private theorem H4X_xpow (P : Globals) (p : ℝ) :
    (P.H ^ 4 / P.X) ^ p = P.X ^ ((4 * ((1 - P.g)/5) - 1) * p) := by
  have hX := P.X_pos
  have hH4 : P.H ^ 4 = P.X ^ (4 * ((1 - P.g)/5)) := by
    rw [Globals.H, ← Real.rpow_natCast (P.X ^ ((1 - P.g)/5)) 4, ← Real.rpow_mul hX.le]
    congr 1; push_cast; ring
  have hHX : P.H ^ 4 / P.X = P.X ^ (4 * ((1 - P.g)/5) - 1) := by
    rw [hH4, Real.rpow_sub hX, Real.rpow_one]
  rw [hHX, ← Real.rpow_mul hX.le]

/-- The fiber factor `φ := (Δ/A)^{8/3}·G^{-2/3} = Ω^{-8/3}·G^{-2/3}`. -/
noncomputable def fiberφ (P : Globals) (S : Scale P) : ℝ :=
  (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)

/-- Unfolding lemma for `fiberφ`. -/
theorem fiberφ_def (P : Globals) (S : Scale P) :
    fiberφ P S = (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ) := rfl

/-- **Term 2** `A·C₁R·φ = C₁·H·G^{1/3}·Ω^{4/3} ≤ C₁c₀^{4/3}·H/U`. Band saturates (`exp = -u`). -/
theorem term2_le (P : Globals) (S : Scale P) (c₀ : ℝ) (C₁ : ℝ) (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.A * (C₁ * S.R) * fiberφ P S ≤ (C₁ * c₀ ^ (4/3:ℝ)) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hG := P.G_pos
  -- reduce to C₁·H·G^{1/3}·Ω^{4/3}
  have hAR : S.A * (C₁ * S.R) = C₁ * (P.H * P.G * S.Ω ^ (4:ℝ)) := by
    have hΩ4 : S.Ω ^ (4:ℝ) = S.Ω ^ (4:ℕ) := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hΩ4]; unfold Scale.A Scale.R; field_simp; try ring
  have hΩcol : S.Ω ^ (4:ℝ) * S.Ω ^ (-8/3:ℝ) = S.Ω ^ (4/3:ℝ) := by
    rw [← Real.rpow_add hΩ]; congr 1; ring
  have hGcol : P.G * P.G ^ (-2/3:ℝ) = P.G ^ (1/3:ℝ) := by
    rw [show (1/3:ℝ) = 1 + (-2/3:ℝ) by norm_num, Real.rpow_add hG, Real.rpow_one]
  have heq : S.A * (C₁ * S.R) * fiberφ P S = C₁ * (P.H * P.G ^ (1/3:ℝ) * S.Ω ^ (4/3:ℝ)) := by
    unfold fiberφ
    rw [deltaA_pow_eq, hAR]
    rw [show C₁ * (P.H * P.G * S.Ω ^ (4:ℝ)) * (S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ))
          = C₁ * (P.H * (P.G * P.G ^ (-2/3:ℝ)) * (S.Ω ^ (4:ℝ) * S.Ω ^ (-8/3:ℝ))) by ring,
        hΩcol, hGcol]
  rw [heq]
  refine term_le_HU P hX (c := C₁ * c₀ ^ (4/3:ℝ))
    (e := (1 - P.g)/5 + P.g * (1/3) + (-P.g/4 - 3*P.u/4) * (4/3)) (by positivity) ?_ ?_
  · have : (1 - P.g)/5 + P.g * (1/3) + (-P.g/4 - 3*P.u/4) * (4/3) = (1 - P.g)/5 - P.u := by ring
    rw [this]
  · have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (4/3:ℝ)) hband
    have hHG : (0:ℝ) ≤ C₁ * (P.H * P.G ^ (1/3:ℝ)) :=
      mul_nonneg hC₁.le (by positivity)
    calc C₁ * (P.H * P.G ^ (1/3:ℝ) * S.Ω ^ (4/3:ℝ))
        = (C₁ * (P.H * P.G ^ (1/3:ℝ))) * S.Ω ^ (4/3:ℝ) := by ring
      _ ≤ (C₁ * (P.H * P.G ^ (1/3:ℝ))) * (c₀ ^ (4/3:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3))) :=
          mul_le_mul_of_nonneg_left hb hHG
      _ = (C₁ * c₀ ^ (4/3:ℝ)) *
            (P.H * P.G ^ (1/3:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3))) := by ring
      _ = (C₁ * c₀ ^ (4/3:ℝ)) *
            P.X ^ ((1 - P.g)/5 + P.g * (1/3) + (-P.g/4 - 3*P.u/4) * (4/3)) := by
          rw [G_xpow, Globals.H, ← Real.rpow_add hX0, ← Real.rpow_add hX0]

/-- `1/H⁴ = X^{-4(1-g)/5}`, the `H^{-4}` block. -/
private theorem Hinv4_xpow (P : Globals) : (P.H ^ 4)⁻¹ = P.X ^ (-(4 * ((1 - P.g)/5))) := by
  have hX := P.X_pos
  have hH4 : P.H ^ 4 = P.X ^ (4 * ((1 - P.g)/5)) := by
    rw [Globals.H, ← Real.rpow_natCast (P.X ^ ((1 - P.g)/5)) 4, ← Real.rpow_mul hX.le]
    congr 1; push_cast; ring
  rw [hH4, ← Real.rpow_neg hX.le]

/-- **Term 3** `A·1·1 = A = ΔΩ ≤ (c₀⁴/64³)·H/U` via the Δ-ceiling (`exp = -3u`). -/
theorem term3_le (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hu : 0 < P.u) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.A ≤ (c₀ ^ (4:ℝ) / 64 ^ 3) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hceil := delta_ceiling P S hΔ1 hNR
  -- A = ΔΩ ≤ Ω⁴ X/(64³H⁴)
  have hAbound : S.A ≤ S.Ω ^ (4:ℝ) * (P.X / ((64:ℝ)^3 * P.H ^ 4)) := by
    have hΩ4eq : S.Ω ^ (4:ℝ) = S.Ω ^ 3 * S.Ω := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    have : S.A = S.Δ * S.Ω := rfl
    rw [this, hΩ4eq]
    have := mul_le_mul_of_nonneg_right hceil hΩ.le
    calc S.Δ * S.Ω ≤ S.Ω ^ 3 * P.X / ((64:ℝ)^3 * P.H ^ 4) * S.Ω := this
      _ = S.Ω ^ 3 * S.Ω * (P.X / ((64:ℝ)^3 * P.H ^ 4)) := by ring
  refine term_le_HU P hX (c := c₀ ^ (4:ℝ) / 64 ^ 3)
    (e := (-P.g/4 - 3*P.u/4) * 4 + (1 + (-(4 * ((1 - P.g)/5))))) (by positivity) ?_ ?_
  · have : (-P.g/4 - 3*P.u/4) * 4 + (1 + (-(4 * ((1 - P.g)/5)))) = (1 - P.g)/5 - 3*P.u := by ring
    rw [this]; linarith [hu]
  · have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (4:ℝ)) hband
    have hXpos : (0:ℝ) < P.X / ((64:ℝ)^3 * P.H ^ 4) := by positivity
    calc S.A ≤ S.Ω ^ (4:ℝ) * (P.X / ((64:ℝ)^3 * P.H ^ 4)) := hAbound
      _ ≤ (c₀ ^ (4:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * 4)) * (P.X / ((64:ℝ)^3 * P.H ^ 4)) :=
          mul_le_mul_of_nonneg_right hb hXpos.le
      _ = (c₀ ^ (4:ℝ) / 64 ^ 3) *
            (P.X ^ ((-P.g/4 - 3*P.u/4) * 4) * (P.X * (P.H ^ 4)⁻¹)) := by
          field_simp; try ring
      _ = (c₀ ^ (4:ℝ) / 64 ^ 3) *
            P.X ^ ((-P.g/4 - 3*P.u/4) * 4 + (1 + (-(4 * ((1 - P.g)/5))))) := by
          rw [Hinv4_xpow]
          rw [show P.X * P.X ^ (-(4 * ((1 - P.g)/5))) = P.X ^ (1 + (-(4 * ((1 - P.g)/5)))) by
                rw [Real.rpow_add hX0, Real.rpow_one]]
          rw [← Real.rpow_add hX0]

/-- **Term 4** `A·1·φ = Δ·Ω^{-5/3}·G^{-2/3} ≤ (c₀^{4/3}/64³)·H/U` via the Δ-ceiling
(band saturates, `exp = -u`). -/
theorem term4_le (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.A * fiberφ P S ≤ (c₀ ^ (4/3:ℝ) / 64 ^ 3) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΩ := S.Ω_pos
  have hΔ := S.Δ_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hceil := delta_ceiling P S hΔ1 hNR
  -- reduce A·φ = Δ·Ω^{-5/3}·G^{-2/3}, then ceiling ⇒ ≤ Ω^{4/3}·X·G^{-2/3}/(64³H⁴)
  have hΩ53 : S.Ω * S.Ω ^ (-8/3:ℝ) = S.Ω ^ (-5/3:ℝ) := by
    rw [show (-5/3:ℝ) = 1 + (-8/3:ℝ) by norm_num, Real.rpow_add hΩ, Real.rpow_one]
  have hAφ : S.A * fiberφ P S = S.Δ * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ) := by
    unfold fiberφ
    rw [deltaA_pow_eq, show S.A = S.Δ * S.Ω from rfl]
    rw [show S.Δ * S.Ω * (S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ))
          = S.Δ * (S.Ω * S.Ω ^ (-8/3:ℝ)) * P.G ^ (-2/3:ℝ) by ring, hΩ53]
  rw [hAφ]
  -- substitute ceiling on Δ
  have hG23pos : (0:ℝ) < P.G ^ (-2/3:ℝ) := Real.rpow_pos_of_pos hG _
  have hΩ53pos : (0:ℝ) < S.Ω ^ (-5/3:ℝ) := Real.rpow_pos_of_pos hΩ _
  have hsub : S.Δ * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ)
      ≤ (S.Ω ^ 3 * P.X / ((64:ℝ)^3 * P.H ^ 4)) * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ) := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hceil hΩ53pos.le) hG23pos.le
    linarith [this]
  -- collect: Ω³·Ω^{-5/3} = Ω^{4/3}
  have hΩcol : S.Ω ^ 3 * S.Ω ^ (-5/3:ℝ) = S.Ω ^ (4/3:ℝ) := by
    rw [show S.Ω ^ 3 = S.Ω ^ ((3:ℕ):ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hΩ]
    congr 1; push_cast; norm_num
  refine term_le_HU P hX (c := c₀ ^ (4/3:ℝ) / 64 ^ 3)
    (e := (-P.g/4 - 3*P.u/4) * (4/3) + (1 + (-(4 * ((1 - P.g)/5))) + P.g * (-2/3)))
    (by positivity) ?_ ?_
  · have : (-P.g/4 - 3*P.u/4) * (4/3) + (1 + (-(4 * ((1 - P.g)/5))) + P.g * (-2/3))
        = (1 - P.g)/5 - P.u := by ring
    rw [this]
  · have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (4/3:ℝ)) hband
    calc S.Δ * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ)
        ≤ (S.Ω ^ 3 * P.X / ((64:ℝ)^3 * P.H ^ 4)) * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ) := hsub
      _ = S.Ω ^ (4/3:ℝ) * (P.X / ((64:ℝ)^3 * P.H ^ 4) * P.G ^ (-2/3:ℝ)) := by
          rw [← hΩcol]; ring
      _ ≤ (c₀ ^ (4/3:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3)))
            * (P.X / ((64:ℝ)^3 * P.H ^ 4) * P.G ^ (-2/3:ℝ)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (c₀ ^ (4/3:ℝ) / 64 ^ 3) *
            (P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3)) * (P.X * (P.H ^ 4)⁻¹) * P.G ^ (-2/3:ℝ)) := by
          field_simp; try ring
      _ = (c₀ ^ (4/3:ℝ) / 64 ^ 3) *
            P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3) + (1 + (-(4 * ((1 - P.g)/5))) + P.g * (-2/3))) := by
          rw [Hinv4_xpow, G_xpow,
              show P.X * P.X ^ (-(4 * ((1 - P.g)/5))) = P.X ^ (1 + (-(4 * ((1 - P.g)/5)))) by
                rw [Real.rpow_add hX0, Real.rpow_one]]
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
          congr 1; ring

/-- From the long-range hypothesis `X^{1/100} ≤ Δ`: `Δ⁻¹ ≤ X^{-1/100}`. -/
theorem deltaInv_le (P : Globals) (S : Scale P) (hX : 1 ≤ P.X)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ) :
    S.Δ⁻¹ ≤ P.X ^ (-1/100 : ℝ) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hpos : (0:ℝ) < P.X ^ (1/100 : ℝ) := Real.rpow_pos_of_pos hX0 _
  rw [show P.X ^ (-1/100 : ℝ) = (P.X ^ (1/100 : ℝ))⁻¹ by rw [← Real.rpow_neg hX0.le]; norm_num]
  exact inv_anti₀ hpos hΔlong

/-- **Term 5** `1·C₁R·1 = C₁·H·G·Ω³/Δ ≤ C₁c₀³·H/U`.  Killed by `Δ ≥ X^{1/100}`
(`exp - exp(H/U) = g/4 - 5u/4 - 1/100 ≤ 0`). -/
theorem term5_le (P : Globals) (S : Scale P) (c₀ : ℝ) (C₁ : ℝ) (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hg : P.g < 2 / 18977) (hu : 0 < P.u)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    C₁ * S.R ≤ (C₁ * c₀ ^ (3:ℝ)) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΔ := S.Δ_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  -- R = H·G·Ω³/Δ = H·G·Ω³·Δ⁻¹
  have hReq : C₁ * S.R = C₁ * (P.H * P.G * S.Ω ^ (3:ℝ) * S.Δ⁻¹) := by
    have hΩ3 : S.Ω ^ (3:ℝ) = S.Ω ^ (3:ℕ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hΩ3]; unfold Scale.R; field_simp; try ring
  rw [hReq]
  have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (3:ℝ)) hband
  have hdinv := deltaInv_le P S hX hΔlong
  refine term_le_HU P hX (c := C₁ * c₀ ^ (3:ℝ))
    (e := (1 - P.g)/5 + P.g + (-P.g/4 - 3*P.u/4) * 3 + (-1/100)) (by positivity) ?_ ?_
  · have : (1 - P.g)/5 + P.g + (-P.g/4 - 3*P.u/4) * 3 + (-1/100)
        = (1 - P.g)/5 - P.u + (P.g/4 - 5*P.u/4 - 1/100) := by ring
    rw [this]
    have : P.g/4 - 5*P.u/4 - 1/100 ≤ 0 := by nlinarith [hg, hu]
    linarith [this]
  · -- collect: H·G·Ω³·Δ⁻¹ ≤ C₁c₀³ X^{...}
    have hHG : (0:ℝ) ≤ C₁ * (P.H * P.G) := mul_nonneg hC₁.le (by positivity)
    calc C₁ * (P.H * P.G * S.Ω ^ (3:ℝ) * S.Δ⁻¹)
        = (C₁ * (P.H * P.G)) * (S.Ω ^ (3:ℝ) * S.Δ⁻¹) := by ring
      _ ≤ (C₁ * (P.H * P.G))
            * ((c₀ ^ (3:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * 3)) * P.X ^ (-1/100 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hHG
          exact mul_le_mul hb hdinv (by positivity) (by positivity)
      _ = (C₁ * c₀ ^ (3:ℝ)) *
            (P.H * P.G * (P.X ^ ((-P.g/4 - 3*P.u/4) * 3) * P.X ^ (-1/100 : ℝ))) := by ring
      _ = (C₁ * c₀ ^ (3:ℝ)) *
            P.X ^ ((1 - P.g)/5 + P.g + (-P.g/4 - 3*P.u/4) * 3 + (-1/100)) := by
          rw [← Real.rpow_add hX0, HG_xpow]
          congr 2; ring

/-- **Term 6** `1·C₁R·φ = C₁·H·G^{1/3}·Ω^{1/3}/Δ ≤ C₁c₀^{1/3}·H/U`.  Killed by `Δ ≥ X^{1/100}`
(`exp - exp(H/U) = g/4 + 3u/4 - 1/100 ≤ 0`). -/
theorem term6_le (P : Globals) (S : Scale P) (c₀ : ℝ) (C₁ : ℝ) (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hg : P.g < 2 / 18977) (hu : 0 < P.u) (hu' : P.u ≤ 1 / 100)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    C₁ * S.R * fiberφ P S ≤ (C₁ * c₀ ^ (1/3:ℝ)) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΔ := S.Δ_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  -- reduce to C₁·H·G^{1/3}·Ω^{1/3}·Δ⁻¹
  have hReq : C₁ * S.R = C₁ * (P.H * P.G * S.Ω ^ (3:ℝ) * S.Δ⁻¹) := by
    have hΩ3 : S.Ω ^ (3:ℝ) = S.Ω ^ (3:ℕ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hΩ3]; unfold Scale.R; field_simp; try ring
  have hΩcol : S.Ω ^ (3:ℝ) * S.Ω ^ (-8/3:ℝ) = S.Ω ^ (1/3:ℝ) := by
    rw [← Real.rpow_add hΩ]; congr 1; norm_num
  have hGcol : P.G * P.G ^ (-2/3:ℝ) = P.G ^ (1/3:ℝ) := by
    rw [show (1/3:ℝ) = 1 + (-2/3:ℝ) by norm_num, Real.rpow_add hG, Real.rpow_one]
  have heq : C₁ * S.R * fiberφ P S = C₁ * (P.H * P.G ^ (1/3:ℝ) * S.Ω ^ (1/3:ℝ) * S.Δ⁻¹) := by
    unfold fiberφ
    rw [deltaA_pow_eq, hReq]
    rw [show C₁ * (P.H * P.G * S.Ω ^ (3:ℝ) * S.Δ⁻¹) * (S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ))
          = C₁ * (P.H * (P.G * P.G ^ (-2/3:ℝ)) * (S.Ω ^ (3:ℝ) * S.Ω ^ (-8/3:ℝ)) * S.Δ⁻¹) by ring,
        hΩcol, hGcol]
  rw [heq]
  have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (1/3:ℝ)) hband
  have hdinv := deltaInv_le P S hX hΔlong
  refine term_le_HU P hX (c := C₁ * c₀ ^ (1/3:ℝ))
    (e := (1 - P.g)/5 + P.g * (1/3) + (-P.g/4 - 3*P.u/4) * (1/3) + (-1/100)) (by positivity) ?_ ?_
  · have : (1 - P.g)/5 + P.g * (1/3) + (-P.g/4 - 3*P.u/4) * (1/3) + (-1/100)
        = (1 - P.g)/5 - P.u + (P.g/4 + 3*P.u/4 - 1/100) := by ring
    rw [this]
    have : P.g/4 + 3*P.u/4 - 1/100 ≤ 0 := by nlinarith [hg, hu, hu']
    linarith [this]
  · have hHG : (0:ℝ) ≤ C₁ * (P.H * P.G ^ (1/3:ℝ)) := mul_nonneg hC₁.le (by positivity)
    calc C₁ * (P.H * P.G ^ (1/3:ℝ) * S.Ω ^ (1/3:ℝ) * S.Δ⁻¹)
        = (C₁ * (P.H * P.G ^ (1/3:ℝ))) * (S.Ω ^ (1/3:ℝ) * S.Δ⁻¹) := by ring
      _ ≤ (C₁ * (P.H * P.G ^ (1/3:ℝ)))
            * ((c₀ ^ (1/3:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (1/3))) * P.X ^ (-1/100 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hHG
          exact mul_le_mul hb hdinv (by positivity) (by positivity)
      _ = (C₁ * c₀ ^ (1/3:ℝ)) *
            (P.H * P.G ^ (1/3:ℝ) * (P.X ^ ((-P.g/4 - 3*P.u/4) * (1/3)) * P.X ^ (-1/100 : ℝ))) := by
          ring
      _ = (C₁ * c₀ ^ (1/3:ℝ)) *
            P.X ^ ((1 - P.g)/5 + P.g * (1/3) + (-P.g/4 - 3*P.u/4) * (1/3) + (-1/100)) := by
          rw [← Real.rpow_add hX0, G_xpow, Globals.H, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
          congr 1; ring

/-- **Term 7** `1·1·1 = 1 ≤ H/U`. Killed by `H/U → ∞` (`exp(H/U) = (1-g)/5 - u ≥ 0`). -/
theorem term7_le (P : Globals) (hX : 1 ≤ P.X) (hg : P.g < 2 / 18977) (hu' : P.u ≤ 1 / 100) :
    (1 : ℝ) ≤ (1 : ℝ) * (P.H / P.U) := by
  refine term_le_HU P hX (c := 1) (e := 0) (by norm_num) ?_ ?_
  · nlinarith [hg, hu']
  · rw [Real.rpow_zero]; norm_num

/-- **Term 8** `1·1·φ = Ω^{-8/3}·G^{-2/3} ≤ 64^{-8/3}·H/U`.  Killed by the Ω lower bound
`Ω ≥ 64(H⁴/X)^{1/3}` plus `H/U → ∞` (`exp - exp(H/U) = u + 11g/45 - 1/45 ≤ 0`). -/
theorem term8_le (P : Globals) (S : Scale P)
    (hX : 1 ≤ P.X) (hg : P.g < 2 / 18977) (hu' : P.u ≤ 1 / 100) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A) :
    fiberφ P S ≤ ((64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos
  have hH := P.H_pos
  have hΩ := S.Ω_pos
  -- φ = Ω^{-8/3}·G^{-2/3}
  have hφ : fiberφ P S = S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ) := by
    unfold fiberφ; rw [deltaA_pow_eq]
  rw [hφ]
  -- lower bound on Ω; (H⁴/X)^{1/3} > 0
  have hL := omega_lb P S hΔ1 hNR
  have hLpos : (0:ℝ) < (64:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := by
    have : (0:ℝ) < (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  -- Ω^{-8/3} ≤ (64·(H⁴/X)^{1/3})^{-8/3}
  have hΩbd : S.Ω ^ (-8/3:ℝ) ≤ ((64:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ (-8/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hLpos hL (by norm_num)
  have hG23pos : (0:ℝ) < P.G ^ (-2/3:ℝ) := Real.rpow_pos_of_pos hG _
  -- expand the bound into an X-power
  have hHX0 : (0:ℝ) < P.H ^ 4 / P.X := by positivity
  have hinner : ((P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ (-8/3:ℝ)
      = P.X ^ ((4 * ((1 - P.g)/5) - 1) * ((1/3 : ℝ) * (-8/3 : ℝ))) := by
    rw [← Real.rpow_mul hHX0.le (1/3 : ℝ) (-8/3 : ℝ), H4X_xpow]
  have hexp : ((64:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ)
      = ((64:ℝ) ^ (-8/3:ℝ)) *
        P.X ^ ((4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hHX0.le _),
        hinner, G_xpow,
        Real.rpow_add hX0 ((4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3))) (P.g * (-2/3))]
    ring
  -- bound the goal by 64^{-8/3}·X^e, then convert X^e to H/U
  have hbound : S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ)
      ≤ ((64:ℝ) ^ (-8/3:ℝ)) *
        P.X ^ ((4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3)) := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_right hΩbd hG23pos.le
  refine term_le_HU P hX (c := (64:ℝ) ^ (-8/3:ℝ))
    (e := (4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3))
    (Real.rpow_nonneg (by norm_num) _) ?_ hbound
  · have : (4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3)
        = (1 - P.g)/5 - P.u + (P.u + 11*P.g/45 - 1/45) := by ring
    rw [this]
    have : P.u + 11*P.g/45 - 1/45 ≤ 0 := by nlinarith [hg, hu']
    linarith [this]

end Squarefree.StripAux
