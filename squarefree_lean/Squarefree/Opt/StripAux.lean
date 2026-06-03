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

/-- The fiber factor `φ := (Δ/A)^{8/3}·G^{-2/3} = Ω^{-8/3}·G^{-2/3}`. -/
noncomputable def fiberφ (P : Globals) (S : Scale P) : ℝ :=
  (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)

/-- Unfolding lemma for `fiberφ`. -/
theorem fiberφ_def (P : Globals) (S : Scale P) :
    fiberφ P S = (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ) := rfl

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

/-- **`𝐃(Ω) ≤ C₂·(1+φ)·Σ #ℛ_a`** for a given Prop-3.2 constant `C₂` and its per-`a` fiber bound
`hfiber` (passed in so callers share one `C₂` across the disjunction); `φ = fiberφ` kept symbolic.
Also returns `0 < a` for each `a` in the block (needed by `prop_5_1`). -/
theorem dblock_le_sum_Ra (P : Globals) (S : Scale P) (C₂ : ℝ) (D' : ℝ)
    (hfiber : ∀ (a : ℤ), 0 < a → 1 ≤ S.Δ →
      (1/4:ℝ) * S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) ≤ (a:ℝ) →
      S.A ≤ (a:ℝ) → (a:ℝ) ≤ 2*S.A → 2*S.A ≤ S.D → ∀ (Dd : ℝ), 0 < Dd → Dd = S.D →
      ∃ Ra : Finset ℕ,
        ((DaCard P.X P.H a Dd : ℝ) ≤ C₂ * (Ra.card:ℝ) * (1 + (S.Δ/S.A)^(8/3:ℝ) * P.G^(-2/3:ℝ))))
    (hΔ1 : 1 ≤ S.Δ)
    (hNR : (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A)
    (h2AD : 2 * S.A ≤ S.D)
    (hDpos : 0 < D') (hDeq : D' = S.D) :
    ∃ (RaOf : ℤ → Finset ℕ),
      (∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, 0 < a) ∧
      DBlock P S D' ≤ C₂ * (1 + fiberφ P S) *
        (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) := by
  have hΔp := S.Δ_pos
  have hΩp := S.Ω_pos
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  -- per-a: pick Ra from prop_3_2_fiber via choice
  have hpera : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, 0 < a ∧
      ∃ Ra : Finset ℕ, (DaCard P.X P.H a D' : ℝ)
        ≤ C₂ * (Ra.card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨haL, haR⟩ := ha
    have hAa : S.A ≤ (a:ℝ) := le_trans (Int.le_ceil S.A) (by exact_mod_cast haL)
    have ha2A : (a:ℝ) ≤ 2 * S.A := le_trans (by exact_mod_cast haR) (Int.floor_le (2 * S.A))
    have ha0 : 0 < a := by
      have : (0:ℤ) < ⌈S.A⌉ := Int.ceil_pos.mpr hApos
      omega
    obtain ⟨Ra, hRaCard⟩ :=
      hfiber a ha0 hΔ1 (le_trans hNR hAa) hAa ha2A h2AD D' hDpos hDeq
    exact ⟨ha0, Ra, hRaCard⟩
  have hapos : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, 0 < a := fun a ha => (hpera a ha).1
  -- build RaOf
  classical
  let RaOf : ℤ → Finset ℕ := fun a =>
    if h : a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋ then (hpera a h).2.choose else ∅
  refine ⟨RaOf, hapos, ?_⟩
  -- per-a bound: DaCard ≤ C₂·(1+φ)·#(RaOf a)
  have hper : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋,
      (DaCard P.X P.H a D' : ℝ)
        ≤ (C₂ * (1 + fiberφ P S)) * ((RaOf a).card : ℝ) := by
    intro a ha
    have hRaSpec := (hpera a ha).2.choose_spec
    have hRaeq : (hpera a ha).2.choose = RaOf a := by
      show (hpera a ha).2.choose = (if h : a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋ then (hpera a h).2.choose else ∅)
      rw [dif_pos ha]
    rw [hRaeq] at hRaSpec
    calc (DaCard P.X P.H a D' : ℝ)
        ≤ C₂ * ((RaOf a).card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)) := hRaSpec
      _ = (C₂ * (1 + fiberφ P S)) * ((RaOf a).card : ℝ) := by rw [fiberφ_def]; ring
  -- sum over the block
  have hsum : DBlock P S D'
      ≤ ∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋,
          (C₂ * (1 + fiberφ P S)) * ((RaOf a).card : ℝ) := by
    unfold DBlock
    exact Finset.sum_le_sum hper
  rw [← Finset.mul_sum] at hsum
  exact hsum

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

/-- The Nair–Roth Ω lower bound: `(1/4)·Δ^{4/3}(H⁴/X)^{1/3} ≤ A = ΔΩ` with `Δ ≥ 1` gives
`Ω ≥ (1/4)·(H⁴/X)^{1/3}`.  Used to upper-bound the bare `Ω^{-8/3}` term. -/
theorem omega_lb (P : Globals) (S : Scale P) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A) :
    (1/4 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.Ω := by
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
  have hstep : (1/4:ℝ) * S.Δ * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.Δ * S.Ω := by
    rw [← hAeq]
    calc (1/4:ℝ) * S.Δ * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)
        ≤ (1/4) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := by
          have : (1/4:ℝ) * S.Δ ≤ (1/4) * S.Δ ^ (4/3 : ℝ) := by nlinarith [hΔ43]
          exact mul_le_mul_of_nonneg_right this hy
      _ ≤ S.A := hNR
  -- cancel Δ > 0
  have := le_of_mul_le_mul_left (by linarith [hstep] :
    S.Δ * ((1/4:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ≤ S.Δ * S.Ω) hΔ
  exact this

/-- The Nair–Roth Δ-ceiling: `(1/4)·Δ^{4/3}(H⁴/X)^{1/3} ≤ A = ΔΩ` gives
`Δ ≤ Ω³·X/((1/4)³·H⁴)`. -/
theorem delta_ceiling (P : Globals) (S : Scale P) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A) :
    S.Δ ≤ S.Ω ^ 3 * P.X / ((1/4:ℝ) ^ 3 * P.H ^ 4) := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hX := P.X_pos
  -- cube both sides of the threshold; A³ = Δ³Ω³, and (64 Δ^{4/3} y^{1/3})³ = 64³ Δ⁴ (H⁴/X)
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  have hcube : ((1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ 3
      = (1/4:ℝ) ^ 3 * S.Δ ^ 4 * (P.H ^ 4 / P.X) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (S.Δ ^ (4/3:ℝ)) 3,
        ← Real.rpow_mul hΔ.le, ← Real.rpow_natCast ((P.H ^ 4 / P.X) ^ (1/3:ℝ)) 3,
        ← Real.rpow_mul (by positivity)]
    rw [show (4:ℝ)/3 * (3:ℕ) = (4:ℕ) by push_cast; ring, Real.rpow_natCast,
        show (1:ℝ)/3 * (3:ℕ) = (1:ℕ) by push_cast; ring, Real.rpow_natCast]
    ring
  have hAcube : S.A ^ 3 = S.Δ ^ 3 * S.Ω ^ 3 := by unfold Scale.A; ring
  have hmono : ((1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ 3 ≤ S.A ^ 3 :=
    pow_le_pow_left₀ (by positivity) hNR 3
  rw [hcube, hAcube] at hmono
  -- (1/4)³ Δ⁴ H⁴/X ≤ Δ³ Ω³  ⟹  Δ ≤ Ω³ X /((1/4)³ H⁴)
  rw [le_div_iff₀ (by positivity)]
  have hkey : (1/4:ℝ) ^ 3 * S.Δ ^ 4 * P.H ^ 4 ≤ S.Δ ^ 3 * S.Ω ^ 3 * P.X := by
    have e : (1/4:ℝ) ^ 3 * S.Δ ^ 4 * (P.H ^ 4 / P.X) * P.X = (1/4:ℝ) ^ 3 * S.Δ ^ 4 * P.H ^ 4 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hmono hX.le, e]
  -- cancel Δ³ > 0 from hkey : Δ³·((1/4)³ΔH⁴) ≤ Δ³·(Ω³X)
  have hΔ3 : (0:ℝ) < S.Δ ^ 3 := by positivity
  have hkey' : S.Δ ^ 3 * (S.Δ * ((1/4:ℝ) ^ 3 * P.H ^ 4)) ≤ S.Δ ^ 3 * (S.Ω ^ 3 * P.X) := by
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
    (hNR : (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.A ≤ (c₀ ^ (4:ℝ) / (1/4) ^ 3) * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hceil := delta_ceiling P S hΔ1 hNR
  -- A = ΔΩ ≤ Ω⁴ X/((1/4)³H⁴)
  have hAbound : S.A ≤ S.Ω ^ (4:ℝ) * (P.X / ((1/4:ℝ)^3 * P.H ^ 4)) := by
    have hΩ4eq : S.Ω ^ (4:ℝ) = S.Ω ^ 3 * S.Ω := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    have : S.A = S.Δ * S.Ω := rfl
    rw [this, hΩ4eq]
    have := mul_le_mul_of_nonneg_right hceil hΩ.le
    calc S.Δ * S.Ω ≤ S.Ω ^ 3 * P.X / ((1/4:ℝ)^3 * P.H ^ 4) * S.Ω := this
      _ = S.Ω ^ 3 * S.Ω * (P.X / ((1/4:ℝ)^3 * P.H ^ 4)) := by ring
  refine term_le_HU P hX (c := c₀ ^ (4:ℝ) / (1/4) ^ 3)
    (e := (-P.g/4 - 3*P.u/4) * 4 + (1 + (-(4 * ((1 - P.g)/5))))) (by positivity) ?_ ?_
  · have : (-P.g/4 - 3*P.u/4) * 4 + (1 + (-(4 * ((1 - P.g)/5)))) = (1 - P.g)/5 - 3*P.u := by ring
    rw [this]; linarith [hu]
  · have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (4:ℝ)) hband
    have hXpos : (0:ℝ) < P.X / ((1/4:ℝ)^3 * P.H ^ 4) := by positivity
    calc S.A ≤ S.Ω ^ (4:ℝ) * (P.X / ((1/4:ℝ)^3 * P.H ^ 4)) := hAbound
      _ ≤ (c₀ ^ (4:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * 4)) * (P.X / ((1/4:ℝ)^3 * P.H ^ 4)) :=
          mul_le_mul_of_nonneg_right hb hXpos.le
      _ = (c₀ ^ (4:ℝ) / (1/4) ^ 3) *
            (P.X ^ ((-P.g/4 - 3*P.u/4) * 4) * (P.X * (P.H ^ 4)⁻¹)) := by
          field_simp; try ring
      _ = (c₀ ^ (4:ℝ) / (1/4) ^ 3) *
            P.X ^ ((-P.g/4 - 3*P.u/4) * 4 + (1 + (-(4 * ((1 - P.g)/5))))) := by
          rw [Hinv4_xpow]
          rw [show P.X * P.X ^ (-(4 * ((1 - P.g)/5))) = P.X ^ (1 + (-(4 * ((1 - P.g)/5)))) by
                rw [Real.rpow_add hX0, Real.rpow_one]]
          rw [← Real.rpow_add hX0]

/-- **Term 4** `A·1·φ = Δ·Ω^{-5/3}·G^{-2/3} ≤ (c₀^{4/3}/64³)·H/U` via the Δ-ceiling
(band saturates, `exp = -u`). -/
theorem term4_le (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A)
    (hband : S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) :
    S.A * fiberφ P S ≤ (c₀ ^ (4/3:ℝ) / (1/4) ^ 3) * (P.H / P.U) := by
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
      ≤ (S.Ω ^ 3 * P.X / ((1/4:ℝ)^3 * P.H ^ 4)) * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ) := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hceil hΩ53pos.le) hG23pos.le
    linarith [this]
  -- collect: Ω³·Ω^{-5/3} = Ω^{4/3}
  have hΩcol : S.Ω ^ 3 * S.Ω ^ (-5/3:ℝ) = S.Ω ^ (4/3:ℝ) := by
    rw [show S.Ω ^ 3 = S.Ω ^ ((3:ℕ):ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hΩ]
    congr 1; push_cast; norm_num
  refine term_le_HU P hX (c := c₀ ^ (4/3:ℝ) / (1/4) ^ 3)
    (e := (-P.g/4 - 3*P.u/4) * (4/3) + (1 + (-(4 * ((1 - P.g)/5))) + P.g * (-2/3)))
    (by positivity) ?_ ?_
  · have : (-P.g/4 - 3*P.u/4) * (4/3) + (1 + (-(4 * ((1 - P.g)/5))) + P.g * (-2/3))
        = (1 - P.g)/5 - P.u := by ring
    rw [this]
  · have hb := band_rpow P S c₀ hc₀ (by norm_num : (0:ℝ) ≤ (4/3:ℝ)) hband
    calc S.Δ * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ)
        ≤ (S.Ω ^ 3 * P.X / ((1/4:ℝ)^3 * P.H ^ 4)) * S.Ω ^ (-5/3:ℝ) * P.G ^ (-2/3:ℝ) := hsub
      _ = S.Ω ^ (4/3:ℝ) * (P.X / ((1/4:ℝ)^3 * P.H ^ 4) * P.G ^ (-2/3:ℝ)) := by
          rw [← hΩcol]; ring
      _ ≤ (c₀ ^ (4/3:ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3)))
            * (P.X / ((1/4:ℝ)^3 * P.H ^ 4) * P.G ^ (-2/3:ℝ)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (c₀ ^ (4/3:ℝ) / (1/4) ^ 3) *
            (P.X ^ ((-P.g/4 - 3*P.u/4) * (4/3)) * (P.X * (P.H ^ 4)⁻¹) * P.G ^ (-2/3:ℝ)) := by
          field_simp; try ring
      _ = (c₀ ^ (4/3:ℝ) / (1/4) ^ 3) *
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

/-- **Term 8** `1·1·φ = Ω^{-8/3}·G^{-2/3} ≤ (1/4)^{-8/3}·H/U`.  Killed by the Ω lower bound
`Ω ≥ (1/4)(H⁴/X)^{1/3}` plus `H/U → ∞` (`exp - exp(H/U) = u + 11g/45 - 1/45 ≤ 0`). -/
theorem term8_le (P : Globals) (S : Scale P)
    (hX : 1 ≤ P.X) (hg : P.g < 2 / 18977) (hu' : P.u ≤ 1 / 100) (hΔ1 : 1 ≤ S.Δ)
    (hNR : (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A) :
    fiberφ P S ≤ ((1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by
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
  have hLpos : (0:ℝ) < (1/4:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := by
    have : (0:ℝ) < (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  -- Ω^{-8/3} ≤ ((1/4)·(H⁴/X)^{1/3})^{-8/3}
  have hΩbd : S.Ω ^ (-8/3:ℝ) ≤ ((1/4:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ (-8/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hLpos hL (by norm_num)
  have hG23pos : (0:ℝ) < P.G ^ (-2/3:ℝ) := Real.rpow_pos_of_pos hG _
  -- expand the bound into an X-power
  have hHX0 : (0:ℝ) < P.H ^ 4 / P.X := by positivity
  have hinner : ((P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ (-8/3:ℝ)
      = P.X ^ ((4 * ((1 - P.g)/5) - 1) * ((1/3 : ℝ) * (-8/3 : ℝ))) := by
    rw [← Real.rpow_mul hHX0.le (1/3 : ℝ) (-8/3 : ℝ), H4X_xpow]
  have hexp : ((1/4:ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ)
      = ((1/4:ℝ) ^ (-8/3:ℝ)) *
        P.X ^ ((4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hHX0.le _),
        hinner, G_xpow,
        Real.rpow_add hX0 ((4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3))) (P.g * (-2/3))]
    ring
  -- bound the goal by (1/4)^{-8/3}·X^e, then convert X^e to H/U
  have hbound : S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ)
      ≤ ((1/4:ℝ) ^ (-8/3:ℝ)) *
        P.X ^ ((4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3)) := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_right hΩbd hG23pos.le
  refine term_le_HU P hX (c := (1/4:ℝ) ^ (-8/3:ℝ))
    (e := (4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3))
    (Real.rpow_nonneg (by norm_num) _) ?_ hbound
  · have : (4 * ((1 - P.g)/5) - 1) * ((1/3) * (-8/3)) + P.g * (-2/3)
        = (1 - P.g)/5 - P.u + (P.u + 11*P.g/45 - 1/45) := by ring
    rw [this]
    have : P.u + 11*P.g/45 - 1/45 ≤ 0 := by nlinarith [hg, hu']
    linarith [this]

/-! ### §8 off-strip exponent budgets (Props 5.1 / 6.1)

The prop-6.1 budget constant is exposed as `C6 := prop_6_1.choose`; the merger picks `Cu`/`u`
relative to it.  Throughout, `S.x = H/Δ²`, `A = ΔΩ`, `R = HGΩ³/Δ`, `Wval = GU⁵`. -/

/-- The (opaque) Prop 6.1 budget constant. -/
noncomputable def C6 : ℝ := prop_6_1.choose

theorem C6_pos : 0 < C6 := prop_6_1.choose_spec.1

/-- Prop 6.1, specialised to `RaOf` with its budget constant named `C6`. -/
theorem prop_6_1_spec (P : Globals) (S : Scale P) (RaOf : ℤ → Finset ℕ) :
    (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) ≤
      C6 * P.H * P.X ^ (C6 * P.u) *
        ( S.x * P.G * S.Ω ^ 2
        + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
        + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) :=
  prop_6_1.choose_spec.2 P S RaOf

/-- Band edge for negative `Ω`-powers: for `p ≤ 0`, `Ω^p ≤ c₀^p·X^{(-g/4-3u/4)·p}`
(the lower band gives an *upper* bound on a negative power of `Ω`). -/
theorem band_rpow_neg (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀) {p : ℝ} (hp : p ≤ 0)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    S.Ω ^ p ≤ c₀ ^ p * P.X ^ ((-P.g/4 - 3*P.u/4) * p) := by
  have hX := P.X_pos
  have hG := P.G_pos
  have hU := P.U_pos
  have hΩ := S.Ω_pos
  have hlb_pos : 0 < c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) := by
    have := Real.rpow_pos_of_pos hG (-1/4 : ℝ)
    have := Real.rpow_pos_of_pos hU (-3/4 : ℝ); positivity
  -- raise band (lb ≤ Ω) to the nonpositive power p (antitone)
  have hpow : S.Ω ^ p ≤ (c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) ^ p :=
    Real.rpow_le_rpow_of_nonpos hlb_pos hband hp
  calc S.Ω ^ p ≤ (c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) ^ p := hpow
    _ = c₀ ^ p * P.X ^ ((-P.g/4 - 3*P.u/4) * p) := by
        rw [band_eq_xpow, Real.mul_rpow hc₀.le (Real.rpow_nonneg hX.le _),
            ← Real.rpow_mul hX.le]

/-- `Ω ≤ U`-form for positive powers: `Ω^p ≤ X^{u·p}` for `p ≥ 0`. -/
theorem omega_le_U_rpow (P : Globals) (S : Scale P) {p : ℝ} (hp : 0 ≤ p)
    (hΩU : S.Ω ≤ P.U) : S.Ω ^ p ≤ P.X ^ (P.u * p) := by
  have hX := P.X_pos
  calc S.Ω ^ p ≤ P.U ^ p := Real.rpow_le_rpow S.Ω_pos.le hΩU hp
    _ = P.X ^ (P.u * p) := by rw [Globals.U, ← Real.rpow_mul hX.le]

/-- `Ω^(n:ℕ) = Ω^(n:ℝ)`, to feed nat-powers (from `prop_6_1`) into the rpow lemmas. -/
private theorem Ωnat {P : Globals} (S : Scale P) (n : ℕ) :
    S.Ω ^ n = S.Ω ^ (n : ℝ) := (Real.rpow_natCast _ _).symm

/-- **Small-x term 2** (binding, exp `= 0` at the edge): `x^{2/3}G^{4/3}Ω^{11/3} ≤ X^{-(2/3)Cu·u}`.
Uses only the edge `x ≤ G^{-2}Ω^{-11/2}X^{-Cu·u}`. -/
theorem smallx_edge_T2 (P : Globals) (S : Scale P) (Cu : ℝ)
    (hx : S.x ≤ P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) :
    S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ) ≤ P.X ^ (-(2/3) * (Cu * P.u)) := by
  have hX := P.X_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  have hxnn : 0 ≤ S.x := by unfold Scale.x; positivity
  have hrhs_nn : 0 ≤ P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)) := by positivity
  have hx23 : S.x ^ (2/3 : ℝ)
      ≤ (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ (2/3 : ℝ) :=
    Real.rpow_le_rpow hxnn hx (by norm_num)
  have hexpand : (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ (2/3 : ℝ)
      = P.G ^ (-4/3 : ℝ) * S.Ω ^ (-11/3 : ℝ) * P.X ^ (-(2/3) * (Cu * P.u)) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hX.le _),
        Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hΩ.le _),
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le, ← Real.rpow_mul hX.le]
    congr 2 <;> ring
  calc S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
      ≤ (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ (2/3 : ℝ)
          * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hx23 (by positivity)
    _ = (P.G ^ (-4/3 : ℝ) * S.Ω ^ (-11/3 : ℝ) * P.X ^ (-(2/3) * (Cu * P.u)))
          * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ) := by rw [hexpand]
    _ = (P.G ^ (-4/3 : ℝ) * P.G ^ (4/3 : ℝ)) * (S.Ω ^ (-11/3 : ℝ) * S.Ω ^ (11/3 : ℝ))
          * P.X ^ (-(2/3) * (Cu * P.u)) := by ring
    _ = P.X ^ (-(2/3) * (Cu * P.u)) := by
        rw [← Real.rpow_add hG, ← Real.rpow_add hΩ]
        norm_num

/-- **Small-x term 1**: `xGΩ² ≤ c₀^{-7/2}·X^{-g/8 + 21u/8 - Cu·u}` using edge + lower band. -/
theorem smallx_edge_T1 (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (hc₀ : 0 < c₀)
    (hx : S.x ≤ P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)))
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    S.x * P.G * S.Ω ^ 2
      ≤ c₀ ^ (-7/2 : ℝ) * P.X ^ (-P.g/8 + 21*P.u/8 - Cu * P.u) := by
  have hX := P.X_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  -- x ≤ G^{-2}Ω^{-11/2}X^{-Cu·u}; so xGΩ² ≤ G^{-1}Ω^{-7/2}X^{-Cu·u}
  have hΩ2 : S.Ω ^ 2 = S.Ω ^ (2 : ℝ) := Ωnat S 2
  have hstep1 : S.x * P.G * S.Ω ^ 2
      ≤ (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) * P.G * S.Ω ^ (2 : ℝ) := by
    rw [hΩ2]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hx hG.le) (by positivity)
  have hcollapse : (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) * P.G * S.Ω ^ (2 : ℝ)
      = P.G ^ (-1 : ℝ) * S.Ω ^ (-7/2 : ℝ) * P.X ^ (-(Cu * P.u)) := by
    have hGe : P.G = P.G ^ (1:ℝ) := (Real.rpow_one _).symm
    rw [show (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) * P.G * S.Ω ^ (2 : ℝ)
          = (P.G ^ (-2 : ℝ) * P.G ^ (1:ℝ)) * (S.Ω ^ (-11/2 : ℝ) * S.Ω ^ (2 : ℝ))
              * P.X ^ (-(Cu * P.u)) by rw [← hGe]; ring]
    rw [← Real.rpow_add hG, ← Real.rpow_add hΩ]
    norm_num
  -- Ω^{-7/2} ≤ c₀^{-7/2}·X^{(-g/4-3u/4)(-7/2)}  (negative power, lower band)
  have hbn := band_rpow_neg P S c₀ hc₀ (by norm_num : (-7/2 : ℝ) ≤ 0) hband
  have hGneg : P.G ^ (-1 : ℝ) = P.X ^ (-P.g) := by
    rw [Globals.G, ← Real.rpow_mul hX.le]; congr 1; ring
  calc S.x * P.G * S.Ω ^ 2
      ≤ P.G ^ (-1 : ℝ) * S.Ω ^ (-7/2 : ℝ) * P.X ^ (-(Cu * P.u)) := by rw [← hcollapse]; exact hstep1
    _ ≤ P.G ^ (-1 : ℝ) * (c₀ ^ (-7/2 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-7/2)))
          * P.X ^ (-(Cu * P.u)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hbn (Real.rpow_nonneg hG.le _)
    _ = c₀ ^ (-7/2 : ℝ) * (P.G ^ (-1 : ℝ)
          * (P.X ^ ((-P.g/4 - 3*P.u/4) * (-7/2)) * P.X ^ (-(Cu * P.u)))) := by ring
    _ = c₀ ^ (-7/2 : ℝ) * P.X ^ (-P.g/8 + 21*P.u/8 - Cu * P.u) := by
        rw [hGneg, ← Real.rpow_add hX, ← Real.rpow_add hX]
        congr 2; ring

/-- **Small-x term 3**: `H^{-1/2}G^{1/2}Ω^{5/2} ≤ X^{-(1-g)/10 + g/2 + 5u/2}` using `Ω ≤ U`. -/
theorem smallx_edge_T3 (P : Globals) (S : Scale P) (hΩU : S.Ω ≤ P.U) :
    P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)
      ≤ P.X ^ (-(1 - P.g)/10 + P.g/2 + 5*P.u/2) := by
  have hX := P.X_pos
  have hΩ52 : S.Ω ^ (5/2 : ℝ) ≤ P.X ^ (P.u * (5/2)) := omega_le_U_rpow P S (by norm_num) hΩU
  have hH12 : P.H ^ (-1/2 : ℝ) = P.X ^ (-(1 - P.g)/10) := by
    rw [Globals.H, ← Real.rpow_mul hX.le]; congr 1; ring
  have hG12 : P.G ^ (1/2 : ℝ) = P.X ^ (P.g/2) := by
    rw [Globals.G, ← Real.rpow_mul hX.le]; congr 1; ring
  calc P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)
      ≤ P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * P.X ^ (P.u * (5/2)) :=
        mul_le_mul_of_nonneg_left hΩ52
          (mul_nonneg (Real.rpow_nonneg P.H_pos.le _) (Real.rpow_nonneg P.G_pos.le _))
    _ = P.X ^ (-(1 - P.g)/10 + P.g/2 + 5*P.u/2) := by
        rw [hH12, hG12, ← Real.rpow_add hX, ← Real.rpow_add hX]; congr 1; ring

/-! #### Large-x branch (Prop 5.1) -/

/-- The Prop 5.1 constant, named. -/
noncomputable def C5 : ℝ := prop_5_1.choose

theorem C5_pos : 0 < C5 := prop_5_1.choose_spec.1

/-- Prop 5.1, specialised with its constant named `C5`. -/
theorem prop_5_1_spec (P : Globals) (S : Scale P) (a : ℤ) (ha : 0 < a) (Ra : Finset ℕ)
    (h1 : ∃ c : ℝ, 0 < c ∧ c * (P.G * P.U ^ 10) ≤ P.H / S.Δ ^ 2)
    (h2 : ∃ c : ℝ, 0 < c ∧ c * (P.G ^ 2 * P.U ^ 5) ≤ S.Δ)
    (h3 : ∃ c : ℝ, 0 < c ∧ c * (S.R / P.Wval) ≤ (Ra.card : ℝ)) :
    (Ra.card : ℝ) ≤ C5 * (P.H / S.Δ) *
      ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
      + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
      + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 ) :=
  prop_5_1.choose_spec.2 P S a ha Ra h1 h2 h3

/-- For nonpositive `p`, `Δ^p ≤ X^{(1/100)·p}` from `Δ ≥ X^{1/100}`. -/
theorem deltaPow_neg_le (P : Globals) (S : Scale P) (hX : 1 ≤ P.X)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ) {p : ℝ} (hp : p ≤ 0) :
    S.Δ ^ p ≤ P.X ^ ((1/100 : ℝ) * p) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hpos : (0:ℝ) < P.X ^ (1/100 : ℝ) := Real.rpow_pos_of_pos hX0 _
  calc S.Δ ^ p ≤ (P.X ^ (1/100 : ℝ)) ^ p := Real.rpow_le_rpow_of_nonpos hpos hΔlong hp
    _ = P.X ^ ((1/100 : ℝ) * p) := by rw [← Real.rpow_mul hX0.le]

/-- Edge bound for the large-`x` branch: `x ≥ G^{17}Ω^{-26}X^{Cu·u}` ⟹
`Δ² ≤ H·G^{-17}·Ω^{26}·X^{-Cu·u}` (since `x = H/Δ²`). -/
theorem delta_sq_edge_le (P : Globals) (S : Scale P) (Cu : ℝ)
    (hx : P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) ≤ S.x) :
    S.Δ ^ 2 ≤ P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))) := by
  have hX := P.X_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  -- x = H/Δ², so Δ² = H/x ≤ H / (G^17 Ω^{-26} X^{Cu u})
  have hxpos : 0 < S.x := by unfold Scale.x; positivity
  have hxval : S.x = P.H / S.Δ ^ 2 := rfl
  have hrhs_pos : 0 < P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) := by positivity
  -- Δ² = H/x
  have hΔ2 : S.Δ ^ 2 = P.H / S.x := by rw [hxval]; field_simp
  rw [hΔ2]
  rw [div_le_iff₀ hxpos]
  rw [show P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))) * S.x
        = P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u)) * S.x) by ring]
  -- want H ≤ H·(G^{-17}Ω^{26}X^{-Cu u}·x); i.e. 1 ≤ G^{-17}Ω^{26}X^{-Cu u}·x
  refine le_mul_of_one_le_right hH.le ?_
  -- G^{-17}Ω^{26}X^{-Cu u}·x ≥ G^{-17}Ω^{26}X^{-Cu u}·(G^17 Ω^{-26}X^{Cu u}) = 1
  have hcoef_pos : 0 < P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hx hcoef_pos.le
  refine le_trans ?_ hmul
  have hGnat : P.G ^ (17 : ℕ) = P.G ^ (17 : ℝ) := by
    rw [← Real.rpow_natCast P.G 17]; norm_num
  have hprod : P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))
        * (P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u)) = 1 := by
    have e1 : P.G ^ (-17 : ℝ) * P.G ^ 17 = 1 := by
      rw [hGnat, ← Real.rpow_add hG]; norm_num
    have e2 : S.Ω ^ (26 : ℝ) * S.Ω ^ (-26 : ℝ) = 1 := by
      rw [← Real.rpow_add hΩ]; norm_num
    have e3 : P.X ^ (-(Cu * P.u)) * P.X ^ (Cu * P.u) = 1 := by
      rw [← Real.rpow_add hX]; norm_num
    calc P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))
          * (P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u))
        = (P.G ^ (-17 : ℝ) * P.G ^ 17) * (S.Ω ^ (26 : ℝ) * S.Ω ^ (-26 : ℝ))
            * (P.X ^ (-(Cu * P.u)) * P.X ^ (Cu * P.u)) := by ring
      _ = 1 := by rw [e1, e2, e3]; norm_num
  rw [hprod]

/-- `Wval = G·U⁵`. -/
theorem Wval_eq (P : Globals) : P.Wval = P.G * P.U ^ 5 := rfl

/-- **Fiber × prop-5.1 monomial**: if `q ≤ c·H·X^e` with `e ≤ -3u` and `c ≥ 0`, then
`(1+φ)·q ≤ (1+c₀^{-8/3})·c·(H/U)` (the `+2u` fiber budget fits in the `-3u → -u` margin). -/
theorem fiber_prop_term (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hX : 1 ≤ P.X) (hu : 0 < P.u)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω)
    {q c e : ℝ} (hc : 0 ≤ c) (hqnn : 0 ≤ q) (hq : q ≤ c * P.H * P.X ^ e)
    (he : e ≤ -3 * P.u) :
    (1 + fiberφ P S) * q ≤ (1 + c₀ ^ (-8/3 : ℝ)) * c * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hH := P.H_pos
  have hφbud := fiber_factor_budget P S c₀ hc₀ hX hu hband  -- 1+φ ≤ (1+c₀^{-8/3})X^{2u}
  rw [← fiberφ_def] at hφbud
  set Bf : ℝ := 1 + c₀ ^ (-8/3 : ℝ) with hBf
  have hBfnn : 0 ≤ Bf := by rw [hBf]; positivity
  have hX2u : 0 ≤ P.X ^ (2 * P.u) := Real.rpow_nonneg hX0.le _
  -- (1+φ)·q ≤ (Bf·X^{2u})·(c·H·X^e) = Bf·c·H·X^{e+2u} ≤ Bf·c·H/U
  have hXprodle : P.X ^ (2 * P.u) * P.X ^ e ≤ (P.U)⁻¹ := by
    rw [← Real.rpow_add hX0]
    exact Budget.rpow_le_Uinv P hX (by linarith [he])
  have hXprod_nn : 0 ≤ P.X ^ (2 * P.u) * P.X ^ e := by positivity
  calc (1 + fiberφ P S) * q
      ≤ (Bf * P.X ^ (2 * P.u)) * (c * P.H * P.X ^ e) :=
        mul_le_mul hφbud hq hqnn (mul_nonneg hBfnn hX2u)
    _ = Bf * c * P.H * (P.X ^ (2 * P.u) * P.X ^ e) := by ring
    _ ≤ Bf * c * P.H * (P.U)⁻¹ :=
        mul_le_mul_of_nonneg_left hXprodle (mul_nonneg (mul_nonneg hBfnn hc) hH.le)
    _ = Bf * c * (P.H / P.U) := by rw [div_eq_mul_inv]; ring

/-- `G^(n:ℕ) = X^{g·n}`, `U^(n:ℕ) = X^{u·n}`, as helpers feeding nat-powers into rpow algebra. -/
private theorem Gnat_xpow (P : Globals) (n : ℕ) : P.G ^ n = P.X ^ (P.g * n) := by
  rw [Globals.G, ← Real.rpow_natCast (P.X ^ P.g) n, ← Real.rpow_mul P.X_pos.le]
private theorem Unat_xpow (P : Globals) (n : ℕ) : P.U ^ n = P.X ^ (P.u * n) := by
  rw [Globals.U, ← Real.rpow_natCast (P.X ^ P.u) n, ← Real.rpow_mul P.X_pos.le]

/-- **Main term 1** `A·(H/Δ)·P₁ = H·G⁹U⁵¹·Δ^{-1/2} ≤ H·X^{9g+51u-1/200}` (via `Δ ≥ X^{1/100}`). -/
theorem largex_main_P1 (P : Globals) (S : Scale P) (hX : 1 ≤ P.X)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ) :
    S.A * (P.H / S.Δ) * (P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω))
      ≤ (1 : ℝ) * P.H * P.X ^ (9 * P.g + 51 * P.u + (1/100 : ℝ) * (-1/2)) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos
  -- A·(H/Δ)·P₁ = H·G⁹·U⁵¹·Δ^{-1/2}
  have hΔhalf : (0:ℝ) < S.Δ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hΔ _
  have heq : S.A * (P.H / S.Δ) * (P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω))
      = P.H * (P.G ^ 9 * P.U ^ 51) * S.Δ ^ (-1/2 : ℝ) := by
    unfold Scale.A
    rw [show S.Δ ^ (-1/2 : ℝ) = (S.Δ ^ (1/2 : ℝ))⁻¹ by
          rw [← Real.rpow_neg hΔ.le]; norm_num]
    field_simp
  rw [heq]
  have hΔneg : S.Δ ^ (-1/2 : ℝ) ≤ P.X ^ ((1/100 : ℝ) * (-1/2)) :=
    deltaPow_neg_le P S hX hΔlong (by norm_num)
  have hGU_nn : (0:ℝ) ≤ P.H * (P.G ^ 9 * P.U ^ 51) := by
    have := hH; have := hG; have := P.U_pos; positivity
  have hxpow : P.G ^ 9 * P.U ^ 51 * P.X ^ ((1/100 : ℝ) * (-1/2))
      = P.X ^ (9 * P.g + 51 * P.u + (1/100 : ℝ) * (-1/2)) := by
    rw [Gnat_xpow, Unat_xpow, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 1; push_cast; ring
  calc P.H * (P.G ^ 9 * P.U ^ 51) * S.Δ ^ (-1/2 : ℝ)
      ≤ P.H * (P.G ^ 9 * P.U ^ 51) * P.X ^ ((1/100 : ℝ) * (-1/2)) :=
        mul_le_mul_of_nonneg_left hΔneg hGU_nn
    _ = (1 : ℝ) * P.H * P.X ^ (9 * P.g + 51 * P.u + (1/100 : ℝ) * (-1/2)) := by
        rw [show P.H * (P.G ^ 9 * P.U ^ 51) * P.X ^ ((1/100 : ℝ) * (-1/2))
              = P.H * (P.G ^ 9 * P.U ^ 51 * P.X ^ ((1/100 : ℝ) * (-1/2))) by ring, hxpow]
        ring

/-- **Main term 2** `A·(H/Δ)·P₂ = H·G¹⁷U⁸⁵·Δ^{-1}·Ω^{-12} ≤ c₀^{-12}·H·X^{20g+94u-1/100}`. -/
theorem largex_main_P2 (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀) (hX : 1 ≤ P.X)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    S.A * (P.H / S.Δ) * (P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13))
      ≤ c₀ ^ (-12 : ℝ) * P.H *
        P.X ^ (17 * P.g + 85 * P.u + (1/100 : ℝ) * (-1) + (-P.g/4 - 3*P.u/4) * (-12)) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos
  have hΩ13 : (S.Ω ^ 13 : ℝ) = S.Ω ^ (13 : ℝ) := Ωnat S 13
  have hΔinv : S.Δ ^ (-1 : ℝ) = (S.Δ)⁻¹ := Real.rpow_neg_one S.Δ
  have hΩ12 : S.Ω ^ (-12 : ℝ) = S.Ω ^ (1:ℝ) * (S.Ω ^ (13:ℝ))⁻¹ := by
    rw [← Real.rpow_neg hΩ.le, ← Real.rpow_add hΩ]; norm_num
  have heq : S.A * (P.H / S.Δ) * (P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13))
      = P.H * (P.G ^ 17 * P.U ^ 85) * (S.Δ ^ (-1 : ℝ) * S.Ω ^ (-12 : ℝ)) := by
    rw [hΔinv, hΩ12, hΩ13, Real.rpow_one]
    unfold Scale.A
    field_simp
  rw [heq]
  have hΔneg : S.Δ ^ (-1 : ℝ) ≤ P.X ^ ((1/100 : ℝ) * (-1)) :=
    deltaPow_neg_le P S hX hΔlong (by norm_num)
  have hΩneg : S.Ω ^ (-12 : ℝ) ≤ c₀ ^ (-12 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12)) :=
    band_rpow_neg P S c₀ hc₀ (by norm_num) hband
  have hGU_nn : (0:ℝ) ≤ P.H * (P.G ^ 17 * P.U ^ 85) := by
    have := hG; have := P.U_pos; positivity
  have hxpow : P.G ^ 17 * P.U ^ 85 * (P.X ^ ((1/100 : ℝ) * (-1))
        * (c₀ ^ (-12 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12))))
      = c₀ ^ (-12 : ℝ) *
          P.X ^ (17 * P.g + 85 * P.u + (1/100 : ℝ) * (-1) + (-P.g/4 - 3*P.u/4) * (-12)) := by
    rw [Gnat_xpow, Unat_xpow]
    rw [show P.X ^ (P.g * (17:ℕ)) * P.X ^ (P.u * (85:ℕ)) * (P.X ^ ((1/100 : ℝ) * (-1))
          * (c₀ ^ (-12 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12))))
        = c₀ ^ (-12 : ℝ) * (P.X ^ (P.g * (17:ℕ)) * P.X ^ (P.u * (85:ℕ)) * P.X ^ ((1/100 : ℝ) * (-1))
            * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12))) by ring]
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 2; push_cast; ring
  calc P.H * (P.G ^ 17 * P.U ^ 85) * (S.Δ ^ (-1 : ℝ) * S.Ω ^ (-12 : ℝ))
      ≤ P.H * (P.G ^ 17 * P.U ^ 85)
          * (P.X ^ ((1/100 : ℝ) * (-1)) * (c₀ ^ (-12 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12)))) := by
        apply mul_le_mul_of_nonneg_left _ hGU_nn
        exact mul_le_mul hΔneg hΩneg (by positivity) (by positivity)
    _ = c₀ ^ (-12 : ℝ) * P.H *
          P.X ^ (17 * P.g + 85 * P.u + (1/100 : ℝ) * (-1) + (-P.g/4 - 3*P.u/4) * (-12)) := by
        rw [show P.H * (P.G ^ 17 * P.U ^ 85) * (P.X ^ ((1/100 : ℝ) * (-1))
              * (c₀ ^ (-12 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12))))
            = P.H * (P.G ^ 17 * P.U ^ 85 * (P.X ^ ((1/100 : ℝ) * (-1))
              * (c₀ ^ (-12 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-12))))) by ring, hxpow]
        ring

/-- **Main term 3** (binding) `A·(H/Δ)·P₃ = Δ²·G¹⁷U¹⁰⁰·Ω^{-26} ≤ H·U¹⁰⁰·X^{-Cu·u}` via the edge
`x ≥ G¹⁷Ω^{-26}X^{Cu·u}`. -/
theorem largex_main_P3 (P : Globals) (S : Scale P) (Cu : ℝ) (hX : 1 ≤ P.X)
    (hx : P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) ≤ S.x) :
    S.A * (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27)
      ≤ (1 : ℝ) * P.H * P.X ^ (100 * P.u - Cu * P.u) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos
  have hΩ27 : (S.Ω ^ 27 : ℝ) = S.Ω ^ (27 : ℝ) := Ωnat S 27
  have hΩ26 : (S.Ω ^ (26 : ℝ) : ℝ) = S.Ω ^ (26 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  -- A·(H/Δ)·P₃ = Δ²·G¹⁷U¹⁰⁰·Ω^{-26}
  have heq : S.A * (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27)
      = S.Δ ^ 2 * (P.G ^ 17 * P.U ^ 100) * S.Ω ^ (-26 : ℝ) := by
    have hΩneg26 : S.Ω ^ (-26 : ℝ) = S.Ω ^ (1:ℝ) * (S.Ω ^ (27:ℝ))⁻¹ := by
      rw [← Real.rpow_neg hΩ.le, ← Real.rpow_add hΩ]; norm_num
    rw [hΩneg26, hΩ27, Real.rpow_one]
    unfold Scale.A
    field_simp
  rw [heq]
  -- substitute Δ² ≤ H·G^{-17}Ω^{26}X^{-Cu u}
  have hΔ2 := delta_sq_edge_le P S Cu hx
  have hrest_nn : (0:ℝ) ≤ P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-26 : ℝ) := by
    have := hG; have := P.U_pos; positivity
  have hΔ2_nn : (0:ℝ) ≤ S.Δ ^ 2 := by positivity
  -- Δ² · (G¹⁷U¹⁰⁰Ω^{-26}) ≤ (H G^{-17}Ω^{26}X^{-Cu u}) · (G¹⁷U¹⁰⁰Ω^{-26})
  have hstep : S.Δ ^ 2 * (P.G ^ 17 * P.U ^ 100) * S.Ω ^ (-26 : ℝ)
      ≤ (P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))))
          * (P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-26 : ℝ)) := by
    rw [show S.Δ ^ 2 * (P.G ^ 17 * P.U ^ 100) * S.Ω ^ (-26 : ℝ)
          = S.Δ ^ 2 * (P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-26 : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_right hΔ2 hrest_nn
  refine hstep.trans (le_of_eq ?_)
  -- collapse: H·G^{-17}·G¹⁷ = H, Ω^{26}·Ω^{-26}=1, U¹⁰⁰=X^{100u}, X^{-Cu u}
  have hGcol : P.G ^ (-17 : ℝ) * P.G ^ 17 = 1 := by
    rw [show (P.G : ℝ) ^ 17 = P.G ^ (17 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
        ← Real.rpow_add hG]; norm_num
  have hΩcol : S.Ω ^ (26 : ℝ) * S.Ω ^ (-26 : ℝ) = 1 := by
    rw [← Real.rpow_add hΩ]; norm_num
  rw [Unat_xpow]
  rw [show (P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u))))
        * (P.G ^ 17 * P.X ^ (P.u * (100:ℕ)) * S.Ω ^ (-26 : ℝ))
      = P.H * (P.G ^ (-17 : ℝ) * P.G ^ 17) * (S.Ω ^ (26 : ℝ) * S.Ω ^ (-26 : ℝ))
          * (P.X ^ (-(Cu * P.u)) * P.X ^ (P.u * (100:ℕ))) by ring,
      hGcol, hΩcol, ← Real.rpow_add hX0]
  rw [show (1:ℝ) * P.H * P.X ^ (100 * P.u - Cu * P.u)
        = P.H * P.X ^ (100 * P.u - Cu * P.u) by ring]
  congr 2
  · ring
  · push_cast; ring

/-- **`+1` term 1** `(H/Δ)·P₁ = H·G⁹U⁵¹·Δ^{-3/2}·Ω^{-1} ≤ c₀^{-1}·H·X^{9g+51u-3/200+(-g/4-3u/4)(-1)}`. -/
theorem largex_plus_P1 (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀) (hX : 1 ≤ P.X)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    (P.H / S.Δ) * (P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω))
      ≤ c₀ ^ (-1 : ℝ) * P.H *
        P.X ^ (9 * P.g + 51 * P.u + (1/100 : ℝ) * (-3/2) + (-P.g/4 - 3*P.u/4) * (-1)) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos
  have hΔ12 : (0:ℝ) < S.Δ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hΔ _
  have heq : (P.H / S.Δ) * (P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω))
      = P.H * (P.G ^ 9 * P.U ^ 51) * (S.Δ ^ (-3/2 : ℝ) * S.Ω ^ (-1 : ℝ)) := by
    have hΔc : S.Δ ^ (-3/2 : ℝ) = (S.Δ)⁻¹ * (S.Δ ^ (1/2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one S.Δ, ← Real.rpow_neg hΔ.le, ← Real.rpow_add hΔ]; norm_num
    rw [hΔc, Real.rpow_neg_one S.Ω]
    field_simp
  rw [heq]
  have hΔneg : S.Δ ^ (-3/2 : ℝ) ≤ P.X ^ ((1/100 : ℝ) * (-3/2)) :=
    deltaPow_neg_le P S hX hΔlong (by norm_num)
  have hΩneg : S.Ω ^ (-1 : ℝ) ≤ c₀ ^ (-1 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1)) :=
    band_rpow_neg P S c₀ hc₀ (by norm_num) hband
  have hGU_nn : (0:ℝ) ≤ P.H * (P.G ^ 9 * P.U ^ 51) := by
    have := hG; have := P.U_pos; positivity
  have hxpow : P.G ^ 9 * P.U ^ 51 * (P.X ^ ((1/100 : ℝ) * (-3/2))
        * (c₀ ^ (-1 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1))))
      = c₀ ^ (-1 : ℝ) *
          P.X ^ (9 * P.g + 51 * P.u + (1/100 : ℝ) * (-3/2) + (-P.g/4 - 3*P.u/4) * (-1)) := by
    rw [Gnat_xpow, Unat_xpow,
        show P.X ^ (P.g * (9:ℕ)) * P.X ^ (P.u * (51:ℕ)) * (P.X ^ ((1/100 : ℝ) * (-3/2))
          * (c₀ ^ (-1 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1))))
        = c₀ ^ (-1 : ℝ) * (P.X ^ (P.g * (9:ℕ)) * P.X ^ (P.u * (51:ℕ)) * P.X ^ ((1/100 : ℝ) * (-3/2))
            * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1))) by ring,
        ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 2; push_cast; ring
  calc P.H * (P.G ^ 9 * P.U ^ 51) * (S.Δ ^ (-3/2 : ℝ) * S.Ω ^ (-1 : ℝ))
      ≤ P.H * (P.G ^ 9 * P.U ^ 51)
          * (P.X ^ ((1/100 : ℝ) * (-3/2)) * (c₀ ^ (-1 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1)))) := by
        apply mul_le_mul_of_nonneg_left _ hGU_nn
        exact mul_le_mul hΔneg hΩneg (by positivity) (by positivity)
    _ = c₀ ^ (-1 : ℝ) * P.H *
          P.X ^ (9 * P.g + 51 * P.u + (1/100 : ℝ) * (-3/2) + (-P.g/4 - 3*P.u/4) * (-1)) := by
        rw [show P.H * (P.G ^ 9 * P.U ^ 51) * (P.X ^ ((1/100 : ℝ) * (-3/2))
              * (c₀ ^ (-1 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1))))
            = P.H * (P.G ^ 9 * P.U ^ 51 * (P.X ^ ((1/100 : ℝ) * (-3/2))
              * (c₀ ^ (-1 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-1))))) by ring, hxpow]
        ring

/-- **`+1` term 2** `(H/Δ)·P₂ = H·G¹⁷U⁸⁵·Δ^{-2}·Ω^{-13} ≤ c₀^{-13}·H·X^{17g+85u-1/50+(-g/4-3u/4)(-13)}`. -/
theorem largex_plus_P2 (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 0 < c₀) (hX : 1 ≤ P.X)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    (P.H / S.Δ) * (P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13))
      ≤ c₀ ^ (-13 : ℝ) * P.H *
        P.X ^ (17 * P.g + 85 * P.u + (1/100 : ℝ) * (-2) + (-P.g/4 - 3*P.u/4) * (-13)) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos
  have hΩ13 : (S.Ω ^ 13 : ℝ) = S.Ω ^ (13 : ℝ) := Ωnat S 13
  have heq : (P.H / S.Δ) * (P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13))
      = P.H * (P.G ^ 17 * P.U ^ 85) * (S.Δ ^ (-2 : ℝ) * S.Ω ^ (-13 : ℝ)) := by
    have hΔc : S.Δ ^ (-2 : ℝ) = (S.Δ)⁻¹ * (S.Δ)⁻¹ := by
      rw [← Real.rpow_neg_one S.Δ, ← Real.rpow_add hΔ]; norm_num
    have hΩc : S.Ω ^ (-13 : ℝ) = (S.Ω ^ (13:ℝ))⁻¹ := by
      rw [← Real.rpow_neg hΩ.le]
    rw [hΔc, hΩc, hΩ13]
    field_simp
  rw [heq]
  have hΔneg : S.Δ ^ (-2 : ℝ) ≤ P.X ^ ((1/100 : ℝ) * (-2)) :=
    deltaPow_neg_le P S hX hΔlong (by norm_num)
  have hΩneg : S.Ω ^ (-13 : ℝ) ≤ c₀ ^ (-13 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13)) :=
    band_rpow_neg P S c₀ hc₀ (by norm_num) hband
  have hGU_nn : (0:ℝ) ≤ P.H * (P.G ^ 17 * P.U ^ 85) := by
    have := hG; have := P.U_pos; positivity
  have hxpow : P.G ^ 17 * P.U ^ 85 * (P.X ^ ((1/100 : ℝ) * (-2))
        * (c₀ ^ (-13 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13))))
      = c₀ ^ (-13 : ℝ) *
          P.X ^ (17 * P.g + 85 * P.u + (1/100 : ℝ) * (-2) + (-P.g/4 - 3*P.u/4) * (-13)) := by
    rw [Gnat_xpow, Unat_xpow,
        show P.X ^ (P.g * (17:ℕ)) * P.X ^ (P.u * (85:ℕ)) * (P.X ^ ((1/100 : ℝ) * (-2))
          * (c₀ ^ (-13 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13))))
        = c₀ ^ (-13 : ℝ) * (P.X ^ (P.g * (17:ℕ)) * P.X ^ (P.u * (85:ℕ)) * P.X ^ ((1/100 : ℝ) * (-2))
            * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13))) by ring,
        ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 2; push_cast; ring
  calc P.H * (P.G ^ 17 * P.U ^ 85) * (S.Δ ^ (-2 : ℝ) * S.Ω ^ (-13 : ℝ))
      ≤ P.H * (P.G ^ 17 * P.U ^ 85)
          * (P.X ^ ((1/100 : ℝ) * (-2)) * (c₀ ^ (-13 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13)))) := by
        apply mul_le_mul_of_nonneg_left _ hGU_nn
        exact mul_le_mul hΔneg hΩneg (by positivity) (by positivity)
    _ = c₀ ^ (-13 : ℝ) * P.H *
          P.X ^ (17 * P.g + 85 * P.u + (1/100 : ℝ) * (-2) + (-P.g/4 - 3*P.u/4) * (-13)) := by
        rw [show P.H * (P.G ^ 17 * P.U ^ 85) * (P.X ^ ((1/100 : ℝ) * (-2))
              * (c₀ ^ (-13 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13))))
            = P.H * (P.G ^ 17 * P.U ^ 85 * (P.X ^ ((1/100 : ℝ) * (-2))
              * (c₀ ^ (-13 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-13))))) by ring, hxpow]
        ring

/-- **`+1` term 3** `(H/Δ)·P₃ = Δ·G¹⁷U¹⁰⁰·Ω^{-27}`.  Via the edge `Δ ≤ H^{1/2}G^{-17/2}Ω^{13}X^{-Cu·u/2}`
and the band on `Ω^{-14}`, this is `≤ c₀^{-14}·H·X^{e}` with
`e = -(1-g)/10 + 17g/2 + 100u + (-g/4-3u/4)(-14) - Cu·u/2`. -/
theorem largex_plus_P3 (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (hc₀ : 0 < c₀) (hX : 1 ≤ P.X)
    (hx : P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) ≤ S.x)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω) :
    (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27)
      ≤ c₀ ^ (-14 : ℝ) * P.H *
        P.X ^ ((-(1 - P.g))/10 + 17 * P.g / 2 + 100 * P.u
          + (-P.g/4 - 3*P.u/4) * (-14) - Cu * P.u / 2) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos
  have hHne : P.H ≠ 0 := ne_of_gt hH
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔ
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩ
  -- (H/Δ)·P₃ = Δ·G¹⁷U¹⁰⁰·Ω^{-27}
  have hΩ27nat : S.Ω ^ (-27 : ℝ) = (S.Ω ^ (27:ℕ))⁻¹ := by
    rw [← Real.rpow_natCast S.Ω 27, ← Real.rpow_neg hΩ.le]; norm_num
  have heq : (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27)
      = S.Δ * (P.G ^ 17 * P.U ^ 100) * S.Ω ^ (-27 : ℝ) := by
    rw [hΩ27nat]; field_simp
  rw [heq]
  -- Δ ≤ sqrt(H G^{-17}Ω^{26}X^{-Cu u}), expand
  have hΔ2 := delta_sq_edge_le P S Cu hx
  have hΔeq : S.Δ = (S.Δ ^ 2) ^ (1/2 : ℝ) := by
    rw [← Real.rpow_natCast S.Δ 2, ← Real.rpow_mul hΔ.le]; norm_num
  have hΔle : S.Δ ≤ (P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u)))) ^ (1/2 : ℝ) := by
    rw [hΔeq]; exact Real.rpow_le_rpow (by positivity) hΔ2 (by norm_num)
  have hsqrt : (P.H * (P.G ^ (-17 : ℝ) * S.Ω ^ (26 : ℝ) * P.X ^ (-(Cu * P.u)))) ^ (1/2 : ℝ)
      = P.H ^ (1/2 : ℝ) * P.G ^ (-17/2 : ℝ) * S.Ω ^ (13 : ℝ) * P.X ^ (-(Cu * P.u) / 2) := by
    rw [Real.mul_rpow hH.le (by positivity),
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hX0.le _),
        Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hΩ.le _),
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le, ← Real.rpow_mul hX0.le]
    rw [show (-(Cu * P.u)) * (1/2 : ℝ) = -(Cu * P.u) / 2 by ring,
        show (-17 : ℝ) * (1/2) = -17/2 by norm_num,
        show (26 : ℝ) * (1/2) = 13 by norm_num]
    ring
  have hmid_nn : (0:ℝ) ≤ P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-27 : ℝ) := by
    have := hG; have := P.U_pos; positivity
  have hstep : S.Δ * (P.G ^ 17 * P.U ^ 100) * S.Ω ^ (-27 : ℝ)
      ≤ (P.H ^ (1/2 : ℝ) * P.G ^ (-17/2 : ℝ) * S.Ω ^ (13 : ℝ) * P.X ^ (-(Cu * P.u) / 2))
          * (P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-27 : ℝ)) := by
    rw [show S.Δ * (P.G ^ 17 * P.U ^ 100) * S.Ω ^ (-27 : ℝ)
          = S.Δ * (P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-27 : ℝ)) by ring]
    refine mul_le_mul_of_nonneg_right ?_ hmid_nn
    rw [← hsqrt]; exact hΔle
  refine hstep.trans ?_
  -- collapse to a clean monomial in X (and c₀)
  have hΩcol : S.Ω ^ (13 : ℝ) * S.Ω ^ (-27 : ℝ) = S.Ω ^ (-14 : ℝ) := by
    rw [← Real.rpow_add hΩ]; norm_num
  have hΩneg : S.Ω ^ (-14 : ℝ) ≤ c₀ ^ (-14 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-14)) :=
    band_rpow_neg P S c₀ hc₀ (by norm_num) hband
  have hH12 : P.H ^ (1/2 : ℝ) = P.H * P.H ^ (-1/2 : ℝ) := by
    rw [show P.H * P.H ^ (-1/2 : ℝ) = P.H ^ (1:ℝ) * P.H ^ (-1/2 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hH]; norm_num
  have hH12x : P.H ^ (-1/2 : ℝ) = P.X ^ ((-(1 - P.g))/10) := by
    rw [Globals.H, ← Real.rpow_mul hX0.le]; congr 1; ring
  have hG17 : (P.G : ℝ) ^ 17 = P.G ^ (17 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hGx : P.G ^ (-17/2 : ℝ) * P.G ^ (17 : ℝ) = P.X ^ (P.g * (17/2 : ℝ)) := by
    rw [← Real.rpow_add hG, Globals.G, ← Real.rpow_mul hX0.le]; congr 1; norm_num
  rw [show (P.H ^ (1/2 : ℝ) * P.G ^ (-17/2 : ℝ) * S.Ω ^ (13 : ℝ) * P.X ^ (-(Cu * P.u) / 2))
        * (P.G ^ 17 * P.U ^ 100 * S.Ω ^ (-27 : ℝ))
      = P.H ^ (1/2 : ℝ) * (P.G ^ (-17/2 : ℝ) * P.G ^ 17) * (S.Ω ^ (13 : ℝ) * S.Ω ^ (-27 : ℝ))
          * (P.U ^ 100 * P.X ^ (-(Cu * P.u) / 2)) by ring]
  rw [hG17, hGx, hΩcol, hH12, hH12x, Unat_xpow]
  -- now: (H·X^{-(1-g)/10})·X^{g·17/2}·Ω^{-14}·(X^{u·100}·X^{-Cu u/2}) ≤ c₀^{-14}·H·X^E
  have hbound : P.H * P.X ^ ((-(1 - P.g))/10) * P.X ^ (P.g * (17/2 : ℝ)) * S.Ω ^ (-14 : ℝ)
        * (P.X ^ (P.u * (100:ℕ)) * P.X ^ (-(Cu * P.u) / 2))
      ≤ P.H * P.X ^ ((-(1 - P.g))/10) * P.X ^ (P.g * (17/2 : ℝ))
          * (c₀ ^ (-14 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-14)))
          * (P.X ^ (P.u * (100:ℕ)) * P.X ^ (-(Cu * P.u) / 2)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hΩneg (by positivity)
  refine hbound.trans (le_of_eq ?_)
  have hcombine : P.H * P.X ^ ((-(1 - P.g))/10) * P.X ^ (P.g * (17/2 : ℝ))
        * (c₀ ^ (-14 : ℝ) * P.X ^ ((-P.g/4 - 3*P.u/4) * (-14)))
        * (P.X ^ (P.u * (100:ℕ)) * P.X ^ (-(Cu * P.u) / 2))
      = c₀ ^ (-14 : ℝ) * P.H * (P.X ^ ((-(1 - P.g))/10) * P.X ^ (P.g * (17/2 : ℝ))
          * P.X ^ ((-P.g/4 - 3*P.u/4) * (-14)) * P.X ^ (P.u * (100:ℕ)) * P.X ^ (-(Cu * P.u) / 2)) := by
    ring
  rw [hcombine, ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
  congr 1
  push_cast; ring

/-! #### Large-x trivial term `R/Wval` (the per-`a` cap when `prop_5_1` does not apply)

`A·R/Wval = H·Ω⁴/U⁵` and `R/Wval = H·Ω³/(Δ·U⁵)`; these are killed directly by `Ω ≤ U`
(and `Δ ≥ X^{1/100}`), without spending the fiber budget, so the `(1+φ)` factor is split. -/

/-- `(1+φ)·A·(R/Wval) ≤ 2·(H/U)` via `Ω ≤ U` and `g ≥ 0`.  Here `φ = Ω^{-8/3}G^{-2/3}`. -/
theorem largex_triv_AR (P : Globals) (S : Scale P) (hg0 : 0 ≤ P.g) (hX : 1 ≤ P.X) (hu : 0 < P.u)
    (hΩU : S.Ω ≤ P.U) :
    (1 + fiberφ P S) * (S.A * (S.R / P.Wval)) ≤ 2 * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos; have hU := P.U_pos
  have hHUeq : P.H / P.U = P.H * P.X ^ (-P.u) := by
    rw [div_eq_mul_inv, Globals.U, ← Real.rpow_neg hX0.le]
  -- A·R/Wval = H·Ω⁴/U⁵
  have hΩ4r : S.Ω ^ (4:ℝ) = S.Ω ^ (4:ℕ) := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hARW : S.A * (S.R / P.Wval) = P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5) := by
    rw [hΩ4r, Wval_eq]; unfold Scale.A Scale.R; field_simp
  have hU5 : P.U ^ 5 = P.X ^ (P.u * 5) := by rw [Unat_xpow]; push_cast; ring_nf
  -- one-part: H·Ω⁴/U⁵ ≤ H·X^{-u}
  have hΩ4le : S.Ω ^ (4:ℝ) / P.U ^ 5 ≤ P.X ^ (-P.u) := by
    have hΩ4 : S.Ω ^ (4:ℝ) ≤ P.X ^ (P.u * 4) := omega_le_U_rpow P S (by norm_num) hΩU
    rw [hU5, div_le_iff₀ (by positivity)]
    refine hΩ4.trans (le_of_eq ?_)
    rw [← Real.rpow_add hX0]; congr 1; ring
  have hone : P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5) ≤ P.H * P.X ^ (-P.u) :=
    mul_le_mul_of_nonneg_left hΩ4le hH.le
  -- φ-part: φ·H·Ω⁴/U⁵ = H·Ω^{4/3}·G^{-2/3}/U⁵ ≤ H·X^{-u}
  have hφpart : fiberφ P S * (P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5)) ≤ P.H * P.X ^ (-P.u) := by
    have hφ : fiberφ P S = S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ) := by rw [fiberφ_def, deltaA_pow_eq]
    have hΩcol : S.Ω ^ (-8/3:ℝ) * S.Ω ^ (4:ℝ) = S.Ω ^ (4/3:ℝ) := by
      rw [← Real.rpow_add hΩ]; norm_num
    have hval : fiberφ P S * (P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5))
        = P.H * (S.Ω ^ (4/3:ℝ) * P.G ^ (-2/3:ℝ) / P.U ^ 5) := by
      rw [hφ]
      rw [show S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ) * (P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5))
            = P.H * ((S.Ω ^ (-8/3:ℝ) * S.Ω ^ (4:ℝ)) * P.G ^ (-2/3:ℝ) / P.U ^ 5) by ring, hΩcol]
    rw [hval]
    refine mul_le_mul_of_nonneg_left ?_ hH.le
    have hΩ43 : S.Ω ^ (4/3:ℝ) ≤ P.X ^ (P.u * (4/3)) := omega_le_U_rpow P S (by norm_num) hΩU
    have hG23 : P.G ^ (-2/3:ℝ) = P.X ^ (P.g * (-2/3)) := by
      rw [Globals.G, ← Real.rpow_mul hX0.le]
    rw [hG23, hU5, div_le_iff₀ (by positivity)]
    have : (0:ℝ) < P.X ^ (P.u * 5) := by positivity
    calc S.Ω ^ (4/3:ℝ) * P.X ^ (P.g * (-2/3))
        ≤ P.X ^ (P.u * (4/3)) * P.X ^ (P.g * (-2/3)) :=
          mul_le_mul_of_nonneg_right hΩ43 (by positivity)
      _ = P.X ^ (P.u * (4/3) + P.g * (-2/3)) := by rw [← Real.rpow_add hX0]
      _ ≤ P.X ^ (-P.u + P.u * 5) := by
          apply Real.rpow_le_rpow_of_exponent_le hX
          nlinarith [hg0, hu]
      _ = P.X ^ (-P.u) * P.X ^ (P.u * 5) := by rw [← Real.rpow_add hX0]
  -- combine
  rw [hARW, hHUeq]
  have hφnn : 0 ≤ fiberφ P S := by
    rw [fiberφ_def]
    have hDA : (0:ℝ) ≤ S.Δ / S.A := by
      have : (0:ℝ) < S.A := by unfold Scale.A; positivity
      positivity
    exact mul_nonneg (Real.rpow_nonneg hDA _) (Real.rpow_nonneg hG.le _)
  calc (1 + fiberφ P S) * (P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5))
      = (P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5)) + fiberφ P S * (P.H * (S.Ω ^ (4:ℝ) / P.U ^ 5)) := by ring
    _ ≤ P.H * P.X ^ (-P.u) + P.H * P.X ^ (-P.u) := add_le_add hone hφpart
    _ = 2 * (P.H * P.X ^ (-P.u)) := by ring

/-- `(1+φ)·(R/Wval) ≤ 2·(H/U)` (the per-`a` `+1` overhead) via `Ω ≤ U`, `Δ ≥ X^{1/100}`, `g ≥ 0`. -/
theorem largex_triv_R (P : Globals) (S : Scale P) (hg0 : 0 ≤ P.g) (hX : 1 ≤ P.X) (hu : 0 < P.u)
    (hΔlong : P.X ^ (1/100 : ℝ) ≤ S.Δ) (hΩU : S.Ω ≤ P.U) :
    (1 + fiberφ P S) * (S.R / P.Wval) ≤ 2 * (P.H / P.U) := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos; have hH := P.H_pos; have hU := P.U_pos
  have hHUeq : P.H / P.U = P.H * P.X ^ (-P.u) := by
    rw [div_eq_mul_inv, Globals.U, ← Real.rpow_neg hX0.le]
  have hU5 : P.U ^ 5 = P.X ^ (P.u * 5) := by rw [Unat_xpow]; push_cast; ring_nf
  have hdinv := deltaInv_le P S hX hΔlong  -- Δ⁻¹ ≤ X^{-1/100}
  -- R/Wval = H·Ω³·Δ⁻¹/U⁵
  have hΩ3r : S.Ω ^ (3:ℝ) = S.Ω ^ (3:ℕ) := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hRW : S.R / P.Wval = P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5) := by
    rw [hΩ3r, Wval_eq]; unfold Scale.R; field_simp
  -- 1-part: H·Ω³·Δ⁻¹/U⁵ ≤ H·X^{-u}
  have hΔinvnn : (0:ℝ) ≤ S.Δ⁻¹ := by positivity
  have hone : S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5 ≤ P.X ^ (-P.u) := by
    have hΩ3 : S.Ω ^ (3:ℝ) ≤ P.X ^ (P.u * 3) := omega_le_U_rpow P S (by norm_num) hΩU
    rw [hU5, div_le_iff₀ (by positivity)]
    calc S.Ω ^ (3:ℝ) * S.Δ⁻¹ ≤ P.X ^ (P.u * 3) * P.X ^ (-1/100 : ℝ) :=
          mul_le_mul hΩ3 hdinv hΔinvnn (by positivity)
      _ = P.X ^ (P.u * 3 + (-1/100)) := by rw [← Real.rpow_add hX0]
      _ ≤ P.X ^ (-P.u + P.u * 5) := by
          apply Real.rpow_le_rpow_of_exponent_le hX; nlinarith [hu]
      _ = P.X ^ (-P.u) * P.X ^ (P.u * 5) := by rw [← Real.rpow_add hX0]
  -- φ-part: φ·H·Ω³·Δ⁻¹/U⁵ = H·Ω^{1/3}·G^{-2/3}·Δ⁻¹/U⁵ ≤ H·X^{-u}
  have hφpart : fiberφ P S * (P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5)) ≤ P.H * P.X ^ (-P.u) := by
    have hφ : fiberφ P S = S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ) := by rw [fiberφ_def, deltaA_pow_eq]
    have hΩcol : S.Ω ^ (-8/3:ℝ) * S.Ω ^ (3:ℝ) = S.Ω ^ (1/3:ℝ) := by
      rw [← Real.rpow_add hΩ]; norm_num
    have hval : fiberφ P S * (P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5))
        = P.H * (S.Ω ^ (1/3:ℝ) * P.G ^ (-2/3:ℝ) * S.Δ⁻¹ / P.U ^ 5) := by
      rw [hφ]
      rw [show S.Ω ^ (-8/3:ℝ) * P.G ^ (-2/3:ℝ) * (P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5))
            = P.H * ((S.Ω ^ (-8/3:ℝ) * S.Ω ^ (3:ℝ)) * P.G ^ (-2/3:ℝ) * S.Δ⁻¹ / P.U ^ 5) by ring,
          hΩcol]
    rw [hval]
    refine mul_le_mul_of_nonneg_left ?_ hH.le
    have hΩ13 : S.Ω ^ (1/3:ℝ) ≤ P.X ^ (P.u * (1/3)) := omega_le_U_rpow P S (by norm_num) hΩU
    have hG23 : P.G ^ (-2/3:ℝ) = P.X ^ (P.g * (-2/3)) := by
      rw [Globals.G, ← Real.rpow_mul hX0.le]
    rw [hG23, hU5, div_le_iff₀ (by positivity)]
    calc S.Ω ^ (1/3:ℝ) * P.X ^ (P.g * (-2/3)) * S.Δ⁻¹
        ≤ P.X ^ (P.u * (1/3)) * P.X ^ (P.g * (-2/3)) * P.X ^ (-1/100 : ℝ) := by
          apply mul_le_mul _ hdinv hΔinvnn (by positivity)
          exact mul_le_mul_of_nonneg_right hΩ13 (by positivity)
      _ = P.X ^ (P.u * (1/3) + P.g * (-2/3) + (-1/100)) := by
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      _ ≤ P.X ^ (-P.u + P.u * 5) := by
          apply Real.rpow_le_rpow_of_exponent_le hX; nlinarith [hg0, hu]
      _ = P.X ^ (-P.u) * P.X ^ (P.u * 5) := by rw [← Real.rpow_add hX0]
  rw [hRW, hHUeq]
  have hφnn : 0 ≤ fiberφ P S := by
    rw [fiberφ_def]
    have hDA : (0:ℝ) ≤ S.Δ / S.A := by
      have : (0:ℝ) < S.A := by unfold Scale.A; positivity
      positivity
    exact mul_nonneg (Real.rpow_nonneg hDA _) (Real.rpow_nonneg hG.le _)
  calc (1 + fiberφ P S) * (P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5))
      = P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5)
          + fiberφ P S * (P.H * (S.Ω ^ (3:ℝ) * S.Δ⁻¹ / P.U ^ 5)) := by ring
    _ ≤ P.H * P.X ^ (-P.u) + P.H * P.X ^ (-P.u) :=
        add_le_add (mul_le_mul_of_nonneg_left hone hH.le) hφpart
    _ = 2 * (P.H * P.X ^ (-P.u)) := by ring

end Squarefree.StripAux
