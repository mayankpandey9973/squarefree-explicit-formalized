import Squarefree.Params
import Squarefree.Structure.DaSpacing
import Squarefree.Upper.Regime6
import Squarefree.Upper.Regime6Count
import Squarefree.Upper.Regime6LowF
import Squarefree.Upper.Regime6Assembly
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §6 regime upper bound: Prop 6.1 (layer L?)

Proof of Prop 6.1 from `../explicit_writeup.md` (lines 1230–1308).
The `a ↔ r` swap (`prop6_swap`) reduces the `a`-sum to a sum over `r` of per-`r` integer
counts.  A curvature split `F < 1` vs `F ≥ 1` (via `prop6ScaleLo·F`) feeds either the
elementary low-curvature count (`prop6_count_per_r_lowF`) or the Prop 4.3 high-curvature count
(`prop6_count_per_r`); both collapse to the displayed three-term bound.
See `CLAUDE.md` §3/§4.
-/

open Classical Finset
open Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 400000

namespace Prop61

/-! ## Shared scale facts -/

/-- `H ≥ 1` from `g ≤ 1` and `X ≥ 1`. -/
private theorem H_ge_one {P : Globals} (hX : 1 ≤ P.X) (hg1 : P.g ≤ 1) : (1:ℝ) ≤ P.H := by
  rw [Globals.H]; exact Real.one_le_rpow hX (by linarith)

/-- The third RHS term `H^{-1/2}G^{1/2}Ω^{5/2}` is positive. -/
private theorem RHS3_pos {P : Globals} (S : Scale P) :
    0 < P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by
  have := Real.rpow_pos_of_pos P.H_pos (-1/2 : ℝ)
  have := Real.rpow_pos_of_pos P.G_pos (1/2 : ℝ)
  have := Real.rpow_pos_of_pos S.Ω_pos (5/2 : ℝ)
  positivity

private theorem RHS1_nonneg {P : Globals} (S : Scale P) :
    0 ≤ S.x * P.G * S.Ω ^ 2 := by
  have hΔ := S.Δ_pos; have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  unfold Scale.x; positivity

private theorem RHS2_nonneg {P : Globals} (S : Scale P) :
    0 ≤ S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ) := by
  have hx : (0:ℝ) ≤ S.x := by have := S.Δ_pos; have := P.H_pos; unfold Scale.x; positivity
  have := Real.rpow_nonneg hx (2/3 : ℝ)
  have := Real.rpow_nonneg P.G_pos.le (4/3 : ℝ)
  have := Real.rpow_nonneg S.Ω_pos.le (11/3 : ℝ)
  positivity

/-- `H·(H^{-1/2}G^{1/2}Ω^{5/2}) = H^{1/2}G^{1/2}Ω^{5/2} = √(G·H·Ω⁵)`, in convenient form. -/
private theorem H_RHS3_eq {P : Globals} (S : Scale P) :
    P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ))
      = P.H ^ (1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by
  have hH := P.H_pos
  have key : P.H * P.H ^ (-1/2 : ℝ) = P.H ^ (1/2 : ℝ) := by
    rw [show P.H * P.H ^ (-1/2 : ℝ) = P.H ^ (1:ℝ) * P.H ^ (-1/2 : ℝ) from by
      rw [Real.rpow_one], ← Real.rpow_add hH]; norm_num
  calc P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ))
      = (P.H * P.H ^ (-1/2 : ℝ)) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by ring
    _ = P.H ^ (1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by rw [key]

/-- **`Ω ≤ H·RHS₃`** via the floor `GHΩ³ ≥ 16777216` (`√(GHΩ³) ≥ 4096 ≥ 1`). -/
private theorem Omega_le_H_RHS3 {P : Globals} (S : Scale P)
    (hΩfloor : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3) :
    S.Ω ≤ P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  rw [H_RHS3_eq]
  -- H^{1/2}G^{1/2}Ω^{5/2} = √(GHΩ³)·Ω ≥ 4096·Ω ≥ Ω
  have hsqrt : P.H ^ (1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)
      = Real.sqrt (P.G * P.H * S.Ω ^ 3) * S.Ω := by
    rw [Real.sqrt_eq_rpow]
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast S.Ω 3, ← Real.rpow_mul hΩ.le]
    rw [show S.Ω ^ (5/2 : ℝ) = S.Ω ^ ((3:ℝ) * (1/2:ℝ) + 1) from by norm_num,
        Real.rpow_add hΩ, Real.rpow_one]
    push_cast; ring_nf
  rw [hsqrt]
  have h4096 : (4096 : ℝ) ≤ Real.sqrt (P.G * P.H * S.Ω ^ 3) := by
    rw [show (4096:ℝ) = Real.sqrt 16777216 by rw [show (16777216:ℝ) = 4096^2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hΩfloor
  exact le_mul_of_one_le_left hΩ.le (by linarith [h4096])

/-- `R²/(H·RHS₃)² = F/H` (exact scale identity). -/
private theorem R_sq_over {P : Globals} (S : Scale P) :
    S.R ^ 2 = (S.F / P.H) * (P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ))) ^ 2 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  rw [H_RHS3_eq]
  rw [show (P.H ^ (1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) ^ 2
      = (P.H ^ (1/2 : ℝ)) ^ 2 * (P.G ^ (1/2 : ℝ)) ^ 2 * (S.Ω ^ (5/2 : ℝ)) ^ 2 from by ring]
  rw [← Real.rpow_natCast (P.H ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hH.le,
      ← Real.rpow_natCast (P.G ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hG.le,
      ← Real.rpow_natCast (S.Ω ^ (5/2 : ℝ)) 2, ← Real.rpow_mul hΩ.le]
  push_cast
  rw [show (1/2 : ℝ) * 2 = 1 by norm_num, show (5/2 : ℝ) * 2 = (5:ℕ) by norm_num,
      Real.rpow_one, Real.rpow_one, Real.rpow_natCast]
  rw [Scale.R, Scale.F]
  field_simp

/-- **`R ≤ √(F/H)·H·RHS₃`** — an exact form; combined with `F/H ≤ const` (the `¬hF` branch)
gives `R ≤ C·H·RHS₃`. -/
private theorem R_le_sqrt_FH_RHS3 {P : Globals} (S : Scale P) :
    S.R ≤ Real.sqrt (S.F / P.H)
      * (P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ))) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hRHS3 := RHS3_pos S
  set V := P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) with hVdef
  have hVpos : 0 < V := by rw [hVdef]; positivity
  have hkey : S.R ^ 2 = (S.F / P.H) * V ^ 2 := R_sq_over S
  -- R = √(R²) = √(F/H)·V  (both sides nonneg with equal squares)
  have heq : S.R = Real.sqrt (S.F / P.H) * V := by
    have hsqsq : (Real.sqrt (S.F / P.H) * V) ^ 2 = S.R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ S.F / P.H by positivity), hkey]
    have hnn : 0 ≤ Real.sqrt (S.F / P.H) * V := mul_nonneg (Real.sqrt_nonneg _) hVpos.le
    exact ((pow_left_inj₀ hnn hRpos.le (by norm_num)).mp hsqsq).symm
  exact le_of_eq heq

/-- Monotonicity in the budget constant: bumping `C₀ ↦ C` (with `C₀ ≤ C`) only enlarges
`C·H·X^{C·u}·RHS` (since `X ≥ 1`, `u ≥ 0`, `RHS ≥ 0`). -/
private theorem widen_budget {P : Globals} (S : Scale P) (Sr C₀ C : ℝ)
    (hX : 1 ≤ P.X) (hu : 0 ≤ P.u) (hC₀ : 0 < C₀) (hCC : C₀ ≤ C)
    (hrhs : 0 ≤ S.x * P.G * S.Ω ^ 2
          + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
          + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ))
    (h : Sr ≤ C₀ * P.H * P.X ^ (C₀ * P.u) *
        ( S.x * P.G * S.Ω ^ 2
        + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
        + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) )) :
    Sr ≤ C * P.H * P.X ^ (C * P.u) *
        ( S.x * P.G * S.Ω ^ 2
        + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
        + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
  refine le_trans h ?_
  have hH := P.H_pos
  have hxle : P.X ^ (C₀ * P.u) ≤ P.X ^ (C * P.u) :=
    Real.rpow_le_rpow_of_exponent_le hX (mul_le_mul_of_nonneg_right hCC hu)
  have hpos0 : (0:ℝ) ≤ P.X ^ (C₀ * P.u) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hCHle : C₀ * P.H * P.X ^ (C₀ * P.u) ≤ C * P.H * P.X ^ (C * P.u) := by
    have h1 : C₀ * P.H ≤ C * P.H := mul_le_mul_of_nonneg_right hCC hH.le
    calc C₀ * P.H * P.X ^ (C₀ * P.u) ≤ C * P.H * P.X ^ (C₀ * P.u) := by
          exact mul_le_mul_of_nonneg_right h1 hpos0
      _ ≤ C * P.H * P.X ^ (C * P.u) := by
          have : (0:ℝ) ≤ C * P.H := mul_nonneg (by linarith) hH.le
          exact mul_le_mul_of_nonneg_left hxle this
  exact mul_le_mul_of_nonneg_right hCHle hrhs

/-! ## Low-curvature branch (`prop6ScaleLo·F ≤ 1`) -/

/-- `K₀·δ₀ ≤ K₀·F/16777216` via the floor `GHΩ³ ≥ 16777216` (since `A² = H²GΩ³/F`). -/
private theorem K0delta0_le {P : Globals} (S : Scale P)
    (hΩfloor : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3) :
    K0 * delta0 S ≤ K0 * S.F / 16777216 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hK0 := K0_pos
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  -- δ₀ = F/(GHΩ³) ≤ F/16777216  (since GHΩ³ ≥ 16777216)
  have hδ0F : delta0 S = S.F / (P.G * P.H * S.Ω ^ 3) := by
    unfold delta0 Scale.F; field_simp
  rw [hδ0F, show K0 * (S.F / (P.G * P.H * S.Ω ^ 3)) = (K0 * S.F) / (P.G * P.H * S.Ω ^ 3) by ring]
  have hKF : (0:ℝ) ≤ K0 * S.F := by positivity
  rw [div_le_iff₀ (by positivity)]
  rw [show K0 * S.F / 16777216 * (P.G * P.H * S.Ω ^ 3)
      = (K0 * S.F) * ((P.G * P.H * S.Ω ^ 3) / 16777216) by ring]
  exact le_mul_of_one_le_right hKF
    (show (1:ℝ) ≤ (P.G * P.H * S.Ω ^ 3) / 16777216 by rw [le_div_iff₀ (by norm_num)]; linarith)

/-- The §6 low-curvature (elementary-count) branch of Prop 6.1. -/
private theorem prop6_lowF :
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P), 1 ≤ P.X → 0 < P.u → P.g ≤ 1 → 10 * S.A ≤ S.D →
      P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω →
      (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 →
      ¬ (1 < prop6ScaleLo * S.F) →
      ∀ (RaOf : ℤ → Finset ℕ),
      (∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (0 < a) ∧ ∀ r ∈ RaOf a, RaWitness P S a r) →
      (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) ≤
        C * P.H * P.X ^ (C * P.u) *
          ( S.x * P.G * S.Ω ^ 2
          + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
          + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
  have hLo := prop6ScaleLo_pos
  have hCv := Cval6_pos
  have hcd := cderiv6_pos
  have hK0 := K0_pos
  set srt : ℝ := Real.sqrt (1 / prop6ScaleLo) with hsrtdef
  have hsrt0 : 0 ≤ srt := Real.sqrt_nonneg _
  set B₁ : ℝ := 2 * Cval6 / prop6ScaleLo + 2 * K0 / (prop6ScaleLo * 16777216) + 1 with hB1def
  have hB1pos : 0 < B₁ := by rw [hB1def]; positivity
  refine ⟨B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt + 1, by positivity, ?_⟩
  set C : ℝ := B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  intro P S hX hu hg1 hAD hband hΩfloor hF RaOf hwit
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hHge1 := H_ge_one hX hg1
  -- abbreviations
  set δ : ℝ := K0 * delta0 S with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; exact mul_pos hK0 (delta0_pos S)
  -- F ≤ 1/prop6ScaleLo
  have hFle : S.F ≤ 1 / prop6ScaleLo := by
    rw [not_lt] at hF
    rw [le_div_iff₀ hLo]; linarith [hF]
  -- RHS nonneg, RHS3 form
  have hRHS3pos := RHS3_pos S
  have hRHSnn : (0:ℝ) ≤ S.x * P.G * S.Ω ^ 2
      + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
      + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by
    have := RHS1_nonneg S; have := RHS2_nonneg S; linarith [hRHS3pos]
  set V3 : ℝ := P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) with hV3def
  have hV3pos : 0 < V3 := by rw [hV3def]; positivity
  -- the per-r constant bound  B₁ ≥ 2Cv·F + 2δ + 1
  have hVar1 : 2 * Cval6 * S.F + 2 * δ + 1 ≤ B₁ := by
    have hδle : δ ≤ K0 * S.F / 16777216 := by rw [hδdef]; exact K0delta0_le S hΩfloor
    have hCvF : 2 * Cval6 * S.F ≤ 2 * Cval6 / prop6ScaleLo := by
      rw [show 2 * Cval6 / prop6ScaleLo = 2 * Cval6 * (1 / prop6ScaleLo) by ring]
      exact mul_le_mul_of_nonneg_left hFle (by positivity)
    have hδF : 2 * δ ≤ 2 * K0 / (prop6ScaleLo * 16777216) := by
      have : 2 * δ ≤ 2 * (K0 * S.F / 16777216) := by linarith [hδle]
      refine le_trans this ?_
      rw [show 2 * (K0 * S.F / 16777216) = (2 * K0 / 16777216) * S.F by ring,
          show 2 * K0 / (prop6ScaleLo * 16777216) = (2 * K0 / 16777216) * (1 / prop6ScaleLo) by ring]
      exact mul_le_mul_of_nonneg_left hFle (by positivity)
    rw [hB1def]; linarith [hCvF, hδF]
  -- the leading factor: 2δ/(cderiv6·F/A) = (2K0/cderiv6)·(δ₀A/F), and δ₀A/F = Ω/R
  have hδ0AF : delta0 S * S.A / S.F = S.Ω / S.R := by
    have hkey : S.R * delta0 S * S.A / S.F = S.Ω := R_delta0_A_div_F S
    field_simp at hkey ⊢
    linear_combination hkey
  have hlead : 2 * δ / (cderiv6 * S.F / S.A) = (2 * K0 / cderiv6) * (S.Ω / S.R) := by
    rw [hδdef, ← hδ0AF]
    field_simp
  -- per-r bound: filter card ≤ B₁·((2K0/cderiv6)(Ω/R) + 1)
  have hperr : ∀ r : ℕ, r ∈ Finset.Icc ⌈(1/72) * S.R⌉₊ ⌊16 * S.R⌋₊ →
      (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
          (fun (n : ℤ) => distInt (ftil P.X (r : ℝ) (n : ℝ)) ≤ K0 * delta0 S)).card : ℝ)
        ≤ B₁ * ((2 * K0 / cderiv6) * (S.Ω / S.R) + 1) := by
    intro r hr
    obtain ⟨hrl, hrr⟩ := Finset.mem_Icc.mp hr
    have hr0 : (0:ℝ) < (r:ℝ) := by
      have hcpos : 0 < ⌈(1/72) * S.R⌉₊ := Nat.ceil_pos.mpr (by positivity)
      have : 1 ≤ r := le_trans hcpos hrl
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hrlo : (1/72) * S.R ≤ (r:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hrl)
    have hrhi : (r:ℝ) ≤ 16 * S.R := le_trans (by exact_mod_cast hrr) (Nat.floor_le (by positivity))
    have hcount := prop6_count_per_r_lowF (P := P) (S := S) (r := (r:ℝ)) (δ := K0 * delta0 S)
      hAD hr0 hrlo hrhi (mul_pos hK0 (delta0_pos S))
    refine le_trans hcount ?_
    rw [← hδdef] at hcount ⊢
    rw [hlead]
    exact mul_le_mul hVar1 (le_refl _) (by positivity) hB1pos.le
  -- swap + sum bound
  have hswap := prop6_swap (P := P) (S := S) hAD (by linarith [hΩfloor] : (500:ℝ) ≤ P.G * P.H * S.Ω ^ 3)
    RaOf hwit
  refine le_trans hswap ?_
  set Ua : Finset ℕ := Finset.Icc ⌈(1/72) * S.R⌉₊ ⌊16 * S.R⌋₊ with hUadef
  -- ∑_r ≤ card·perB
  have hsum : (∑ r ∈ Ua,
      (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
          (fun (n : ℤ) => distInt (ftil P.X (r : ℝ) (n : ℝ)) ≤ K0 * delta0 S)).card : ℝ))
      ≤ (Ua.card : ℝ) * (B₁ * ((2 * K0 / cderiv6) * (S.Ω / S.R) + 1)) := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul Ua _ _ hperr
  refine le_trans hsum ?_
  -- collapse: card·perB ≤ C·H·RHS₃ ≤ C·H·X^{Cu}·(RHS)
  rcases Finset.eq_empty_or_nonempty Ua with hempty | hne
  · rw [hempty, Finset.card_empty]; push_cast
    have : (0:ℝ) ≤ C * P.H * P.X ^ (C * P.u) *
        ( S.x * P.G * S.Ω ^ 2
        + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
        + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
      have : (0:ℝ) ≤ C * P.H * P.X ^ (C * P.u) := by positivity
      exact mul_nonneg this hRHSnn
    simpa using this
  · -- non-empty ⟹ R ≥ 1/16
    obtain ⟨r0, hr0mem⟩ := hne
    have hRge : (1/16 : ℝ) ≤ S.R := by
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hr0mem
      have h1 : 1 ≤ ⌊16 * S.R⌋₊ := by
        have : 1 ≤ ⌈(1/72) * S.R⌉₊ := Nat.ceil_pos.mpr (by positivity)
        omega
      have : (1:ℝ) ≤ 16 * S.R := le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
      linarith
    -- card ≤ 16R + 1
    have hcardle : (Ua.card : ℝ) ≤ 16 * S.R + 1 := by
      rw [hUadef, Nat.card_Icc]
      have hnat : (⌊16 * S.R⌋₊ + 1 - ⌈(1/72) * S.R⌉₊ : ℕ) ≤ ⌊16 * S.R⌋₊ + 1 := by omega
      have hcast : ((⌊16 * S.R⌋₊ + 1 - ⌈(1/72) * S.R⌉₊ : ℕ) : ℝ) ≤ ((⌊16 * S.R⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      refine le_trans hcast ?_
      have hfl : (⌊16 * S.R⌋₊ : ℝ) ≤ 16 * S.R := Nat.floor_le (by positivity)
      push_cast; linarith
    -- Ω/R ≤ 16Ω,  1 ≤ 16R
    have hΩR : S.Ω / S.R ≤ 16 * S.Ω := by
      rw [div_le_iff₀ hRpos]
      linarith [mul_le_mul_of_nonneg_left hRge (by positivity : (0:ℝ) ≤ 16 * S.Ω)]
    -- collapse to (64K0/cderiv6)Ω + 32R, times B₁
    set q : ℝ := S.Ω / S.R with hqdef
    have hqR : q * S.R = S.Ω := by rw [hqdef]; field_simp
    have hqnn : 0 ≤ q := by rw [hqdef]; positivity
    set k : ℝ := 2 * K0 / cderiv6 with hkdef
    have hk : (0:ℝ) ≤ k := by rw [hkdef]; positivity
    have hcollapse : (Ua.card : ℝ) * (B₁ * (k * q + 1))
        ≤ B₁ * ((64 * K0 / cderiv6) * S.Ω + 32 * S.R) := by
      have hpf : (0:ℝ) ≤ B₁ * (k * q + 1) := by
        have hkq : (0:ℝ) ≤ k * q := mul_nonneg hk hqnn
        exact mul_nonneg hB1pos.le (by linarith)
      have h16R : (1:ℝ) ≤ 16 * S.R := by linarith [hRge]
      -- (16R+1)·(kq+1) = 16R·kq + kq + 16R + 1 ≤ 16kΩ + 16kΩ + 16R + 16R
      have hstepc : (16 * S.R + 1) * (k * q + 1)
          ≤ (64 * K0 / cderiv6) * S.Ω + 32 * S.R := by
        have e1 : (16 * S.R) * (k * q) = 16 * k * S.Ω := by rw [← hqR]; ring
        have e2 : k * q ≤ 16 * k * S.Ω := by
          linarith [mul_le_mul_of_nonneg_left hΩR hk]
        have hkΩ : (64 * K0 / cderiv6) * S.Ω = 16 * k * S.Ω + 16 * k * S.Ω := by
          rw [hkdef]; ring
        have hexp : (16 * S.R + 1) * (k * q + 1)
            = 16 * S.R * (k * q) + 16 * S.R + k * q + 1 := by ring
        linarith [e1, e2, h16R, hkΩ, hexp]
      calc (Ua.card : ℝ) * (B₁ * (k * q + 1))
          ≤ (16 * S.R + 1) * (B₁ * (k * q + 1)) :=
            mul_le_mul_of_nonneg_right hcardle hpf
        _ = B₁ * ((16 * S.R + 1) * (k * q + 1)) := by ring
        _ ≤ B₁ * ((64 * K0 / cderiv6) * S.Ω + 32 * S.R) :=
            mul_le_mul_of_nonneg_left hstepc hB1pos.le
    refine le_trans hcollapse ?_
    -- Ω ≤ V3 = H·RHS3 ;  R ≤ srt·V3
    have hΩV3 : S.Ω ≤ V3 := by rw [hV3def]; exact Omega_le_H_RHS3 S hΩfloor
    have hRV3 : S.R ≤ srt * V3 := by
      have hRle := R_le_sqrt_FH_RHS3 S
      rw [← hV3def] at hRle
      refine le_trans hRle ?_
      have hsqle : Real.sqrt (S.F / P.H) ≤ srt := by
        rw [hsrtdef]
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hH, one_div, inv_mul_eq_div, le_div_iff₀ hLo]
        have h1 := mul_le_mul_of_nonneg_right hFle hLo.le
        have h2 : (1 / prop6ScaleLo) * prop6ScaleLo = 1 := by field_simp
        linarith [h1, h2, hHge1]
      exact mul_le_mul_of_nonneg_right hsqle hV3pos.le
    -- B₁·((64K0/cderiv6)Ω + 32R) ≤ C·V3 ≤ C·H·X^{Cu}·RHS
    have hstep : B₁ * ((64 * K0 / cderiv6) * S.Ω + 32 * S.R) ≤ C * V3 := by
      have hb : (0:ℝ) ≤ 64 * K0 / cderiv6 := by positivity
      have e1 : (64 * K0 / cderiv6) * S.Ω ≤ (64 * K0 / cderiv6) * V3 :=
        mul_le_mul_of_nonneg_left hΩV3 hb
      have e2 : 32 * S.R ≤ 32 * (srt * V3) := by linarith [hRV3]
      have : B₁ * ((64 * K0 / cderiv6) * S.Ω + 32 * S.R)
          ≤ B₁ * ((64 * K0 / cderiv6) * V3 + 32 * (srt * V3)) :=
        mul_le_mul_of_nonneg_left (by linarith [e1, e2]) hB1pos.le
      refine le_trans this ?_
      rw [hCdef]
      have : B₁ * ((64 * K0 / cderiv6) * V3 + 32 * (srt * V3))
          = (B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt) * V3 := by ring
      rw [this]
      have hVle : (B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt) * V3
          ≤ (B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt + 1) * V3 := by
        have hd : (B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt + 1) * V3
            = (B₁ * (64 * K0 / cderiv6) + 32 * B₁ * srt) * V3 + V3 := by ring
        linarith [hV3pos, hd]
      exact hVle
    refine le_trans hstep ?_
    -- C·V3 = C·H·RHS3 ≤ C·H·RHS3·X^{Cu} ≤ C·H·X^{Cu}·(RHS)
    have hXpow : (1:ℝ) ≤ P.X ^ (C * P.u) := Real.one_le_rpow hX (by positivity)
    have hCV3 : C * V3 = C * P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) := by
      rw [hV3def]; ring
    rw [hCV3]
    calc C * P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ))
        ≤ C * P.H * P.X ^ (C * P.u) * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) := by
          have hCHnn : (0:ℝ) ≤ C * P.H := by positivity
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCHnn hXpow) hRHS3pos.le
      _ ≤ C * P.H * P.X ^ (C * P.u) *
          ( S.x * P.G * S.Ω ^ 2
          + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
          + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
          have hCHX : (0:ℝ) ≤ C * P.H * P.X ^ (C * P.u) := by positivity
          have hr1 := RHS1_nonneg S; have hr2 := RHS2_nonneg S
          exact mul_le_mul_of_nonneg_left (by linarith) hCHX

/-! ## High-curvature branch (`1 < prop6ScaleLo·F`) -/

/-- **(b)** exact identity `R·A·δ₀ = Ω·F = H·RHS₁`. -/
private theorem highF_idb {P : Globals} (S : Scale P) :
    S.R * S.A * delta0 S = P.H * (S.x * P.G * S.Ω ^ 2) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.R Scale.A Scale.x delta0
  field_simp

/-- **(a₃)** the cube identity `(R·(A·F)^{1/3})³ = (H·RHS₂)³`, hence (both nonneg) the
exact identity `R·(A·F)^{1/3} = H·RHS₂`. -/
private theorem highF_ida {P : Globals} (S : Scale P) :
    S.R * (S.A * S.F) ^ (1/3 : ℝ)
      = P.H * (S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hApos : 0 < S.A := by rw [Scale.A]; positivity
  have hFpos : 0 < S.F := by rw [Scale.F]; positivity
  have hxpos : 0 < S.x := by rw [Scale.x]; positivity
  set L := S.R * (S.A * S.F) ^ (1/3 : ℝ) with hLdef
  set Rt := P.H * (S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)) with hRtdef
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  have hRtnn : 0 ≤ Rt := by rw [hRtdef]; positivity
  -- ((A·F)^{1/3})³ = A·F  and  (x^{2/3})³ = x²,  (G^{4/3})³ = G⁴,  (Ω^{11/3})³ = Ω¹¹
  have hcr : ((S.A * S.F) ^ (1/3 : ℝ)) ^ 3 = S.A * S.F := by
    rw [← Real.rpow_natCast ((S.A * S.F) ^ (1/3 : ℝ)) 3, ← Real.rpow_mul (by positivity)]
    norm_num
  have hx3 : (S.x ^ (2/3 : ℝ)) ^ 3 = S.x ^ 2 := by
    rw [← Real.rpow_natCast (S.x ^ (2/3 : ℝ)) 3, ← Real.rpow_mul hxpos.le]
    norm_num
  have hg3 : (P.G ^ (4/3 : ℝ)) ^ 3 = P.G ^ 4 := by
    rw [← Real.rpow_natCast (P.G ^ (4/3 : ℝ)) 3, ← Real.rpow_mul hG.le]
    norm_num
  have hΩ3 : (S.Ω ^ (11/3 : ℝ)) ^ 3 = S.Ω ^ 11 := by
    rw [← Real.rpow_natCast (S.Ω ^ (11/3 : ℝ)) 3, ← Real.rpow_mul hΩ.le]
    norm_num
  have hcube : L ^ 3 = Rt ^ 3 := by
    rw [hLdef, hRtdef]
    simp only [mul_pow]
    rw [hcr, hx3, hg3, hΩ3]
    rw [Scale.R, Scale.A, Scale.F, Scale.x]
    field_simp
  exact (pow_left_inj₀ hLnn hRtnn (by norm_num)).mp hcube

/-- **(c₂)** the square identity `(R·A·√(δ₀/F))² = (H·RHS₃)²`, hence (both nonneg)
the exact identity `R·A·√(δ₀/F) = H·RHS₃`. -/
private theorem highF_idc {P : Globals} (S : Scale P) :
    S.R * S.A * Real.sqrt (delta0 S / S.F)
      = P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hApos : 0 < S.A := by rw [Scale.A]; positivity
  have hFpos : 0 < S.F := by rw [Scale.F]; positivity
  have hd0pos := delta0_pos S
  set L := S.R * S.A * Real.sqrt (delta0 S / S.F) with hLdef
  set Rt := P.H * (P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ)) with hRtdef
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  have hRtnn : 0 ≤ Rt := by rw [hRtdef]; positivity
  have hh2 : (P.H ^ (-1/2 : ℝ)) ^ 2 = P.H⁻¹ := by
    rw [← Real.rpow_natCast (P.H ^ (-1/2 : ℝ)) 2, ← Real.rpow_mul hH.le]
    rw [show (-1/2 : ℝ) * (2:ℕ) = (-1 : ℝ) by push_cast; ring, Real.rpow_neg_one]
  have hg2 : (P.G ^ (1/2 : ℝ)) ^ 2 = P.G := by
    rw [← Real.rpow_natCast (P.G ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hG.le]
    norm_num
  have hΩ2 : (S.Ω ^ (5/2 : ℝ)) ^ 2 = S.Ω ^ 5 := by
    rw [← Real.rpow_natCast (S.Ω ^ (5/2 : ℝ)) 2, ← Real.rpow_mul hΩ.le]
    norm_num
  have hsq : L ^ 2 = Rt ^ 2 := by
    rw [hLdef, hRtdef]
    simp only [mul_pow]
    rw [Real.sq_sqrt (by positivity), hh2, hg2, hΩ2]
    rw [Scale.R, Scale.A, Scale.F, delta0]
    field_simp
  exact (pow_left_inj₀ hLnn hRtnn (by norm_num)).mp hsq

/-- `A²·δ₀ = H` (exact scale identity). -/
private theorem highF_A2delta0 {P : Globals} (S : Scale P) :
    S.A ^ 2 * delta0 S = P.H := by
  have hH := P.H_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A delta0
  field_simp

/-- **`R = A·RHS₁`** (exact scale identity).  When `A ≤ 1 ≤ H`, this yields `R ≤ H·RHS₁`. -/
private theorem highF_R_eq_A_RHS1 {P : Globals} (S : Scale P) :
    S.R = S.A * (S.x * P.G * S.Ω ^ 2) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.R Scale.A Scale.x
  field_simp

/-- **`H ≤ X`** in the §6 high-curvature regime.  From `10A ≤ D` (i.e. `Ω ≤ H/10`) and the floor
`16777216 ≤ GHΩ³` together with `X = G·H⁵`: `16777216 ≤ GH(H/10)³ = X/(1000·H)`, so `H ≤ X`.
This replaces the `g ≥ 0` route (the §6 floor + spacing already force `g > -4`). -/
private theorem highF_H_le {P : Globals} (S : Scale P)
    (hAD : 10 * S.A ≤ S.D) (hΩfloor : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3) :
    P.H ≤ P.X := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  -- Ω ≤ H/10
  have hΩle : S.Ω ≤ P.H / 10 := by
    have hAD' : 10 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by rw [Scale.A, Scale.D] at hAD; exact hAD
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hAD', hΔ]
  -- G H Ω³ ≤ G H⁴/1000 = X/(1000 H)
  have hXid : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
  have hΩ3 : S.Ω ^ 3 ≤ (P.H / 10) ^ 3 := by
    apply pow_le_pow_left₀ hΩ.le hΩle
  have hchain : (16777216 : ℝ) ≤ P.G * P.H * (P.H / 10) ^ 3 := by
    refine le_trans hΩfloor ?_
    apply mul_le_mul_of_nonneg_left hΩ3 (by positivity)
  -- G H (H/10)³ = G H⁴/1000 = X/(1000 H)
  have heq : P.G * P.H * (P.H / 10) ^ 3 = P.X / (1000 * P.H) := by
    rw [hXid]; field_simp; ring
  rw [heq] at hchain
  rw [le_div_iff₀ (by positivity)] at hchain
  linarith [hchain, hH]

/-- **Index bridge**: the count over the integer window `[⌈A⌉, ⌊2A⌋]` is at most the count over
the real image of the half-open window `(⌊A⌋, ⌊2A⌋]` plus one (the possibly-omitted endpoint
`⌊A⌋`).  `Int.cast` injectivity turns the `ℝ`-image filter into the `ℤ`-`Ioc` filter. -/
private theorem highF_index_bridge {X r δ A : ℝ} :
    (((Finset.Icc ⌈A⌉ ⌊2 * A⌋).filter
        (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ ((((Finset.Ioc ⌊A⌋ ⌊2 * A⌋).image (Int.cast : ℤ → ℝ)).filter
          (fun n => distInt (ftil X r n) ≤ δ)).card : ℝ) + 1 := by
  classical
  -- the ℝ-image filter equals (as cardinality) the ℤ-Ioc filter
  have himg : (((Finset.Ioc ⌊A⌋ ⌊2 * A⌋).image (Int.cast : ℤ → ℝ)).filter
        (fun n => distInt (ftil X r n) ≤ δ)).card
      = ((Finset.Ioc ⌊A⌋ ⌊2 * A⌋).filter
          (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ)).card := by
    rw [Finset.filter_image,
        Finset.card_image_of_injective _ (Int.cast_injective)]
  rw [himg]
  -- Icc ⌈A⌉ ⌊2A⌋ ⊆ insert ⌊A⌋ (Ioc ⌊A⌋ ⌊2A⌋)
  have hsub : (Finset.Icc ⌈A⌉ ⌊2 * A⌋).filter (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ)
      ⊆ insert ⌊A⌋ ((Finset.Ioc ⌊A⌋ ⌊2 * A⌋).filter
          (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hmem, hp⟩ := hn
    rw [Finset.mem_Icc] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [Finset.mem_insert]
    rcases eq_or_lt_of_le (Int.floor_le_ceil A) with hfc | hfc
    · -- ⌊A⌋ = ⌈A⌉ : n could be ⌊A⌋ or > ⌊A⌋
      rcases le_or_gt n ⌊A⌋ with hle | hlt
      · left; omega
      · right; rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hlt, h2⟩, hp⟩
    · -- ⌊A⌋ < ⌈A⌉ ≤ n
      rcases le_or_gt n ⌊A⌋ with hle | hlt
      · omega
      · right; rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hlt, h2⟩, hp⟩
  have hcard := Finset.card_le_card hsub
  have hins := Finset.card_insert_le ⌊A⌋ ((Finset.Ioc ⌊A⌋ ⌊2 * A⌋).filter
      (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ))
  have : ((Finset.Icc ⌈A⌉ ⌊2 * A⌋).filter
      (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ)).card
      ≤ ((Finset.Ioc ⌊A⌋ ⌊2 * A⌋).filter
          (fun (n : ℤ) => distInt (ftil X r (n : ℝ)) ≤ δ)).card + 1 :=
    le_trans hcard hins
  exact_mod_cast this

/-- **Per-`r` count** for the §6 high-curvature branch (`A > 1`): the integer count over
`[⌈A⌉,⌊2A⌋]` is at most an `r`-uniform multiple of the three scale terms, with the log factor
carrying a single `X^u`.  Extracted as a standalone lemma to keep elaboration cheap. -/
private theorem highF_perr_count {P : Globals} (S : Scale P) {r : ℝ}
    (hX : 1 ≤ P.X) (hu : 0 < P.u) (hg1 : P.g ≤ 1)
    (hAD : 10 * S.A ≤ S.D) (hΩfloor : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3)
    (hlog : Real.log P.X ≤ P.X ^ P.u) (hF : 1 < prop6ScaleLo * S.F)
    (hr0 : 0 < r) (hrlo : (1/72) * S.R ≤ r) (hrhi : r ≤ 16 * S.R) (hA1 : 1 < S.A) :
    (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
        (fun (n : ℤ) => distInt (ftil P.X r (n:ℝ)) ≤ K0 * delta0 S)).card : ℝ)
      ≤ prop6CountConst * (3 * (prop6ScaleHi ^ (1/3 : ℝ) * (S.A * S.F) ^ (1/3 : ℝ))
          + K0 * (S.A * delta0 S)
          + Real.sqrt (K0 / prop6ScaleLo) * (S.A * Real.sqrt (delta0 S / S.F))
            * ((Real.log (2 + Real.sqrt K0) + 1/2) * P.X ^ P.u)) := by
  have hLo := prop6ScaleLo_pos
  have hHi := prop6ScaleHi_pos
  have hK0 := K0_pos
  have hcc := prop6CountConst_pos
  have hkk2 : (2:ℝ) ≤ prop6CountConst := by rw [prop6CountConst]; exact le_max_right _ _
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hApos : 0 < S.A := lt_trans one_pos hA1
  have hHge1 := H_ge_one hX hg1
  have hHleX := highF_H_le S hAD hΩfloor
  have hd0pos := delta0_pos S
  set kk : ℝ := prop6CountConst with hkkdef
  set logc : ℝ := Real.log (2 + Real.sqrt K0) + 1/2 with hlogcdef
  have hlogc0 : 0 ≤ logc := by
    rw [hlogcdef]
    have : (0:ℝ) ≤ Real.log (2 + Real.sqrt K0) :=
      Real.log_nonneg (by have := Real.sqrt_nonneg K0; linarith)
    linarith
  set AF13 : ℝ := (S.A * S.F) ^ (1/3 : ℝ) with hAF13def
  have hAF13nn : 0 ≤ AF13 := by rw [hAF13def]; exact Real.rpow_nonneg (by positivity) _
  set sd0F : ℝ := S.A * Real.sqrt (delta0 S / S.F) with hsd0Fdef
  have hsd0Fnn : 0 ≤ sd0F := by rw [hsd0Fdef]; positivity
  -- apply the (uniform-constant) Prop 4.3 count
  obtain ⟨T, hT1, hTlo, hThi, hcnt⟩ :=
    prop6_count_per_r (P := P) (S := S) (r := r) (δ := K0 * delta0 S)
      hAD hr0 hrlo hrhi hA1 (mul_pos hK0 (delta0_pos S)) hF
  have hTpos : 0 < T := lt_trans one_pos hT1
  have hbridge := highF_index_bridge (X := P.X) (r := r) (δ := K0 * delta0 S) (A := S.A)
  have hcnt' : ((((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ)).filter
      (fun n => distInt (ftil P.X r n) ≤ K0 * delta0 S)).card : ℝ)
      ≤ kk * ((S.A * T) ^ (1/3 : ℝ) + S.A * (K0 * delta0 S)
          + S.A * Real.sqrt ((K0 * delta0 S) / T)
            * Real.log (2 + S.A * Real.sqrt ((K0 * delta0 S) / T)) + 1) := by
    rw [← hkkdef] at hcnt; exact hcnt
  have hcomb : (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
        (fun (n : ℤ) => distInt (ftil P.X r (n:ℝ)) ≤ K0 * delta0 S)).card : ℝ)
      ≤ kk * ((S.A * T) ^ (1/3 : ℝ) + S.A * (K0 * delta0 S)
          + S.A * Real.sqrt ((K0 * delta0 S) / T)
            * Real.log (2 + S.A * Real.sqrt ((K0 * delta0 S) / T)) + 1) + 1 :=
    le_trans hbridge (by linarith [hcnt'])
  refine le_trans hcomb ?_
  set Tt1 : ℝ := (S.A * T) ^ (1/3 : ℝ) with hTt1def
  set Tt3arg : ℝ := S.A * Real.sqrt ((K0 * delta0 S) / T) with hTt3argdef
  have hTt1pos : 0 < Tt1 := by rw [hTt1def]; exact Real.rpow_pos_of_pos (by positivity) _
  have hTt1ge1 : (1:ℝ) ≤ Tt1 := by
    rw [hTt1def]; apply Real.one_le_rpow _ (by norm_num)
    calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ S.A * T := mul_le_mul hA1.le hT1.le zero_le_one (by linarith [hA1])
  have hTt3argnn : 0 ≤ Tt3arg := by rw [hTt3argdef]; positivity
  have hkk0 : 0 ≤ kk := hcc.le
  -- (1) (A·T)^{1/3} ≤ prop6ScaleHi^{1/3}·AF13
  have hb1 : Tt1 ≤ prop6ScaleHi ^ (1/3 : ℝ) * AF13 := by
    rw [hTt1def, hAF13def]
    rw [show prop6ScaleHi ^ (1/3 : ℝ) * (S.A * S.F) ^ (1/3 : ℝ)
          = (prop6ScaleHi * (S.A * S.F)) ^ (1/3 : ℝ) from
      (Real.mul_rpow hHi.le (by positivity)).symm]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [show prop6ScaleHi * (S.A * S.F) = S.A * (prop6ScaleHi * S.F) by ring]
    exact mul_le_mul_of_nonneg_left hThi hApos.le
  have hb2 : S.A * (K0 * delta0 S) = K0 * (S.A * delta0 S) := by ring
  -- (3) magnitude: A√(δ/T) ≤ √(K0/SLo)·sd0F
  have hb3 : Tt3arg ≤ Real.sqrt (K0 / prop6ScaleLo) * sd0F := by
    rw [hTt3argdef, hsd0Fdef]
    have hinner : K0 * delta0 S / T ≤ (K0 / prop6ScaleLo) * (delta0 S / S.F) := by
      rw [show (K0 / prop6ScaleLo) * (delta0 S / S.F) = K0 * delta0 S / (prop6ScaleLo * S.F) by
        field_simp]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hTlo
    have hsqrtle : Real.sqrt (K0 * delta0 S / T)
        ≤ Real.sqrt (K0 / prop6ScaleLo) * Real.sqrt (delta0 S / S.F) := by
      rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hinner
    calc S.A * Real.sqrt (K0 * delta0 S / T)
        ≤ S.A * (Real.sqrt (K0 / prop6ScaleLo) * Real.sqrt (delta0 S / S.F)) :=
          mul_le_mul_of_nonneg_left hsqrtle hApos.le
      _ = Real.sqrt (K0 / prop6ScaleLo) * (S.A * Real.sqrt (delta0 S / S.F)) := by ring
  -- (4) log argument: A√(δ/T) ≤ √(K0·H)
  have hb4arg : Tt3arg ≤ Real.sqrt (K0 * P.H) := by
    rw [hTt3argdef]
    rw [show S.A * Real.sqrt (K0 * delta0 S / T) = Real.sqrt (S.A ^ 2 * (K0 * delta0 S / T)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hApos.le]]
    apply Real.sqrt_le_sqrt
    rw [show S.A ^ 2 * (K0 * delta0 S / T) = K0 * (S.A ^ 2 * delta0 S) / T by ring,
        highF_A2delta0 S]
    rw [div_le_iff₀ hTpos]
    exact le_mul_of_one_le_right (mul_pos hK0 hH).le hT1.le
  -- log bound: log(2+Tt3arg) ≤ logc·X^u
  have hlogbound : Real.log (2 + Tt3arg) ≤ logc * P.X ^ P.u := by
    have hmono : Real.log (2 + Tt3arg) ≤ Real.log (2 + Real.sqrt (K0 * P.H)) :=
      Real.log_le_log (by linarith [hTt3argnn]) (by linarith [hb4arg])
    refine le_trans hmono ?_
    have hsqrtH1 : (1:ℝ) ≤ Real.sqrt P.H := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hHge1
    have hsplit : Real.sqrt (K0 * P.H) = Real.sqrt K0 * Real.sqrt P.H := Real.sqrt_mul hK0.le P.H
    have hub : (2:ℝ) + Real.sqrt (K0 * P.H) ≤ (2 + Real.sqrt K0) * Real.sqrt P.H := by
      rw [hsplit]
      have hd : (2 + Real.sqrt K0) * Real.sqrt P.H
          = 2 * Real.sqrt P.H + Real.sqrt K0 * Real.sqrt P.H := by ring
      linarith [hd, hsqrtH1]
    have hlogle : Real.log (2 + Real.sqrt (K0 * P.H))
        ≤ Real.log (2 + Real.sqrt K0) + Real.log (Real.sqrt P.H) := by
      refine le_trans (Real.log_le_log (by positivity) hub) ?_
      rw [Real.log_mul (by positivity) (by positivity)]
    refine le_trans hlogle ?_
    have hlogsqrtH : Real.log (Real.sqrt P.H) ≤ (1/2) * P.X ^ P.u := by
      rw [Real.log_sqrt hH.le]
      have hlH : Real.log P.H ≤ Real.log P.X := Real.log_le_log hH hHleX
      linarith [hlH, hlog]
    have hXupow : (1:ℝ) ≤ P.X ^ P.u := Real.one_le_rpow hX hu.le
    have hl2K0 : (0:ℝ) ≤ Real.log (2 + Real.sqrt K0) :=
      Real.log_nonneg (by have := Real.sqrt_nonneg K0; linarith)
    rw [hlogcdef]
    have hself : Real.log (2 + Real.sqrt K0) ≤ Real.log (2 + Real.sqrt K0) * P.X ^ P.u :=
      le_mul_of_one_le_right hl2K0 hXupow
    rw [show (Real.log (2 + Real.sqrt K0) + 1/2) * P.X ^ P.u
          = Real.log (2 + Real.sqrt K0) * P.X ^ P.u + (1/2) * P.X ^ P.u from by ring]
    linarith [hself, hlogsqrtH]
  -- log-term product bound
  have hlogval : (0:ℝ) ≤ Real.log (2 + Tt3arg) := Real.log_nonneg (by linarith [hTt3argnn])
  have hb3logterm : Tt3arg * Real.log (2 + Tt3arg)
      ≤ Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u) := by
    have hstep := mul_le_mul hb3 hlogbound hlogval (by positivity)
    calc Tt3arg * Real.log (2 + Tt3arg)
        ≤ (Real.sqrt (K0 / prop6ScaleLo) * sd0F) * (logc * P.X ^ P.u) := hstep
      _ = Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u) := by ring
  -- final per-r algebra (explicit)
  rw [hb2]
  set SAF : ℝ := prop6ScaleHi ^ (1/3 : ℝ) * AF13 with hSAFdef
  have hSAFnn : 0 ≤ SAF := by rw [hSAFdef]; positivity
  have hSAF1 : (1:ℝ) ≤ SAF := le_trans hTt1ge1 hb1
  have q1 : kk * Tt1 ≤ kk * SAF := mul_le_mul_of_nonneg_left hb1 hkk0
  have q3 : kk * (Tt3arg * Real.log (2 + Tt3arg))
      ≤ kk * (Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u)) :=
    mul_le_mul_of_nonneg_left hb3logterm hkk0
  have q4 : kk * 1 + 1 ≤ 2 * (kk * SAF) := by
    have hmul : kk ≤ kk * SAF := le_mul_of_one_le_right hcc.le hSAF1
    linarith [hmul, hkk2]
  rw [show kk * (Tt1 + K0 * (S.A * delta0 S) + Tt3arg * Real.log (2 + Tt3arg) + 1) + 1
        = kk * Tt1 + kk * (K0 * (S.A * delta0 S))
          + kk * (Tt3arg * Real.log (2 + Tt3arg)) + (kk * 1 + 1) from by ring]
  rw [show kk * (3 * SAF + K0 * (S.A * delta0 S)
        + Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u))
      = (kk * SAF + 2 * (kk * SAF)) + kk * (K0 * (S.A * delta0 S))
        + kk * (Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u)) from by ring]
  linarith [q1, q3, q4]

/-- The §6 high-curvature (Prop 4.3 sharp-count) branch of Prop 6.1. -/
private theorem prop6_highF :
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P), 1 ≤ P.X → 0 < P.u → P.g ≤ 1 → 10 * S.A ≤ S.D →
      P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω →
      (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 →
      Real.log P.X ≤ P.X ^ P.u →
      (1 < prop6ScaleLo * S.F) →
      ∀ (RaOf : ℤ → Finset ℕ),
      (∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (0 < a) ∧ ∀ r ∈ RaOf a, RaWitness P S a r) →
      (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) ≤
        C * P.H * P.X ^ (C * P.u) *
          ( S.x * P.G * S.Ω ^ 2
          + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
          + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
  have hLo := prop6ScaleLo_pos
  have hHi := prop6ScaleHi_pos
  have hK0 := K0_pos
  have hcc := prop6CountConst_pos
  set kk : ℝ := prop6CountConst with hkkdef
  have hkk2 : (2:ℝ) ≤ kk := by rw [hkkdef, prop6CountConst]; exact le_max_right _ _
  set srt : ℝ := Real.sqrt (1 / prop6ScaleLo) with hsrtdef
  have hsrt0 : 0 ≤ srt := Real.sqrt_nonneg _
  set logc : ℝ := Real.log (2 + Real.sqrt K0) + 1/2 with hlogcdef
  have hlogc0 : 0 ≤ logc := by
    rw [hlogcdef]
    have : (0:ℝ) ≤ Real.log (2 + Real.sqrt K0) :=
      Real.log_nonneg (by have := Real.sqrt_nonneg K0; linarith)
    linarith
  -- the huge absolute constant
  set Ccoef : ℝ := prop6ScaleHi ^ (1/3 : ℝ) + K0
      + Real.sqrt (K0 / prop6ScaleLo) * logc + srt + 1 with hCcoefdef
  have hCcoef0 : 0 < Ccoef := by
    rw [hCcoefdef]
    have h1 : (0:ℝ) ≤ prop6ScaleHi ^ (1/3 : ℝ) := Real.rpow_nonneg hHi.le _
    have h2 : (0:ℝ) ≤ Real.sqrt (K0 / prop6ScaleLo) * logc :=
      mul_nonneg (Real.sqrt_nonneg _) hlogc0
    positivity
  refine ⟨96 * kk * Ccoef + 1, by positivity, ?_⟩
  set C : ℝ := 96 * kk * Ccoef + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC1 : (1:ℝ) ≤ C := by
    rw [hCdef]; linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 96) hcc.le) hCcoef0.le]
  intro P S hX hu hg1 hAD hband hΩfloor hlog hF RaOf hwit
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hHge1 := H_ge_one hX hg1
  have hHleX := highF_H_le S hAD hΩfloor
  have hd0pos := delta0_pos S
  set δ : ℝ := K0 * delta0 S with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; exact mul_pos hK0 (delta0_pos S)
  -- RHS pieces
  have hRHS3pos := RHS3_pos S
  have hRHS1nn := RHS1_nonneg S
  have hRHS2nn := RHS2_nonneg S
  have hRHSnn : (0:ℝ) ≤ S.x * P.G * S.Ω ^ 2
      + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
      + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by linarith
  set RHS1 : ℝ := S.x * P.G * S.Ω ^ 2 with hRHS1def
  set RHS2 : ℝ := S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ) with hRHS2def
  set RHS3 : ℝ := P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) with hRHS3def
  set V3 : ℝ := P.H * RHS3 with hV3def
  have hV3pos : 0 < V3 := by rw [hV3def, hRHS3def]; positivity
  -- X^{Cu} ≥ 1
  have hXpow : (1:ℝ) ≤ P.X ^ (C * P.u) := Real.one_le_rpow hX (by positivity)
  -- the swap
  have hswap := prop6_swap (P := P) (S := S) hAD
    (by linarith [hΩfloor] : (500:ℝ) ≤ P.G * P.H * S.Ω ^ 3) RaOf hwit
  refine le_trans hswap ?_
  set Ua : Finset ℕ := Finset.Icc ⌈(1/72) * S.R⌉₊ ⌊16 * S.R⌋₊ with hUadef
  -- The target packaging value `Tgt`.
  set Tgt : ℝ := C * P.H * P.X ^ (C * P.u) * (RHS1 + RHS2 + RHS3) with hTgtdef
  have hTgtnn : 0 ≤ Tgt := by rw [hTgtdef]; positivity
  -- Empty window case.
  rcases Finset.eq_empty_or_nonempty Ua with hempty | hne
  · rw [hempty]; simp only [Finset.sum_empty]; exact hTgtnn
  -- Non-empty ⟹ 1/16 ≤ R, 1 ≤ 16R, |Ua| ≤ 32R.
  obtain ⟨r0, hr0mem⟩ := hne
  have hRge : (1/16 : ℝ) ≤ S.R := by
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hr0mem
    have h1 : 1 ≤ ⌊16 * S.R⌋₊ := by
      have : 1 ≤ ⌈(1/72) * S.R⌉₊ := Nat.ceil_pos.mpr (by positivity)
      omega
    have : (1:ℝ) ≤ 16 * S.R := le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
    linarith
  have h16R : (1:ℝ) ≤ 16 * S.R := by linarith [hRge]
  have hcardle : (Ua.card : ℝ) ≤ 32 * S.R := by
    rw [hUadef, Nat.card_Icc]
    have hnat : (⌊16 * S.R⌋₊ + 1 - ⌈(1/72) * S.R⌉₊ : ℕ) ≤ ⌊16 * S.R⌋₊ + 1 := by omega
    have hcast : ((⌊16 * S.R⌋₊ + 1 - ⌈(1/72) * S.R⌉₊ : ℕ) : ℝ) ≤ ((⌊16 * S.R⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine le_trans hcast ?_
    have hfl : (⌊16 * S.R⌋₊ : ℝ) ≤ 16 * S.R := Nat.floor_le (by positivity)
    push_cast; linarith
  -- ∑_{r∈Ua} (per-r card) is what we bound (the swap RHS).
  by_cases hA1 : 1 < S.A
  · -- ── high-curvature, A > 1 : Prop 4.3 sharp count ──
    -- scale abbreviations (matching `highF_perr_count` conclusion)
    set AF13 : ℝ := (S.A * S.F) ^ (1/3 : ℝ) with hAF13def
    have hAF13nn : 0 ≤ AF13 := by rw [hAF13def]; exact Real.rpow_nonneg (by positivity) _
    set sd0F : ℝ := S.A * Real.sqrt (delta0 S / S.F) with hsd0Fdef
    have hsd0Fnn : 0 ≤ sd0F := by rw [hsd0Fdef]; positivity
    have hSHi13nn : 0 ≤ prop6ScaleHi ^ (1/3 : ℝ) := Real.rpow_nonneg hHi.le _
    have hsKL0 : 0 ≤ Real.sqrt (K0 / prop6ScaleLo) := Real.sqrt_nonneg _
    have hkk0 : (0:ℝ) ≤ kk := hcc.le
    have hAd0nn : 0 ≤ S.A * delta0 S := by positivity
    set Bperr : ℝ := kk * (3 * (prop6ScaleHi ^ (1/3 : ℝ) * AF13)
        + K0 * (S.A * delta0 S)
        + Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u)) with hBperrdef
    have hBperrnn : 0 ≤ Bperr := by
      rw [hBperrdef]
      have h3 : (0:ℝ) ≤ 3 * (prop6ScaleHi ^ (1/3 : ℝ) * AF13) := by positivity
      have h2 : (0:ℝ) ≤ K0 * (S.A * delta0 S) := by positivity
      have h1 : (0:ℝ) ≤ Real.sqrt (K0 / prop6ScaleLo) * sd0F * (logc * P.X ^ P.u) := by
        have := Real.rpow_pos_of_pos hX0 P.u
        positivity
      positivity
    -- the per-r bound via the extracted lemma
    have hperr : ∀ r ∈ Ua,
        (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
            (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ K0 * delta0 S)).card : ℝ)
          ≤ Bperr := by
      intro r hrU
      obtain ⟨hrl, hrr⟩ := Finset.mem_Icc.mp hrU
      have hr0 : (0:ℝ) < (r:ℝ) := by
        have hcpos : 0 < ⌈(1/72) * S.R⌉₊ := Nat.ceil_pos.mpr (by positivity)
        have : 1 ≤ r := le_trans hcpos hrl
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      have hrlo : (1/72) * S.R ≤ (r:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hrl)
      have hrhi : (r:ℝ) ≤ 16 * S.R := le_trans (by exact_mod_cast hrr) (Nat.floor_le (by positivity))
      have hcnt := highF_perr_count (P := P) S (r := (r:ℝ)) hX hu hg1 hAD hΩfloor hlog hF
        hr0 hrlo hrhi hA1
      rw [← hkkdef, ← hAF13def, ← hsd0Fdef, ← hlogcdef, ← hBperrdef] at hcnt
      exact hcnt
    -- sum ≤ |Ua|·Bperr ≤ 32R·Bperr
    have hsum : (∑ r ∈ Ua,
        (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
            (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ K0 * delta0 S)).card : ℝ))
        ≤ (Ua.card : ℝ) * Bperr := by
      rw [← nsmul_eq_mul]; exact Finset.sum_le_card_nsmul Ua _ _ hperr
    refine le_trans hsum ?_
    have hcard32 : (Ua.card : ℝ) * Bperr ≤ 32 * S.R * Bperr :=
      mul_le_mul_of_nonneg_right hcardle hBperrnn
    refine le_trans hcard32 ?_
    -- distribute: 32R·Bperr = 96·kk·SHi^{1/3}·(R·AF13) + 32·kk·K0·(R·Aδ0) + 32·kk·√(K0/pLo)·logc·(R·sd0F)·X^u
    -- identities mapping R·(scale) → H·RHSi
    have hidA : S.R * AF13 = P.H * RHS2 := by rw [hAF13def, hRHS2def]; exact highF_ida S
    have hidB : S.R * (S.A * delta0 S) = P.H * RHS1 := by
      rw [hRHS1def]; rw [show S.R * (S.A * delta0 S) = S.R * S.A * delta0 S by ring]; exact highF_idb S
    have hidC : S.R * sd0F = P.H * RHS3 := by
      rw [hsd0Fdef, hRHS3def]
      rw [show S.R * (S.A * Real.sqrt (delta0 S / S.F)) = S.R * S.A * Real.sqrt (delta0 S / S.F) by ring]
      exact highF_idc S
    -- rewrite 32R·Bperr in terms of H·RHSi
    have hexpand : 32 * S.R * Bperr
        = 96 * kk * prop6ScaleHi ^ (1/3 : ℝ) * (S.R * AF13)
          + 32 * kk * K0 * (S.R * (S.A * delta0 S))
          + 32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc * (S.R * sd0F) * P.X ^ P.u := by
      rw [hBperrdef]; ring
    rw [hexpand, hidA, hidB, hidC]
    -- now: 96 kk SHi^{1/3} H RHS2 + 32 kk K0 H RHS1 + 32 kk √(K0/pLo) logc H RHS3 X^u ≤ Tgt
    rw [hTgtdef]
    -- each term ≤ C·H·X^{Cu}·RHSi
    have hl2K0 : (0:ℝ) ≤ Real.log (2 + Real.sqrt K0) :=
      Real.log_nonneg (by have := Real.sqrt_nonneg K0; linarith)
    -- coefficient bounds: each absolute coeff ≤ C
    have hSHicoef : (96:ℝ) * kk * prop6ScaleHi ^ (1/3 : ℝ) ≤ C := by
      have h2 : (0:ℝ) ≤ Real.sqrt (K0 / prop6ScaleLo) * logc := mul_nonneg hsKL0 hlogc0
      have hle : prop6ScaleHi ^ (1/3 : ℝ) ≤ Ccoef := by
        rw [hCcoefdef]; linarith [hK0.le, h2, hsrt0]
      calc (96:ℝ) * kk * prop6ScaleHi ^ (1/3 : ℝ)
          ≤ 96 * kk * Ccoef := mul_le_mul_of_nonneg_left hle (by linarith [hkk0])
        _ ≤ C := by rw [hCdef]; linarith
    have hK0coef : (32:ℝ) * kk * K0 ≤ C := by
      have h2 : (0:ℝ) ≤ Real.sqrt (K0 / prop6ScaleLo) * logc := mul_nonneg hsKL0 hlogc0
      have hle : K0 ≤ Ccoef := by
        rw [hCcoefdef]; linarith [hSHi13nn, h2, hsrt0]
      calc (32:ℝ) * kk * K0
          ≤ 96 * kk * Ccoef :=
            mul_le_mul (by linarith [hkk0]) hle hK0.le (by linarith [hkk0])
        _ ≤ C := by rw [hCdef]; linarith
    have hRHS3coef : (32:ℝ) * kk * Real.sqrt (K0 / prop6ScaleLo) * logc ≤ C := by
      have h3 : (0:ℝ) ≤ Real.sqrt (K0 / prop6ScaleLo) * logc := mul_nonneg hsKL0 hlogc0
      have hle : Real.sqrt (K0 / prop6ScaleLo) * logc ≤ Ccoef := by
        rw [hCcoefdef]; linarith [hSHi13nn, hK0.le, hsrt0]
      have heq : (32:ℝ) * kk * Real.sqrt (K0 / prop6ScaleLo) * logc
          = 32 * kk * (Real.sqrt (K0 / prop6ScaleLo) * logc) := by ring
      rw [heq]
      calc (32:ℝ) * kk * (Real.sqrt (K0 / prop6ScaleLo) * logc)
          ≤ 96 * kk * Ccoef :=
            mul_le_mul (by linarith [hkk0]) hle h3 (by linarith [hkk0])
        _ ≤ C := by rw [hCdef]; linarith
    -- X^u ≤ X^{Cu}
    have hXuCu : P.X ^ P.u ≤ P.X ^ (C * P.u) :=
      Real.rpow_le_rpow_of_exponent_le hX (le_mul_of_one_le_left hu.le hC1)
    have hHnn : (0:ℝ) ≤ P.H := hH.le
    have hkkH : (0:ℝ) ≤ kk := hkk0
    -- term 1 (RHS2)
    have t1 : 96 * kk * prop6ScaleHi ^ (1/3 : ℝ) * (P.H * RHS2)
        ≤ C * P.H * P.X ^ (C * P.u) * RHS2 := by
      have hcoef := mul_le_mul_of_nonneg_right hSHicoef (mul_nonneg hHnn hRHS2nn)
      calc 96 * kk * prop6ScaleHi ^ (1/3 : ℝ) * (P.H * RHS2)
          = (96 * kk * prop6ScaleHi ^ (1/3 : ℝ)) * (P.H * RHS2) := by ring
        _ ≤ C * (P.H * RHS2) := hcoef
        _ = C * P.H * 1 * RHS2 := by ring
        _ ≤ C * P.H * P.X ^ (C * P.u) * RHS2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXpow (by positivity)) hRHS2nn
    -- term 2 (RHS1)
    have t2 : 32 * kk * K0 * (P.H * RHS1)
        ≤ C * P.H * P.X ^ (C * P.u) * RHS1 := by
      have hcoef := mul_le_mul_of_nonneg_right hK0coef (mul_nonneg hHnn hRHS1nn)
      calc 32 * kk * K0 * (P.H * RHS1)
          = (32 * kk * K0) * (P.H * RHS1) := by ring
        _ ≤ C * (P.H * RHS1) := hcoef
        _ = C * P.H * 1 * RHS1 := by ring
        _ ≤ C * P.H * P.X ^ (C * P.u) * RHS1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXpow (by positivity)) hRHS1nn
    -- term 3 (RHS3, with X^u)
    have t3 : 32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc * (P.H * RHS3) * P.X ^ P.u
        ≤ C * P.H * P.X ^ (C * P.u) * RHS3 := by
      have hcoef := mul_le_mul_of_nonneg_right hRHS3coef (mul_nonneg hHnn hRHS3pos.le)
      calc 32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc * (P.H * RHS3) * P.X ^ P.u
          = ((32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc) * (P.H * RHS3)) * P.X ^ P.u := by ring
        _ ≤ (C * (P.H * RHS3)) * P.X ^ P.u :=
            mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos hX0 _).le
        _ = C * P.H * RHS3 * P.X ^ P.u := by ring
        _ ≤ C * P.H * RHS3 * P.X ^ (C * P.u) :=
            mul_le_mul_of_nonneg_left hXuCu (by positivity)
        _ = C * P.H * P.X ^ (C * P.u) * RHS3 := by ring
    -- combine: each Tgt-term widened over the full RHS sum
    have hTgtsplit : C * P.H * P.X ^ (C * P.u) * RHS1
          + C * P.H * P.X ^ (C * P.u) * RHS2
          + C * P.H * P.X ^ (C * P.u) * RHS3
        = C * P.H * P.X ^ (C * P.u) * (RHS1 + RHS2 + RHS3) := by ring
    -- assemble LHS ≤ sum of the three Tgt-terms
    have hLHSeq : 96 * kk * prop6ScaleHi ^ (1/3 : ℝ) * (P.H * RHS2)
          + 32 * kk * K0 * (P.H * RHS1)
          + 32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc * (P.H * RHS3) * P.X ^ P.u
        = 96 * kk * prop6ScaleHi ^ (1/3 : ℝ) * (P.H * RHS2)
          + 32 * kk * K0 * (P.H * RHS1)
          + 32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc * (P.H * RHS3) * P.X ^ P.u := rfl
    calc 96 * kk * prop6ScaleHi ^ (1/3 : ℝ) * (P.H * RHS2)
          + 32 * kk * K0 * (P.H * RHS1)
          + 32 * kk * Real.sqrt (K0 / prop6ScaleLo) * logc * (P.H * RHS3) * P.X ^ P.u
        ≤ C * P.H * P.X ^ (C * P.u) * RHS2
          + C * P.H * P.X ^ (C * P.u) * RHS1
          + C * P.H * P.X ^ (C * P.u) * RHS3 := by linarith [t1, t2, t3]
      _ = C * P.H * P.X ^ (C * P.u) * (RHS1 + RHS2 + RHS3) := by ring
  · -- ── A ≤ 1 : index set has ≤ 2 elements, count ≤ 2 per r ──
    push Not at hA1
    -- each per-r filter card ≤ 2
    have hperr2 : ∀ r ∈ Ua,
        (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
            (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ K0 * delta0 S)).card : ℝ) ≤ 2 := by
      intro r _
      have hcardf : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
          (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ K0 * delta0 S)).card
          ≤ (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card := Finset.card_filter_le _ _
      have hIcc2 : (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card ≤ 2 := by
        rw [Int.card_Icc]
        have hce1 : (1:ℤ) ≤ ⌈S.A⌉ := Int.one_le_ceil_iff.mpr hApos
        have hfl2 : ⌊2 * S.A⌋ ≤ 2 := by
          rw [Int.floor_le_iff]; push_cast; linarith [hA1]
        omega
      have : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
          (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ K0 * delta0 S)).card ≤ 2 :=
        le_trans hcardf hIcc2
      exact_mod_cast this
    -- ∑ ≤ 2·|Ua| ≤ 64R
    have hsum2 : (∑ r ∈ Ua,
        (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
            (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ K0 * delta0 S)).card : ℝ))
        ≤ (Ua.card : ℝ) * 2 := by
      rw [← nsmul_eq_mul]
      exact Finset.sum_le_card_nsmul Ua _ _ hperr2
    refine le_trans hsum2 ?_
    have h64R : (Ua.card : ℝ) * 2 ≤ 64 * S.R := by linarith [hcardle]
    refine le_trans h64R ?_
    -- 64R = 64·A·RHS1 ≤ 64·H·RHS1 ≤ Tgt
    have hReq : S.R = S.A * RHS1 := by rw [hRHS1def]; exact highF_R_eq_A_RHS1 S
    have hRle : S.R ≤ P.H * RHS1 := by
      rw [hReq]
      exact mul_le_mul_of_nonneg_right (le_trans hA1 hHge1) hRHS1nn
    have h64HRHS1 : (64:ℝ) * S.R ≤ 64 * (P.H * RHS1) := by linarith [hRle]
    refine le_trans h64HRHS1 ?_
    rw [hTgtdef]
    -- 64·H·RHS1 ≤ C·H·X^{Cu}·(RHS1+RHS2+RHS3)
    have hCcoef1 : (1:ℝ) ≤ Ccoef := by
      rw [hCcoefdef]
      have h1 : (0:ℝ) ≤ prop6ScaleHi ^ (1/3 : ℝ) := Real.rpow_nonneg hHi.le _
      have h2 : (0:ℝ) ≤ Real.sqrt (K0 / prop6ScaleLo) * logc :=
        mul_nonneg (Real.sqrt_nonneg _) hlogc0
      linarith [hK0, hsrt0, h1, h2]
    have h64C : (64:ℝ) ≤ C := by
      rw [hCdef]
      have hm : (2:ℝ) ≤ kk * Ccoef := by
        have := mul_le_mul hkk2 hCcoef1 (by norm_num) hcc.le; linarith [this]
      linarith [hm]
    have e1 : (64:ℝ) * (P.H * RHS1) ≤ C * (P.H * RHS1) :=
      mul_le_mul_of_nonneg_right h64C (by positivity)
    refine le_trans e1 ?_
    have e2 : C * (P.H * RHS1) ≤ C * P.H * P.X ^ (C * P.u) * (RHS1 + RHS2 + RHS3) := by
      have hbase : C * (P.H * RHS1) ≤ C * P.H * P.X ^ (C * P.u) * RHS1 := by
        have : C * (P.H * RHS1) = C * P.H * 1 * RHS1 := by ring
        rw [this]
        have hstep : C * P.H * 1 * RHS1 ≤ C * P.H * P.X ^ (C * P.u) * RHS1 := by
          apply mul_le_mul_of_nonneg_right _ hRHS1nn
          apply mul_le_mul_of_nonneg_left hXpow (by positivity)
        exact hstep
      refine le_trans hbase ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hRHS2nn, hRHS3pos]
    exact e2

end Prop61

/-- **Prop 6.1** (writeup 1230–1236); `x = H/Δ²` is `S.x`; the single `C` is both the `≪`
constant and the absolute `X^{O(u)}` budget constant.  The `a ↔ r` swap reduces to per-`r`
integer counts; a curvature split (`prop6ScaleLo·F` vs `1`) feeds the elementary low-curvature
count (`prop6_lowF`) or the Prop 4.3 sharp count (`prop6_highF`). -/
theorem prop_6_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P), 1 ≤ P.X → 0 < P.u → P.g ≤ 1 → 10 * S.A ≤ S.D →
      P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω →
      (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 →
      Real.log P.X ≤ P.X ^ P.u →
      ∀ (RaOf : ℤ → Finset ℕ),
      (∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (0 < a) ∧ ∀ r ∈ RaOf a, RaWitness P S a r) →
      (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) ≤
        C * P.H * P.X ^ (C * P.u) *
          ( S.x * P.G * S.Ω ^ 2
          + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
          + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) ) := by
  obtain ⟨Clo, hClo, hlo⟩ := Prop61.prop6_lowF
  obtain ⟨Chi, hChi, hhi⟩ := Prop61.prop6_highF
  refine ⟨max Clo Chi, lt_max_of_lt_left hClo, ?_⟩
  intro P S hX hu hg1 hAD hband hΩfloor hlog RaOf hwit
  have hu0 : 0 ≤ P.u := hu.le
  have hRHSnn : (0:ℝ) ≤ S.x * P.G * S.Ω ^ 2
      + S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ)
      + P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) := by
    have := Prop61.RHS1_nonneg S; have := Prop61.RHS2_nonneg S
    have := Prop61.RHS3_pos S; linarith
  by_cases hF : 1 < prop6ScaleLo * S.F
  · have h := hhi P S hX hu hg1 hAD hband hΩfloor hlog hF RaOf hwit
    exact Prop61.widen_budget S _ Chi (max Clo Chi) hX hu0 hChi (le_max_right _ _) hRHSnn h
  · have h := hlo P S hX hu hg1 hAD hband hΩfloor hF RaOf hwit
    exact Prop61.widen_budget S _ Clo (max Clo Chi) hX hu0 hClo (le_max_left _ _) hRHSnn h

end Squarefree
