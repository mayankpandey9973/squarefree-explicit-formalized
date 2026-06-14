import Squarefree.Upper.Regime6
import Squarefree.Counting.Preimage
import Mathlib

/-!
# §6 regime, low-curvature branch (`F < 1`): per-`r` count via Lemma 4.1

When the curvature scale `F = H²GΩ/Δ²` is `< 1`, the sharp Prop 4.3 count is not needed:
the phase `f̃ₐ(r)` is `≍ F` in value with first derivative `≍ F/A`, so the elementary
preimage count (`Counting.preimage_count`, Lemma 4.1) on `[A, 2A]` already gives the right
per-`r` bound.  This file supplies:

* `ftil_value_le`    — `|f̃ₐ(r)| ≤ C_v · F` on `[A/2, 5A/2]` (value `≍ F`);
* `ftil_deriv1_lb`   — `c_l · (F/A) ≤ |f̃ₐ'(r)|` on `[A, 2A]` (first-deriv lower bound);
* `prop6_count_per_r_lowF` — the per-`r` integer count, via `preimage_count`.

All constants are explicit.  See `../explicit_writeup.md` lines 1253–1308 and `math_audit.md` §6.
-/

open Classical Finset
open Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 1000000

/-- The §6 low-`F` value constant `C_v = ((17/4)²·16³·32)^{1/4}`. -/
noncomputable def Cval6 : ℝ := ((17/4 : ℝ) ^ 2 * 16 ^ 3 * 32) ^ (1/4 : ℝ)

/-- The §6 low-`F` first-derivative constant `c_l = (10/√17)·((1/72)³·(1/2)⁹)^{1/4}`. -/
noncomputable def cderiv6 : ℝ := (10 / Real.sqrt 17) * ((1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9) ^ (1/4 : ℝ)

theorem Cval6_pos : 0 < Cval6 := by unfold Cval6; positivity
theorem cderiv6_pos : 0 < cderiv6 := by
  unfold cderiv6
  have h17 : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- The polynomial identity `R³·X/A⁵ = F⁴` (writeup line 1258 scale). -/
private theorem lowF_R3X_div_A5_eq_F4 {P : Globals} (S : Scale P) :
    S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hH := P.H_pos; have hG := P.G_pos
  rw [Scale.R, Scale.A, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

/-- **Value bound `f̃ₐ ≍ F`** (writeup line 1255).  For `a ∈ [A/2, 5A/2]` and `r ∈ [R/72, 16R]`,
`|f̃ₐ(r)| ≤ C_v · F` with `C_v = ((17/4)²·16³·32)^{1/4}`.  Proved by a 4th-power comparison
against `F⁴ = R³X/A⁵`. -/
theorem ftil_value_le {P : Globals} {S : Scale P} {r a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hrhi : r ≤ 16 * S.R)
    (haL : S.A / 2 ≤ a) (haU : a ≤ 5 * S.A / 2) :
    |ftil P.X r a| ≤ Cval6 * S.F := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hapos : 0 < a := by linarith
  -- regime: 4a² ≤ w
  have hreg := prop6_curv_regime hAD hr0 hrhi a ⟨haL, haU⟩
  set w := Real.sqrt (P.X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w ^ 2 = P.X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  have hreg' : 4 * a ^ 2 ≤ w := by linarith [hreg]
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  -- ftil value = r·D/a²  (positive)
  have hval : ftil P.X r a = r * D / a ^ 2 := by rw [ftil, ← hwdef, ← hDdef]
  have hftilpos : 0 < ftil P.X r a := by rw [hval]; positivity
  rw [abs_of_pos hftilpos, hval]
  -- 4th-power comparison: (r·D/a²)⁴ ≤ (C_v·F)⁴
  have hF4 : S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := lowF_R3X_div_A5_eq_F4 S
  -- key normalization: (rD/a²)⁴ = r⁴ D⁴/a⁸ = r⁴(a²+4w)²/a⁸
  -- and r⁴ w²/a⁸ = r³X/a⁵ (since w² = Xa³/r)
  have hr4w2 : r ^ 4 * w ^ 2 / a ^ 8 = r ^ 3 * P.X / a ^ 5 := by
    rw [hw2]; field_simp
  -- D⁴ = (a²+4w)² ≤ (17/4)² w²  (since a² ≤ w/4)
  have hD4le : D ^ 4 ≤ (17/4 : ℝ) ^ 2 * w ^ 2 := by
    have hD4 : D ^ 4 = (a ^ 2 + 4 * w) ^ 2 := by rw [show D ^ 4 = (D ^ 2) ^ 2 by ring, hD2]
    rw [hD4]; nlinarith [hreg', hwpos, sq_nonneg a]
  -- (rD/a²)⁴ = r⁴ D⁴/a⁸ ≤ (17/4)² r⁴ w²/a⁸ = (17/4)² r³X/a⁵
  have hlhs4 : (r * D / a ^ 2) ^ 4 ≤ (17/4 : ℝ) ^ 2 * (r ^ 3 * P.X / a ^ 5) := by
    have hlhseq : (r * D / a ^ 2) ^ 4 = r ^ 4 * D ^ 4 / a ^ 8 := by
      rw [div_pow]; congr 1 <;> ring
    have hrhseq : (17/4 : ℝ) ^ 2 * (r ^ 3 * P.X / a ^ 5)
        = ((17/4 : ℝ) ^ 2 * r ^ 4 * w ^ 2) / a ^ 8 := by
      rw [← hr4w2]; field_simp
    rw [hlhseq, hrhseq]
    gcongr ?_ / a ^ 8
    have := mul_le_mul_of_nonneg_left hD4le (pow_pos hr0 4).le
    nlinarith [this]
  -- r³X/a⁵ ≤ 16³·32·R³X/A⁵ = 16³·32·F⁴   (r ≤ 16R, a ≥ A/2)
  have hr3X : r ^ 3 * P.X / a ^ 5 ≤ (16 ^ 3 * 32 : ℝ) * S.F ^ 4 := by
    rw [← hF4]
    have hr3 : r ^ 3 ≤ (16 * S.R) ^ 3 := pow_le_pow_left₀ hr0.le hrhi 3
    have ha5 : (S.A / 2) ^ 5 ≤ a ^ 5 := pow_le_pow_left₀ (by positivity) haL 5
    have ha5pos : 0 < (S.A / 2) ^ 5 := by positivity
    calc r ^ 3 * P.X / a ^ 5 ≤ (16 * S.R) ^ 3 * P.X / (S.A / 2) ^ 5 := by
          apply div_le_div₀ (by positivity) (by nlinarith [hr3, hX.le]) ha5pos ha5
      _ = (16 ^ 3 * 32 : ℝ) * (S.R ^ 3 * P.X / S.A ^ 5) := by ring
  -- combine
  have hC4 : (Cval6 * S.F) ^ 4 = ((17/4 : ℝ) ^ 2 * 16 ^ 3 * 32) * S.F ^ 4 := by
    rw [Cval6, mul_pow]
    rw [show (((17/4 : ℝ) ^ 2 * 16 ^ 3 * 32) ^ (1/4 : ℝ)) ^ 4
          = (17/4 : ℝ) ^ 2 * 16 ^ 3 * 32 by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]; norm_num]
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
    (mul_nonneg Cval6_pos.le hFpos.le)
  rw [hC4]
  calc (r * D / a ^ 2) ^ 4 ≤ (17/4 : ℝ) ^ 2 * (r ^ 3 * P.X / a ^ 5) := hlhs4
    _ ≤ (17/4 : ℝ) ^ 2 * ((16 ^ 3 * 32 : ℝ) * S.F ^ 4) :=
        mul_le_mul_of_nonneg_left hr3X (by positivity)
    _ = ((17/4 : ℝ) ^ 2 * 16 ^ 3 * 32) * S.F ^ 4 := by ring

/-- **First-derivative lower bound `A|f̃ₐ'| ≳ F`** (writeup line 1255).  For `a ∈ [A, 2A]` and
`r ∈ [R/72, 16R]`, `c_l · (F/A) ≤ |f̃ₐ'(r)|` with `c_l = (10/√17)·((1/72)³(1/2)⁹)^{1/4}`.
Uses the closed form `f̃'(a) = −r(a²+5w)/(a³D)` and a 4th-power comparison against `F⁴`. -/
theorem ftil_deriv1_lb {P : Globals} {S : Scale P} {r a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hrlo : (1/72) * S.R ≤ r) (hrhi : r ≤ 16 * S.R)
    (haL : S.A ≤ a) (haU : a ≤ 2 * S.A) :
    cderiv6 * (S.F / S.A) ≤ |deriv (fun t => ftil P.X r t) a| := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  have hapos : 0 < a := by linarith [hApos]
  -- a lies in the curvature window [A/2, 5A/2]
  have haL' : S.A / 2 ≤ a := by linarith
  have haU' : a ≤ 5 * S.A / 2 := by linarith
  have hreg := prop6_curv_regime hAD hr0 hrhi a ⟨haL', haU'⟩
  set w := Real.sqrt (P.X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w ^ 2 = P.X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  have hreg' : 4 * a ^ 2 ≤ w := by linarith [hreg]
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  -- deriv value (negative); |deriv| = r(a²+5w)/(a³D)
  have hderiv : deriv (fun t => ftil P.X r t) a
      = -r * (a ^ 2 + 5 * w) / (a ^ 3 * D) := by
    rw [(ftil_hasDerivAt1 P.X r a hX hr0 hapos).deriv, ← hwdef, ← hDdef]
  have hsqw : Real.sqrt w ^ 2 = w := Real.sq_sqrt hwpos.le
  have hsqwpos : 0 < Real.sqrt w := Real.sqrt_pos.mpr hwpos
  have habs : |deriv (fun t => ftil P.X r t) a| = r * (a ^ 2 + 5 * w) / (a ^ 3 * D) := by
    rw [hderiv]
    have hneg : -r * (a ^ 2 + 5 * w) / (a ^ 3 * D) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [hr0, hwpos, sq_nonneg a]
    rw [abs_of_nonpos hneg]
    field_simp
  rw [habs]
  -- Step A: r(a²+5w)/(a³D) ≥ (10/√17)·r√w/a³
  -- since a²+5w ≥ 5w and D ≤ (√17/2)·√w
  have hsqrt17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hDle : D ≤ (Real.sqrt 17 / 2) * Real.sqrt w := by
    have hrhsnn : 0 ≤ (Real.sqrt 17 / 2) * Real.sqrt w := by positivity
    have hsq : D ^ 2 ≤ ((Real.sqrt 17 / 2) * Real.sqrt w) ^ 2 := by
      rw [hD2, mul_pow, div_pow, hsqrt17, hsqw]
      nlinarith [hreg', hwpos]
    nlinarith [hsq, hDpos.le, hrhsnn, sq_nonneg (D - (Real.sqrt 17 / 2) * Real.sqrt w)]
  have h17 : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have hstepA : (10 / Real.sqrt 17) * (r * Real.sqrt w / a ^ 3)
      ≤ r * (a ^ 2 + 5 * w) / (a ^ 3 * D) := by
    have hLeq : (10 / Real.sqrt 17) * (r * Real.sqrt w / a ^ 3)
        = ((10 / Real.sqrt 17) * (r * Real.sqrt w)) / a ^ 3 := by ring
    rw [hLeq, div_le_div_iff₀ (by positivity) (by positivity)]
    -- (10/√17)·r√w·(a³D) ≤ r(a²+5w)·a³
    have hnum : 5 * w ≤ a ^ 2 + 5 * w := by nlinarith [sq_nonneg a]
    have hkey : (10 / Real.sqrt 17) * (r * Real.sqrt w) * D
        ≤ r * (a ^ 2 + 5 * w) := by
      have h1 : (10 / Real.sqrt 17) * (r * Real.sqrt w) * D
          ≤ (10 / Real.sqrt 17) * (r * Real.sqrt w) * ((Real.sqrt 17 / 2) * Real.sqrt w) :=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      have h2 : (10 / Real.sqrt 17) * (r * Real.sqrt w) * ((Real.sqrt 17 / 2) * Real.sqrt w)
          = r * (5 * w) := by
        field_simp
        nlinarith [hsqw, hsqrt17, h17]
      calc (10 / Real.sqrt 17) * (r * Real.sqrt w) * D
          ≤ r * (5 * w) := by rw [h2] at h1; exact h1
        _ ≤ r * (a ^ 2 + 5 * w) := by nlinarith [hr0, hnum]
    nlinarith [mul_le_mul_of_nonneg_right hkey (pow_pos hapos 3).le, pow_pos hapos 3,
      mul_pos (pow_pos hapos 3) hDpos]
  refine le_trans ?_ hstepA
  -- Step B: c_l·(F/A) ≤ (10/√17)·r√w/a³, via 4th-power comparison
  -- (r√w/a³)⁴ = r³X/a⁹ ;  (F/A)⁴ = R³X/A⁹
  have hF4 : S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := lowF_R3X_div_A5_eq_F4 S
  -- (r√w/a³)⁴ = r³X/a⁹
  have hlhs4 : (r * Real.sqrt w / a ^ 3) ^ 4 = r ^ 3 * P.X / a ^ 9 := by
    rw [div_pow, mul_pow]
    rw [show (Real.sqrt w) ^ 4 = w ^ 2 by rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, hsqw]]
    rw [hw2]; field_simp
  -- (F/A)⁴ = R³X/A⁹
  have hrhs4 : (S.F / S.A) ^ 4 = S.R ^ 3 * P.X / S.A ^ 9 := by
    rw [div_pow, ← hF4]; field_simp
  -- r³X/a⁹ ≥ (1/72)³(1/2)⁹·R³X/A⁹
  have hcomp : ((1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9) * (S.R ^ 3 * P.X / S.A ^ 9)
      ≤ r ^ 3 * P.X / a ^ 9 := by
    have hr3 : ((1/72 : ℝ) * S.R) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by positivity) hrlo 3
    have ha9 : a ^ 9 ≤ (2 * S.A) ^ 9 := pow_le_pow_left₀ hapos.le haU 9
    have hXpos : 0 < P.X := hX
    calc ((1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9) * (S.R ^ 3 * P.X / S.A ^ 9)
        = ((1/72 : ℝ) * S.R) ^ 3 * P.X / (2 * S.A) ^ 9 := by ring
      _ ≤ r ^ 3 * P.X / (2 * S.A) ^ 9 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [hr3, hX.le]
      _ ≤ r ^ 3 * P.X / a ^ 9 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) ha9
  -- Step B core: ((1/72)³(1/2)⁹)^{1/4}·(F/A) ≤ r√w/a³  (4th-power comparison)
  set cB : ℝ := ((1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9) ^ (1/4 : ℝ) with hcBdef
  have hcBpos : 0 < cB := by rw [hcBdef]; positivity
  have hStepB : cB * (S.F / S.A) ≤ r * Real.sqrt w / a ^ 3 := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
    rw [hlhs4, mul_pow]
    rw [show (cB ^ 4 : ℝ) = (1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9 by
      rw [hcBdef, ← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]; norm_num]
    calc (1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9 * (S.F / S.A) ^ 4
        = ((1/72 : ℝ) ^ 3 * (1/2 : ℝ) ^ 9) * (S.R ^ 3 * P.X / S.A ^ 9) := by rw [hrhs4]
      _ ≤ r ^ 3 * P.X / a ^ 9 := hcomp
  -- combine: cderiv6·(F/A) = (10/√17)·(cB·(F/A)) ≤ (10/√17)·(r√w/a³)
  have hfinal : cderiv6 * (S.F / S.A) = (10 / Real.sqrt 17) * (cB * (S.F / S.A)) := by
    rw [cderiv6, hcBdef]; ring
  rw [hfinal]
  exact mul_le_mul_of_nonneg_left hStepB (by positivity)

/-- **MVT expansion**: with `f̃ₐ'` strictly negative and `|f̃ₐ'| ≥ Fexp` throughout `[A,2A]`,
the phase `f̃` expands: `Fexp·|x − y| ≤ |f̃(x) − f̃(y)|` for `x,y ∈ [A,2A]`. -/
private theorem ftil_expand {P : Globals} {S : Scale P} {r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hrlo : (1/72) * S.R ≤ r) (hrhi : r ≤ 16 * S.R) :
    ∀ x ∈ Set.Icc S.A (2 * S.A), ∀ y ∈ Set.Icc S.A (2 * S.A),
      (cderiv6 * (S.F / S.A)) * |x - y| ≤ |ftil P.X r x - ftil P.X r y| := by
  have hX := P.X_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hApos : 0 < S.A := by rw [show S.A = S.Δ * S.Ω from rfl]; positivity
  -- the deriv-function of ftil and its derivative
  have hderivAt : ∀ c : ℝ, 0 < c → HasDerivAt (fun t => ftil P.X r t)
      (deriv (fun t => ftil P.X r t) c) c := by
    intro c hc
    have h := ftil_hasDerivAt1 P.X r c hX hr0 hc
    rw [h.deriv]; exact h
  intro x hx y hy
  obtain ⟨hxL, hxU⟩ := hx
  obtain ⟨hyL, hyU⟩ := hy
  -- WLOG handle x = y, x < y, y < x symmetrically via the slope MVT
  rcases lt_trichotomy x y with hlt | heq | hgt
  · -- x < y
    have hcont : ContinuousOn (fun t => ftil P.X r t) (Set.Icc x y) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hApos (le_trans hxL hs.1)
      exact ((ftil_hasDerivAt1 P.X r s hX hr0 hs0).continuousAt).continuousWithinAt
    have hderiv : ∀ s ∈ Set.Ioo x y, HasDerivAt (fun t => ftil P.X r t)
        (deriv (fun t => ftil P.X r t) s) s := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hApos (le_trans hxL (le_of_lt hs.1))
      exact hderivAt s hs0
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
    have hcmem : c ∈ Set.Icc S.A (2 * S.A) :=
      ⟨le_trans hxL hc.1.le, le_trans hc.2.le hyU⟩
    have hclb := ftil_deriv1_lb hAD hr0 hrlo hrhi hcmem.1 hcmem.2
    -- slope = (ftil y - ftil x)/(y-x); |slope|·(y-x) = |ftil y - ftil x|
    have hslope' : deriv (fun t => ftil P.X r t) c
        = (ftil P.X r y - ftil P.X r x) / (y - x) := hslope
    have hyx : (0:ℝ) < y - x := by linarith
    have heq2 : |ftil P.X r x - ftil P.X r y|
        = |deriv (fun t => ftil P.X r t) c| * (y - x) := by
      rw [hslope', abs_div, abs_of_pos hyx, abs_sub_comm,
        div_mul_cancel₀ _ (ne_of_gt hyx)]
    rw [heq2, abs_of_neg (by linarith : x - y < 0), neg_sub]
    exact mul_le_mul_of_nonneg_right hclb hyx.le
  · rw [heq, sub_self, abs_zero, sub_self, abs_zero, mul_zero]
  · -- y < x  (symmetric)
    have hcont : ContinuousOn (fun t => ftil P.X r t) (Set.Icc y x) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hApos (le_trans hyL hs.1)
      exact ((ftil_hasDerivAt1 P.X r s hX hr0 hs0).continuousAt).continuousWithinAt
    have hderiv : ∀ s ∈ Set.Ioo y x, HasDerivAt (fun t => ftil P.X r t)
        (deriv (fun t => ftil P.X r t) s) s := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hApos (le_trans hyL (le_of_lt hs.1))
      exact hderivAt s hs0
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope _ _ hgt hcont hderiv
    have hcmem : c ∈ Set.Icc S.A (2 * S.A) :=
      ⟨le_trans hyL hc.1.le, le_trans hc.2.le hxU⟩
    have hclb := ftil_deriv1_lb hAD hr0 hrlo hrhi hcmem.1 hcmem.2
    have hslope' : deriv (fun t => ftil P.X r t) c
        = (ftil P.X r x - ftil P.X r y) / (x - y) := hslope
    have hxy : (0:ℝ) < x - y := by linarith
    have heq2 : |ftil P.X r x - ftil P.X r y|
        = |deriv (fun t => ftil P.X r t) c| * (x - y) := by
      rw [hslope', abs_div, abs_of_pos hxy, div_mul_cancel₀ _ (ne_of_gt hxy)]
    rw [heq2, abs_of_pos (by linarith : (0:ℝ) < x - y)]
    exact mul_le_mul_of_nonneg_right hclb (by linarith)

/-- **Per-`r` count, low-`F` branch** (writeup line 1267).  For `r ∈ [R/72, 16R]`, `F < 1`,
and a near-integer width `0 < δ < 1`, the number of `a ∈ [⌈A⌉, ⌊2A⌋]` with
`distInt(f̃ₐ(r)) ≤ δ` is at most `(2·C_v + 2δ + 1)·(2δ·A/(c_l·F) + 1)`, by `preimage_count`
(Lemma 4.1) applied on `[A, 2A]` with `Fexp = c_l·F/A` and `V = 2·C_v·F`. -/
theorem prop6_count_per_r_lowF {P : Globals} {S : Scale P} {r δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hrlo : (1/72) * S.R ≤ r) (hrhi : r ≤ 16 * S.R)
    (hδ0 : 0 < δ) :
    (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
        (fun (n : ℤ) => distInt (ftil P.X r (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (2 * Cval6 * S.F + 2 * δ + 1) * (2 * δ / (cderiv6 * S.F / S.A) + 1) := by
  have hX := P.X_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hApos : 0 < S.A := by rw [show S.A = S.Δ * S.Ω from rfl]; positivity
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  set Fexp : ℝ := cderiv6 * S.F / S.A with hFexpdef
  have hFexppos : 0 < Fexp := by
    rw [hFexpdef]; exact div_pos (mul_pos cderiv6_pos hFpos) hApos
  set V : ℝ := 2 * Cval6 * S.F with hVdef
  have hVnn : 0 ≤ V := by
    rw [hVdef]; exact mul_nonneg (mul_nonneg (by norm_num) Cval6_pos.le) hFpos.le
  -- expansion (hexp)
  have hexp : ∀ x ∈ Set.Icc S.A (2 * S.A), ∀ y ∈ Set.Icc S.A (2 * S.A),
      Fexp * |x - y| ≤ |ftil P.X r x - ftil P.X r y| := by
    intro x hx y hy
    have h := ftil_expand hAD hr0 hrlo hrhi x hx y hy
    have : Fexp = cderiv6 * (S.F / S.A) := by rw [hFexpdef]; ring
    rw [this]; exact h
  -- variation (hvar)
  have hvar : ∀ x ∈ Set.Icc S.A (2 * S.A), ∀ y ∈ Set.Icc S.A (2 * S.A),
      |ftil P.X r x - ftil P.X r y| ≤ V := by
    intro x hx y hy
    obtain ⟨hxL, hxU⟩ := hx
    obtain ⟨hyL, hyU⟩ := hy
    have hvx := ftil_value_le hAD hr0 hrhi (by linarith : S.A / 2 ≤ x) (by linarith)
    have hvy := ftil_value_le hAD hr0 hrhi (by linarith : S.A / 2 ≤ y) (by linarith)
    calc |ftil P.X r x - ftil P.X r y| ≤ |ftil P.X r x| + |ftil P.X r y| := abs_sub _ _
      _ ≤ Cval6 * S.F + Cval6 * S.F := add_le_add hvx hvy
      _ = V := by rw [hVdef]; ring
  -- apply preimage_count with a = A, b = 2A, φ = ftil P.X r ·
  have hkey := preimage_count S.A (2 * S.A) V Fexp δ (fun t => ftil P.X r t)
    hFexppos hδ0.le hVnn hexp hvar
  -- the bound; ⌈A⌉..⌊2A⌋ matches
  rw [hVdef, hFexpdef] at hkey ⊢
  exact hkey

end Squarefree
