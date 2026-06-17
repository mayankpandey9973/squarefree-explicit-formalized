import Squarefree.Lower.Step2CountCurv
import Squarefree.Lower.Step23Phase

/-!
# §5 Step-2 all-`f` lower bound at the FULL variation scale `T = T₀ + T_curv`

`phif_lower_max` upgrades the all-`f` curvature lower bound `phif_curvature_lower_band` (which only
carries the curvature scale `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`) to the full §5 variation scale
`T₀ + T_curv` with `T₀ = |f|·D⁴/(X·A)`, matching writeup line 913 (`|φ_f'|+R|φ_f''| ≍ T/R`,
`T = max(T₀,T_curv)`).  The mechanism is the exact scale identity `L·κ = T_curv`
(`κ = D⁴/(X·A)`, `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(G·Ω⁵)`), so that the `f`-large threshold `10⁵⁵·L ≤ |f|` is
EXACTLY `10⁵⁵·T_curv ≤ T₀`:

* `|f| ≥ 10⁵⁵·L` (so `T₀ ≥ 10⁵⁵·T_curv ≥ T_curv`): the `f`-large derivative floor `phif_deriv_lb`
  (`T₀/(R·10⁵⁰) ≤ |φ_f'|`) dominates `T₀ + T_curv ≤ 2·T₀`;
* `|f| < 10⁵⁵·L` (so `T₀ < 10⁵⁵·T_curv`, hence `T₀ + T_curv ≤ 2·10⁵⁵·T_curv`): the curvature band
  `(1/(5184·10⁷²))·T_curv/N ≤ |φ_f'|+N|φ_f''|` carries it.

With the absolute constant `cl = 1/(5184·10¹²⁸)` both cases close.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **Scale identity `L·κ = T_curv`.**  `(ℓ₁ℓ₂(ℓ₂−ℓ₁)/(G·Ω⁵))·(D⁴/(X·A)) = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`,
the bridge between the geometric threshold scale `L` and the curvature scale `T_curv`. -/
private theorem Lkappa_eq_Tcurv (ℓ₁ ℓ₂ : ℝ) :
    (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) * (S.D ^ 4 / (P.X * S.A))
      = ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.B Scale.D Scale.A
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

/-- **§5 Step-2 all-`f` lower bound at the full scale `T₀ + T_curv`.**  For ALL `f`, with band
scale `N` (`R ≤ 72·N`), `cl·((T₀ + T_curv)/N) ≤ |φ_f'(r)| + N·|φ_f''(r)|`, where
`T₀ = |f|·D⁴/(X·A)`, `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`, and `cl = 1/(5184·10¹²⁸)`. -/
theorem phif_lower_max {a ℓ₁ ℓ₂ f r N : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1 / 72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 78 * ℓ₁ ≤ S.R)
    (hNpos : 0 < N) (hRN : S.R ≤ 72 * N) :
    (1 / (5184 * 10 ^ 128))
        * ((|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / N)
      ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r|
        + N * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hXpos : 0 < P.X := P.X_pos
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  set κ : ℝ := S.D ^ 4 / (P.X * S.A) with hκ_def
  have hκpos : 0 < κ := by rw [hκ_def]; positivity
  set L : ℝ := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; have := P.G_pos; have := S.Ω_pos; positivity
  set T₀ : ℝ := |f| * S.D ^ 4 / (P.X * S.A) with hT0_def
  have hT0_eq : T₀ = |f| * κ := by rw [hT0_def, hκ_def]; ring
  have hT0nn : 0 ≤ T₀ := by rw [hT0_def]; positivity
  set Tc : ℝ := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D with hTc_def
  have hTcpos : 0 < Tc := by rw [hTc_def]; positivity
  -- the scale bridge `T_curv = L·κ`
  have hTc_eq : Tc = L * κ := by rw [hTc_def, hL_def, hκ_def]; exact (Lkappa_eq_Tcurv ℓ₁ ℓ₂).symm
  set A := |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| with hA_def
  set Bv := N * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| with hBv_def
  have hAnn : 0 ≤ A := abs_nonneg _
  have hBvnn : 0 ≤ Bv := by rw [hBv_def]; positivity
  have hsmall33 : (10 : ℝ) ^ 33 * ℓ₁ ≤ S.R :=
    le_trans (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 33, hℓ1.le]) hsmall
  by_cases hfl : (10 : ℝ) ^ 55 * L ≤ |f|
  · -- f-large:  T₀ ≥ 10⁵⁵·T_curv, the derivative floor dominates.
    have hflarge : (10 : ℝ) ^ 55 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f| := hfl
    have hlb := phif_deriv_lb (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hsmall33 hflarge
    -- `|f|·D⁴/(XA·R·10⁵⁰) = T₀/(R·10⁵⁰)`
    have hlb' : T₀ / (S.R * 10 ^ 50) ≤ A := by
      rw [hA_def]
      have : |f| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50) = T₀ / (S.R * 10 ^ 50) := by
        rw [hT0_def]; ring
      rwa [this] at hlb
    -- T_curv ≤ T₀
    have hTc_le_T0 : Tc ≤ T₀ := by
      rw [hTc_eq, hT0_eq]
      have : 10 ^ 55 * L * κ ≤ |f| * κ := mul_le_mul_of_nonneg_right hfl hκpos.le
      nlinarith [this, mul_pos hLpos hκpos, one_le_pow₀ (show (1:ℝ) ≤ 10 by norm_num) (n := 55)]
    -- assemble:  cl·(T₀+Tc)/N ≤ T₀/(R·10⁵⁰) ≤ A
    have hkey : (1 / (5184 * 10 ^ 128)) * ((T₀ + Tc) / N) ≤ T₀ / (S.R * 10 ^ 50) := by
      have h2T0 : T₀ + Tc ≤ 2 * T₀ := by linarith [hTc_le_T0]
      rw [show (1 / (5184 * 10 ^ 128)) * ((T₀ + Tc) / N)
            = (T₀ + Tc) / ((5184 * 10 ^ 128) * N) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- (T₀+Tc)·(R·10^50) ≤ T₀·(5184·10^128·N)
      have hc1 : (T₀ + Tc) * (S.R * 10 ^ 50) ≤ (2 * T₀) * (S.R * 10 ^ 50) :=
        mul_le_mul_of_nonneg_right h2T0 (by positivity)
      have hc2 : (2 * T₀) * (S.R * 10 ^ 50) ≤ (2 * T₀) * ((72 * N) * 10 ^ 50) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hRN (by positivity)
      have hc3 : (2 * T₀) * ((72 * N) * 10 ^ 50) ≤ T₀ * (5184 * 10 ^ 128 * N) := by
        rw [show (2 * T₀) * ((72 * N) * 10 ^ 50) = (144 * 10 ^ 50) * (T₀ * N) by ring,
            show T₀ * (5184 * 10 ^ 128 * N) = (5184 * 10 ^ 128) * (T₀ * N) by ring]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hT0nn hNpos.le)
        norm_num
      linarith [hc1, hc2, hc3]
    calc (1 / (5184 * 10 ^ 128)) * ((T₀ + Tc) / N)
        ≤ T₀ / (S.R * 10 ^ 50) := hkey
      _ ≤ A := hlb'
      _ ≤ A + Bv := by linarith [hBvnn]
  · -- f-small:  T₀ < 10⁵⁵·T_curv, the curvature floor carries it.
    push Not at hfl
    have hband := phif_curvature_lower_band (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      (f := f) (r := r) (N := N)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hsmall hNpos hRN
    -- `phif_curvature_lower_band`'s LHS is `(1/(5184·10⁷²))·Tc/N`
    have hband' : (1 / (5184 * 10 ^ 72)) * (Tc / N) ≤ A + Bv := by
      rw [hA_def, hBv_def, hTc_def]
      have heq : (1 / (5184 * 10 ^ 72))
          * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / N
          = (1 / (5184 * 10 ^ 72)) * ((ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / N) := by ring
      rw [heq] at hband; exact hband
    -- T₀ < 10⁵⁵·Tc  ⟹  T₀ + Tc ≤ 2·10⁵⁵·Tc
    have hT0_lt : T₀ < 10 ^ 55 * Tc := by
      rw [hT0_eq, hTc_eq]
      have : |f| * κ < 10 ^ 55 * L * κ := by
        have := mul_lt_mul_of_pos_right hfl hκpos; linarith [this]
      nlinarith [this]
    have hkey : (1 / (5184 * 10 ^ 128)) * ((T₀ + Tc) / N) ≤ (1 / (5184 * 10 ^ 72)) * (Tc / N) := by
      have hbound : T₀ + Tc ≤ 2 * 10 ^ 55 * Tc := by nlinarith [hT0_lt, hTcpos.le]
      rw [show (1 / (5184 * 10 ^ 128)) * ((T₀ + Tc) / N) = (T₀ + Tc) / ((5184 * 10 ^ 128) * N) by ring,
          show (1 / (5184 * 10 ^ 72)) * (Tc / N) = Tc / ((5184 * 10 ^ 72) * N) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (T₀ + Tc) * (5184 * 10 ^ 72 * N) ≤ (2 * 10 ^ 55 * Tc) * (5184 * 10 ^ 72 * N) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
      refine le_trans h1 ?_
      rw [show (2 * 10 ^ 55 * Tc) * (5184 * 10 ^ 72 * N) = (2 * 5184 * 10 ^ 127) * (Tc * N) by ring,
          show Tc * (5184 * 10 ^ 128 * N) = (5184 * 10 ^ 128) * (Tc * N) by ring]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hTcpos.le hNpos.le)
      norm_num
    calc (1 / (5184 * 10 ^ 128)) * ((T₀ + Tc) / N)
        ≤ (1 / (5184 * 10 ^ 72)) * (Tc / N) := hkey
      _ ≤ A + Bv := hband'

end Squarefree
