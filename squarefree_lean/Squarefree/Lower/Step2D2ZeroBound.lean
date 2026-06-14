import Squarefree.Lower.Step2D2ZeroAux
import Squarefree.Lower.DefectDeriv4

/-!
# §5 Step-2 φ″-zero count — the `f`-free Wronskian `W₂` is sign-definite (`< 0`)

This module turns the algebraic identities of `Step2D2ZeroAux` into the analytic fact needed by the
ratio-monotonicity step: on the §5 band, the smooth `W₂` numerator `W2num_s` is bounded away from `0`
(`w2_smooth_upper`, mirror of `Ns_chi_lower`) and the finite-difference correction is negligible
(`w2_correction_abstract`, mirror of `chi_correction_abstract` with `ε₁..ε₄`).  Because `W₂` scales
like `B⁷` (no `R³` cushion, unlike `χ''`), the smoothness threshold is `10¹¹⁰·ℓ₁ ≤ R` instead of
`10⁷⁸·ℓ₁ ≤ R` — still satisfied by the actual §5 `ℓ₁` (`≍ R·X^{−c}`).
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

/-- **The smooth `W₂` numerator is `≤ −B⁷/10⁴²`** (mirror of `Ns_chi_lower`).  Via `smooth_W2_eq`,
`W2num_s = −3 d̃⁷(a+d̃)³ P₈ / (16 r⁷ (a+2d̃)¹¹)`, whose magnitude is `≥ B⁷/10⁴²` on the §5 window. -/
lemma w2_smooth_upper {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1 / 72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    8 * dtilde P.X r a ^ 4 * deriv (fun u => dtilde P.X u a) r
          * iteratedDeriv 2 (fun u => dtilde P.X u a) r * iteratedDeriv 4 (fun u => dtilde P.X u a) r
        - 8 * dtilde P.X r a ^ 4 * deriv (fun u => dtilde P.X u a) r
            * iteratedDeriv 3 (fun u => dtilde P.X u a) r ^ 2
        + 16 * dtilde P.X r a ^ 4 * iteratedDeriv 2 (fun u => dtilde P.X u a) r ^ 2
            * iteratedDeriv 3 (fun u => dtilde P.X u a) r
        + 24 * dtilde P.X r a ^ 3 * deriv (fun u => dtilde P.X u a) r ^ 3
            * iteratedDeriv 4 (fun u => dtilde P.X u a) r
        - 8 * dtilde P.X r a ^ 3 * deriv (fun u => dtilde P.X u a) r ^ 2
            * iteratedDeriv 2 (fun u => dtilde P.X u a) r * iteratedDeriv 3 (fun u => dtilde P.X u a) r
        - 120 * dtilde P.X r a ^ 3 * deriv (fun u => dtilde P.X u a) r
            * iteratedDeriv 2 (fun u => dtilde P.X u a) r ^ 3
        - 140 * dtilde P.X r a ^ 2 * deriv (fun u => dtilde P.X u a) r ^ 4
            * iteratedDeriv 3 (fun u => dtilde P.X u a) r
        + 60 * dtilde P.X r a ^ 2 * deriv (fun u => dtilde P.X u a) r ^ 3
            * iteratedDeriv 2 (fun u => dtilde P.X u a) r ^ 2
        + 240 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r ^ 5
            * iteratedDeriv 2 (fun u => dtilde P.X u a) r
        - 120 * deriv (fun u => dtilde P.X u a) r ^ 7
      ≤ -(S.B ^ 7 / 10 ^ 42) := by
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by
    unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrne : r ≠ 0 := ne_of_gt hr0
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos P.X_pos ha0 hr0
  have hd1cf := (dtilde_r_hasDerivAt P.X_pos ha0 hr0).deriv
  have hd2cf := dtilde_r_iteratedDeriv2 P.X_pos ha0 hr0
  have hs4cf := dtilde_r_iteratedDeriv3 P.X_pos ha0 hr0
  have hd4cf := dtilde_r_iteratedDeriv4 P.X_pos ha0 hr0
  have had2 : a + 2 * dtilde P.X r a ≠ 0 := ne_of_gt (by linarith [hd_pos, ha0])
  rw [hd1cf, hd2cf, hs4cf, hd4cf, smooth_W2_eq a (dtilde P.X r a) r hrne had2]
  set d := dtilde P.X r a with hd_def
  have hAD10 : S.A ≤ S.D / 10 := by linarith
  have hda : 0 < d + a := by linarith
  have ha2d : 0 < a + 2 * d := by linarith
  set P8 := 35 * a ^ 8 + 552 * a ^ 7 * d + 4014 * a ^ 6 * d ^ 2 + 16847 * a ^ 5 * d ^ 3
      + 44170 * a ^ 4 * d ^ 4 + 74048 * a ^ 3 * d ^ 5 + 77708 * a ^ 2 * d ^ 6 + 46840 * a * d ^ 7
      + 12480 * d ^ 8 with hP8_def
  have h7 : (S.D / 10) ^ 7 ≤ d ^ 7 := pow_le_pow_left₀ (by positivity) hd_lo 7
  have h3 : (S.D / 10) ^ 3 ≤ (a + d) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hP8 : 12480 * (S.D / 10) ^ 8 ≤ P8 := by
    have h8 : (S.D / 10) ^ 8 ≤ d ^ 8 := pow_le_pow_left₀ (by positivity) hd_lo 8
    rw [hP8_def]
    nlinarith [h8, pow_nonneg ha0.le 8, mul_nonneg (pow_nonneg ha0.le 7) hd_pos.le,
      mul_nonneg (pow_nonneg ha0.le 6) (pow_nonneg hd_pos.le 2),
      mul_nonneg (pow_nonneg ha0.le 5) (pow_nonneg hd_pos.le 3),
      mul_nonneg (pow_nonneg ha0.le 4) (pow_nonneg hd_pos.le 4),
      mul_nonneg (pow_nonneg ha0.le 3) (pow_nonneg hd_pos.le 5),
      mul_nonneg (pow_nonneg ha0.le 2) (pow_nonneg hd_pos.le 6),
      mul_nonneg ha0.le (pow_nonneg hd_pos.le 7)]
  have hnum_lo : 12480 * (S.D / 10) ^ 18 ≤ d ^ 7 * (a + d) ^ 3 * P8 := by
    have s1 : (S.D / 10) ^ 7 * (S.D / 10) ^ 3 ≤ d ^ 7 * (a + d) ^ 3 :=
      mul_le_mul h7 h3 (by positivity) (by positivity)
    have s2 : (S.D / 10) ^ 7 * (S.D / 10) ^ 3 * (12480 * (S.D / 10) ^ 8)
        ≤ d ^ 7 * (a + d) ^ 3 * P8 :=
      mul_le_mul s1 hP8 (by positivity) (by positivity)
    calc 12480 * (S.D / 10) ^ 18 = (S.D / 10) ^ 7 * (S.D / 10) ^ 3 * (12480 * (S.D / 10) ^ 8) := by
          ring
      _ ≤ d ^ 7 * (a + d) ^ 3 * P8 := s2
  have ha2d_hi : a + 2 * d ≤ 38 * S.D := by linarith
  have hden_hi : 16 * r ^ 7 * (a + 2 * d) ^ 11 ≤ 16 * (16 * S.R) ^ 7 * (38 * S.D) ^ 11 := by
    have hr7 : r ^ 7 ≤ (16 * S.R) ^ 7 := pow_le_pow_left₀ hr0.le hr_hi 7
    have ha2d11 : (a + 2 * d) ^ 11 ≤ (38 * S.D) ^ 11 := pow_le_pow_left₀ ha2d.le ha2d_hi 11
    have s1 : 16 * r ^ 7 ≤ 16 * (16 * S.R) ^ 7 := by nlinarith [hr7]
    exact mul_le_mul s1 ha2d11 (by positivity) (by positivity)
  -- the smooth value is `−(3 d⁷(a+d)³ P₈ / denom)`; reduce to a magnitude lower bound
  have hsplit : -3 * d ^ 7 * (a + d) ^ 3 * P8 / (16 * r ^ 7 * (a + 2 * d) ^ 11)
      = -(3 * d ^ 7 * (a + d) ^ 3 * P8 / (16 * r ^ 7 * (a + 2 * d) ^ 11)) := by ring
  rw [hsplit, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  -- assemble: `B⁷/10⁴² · (16 r⁷ (a+2d)¹¹) ≤ 3 d⁷(a+d)³ P₈`
  calc S.B ^ 7 / 10 ^ 42 * (16 * r ^ 7 * (a + 2 * d) ^ 11)
      ≤ S.B ^ 7 / 10 ^ 42 * (16 * (16 * S.R) ^ 7 * (38 * S.D) ^ 11) := by
        gcongr
    _ ≤ 3 * d ^ 7 * (a + d) ^ 3 * P8 := by
        rw [Scale.B_eq_D_div_R S]
        have eL : (S.D / S.R) ^ 7 / 10 ^ 42 * (16 * (16 * S.R) ^ 7 * (38 * S.D) ^ 11)
            = 16 ^ 8 * 38 ^ 11 / 10 ^ 42 * S.D ^ 18 := by field_simp
        rw [eL]
        have hcoef : 16 ^ 8 * 38 ^ 11 / 10 ^ 42 * S.D ^ 18 ≤ 3 * (12480 * (S.D / 10) ^ 18) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have : (3 : ℝ) * (12480 * (S.D / 10) ^ 18) * 10 ^ 42 = 37440 * 10 ^ 24 * S.D ^ 18 := by
            ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hDpos.le 18)
        nlinarith [hcoef, hnum_lo]

end Squarefree
