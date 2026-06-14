import Squarefree.Lower.Step4CubicLip
import Squarefree.Lower.Step4P2Capped
import Squarefree.Lower.Step4SqDiffShell
import Squarefree.Lower.Step4Combine
import Squarefree.Lower.Step4P2Hybrid

/-!
# §5 Step-4 `diam` — HYBRID (fibre-local v-box) variant

Hybrid version of the (pruned) Vmax-form `diam2` route: the same corrected shell structure (cubic slope as the
`θ = 1/2`), but with the budget evaluated at a **fibre-local** `v`-box `V ≤ Vmax` wherever the
audit requires it:

* the cubic cross-fibre prefactor drift sits at `V` (`Step4EcubV`, via `cubic_pref_drift_le`
  instantiated at the box `V`);
* the gap/slope-reconstruction drift sits at `V` (first `Step4EremHyb` term);
* the `p₂` `v`-degree-1,2 monomials sit at `V` (via `p2_hybrid_additive_le` / `E0_p2_hyb`);
* the flat-coefficient drift STAYS at `Vmax` (second `Step4EremHyb` term);
* the `p₂` `v`-degree-3,4 monomials STAY at `Vmax` (inside `E0_p2_hyb`).

The in-fibre cubic Lipschitz SLOPE is unchanged (it is the shell's `θ`, needs only
`|v| ≤ Vmax`, derived from `|v| ≤ V ≤ Vmax`).
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000

/-- Cubic cross-fibre prefactor drift at the fibre-local box `V`. -/
noncomputable def Step4EcubV (P : Globals) (S : Scale P) (ℓ₁ ℓ₂ V : ℝ) : ℝ :=
  2 * (77 * (P.G * S.Ω / S.Δ ^ 4)) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * V ^ 3

/-- Hybrid per-endpoint remainder: gap/recon drift at `V`, flat drift capped at `Vmax`,
`p₂` hybrid (degrees 1,2 at `V`; degrees 3,4 at `Vmax`). -/
noncomputable def Step4EremHyb (P : Globals) (S : Scale P) (a ℓ₁ ℓ₂ gap V : ℝ) : ℝ :=
  77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap * (ℓ₁ * V) ^ 2
    + 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * Vmax P S) ^ 2
    + E0_p2_hyb P S ℓ₁ ℓ₂ V

theorem Step4EcubV_nonneg {ℓ₁ ℓ₂ V : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hV0 : 0 ≤ V) :
    0 ≤ Step4EcubV P S ℓ₁ ℓ₂ V := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  unfold Step4EcubV
  exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) h2ℓ))
    (by positivity)

theorem Step4EremHyb_nonneg {a ℓ₁ ℓ₂ gap V : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hgap0 : 0 ≤ gap) (hV0 : 0 ≤ V) :
    0 ≤ Step4EremHyb P S a ℓ₁ ℓ₂ gap V := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hCref_nn : (0:ℝ) ≤ Cref P S ℓ₁ ℓ₂ := (Cref_pos hℓ1pos hℓ12).le
  have t1 : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap
      * (ℓ₁ * V) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) h21)) hgap0) (sq_nonneg _)
  have t2 : (0:ℝ) ≤ 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
      * (ℓ₁ * Vmax P S) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hCref_nn (sq_nonneg _))) (sq_nonneg _)
  have t3 : (0:ℝ) ≤ E0_p2_hyb P S ℓ₁ ℓ₂ V := E0_p2_hyb_nonneg hℓ1 hℓ12 hV0
  unfold Step4EremHyb
  linarith

/-- **Prefactor magnitude** `|(Xa/d⁵)(−4+10a/d)| ≤ 77·G·Ω/Δ⁴`. -/
private theorem pref_abs_le_hyb {a d : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by
  have hGpos : 0 < P.G := P.G_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  obtain ⟨had0, hadhi⟩ := bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hD5 : S.D ^ 5 = P.X * S.Δ ^ 5 / P.G := by
    unfold Scale.D; rw [P.X_eq_G_mul_H_pow_five]; field_simp
  have hQle : Q ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
    have hd5ge : S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5 ≤ d ^ 5 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hdD 5
    calc Q = P.X * a / d ^ 5 := hQdef
      _ ≤ P.X * a / (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by gcongr
      _ = a * P.G / (S.Δ ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by rw [hD5]; field_simp
      _ ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right haA (by positivity : (0:ℝ) ≤ P.G * S.Δ ^ 4),
            hΔpos, hΩpos, hGpos, mul_pos (mul_pos hGpos (pow_pos hΔpos 5)) hΩpos]
  rw [abs_mul, abs_of_pos hQpos]
  calc Q * |(-4 + 10 * a / d)|
      ≤ Q * 4 := mul_le_mul_of_nonneg_left hbr_hi hQpos.le
    _ ≤ (12 * P.G * S.Ω / S.Δ ^ 4) * 4 := mul_le_mul_of_nonneg_right hQle (by norm_num)
    _ = 48 * (P.G * S.Ω / S.Δ ^ 4) := by ring
    _ ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by
        have hnn : (0:ℝ) ≤ P.G * S.Ω / S.Δ ^ 4 := by positivity
        linarith

/-- **§5 Step-4 perturbed-quadratic shell data — HYBRID box** (audit-corrected).  Same statement
as the historical Vmax-form perturbation bound, but with both fibre points in the fibre-local box `|·| ≤ V ≤ Vmax`:
the additive budget becomes `Step4EcubV(V) + 2·Step4EremHyb(V)` — cubic prefactor drift,
recon drift, and `p₂` degrees 1,2 at `V`; flat drift and `p₂` degrees 3,4 at `Vmax`.  The cubic
SLOPE part `(1/2)·Ĉ·|v²−v'²|` is unchanged. -/
theorem Sigma_closed_perturb_hyb
    {a v v' d d' b₀ b₀' gap V : ℝ} {ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (had : a ≤ d) (had' : a ≤ d')
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hv : |v| ≤ V) (hv' : |v'| ≤ V) (hVcap : V ≤ Vmax P S) (hV0 : 0 ≤ V)
    (hsign : 0 ≤ v * v')
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd'D : S.D * (1 - 1/10 ^ 9) ≤ d')
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hbgap : |b₀ - b1Model P.X a d| ≤ gap) (hbgap' : |b₀' - b1Model P.X a d'| ≤ gap)
    (hgap0 : 0 ≤ gap)
    (hb0box : |b₀| ≤ 3000000000000 * S.B) (hb0box' : |b₀'| ≤ 3000000000000 * S.B) :
    |(Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2)
        - (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2)|
      ≤ (1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * |v ^ 2 - v' ^ 2|
        + (Step4EcubV P S ℓ₁ ℓ₂ V + 2 * Step4EremHyb P S a ℓ₁ ℓ₂ gap V) := by
  -- positivity scaffolding
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hd'_pos : 0 < d' := S.D_pos_of_eps hd'D
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  have h21 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have h3ℓnn : (0:ℝ) ≤ 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hℓ1R.le) hℓ2R.le) h21.le
  have hPmaj_nn : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by positivity
  have hCref_nn : (0:ℝ) ≤ Cref P S ℓ₁ ℓ₂ := (Cref_pos hℓ1R hℓ12).le
  have hCAnn : (0:ℝ) ≤ Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 := mul_nonneg hCref_nn (sq_nonneg _)
  have hdriftcoef_nn : (0:ℝ) ≤ 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hCAnn
  -- global-cap consequences of the fibre-local box
  have hv_max : |v| ≤ Vmax P S := hv.trans hVcap
  have hv'_max : |v'| ≤ Vmax P S := hv'.trans hVcap
  -- box-square bounds: LOCAL box `V` (for the recon drift) …
  have hvL : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by simpa only [Vmax] using hv_max
  have hv'L : |v'| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by simpa only [Vmax] using hv'_max
  have hv2 : v ^ 2 ≤ V ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg v) hv 2
  have hv'2 : v' ^ 2 ≤ V ^ 2 := by
    rw [← sq_abs v']; exact pow_le_pow_left₀ (abs_nonneg v') hv' 2
  have hsqle : (ℓ₁ * v) ^ 2 ≤ (ℓ₁ * V) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_left hv2 (sq_nonneg ℓ₁)
  have hsqle' : (ℓ₁ * v') ^ 2 ≤ (ℓ₁ * V) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_left hv'2 (sq_nonneg ℓ₁)
  -- … and GLOBAL cap `Vmax` (for the flat drift)
  have hv2_max : v ^ 2 ≤ (Vmax P S) ^ 2 := by
    rw [← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg v) hv_max 2
  have hv'2_max : v' ^ 2 ≤ (Vmax P S) ^ 2 := by
    rw [← sq_abs v']; exact pow_le_pow_left₀ (abs_nonneg v') hv'_max 2
  have hsqle_max : (ℓ₁ * v) ^ 2 ≤ (ℓ₁ * Vmax P S) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_left hv2_max (sq_nonneg ℓ₁)
  have hsqle'_max : (ℓ₁ * v') ^ 2 ≤ (ℓ₁ * Vmax P S) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_left hv'2_max (sq_nonneg ℓ₁)
  -- prefactor magnitudes for both fibres
  have hpref_d : |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) :=
    pref_abs_le_hyb ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hpref_d' : |(P.X * a / d' ^ 5) * (-4 + 10 * a / d')| ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) :=
    pref_abs_le_hyb ha0 ha_hi hd'D h1 hG1 hU1 hΔ1 hΩU hUbig
  -- (A) cubic in-fibre Lipschitz slope (the `θ` — needs only the GLOBAL cap, unchanged)
  have hA : |(P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (v ^ 3 - v' ^ 3))|
      ≤ (1 / 2 : ℝ) * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * |v ^ 2 - v' ^ 2| :=
    cubic_lipschitz_le ha0 ha_hi hℓ1 hℓ12 hℓ12' hvL hv'L hsign hdD h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
  -- (B) cubic cross-fibre prefactor drift at the LOCAL box `V` (additive Step4EcubV)
  have hB : |(P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3)
        - (P.X * a / d' ^ 5) * (-4 + 10 * a / d') * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3)|
      ≤ Step4EcubV P S ℓ₁ ℓ₂ V := by
    have h := cubic_pref_drift_le
      (pref := (P.X * a / d ^ 5) * (-4 + 10 * a / d))
      (pref' := (P.X * a / d' ^ 5) * (-4 + 10 * a / d'))
      (Pmaj := 77 * (P.G * S.Ω / S.Δ ^ 4)) (v' := v') (V := V)
      hpref_d hpref_d' hℓ1 hℓ12 hv'
    rw [Step4EcubV]; exact h
  -- per-endpoint reconstruction drift bounds, at the LOCAL box `V`
  have hrecon : ∀ {b v d : ℝ}, |b - b1Model P.X a d| ≤ gap → (ℓ₁ * v) ^ 2 ≤ (ℓ₁ * V) ^ 2 →
      |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) →
      |(Cprime P.X a b d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2|
        ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap * (ℓ₁ * V) ^ 2 := by
    intro b v d hbg hsq hpr
    have hRCeq2 : Cprime P.X a b d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂
        = ((P.X * a / d ^ 5) * (-4 + 10 * a / d)) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
            * (b - b1Model P.X a d) := by
      unfold Cprime; ring
    rw [hRCeq2, abs_mul, abs_mul, abs_mul, abs_of_nonneg h3ℓnn,
      abs_of_nonneg (sq_nonneg (ℓ₁ * v))]
    have step1 : |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
          * |b - b1Model P.X a d|
        ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpr h3ℓnn) hbg (abs_nonneg _)
        (mul_nonneg hPmaj_nn h3ℓnn)
    calc |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
            * |b - b1Model P.X a d| * (ℓ₁ * v) ^ 2
        ≤ (77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap) * (ℓ₁ * v) ^ 2 :=
          mul_le_mul_of_nonneg_right step1 (sq_nonneg _)
      _ ≤ (77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap) * (ℓ₁ * V) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg (mul_nonneg hPmaj_nn h3ℓnn) hgap0)
      _ = 77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap * (ℓ₁ * V) ^ 2 := by
          ring
  have hrx := hrecon hbgap hsqle hpref_d
  have hry := hrecon hbgap' hsqle' hpref_d'
  -- per-endpoint flat-coefficient drift bounds (UNCHANGED: still at the GLOBAL cap `Vmax`)
  have hdrift : ∀ {v d : ℝ}, a ≤ d → 0 < d → S.D * (1 - 1/10 ^ 9) ≤ d →
      (ℓ₁ * v) ^ 2 ≤ (ℓ₁ * Vmax P S) ^ 2 →
      |(Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2|
        ≤ 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * Vmax P S) ^ 2 := by
    intro v d hadx hdx hdDx hsq
    rw [abs_mul, abs_of_nonneg (sq_nonneg (ℓ₁ * v))]
    have hstepd : |Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2|
        ≤ 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) :=
      Cref_drift_le_winD ha0 hdx hadx hdDx hℓ1R hℓ12
    calc |Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2| * (ℓ₁ * v) ^ 2
        ≤ (20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)) * (ℓ₁ * v) ^ 2 :=
          mul_le_mul_of_nonneg_right hstepd (sq_nonneg _)
      _ ≤ (20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)) * (ℓ₁ * Vmax P S) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hdriftcoef_nn
  have hdx := hdrift had hd_pos hdD hsqle_max
  have hdy := hdrift had' hd'_pos hd'D hsqle'_max
  -- per-endpoint HYBRID p₂ bounds (degrees 1,2 at `V`; degrees 3,4 at `Vmax`)
  have hp2x : |(P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))|
      ≤ E0_p2_hyb P S ℓ₁ ℓ₂ V :=
    p2_hybrid_additive_le ha0 ha_hi hℓ1 hℓ12 hb0box hv hVcap hV0 hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hp2y : |(P.X * a / d' ^ 5) * ((-4 + 10 * a / d') * (Ptwo b₀' v' ℓ₁ ℓ₂ / d'))|
      ≤ E0_p2_hyb P S ℓ₁ ℓ₂ V :=
    p2_hybrid_additive_le ha0 ha_hi hℓ1 hℓ12 hb0box' hv' hVcap hV0 hd'D h1 hG1 hU1 hΔ1 hΩU hUbig
  -- the exact 5-piece decomposition of ex − ey
  have hdiffx : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
      = (Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2
        + (Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
        + (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)
        + (P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d)) := by
    unfold Sigma_closed Pone Cprime; ring
  have hdiffy : Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂
        - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2
      = (Cprime P.X a b₀' d' ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d') d' ℓ₁ ℓ₂) * (ℓ₁ * v') ^ 2
        + (Cprime P.X a (b1Model P.X a d') d' ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v') ^ 2
        + (P.X * a / d' ^ 5) * (-4 + 10 * a / d') * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3)
        + (P.X * a / d' ^ 5) * ((-4 + 10 * a / d') * (Ptwo b₀' v' ℓ₁ ℓ₂ / d')) := by
    unfold Sigma_closed Pone Cprime; ring
  have hid :
      (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2)
        - (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2)
      = ((P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (v ^ 3 - v' ^ 3)))
        + ((P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3)
            - (P.X * a / d' ^ 5) * (-4 + 10 * a / d') * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v' ^ 3))
        + ((Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2
            - (Cprime P.X a b₀' d' ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d') d' ℓ₁ ℓ₂)
              * (ℓ₁ * v') ^ 2)
        + ((Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
            - (Cprime P.X a (b1Model P.X a d') d' ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
              * (ℓ₁ * v') ^ 2)
        + ((P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))
            - (P.X * a / d' ^ 5) * ((-4 + 10 * a / d') * (Ptwo b₀' v' ℓ₁ ℓ₂ / d'))) := by
    rw [hdiffx, hdiffy]; ring
  -- assemble via the triangle inequality on the 5-piece sum
  rw [hid]
  refine le_trans
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) ?_
  have hC : |(Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2
        - (Cprime P.X a b₀' d' ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d') d' ℓ₁ ℓ₂) * (ℓ₁ * v') ^ 2|
      ≤ 2 * (77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap * (ℓ₁ * V) ^ 2) := by
    have := (abs_sub _ _).trans (add_le_add hrx hry); linarith
  have hD : |(Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
        - (Cprime P.X a (b1Model P.X a d') d' ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
          * (ℓ₁ * v') ^ 2|
      ≤ 2 * (20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * Vmax P S) ^ 2) := by
    have := (abs_sub _ _).trans (add_le_add hdx hdy); linarith
  have hE : |(P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))
        - (P.X * a / d' ^ 5) * ((-4 + 10 * a / d') * (Ptwo b₀' v' ℓ₁ ℓ₂ / d'))|
      ≤ 2 * E0_p2_hyb P S ℓ₁ ℓ₂ V := by
    have := (abs_sub _ _).trans (add_le_add hp2x hp2y); linarith
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add hA hB) hC) hD) hE)
    (le_of_eq ?_)
  rw [Step4EcubV, Step4EremHyb]; ring

/-- **§5 Step-4 two-point square-difference diameter — HYBRID box** (audit-corrected).  Same as
the historical Vmax-form `diam2`, but with both fibre points in the fibre-local box `|·| ≤ V ≤ Vmax` and the
hybrid budget `Step4EcubV(V) + 2·Step4EremHyb(V)`:

  `|v² − v'²| ≤ (4·err + 2·(Step4EcubV + 2·Step4EremHyb)) / Ĉ`,

with `Ĉ = Cref·(A/a)²·ℓ₁² > 0`. -/
theorem step4_sqdiff_diam2_hyb
    {a v v' d d' b₀ b₀' err gap V : ℝ} {ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (had : a ≤ d) (had' : a ≤ d')
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hv : |v| ≤ V) (hv' : |v'| ≤ V) (hVcap : V ≤ Vmax P S) (hV0 : 0 ≤ V)
    (hsign : 0 ≤ v * v')
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd'D : S.D * (1 - 1/10 ^ 9) ≤ d')
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hbgap : |b₀ - b1Model P.X a d| ≤ gap) (hbgap' : |b₀' - b1Model P.X a d'| ≤ gap)
    (hgap0 : 0 ≤ gap)
    (hb0box : |b₀| ≤ 3000000000000 * S.B) (hb0box' : |b₀'| ≤ 3000000000000 * S.B)
    (hx_ni : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)| ≤ err)
    (hy_ni : |Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - (s : ℝ)| ≤ err) :
    |v ^ 2 - v' ^ 2|
      ≤ (4 * err + 2 * (Step4EcubV P S ℓ₁ ℓ₂ V + 2 * Step4EremHyb P S a ℓ₁ ℓ₂ gap V))
          / (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) := by
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; exact mul_pos hΔpos hΩpos
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hC : 0 < Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2 :=
    mul_pos (mul_pos (Cref_pos hℓ1R hℓ12) (pow_pos (div_pos hApos ha0) 2)) (pow_pos hℓ1R 2)
  have hpert := Sigma_closed_perturb_hyb ha0 ha_hi had had' hℓ1 hℓ12 hℓ12' hv hv' hVcap hV0
    hsign hdD hd'D h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hbgap hbgap' hgap0 hb0box hb0box'
  exact abs_sq_sub_le_of_perturbed_quadratic_shell
    (C := Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) (theta := (1 / 2 : ℝ)) (eta := err)
    (E0 := Step4EcubV P S ℓ₁ ℓ₂ V + 2 * Step4EremHyb P S a ℓ₁ ℓ₂ gap V)
    (x := v) (y := v') (center := (s : ℝ))
    (ex := Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2)
    (ey := Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2)
    hC le_rfl
    (by
      have e : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
          + (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2)
          = Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ := by ring
      rw [e]; exact hx_ni)
    (by
      have e : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2
          + (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2)
          = Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ := by ring
      rw [e]; exact hy_ni)
    hpert

end Squarefree
