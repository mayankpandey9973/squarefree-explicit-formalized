import Squarefree.Structure.PhaseCurv
import Squarefree.Structure.NearCurveBridge
import Squarefree.Geometry.NearCurve
import Mathlib

/-!
# §6 regime assembly: helper sub-lemmas for Prop 6.1

Factored sub-lemmas feeding `prop_6_1` (`Upper/Regime.lean`).  See `../explicit_writeup.md`
lines 1230–1308 and `math_audit.md` §6.

The pipeline (per `a ∼ A`, then summed over `r ≍ R`):
* `prop6_curv_regime`  — the curvature regime `16a² ≤ 4√(Xa³/r)` on `[A/2,5A/2]`, from `10A≤D`;
* `ftil_dtilde_window` — `D/2 ≤ d̃ₐ(r) ≤ 3D` for `r ∈ [R/72,16R]` (inverting `R_a`);
* `ftil_dtilde_close`  — `|d − d̃ₐ(r)| ≤ 12096·(Δ/G)(Δ³/A³)` (MVT on `R_a`);
* `ftil_near_integer`  — `distInt(f̃ₐ(r)) ≤ K₀·δ₀` (via `nearcurve_membership`);
* `prop6_count_per_r`  — per-`r` count over `a ∼ A` (via `nearCurve_count`);
* `prop6_rpow`/assembly — the 4 rpow identities and the `+1`/log absorption.
-/

open Classical Finset
open Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 1000000

/-- `R_a` is antitone on the positive reals (for `0 < X`, `0 < a`): the closed form
`X a³/(d²(d+a)²)` has a decreasing denominator. -/
private theorem Rfun_antitone {X a : ℝ} (hX : 0 < X) (ha : 0 < a) {d₁ d₂ : ℝ}
    (hd₁ : 0 < d₁) (hle : d₁ ≤ d₂) : Rfun X a d₂ ≤ Rfun X a d₁ := by
  have hd₂ : 0 < d₂ := lt_of_lt_of_le hd₁ hle
  rw [Rfun_factor' X a d₁ (ne_of_gt hd₁) (by positivity),
      Rfun_factor' X a d₂ (ne_of_gt hd₂) (by positivity)]
  have hnum : 0 ≤ X * a ^ 3 := by positivity
  apply div_le_div_of_nonneg_left hnum (by positivity)
  apply mul_le_mul (pow_le_pow_left₀ hd₁.le hle 2) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
    (by positivity) (by positivity)

/-- **Curvature regime** (writeup line 1255 hypothesis).  For `r ≤ 16R` and `a ∈ [A/2,5A/2]`,
the regime hypothesis `16a² ≤ 4√(Xa³/r)` of `ftil_curv_bound` holds, using `10A ≤ D`
(equivalently `640A⁴ ≤ D⁴`). -/
theorem prop6_curv_regime {P : Globals} {S : Scale P} {r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hr : r ≤ 16 * S.R) :
    ∀ a ∈ Set.Icc (S.A / 2) (5 * S.A / 2), 16 * a ^ 2 ≤ 4 * Real.sqrt (P.X * a ^ 3 / r) := by
  intro a ha
  obtain ⟨haL, haU⟩ := ha
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hDeq : S.D = P.H * S.Δ := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hDpos : 0 < S.D := by rw [hDeq]; positivity
  have hapos : 0 < a := by linarith
  -- reduce `16a² ≤ 4√(Xa³/r)` to `(4a²)² ≤ Xa³/r`, i.e. `16 a r ≤ X`
  have hkey : 16 * a * r ≤ P.X := by
    -- a ≤ 5A/2, r ≤ 16R, X = G H⁵, R = H G Ω³/Δ, A = ΔΩ, D = HΔ.
    have hRval : 16 * S.R = 16 * (P.H * P.G * S.Ω ^ 3 / S.Δ) := by rw [Scale.R]
    have hXval : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
    -- 640 A⁴ ≤ D⁴  ⟸  10A ≤ D
    have h640 : 640 * S.A ^ 4 ≤ S.D ^ 4 := by
      have h10 : (10 * S.A) ^ 4 ≤ S.D ^ 4 := by
        apply pow_le_pow_left₀ (by positivity) hAD
      have hexp : (10 * S.A) ^ 4 = 10000 * S.A ^ 4 := by ring
      rw [hexp] at h10
      nlinarith [h10, pow_pos hApos 4]
    -- 640 Δ⁴Ω⁴ ≤ H⁴Δ⁴  ⟹  640 Ω⁴ ≤ H⁴
    have hΩ4H4 : 640 * S.Ω ^ 4 ≤ P.H ^ 4 := by
      have h1 : 640 * (S.Δ * S.Ω) ^ 4 ≤ (P.H * S.Δ) ^ 4 := by rw [← hAeq, ← hDeq]; exact h640
      have hΔ4 : 0 < S.Δ ^ 4 := by positivity
      nlinarith [h1, hΔ4]
    -- 16 a r ≤ 16·(5A/2)·(16R) = 640 H G Ω⁴ ≤ G H⁵ = X
    have hr16 : r ≤ 16 * (P.H * P.G * S.Ω ^ 3 / S.Δ) := by rw [← hRval]; exact hr
    have hstep : 16 * a * r ≤ 16 * (5 * S.A / 2) * (16 * (P.H * P.G * S.Ω ^ 3 / S.Δ)) := by
      apply mul_le_mul (by nlinarith [haU]) hr16 hr0.le (by positivity)
    have hsimp : 16 * (5 * S.A / 2) * (16 * (P.H * P.G * S.Ω ^ 3 / S.Δ))
        = 640 * P.H * P.G * S.Ω ^ 4 := by
      rw [hAeq]; field_simp; ring
    rw [hsimp] at hstep
    have hfin : 640 * P.H * P.G * S.Ω ^ 4 ≤ P.X := by
      rw [hXval]
      have : 640 * P.H * P.G * S.Ω ^ 4 = P.G * P.H * (640 * S.Ω ^ 4) := by ring
      rw [this]
      have hGH : 0 < P.G * P.H := by positivity
      calc P.G * P.H * (640 * S.Ω ^ 4) ≤ P.G * P.H * P.H ^ 4 :=
            mul_le_mul_of_nonneg_left hΩ4H4 hGH.le
        _ = P.G * P.H ^ 5 := by ring
    linarith [hstep, hfin]
  -- now `16a² ≤ 4√(Xa³/r)` from `16 a r ≤ X`
  have hrad : 0 ≤ P.X * a ^ 3 / r := by positivity
  have hsq : (4 * a ^ 2) ^ 2 ≤ P.X * a ^ 3 / r := by
    rw [le_div_iff₀ hr0]
    -- (4a²)²·r = 16 a⁴ r = a³·(16 a r) ≤ a³·X = X a³
    have : (4 * a ^ 2) ^ 2 * r = a ^ 3 * (16 * a * r) := by ring
    rw [this]
    calc a ^ 3 * (16 * a * r) ≤ a ^ 3 * P.X := by
          apply mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = P.X * a ^ 3 := by ring
  -- 4a² ≤ √(Xa³/r) ⟹ 16a² ≤ 4√(...)
  have h4a2 : 4 * a ^ 2 ≤ Real.sqrt (P.X * a ^ 3 / r) := by
    rw [show (4 : ℝ) * a ^ 2 = Real.sqrt ((4 * a ^ 2) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq
  linarith [h4a2]

/-- **Inverse window** (writeup ~1241).  For `a ∈ [A,2A]`, a real `d ∈ [D,2D]` with
`|R_a(d) − r| ≤ 14H/D`, under `10A ≤ D` and the floor `500 ≤ GHΩ³`, the curve point
`d̃ₐ(r)` lies in the widened dyadic band `[D/2, 3D]`. -/
theorem ftil_dtilde_window {P : Globals} {S : Scale P} {a : ℤ} {r : ℝ} {d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hΩfloor : (500 : ℝ) ≤ P.G * P.H * S.Ω ^ 3)
    (ha0 : 0 < a) (haA : S.A ≤ (a : ℝ)) (haA2 : (a : ℝ) ≤ 2 * S.A) (hr0 : 0 < r)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hrd : |Rfun P.X (a : ℝ) d - r| ≤ 14 * P.H / S.D) :
    S.D / 2 ≤ dtilde P.X r (a : ℝ) ∧ dtilde P.X r (a : ℝ) ≤ 3 * S.D := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hDeq : S.D = P.H * S.Δ := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hDpos : 0 < S.D := by rw [hDeq]; positivity
  -- key bridge: X·a³ between R·D⁴ and 8·R·D⁴ (using A ≤ a ≤ 2A and X·A³ = R·D⁴)
  have hXA3 : P.X * S.A ^ 3 = S.R * S.D ^ 4 := by
    rw [Scale.R, hAeq, hDeq, P.X_eq_G_mul_H_pow_five]; field_simp
  have hRpos : 0 < S.R := by
    have : 0 < S.R * S.D ^ 4 := by rw [← hXA3]; positivity
    nlinarith [this, pow_pos hDpos 4]
  set Y : ℝ := P.X * (a : ℝ) ^ 3 with hYdef
  have hYpos : 0 < Y := by rw [hYdef]; positivity
  have hYlo : S.R * S.D ^ 4 ≤ Y := by
    rw [hYdef, ← hXA3]
    apply mul_le_mul_of_nonneg_left _ hX.le
    apply pow_le_pow_left₀ hApos.le haA
  have hYhi : Y ≤ 8 * (S.R * S.D ^ 4) := by
    rw [hYdef, ← hXA3]
    have : P.X * (a : ℝ) ^ 3 ≤ P.X * (2 * S.A) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hX.le
      apply pow_le_pow_left₀ haR.le haA2
    calc P.X * (a:ℝ) ^ 3 ≤ P.X * (2 * S.A) ^ 3 := this
      _ = 8 * (P.X * S.A ^ 3) := by ring
  -- a ≤ 2D/5
  have ha2D5 : (a : ℝ) ≤ 2 * S.D / 5 := by
    have : 5 * (a : ℝ) ≤ S.D := by nlinarith [haA2, hAD, hApos]
    linarith
  -- 14H/D = 14/Δ ≤ (1/35)·R   (from GHΩ³ ≥ 500)
  have h14 : 14 * P.H / S.D ≤ (1 / 35 : ℝ) * S.R := by
    have hfloor490 : (490 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 := by linarith [hΩfloor]
    have hlhs : 14 * P.H / S.D = 14 / S.Δ := by rw [hDeq]; field_simp
    have hrhs : (1 / 35 : ℝ) * S.R = P.H * P.G * S.Ω ^ 3 / (35 * S.Δ) := by
      rw [Scale.R]; ring
    rw [hlhs, hrhs, div_le_div_iff₀ hΔ (by positivity)]
    nlinarith [hfloor490, hΔ]
  -- abbreviate the inverse point
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdtdef
  have hdtpos : 0 < dt := dtilde_pos hX haR hr0
  have hRdt : Rfun P.X (a : ℝ) dt = r := dtilde_spec hX haR hr0
  -- value bounds: R_a(d) for d at the four band points, via Rfun_factor'
  have hRval : ∀ s : ℝ, 0 < s → Rfun P.X (a : ℝ) s = Y / (s ^ 2 * (s + (a:ℝ)) ^ 2) := by
    intro s hs; rw [Rfun_factor' P.X (a:ℝ) s (ne_of_gt hs) (by positivity), hYdef]
  -- R_a(3D) ≤ r  ⟹  dt ≤ 3D
  refine ⟨?_, ?_⟩
  · -- dt ≥ D/2 : need r ≤ R_a(D/2)
    -- r ≤ R_a(d) + 14H/D ≤ R_a(D) + 14H/D ≤ R_a(D/2)
    have hrub : r ≤ Rfun P.X (a:ℝ) d + 14 * P.H / S.D := by
      have := abs_le.mp hrd; linarith [this.1, this.2]
    have hRd_D : Rfun P.X (a:ℝ) d ≤ Rfun P.X (a:ℝ) S.D :=
      Rfun_antitone hX haR hDpos hdD
    -- R_a(D) ≤ Y/D⁴ ≤ 8R
    have hRD_ub : Rfun P.X (a:ℝ) S.D ≤ Y / S.D ^ 4 := by
      rw [hRval S.D hDpos]
      apply div_le_div_of_nonneg_left hYpos.le (by positivity)
      nlinarith [sq_nonneg (S.D + (a:ℝ)), hDpos, haR, mul_pos hDpos haR]
    have hYD4_8R : Y / S.D ^ 4 ≤ 8 * S.R := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hYhi]
    -- R_a(D/2) ≥ Y·400/(81 D⁴) ≥ 400/81 · R > 4 R
    have hRDhalf_lb : (400 / 81 : ℝ) * (Y / S.D ^ 4) ≤ Rfun P.X (a:ℝ) (S.D / 2) := by
      rw [hRval (S.D/2) (by positivity), le_div_iff₀ (by positivity)]
      -- (400/81)·(Y/D⁴)·((D/2)²(D/2+a)²) ≤ Y
      have hbound : (S.D/2) ^ 2 * (S.D/2 + (a:ℝ)) ^ 2 ≤ (81 / 400 : ℝ) * S.D ^ 4 := by
        have hda : S.D/2 + (a:ℝ) ≤ (9/10 : ℝ) * S.D := by linarith [ha2D5]
        have hda0 : 0 ≤ S.D/2 + (a:ℝ) := by positivity
        have hsq : (S.D/2 + (a:ℝ)) ^ 2 ≤ ((9/10 : ℝ) * S.D) ^ 2 := by
          apply pow_le_pow_left₀ hda0 hda
        calc (S.D/2) ^ 2 * (S.D/2 + (a:ℝ)) ^ 2
            ≤ (S.D/2) ^ 2 * ((9/10 : ℝ) * S.D) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (81 / 400 : ℝ) * S.D ^ 4 := by ring
      have hYD4 : Y / S.D ^ 4 * S.D ^ 4 = Y := by field_simp
      have hkey : (400 / 81 : ℝ) * (Y / S.D ^ 4) * ((S.D/2) ^ 2 * (S.D/2 + (a:ℝ)) ^ 2)
          ≤ (400 / 81 : ℝ) * (Y / S.D ^ 4) * ((81 / 400 : ℝ) * S.D ^ 4) := by
        apply mul_le_mul_of_nonneg_left hbound (by positivity)
      calc (400 / 81 : ℝ) * (Y / S.D ^ 4) * ((S.D/2) ^ 2 * (S.D/2 + (a:ℝ)) ^ 2)
          ≤ (400 / 81 : ℝ) * (Y / S.D ^ 4) * ((81 / 400 : ℝ) * S.D ^ 4) := hkey
        _ = Y / S.D ^ 4 * S.D ^ 4 := by ring
        _ = Y := hYD4
    have hYR : S.R ≤ Y / S.D ^ 4 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hYlo]
    -- chain: r ≤ R_a(D) + 14H/D ≤ Y/D⁴·8 + (1/35)R ≤ ... ≤ R_a(D/2)
    have hchain : r ≤ Rfun P.X (a:ℝ) (S.D / 2) := by
      have e1 : Rfun P.X (a:ℝ) d + 14 * P.H / S.D ≤ Y / S.D ^ 4 + (1/35) * S.R := by
        linarith [hRd_D, hRD_ub, h14]
      have e2 : Y / S.D ^ 4 + (1/35) * S.R ≤ (400/81) * (Y / S.D ^ 4) := by
        have : S.R ≤ Y / S.D ^ 4 := hYR
        nlinarith [this, hYpos, pow_pos hDpos 4, div_pos hYpos (pow_pos hDpos 4)]
      linarith [hrub, e1, e2, hRDhalf_lb]
    -- r = R_a(dt), R_a antitone ⟹ dt ≥ D/2
    by_contra hlt
    push_neg at hlt
    have : Rfun P.X (a:ℝ) (S.D/2) ≤ Rfun P.X (a:ℝ) dt :=
      Rfun_antitone hX haR hdtpos hlt.le
    rw [hRdt] at this; linarith [hchain, this]
  · -- dt ≤ 3D : need R_a(3D) ≤ r
    have hrlb : Rfun P.X (a:ℝ) d - 14 * P.H / S.D ≤ r := by
      have := abs_le.mp hrd; linarith [this.1, this.2]
    have hRd_2D : Rfun P.X (a:ℝ) (2 * S.D) ≤ Rfun P.X (a:ℝ) d :=
      Rfun_antitone hX haR (by linarith [hDpos]) hd2D
    -- R_a(2D) ≥ Y·25/(484 D⁴) ;  R_a(3D) ≤ Y/(81 D⁴)
    have hR2D_lb : (25 / 484 : ℝ) * (Y / S.D ^ 4) ≤ Rfun P.X (a:ℝ) (2 * S.D) := by
      rw [hRval (2 * S.D) (by linarith [hDpos]), le_div_iff₀ (by positivity)]
      have hbound : (2 * S.D) ^ 2 * (2 * S.D + (a:ℝ)) ^ 2 ≤ (484 / 25 : ℝ) * S.D ^ 4 := by
        have hda : 2 * S.D + (a:ℝ) ≤ (11/5 : ℝ) * S.D := by linarith [ha2D5]
        have hda0 : 0 ≤ 2 * S.D + (a:ℝ) := by positivity
        have hsq : (2 * S.D + (a:ℝ)) ^ 2 ≤ ((11/5 : ℝ) * S.D) ^ 2 :=
          pow_le_pow_left₀ hda0 hda 2
        calc (2 * S.D) ^ 2 * (2 * S.D + (a:ℝ)) ^ 2
            ≤ (2 * S.D) ^ 2 * ((11/5 : ℝ) * S.D) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (484 / 25 : ℝ) * S.D ^ 4 := by ring
      have hYD4 : Y / S.D ^ 4 * S.D ^ 4 = Y := by field_simp
      have hkey : (25 / 484 : ℝ) * (Y / S.D ^ 4) * ((2 * S.D) ^ 2 * (2 * S.D + (a:ℝ)) ^ 2)
          ≤ (25 / 484 : ℝ) * (Y / S.D ^ 4) * ((484 / 25 : ℝ) * S.D ^ 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      calc (25 / 484 : ℝ) * (Y / S.D ^ 4) * ((2 * S.D) ^ 2 * (2 * S.D + (a:ℝ)) ^ 2)
          ≤ (25 / 484 : ℝ) * (Y / S.D ^ 4) * ((484 / 25 : ℝ) * S.D ^ 4) := hkey
        _ = Y / S.D ^ 4 * S.D ^ 4 := by ring
        _ = Y := hYD4
    have hR3D_ub : Rfun P.X (a:ℝ) (3 * S.D) ≤ (1 / 81 : ℝ) * (Y / S.D ^ 4) := by
      rw [hRval (3 * S.D) (by linarith [hDpos]), div_le_iff₀ (by positivity)]
      have hbound : (81 : ℝ) * S.D ^ 4 ≤ (3 * S.D) ^ 2 * (3 * S.D + (a:ℝ)) ^ 2 := by
        have hda : (3 : ℝ) * S.D ≤ 3 * S.D + (a:ℝ) := by linarith [haR]
        have hda0 : 0 ≤ (3:ℝ) * S.D := by positivity
        have hsq : ((3:ℝ) * S.D) ^ 2 ≤ (3 * S.D + (a:ℝ)) ^ 2 := pow_le_pow_left₀ hda0 hda 2
        calc (81 : ℝ) * S.D ^ 4 = (3 * S.D) ^ 2 * ((3:ℝ) * S.D) ^ 2 := by ring
          _ ≤ (3 * S.D) ^ 2 * (3 * S.D + (a:ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
      have hYD4 : Y / S.D ^ 4 * S.D ^ 4 = Y := by field_simp
      -- Y ≤ (1/81)*(Y/D⁴)*((3D)²(3D+a)²)
      have hkey : (1 / 81 : ℝ) * (Y / S.D ^ 4) * ((81 : ℝ) * S.D ^ 4)
          ≤ (1 / 81 : ℝ) * (Y / S.D ^ 4) * ((3 * S.D) ^ 2 * (3 * S.D + (a:ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      calc Y = Y / S.D ^ 4 * S.D ^ 4 := hYD4.symm
        _ = (1 / 81 : ℝ) * (Y / S.D ^ 4) * ((81 : ℝ) * S.D ^ 4) := by ring
        _ ≤ (1 / 81 : ℝ) * (Y / S.D ^ 4) * ((3 * S.D) ^ 2 * (3 * S.D + (a:ℝ)) ^ 2) := hkey
    have hYR : S.R ≤ Y / S.D ^ 4 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hYlo]
    -- R_a(3D) ≤ R_a(2D) - 14H/D ≤ R_a(d) - 14H/D ≤ r
    have hgap : Rfun P.X (a:ℝ) (3 * S.D) + 14 * P.H / S.D ≤ Rfun P.X (a:ℝ) (2 * S.D) := by
      have e1 : (1/81 : ℝ) * (Y / S.D ^ 4) + (1/35) * S.R ≤ (25/484) * (Y / S.D ^ 4) := by
        have : S.R ≤ Y / S.D ^ 4 := hYR
        nlinarith [this, hYpos, pow_pos hDpos 4, div_pos hYpos (pow_pos hDpos 4)]
      linarith [hR3D_ub, h14, e1, hR2D_lb]
    have hchain : Rfun P.X (a:ℝ) (3 * S.D) ≤ r := by
      linarith [hgap, hRd_2D, hrlb]
    by_contra hlt
    push_neg at hlt
    have : Rfun P.X (a:ℝ) dt ≤ Rfun P.X (a:ℝ) (3 * S.D) :=
      Rfun_antitone hX haR (by positivity) hlt.le
    rw [hRdt] at this; linarith [hchain, this]

/-- **MVT slope identity** for `R_a` on `[p,q]` (`0 < p < q`): there is an interior point `c`
with `R_a(q) − R_a(p) = R_a'(c)·(q − p)`, where `R_a'(c) = −2 X a³ (2c+a)/(c³(c+a)³)`. -/
private theorem Rfun_mvt {X a p q : ℝ} (hX : 0 < X) (ha : 0 < a) (hp : 0 < p) (hpq : p < q) :
    ∃ c, p < c ∧ c < q ∧
      Rfun X a q - Rfun X a p
        = (-2 * X * a ^ 3 * (2 * c + a) / (c ^ 3 * (c + a) ^ 3)) * (q - p) := by
  have hcont : ContinuousOn (fun t => Rfun X a t) (Set.Icc p q) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hp hs.1
    exact (Rfun_contDiffAt (ne_of_gt hs0) (by positivity)).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ioo p q, HasDerivAt (fun t => Rfun X a t)
      (-2 * X * a ^ 3 * (2 * s + a) / (s ^ 3 * (s + a) ^ 3)) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hp hs.1
    exact Rfun_hasDerivAt_d X a s (ne_of_gt hs0) (by positivity)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => Rfun X a t) _ hpq hcont hderiv
  refine ⟨c, hc.1, hc.2, ?_⟩
  rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hpq))]

/-- **Curve closeness** (writeup ~1241).  For `a ∈ [A,2A]`, real `d ∈ [D,2D]` with
`|R_a(d) − r| ≤ 14H/D`, and the inverse point in the band `[D/2, 3D]`, one has
`|d − d̃ₐ(r)| ≤ 12096·(Δ/G)·(Δ³/A³)` (the `Capx` of `nearcurve_membership`). -/
theorem ftil_dtilde_close {P : Globals} {S : Scale P} {a : ℤ} {r : ℝ} {d : ℝ}
    (hAD : 10 * S.A ≤ S.D)
    (ha0 : 0 < a) (haA : S.A ≤ (a : ℝ)) (haA2 : (a : ℝ) ≤ 2 * S.A) (hr0 : 0 < r)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hrd : |Rfun P.X (a : ℝ) d - r| ≤ 14 * P.H / S.D)
    (hwlo : S.D / 2 ≤ dtilde P.X r (a : ℝ)) (hwhi : dtilde P.X r (a : ℝ) ≤ 3 * S.D) :
    |d - dtilde P.X r (a : ℝ)| ≤ 12096 * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3) := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hDeq : S.D = P.H * S.Δ := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hDpos : 0 < S.D := by rw [hDeq]; positivity
  have hXA3 : P.X * S.A ^ 3 = S.R * S.D ^ 4 := by
    rw [Scale.R, hAeq, hDeq, P.X_eq_G_mul_H_pow_five]; field_simp
  have hRpos : 0 < S.R := by
    have : 0 < S.R * S.D ^ 4 := by rw [← hXA3]; positivity
    nlinarith [this, pow_pos hDpos 4]
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdtdef
  have hdtpos : 0 < dt := dtilde_pos hX haR hr0
  have hRdt : Rfun P.X (a : ℝ) dt = r := dtilde_spec hX haR hr0
  -- a ≤ 2D/5  (so d + a ≤ 4D on the band)
  have ha2D5 : (a : ℝ) ≤ 2 * S.D / 5 := by
    have : 5 * (a : ℝ) ≤ S.D := by nlinarith [haA2, hAD, hApos]
    linarith
  -- target RHS equals 12096 · H / R  (so |R_a(d)-r| / |R_a'| ≤ 12096 H/R)
  have htgt : 12096 * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3) = 12096 * P.H / S.R := by
    rw [Scale.R, hAeq]; field_simp
  -- lower bound on |R_a'(c)| for c ∈ [D/2, 3D]: |R_a'(c)| ≥ R/(864 D)
  have hderiv_lb : ∀ c : ℝ, S.D / 2 ≤ c → c ≤ 3 * S.D →
      S.R / (864 * S.D) ≤ 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3) := by
    intro c hclo hchi
    have hc0 : 0 < c := by linarith [hDpos]
    have hca : 0 < c + (a:ℝ) := by linarith [haR]
    rw [div_le_div_iff₀ (by have := hDpos; positivity) (mul_pos (pow_pos hc0 3) (pow_pos hca 3))]
    -- R·(c³(c+a)³) ≤ 864 D · 2 X a³ (2c+a)
    -- numerator lower bound: 2Xa³(2c+a) ≥ 2Xa³·(2·(D/2)) = 2 X a³ D ≥ 2 X A³ D = 2 R D⁵... wait scale
    -- denominator upper bound: c³(c+a)³ ≤ (3D)³(4D)³ = 1728 D⁶
    have hcub : c ^ 3 * (c + (a:ℝ)) ^ 3 ≤ 1728 * S.D ^ 6 := by
      have h1 : c ≤ 3 * S.D := hchi
      have h2 : c + (a:ℝ) ≤ 4 * S.D := by linarith [ha2D5]
      have hc3 : c ^ 3 ≤ (3 * S.D) ^ 3 := pow_le_pow_left₀ hc0.le h1 3
      have hca3 : (c + (a:ℝ)) ^ 3 ≤ (4 * S.D) ^ 3 := pow_le_pow_left₀ hca.le h2 3
      calc c ^ 3 * (c + (a:ℝ)) ^ 3 ≤ (3 * S.D) ^ 3 * (4 * S.D) ^ 3 :=
            mul_le_mul hc3 hca3 (by positivity) (by positivity)
        _ = 1728 * S.D ^ 6 := by ring
    -- 2 X a³ (2c+a) ≥ 2 X A³ D = 2 R D⁵
    have hXa3 : P.X * S.A ^ 3 ≤ P.X * (a:ℝ) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hX.le; exact pow_le_pow_left₀ hApos.le haA 3
    have hnum_lb : 2 * S.R * S.D ^ 5 ≤ 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) := by
      have h2cD : S.D ≤ 2 * c + (a:ℝ) := by linarith [hclo, haR]
      have hstep : 2 * (P.X * S.A ^ 3) * S.D ≤ 2 * (P.X * (a:ℝ) ^ 3) * (2 * c + (a:ℝ)) :=
        mul_le_mul (by linarith [hXa3]) h2cD hDpos.le (by positivity)
      have : 2 * (P.X * S.A ^ 3) * S.D = 2 * S.R * S.D ^ 5 := by rw [hXA3]; ring
      linarith [hstep, this.symm.le, this.le]
    -- combine: R·c³(c+a)³ ≤ R·1728 D⁶ = 1728 R D⁶ ;  864 D·(num) ≥ 864 D·2 R D⁵ = 1728 R D⁶
    calc S.R * (c ^ 3 * (c + (a:ℝ)) ^ 3) ≤ S.R * (1728 * S.D ^ 6) :=
          mul_le_mul_of_nonneg_left hcub hRpos.le
      _ = (864 * S.D) * (2 * S.R * S.D ^ 5) := by ring
      _ ≤ (864 * S.D) * (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ))) :=
          mul_le_mul_of_nonneg_left hnum_lb (by have := hDpos; positivity)
      _ = 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) * (864 * S.D) := by ring
  -- now the MVT step, casing on d vs dt
  rw [htgt]
  rcases lt_trichotomy d dt with hlt | heq | hgt
  · -- d < dt
    obtain ⟨c, hc1, hc2, hslope⟩ := Rfun_mvt hX haR (by linarith [hDpos] : 0 < d) hlt
    have hclo : S.D / 2 ≤ c := by linarith [hdD, hc1]
    have hchi : c ≤ 3 * S.D := by linarith [hwhi, hc2]
    -- |R_a(d) - r| = |R_a(d) - R_a(dt)| = |R_a'(c)|·(dt-d)
    have hRdtval : Rfun P.X (a:ℝ) dt = r := hRdt
    have hc0 : 0 < c := by linarith [hDpos, hclo]
    have hcden : 0 < c ^ 3 * (c + (a:ℝ)) ^ 3 := by positivity
    have hslopepos : 0 < 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3) := by
      apply div_pos (by positivity) hcden
    have hdiff : Rfun P.X (a:ℝ) d - r
        = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := by
      have hs : Rfun P.X (a:ℝ) dt - Rfun P.X (a:ℝ) d
          = (-2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := hslope
      rw [← hRdtval]
      have : Rfun P.X (a:ℝ) d - Rfun P.X (a:ℝ) dt
          = -(Rfun P.X (a:ℝ) dt - Rfun P.X (a:ℝ) d) := by ring
      rw [this, hs]; ring
    have hderlb := hderiv_lb c hclo hchi
    -- |R_a(d)-r| = slope·(dt-d), slope ≥ R/(864D), |R_a(d)-r| ≤ 14H/D
    have habs : |Rfun P.X (a:ℝ) d - r|
        = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := by
      rw [hdiff, abs_of_pos (mul_pos (div_pos (by positivity) hcden) (by linarith [hlt]))]
    -- so (dt - d) = |R_a(d)-r|/slope ≤ (14H/D)/(R/(864D)) = 12096 H/R
    have hge : S.R / (864 * S.D) * (dt - d) ≤ 14 * P.H / S.D := by
      calc S.R / (864 * S.D) * (dt - d)
          ≤ (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) :=
            mul_le_mul_of_nonneg_right hderlb (by linarith [hlt])
        _ = |Rfun P.X (a:ℝ) d - r| := habs.symm
        _ ≤ 14 * P.H / S.D := hrd
    -- conclude |d - dt| = dt - d ≤ 12096 H/R
    rw [abs_of_nonpos (by linarith [hlt])]
    have hfin : dt - d ≤ 12096 * P.H / S.R := by
      have hRD : 0 < S.R / (864 * S.D) := by positivity
      have hmul : (dt - d) ≤ (14 * P.H / S.D) / (S.R / (864 * S.D)) := by
        rw [le_div_iff₀ hRD]; linarith [hge]
      have hsimp : (14 * P.H / S.D) / (S.R / (864 * S.D)) = 12096 * P.H / S.R := by
        field_simp; ring
      linarith [hmul, hsimp.le, hsimp.ge]
    linarith [hfin]
  · rw [heq, sub_self, abs_zero]; positivity
  · -- dt < d
    obtain ⟨c, hc1, hc2, hslope⟩ := Rfun_mvt hX haR hdtpos hgt
    have hclo : S.D / 2 ≤ c := by linarith [hwlo, hc1]
    have hchi : c ≤ 3 * S.D := by linarith [hd2D, hc2, hDpos]
    have hRdtval : Rfun P.X (a:ℝ) dt = r := hRdt
    have hc0 : 0 < c := by linarith [hDpos, hclo]
    have hcden : 0 < c ^ 3 * (c + (a:ℝ)) ^ 3 := by positivity
    have hdiff : Rfun P.X (a:ℝ) d - r
        = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := by
      have hs : Rfun P.X (a:ℝ) d - Rfun P.X (a:ℝ) dt
          = (-2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (d - dt) := hslope
      rw [← hRdtval, hs]; ring
    have hderlb := hderiv_lb c hclo hchi
    have habs : |Rfun P.X (a:ℝ) d - r|
        = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (d - dt) := by
      rw [hdiff, abs_of_nonpos (by
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity); linarith [hgt])]
      ring
    have hge : S.R / (864 * S.D) * (d - dt) ≤ 14 * P.H / S.D := by
      calc S.R / (864 * S.D) * (d - dt)
          ≤ (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (d - dt) :=
            mul_le_mul_of_nonneg_right hderlb (by linarith [hgt])
        _ = |Rfun P.X (a:ℝ) d - r| := habs.symm
        _ ≤ 14 * P.H / S.D := hrd
    rw [abs_of_nonneg (by linarith [hgt])]
    have hRD : 0 < S.R / (864 * S.D) := by positivity
    have hmul : (d - dt) ≤ (14 * P.H / S.D) / (S.R / (864 * S.D)) := by
      rw [le_div_iff₀ hRD]; linarith [hge]
    have hsimp : (14 * P.H / S.D) / (S.R / (864 * S.D)) = 12096 * P.H / S.R := by
      field_simp; ring
    linarith [hmul, hsimp.le, hsimp.ge]

/-- The §6 small-ball constant `K₀ = C₀·12097` (with `C₀ = 832` the `nearcurve_membership`
constant) and width `δ₀ = H/(Δ²Ω²)`. -/
noncomputable def K0 : ℝ := nearcurve_membership.choose * 12097

theorem K0_pos : 0 < K0 := by
  unfold K0; have := nearcurve_membership.choose_spec.1; positivity

/-- **Near-integer transfer** (writeup ~1241–1248).  A `RaWitness` for `r` at `a ∈ [A,2A]`,
under `10A ≤ D` and `500 ≤ GHΩ³`, makes the §6 phase `f̃ₐ(r) = F_a(d̃ₐ(r))` lie within
`K₀·δ₀` of an integer, where `K₀ = 832·12097` and `δ₀ = H/(Δ²Ω²)`. -/
theorem ftil_near_integer {P : Globals} {S : Scale P} {a : ℤ} {r : ℕ}
    (hAD : 10 * S.A ≤ S.D) (hΩfloor : (500 : ℝ) ≤ P.G * P.H * S.Ω ^ 3)
    (ha0 : 0 < a) (haA : S.A ≤ (a : ℝ)) (haA2 : (a : ℝ) ≤ 2 * S.A)
    (hwit : RaWitness P S a r) :
    distInt (ftil P.X (r : ℝ) (a : ℝ)) ≤ K0 * (P.H / (S.Δ ^ 2 * S.Ω ^ 2)) := by
  have hCpos := nearcurve_membership.choose_spec.1
  have hmem := nearcurve_membership.choose_spec.2
  set C := nearcurve_membership.choose with hCdef
  obtain ⟨d, hinDa, hDd, hd2D, hrd, hrlo, hrhi⟩ := hwit
  have hX := P.X_pos
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hDeq : S.D = P.H * S.Δ := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hDpos : 0 < S.D := by rw [hDeq]; positivity
  have hG := P.G_pos
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  -- r > 0  (from (1/72)·R ≤ r and R > 0)
  have hr0 : 0 < (r:ℝ) := lt_of_lt_of_le (by positivity) hrlo
  -- 2A ≤ D and Ω ≤ H from 10A ≤ D
  have h2AD : 2 * S.A ≤ S.D := by linarith [hAD, hApos]
  have hΩH : S.Ω ≤ P.H := by
    have : 10 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by rw [← hAeq, ← hDeq]; exact hAD
    nlinarith [this, hΔ, hΩ]
  -- window and closeness, for the integer d cast to ℝ
  have hwin := ftil_dtilde_window (P := P) (S := S) (a := a) (r := (r:ℝ)) (d := (d:ℝ))
    hAD hΩfloor ha0 haA haA2 hr0 hDd hd2D hrd
  have hclose := ftil_dtilde_close (P := P) (S := S) (a := a) (r := (r:ℝ)) (d := (d:ℝ))
    hAD ha0 haA haA2 hr0 hDd hd2D hrd hwin.1 hwin.2
  -- apply nearcurve_membership with dtil := fun ρ => dtilde X ρ a, Capx := 12096
  have hkey := hmem P S a (fun ρ => dtilde P.X ρ (a:ℝ)) r d 12096
    ha0 haA haA2 hΩH (by norm_num) h2AD hinDa hDd hd2D
    (by simpa using hwin.1) (by simpa using hwin.2)
    (by simpa using hclose)
  -- ftil X r a = Ffun X a (dtilde X r a)
  have hftil : ftil P.X (r:ℝ) (a:ℝ) = Ffun P.X (a:ℝ) (dtilde P.X (r:ℝ) (a:ℝ)) :=
    ftil_eq_phase hX haR hr0
  rw [hftil]
  -- C·(1+12096)·δ₀ ≤ K₀·δ₀ requires C ≤ 832; but nearcurve_membership's C is exactly 832.
  -- Use the proof's value: hmem provides C with the bound; re-derive via the concrete constant.
  refine le_trans (by simpa using hkey) ?_
  have hδ0 : 0 ≤ P.H / (S.Δ ^ 2 * S.Ω ^ 2) := by positivity
  have hCle : C * (1 + 12096) ≤ K0 := by
    rw [K0, ← hCdef]; apply le_of_eq; ring
  exact mul_le_mul_of_nonneg_right hCle hδ0


end Squarefree
