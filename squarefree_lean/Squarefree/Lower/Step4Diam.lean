import Squarefree.Lower.Step4Combine
import Squarefree.Lower.Step4Cref
import Squarefree.Lower.Step4CubicSize
import Squarefree.Lower.Step4P2Size
import Squarefree.Lower.Step4SqDiffShell

/-!
# §5 Step-4 `diam` budget assembly (writeup 1052–1058; ADDITIVE route)

This file assembles the four green SIZE inputs (coefficient-drift, slope-reconstruction, cubic
tail, quartic `p₂`) into the two-point square-difference **diameter** budget the large-defect
`v`-band count (`sqdiff_band_card_le`) consumes.

## Step 1 — the difference form `|Σ_closed − Ĉ·v²| ≤ E`

`Σ_closed` is a near-parabola in `v` whose *fixed*, `r`-independent leading coefficient (in `v²`
units) is

  `Ĉ := Cref·(A/a)²·ℓ₁² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)/a²  (> 0)`.

`Sigma_closed_diff_Cref_le` shows the deviation from the model parabola `Ĉ·v²` splits, by the
exact decomposition `Σ_closed = C'(b₀)·(ℓ₁v)² + cubic + p₂` (where `C'(b₀)` is the per-`r`
bracket-included quadratic coefficient `Cprime`), into four green pieces:

  `E = E_recon + E_drift + E_cubic + E_p2`,

* `E_recon = (Xa/d⁵)·3ℓ₁ℓ₂(ℓ₂−ℓ₁)·|−4+10a/d|·gap·(ℓ₁v)²`  — the slope-reconstruction drift
  `|C'(b₀) − C'(b̃ₐ)|·(ℓ₁v)²`, linear in `b₀`, bounded by the smooth-slope gap `hb0gap`;
* `E_drift = 20·(a/d)²·(Cref·(A/a)²)·(ℓ₁v)²`  — the flat-coefficient drift `|C'(b̃ₐ) − Cref·(A/a)²|`
  at the smooth model (`Cref_drift_le`);
* `E_cubic = (1/U¹⁴)·|s|`  — the cubic-in-`v` tail (`cubic_size_le`);
* `E_p2 = 77·(GΩ/Δ⁴)·P2AbsMaj/D`  — the quartic `p₂`-contribution (`abs_pref_mul_Ptwo_div_le_p2PointBudget`).

Each piece is a negative `X`-power × `|s|` after the downstream size collapse; this file keeps `E`
symbolic as the four-term sum.

## Step 2 — the two-point square-difference `|v² − v'²| ≤ diam`

For two fibre points (same `a`, `ℓ₁`, `ℓ₂`, and same near-integer `s`, both `b₀ < 0`), the
perturbed-quadratic shell (`abs_sq_sub_le_of_perturbed_quadratic_shell`, additive route `θ = 0`,
`E0 = 2·E_max`) converts the near-integer tolerance `err` (both `|Σ_closed − s| ≤ err`) and the
step-1 difference bound `E_max` (both `|Σ_closed − Ĉ·v²| ≤ E_max`) into

  `|v² − v'²| ≤ diam := (4·err + 4·E_max)/Ĉ`,

precisely the `hpair` shape `sqdiff_band_card_le` consumes.  The `b₀ < 0` restriction (the sign
split, pitfall 3) and the smooth-slope gap `hb0gap` are carried as hypotheses for the size agent
to discharge; they do not enter the algebra here.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 difference-form budget** (writeup 1052).  The deviation of the closed form
`Σ_closed` from the fixed model parabola `Ĉ·v²` (with `Ĉ = Cref·(A/a)²·ℓ₁²`, `r`-independent) is
bounded by the four-part additive budget `E_recon + E_drift + E_cubic + E_p2`.  The decomposition is
exact: `Σ_closed = C'(b₀)·(ℓ₁v)² + cubic + p₂`, then `C'(b₀) − Cref·(A/a)²` is split through the
smooth-slope model `b̃ₐ = b1Model` into the reconstruction drift (`E_recon`, via the linearity of
`Cprime` in `b₀` and the slope gap `hb0gap`) and the flat-coefficient drift (`E_drift`, via
`Cref_drift_le`); the cubic and `p₂` tails are `cubic_size_le` and
`abs_pref_mul_Ptwo_div_le_p2PointBudget`. -/
theorem Sigma_closed_diff_Cref_le
    {a b₀ v d ℓ₁ ℓ₂ Bx Vx gap : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (had : a ≤ d)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hdD : S.D ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hvpin_hi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2
        ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|))
    (hb : |b₀| ≤ Bx) (hBx0 : 0 ≤ Bx) (hvx : |v| ≤ Vx) (_hVx0 : 0 ≤ Vx)
    (hb0gap : |b₀ - b1Model P.X a d| ≤ gap) :
    |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2|
      ≤ (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)| * gap * (ℓ₁ * v) ^ 2
        + 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
        + (1 / P.U ^ 14) * |(s : ℝ)|
        + 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D) := by
  -- positivity scaffolding
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; exact mul_pos P.H_pos hΔpos
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  have h21 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hKnn : (0:ℝ) ≤ (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg hXpos.le ha0.le) (pow_nonneg hd_pos.le 5)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hℓ1R.le) hℓ2R.le) h21.le
  -- exact decomposition  Σ_closed = C'(b₀)·(ℓ₁v)² + cubic + p₂
  have hcore : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
      = Cprime P.X a b₀ d ℓ₁ ℓ₂ * (ℓ₁ * v) ^ 2
        + (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)
        + (P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d)) := by
    unfold Sigma_closed Pone Cprime; ring
  -- difference identity: split the v²-coefficient drift through the smooth model b̃ₐ = b1Model
  have hdiff : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
      = (Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2
        + (Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
        + (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)
        + (P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d)) := by
    rw [hcore]; ring
  -- E_recon: linearity of Cprime in b₀ + slope gap
  have hbRC : |(Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2|
      ≤ (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)| * gap * (ℓ₁ * v) ^ 2 := by
    have hRCeq : Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂
        = (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (-4 + 10 * a / d)
            * (b₀ - b1Model P.X a d) := by
      unfold Cprime; ring
    rw [hRCeq, abs_mul, abs_mul, abs_mul, abs_of_nonneg hKnn, abs_of_nonneg (sq_nonneg (ℓ₁ * v))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb0gap (mul_nonneg hKnn (abs_nonneg _))) (sq_nonneg (ℓ₁ * v))
  -- E_drift: flat-coefficient drift at the smooth model
  have hbDC : |(Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
        * (ℓ₁ * v) ^ 2|
      ≤ 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (ℓ₁ * v))]
    exact mul_le_mul_of_nonneg_right (Cref_drift_le ha0 hd_pos had hℓ1R hℓ12) (sq_nonneg (ℓ₁ * v))
  -- E_cubic: the cubic-in-v tail
  have hbCUB : |(P.X * a / d ^ 5) * (-4 + 10 * a / d) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3)|
      ≤ (1 / P.U ^ 14) * |(s : ℝ)| :=
    cubic_size_le ha0 ha_hi hℓ1 hℓ12 hℓ12' hv hdD h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hvpin_hi
  -- E_p2: the quartic p₂-contribution
  have hbP2 : |(P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))|
      ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D) :=
    abs_pref_mul_Ptwo_div_le_p2PointBudget ha0 ha_hi hℓ1 hℓ12 hb hBx0 hvx (S.D_eps_lo hdD) h1 hG1 hU1 hΔ1
      hΩU hUbig
  -- assemble: triangle inequality across the four pieces
  rw [hdiff]
  refine le_trans ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) ?_
  exact add_le_add (add_le_add (add_le_add hbRC hbDC) hbCUB) hbP2

/-- **§5 Step-4 two-point square-difference diameter** (writeup 1058).  Two fibre points sharing
`a`, `ℓ₁`, `ℓ₂` and the same near-integer `s` (both `b₀ < 0` — the sign split, pitfall 3) — each
within the near-integer tolerance `err` of `s` and within the step-1 difference budget `E_max` of
the fixed model parabola `Ĉ·v²` — satisfy the band-variation square-difference bound

  `|v² − v'²| ≤ (4·err + 4·E_max)/Ĉ`,

with `Ĉ = Cref·(A/a)²·ℓ₁² > 0`.  This is the additive-route (`θ = 0`) instance of the
perturbed-quadratic shell with `E0 = 2·E_max`, producing exactly the `hpair` shape consumed by
`sqdiff_band_card_le`. -/
theorem step4_sqdiff_diam
    {a v v' d d' b₀ b₀' err E_max : ℝ} {ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha : 0 < a) (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hx_ni : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)| ≤ err)
    (hy_ni : |Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - (s : ℝ)| ≤ err)
    (hEx : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2| ≤ E_max)
    (hEy : |Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂
        - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v' ^ 2| ≤ E_max) :
    |v ^ 2 - v' ^ 2|
      ≤ (4 * err + 4 * E_max) / (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) := by
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; exact mul_pos hΔpos hΩpos
  set Chat : ℝ := Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2 with hChat
  have hC : 0 < Chat := by
    rw [hChat]
    exact mul_pos (mul_pos (Cref_pos hℓ1 hℓ12) (pow_pos (div_pos hApos ha) 2)) (pow_pos hℓ1 2)
  -- the perturbed-quadratic shell, additive route θ = 0, E0 = 2·E_max
  have hpert :
      |(Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - Chat * v ^ 2)
          - (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - Chat * v' ^ 2)|
        ≤ 0 * Chat * |v ^ 2 - v' ^ 2| + 2 * E_max := by
    have habs : |(Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - Chat * v ^ 2)
        - (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - Chat * v' ^ 2)| ≤ 2 * E_max := by
      calc |(Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - Chat * v ^ 2)
              - (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - Chat * v' ^ 2)|
            ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - Chat * v ^ 2|
              + |Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - Chat * v' ^ 2| := by
              rw [sub_eq_add_neg]
              exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
        _ ≤ E_max + E_max := add_le_add hEx hEy
        _ = 2 * E_max := by ring
    exact habs.trans_eq (by ring)
  have hshell := abs_sq_sub_le_of_perturbed_quadratic_shell
    (C := Chat) (theta := 0) (eta := err) (E0 := 2 * E_max)
    (x := v) (y := v') (center := (s : ℝ))
    (ex := Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - Chat * v ^ 2)
    (ey := Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - Chat * v' ^ 2)
    hC (by norm_num)
    (by
      have e : Chat * v ^ 2 + (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - Chat * v ^ 2)
          = Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ := by ring
      rw [e]; exact hx_ni)
    (by
      have e : Chat * v' ^ 2 + (Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ - Chat * v' ^ 2)
          = Sigma_closed P.X a b₀' v' d' ℓ₁ ℓ₂ := by ring
      rw [e]; exact hy_ni)
    hpert
  exact hshell.trans_eq (by ring)

end Squarefree
