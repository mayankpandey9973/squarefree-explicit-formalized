import Squarefree.Lower.Step4Compose
import Squarefree.Lower.Step4DiamHybrid
import Squarefree.Lower.Step4VsBand

/-!
# §5 Step-4 pairwise budget at the `Vbox` v-box

Derives the pairwise hypothesis of `step4_fibre_branch_le` from the two-point hybrid
diameter `step4_sqdiff_diam2_hyb` evaluated at `V := min (Vbox S ℓ₁ ℓ₂ n) (Vmax P S)`,
then enlarged to `Vbox` by budget monotonicity.  The `err`-slot is the single per-point
near-integer tolerance shared by both pins (as in the supplier).
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

/-- `Step4EcubV` is `const⁺ · V³`, hence monotone in `V ≥ 0`. -/
private theorem ecubV_mono {ℓ₁ ℓ₂ V V' : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hV0 : 0 ≤ V) (hVV' : V ≤ V') :
    Step4EcubV P S ℓ₁ ℓ₂ V ≤ Step4EcubV P S ℓ₁ ℓ₂ V' := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hcoef : (0:ℝ) ≤ 2 * (77 * (P.G * S.Ω / S.Δ ^ 4)) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) h2ℓ)
  unfold Step4EcubV
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV0 hVV' 3) hcoef

/-- `Step4EremHyb` is `c₁⁺·(ℓ₁V)² + c₂ + E0_p2_hyb`, hence monotone in `V ≥ 0`. -/
private theorem eremHyb_mono {a ℓ₁ ℓ₂ gap V V' : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hgap0 : 0 ≤ gap) (hV0 : 0 ≤ V) (hVV' : V ≤ V') :
    Step4EremHyb P S a ℓ₁ ℓ₂ gap V ≤ Step4EremHyb P S a ℓ₁ ℓ₂ gap V' := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := lt_trans hℓ1p hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hc1 : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) h21)) hgap0
  have hsq : (ℓ₁ * V) ^ 2 ≤ (ℓ₁ * V') ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hℓ1p.le hV0) (mul_le_mul_of_nonneg_left hVV' hℓ1p.le) 2
  have h1 := mul_le_mul_of_nonneg_left hsq hc1
  have h3 := E0_p2_hyb_mono (P := P) (S := S) hℓ1 hℓ12 hV0 hVV'
  unfold Step4EremHyb
  linarith

/-- **§5 Step-4 pairwise square-diff budget at `Vbox`.**  Two fibre points, each in the
`Vbox`-box AND under the global cap `Vmax`, with near-integer pins to the same `s` at the
shared tolerance `err`, satisfy the pairwise bound of `step4_fibre_branch_le` with the
budget evaluated at `Vbox S ℓ₁ ℓ₂ n`. -/
theorem step4_pack_pair
    {a v v' d d' b₀ b₀' err gap n : ℝ} {ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (had : a ≤ d) (had' : a ≤ d')
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hvbox : |v| ≤ Vbox S ℓ₁ ℓ₂ n) (hvbox' : |v'| ≤ Vbox S ℓ₁ ℓ₂ n)
    (hvmax : |v| ≤ Vmax P S) (hvmax' : |v'| ≤ Vmax P S)
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
      ≤ (4 * err + 2 * (Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n)
            + 2 * Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ n)))
          / (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) := by
  set V := min (Vbox S ℓ₁ ℓ₂ n) (Vmax P S) with hVdef
  have hV0 : (0:ℝ) ≤ V := le_min Vbox_nonneg Vmax_nonneg
  have hVcap : V ≤ Vmax P S := min_le_right _ _
  have hVle : V ≤ Vbox S ℓ₁ ℓ₂ n := min_le_left _ _
  have hd := step4_sqdiff_diam2_hyb ha0 ha_hi had had' hℓ1 hℓ12 hℓ12'
    (le_min hvbox hvmax) (le_min hvbox' hvmax') hVcap hV0 hsign hdD hd'D
    h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hbgap hbgap' hgap0 hb0box hb0box' hx_ni hy_ni
  refine hd.trans (div_le_div_of_nonneg_right ?_ ?_)
  · have hcub := ecubV_mono (P := P) (S := S) hℓ1 hℓ12 hV0 hVle
    have hrem := eremHyb_mono (P := P) (S := S) (a := a) (gap := gap) hℓ1 hℓ12 hgap0 hV0 hVle
    linarith
  · have hApos : (0:ℝ) < S.A := by
      rw [show S.A = S.Δ * S.Ω from rfl]; exact mul_pos S.Δ_pos S.Ω_pos
    have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
    exact (mul_pos (mul_pos (Cref_pos hℓ1p hℓ12)
      (pow_pos (div_pos hApos ha0) 2)) (pow_pos hℓ1p 2)).le

end Squarefree
