import Squarefree.Bracket.Sec7Defs
import Squarefree.Bracket.Sec7PhaseExp
import Squarefree.Bracket.Sec7PhiDeriv
import Squarefree.Opt.OnStripAux
import Squarefree.Counting.Preimage
import Squarefree.Geometry.NearCurveResidual
import Mathlib

/-!
# §7 nonzero top-carry branch (plan nodes N16–N20)

Statement layer for the `ρ₀ ≠ 0` branch of Prop 7.1 (md 1827–1934): the `X^{-c}`
smallness facts (N16, TRAP-3: stated from the verified strip facts `OnStripAux.StripData`,
NEVER the md-1717 literal `x ≫ GU¹⁰`), the local-piece decomposition with `T_{ρ,q} ≍ T₁`
(N17), the §4.3 side conditions (N18, TRAP-2b), the local Prop 4.3 count (7.8) (N19;
in-tree `Geometry.nearCurve_count` carries a log — kept here as a `(1 + log X)` factor,
absorbed by the harvest N22), and the square-root evaluations (N20; the third is lossy
by `√H`, intentionally, md 1929).

PHASE-1f SEAM: N17/N19 take their N10/N11-parent inputs in the ACTUAL parent forms —
the N9 bundle `Sec7MonExp` (so `Φ = sec7_Phi`, `Φ₂ = iteratedDeriv 2 (sec7_Phi …)`, and
eq (7.5)/`C* ≠ 0` come from `sec7_eq75`/`Cstar_eq`/`Cstar_lower`), the N11 conclusion
`sec7_err_deriv_bound` VERBATIM as `hErr`, and the N7-cover carry/fiber sizes
(`sec7_cCarry`, `sec7_cFib·(1 + h_jh_k·T₂/R²)`); the top-carry bound is `sec7_cCarry`
(N7's actual conclusion; md 1854–56 "bounded by an absolute constant").

## Constant ledger (provisional; Phase-2 re-pins)
* `sec7_cSmall = 1/100` — the `X^{-c}` smallness exponent of md 1830–33.
* `sec7_cD1 = 10¹²` — constant in the md 1903–07 `δ₁(h)` upper-bound hypothesis.
* `sec7_cN19 = 10¹²` (AM-6; ARB-1, A5: engine constant PINNED) — the N19 count constant.
  The engine constant is `prop43_local`'s literal `C = 109159296 ≈ 1.1·10⁸ ≤ 10⁹`
  (Geometry/NearCurveResidual.lean:402, proved — the 10⁴-class estimate of the A5 ruling
  is superseded by the on-disk value); content `1.1·10⁸ × ≤100 pieces ≈ 1.1·10¹⁰ ≤ 10¹²`
  (91×).  The `T_{ρ,q} ≍ T₁` calibration losses are charged to `sec7_cBand`, NOT cN19.
* `sec7_cN20 = 10³` (AM-6) — the pinned N20 evaluation constant: the four evaluations
  are exact monomial identities (sympy-banked) except the third, which is intentionally
  lossy by `√H`, so a small absolute constant suffices (ledger).
-/

open Classical Finset

namespace Squarefree

open Counting

/-- `X^{-c}` smallness exponent for the §7 nonzero-branch facts (ledger; md 1830–33). -/
noncomputable def sec7_cSmall : ℝ := 1 / 100

/-- Constant in the `δ₁(h)` three-term upper-bound hypothesis (ledger; md 1903–07). -/
def sec7_cD1 : ℝ := 10 ^ 12

/-- Pinned N17/N19 constant (AM-6; ledger): piece calibration `T_q ≍ T₁` and the (7.8)
count (engine constant × ≤100 pieces × calibration losses). -/
def sec7_cN19 : ℝ := 10 ^ 12

/-- N17 `T_q ≍ T₁` band constant (A5 gate; ledger U4): the pack admits
`|c₁| ≤ cMon = 10⁶`, `|ρ₀| ≤ cCarry = 10⁶`, and `p = ⌈R/72⌉`, so the pin
`Tq ≤ R²|Φ₂| ≤ 2Tq` forces `Tq` up to `2·cMon·cCarry·72³ ≈ 1.5·10¹⁸ · T₁`;
`10²⁰` gives slack (the old shared `cN19 = 10¹²` was unsatisfiable here). -/
def sec7_cBand : ℝ := 10 ^ 20

/-- Pinned N20 evaluation constant (AM-6; ledger): the evaluations are exact (third
lossy by `√H`), so `10³` suffices. -/
def sec7_cN20 : ℝ := 10 ^ 3

theorem sec7_cSmall_pos : (0:ℝ) < sec7_cSmall := by norm_num [sec7_cSmall]
theorem sec7_cD1_pos : (0:ℝ) < sec7_cD1 := by norm_num [sec7_cD1]
theorem sec7_cN19_pos : (0:ℝ) < sec7_cN19 := by norm_num [sec7_cN19]
theorem sec7_cBand_pos : (0:ℝ) < sec7_cBand := by norm_num [sec7_cBand]
theorem sec7_cN20_pos : (0:ℝ) < sec7_cN20 := by norm_num [sec7_cN20]

/-- `X^{1/50} = H^{1/10}·G^{1/50}` (from `H = X^{(1-g)/5}`, `G = X^g`). -/
private theorem sec7_X150_eq (P : Globals) :
    P.X ^ ((1:ℝ)/50) = P.H ^ ((1:ℝ)/10) * P.G ^ ((1:ℝ)/50) := by
  rw [Globals.H, Globals.G, ← Real.rpow_mul P.X_pos.le, ← Real.rpow_mul P.X_pos.le,
      ← Real.rpow_add P.X_pos]
  congr 1; ring

/-- `H^{1/2}·x^{1/2} = H/Δ` (since `x = H/Δ²`). -/
private theorem sec7_Hx_half (P : Globals) (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) = P.H / S.Δ := by
  have hH := P.H_pos; have hΔ := S.Δ_pos
  have hx := OnStripAux.x_pos P S
  rw [← Real.mul_rpow hH.le hx.le]
  have hHx : P.H * S.x = (P.H / S.Δ) ^ (2:ℕ) := by
    unfold Scale.x; field_simp
  rw [hHx, ← Real.rpow_natCast (P.H / S.Δ) 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- `R³·T₁ = H²G²Ω⁸` (sympy-banked). -/
private theorem sec7_R3T1 (P : Globals) (S : Scale P) :
    S.R ^ 3 * S.T₁ = P.H ^ 2 * P.G ^ 2 * S.Ω ^ 8 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos
  unfold Scale.R Scale.T₁ Scale.F
  field_simp

/-- `N·s ≤ D ⟹ N/D ≤ s⁻¹` (for `D, s > 0`). -/
private theorem sec7_div_le_inv {N D s : ℝ} (hD : 0 < D) (hs : 0 < s)
    (h : N * s ≤ D) : N / D ≤ s⁻¹ := by
  rw [div_le_iff₀ hD, inv_mul_eq_div, le_div_iff₀ hs]
  exact h

/-- `a² ≤ b²` with `a, b ≥ 0` gives `a ≤ b`. -/
private theorem sec7_le_of_sq {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by nlinarith

/-- `X^{1/50} ≤ R` on the strip: `R·X^{-1/50} = H^{2/5}x^{1/2}G^{49/50}Ω³` has worst-corner
`X`-exponent `2/25 − 13g/80 − Cu·u/2 − 3u/16 > 0` on the budget (sympy-banked, ≈ 0.078). -/
private theorem sec7_X150_le_R (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg : 0 ≤ P.g) (hu : 0 ≤ P.u) (hXgt : 1 < P.X) :
    P.X ^ ((1:ℝ)/50) ≤ S.R := by
  have hH := P.H_pos; have hG := P.G_pos
  have hCu := D.hCu
  have hbudE : 18977 * P.g + 18675 * P.u + 790 * (Cu * P.u) ≤ 2 := by
    have h := hbud; unfold OnStripAux.Budget at h; nlinarith
  have hw : (0:ℝ) ≤ Cu * P.u := mul_nonneg (by linarith) hu
  have hkey : (1:ℝ) <
      P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((49:ℝ)/50) * S.Ω ^ ((3:ℝ)) :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt ((2:ℝ)/5) ((1:ℝ)/2) ((49:ℝ)/50) ((3:ℝ))
      (by unfold OnStripAux.ratioExp; norm_num; nlinarith [hbudE, hg, hu, hw])
  have hsplit : S.R = P.X ^ ((1:ℝ)/50)
      * (P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((49:ℝ)/50) * S.Ω ^ ((3:ℝ))) := by
    rw [OnStripAux.R_mono P S, sec7_X150_eq,
        show P.H ^ ((1:ℝ)/10) * P.G ^ ((1:ℝ)/50)
            * (P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((49:ℝ)/50) * S.Ω ^ ((3:ℝ)))
          = (P.H ^ ((1:ℝ)/10) * P.H ^ ((2:ℝ)/5)) * S.x ^ ((1:ℝ)/2)
            * (P.G ^ ((1:ℝ)/50) * P.G ^ ((49:ℝ)/50)) * S.Ω ^ ((3:ℝ)) from by ring,
        ← Real.rpow_add hH, ← Real.rpow_add hG]
    norm_num
  calc P.X ^ ((1:ℝ)/50) = P.X ^ ((1:ℝ)/50) * 1 := by ring
    _ ≤ P.X ^ ((1:ℝ)/50)
        * (P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((49:ℝ)/50) * S.Ω ^ ((3:ℝ))) :=
        mul_le_mul_of_nonneg_left hkey.le (Real.rpow_nonneg P.X_pos.le _)
    _ = S.R := hsplit.symm

/-- `X^{1/50} ≤ H^{1/2}x^{1/2}G²Ω⁸` on the strip: the ratio monomial
`H^{2/5}x^{1/2}G^{99/50}Ω⁸` has worst-corner `X`-exponent
`2/25 − 33g/80 − Cu·u/2 − 63u/16 > 0` on the budget (sympy-banked, ≈ 0.069). -/
private theorem sec7_X150_le_M (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg : 0 ≤ P.g) (hu : 0 ≤ P.u) (hXgt : 1 < P.X) :
    P.X ^ ((1:ℝ)/50) ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hCu := D.hCu
  have hbudE : 18977 * P.g + 18675 * P.u + 790 * (Cu * P.u) ≤ 2 := by
    have h := hbud; unfold OnStripAux.Budget at h; nlinarith
  have hw : (0:ℝ) ≤ Cu * P.u := mul_nonneg (by linarith) hu
  have hkey : (1:ℝ) <
      P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((99:ℝ)/50) * S.Ω ^ ((8:ℝ)) :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt ((2:ℝ)/5) ((1:ℝ)/2) ((99:ℝ)/50) ((8:ℝ))
      (by unfold OnStripAux.ratioExp; norm_num; nlinarith [hbudE, hg, hu, hw])
  have hsplit : P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8
      = P.X ^ ((1:ℝ)/50)
      * (P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((99:ℝ)/50) * S.Ω ^ ((8:ℝ))) := by
    rw [sec7_X150_eq,
        show P.H ^ ((1:ℝ)/10) * P.G ^ ((1:ℝ)/50)
            * (P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((99:ℝ)/50) * S.Ω ^ ((8:ℝ)))
          = (P.H ^ ((1:ℝ)/10) * P.H ^ ((2:ℝ)/5)) * S.x ^ ((1:ℝ)/2)
            * (P.G ^ ((1:ℝ)/50) * P.G ^ ((99:ℝ)/50)) * S.Ω ^ ((8:ℝ)) from by ring,
        ← Real.rpow_add hH, ← Real.rpow_add hG,
        show (1:ℝ)/10 + (2:ℝ)/5 = (1:ℝ)/2 from by norm_num,
        show (1:ℝ)/50 + (99:ℝ)/50 = (2:ℝ) from by norm_num,
        show ((2:ℝ):ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast,
        show ((8:ℝ):ℝ) = ((8:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  calc P.X ^ ((1:ℝ)/50) = P.X ^ ((1:ℝ)/50) * 1 := by ring
    _ ≤ P.X ^ ((1:ℝ)/50)
        * (P.H ^ ((2:ℝ)/5) * S.x ^ ((1:ℝ)/2) * P.G ^ ((99:ℝ)/50) * S.Ω ^ ((8:ℝ))) :=
        mul_le_mul_of_nonneg_left hkey.le (Real.rpow_nonneg P.X_pos.le _)
    _ = _ := hsplit.symm

/- md 1827–36: "Now suppose ρ₀ ≠ 0. Then the term c₁ρ₀T₁y⁻¹ dominates the principal part.
   For the displayed choice of W, the remaining monomials in (7.5) are o(T₁).
   Quantitatively this uses
     W⁴/R ≪ X^{-c},   P·T₃/(R³T₁) ≪ X^{-c},   W⁸/R² ≪ X^{-c}
   for some c > 0, after shrinking u in terms of g. These inequalities are immediate from
   the displayed W-constraints, P ≤ W⁷, and the ambient parameter range."
   TRAP-3: the ambient range enters ONLY as the verified strip facts (`StripData`) and the
   u-budget — never the md-1717 literal `x ≫ GU¹⁰`. -/
/-- **N16** (md 1827–36): the three `X^{-c}` smallness facts of the `ρ₀ ≠ 0` branch, with
`c = sec7_cSmall`, from the envelope plus the strip regime. -/
theorem sec7_nonzero_smallness :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 ≤ W →
    ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
    0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      W ^ 4 / S.R ≤ P.X ^ (-sec7_cSmall) ∧
      W ^ 8 / S.R ^ 2 ≤ P.X ^ (-sec7_cSmall) ∧
      ∀ Pv : ℝ, 0 ≤ Pv → Pv ≤ W ^ 7 →
        Pv * S.T₃ / (S.R ^ 3 * S.T₁) ≤ P.X ^ (-sec7_cSmall) := by
  intro P S W Env hW c₀ Cu hsd hbud hg0 hu0 hX24
  have hX0 := P.X_pos
  have hXgt : 1 < P.X := by
    by_contra h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le (not_lt.mp h) (by norm_num)
    linarith
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos
  have hx := OnStripAux.x_pos P S
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hW0 : (0:ℝ) ≤ W := le_trans zero_le_one hW
  have hs : 0 < P.X ^ sec7_cSmall := Real.rpow_pos_of_pos hX0 _
  have hs2 : (P.X ^ sec7_cSmall) ^ 2 = P.X ^ ((1:ℝ)/50) := by
    rw [← Real.rpow_natCast (P.X ^ sec7_cSmall) 2, ← Real.rpow_mul hX0.le]
    norm_num [sec7_cSmall]
  have hlog : (1:ℝ) ≤ 1 + Real.log P.X := by have := Real.log_nonneg hsd.hX; linarith
  have henvC : (1:ℝ) ≤ sec7_envC := by norm_num [sec7_envC]
  have hX150R := sec7_X150_le_R P S c₀ Cu hsd hbud hg0 hu0.le hXgt
  have hX150M := sec7_X150_le_M P S c₀ Cu hsd hbud hg0 hu0.le hXgt
  have hMpos : 0 < P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by positivity
  have hRform : S.R = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
    rw [OnStripAux.R_mono P S, Real.rpow_one,
        show (3:ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have hW8R : W ^ 8 ≤ S.R := by
    have htc4 : sec7_envC * W ^ 8 * (1 + Real.log P.X) ≤ S.R :=
      le_trans Env.tc4 (le_of_eq hRform.symm)
    have hWp : (0:ℝ) ≤ W ^ 8 := pow_nonneg hW0 8
    nlinarith [htc4, mul_nonneg hWp (sub_nonneg.mpr hlog),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr henvC) hWp) (le_trans zero_le_one hlog)]
  have hW14M : W ^ 14 ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
    have hWp : (0:ℝ) ≤ W ^ 14 := pow_nonneg hW0 14
    nlinarith [Env.tc8, mul_nonneg hWp (sub_nonneg.mpr hlog),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr henvC) hWp) (le_trans zero_le_one hlog)]
  refine ⟨?_, ?_, ?_⟩
  · have hg1 : W ^ 4 * P.X ^ sec7_cSmall ≤ S.R := by
      refine sec7_le_of_sq (by positivity) hRpos.le ?_
      rw [show (W ^ 4 * P.X ^ sec7_cSmall) ^ 2 = W ^ 8 * (P.X ^ sec7_cSmall) ^ 2
            from by ring, hs2]
      calc W ^ 8 * P.X ^ ((1:ℝ)/50) ≤ S.R * S.R :=
            mul_le_mul hW8R hX150R (Real.rpow_nonneg hX0.le _) hRpos.le
        _ = S.R ^ 2 := by ring
    rw [Real.rpow_neg hX0.le]
    exact sec7_div_le_inv hRpos hs hg1
  · have hsR : P.X ^ sec7_cSmall ≤ S.R :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hsd.hX (by norm_num [sec7_cSmall])) hX150R
    have hg2 : W ^ 8 * P.X ^ sec7_cSmall ≤ S.R ^ 2 := by
      calc W ^ 8 * P.X ^ sec7_cSmall ≤ S.R * S.R := mul_le_mul hW8R hsR hs.le hRpos.le
        _ = S.R ^ 2 := by ring
    rw [Real.rpow_neg hX0.le]
    exact sec7_div_le_inv (by positivity) hs hg2
  · intro Pv hPv0 hPvW
    have hT3pos : (0:ℝ) < S.T₃ := by unfold Scale.T₃; positivity
    have hRT := sec7_R3T1 P S
    have hRTpos : 0 < S.R ^ 3 * S.T₁ := by rw [hRT]; positivity
    have hMT : (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) * S.T₃
        = S.R ^ 3 * S.T₁ := by
      rw [hRT, show P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8
            = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * (P.G ^ 2 * S.Ω ^ 8) from by ring,
          sec7_Hx_half]
      unfold Scale.T₃
      field_simp
    have hW7s : W ^ 7 * P.X ^ sec7_cSmall
        ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
      refine sec7_le_of_sq (by positivity) hMpos.le ?_
      rw [show (W ^ 7 * P.X ^ sec7_cSmall) ^ 2 = W ^ 14 * (P.X ^ sec7_cSmall) ^ 2
            from by ring, hs2]
      calc W ^ 14 * P.X ^ ((1:ℝ)/50)
          ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8)
            * (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) :=
            mul_le_mul hW14M hX150M (Real.rpow_nonneg hX0.le _) hMpos.le
        _ = (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) ^ 2 := by ring
    have hg3 : Pv * S.T₃ * P.X ^ sec7_cSmall ≤ S.R ^ 3 * S.T₁ := by
      calc Pv * S.T₃ * P.X ^ sec7_cSmall
          ≤ W ^ 7 * S.T₃ * P.X ^ sec7_cSmall :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hPvW hT3pos.le) hs.le
        _ = (W ^ 7 * P.X ^ sec7_cSmall) * S.T₃ := by ring
        _ ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) * S.T₃ :=
            mul_le_mul_of_nonneg_right hW7s hT3pos.le
        _ = S.R ^ 3 * S.T₁ := hMT
    rw [Real.rpow_neg hX0.le]
    exact sec7_div_le_inv hRTpos hs hg3

/- md 1837–68: "Split each fixed grouped fiber into absolutely many subintervals on which
   y = r/R ranges over an interval where the leading factor y⁻³ varies by at most a fixed
   constant. On such a piece I_q, choose a reference point y_q ≍ 1 and set
   T_{ρ,q} ≍ |ρ₀| a²/R · y_q⁻³. Since a ≍ A = ΔΩ and R ≍ R₀ := H^{1/2}x^{1/2}GΩ³,
   R₀T₁ = A², we have, with absolute constants only, T_{ρ,q} ≍ |ρ₀|T₁ ≍ T₁. […] The
   normalized phase on I_q is Φ_{ρ,u}(r) = T_{ρ,q}·F_{ρ,u,q}(r/R), and the preceding
   domination estimates give the literal local curvature hypotheses 1 ≤ |F''_{ρ,u,q}(y)| ≤ 2
   on the inner interval of I_q, after enlarging the fixed constants and shrinking u."
   PHASE-1f: the parents (N10/N11/N16) enter in their ACTUAL conclusion forms — the N9
   bundle `ME : Sec7MonExp` (whence eq (7.5) `Φ = principal + Err` via `sec7_eq75`, the
   main second-derivative term `2c₁ρ₀(T₁/R²)y⁻³` from `ME.principal`, and `C* ≠ 0` via
   `Cstar_lower`), the N11 conclusion `sec7_err_deriv_bound` VERBATIM (`hErr`), the
   N7-cover carry/fiber sizes (which size the `B_{ρ,u}`-monomial), and N16 in scope. -/
/- N17 is proved below its private support lemmas, before N18c/N19/N20. -/

/- md 1870–74: "The remaining numerical hypotheses of Proposition 4.3 are the following
   explicit side inequalities:  R ≥ W⁸ > 1  for every relevant dyadic window, and the base
   support scale is R₀ = H^{1/2}x^{1/2}GΩ³." (`S.R = R₀` identically, since `Δ = √(H/x)`;
   `W⁸ ≤ R` is the envelope entry `tc4` with `sec7_envC ≥ 1`.)
   A5 gate: post-AM-7 `tc4` carries `(1 + log X)` on the W-side, which is vacuous for
   `X < e⁻¹`; the route `W⁸ ≤ envC·W⁸·(1+log X) ≤ H^{1/2}x^{1/2}GΩ³ = R` needs `1 ≤ X`
   (then `1 + log X ≥ 1`).  Callers hold it (prop_7_1 derives it from the X-floor). -/
/-- **N18a** (md 1870–74; A5 gate: + `1 ≤ X`): the side condition `R ≥ W⁸ > 1`. -/
theorem sec7_side_R_ge_W8 :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 ≤ P.X → 1 < W →
      1 < W ^ 8 ∧ W ^ 8 ≤ S.R := by
  intro P S W Env hX hW
  have hW8 : (1:ℝ) < W ^ 8 := one_lt_pow₀ hW (by norm_num)
  refine ⟨hW8, ?_⟩
  have hlog : (0:ℝ) ≤ Real.log P.X := Real.log_nonneg hX
  have henvC : (1:ℝ) ≤ sec7_envC := by norm_num [sec7_envC]
  have hW8pos : (0:ℝ) < W ^ 8 := lt_trans one_pos hW8
  have h1 : W ^ 8 ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
    have e1 : (1:ℝ) ≤ sec7_envC * (1 + Real.log P.X) := by nlinarith [henvC, hlog]
    calc W ^ 8 = W ^ 8 * 1 := (mul_one _).symm
      _ ≤ W ^ 8 * (sec7_envC * (1 + Real.log P.X)) :=
          mul_le_mul_of_nonneg_left e1 hW8pos.le
      _ = sec7_envC * W ^ 8 * (1 + Real.log P.X) := by ring
  have hR : P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
    rw [OnStripAux.R_mono P S, Real.rpow_one,
        show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  calc W ^ 8 ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := h1
    _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := Env.tc4
    _ = S.R := hR

/- md 1875–1900: "T₁ = H^{1/2}x^{-3/2}(GΩ)⁻¹ > 1 ⟺ x³G²Ω² < H. The inequality T₁ > 1 is
   not a consequence of the W-constraints alone; it is a genuine Section 4 side condition,
   verified in the final application from the unresolved strip of Proposition 8.1. Namely,
   using x ≪ G¹⁷Ω⁻²⁶X^{O(u)}, Ω ≫ G^{-1/4}U^{-3/4}X^{-O(u)}, one gets
   T₁ ≫ H^{1/2}G^{-69/2}U^{-57/2}X^{-O(u)} > 1 for g < 2/18977 and u > 0 small."
   TRAP-2b: md 1898's G^{-69/2} is really G^{-36} (benign; T₁ > 1 still holds for
   g < 1/361, a fortiori on the Budget window g ≤ 2/18977). -/
/-- **N18b** (md 1875–1900): the genuine §4 side condition `T₁ > 1`, from the strip regime
(this is what lets the call site populate the envelope field `T1_gt_one`). -/
theorem sec7_side_T1_gt_one :
    ∀ (P : Globals) (S : Scale P), ∀ c₀ Cu : ℝ,
      OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
      0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      1 < S.T₁ := by
  intro P S c₀ Cu D hbud hg hu hX24
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu.le (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu.le (by linarith)
  have key : (1:ℝ) < P.H ^ (1/2:ℝ) * S.x ^ (-3/2:ℝ) * P.G ^ (-1:ℝ) * S.Ω ^ (-1:ℝ) :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt (1/2) (-3/2) (-1) (-1)
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg, hu, huCu, huCu1])
  rw [OnStripAux.T1_mono P S]
  exact key

/-- Quantitative strip smallness: if the `X^{-7/100}`-deflated exponent is still positive
on the budget, the inverse monomial is `≤ 10⁻⁵⁰` (via `X^{7/100} = H^{7/20}G^{7/100}` and
the `X`-floor `X^{1/100} ≥ 2²⁴`, so `X^{7/100} ≥ 2¹⁶⁸ > 10⁵⁰`). -/
private theorem sec7_inv_small (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hXgt : 1 < P.X)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) (a b c d : ℝ)
    (hE : 0 < OnStripAux.ratioExp P.g P.u Cu (a - 7/20) b (c - 7/100) d) :
    1 / (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ≤ 1 / 10 ^ 50 := by
  have hH := P.H_pos; have hG := P.G_pos
  have key : (1:ℝ) < P.H ^ (a - 7/20) * S.x ^ b * P.G ^ (c - 7/100) * S.Ω ^ d :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt _ _ _ _ hE
  have hX7 : P.H ^ (7/20:ℝ) * P.G ^ (7/100:ℝ) = P.X ^ (7/100:ℝ) := by
    unfold Globals.H Globals.G
    rw [← Real.rpow_mul P.X_pos.le, ← Real.rpow_mul P.X_pos.le, ← Real.rpow_add P.X_pos]
    congr 1; ring
  have hbig : (10:ℝ) ^ 50 ≤ P.X ^ (7/100:ℝ) := by
    have h7 : P.X ^ (7/100:ℝ) = (P.X ^ (1/100:ℝ)) ^ (7:ℕ) := by
      rw [← Real.rpow_natCast (P.X ^ (1/100:ℝ)) 7, ← Real.rpow_mul P.X_pos.le]
      norm_num
    rw [h7]
    calc (10:ℝ) ^ 50 ≤ (16777216:ℝ) ^ (7:ℕ) := by norm_num
      _ ≤ (P.X ^ (1/100:ℝ)) ^ (7:ℕ) := pow_le_pow_left₀ (by norm_num) hX24 7
  have hsplit : P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d
      = (P.H ^ (a - 7/20) * S.x ^ b * P.G ^ (c - 7/100) * S.Ω ^ d)
          * (P.H ^ (7/20:ℝ) * P.G ^ (7/100:ℝ)) := by
    have h1 : P.H ^ a = P.H ^ (a - 7/20) * P.H ^ (7/20:ℝ) := by
      rw [← Real.rpow_add hH]; congr 1; ring
    have h2 : P.G ^ c = P.G ^ (c - 7/100) * P.G ^ (7/100:ℝ) := by
      rw [← Real.rpow_add hG]; congr 1; ring
    rw [h1, h2]; ring
  have hM : (10:ℝ) ^ 50 ≤ P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d := by
    calc (10:ℝ) ^ 50 ≤ P.X ^ (7/100:ℝ) := hbig
      _ = 1 * P.X ^ (7/100:ℝ) := (one_mul _).symm
      _ ≤ (P.H ^ (a - 7/20) * S.x ^ b * P.G ^ (c - 7/100) * S.Ω ^ d) * P.X ^ (7/100:ℝ) :=
          mul_le_mul_of_nonneg_right key.le (Real.rpow_pos_of_pos P.X_pos _).le
      _ = P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d := by rw [← hX7, ← hsplit]
  exact one_div_le_one_div_of_le (by norm_num) hM

private theorem sec7_nonzero_dyadic_window_bounds {P : Globals} {S : Scale P}
    {p q : ℕ} {r : ℝ}
    (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hr : r ∈ Set.Icc (p : ℝ) (q : ℝ)) :
    S.R / 72 ≤ r ∧ r ≤ 16 * S.R := by
  have hpqR : (p : ℝ) ≤ (q : ℝ) := le_trans hr.1 hr.2
  have hpq : p ≤ q := by exact_mod_cast hpqR
  have hpmem : (p : ℤ) ∈ Finset.Icc (p : ℤ) (q : ℤ) := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, by exact_mod_cast hpq⟩
  have hqmem : (q : ℤ) ∈ Finset.Icc (p : ℤ) (q : ℤ) := by
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast hpq, le_rfl⟩
  have hpwide := hwin hpmem
  have hqwide := hwin hqmem
  rw [Finset.mem_Icc] at hpwide hqwide
  have hpR : S.R / 72 ≤ (p : ℝ) :=
    le_trans (Int.le_ceil (S.R / 72)) (by exact_mod_cast hpwide.1)
  have hqR : (q : ℝ) ≤ 16 * S.R :=
    le_trans (by exact_mod_cast hqwide.2) (Int.floor_le (16 * S.R))
  exact ⟨le_trans hpR hr.1, le_trans hr.2 hqR⟩

private theorem sec7_nonzero_dyadic_window_mem_rWin {P : Globals} {S : Scale P} {W : ℝ}
    {p q : ℕ} {r : ℝ}
    (hW : 0 < W)
    (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hr : r ∈ Set.Icc (p : ℝ) (q : ℝ)) :
    r ∈ sec7_rWin S W := by
  have hb := sec7_nonzero_dyadic_window_bounds (S := S) hwin hr
  have hpad0 : 0 ≤ W + W ^ 2 + W ^ 4 := by
    have hW0 : 0 ≤ W := le_of_lt hW
    have hW2 : 0 ≤ W ^ 2 := sq_nonneg W
    have hW4 : 0 ≤ W ^ 4 := pow_nonneg hW0 4
    nlinarith
  simp only [sec7_rWin, Set.mem_Icc]
  constructor <;> nlinarith

private theorem sec7_nonzero_hsh {P : Globals} {S : Scale P} {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    24 * sec7_hSum h₁ h₂ h₃ * sec7_cWin ≤ S.R := by
  have hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R := sec7_hSum_R_small Env hbox
  calc 24 * sec7_hSum h₁ h₂ h₃ * sec7_cWin
      = sec7_hSum h₁ h₂ h₃ * 24000 := by norm_num [sec7_cWin]; ring
    _ ≤ sec7_hSum h₁ h₂ h₃ * 10 ^ 149 := by
        have hS3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
          sec7_hSum_ge3 hbox.1.1 hbox.2.1.1 hbox.2.2.1
        have hS0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by linarith
        gcongr
        norm_num
    _ ≤ S.R := hSR

private theorem sec7_nonzero_Pprod_le_W7 {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_Pprod h₁ h₂ h₃ ≤ W ^ 7 := by
  have hW : (1 : ℝ) ≤ W := sec7_W_ge_one hbox
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have a1 : (0 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.1.1)
  have a2 : (0 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.1.1)
  have a3 : (0 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.2.1)
  have h1 : (h₁ : ℝ) ≤ W := hbox.1.2
  have h2 : (h₂ : ℝ) ≤ W ^ 2 := hbox.2.1.2
  have h3 : (h₃ : ℝ) ≤ W ^ 4 := hbox.2.2.2
  unfold sec7_Pprod
  calc (h₁ : ℝ) * h₂ * h₃
      ≤ W * W ^ 2 * W ^ 4 := by
          gcongr
    _ = W ^ 7 := by ring

private theorem sec7_nonzero_Pprod_ge_one_of_box {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    (1 : ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
  have a1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hbox.1.1
  have a2 : (1 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hbox.2.1.1
  have a3 : (1 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hbox.2.2.1
  unfold sec7_Pprod
  have h12 : (1 : ℝ) ≤ (h₁ : ℝ) * h₂ := by nlinarith
  nlinarith

private theorem sec7_nonzero_Pprod_T3_R3_small {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ : ℤ} (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hX1 : 1 ≤ P.X) :
    sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) ≤ S.T₁ / sec7_envC := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hW : (1 : ℝ) ≤ W := sec7_W_ge_one hbox
  have hlog : (0:ℝ) ≤ Real.log P.X := Real.log_nonneg hX1
  have hP := sec7_nonzero_Pprod_le_W7 hbox
  have hW714 : W ^ 7 ≤ W ^ 14 := pow_le_pow_right₀ hW (by norm_num)
  have hPt : sec7_Pprod h₁ h₂ h₃ ≤ W ^ 14 := le_trans hP hW714
  have hM :
      sec7_envC * W ^ 14 ≤
        P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
    calc sec7_envC * W ^ 14
        ≤ sec7_envC * W ^ 14 * (1 + Real.log P.X) := by
            have h0 : 0 ≤ sec7_envC * W ^ 14 :=
              mul_nonneg sec7_envC_pos.le (pow_nonneg (le_trans zero_le_one hW) 14)
            exact le_mul_of_one_le_right h0 (by linarith)
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := Env.tc8
  have hMpos : 0 < P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΩ := S.Ω_pos
    have hx : 0 < S.x := by
      unfold Scale.x
      exact div_pos P.H_pos (pow_pos S.Δ_pos 2)
    exact mul_pos
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos hH _) (Real.rpow_pos_of_pos hx _))
        (pow_pos hG 2))
      (pow_pos hΩ 8)
  have hMT : (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) * S.T₃
      = S.R ^ 3 * S.T₁ := by
    rw [sec7_R3T1 P S, show P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8
          = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * (P.G ^ 2 * S.Ω ^ 8) from by ring,
        sec7_Hx_half]
    unfold Scale.T₃
    field_simp [S.Δ_pos.ne']
  have hmul :
      sec7_envC * sec7_Pprod h₁ h₂ h₃ * S.T₃ ≤ S.R ^ 3 * S.T₁ := by
    calc sec7_envC * sec7_Pprod h₁ h₂ h₃ * S.T₃
        ≤ sec7_envC * W ^ 14 * S.T₃ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hPt sec7_envC_pos.le) hT3.le
      _ ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) * S.T₃ := by
            gcongr
      _ = S.R ^ 3 * S.T₁ := hMT
  rw [le_div_iff₀ sec7_envC_pos]
  rw [show sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_envC =
      (sec7_Pprod h₁ h₂ h₃ * S.T₃ * sec7_envC) / S.R ^ 3 by
        ring]
  rw [div_le_iff₀ (pow_pos hR 3)]
  calc sec7_Pprod h₁ h₂ h₃ * S.T₃ * sec7_envC
      = sec7_envC * sec7_Pprod h₁ h₂ h₃ * S.T₃ := by ring
    _ ≤ S.R ^ 3 * S.T₁ := hmul
    _ = S.T₁ * S.R ^ 3 := by ring

private theorem sec7_nonzero_hSum_div_R_small {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ : ℤ} (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_hSum h₁ h₂ h₃ / S.R ≤ 1 / (10 : ℝ) ^ 149 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R := sec7_hSum_R_small Env hbox
  have hpow : 0 < (10 : ℝ) ^ 149 := by positivity
  rw [le_div_iff₀ hpow]
  have hdiv := div_le_div_of_nonneg_right hSR hR.le
  calc
    sec7_hSum h₁ h₂ h₃ / S.R * (10 : ℝ) ^ 149
        = (sec7_hSum h₁ h₂ h₃ * (10 : ℝ) ^ 149) / S.R := by ring
    _ ≤ S.R / S.R := hdiv
    _ = 1 := by field_simp [hR.ne']

private theorem sec7_nonzero_relErr_small {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ : ℤ} (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (c₀ Cu : ℝ) (D : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg : 0 ≤ P.g) (hu : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143 := by
  have hpow : 0 < (10 : ℝ) ^ 143 := by positivity
  rw [le_div_iff₀ hpow]
  exact sec7_relErr_le Env (sec7_W_ge_one hbox) D hbud hg hu hX24

private theorem sec7_nonzero_relErrF_small {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ : ℤ} (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (c₀ Cu : ℝ) (D : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg : 0 ≤ P.g) (hu : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    sec7_relErrF P S ≤ 1 / (10 : ℝ) ^ 143 := by
  have hpow : 0 < (10 : ℝ) ^ 143 := by positivity
  rw [le_div_iff₀ hpow]
  exact sec7_relErrF_le Env (sec7_W_ge_one hbox) D hbud hg hu hX24

private theorem Sec7MonExp.nonzero_Cstar_upper_tight {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) :
    |ME.Cstar| ≤ (21 : ℝ) := by
  rw [ME.Cstar_eq]
  have h1 := ME.c₁_window.2
  have h2 := ME.c₂_window.2
  have habs : |-(21 / 16) * ME.c₁ * ME.c₂| =
      (21 / 16 : ℝ) * |ME.c₁| * |ME.c₂| := by
    rw [abs_mul, abs_mul]
    norm_num
  rw [habs]
  nlinarith [abs_nonneg ME.c₁, abs_nonneg ME.c₂]

private theorem sec7_Bcoef_nonzero_upper {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃) (hρ₀abs : (|ρ₀| : ℝ) ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) :
    |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃| ≤
      4 * ((sec7_cCarry + sec7_cFib) *
          (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) +
        3 * sec7_cFib * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT2 : 0 < S.T₂ := sec7_T₂_pos S
  have hTR : 0 < S.T₁ / S.R := div_pos hT1 hR
  have hT2R : 0 < S.T₂ / S.R ^ 2 := by positivity
  have hh₁ : 1 ≤ h₁ := hbox.1.1
  have hh₂ : 1 ≤ h₂ := hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := hbox.2.2.1
  have a1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hh₁
  have a2 : (1 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hh₂
  have a3 : (1 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hh₃
  have hSv0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
    unfold sec7_hSum
    linarith
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_nonzero_Pprod_ge_one_of_box (W := W) hbox
    linarith
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hc1 : |ME.c₁| ≤ 4 := ME.c₁_window.2
  have hsum_abs :
      |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| ≤
        sec7_cFib * (sec7_hSum h₁ h₂ h₃ +
          3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2)) := by
    have htri :
        |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| ≤
        (h₁ : ℝ) * |(u₁ : ℝ) - ρ₁| + (h₂ : ℝ) * |(u₂ : ℝ) - ρ₂| +
          (h₃ : ℝ) * |(u₃ : ℝ) - ρ₃| := by
      calc
        |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
            (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)|
            ≤ |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁)| +
                |(h₂ : ℝ) * ((u₂ : ℝ) - ρ₂)| +
                |(h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| := by
              have h := abs_add_le ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) +
                (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂)) ((h₃ : ℝ) * ((u₃ : ℝ) - ρ₃))
              have h' := abs_add_le ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁))
                ((h₂ : ℝ) * ((u₂ : ℝ) - ρ₂))
              linarith
          _ = (h₁ : ℝ) * |(u₁ : ℝ) - ρ₁| + (h₂ : ℝ) * |(u₂ : ℝ) - ρ₂| +
                (h₃ : ℝ) * |(u₃ : ℝ) - ρ₃| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ (h₁ : ℝ)),
                abs_of_nonneg (by linarith : 0 ≤ (h₂ : ℝ)),
                abs_of_nonneg (by linarith : 0 ≤ (h₃ : ℝ))]
    calc
      |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)|
          ≤ (h₁ : ℝ) * |(u₁ : ℝ) - ρ₁| + (h₂ : ℝ) * |(u₂ : ℝ) - ρ₂| +
              (h₃ : ℝ) * |(u₃ : ℝ) - ρ₃| := htri
      _ ≤ (h₁ : ℝ) * (sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))) +
            (h₂ : ℝ) * (sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))) +
            (h₃ : ℝ) * (sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) := by
          gcongr
      _ = sec7_cFib * (sec7_hSum h₁ h₂ h₃ +
          3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2)) := by
          unfold sec7_hSum sec7_Pprod
          ring
  have hrho_abs : |(ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃| ≤
      sec7_cCarry * sec7_hSum h₁ h₂ h₃ := by
    rw [abs_mul, abs_of_nonneg hSv0]
    exact mul_le_mul_of_nonneg_right hρ₀abs hSv0
  have hinside :
      |((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃| ≤
        (sec7_cCarry + sec7_cFib) * sec7_hSum h₁ h₂ h₃ +
          3 * sec7_cFib * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2) := by
    have htri := abs_sub_le
      ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
        (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃))
      ((ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃) 0
    have htri' :
        |((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃| ≤
        |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| +
        |(ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃| := by
      have h := abs_add_le
        ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃))
        (-(ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃)
      simpa [sub_eq_add_neg, abs_mul] using h
    calc
      |((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃|
          ≤ |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
              (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| +
            |(ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃| := htri'
      _ ≤ sec7_cFib * (sec7_hSum h₁ h₂ h₃ +
            3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2)) +
          sec7_cCarry * sec7_hSum h₁ h₂ h₃ := by gcongr
      _ = (sec7_cCarry + sec7_cFib) * sec7_hSum h₁ h₂ h₃ +
          3 * sec7_cFib * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2) := by ring
  calc
    |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃|
        ≤ 4 * (S.T₁ / S.R) *
            ((sec7_cCarry + sec7_cFib) * sec7_hSum h₁ h₂ h₃ +
              3 * sec7_cFib * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2)) := by
        unfold Sec7MonExp.Bcoef
        have hmul :
            |ME.c₁ * (S.T₁ / S.R) *
              (((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
                (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃)| =
              |ME.c₁| * (S.T₁ / S.R) *
                |((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
                  (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃| := by
          rw [abs_mul, abs_mul, abs_of_pos hTR]
        rw [hmul]
        nlinarith [mul_le_mul_of_nonneg_right hinside hTR.le,
          mul_le_mul_of_nonneg_right hc1
            (mul_nonneg hTR.le
              (abs_nonneg (((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) +
                (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) + (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) -
                (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃)))]
    _ = 4 * ((sec7_cCarry + sec7_cFib) *
          (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) +
        3 * sec7_cFib * (sec7_Pprod h₁ h₂ h₃ * (S.T₁ * S.T₂ / S.R ^ 3))) := by ring
    _ = 4 * ((sec7_cCarry + sec7_cFib) *
          (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) +
        3 * sec7_cFib * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
        rw [sec7_T₁_mul_T₂ S]

private theorem sec7_nonzero_hSum_T1_R_small {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ : ℤ} (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) ≤ S.T₁ / (10 : ℝ) ^ 149 := by
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hSRdiv := sec7_nonzero_hSum_div_R_small Env hbox
  calc
    sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)
        = S.T₁ * (sec7_hSum h₁ h₂ h₃ / S.R) := by ring
    _ ≤ S.T₁ * (1 / (10 : ℝ) ^ 149) :=
        mul_le_mul_of_nonneg_left hSRdiv hT1.le
    _ = S.T₁ / (10 : ℝ) ^ 149 := by ring

private theorem sec7_Bcoef_nonzero_subordinate {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (Env : Sec7Envelope P S W) (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃) (hX1 : 1 ≤ P.X)
    (hρ₀abs : (|ρ₀| : ℝ) ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) :
    |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃| ≤ S.T₁ / (10 : ℝ) ^ 100 := by
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hB := sec7_Bcoef_nonzero_upper (ME := ME) hbox hρ₀abs hu₁ hu₂ hu₃
  have hA := sec7_nonzero_hSum_T1_R_small Env hbox
  have hC := sec7_nonzero_Pprod_T3_R3_small Env hbox hX1
  have hcf0 : 0 ≤ sec7_cCarry + sec7_cFib := by norm_num [sec7_cCarry, sec7_cFib]
  have h3fib0 : 0 ≤ 3 * sec7_cFib := by norm_num [sec7_cFib]
  calc
    |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃|
        ≤ 4 * ((sec7_cCarry + sec7_cFib) *
            (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) +
          3 * sec7_cFib * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := hB
    _ ≤ 4 * ((sec7_cCarry + sec7_cFib) * (S.T₁ / (10 : ℝ) ^ 149) +
          3 * sec7_cFib * (S.T₁ / sec7_envC)) := by
        gcongr
    _ ≤ S.T₁ / (10 : ℝ) ^ 100 := by
        norm_num [sec7_cCarry, sec7_cFib, sec7_envC]
        nlinarith [hT1.le]

private theorem sec7_Ccoef_nonzero_subordinate {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (Env : Sec7Envelope P S W) (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃) (hX1 : 1 ≤ P.X) :
    |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)| ≤
      S.T₁ / (10 : ℝ) ^ 100 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_nonzero_Pprod_ge_one_of_box (W := W) hbox
    linarith
  have hbase0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
  have hbase := sec7_nonzero_Pprod_T3_R3_small Env hbox hX1
  calc
    |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)|
        = |ME.Cstar| * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hPP0, abs_of_pos (div_pos hT3 (pow_pos hR 3))]
          ring
    _ ≤ 21 * (S.T₁ / sec7_envC) := by
          gcongr
          exact ME.nonzero_Cstar_upper_tight
    _ ≤ S.T₁ / (10 : ℝ) ^ 100 := by
          norm_num [sec7_envC]
          nlinarith [hT1.le]

private theorem sec7_errScale_nonzero_subordinate {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ ρ₀ : ℤ} (Env : Sec7Envelope P S W)
    (hbox : sec7_shiftBox W h₁ h₂ h₃) (hrel : sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143)
    (hrelF : sec7_relErrF P S ≤ 1 / (10 : ℝ) ^ 143)
    (hρ₀ne : ρ₀ ≠ 0) (hX1 : 1 ≤ P.X) :
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ ≤ S.T₁ / (10 : ℝ) ^ 100 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hrelF0 : 0 ≤ sec7_relErrF P S := (sec7_relErrF_pos P S).le
  have hrel1 : sec7_relErr P S ≤ 1 := by
    calc sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143 := hrel
      _ ≤ 1 := by norm_num
  have hrelF1 : sec7_relErrF P S ≤ 1 := by
    calc sec7_relErrF P S ≤ 1 / (10 : ℝ) ^ 143 := hrelF
      _ ≤ 1 := by norm_num
  have hA := sec7_nonzero_hSum_T1_R_small Env hbox
  have hSdiv := sec7_nonzero_hSum_div_R_small Env hbox
  have hSdiv1 : sec7_hSum h₁ h₂ h₃ / S.R ≤ 1 := by
    calc sec7_hSum h₁ h₂ h₃ / S.R ≤ 1 / (10 : ℝ) ^ 149 := hSdiv
      _ ≤ 1 := by norm_num
  have hC := sec7_nonzero_Pprod_T3_R3_small Env hbox hX1
  have hSv0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
    have hSv3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
      sec7_hSum_ge3 hbox.1.1 hbox.2.1.1 hbox.2.2.1
    linarith
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_nonzero_Pprod_ge_one_of_box (W := W) hbox
    linarith
  have hA0 : 0 ≤ sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) := by positivity
  have hC0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
  have hTrel :
      S.T₁ * sec7_relErr P S ≤ S.T₁ / (10 : ℝ) ^ 143 := by
    calc
      S.T₁ * sec7_relErr P S ≤ S.T₁ * (1 / (10 : ℝ) ^ 143) := by gcongr
      _ = S.T₁ / (10 : ℝ) ^ 143 := by ring
  have hTrelF :
      S.T₁ * sec7_relErrF P S ≤ S.T₁ / (10 : ℝ) ^ 143 := by
    calc
      S.T₁ * sec7_relErrF P S ≤ S.T₁ * (1 / (10 : ℝ) ^ 143) := by gcongr
      _ = S.T₁ / (10 : ℝ) ^ 143 := by ring
  have hACrel :
      (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * sec7_relErr P S
        ≤ 2 * (S.T₁ / (10 : ℝ) ^ 149) := by
    calc
      (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * sec7_relErr P S
          ≤ (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * 1 := by
            gcongr
      _ = sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by ring
      _ ≤ S.T₁ / (10 : ℝ) ^ 149 + S.T₁ / sec7_envC := add_le_add hA hC
      _ ≤ 2 * (S.T₁ / (10 : ℝ) ^ 149) := by
            norm_num [sec7_envC]
            nlinarith [hT1.le]
  have hACrelF :
      (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * sec7_relErrF P S
        ≤ 2 * (S.T₁ / (10 : ℝ) ^ 149) := by
    calc
      (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * sec7_relErrF P S
          ≤ (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * 1 := by
            gcongr
      _ = sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by ring
      _ ≤ S.T₁ / (10 : ℝ) ^ 149 + S.T₁ / sec7_envC := add_le_add hA hC
      _ ≤ 2 * (S.T₁ / (10 : ℝ) ^ 149) := by
            norm_num [sec7_envC]
            nlinarith [hT1.le]
  have hSq :
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 ≤
        S.T₁ / (10 : ℝ) ^ 149 := by
    calc
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2
          = (sec7_hSum h₁ h₂ h₃ / S.R) *
              (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) := by ring
      _ ≤ 1 * (S.T₁ / (10 : ℝ) ^ 149) := by
            gcongr
      _ = S.T₁ / (10 : ℝ) ^ 149 := by ring
  have hPC :
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4) ≤
        S.T₁ / (10 : ℝ) ^ 149 := by
    calc
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)
          = (sec7_hSum h₁ h₂ h₃ / S.R) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
      _ ≤ 1 * (S.T₁ / sec7_envC) := by
            gcongr
      _ ≤ S.T₁ / (10 : ℝ) ^ 149 := by
            norm_num [sec7_envC]
            nlinarith [hT1.le]
  have herr :
      sec7_errScale P S h₁ h₂ h₃ ρ₀ ≤ S.T₁ / (10 : ℝ) ^ 142 := by
    calc
      sec7_errScale P S h₁ h₂ h₃ ρ₀ =
          S.T₁ * sec7_relErrF P S +
            sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S +
            sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
            sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S +
            (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
            sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4) := by
            unfold sec7_errScale
            rw [if_neg hρ₀ne]
            ring
      _ ≤ S.T₁ / (10 : ℝ) ^ 143 + 2 * (S.T₁ / (10 : ℝ) ^ 149) +
            2 * (S.T₁ / (10 : ℝ) ^ 149) +
            S.T₁ / (10 : ℝ) ^ 149 + S.T₁ / (10 : ℝ) ^ 149 := by
            nlinarith
      _ ≤ S.T₁ / (10 : ℝ) ^ 142 := by
            norm_num
            nlinarith [hT1.le]
  calc
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀
        ≤ sec7_cErr * (S.T₁ / (10 : ℝ) ^ 142) := by
          exact mul_le_mul_of_nonneg_left herr sec7_cErr_pos.le
    _ ≤ S.T₁ / (10 : ℝ) ^ 100 := by
          norm_num [sec7_cErr]
          nlinarith [hT1.le]

private theorem sec7_nonzero_powMonD_dyadic_bound {R c α K t : ℝ} {k : ℕ}
    (hR : 0 < R) (hK : 1 ≤ K) (hαk : α - (k : ℝ) ≤ 0)
    (ht0 : 0 < t / R) (ht : 1 / K ≤ t / R) :
    |sec7_powMonD R c α k t| ≤
      |c| * |sec7_aprod α k| / R ^ k * K ^ ((k : ℝ) - α) := by
  have h := sec7_powMon_abs_le (R := R) (c := c * sec7_aprod α k / R ^ k)
    (α := α - k) (K := K) (t := t) hK hαk ht0 ht
  have habs : |c * sec7_aprod α k / R ^ k| = |c| * |sec7_aprod α k| / R ^ k := by
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hR k)]
  have hexp : -(α - (k : ℝ)) = (k : ℝ) - α := by ring
  rwa [habs, hexp] at h

private theorem sec7_nonzero_Bterm_two_small {P : Globals} {S : Scale P} {B r : ℝ}
    (hB : |B| ≤ S.T₁ / (10 : ℝ) ^ 100)
    (hrb : S.R / 72 ≤ r ∧ r ≤ 16 * S.R) :
    S.R ^ 2 * |sec7_powMonD S.R B (-(2 : ℝ)) 2 r| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrpos : 0 < r := by nlinarith
  have hyrpos : 0 < r / S.R := div_pos hrpos hR
  have hylo : (1 / 72 : ℝ) ≤ r / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  have hbd := sec7_nonzero_powMonD_dyadic_bound (R := S.R) (c := B) (α := (-(2 : ℝ)))
    (K := (72 : ℝ)) (k := 2) hR (by norm_num) (by norm_num) hyrpos hylo
  have hbd' :
      |sec7_powMonD S.R B (-(2 : ℝ)) 2 r| ≤ 6 * 72 ^ 4 * |B| / S.R ^ 2 := by
    calc
      |sec7_powMonD S.R B (-(2 : ℝ)) 2 r|
          ≤ |B| * |sec7_aprod (-(2 : ℝ)) 2| / S.R ^ 2 *
              (72 : ℝ) ^ (((2 : ℕ) : ℝ) - (-(2 : ℝ))) := hbd
      _ = 6 * 72 ^ 4 * |B| / S.R ^ 2 := by
            norm_num [sec7_aprod]
            ring
  calc
    S.R ^ 2 * |sec7_powMonD S.R B (-(2 : ℝ)) 2 r|
        ≤ S.R ^ 2 * (6 * 72 ^ 4 * |B| / S.R ^ 2) := by gcongr
    _ = 6 * 72 ^ 4 * |B| := by field_simp [hR.ne']
    _ ≤ 6 * 72 ^ 4 * (S.T₁ / (10 : ℝ) ^ 100) := by gcongr
    _ ≤ S.T₁ / (10 : ℝ) ^ 80 := by
          norm_num
          nlinarith [hT1.le]

private theorem sec7_nonzero_Cterm_two_small {P : Globals} {S : Scale P} {C r : ℝ}
    (hC : |C| ≤ S.T₁ / (10 : ℝ) ^ 100)
    (hrb : S.R / 72 ≤ r ∧ r ≤ 16 * S.R) :
    S.R ^ 2 * |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r| ≤
      S.T₁ / (10 : ℝ) ^ 80 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrpos : 0 < r := by nlinarith
  have hyrpos : 0 < r / S.R := div_pos hrpos hR
  have hylo : (1 / 72 : ℝ) ≤ r / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  have hbd := sec7_nonzero_powMonD_dyadic_bound (R := S.R) (c := C)
    (α := (-(13 : ℝ) / 4)) (K := (72 : ℝ)) (k := 2) hR (by norm_num)
    (by norm_num) hyrpos hylo
  have hpow : (72 : ℝ) ^ ((21 : ℝ) / 4) ≤ 72 ^ 6 := by
    have h72 : (1 : ℝ) ≤ 72 := by norm_num
    calc
      (72 : ℝ) ^ ((21 : ℝ) / 4) ≤ (72 : ℝ) ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h72 (by norm_num)
      _ = 72 ^ 6 := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbd' :
      |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r| ≤
        (221 / 16 : ℝ) * 72 ^ 6 * |C| / S.R ^ 2 := by
    calc
      |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r|
          ≤ |C| * |sec7_aprod (-(13 : ℝ) / 4) 2| / S.R ^ 2 *
              (72 : ℝ) ^ (((2 : ℕ) : ℝ) - (-(13 : ℝ) / 4)) := hbd
      _ = |C| * (221 / 16 : ℝ) / S.R ^ 2 * (72 : ℝ) ^ ((21 : ℝ) / 4) := by
            norm_num [sec7_aprod]
      _ ≤ |C| * (221 / 16 : ℝ) / S.R ^ 2 * 72 ^ 6 := by
            gcongr
      _ = (221 / 16 : ℝ) * 72 ^ 6 * |C| / S.R ^ 2 := by ring
  calc
    S.R ^ 2 * |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r|
        ≤ S.R ^ 2 * ((221 / 16 : ℝ) * 72 ^ 6 * |C| / S.R ^ 2) := by gcongr
    _ = (221 / 16 : ℝ) * 72 ^ 6 * |C| := by field_simp [hR.ne']
    _ ≤ (221 / 16 : ℝ) * 72 ^ 6 * (S.T₁ / (10 : ℝ) ^ 100) := by gcongr
    _ ≤ S.T₁ / (10 : ℝ) ^ 80 := by
          norm_num
          nlinarith [hT1.le]

private theorem sec7_nonzero_Bterm_two_small_wide {P : Globals} {S : Scale P} {B r : ℝ}
    (hB : |B| ≤ S.T₁ / (10 : ℝ) ^ 100)
    (hrb : S.R / 144 ≤ r ∧ r ≤ 40 * S.R) :
    S.R ^ 2 * |sec7_powMonD S.R B (-(2 : ℝ)) 2 r| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrpos : 0 < r := by nlinarith
  have hyrpos : 0 < r / S.R := div_pos hrpos hR
  have hylo : (1 / 144 : ℝ) ≤ r / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  have hbd := sec7_nonzero_powMonD_dyadic_bound (R := S.R) (c := B) (α := (-(2 : ℝ)))
    (K := (144 : ℝ)) (k := 2) hR (by norm_num) (by norm_num) hyrpos hylo
  have hbd' :
      |sec7_powMonD S.R B (-(2 : ℝ)) 2 r| ≤ 6 * 144 ^ 4 * |B| / S.R ^ 2 := by
    calc
      |sec7_powMonD S.R B (-(2 : ℝ)) 2 r|
          ≤ |B| * |sec7_aprod (-(2 : ℝ)) 2| / S.R ^ 2 *
              (144 : ℝ) ^ (((2 : ℕ) : ℝ) - (-(2 : ℝ))) := hbd
      _ = 6 * 144 ^ 4 * |B| / S.R ^ 2 := by
            norm_num [sec7_aprod]
            ring
  calc
    S.R ^ 2 * |sec7_powMonD S.R B (-(2 : ℝ)) 2 r|
        ≤ S.R ^ 2 * (6 * 144 ^ 4 * |B| / S.R ^ 2) := by gcongr
    _ = 6 * 144 ^ 4 * |B| := by field_simp [hR.ne']
    _ ≤ 6 * 144 ^ 4 * (S.T₁ / (10 : ℝ) ^ 100) := by gcongr
    _ ≤ S.T₁ / (10 : ℝ) ^ 80 := by
          norm_num
          nlinarith [hT1.le]

private theorem sec7_nonzero_Cterm_two_small_wide {P : Globals} {S : Scale P} {C r : ℝ}
    (hC : |C| ≤ S.T₁ / (10 : ℝ) ^ 100)
    (hrb : S.R / 144 ≤ r ∧ r ≤ 40 * S.R) :
    S.R ^ 2 * |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r| ≤
      S.T₁ / (10 : ℝ) ^ 80 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrpos : 0 < r := by nlinarith
  have hyrpos : 0 < r / S.R := div_pos hrpos hR
  have hylo : (1 / 144 : ℝ) ≤ r / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  have hbd := sec7_nonzero_powMonD_dyadic_bound (R := S.R) (c := C)
    (α := (-(13 : ℝ) / 4)) (K := (144 : ℝ)) (k := 2) hR (by norm_num)
    (by norm_num) hyrpos hylo
  have hpow : (144 : ℝ) ^ ((21 : ℝ) / 4) ≤ 144 ^ 6 := by
    have h144 : (1 : ℝ) ≤ 144 := by norm_num
    calc
      (144 : ℝ) ^ ((21 : ℝ) / 4) ≤ (144 : ℝ) ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h144 (by norm_num)
      _ = 144 ^ 6 := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbd' :
      |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r| ≤
        (221 / 16 : ℝ) * 144 ^ 6 * |C| / S.R ^ 2 := by
    calc
      |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r|
          ≤ |C| * |sec7_aprod (-(13 : ℝ) / 4) 2| / S.R ^ 2 *
              (144 : ℝ) ^ (((2 : ℕ) : ℝ) - (-(13 : ℝ) / 4)) := hbd
      _ = |C| * (221 / 16 : ℝ) / S.R ^ 2 * (144 : ℝ) ^ ((21 : ℝ) / 4) := by
            norm_num [sec7_aprod]
      _ ≤ |C| * (221 / 16 : ℝ) / S.R ^ 2 * 144 ^ 6 := by
            gcongr
      _ = (221 / 16 : ℝ) * 144 ^ 6 * |C| / S.R ^ 2 := by ring
  calc
    S.R ^ 2 * |sec7_powMonD S.R C (-(13 : ℝ) / 4) 2 r|
        ≤ S.R ^ 2 * ((221 / 16 : ℝ) * 144 ^ 6 * |C| / S.R ^ 2) := by gcongr
    _ = (221 / 16 : ℝ) * 144 ^ 6 * |C| := by field_simp [hR.ne']
    _ ≤ (221 / 16 : ℝ) * 144 ^ 6 * (S.T₁ / (10 : ℝ) ^ 100) := by gcongr
    _ ≤ S.T₁ / (10 : ℝ) ^ 80 := by
          norm_num
          nlinarith [hT1.le]

private theorem sec7_nonzero_main_scaled_eq {P : Globals} {S : Scale P} {c ρ r : ℝ}
    (hr : 0 < r) :
    S.R ^ 2 * |sec7_powMonD S.R (c * ρ * S.T₁) (-(1 : ℝ)) 2 r| =
      2 * |c| * |ρ| * S.T₁ * (r / S.R) ^ (-(3 : ℝ)) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hy : 0 < r / S.R := div_pos hr hR
  unfold sec7_powMonD sec7_powMon
  norm_num [sec7_aprod]
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hR 2), abs_of_pos hT1,
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hy]
  field_simp [hR.ne']

private theorem sec7_nonzero_rpow_neg_three_local {P : Globals} {S : Scale P} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (htr : t ≤ (101 / 100 : ℝ) * r) :
    (r / S.R) ^ (-(3 : ℝ)) ≤ (5 / 4 : ℝ) * (t / S.R) ^ (-(3 : ℝ)) := by
  have hR : 0 < S.R := sec7_R_pos S
  set x : ℝ := r / S.R with hxdef
  set y : ℝ := t / S.R with hydef
  have hxpos : 0 < x := by rw [hxdef]; exact div_pos hr hR
  have hypos : 0 < y := by rw [hydef]; exact div_pos ht hR
  have hyx : y ≤ (101 / 100 : ℝ) * x := by
    rw [hxdef, hydef]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right htr hR.le
  have hy3 : y ^ 3 ≤ ((101 / 100 : ℝ) * x) ^ 3 := pow_le_pow_left₀ hypos.le hyx 3
  have hy3' : y ^ 3 ≤ (5 / 4 : ℝ) * x ^ 3 := by
    have hc : ((101 / 100 : ℝ) ^ 3) ≤ (5 / 4 : ℝ) := by norm_num
    have hx3 : 0 ≤ x ^ 3 := pow_nonneg hxpos.le 3
    calc y ^ 3 ≤ ((101 / 100 : ℝ) * x) ^ 3 := hy3
      _ = ((101 / 100 : ℝ) ^ 3) * x ^ 3 := by ring
      _ ≤ (5 / 4 : ℝ) * x ^ 3 := mul_le_mul_of_nonneg_right hc hx3
  change x ^ (-(3 : ℝ)) ≤ (5 / 4 : ℝ) * y ^ (-(3 : ℝ))
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hypos.le]
  norm_num
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [ne_of_gt (pow_pos hxpos 3), ne_of_gt (pow_pos hypos 3)]
  nlinarith

private theorem sec7_nonzero_rpow_neg_three_factor5 {P : Globals} {S : Scale P} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (htr : t ≤ 5 * r) :
    (r / S.R) ^ (-(3 : ℝ)) ≤ 125 * (t / S.R) ^ (-(3 : ℝ)) := by
  have hR : 0 < S.R := sec7_R_pos S
  set x : ℝ := r / S.R with hxdef
  set y : ℝ := t / S.R with hydef
  have hxpos : 0 < x := by rw [hxdef]; exact div_pos hr hR
  have hypos : 0 < y := by rw [hydef]; exact div_pos ht hR
  have hyx : y ≤ 5 * x := by
    rw [hxdef, hydef]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right htr hR.le
  have hy3 : y ^ 3 ≤ (5 * x) ^ 3 := pow_le_pow_left₀ hypos.le hyx 3
  have hy3' : y ^ 3 ≤ 125 * x ^ 3 := by
    calc y ^ 3 ≤ (5 * x) ^ 3 := hy3
      _ = 125 * x ^ 3 := by ring
  change x ^ (-(3 : ℝ)) ≤ 125 * y ^ (-(3 : ℝ))
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hypos.le]
  norm_num
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [ne_of_gt (pow_pos hxpos 3), ne_of_gt (pow_pos hypos 3)]
  nlinarith

private theorem sec7_nonzero_Tq_band {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ t : ℝ} {ρ₀ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hρ₀ne : ρ₀ ≠ 0) (hρ₀abs : (|ρ₀| : ℝ) ≤ sec7_cCarry)
    (htb : S.R / 72 ≤ t ∧ t ≤ 16 * S.R) :
    S.T₁ / sec7_cBand ≤
        (3 / 4 : ℝ) * (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
          (t / S.R) ^ (-(3 : ℝ))) ∧
      (3 / 4 : ℝ) * (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
          (t / S.R) ^ (-(3 : ℝ))) ≤ sec7_cBand * S.T₁ := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have htpos : 0 < t := by nlinarith
  have hypos : 0 < t / S.R := div_pos htpos hR
  have hyle : t / S.R ≤ 16 := by
    rw [div_le_iff₀ hR]
    linarith
  have hylo : (1 / 72 : ℝ) ≤ t / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  have hpowlo : (16 : ℝ) ^ (-(3 : ℝ)) ≤ (t / S.R) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hypos hyle (by norm_num)
  have hpowhi : (t / S.R) ^ (-(3 : ℝ)) ≤ (72 : ℝ) ^ 3 := by
    have hraw : (t / S.R) ^ (-(3 : ℝ)) ≤ (1 / 72 : ℝ) ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 72) hylo (by norm_num)
    calc (t / S.R) ^ (-(3 : ℝ)) ≤ (1 / 72 : ℝ) ^ (-(3 : ℝ)) := hraw
      _ = (72 : ℝ) ^ 3 := by norm_num [Real.rpow_natCast]
  have hρlo : (1 : ℝ) ≤ |(ρ₀ : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |ρ₀| := Int.one_le_abs hρ₀ne
    rw [← Int.cast_abs]
    exact_mod_cast h1
  have hleft :
      (3 / 4 : ℝ) * (2 * (1 / 16 : ℝ) * 1 * S.T₁ * (16 : ℝ) ^ (-(3 : ℝ))) ≤
        (3 / 4 : ℝ) * (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
          (t / S.R) ^ (-(3 : ℝ))) := by
    gcongr
    exact ME.c₁_window.1
  have hright :
      (3 / 4 : ℝ) * (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
          (t / S.R) ^ (-(3 : ℝ))) ≤
        (3 / 4 : ℝ) * (2 * 4 * sec7_cCarry * S.T₁ * (72 : ℝ) ^ 3) := by
    have hpow0 : 0 ≤ (t / S.R) ^ (-(3 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hypos _)
    have hcoef :
        |ME.c₁| * |(ρ₀ : ℝ)| ≤ 4 * sec7_cCarry := by
      nlinarith [ME.c₁_window.2, hρ₀abs, abs_nonneg ME.c₁, abs_nonneg (ρ₀ : ℝ)]
    have hcoef0 : 0 ≤ 2 * 4 * sec7_cCarry * S.T₁ := by
      norm_num [sec7_cCarry]
      exact hT1.le
    have hxle :
        2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ ≤ 2 * 4 * sec7_cCarry * S.T₁ := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hT1.le]
    have hmain :
        2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
            (t / S.R) ^ (-(3 : ℝ))
          ≤ 2 * 4 * sec7_cCarry * S.T₁ * (72 : ℝ) ^ 3 := by
      exact mul_le_mul hxle hpowhi hpow0 hcoef0
    nlinarith
  constructor
  · calc
      S.T₁ / sec7_cBand
          ≤ (3 / 4 : ℝ) * (2 * (1 / 16 : ℝ) * 1 * S.T₁ * (16 : ℝ) ^ (-(3 : ℝ))) := by
            norm_num [sec7_cBand]
            nlinarith [hT1.le]
      _ ≤ (3 / 4 : ℝ) * (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
          (t / S.R) ^ (-(3 : ℝ))) := hleft
  · calc
      (3 / 4 : ℝ) * (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ *
          (t / S.R) ^ (-(3 : ℝ)))
          ≤ (3 / 4 : ℝ) * (2 * 4 * sec7_cCarry * S.T₁ * (72 : ℝ) ^ 3) := hright
      _ ≤ sec7_cBand * S.T₁ := by
            norm_num [sec7_cBand, sec7_cCarry]
            nlinarith [hT1.le]

private theorem sec7_nonzero_curvature_algebra {T Mr Phi Tail : ℝ}
    (hT0 : 0 ≤ T) (hT_Mr : (5 / 4 : ℝ) * T ≤ Mr)
    (hMr_T : Mr ≤ (5 / 3 : ℝ) * T) (hMr_le_phi_tail : Mr ≤ Phi + Tail)
    (hPhi_le_Mr_tail : Phi ≤ Mr + Tail) (htailT : Tail ≤ T / 4) :
    T ≤ Phi ∧ Phi ≤ 2 * T := by
  constructor <;> nlinarith

set_option maxHeartbeats 1600000 in
private theorem sec7_nonzero_piece_curvature {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ r ref : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (Env : Sec7Envelope P S W) (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hrel : sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143)
    (hrelF : sec7_relErrF P S ≤ 1 / (10 : ℝ) ^ 143)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) (hX1 : 1 ≤ P.X)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hρ₀ne : ρ₀ ≠ 0) (hρ₀abs : (|ρ₀| : ℝ) ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)))
    (hErr : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ m)
    (hrb : S.R / 72 ≤ r ∧ r ≤ 16 * S.R)
    (hrefb : S.R / 72 ≤ ref ∧ ref ≤ 16 * S.R) (hrWin : r ∈ sec7_rWin S W)
    (hrref : r ≤ ref) (hrefLocal : ref ≤ (101 / 100 : ℝ) * r) :
    let T := (3 / 4 : ℝ) *
      (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ)))
    T ≤ S.R ^ 2 *
        |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ∧
      S.R ^ 2 *
        |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤ 2 * T := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrpos : 0 < r := by nlinarith [hrb.1, hR]
  have hrefpos : 0 < ref := by nlinarith [hrefb.1, hR]
  let Phi2 : ℝ := iteratedDeriv 2
    (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r
  let A : ℝ := sec7_powMonD S.R (ME.c₁ * (ρ₀ : ℝ) * S.T₁) (-(1 : ℝ)) 2 r
  let B : ℝ := sec7_powMonD S.R (ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) 2 r
  let C : ℝ := sec7_powMonD S.R
    (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) 2 r
  let E : ℝ := iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r
  let Mr : ℝ := 2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (r / S.R) ^ (-(3 : ℝ))
  let Mref : ℝ := 2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
  let T : ℝ := (3 / 4 : ℝ) * Mref
  change T ≤ S.R ^ 2 * |Phi2| ∧ S.R ^ 2 * |Phi2| ≤ 2 * T
  have hTband : S.T₁ / sec7_cBand ≤ T ∧ T ≤ sec7_cBand * S.T₁ := by
    simpa [T, Mref] using sec7_nonzero_Tq_band (ME := ME) hρ₀ne hρ₀abs hrefb
  have hTpos : 0 < T := lt_of_lt_of_le (div_pos hT1 sec7_cBand_pos) hTband.1
  have hBcoef := sec7_Bcoef_nonzero_subordinate Env ME hbox hX1 hρ₀abs hu₁ hu₂ hu₃
  have hCcoef := sec7_Ccoef_nonzero_subordinate Env ME hbox hX1
  have hErrSub := sec7_errScale_nonzero_subordinate Env hbox hrel hrelF hρ₀ne hX1
  have hBterm : S.R ^ 2 * |B| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
    dsimp [B]
    exact sec7_nonzero_Bterm_two_small hBcoef hrb
  have hCterm : S.R ^ 2 * |C| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
    dsimp [C]
    exact sec7_nonzero_Cterm_two_small hCcoef hrb
  have hEraw := hErr 2 (by norm_num) r hrWin
  have hEterm : S.R ^ 2 * |E| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
    dsimp [E]
    calc
      S.R ^ 2 * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          ≤ S.R ^ 2 * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ 2) :=
            mul_le_mul_of_nonneg_left hEraw (sq_nonneg S.R)
      _ = sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ := by field_simp [hR.ne']
      _ ≤ S.T₁ / (10 : ℝ) ^ 100 := hErrSub
      _ ≤ S.T₁ / (10 : ℝ) ^ 80 := by
            norm_num
            nlinarith [hT1.le]
  have htail_abs : |B + C + E| ≤ |B| + |C| + |E| := by
    calc
      |B + C + E| ≤ |B + C| + |E| := abs_add_le _ _
      _ ≤ (|B| + |C|) + |E| := by nlinarith [abs_add_le B C]
      _ = |B| + |C| + |E| := by ring
  have htail : S.R ^ 2 * |B + C + E| ≤ S.T₁ / (10 : ℝ) ^ 70 := by
    have hmul := mul_le_mul_of_nonneg_left htail_abs (sq_nonneg S.R)
    calc
      S.R ^ 2 * |B + C + E| ≤ S.R ^ 2 * (|B| + |C| + |E|) := hmul
      _ = S.R ^ 2 * |B| + S.R ^ 2 * |C| + S.R ^ 2 * |E| := by ring
      _ ≤ S.T₁ / (10 : ℝ) ^ 80 + S.T₁ / (10 : ℝ) ^ 80 + S.T₁ / (10 : ℝ) ^ 80 := by
            nlinarith
      _ ≤ S.T₁ / (10 : ℝ) ^ 70 := by
            norm_num
            nlinarith [hT1.le]
  have htailT : S.R ^ 2 * |B + C + E| ≤ T / 4 := by
    have hconst : (1 / (10 : ℝ) ^ 70) ≤ 1 / (4 * sec7_cBand) := by
      norm_num [sec7_cBand]
    have hsmall : S.T₁ / (10 : ℝ) ^ 70 ≤ (S.T₁ / sec7_cBand) / 4 := by
      calc
        S.T₁ / (10 : ℝ) ^ 70 = S.T₁ * (1 / (10 : ℝ) ^ 70) := by ring
        _ ≤ S.T₁ * (1 / (4 * sec7_cBand)) :=
            mul_le_mul_of_nonneg_left hconst hT1.le
        _ = (S.T₁ / sec7_cBand) / 4 := by ring
    calc
      S.R ^ 2 * |B + C + E| ≤ S.T₁ / (10 : ℝ) ^ 70 := htail
      _ ≤ (S.T₁ / sec7_cBand) / 4 := hsmall
      _ ≤ T / 4 := by
            exact div_le_div_of_nonneg_right hTband.1 (by norm_num)
  have hcoef0 : 0 ≤ 2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg ME.c₁))
      (abs_nonneg (ρ₀ : ℝ))) hT1.le
  have hdiv_ref : r / S.R ≤ ref / S.R := div_le_div_of_nonneg_right hrref hR.le
  have hpow_ref_le_r : (ref / S.R) ^ (-(3 : ℝ)) ≤ (r / S.R) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hrpos hR) hdiv_ref (by norm_num)
  have hMref_le_Mr : Mref ≤ Mr := by
    have h := mul_le_mul_of_nonneg_left hpow_ref_le_r hcoef0
    simpa [Mref, Mr, mul_assoc] using h
  have hpow_local :=
    sec7_nonzero_rpow_neg_three_local (S := S) hrpos hrefpos hrefLocal
  have hMr_le_Mref : Mr ≤ (5 / 4 : ℝ) * Mref := by
    have h := mul_le_mul_of_nonneg_left hpow_local hcoef0
    dsimp [Mr, Mref] at h ⊢
    nlinarith
  have hA_scaled : S.R ^ 2 * |A| = Mr := by
    dsimp [A, Mr]
    exact sec7_nonzero_main_scaled_eq (S := S) (c := ME.c₁) (ρ := (ρ₀ : ℝ)) (r := r) hrpos
  have hh₁ : 1 ≤ h₁ := hbox.1.1
  have hh₂ : 1 ≤ h₂ := hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := hbox.2.2.1
  have hsh := sec7_nonzero_hsh Env hbox
  have hsplit := sec7_Phi_iteratedDeriv_two_eq_principal_add_Err ME hh₁ hh₂ hh₃
    hξ₁ hξ₂ hξ₃ Env.W_pos hpad hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r := r) hrWin
  have hp := sec7_principal_iteratedDeriv_eq ME Env.W_pos hpad ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2
    (by norm_num) r hrWin
  have hPhi_eq : Phi2 = A + B + C + E := by
    dsimp [Phi2]
    rw [hsplit, hp]
    dsimp [A, B, C, E, sec7_principalJet]
  have hA_le_phi_tail : |A| ≤ |Phi2| + |B + C + E| := by
    have hAeq : A = Phi2 + (-(B + C + E)) := by
      rw [hPhi_eq]
      ring
    calc
      |A| = |Phi2 + (-(B + C + E))| := by rw [hAeq]
      _ ≤ |Phi2| + |-(B + C + E)| := abs_add_le _ _
      _ = |Phi2| + |B + C + E| := by rw [abs_neg]
  have hPhi_le_A_tail : |Phi2| ≤ |A| + |B + C + E| := by
    calc
      |Phi2| = |A + (B + C + E)| := by
        rw [hPhi_eq]
        ring_nf
      _ ≤ |A| + |B + C + E| := abs_add_le _ _
  have hA_scaled_le : S.R ^ 2 * |A| ≤ S.R ^ 2 * |Phi2| + S.R ^ 2 * |B + C + E| := by
    have h := mul_le_mul_of_nonneg_left hA_le_phi_tail (sq_nonneg S.R)
    nlinarith
  have hPhi_scaled_le : S.R ^ 2 * |Phi2| ≤ S.R ^ 2 * |A| + S.R ^ 2 * |B + C + E| := by
    have h := mul_le_mul_of_nonneg_left hPhi_le_A_tail (sq_nonneg S.R)
    nlinarith
  have hTdef : T = (3 / 4 : ℝ) * Mref := rfl
  have hT_Mr : (5 / 4 : ℝ) * T ≤ Mr := by nlinarith [hMref_le_Mr, hTdef]
  have hMr_T : Mr ≤ (5 / 3 : ℝ) * T := by nlinarith [hMr_le_Mref, hTdef]
  have hMr_le_phi_tail : Mr ≤ S.R ^ 2 * |Phi2| + S.R ^ 2 * |B + C + E| := by
    calc
      Mr = S.R ^ 2 * |A| := hA_scaled.symm
      _ ≤ S.R ^ 2 * |Phi2| + S.R ^ 2 * |B + C + E| := hA_scaled_le
  have hPhi_le_Mr_tail : S.R ^ 2 * |Phi2| ≤ Mr + S.R ^ 2 * |B + C + E| := by
    calc
      S.R ^ 2 * |Phi2| ≤ S.R ^ 2 * |A| + S.R ^ 2 * |B + C + E| := hPhi_scaled_le
      _ = Mr + S.R ^ 2 * |B + C + E| := by rw [hA_scaled]
  exact sec7_nonzero_curvature_algebra hTpos.le hT_Mr hMr_T hMr_le_phi_tail
    hPhi_le_Mr_tail htailT

/- md 1837–68: "Split each fixed grouped fiber into absolutely many subintervals on which
   y = r/R ranges over an interval where the leading factor y⁻³ varies by at most a fixed
   constant. On such a piece I_q, choose a reference point y_q ≍ 1 and set
   T_{ρ,q} ≍ |ρ₀|T₁ ≍ T₁." -/
/-- **N17** (md 1837–68; AM-2): decomposition of a dyadic sub-window `[p,q]` of the wide
count range (`[p,q] ⊆ [⌈R/72⌉,⌊16R⌋]`, `q ≤ 2p`) into at most 100 pieces, on each of
which the curvature scale `T_q` is pinned (`R²|Φ₂| ∈ [T_q, 2T_q]` for
`Φ₂ = iteratedDeriv 2 (sec7_Phi …)`) and `T_q ≍ T₁`. -/
theorem sec7_nonzero_pieces :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 ≤ W →
    ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
    0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
    ∀ (a : ℤ) (Ph : Sec7Phase P S W a) (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ)
      (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃),
      sec7_jBand P S j → sec7_shiftBox W h₁ h₂ h₃ →
      6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288 →
      3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4) →
      |ξ₁| ≤ sec7_hSum h₁ h₂ h₃ → |ξ₂| ≤ sec7_hSum h₁ h₂ h₃ →
      |ξ₃| ≤ sec7_hSum h₁ h₂ h₃ →
    ∀ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ, ρ₀ ≠ 0 → (|ρ₀| : ℝ) ≤ sec7_cCarry →
      |(ρ₁ : ℝ)| ≤ sec7_cCarry → |(ρ₂ : ℝ)| ≤ sec7_cCarry → |(ρ₃ : ℝ)| ≤ sec7_cCarry →
      |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) →
      |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) →
      |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)) →
      (∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
        |iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
          sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ m) →
      ∀ p q : ℕ, Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋ →
        q ≤ 2 * p → p ≤ q →
      ∃ (K : ℕ) (pt : ℕ → ℝ) (Tq : ℕ → ℝ), 0 < K ∧ K ≤ 100 ∧
        pt 0 = (p : ℝ) ∧ pt K = (q : ℝ) ∧ (∀ i < K, pt i ≤ pt (i + 1)) ∧
        ∀ i < K,
          (S.T₁ / sec7_cBand ≤ Tq i ∧ Tq i ≤ sec7_cBand * S.T₁) ∧
          ∀ r ∈ Set.Icc (pt i) (pt (i + 1)),
            Tq i ≤ S.R ^ 2 *
                |iteratedDeriv 2
                  (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ∧
              S.R ^ 2 *
                |iteratedDeriv 2
                  (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤ 2 * Tq i := by
  intro P S W Env _hW c₀ Cu D hbud hg hu hX24
  intro a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ME _hj hbox hpad hshift hξ₁ hξ₂ hξ₃
  intro ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ₀ne hρ₀abs _hρ₁ _hρ₂ _hρ₃ hu₁ hu₂ hu₃ hErr
  intro p q hwin hdyad hpq
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hX1 : 1 ≤ P.X := hXgt.le
  have hrel := sec7_nonzero_relErr_small Env hbox c₀ Cu D hbud hg hu hX24
  have hrelF := sec7_nonzero_relErrF_small Env hbox c₀ Cu D hbud hg hu hX24
  let K : ℕ := 100
  let pt : ℕ → ℝ := fun i => (p : ℝ) + (i : ℝ) * (((q : ℝ) - (p : ℝ)) / 100)
  let Tq : ℕ → ℝ := fun i =>
    (3 / 4 : ℝ) *
      (2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (pt (i + 1) / S.R) ^ (-(3 : ℝ)))
  have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  have hstep_nonneg : 0 ≤ (((q : ℝ) - (p : ℝ)) / 100) :=
    div_nonneg (sub_nonneg.mpr hpqR) (by norm_num)
  have hpt_lower : ∀ n : ℕ, n ≤ 100 → (p : ℝ) ≤ pt n := by
    intro n _hn
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hmul0 : 0 ≤ (n : ℝ) * (((q : ℝ) - (p : ℝ)) / 100) :=
      mul_nonneg hn0 hstep_nonneg
    dsimp [pt]
    nlinarith
  have hpt_upper : ∀ n : ℕ, n ≤ 100 → pt n ≤ (q : ℝ) := by
    intro n hn
    have hnR : (n : ℝ) ≤ 100 := by exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_right hnR hstep_nonneg
    dsimp [pt] at hmul ⊢
    have h100 : (100 : ℝ) * (((q : ℝ) - (p : ℝ)) / 100) = (q : ℝ) - p := by ring
    nlinarith
  have hdyadR : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hdyad
  have hstep_le_p100 : (((q : ℝ) - (p : ℝ)) / 100) ≤ (p : ℝ) / 100 := by
    nlinarith
  refine ⟨K, pt, Tq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [K]
  · norm_num [K]
  · simp [pt]
  · simp [K, pt]
    ring
  · intro i _hi
    have hiR : (i : ℝ) ≤ (i + 1 : ℕ) := by exact_mod_cast Nat.le_succ i
    have hmul := mul_le_mul_of_nonneg_right hiR hstep_nonneg
    dsimp [pt]
    nlinarith
  · intro i hi
    have hi100 : i < 100 := by simpa [K] using hi
    have hi_le100 : i ≤ 100 := le_of_lt hi100
    have hisucc_le100 : i + 1 ≤ 100 := Nat.succ_le_of_lt hi100
    have hrefpq : pt (i + 1) ∈ Set.Icc (p : ℝ) (q : ℝ) :=
      ⟨hpt_lower (i + 1) hisucc_le100, hpt_upper (i + 1) hisucc_le100⟩
    have hrefb := sec7_nonzero_dyadic_window_bounds (S := S) hwin hrefpq
    constructor
    · simpa [Tq] using sec7_nonzero_Tq_band (ME := ME) hρ₀ne hρ₀abs hrefb
    · intro r hr
      have hrpq : r ∈ Set.Icc (p : ℝ) (q : ℝ) := by
        exact ⟨le_trans (hpt_lower i hi_le100) hr.1,
          le_trans hr.2 (hpt_upper (i + 1) hisucc_le100)⟩
      have hrb := sec7_nonzero_dyadic_window_bounds (S := S) hwin hrpq
      have hrWin := sec7_nonzero_dyadic_window_mem_rWin (S := S) (W := W) Env.W_pos hwin hrpq
      have hratio : pt (i + 1) ≤ (101 / 100 : ℝ) * r := by
        let step : ℝ := (((q : ℝ) - (p : ℝ)) / 100)
        have hstep_le_r100 : step ≤ r / 100 := by
          dsimp [step]
          nlinarith [hstep_le_p100, hrpq.1]
        have hstep_eq : pt (i + 1) = pt i + step := by
          have hsucc : (((i + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by
            norm_num
          dsimp [pt, step]
          rw [hsucc]
          ring
        calc
          pt (i + 1) = pt i + step := hstep_eq
          _ ≤ r + r / 100 := add_le_add hr.1 hstep_le_r100
          _ = (101 / 100 : ℝ) * r := by ring
      have hcurv := sec7_nonzero_piece_curvature Env ME hbox hrel hrelF hpad hshift hX1 hξ₁ hξ₂ hξ₃
        hρ₀ne hρ₀abs hu₁ hu₂ hu₃ hErr hrb hrefb hrWin hr.2 hratio
      simpa [Tq] using hcurv

/- md 1901–11: "and 0 < δ₁(h) < 1. The positivity is immediate. For the upper bound,
     δ₁(h) ≪ H^{-1/2}x^{-5/2}Ω^{-2} + H^{-3/2}x^{-1/2}G^{-1}Ω^{-1} + W⁶/(H^{1/2}x^{5/2}G³Ω⁷),
   so δ₁(h) < 1 follows from the ambient large-X inequalities and from the offset
   constraint W¹² ≪ H^{1/2}x^{5/2}G³Ω⁷ [envelope entry `off1`]."
   The parent (N8/N13) supplies the displayed three-term bound; constant `sec7_cD1`. -/
/-- **N18c** (md 1901–11): the side condition `δ₁(h) < 1`, from the three-term bound, the
strip regime, and the offset envelope entry `off1`. -/
theorem sec7_side_delta1_lt_one :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 ≤ W →
    ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
    0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
    ∀ δ₁ : ℝ,
      δ₁ ≤ sec7_cD1 *
        (1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2)
          + 1 / (P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω)
          + W ^ 6 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7)) →
      δ₁ < 1 := by
  intro P S W Env hW c₀ Cu D hbud hg hu hX24 δ₁ hδ
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu.le (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu.le (by linarith)
  -- term 1: `1/(H^{1/2}x^{5/2}Ω²) ≤ 10⁻⁵⁰` (deflated exponent margin ≈ 0.0237)
  have e1 : P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2
      = P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ (0:ℝ) * S.Ω ^ (2:ℝ) := by
    rw [Real.rpow_zero, mul_one, ← Real.rpow_natCast S.Ω 2]; norm_num
  have ht1 : 1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2) ≤ 1 / 10 ^ 50 := by
    rw [e1]
    exact sec7_inv_small P S c₀ Cu D hXgt hX24 _ _ _ _
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg, hu, huCu, huCu1])
  -- term 2: `1/(H^{3/2}x^{1/2}GΩ) ≤ 10⁻⁵⁰` (deflated exponent margin ≈ 0.2287)
  have e2 : P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω
      = P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (1:ℝ) * S.Ω ^ (1:ℝ) := by
    rw [Real.rpow_one, Real.rpow_one]
  have ht2 : 1 / (P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω) ≤ 1 / 10 ^ 50 := by
    rw [e2]
    exact sec7_inv_small P S c₀ Cu D hXgt hX24 _ _ _ _
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg, hu, huCu, huCu1])
  -- term 3: the offset entry `off1` (`envC·W¹² ≤ H^{1/2}x^{5/2}G³Ω⁷`) plus `W ≥ 1`
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hMpos : (0:ℝ) < P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7 := by
    positivity
  have ht3 : W ^ 6 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7)
      ≤ 1 / sec7_envC := by
    rw [div_le_div_iff₀ hMpos sec7_envC_pos]
    have hWp : W ^ 6 ≤ W ^ 12 := pow_le_pow_right₀ hW (by norm_num)
    nlinarith [Env.off1, hWp, sec7_envC_pos]
  -- assemble: `δ₁ ≤ cD1·(10⁻⁵⁰ + 10⁻⁵⁰ + 10⁻²⁰⁰) < 1`
  calc δ₁ ≤ sec7_cD1 * (1 / 10 ^ 50 + 1 / 10 ^ 50 + 1 / sec7_envC) :=
        le_trans hδ (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add ht1 ht2) ht3) sec7_cD1_pos.le)
    _ < 1 := by norm_num [sec7_cD1, sec7_envC]

private theorem sec7_nonzero_prop_window_bounds {P : Globals} {S : Scale P}
    {p q : ℕ} {r : ℝ}
    (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hpq : p ≤ q) (hr : r ∈ Set.Icc ((p : ℝ) / 2) (5 * (p : ℝ) / 2)) :
    S.R / 144 ≤ r ∧ r ≤ 40 * S.R := by
  have hpmem : (p : ℤ) ∈ Finset.Icc (p : ℤ) (q : ℤ) := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, by exact_mod_cast hpq⟩
  have hpwide := hwin hpmem
  rw [Finset.mem_Icc] at hpwide
  have hpR : S.R / 72 ≤ (p : ℝ) :=
    le_trans (Int.le_ceil (S.R / 72)) (by exact_mod_cast hpwide.1)
  have hpRhi : (p : ℝ) ≤ 16 * S.R :=
    le_trans (by exact_mod_cast hpwide.2) (Int.floor_le (16 * S.R))
  obtain ⟨hrl, hrr⟩ := hr
  constructor <;> nlinarith

private theorem sec7_nonzero_prop_window_mem_rWin {P : Globals} {S : Scale P} {W : ℝ}
    {p q : ℕ} {r : ℝ}
    (hcover : ∀ y : ℝ, S.R / 144 ≤ y → y ≤ 40 * S.R → y ∈ sec7_rWin S W)
    (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hpq : p ≤ q) (hr : r ∈ Set.Icc ((p : ℝ) / 2) (5 * (p : ℝ) / 2)) :
    r ∈ sec7_rWin S W := by
  have hb := sec7_nonzero_prop_window_bounds (S := S) hwin hpq hr
  exact hcover r hb.1 hb.2

private theorem sec7_nonzero_block_T_band {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ ref : ℝ} {ρ₀ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hρ₀ne : ρ₀ ≠ 0) (hρ₀abs : (|ρ₀| : ℝ) ≤ sec7_cCarry)
    (hrefb : 5 * S.R / 144 ≤ ref ∧ ref ≤ 40 * S.R) :
    S.T₁ / (1024000 : ℝ) ≤
        |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ)) ∧
      |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
        ≤ (10 : ℝ) ^ 11 * S.T₁ := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrefpos : 0 < ref := by nlinarith [hrefb.1, hR]
  have hypos : 0 < ref / S.R := div_pos hrefpos hR
  have hyle : ref / S.R ≤ 40 := by
    rw [div_le_iff₀ hR]
    linarith
  have hylo : (5 / 144 : ℝ) ≤ ref / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  have hpowlo : (40 : ℝ) ^ (-(3 : ℝ)) ≤ (ref / S.R) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hypos hyle (by norm_num)
  have hpowhi : (ref / S.R) ^ (-(3 : ℝ)) ≤ (144 / 5 : ℝ) ^ 3 := by
    have hraw : (ref / S.R) ^ (-(3 : ℝ)) ≤ (5 / 144 : ℝ) ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 5 / 144) hylo (by norm_num)
    calc (ref / S.R) ^ (-(3 : ℝ)) ≤ (5 / 144 : ℝ) ^ (-(3 : ℝ)) := hraw
      _ = (144 / 5 : ℝ) ^ 3 := by norm_num [Real.rpow_natCast]
  have hρlo : (1 : ℝ) ≤ |(ρ₀ : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |ρ₀| := Int.one_le_abs hρ₀ne
    rw [← Int.cast_abs]
    exact_mod_cast h1
  constructor
  · calc
      S.T₁ / (1024000 : ℝ)
          ≤ (1 / 16 : ℝ) * 1 * S.T₁ * (40 : ℝ) ^ (-(3 : ℝ)) := by
            norm_num
            nlinarith [hT1.le]
      _ ≤ |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ)) := by
            gcongr
            exact ME.c₁_window.1
  · have hpow0 : 0 ≤ (ref / S.R) ^ (-(3 : ℝ)) :=
      le_of_lt (Real.rpow_pos_of_pos hypos _)
    have hcoef :
        |ME.c₁| * |(ρ₀ : ℝ)| ≤ 4 * sec7_cCarry := by
      nlinarith [ME.c₁_window.2, hρ₀abs, abs_nonneg ME.c₁, abs_nonneg (ρ₀ : ℝ)]
    have hcoefT0 : 0 ≤ 4 * sec7_cCarry * S.T₁ := by
      norm_num [sec7_cCarry]
      exact hT1.le
    calc
      |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
          ≤ 4 * sec7_cCarry * S.T₁ * (144 / 5 : ℝ) ^ 3 := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right hcoef hT1.le) hpowhi hpow0
              hcoefT0
      _ ≤ (10 : ℝ) ^ 11 * S.T₁ := by
            norm_num [sec7_cCarry]
            nlinarith [hT1.le]

private theorem sec7_nonzero_block_curvature_algebra {T Mr Phi Tail : ℝ}
    (hT0 : 0 ≤ T) (h2T_Mr : 2 * T ≤ Mr) (hMr_250T : Mr ≤ 250 * T)
    (hMr_le_phi_tail : Mr ≤ Phi + Tail)
    (hPhi_le_Mr_tail : Phi ≤ Mr + Tail) (htailT : Tail ≤ T / 4) :
    T ≤ Phi ∧ Phi ≤ 256 * T := by
  constructor <;> nlinarith

set_option maxHeartbeats 1800000 in
private theorem sec7_nonzero_block_curvature {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ r ref : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (Env : Sec7Envelope P S W) (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hrel : sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143)
    (hrelF : sec7_relErrF P S ≤ 1 / (10 : ℝ) ^ 143)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) (hX1 : 1 ≤ P.X)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hρ₀ne : ρ₀ ≠ 0) (hρ₀abs : (|ρ₀| : ℝ) ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)))
    (hErr : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ m)
    (hrb : S.R / 144 ≤ r ∧ r ≤ 40 * S.R)
    (hrefb : 5 * S.R / 144 ≤ ref ∧ ref ≤ 40 * S.R) (hrWin : r ∈ sec7_rWin S W)
    (hrref : r ≤ ref) (hrefLocal : ref ≤ 5 * r) :
    let T := |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
    T ≤ S.R ^ 2 *
        |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ∧
      S.R ^ 2 *
        |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤ 256 * T := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hrpos : 0 < r := by nlinarith [hrb.1, hR]
  have hrefpos : 0 < ref := by nlinarith [hrefb.1, hR]
  let Phi2 : ℝ := iteratedDeriv 2
    (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r
  let A : ℝ := sec7_powMonD S.R (ME.c₁ * (ρ₀ : ℝ) * S.T₁) (-(1 : ℝ)) 2 r
  let B : ℝ := sec7_powMonD S.R (ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) 2 r
  let C : ℝ := sec7_powMonD S.R
    (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) 2 r
  let E : ℝ := iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r
  let Mr : ℝ := 2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (r / S.R) ^ (-(3 : ℝ))
  let Mref : ℝ := 2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
  let T : ℝ := |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
  change T ≤ S.R ^ 2 * |Phi2| ∧ S.R ^ 2 * |Phi2| ≤ 256 * T
  have hTband : S.T₁ / (1024000 : ℝ) ≤ T ∧ T ≤ (10 : ℝ) ^ 11 * S.T₁ := by
    simpa [T] using sec7_nonzero_block_T_band (ME := ME) hρ₀ne hρ₀abs hrefb
  have hTpos : 0 < T := lt_of_lt_of_le (div_pos hT1 (by norm_num)) hTband.1
  have hBcoef := sec7_Bcoef_nonzero_subordinate Env ME hbox hX1 hρ₀abs hu₁ hu₂ hu₃
  have hCcoef := sec7_Ccoef_nonzero_subordinate Env ME hbox hX1
  have hErrSub := sec7_errScale_nonzero_subordinate Env hbox hrel hrelF hρ₀ne hX1
  have hBterm : S.R ^ 2 * |B| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
    dsimp [B]
    exact sec7_nonzero_Bterm_two_small_wide hBcoef hrb
  have hCterm : S.R ^ 2 * |C| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
    dsimp [C]
    exact sec7_nonzero_Cterm_two_small_wide hCcoef hrb
  have hEraw := hErr 2 (by norm_num) r hrWin
  have hEterm : S.R ^ 2 * |E| ≤ S.T₁ / (10 : ℝ) ^ 80 := by
    dsimp [E]
    calc
      S.R ^ 2 * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          ≤ S.R ^ 2 * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ 2) :=
            mul_le_mul_of_nonneg_left hEraw (sq_nonneg S.R)
      _ = sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ := by field_simp [hR.ne']
      _ ≤ S.T₁ / (10 : ℝ) ^ 100 := hErrSub
      _ ≤ S.T₁ / (10 : ℝ) ^ 80 := by
            norm_num
            nlinarith [hT1.le]
  have htail_abs : |B + C + E| ≤ |B| + |C| + |E| := by
    calc
      |B + C + E| ≤ |B + C| + |E| := abs_add_le _ _
      _ ≤ (|B| + |C|) + |E| := by nlinarith [abs_add_le B C]
      _ = |B| + |C| + |E| := by ring
  have htail : S.R ^ 2 * |B + C + E| ≤ S.T₁ / (10 : ℝ) ^ 70 := by
    have hmul := mul_le_mul_of_nonneg_left htail_abs (sq_nonneg S.R)
    calc
      S.R ^ 2 * |B + C + E| ≤ S.R ^ 2 * (|B| + |C| + |E|) := hmul
      _ = S.R ^ 2 * |B| + S.R ^ 2 * |C| + S.R ^ 2 * |E| := by ring
      _ ≤ S.T₁ / (10 : ℝ) ^ 80 + S.T₁ / (10 : ℝ) ^ 80 + S.T₁ / (10 : ℝ) ^ 80 := by
            nlinarith
      _ ≤ S.T₁ / (10 : ℝ) ^ 70 := by
            norm_num
            nlinarith [hT1.le]
  have htailT : S.R ^ 2 * |B + C + E| ≤ T / 4 := by
    have hconst : (1 / (10 : ℝ) ^ 70) ≤ 1 / (4 * (1024000 : ℝ)) := by
      norm_num
    have hsmall : S.T₁ / (10 : ℝ) ^ 70 ≤ (S.T₁ / (1024000 : ℝ)) / 4 := by
      calc
        S.T₁ / (10 : ℝ) ^ 70 = S.T₁ * (1 / (10 : ℝ) ^ 70) := by ring
        _ ≤ S.T₁ * (1 / (4 * (1024000 : ℝ))) :=
            mul_le_mul_of_nonneg_left hconst hT1.le
        _ = (S.T₁ / (1024000 : ℝ)) / 4 := by ring
    calc
      S.R ^ 2 * |B + C + E| ≤ S.T₁ / (10 : ℝ) ^ 70 := htail
      _ ≤ (S.T₁ / (1024000 : ℝ)) / 4 := hsmall
      _ ≤ T / 4 := by
            exact div_le_div_of_nonneg_right hTband.1 (by norm_num)
  have hcoef0 : 0 ≤ 2 * |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg ME.c₁))
      (abs_nonneg (ρ₀ : ℝ))) hT1.le
  have hdiv_ref : r / S.R ≤ ref / S.R := div_le_div_of_nonneg_right hrref hR.le
  have hpow_ref_le_r : (ref / S.R) ^ (-(3 : ℝ)) ≤ (r / S.R) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hrpos hR) hdiv_ref (by norm_num)
  have hMref_le_Mr : Mref ≤ Mr := by
    have h := mul_le_mul_of_nonneg_left hpow_ref_le_r hcoef0
    simpa [Mref, Mr, mul_assoc] using h
  have hpow_local :=
    sec7_nonzero_rpow_neg_three_factor5 (S := S) hrpos hrefpos hrefLocal
  have hMr_le_Mref : Mr ≤ 125 * Mref := by
    have h := mul_le_mul_of_nonneg_left hpow_local hcoef0
    dsimp [Mr, Mref] at h ⊢
    nlinarith
  have hA_scaled : S.R ^ 2 * |A| = Mr := by
    dsimp [A, Mr]
    exact sec7_nonzero_main_scaled_eq (S := S) (c := ME.c₁) (ρ := (ρ₀ : ℝ)) (r := r) hrpos
  have hh₁ : 1 ≤ h₁ := hbox.1.1
  have hh₂ : 1 ≤ h₂ := hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := hbox.2.2.1
  have hsh := sec7_nonzero_hsh Env hbox
  have hsplit := sec7_Phi_iteratedDeriv_two_eq_principal_add_Err ME hh₁ hh₂ hh₃
    hξ₁ hξ₂ hξ₃ Env.W_pos hpad hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r := r) hrWin
  have hp := sec7_principal_iteratedDeriv_eq ME Env.W_pos hpad ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2
    (by norm_num) r hrWin
  have hPhi_eq : Phi2 = A + B + C + E := by
    dsimp [Phi2]
    rw [hsplit, hp]
    dsimp [A, B, C, E, sec7_principalJet]
  have hA_le_phi_tail : |A| ≤ |Phi2| + |B + C + E| := by
    have hAeq : A = Phi2 + (-(B + C + E)) := by
      rw [hPhi_eq]
      ring
    calc
      |A| = |Phi2 + (-(B + C + E))| := by rw [hAeq]
      _ ≤ |Phi2| + |-(B + C + E)| := abs_add_le _ _
      _ = |Phi2| + |B + C + E| := by rw [abs_neg]
  have hPhi_le_A_tail : |Phi2| ≤ |A| + |B + C + E| := by
    calc
      |Phi2| = |A + (B + C + E)| := by
        rw [hPhi_eq]
        ring_nf
      _ ≤ |A| + |B + C + E| := abs_add_le _ _
  have hA_scaled_le : S.R ^ 2 * |A| ≤ S.R ^ 2 * |Phi2| + S.R ^ 2 * |B + C + E| := by
    have h := mul_le_mul_of_nonneg_left hA_le_phi_tail (sq_nonneg S.R)
    nlinarith
  have hPhi_scaled_le : S.R ^ 2 * |Phi2| ≤ S.R ^ 2 * |A| + S.R ^ 2 * |B + C + E| := by
    have h := mul_le_mul_of_nonneg_left hPhi_le_A_tail (sq_nonneg S.R)
    nlinarith
  have hTdef : T = Mref / 2 := by dsimp [T, Mref]; ring
  have h2T_Mr : 2 * T ≤ Mr := by nlinarith [hMref_le_Mr, hTdef]
  have hMr_250T : Mr ≤ 250 * T := by nlinarith [hMr_le_Mref, hTdef]
  have hMr_le_phi_tail : Mr ≤ S.R ^ 2 * |Phi2| + S.R ^ 2 * |B + C + E| := by
    calc
      Mr = S.R ^ 2 * |A| := hA_scaled.symm
      _ ≤ S.R ^ 2 * |Phi2| + S.R ^ 2 * |B + C + E| := hA_scaled_le
  have hPhi_le_Mr_tail : S.R ^ 2 * |Phi2| ≤ Mr + S.R ^ 2 * |B + C + E| := by
    calc
      S.R ^ 2 * |Phi2| ≤ S.R ^ 2 * |A| + S.R ^ 2 * |B + C + E| := hPhi_scaled_le
      _ = Mr + S.R ^ 2 * |B + C + E| := by rw [hA_scaled]
  exact sec7_nonzero_block_curvature_algebra hTpos.le h2T_Mr hMr_250T hMr_le_phi_tail
    hPhi_le_Mr_tail htailT

private theorem sec7_one_add_logX_ge_ten (P : Globals)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    (10 : ℝ) ≤ 1 + Real.log P.X := by
  have hX0 : (0:ℝ) < P.X := P.X_pos
  have he2 : Real.exp 2 ≤ 16777216 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hl24 : (2:ℝ) ≤ Real.log 16777216 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr he2
  have hlX : (200:ℝ) ≤ Real.log P.X := by
    have hm : Real.log 16777216 ≤ Real.log (P.X ^ (1/100 : ℝ)) :=
      Real.log_le_log (by norm_num) hX24
    rw [Real.log_rpow hX0] at hm
    linarith
  linarith

private theorem sec7_T1_ge_pow50 (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg : 0 ≤ P.g) (hu : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    (10 : ℝ) ^ 50 ≤ S.T₁ := by
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu.le (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu.le (by linarith)
  have hinv : 1 / S.T₁ ≤ 1 / (10 : ℝ) ^ 50 := by
    rw [OnStripAux.T1_mono P S]
    exact sec7_inv_small P S c₀ Cu D hXgt hX24 (1/2) (-3/2) (-1) (-1)
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg, hu.le, huCu, huCu1])
  have hinv' : S.T₁⁻¹ ≤ ((10 : ℝ) ^ 50)⁻¹ := by
    simpa [one_div] using hinv
  exact (inv_le_inv₀ (sec7_T₁_pos S) (by norm_num : (0:ℝ) < (10 : ℝ) ^ 50)).mp hinv'

private theorem sec7_R_le_X (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg : 0 ≤ P.g) (hu : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    S.R ≤ P.X := by
  have hXgt : 1 < P.X := by
    by_contra h
    have hle : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le hle (by norm_num)
    linarith
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu.le (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu.le (by linarith)
  have hmono : (1:ℝ) <
      P.H ^ ((9:ℝ)/2) * S.x ^ (-(1:ℝ)/2) * P.G ^ (0:ℝ) * S.Ω ^ (-(3:ℝ)) :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt ((9:ℝ)/2) (-(1:ℝ)/2) (0:ℝ) (-(3:ℝ))
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg, hu.le, huCu, huCu1])
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hRpos := sec7_R_pos S
  have hXeq : P.X = P.H ^ (5:ℝ) * P.G := by
    unfold Globals.H Globals.G
    rw [← Real.rpow_mul P.X_pos.le, ← Real.rpow_add P.X_pos]
    rw [show ((1 - P.g) / 5) * (5:ℝ) + P.g = (1:ℝ) by ring, Real.rpow_one]
  have hprod :
      (P.H ^ ((9:ℝ)/2) * S.x ^ (-(1:ℝ)/2) * P.G ^ (0:ℝ) * S.Ω ^ (-(3:ℝ))) * S.R
        = P.X := by
    rw [OnStripAux.R_mono P S, hXeq, Real.rpow_zero, Real.rpow_one]
    calc
      P.H ^ ((9:ℝ) / 2) * S.x ^ (-(1:ℝ) / 2) * 1 * S.Ω ^ (-(3:ℝ)) *
          (P.H ^ (1 / 2 : ℝ) * S.x ^ (1 / 2 : ℝ) * P.G * S.Ω ^ (3:ℝ))
          = (P.H ^ ((9:ℝ) / 2) * P.H ^ (1 / 2 : ℝ)) *
              (S.x ^ (-(1:ℝ) / 2) * S.x ^ (1 / 2 : ℝ)) *
              P.G * (S.Ω ^ (-(3:ℝ)) * S.Ω ^ (3:ℝ)) := by ring
      _ = P.H ^ (5:ℝ) * P.G := by
          rw [← Real.rpow_add hH, ← Real.rpow_add hx, ← Real.rpow_add hΩ]
          norm_num [Real.rpow_natCast]
  calc
    S.R = 1 * S.R := by ring
    _ ≤ (P.H ^ ((9:ℝ)/2) * S.x ^ (-(1:ℝ)/2) * P.G ^ (0:ℝ) * S.Ω ^ (-(3:ℝ))) * S.R :=
        mul_le_mul_of_nonneg_right hmono.le hRpos.le
    _ = P.X := hprod

private theorem sec7_engine_cube_bound {N R T T₁ lam : ℝ}
    (hN0 : 0 ≤ N) (hR : 0 < R) (hT0 : 0 ≤ T) (hT₁ : 0 < T₁)
    (hNle : N ≤ 16 * R) (hTle : T ≤ (10 : ℝ) ^ 11 * T₁)
    (hlam : lam = T / R ^ 2) :
    N * lam ^ (1/3 : ℝ) ≤ (80000 : ℝ) * (R * T₁) ^ (1/3 : ℝ) := by
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hRT0 : 0 ≤ R * T₁ := by positivity
  refine le_of_pow_le_pow_left₀ (n := 3)
    (a := N * lam ^ (1/3 : ℝ)) (b := (80000 : ℝ) * (R * T₁) ^ (1/3 : ℝ))
    (by norm_num) (by positivity) ?_
  have hlam13 : (lam ^ (1/3 : ℝ)) ^ 3 = lam := by
    rw [← Real.rpow_natCast (lam ^ (1/3 : ℝ)) 3, ← Real.rpow_mul hlam0]
    norm_num
  have hRT13 : ((R * T₁) ^ (1/3 : ℝ)) ^ 3 = R * T₁ := by
    rw [← Real.rpow_natCast ((R * T₁) ^ (1/3 : ℝ)) 3, ← Real.rpow_mul hRT0]
    norm_num
  have hN3 : N ^ 3 ≤ (16 * R) ^ 3 := pow_le_pow_left₀ hN0 hNle 3
  have hN3T : N ^ 3 * T ≤ (16 * R) ^ 3 * ((10 : ℝ) ^ 11 * T₁) := by
    exact mul_le_mul hN3 hTle hT0 (pow_nonneg (by positivity : (0:ℝ) ≤ 16 * R) 3)
  rw [mul_pow, hlam13, mul_pow, hRT13, hlam]
  field_simp [hR.ne']
  nlinarith [hN3T, hR.le, hT₁.le]

private theorem sec7_engine_sqrt_bound {R T T₁ lam δ : ℝ}
    (hR : 0 < R) (hT₁ : 0 < T₁) (hδ : 0 < δ)
    (hTlo : T₁ / (1024000 : ℝ) ≤ T) (hlam : lam = T / R ^ 2) :
    Real.sqrt (δ / lam) ≤ (1024 : ℝ) * R * Real.sqrt (δ / T₁) := by
  have hTpos : 0 < T := lt_of_lt_of_le (div_pos hT₁ (by norm_num)) hTlo
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hratio : δ / lam ≤ (1024 : ℝ) ^ 2 * (R ^ 2 * (δ / T₁)) := by
    rw [hlam]
    rw [div_div_eq_mul_div]
    field_simp [hTpos.ne', hT₁.ne']
    nlinarith [hTlo, hδ.le, sq_nonneg R]
  calc
    Real.sqrt (δ / lam) ≤ Real.sqrt ((1024 : ℝ) ^ 2 * (R ^ 2 * (δ / T₁))) :=
        Real.sqrt_le_sqrt hratio
    _ = (1024 : ℝ) * R * Real.sqrt (δ / T₁) := by
        rw [Real.sqrt_mul (sq_nonneg (1024 : ℝ)),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1024),
          Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]
        ring

private theorem sec7_engine_sqrt_le_N {N lam δ : ℝ}
    (hN0 : 0 ≤ N) (hlam : 0 < lam) (hδlt : δ < 1)
    (hfloor : 1 ≤ N ^ 2 * lam) :
    Real.sqrt (δ / lam) ≤ N := by
  refine Real.sqrt_le_iff.mpr ⟨hN0, ?_⟩
  have hδle : δ ≤ 1 := hδlt.le
  have hδdiv : δ / lam ≤ 1 / lam := div_le_div_of_nonneg_right hδle hlam.le
  have hinvle : 1 / lam ≤ N ^ 2 := by
    rw [div_le_iff₀ hlam]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor
  exact le_trans hδdiv hinvle

private theorem sec7_engine_log_bound {P : Globals} {S : Scale P} {N lam δ : ℝ}
    (hN0 : 0 ≤ N) (hNle : N ≤ 16 * S.R) (hRleX : S.R ≤ P.X)
    (hX1 : 1 ≤ P.X) (hlam : 0 < lam) (hδlt : δ < 1)
    (hfloor : 1 ≤ N ^ 2 * lam) :
    Real.log (2 + Real.sqrt (δ / lam)) ≤ 5 * (1 + Real.log P.X) := by
  have hsN := sec7_engine_sqrt_le_N hN0 hlam hδlt hfloor
  have hargpos : 0 < 2 + Real.sqrt (δ / lam) := by positivity
  have hargle : 2 + Real.sqrt (δ / lam) ≤ 18 * P.X := by
    nlinarith [hsN, hNle, hRleX, hX1]
  have hlogle : Real.log (2 + Real.sqrt (δ / lam)) ≤ Real.log (18 * P.X) :=
    Real.log_le_log hargpos hargle
  have hlogmul : Real.log (18 * P.X) = Real.log (18 : ℝ) + Real.log P.X := by
    rw [Real.log_mul (by norm_num) P.X_pos.ne']
  have hlog18 : Real.log (18 : ℝ) ≤ 4 := by
    have he1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : (5 / 2 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5 / 2) he1 4
    have hexp4 : (Real.exp 1) ^ 4 = Real.exp 4 := by
      rw [show (4:ℝ) = 1 + 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    have he4 : (18 : ℝ) ≤ Real.exp 4 := by
      norm_num at hpow ⊢
      rw [← hexp4]
      nlinarith
    exact (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 18)).mpr he4
  have hlogX0 : 0 ≤ Real.log P.X := Real.log_nonneg hX1
  calc
    Real.log (2 + Real.sqrt (δ / lam)) ≤ Real.log (18 * P.X) := hlogle
    _ = Real.log (18 : ℝ) + Real.log P.X := hlogmul
    _ ≤ 5 * (1 + Real.log P.X) := by nlinarith

private theorem sec7_engine_terms_absorb {P : Globals} {S : Scale P} {N T T₁ lam δ : ℝ}
    (hN0 : 0 ≤ N) (hR : 0 < S.R) (hT0 : 0 ≤ T) (hT₁ : 0 < T₁)
    (hδ : 0 < δ) (hδlt : δ < 1) (hNle : N ≤ 16 * S.R)
    (hTlo : T₁ / (1024000 : ℝ) ≤ T) (hTle : T ≤ (10 : ℝ) ^ 11 * T₁)
    (hlamdef : lam = T / S.R ^ 2) (hfloor : 1 ≤ N ^ 2 * lam)
    (hRleX : S.R ≤ P.X) (hX1 : 1 ≤ P.X)
    (hL10 : (10 : ℝ) ≤ 1 + Real.log P.X) :
    109159296 * (N * lam ^ (1/3 : ℝ) + N * δ
        + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1)
      ≤ sec7_cN19 * (1 + Real.log P.X)
        * ((S.R * T₁) ^ (1/3 : ℝ) + S.R * δ + S.R * Real.sqrt (δ / T₁) + 1) := by
  have hlampos : 0 < lam := by
    rw [hlamdef]
    have hTpos : 0 < T := lt_of_lt_of_le (div_pos hT₁ (by norm_num)) hTlo
    positivity
  have hcube := sec7_engine_cube_bound hN0 hR hT0 hT₁ hNle hTle hlamdef
  have hdelta : N * δ ≤ 16 * (S.R * δ) := by
    have := mul_le_mul_of_nonneg_right hNle hδ.le
    nlinarith
  have hsqrt := sec7_engine_sqrt_bound hR hT₁ hδ hTlo hlamdef
  have hlog := sec7_engine_log_bound hN0 hNle hRleX hX1 hlampos hδlt hfloor
  have hlog_nonneg : 0 ≤ Real.log (2 + Real.sqrt (δ / lam)) := by
    apply Real.log_nonneg
    have hs := Real.sqrt_nonneg (δ / lam)
    linarith
  have hslog :
      Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam))
        ≤ 5120 * ((1 + Real.log P.X) * (S.R * Real.sqrt (δ / T₁))) := by
    have hRhsSqrt : 0 ≤ (1024 : ℝ) * S.R * Real.sqrt (δ / T₁) := by positivity
    have hmul := mul_le_mul hsqrt hlog hlog_nonneg hRhsSqrt
    nlinarith [hmul]
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hcube0 : 0 ≤ (S.R * T₁) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hdelta0 : 0 ≤ S.R * δ := by positivity
  have hsqrt0 : 0 ≤ S.R * Real.sqrt (δ / T₁) := by positivity
  have hengine0 : 0 ≤ N * lam ^ (1/3 : ℝ) + N * δ
        + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1 := by
    have hNl0 : 0 ≤ N * lam ^ (1/3 : ℝ) := by positivity
    have hNd0 : 0 ≤ N * δ := by positivity
    have hslog0 : 0 ≤ Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) :=
      mul_nonneg (Real.sqrt_nonneg _) hlog_nonneg
    nlinarith
  norm_num [sec7_cN19]
  nlinarith [hcube, hdelta, hslog, hL10, hL0, hcube0, hdelta0, hsqrt0, hengine0]

/- md 1911–22: "Therefore the hypotheses of Proposition 4.3 are satisfied on each local
   piece with N = R, T = T_{ρ,q}, and tolerance δ₁(h). Summing over the absolutely many
   pieces and using T_{ρ,q} ≍ T₁ gives, up to a harmless logarithm,
     #{r in the fixed fiber : ‖Φ_{ρ,u}(r)‖ ≪ δ₁(h)}
        ≪ (RT₁)^{1/3} + Rδ₁(h) + R√(δ₁(h)/T₁) + 1.            (7.8)
   The logarithm in Proposition 4.3 is X^{o(1)} in the present range and is absorbed by
   shrinking the absolute constant c in the W-constraints."
   TRAP-2: the in-tree Prop 4.3 (`Geometry.nearCurve_count`, Geometry/NearCurve.lean:25)
   carries `log(2 + N√(δ/T))`; here it is kept as an explicit `(1 + log X)` factor in the
   conclusion, absorbed by the harvest N22 against the strip's X-slack. -/
set_option maxHeartbeats 3000000 in
/-- **N19** (md 1911–22; AM-2: counted on a dyadic sub-window `[p,q] ⊆ [⌈R/72⌉,⌊16R⌋]`,
`q ≤ 2p` — the engine interface): the local-Prop-4.3 fiber count (7.8) for the `ρ₀ ≠ 0`
branch, with the Prop 4.3 logarithm kept as a `(1 + log X)` factor. Hypotheses: side conditions
(N18), the N17 piece data via the same parent inputs (the N9 bundle `ME`, the N11
conclusion `hErr` verbatim, the N7 carry/fiber sizes), and `C²`-regularity of the phase
`sec7_Phi` (the `Sec7ZeroHyp.hcd` shape; concrete §3 call site). -/
theorem sec7_nonzero_count_78 :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 < W →
    ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
    0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
    ∀ (a : ℤ) (Ph : Sec7Phase P S W a) (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ)
      (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃),
      sec7_jBand P S j → sec7_shiftBox W h₁ h₂ h₃ →
      6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288 →
      3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4) →
      |ξ₁| ≤ sec7_hSum h₁ h₂ h₃ → |ξ₂| ≤ sec7_hSum h₁ h₂ h₃ →
      |ξ₃| ≤ sec7_hSum h₁ h₂ h₃ →
    ∀ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ, ρ₀ ≠ 0 → (|ρ₀| : ℝ) ≤ sec7_cCarry →
      |(ρ₁ : ℝ)| ≤ sec7_cCarry → |(ρ₂ : ℝ)| ≤ sec7_cCarry → |(ρ₃ : ℝ)| ≤ sec7_cCarry →
      |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) →
      |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) →
      |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)) →
      (∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
        |iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
          sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ m) →
      ContDiff ℝ 2 (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) →
      -- AM-2: dyadic sub-window of the wide count range
      ∀ p q : ℕ, Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋ →
        q ≤ 2 * p →
      (∀ y : ℝ, S.R / 144 ≤ y → y ≤ 40 * S.R → y ∈ sec7_rWin S W) →
      ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 →
        (((Finset.Icc (p : ℤ) (q : ℤ)).filter
            (fun r : ℤ => distInt
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ)) ≤ δ₁)).card : ℝ)
          ≤ sec7_cN19 * (1 + Real.log P.X)
            * ((S.R * S.T₁) ^ ((1:ℝ)/3) + S.R * δ₁
                + S.R * Real.sqrt (δ₁ / S.T₁) + 1) := by
  intro P S W Env _hW c₀ Cu D hbud hg hu hX24
  intro a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ME _hj hbox hpad hshift hξ₁ hξ₂ hξ₃
  intro ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ₀ne hρ₀abs _hρ₁ _hρ₂ _hρ₃ hu₁ hu₂ hu₃ hErr hcd
  intro p q hwin hdyad hcover δ₁ hδpos hδlt
  have hrel := sec7_nonzero_relErr_small Env hbox c₀ Cu D hbud hg hu hX24
  have hrelF := sec7_nonzero_relErrF_small Env hbox c₀ Cu D hbud hg hu hX24
  let f : ℝ → ℝ :=
    sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃
  by_cases hpq : p ≤ q
  · let ref : ℝ := 5 * (p : ℝ) / 2
    let T : ℝ := |ME.c₁| * |(ρ₀ : ℝ)| * S.T₁ * (ref / S.R) ^ (-(3 : ℝ))
    let lam : ℝ := T / S.R ^ 2
    have hR : 0 < S.R := sec7_R_pos S
    have hT1 : 0 < S.T₁ := sec7_T₁_pos S
    have hpmem : (p : ℤ) ∈ Finset.Icc (p : ℤ) (q : ℤ) := by
      rw [Finset.mem_Icc]
      exact ⟨le_rfl, by exact_mod_cast hpq⟩
    have hpwide := hwin hpmem
    rw [Finset.mem_Icc] at hpwide
    have hpRlo : S.R / 72 ≤ (p : ℝ) :=
      le_trans (Int.le_ceil (S.R / 72)) (by exact_mod_cast hpwide.1)
    have hpRhi : (p : ℝ) ≤ 16 * S.R :=
      le_trans (by exact_mod_cast hpwide.2) (Int.floor_le (16 * S.R))
    have hp_pos : 0 < (p : ℝ) := by nlinarith [hpRlo, hR]
    have hp_nonneg : 0 ≤ (p : ℝ) := hp_pos.le
    have hrefb : 5 * S.R / 144 ≤ ref ∧ ref ≤ 40 * S.R := by
      dsimp [ref]
      constructor <;> nlinarith
    have hTband : S.T₁ / (1024000 : ℝ) ≤ T ∧ T ≤ (10 : ℝ) ^ 11 * S.T₁ := by
      dsimp [T]
      simpa using sec7_nonzero_block_T_band (ME := ME) hρ₀ne hρ₀abs hrefb
    have hTpos : 0 < T := lt_of_lt_of_le (div_pos hT1 (by norm_num)) hTband.1
    have hT0 : 0 ≤ T := hTpos.le
    have hlampos : 0 < lam := by
      dsimp [lam]
      positivity
    have hT1ge := sec7_T1_ge_pow50 P S c₀ Cu D hbud hg hu hX24
    have hTge72 : (72 : ℝ) ^ 2 ≤ T := by
      calc
        (72 : ℝ) ^ 2 ≤ S.T₁ / (1024000 : ℝ) := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1024000)]
          norm_num
          nlinarith [hT1ge]
        _ ≤ T := hTband.1
    have hp_div : (1 / 72 : ℝ) ≤ (p : ℝ) / S.R := by
      rw [le_div_iff₀ hR]
      nlinarith
    have hp_div_sq : (1 / 72 : ℝ) ^ 2 ≤ ((p : ℝ) / S.R) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 72) hp_div 2
    have hfloor : 1 ≤ (p : ℝ) ^ 2 * lam := by
      have hmul := mul_le_mul hp_div_sq hTge72
        (by positivity : 0 ≤ (72 : ℝ) ^ 2)
        (sq_nonneg ((p : ℝ) / S.R))
      have hscale : 1 ≤ ((p : ℝ) / S.R) ^ 2 * T := by
        norm_num at hmul
        nlinarith
      change 1 ≤ (p : ℝ) ^ 2 * (T / S.R ^ 2)
      calc
        1 ≤ ((p : ℝ) / S.R) ^ 2 * T := hscale
        _ = (p : ℝ) ^ 2 * (T / S.R ^ 2) := by
          field_simp [hR.ne']
    have hlower : ∀ x ∈ Set.Icc ((p : ℝ) / 2) (5 * (p : ℝ) / 2),
        lam ≤ |iteratedDeriv 2 f x| := by
      intro x hx
      have hb := sec7_nonzero_prop_window_bounds (S := S) hwin hpq hx
      have hxwin := sec7_nonzero_prop_window_mem_rWin (S := S) (W := W) hcover hwin hpq hx
      have hxref : x ≤ ref := by
        dsimp [ref]
        exact hx.2
      have hrefLocal : ref ≤ 5 * x := by
        calc
          ref = 5 * ((p : ℝ) / 2) := by
            dsimp [ref]
            ring
          _ ≤ 5 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)
      have hcurv := sec7_nonzero_block_curvature Env ME hbox hrel hrelF hpad hshift D.hX hξ₁ hξ₂ hξ₃
        hρ₀ne hρ₀abs hu₁ hu₂ hu₃ hErr hb hrefb hxwin hxref hrefLocal
      have hscaled : T / S.R ^ 2 ≤ |iteratedDeriv 2 f x| := by
        rw [div_le_iff₀ (pow_pos hR 2)]
        change T ≤ |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) x| * S.R ^ 2
        simpa [T, Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc] using hcurv.1
      simpa [lam] using hscaled
    have hupper : ∀ x ∈ Set.Icc ((p : ℝ) / 2) (5 * (p : ℝ) / 2),
        |iteratedDeriv 2 f x| ≤ 256 * lam := by
      intro x hx
      have hb := sec7_nonzero_prop_window_bounds (S := S) hwin hpq hx
      have hxwin := sec7_nonzero_prop_window_mem_rWin (S := S) (W := W) hcover hwin hpq hx
      have hxref : x ≤ ref := by
        dsimp [ref]
        exact hx.2
      have hrefLocal : ref ≤ 5 * x := by
        calc
          ref = 5 * ((p : ℝ) / 2) := by
            dsimp [ref]
            ring
          _ ≤ 5 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)
      have hcurv := sec7_nonzero_block_curvature Env ME hbox hrel hrelF hpad hshift D.hX hξ₁ hξ₂ hξ₃
        hρ₀ne hρ₀abs hu₁ hu₂ hu₃ hErr hb hrefb hxwin hxref hrefLocal
      have hscaled :
          |iteratedDeriv 2 f x| ≤ (256 * T) / S.R ^ 2 := by
        rw [le_div_iff₀ (pow_pos hR 2)]
        change |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) x| * S.R ^ 2 ≤
            256 * T
        simpa [T, Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc] using hcurv.2
      simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hscaled
    have hcore := Geometry.prop43_local_explicit (p : ℝ) lam δ₁ f
      hp_pos hlampos hδpos hδlt hcd hfloor hlower hupper
    have hsub :
        (((Finset.Icc (p : ℤ) (q : ℤ)).filter
            (fun r : ℤ => distInt (f (r : ℝ)) ≤ δ₁)).image
            (Int.cast : ℤ → ℝ))
          ⊆
        (((Finset.Icc ⌊(p : ℝ)⌋ ⌊2 * (p : ℝ)⌋).image
            (Int.cast : ℤ → ℝ)).filter
            (fun r : ℝ => distInt (f r) ≤ δ₁)) := by
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨n, hn, rfl⟩
      rw [Finset.mem_filter] at hn ⊢
      refine ⟨?_, hn.2⟩
      rw [Finset.mem_image]
      refine ⟨n, ?_, rfl⟩
      rw [Finset.mem_Icc] at hn ⊢
      constructor
      · rw [Int.floor_natCast]
        exact hn.1.1
      · have hnq : n ≤ (q : ℤ) := hn.1.2
        have hq2pZ : (q : ℤ) ≤ (2 * p : ℤ) := by exact_mod_cast hdyad
        have hn2p : n ≤ (2 * p : ℤ) := le_trans hnq hq2pZ
        have hfloor2 : ⌊2 * (p : ℝ)⌋ = (2 * p : ℤ) := by
          have : 2 * (p : ℝ) = ((2 * p : ℕ) : ℝ) := by norm_num
          rw [this, Int.floor_natCast]
          norm_num
        rwa [hfloor2]
    have hcardle :
        (((Finset.Icc (p : ℤ) (q : ℤ)).filter
            (fun r : ℤ => distInt (f (r : ℝ)) ≤ δ₁)).card : ℝ)
          ≤ ((((Finset.Icc ⌊(p : ℝ)⌋ ⌊2 * (p : ℝ)⌋).image
            (Int.cast : ℤ → ℝ)).filter
            (fun r : ℝ => distInt (f r) ≤ δ₁)).card : ℝ) := by
      have hcardimg :
          (((Finset.Icc (p : ℤ) (q : ℤ)).filter
            (fun r : ℤ => distInt (f (r : ℝ)) ≤ δ₁)).card : ℝ)
            =
          ((((Finset.Icc (p : ℤ) (q : ℤ)).filter
            (fun r : ℤ => distInt (f (r : ℝ)) ≤ δ₁)).image
            (Int.cast : ℤ → ℝ)).card : ℝ) := by
        rw [Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)]
      rw [hcardimg]
      exact_mod_cast Finset.card_le_card hsub
    have hRleX := sec7_R_le_X P S c₀ Cu D hbud hg hu hX24
    have hL10 := sec7_one_add_logX_ge_ten P hX24
    have habs := sec7_engine_terms_absorb (P := P) (S := S)
      (N := (p : ℝ)) (T := T) (T₁ := S.T₁) (lam := lam) (δ := δ₁)
      hp_nonneg hR hT0 hT1 hδpos hδlt hpRhi hTband.1 hTband.2 (by rfl)
      hfloor hRleX D.hX hL10
    have hcore' :
        ((((Finset.Icc ⌊(p : ℝ)⌋ ⌊2 * (p : ℝ)⌋).image
          (Int.cast : ℤ → ℝ)).filter
          (fun r : ℝ => distInt (f r) ≤ δ₁)).card : ℝ)
          ≤ 109159296 * ((p : ℝ) * lam ^ (1 / 3 : ℝ) + (p : ℝ) * δ₁
            + Real.sqrt (δ₁ / lam) * Real.log (2 + Real.sqrt (δ₁ / lam)) + 1) := by
      simpa only [bind_pure_comp, Finset.fmap_def] using hcore
    simpa [f] using (hcardle.trans hcore').trans habs
  · have hnot : ¬ (p : ℤ) ≤ (q : ℤ) := by
      intro hpz
      have hpq' : p ≤ q := by exact_mod_cast hpz
      exact hpq hpq'
    have hempty : Finset.Icc (p : ℤ) (q : ℤ) = ∅ := Finset.Icc_eq_empty hnot
    have hfilter_empty :
        (Finset.Icc (p : ℤ) (q : ℤ)).filter
          (fun r : ℤ => distInt (f (r : ℝ)) ≤ δ₁) = ∅ := by
      simp [hempty]
    rw [hfilter_empty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hlog0 : 0 ≤ 1 + Real.log P.X := by
      exact add_nonneg zero_le_one (Real.log_nonneg D.hX)
    have hbr : 0 ≤ (S.R * S.T₁) ^ ((1 : ℝ) / 3) + S.R * δ₁
        + S.R * Real.sqrt (δ₁ / S.T₁) + 1 := by
      have hcube0 : 0 ≤ (S.R * S.T₁) ^ ((1 : ℝ) / 3) :=
        Real.rpow_nonneg (mul_nonneg (sec7_R_pos S).le (sec7_T₁_pos S).le) _
      have hdelta0 : 0 ≤ S.R * δ₁ := mul_nonneg (sec7_R_pos S).le hδpos.le
      have hsqrt0 : 0 ≤ S.R * Real.sqrt (δ₁ / S.T₁) :=
        mul_nonneg (sec7_R_pos S).le (Real.sqrt_nonneg _)
      exact add_nonneg (add_nonneg (add_nonneg hcube0 hdelta0) hsqrt0) zero_le_one
    simpa [mul_assoc] using mul_nonneg (mul_nonneg sec7_cN19_pos.le hlog0) hbr

/- md 1923–34: "Here, using R ≍ R₀,
     (RT₁)^{1/3} ≪ (R₀T₁)^{1/3} = H^{1/3}x^{-1/3}Ω^{2/3},
     R√(δ₀/T₁) ≪ G^{3/2}Ω^{5/2},
     R√((Ω²/(RH))/T₁) ≪ xGΩ³,
     R√((S/(Rx²G²Ω⁴))/T₁) ≪ S^{1/2}."
   The third eval is intentionally lossy by `√H` (exact value `xGΩ³H^{-1/2}`, md keeps
   `xGΩ³`); the second needs the strip (`x ≤ G¹⁷Ω⁻²⁶X^{O(u)}` against `H^{1/2}`) for its
   `Δ²/(H²GA)`-piece. `δ₀ = sec7_delta0` (md 1360, TRAP-1 display form). -/

private theorem sec7_N20_cube_eval (P : Globals) (S : Scale P) :
    (S.R * S.T₁) ^ ((1:ℝ)/3) =
      P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) := by
  have hH := P.H_pos
  have hΩ := S.Ω_pos
  have hΔ := S.Δ_pos
  rw [sec7_R_mul_T₁ S]
  unfold Scale.A Scale.x
  rw [mul_pow]
  rw [Real.mul_rpow (sq_nonneg S.Δ) (sq_nonneg S.Ω)]
  rw [show (-(1:ℝ)/3) = -((1:ℝ)/3) by ring]
  rw [Real.div_rpow hH.le (sq_nonneg S.Δ)]
  rw [Real.rpow_neg hH.le]
  rw [Real.rpow_neg (sq_nonneg S.Δ)]
  rw [← Real.rpow_natCast S.Δ 2, ← Real.rpow_natCast S.Ω 2]
  rw [← Real.rpow_mul hΔ.le, ← Real.rpow_mul hΩ.le]
  field_simp [hH.ne']
  ring_nf

private theorem sec7_N20_delta0_sq_eval (P : Globals) (S : Scale P) :
    (S.R * Real.sqrt (sec7_delta0 P S / S.T₁)) ^ 2 =
      P.G ^ 3 * S.Ω ^ 5 + S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H := by
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hΔ := S.Δ_pos
  have hd1 : 0 ≤ S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) :=
    div_nonneg (pow_nonneg hΔ.le 5)
      (mul_nonneg (pow_nonneg hH.le 3) (sq_nonneg S.Ω))
  have hd2 : 0 ≤ S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A) := by
    have hA0 : 0 ≤ S.A := by
      unfold Scale.A
      positivity
    exact div_nonneg (sq_nonneg S.Δ)
      (mul_nonneg (mul_nonneg (sq_nonneg P.H) hG.le) hA0)
  have hd0 : 0 ≤ sec7_delta0 P S := by
    rw [sec7_delta0_eq P S]
    exact add_nonneg hd1 hd2
  have harg0 : 0 ≤ sec7_delta0 P S / S.T₁ := div_nonneg hd0 hT1.le
  calc
    (S.R * Real.sqrt (sec7_delta0 P S / S.T₁)) ^ 2
        = S.R ^ 2 * (sec7_delta0 P S / S.T₁) := by
          rw [mul_pow, Real.sq_sqrt harg0]
    _ = P.G ^ 3 * S.Ω ^ 5 + S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H := by
          rw [sec7_delta0_eq P S]
          unfold Scale.R Scale.T₁ Scale.F Scale.A Scale.x
          field_simp

private theorem sec7_N20_third_sq_eval (P : Globals) (S : Scale P) :
    (S.R * Real.sqrt (((S.Ω ^ 2 / (S.R * P.H)) / S.T₁))) ^ 2 =
      S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hnum0 : 0 ≤ S.Ω ^ 2 / (S.R * P.H) :=
    div_nonneg (sq_nonneg S.Ω) (mul_nonneg hR.le P.H_pos.le)
  have harg0 : 0 ≤ ((S.Ω ^ 2 / (S.R * P.H)) / S.T₁) :=
    div_nonneg hnum0 hT1.le
  calc
    (S.R * Real.sqrt (((S.Ω ^ 2 / (S.R * P.H)) / S.T₁))) ^ 2
        = S.R ^ 2 * ((S.Ω ^ 2 / (S.R * P.H)) / S.T₁) := by
          rw [mul_pow, Real.sq_sqrt harg0]
    _ = S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H := by
          have hH := P.H_pos
          have hG := P.G_pos
          have hΩ := S.Ω_pos
          have hΔ := S.Δ_pos
          unfold Scale.R Scale.T₁ Scale.F Scale.x
          field_simp

private theorem sec7_N20_Sv_sq_eval (P : Globals) (S : Scale P) {Sv : ℝ}
    (hSv : 0 ≤ Sv) :
    (S.R * Real.sqrt ((Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁)) ^ 2 = Sv := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hden0 : 0 ≤ S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4 := by
    have hx := OnStripAux.x_pos P S
    positivity
  have hnum0 : 0 ≤ Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) :=
    div_nonneg hSv hden0
  have harg0 : 0 ≤ (Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁ :=
    div_nonneg hnum0 hT1.le
  calc
    (S.R * Real.sqrt ((Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁)) ^ 2
        = S.R ^ 2 * ((Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁) := by
          rw [mul_pow, Real.sq_sqrt harg0]
    _ = Sv := by
          have hH := P.H_pos
          have hG := P.G_pos
          have hΩ := S.Ω_pos
          have hΔ := S.Δ_pos
          unfold Scale.R Scale.T₁ Scale.F Scale.x
          field_simp

private theorem sec7_N20_delta0_strip_piece (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg : 0 ≤ P.g) (hu : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H ≤ P.G ^ 3 * S.Ω ^ 5 := by
  have hXgt : 1 < P.X := by
    by_contra h
    have hle : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le hle (by norm_num)
    linarith
  have hCu := D.hCu
  have hbudE : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu.le (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu.le (by linarith)
  have hkey : (1:ℝ) <
      P.H ^ (1:ℝ) * S.x ^ (-(2:ℝ)) * P.G ^ (1:ℝ) * S.Ω ^ (-(1:ℝ)) :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt (1:ℝ) (-(2:ℝ)) (1:ℝ) (-(1:ℝ))
      (by
        unfold OnStripAux.ratioExp
        norm_num
        nlinarith [hbudE, hg, hu.le, huCu, huCu1])
  have hterm0 : 0 ≤ S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H :=
    div_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg S.x) (sq_nonneg P.G))
        (pow_nonneg S.Ω_pos.le 6))
      P.H_pos.le
  calc
    S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H
        = (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H) * 1 := by ring
    _ ≤ (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H) *
          (P.H ^ (1:ℝ) * S.x ^ (-(2:ℝ)) * P.G ^ (1:ℝ) * S.Ω ^ (-(1:ℝ))) :=
        mul_le_mul_of_nonneg_left hkey.le hterm0
    _ = P.G ^ 3 * S.Ω ^ 5 := by
        have hH := P.H_pos
        have hΩ := S.Ω_pos
        have hx := OnStripAux.x_pos P S
        rw [Real.rpow_one, Real.rpow_one]
        rw [show (-(2:ℝ)) = -((2:ℝ)) by ring, Real.rpow_neg hx.le]
        rw [show (-(1:ℝ)) = -((1:ℝ)) by ring, Real.rpow_neg hΩ.le]
        rw [Real.rpow_one]
        field_simp [hH.ne', hx.ne', hΩ.ne']
        rw [← Real.rpow_natCast S.x 2]
        exact mul_comm (S.x ^ (2:ℝ)) (P.G ^ 3)

private theorem sec7_N20_one_le_H {P : Globals} {S : Scale P} {c₀ Cu : ℝ}
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hu : 0 < P.u) :
    (1:ℝ) ≤ P.H := by
  have hcoef0 : 0 ≤ (18675 + 790 * Cu) * P.u := by
    nlinarith [D.hCu, hu.le]
  have hgsmall : 18977 * P.g ≤ 2 := by
    have hb : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
    nlinarith
  have hg_le_one : P.g ≤ 1 := by
    nlinarith
  unfold Globals.H
  exact Real.one_le_rpow D.hX (by nlinarith)

private theorem sec7_N20_GΩ_sq (P : Globals) (S : Scale P) :
    (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) ^ 2 = P.G ^ 3 * S.Ω ^ 5 := by
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  rw [mul_pow]
  rw [show (P.G ^ ((3:ℝ)/2)) ^ 2 = P.G ^ (((3:ℝ)/2) * 2) by
    rw [← Real.rpow_natCast (P.G ^ ((3:ℝ)/2)) 2, ← Real.rpow_mul hG.le]
    norm_num]
  rw [show (S.Ω ^ ((5:ℝ)/2)) ^ 2 = S.Ω ^ (((5:ℝ)/2) * 2) by
    rw [← Real.rpow_natCast (S.Ω ^ ((5:ℝ)/2)) 2, ← Real.rpow_mul hΩ.le]
    norm_num]
  norm_num

/-- **N20** (md 1923–34): the four nonzero-branch evaluations — the cube-root term and the
three square-root terms of (7.8), at scale `T₁`, in `R ≍ R₀` form. -/
theorem sec7_nonzero_sqrt_evals :
    ∀ (P : Globals) (S : Scale P), ∀ c₀ Cu : ℝ,
      OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
      0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      (S.R * S.T₁) ^ ((1:ℝ)/3)
          ≤ sec7_cN20 * (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) ∧
      S.R * Real.sqrt (sec7_delta0 P S / S.T₁)
          ≤ sec7_cN20 * (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) ∧
      S.R * Real.sqrt ((S.Ω ^ 2 / (S.R * P.H)) / S.T₁)
          ≤ sec7_cN20 * (S.x * P.G * S.Ω ^ 3) ∧
      ∀ Sv : ℝ, 0 ≤ Sv →
        S.R * Real.sqrt ((Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁)
          ≤ sec7_cN20 * Real.sqrt Sv := by
  intro P S c₀ Cu D hbud hg hu hX24
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hR : 0 < S.R := sec7_R_pos S
  have hstrip := sec7_N20_delta0_strip_piece P S c₀ Cu D hbud hg hu hX24
  have hHge1 : (1:ℝ) ≤ P.H := sec7_N20_one_le_H (S := S) D hbud hu
  have hGΩ0 : 0 ≤ P.G ^ 3 * S.Ω ^ 5 := by positivity
  have hcN20ge1 : (1:ℝ) ≤ sec7_cN20 := by norm_num [sec7_cN20]
  have hcN20ge2 : (2:ℝ) ≤ sec7_cN20 := by norm_num [sec7_cN20]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sec7_N20_cube_eval P S]
    have hbase0 :
        0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) := by
      positivity
    nlinarith
  · let B : ℝ := P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
    have hleft0 : 0 ≤ S.R * Real.sqrt (sec7_delta0 P S / S.T₁) :=
      mul_nonneg hR.le (Real.sqrt_nonneg _)
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    refine le_trans (sec7_le_of_sq hleft0 (by positivity : 0 ≤ 2 * B) ?_) ?_
    · calc
        (S.R * Real.sqrt (sec7_delta0 P S / S.T₁)) ^ 2
            = P.G ^ 3 * S.Ω ^ 5 + S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H :=
                sec7_N20_delta0_sq_eval P S
        _ ≤ P.G ^ 3 * S.Ω ^ 5 + P.G ^ 3 * S.Ω ^ 5 :=
                add_le_add_right hstrip _
        _ ≤ (2 * B) ^ 2 := by
          have hBsq : B ^ 2 = P.G ^ 3 * S.Ω ^ 5 := by
            dsimp [B]
            exact sec7_N20_GΩ_sq P S
          rw [show (2 * B) ^ 2 = 4 * B ^ 2 by ring, hBsq]
          nlinarith [hGΩ0]
    · nlinarith
  · have hleft0 : 0 ≤ S.R * Real.sqrt ((S.Ω ^ 2 / (S.R * P.H)) / S.T₁) :=
      mul_nonneg hR.le (Real.sqrt_nonneg _)
    have hright0 : 0 ≤ S.x * P.G * S.Ω ^ 3 := by positivity
    refine le_trans (sec7_le_of_sq hleft0 hright0 ?_) ?_
    · calc
        (S.R * Real.sqrt ((S.Ω ^ 2 / (S.R * P.H)) / S.T₁)) ^ 2
            = S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 / P.H := sec7_N20_third_sq_eval P S
        _ ≤ S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 := by
          rw [div_le_iff₀ hH]
          have hmon0 : 0 ≤ S.x ^ 2 * P.G ^ 2 * S.Ω ^ 6 := by positivity
          nlinarith [hmon0, hHge1]
        _ = (S.x * P.G * S.Ω ^ 3) ^ 2 := by ring
    · have hbase0 : 0 ≤ S.x * P.G * S.Ω ^ 3 := by positivity
      nlinarith
  · intro Sv hSv
    have hleft0 :
        0 ≤ S.R * Real.sqrt ((Sv / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁) :=
      mul_nonneg hR.le (Real.sqrt_nonneg _)
    have hright0 : 0 ≤ Real.sqrt Sv := Real.sqrt_nonneg Sv
    refine le_trans (sec7_le_of_sq hleft0 hright0 ?_) ?_
    · rw [sec7_N20_Sv_sq_eval P S hSv, Real.sq_sqrt hSv]
    · nlinarith

end Squarefree
