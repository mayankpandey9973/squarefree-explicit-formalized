import Squarefree.Params
import Squarefree.Bracket.Admissible
import Squarefree.Bracket.Sec7Defs
import Squarefree.Bracket.Sec7Branch
import Squarefree.Bracket.Sec7Cube
import Squarefree.Bracket.Sec7Harvest
import Squarefree.Bracket.Sec7MonExpBuild
import Squarefree.Bracket.Sec7Nonzero
import Squarefree.Bracket.Sec7Prox
import Squarefree.Counting.Preimage
import Squarefree.Structure.DaSpacing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

/-!
# §7 box-sum bracket counts (Prop 7.1, Prop 7.3)

Faithful statements of Prop 7.1 and Prop 7.3 from `../explicit_writeup.md` (lines 1404–1435
and 1993–2000), with PROVED root assemblies (P1e, 2026-06-11): `prop_7_1` = the N23
contradiction (N5 `sec7_averaged_cube_lower` vs the N15/N22 harvests, `C = sec7_cCubeIn`,
margin `2·sec7_cCube < sec7_harvM`); `prop_7_3` = N24 (N3 + N4 + prop_7_1 over the `j`-band,
`C = 3·sec7_cJ·C₇₁`). G1 ruling AM-8: the strip-regime pack (`StripData`, `Budget`,
`0 ≤ g`, `0 < u`, X-largeness, `log X ≤ X^u`) is carried by the root contracts themselves,
mirrored verbatim from the §8/§9 call site `dblock_on_strip` (`Opt/Global.lean`). Sorries
live ONLY in the two `private` G1-AUDIT supplier stubs below (per-triple split / r-side
data pack), each tagged `STUB: N23/N24`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset Squarefree.Counting Squarefree.FiniteDiff

namespace Squarefree

set_option exponentiation.threshold 400
set_option maxHeartbeats 10000000

/-- ARB-2 (A4/A6): the §7 `hxsmall` fact `x²Ω ≤ HG`, DERIVED on the strip — the binding
strip-corner `X`-exponent of `H·x⁻²·G·Ω⁻¹` has margin `≈ 0.186 > 0` at the budget
(sympy-banked, tools/sec7_ledger.py).  Needed by the N13 zero-branch evaluations (the
`Ω²/H ≤ GΩ/x²` domination); derived in-file so `sec7_triple_split` keeps its signature. -/
private theorem sec7_hxsmall (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg : 0 ≤ P.g) (hu : 0 ≤ P.u) (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    S.x ^ 2 * S.Ω ≤ P.H * P.G := by
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (16995 + 790 * Cu) * P.u ≤ 2 := by
    have h := hbud
    unfold OnStripAux.Budget at h
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1680) hu]
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu (by linarith)
  have hkey : (1:ℝ) < P.H ^ (1:ℝ) * S.x ^ (-2:ℝ) * P.G ^ (1:ℝ) * S.Ω ^ (-1:ℝ) :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt 1 (-2) 1 (-1)
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg, hu, huCu, huCu1])
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hpos : (0:ℝ) < S.x ^ 2 * S.Ω := by positivity
  have heq : P.H ^ (1:ℝ) * S.x ^ (-2:ℝ) * P.G ^ (1:ℝ) * S.Ω ^ (-1:ℝ) * (S.x ^ 2 * S.Ω)
      = P.H * P.G := by
    rw [Real.rpow_one, Real.rpow_one, Real.rpow_neg hx.le, Real.rpow_neg hΩ.le,
        Real.rpow_one, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have := mul_lt_mul_of_pos_right hkey hpos
  rw [one_mul, heq] at this
  exact this.le

/-- Local copy of the quantitative strip inverse-monomial smallness helper used in the
nonzero side-condition proofs; the original helper is private to `Sec7Nonzero`. -/
private theorem sec7_inv_small_local (P : Globals) (S : Scale P) (c₀ Cu : ℝ)
    (D : OnStripAux.StripData P S c₀ Cu) (hXgt : 1 < P.X)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) (a b c d : ℝ)
    (hE : 0 < OnStripAux.ratioExp P.g P.u Cu (a - 7/20) b (c - 7/100) d) :
    1 / (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ≤ 1 / 10 ^ 50 := by
  have hH := P.H_pos
  have hG := P.G_pos
  have key : (1:ℝ) < P.H ^ (a - 7/20) * S.x ^ b * P.G ^ (c - 7/100) * S.Ω ^ d :=
    OnStripAux.one_lt_mono P S c₀ Cu D hXgt _ _ _ _ hE
  have hX7 : P.H ^ (7/20:ℝ) * P.G ^ (7/100:ℝ) = P.X ^ (7/100:ℝ) := by
    unfold Globals.H Globals.G
    rw [← Real.rpow_mul P.X_pos.le, ← Real.rpow_mul P.X_pos.le, ← Real.rpow_add P.X_pos]
    congr 1
    ring
  have hbig : (10:ℝ) ^ 50 ≤ P.X ^ (7/100:ℝ) := by
    have h7 : P.X ^ (7/100:ℝ) = (P.X ^ (1/100:ℝ)) ^ (7:ℕ) := by
      rw [← Real.rpow_natCast (P.X ^ (1/100:ℝ)) 7, ← Real.rpow_mul P.X_pos.le]
      norm_num
    rw [h7]
    calc
      (10:ℝ) ^ 50 ≤ (16777216:ℝ) ^ (7:ℕ) := by norm_num
      _ ≤ (P.X ^ (1/100:ℝ)) ^ (7:ℕ) := pow_le_pow_left₀ (by norm_num) hX24 7
  have hsplit : P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d
      = (P.H ^ (a - 7/20) * S.x ^ b * P.G ^ (c - 7/100) * S.Ω ^ d)
          * (P.H ^ (7/20:ℝ) * P.G ^ (7/100:ℝ)) := by
    have h1 : P.H ^ a = P.H ^ (a - 7/20) * P.H ^ (7/20:ℝ) := by
      rw [← Real.rpow_add hH]
      congr 1
      ring
    have h2 : P.G ^ c = P.G ^ (c - 7/100) * P.G ^ (7/100:ℝ) := by
      rw [← Real.rpow_add hG]
      congr 1
      ring
    rw [h1, h2]
    ring
  have hM : (10:ℝ) ^ 50 ≤ P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d := by
    calc
      (10:ℝ) ^ 50 ≤ P.X ^ (7/100:ℝ) := hbig
      _ = 1 * P.X ^ (7/100:ℝ) := (one_mul _).symm
      _ ≤ (P.H ^ (a - 7/20) * S.x ^ b * P.G ^ (c - 7/100) * S.Ω ^ d) *
            P.X ^ (7/100:ℝ) :=
          mul_le_mul_of_nonneg_right key.le (Real.rpow_pos_of_pos P.X_pos _).le
      _ = P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d := by rw [← hX7, ← hsplit]
  exact one_div_le_one_div_of_le (by norm_num) hM

/-- Repackage the §3 expansion fields carried by a concrete `Sec7Phase` as the N9′ input
record consumed by `sec7_monExp_build`. -/
private noncomputable def sec7_raExpData_of_phase (P : Globals) (S : Scale P) (W : ℝ)
    (a : ℤ) (Ph : Sec7Phase P S W a) (j : ℤ) (hj : sec7_jBand P S j) :
    Sec7RaExpData P S W a Ph j where
  c₁ := Ph.ra_c₁ j
  c₂ := Ph.ra_c₂ j
  c₁_lo := Ph.ra_c₁_lo j hj
  c₁_hi := Ph.ra_c₁_hi j hj
  c₂_lo := Ph.ra_c₂_lo j hj
  c₂_hi := Ph.ra_c₂_hi j hj
  e₁D := Ph.ra_e₁D j
  e₂D := Ph.ra_e₂D j
  e₃D := Ph.ra_e₃D j
  e₁D_zero := Ph.ra_e₁D_zero j hj
  e₂D_zero := Ph.ra_e₂D_zero j hj
  e₃D_zero := Ph.ra_e₃D_zero j hj
  e₁D_deriv := Ph.ra_e₁D_deriv j hj
  e₂D_deriv := Ph.ra_e₂D_deriv j hj
  e₃D_deriv := Ph.ra_e₃D_deriv j hj
  e₁D_bound := by
    intro m hm r hr
    simpa [sec7_cExpIn, sec7_relErr] using Ph.ra_e₁D_bound j hj m hm r hr
  e₂D_bound := by
    intro m hm r hr
    simpa [sec7_cExpIn, sec7_relErr] using Ph.ra_e₂D_bound j hj m hm r hr
  e₃D_bound := by
    intro m hm r hr
    simpa [sec7_cExpIn, sec7_relErr] using Ph.ra_e₃D_bound j hj m hm r hr

/-- The `Sec7Phase` regularity field in the exact `sec7_Phi` shape used by N13/N19. -/
private theorem sec7_phase_phi_contDiff {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    (Ph : Sec7Phase P S W a) (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ContDiff ℝ 2 (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) := by
  simpa [sec7_Phi, sec7_hSum] using
    Ph.phiContDiff j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃

/-- The `Sec7Phase` critical-zero field in the exact `Sec7ZeroHyp` shape. -/
private theorem sec7_phase_phi_fewCritical {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    (Ph : Sec7Phase P S W a) (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ p q : ℕ,
      Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋ → q ≤ 2 * p →
      ((Set.Icc (p : ℝ) (q : ℝ) ∩
          {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).Finite ∧
        (Set.Icc (p : ℝ) (q : ℝ) ∩
          {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).ncard ≤
          sec7_KZero) ∧
      ((Set.Icc (p : ℝ) (q : ℝ) ∩
          {r | iteratedDeriv 2
            (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).Finite ∧
        (Set.Icc (p : ℝ) (q : ℝ) ∩
          {r | iteratedDeriv 2
            (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).ncard ≤
          sec7_KZero) := by
  intro p q hwin hdyad
  simpa [sec7_Phi, sec7_hSum, sec7_KZero] using
    Ph.phiFewCritical j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ p q hwin hdyad

private theorem sec7_shiftBox_of_box {W : ℝ} {p : ℕ × ℕ × ℕ} (hW : 1 ≤ W)
    (hp : p ∈ box W) : sec7_shiftBox W (p.1 : ℤ) (p.2.1 : ℤ) (p.2.2 : ℤ) := by
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hp
  rcases hp with ⟨hp₁, hp₂₃⟩
  rcases hp₂₃ with ⟨hp₂, hp₃⟩
  have hf₁ : ((⌊W ^ 1⌋₊ : ℕ) : ℝ) ≤ W ^ 1 := floor_pow_le W hW 1
  have hf₂ : ((⌊W ^ 2⌋₊ : ℕ) : ℝ) ≤ W ^ 2 := floor_pow_le W hW 2
  have hf₃ : ((⌊W ^ 4⌋₊ : ℕ) : ℝ) ≤ W ^ 4 := floor_pow_le W hW 4
  constructor
  · constructor
    · exact_mod_cast hp₁.1
    · have hp₁R : (p.1 : ℝ) ≤ (⌊W⌋₊ : ℕ) := by exact_mod_cast hp₁.2
      simpa using le_trans hp₁R (by simpa using hf₁)
  · constructor
    · constructor
      · exact_mod_cast hp₂.1
      · have hp₂R : (p.2.1 : ℝ) ≤ (⌊W ^ 2⌋₊ : ℕ) := by exact_mod_cast hp₂.2
        exact le_trans hp₂R hf₂
    · constructor
      · exact_mod_cast hp₃.1
      · have hp₃R : (p.2.2 : ℝ) ≤ (⌊W ^ 4⌋₊ : ℕ) := by exact_mod_cast hp₃.2
        exact le_trans hp₃R hf₃

private theorem sec7_Ssym_natCast (h₁ h₂ h₃ : ℕ) :
    sec7_Ssym (h₁ : ℤ) (h₂ : ℤ) (h₃ : ℤ) = (Sbox h₁ h₂ h₃ : ℝ) := by
  simp only [sec7_Ssym, Sbox]
  push_cast
  ring

private theorem sec7_Pprod_natCast (h₁ h₂ h₃ : ℕ) :
    sec7_Pprod (h₁ : ℤ) (h₂ : ℤ) (h₃ : ℤ) = (Pbox h₁ h₂ h₃ : ℝ) := by
  simp only [sec7_Pprod, Pbox]
  push_cast
  ring

private theorem sec7_hSum_natCast (h₁ h₂ h₃ : ℕ) :
    sec7_hSum (h₁ : ℤ) (h₂ : ℤ) (h₃ : ℤ) = (HSbox h₁ h₂ h₃ : ℝ) := by
  simp only [sec7_hSum, HSbox]
  push_cast
  ring

private theorem sec7_monExp_shift_small {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    24 * sec7_hSum h₁ h₂ h₃ * sec7_cWin ≤ S.R := by
  have hsum0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
    have h3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
      sec7_hSum_ge3 hbox.1.1 hbox.2.1.1 hbox.2.2.1
    linarith
  calc
    24 * sec7_hSum h₁ h₂ h₃ * sec7_cWin
        = sec7_hSum h₁ h₂ h₃ * 24000 := by
          rw [show sec7_cWin = 1000 from by norm_num [sec7_cWin]]
          ring
    _ ≤ sec7_hSum h₁ h₂ h₃ * 10 ^ 149 := by
          exact mul_le_mul_of_nonneg_left (by norm_num) hsum0
    _ ≤ S.R := sec7_hSum_R_small Env hbox

private theorem sec7_shift_margin {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    W + W ^ 2 + W ^ 4 ≤ S.R / 2000 := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hlog : (1 : ℝ) ≤ 1 + Real.log P.X := by
    have := Real.log_nonneg hsd.hX
    linarith
  have hRform :
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
    rw [OnStripAux.R_mono P S, Real.rpow_one,
      show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have henv : sec7_envC * W ^ 8 ≤ S.R := by
    calc
      sec7_envC * W ^ 8
          ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
            exact le_mul_of_one_le_right (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 8)) hlog
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
            simpa only [Real.rpow_one, show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
              rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]] using Env.tc4
      _ = S.R := hRform
  have hW14 : W ≤ W ^ 4 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW24 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW48 : W ^ 4 ≤ W ^ 8 := pow_le_pow_right₀ hW (by omega)
  have hsum : W + W ^ 2 + W ^ 4 ≤ 3 * W ^ 4 := by linarith
  have h6000 : 2000 * (W + W ^ 2 + W ^ 4) ≤ 6000 * W ^ 8 := by
    calc
      2000 * (W + W ^ 2 + W ^ 4) ≤ 2000 * (3 * W ^ 4) := by gcongr
      _ = 6000 * W ^ 4 := by ring
      _ ≤ 6000 * W ^ 8 := by gcongr
  have hC : (6000 : ℝ) * W ^ 8 ≤ sec7_envC * W ^ 8 := by
    gcongr
    norm_num [sec7_envC]
  have h2000 : 2000 * (W + W ^ 2 + W ^ 4) ≤ S.R := le_trans (le_trans h6000 hC) henv
  nlinarith

private theorem sec7_cSub_le_X_2_25 (P : Globals)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    sec7_cSub ≤ P.X ^ (2/25 : ℝ) := by
  have hbase0 : 0 ≤ (16777216 : ℝ) := by norm_num
  have hpow := pow_le_pow_left₀ hbase0 hX24 8
  have hc : sec7_cSub ≤ (16777216 : ℝ) ^ 8 := by norm_num [sec7_cSub]
  have hxp : (P.X ^ (1/100 : ℝ)) ^ 8 = P.X ^ (2/25 : ℝ) := by
    rw [← Real.rpow_natCast (P.X ^ (1/100 : ℝ)) 8,
      ← Real.rpow_mul P.X_pos.le]
    norm_num
  rw [hxp] at hpow
  exact le_trans hc hpow

private theorem sec7_X_2_25_eq_HG (P : Globals) :
    P.X ^ (2/25 : ℝ) = P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ) := by
  have hX := P.X_pos
  rw [Globals.H, Globals.G]
  rw [← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le, ← Real.rpow_add hX]
  ring_nf

private theorem sec7_zero_hsub1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_cSub * (W ^ 4 * S.Ω ^ 2) ≤ Real.sqrt (P.H * S.x) := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hΩ0 : 0 ≤ S.Ω := S.Ω_pos.le
  apply Real.le_sqrt_of_sq_le
  calc
    (sec7_cSub * (W ^ 4 * S.Ω ^ 2)) ^ 2
        = sec7_cSub ^ 2 * W ^ 8 * S.Ω ^ 4 := by ring
    _ ≤ sec7_envC2 * (W ^ 30 * S.Ω ^ 4) := by
        have hC : sec7_cSub ^ 2 ≤ sec7_envC2 := by
          norm_num [sec7_cSub, sec7_envC2]
        have hWpow : W ^ 8 ≤ W ^ 30 := pow_le_pow_right₀ hW (by omega)
        calc
          sec7_cSub ^ 2 * W ^ 8 * S.Ω ^ 4
              ≤ sec7_envC2 * W ^ 30 * S.Ω ^ 4 := by
                gcongr
                exact sec7_envC2_pos.le
          _ = sec7_envC2 * (W ^ 30 * S.Ω ^ 4) := by ring
    _ ≤ P.H * S.x := Env.n6

private theorem sec7_zero_hrel {P : Globals} {S : Scale P} {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    sec7_relErr P S * 10 ^ 143 ≤ 1 :=
  sec7_relErr_le Env (sec7_W_ge_one hbox) hsd hbud hg0 hu0 hX24

private theorem sec7_zero_hsub2 {P : Globals} {S : Scale P} (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) (hbud : OnStripAux.Budget P.g P.u Cu)
    (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    sec7_cSub * (P.G * S.Ω ^ 6 * P.U ^ 3) ≤ P.H := by
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hbud' : 18977 * P.g + 18675 * P.u ≤ 2 := by
    have hCu0 : 0 ≤ Cu := le_trans zero_le_one hsd.hCu
    have hextra : 0 ≤ 790 * Cu * P.u := by
      nlinarith [mul_nonneg hCu0 hu0.le]
    unfold OnStripAux.Budget at hbud
    nlinarith [hbud, hextra]
  have hratio : (1 : ℝ) <
      P.H ^ ((3/5 : ℝ) - 15 * P.u) * S.x ^ (0 : ℝ) *
        P.G ^ (-(27/25 : ℝ) - 3 * P.u) *
        S.Ω ^ (-(6 : ℝ)) :=
    OnStripAux.one_lt_mono P S c₀ Cu hsd hXgt
      ((3/5 : ℝ) - 15 * P.u) 0 (-(27/25 : ℝ) - 3 * P.u) (-(6 : ℝ))
      (by
        unfold OnStripAux.ratioExp
        norm_num
        nlinarith [hbud', hg0, hu0.le])
  have hcX : sec7_cSub ≤ P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ) := by
    simpa [sec7_X_2_25_eq_HG P] using sec7_cSub_le_X_2_25 P hX24
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hratio_nonneg :
      0 ≤ P.H ^ ((3/5 : ℝ) - 15 * P.u) * S.x ^ (0 : ℝ) *
        P.G ^ (-(27/25 : ℝ) - 3 * P.u) *
        S.Ω ^ (-(6 : ℝ)) := by positivity
  have hcX_nonneg : 0 ≤ P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ) := by positivity
  have hUeq : P.U ^ 3 = P.H ^ (15 * P.u) * P.G ^ (3 * P.u) := by
    unfold Globals.U Globals.H Globals.G
    rw [← Real.rpow_natCast (P.X ^ P.u) 3, ← Real.rpow_mul P.X_pos.le]
    rw [← Real.rpow_mul P.X_pos.le, ← Real.rpow_mul P.X_pos.le, ← Real.rpow_add P.X_pos]
    congr 1
    ring
  have htarget :
      sec7_cSub * P.U ^ 3 ≤ P.H / (P.G * S.Ω ^ 6) := by
    calc
      sec7_cSub * P.U ^ 3
          ≤ (P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ)) * P.U ^ 3 := by
          exact mul_le_mul_of_nonneg_right hcX (pow_nonneg P.U_pos.le 3)
      _ = (P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ)) *
            (P.H ^ (15 * P.u) * P.G ^ (3 * P.u)) := by rw [hUeq]
      _ ≤ (P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ)) *
            (P.H ^ (15 * P.u) * P.G ^ (3 * P.u)) *
            (P.H ^ ((3/5 : ℝ) - 15 * P.u) * S.x ^ (0 : ℝ) *
              P.G ^ (-(27/25 : ℝ) - 3 * P.u) * S.Ω ^ (-(6 : ℝ))) := by
          exact le_mul_of_one_le_right (by positivity) hratio.le
      _ = P.H / (P.G * S.Ω ^ 6) := by
          rw [Real.rpow_zero]
          rw [show (P.H ^ (2/5 : ℝ) * P.G ^ (2/25 : ℝ)) *
                (P.H ^ (15 * P.u) * P.G ^ (3 * P.u)) *
                (P.H ^ ((3/5 : ℝ) - 15 * P.u) * 1 *
                  P.G ^ (-(27/25 : ℝ) - 3 * P.u) * S.Ω ^ (-(6 : ℝ))) =
                (P.H ^ (2/5 : ℝ) * P.H ^ (15 * P.u) *
                  P.H ^ ((3/5 : ℝ) - 15 * P.u)) *
                  (P.G ^ (2/25 : ℝ) * P.G ^ (3 * P.u) *
                    P.G ^ (-(27/25 : ℝ) - 3 * P.u)) *
                  S.Ω ^ (-(6 : ℝ)) by ring]
          rw [← Real.rpow_add hH, ← Real.rpow_add hH, ← Real.rpow_add hG,
            ← Real.rpow_add hG, Real.rpow_neg hΩ.le]
          rw [show (2 / 5 : ℝ) + 15 * P.u + (3 / 5 - 15 * P.u) = 1 by ring,
            show (2 / 25 : ℝ) + 3 * P.u + (-(27 / 25) - 3 * P.u) = -1 by ring,
            Real.rpow_one, Real.rpow_neg hG.le]
          rw [Real.rpow_one]
          field_simp [hG.ne', hΩ.ne']
          rw [show S.Ω ^ (6 : ℝ) = S.Ω ^ 6 by
            rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  calc
    sec7_cSub * (P.G * S.Ω ^ 6 * P.U ^ 3)
        = (sec7_cSub * P.U ^ 3) * (P.G * S.Ω ^ 6) := by ring
    _ ≤ (P.H / (P.G * S.Ω ^ 6)) * (P.G * S.Ω ^ 6) := by
          exact mul_le_mul_of_nonneg_right htarget (by positivity)
    _ = P.H := by field_simp [hG.ne', hΩ.ne']

private theorem sec7_dyadic_cover_sum (f : ℤ → ℝ) (hf : ∀ a, 0 ≤ f a) (t : ℝ)
    (ht : 0 < t) :
    ∀ K : ℕ,
      ∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋, f a ≤
        ∑ k ∈ Finset.range (K + 1),
          ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a := by
  intro K
  induction K with
  | zero =>
    rw [zero_add, Finset.sum_range_one]
    norm_num
  | succ K ih =>
    have hcover :
        Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1 + 1)⌋ ⊆
          Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋ ∪
            Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋ := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      by_cases hle : a ≤ ⌊t * 2 ^ (K + 1)⌋
      · exact Or.inl ⟨ha.1, hle⟩
      · refine Or.inr ⟨?_, ha.2⟩
        have h1 : ⌈t * 2 ^ (K + 1)⌉ ≤ ⌊t * 2 ^ (K + 1)⌋ + 1 :=
          Int.ceil_le_floor_add_one _
        omega
    calc
      ∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1 + 1)⌋, f a
          ≤ ∑ a ∈ (Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋ ∪
              Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋), f a :=
            Finset.sum_le_sum_of_subset_of_nonneg hcover (fun a _ _ => hf a)
      _ ≤ (∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋, f a) +
            ∑ a ∈ Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋, f a := by
            set s₁ := Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋ with hs₁
            set s₂ := Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋ with hs₂
            have hui : (∑ x ∈ s₁ ∪ s₂, f x) + ∑ x ∈ s₁ ∩ s₂, f x =
                (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := Finset.sum_union_inter
            have hinter : 0 ≤ ∑ a ∈ (s₁ ∩ s₂), f a :=
              Finset.sum_nonneg (fun a _ => hf a)
            linarith
      _ ≤ (∑ k ∈ Finset.range (K + 1),
              ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a) +
            ∑ a ∈ Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋, f a := by
            gcongr
      _ = ∑ k ∈ Finset.range (K + 1 + 1),
              ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a := by
            rw [Finset.sum_range_succ (fun k =>
              ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a) (K + 1)]

private theorem sec7_card_filter_eq_sum_indicator (s : Finset ℤ) (P : ℤ → Prop)
    [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ n ∈ s, (if P n then (1 : ℝ) else 0) := by
  rw [Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun n hn => by by_cases h : P n <;> simp [h])

private theorem sec7_wide_filter_dyadic_bound {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (P : ℤ → Prop) [DecidablePred P]
    (hblock : ∀ k ∈ Finset.range 10,
      (((Finset.Icc ⌈(R / 72) * 2 ^ k⌉ ⌊(R / 72) * 2 ^ (k + 1)⌋).filter P).card : ℝ) ≤ B)
    (hlast :
      (((Finset.Icc ⌈(R / 72) * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋).filter P).card : ℝ) ≤ B) :
    (((Finset.Icc ⌈R / 72⌉ ⌊16 * R⌋).filter P).card : ℝ) ≤ 11 * B := by
  classical
  set t : ℝ := R / 72 with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  let f : ℤ → ℝ := fun n => if P n then (1 : ℝ) else 0
  have hf : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; split <;> norm_num
  have hwide_sum :
      (((Finset.Icc ⌈R / 72⌉ ⌊16 * R⌋).filter P).card : ℝ) =
        ∑ n ∈ Finset.Icc ⌈t⌉ ⌊16 * R⌋, f n := by
    rw [htdef]
    exact sec7_card_filter_eq_sum_indicator _ P
  have hfirst_sum :
      ∑ n ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋, f n ≤
        ∑ k ∈ Finset.range 10,
          ∑ n ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f n := by
    simpa using sec7_dyadic_cover_sum f hf t ht 9
  have hcover :
      Finset.Icc ⌈t⌉ ⌊16 * R⌋ ⊆
        Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋ ∪
          Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋ := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    by_cases hle : a ≤ ⌊t * 2 ^ (10 : ℕ)⌋
    · exact Or.inl ⟨ha.1, hle⟩
    · refine Or.inr ⟨?_, ha.2⟩
      have h1 : ⌈t * 2 ^ (10 : ℕ)⌉ ≤ ⌊t * 2 ^ (10 : ℕ)⌋ + 1 :=
        Int.ceil_le_floor_add_one _
      omega
  have hsplit :
      ∑ n ∈ Finset.Icc ⌈t⌉ ⌊16 * R⌋, f n ≤
        (∑ n ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋, f n) +
          ∑ n ∈ Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋, f n := by
    calc
      ∑ n ∈ Finset.Icc ⌈t⌉ ⌊16 * R⌋, f n
          ≤ ∑ n ∈ (Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋ ∪
              Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋), f n :=
            Finset.sum_le_sum_of_subset_of_nonneg hcover (fun a _ _ => hf a)
      _ ≤ (∑ n ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋, f n) +
            ∑ n ∈ Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋, f n := by
            set s₁ := Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋ with hs₁
            set s₂ := Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋ with hs₂
            have hui : (∑ x ∈ s₁ ∪ s₂, f x) + ∑ x ∈ s₁ ∩ s₂, f x =
                (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := Finset.sum_union_inter
            have hinter : 0 ≤ ∑ a ∈ (s₁ ∩ s₂), f a :=
              Finset.sum_nonneg (fun a _ => hf a)
            linarith
  have hblocks :
      ∑ k ∈ Finset.range 10,
          ∑ n ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f n ≤
        ∑ _k ∈ Finset.range 10, B := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk' := hblock k hk
    rw [htdef] at hk'
    rw [sec7_card_filter_eq_sum_indicator] at hk'
    simpa [f] using hk'
  have hlast_sum :
      ∑ n ∈ Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋, f n ≤ B := by
    have h := hlast
    rw [htdef] at h
    rw [sec7_card_filter_eq_sum_indicator] at h
    simpa [f] using h
  rw [hwide_sum]
  calc
    ∑ n ∈ Finset.Icc ⌈t⌉ ⌊16 * R⌋, f n
        ≤ (∑ n ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (10 : ℕ)⌋, f n) +
            ∑ n ∈ Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋, f n := hsplit
    _ ≤ (∑ k ∈ Finset.range 10,
            ∑ n ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f n) +
          ∑ n ∈ Finset.Icc ⌈t * 2 ^ (10 : ℕ)⌉ ⌊16 * R⌋, f n := by gcongr
    _ ≤ (∑ _k ∈ Finset.range 10, B) + B := add_le_add hblocks hlast_sum
    _ = 11 * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num; ring

private theorem sec7_dyadic_block_subset_wide {P : Globals} {S : Scale P}
    {xl xu : ℝ} (hxl0 : 0 ≤ xl) (hxu0 : 0 ≤ xu)
    (hlo : S.R / 72 ≤ xl) (hhi : xu ≤ 16 * S.R) :
    Finset.Icc ((⌈xl⌉₊ : ℕ) : ℤ) ((⌊xu⌋₊ : ℕ) : ℤ) ⊆
      Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋ := by
  intro n hn
  rw [Finset.mem_Icc] at hn ⊢
  have hpcast : (((⌈xl⌉₊ : ℕ) : ℤ) : ℝ) = (⌈xl⌉ : ℤ) := by
    rw [Int.natCast_ceil_eq_ceil hxl0]
  have hqcast : (((⌊xu⌋₊ : ℕ) : ℤ) : ℝ) = (⌊xu⌋ : ℤ) := by
    rw [Int.natCast_floor_eq_floor hxu0]
  constructor
  · apply Int.ceil_le.mpr
    have hnlo : (((⌈xl⌉₊ : ℕ) : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hxlceil : xl ≤ (⌈xl⌉ : ℤ) := Int.le_ceil xl
    linarith
  · apply Int.le_floor.mpr
    have hnhi : (n : ℝ) ≤ (((⌊xu⌋₊ : ℕ) : ℤ) : ℝ) := by exact_mod_cast hn.2
    have hfloorxu : ((⌊xu⌋ : ℤ) : ℝ) ≤ xu := Int.floor_le xu
    linarith

private theorem sec7_dyadic_block_dyad {xl xu : ℝ} (hxl0 : 0 ≤ xl) (hxu0 : 0 ≤ xu)
    (hxu : xu ≤ 2 * xl) :
    ⌊xu⌋₊ ≤ 2 * ⌈xl⌉₊ := by
  have hq : (⌊xu⌋₊ : ℝ) ≤ xu := Nat.floor_le hxu0
  have hp : xl ≤ (⌈xl⌉₊ : ℝ) := Nat.le_ceil xl
  have hR : (⌊xu⌋₊ : ℝ) ≤ (2 * ⌈xl⌉₊ : ℕ) := by
    norm_num
    nlinarith
  exact_mod_cast hR

private theorem sec7_zero_wide_count {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    (hxsmall : S.x ^ 2 * S.Ω ≤ P.H * P.G)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) :
    (((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter (fun n : ℤ =>
        Counting.distInt
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 11 * sec7_cN13 *
        (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) /
            Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
            Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
          sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
          1) := by
  classical
  have hR : 0 < S.R := sec7_R_pos S
  set B : ℝ := sec7_cN13 *
        (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) /
            Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
            Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
          sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
          1) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have hHpos : 0 < P.H := P.H_pos
    have hGpos : 0 < P.G := P.G_pos
    have hΩpos : 0 < S.Ω := S.Ω_pos
    have hxpos : 0 < S.x := OnStripAux.x_pos P S
    have hh₁0 : (0 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast (le_trans (by norm_num) Hyp.hbox.1.1)
    have hh₂0 : (0 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast (le_trans (by norm_num) Hyp.hbox.2.1.1)
    have hh₃0 : (0 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast (le_trans (by norm_num) Hyp.hbox.2.2.1)
    have hh₁pos : (0 : ℝ) < (h₁ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one Hyp.hbox.1.1)
    have hh₂pos : (0 : ℝ) < (h₂ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one Hyp.hbox.2.1.1)
    have hh₃pos : (0 : ℝ) < (h₃ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one Hyp.hbox.2.2.1)
    have hPPpos : 0 < sec7_Pprod h₁ h₂ h₃ := by
      simp only [sec7_Pprod]
      exact mul_pos (mul_pos hh₁pos hh₂pos) hh₃pos
    have hSsym0 : 0 ≤ sec7_Ssym h₁ h₂ h₃ := by
      simp only [sec7_Ssym]
      nlinarith
    have hHsum0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
      simp only [sec7_hSum]
      linarith
    have hratio0 : 0 ≤ sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃ :=
      div_nonneg hSsym0 hPPpos.le
    have hden3 : 0 ≤ S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4 := by positivity
    have hA1 : 0 ≤ P.G * S.Ω / S.x ^ 2 :=
      div_nonneg (mul_nonneg hGpos.le hΩpos.le) (sq_nonneg S.x)
    have hA2 : 0 ≤ S.Ω ^ 2 / P.H :=
      div_nonneg (sq_nonneg S.Ω) hHpos.le
    have hA3 : 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
      exact div_nonneg hSsym0 hden3
    have hA4 : 0 ≤
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
          S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) := by
      exact div_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hA5 : 0 ≤
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
          Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) := by
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hA6 : 0 ≤ sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
      exact div_nonneg hHsum0 hden3
    have hA7 : 0 ≤ sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) := by
      exact div_nonneg hPPpos.le (by positivity)
    have hbody : 0 ≤
        (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
            S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
            Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
          sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
          1) := by
      nlinarith
    exact mul_nonneg (by norm_num [sec7_cN13]) hbody
  have htarget :
      11 * B = 11 * sec7_cN13 *
        (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) /
            Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
            Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
          sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
          1) := by
    rw [hBdef]
    ring
  rw [← htarget]
  apply sec7_wide_filter_dyadic_bound (R := S.R) hR hB0
  · intro k hk
    set xl : ℝ := (S.R / 72) * 2 ^ k with hxl
    set xu : ℝ := (S.R / 72) * 2 ^ (k + 1) with hxu
    have hxl0 : 0 ≤ xl := by rw [hxl]; positivity
    have hxu0 : 0 ≤ xu := by rw [hxu]; positivity
    have hk9 : k ≤ 9 := by
      have : k < 10 := Finset.mem_range.mp hk
      omega
    have hlo : S.R / 72 ≤ xl := by
      rw [hxl]
      have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact le_mul_of_one_le_right (by positivity) hpow
    have hhi : xu ≤ 16 * S.R := by
      rw [hxu]
      have hk10 : k + 1 ≤ 10 := by omega
      have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (10 : ℕ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk10
      calc (S.R / 72) * 2 ^ (k + 1)
          ≤ (S.R / 72) * 2 ^ (10 : ℕ) := by gcongr
        _ ≤ 16 * S.R := by norm_num; nlinarith [hR]
    have hdy : ⌊xu⌋₊ ≤ 2 * ⌈xl⌉₊ := by
      apply sec7_dyadic_block_dyad hxl0 hxu0
      rw [hxl, hxu]
      ring_nf
      exact le_rfl
    have hwin := sec7_dyadic_block_subset_wide (S := S) hxl0 hxu0 hlo hhi
    have hcnt := sec7_zero_triple_count (ME := ME) Hyp hxsmall hδ0 hδ
      ⌈xl⌉₊ ⌊xu⌋₊ hwin hdy
    have hceil : ((⌈xl⌉₊ : ℕ) : ℤ) = ⌈xl⌉ := Int.natCast_ceil_eq_ceil hxl0
    have hfloor : ((⌊xu⌋₊ : ℕ) : ℤ) = ⌊xu⌋ := Int.natCast_floor_eq_floor hxu0
    have hcnt' :
        (((Finset.Icc ⌈xl⌉ ⌊xu⌋).filter (fun n : ℤ =>
            Counting.distInt
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B := by
      simpa [B, hBdef, hceil, hfloor] using hcnt
    simpa [hxl, hxu] using hcnt'
  · set xl : ℝ := (S.R / 72) * 2 ^ (10 : ℕ) with hxl
    set xu : ℝ := 16 * S.R with hxu
    have hxl0 : 0 ≤ xl := by rw [hxl]; positivity
    have hxu0 : 0 ≤ xu := by rw [hxu]; positivity
    have hlo : S.R / 72 ≤ xl := by
      rw [hxl]
      have hpow : (1 : ℝ) ≤ 2 ^ (10 : ℕ) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact le_mul_of_one_le_right (by positivity) hpow
    have hhi : xu ≤ 16 * S.R := by rw [hxu]
    have hdy : ⌊xu⌋₊ ≤ 2 * ⌈xl⌉₊ := by
      apply sec7_dyadic_block_dyad hxl0 hxu0
      rw [hxl, hxu]
      norm_num
      nlinarith [hR]
    have hwin := sec7_dyadic_block_subset_wide (S := S) hxl0 hxu0 hlo hhi
    have hcnt := sec7_zero_triple_count (ME := ME) Hyp hxsmall hδ0 hδ
      ⌈xl⌉₊ ⌊xu⌋₊ hwin hdy
    have hceil : ((⌈xl⌉₊ : ℕ) : ℤ) = ⌈xl⌉ := Int.natCast_ceil_eq_ceil hxl0
    have hfloor : ((⌊xu⌋₊ : ℕ) : ℤ) = ⌊xu⌋ := Int.natCast_floor_eq_floor hxu0
    have hcnt' :
        (((Finset.Icc ⌈xl⌉ ⌊xu⌋).filter (fun n : ℤ =>
            Counting.distInt
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B := by
      simpa [B, hBdef, hceil, hfloor] using hcnt
    simpa [hxl, hxu] using hcnt'

private theorem sec7_cover_card_bound {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset α) (Λ : Finset ι) (T : ι → Finset α)
    (hcover : ∀ x ∈ s, ∃ i ∈ Λ, x ∈ T i) :
    (s.card : ℝ) ≤ ∑ i ∈ Λ, ((T i).card : ℝ) := by
  classical
  have hsub : s ⊆ Λ.biUnion T := by
    intro x hx
    obtain ⟨i, hiΛ, hxi⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨i, hiΛ, hxi⟩
  calc
    (s.card : ℝ) ≤ ((Λ.biUnion T).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Λ, ((T i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le

private theorem sec7_cover_card_mul_bound {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset α) (Λ : Finset ι) (T : ι → Finset α) (B : ℝ)
    (hcover : ∀ x ∈ s, ∃ i ∈ Λ, x ∈ T i)
    (hT : ∀ i ∈ Λ, ((T i).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ (Λ.card : ℝ) * B := by
  calc
    (s.card : ℝ) ≤ ∑ i ∈ Λ, ((T i).card : ℝ) :=
      sec7_cover_card_bound s Λ T hcover
    _ ≤ ∑ _i ∈ Λ, B := Finset.sum_le_sum hT
    _ = (Λ.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

private theorem sec7_mem_wide_real {P : Globals} {S : Scale P} {r : ℤ}
    (hr : r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋) :
    (r : ℝ) ∈ Set.Icc (S.R / 72) (16 * S.R) := by
  rw [Finset.mem_Icc] at hr
  constructor
  · exact le_trans (Int.le_ceil (S.R / 72)) (by exact_mod_cast hr.1)
  · exact le_trans (by exact_mod_cast hr.2) (Int.floor_le (16 * S.R))

private theorem sec7_delta1_pos {P : Globals} {S : Scale P} {W : ℝ}
    {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    0 < sec7_delta1 P S h₁ h₂ h₃ := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hA : 0 < S.A := by unfold Scale.A; positivity
  have hδ0 : 0 < sec7_delta0 P S := by
    rw [sec7_delta0_eq P S]
    have h1 : 0 < S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) := by positivity
    have h2 : 0 ≤ S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A) := by positivity
    linarith
  have hS0 : 0 ≤ sec7_Ssym h₁ h₂ h₃ := by
    have h10 : (0 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.1.1)
    have h20 : (0 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.1.1)
    have h30 : (0 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.2.1)
    simp only [sec7_Ssym]
    nlinarith [mul_nonneg h10 h20, mul_nonneg h10 h30, mul_nonneg h20 h30]
  have htail : 0 ≤ sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2 :=
    div_nonneg (mul_nonneg hS0 (sec7_T₁_pos S).le) (sq_nonneg S.R)
  rw [sec7_delta1]
  linarith

private theorem sec7_T₁_div_R_eval_local {P : Globals} (S : Scale P) :
    S.T₁ / S.R = 1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.T₁ Scale.F Scale.R Scale.x
  field_simp

private theorem sec7_R_delta0_eq_local (P : Globals) (S : Scale P) :
    S.R * sec7_delta0 P S = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold sec7_delta0 Scale.R Scale.x Scale.A
  field_simp

private theorem sec7_R_delta1_eq_local (P : Globals) (S : Scale P) (h₁ h₂ h₃ : ℤ) :
    S.R * sec7_delta1 P S h₁ h₂ h₃ =
      P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
        sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
  have hR := sec7_R_pos S
  calc
    S.R * sec7_delta1 P S h₁ h₂ h₃
        = S.R * sec7_delta0 P S +
            S.R * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) := by
          rw [sec7_delta1]
          ring
    _ = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            S.R * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) := by
          rw [sec7_R_delta0_eq_local]
    _ = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ * (S.T₁ / S.R) := by
          congr 1
          field_simp [hR.ne']
    _ = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
          rw [sec7_T₁_div_R_eval_local]
          ring

private theorem sec7_rpow_five_halves_local {x : ℝ} (hx : 0 < x) :
    x ^ ((5:ℝ)/2) = x ^ ((1:ℝ)/2) * x ^ 2 := by
  calc
    x ^ ((5:ℝ)/2) = x ^ ((1:ℝ)/2 + 2) := by norm_num
    _ = x ^ ((1:ℝ)/2) * x ^ (2:ℝ) := by rw [Real.rpow_add hx]
    _ = x ^ ((1:ℝ)/2) * x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

private theorem sec7_R_mono_nat_local {P : Globals} (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
  rw [OnStripAux.R_mono P S, Real.rpow_one]
  rw [show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]]

private theorem sec7_T₁_div_R_sq_eval_local {P : Globals} (S : Scale P) :
    S.T₁ / S.R ^ 2 =
      1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hR : 0 < S.R := sec7_R_pos S
  calc
    S.T₁ / S.R ^ 2 = (S.T₁ / S.R) / S.R := by
      field_simp [hR.ne']
    _ = (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.R := by
      rw [sec7_T₁_div_R_eval_local]
    _ = 1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4 * S.R) := by ring
    _ = 1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7) := by
      rw [← sec7_R_mono_nat_local S]
      rw [sec7_rpow_five_halves_local hx]
      ring_nf

private theorem sec7_Hx_half_local (P : Globals) (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) = P.H / S.Δ := by
  have hH := P.H_pos; have hΔ := S.Δ_pos
  have hx := OnStripAux.x_pos P S
  rw [← Real.mul_rpow hH.le hx.le]
  have hHx : P.H * S.x = (P.H / S.Δ) ^ (2:ℕ) := by
    unfold Scale.x
    field_simp [hΔ.ne']
  rw [hHx, ← Real.rpow_natCast (P.H / S.Δ) 2, ← Real.rpow_mul (by positivity)]
  norm_num

private theorem sec7_delta0_side_eq (P : Globals) (S : Scale P) :
    sec7_delta0 P S =
      1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2) +
        1 / (P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hHx := sec7_Hx_half_local P S
  rw [sec7_delta0_eq P S]
  have hH32 : P.H ^ ((3:ℝ)/2) = P.H ^ ((1:ℝ)/2) * P.H := by
    calc
      P.H ^ ((3:ℝ)/2) = P.H ^ ((1:ℝ)/2 + 1) := by norm_num
      _ = P.H ^ ((1:ℝ)/2) * P.H ^ (1:ℝ) := by rw [Real.rpow_add hH]
      _ = P.H ^ ((1:ℝ)/2) * P.H := by rw [Real.rpow_one]
  have ht1 :
      1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2) =
        S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) := by
    rw [sec7_rpow_five_halves_local hx]
    rw [show P.H ^ ((1:ℝ)/2) * (S.x ^ ((1:ℝ)/2) * S.x ^ 2) * S.Ω ^ 2 =
        (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2)) * S.x ^ 2 * S.Ω ^ 2 by ring]
    rw [hHx]
    unfold Scale.x
    field_simp [hH.ne', hΔ.ne', hΩ.ne']
  have ht2 :
      1 / (P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω) =
        S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A) := by
    rw [hH32]
    rw [show (P.H ^ ((1:ℝ)/2) * P.H) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω =
        P.H * (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2)) * P.G * S.Ω by ring]
    rw [hHx]
    unfold Scale.A
    field_simp [hH.ne', hG.ne', hΔ.ne', hΩ.ne']
  rw [← ht1, ← ht2]

private theorem sec7_sqrt_le_of_sq_local {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  have hsq := sq_le_sq.mp h
  rwa [abs_of_nonneg hx, abs_of_nonneg hy] at hsq

private theorem sec7_sqrt_add_le_local (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply sec7_sqrt_le_of_sq_local (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [Real.sq_sqrt (add_nonneg hx hy)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

private theorem sec7_cCal_delta1_lt_one {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ < 1 := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  let t₁ : ℝ := 1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2)
  let t₂ : ℝ := 1 / (P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω)
  let t₃ : ℝ := W ^ 6 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7)
  have ht₁0 : 0 ≤ t₁ := by dsimp [t₁]; positivity
  have ht₂0 : 0 ≤ t₂ := by dsimp [t₂]; positivity
  have ht₃0 : 0 ≤ t₃ := by dsimp [t₃]; positivity
  have h10 : (0 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.1.1)
  have h20 : (0 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.1.1)
  have h30 : (0 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.2.1)
  have h12 : (h₁ : ℝ) * h₂ ≤ W ^ 6 := by
    calc
      (h₁ : ℝ) * h₂ ≤ W * W ^ 2 :=
        mul_le_mul hbox.1.2 hbox.2.1.2 h20 hW0
      _ = W ^ 3 := by ring
      _ ≤ W ^ 6 := pow_le_pow_right₀ hW (by norm_num)
  have h13 : (h₁ : ℝ) * h₃ ≤ W ^ 6 := by
    calc
      (h₁ : ℝ) * h₃ ≤ W * W ^ 4 :=
        mul_le_mul hbox.1.2 hbox.2.2.2 h30 hW0
      _ = W ^ 5 := by ring
      _ ≤ W ^ 6 := pow_le_pow_right₀ hW (by norm_num)
  have h23 : (h₂ : ℝ) * h₃ ≤ W ^ 6 := by
    calc
      (h₂ : ℝ) * h₃ ≤ W ^ 2 * W ^ 4 :=
        mul_le_mul hbox.2.1.2 hbox.2.2.2 h30 (pow_nonneg hW0 2)
      _ = W ^ 6 := by ring
  have hSle : sec7_Ssym h₁ h₂ h₃ ≤ 3 * W ^ 6 := by
    simp only [sec7_Ssym]
    nlinarith
  have htail :
      sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2 ≤ 3 * t₃ := by
    rw [show sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2 =
      sec7_Ssym h₁ h₂ h₃ * (S.T₁ / S.R ^ 2) by ring]
    rw [sec7_T₁_div_R_sq_eval_local]
    dsimp [t₃]
    have hden0 :
        0 ≤ 1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7) := by
      positivity
    calc
      sec7_Ssym h₁ h₂ h₃ *
          (1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7))
          ≤ (3 * W ^ 6) *
            (1 / (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7)) :=
            mul_le_mul_of_nonneg_right hSle hden0
      _ = 3 * (W ^ 6 /
            (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7)) := by ring
  have hδleSide :
      sec7_delta1 P S h₁ h₂ h₃ ≤ t₁ + t₂ + 3 * t₃ := by
    rw [sec7_delta1, sec7_delta0_side_eq P S]
    dsimp [t₁, t₂] at *
    nlinarith
  have hXgt : 1 < P.X := by
    by_contra h
    have h' : P.X ≤ 1 := not_lt.mp h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one P.X_pos.le h' (by norm_num)
    linarith
  have hbud' : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2 := hbud
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu0.le (by linarith [hsd.hCu])
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu0.le (by linarith [hsd.hCu])
  have e1 : P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * S.Ω ^ 2
      = P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ (0:ℝ) * S.Ω ^ (2:ℝ) := by
    rw [Real.rpow_zero, mul_one, ← Real.rpow_natCast S.Ω 2]
    norm_num
  have ht1small : t₁ ≤ 1 / 10 ^ 50 := by
    dsimp [t₁]
    rw [e1]
    exact sec7_inv_small_local P S c₀ Cu hsd hXgt hX24 _ _ _ _
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg0, hu0, huCu, huCu1])
  have e2 : P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω
      = P.H ^ ((3:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (1:ℝ) * S.Ω ^ (1:ℝ) := by
    rw [Real.rpow_one, Real.rpow_one]
  have ht2small : t₂ ≤ 1 / 10 ^ 50 := by
    dsimp [t₂]
    rw [e2]
    exact sec7_inv_small_local P S c₀ Cu hsd hXgt hX24 _ _ _ _
      (by unfold OnStripAux.ratioExp; norm_num
          nlinarith [hbud', hg0, hu0, huCu, huCu1])
  have hMpos :
      (0:ℝ) < P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7 := by
    positivity
  have ht3small : t₃ ≤ 1 / sec7_envC := by
    dsimp [t₃]
    rw [div_le_div_iff₀ hMpos sec7_envC_pos]
    have hWp : W ^ 6 ≤ W ^ 12 := pow_le_pow_right₀ hW (by norm_num)
    nlinarith [Env.off1, hWp, sec7_envC_pos]
  calc
    sec7_cCal * sec7_delta1 P S h₁ h₂ h₃
        ≤ sec7_cCal * (t₁ + t₂ + 3 * t₃) := by
          exact mul_le_mul_of_nonneg_left hδleSide sec7_cCal_pos.le
    _ ≤ sec7_cCal * (1 / 10 ^ 50 + 1 / 10 ^ 50 + 3 * (1 / sec7_envC)) := by
          exact mul_le_mul_of_nonneg_left
            (by nlinarith [ht1small, ht2small, ht3small]) sec7_cCal_pos.le
    _ < 1 := by norm_num [sec7_cCal, sec7_envC]

private theorem sec7_nonzero_wide_count {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (Env : Sec7Envelope P S W) (hW : 1 < W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ))
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hj : sec7_jBand P S j) (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hρ₀ne : ρ₀ ≠ 0) (hρ₀ : |(ρ₀ : ℝ)| ≤ sec7_cCarry)
    (hρ₁ : |(ρ₁ : ℝ)| ≤ sec7_cCarry) (hρ₂ : |(ρ₂ : ℝ)| ≤ sec7_cCarry)
    (hρ₃ : |(ρ₃ : ℝ)| ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) :
    (((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter (fun n : ℤ =>
        Counting.distInt
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤
            sec7_cCal * sec7_delta1 P S h₁ h₂ h₃)).card : ℝ)
      ≤ 11 * sec7_cN19 * (1 + Real.log P.X) *
        ((S.R * S.T₁) ^ ((1:ℝ)/3) +
          S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
          S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1) := by
  classical
  have hR : 0 < S.R := sec7_R_pos S
  have hδpos : 0 < sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ :=
    mul_pos sec7_cCal_pos (sec7_delta1_pos hbox)
  have hδlt : sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ < 1 :=
    sec7_cCal_delta1_lt_one Env hW.le hbox c₀ Cu hsd hbud hg0 hu0 hX24
  have hWpos : 0 < W := by linarith
  have hs_nonneg : 0 ≤ W + W ^ 2 + W ^ 4 := by positivity
  have hmargin : W + W ^ 2 + W ^ 4 ≤ S.R / 2000 :=
    sec7_shift_margin Env hW.le c₀ Cu hsd
  have hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288 := by
    nlinarith [hmargin, hR]
  have hsum_le : sec7_hSum h₁ h₂ h₃ ≤ W + W ^ 2 + W ^ 4 := by
    simp only [sec7_hSum]
    linarith [hbox.1.2, hbox.2.1.2, hbox.2.2.2]
  have hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4) := by
    nlinarith
  have hrel143 : sec7_relErr P S * 10 ^ 143 ≤ 1 :=
    sec7_relErr_le Env hW.le hsd hbud hg0 hu0 hX24
  have hcover : ∀ y : ℝ, S.R / 144 ≤ y → y ≤ 40 * S.R → y ∈ sec7_rWin S W := by
    intro y hylo hyhi
    rw [sec7_rWin, Set.mem_Icc]
    constructor <;> nlinarith [hylo, hyhi, hs_nonneg]
  have hErr := sec7_err_deriv_bound (ME := ME) Env hj hbox hWpos hpad hshift hrel143 hξ₁ hξ₂ hξ₃
    ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ₀ hρ₁ hρ₂ hρ₃ hu₁ hu₂ hu₃
  have hcd := sec7_phase_phi_contDiff Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃
  set δ : ℝ := sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ with hδdef
  set B : ℝ := sec7_cN19 * (1 + Real.log P.X) *
        ((S.R * S.T₁) ^ ((1:ℝ)/3) + S.R * δ +
          S.R * Real.sqrt (δ / S.T₁) + 1) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have hlogfac : 0 ≤ 1 + Real.log P.X := by
      have hlog : 0 ≤ Real.log P.X := Real.log_nonneg hsd.hX
      linarith
    have hbr : 0 ≤ (S.R * S.T₁) ^ ((1:ℝ)/3) + S.R * δ +
        S.R * Real.sqrt (δ / S.T₁) + 1 := by
      have hRT0 : 0 ≤ S.R * S.T₁ := mul_nonneg hR.le (sec7_T₁_pos S).le
      have h1 : 0 ≤ (S.R * S.T₁) ^ ((1:ℝ)/3) := Real.rpow_nonneg hRT0 _
      have h2 : 0 ≤ S.R * δ := mul_nonneg hR.le (by rw [hδdef]; exact hδpos.le)
      have h3 : 0 ≤ S.R * Real.sqrt (δ / S.T₁) := mul_nonneg hR.le (Real.sqrt_nonneg _)
      nlinarith
    exact mul_nonneg (mul_nonneg (by norm_num [sec7_cN19]) hlogfac) hbr
  have htarget :
      11 * B = 11 * sec7_cN19 * (1 + Real.log P.X) *
        ((S.R * S.T₁) ^ ((1:ℝ)/3) +
          S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
          S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1) := by
    rw [hBdef, hδdef]
    ring
  rw [← htarget]
  apply sec7_wide_filter_dyadic_bound (R := S.R) hR hB0
  · intro k hk
    set xl : ℝ := (S.R / 72) * 2 ^ k with hxl
    set xu : ℝ := (S.R / 72) * 2 ^ (k + 1) with hxu
    have hxl0 : 0 ≤ xl := by rw [hxl]; positivity
    have hxu0 : 0 ≤ xu := by rw [hxu]; positivity
    have hk9 : k ≤ 9 := by
      have : k < 10 := Finset.mem_range.mp hk
      omega
    have hlo : S.R / 72 ≤ xl := by
      rw [hxl]
      have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact le_mul_of_one_le_right (by positivity) hpow
    have hhi : xu ≤ 16 * S.R := by
      rw [hxu]
      have hk10 : k + 1 ≤ 10 := by omega
      have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (10 : ℕ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk10
      calc (S.R / 72) * 2 ^ (k + 1)
          ≤ (S.R / 72) * 2 ^ (10 : ℕ) := by gcongr
        _ ≤ 16 * S.R := by norm_num; nlinarith [hR]
    have hdy : ⌊xu⌋₊ ≤ 2 * ⌈xl⌉₊ := by
      apply sec7_dyadic_block_dyad hxl0 hxu0
      rw [hxl, hxu]
      ring_nf
      exact le_rfl
    have hwin := sec7_dyadic_block_subset_wide (S := S) hxl0 hxu0 hlo hhi
    have hcnt := sec7_nonzero_count_78 P S W Env hW c₀ Cu hsd hbud hg0 hu0 hX24
      a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ME hj hbox hpad hshift hξ₁ hξ₂ hξ₃
      ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ₀ne hρ₀ hρ₁ hρ₂ hρ₃ hu₁ hu₂ hu₃ hErr hcd
      ⌈xl⌉₊ ⌊xu⌋₊ hwin hdy hcover δ (by rw [hδdef]; exact hδpos) (by rw [hδdef]; exact hδlt)
    have hceil : ((⌈xl⌉₊ : ℕ) : ℤ) = ⌈xl⌉ := Int.natCast_ceil_eq_ceil hxl0
    have hfloor : ((⌊xu⌋₊ : ℕ) : ℤ) = ⌊xu⌋ := Int.natCast_floor_eq_floor hxu0
    have hcnt' :
        (((Finset.Icc ⌈xl⌉ ⌊xu⌋).filter (fun n : ℤ =>
            Counting.distInt
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B := by
      simpa [B, hBdef, hceil, hfloor] using hcnt
    simpa [hxl, hxu, hδdef] using hcnt'
  · set xl : ℝ := (S.R / 72) * 2 ^ (10 : ℕ) with hxl
    set xu : ℝ := 16 * S.R with hxu
    have hxl0 : 0 ≤ xl := by rw [hxl]; positivity
    have hxu0 : 0 ≤ xu := by rw [hxu]; positivity
    have hlo : S.R / 72 ≤ xl := by
      rw [hxl]
      have hpow : (1 : ℝ) ≤ 2 ^ (10 : ℕ) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact le_mul_of_one_le_right (by positivity) hpow
    have hhi : xu ≤ 16 * S.R := by rw [hxu]
    have hdy : ⌊xu⌋₊ ≤ 2 * ⌈xl⌉₊ := by
      apply sec7_dyadic_block_dyad hxl0 hxu0
      rw [hxl, hxu]
      norm_num
      nlinarith [hR]
    have hwin := sec7_dyadic_block_subset_wide (S := S) hxl0 hxu0 hlo hhi
    have hcnt := sec7_nonzero_count_78 P S W Env hW c₀ Cu hsd hbud hg0 hu0 hX24
      a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ME hj hbox hpad hshift hξ₁ hξ₂ hξ₃
      ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ₀ne hρ₀ hρ₁ hρ₂ hρ₃ hu₁ hu₂ hu₃ hErr hcd
      ⌈xl⌉₊ ⌊xu⌋₊ hwin hdy hcover δ (by rw [hδdef]; exact hδpos) (by rw [hδdef]; exact hδlt)
    have hceil : ((⌈xl⌉₊ : ℕ) : ℤ) = ⌈xl⌉ := Int.natCast_ceil_eq_ceil hxl0
    have hfloor : ((⌊xu⌋₊ : ℕ) : ℤ) = ⌊xu⌋ := Int.natCast_floor_eq_floor hxu0
    have hcnt' :
        (((Finset.Icc ⌈xl⌉ ⌊xu⌋).filter (fun n : ℤ =>
            Counting.distInt
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B := by
      simpa [B, hBdef, hceil, hfloor] using hcnt
    simpa [hxl, hxu, hδdef] using hcnt'

private theorem sec7_nonzero_bracket_eval_bound {P : Globals} {S : Scale P}
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ))
    {h₁ h₂ h₃ : ℤ} (hSsym0 : 0 ≤ sec7_Ssym h₁ h₂ h₃) :
    (S.R * S.T₁) ^ ((1:ℝ)/3) +
        S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
        S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1
      ≤ (10 : ℝ) ^ 20 *
        (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
          + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
          + sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
          + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
          + S.x * P.G * S.Ω ^ 3
          + Real.sqrt (sec7_Ssym h₁ h₂ h₃)
          + 1) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hT1pos : 0 < S.T₁ := sec7_T₁_pos S
  have hRpos : 0 < S.R := sec7_R_pos S
  let body : ℝ :=
    P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
      + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
      + sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
      + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
      + S.x * P.G * S.Ω ^ 3
      + Real.sqrt (sec7_Ssym h₁ h₂ h₃)
      + 1
  have hbody0 : 0 ≤ body := by
    dsimp [body]
    linarith [show 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) by positivity,
      show 0 ≤ P.G * S.Ω / S.x ^ 2 by positivity,
      show 0 ≤ S.Ω ^ 2 / P.H by positivity,
      show 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) by positivity,
      show 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) by positivity,
      show 0 ≤ S.x * P.G * S.Ω ^ 3 by positivity,
      Real.sqrt_nonneg (sec7_Ssym h₁ h₂ h₃)]
  have hA0 :
      P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) ≤ body := by
    dsimp [body]
    linarith [show 0 ≤ P.G * S.Ω / S.x ^ 2 by positivity,
      show 0 ≤ S.Ω ^ 2 / P.H by positivity,
      show 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) by positivity,
      show 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) by positivity,
      show 0 ≤ S.x * P.G * S.Ω ^ 3 by positivity,
      Real.sqrt_nonneg (sec7_Ssym h₁ h₂ h₃)]
  have hA123 :
      P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
        sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) ≤ body := by
    dsimp [body]
    linarith [show 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) by positivity,
      show 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) by positivity,
      show 0 ≤ S.x * P.G * S.Ω ^ 3 by positivity,
      Real.sqrt_nonneg (sec7_Ssym h₁ h₂ h₃)]
  have hA4 : P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) ≤ body := by
    dsimp [body]
    linarith [show 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) by positivity,
      show 0 ≤ P.G * S.Ω / S.x ^ 2 by positivity,
      show 0 ≤ S.Ω ^ 2 / P.H by positivity,
      show 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) by positivity,
      show 0 ≤ S.x * P.G * S.Ω ^ 3 by positivity,
      Real.sqrt_nonneg (sec7_Ssym h₁ h₂ h₃)]
  have hAsqrt : Real.sqrt (sec7_Ssym h₁ h₂ h₃) ≤ body := by
    dsimp [body]
    linarith [show 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) by positivity,
      show 0 ≤ P.G * S.Ω / S.x ^ 2 by positivity,
      show 0 ≤ S.Ω ^ 2 / P.H by positivity,
      show 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) by positivity,
      show 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) by positivity,
      show 0 ≤ S.x * P.G * S.Ω ^ 3 by positivity]
  have hOne : (1 : ℝ) ≤ body := by
    dsimp [body]
    linarith [show 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) by positivity,
      show 0 ≤ P.G * S.Ω / S.x ^ 2 by positivity,
      show 0 ≤ S.Ω ^ 2 / P.H by positivity,
      show 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) by positivity,
      show 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) by positivity,
      show 0 ≤ S.x * P.G * S.Ω ^ 3 by positivity,
      Real.sqrt_nonneg (sec7_Ssym h₁ h₂ h₃)]
  obtain ⟨hCube, hD0sqrt, _hOmegaHsqrt, hSvsqrt⟩ :=
    sec7_nonzero_sqrt_evals P S c₀ Cu hsd hbud hg0 hu0 hX24
  have hterm_cube :
      (S.R * S.T₁) ^ ((1:ℝ)/3) ≤ (10 : ℝ) ^ 19 * body := by
    calc
      (S.R * S.T₁) ^ ((1:ℝ)/3)
          ≤ sec7_cN20 * (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) := hCube
      _ ≤ (10 : ℝ) ^ 19 * body := by
        norm_num [sec7_cN20]
        nlinarith [hA0, hbody0]
  have hterm_linear :
      S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) ≤ (10 : ℝ) ^ 19 * body := by
    have hRδ := sec7_R_delta1_eq_local P S h₁ h₂ h₃
    calc
      S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃)
          = sec7_cCal * (S.R * sec7_delta1 P S h₁ h₂ h₃) := by ring
      _ = sec7_cCal * (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) := by rw [hRδ]
      _ ≤ (10 : ℝ) ^ 19 * body := by
        norm_num [sec7_cCal]
        nlinarith [hA123, hbody0]
  have htail_eq :
      sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2 =
        sec7_Ssym h₁ h₂ h₃ / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
    rw [show sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2 =
      sec7_Ssym h₁ h₂ h₃ * (S.T₁ / S.R) / S.R by ring]
    rw [sec7_T₁_div_R_eval_local]
    ring
  have hdelta_decomp :
      sec7_delta1 P S h₁ h₂ h₃ =
        sec7_delta0 P S +
          sec7_Ssym h₁ h₂ h₃ / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
    rw [sec7_delta1, htail_eq]
  have htail0 :
      0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
    positivity
  have hdelta0_nonneg : 0 ≤ sec7_delta0 P S := by
    rw [sec7_delta0_side_eq P S]
    positivity
  have hsCal : Real.sqrt sec7_cCal ≤ (10 : ℝ) ^ 8 := by
    apply sec7_sqrt_le_of_sq_local (Real.sqrt_nonneg _) (by norm_num)
    rw [Real.sq_sqrt sec7_cCal_pos.le]
    norm_num [sec7_cCal]
  have hs_delta1 :
      S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / S.T₁) ≤
        sec7_cN20 * (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) +
          sec7_cN20 * Real.sqrt (sec7_Ssym h₁ h₂ h₃) := by
    have hsplit :
        Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / S.T₁) ≤
          Real.sqrt (sec7_delta0 P S / S.T₁) +
            Real.sqrt ((sec7_Ssym h₁ h₂ h₃ /
              (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁) := by
      rw [hdelta_decomp]
      rw [show (sec7_delta0 P S +
            sec7_Ssym h₁ h₂ h₃ / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁ =
          sec7_delta0 P S / S.T₁ +
            (sec7_Ssym h₁ h₂ h₃ / (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁ by ring]
      exact sec7_sqrt_add_le_local _ _
        (div_nonneg hdelta0_nonneg hT1pos.le) (div_nonneg htail0 hT1pos.le)
    calc
      S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / S.T₁)
          ≤ S.R * (Real.sqrt (sec7_delta0 P S / S.T₁) +
            Real.sqrt ((sec7_Ssym h₁ h₂ h₃ /
              (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁)) :=
            mul_le_mul_of_nonneg_left hsplit hRpos.le
      _ = S.R * Real.sqrt (sec7_delta0 P S / S.T₁) +
            S.R * Real.sqrt ((sec7_Ssym h₁ h₂ h₃ /
              (S.R * S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.T₁) := by ring
      _ ≤ sec7_cN20 * (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) +
            sec7_cN20 * Real.sqrt (sec7_Ssym h₁ h₂ h₃) :=
            add_le_add hD0sqrt (hSvsqrt (sec7_Ssym h₁ h₂ h₃) hSsym0)
  have hterm_sqrt :
      S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) ≤
        (10 : ℝ) ^ 19 * body := by
    calc
      S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁)
          = S.R * (Real.sqrt sec7_cCal *
              Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / S.T₁)) := by
            rw [show (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁ =
              sec7_cCal * (sec7_delta1 P S h₁ h₂ h₃ / S.T₁) by ring]
            rw [Real.sqrt_mul sec7_cCal_pos.le]
      _ = Real.sqrt sec7_cCal *
            (S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / S.T₁)) := by ring
      _ ≤ (10 : ℝ) ^ 8 *
            (sec7_cN20 * (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) +
              sec7_cN20 * Real.sqrt (sec7_Ssym h₁ h₂ h₃)) := by
            exact mul_le_mul hsCal hs_delta1
              (mul_nonneg hRpos.le (Real.sqrt_nonneg _))
              (by positivity)
      _ ≤ (10 : ℝ) ^ 19 * body := by
            norm_num [sec7_cN20]
            nlinarith [hA4, hAsqrt, hbody0]
  have hOne' : (1 : ℝ) ≤ (10 : ℝ) ^ 19 * body := by
    nlinarith [hOne, hbody0]
  have hsum :
      (S.R * S.T₁) ^ ((1:ℝ)/3) +
          S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
          S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1
        ≤ (10 : ℝ) ^ 20 * body := by
    calc
      (S.R * S.T₁) ^ ((1:ℝ)/3) +
          S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
          S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1
          ≤ (10 : ℝ) ^ 19 * body + (10 : ℝ) ^ 19 * body +
              (10 : ℝ) ^ 19 * body + (10 : ℝ) ^ 19 * body := by
            nlinarith [hterm_cube, hterm_linear, hterm_sqrt, hOne']
      _ ≤ (10 : ℝ) ^ 20 * body := by
            nlinarith [hbody0]
  simpa [body] using hsum

/-- G1-AUDIT: dischargeability — the per-triple zero/nonzero-carry split of the cube count
(the N15/N22 `cnt`-hypotheses, instantiated at the eight-corner cube sets of the popular set
`E`). This is the inline composition N6 (ξ's) + N7 (carry/fiber cover, `≤ cFib·(1+S/(GΩ⁵))`
pieces) + N8 (per-corner ⟹ `‖Φ_{ρ,u}‖ ≤ cCal·δ₁`) + per-piece counts N13 (`ρ₀ = 0`) resp.
N16–N20 (`ρ₀ ≠ 0`, with the `(1+log X)` of N19), summed over the cover; dischargeable from
those nodes once their own hypothesis seams (Sec7ZeroHyp's `hcd/hsub/hrel/few_critical`, N19's
Φ₂-pinning from N9–N11) are threaded — wave-3 work, audit at G1/G2.
AM-2 (G1/U4): the count window is the WIDE `[⌈R/72⌉,⌊16R⌋]` and the per-window counts
N13/N19 are dyadic-parameterized (`[p,q] ⊆ [⌈R/72⌉,⌊16R⌋]`, `q ≤ 2p`); the ≤11-window
dyadic sum covering `[R/72,16R]` (ratio 1152 ≤ 2¹¹, ledger U4) happens INSIDE this proof
and is absorbed by `sec7_cTriple` (the `·11` factor in the AM-6 ledger chain).
AM-1: the popular-set threshold is the renormalized `δ₀ ≤ sec7_cTay·sec7_delta0`. -/
private theorem sec7_triple_split (P : Globals) (S : Scale P) (W : ℝ)
    (Env : Sec7Envelope P S W) (hW : 1 < W) (a : ℤ) (Ph : Sec7Phase P S W a)
    (gfun : ℤ → ℝ → ℝ)
    (hg : ∀ (j : ℤ) (r : ℝ),
      gfun j r = Ph.dBreve (Ph.ftil r + j)
        - Ph.dBreve' (Ph.ftil r + j) * Int.fract (Ph.ftil r))
    (δ₀ : ℝ) (_hδ0 : 0 < δ₀) (hδle : δ₀ ≤ sec7_cTay * sec7_delta0 P S)
    (j : ℤ) (hj : sec7_jBand P S j)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    ∃ cz cn : ℕ × ℕ × ℕ → ℝ,
      (∀ p ∈ box W,
        ((sec7_cubeSet ((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
            (fun r => distInt (gfun j (r : ℝ)) ≤ δ₀)) p.1 p.2.1 p.2.2).card : ℝ)
          ≤ cz p + cn p) ∧
      (∀ p ∈ box W,
        cz p ≤ sec7_cTriple * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
          (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
            + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            -- Phase-1f seam: root terms in N13's literal `Real.sqrt` forms (= N15's).
            + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)
                / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)
            + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4
                * Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ))
            + (HSbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            + (Pbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)
            + 1
            + (HSbox p.1 p.2.1 p.2.2 : ℝ) * S.T₁ / S.R)) ∧
      (∀ p ∈ box W,
        cn p ≤ sec7_cTriple * (1 + Real.log P.X)
          * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
          (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
            + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
            + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
            + S.x * P.G * S.Ω ^ 3
            -- Phase-1f seam: residual root term in N20's literal `Real.sqrt` form (= N22's).
            + Real.sqrt (Sbox p.1 p.2.1 p.2.2 : ℝ)
            + 1)) := by
  -- ARB-2 (A4/A6): `hxsmall` is derived HERE from the strip pack — no signature change.
  have hxsmall : S.x ^ 2 * S.Ω ≤ P.H * P.G :=
    sec7_hxsmall P S c₀ Cu hsd hbud hg0 hu0.le hX24
  classical
  let cz : ℕ × ℕ × ℕ → ℝ := fun p =>
    sec7_cTriple * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
      (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
        + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
        + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)
            / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)
        + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4
            * Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ))
        + (HSbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
        + (Pbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)
        + 1
        + (HSbox p.1 p.2.1 p.2.2 : ℝ) * S.T₁ / S.R)
  let cn : ℕ × ℕ × ℕ → ℝ := fun p =>
    sec7_cTriple * (1 + Real.log P.X)
      * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
      (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
        + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
        + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
        + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
        + S.x * P.G * S.Ω ^ 3
        + Real.sqrt (Sbox p.1 p.2.1 p.2.2 : ℝ)
        + 1)
  refine ⟨cz, cn, ?_, ?_, ?_⟩
  · intro p hp
    let h₁ : ℤ := (p.1 : ℤ)
    let h₂ : ℤ := (p.2.1 : ℤ)
    let h₃ : ℤ := (p.2.2 : ℤ)
    have hbox : sec7_shiftBox W h₁ h₂ h₃ := by
      simpa [h₁, h₂, h₃] using sec7_shiftBox_of_box hW.le hp
    have hRpos : 0 < S.R := sec7_R_pos S
    have hs_nonneg : 0 ≤ W + W ^ 2 + W ^ 4 := by positivity
    have hmargin2000 : W + W ^ 2 + W ^ 4 ≤ S.R / 2000 :=
      sec7_shift_margin Env hW.le c₀ Cu hsd
    have hmargin : W + W ^ 2 + W ^ 4 ≤ S.R / 100 := by
      nlinarith [hmargin2000, hRpos]
    have hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288 := by
      nlinarith [hmargin2000, hRpos]
    have hsum_le : sec7_hSum h₁ h₂ h₃ ≤ W + W ^ 2 + W ^ 4 := by
      simp only [sec7_hSum]
      linarith [hbox.1.2, hbox.2.1.2, hbox.2.2.2]
    have hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4) := by
      nlinarith
    let M : ℝ := 2 * (W + W ^ 2 + W ^ 4)
    have hMbranch : W + W ^ 2 + W ^ 4 ≤ M := by
      dsimp [M]
      nlinarith [hs_nonneg]
    have hMcarry : 2 * (W + W ^ 2 + W ^ 4) ≤ M := by
      dsimp [M]
      exact le_rfl
    have hwinFrontier :
        ∀ y : ℝ, S.R / 72 - M ≤ y → y ≤ 16 * S.R + M → y ∈ sec7_rWin S W := by
      intro y hylo hyhi
      dsimp [M] at hylo hyhi
      rw [sec7_rWin, Set.mem_Icc]
      constructor <;> nlinarith [hylo, hyhi, hRpos]
    obtain ⟨ξ₁, ξ₂, ξ₃, hξ₁, hξ₂, hξ₃, hprod⟩ :=
      sec7_third_diff_product_rule Ph Env hj hbox hmargin (M := M) hMbranch hwinFrontier gfun hg
    let RE : Sec7RaExpData P S W a Ph j := sec7_raExpData_of_phase P S W a Ph j hj
    let ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ :=
      sec7_monExp_build RE hbox.1.1 hbox.2.1.1 hbox.2.2.1 hξ₁ hξ₂ hξ₃
        (by linarith : 0 < W) hpad hshift
    obtain ⟨Λ0, hΛ0card, hΛ0zero, hΛ0piece, hΛ0cover⟩ :=
      sec7_carry_fiber_cover_zero Ph Env hj hbox hξ₁ hξ₂ hξ₃ (M := M) hMcarry hwinFrontier
    obtain ⟨Λ, hΛcard, hΛpiece, hΛcover⟩ :=
      sec7_carry_fiber_cover Ph Env hj hbox hξ₁ hξ₂ hξ₃ (M := M) hMcarry hwinFrontier
    let wide : Finset ℤ := Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋
    let E : Finset ℤ := wide.filter (fun r : ℤ => Counting.distInt (gfun j (r : ℝ)) ≤ δ₀)
    let C : Finset ℤ := sec7_cubeSet E p.1 p.2.1 p.2.2
    let topZero : ℤ → Prop := fun r =>
      diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
        diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + (0 : ℝ)
    let C0 : Finset ℤ := C.filter topZero
    let Cn : Finset ℤ := C.filter (fun r => ¬ topZero r)
    have hnear_of_branch :
        ∀ {r : ℤ}
          {pc : ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ))},
          r ∈ C →
          diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
            diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + pc.1.1 →
          diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
            diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
              - pc.2.1.1 + pc.1.2.1 →
          diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
            diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
              - pc.2.1.2.1 + pc.1.2.2.1 →
          diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
            diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
              - pc.2.1.2.2 + pc.1.2.2.2 →
          Counting.distInt
            (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃
              pc.1.1 pc.1.2.1 pc.1.2.2.1 pc.1.2.2.2
              pc.2.1.1 pc.2.1.2.1 pc.2.1.2.2 (r : ℝ))
            ≤ sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ := by
      intro r pc hrC hbr0 hbr1 hbr2 hbr3
      have hcube :
          r ∈ E ∧
            (∀ ε₁ ε₂ ε₃ : ℕ, ε₁ ≤ 1 → ε₂ ≤ 1 → ε₃ ≤ 1 →
              r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ) ∈ E) := by
        simpa [C, sec7_cubeSet] using hrC
      have hEbase : r ∈ wide ∧ Counting.distInt (gfun j (r : ℝ)) ≤ δ₀ := by
        simpa [E] using hcube.1
      have hrwide : r ∈ wide := hEbase.1
      have hcorner : ∀ ε₁ ε₂ ε₃ : ℕ, ε₁ ≤ 1 → ε₂ ≤ 1 → ε₃ ≤ 1 →
          Counting.distInt (gfun j ((r : ℝ) + ε₁ * h₁ + ε₂ * h₂ + ε₃ * h₃)) ≤
            sec7_cTay * sec7_delta0 P S := by
        intro ε₁ ε₂ ε₃ hε₁ hε₂ hε₃
        have hEc := hcube.2 ε₁ ε₂ ε₃ hε₁ hε₂ hε₃
        have hEc' :
            (r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ)) ∈ wide ∧
              Counting.distInt
                (gfun j ((r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ) : ℤ) : ℝ)) ≤ δ₀ := by
          simpa [E] using hEc
        have harg :
            (((r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ) : ℤ) : ℝ)) =
              (r : ℝ) + ε₁ * h₁ + ε₂ * h₂ + ε₃ * h₃ := by
          dsimp [h₁, h₂, h₃]
          push_cast
          ring
        calc
          Counting.distInt (gfun j ((r : ℝ) + ε₁ * h₁ + ε₂ * h₂ + ε₃ * h₃))
              = Counting.distInt
                  (gfun j ((r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ) : ℤ) : ℝ)) := by
                rw [harg]
          _ ≤ δ₀ := hEc'.2
          _ ≤ sec7_cTay * sec7_delta0 P S := hδle
      exact sec7_phi_near_int Ph hj hbox gfun hg hrwide hcorner
        (hprod (r : ℝ) (sec7_mem_wide_real (S := S) hrwide))
        hbr0 hbr1 hbr2 hbr3
    let Tpiece :
        ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ)) → Finset ℤ := fun pc =>
      wide.filter (fun n : ℤ =>
        Counting.distInt
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃
            pc.1.1 pc.1.2.1 pc.1.2.2.1 pc.1.2.2.2
            pc.2.1.1 pc.2.1.2.1 pc.2.1.2.2 (n : ℝ))
          ≤ sec7_cCal * sec7_delta1 P S h₁ h₂ h₃)
    let Bz : ℝ := 11 * sec7_cN13 *
      (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
        sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) /
          Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
          Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
        sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
        sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
        1)
    have hδNpos : 0 < sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ :=
      mul_pos sec7_cCal_pos (sec7_delta1_pos hbox)
    have hC0_le : (C0.card : ℝ) ≤ (Λ0.card : ℝ) * Bz := by
      apply sec7_cover_card_mul_bound C0 Λ0 Tpiece Bz
      · intro r hr
        have hr' := Finset.mem_filter.mp hr
        have hrC : r ∈ C := hr'.1
        have htop : topZero r := hr'.2
        have hcube : r ∈ E ∧
            (∀ ε₁ ε₂ ε₃ : ℕ, ε₁ ≤ 1 → ε₂ ≤ 1 → ε₃ ≤ 1 →
              r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ) ∈ E) := by
          simpa [C, sec7_cubeSet] using hrC
        have hEbase : r ∈ wide ∧ Counting.distInt (gfun j (r : ℝ)) ≤ δ₀ := by
          simpa [E] using hcube.1
        obtain ⟨pc, hpc, _hrint, hbr0, hbr1, hbr2, hbr3⟩ :=
          hΛ0cover r hEbase.1 htop
        refine ⟨pc, hpc, ?_⟩
        have hnear := hnear_of_branch (pc := pc) hrC hbr0 hbr1 hbr2 hbr3
        exact Finset.mem_filter.mpr ⟨hEbase.1, hnear⟩
      · intro pc hpc
        have hpcData := hΛ0piece pc hpc
        let Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃
            pc.1.1 pc.1.2.1 pc.1.2.2.1 pc.1.2.2.2
            pc.2.1.1 pc.2.1.2.1 pc.2.1.2.2 :=
          { env := Env
            hj := hj
            hbox := hbox
            hW := by linarith
            hpad := hpad
            hshift := hshift
            hξ₁ := hξ₁
            hξ₂ := hξ₂
            hξ₃ := hξ₃
            hρ₀ := hΛ0zero pc hpc
            hρ₁ := hpcData.1.2.1
            hρ₂ := hpcData.1.2.2.1
            hρ₃ := hpcData.1.2.2.2
            hu₁ := hpcData.2.1.1
            hu₂ := hpcData.2.1.2.1
            hu₃ := hpcData.2.1.2.2
            hcd := sec7_phase_phi_contDiff Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃
              pc.1.1 pc.1.2.1 pc.1.2.2.1 pc.1.2.2.2
              pc.2.1.1 pc.2.1.2.1 pc.2.1.2.2
            hsub1 := sec7_zero_hsub1 Env hW.le
            hsub2 := sec7_zero_hsub2 c₀ Cu hsd hbud hg0 hu0 hX24
            hrel := sec7_zero_hrel Env hbox c₀ Cu hsd hbud hg0 hu0 hX24
            few_critical := sec7_phase_phi_fewCritical Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃
              pc.1.1 pc.1.2.1 pc.1.2.2.1 pc.1.2.2.2
              pc.2.1.1 pc.2.1.2.1 pc.2.1.2.2 }
        have hcnt := sec7_zero_wide_count (ME := ME) Hyp hxsmall hδNpos le_rfl
        simpa [Tpiece, Bz, wide] using hcnt
    let Bn : ℝ := 11 * sec7_cN19 * (1 + Real.log P.X) *
      ((S.R * S.T₁) ^ ((1:ℝ)/3) +
        S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
        S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1)
    have hCn_le : (Cn.card : ℝ) ≤ (((Λ.filter (fun pc => pc.1.1 ≠ 0)).card : ℝ)) * Bn := by
      apply sec7_cover_card_mul_bound Cn (Λ.filter (fun pc => pc.1.1 ≠ 0)) Tpiece Bn
      · intro r hr
        have hr' := Finset.mem_filter.mp hr
        have hrC : r ∈ C := hr'.1
        have hnotTop : ¬ topZero r := hr'.2
        have hcube : r ∈ E ∧
            (∀ ε₁ ε₂ ε₃ : ℕ, ε₁ ≤ 1 → ε₂ ≤ 1 → ε₃ ≤ 1 →
              r + ε₁ * (p.1 : ℤ) + ε₂ * (p.2.1 : ℤ) + ε₃ * (p.2.2 : ℤ) ∈ E) := by
          simpa [C, sec7_cubeSet] using hrC
        have hEbase : r ∈ wide ∧ Counting.distInt (gfun j (r : ℝ)) ≤ δ₀ := by
          simpa [E] using hcube.1
        obtain ⟨pc, hpc, _hrint, hbr0, hbr1, hbr2, hbr3⟩ := hΛcover r hEbase.1
        have hpcne : pc.1.1 ≠ 0 := by
          intro hzero
          apply hnotTop
          simpa [topZero, hzero] using hbr0
        refine ⟨pc, Finset.mem_filter.mpr ⟨hpc, hpcne⟩, ?_⟩
        have hnear := hnear_of_branch (pc := pc) hrC hbr0 hbr1 hbr2 hbr3
        exact Finset.mem_filter.mpr ⟨hEbase.1, hnear⟩
      · intro pc hpc
        have hpcΛ : pc ∈ Λ := (Finset.mem_filter.mp hpc).1
        have hpcne : pc.1.1 ≠ 0 := (Finset.mem_filter.mp hpc).2
        have hpcData := hΛpiece pc hpcΛ
        have hcnt := sec7_nonzero_wide_count Env hW c₀ Cu hsd hbud hg0 hu0 hX24
          ME hj hbox hξ₁ hξ₂ hξ₃ hpcne hpcData.1.1 hpcData.1.2.1
          hpcData.1.2.2.1 hpcData.1.2.2.2 hpcData.2.1.1 hpcData.2.1.2.1 hpcData.2.1.2.2
        simpa [Tpiece, Bn, wide] using hcnt
    have hcard_split : (C.card : ℝ) = (C0.card : ℝ) + (Cn.card : ℝ) := by
      have hnat := Finset.card_filter_add_card_filter_not (s := C) topZero
      dsimp [C0, Cn]
      exact_mod_cast hnat.symm
    have hH := P.H_pos
    have hG := P.G_pos
    have hΩ := S.Ω_pos
    have hx := OnStripAux.x_pos P S
    have hT1pos : 0 < S.T₁ := sec7_T₁_pos S
    have hRpos : 0 < S.R := sec7_R_pos S
    have hSbox_id : sec7_Ssym h₁ h₂ h₃ = (Sbox p.1 p.2.1 p.2.2 : ℝ) := by
      simpa [h₁, h₂, h₃] using sec7_Ssym_natCast p.1 p.2.1 p.2.2
    have hPbox_id : sec7_Pprod h₁ h₂ h₃ = (Pbox p.1 p.2.1 p.2.2 : ℝ) := by
      simpa [h₁, h₂, h₃] using sec7_Pprod_natCast p.1 p.2.1 p.2.2
    have hHSbox_id : sec7_hSum h₁ h₂ h₃ = (HSbox p.1 p.2.1 p.2.2 : ℝ) := by
      simpa [h₁, h₂, h₃] using sec7_hSum_natCast p.1 p.2.1 p.2.2
    have hSsym0 : 0 ≤ sec7_Ssym h₁ h₂ h₃ := by
      have hh10 : (0 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.1.1)
      have hh20 : (0 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.1.1)
      have hh30 : (0 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.2.1)
      simp only [sec7_Ssym]
      nlinarith [mul_nonneg hh10 hh20, mul_nonneg hh10 hh30, mul_nonneg hh20 hh30]
    have hPPpos : 0 < sec7_Pprod h₁ h₂ h₃ := by
      have hh1pos : (0 : ℝ) < (h₁ : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one hbox.1.1)
      have hh2pos : (0 : ℝ) < (h₂ : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one hbox.2.1.1)
      have hh3pos : (0 : ℝ) < (h₃ : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one hbox.2.2.1)
      simp only [sec7_Pprod]
      exact mul_pos (mul_pos hh1pos hh2pos) hh3pos
    have hHS0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
      have hh10 : (0 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.1.1)
      have hh20 : (0 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.1.1)
      have hh30 : (0 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hbox.2.2.1)
      simp only [sec7_hSum]
      linarith
    let q : ℝ := sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)
    have hq0 : 0 ≤ q := by
      dsimp [q]
      positivity
    let zeroCore : ℝ :=
      P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
        sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) /
          Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
          Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
        sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
        sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
        1
    let zeroFull : ℝ := zeroCore + sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R
    have hzeroCore0 : 0 ≤ zeroCore := by
      dsimp [zeroCore]
      have hratio0 : 0 ≤ sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃ :=
        div_nonneg hSsym0 hPPpos.le
      have hden3 : 0 ≤ S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4 := by positivity
      have hA1 : 0 ≤ P.G * S.Ω / S.x ^ 2 :=
        div_nonneg (mul_nonneg hG.le hΩ.le) (sq_nonneg S.x)
      have hA2 : 0 ≤ S.Ω ^ 2 / P.H :=
        div_nonneg (sq_nonneg S.Ω) hH.le
      have hA3 : 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) :=
        div_nonneg hSsym0 hden3
      have hA4 : 0 ≤
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
            S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) :=
        div_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hA5 : 0 ≤
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
            Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hA6 : 0 ≤ sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) :=
        div_nonneg hHS0 hden3
      have hA7 : 0 ≤ sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) :=
        div_nonneg hPPpos.le (by positivity)
      nlinarith
    have hzeroFull_ge : zeroCore ≤ zeroFull := by
      dsimp [zeroFull]
      have hextra : 0 ≤ sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R := by
        positivity
      linarith
    have hBz0 : 0 ≤ Bz := by
      dsimp [Bz]
      exact mul_nonneg (mul_nonneg (by norm_num) (by norm_num [sec7_cN13])) hzeroCore0
    have hC0_final : (C0.card : ℝ) ≤ cz p := by
      have hcoef :
          343 * (4 + 2 * (sec7_cPh * q)) * (11 * sec7_cN13) ≤
            sec7_cTriple * (1 + q) := by
        norm_num [sec7_cPh, sec7_cN13, sec7_cTriple]
        nlinarith [hq0]
      have hmulcoef0 : 0 ≤ sec7_cTriple * (1 + q) := by
        exact mul_nonneg sec7_cTriple_pos.le (by linarith [hq0])
      calc
        (C0.card : ℝ) ≤ (Λ0.card : ℝ) * Bz := hC0_le
        _ ≤ (343 * (4 + 2 * (sec7_cPh * q))) * Bz := by
          exact mul_le_mul_of_nonneg_right (by simpa [q] using hΛ0card) hBz0
        _ = (343 * (4 + 2 * (sec7_cPh * q)) * (11 * sec7_cN13)) * zeroCore := by
          dsimp [Bz, zeroCore, q]
          ring
        _ ≤ (sec7_cTriple * (1 + q)) * zeroCore :=
          mul_le_mul_of_nonneg_right hcoef hzeroCore0
        _ ≤ (sec7_cTriple * (1 + q)) * zeroFull :=
          mul_le_mul_of_nonneg_left hzeroFull_ge hmulcoef0
        _ = cz p := by
          dsimp [cz, q, zeroFull, zeroCore]
          rw [hSbox_id, hPbox_id, hHSbox_id]
    let nonzeroBody : ℝ :=
      P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
        + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
        + sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
        + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
        + S.x * P.G * S.Ω ^ 3
        + Real.sqrt (sec7_Ssym h₁ h₂ h₃)
        + 1
    let bracket : ℝ :=
      (S.R * S.T₁) ^ ((1:ℝ)/3) +
        S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) +
        S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) + 1
    have hnonzeroBody0 : 0 ≤ nonzeroBody := by
      dsimp [nonzeroBody]
      have hA0 : 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) := by
        positivity
      have hA1 : 0 ≤ P.G * S.Ω / S.x ^ 2 := by positivity
      have hA2 : 0 ≤ S.Ω ^ 2 / P.H := by positivity
      have hA3 : 0 ≤ sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
        positivity
      have hA4 : 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) := by positivity
      have hA5 : 0 ≤ S.x * P.G * S.Ω ^ 3 := by positivity
      have hA6 : 0 ≤ Real.sqrt (sec7_Ssym h₁ h₂ h₃) := Real.sqrt_nonneg _
      linarith
    have hbracket0 : 0 ≤ bracket := by
      dsimp [bracket]
      have hRT0 : 0 ≤ S.R * S.T₁ := mul_nonneg hRpos.le hT1pos.le
      have h1 : 0 ≤ (S.R * S.T₁) ^ ((1:ℝ)/3) := Real.rpow_nonneg hRT0 _
      have h2 : 0 ≤ S.R * (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) :=
        mul_nonneg hRpos.le hδNpos.le
      have h3 : 0 ≤ S.R * Real.sqrt ((sec7_cCal * sec7_delta1 P S h₁ h₂ h₃) / S.T₁) :=
        mul_nonneg hRpos.le (Real.sqrt_nonneg _)
      linarith
    have hbracket_eval : bracket ≤ (10 : ℝ) ^ 20 * nonzeroBody := by
      simpa [bracket, nonzeroBody] using
        sec7_nonzero_bracket_eval_bound (P := P) (S := S) c₀ Cu hsd hbud hg0 hu0 hX24
          (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hSsym0
    have hlogfac0 : 0 ≤ 1 + Real.log P.X := by
      have hlog0 : 0 ≤ Real.log P.X := Real.log_nonneg hsd.hX
      linarith
    have hqfac0 : 0 ≤ 1 + q := by
      linarith [hq0]
    have hcoefBn0 : 0 ≤ 11 * sec7_cN19 * (1 + Real.log P.X) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by norm_num [sec7_cN19])) hlogfac0
    have hBn0 : 0 ≤ Bn := by
      simpa [Bn, bracket] using mul_nonneg hcoefBn0 hbracket0
    have hBn_eval :
        Bn ≤ 11 * sec7_cN19 * (1 + Real.log P.X) *
          ((10 : ℝ) ^ 20 * nonzeroBody) := by
      simpa [Bn, bracket] using mul_le_mul_of_nonneg_left hbracket_eval hcoefBn0
    have hfilterCard_le : (((Λ.filter (fun pc => pc.1.1 ≠ 0)).card : ℝ)) ≤
        (Λ.card : ℝ) := by
      have hfilterCard_nat :
          (Λ.filter (fun pc => pc.1.1 ≠ 0)).card ≤ Λ.card :=
        Finset.card_filter_le Λ (fun pc => pc.1.1 ≠ 0)
      exact_mod_cast hfilterCard_nat
    have hcoverCoeff0 : 0 ≤ sec7_cMult * sec7_cPh * (1 + q) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num [sec7_cMult]) (by norm_num [sec7_cPh])) hqfac0
    have hCn_cover : (Cn.card : ℝ) ≤ (sec7_cMult * sec7_cPh * (1 + q)) * Bn := by
      calc
        (Cn.card : ℝ) ≤ (((Λ.filter (fun pc => pc.1.1 ≠ 0)).card : ℝ)) * Bn := hCn_le
        _ ≤ (Λ.card : ℝ) * Bn := mul_le_mul_of_nonneg_right hfilterCard_le hBn0
        _ ≤ (sec7_cMult * sec7_cPh * (1 + q)) * Bn := by
          exact mul_le_mul_of_nonneg_right (by simpa [q] using hΛcard) hBn0
    have hcoef_nonzero :
        sec7_cMult * sec7_cPh * (11 * sec7_cN19) * (10 : ℝ) ^ 20 ≤
          sec7_cTriple := by
      norm_num [sec7_cMult, sec7_cPh, sec7_cN19, sec7_cTriple]
    have hright_nonneg : 0 ≤ (1 + Real.log P.X) * (1 + q) * nonzeroBody := by
      exact mul_nonneg (mul_nonneg hlogfac0 hqfac0) hnonzeroBody0
    have hcover_to_cn : (sec7_cMult * sec7_cPh * (1 + q)) * Bn ≤ cn p := by
      calc
        (sec7_cMult * sec7_cPh * (1 + q)) * Bn
            ≤ (sec7_cMult * sec7_cPh * (1 + q)) *
                (11 * sec7_cN19 * (1 + Real.log P.X) *
                  ((10 : ℝ) ^ 20 * nonzeroBody)) :=
              mul_le_mul_of_nonneg_left hBn_eval hcoverCoeff0
        _ = (sec7_cMult * sec7_cPh * (11 * sec7_cN19) * (10 : ℝ) ^ 20) *
              ((1 + Real.log P.X) * (1 + q) * nonzeroBody) := by ring
        _ ≤ sec7_cTriple * ((1 + Real.log P.X) * (1 + q) * nonzeroBody) :=
              mul_le_mul_of_nonneg_right hcoef_nonzero hright_nonneg
        _ = cn p := by
          dsimp [cn, q, nonzeroBody]
          rw [hSbox_id]
          ring
    have hCn_final : (Cn.card : ℝ) ≤ cn p :=
      hCn_cover.trans hcover_to_cn
    calc
      ((sec7_cubeSet ((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
          (fun r => Counting.distInt (gfun j (r : ℝ)) ≤ δ₀)) p.1 p.2.1 p.2.2).card : ℝ)
          = (C.card : ℝ) := by
            simp [C, E, wide]
      _ = (C0.card : ℝ) + (Cn.card : ℝ) := hcard_split
      _ ≤ cz p + cn p := add_le_add hC0_final hCn_final
  · intro p hp
    rfl
  · intro p hp
    rfl

/-- G1-AUDIT: the §7 phase constructor for one dyadic `a`-block.  This is the single
remaining local supplier for the inverse-`F_a` map (`dBreve`, its first two derivatives, and
the derivative-family fields bundled in `Sec7Phase`).  The extra output facts are exactly the
interfaces consumed by `sec7_ra_data_pack`: `ftil` agrees with the smooth `F_a(d̃_a(r))` on the
wide `RaWitness` window, and rounded `F_a(d)` values in the `D`-window map back to `d` with the
N4 margin. -/
private theorem sec7_phase_build (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) (ha : 0 < a)
    (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu) :
    ∃ Ph : Sec7Phase P S W a,
      (∀ {r : ℝ}, (1/72) * S.R ≤ r → r ≤ 16 * S.R →
        Ph.ftil r = Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ∧
      (∀ {d f : ℤ}, S.D ≤ (d : ℝ) → (d : ℝ) ≤ 2 * S.D →
        f = round (Ffun P.X (a : ℝ) (d : ℝ)) →
        |(d : ℝ) - Ph.dBreve (f : ℝ)| ≤
          sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A))) := by
  sorry -- STUB: N24-PHASE (inverse-F_a Sec7Phase construction + rounded inverse margin)

/-- G1-AUDIT: dischargeability — the r-side phase/branch data pack for prop_7_3 (N24):
the `Sec7Phase` bundle for the fiber `a` (a §3 construction, not yet in-tree), the N4
Taylor budget `hTaylor` (AM-1: the G≥1-provable form `cPh·(HΔ/F²) ≤ cPh·(Δ⁵/(H³Ω²))` —
no G-largeness; sympy-banked chain `HΔ/F² = (Δ⁵/(H³Ω²))·G⁻²`, ledger U4), the N3 inputs
`hnear` (the Prop-3.2 near-integrality, md 1317, not in-tree) and `hprox` (PRODUCER:
`ftil_prox`, Bracket/Sec7Prox.lean:100, in its EXACT shape `≤ 10¹⁸·(H/A²)`), and the
per-`r` window facts.  AM-2: `hmem` is the WIDE `RaWitness` window `[⌈R/72⌉,⌊16R⌋]` —
exactly what `RaWitness` confines (`(1/72)R ≤ r ≤ 16R`); the dyadic pass is downstream. -/
private theorem sec7_ra_data_pack (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) (ha : 0 < a)
    (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (Ra : Finset ℕ)
    (hRa : ∀ r ∈ Ra, RaWitness P S a r) :
    ∃ (Ph : Sec7Phase P S W a) (FdStar : ℤ → ℝ) (dStar fStar : ℤ → ℤ),
      -- A1 gate: the A–D separation feeding N3 (held by the §3 construction; it is
      -- `ftil_prox`'s own `hAD` input)
      10 * S.A ≤ S.D ∧
      sec7_cPh * (P.H * S.Δ / S.F ^ 2) ≤
        sec7_cPh * (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)) ∧
      ∀ r ∈ Ra.image (fun n : ℕ => (n : ℤ)),
        r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋ ∧
        (r : ℝ) ∈ sec7_rWin S W ∧
        |(dStar r : ℝ) - Ph.dBreve (fStar r)| ≤
          sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A)) ∧
        |(fStar r : ℝ) - FdStar r| ≤ 2 * P.H / S.D ^ 2 ∧
        |FdStar r - Ph.ftil (r : ℝ)| ≤ 10 ^ 18 * (P.H / S.A ^ 2) := by
  obtain ⟨Ph, hftil, hdBreve⟩ :=
    sec7_phase_build P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
  let Wint : ℤ → Prop := fun r => ∃ n ∈ Ra, (n : ℤ) = r ∧ RaWitness P S a n
  let dStar : ℤ → ℤ := fun r =>
    if h : Wint r then Classical.choose (Classical.choose_spec h).2.2 else 0
  let FdStar : ℤ → ℝ := fun r => Ffun P.X (a : ℝ) (dStar r : ℝ)
  let fStar : ℤ → ℤ := fun r => round (FdStar r)
  refine ⟨Ph, FdStar, dStar, fStar, hAD, ?_, ?_⟩
  · have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
    have hF : 0 < S.F := by unfold Scale.F; positivity
    have hbase :
        P.H * S.Δ / S.F ^ 2 =
          (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)) / P.G ^ 2 := by
      unfold Scale.F
      field_simp [hH.ne', hG.ne', hΔ.ne', hΩ.ne']
    have hG2 : (1 : ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
    have hmain_nonneg : 0 ≤ S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) := by positivity
    have hdiv :
        (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)) / P.G ^ 2 ≤
          S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) := by
      rw [div_le_iff₀ (by positivity : 0 < P.G ^ 2)]
      nlinarith [hG2, hmain_nonneg]
    have hcPh : 0 ≤ sec7_cPh := by norm_num [sec7_cPh]
    calc
      sec7_cPh * (P.H * S.Δ / S.F ^ 2)
          = sec7_cPh * ((S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)) / P.G ^ 2) := by rw [hbase]
      _ ≤ sec7_cPh * (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)) :=
          mul_le_mul_of_nonneg_left hdiv hcPh
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨n, hnRa, hnr⟩ := hr
    have hw : Wint r := ⟨n, hnRa, hnr, hRa n hnRa⟩
    let n₀ : ℕ := Classical.choose hw
    have hn₀spec := Classical.choose_spec hw
    have hn₀Ra : n₀ ∈ Ra := hn₀spec.1
    have hn₀r : (n₀ : ℤ) = r := hn₀spec.2.1
    have hwit : RaWitness P S a n₀ := hn₀spec.2.2
    let d : ℤ := Classical.choose hwit
    have hdspec := Classical.choose_spec hwit
    have hdStar : dStar r = d := by
      simp [dStar, Wint, hw, d]
    have hFdStar : FdStar r = Ffun P.X (a : ℝ) (d : ℝ) := by
      simp [FdStar, hdStar]
    have hfStar : fStar r = round (Ffun P.X (a : ℝ) (d : ℝ)) := by
      simp [fStar, FdStar, hdStar]
    obtain ⟨hinDa, hdD, hd2D, hRd, hrlo₀, hrhi₀⟩ := hdspec
    have hn₀rR : (n₀ : ℝ) = (r : ℝ) := by exact_mod_cast hn₀r
    have hrlo : (1/72) * S.R ≤ (r : ℝ) := by simpa [← hn₀rR] using hrlo₀
    have hrhi : (r : ℝ) ≤ 16 * S.R := by simpa [← hn₀rR] using hrhi₀
    have hRpos : 0 < S.R := by
      have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
      unfold Scale.R
      positivity
    have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le S.D_pos hdD
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Int.ceil_le.mpr (by simpa [show S.R / 72 = (1/72) * S.R by ring] using hrlo),
        Int.le_floor.mpr hrhi⟩
    · rw [sec7_rWin, Set.mem_Icc]
      have hs_nonneg : 0 ≤ W + W ^ 2 + W ^ 4 := by
        have hW0 : 0 ≤ W := Env.W_pos.le
        positivity
      constructor
      · nlinarith [hrlo, hRpos, hs_nonneg]
      · nlinarith [hrhi, hRpos, hs_nonneg]
    · simpa [d, hdStar, hfStar] using hdBreve hdD hd2D hfStar
    · have hdist := inDa_distInt_Ffun (X := P.X) (H := P.H) (a := a) (d := d)
        P.X_pos hdpos ha hinDa
      have hnear_d : |(round (Ffun P.X (a : ℝ) (d : ℝ)) : ℝ) -
            Ffun P.X (a : ℝ) (d : ℝ)| ≤ 2 * P.H / (d : ℝ) ^ 2 := by
        simpa [Counting.distInt, abs_sub_comm] using hdist
      have hDsq : S.D ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ S.D_pos.le hdD 2
      have hden :
          2 * P.H / (d : ℝ) ^ 2 ≤ 2 * P.H / S.D ^ 2 := by
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) P.H_pos.le)
          (pow_pos S.D_pos 2) hDsq
      rw [hfStar, hFdStar]
      exact le_trans hnear_d hden
    · have hRd' : |Rfun P.X (a : ℝ) (d : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D := by
        simpa [d, hn₀rR] using hRd
      have hApos : 0 < S.A := by
        have hΔ : 0 < S.Δ := S.Δ_pos
        have hΩ : 0 < S.Ω := S.Ω_pos
        unfold Scale.A
        positivity
      have ha_lo_wide : S.A / 5 ≤ (a : ℝ) := by nlinarith
      have ha_hi_wide : (a : ℝ) ≤ 11 * S.A := by nlinarith
      have hprox := ftil_prox (P := P) (S := S) (a := a) (r := (r : ℝ)) (d := (d : ℝ))
        hAD ha ha_lo_wide ha_hi_wide hrlo hrhi hdD hd2D hRd'
      rw [hFdStar, hftil hrlo hrhi]
      exact hprox

private theorem sec7_ra_card_le_17R {P : Globals} {S : Scale P} {a : ℤ} {Ra : Finset ℕ}
    (hR1 : (1 : ℝ) < S.R) (hRa : ∀ r ∈ Ra, RaWitness P S a r) :
    (Ra.card : ℝ) ≤ 17 * S.R := by
  have hRpos : 0 < S.R := by linarith
  have hsubset :
      Ra.image (fun n : ℕ => (n : ℤ)) ⊆ Finset.Icc (0 : ℤ) ⌊16 * S.R⌋ := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨n, hnRa, hzn⟩ := hz
    subst z
    have hwit := hRa n hnRa
    obtain ⟨_, _, _, _, _, hrhi⟩ := Classical.choose_spec hwit
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le n
    · exact Int.le_floor.mpr hrhi
  have hcard :=
    Finset.card_le_card hsubset
  have himg :
      (Ra.image (fun n : ℕ => (n : ℤ))).card = Ra.card := by
    exact Finset.card_image_of_injective Ra (fun x y h => by exact_mod_cast h)
  have hIcc : (((Finset.Icc (0 : ℤ) ⌊16 * S.R⌋).card : ℕ) : ℝ) ≤ 16 * S.R + 1 := by
    rw [Int.card_Icc]
    rcases le_or_gt (⌊16 * S.R⌋ + 1 - (0 : ℤ)) 0 with hle | hpos
    · rw [Int.toNat_of_nonpos hle]
      push_cast
      linarith
    · rw [show (((⌊16 * S.R⌋ + 1 - (0 : ℤ)).toNat : ℕ) : ℝ)
            = ((⌊16 * S.R⌋ + 1 - (0 : ℤ) : ℤ) : ℝ) from by
          exact_mod_cast Int.toNat_of_nonneg hpos.le]
      push_cast
      linarith [Int.floor_le (16 * S.R)]
  calc
    (Ra.card : ℝ)
        = ((Ra.image (fun n : ℕ => (n : ℤ))).card : ℝ) := by rw [himg]
    _ ≤ ((Finset.Icc (0 : ℤ) ⌊16 * S.R⌋).card : ℝ) := by exact_mod_cast hcard
    _ ≤ 16 * S.R + 1 := hIcc
    _ ≤ 17 * S.R := by nlinarith

/-- **Prop 7.1** (writeup 1388–1419). Fixed `j` in the §7 band `|j| ≪ 1+H/A²` (md 1307–09,
fixed absolute constant `sec7_cJ`): `#{r≍R : ‖g_j(r)‖ ≤ δ₀} ≪ R/W` under the admissibility
envelope. The phase functions `f̃ₐ, d̆ₐ, d̆ₐ'` now come with the `Sec7Phase` regularity bundle
(`Bracket/Sec7Defs.lean`: the md 1327–31 inverse-function scales `F·d̆'≍HΔ`, `F²·d̆''≍HΔ` on
`t≍F`, and the md 1509–14 windows `f_i^{(m)}≍T_i/Rᵐ`), fixing the 2026-06-03 audit (bare
∀-functions admit `count ≍ R`); the `j`-band constant is likewise pinned to `sec7_cJ` (a free
per-`j` constant would quantify over all `j ∈ ℤ`, escaping the phase window). `g_j` keeps its
defining equation (md 1313); `δ₀ ≤ sec7_cTay·sec7_delta0` is the md-1360 display (TRAP-1:
the larger `Δ⁵/(H³Ω²)+Δ²/(H²GA)`, never the md-1352 `G²`-identity), renormalized by the
AM-1 Taylor constant `sec7_cTay`. AM-2: the count runs over the WIDE `RaWitness` window
`[⌈R/72⌉,⌊16R⌋]`. AM-8: carries the strip-regime pack (`StripData`, `Budget`, `0 ≤ g`,
`0 < u`, X-largeness, `log X ≤ X^u`), mirrored verbatim from `dblock_on_strip`. -/
theorem prop_7_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W →
      ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
      0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      Real.log P.X ≤ P.X ^ P.u →
      ∀ (a : ℤ) (Ph : Sec7Phase P S W a) (gfun : ℤ → ℝ → ℝ),
        (∀ (j : ℤ) (r : ℝ),
          gfun j r = Ph.dBreve (Ph.ftil r + j)
            - Ph.dBreve' (Ph.ftil r + j) * Int.fract (Ph.ftil r)) →
        ∀ (δ₀ : ℝ), 0 < δ₀ → δ₀ ≤ sec7_cTay * sec7_delta0 P S →
          ∀ (j : ℤ), sec7_jBand P S j →
            -- P1e elaboration fix: the count binder is pinned `r : ℤ` (md: #{r ≍ R}, an
            -- integer count); the bare binder elaborated as a `Lean.Internal.coeM`-coerced
            -- `Finset ℝ` filter (same cardinality, wrong interface for N5's `Finset ℤ`).
            (((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
                (fun r : ℤ => distInt (gfun j (r : ℝ)) ≤ δ₀)).card : ℝ) ≤ C * (S.R / W) := by
  -- N23 (md 1453–61, 1973–75): contradiction assembly. `C := sec7_cCubeIn`; ledger chain
  -- (sympy-checked): trivial branch needs `C ≥ 2`; main branch needs `2·sec7_cCube <
  -- sec7_harvM` (200 < 1000, slack 5): N5 forces `(R/W)/cCube ≤ Σ cubes`, the two harvests
  -- cap `Σ cubes ≤ 2·(R/W)/harvM` — impossible for `R/W > 0`.
  refine ⟨sec7_cCubeIn, sec7_cCubeIn_pos, ?_⟩
  intro P S W Env c₀ Cu hsd hbud hg0 hu0 hX24 _hlog a Ph gfun hg δ₀ hδ0 hδle j hjB
  have hR1 : (1 : ℝ) < S.R := Env.R_gt_one
  have hW0 : (0 : ℝ) < W := Env.W_pos
  rcases le_or_gt W 1 with hW1 | hW1
  · -- `W ≤ 1`: the wide interval has `≤ 16R + 1 ≤ 17R ≤ C·R ≤ C·(R/W)` integers.
    have hcard : (((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
        (fun r : ℤ => distInt (gfun j (r : ℝ)) ≤ δ₀)).card : ℝ)
        ≤ ((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hIcc : ((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).card : ℝ) ≤ 16 * S.R + 1 := by
      rw [Int.card_Icc]
      rcases le_or_gt (⌊16 * S.R⌋ + 1 - ⌈S.R / 72⌉) 0 with hle | hpos
      · rw [Int.toNat_of_nonpos hle]; push_cast; linarith
      · rw [show (((⌊16 * S.R⌋ + 1 - ⌈S.R / 72⌉).toNat : ℕ) : ℝ)
            = ((⌊16 * S.R⌋ + 1 - ⌈S.R / 72⌉ : ℤ) : ℝ) from by
          exact_mod_cast Int.toNat_of_nonneg hpos.le]
        push_cast
        linarith [Int.floor_le (16 * S.R), Int.le_ceil (S.R / 72)]
    have hRdiv : S.R ≤ S.R / W := by
      rw [le_div_iff₀ hW0]; nlinarith
    have hC : sec7_cCubeIn = (1000 : ℝ) := by norm_num [sec7_cCubeIn]
    rw [hC]; linarith
  · -- `1 < W`: by contradiction via N5 (cube lower bound) against N15+N22 (harvests).
    by_contra hcon
    rw [not_le] at hcon
    -- A5 gate: `1 ≤ X` for N18a, from the X-floor `16777216 ≤ X^{1/100}`
    have hX1 : (1 : ℝ) ≤ P.X := by
      rcases le_or_gt 1 P.X with h | h
      · exact h
      · have : P.X ^ (1/100 : ℝ) ≤ 1 :=
          Real.rpow_le_one P.X_pos.le h.le (by norm_num)
        linarith
    obtain ⟨-, hW8⟩ := sec7_side_R_ge_W8 P S W Env hX1 hW1
    have hcube := sec7_averaged_cube_lower hW1.le hW8
      ((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
        (fun r : ℤ => distInt (gfun j (r : ℝ)) ≤ δ₀))
      (Finset.filter_subset _ _) hcon.le
    obtain ⟨cz, cn, hsplit, hzb, hnb⟩ := sec7_triple_split P S W Env hW1 a Ph gfun hg
      δ₀ hδ0 hδle j hjB c₀ Cu hsd hbud hg0 hu0 hX24
    have hZ := sec7_harvest_zero P S W Env hW1.le c₀ Cu hsd hbud hg0 hu0 hX24 cz hzb
    have hN := sec7_harvest_nonzero P S W Env hW1.le c₀ Cu hsd hbud hg0 hu0 hX24 cn hnb
    have hsum : (∑ p ∈ box W,
        ((sec7_cubeSet ((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
            (fun r : ℤ => distInt (gfun j (r : ℝ)) ≤ δ₀)) p.1 p.2.1 p.2.2).card : ℝ))
        ≤ (∑ p ∈ box W, cz p) + (∑ p ∈ box W, cn p) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hsplit
    have ht : (0 : ℝ) < S.R / W := div_pos (by linarith) hW0
    rw [show W * sec7_cCube = W * 100 from by norm_num [sec7_cCube], ← div_div] at hcube
    rw [show W * sec7_harvM = W * 1000 from by norm_num [sec7_harvM], ← div_div] at hZ hN
    linarith

/-- **Prop 7.3** (writeup 1993–2000): `#ℛ_a ≪ (1+H/A²)·R/W`. `Ra` is the §3 set; each
`r ∈ ℛ_a` carries the faithful r-side structural data `RaWitness` (a popular `d` at the
`D`-scale with `r ≈ R_a(d)`), from which the proof builds the `g_j` phase and applies Prop 7.1.
AM-8: carries the strip-regime pack, mirrored verbatim from `dblock_on_strip`. -/
theorem prop_7_3 : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a → 10 * S.A ≤ S.D → 1 ≤ P.G →
      S.A ≤ (a : ℝ) → (a : ℝ) ≤ 2 * S.A →
      ∀ (W : ℝ), Sec7Envelope P S W →
      ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
      0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      Real.log P.X ≤ P.X ^ P.u →
      ∀ (Ra : Finset ℕ), (∀ r ∈ Ra, RaWitness P S a r) →
        (Ra.card : ℝ) ≤ C * ((1 + P.H / S.A ^ 2) * (S.R / W)) := by
  -- N24 (md 1977–84): N3 (branch j) + N4 (reduction to the j-band sum, AM-1 threshold
  -- `cTay·δ₀`) + prop_7_1 per band value; the band has `2⌊z⌋+1 ≤ 3z` values,
  -- `z := sec7_cJ·(1+H/A²) ≥ sec7_cJ ≥ 1`, so `C := 3·sec7_cJ·C₇₁` (ledger U4: cJ = 10²⁰).
  obtain ⟨C₁, hC₁, h71⟩ := prop_7_1
  refine ⟨3 * sec7_cJ * C₁ + 1000, by have := sec7_cJ_pos; positivity, ?_⟩
  intro P S a ha hAD hG1 ha_lo ha_hi W Env c₀ Cu hsd hbud hg0 hu0 hX24 hlog Ra hRa
  have hR1 : (1 : ℝ) < S.R := Env.R_gt_one
  have hW0 : (0 : ℝ) < W := Env.W_pos
  rcases le_or_gt 1 W with hW | hWlt
  · obtain ⟨Ph, FdStar, dStar, fStar, hAD, hTay, hdata⟩ :=
      sec7_ra_data_pack P S W a ha hAD hG1 ha_lo ha_hi c₀ Cu hsd Env hW Ra hRa
    -- the `g_j` phase (md 1313), with its defining equation by `rfl`
    set gfun : ℤ → ℝ → ℝ := fun j t =>
      Ph.dBreve (Ph.ftil t + j) - Ph.dBreve' (Ph.ftil t + j) * Int.fract (Ph.ftil t) with hgdef
    -- N3 per `r`: the branch integer
    have hbranch : ∀ r ∈ Ra.image (fun n : ℕ => (n : ℤ)),
        ∃ jj : ℤ, sec7_jBand P S jj ∧ fStar r = ⌊Ph.ftil (r : ℝ)⌋ + jj := fun r hr =>
      sec7_branch_exists Ph (FdStar r) (fStar r) hAD (hdata r hr).2.1
        (hdata r hr).2.2.2.1 (hdata r hr).2.2.2.2
    -- N4: the branch reduction to the j-band sum
    have hred := sec7_branch_reduction Ph gfun (fun _ _ => rfl) hTay
      (Ra.image (fun n : ℕ => (n : ℤ))) dStar fStar
      (fun r hr => (hdata r hr).1) (fun r hr => (hdata r hr).2.1)
      (fun r hr => (hdata r hr).2.2.1) hbranch
    -- prop_7_1 at each band value (AM-1: at the renormalized threshold `cTay·δ₀`)
    have hδpos : 0 < sec7_cTay * sec7_delta0 P S := by
      have h1 := P.H_pos; have h2 := P.G_pos; have h3 := S.Δ_pos; have h4 := S.Ω_pos
      have hA : 0 < S.A := by unfold Scale.A; positivity
      unfold sec7_cTay sec7_delta0; positivity
    set z : ℝ := sec7_cJ * (1 + P.H / S.A ^ 2) with hzdef
    have hz1 : (1 : ℝ) ≤ z := by
      have hA : 0 < S.A := by have := S.Δ_pos; have := S.Ω_pos; unfold Scale.A; positivity
      have hHA : 0 ≤ P.H / S.A ^ 2 := by have := P.H_pos; positivity
      have : sec7_cJ = (10 : ℝ) ^ 20 := rfl
      nlinarith
    have hperj : ∀ jj ∈ Finset.Icc (-⌊z⌋) ⌊z⌋,
        (((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
            (fun r : ℤ =>
              distInt (gfun jj (r : ℝ)) ≤ sec7_cTay * sec7_delta0 P S)).card : ℝ)
          ≤ C₁ * (S.R / W) := by
      intro jj hjj
      rw [Finset.mem_Icc] at hjj
      have hband : sec7_jBand P S jj := by
        have habs : |jj| ≤ ⌊z⌋ := abs_le.mpr ⟨by linarith [hjj.1], hjj.2⟩
        have hcast : |(jj : ℝ)| ≤ ((⌊z⌋ : ℤ) : ℝ) := by exact_mod_cast habs
        exact le_trans hcast (Int.floor_le z)
      exact h71 P S W Env c₀ Cu hsd hbud hg0 hu0 hX24 hlog a Ph gfun (fun _ _ => rfl)
        (sec7_cTay * sec7_delta0 P S) hδpos le_rfl jj hband
    -- sum the band: `2⌊z⌋+1 ≤ 3z` values
    have hsum := Finset.sum_le_card_nsmul _ _ _ hperj
    rw [nsmul_eq_mul] at hsum
    have hfl1 : (1 : ℤ) ≤ ⌊z⌋ := Int.le_floor.mpr (by exact_mod_cast hz1)
    have hcardz : (((Finset.Icc (-⌊z⌋) ⌊z⌋).card : ℕ) : ℝ) ≤ 3 * z := by
      rw [Int.card_Icc, show ⌊z⌋ + 1 - -⌊z⌋ = 2 * ⌊z⌋ + 1 by ring,
        show (((2 * ⌊z⌋ + 1).toNat : ℕ) : ℝ) = ((2 * ⌊z⌋ + 1 : ℤ) : ℝ) from by
          exact_mod_cast Int.toNat_of_nonneg (by linarith)]
      push_cast
      linarith [Int.floor_le z]
    -- assemble
    have htC : (0 : ℝ) ≤ C₁ * (S.R / W) :=
      le_of_lt (mul_pos hC₁ (div_pos (by linarith) hW0))
    calc (Ra.card : ℝ)
        = ((Ra.image (fun n : ℕ => (n : ℤ))).card : ℝ) := by
          rw [Finset.card_image_of_injective Ra (fun x y h => by exact_mod_cast h)]
      _ ≤ _ := hred
      _ ≤ (((Finset.Icc (-⌊z⌋) ⌊z⌋).card : ℕ) : ℝ) * (C₁ * (S.R / W)) := hsum
      _ ≤ (3 * z) * (C₁ * (S.R / W)) := mul_le_mul_of_nonneg_right hcardz htC
      _ = (3 * sec7_cJ * C₁) * ((1 + P.H / S.A ^ 2) * (S.R / W)) := by
          rw [hzdef]; ring
      _ ≤ (3 * sec7_cJ * C₁ + 1000) * ((1 + P.H / S.A ^ 2) * (S.R / W)) := by
          have hHA0 : 0 ≤ P.H / S.A ^ 2 :=
            div_nonneg P.H_pos.le (sq_nonneg S.A)
          have hRdiv0 : 0 ≤ S.R / W :=
            (div_pos (by linarith : 0 < S.R) hW0).le
          have hfac : 0 ≤ (1 + P.H / S.A ^ 2) * (S.R / W) :=
            mul_nonneg (by nlinarith) hRdiv0
          nlinarith
  · have hcard : (Ra.card : ℝ) ≤ 17 * S.R :=
      sec7_ra_card_le_17R (P := P) (S := S) (a := a) (Ra := Ra) hR1 hRa
    have hRpos : 0 < S.R := by linarith
    have hHA0 : 0 ≤ P.H / S.A ^ 2 :=
      div_nonneg P.H_pos.le (sq_nonneg S.A)
    have hRdiv : S.R ≤ S.R / W := by
      rw [le_div_iff₀ hW0]
      nlinarith
    have hRdiv_nonneg : 0 ≤ S.R / W := (div_pos hRpos hW0).le
    have hfac_ge : S.R ≤ (1 + P.H / S.A ^ 2) * (S.R / W) := by
      calc
        S.R ≤ S.R / W := hRdiv
        _ ≤ (1 + P.H / S.A ^ 2) * (S.R / W) := by
          exact le_mul_of_one_le_left hRdiv_nonneg (by nlinarith)
    have hfac_nonneg : 0 ≤ (1 + P.H / S.A ^ 2) * (S.R / W) :=
      mul_nonneg (by nlinarith) hRdiv_nonneg
    have hmain_nonneg : 0 ≤ 3 * sec7_cJ * C₁ := by
      have := sec7_cJ_pos
      positivity
    calc
      (Ra.card : ℝ) ≤ 17 * S.R := hcard
      _ ≤ 1000 * ((1 + P.H / S.A ^ 2) * (S.R / W)) := by nlinarith
      _ ≤ (3 * sec7_cJ * C₁ + 1000) * ((1 + P.H / S.A ^ 2) * (S.R / W)) := by
        nlinarith

end Squarefree
