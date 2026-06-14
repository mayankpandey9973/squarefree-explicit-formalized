import Squarefree.Bracket.Sec7FInverse
import Squarefree.Bracket.Sec7ErrAux
import Squarefree.Bracket.Sec7MonExpData
import Squarefree.Lower.DefectDeriv5
import Squarefree.Lower.Sec7DtildeWide
import Squarefree.Lower.Sec7RaResidual
import Squarefree.Opt.OnStripAux

/-!
# §7 phase constructor, final `F_a⁻¹` layer

This file is the integration layer for the concrete §7 phase functions attached to one
dyadic `a`-block.  It deliberately does not edit `BoxSum.lean` or `Sec7FInverse.lean`.

The concrete functions are defined here:

* `sec7_phase_ftil r = F_a(dtilde_a(r))`;
* `sec7_phase_f2D m` is the `m`-th `r`-derivative family of `ftil`;
* `sec7_phase_f1D j m` is the derivative family of `-dBreve'(ftil + j)`;
* `sec7_phase_f3D j m` is the derivative family of `dBreve(ftil + j)`.

The remaining theorem stubs are intentionally local to this new file: they mark the scale
and §3 expansion/critical-zero obligations needed to turn these definitions into the full
`Sec7Phase` bundle consumed by `BoxSum.sec7_phase_build`.
-/

open Classical Filter Real
open scoped Topology

namespace Squarefree

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-- Concrete §7 `ftil`: `F_a(dtilde_a(r))`. -/
noncomputable def sec7_phase_ftil (P : Globals) (_S : Scale P) (a : ℤ) : ℝ → ℝ :=
  fun r => Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))

/-- Concrete inverse branch `dBreve = F_a⁻¹`. -/
noncomputable def sec7_phase_dBreve (P : Globals) (a : ℤ) : ℝ → ℝ :=
  dBreve P.X (a : ℝ)

/-- First inverse-derivative handle. -/
noncomputable def sec7_phase_dBreve' (P : Globals) (a : ℤ) : ℝ → ℝ :=
  dBreve' P.X (a : ℝ)

/-- Second inverse-derivative handle. -/
noncomputable def sec7_phase_dBreve'' (P : Globals) (a : ℤ) : ℝ → ℝ :=
  dBreve'' P.X (a : ℝ)

/-- Third inverse-derivative handle, used in the chain-rule bookkeeping. -/
noncomputable def sec7_phase_dBreve''' (P : Globals) (a : ℤ) : ℝ → ℝ :=
  dBreve''' P.X (a : ℝ)

/-- Fourth inverse-derivative handle, used in the chain-rule bookkeeping. -/
noncomputable def sec7_phase_dBreve'''' (P : Globals) (a : ℤ) : ℝ → ℝ :=
  dBreve'''' P.X (a : ℝ)

/-- `f₂^{(m)}`: the `m`-th `r`-derivative family of `ftil`. -/
noncomputable def sec7_phase_f2D (P : Globals) (S : Scale P) (a : ℤ) :
    ℕ → ℝ → ℝ :=
  fun m => iteratedDeriv m (sec7_phase_ftil P S a)

/-- `f₁^{(m)}`: the derivative family of `-dBreve'(ftil + j)`. -/
noncomputable def sec7_phase_f1D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ :=
  fun j m =>
    iteratedDeriv m
      (fun r => -sec7_phase_dBreve' P a (sec7_phase_ftil P S a r + (j : ℝ)))

/-- `f₃^{(m)}`: the derivative family of `dBreve(ftil + j)`. -/
noncomputable def sec7_phase_f3D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ :=
  fun j m =>
    iteratedDeriv m
      (fun r => sec7_phase_dBreve P a (sec7_phase_ftil P S a r + (j : ℝ)))

/-- Local copy of the §7 envelope margin needed by this constructor. -/
private theorem sec7_phase_shift_margin {P : Globals} {S : Scale P} {W : ℝ}
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

private theorem sec7_phase_shift_margin_strong {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    W + W ^ 2 + W ^ 4 ≤ S.R / 6000 := by
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
  have h6000 : 6000 * (W + W ^ 2 + W ^ 4) ≤ 18000 * W ^ 8 := by
    calc
      6000 * (W + W ^ 2 + W ^ 4) ≤ 6000 * (3 * W ^ 4) := by gcongr
      _ = 18000 * W ^ 4 := by ring
      _ ≤ 18000 * W ^ 8 := by gcongr
  have hC : (18000 : ℝ) * W ^ 8 ≤ sec7_envC * W ^ 8 := by
    gcongr
    norm_num [sec7_envC]
  have h6000R : 6000 * (W + W ^ 2 + W ^ 4) ≤ S.R := le_trans (le_trans h6000 hC) henv
  nlinarith

private theorem sec7_phase_rWin_pos {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    ∀ r ∈ sec7_rWin S W, 0 < r := by
  intro r hr
  have hR : 0 < S.R := sec7_R_pos S
  have hs := sec7_phase_shift_margin Env hW c₀ Cu hsd
  simp only [sec7_rWin, Set.mem_Icc] at hr
  nlinarith

private theorem sec7_phase_rWinWide_pos {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    ∀ r ∈ sec7_rWinWide S W, 0 < r := by
  intro r hr
  have hR : 0 < S.R := sec7_R_pos S
  have hs := sec7_phase_shift_margin Env hW c₀ Cu hsd
  simp only [sec7_rWinWide, Set.mem_Ioo] at hr
  nlinarith

private theorem sec7_hasDerivAt_iteratedDeriv_of_contDiffAt {g : ℝ → ℝ} {r : ℝ} {m : ℕ}
    (hg : ContDiffAt ℝ 4 g r) (hm : m < 4) :
    HasDerivAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g r) r := by
  rw [iteratedDeriv_succ]
  refine (?_ : DifferentiableAt ℝ (iteratedDeriv m g) r).hasDerivAt
  have hF : DifferentiableAt ℝ (iteratedFDeriv ℝ m g) r := by
    exact hg.differentiableAt_iteratedFDeriv (by exact_mod_cast hm)
  rw [iteratedDeriv_eq_equiv_comp]
  exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm.differentiableAt).comp r hF

private theorem sec7_hasDerivAt_iteratedDeriv_of_contDiffAt5 {g : ℝ → ℝ} {r : ℝ} {m : ℕ}
    (hg : ContDiffAt ℝ 5 g r) (hm : m < 5) :
    HasDerivAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g r) r := by
  rw [iteratedDeriv_succ]
  refine (?_ : DifferentiableAt ℝ (iteratedDeriv m g) r).hasDerivAt
  have hF : DifferentiableAt ℝ (iteratedFDeriv ℝ m g) r := by
    exact hg.differentiableAt_iteratedFDeriv (by exact_mod_cast hm)
  rw [iteratedDeriv_eq_equiv_comp]
  exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm.differentiableAt).comp r hF

private theorem sec7_Ffun_contDiffAt {n : WithTop ℕ∞} {X a d : ℝ}
    (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ n (fun t => Ffun X a t) d := by
  have h1 : ContDiffAt ℝ n (fun t : ℝ => X / t ^ 2) d :=
    (contDiffAt_const).div (contDiffAt_id.pow 2) (pow_ne_zero 2 hd)
  have h2 : ContDiffAt ℝ n (fun t : ℝ => X / (t + a) ^ 2) d :=
    (contDiffAt_const).div ((contDiffAt_id.add contDiffAt_const).pow 2) (pow_ne_zero 2 hda)
  have h := h1.sub h2
  have hfun : (fun t => Ffun X a t) = (fun t : ℝ => X / t ^ 2) - (fun t : ℝ => X / (t + a) ^ 2) := by
    funext t
    simp [Ffun, Pi.sub_apply]
  rw [hfun]
  exact h

private theorem sec7_dtilde_r_contDiffAt {n : WithTop ℕ∞} {X r a : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ n (fun y => dtilde X y a) r := by
  have hinner_arg : ContDiffAt ℝ n (fun y : ℝ => X * a ^ 3 / y) r := by
    exact (contDiffAt_const (c := X * a ^ 3)).div contDiffAt_id (ne_of_gt hr)
  have hinner : ContDiffAt ℝ n (fun y : ℝ => Real.sqrt (X * a ^ 3 / y)) r := by
    refine ContDiffAt.sqrt hinner_arg ?_
    exact ne_of_gt (by positivity : 0 < X * a ^ 3 / r)
  have hrad : ContDiffAt ℝ n
      (fun y : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / y)) r := by
    fun_prop (disch := assumption)
  have houter : ContDiffAt ℝ n
      (fun y : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / y))) r := by
    refine ContDiffAt.sqrt hrad ?_
    have : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have : ContDiffAt ℝ n
      (fun y : ℝ => (-a + Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / y))) / 2) r := by
    fun_prop (disch := assumption)
  simpa [dtilde] using this

private theorem sec7_dtilde_r_contDiffAt4 {X r a : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 4 (fun y => dtilde X y a) r :=
  sec7_dtilde_r_contDiffAt (n := 4) hX ha hr

private theorem sec7_dtilde_r_contDiffAt5 {X r a : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 5 (fun y => dtilde X y a) r :=
  sec7_dtilde_r_contDiffAt (n := 5) hX ha hr

private theorem sec7_phase_ftil_contDiffAt {n : WithTop ℕ∞} {P : Globals} {S : Scale P}
    {a : ℤ} {r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ n (sec7_phase_ftil P S a) r := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hdt := sec7_dtilde_r_contDiffAt (n := n) (X := P.X) (a := (a : ℝ)) P.X_pos haR hr
  have hdt_pos : 0 < dtilde P.X r (a : ℝ) := dtilde_pos P.X_pos haR hr
  have hF : ContDiffAt ℝ n (fun d => Ffun P.X (a : ℝ) d) (dtilde P.X r (a : ℝ)) :=
    sec7_Ffun_contDiffAt (X := P.X) (a := (a : ℝ)) (d := dtilde P.X r (a : ℝ))
      (ne_of_gt hdt_pos) (by positivity)
  exact hF.comp r hdt

private theorem sec7_phase_ftil_contDiffAt4 {P : Globals} {S : Scale P} {a : ℤ} {r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 4 (sec7_phase_ftil P S a) r :=
  sec7_phase_ftil_contDiffAt (n := 4) (P := P) (S := S) (a := a) ha hr

private theorem sec7_phase_ftil_contDiffAt5 {P : Globals} {S : Scale P} {a : ℤ} {r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 5 (sec7_phase_ftil P S a) r :=
  sec7_phase_ftil_contDiffAt (n := 5) (P := P) (S := S) (a := a) ha hr

private theorem sec7_phase_R3X_div_A5_eq_F4 {P : Globals} (S : Scale P) :
    S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hH := P.H_pos
  have hG := P.G_pos
  rw [Scale.R, Scale.A, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_phase_ftil_F_factor {P : Globals} (S : Scale P) :
    P.H / S.A ^ 2 * (S.R * S.Δ) = S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.A Scale.R Scale.F
  field_simp

private theorem sec7_phase_rWin_core {P : Globals} {S : Scale P} {W r : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) (hr : r ∈ sec7_rWin S W) :
    (107 / 18000 : ℝ) * S.R ≤ r ∧ r ≤ (40001 / 1000 : ℝ) * S.R := by
  have hR : 0 < S.R := sec7_R_pos S
  have hs := sec7_phase_shift_margin Env hW c₀ Cu hsd
  simp only [sec7_rWin, Set.mem_Icc] at hr
  constructor <;> nlinarith

private theorem sec7_phase_rWinWide_core {P : Globals} {S : Scale P} {W r : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) (hr : r ∈ sec7_rWinWide S W) :
    (107 / 18000 : ℝ) * S.R ≤ r ∧ r ≤ (40001 / 1000 : ℝ) * S.R := by
  have hR : 0 < S.R := sec7_R_pos S
  have hs := sec7_phase_shift_margin_strong Env hW c₀ Cu hsd
  simp only [sec7_rWinWide, Set.mem_Ioo] at hr
  constructor <;> nlinarith

private theorem sec7_phase_AD_omega_le {P : Globals} {S : Scale P}
    (hAD : 10 * S.A ≤ S.D) : 10 * S.Ω ≤ P.H := by
  have hΔ : 0 < S.Δ := S.Δ_pos
  have hAD' : 10 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by
    simpa [Scale.A, Scale.D, mul_assoc, mul_left_comm, mul_comm] using hAD
  have hAD'' : S.Δ * (10 * S.Ω) ≤ S.Δ * P.H := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hAD'
  exact le_of_mul_le_mul_left hAD'' hΔ

private theorem sec7_phase_le_of_fourth {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  exact le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hb h

private theorem sec7_phase_F_pos {P : Globals} (S : Scale P) : 0 < S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.F
  positivity

private theorem sec7_phase_R_mono_nat {P : Globals} (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
  rw [OnStripAux.R_mono P S, Real.rpow_one,
    show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]]

private theorem sec7_phase_F_large_const {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    (10:ℝ) ^ 100 * (sec7_cJ + 1) ≤ S.F := by
  have hF : 0 < S.F := sec7_phase_F_pos S
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hΩ : 0 < S.Ω := S.Ω_pos
  have hC : 0 < sec7_envC2 := sec7_envC2_pos
  have hn6 : sec7_envC2 * S.Ω ^ 4 ≤ P.H * S.x := by
    have hW30 : (1:ℝ) ≤ W ^ 30 := one_le_pow₀ hW
    have h0 : 0 ≤ sec7_envC2 * S.Ω ^ 4 :=
      mul_nonneg hC.le (pow_nonneg hΩ.le 4)
    calc
      sec7_envC2 * S.Ω ^ 4 ≤ sec7_envC2 * S.Ω ^ 4 * W ^ 30 :=
        le_mul_of_one_le_right h0 hW30
      _ = sec7_envC2 * (W ^ 30 * S.Ω ^ 4) := by ring
      _ ≤ P.H * S.x := Env.n6
  have hn6div : sec7_envC2 ≤ P.H * S.x / S.Ω ^ 4 := by
    rw [le_div_iff₀ (by positivity : 0 < S.Ω ^ 4)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hn6
  have hn7 : sec7_envC2 ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := by
    have hW54 : (1:ℝ) ≤ W ^ 54 := one_le_pow₀ hW
    have h0 : 0 ≤ sec7_envC2 := hC.le
    calc
      sec7_envC2 ≤ sec7_envC2 * W ^ 54 :=
        le_mul_of_one_le_right h0 hW54
      _ ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := Env.n7
  have hF4 : sec7_envC2 ^ 4 ≤ S.F ^ 4 := by
    calc
      sec7_envC2 ^ 4 = sec7_envC2 ^ 3 * sec7_envC2 := by ring
      _ ≤ (P.H * S.x / S.Ω ^ 4) ^ 3 *
          (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) := by
            exact mul_le_mul (pow_le_pow_left₀ hC.le hn6div 3) hn7
              hC.le
              (pow_nonneg
                (div_nonneg (mul_nonneg P.H_pos.le (OnStripAux.x_pos P S).le)
                  (pow_nonneg hΩ.le 4)) 3)
      _ = S.F ^ 4 := by
            rw [Scale.F_eq_H_x_G_Ω]
            field_simp [hΩ.ne']
  have hK0 : 0 ≤ (10:ℝ) ^ 100 * (sec7_cJ + 1) := by
    have := sec7_cJ_pos
    positivity
  have hKleC : (10:ℝ) ^ 100 * (sec7_cJ + 1) ≤ sec7_envC2 := by
    norm_num [sec7_cJ, sec7_envC2]
  have hK4 : ((10:ℝ) ^ 100 * (sec7_cJ + 1)) ^ 4 ≤ S.F ^ 4 :=
    le_trans (pow_le_pow_left₀ hK0 hKleC 4) hF4
  exact sec7_phase_le_of_fourth hK0 hF.le hK4

private theorem sec7_phase_HA2_large {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) :
    (10:ℝ) ^ 100 * sec7_cJ * (P.H / S.A ^ 2) ≤ S.F := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hlog0 : 0 ≤ Real.log P.X := Real.log_nonneg hsd.hX
  have hlog1 : (1:ℝ) ≤ 1 + Real.log P.X := by linarith
  have hR : 0 < S.R := sec7_R_pos S
  have hΔ : 0 < S.Δ := S.Δ_pos
  have hΩ : 0 < S.Ω := S.Ω_pos
  have hA : 0 < S.A := by
    unfold Scale.A
    positivity
  have hHA : 0 ≤ P.H / S.A ^ 2 := div_nonneg P.H_pos.le (sq_nonneg S.A)
  have hRlarge : sec7_envC ≤ S.R := by
    calc
      sec7_envC ≤ sec7_envC * W ^ 8 := by
        exact le_mul_of_one_le_right sec7_envC_pos.le (one_le_pow₀ hW)
      _ ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 8)) hlog1
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := Env.tc4
      _ = S.R := sec7_phase_R_mono_nat S
  have hΔlarge_sq : sec7_envC ≤ S.Δ ^ 2 := by
    have htc9x : sec7_envC * S.x ≤ P.H := by
      have hW16 : (1:ℝ) ≤ W ^ 16 := one_le_pow₀ hW
      have hL2 : (1:ℝ) ≤ (1 + Real.log P.X) ^ 2 := by
        have hs := (sq_le_sq₀ zero_le_one
          (by linarith : 0 ≤ 1 + Real.log P.X)).mpr hlog1
        simpa using hs
      calc
        sec7_envC * S.x ≤ sec7_envC * (W ^ 16 * S.x) := by
          have hxW : S.x ≤ W ^ 16 * S.x :=
            le_mul_of_one_le_left (OnStripAux.x_pos P S).le hW16
          exact mul_le_mul_of_nonneg_left
            hxW sec7_envC_pos.le
        _ ≤ sec7_envC * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2 := by
          exact le_mul_of_one_le_right
            (mul_nonneg sec7_envC_pos.le
              (mul_nonneg (pow_nonneg hW0 16) (OnStripAux.x_pos P S).le)) hL2
        _ ≤ P.H := Env.tc9
    have hmul : sec7_envC * P.H ≤ P.H * S.Δ ^ 2 := by
      have htc9x' : sec7_envC * (P.H / S.Δ ^ 2) ≤ P.H := by
        simpa [Scale.x] using htc9x
      have hstep := mul_le_mul_of_nonneg_right htc9x' (pow_nonneg hΔ.le 2)
      calc
        sec7_envC * P.H = sec7_envC * (P.H / S.Δ ^ 2) * S.Δ ^ 2 := by
          field_simp [hΔ.ne']
        _ ≤ P.H * S.Δ ^ 2 := hstep
    exact le_of_mul_le_mul_left (by simpa [mul_comm] using hmul) P.H_pos
  have hΔlarge : 1 ≤ S.Δ := by
    have h1 : (1:ℝ) ≤ S.Δ ^ 2 := le_trans (by norm_num [sec7_envC]) hΔlarge_sq
    exact (sq_le_sq₀ zero_le_one hΔ.le).mp (by simpa using h1)
  have hRDlarge : (10:ℝ) ^ 100 * sec7_cJ ≤ S.R * S.Δ := by
    calc
      (10:ℝ) ^ 100 * sec7_cJ ≤ sec7_envC := by
        norm_num [sec7_cJ, sec7_envC]
      _ ≤ S.R := hRlarge
      _ ≤ S.R * S.Δ := by
        exact le_mul_of_one_le_right hR.le hΔlarge
  calc
    (10:ℝ) ^ 100 * sec7_cJ * (P.H / S.A ^ 2)
        ≤ (S.R * S.Δ) * (P.H / S.A ^ 2) := by
          exact mul_le_mul_of_nonneg_right hRDlarge hHA
    _ = S.F := by
          rw [← sec7_phase_ftil_F_factor S]
          ring

private theorem sec7_phase_shift_error_bound {P : Globals} {S : Scale P} {W θ : ℝ}
    {j : ℤ} (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (c₀ Cu : ℝ)
    (hsd : OnStripAux.StripData P S c₀ Cu) (hj : sec7_jBand P S j)
    (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    |(j : ℝ)| + θ ≤ S.F / 1000 := by
  have hF : 0 < S.F := sec7_phase_F_pos S
  have hpow : (0:ℝ) < (10:ℝ) ^ 100 := by positivity
  have hlarge0 := sec7_phase_F_large_const (P := P) (S := S) (W := W) Env hW
  have hlargeHA := sec7_phase_HA2_large (P := P) (S := S) (W := W) Env hW c₀ Cu hsd
  have hsmall0 : sec7_cJ + 1 ≤ S.F / (10:ℝ) ^ 100 := by
    rw [le_div_iff₀ hpow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlarge0
  have hsmallHA : sec7_cJ * (P.H / S.A ^ 2) ≤ S.F / (10:ℝ) ^ 100 := by
    rw [le_div_iff₀ hpow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlargeHA
  have hj_abs : |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := by
    rw [← Int.cast_abs]
    simpa [sec7_jBand] using hj
  have hj_split : |(j : ℝ)| ≤ sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := by
    calc
      |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := hj_abs
      _ = sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := by ring
  have hθhi : θ ≤ 1 := hθ.2
  have hc : (2:ℝ) / (10:ℝ) ^ 100 ≤ 1 / 1000 := by norm_num
  calc
    |(j : ℝ)| + θ ≤ (sec7_cJ + sec7_cJ * (P.H / S.A ^ 2)) + 1 := by
      linarith
    _ = (sec7_cJ + 1) + sec7_cJ * (P.H / S.A ^ 2) := by ring
    _ ≤ S.F / (10:ℝ) ^ 100 + S.F / (10:ℝ) ^ 100 := by
      exact add_le_add hsmall0 hsmallHA
    _ ≤ S.F / 1000 := by
      nlinarith

private theorem sec7_phase_ftil_scale {P : Globals} {S : Scale P} {r : ℝ} {a : ℤ}
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hrlo : (107 / 18000 : ℝ) * S.R ≤ r)
    (hrhi : r ≤ (40001 / 1000 : ℝ) * S.R) :
    S.F / 500 ≤ sec7_phase_ftil P S a r ∧
      sec7_phase_ftil P S a r ≤ 300 * S.F := by
  have hR : 0 < S.R := sec7_R_pos S
  have hF : 0 < S.F := sec7_phase_F_pos S
  have hA : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have hX : 0 < P.X := P.X_pos
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hr0 : 0 < r := by
    have hbase : 0 < (107 / 18000 : ℝ) * S.R := by positivity
    exact lt_of_lt_of_le hbase hrlo
  have hclosed := ftil_closed (X := P.X) (r := r) (a := (a : ℝ)) hX haR hr0
  have hftil_eq :
      sec7_phase_ftil P S a r =
        r * Real.sqrt ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) /
          (a : ℝ) ^ 2 := by
    simpa [sec7_phase_ftil] using hclosed
  have hq_nonneg : 0 ≤ P.X * (a : ℝ) ^ 3 / r := by positivity
  have hrad_nonneg :
      0 ≤ (a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by positivity
  have hftil_nonneg : 0 ≤ sec7_phase_ftil P S a r := by
    rw [hftil_eq]
    positivity
  have hclosed_low :
      16 * P.X * r ^ 3 / (a : ℝ) ^ 5 ≤ (sec7_phase_ftil P S a r) ^ 4 := by
    rw [hftil_eq]
    calc
      16 * P.X * r ^ 3 / (a : ℝ) ^ 5
          = r ^ 4 * (4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 /
              (a : ℝ) ^ 8 := by
            rw [show (4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 =
                16 * (P.X * (a : ℝ) ^ 3 / r) by
                  rw [mul_pow, Real.sq_sqrt hq_nonneg]
                  ring]
            field_simp [ne_of_gt hr0, ne_of_gt haR]
      _ ≤ r ^ 4 *
            (((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) /
              (a : ℝ) ^ 8 := by
            have hterm_nonneg :
                0 ≤ 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by positivity
            have hrad_ge :
                4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) ≤
                  (a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by
              nlinarith [sq_nonneg (a : ℝ)]
            have hsq :=
              pow_le_pow_left₀ hterm_nonneg hrad_ge 2
            gcongr
      _ = (r * Real.sqrt
              ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) /
            (a : ℝ) ^ 2) ^ 4 := by
            rw [div_pow, mul_pow,
              show Real.sqrt
                  ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 by
                  rw [show Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                    (Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) ^ 2
                    by ring, Real.sq_sqrt hrad_nonneg]]
            ring
  have hconst_low :
      (1 : ℝ) / 500 ^ 4 ≤
        16 * ((107 / 18000 : ℝ) ^ 3) / 11 ^ 5 := by
    norm_num
  have hscale_low :
      (S.F / 500) ^ 4 ≤ 16 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
    have hr3 :
        ((107 / 18000 : ℝ) * S.R) ^ 3 ≤ r ^ 3 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ (107 / 18000 : ℝ) * S.R) hrlo 3
    have ha5 : (a : ℝ) ^ 5 ≤ (11 * S.A) ^ 5 :=
      pow_le_pow_left₀ haR.le ha_hi 5
    have hnum :
        16 * P.X * (((107 / 18000 : ℝ) * S.R) ^ 3) ≤
          16 * P.X * r ^ 3 := by
      gcongr
    have hdenpos : 0 < (a : ℝ) ^ 5 := pow_pos haR 5
    calc
      (S.F / 500) ^ 4
          = (1 / (500:ℝ) ^ 4) * (S.R ^ 3 * P.X / S.A ^ 5) := by
            rw [sec7_phase_R3X_div_A5_eq_F4 S]
            ring
      _ ≤ (16 * ((107 / 18000 : ℝ) ^ 3) / 11 ^ 5) *
            (S.R ^ 3 * P.X / S.A ^ 5) := by
            exact mul_le_mul_of_nonneg_right hconst_low (by positivity)
      _ = 16 * P.X * (((107 / 18000 : ℝ) * S.R) ^ 3) / (11 * S.A) ^ 5 := by
            field_simp [ne_of_gt hA]
      _ ≤ 16 * P.X * r ^ 3 / (11 * S.A) ^ 5 := by
            exact div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 16 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
            exact div_le_div_of_nonneg_left (by positivity) hdenpos ha5
  have hlow4 : (S.F / 500) ^ 4 ≤ (sec7_phase_ftil P S a r) ^ 4 :=
    le_trans hscale_low hclosed_low
  have hlow :
      S.F / 500 ≤ sec7_phase_ftil P S a r :=
    sec7_phase_le_of_fourth (by positivity) hftil_nonneg hlow4
  have hΩH : 10 * S.Ω ≤ P.H := sec7_phase_AD_omega_le hAD
  have hΩle : S.Ω ≤ P.H / 10 := by nlinarith
  have hΩ4 : S.Ω ^ 4 ≤ (P.H / 10) ^ 4 :=
    pow_le_pow_left₀ S.Ω_pos.le hΩle 4
  have harX : (a : ℝ) * r ≤ P.X := by
    have hstep :
        (a : ℝ) * r ≤ (11 * S.A) * ((40001 / 1000 : ℝ) * S.R) := by
      exact mul_le_mul ha_hi hrhi hr0.le (by positivity)
    calc
      (a : ℝ) * r ≤ (11 * S.A) * ((40001 / 1000 : ℝ) * S.R) := hstep
      _ = (11 * (40001 / 1000 : ℝ)) * (P.H * P.G * S.Ω ^ 4) := by
            unfold Scale.A Scale.R
            field_simp [S.Δ_pos.ne']
      _ ≤ (11 * (40001 / 1000 : ℝ)) * (P.H * P.G * (P.H / 10) ^ 4) := by
            have hmid :
                P.H * P.G * S.Ω ^ 4 ≤ P.H * P.G * (P.H / 10) ^ 4 := by
              exact mul_le_mul_of_nonneg_left hΩ4
                (mul_nonneg P.H_pos.le P.G_pos.le)
            exact mul_le_mul_of_nonneg_left hmid (by norm_num)
      _ ≤ P.X := by
            rw [P.X_eq_G_mul_H_pow_five]
            have hc : (11 * (40001 / 1000 : ℝ)) / 10 ^ 4 ≤ 1 := by norm_num
            calc
              (11 * (40001 / 1000 : ℝ)) * (P.H * P.G * (P.H / 10) ^ 4)
                  = ((11 * (40001 / 1000 : ℝ)) / 10 ^ 4) *
                      (P.G * P.H ^ 5) := by ring_nf
              _ ≤ 1 * (P.G * P.H ^ 5) := by
                    exact mul_le_mul_of_nonneg_right hc
                      (mul_nonneg P.G_pos.le (pow_nonneg P.H_pos.le 5))
              _ = P.G * P.H ^ 5 := by ring
  have ha2_sq_le : ((a : ℝ) ^ 2) ^ 2 ≤ P.X * (a : ℝ) ^ 3 / r := by
    rw [le_div_iff₀ hr0]
    calc
      ((a : ℝ) ^ 2) ^ 2 * r = (a : ℝ) ^ 3 * ((a : ℝ) * r) := by ring
      _ ≤ (a : ℝ) ^ 3 * P.X := by
            exact mul_le_mul_of_nonneg_left harX (by positivity)
      _ = P.X * (a : ℝ) ^ 3 := by ring
  have ha2_le_sqrt :
      (a : ℝ) ^ 2 ≤ Real.sqrt (P.X * (a : ℝ) ^ 3 / r) :=
    Real.le_sqrt_of_sq_le ha2_sq_le
  have hrad_le :
      (a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) ≤
        5 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r) := by
    nlinarith
  have hclosed_hi :
      (sec7_phase_ftil P S a r) ^ 4 ≤
        25 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
    rw [hftil_eq]
    calc
      (r * Real.sqrt
              ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) /
            (a : ℝ) ^ 2) ^ 4
          = r ^ 4 *
              (((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) /
                (a : ℝ) ^ 8 := by
            rw [div_pow, mul_pow,
              show Real.sqrt
                  ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 by
                  rw [show Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 4 =
                    (Real.sqrt
                      ((a : ℝ) ^ 2 + 4 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2) ^ 2
                    by ring, Real.sq_sqrt hrad_nonneg]]
            ring
      _ ≤ r ^ 4 * (5 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 /
            (a : ℝ) ^ 8 := by
            have hsq := pow_le_pow_left₀ hrad_nonneg hrad_le 2
            gcongr
      _ = 25 * P.X * r ^ 3 / (a : ℝ) ^ 5 := by
            rw [show (5 * Real.sqrt (P.X * (a : ℝ) ^ 3 / r)) ^ 2 =
                25 * (P.X * (a : ℝ) ^ 3 / r) by
                  rw [mul_pow, Real.sq_sqrt hq_nonneg]
                  ring]
            field_simp [ne_of_gt hr0, ne_of_gt haR]
  have hconst_hi :
      25 * ((40001 / 1000 : ℝ) ^ 3) * 5 ^ 5 ≤ 300 ^ 4 := by
    norm_num
  have hscale_hi :
      25 * P.X * r ^ 3 / (a : ℝ) ^ 5 ≤ (300 * S.F) ^ 4 := by
    have hr3 : r ^ 3 ≤ ((40001 / 1000 : ℝ) * S.R) ^ 3 :=
      pow_le_pow_left₀ hr0.le hrhi 3
    have ha5 : (S.A / 5) ^ 5 ≤ (a : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ S.A / 5) ha_lo 5
    have hnum :
        25 * P.X * r ^ 3 ≤
          25 * P.X * (((40001 / 1000 : ℝ) * S.R) ^ 3) := by
      gcongr
    have hdenposa : 0 < (a : ℝ) ^ 5 := pow_pos haR 5
    have hdenposlo : 0 < (S.A / 5) ^ 5 := by positivity
    calc
      25 * P.X * r ^ 3 / (a : ℝ) ^ 5
          ≤ 25 * P.X * (((40001 / 1000 : ℝ) * S.R) ^ 3) / (a : ℝ) ^ 5 := by
            exact div_le_div_of_nonneg_right hnum hdenposa.le
      _ ≤ 25 * P.X * (((40001 / 1000 : ℝ) * S.R) ^ 3) / (S.A / 5) ^ 5 := by
            exact div_le_div_of_nonneg_left (by positivity) hdenposlo ha5
      _ = (25 * ((40001 / 1000 : ℝ) ^ 3) * 5 ^ 5) *
            (S.R ^ 3 * P.X / S.A ^ 5) := by
            field_simp [ne_of_gt hA]
      _ ≤ 300 ^ 4 * (S.R ^ 3 * P.X / S.A ^ 5) := by
            exact mul_le_mul_of_nonneg_right hconst_hi (by positivity)
      _ = (300 * S.F) ^ 4 := by
            rw [sec7_phase_R3X_div_A5_eq_F4 S]
            ring
  have hhi4 : (sec7_phase_ftil P S a r) ^ 4 ≤ (300 * S.F) ^ 4 :=
    le_trans hclosed_hi hscale_hi
  have hhi :
      sec7_phase_ftil P S a r ≤ 300 * S.F :=
    sec7_phase_le_of_fourth hftil_nonneg (by positivity) hhi4
  exact ⟨hlow, hhi⟩

private noncomputable def sec7_F1loc (X a d : ℝ) : ℝ :=
  -2 * X / d ^ 3 + 2 * X / (d + a) ^ 3

private theorem sec7_F1_contDiffAt {n : WithTop ℕ∞} {X a d : ℝ}
    (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ n (fun t => sec7_F1loc X a t) d := by
  have h1 : ContDiffAt ℝ n (fun t : ℝ => -2 * X / t ^ 3) d :=
    (contDiffAt_const (c := -2 * X)).div (contDiffAt_id.pow 3) (pow_ne_zero 3 hd)
  have h2 : ContDiffAt ℝ n (fun t : ℝ => 2 * X / (t + a) ^ 3) d :=
    (contDiffAt_const (c := 2 * X)).div ((contDiffAt_id.add contDiffAt_const).pow 3)
      (pow_ne_zero 3 hda)
  simpa [sec7_F1loc] using h1.add h2

private theorem sec7_F1_contDiffAt4 {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ 4 (fun t => sec7_F1loc X a t) d :=
  sec7_F1_contDiffAt (n := 4) hd hda

private theorem sec7_F1_contDiffAt5 {X a d : ℝ} (hd : d ≠ 0) (hda : d + a ≠ 0) :
    ContDiffAt ℝ 5 (fun t => sec7_F1loc X a t) d :=
  sec7_F1_contDiffAt (n := 5) hd hda

private theorem sec7_Ffun_deriv_neg {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    sec7_F1loc X a d < 0 := by
  have hda : d + a ≠ 0 := by positivity
  rw [sec7_F1loc, Ffun_deriv1_factor X a d (ne_of_gt hd) hda]
  have hnum : 0 < 2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by positivity
  have hden : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
  rw [show -2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
        (d ^ 3 * (d + a) ^ 3)
      = -(2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) /
        (d ^ 3 * (d + a) ^ 3)) by ring]
  exact neg_neg_of_pos (div_pos hnum hden)

private theorem sec7_dBreve_contDiffAt_Ffun {n : WithTop ℕ∞} {X a d : ℝ}
    (hn : n ≠ 0)
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ n (dBreve X a) (Ffun X a d) := by
  let A : ℝ := sec7_F1loc X a d
  have hA_ne : A ≠ 0 := by
    exact ne_of_lt (by simpa [A] using sec7_Ffun_deriv_neg hX ha hd)
  let i : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 A hA_ne)
  have hFcd : ContDiffAt ℝ n (fun t => Ffun X a t) d :=
    sec7_Ffun_contDiffAt (X := X) (a := a) (d := d) (ne_of_gt hd) (by positivity)
  have hFd : HasDerivAt (fun t => Ffun X a t) A d := by
    simpa [A, sec7_F1loc] using Ffun_hasDerivAt_d X a d (ne_of_gt hd) (by positivity)
  have hFdF : HasFDerivAt (fun t => Ffun X a t) (i : ℝ →L[ℝ] ℝ) d := by
    simpa [i] using hFd.hasFDerivAt_equiv hA_ne
  have hloc : ContDiffAt ℝ n (hFcd.localInverse hFdF hn) (Ffun X a d) :=
    hFcd.to_localInverse hFdF hn
  have hleft : ∀ᶠ x in 𝓝 d, dBreve X a (Ffun X a x) = x := by
    filter_upwards [eventually_gt_nhds hd] with x hx
    exact dBreve_spec hX ha hx
  have heq : dBreve X a =ᶠ[𝓝 (Ffun X a d)] hFcd.localInverse hFdF hn := by
    have hstrict := hFcd.hasStrictFDerivAt' hFdF hn
    exact hstrict.localInverse_unique hleft
  exact ContDiffAt.congr_of_eventuallyEq hloc heq

private theorem sec7_dBreve_contDiffAt4_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 4 (dBreve X a) (Ffun X a d) :=
  sec7_dBreve_contDiffAt_Ffun (n := 4) (by norm_num) hX ha hd

private theorem sec7_dBreve_contDiffAt5_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 5 (dBreve X a) (Ffun X a d) :=
  sec7_dBreve_contDiffAt_Ffun (n := 5) (by norm_num) hX ha hd

private theorem sec7_dBreve_contDiffAt6_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 6 (dBreve X a) (Ffun X a d) :=
  sec7_dBreve_contDiffAt_Ffun (n := 6) (by norm_num) hX ha hd

private theorem sec7_dBreve'_contDiffAt_Ffun {n : WithTop ℕ∞} {X a d : ℝ}
    (hn : n ≠ 0)
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ n (dBreve' X a) (Ffun X a d) := by
  have hdb := sec7_dBreve_contDiffAt_Ffun (n := n) hn (X := X) (a := a) (d := d) hX ha hd
  have hdval : dBreve X a (Ffun X a d) = d := dBreve_spec hX ha hd
  have hF1 : ContDiffAt ℝ n (fun y => sec7_F1loc X a y)
      (dBreve X a (Ffun X a d)) := by
    rw [hdval]
    exact sec7_F1_contDiffAt (n := n) (X := X) (a := a) (d := d) (ne_of_gt hd) (by positivity)
  have hcomp := hF1.comp (Ffun X a d) hdb
  have hne : sec7_F1loc X a (dBreve X a (Ffun X a d)) ≠ 0 := by
    rw [hdval]
    exact ne_of_lt (sec7_Ffun_deriv_neg hX ha hd)
  have hinv : ContDiffAt ℝ n (fun t => (sec7_F1loc X a (dBreve X a t))⁻¹) (Ffun X a d) :=
    hcomp.inv hne
  unfold dBreve'
  change ContDiffAt ℝ n (fun t => (sec7_F1loc X a (dBreve X a t))⁻¹) (Ffun X a d)
  exact hinv

private theorem sec7_dBreve'_contDiffAt4_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 4 (dBreve' X a) (Ffun X a d) :=
  sec7_dBreve'_contDiffAt_Ffun (n := 4) (by norm_num) hX ha hd

private theorem sec7_dBreve'_contDiffAt5_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 5 (dBreve' X a) (Ffun X a d) :=
  sec7_dBreve'_contDiffAt_Ffun (n := 5) (by norm_num) hX ha hd

private theorem sec7_phase_shift_mem (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (_hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu) :
    ∀ r ∈ sec7_rWin S W, ∀ j, sec7_jBand P S j →
      ∀ θ ∈ Set.Icc (0:ℝ) 1, sec7_phase_ftil P S a r + j - θ ∈ sec7_tWin S := by
  intro r hr j hj θ hθ
  have hrcore := sec7_phase_rWin_core Env hW c₀ Cu hsd hr
  obtain ⟨hftil_lo, hftil_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD ha_lo ha_hi hrcore.1 hrcore.2
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := θ) (j := j)
      Env hW c₀ Cu hsd hj hθ
  have hshift_lo : -(S.F / 1000) ≤ (j : ℝ) - θ := by
    have hjlo : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le (j : ℝ)
    have hθlo : 0 ≤ θ := hθ.1
    nlinarith
  have hshift_hi : (j : ℝ) - θ ≤ S.F / 1000 := by
    have hjhi : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
    have hθlo : 0 ≤ θ := hθ.1
    nlinarith
  have hcWin : sec7_cWin = (1000:ℝ) := by norm_num [sec7_cWin]
  simp only [sec7_tWin, Set.mem_Icc]
  constructor
  · rw [hcWin]
    nlinarith
  · rw [hcWin]
    nlinarith [hftil_hi, hshift_hi, sec7_phase_F_pos S]

private theorem sec7_phase_f3_base_contDiffAt4 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWin S W) :
    ContDiffAt ℝ 4
      (fun x => sec7_phase_dBreve P a (sec7_phase_ftil P S a x + (j : ℝ))) r := by
  have hr0 : 0 < r := sec7_phase_rWin_pos Env hW c₀ Cu hsd r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hftil : ContDiffAt ℝ 4 (sec7_phase_ftil P S a) r :=
    sec7_phase_ftil_contDiffAt4 (P := P) (S := S) (a := a) ha hr0
  set t : ℝ := sec7_phase_ftil P S a r + (j : ℝ) with ht
  have htWin : t ∈ sec7_tWin S := by
    have h :=
      sec7_phase_shift_mem P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
        r hr j hj 0 (by norm_num)
    simpa [t, ht] using h
  have himg :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo ha_hi htWin
  have hd0 : 0 < dBreve P.X (a : ℝ) t := dBreve_pos
  have hdb :=
    sec7_dBreve_contDiffAt4_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR hd0
  have hdb_at : ContDiffAt ℝ 4 (dBreve P.X (a : ℝ)) t := by
    simpa [himg.1] using hdb
  have harg : ContDiffAt ℝ 4 (fun x => sec7_phase_ftil P S a x + (j : ℝ)) r :=
    hftil.add contDiffAt_const
  simpa [sec7_phase_dBreve, t, ht] using hdb_at.comp r harg

private theorem sec7_phase_f1_base_contDiffAt4 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWin S W) :
    ContDiffAt ℝ 4
      (fun x => -sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ))) r := by
  have hr0 : 0 < r := sec7_phase_rWin_pos Env hW c₀ Cu hsd r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hftil : ContDiffAt ℝ 4 (sec7_phase_ftil P S a) r :=
    sec7_phase_ftil_contDiffAt4 (P := P) (S := S) (a := a) ha hr0
  set t : ℝ := sec7_phase_ftil P S a r + (j : ℝ) with ht
  have htWin : t ∈ sec7_tWin S := by
    have h :=
      sec7_phase_shift_mem P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
        r hr j hj 0 (by norm_num)
    simpa [t, ht] using h
  have himg :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo ha_hi htWin
  have hd0 : 0 < dBreve P.X (a : ℝ) t := dBreve_pos
  have hdb :=
    sec7_dBreve'_contDiffAt4_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR hd0
  have hdb_at : ContDiffAt ℝ 4 (dBreve' P.X (a : ℝ)) t := by
    simpa [himg.1] using hdb
  have harg : ContDiffAt ℝ 4 (fun x => sec7_phase_ftil P S a x + (j : ℝ)) r :=
    hftil.add contDiffAt_const
  have hcomp : ContDiffAt ℝ 4
      (fun x => sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ))) r := by
    simpa [sec7_phase_dBreve', t, ht] using hdb_at.comp r harg
  simpa using hcomp.neg

/-- §3 leading coefficient for the `f₁` monomial expansion. -/
noncomputable def sec7_phase_ra_c₁ (P : Globals) (S : Scale P) (a : ℤ) : ℤ → ℝ :=
  fun _ => (1 / 6) * ((a : ℝ) / S.A) ^ 2

/-- §3 leading coefficient for the `f₂` monomial expansion. -/
noncomputable def sec7_phase_ra_c₂ (P : Globals) (S : Scale P) (a : ℤ) : ℤ → ℝ :=
  fun _ => 2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)

private theorem sec7_phase_a_lo_wide {P : Globals} {S : Scale P} {a : ℤ}
    (ha_lo : S.A ≤ (a : ℝ)) :
    S.A / 5 ≤ (a : ℝ) := by
  have hApos : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  nlinarith

private theorem sec7_phase_a_hi_wide {P : Globals} {S : Scale P} {a : ℤ}
    (ha_hi : (a : ℝ) ≤ 2 * S.A) :
    (a : ℝ) ≤ 11 * S.A := by
  have hApos : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  nlinarith

private theorem sec7_phase_ra_c₁_window_lo {P : Globals} {S : Scale P} {a j : ℤ}
    (ha_lo : S.A ≤ (a : ℝ)) :
    1 / 16 ≤ |sec7_phase_ra_c₁ P S a j| := by
  have hApos : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have hs_lo : (1 : ℝ) ≤ (a : ℝ) / S.A := by
    rw [le_div_iff₀ hApos]
    simpa using ha_lo
  have hsq_ge : (1 : ℝ) ≤ ((a : ℝ) / S.A) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs_lo 2
    simpa using h
  rw [sec7_phase_ra_c₁, abs_of_nonneg (by positivity :
    0 ≤ (1 / 6 : ℝ) * ((a : ℝ) / S.A) ^ 2)]
  nlinarith

private theorem sec7_phase_ra_c₁_window_hi {P : Globals} {S : Scale P} {a j : ℤ}
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A) :
    |sec7_phase_ra_c₁ P S a j| ≤ 4 := by
  have hApos : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have hs_lo : (1 : ℝ) ≤ (a : ℝ) / S.A := by
    rw [le_div_iff₀ hApos]
    simpa using ha_lo
  have hs_nonneg : 0 ≤ (a : ℝ) / S.A := le_trans zero_le_one hs_lo
  have hs_hi : (a : ℝ) / S.A ≤ 2 := by
    rw [div_le_iff₀ hApos]
    simpa using ha_hi
  have hsq_le : ((a : ℝ) / S.A) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hs_nonneg hs_hi 2
  rw [sec7_phase_ra_c₁, abs_of_nonneg (by positivity :
    0 ≤ (1 / 6 : ℝ) * ((a : ℝ) / S.A) ^ 2)]
  nlinarith

private theorem sec7_phase_ra_c₂_window_lo {P : Globals} {S : Scale P} {a j : ℤ}
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A) :
    1 / 16 ≤ |sec7_phase_ra_c₂ P S a j| := by
  have hApos : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have ha_pos : 0 < (a : ℝ) := lt_of_lt_of_le hApos ha_lo
  have hu_lo : (1 / 2 : ℝ) ≤ S.A / (a : ℝ) := by
    rw [le_div_iff₀ ha_pos]
    nlinarith
  have hpow_mono :
      (1 / 2 : ℝ) ^ ((5 : ℝ) / 4) ≤
        (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4) := by
    exact Real.rpow_le_rpow (by norm_num) hu_lo (by norm_num)
  have hhalf_floor : (1 / 32 : ℝ) ≤ (1 / 2 : ℝ) ^ ((5 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : ((5 : ℝ) / 4) ≤ 5)
    rw [show (1 / 2 : ℝ) ^ (5 : ℝ) = (1 / 2 : ℝ) ^ (5 : ℕ) by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]] at h
    norm_num at h
    exact h
  rw [sec7_phase_ra_c₂, abs_of_nonneg (by positivity :
    0 ≤ 2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4))]
  nlinarith

private theorem sec7_phase_ra_c₂_window_hi {P : Globals} {S : Scale P} {a j : ℤ}
    (ha_lo : S.A ≤ (a : ℝ)) :
    |sec7_phase_ra_c₂ P S a j| ≤ 4 := by
  have hApos : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have ha_pos : 0 < (a : ℝ) := lt_of_lt_of_le hApos ha_lo
  have hu_hi : S.A / (a : ℝ) ≤ 1 := by
    rw [div_le_iff₀ ha_pos]
    simpa using ha_lo
  have hu_nonneg : 0 ≤ S.A / (a : ℝ) := by positivity
  have hpow_le : (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4) ≤ 1 := by
    have h := Real.rpow_le_rpow hu_nonneg hu_hi (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 4)
    simpa using h
  rw [sec7_phase_ra_c₂, abs_of_nonneg (by positivity :
    0 ≤ 2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4))]
  nlinarith

private theorem sec7_phase_shift_mem_wide_zero (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (_hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu) :
    ∀ r ∈ sec7_rWinWide S W, ∀ j, sec7_jBand P S j →
      sec7_phase_ftil P S a r + j ∈ sec7_tWin S := by
  intro r hr j hj
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hftil_lo, hftil_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD ha_lo ha_hi hrcore.1 hrcore.2
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hshift_lo : -(S.F / 1000) ≤ (j : ℝ) := by
    have hjlo : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le (j : ℝ)
    nlinarith
  have hshift_hi : (j : ℝ) ≤ S.F / 1000 := by
    have hjhi : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
    nlinarith
  have hcWin : sec7_cWin = (1000:ℝ) := by norm_num [sec7_cWin]
  simp only [sec7_tWin, Set.mem_Icc]
  constructor
  · rw [hcWin]
    nlinarith
  · rw [hcWin]
    nlinarith [hftil_hi, hshift_hi, sec7_phase_F_pos S]

private theorem sec7_phase_f3_base_contDiffAt5 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5
      (fun x => sec7_phase_dBreve P a (sec7_phase_ftil P S a x + (j : ℝ))) r := by
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hftil : ContDiffAt ℝ 5 (sec7_phase_ftil P S a) r :=
    sec7_phase_ftil_contDiffAt5 (P := P) (S := S) (a := a) ha hr0
  set t : ℝ := sec7_phase_ftil P S a r + (j : ℝ) with ht
  have htWin : t ∈ sec7_tWin S := by
    have h :=
      sec7_phase_shift_mem_wide_zero P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
        r hr j hj
    simpa [t, ht] using h
  have himg :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo ha_hi htWin
  have hd0 : 0 < dBreve P.X (a : ℝ) t := dBreve_pos
  have hdb :=
    sec7_dBreve_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR hd0
  have hdb_at : ContDiffAt ℝ 5 (dBreve P.X (a : ℝ)) t := by
    simpa [himg.1] using hdb
  have harg : ContDiffAt ℝ 5 (fun x => sec7_phase_ftil P S a x + (j : ℝ)) r :=
    hftil.add contDiffAt_const
  simpa [sec7_phase_dBreve, t, ht] using hdb_at.comp r harg

private theorem sec7_phase_f1_base_contDiffAt5 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5
      (fun x => -sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ))) r := by
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hftil : ContDiffAt ℝ 5 (sec7_phase_ftil P S a) r :=
    sec7_phase_ftil_contDiffAt5 (P := P) (S := S) (a := a) ha hr0
  set t : ℝ := sec7_phase_ftil P S a r + (j : ℝ) with ht
  have htWin : t ∈ sec7_tWin S := by
    have h :=
      sec7_phase_shift_mem_wide_zero P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
        r hr j hj
    simpa [t, ht] using h
  have himg :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo ha_hi htWin
  have hd0 : 0 < dBreve P.X (a : ℝ) t := dBreve_pos
  have hdb :=
    sec7_dBreve'_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR hd0
  have hdb_at : ContDiffAt ℝ 5 (dBreve' P.X (a : ℝ)) t := by
    simpa [himg.1] using hdb
  have harg : ContDiffAt ℝ 5 (fun x => sec7_phase_ftil P S a x + (j : ℝ)) r :=
    hftil.add contDiffAt_const
  have hcomp : ContDiffAt ℝ 5
      (fun x => sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ))) r := by
    simpa [sec7_phase_dBreve', t, ht] using hdb_at.comp r harg
  simpa using hcomp.neg

private theorem sec7_phase_rpow_div_contDiffAt5 {P : Globals} {S : Scale P}
    {r α : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ 5 (fun t : ℝ => (t / S.R) ^ α) r := by
  have hR : 0 < S.R := sec7_R_pos S
  have harg : ContDiffAt ℝ 5 (fun t : ℝ => t / S.R) r := contDiffAt_id.div_const S.R
  exact harg.rpow_const_of_ne (div_ne_zero (ne_of_gt hr) (ne_of_gt hR))

private theorem sec7_phase_ra_e₁_base_contDiffAt5 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5
      (fun t => sec7_phase_f1D P S a j 0 t
        - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ))) r := by
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hbase0 : ContDiffAt ℝ 5
      (fun x => -sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ))) r :=
    sec7_phase_f1_base_contDiffAt5 (P := P) (S := S) (W := W) (a := a) (j := j)
      (r := r) ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd hj hr
  have hbase : ContDiffAt ℝ 5 (fun t => sec7_phase_f1D P S a j 0 t) r := by
    simpa [sec7_phase_f1D] using hbase0
  have hpow := sec7_phase_rpow_div_contDiffAt5 (P := P) (S := S)
    (r := r) (α := (-(1 : ℝ))) hr0
  have hmon : ContDiffAt ℝ 5
      (fun t => sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ))) r := by
    simpa [mul_assoc] using
      ((contDiffAt_const :
        ContDiffAt ℝ 5 (fun _ : ℝ => sec7_phase_ra_c₁ P S a j * S.T₁) r).mul hpow)
  exact hbase.sub hmon

private theorem sec7_phase_ra_e₂_base_contDiffAt5 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5
      (fun t => sec7_phase_f2D P S a 0 t
        - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)) r := by
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hbase0 : ContDiffAt ℝ 5 (sec7_phase_ftil P S a) r :=
    sec7_phase_ftil_contDiffAt5 (P := P) (S := S) (a := a) ha hr0
  have hbase : ContDiffAt ℝ 5 (fun t => sec7_phase_f2D P S a 0 t) r := by
    simpa [sec7_phase_f2D] using hbase0
  have hpow := sec7_phase_rpow_div_contDiffAt5 (P := P) (S := S)
    (r := r) (α := ((3 : ℝ) / 4)) hr0
  have hmon : ContDiffAt ℝ 5
      (fun t => sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)) r := by
    simpa [mul_assoc] using
      ((contDiffAt_const :
        ContDiffAt ℝ 5 (fun _ : ℝ => sec7_phase_ra_c₂ P S a j * S.T₂) r).mul hpow)
  exact hbase.sub hmon

private theorem sec7_phase_ra_e₃_base_contDiffAt5 {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5
      (fun t => sec7_phase_f3D P S a j 0 t
        - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
            * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4)) r := by
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hbase0 : ContDiffAt ℝ 5
      (fun x => sec7_phase_dBreve P a (sec7_phase_ftil P S a x + (j : ℝ))) r :=
    sec7_phase_f3_base_contDiffAt5 (P := P) (S := S) (W := W) (a := a) (j := j)
      (r := r) ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd hj hr
  have hbase : ContDiffAt ℝ 5 (fun t => sec7_phase_f3D P S a j 0 t) r := by
    simpa [sec7_phase_f3D] using hbase0
  have hpow := sec7_phase_rpow_div_contDiffAt5 (P := P) (S := S)
    (r := r) (α := (-(1 : ℝ) / 4)) hr0
  have hmon : ContDiffAt ℝ 5
      (fun t => 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
          * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4)) r := by
    simpa [mul_assoc] using
      ((contDiffAt_const :
        ContDiffAt ℝ 5
          (fun _ : ℝ => 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
            * S.T₃) r).mul hpow)
  exact hbase.sub hmon

/-- Budget absorption for the `f₂` residual tower after the cancellation has produced an
`(Ω/H)^2` pointwise scale. -/
private theorem sec7_phase_ra_e₂D_budget_absorb {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) (m : ℕ) :
    (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 ≤
      sec7_cExpIn * (S.T₂ / S.R ^ m) * sec7_relErr P S := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT₂ : 0 < S.T₂ := sec7_T₂_pos S
  have hB0 : 0 ≤ S.T₂ / S.R ^ m := by positivity
  have hΩH0 : 0 ≤ S.Ω / P.H := div_nonneg S.Ω_pos.le P.H_pos.le
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hU1 : (1 : ℝ) ≤ P.U := by
    unfold Globals.U
    exact Real.one_le_rpow hsd.hX hu0.le
  have hU3 : (1 : ℝ) ≤ P.U ^ 3 := one_le_pow₀ hU1
  have hΩH_le_rel : S.Ω / P.H ≤ sec7_relErr P S := by
    unfold sec7_relErr
    calc
      S.Ω / P.H = (S.Ω / P.H) * 1 := by ring
      _ ≤ (S.Ω / P.H) * P.U ^ 3 := mul_le_mul_of_nonneg_left hU3 hΩH0
      _ = (S.Ω / P.H) * P.U ^ 3 := rfl
  have hrel143 : sec7_relErr P S * 10 ^ 143 ≤ 1 :=
    sec7_relErr_le Env hW hsd hbud hg0 hu0 hX24
  have hrel_small : sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (10 : ℝ) ^ 143)]
    simpa [mul_comm] using hrel143
  have hΩH_small : S.Ω / P.H ≤ 1 / (10 : ℝ) ^ 143 :=
    le_trans hΩH_le_rel hrel_small
  have hsq :
      (S.Ω / P.H) ^ 2 ≤ (1 / (10 : ℝ) ^ 143) * sec7_relErr P S := by
    calc
      (S.Ω / P.H) ^ 2 = (S.Ω / P.H) * (S.Ω / P.H) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 143) * (S.Ω / P.H) :=
          mul_le_mul hΩH_small le_rfl hΩH0 (by positivity)
      _ ≤ (1 / (10 : ℝ) ^ 143) * sec7_relErr P S := by
          exact mul_le_mul_of_nonneg_left hΩH_le_rel (by positivity)
  have hconst : (10 ^ 80 : ℝ) * (1 / (10 : ℝ) ^ 143) ≤ sec7_cExpIn := by
    norm_num [sec7_cExpIn]
  calc
    (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2
        ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) *
            ((1 / (10 : ℝ) ^ 143) * sec7_relErr P S) := by
          gcongr
    _ = ((10 ^ 80 : ℝ) * (1 / (10 : ℝ) ^ 143)) *
          (S.T₂ / S.R ^ m) * sec7_relErr P S := by ring
    _ ≤ sec7_cExpIn * (S.T₂ / S.R ^ m) * sec7_relErr P S := by
          gcongr

private theorem sec7_phase_T₂_four_A_five_div_R_three {P : Globals} (S : Scale P) :
    S.T₂ ^ 4 * S.A ^ 5 / S.R ^ 3 = P.X := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  rw [Scale.T₂, Scale.F, Scale.A, Scale.R, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_ra_e₂D_principal_bridge {P : Globals} {S : Scale P}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hr0 : 0 < r) :
    sec7_phase_ra_c₂ P S a j * S.T₂ * (r / S.R) ^ ((3 : ℝ) / 4) =
      2 * P.X * (a : ℝ) /
        ((dtilde P.X r (a : ℝ)) ^ ((3 : ℝ) / 2) *
          (dtilde P.X r (a : ℝ) + (a : ℝ)) ^ ((3 : ℝ) / 2)) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hX : 0 < P.X := P.X_pos
  have hA : 0 < S.A := by
    have := S.Δ_pos
    have := S.Ω_pos
    unfold Scale.A
    positivity
  have hR : 0 < S.R := sec7_R_pos S
  have hT : 0 < S.T₂ := sec7_T₂_pos S
  set d := dtilde P.X r (a : ℝ) with hddef
  have hd : 0 < d := by simpa [d] using dtilde_pos P.X_pos haR hr0
  have hda : 0 < d + (a : ℝ) := by linarith
  have hratio0 : 0 ≤ r / S.R := by positivity
  have hz0 : 0 ≤ S.A / (a : ℝ) := by positivity
  have hLnonneg : 0 ≤
      sec7_phase_ra_c₂ P S a j * S.T₂ * (r / S.R) ^ ((3 : ℝ) / 4) := by
    rw [sec7_phase_ra_c₂]
    positivity
  have hMnonneg : 0 ≤ 2 * P.X * (a : ℝ) /
      (d ^ ((3 : ℝ) / 2) * (d + (a : ℝ)) ^ ((3 : ℝ) / 2)) := by
    positivity
  have hzpow :
      ((S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) ^ 4 =
        (S.A / (a : ℝ)) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast ((S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) 4]
    rw [← Real.rpow_mul hz0]
    norm_num
  have hupow : ((r / S.R) ^ ((3 : ℝ) / 4)) ^ 4 = (r / S.R) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast ((r / S.R) ^ ((3 : ℝ) / 4)) 4]
    rw [← Real.rpow_mul hratio0]
    norm_num
  have hdpow : (d ^ ((3 : ℝ) / 2)) ^ 4 = d ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast (d ^ ((3 : ℝ) / 2)) 4]
    rw [← Real.rpow_mul hd.le]
    norm_num
  have hdapow :
      ((d + (a : ℝ)) ^ ((3 : ℝ) / 2)) ^ 4 = (d + (a : ℝ)) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast ((d + (a : ℝ)) ^ ((3 : ℝ) / 2)) 4]
    rw [← Real.rpow_mul hda.le]
    norm_num
  have hL4 :
      (sec7_phase_ra_c₂ P S a j * S.T₂ * (r / S.R) ^ ((3 : ℝ) / 4)) ^ 4 =
        16 * (S.A / (a : ℝ)) ^ (5 : ℕ) * S.T₂ ^ 4 * (r / S.R) ^ (3 : ℕ) := by
    rw [sec7_phase_ra_c₂]
    rw [mul_pow, mul_pow]
    rw [show (2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) ^ 4 =
        2 ^ 4 * ((S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) ^ 4 by ring]
    rw [hzpow, hupow]
    norm_num
  have hM4 :
      (2 * P.X * (a : ℝ) /
        (d ^ ((3 : ℝ) / 2) * (d + (a : ℝ)) ^ ((3 : ℝ) / 2))) ^ 4 =
        16 * P.X ^ 4 * (a : ℝ) ^ 4 / (d ^ 6 * (d + (a : ℝ)) ^ 6) := by
    rw [div_pow, mul_pow, mul_pow]
    rw [show (d ^ ((3 : ℝ) / 2) * (d + (a : ℝ)) ^ ((3 : ℝ) / 2)) ^ 4 =
        (d ^ ((3 : ℝ) / 2)) ^ 4 * ((d + (a : ℝ)) ^ ((3 : ℝ) / 2)) ^ 4 by ring]
    rw [hdpow, hdapow]
    norm_num
  have hspec0 : Rfun P.X (a : ℝ) d = r := by
    simpa [d, hddef] using dtilde_spec P.X_pos haR hr0
  have hspec : P.X * (a : ℝ) ^ 3 / (d ^ 2 * (d + (a : ℝ)) ^ 2) = r := by
    rw [Rfun_factor' P.X (a : ℝ) d (ne_of_gt hd) (ne_of_gt hda)] at hspec0
    exact hspec0
  have hscale' : S.T₂ ^ 4 * S.A ^ 5 = P.X * S.R ^ 3 := by
    have hscale := sec7_phase_T₂_four_A_five_div_R_three S
    rw [div_eq_iff (by positivity : S.R ^ 3 ≠ 0)] at hscale
    nlinarith
  have hfour :
      (sec7_phase_ra_c₂ P S a j * S.T₂ * (r / S.R) ^ ((3 : ℝ) / 4)) ^ 4 =
      (2 * P.X * (a : ℝ) /
        (d ^ ((3 : ℝ) / 2) * (d + (a : ℝ)) ^ ((3 : ℝ) / 2))) ^ 4 := by
    rw [hL4, hM4, ← hspec]
    field_simp [ne_of_gt hX, ne_of_gt haR, ne_of_gt hd, ne_of_gt hda,
      ne_of_gt hA, ne_of_gt hR]
    nlinarith
  apply le_antisymm
  · exact sec7_phase_le_of_fourth hLnonneg hMnonneg (by rw [hfour])
  · exact sec7_phase_le_of_fourth hMnonneg hLnonneg (by rw [hfour])

private theorem sec7_ra_e₂D_residual_bridge_point {P : Globals} {S : Scale P}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hr0 : 0 < r) :
    sec7_phase_f2D P S a 0 r
        - sec7_phase_ra_c₂ P S a j * S.T₂ * (r / S.R) ^ ((3 : ℝ) / 4) =
      Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))
        - 2 * P.X * (a : ℝ) /
          ((dtilde P.X r (a : ℝ)) ^ ((3 : ℝ) / 2) *
            (dtilde P.X r (a : ℝ) + (a : ℝ)) ^ ((3 : ℝ) / 2)) := by
  have hmain := sec7_ra_e₂D_principal_bridge (P := P) (S := S)
    (a := a) (j := j) (r := r) ha hr0
  simp [sec7_phase_f2D, sec7_phase_ftil, hmain]

/-- Graded expansion error for `f₁`, defined as derivatives of the genuine grade-0 residual. -/
noncomputable def sec7_phase_ra_e₁D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ := fun j m =>
  iteratedDeriv m
    (fun t => sec7_phase_f1D P S a j 0 t
        - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ))
    )

private theorem sec7_phase_inv3_scale_base {P : Globals} (S : Scale P) :
    S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) = S.D := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.F Scale.D Scale.A
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_phase_inv4_scale_base {P : Globals} (S : Scale P) :
    S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) = S.D := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.F Scale.D Scale.A
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem dBreve_deriv3_abs_base_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) ≤
        |dBreve''' P.X a (Ffun P.X a d)| ∧
      |dBreve''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) := by
  have hXpos : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have hAleD : S.A ≤ S.D / 10 := by nlinarith
  have hAle_d : S.A ≤ d := by nlinarith
  have ha_le_11d : a ≤ 11 * d := by nlinarith
  have ha_le_2D : a ≤ 2 * S.D := by nlinarith
  have hda_lo : d ≤ d + a := by linarith
  have hda_hi : d + a ≤ 20 * S.D := by nlinarith
  set Q : ℝ := a ^ 2 + 3 * a * d + 3 * d ^ 2 with hQ
  set Poly : ℝ := 5 * a ^ 6 + 40 * a ^ 5 * d + 140 * a ^ 4 * d ^ 2
      + 284 * a ^ 3 * d ^ 3 + 352 * a ^ 2 * d ^ 4
      + 252 * a * d ^ 5 + 84 * d ^ 6 with hPoly
  have hQ_le : Q ≤ 157 * d ^ 2 := by
    rw [hQ]
    nlinarith [sq_nonneg (a - 11 * d), hd0.le]
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ]
    positivity
  have hQ_ge : 3 * d ^ 2 ≤ Q := by
    rw [hQ]
    nlinarith [sq_nonneg a, mul_nonneg ha0.le hd0.le]
  have hpoly_lo : 84 * d ^ 6 ≤ Poly := by
    rw [hPoly]
    have h1 : 0 ≤ 5 * a ^ 6 := by positivity
    have h2 : 0 ≤ 40 * a ^ 5 * d := by positivity
    have h3 : 0 ≤ 140 * a ^ 4 * d ^ 2 := by positivity
    have h4 : 0 ≤ 284 * a ^ 3 * d ^ 3 := by positivity
    have h5 : 0 ≤ 352 * a ^ 2 * d ^ 4 := by positivity
    have h6 : 0 ≤ 252 * a * d ^ 5 := by positivity
    nlinarith
  have hterm1 : 5 * a ^ 6 ≤ 5 * (2 * S.D) ^ 6 := by gcongr
  have hterm2 : 40 * a ^ 5 * d ≤ 40 * (2 * S.D) ^ 5 * (18 * S.D) := by gcongr
  have hterm3 : 140 * a ^ 4 * d ^ 2 ≤ 140 * (2 * S.D) ^ 4 * (18 * S.D) ^ 2 := by gcongr
  have hterm4 : 284 * a ^ 3 * d ^ 3 ≤ 284 * (2 * S.D) ^ 3 * (18 * S.D) ^ 3 := by gcongr
  have hterm5 : 352 * a ^ 2 * d ^ 4 ≤ 352 * (2 * S.D) ^ 2 * (18 * S.D) ^ 4 := by gcongr
  have hterm6 : 252 * a * d ^ 5 ≤ 252 * (2 * S.D) * (18 * S.D) ^ 5 := by gcongr
  have hterm7 : 84 * d ^ 6 ≤ 84 * (18 * S.D) ^ 6 := by gcongr
  have hpoly_hi : Poly ≤ 3971174720 * S.D ^ 6 := by
    rw [hPoly]
    nlinarith [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7]
  have hda7 : d ^ 7 ≤ (d + a) ^ 7 := pow_le_pow_left₀ hd0.le hda_lo 7
  have hnum_lo : 3 * 84 * d ^ 20 ≤ 3 * d ^ 7 * (d + a) ^ 7 * Poly := by
    have hprod : d ^ 7 * d ^ 7 * (84 * d ^ 6) ≤ d ^ 7 * (d + a) ^ 7 * Poly := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hda7 (by positivity)) hpoly_lo
        (by positivity) (by positivity)
    nlinarith [hprod, hd0]
  have hQ5_hi : Q ^ 5 ≤ (157 * d ^ 2) ^ 5 := pow_le_pow_left₀ hQ_nonneg hQ_le 5
  have hden_hi : 8 * P.X ^ 3 * a ^ 3 * Q ^ 5 ≤
      8 * P.X ^ 3 * (11 * S.A) ^ 3 * (157 * d ^ 2) ^ 5 := by
    gcongr
  have hden_pos : 0 < 8 * P.X ^ 3 * a ^ 3 * Q ^ 5 := by
    rw [hQ]
    positivity
  have hden_hi_pos : 0 < 8 * P.X ^ 3 * (11 * S.A) ^ 3 * (157 * d ^ 2) ^ 5 := by
    positivity
  have hloc_lo :
      3 * 84 * d ^ 20 / (8 * P.X ^ 3 * (11 * S.A) ^ 3 * (157 * d ^ 2) ^ 5) ≤
        3 * d ^ 7 * (d + a) ^ 7 * Poly / (8 * P.X ^ 3 * a ^ 3 * Q ^ 5) := by
    rw [div_le_div_iff₀ hden_hi_pos hden_pos]
    have hmul := mul_le_mul hnum_lo hden_hi
      (by positivity : 0 ≤ 8 * P.X ^ 3 * a ^ 3 * Q ^ 5)
      (by positivity : 0 ≤ 3 * d ^ 7 * (d + a) ^ 7 * Poly)
    nlinarith [hmul]
  have hD10 : S.D ^ 10 ≤ 10 ^ 10 * d ^ 10 := by
    have hpow : (S.D / 10) ^ 10 ≤ d ^ 10 :=
      pow_le_pow_left₀ (by positivity) hd_lo 10
    nlinarith [hpow, hDpos]
  have hbase_d_lo :
      (3 * 84 : ℝ) / (8 * 11 ^ 3 * 157 ^ 5 * 10 ^ 10) *
          (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) ≤
        (3 * 84 : ℝ) / (8 * 11 ^ 3 * 157 ^ 5) *
          (d ^ 10 / (P.X ^ 3 * S.A ^ 3)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos]
    nlinarith [hD10]
  have hbase_eq_lo :
      (3 * 84 : ℝ) / (8 * 11 ^ 3 * 157 ^ 5) *
          (d ^ 10 / (P.X ^ 3 * S.A ^ 3)) =
        3 * 84 * d ^ 20 / (8 * P.X ^ 3 * (11 * S.A) ^ 3 * (157 * d ^ 2) ^ 5) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
  have hbase_lo :
      (1 / 10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) ≤
        3 * d ^ 7 * (d + a) ^ 7 * Poly / (8 * P.X ^ 3 * a ^ 3 * Q ^ 5) := by
    refine le_trans ?_ hloc_lo
    refine le_trans ?_ (by simpa [hbase_eq_lo] using hbase_d_lo)
    have hc : (1 / 10 ^ 80 : ℝ) ≤
        (3 * 84) / (8 * 11 ^ 3 * 157 ^ 5 * 10 ^ 10) := by
      norm_num
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hd7_hi : d ^ 7 ≤ (18 * S.D) ^ 7 := pow_le_pow_left₀ hd0.le hd_hi 7
  have hda7_hi : (d + a) ^ 7 ≤ (20 * S.D) ^ 7 :=
    pow_le_pow_left₀ (by positivity) hda_hi 7
  have hnum_hi : 3 * d ^ 7 * (d + a) ^ 7 * Poly ≤
      3 * (18 * S.D) ^ 7 * (20 * S.D) ^ 7 * (3971174720 * S.D ^ 6) := by
    have hprod1 : d ^ 7 * (d + a) ^ 7 ≤ (18 * S.D) ^ 7 * (20 * S.D) ^ 7 :=
      mul_le_mul hd7_hi hda7_hi (by positivity) (by positivity)
    have hprod2 := mul_le_mul hprod1 hpoly_hi (by positivity)
      (by positivity : 0 ≤ (18 * S.D) ^ 7 * (20 * S.D) ^ 7)
    nlinarith [hprod2]
  have hQ5_lo : (3 * d ^ 2) ^ 5 ≤ Q ^ 5 := pow_le_pow_left₀ (by positivity) hQ_ge 5
  have hden_lo : 8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5 ≤
      8 * P.X ^ 3 * a ^ 3 * Q ^ 5 := by
    gcongr
  have hden_lo_pos : 0 < 8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5 := by
    positivity
  have hloc_hi :
      3 * d ^ 7 * (d + a) ^ 7 * Poly / (8 * P.X ^ 3 * a ^ 3 * Q ^ 5) ≤
        3 * (18 * S.D) ^ 7 * (20 * S.D) ^ 7 * (3971174720 * S.D ^ 6) /
          (8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5) := by
    rw [div_le_div_iff₀ hden_pos hden_lo_pos]
    have hmul := mul_le_mul hnum_hi hden_lo
      (by positivity : 0 ≤ 8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5)
      (by positivity : 0 ≤ 3 * (18 * S.D) ^ 7 * (20 * S.D) ^ 7 *
        (3971174720 * S.D ^ 6))
    nlinarith [hmul]
  have hbase_hi :
      3 * (18 * S.D) ^ 7 * (20 * S.D) ^ 7 * (3971174720 * S.D ^ 6) /
          (8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5) ≤
        (10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
    have hconst : (18 : ℝ) ^ 7 * 20 ^ 7 * 3971174720 * 5 ^ 3 * 10 ^ 10 ≤
        3 ^ 4 * 8 * 10 ^ 80 := by
      norm_num
    have hright : (18 : ℝ) ^ 7 * S.D ^ 10 * 20 ^ 7 * 3971174720 * 5 ^ 3 ≤
        3 ^ 4 * 8 * d ^ 10 * 10 ^ 80 := by
      calc (18 : ℝ) ^ 7 * S.D ^ 10 * 20 ^ 7 * 3971174720 * 5 ^ 3
          ≤ (18 : ℝ) ^ 7 * (10 ^ 10 * d ^ 10) * 20 ^ 7 * 3971174720 * 5 ^ 3 := by
            gcongr
        _ = ((18 : ℝ) ^ 7 * 20 ^ 7 * 3971174720 * 5 ^ 3 * 10 ^ 10) *
              d ^ 10 := by ring
        _ ≤ (3 ^ 4 * 8 * 10 ^ 80) * d ^ 10 := by
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 3 ^ 4 * 8 * d ^ 10 * 10 ^ 80 := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hright
  rw [dBreve_deriv3_abs_factor_image P.X_pos ha0 hd0]
  rw [hQ, hPoly] at hbase_lo hloc_hi
  exact ⟨hbase_lo, le_trans hloc_hi hbase_hi⟩

/-- Graded expansion error for `f₂`, defined as derivatives of the genuine grade-0 residual. -/
noncomputable def sec7_phase_ra_e₂D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ := fun j m =>
  iteratedDeriv m
    (fun t => sec7_phase_f2D P S a 0 t
        - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)
    )

/-- Graded expansion error for `f₃`, defined as derivatives of the genuine grade-0 residual. -/
noncomputable def sec7_phase_ra_e₃D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ := fun j m =>
  iteratedDeriv m
    (fun t => sec7_phase_f3D P S a j 0 t
        - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
            * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4)
    )

/-- Planned k=3 inverse scale packaging: `F³ |dBreve'''| ≍ HΔ` on the wide image window. -/
theorem dBreve_deriv3_scale_wide_image_construct {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 80 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 80 : ℝ) * (P.H * S.Δ) := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  obtain ⟨hlo, hhi⟩ :=
    dBreve_deriv3_abs_base_wide (P := P) (S := S) (a := a) (d := d)
      hAD ha_lo ha_hi hd_lo hd_hi
  constructor
  · calc (1 / 10 ^ 80 : ℝ) * (P.H * S.Δ)
        = (1 / 10 ^ 80 : ℝ) * S.D := rfl
      _ = S.F ^ 3 * ((1 / 10 ^ 80 : ℝ) *
            (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) := by
            rw [show S.F ^ 3 * ((1 / 10 ^ 80 : ℝ) *
                  (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) =
                (1 / 10 ^ 80 : ℝ) *
                  (S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) by ring,
              sec7_phase_inv3_scale_base S]
      _ ≤ S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)|
        ≤ S.F ^ 3 * ((10 ^ 80 : ℝ) *
            (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = (10 ^ 80 : ℝ) * (P.H * S.Δ) := by
            rw [show S.F ^ 3 * ((10 ^ 80 : ℝ) *
                  (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) =
                (10 ^ 80 : ℝ) *
                  (S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) by ring,
              sec7_phase_inv3_scale_base S]
            rfl

private theorem dBreve_deriv4_abs_base_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) ≤
        |dBreve'''' P.X a (Ffun P.X a d)| ∧
      |dBreve'''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) := by
  have hXpos : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 10) hd_lo
  have hAleD : S.A ≤ S.D / 10 := by nlinarith
  have hAle_d : S.A ≤ d := by nlinarith
  have ha_le_11d : a ≤ 11 * d := by nlinarith
  have ha_le_2D : a ≤ 2 * S.D := by nlinarith
  have hda_lo : d ≤ d + a := by linarith
  have hda_hi : d + a ≤ 20 * S.D := by nlinarith
  have had2_lo : 2 * d ≤ a + 2 * d := by linarith
  have had2_hi : a + 2 * d ≤ 38 * S.D := by nlinarith
  set Q : ℝ := a ^ 2 + 3 * a * d + 3 * d ^ 2 with hQ
  set Poly : ℝ := 7 * a ^ 8 + 70 * a ^ 7 * d + 322 * a ^ 6 * d ^ 2
      + 912 * a ^ 5 * d ^ 3 + 1728 * a ^ 4 * d ^ 4
      + 2232 * a ^ 3 * d ^ 5 + 1920 * a ^ 2 * d ^ 6
      + 1008 * a * d ^ 7 + 252 * d ^ 8 with hPoly
  have hQ_le : Q ≤ 157 * d ^ 2 := by
    rw [hQ]
    nlinarith [sq_nonneg (a - 11 * d), hd0.le]
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ]
    positivity
  have hQ_ge : 3 * d ^ 2 ≤ Q := by
    rw [hQ]
    nlinarith [sq_nonneg a, mul_nonneg ha0.le hd0.le]
  have hpoly_lo : 252 * d ^ 8 ≤ Poly := by
    rw [hPoly]
    have h1 : 0 ≤ 7 * a ^ 8 := by positivity
    have h2 : 0 ≤ 70 * a ^ 7 * d := by positivity
    have h3 : 0 ≤ 322 * a ^ 6 * d ^ 2 := by positivity
    have h4 : 0 ≤ 912 * a ^ 5 * d ^ 3 := by positivity
    have h5 : 0 ≤ 1728 * a ^ 4 * d ^ 4 := by positivity
    have h6 : 0 ≤ 2232 * a ^ 3 * d ^ 5 := by positivity
    have h7 : 0 ≤ 1920 * a ^ 2 * d ^ 6 := by positivity
    have h8 : 0 ≤ 1008 * a * d ^ 7 := by positivity
    nlinarith
  have hterm1 : 7 * a ^ 8 ≤ 7 * (2 * S.D) ^ 8 := by gcongr
  have hterm2 : 70 * a ^ 7 * d ≤ 70 * (2 * S.D) ^ 7 * (18 * S.D) := by gcongr
  have hterm3 : 322 * a ^ 6 * d ^ 2 ≤ 322 * (2 * S.D) ^ 6 * (18 * S.D) ^ 2 := by gcongr
  have hterm4 : 912 * a ^ 5 * d ^ 3 ≤ 912 * (2 * S.D) ^ 5 * (18 * S.D) ^ 3 := by gcongr
  have hterm5 : 1728 * a ^ 4 * d ^ 4 ≤ 1728 * (2 * S.D) ^ 4 * (18 * S.D) ^ 4 := by gcongr
  have hterm6 : 2232 * a ^ 3 * d ^ 5 ≤ 2232 * (2 * S.D) ^ 3 * (18 * S.D) ^ 5 := by gcongr
  have hterm7 : 1920 * a ^ 2 * d ^ 6 ≤ 1920 * (2 * S.D) ^ 2 * (18 * S.D) ^ 6 := by gcongr
  have hterm8 : 1008 * a * d ^ 7 ≤ 1008 * (2 * S.D) * (18 * S.D) ^ 7 := by gcongr
  have hterm9 : 252 * d ^ 8 ≤ 252 * (18 * S.D) ^ 8 := by gcongr
  have hpoly_hi : Poly ≤ 4309299073792 * S.D ^ 8 := by
    rw [hPoly]
    nlinarith [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8, hterm9]
  have hda9 : d ^ 9 ≤ (d + a) ^ 9 := pow_le_pow_left₀ hd0.le hda_lo 9
  have hnum_lo : 15 * 2 * 252 * d ^ 27 ≤
      15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly := by
    have hprod1 : d ^ 9 * d ^ 9 ≤ d ^ 9 * (d + a) ^ 9 :=
      mul_le_mul_of_nonneg_left hda9 (by positivity)
    have hprod2 : d ^ 9 * d ^ 9 * (2 * d) ≤
        d ^ 9 * (d + a) ^ 9 * (a + 2 * d) :=
      mul_le_mul hprod1 had2_lo (by positivity) (by positivity)
    have hprod3 : d ^ 9 * d ^ 9 * (2 * d) * (252 * d ^ 8) ≤
        d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly :=
      mul_le_mul hprod2 hpoly_lo (by positivity) (by positivity)
    nlinarith [hprod3, hd0]
  have hQ7_hi : Q ^ 7 ≤ (157 * d ^ 2) ^ 7 := pow_le_pow_left₀ hQ_nonneg hQ_le 7
  have hden_hi : 16 * P.X ^ 4 * a ^ 4 * Q ^ 7 ≤
      16 * P.X ^ 4 * (11 * S.A) ^ 4 * (157 * d ^ 2) ^ 7 := by
    gcongr
  have hden_pos : 0 < 16 * P.X ^ 4 * a ^ 4 * Q ^ 7 := by
    rw [hQ]
    positivity
  have hden_hi_pos : 0 < 16 * P.X ^ 4 * (11 * S.A) ^ 4 * (157 * d ^ 2) ^ 7 := by
    positivity
  have hloc_lo :
      15 * 2 * 252 * d ^ 27 /
          (16 * P.X ^ 4 * (11 * S.A) ^ 4 * (157 * d ^ 2) ^ 7) ≤
        15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly /
          (16 * P.X ^ 4 * a ^ 4 * Q ^ 7) := by
    rw [div_le_div_iff₀ hden_hi_pos hden_pos]
    have hmul := mul_le_mul hnum_lo hden_hi
      (by positivity : 0 ≤ 16 * P.X ^ 4 * a ^ 4 * Q ^ 7)
      (by positivity : 0 ≤ 15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly)
    nlinarith [hmul]
  have hD13 : S.D ^ 13 ≤ 10 ^ 13 * d ^ 13 := by
    have hpow : (S.D / 10) ^ 13 ≤ d ^ 13 :=
      pow_le_pow_left₀ (by positivity) hd_lo 13
    nlinarith [hpow, hDpos]
  have hbase_d_lo :
      (15 * 2 * 252 : ℝ) / (16 * 11 ^ 4 * 157 ^ 7 * 10 ^ 13) *
          (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) ≤
        (15 * 2 * 252 : ℝ) / (16 * 11 ^ 4 * 157 ^ 7) *
          (d ^ 13 / (P.X ^ 4 * S.A ^ 4)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos]
    nlinarith [hD13]
  have hbase_eq_lo :
      (15 * 2 * 252 : ℝ) / (16 * 11 ^ 4 * 157 ^ 7) *
          (d ^ 13 / (P.X ^ 4 * S.A ^ 4)) =
        15 * 2 * 252 * d ^ 27 /
          (16 * P.X ^ 4 * (11 * S.A) ^ 4 * (157 * d ^ 2) ^ 7) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
  have hbase_lo :
      (1 / 10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) ≤
        15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly /
          (16 * P.X ^ 4 * a ^ 4 * Q ^ 7) := by
    refine le_trans ?_ hloc_lo
    refine le_trans ?_ (by simpa [hbase_eq_lo] using hbase_d_lo)
    have hc : (1 / 10 ^ 100 : ℝ) ≤
        (15 * 2 * 252) / (16 * 11 ^ 4 * 157 ^ 7 * 10 ^ 13) := by
      norm_num
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hd9_hi : d ^ 9 ≤ (18 * S.D) ^ 9 := pow_le_pow_left₀ hd0.le hd_hi 9
  have hda9_hi : (d + a) ^ 9 ≤ (20 * S.D) ^ 9 :=
    pow_le_pow_left₀ (by positivity) hda_hi 9
  have hnum_hi : 15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly ≤
      15 * (18 * S.D) ^ 9 * (20 * S.D) ^ 9 * (38 * S.D) *
        (4309299073792 * S.D ^ 8) := by
    have hprod1 : d ^ 9 * (d + a) ^ 9 ≤ (18 * S.D) ^ 9 * (20 * S.D) ^ 9 :=
      mul_le_mul hd9_hi hda9_hi (by positivity) (by positivity)
    have hprod2 : d ^ 9 * (d + a) ^ 9 * (a + 2 * d) ≤
        (18 * S.D) ^ 9 * (20 * S.D) ^ 9 * (38 * S.D) :=
      mul_le_mul hprod1 had2_hi (by positivity) (by positivity)
    have hprod3 := mul_le_mul hprod2 hpoly_hi (by positivity)
      (by positivity : 0 ≤ (18 * S.D) ^ 9 * (20 * S.D) ^ 9 * (38 * S.D))
    nlinarith [hprod3]
  have hQ7_lo : (3 * d ^ 2) ^ 7 ≤ Q ^ 7 := pow_le_pow_left₀ (by positivity) hQ_ge 7
  have hden_lo : 16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7 ≤
      16 * P.X ^ 4 * a ^ 4 * Q ^ 7 := by
    gcongr
  have hden_lo_pos : 0 < 16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7 := by
    positivity
  have hloc_hi :
      15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly /
          (16 * P.X ^ 4 * a ^ 4 * Q ^ 7) ≤
        15 * (18 * S.D) ^ 9 * (20 * S.D) ^ 9 * (38 * S.D) *
          (4309299073792 * S.D ^ 8) /
          (16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7) := by
    rw [div_le_div_iff₀ hden_pos hden_lo_pos]
    have hmul := mul_le_mul hnum_hi hden_lo
      (by positivity : 0 ≤ 16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7)
      (by positivity : 0 ≤ 15 * (18 * S.D) ^ 9 * (20 * S.D) ^ 9 * (38 * S.D) *
        (4309299073792 * S.D ^ 8))
    nlinarith [hmul]
  have hD14 : S.D ^ 14 ≤ 10 ^ 14 * d ^ 14 := by
    have hpow : (S.D / 10) ^ 14 ≤ d ^ 14 :=
      pow_le_pow_left₀ (by positivity) hd_lo 14
    nlinarith [hpow, hDpos]
  have hbase_hi :
      15 * (18 * S.D) ^ 9 * (20 * S.D) ^ 9 * (38 * S.D) *
          (4309299073792 * S.D ^ 8) /
          (16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7) ≤
        (10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
    have hconst : (15 : ℝ) * 18 ^ 9 * 20 ^ 9 * 38 * 4309299073792 *
        5 ^ 4 * 10 ^ 14 ≤ 16 * 3 ^ 7 * 10 ^ 100 := by
      norm_num
    have hright : (15 : ℝ) * 18 ^ 9 * S.D ^ 14 * 20 ^ 9 * 38 *
        4309299073792 * 5 ^ 4 ≤ 16 * 3 ^ 7 * d ^ 14 * 10 ^ 100 := by
      calc (15 : ℝ) * 18 ^ 9 * S.D ^ 14 * 20 ^ 9 * 38 * 4309299073792 * 5 ^ 4
          ≤ (15 : ℝ) * 18 ^ 9 * (10 ^ 14 * d ^ 14) * 20 ^ 9 * 38 *
              4309299073792 * 5 ^ 4 := by
            gcongr
        _ = ((15 : ℝ) * 18 ^ 9 * 20 ^ 9 * 38 * 4309299073792 * 5 ^ 4 *
              10 ^ 14) * d ^ 14 := by ring
        _ ≤ (16 * 3 ^ 7 * 10 ^ 100) * d ^ 14 := by
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 16 * 3 ^ 7 * d ^ 14 * 10 ^ 100 := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hright
  rw [dBreve_deriv4_abs_factor_image P.X_pos ha0 hd0]
  rw [hQ, hPoly] at hbase_lo hloc_hi
  exact ⟨hbase_lo, le_trans hloc_hi hbase_hi⟩

/-- Planned k=4 inverse scale packaging: `F⁴ |dBreve''''| ≍ HΔ` on the wide image window. -/
theorem dBreve_deriv4_scale_wide_image_construct {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  obtain ⟨hlo, hhi⟩ :=
    dBreve_deriv4_abs_base_wide (P := P) (S := S) (a := a) (d := d)
      hAD ha_lo ha_hi hd_lo hd_hi
  constructor
  · calc (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ)
        = (1 / 10 ^ 100 : ℝ) * S.D := rfl
      _ = S.F ^ 4 * ((1 / 10 ^ 100 : ℝ) *
            (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) := by
            rw [show S.F ^ 4 * ((1 / 10 ^ 100 : ℝ) *
                  (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) =
                (1 / 10 ^ 100 : ℝ) *
                  (S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) by ring,
              sec7_phase_inv4_scale_base S]
      _ ≤ S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)|
        ≤ S.F ^ 4 * ((10 ^ 100 : ℝ) *
            (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
            rw [show S.F ^ 4 * ((10 ^ 100 : ℝ) *
                  (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) =
                (10 ^ 100 : ℝ) *
                  (S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) by ring,
              sec7_phase_inv4_scale_base S]
            rfl

/-- The one-variable residual after subtracting the §7 `f₂` principal term. -/
private noncomputable def sec7_ra_rhoFun (X a : ℝ) : ℝ → ℝ :=
  fun d => Ffun X a d
    - 2 * X * a / (d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2))

private theorem sec7_ra_rhoFun_contDiffOn_Ioi {X a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ 5 (sec7_ra_rhoFun X a) (Set.Ioi 0) := by
  have hF : ContDiffOn ℝ 5 (fun d => Ffun X a d) (Set.Ioi 0) := by
    intro d hd
    have hd0 : 0 < d := hd
    exact (sec7_Ffun_contDiffAt (X := X) (a := a) (d := d)
      (ne_of_gt hd0) (ne_of_gt (by linarith))).contDiffWithinAt
  have hid : ContDiffOn ℝ 5 (fun d : ℝ => d) (Set.Ioi 0) := contDiff_id.contDiffOn
  have hp₁ : ContDiffOn ℝ 5 (fun d : ℝ => d ^ ((3 : ℝ) / 2)) (Set.Ioi 0) :=
    hid.rpow_const_of_ne (by intro d hd; exact ne_of_gt hd)
  have hp₂ : ContDiffOn ℝ 5 (fun d : ℝ => (d + a) ^ ((3 : ℝ) / 2)) (Set.Ioi 0) :=
    (hid.add contDiffOn_const).rpow_const_of_ne
      (by
        intro d hd
        have hd0 : 0 < d := hd
        exact ne_of_gt (by linarith))
  have hden : ContDiffOn ℝ 5
      (fun d : ℝ => d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2)) (Set.Ioi 0) :=
    hp₁.mul hp₂
  have hterm : ContDiffOn ℝ 5
      (fun d : ℝ => 2 * X * a /
        (d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2))) (Set.Ioi 0) := by
    exact contDiffOn_const.div hden (by
      intro d hd
      have hd0 : 0 < d := hd
      exact mul_ne_zero
        (ne_of_gt (Real.rpow_pos_of_pos hd0 _))
        (ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)))
  exact hF.sub hterm

private theorem sec7_ra_rpow_neg_cancel_bound {D d : ℝ} {i : ℕ}
    (hD : 0 < D) (hdlo : D / 20 ≤ d) :
    D ^ i * d ^ ((-5 : ℝ) - i) ≤ 20 ^ (5 + i) / D ^ 5 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity : 0 < D / 20) hdlo
  have hpow_lo : (D / 20) ^ (5 + i) ≤ d ^ (5 + i) :=
    pow_le_pow_left₀ (by positivity : 0 ≤ D / 20) hdlo (5 + i)
  have hpow_pos : 0 < (D / 20) ^ (5 + i) := by positivity
  have hinv : (d ^ (5 + i))⁻¹ ≤ ((D / 20) ^ (5 + i))⁻¹ :=
    inv_anti₀ hpow_pos hpow_lo
  have hrpow : d ^ ((-5 : ℝ) - i) = (d ^ (5 + i))⁻¹ := by
    rw [show ((-5 : ℝ) - (i : ℝ)) = -(((5 + i : ℕ) : ℝ)) by norm_num; ring]
    rw [Real.rpow_neg hdpos.le, Real.rpow_natCast]
  have hstep : D ^ i * d ^ ((-5 : ℝ) - i) ≤ D ^ i * ((D / 20) ^ (5 + i))⁻¹ := by
    rw [hrpow]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  calc
    D ^ i * d ^ ((-5 : ℝ) - i) ≤ D ^ i * ((D / 20) ^ (5 + i))⁻¹ := hstep
    _ = 20 ^ (5 + i) / D ^ 5 := by
      rw [div_pow, inv_div]
      rw [show D ^ (5 + i) = D ^ 5 * D ^ i by rw [pow_add]]
      field_simp [ne_of_gt hD, pow_ne_zero _ (ne_of_gt hD)]

private theorem sec7_ra_rho_rescale_const_bound {i : ℕ} (hi : i ≤ 5) :
    sec7_ra_rhoScale i * 20 ^ (5 + i) ≤ (10 ^ 20 : ℝ) := by
  interval_cases i <;> norm_num [sec7_ra_rhoScale]

private theorem sec7_ra_rho_rescaled_FDeriv_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) {i : ℕ} (hi : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) (Set.Ioi 0)
        (dtilde P.X r (a : ℝ) / S.D)‖
      ≤ (10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5) := by
  have hDpos : 0 < S.D := S.D_pos
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨hd_lo, hd_ge_a, _hd_hi⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  set u : ℝ := d / S.D with hu_def
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 20) (by simpa [d] using hd_lo)
  have hu : u ∈ Set.Ioi (0 : ℝ) := by
    rw [hu_def]
    exact div_pos hdpos hDpos
  have hSDu : S.D * u = d := by
    rw [hu_def]
    field_simp [ne_of_gt hDpos]
  have hmaps : Set.MapsTo (fun y : ℝ => S.D * y) (Set.Ioi 0) (Set.Ioi 0) := by
    intro y hy
    exact mul_pos hDpos hy
  have hrho5 : ContDiffOn ℝ 5 (sec7_ra_rhoFun P.X (a : ℝ)) (Set.Ioi 0) :=
    sec7_ra_rhoFun_contDiffOn_Ioi (X := P.X) (a := (a : ℝ)) haR
  have hrhoi : ContDiffOn ℝ i (sec7_ra_rhoFun P.X (a : ℝ)) (Set.Ioi 0) :=
    hrho5.of_le (by exact_mod_cast hi)
  have hscale :=
    iteratedDerivWithin_comp_const_smul (x := u) (s := Set.Ioi (0 : ℝ))
      (f := sec7_ra_rhoFun P.X (a : ℝ)) (n := i)
      hu isOpen_Ioi.uniqueDiffOn hrhoi S.D hmaps
  have hwithin :
      iteratedDerivWithin i (sec7_ra_rhoFun P.X (a : ℝ)) (Set.Ioi 0) (S.D * u) =
        iteratedDeriv i (sec7_ra_rhoFun P.X (a : ℝ)) (S.D * u) :=
    (iteratedDerivWithin_of_isOpen (𝕜 := ℝ) (n := i)
      (f := sec7_ra_rhoFun P.X (a : ℝ)) isOpen_Ioi) (hmaps hu)
  have htower :
      |iteratedDeriv i (sec7_ra_rhoFun P.X (a : ℝ)) (S.D * u)|
        ≤ sec7_ra_rhoScale i * P.X * (a : ℝ) ^ 3 * (S.D * u) ^ ((-5 : ℝ) - i) := by
    simpa [sec7_ra_rhoFun] using
      sec7_ra_rho_tower (X := P.X) (a := (a : ℝ)) (d := S.D * u)
        (d_lo := S.D / 20) hi P.X_pos haR (by positivity)
        (by simpa [hSDu, d] using hd_lo)
        (by simpa [hSDu, d] using hd_ge_a)
  have hcancel :
      S.D ^ i * (S.D * u) ^ ((-5 : ℝ) - i) ≤ 20 ^ (5 + i) / S.D ^ 5 := by
    simpa [hSDu, d] using
      sec7_ra_rpow_neg_cancel_bound (D := S.D) (d := d) (i := i) hDpos
        (by simpa [d] using hd_lo)
  have hmain :
      S.D ^ i * |iteratedDeriv i (sec7_ra_rhoFun P.X (a : ℝ)) (S.D * u)|
        ≤ (10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5) := by
    have hleft_nonneg : 0 ≤ S.D ^ i := by positivity
    have hmul := mul_le_mul_of_nonneg_left htower hleft_nonneg
    have hpow_nonneg : 0 ≤ (S.D * u) ^ ((-5 : ℝ) - i) :=
      (Real.rpow_pos_of_pos (hmaps hu) _).le
    have hscale_nonneg : 0 ≤ P.X * (a : ℝ) ^ 3 :=
      mul_nonneg P.X_pos.le (pow_nonneg haR.le 3)
    have hbound_pow :
        S.D ^ i * (sec7_ra_rhoScale i * P.X * (a : ℝ) ^ 3 *
            (S.D * u) ^ ((-5 : ℝ) - i))
          ≤ sec7_ra_rhoScale i * 20 ^ (5 + i) *
              (P.X * (a : ℝ) ^ 3 / S.D ^ 5) := by
      have hconst_nonneg : 0 ≤ sec7_ra_rhoScale i := by
        interval_cases i <;> norm_num [sec7_ra_rhoScale]
      calc
        S.D ^ i * (sec7_ra_rhoScale i * P.X * (a : ℝ) ^ 3 *
            (S.D * u) ^ ((-5 : ℝ) - i))
            = (sec7_ra_rhoScale i * (P.X * (a : ℝ) ^ 3)) *
                (S.D ^ i * (S.D * u) ^ ((-5 : ℝ) - i)) := by ring
        _ ≤ (sec7_ra_rhoScale i * (P.X * (a : ℝ) ^ 3)) *
              (20 ^ (5 + i) / S.D ^ 5) := by
              exact mul_le_mul_of_nonneg_left hcancel (mul_nonneg hconst_nonneg hscale_nonneg)
        _ = sec7_ra_rhoScale i * 20 ^ (5 + i) *
              (P.X * (a : ℝ) ^ 3 / S.D ^ 5) := by ring
    have hconst := sec7_ra_rho_rescale_const_bound hi
    have hscalea_nonneg : 0 ≤ P.X * (a : ℝ) ^ 3 / S.D ^ 5 := by positivity
    calc
      S.D ^ i * |iteratedDeriv i (sec7_ra_rhoFun P.X (a : ℝ)) (S.D * u)|
          ≤ S.D ^ i * (sec7_ra_rhoScale i * P.X * (a : ℝ) ^ 3 *
              (S.D * u) ^ ((-5 : ℝ) - i)) := hmul
      _ ≤ sec7_ra_rhoScale i * 20 ^ (5 + i) *
              (P.X * (a : ℝ) ^ 3 / S.D ^ 5) := hbound_pow
      _ ≤ (10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5) :=
          mul_le_mul_of_nonneg_right hconst hscalea_nonneg
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs]
  rw [hscale, hwithin]
  simpa [smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hDpos.le i)] using hmain

private theorem sec7_ra_ftilde_contDiffOn_wide {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} (ha : 0 < a) (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) :
    ContDiffOn ℝ 5 (fun s => dtilde P.X s (a : ℝ) / S.D) (sec7_rWinWide S W) := by
  intro r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  exact ((sec7_dtilde_r_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ))
    P.X_pos haR hr0).div_const S.D).contDiffWithinAt

private theorem sec7_ra_gtilde_contDiffOn_Ioi {P : Globals} {S : Scale P} {a : ℤ}
    (ha : 0 < a) :
    ContDiffOn ℝ 5 (fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) (Set.Ioi 0) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  exact (sec7_ra_rhoFun_contDiffOn_Ioi (X := P.X) (a := (a : ℝ)) haR).comp
    (by fun_prop)
    (by intro u hu; exact mul_pos S.D_pos hu)

private theorem sec7_ra_ftilde_FDeriv_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) {i : ℕ} (hi₁ : 1 ≤ i) (hi₅ : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i (fun s => dtilde P.X s (a : ℝ) / S.D)
        (sec7_rWinWide S W) r‖ ≤ ((10 ^ 10 : ℝ) / S.R) ^ i := by
  have hDpos : 0 < S.D := S.D_pos
  have hRpos : 0 < S.R := sec7_R_pos S
  have hopen : IsOpen (sec7_rWinWide S W) := by
    simpa [sec7_rWinWide] using (isOpen_Ioo : IsOpen (Set.Ioo
      (S.R / 144 - 6 * (W + W ^ 2 + W ^ 4))
      (40 * S.R + 6 * (W + W ^ 2 + W ^ 4))))
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  rw [(iteratedDerivWithin_of_isOpen (𝕜 := ℝ) (n := i)
    (f := fun s => dtilde P.X s (a : ℝ) / S.D) hopen) hr]
  rw [Real.norm_eq_abs, iteratedDeriv_div_const, abs_div, abs_of_pos hDpos]
  interval_cases i
  · have hdt := sec7_ra_dtilde_wide_d1 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 1 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt1 * (S.D / S.R)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 10 : ℝ) / S.R) ^ 1 := by
            norm_num [sec7_ra_Cdt1]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
  · have hdt := sec7_ra_dtilde_wide_d2 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 2 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt2 * (S.D / S.R ^ 2)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 10 : ℝ) / S.R) ^ 2 := by
            norm_num [sec7_ra_Cdt2]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d3 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 3 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt3 * (S.D / S.R ^ 3)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 10 : ℝ) / S.R) ^ 3 := by
            norm_num [sec7_ra_Cdt3]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d4 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 4 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt4 * (S.D / S.R ^ 4)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 10 : ℝ) / S.R) ^ 4 := by
            norm_num [sec7_ra_Cdt4]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d5 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 5 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt5 * (S.D / S.R ^ 5)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 10 : ℝ) / S.R) ^ 5 := by
            norm_num [sec7_ra_Cdt5]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring

private theorem sec7_ra_residual_scale_base {P : Globals} (S : Scale P) :
    P.X * S.A ^ 3 / S.D ^ 5 = S.T₂ * (S.Ω / P.H) ^ 2 := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.A Scale.D Scale.T₂ Scale.F
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_ra_residual_scale_le {P : Globals} {S : Scale P} {a : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 2 * S.A) :
    P.X * a ^ 3 / S.D ^ 5 ≤ 8 * (S.T₂ * (S.Ω / P.H) ^ 2) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha3 : a ^ 3 ≤ (2 * S.A) ^ 3 := pow_le_pow_left₀ ha0.le ha_hi 3
  have hbase : P.X * a ^ 3 / S.D ^ 5 ≤ P.X * ((2 * S.A) ^ 3) / S.D ^ 5 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha3 P.X_pos.le)
      (by positivity)
  calc
    P.X * a ^ 3 / S.D ^ 5 ≤ P.X * ((2 * S.A) ^ 3) / S.D ^ 5 := hbase
    _ = 8 * (P.X * S.A ^ 3 / S.D ^ 5) := by ring
    _ = 8 * (S.T₂ * (S.Ω / P.H) ^ 2) := by rw [sec7_ra_residual_scale_base S]

private theorem sec7_ra_e₂D_comp_scale_absorb {P : Globals} {S : Scale P} {a : ℝ} {m : ℕ}
    (hm : m ≤ 5) (ha0 : 0 < a) (ha_hi : a ≤ 2 * S.A) :
    (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * a ^ 3 / S.D ^ 5)) *
        (((10 ^ 10 : ℝ) / S.R) ^ m)
      ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by
  have hRpos : 0 < S.R := sec7_R_pos S
  have hscale := sec7_ra_residual_scale_le (P := P) (S := S) (a := a) ha0 ha_hi
  have hscale_nonneg : 0 ≤ S.T₂ * (S.Ω / P.H) ^ 2 :=
    mul_nonneg (sec7_T₂_pos S).le (sq_nonneg _)
  calc
    (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * a ^ 3 / S.D ^ 5)) *
        (((10 ^ 10 : ℝ) / S.R) ^ m)
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) *
            (8 * (S.T₂ * (S.Ω / P.H) ^ 2))) *
              (((10 ^ 10 : ℝ) / S.R) ^ m) := by
          gcongr
    _ = ((m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 10 : ℝ) ^ m) *
          (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by
          rw [div_pow]
          field_simp [ne_of_gt hRpos]
          rw [div_pow]
          field_simp [ne_of_gt hRpos]
    _ ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by
          have hconst :
              (m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 10 : ℝ) ^ m
                ≤ (10 ^ 80 : ℝ) := by
            interval_cases m <;> norm_num
          have hB : 0 ≤ (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 :=
            mul_nonneg
              (div_nonneg (sec7_T₂_pos S).le (pow_nonneg hRpos.le m))
              (sq_nonneg _)
          calc
            ((m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 10 : ℝ) ^ m) *
                (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2
                = ((m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 10 : ℝ) ^ m) *
                    ((S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2) := by ring
            _ ≤ (10 ^ 80 : ℝ) * ((S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2) :=
                mul_le_mul_of_nonneg_right hconst hB
            _ = (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by ring

/-- **STUB (N24-PHASE/ra-expansion, f₂ core).** The §3 next-order residual tower for `f₂`:
`|ra_e₂D^{(m)}| ≤ sec7_cExpIn·(T₂/Rᵐ)·sec7_relErr` on the wide window, `m ≤ 5`.
Native progress below the stub has established the pointwise bridge
`residual₂(r) = ρ (dtilde P.X r a)` and the wide-window image
`D/20 ≤ dtilde`, `a ≤ dtilde`, `dtilde ≤ 40D`.  The remaining closure is the within/open
composition estimate for the `ρ ∘ dtilde` tower on the full `sec7_rWinWide` aperture, followed
by the `(Ω/H)^2` scale absorption through `sec7_phase_ra_e₂D_budget_absorb`. -/
theorem sec7_ra_e₂D_core (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (_hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) :
    ∀ j, sec7_jBand P S j → ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
      |sec7_phase_ra_e₂D P S a j m r| ≤
        sec7_cExpIn * (S.T₂ / S.R ^ m) * sec7_relErr P S := by
  intro j _hj m hm r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hwideOpen : IsOpen (sec7_rWinWide S W) := by
    simpa [sec7_rWinWide] using (isOpen_Ioo : IsOpen (Set.Ioo
      (S.R / 144 - 6 * (W + W ^ 2 + W ^ 4))
      (40 * S.R + 6 * (W + W ^ 2 + W ^ 4))))
  have htOpen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hftilde_cd :
      ContDiffOn ℝ 5 (fun s => dtilde P.X s (a : ℝ) / S.D) (sec7_rWinWide S W) :=
    sec7_ra_ftilde_contDiffOn_wide (P := P) (S := S) (W := W) (a := a)
      ha Env hW hsd
  have hgtilde_cd :
      ContDiffOn ℝ 5 (fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) (Set.Ioi 0) :=
    sec7_ra_gtilde_contDiffOn_Ioi (P := P) (S := S) (a := a) ha
  have hmaps : Set.MapsTo (fun s => dtilde P.X s (a : ℝ) / S.D)
      (sec7_rWinWide S W) (Set.Ioi 0) := by
    intro x hx
    have hDpos : 0 < S.D := S.D_pos
    obtain ⟨hd_lo, _hd_ge, _hd_hi⟩ :=
      sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := x)
        ha hAD ha_lo ha_hi Env hW hsd hx
    exact div_pos (lt_of_lt_of_le (by positivity : 0 < S.D / 20) hd_lo) hDpos
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i
          (fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) (Set.Ioi 0)
          ((fun s => dtilde P.X s (a : ℝ) / S.D) r)‖
        ≤ (10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5) := by
    intro i hi
    exact sec7_ra_rho_rescaled_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr (le_trans hi hm)
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i (fun s => dtilde P.X s (a : ℝ) / S.D)
          (sec7_rWinWide S W) r‖ ≤ (((10 ^ 10 : ℝ) / S.R) ^ i) := by
    intro i hi₁ hi
    exact sec7_ra_ftilde_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr hi₁ (le_trans hi hm)
  have hcomp :
      ‖iteratedFDerivWithin ℝ m
          ((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))
          (sec7_rWinWide S W) r‖
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
            (((10 ^ 10 : ℝ) / S.R) ^ m) :=
    norm_iteratedFDerivWithin_comp_le hgtilde_cd hftilde_cd
      (by exact_mod_cast hm) htOpen.uniqueDiffOn hwideOpen.uniqueDiffOn hmaps hr hC hD
  have hcomp_deriv :
      |iteratedDeriv m
          (((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r|
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
            (((10 ^ 10 : ℝ) / S.R) ^ m) := by
    have hwithin :
        iteratedFDerivWithin ℝ m
          (((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D)))
          (sec7_rWinWide S W) r =
        iteratedFDeriv ℝ m
          (((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := m)
        (f := ((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
          (fun s => dtilde P.X s (a : ℝ) / S.D))) hwideOpen) hr
    rw [hwithin, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hcomp
    simpa [Real.norm_eq_abs] using hcomp
  have hres_eq : (fun t =>
      sec7_phase_f2D P S a 0 t
        - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4))
        =ᶠ[𝓝 r]
      (((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
        (fun s => dtilde P.X s (a : ℝ) / S.D))) := by
    filter_upwards [hwideOpen.mem_nhds hr] with t ht
    have ht0 : 0 < t := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd t ht
    have hbridge := sec7_ra_e₂D_residual_bridge_point (P := P) (S := S)
      (a := a) (j := j) (r := t) ha ht0
    have hDpos : 0 < S.D := S.D_pos
    simpa [Function.comp_def, sec7_ra_rhoFun, mul_div_cancel₀, hDpos.ne'] using hbridge
  have hres_deriv :
      iteratedDeriv m
        (fun t =>
          sec7_phase_f2D P S a 0 t
            - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)) r
      =
      iteratedDeriv m
        (((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
          (fun s => dtilde P.X s (a : ℝ) / S.D))) r :=
    Filter.EventuallyEq.iteratedDeriv_eq m hres_eq
  have hnative :
      |sec7_phase_ra_e₂D P S a j m r|
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
            (((10 ^ 10 : ℝ) / S.R) ^ m) := by
    simpa [sec7_phase_ra_e₂D, hres_deriv] using hcomp_deriv
  have hscale :
      (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
          (((10 ^ 10 : ℝ) / S.R) ^ m)
        ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 :=
    sec7_ra_e₂D_comp_scale_absorb (P := P) (S := S) (a := (a : ℝ)) (m := m)
      hm haR ha_hi
  exact le_trans hnative (le_trans hscale
    (sec7_phase_ra_e₂D_budget_absorb (P := P) (S := S) (W := W)
      Env hW hsd hbud hg0 hu0 hX24 m))

/-- Concrete phase bundle assembled from the definitions above.

The analytic fields that require substantial scale or §3 expansion bookkeeping are left as
localized stubs in this constructor file; no upstream file is modified. -/
noncomputable def sec7_phase_concrete (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (_hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) :
    Sec7Phase P S W a where
  ftil := sec7_phase_ftil P S a
  dBreve := sec7_phase_dBreve P a
  dBreve' := sec7_phase_dBreve' P a
  dBreve'' := sec7_phase_dBreve'' P a
  dBreve_hasDeriv := by
    intro t ht
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have himg :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi) ht
    have hd0 : 0 < dBreve P.X (a : ℝ) t := dBreve_pos
    have h :=
      dBreve_hasDerivAt_Ffun (X := P.X) (a := (a : ℝ))
        (d := dBreve P.X (a : ℝ) t) P.X_pos haR hd0
    simpa [sec7_phase_dBreve, sec7_phase_dBreve', himg.1] using h
  dBreve'_hasDeriv := by
    intro t ht
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have himg :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi) ht
    have hd0 : 0 < dBreve P.X (a : ℝ) t := dBreve_pos
    have h :=
      dBreve_deriv1_hasDerivAt_Ffun (X := P.X) (a := (a : ℝ))
        (d := dBreve P.X (a : ℝ) t) P.X_pos haR hd0
    simpa [sec7_phase_dBreve', sec7_phase_dBreve'', himg.1] using h
  Fd'_lo := by
    intro t ht
    have h :=
      dBreve_sec7_tWin_scale (P := P) (S := S) (a := (a : ℝ)) (t := t)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi) ht
    simpa [sec7_phase_dBreve'] using h.1.1
  Fd'_hi := by
    intro t ht
    have h :=
      dBreve_sec7_tWin_scale (P := P) (S := S) (a := (a : ℝ)) (t := t)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi) ht
    simpa [sec7_phase_dBreve'] using h.1.2
  F2d''_lo := by
    intro t ht
    have h :=
      dBreve_sec7_tWin_scale (P := P) (S := S) (a := (a : ℝ)) (t := t)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi) ht
    simpa [sec7_phase_dBreve''] using h.2.1
  F2d''_hi := by
    intro t ht
    have h :=
      dBreve_sec7_tWin_scale (P := P) (S := S) (a := (a : ℝ)) (t := t)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi) ht
    simpa [sec7_phase_dBreve''] using h.2.2
  f1D := sec7_phase_f1D P S a
  f2D := sec7_phase_f2D P S a
  f3D := sec7_phase_f3D P S a
  f1D_zero := by
    intro j r
    simp [sec7_phase_f1D, sec7_phase_dBreve', sec7_phase_ftil]
  f2D_zero := by
    funext r
    simp [sec7_phase_f2D, sec7_phase_ftil]
  f3D_zero := by
    intro j r
    simp [sec7_phase_f3D, sec7_phase_dBreve, sec7_phase_ftil]
  f1D_hasDeriv := by
    intro j hj m hm r hr
    have hcd : ContDiffAt ℝ 4
        (fun x => -sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ))) r :=
      sec7_phase_f1_base_contDiffAt4 (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha hAD _hG1 (sec7_phase_a_lo_wide ha_lo)
        (sec7_phase_a_hi_wide ha_hi) Env hW c₀ Cu hsd hj hr
    simpa [sec7_phase_f1D] using
      sec7_hasDerivAt_iteratedDeriv_of_contDiffAt
        (g := fun x => -sec7_phase_dBreve' P a (sec7_phase_ftil P S a x + (j : ℝ)))
        (r := r) (m := m) hcd hm
  f2D_hasDeriv := by
    intro m hm r hr
    have hr0 : 0 < r := sec7_phase_rWin_pos Env hW c₀ Cu hsd r hr
    have hcd : ContDiffAt ℝ 4 (sec7_phase_ftil P S a) r :=
      sec7_phase_ftil_contDiffAt4 (P := P) (S := S) (a := a) ha hr0
    simpa [sec7_phase_f2D] using
      sec7_hasDerivAt_iteratedDeriv_of_contDiffAt (g := sec7_phase_ftil P S a)
        (r := r) (m := m) hcd hm
  f3D_hasDeriv := by
    intro j hj m hm r hr
    have hcd : ContDiffAt ℝ 4
        (fun x => sec7_phase_dBreve P a (sec7_phase_ftil P S a x + (j : ℝ))) r :=
      sec7_phase_f3_base_contDiffAt4 (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha hAD _hG1 (sec7_phase_a_lo_wide ha_lo)
        (sec7_phase_a_hi_wide ha_hi) Env hW c₀ Cu hsd hj hr
    simpa [sec7_phase_f3D] using
      sec7_hasDerivAt_iteratedDeriv_of_contDiffAt
        (g := fun x => sec7_phase_dBreve P a (sec7_phase_ftil P S a x + (j : ℝ)))
        (r := r) (m := m) hcd hm
  f1D_lo := by
    -- TODO(N24-PHASE/f1-scale): prove `f₁^{(m)} ≍ T₁/R^m`.
    sorry
  f1D_hi := by
    -- TODO(N24-PHASE/f1-scale): prove `f₁^{(m)} ≍ T₁/R^m`.
    sorry
  f2D_lo := by
    -- TODO(N24-PHASE/f2-scale): prove `f₂^{(m)} ≍ T₂/R^m`.
    sorry
  f2D_hi := by
    -- TODO(N24-PHASE/f2-scale): prove `f₂^{(m)} ≍ T₂/R^m`.
    sorry
  f3D_lo := by
    -- TODO(N24-PHASE/f3-scale): prove `f₃^{(m)} ≍ T₃/R^m`.
    sorry
  f3D_hi := by
    -- TODO(N24-PHASE/f3-scale): prove `f₃^{(m)} ≍ T₃/R^m`.
    sorry
  shift_mem := by
    exact sec7_phase_shift_mem P S W a ha hAD _hG1 (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) Env hW c₀ Cu hsd
  ra_c₁ := sec7_phase_ra_c₁ P S a
  ra_c₂ := sec7_phase_ra_c₂ P S a
  ra_c₁_lo := by
    intro j hj
    exact sec7_phase_ra_c₁_window_lo (P := P) (S := S) (a := a) (j := j) ha_lo
  ra_c₁_hi := by
    intro j hj
    exact sec7_phase_ra_c₁_window_hi (P := P) (S := S) (a := a) (j := j) ha_lo ha_hi
  ra_c₂_lo := by
    intro j hj
    exact sec7_phase_ra_c₂_window_lo (P := P) (S := S) (a := a) (j := j) ha_lo ha_hi
  ra_c₂_hi := by
    intro j hj
    exact sec7_phase_ra_c₂_window_hi (P := P) (S := S) (a := a) (j := j) ha_lo
  ra_e₁D := sec7_phase_ra_e₁D P S a
  ra_e₂D := sec7_phase_ra_e₂D P S a
  ra_e₃D := sec7_phase_ra_e₃D P S a
  ra_e₁D_zero := by
    intro j hj t
    simp [sec7_phase_ra_e₁D, sec7_phase_ra_c₁, iteratedDeriv_zero]
  ra_e₂D_zero := by
    intro j hj t
    simp [sec7_phase_ra_e₂D, sec7_phase_ra_c₂, iteratedDeriv_zero]
  ra_e₃D_zero := by
    intro j hj t
    simp [sec7_phase_ra_e₃D, sec7_phase_ra_c₁, sec7_phase_ra_c₂, iteratedDeriv_zero]
  ra_e₁D_deriv := by
    intro j hj m hm r hr
    have hcd : ContDiffAt ℝ 5
        (fun t => sec7_phase_f1D P S a j 0 t
          - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ))) r :=
      sec7_phase_ra_e₁_base_contDiffAt5 (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha hAD _hG1 (sec7_phase_a_lo_wide ha_lo)
        (sec7_phase_a_hi_wide ha_hi) Env hW c₀ Cu hsd hj hr
    simpa [sec7_phase_ra_e₁D] using
      sec7_hasDerivAt_iteratedDeriv_of_contDiffAt5
        (g := fun t => sec7_phase_f1D P S a j 0 t
          - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ)))
        (r := r) (m := m) hcd hm
  ra_e₂D_deriv := by
    intro j hj m hm r hr
    have hcd : ContDiffAt ℝ 5
        (fun t => sec7_phase_f2D P S a 0 t
          - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)) r :=
      sec7_phase_ra_e₂_base_contDiffAt5 (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha Env hW c₀ Cu hsd hr
    simpa [sec7_phase_ra_e₂D] using
      sec7_hasDerivAt_iteratedDeriv_of_contDiffAt5
        (g := fun t => sec7_phase_f2D P S a 0 t
          - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4))
        (r := r) (m := m) hcd hm
  ra_e₃D_deriv := by
    intro j hj m hm r hr
    have hcd : ContDiffAt ℝ 5
        (fun t => sec7_phase_f3D P S a j 0 t
          - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
              * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4)) r :=
      sec7_phase_ra_e₃_base_contDiffAt5 (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha hAD _hG1 (sec7_phase_a_lo_wide ha_lo)
        (sec7_phase_a_hi_wide ha_hi) Env hW c₀ Cu hsd hj hr
    simpa [sec7_phase_ra_e₃D] using
      sec7_hasDerivAt_iteratedDeriv_of_contDiffAt5
        (g := fun t => sec7_phase_f3D P S a j 0 t
          - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
              * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4))
        (r := r) (m := m) hcd hm
  ra_e₁D_bound := by
    -- TODO(N24-PHASE/ra-expansion): §3 graded expansion bound for `f₁`.
    sorry
  ra_e₂D_bound := by
    intro j hj m hm r hr
    exact sec7_ra_e₂D_core P S W a ha hAD _hG1 ha_lo ha_hi Env hW c₀ Cu hsd
      hbud hg0 hu0 hX24 j hj m hm r hr
  ra_e₃D_bound := by
    -- TODO(N24-PHASE/ra-expansion): §3 graded expansion bound for `f₃`.
    sorry
  phiContDiff := by
    -- TODO(N24-PHASE/critical): global `C²` regularity of the §7 branch phase.
    sorry
  phiFewCritical := by
    -- TODO(N24-PHASE/critical): finite critical-zero bound for the §7 branch phase.
    sorry

/-- Rounded inverse margin for the concrete `dBreve`.

This is the exact auxiliary fact needed by the public constructor.  The intended proof is:
`|round x - x| ≤ 1/2`, the inverse MVT using `|dBreve'| ≍ D/F`, and the scale identity
`D/F = Δ²/(H² G A)` (up to the ledger slack `sec7_cdMar`). -/
private theorem sec7_phase_round_inverse_margin (P : Globals) (S : Scale P) (a : ℤ)
    (_ha : 0 < a) (_hAD : 10 * S.A ≤ S.D) (_hG1 : 1 ≤ P.G)
    (_ha_lo : S.A ≤ (a : ℝ)) (_ha_hi : (a : ℝ) ≤ 2 * S.A)
    {d f : ℤ} (_hdD : S.D ≤ (d : ℝ)) (_hd2D : (d : ℝ) ≤ 2 * S.D)
    (hf : f = round (Ffun P.X (a : ℝ) (d : ℝ))) :
    |(d : ℝ) - sec7_phase_dBreve P a (f : ℝ)| ≤
      sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A)) := by
  -- TODO(N24-PHASE/margin): round step + inverse MVT on the image interval.
  sorry

/-- Public constructor matching the private `BoxSum.sec7_phase_build` input/output shape. -/
theorem sec7_phase_construct (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) (ha : 0 < a)
    (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ)) :
    ∃ Ph : Sec7Phase P S W a,
      (∀ {r : ℝ}, (1/72) * S.R ≤ r → r ≤ 16 * S.R →
        Ph.ftil r = Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ∧
      (∀ {d f : ℤ}, S.D ≤ (d : ℝ) → (d : ℝ) ≤ 2 * S.D →
        f = round (Ffun P.X (a : ℝ) (d : ℝ)) →
        |(d : ℝ) - Ph.dBreve (f : ℝ)| ≤
          sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A))) := by
  refine ⟨sec7_phase_concrete P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
    hbud hg0 hu0 hX24, ?_, ?_⟩
  · intro r hrlo hrhi
    rfl
  · intro d f hdD hd2D hf
    exact sec7_phase_round_inverse_margin P S a ha hAD hG1 ha_lo ha_hi hdD hd2D hf

end Squarefree
