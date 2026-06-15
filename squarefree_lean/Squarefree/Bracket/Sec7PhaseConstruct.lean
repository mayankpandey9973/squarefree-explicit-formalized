import Squarefree.Bracket.Sec7FInverse
import Squarefree.Bracket.Sec7ErrAux
import Squarefree.Bracket.Sec7MonExpData
import Squarefree.Lower.Sec7DBreveScale
import Squarefree.Lower.DefectDeriv5
import Squarefree.Lower.Sec7DtildeWide
import Squarefree.Lower.Sec7RaB1Tower
import Squarefree.Lower.Sec7RaCompose
import Squarefree.Opt.OnStripAux
import Squarefree.Opt.StripRegimePack

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

private theorem sec7_iteratedDeriv_comp_const_mul_at5 {f : ℝ → ℝ} {x c : ℝ} {n : ℕ}
    (hn : n ≤ 5) (hf : ContDiffAt ℝ 5 f (c * x)) :
    iteratedDeriv n (fun y : ℝ => f (c * y)) x =
      c ^ n * iteratedDeriv n f (c * x) := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      have hnlt : n < 5 := Nat.lt_of_succ_le hn
      have hnle : n ≤ 5 := le_trans (Nat.le_succ n) hn
      let g : ℝ → ℝ := fun y => f (c * y)
      have hlin_cd : ContDiffAt ℝ 5 (fun y : ℝ => c * y) x :=
        contDiffAt_const.mul contDiffAt_id
      have hg_cd : ContDiffAt ℝ 5 g x := by
        exact hf.comp x hlin_cd
      have hnear_f : ∀ᶠ z in 𝓝 (c * x), ContDiffAt ℝ 5 f z :=
        hf.eventually (by simp)
      have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 5 f (c * y) :=
        hlin_cd.continuousAt.tendsto.eventually hnear_f
      have hev : (fun y : ℝ => iteratedDeriv n g y) =ᶠ[𝓝 x]
          (fun y : ℝ => c ^ n * iteratedDeriv n f (c * y)) := by
        filter_upwards [hnear] with y hy
        exact ih hnle hy
      have hder_g :=
        sec7_hasDerivAt_iteratedDeriv_of_contDiffAt5 (g := g) (r := x) (m := n)
          hg_cd hnlt
      have hder_f :=
        sec7_hasDerivAt_iteratedDeriv_of_contDiffAt5 (g := f) (r := c * x) (m := n)
          hf hnlt
      have hlin_der : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have hcomp_der :
          HasDerivAt (fun y : ℝ => iteratedDeriv n f (c * y))
            (iteratedDeriv (n + 1) f (c * x) * c) x := by
        simpa [Function.comp_def, mul_comm] using hder_f.comp x hlin_der
      calc
        iteratedDeriv (n + 1) g x
            = deriv (iteratedDeriv n g) x := by rw [iteratedDeriv_succ]
        _ = deriv (fun y : ℝ => c ^ n * iteratedDeriv n f (c * y)) x :=
            Filter.EventuallyEq.deriv_eq hev
        _ = c ^ n * deriv (fun y : ℝ => iteratedDeriv n f (c * y)) x := by
            rw [deriv_const_mul_field]
        _ = c ^ n * (iteratedDeriv (n + 1) f (c * x) * c) := by
            rw [hcomp_der.deriv]
        _ = c ^ (n + 1) * iteratedDeriv (n + 1) f (c * x) := by ring

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

private theorem sec7_Ffun_strictAntiOn_pos {X a : ℝ} (hX : 0 < X) (ha : 0 < a) :
    StrictAntiOn (fun d => Ffun X a d) (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro d hd
    have hd0 : 0 < d := by simpa using hd
    exact (Ffun_contDiffAt4 (X := X) (a := a) (d := d)
      (ne_of_gt hd0) (by positivity)).continuousAt.continuousWithinAt
  · intro d hd
    have hd0 : 0 < d := by simpa using hd
    rw [Ffun_deriv_d X a d (ne_of_gt hd0) (by positivity)]
    simpa [sec7_F1loc] using sec7_Ffun_deriv_neg hX ha hd0

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

private theorem sec7_phase_powMon_iteratedDeriv_eq {P : Globals} {S : Scale P}
    {c α r : ℝ} (m : ℕ) (hr : 0 < r) :
    iteratedDeriv m (fun t : ℝ => c * (t / S.R) ^ α) r =
      sec7_powMonD S.R c α m r := by
  have hR : 0 < S.R := sec7_R_pos S
  have hchain : ∀ k < m, ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (sec7_powMonD S.R c α k) (sec7_powMonD S.R c α (k + 1) x) x := by
    intro k _hk x hx
    exact sec7_powMonD_hasDerivAt hR c α k hx
  have h :=
    sec7_iteratedDeriv_eq_of_chain (F := sec7_powMonD S.R c α)
      (s := Set.Ioi (0 : ℝ)) isOpen_Ioi (n := m) hchain m le_rfl r hr
  rw [sec7_powMonD_zero] at h
  change iteratedDeriv m (sec7_powMon S.R c α) r = sec7_powMonD S.R c α m r
  exact h

private theorem sec7_phase_rpow_quarter_le {x b : ℝ} {q : ℕ}
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ^ q ≤ b ^ 4) :
    x ^ ((q : ℝ) / 4) ≤ b := by
  have h1 : x ^ ((q : ℝ) / 4) = (x ^ q) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast x q, ← Real.rpow_mul hx]
    ring_nf
  have h2 : (x ^ q) ^ ((1 : ℝ) / 4) ≤ (b ^ 4) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h3 : (b ^ 4) ^ ((1 : ℝ) / 4) = b := by
    rw [← Real.rpow_natCast b 4, ← Real.rpow_mul hb]
    norm_num
  rw [h1]
  rwa [h3] at h2

private theorem sec7_phase_le_rpow_quarter {x b : ℝ} {q : ℕ}
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : b ^ 4 ≤ x ^ q) :
    b ≤ x ^ ((q : ℝ) / 4) := by
  have h1 : b = (b ^ 4) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast b 4, ← Real.rpow_mul hb]
    norm_num
  have h2 : (b ^ 4) ^ ((1 : ℝ) / 4) ≤ (x ^ q) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h3 : (x ^ q) ^ ((1 : ℝ) / 4) = x ^ ((q : ℝ) / 4) := by
    rw [← Real.rpow_natCast x q, ← Real.rpow_mul hx]
    ring_nf
  rw [h1]
  exact h2.trans_eq h3

private theorem sec7_phase_rpow_neg_quarter_lower {x b : ℝ} {q : ℕ}
    (hx : 0 < x) (hb : 0 < b) (h : x ^ ((q : ℝ) / 4) ≤ b) :
    1 / b ≤ x ^ (-((q : ℝ) / 4)) := by
  have hxq : 0 < x ^ ((q : ℝ) / 4) := Real.rpow_pos_of_pos hx _
  rw [Real.rpow_neg hx.le]
  simpa [one_div] using (one_div_le_one_div hb hxq).2 h

private theorem sec7_phase_rpow_neg_quarter_upper {x b : ℝ} {q : ℕ}
    (hx : 0 < x) (hb : 0 < b) (h : b ≤ x ^ ((q : ℝ) / 4)) :
    x ^ (-((q : ℝ) / 4)) ≤ 1 / b := by
  have hxq : 0 < x ^ ((q : ℝ) / 4) := Real.rpow_pos_of_pos hx _
  rw [Real.rpow_neg hx.le]
  simpa [one_div] using (one_div_le_one_div hxq hb).2 h

private theorem sec7_phase_f2D_rpow_factor_bounds {P : Globals} {S : Scale P}
    {W r : ℝ} {m : ℕ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hm : m ≤ 3) (hr : r ∈ sec7_rWin S W) :
    1 / (10 : ℝ) ^ 5 ≤ (r / S.R) ^ (((3 : ℝ) / 4) - m) ∧
      (r / S.R) ^ (((3 : ℝ) / 4) - m) ≤ (10 : ℝ) ^ 6 := by
  have hR : 0 < S.R := sec7_R_pos S
  have hcore := sec7_phase_rWin_core Env hW c₀ Cu hsd hr
  set y : ℝ := r / S.R with hydef
  have hypos : 0 < y := by
    rw [hydef]
    exact div_pos (sec7_phase_rWin_pos Env hW c₀ Cu hsd r hr) hR
  have hy0 : 0 ≤ y := hypos.le
  have hylo : (1 / 200 : ℝ) ≤ y := by
    rw [hydef, le_div_iff₀ hR]
    nlinarith [hcore.1]
  have hyhi : y ≤ (41 : ℝ) := by
    rw [hydef, div_le_iff₀ hR]
    nlinarith [hcore.2]
  interval_cases m
  · have hpowlo : (1 / (10 : ℝ) ^ 5) ^ 4 ≤ y ^ 3 := by
      have hbase : (1 / 200 : ℝ) ^ 3 ≤ y ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hylo 3
      norm_num at hbase ⊢
      exact le_trans (by norm_num) hbase
    have hlo := sec7_phase_le_rpow_quarter (x := y) (b := 1 / (10 : ℝ) ^ 5)
      (q := 3) hy0 (by positivity) hpowlo
    have hpowhi : y ^ 3 ≤ ((10 : ℝ) ^ 6) ^ 4 := by
      have hbase : y ^ 3 ≤ (41 : ℝ) ^ 3 := pow_le_pow_left₀ hy0 hyhi 3
      exact le_trans hbase (by norm_num)
    have hhi := sec7_phase_rpow_quarter_le (x := y) (b := (10 : ℝ) ^ 6)
      (q := 3) hy0 (by positivity) hpowhi
    constructor
    · simpa [one_div] using hlo
    · simpa using hhi
  · have hpowhi₀ : y ^ 1 ≤ ((10 : ℝ) ^ 5) ^ 4 := by
      have : y ≤ (41 : ℝ) := hyhi
      norm_num at this ⊢
      exact le_trans this (by norm_num)
    have hqhi := sec7_phase_rpow_quarter_le (x := y) (b := (10 : ℝ) ^ 5)
      (q := 1) hy0 (by positivity) hpowhi₀
    have hlo := sec7_phase_rpow_neg_quarter_lower (x := y) (b := (10 : ℝ) ^ 5)
      (q := 1) hypos (by positivity) hqhi
    have hpowlo₀ : (1 / (10 : ℝ) ^ 6) ^ 4 ≤ y ^ 1 := by
      have : (1 / (10 : ℝ) ^ 6) ^ 4 ≤ (1 / 200 : ℝ) := by norm_num
      exact le_trans this (by simpa using hylo)
    have hqlo := sec7_phase_le_rpow_quarter (x := y) (b := 1 / (10 : ℝ) ^ 6)
      (q := 1) hy0 (by positivity) hpowlo₀
    have hhi₀ := sec7_phase_rpow_neg_quarter_upper (x := y)
      (b := 1 / (10 : ℝ) ^ 6) (q := 1) hypos (by positivity) hqlo
    have hhi : y ^ (-((1 : ℝ) / 4)) ≤ (10 : ℝ) ^ 6 := by
      simpa using hhi₀
    constructor
    · simpa [one_div, show ((3 : ℝ) / 4 - 1) = -((1 : ℝ) / 4) by norm_num] using hlo
    · simpa [show ((3 : ℝ) / 4 - 1) = -((1 : ℝ) / 4) by norm_num] using hhi
  · have hpowhi₀ : y ^ 5 ≤ ((10 : ℝ) ^ 5) ^ 4 := by
      have hbase : y ^ 5 ≤ (41 : ℝ) ^ 5 := pow_le_pow_left₀ hy0 hyhi 5
      exact le_trans hbase (by norm_num)
    have hqhi := sec7_phase_rpow_quarter_le (x := y) (b := (10 : ℝ) ^ 5)
      (q := 5) hy0 (by positivity) hpowhi₀
    have hlo := sec7_phase_rpow_neg_quarter_lower (x := y) (b := (10 : ℝ) ^ 5)
      (q := 5) hypos (by positivity) hqhi
    have hpowlo₀ : (1 / (10 : ℝ) ^ 6) ^ 4 ≤ y ^ 5 := by
      have hbase : (1 / 200 : ℝ) ^ 5 ≤ y ^ 5 :=
        pow_le_pow_left₀ (by norm_num) hylo 5
      exact le_trans (by norm_num) hbase
    have hqlo := sec7_phase_le_rpow_quarter (x := y) (b := 1 / (10 : ℝ) ^ 6)
      (q := 5) hy0 (by positivity) hpowlo₀
    have hhi₀ := sec7_phase_rpow_neg_quarter_upper (x := y)
      (b := 1 / (10 : ℝ) ^ 6) (q := 5) hypos (by positivity) hqlo
    have hhi : y ^ (-((5 : ℝ) / 4)) ≤ (10 : ℝ) ^ 6 := by
      simpa using hhi₀
    constructor
    · simpa [one_div, show ((3 : ℝ) / 4 - 2) = -((5 : ℝ) / 4) by norm_num] using hlo
    · simpa [show ((3 : ℝ) / 4 - 2) = -((5 : ℝ) / 4) by norm_num] using hhi
  · have hpowhi₀ : y ^ 9 ≤ ((10 : ℝ) ^ 5) ^ 4 := by
      have hbase : y ^ 9 ≤ (41 : ℝ) ^ 9 := pow_le_pow_left₀ hy0 hyhi 9
      exact le_trans hbase (by norm_num)
    have hqhi := sec7_phase_rpow_quarter_le (x := y) (b := (10 : ℝ) ^ 5)
      (q := 9) hy0 (by positivity) hpowhi₀
    have hlo := sec7_phase_rpow_neg_quarter_lower (x := y) (b := (10 : ℝ) ^ 5)
      (q := 9) hypos (by positivity) hqhi
    have hpowlo₀ : (1 / (10 : ℝ) ^ 6) ^ 4 ≤ y ^ 9 := by
      have hbase : (1 / 200 : ℝ) ^ 9 ≤ y ^ 9 :=
        pow_le_pow_left₀ (by norm_num) hylo 9
      exact le_trans (by norm_num) hbase
    have hqlo := sec7_phase_le_rpow_quarter (x := y) (b := 1 / (10 : ℝ) ^ 6)
      (q := 9) hy0 (by positivity) hpowlo₀
    have hhi₀ := sec7_phase_rpow_neg_quarter_upper (x := y)
      (b := 1 / (10 : ℝ) ^ 6) (q := 9) hypos (by positivity) hqlo
    have hhi : y ^ (-((9 : ℝ) / 4)) ≤ (10 : ℝ) ^ 6 := by
      simpa using hhi₀
    constructor
    · simpa [one_div, show ((3 : ℝ) / 4 - 3) = -((9 : ℝ) / 4) by norm_num] using hlo
    · simpa [show ((3 : ℝ) / 4 - 3) = -((9 : ℝ) / 4) by norm_num] using hhi

private theorem sec7_phase_f2D_monomial_scale {P : Globals} {S : Scale P}
    {W : ℝ} {a : ℤ} {m : ℕ} {r : ℝ}
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hm : m ≤ 3) (hr : r ∈ sec7_rWin S W) :
    (1 / (10 : ℝ) ^ 8) * (S.T₂ / S.R ^ m) ≤
        |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
          ((3 : ℝ) / 4) m r| ∧
      |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
          ((3 : ℝ) / 4) m r| ≤
        (10 : ℝ) ^ 8 * (S.T₂ / S.R ^ m) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT : 0 < S.T₂ := sec7_T₂_pos S
  have hr0 : 0 < r := sec7_phase_rWin_pos Env hW c₀ Cu hsd r hr
  have hypos : 0 < r / S.R := div_pos hr0 hR
  have hfacpos :
      0 < (r / S.R) ^ (((3 : ℝ) / 4) - m) := Real.rpow_pos_of_pos hypos _
  have hB0 : 0 ≤ S.T₂ / S.R ^ m := by positivity
  have hc_lo : 1 / 16 ≤ |sec7_phase_ra_c₂ P S a 0| :=
    sec7_phase_ra_c₂_window_lo (P := P) (S := S) (a := a) (j := 0) ha_lo ha_hi
  have hc_hi : |sec7_phase_ra_c₂ P S a 0| ≤ 4 :=
    sec7_phase_ra_c₂_window_hi (P := P) (S := S) (a := a) (j := 0) ha_lo
  have haprod_lo : 1 / 16 ≤ |sec7_aprod ((3 : ℝ) / 4) m| := by
    interval_cases m <;> norm_num [sec7_aprod]
  have haprod_hi : |sec7_aprod ((3 : ℝ) / 4) m| ≤ 1 := by
    interval_cases m <;> norm_num [sec7_aprod]
  have hfac := sec7_phase_f2D_rpow_factor_bounds (P := P) (S := S)
    (W := W) (r := r) (m := m) Env hW c₀ Cu hsd hm hr
  have habs :
      |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
          ((3 : ℝ) / 4) m r| =
        |sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m| *
          (S.T₂ / S.R ^ m) * (r / S.R) ^ (((3 : ℝ) / 4) - m) := by
    unfold sec7_powMonD sec7_powMon
    rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_pos hT,
      abs_of_pos (pow_pos hR m), abs_of_pos hfacpos]
    ring
  have hcoef_lo :
      1 / (10 : ℝ) ^ 3 ≤
        |sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m| := by
    nlinarith [hc_lo, haprod_lo, abs_nonneg (sec7_phase_ra_c₂ P S a 0),
      abs_nonneg (sec7_aprod ((3 : ℝ) / 4) m)]
  have hcoef_hi :
      |sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m| ≤ 4 := by
    nlinarith [hc_hi, haprod_hi, abs_nonneg (sec7_phase_ra_c₂ P S a 0),
      abs_nonneg (sec7_aprod ((3 : ℝ) / 4) m)]
  constructor
  · have hcoefB :
        (1 / (10 : ℝ) ^ 3) * (S.T₂ / S.R ^ m) ≤
          (|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
            (S.T₂ / S.R ^ m) :=
      mul_le_mul_of_nonneg_right hcoef_lo hB0
    have hstep :
        ((|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
            (S.T₂ / S.R ^ m)) * (1 / (10 : ℝ) ^ 5) ≤
          ((|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
            (S.T₂ / S.R ^ m)) * (r / S.R) ^ (((3 : ℝ) / 4) - m) := by
      exact mul_le_mul_of_nonneg_left hfac.1 (by positivity)
    calc
      (1 / (10 : ℝ) ^ 8) * (S.T₂ / S.R ^ m)
          = ((1 / (10 : ℝ) ^ 3) * (S.T₂ / S.R ^ m)) *
              (1 / (10 : ℝ) ^ 5) := by ring
      _ ≤ ((|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
              (S.T₂ / S.R ^ m)) * (1 / (10 : ℝ) ^ 5) :=
            mul_le_mul_of_nonneg_right hcoefB (by positivity)
      _ ≤ ((|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
              (S.T₂ / S.R ^ m)) * (r / S.R) ^ (((3 : ℝ) / 4) - m) := hstep
      _ = |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
            ((3 : ℝ) / 4) m r| := by
            rw [habs]
  · have hcoefB :
        (|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
            (S.T₂ / S.R ^ m) ≤
          4 * (S.T₂ / S.R ^ m) :=
      mul_le_mul_of_nonneg_right hcoef_hi hB0
    have hstep :
        ((|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
            (S.T₂ / S.R ^ m)) *
            (r / S.R) ^ (((3 : ℝ) / 4) - m) ≤
          (4 * (S.T₂ / S.R ^ m)) * (10 : ℝ) ^ 6 := by
      exact mul_le_mul hcoefB hfac.2 (by positivity) (by positivity)
    calc
      |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
          ((3 : ℝ) / 4) m r|
          = ((|sec7_phase_ra_c₂ P S a 0| * |sec7_aprod ((3 : ℝ) / 4) m|) *
              (S.T₂ / S.R ^ m)) * (r / S.R) ^ (((3 : ℝ) / 4) - m) := by
            rw [habs]
      _ ≤ (4 * (S.T₂ / S.R ^ m)) * (10 : ℝ) ^ 6 := hstep
      _ ≤ (10 : ℝ) ^ 8 * (S.T₂ / S.R ^ m) := by
            nlinarith [hB0]

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

private theorem sec7_ra_e₁D_principal_bridge {P : Globals} {S : Scale P}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hr0 : 0 < r) :
    sec7_phase_ra_c₁ P S a j * S.T₁ * (r / S.R) ^ (-(1 : ℝ)) =
      (dtilde P.X r (a : ℝ)) ^ 2 * (dtilde P.X r (a : ℝ) + (a : ℝ)) ^ 2 /
        (6 * P.X * (a : ℝ)) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hX : 0 < P.X := P.X_pos
  have hA : 0 < S.A := by
    have hΔ : 0 < S.Δ := S.Δ_pos
    have hΩ : 0 < S.Ω := S.Ω_pos
    unfold Scale.A
    positivity
  have hR : 0 < S.R := sec7_R_pos S
  set d := dtilde P.X r (a : ℝ) with hddef
  have hd : 0 < d := by simpa [d] using dtilde_pos P.X_pos haR hr0
  have hda : 0 < d + (a : ℝ) := by linarith
  have hratio : 0 < r / S.R := div_pos hr0 hR
  have hspec0 : Rfun P.X (a : ℝ) d = r := by
    simpa [d] using dtilde_spec (X := P.X) (a := (a : ℝ)) (r := r) hX haR hr0
  have hspec : P.X * (a : ℝ) ^ 3 / (d ^ 2 * (d + (a : ℝ)) ^ 2) = r := by
    rw [← hspec0, Rfun_factor' P.X (a : ℝ) d hd.ne' hda.ne']
  have hRT : S.R * S.T₁ = S.A ^ 2 := sec7_R_mul_T₁ S
  calc
    sec7_phase_ra_c₁ P S a j * S.T₁ * (r / S.R) ^ (-(1 : ℝ))
        = (a : ℝ) ^ 2 / (6 * r) := by
          rw [sec7_phase_ra_c₁]
          rw [Real.rpow_neg hratio.le, Real.rpow_one]
          rw [show (r / S.R)⁻¹ = S.R / r by field_simp [hr0.ne', hR.ne']]
          rw [show (1 / 6) * ((a : ℝ) / S.A) ^ 2 * S.T₁ * (S.R / r)
                = (a : ℝ) ^ 2 * (S.R * S.T₁) / (6 * S.A ^ 2 * r) by ring]
          rw [hRT]
          field_simp [hA.ne', hr0.ne']
    _ = d ^ 2 * (d + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ)) := by
          rw [← hspec]
          field_simp [hX.ne', haR.ne', hd.ne', hda.ne']

private theorem sec7_ra_e₁D_residual_bridge_point {P : Globals} {S : Scale P}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hr0 : 0 < r) :
    sec7_phase_f1D P S a j 0 r
        - sec7_phase_ra_c₁ P S a j * S.T₁ * (r / S.R) ^ (-(1 : ℝ)) =
      -dBreve' P.X (a : ℝ)
          (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) + (j : ℝ))
        - (dtilde P.X r (a : ℝ)) ^ 2 *
            (dtilde P.X r (a : ℝ) + (a : ℝ)) ^ 2 /
          (6 * P.X * (a : ℝ)) := by
  have hmain := sec7_ra_e₁D_principal_bridge (P := P) (S := S)
    (a := a) (j := j) (r := r) ha hr0
  simp [sec7_phase_f1D, sec7_phase_dBreve', sec7_phase_ftil, hmain]

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

private theorem sec7_phase_T₃_four_mul_R {P : Globals} (S : Scale P) :
    S.T₃ ^ 4 * S.R = P.X * S.A ^ 3 := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  rw [Scale.T₃, Scale.R, Scale.A, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_ra_e₃D_principal_bridge {P : Globals} {S : Scale P}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hr0 : 0 < r) :
    3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
        * S.T₃ * (r / S.R) ^ (-(1 : ℝ) / 4) =
      Real.sqrt
        (dtilde P.X r (a : ℝ) * (dtilde P.X r (a : ℝ) + (a : ℝ))) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hX : 0 < P.X := P.X_pos
  have hA : 0 < S.A := by
    have := S.Δ_pos
    have := S.Ω_pos
    unfold Scale.A
    positivity
  have hR : 0 < S.R := sec7_R_pos S
  have hT : 0 < S.T₃ := sec7_T₃_pos S
  set d := dtilde P.X r (a : ℝ) with hddef
  have hd : 0 < d := by simpa [d] using dtilde_pos P.X_pos haR hr0
  have hda : 0 < d + (a : ℝ) := by linarith
  have hratio0 : 0 ≤ r / S.R := by positivity
  have hratio_pos : 0 < r / S.R := div_pos hr0 hR
  have hz0 : 0 ≤ S.A / (a : ℝ) := by positivity
  have hLnonneg :
      0 ≤ 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
          * S.T₃ * (r / S.R) ^ (-(1 : ℝ) / 4) := by
    rw [sec7_phase_ra_c₁, sec7_phase_ra_c₂]
    positivity
  have hMnonneg : 0 ≤ Real.sqrt (d * (d + (a : ℝ))) := Real.sqrt_nonneg _
  have hzpow :
      ((S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) ^ 4 =
        (S.A / (a : ℝ)) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast ((S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) 4]
    rw [← Real.rpow_mul hz0]
    norm_num
  have hupow :
      ((r / S.R) ^ (-(1 : ℝ) / 4)) ^ 4 = (r / S.R) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast ((r / S.R) ^ (-(1 : ℝ) / 4)) 4]
    rw [← Real.rpow_mul hratio0]
    norm_num
  have hMin :
      0 ≤ d * (d + (a : ℝ)) := mul_nonneg hd.le hda.le
  have hM4 :
      (Real.sqrt (d * (d + (a : ℝ)))) ^ 4 =
        d ^ 2 * (d + (a : ℝ)) ^ 2 := by
    rw [show (Real.sqrt (d * (d + (a : ℝ)))) ^ 4 =
        (Real.sqrt (d * (d + (a : ℝ))) ^ 2) ^ 2 by ring]
    rw [Real.sq_sqrt hMin]
    ring
  have hL4 :
      (3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
          * S.T₃ * (r / S.R) ^ (-(1 : ℝ) / 4)) ^ 4 =
        ((a : ℝ) ^ 3 / S.A ^ 3) * S.T₃ ^ 4 * (r / S.R) ^ (-(1 : ℝ)) := by
    have hcoef :
        (3 * ((1 / 6 : ℝ) * ((a : ℝ) / S.A) ^ 2) *
            (2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4))) ^ 4 =
          (a : ℝ) ^ 3 / S.A ^ 3 := by
      rw [show 3 * ((1 / 6 : ℝ) * ((a : ℝ) / S.A) ^ 2) *
            (2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) =
          ((a : ℝ) / S.A) ^ 2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4) by ring]
      rw [mul_pow, hzpow]
      field_simp [ne_of_gt haR, ne_of_gt hA]
    rw [sec7_phase_ra_c₁, sec7_phase_ra_c₂]
    rw [show (3 * ((1 / 6 : ℝ) * ((a : ℝ) / S.A) ^ 2) *
          (2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4)) * S.T₃ *
            (r / S.R) ^ (-(1 : ℝ) / 4)) ^ 4 =
        (3 * ((1 / 6 : ℝ) * ((a : ℝ) / S.A) ^ 2) *
          (2 * (S.A / (a : ℝ)) ^ ((5 : ℝ) / 4))) ^ 4 *
            S.T₃ ^ 4 * ((r / S.R) ^ (-(1 : ℝ) / 4)) ^ 4 by ring]
    rw [hcoef]
    rw [hupow]
  have hspec0 : Rfun P.X (a : ℝ) d = r := by
    simpa [d, hddef] using dtilde_spec P.X_pos haR hr0
  have hspec : P.X * (a : ℝ) ^ 3 / (d ^ 2 * (d + (a : ℝ)) ^ 2) = r := by
    rw [Rfun_factor' P.X (a : ℝ) d (ne_of_gt hd) (ne_of_gt hda)] at hspec0
    exact hspec0
  have hscale : S.T₃ ^ 4 * S.R = P.X * S.A ^ 3 :=
    sec7_phase_T₃_four_mul_R S
  have hfour :
      (3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
          * S.T₃ * (r / S.R) ^ (-(1 : ℝ) / 4)) ^ 4 =
        (Real.sqrt (d * (d + (a : ℝ)))) ^ 4 := by
    rw [hL4, hM4]
    rw [Real.rpow_neg hratio_pos.le, Real.rpow_one]
    rw [← hspec]
    field_simp [ne_of_gt hX, ne_of_gt haR, ne_of_gt hd, ne_of_gt hda,
      ne_of_gt hA, ne_of_gt hR]
    nlinarith [hscale]
  apply le_antisymm
  · exact sec7_phase_le_of_fourth hLnonneg hMnonneg (by rw [hfour])
  · exact sec7_phase_le_of_fourth hMnonneg hLnonneg (by rw [hfour])

private theorem sec7_ra_e₃D_residual_bridge_point {P : Globals} {S : Scale P}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hr0 : 0 < r) :
    sec7_phase_f3D P S a j 0 r
        - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
          * S.T₃ * (r / S.R) ^ (-(1 : ℝ) / 4) =
      dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) + (j : ℝ))
        - Real.sqrt
          (dtilde P.X r (a : ℝ) * (dtilde P.X r (a : ℝ) + (a : ℝ))) := by
  have hmain := sec7_ra_e₃D_principal_bridge (P := P) (S := S)
    (a := a) (j := j) (r := r) ha hr0
  simp [sec7_phase_f3D, sec7_phase_dBreve, sec7_phase_ftil, hmain]

/-- The one-variable `f₃` residual after subtracting the square-root principal term. -/
private noncomputable def sec7_raC_rho3Fun (X a j : ℝ) : ℝ → ℝ :=
  fun d => dBreve X a (Ffun X a d + j) - Real.sqrt (d * (d + a))

/-- The one-variable `f₁` residual after subtracting its leading monomial. -/
private noncomputable def sec7_ra_rho1Fun (X a j : ℝ) : ℝ → ℝ :=
  fun d => -dBreve' X a (Ffun X a d + j) -
    d ^ 2 * (d + a) ^ 2 / (6 * X * a)

/-- Normalized `d/D` target interval corresponding to the unshifted phase band
`F/500 ≤ F_a(d) ≤ 300F`. -/
private noncomputable def sec7_raC_rho3Target (P : Globals) (S : Scale P) (a : ℝ) : Set ℝ :=
  Set.Icc (dBreve P.X a (300 * S.F) / S.D) (dBreve P.X a (S.F / 500) / S.D)

/-- Physical `d` target corresponding to `sec7_ra_rho3Target`. -/
private noncomputable def sec7_ra_rho3DTarget (P : Globals) (S : Scale P) (a : ℝ) : Set ℝ :=
  Set.Icc (dBreve P.X a (300 * S.F)) (dBreve P.X a (S.F / 500))

private theorem sec7_raC_rho3Target_uniqueDiffOn {P : Globals} {S : Scale P} {a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) :
    UniqueDiffOn ℝ (sec7_ra_rho3Target P S a) := by
  have ha0 : 0 < a := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    linarith
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := 300 * S.F)
      hAD ha_lo ha_hi ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := S.F / 500)
      hAD ha_lo ha_hi ht_lo
  set q_hi : ℝ := dBreve P.X a (300 * S.F)
  set q_lo : ℝ := dBreve P.X a (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hq_order : q_hi < q_lo := by
    by_contra hnot
    have hle : q_lo ≤ q_hi := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hanti := sec7_Ffun_strictAntiOn_pos (X := P.X) (a := a) P.X_pos ha0
      have hval := hanti (by simpa using hqlo_pos) (by simpa using hqhi_pos) hlt
      change Ffun P.X a q_hi < Ffun P.X a q_lo at hval
      rw [himg_hi, himg_lo] at hval
      nlinarith
    · have heqF : 300 * S.F = S.F / 500 := by
        rw [← himg_hi, ← himg_lo]
        rw [heq]
      nlinarith [hFpos, heqF]
  have hDpos : 0 < S.D := S.D_pos
  have htarget_order :
      dBreve P.X a (300 * S.F) / S.D < dBreve P.X a (S.F / 500) / S.D := by
    simpa [q_hi, q_lo] using div_lt_div_of_pos_right hq_order hDpos
  simpa [sec7_ra_rho3Target] using uniqueDiffOn_Icc htarget_order

private theorem sec7_ra_rho3DTarget_uniqueDiffOn {P : Globals} {S : Scale P} {a : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) :
    UniqueDiffOn ℝ (sec7_ra_rho3DTarget P S a) := by
  have ha0 : 0 < a := by
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    linarith
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := 300 * S.F)
      hAD ha_lo ha_hi ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := S.F / 500)
      hAD ha_lo ha_hi ht_lo
  set q_hi : ℝ := dBreve P.X a (300 * S.F)
  set q_lo : ℝ := dBreve P.X a (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hq_order : q_hi < q_lo := by
    by_contra hnot
    have hle : q_lo ≤ q_hi := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hanti := sec7_Ffun_strictAntiOn_pos (X := P.X) (a := a) P.X_pos ha0
      have hval := hanti (by simpa using hqlo_pos) (by simpa using hqhi_pos) hlt
      change Ffun P.X a q_hi < Ffun P.X a q_lo at hval
      rw [himg_hi, himg_lo] at hval
      nlinarith
    · have heqF : 300 * S.F = S.F / 500 := by
        rw [← himg_hi, ← himg_lo]
        rw [heq]
      nlinarith [hFpos, heqF]
  simpa [sec7_ra_rho3DTarget, q_hi, q_lo] using uniqueDiffOn_Icc hq_order

private theorem sec7_ra_rho3Target_mulD_mapsTo {P : Globals} {S : Scale P} {a : ℝ} :
    Set.MapsTo (fun u : ℝ => S.D * u)
      (sec7_ra_rho3Target P S a) (sec7_ra_rho3DTarget P S a) := by
  intro u hu
  have hDpos : 0 < S.D := S.D_pos
  have huI : dBreve P.X a (300 * S.F) / S.D ≤ u ∧
      u ≤ dBreve P.X a (S.F / 500) / S.D := by
    simpa [sec7_ra_rho3Target] using hu
  constructor
  · have h := mul_le_mul_of_nonneg_right huI.1 hDpos.le
    field_simp [ne_of_gt hDpos] at h
    simpa [sec7_ra_rho3DTarget, mul_comm] using h
  · have h := mul_le_mul_of_nonneg_right huI.2 hDpos.le
    field_simp [ne_of_gt hDpos] at h
    simpa [sec7_ra_rho3DTarget, mul_comm] using h

private theorem sec7_ra_rho3_contDiffOn_DTarget {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 5 (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ))
      (sec7_ra_rho3DTarget P S (a : ℝ)) := by
  intro d hdmem
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha_lo_w : S.A / 5 ≤ (a : ℝ) := sec7_phase_a_lo_wide ha_lo
  have ha_hi_w : (a : ℝ) ≤ 11 * S.A := sec7_phase_a_hi_wide ha_hi
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := 300 * S.F)
      hAD ha_lo_w ha_hi_w ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := S.F / 500)
      hAD ha_lo_w ha_hi_w ht_lo
  set q_hi : ℝ := dBreve P.X (a : ℝ) (300 * S.F)
  set q_lo : ℝ := dBreve P.X (a : ℝ) (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hdI : q_hi ≤ d ∧ d ≤ q_lo := by
    simpa [sec7_ra_rho3DTarget, q_hi, q_lo] using hdmem
  have hdpos : 0 < d := lt_of_lt_of_le hqhi_pos hdI.1
  have hanti := sec7_Ffun_strictAntiOn_pos (X := P.X) (a := (a : ℝ)) P.X_pos haR
  have hFd_hi : Ffun P.X (a : ℝ) d ≤ 300 * S.F := by
    rcases lt_or_eq_of_le hdI.1 with hlt | heq
    · have hval := hanti (by simpa using hqhi_pos) (by simpa using hdpos) hlt
      change Ffun P.X (a : ℝ) d < Ffun P.X (a : ℝ) q_hi at hval
      rw [himg_hi] at hval
      exact le_of_lt hval
    · rw [← heq]
      simpa [q_hi] using himg_hi.le
  have hFd_lo : S.F / 500 ≤ Ffun P.X (a : ℝ) d := by
    rcases lt_or_eq_of_le hdI.2 with hlt | heq
    · have hval := hanti (by simpa using hdpos) (by simpa using hqlo_pos) hlt
      change Ffun P.X (a : ℝ) q_lo < Ffun P.X (a : ℝ) d at hval
      rw [himg_lo] at hval
      exact le_of_lt hval
    · rw [heq]
      simpa [q_lo] using himg_lo.ge
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
    have hjlo' : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le (j : ℝ)
    nlinarith
  have hjhi : (j : ℝ) ≤ S.F / 1000 := by
    have hjhi' : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
    nlinarith
  have htWin : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  set t : ℝ := Ffun P.X (a : ℝ) d + (j : ℝ)
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo_w ha_hi_w (by simpa [t] using htWin)
  have hdb :=
    sec7_dBreve_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR dBreve_pos
  have hdb_at : ContDiffAt ℝ 5 (dBreve P.X (a : ℝ)) t := by
    simpa [himg] using hdb
  have hFbase : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y) d :=
    sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := d)
      (ne_of_gt hdpos) (by positivity)
  have harg : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y + (j : ℝ)) d :=
    hFbase.add contDiffAt_const
  have hB : ContDiffAt ℝ 5
      (fun y : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) y + (j : ℝ))) d := by
    simpa [t] using hdb_at.comp d harg
  have hrad : ContDiffAt ℝ 5 (fun y : ℝ => y * (y + (a : ℝ))) d :=
    contDiffAt_id.mul (contDiffAt_id.add contDiffAt_const)
  have hsqrt : ContDiffAt ℝ 5 (fun y : ℝ => Real.sqrt (y * (y + (a : ℝ)))) d := by
    refine ContDiffAt.sqrt hrad ?_
    positivity
  simpa [sec7_ra_rho3Fun] using (hB.sub hsqrt).contDiffWithinAt

private theorem sec7_ra_rho1_contDiffOn_DTarget {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 5 (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ))
      (sec7_ra_rho3DTarget P S (a : ℝ)) := by
  intro d hdmem
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha_lo_w : S.A / 5 ≤ (a : ℝ) := sec7_phase_a_lo_wide ha_lo
  have ha_hi_w : (a : ℝ) ≤ 11 * S.A := sec7_phase_a_hi_wide ha_hi
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := 300 * S.F)
      hAD ha_lo_w ha_hi_w ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := S.F / 500)
      hAD ha_lo_w ha_hi_w ht_lo
  set q_hi : ℝ := dBreve P.X (a : ℝ) (300 * S.F)
  set q_lo : ℝ := dBreve P.X (a : ℝ) (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hdI : q_hi ≤ d ∧ d ≤ q_lo := by
    simpa [sec7_ra_rho3DTarget, q_hi, q_lo] using hdmem
  have hdpos : 0 < d := lt_of_lt_of_le hqhi_pos hdI.1
  have hanti := sec7_Ffun_strictAntiOn_pos (X := P.X) (a := (a : ℝ)) P.X_pos haR
  have hFd_hi : Ffun P.X (a : ℝ) d ≤ 300 * S.F := by
    rcases lt_or_eq_of_le hdI.1 with hlt | heq
    · have hval := hanti (by simpa using hqhi_pos) (by simpa using hdpos) hlt
      change Ffun P.X (a : ℝ) d < Ffun P.X (a : ℝ) q_hi at hval
      rw [himg_hi] at hval
      exact le_of_lt hval
    · rw [← heq]
      simpa [q_hi] using himg_hi.le
  have hFd_lo : S.F / 500 ≤ Ffun P.X (a : ℝ) d := by
    rcases lt_or_eq_of_le hdI.2 with hlt | heq
    · have hval := hanti (by simpa using hdpos) (by simpa using hqlo_pos) hlt
      change Ffun P.X (a : ℝ) q_lo < Ffun P.X (a : ℝ) d at hval
      rw [himg_lo] at hval
      exact le_of_lt hval
    · rw [heq]
      simpa [q_lo] using himg_lo.ge
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
    have hjlo' : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le (j : ℝ)
    nlinarith
  have hjhi : (j : ℝ) ≤ S.F / 1000 := by
    have hjhi' : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
    nlinarith
  have htWin : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  set t : ℝ := Ffun P.X (a : ℝ) d + (j : ℝ)
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo_w ha_hi_w (by simpa [t] using htWin)
  have hdb :=
    sec7_dBreve'_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR dBreve_pos
  have hdb_at : ContDiffAt ℝ 5 (dBreve' P.X (a : ℝ)) t := by
    simpa [himg] using hdb
  have hFbase : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y) d :=
    sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := d)
      (ne_of_gt hdpos) (by positivity)
  have harg : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y + (j : ℝ)) d :=
    hFbase.add contDiffAt_const
  have hB : ContDiffAt ℝ 5
      (fun y : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y + (j : ℝ))) d := by
    simpa [t] using (hdb_at.comp d harg).neg
  have hmono : ContDiffAt ℝ 5
      (fun y : ℝ => y ^ 2 * (y + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d := by
    fun_prop
  simpa [sec7_ra_rho1Fun] using (hB.sub hmono).contDiffWithinAt

private theorem sec7_raC_ftilde_mapsTo_rho3Target {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) :
    Set.MapsTo (fun s => dtilde P.X s (a : ℝ) / S.D)
      (sec7_rWinWide S W) (sec7_ra_rho3Target P S (a : ℝ)) := by
  intro r hr
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  have ha_lo_w : S.A / 5 ≤ (a : ℝ) := sec7_phase_a_lo_wide ha_lo
  have ha_hi_w : (a : ℝ) ≤ 11 * S.A := sec7_phase_a_hi_wide ha_hi
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD ha_lo_w ha_hi_w hrcore.1 hrcore.2
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := 300 * S.F)
      hAD ha_lo_w ha_hi_w ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := S.F / 500)
      hAD ha_lo_w ha_hi_w ht_lo
  set d : ℝ := dtilde P.X r (a : ℝ)
  set q_hi : ℝ := dBreve P.X (a : ℝ) (300 * S.F)
  set q_lo : ℝ := dBreve P.X (a : ℝ) (S.F / 500)
  have hdpos : 0 < d := by
    dsimp [d]
    exact dtilde_pos P.X_pos haR hr0
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hanti := sec7_Ffun_strictAntiOn_pos (X := P.X) (a := (a : ℝ)) P.X_pos haR
  have hleft_d : q_hi ≤ d := by
    by_contra hnot
    have hlt : d < q_hi := lt_of_not_ge hnot
    have hval := hanti (by simpa using hdpos) (by simpa using hqhi_pos) hlt
    change Ffun P.X (a : ℝ) q_hi < Ffun P.X (a : ℝ) d at hval
    rw [himg_hi, hFd] at hval
    nlinarith
  have hright_d : d ≤ q_lo := by
    by_contra hnot
    have hlt : q_lo < d := lt_of_not_ge hnot
    have hval := hanti (by simpa using hqlo_pos) (by simpa using hdpos) hlt
    change Ffun P.X (a : ℝ) d < Ffun P.X (a : ℝ) q_lo at hval
    rw [hFd, himg_lo] at hval
    nlinarith
  constructor
  · simpa [sec7_ra_rho3Target, d, q_hi] using div_le_div_of_nonneg_right hleft_d hDpos.le
  · simpa [sec7_ra_rho3Target, d, q_lo] using div_le_div_of_nonneg_right hright_d hDpos.le

private theorem sec7_raC_gtilde3_contDiffOn_target {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 5
      (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
      (sec7_ra_rho3Target P S (a : ℝ)) := by
  intro u hu
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  have ha_lo_w : S.A / 5 ≤ (a : ℝ) := sec7_phase_a_lo_wide ha_lo
  have ha_hi_w : (a : ℝ) ≤ 11 * S.A := sec7_phase_a_hi_wide ha_hi
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have ht_hi : 300 * S.F ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have ht_lo : S.F / 500 ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  obtain ⟨himg_hi, _hhi_lo, _hhi_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := 300 * S.F)
      hAD ha_lo_w ha_hi_w ht_hi
  obtain ⟨himg_lo, _hlo_lo, _hlo_hi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := S.F / 500)
      hAD ha_lo_w ha_hi_w ht_lo
  set q_hi : ℝ := dBreve P.X (a : ℝ) (300 * S.F)
  set q_lo : ℝ := dBreve P.X (a : ℝ) (S.F / 500)
  have hqhi_pos : 0 < q_hi := by
    dsimp [q_hi]
    exact dBreve_pos
  have hqlo_pos : 0 < q_lo := by
    dsimp [q_lo]
    exact dBreve_pos
  have huI : dBreve P.X (a : ℝ) (300 * S.F) / S.D ≤ u ∧
      u ≤ dBreve P.X (a : ℝ) (S.F / 500) / S.D := by
    simpa [sec7_ra_rho3Target] using hu
  have hu_pos : 0 < u := by
    have hqdiv : 0 < dBreve P.X (a : ℝ) (300 * S.F) / S.D := by
      simpa [q_hi] using div_pos hqhi_pos hDpos
    exact lt_of_lt_of_le hqdiv huI.1
  have hdu_pos : 0 < S.D * u := mul_pos hDpos hu_pos
  have hqhi_le_du : q_hi ≤ S.D * u := by
    have h := mul_le_mul_of_nonneg_right huI.1 hDpos.le
    field_simp [ne_of_gt hDpos] at h
    simpa [q_hi, mul_comm] using h
  have hdu_le_qlo : S.D * u ≤ q_lo := by
    have h := mul_le_mul_of_nonneg_right huI.2 hDpos.le
    field_simp [ne_of_gt hDpos] at h
    simpa [q_lo, mul_comm] using h
  have hanti := sec7_Ffun_strictAntiOn_pos (X := P.X) (a := (a : ℝ)) P.X_pos haR
  have hFdu_hi : Ffun P.X (a : ℝ) (S.D * u) ≤ 300 * S.F := by
    rcases lt_or_eq_of_le hqhi_le_du with hlt | heq
    · have hval := hanti (by simpa using hqhi_pos) (by simpa using hdu_pos) hlt
      change Ffun P.X (a : ℝ) (S.D * u) < Ffun P.X (a : ℝ) q_hi at hval
      rw [himg_hi] at hval
      exact le_of_lt hval
    · rw [← heq]
      simpa [q_hi] using himg_hi.le
  have hFdu_lo : S.F / 500 ≤ Ffun P.X (a : ℝ) (S.D * u) := by
    rcases lt_or_eq_of_le hdu_le_qlo with hlt | heq
    · have hval := hanti (by simpa using hdu_pos) (by simpa using hqlo_pos) hlt
      change Ffun P.X (a : ℝ) q_lo < Ffun P.X (a : ℝ) (S.D * u) at hval
      rw [himg_lo] at hval
      exact le_of_lt hval
    · rw [heq]
      simpa [q_lo] using himg_lo.ge
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
    have hjlo' : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le (j : ℝ)
    nlinarith
  have hjhi : (j : ℝ) ≤ S.F / 1000 := by
    have hjhi' : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
    nlinarith
  have htWin : Ffun P.X (a : ℝ) (S.D * u) + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  set t : ℝ := Ffun P.X (a : ℝ) (S.D * u) + (j : ℝ)
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD ha_lo_w ha_hi_w (by simpa [t] using htWin)
  have hdb :=
    sec7_dBreve_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR dBreve_pos
  have hdb_at : ContDiffAt ℝ 5 (dBreve P.X (a : ℝ)) t := by
    simpa [himg] using hdb
  have hlin : ContDiffAt ℝ 5 (fun y : ℝ => S.D * y) u :=
    contDiffAt_const.mul contDiffAt_id
  have hFbase : ContDiffAt ℝ 5 (fun d : ℝ => Ffun P.X (a : ℝ) d) (S.D * u) :=
    sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := S.D * u)
      (ne_of_gt hdu_pos) (by positivity)
  have hFarg : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) (S.D * y)) u :=
    hFbase.comp u hlin
  have harg : ContDiffAt ℝ 5
      (fun y : ℝ => Ffun P.X (a : ℝ) (S.D * y) + (j : ℝ)) u :=
    hFarg.add contDiffAt_const
  have hB : ContDiffAt ℝ 5
      (fun y : ℝ => dBreve P.X (a : ℝ)
        (Ffun P.X (a : ℝ) (S.D * y) + (j : ℝ))) u := by
    simpa [t] using hdb_at.comp u harg
  have hrad : ContDiffAt ℝ 5
      (fun y : ℝ => (S.D * y) * (S.D * y + (a : ℝ))) u :=
    hlin.mul (hlin.add contDiffAt_const)
  have hsqrt : ContDiffAt ℝ 5
      (fun y : ℝ => Real.sqrt ((S.D * y) * (S.D * y + (a : ℝ)))) u := by
    refine ContDiffAt.sqrt hrad ?_
    positivity
  have hmain := hB.sub hsqrt
  simpa [sec7_ra_rho3Fun, mul_assoc] using hmain.contDiffWithinAt

private theorem sec7_raC_gtilde1_contDiffOn_target {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 5
      (fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
      (sec7_ra_rho3Target P S (a : ℝ)) := by
  exact
    (sec7_ra_rho1_contDiffOn_DTarget (P := P) (S := S) (W := W)
      (a := a) (j := j) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj).comp
      (by fun_prop :
        ContDiffOn ℝ 5 (fun u : ℝ => S.D * u)
          (sec7_ra_rho3Target P S (a : ℝ)))
      (sec7_ra_rho3Target_mulD_mapsTo (P := P) (S := S) (a := (a : ℝ)))

private theorem sec7_ra_rho3_contDiffAt_dtilde {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5 (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ))
      (dtilde P.X r (a : ℝ)) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hshift : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
        have h := neg_abs_le (j : ℝ)
        nlinarith
      nlinarith
    · rw [sec7_cWin, hFd]
      have hjhi : (j : ℝ) ≤ S.F / 1000 := by
        have h := le_abs_self (j : ℝ)
        nlinarith
      nlinarith
  set t : ℝ := Ffun P.X (a : ℝ) d + (j : ℝ)
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      (by simpa [t] using hshift)
  have hdb :=
    sec7_dBreve_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR dBreve_pos
  have hdb_at : ContDiffAt ℝ 5 (dBreve P.X (a : ℝ)) t := by
    simpa [himg] using hdb
  have hFbase : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y) d :=
    sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := d)
      (ne_of_gt hdpos) (by positivity)
  have harg : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y + (j : ℝ)) d :=
    hFbase.add contDiffAt_const
  have hB : ContDiffAt ℝ 5
      (fun y : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) y + (j : ℝ))) d := by
    simpa [t] using hdb_at.comp d harg
  have hrad : ContDiffAt ℝ 5 (fun y : ℝ => y * (y + (a : ℝ))) d :=
    contDiffAt_id.mul (contDiffAt_id.add contDiffAt_const)
  have hsqrt : ContDiffAt ℝ 5 (fun y : ℝ => Real.sqrt (y * (y + (a : ℝ)))) d := by
    refine ContDiffAt.sqrt hrad ?_
    positivity
  simpa [sec7_ra_rho3Fun, d, hd_def] using (hB.sub hsqrt)

private theorem sec7_ra_rho1_contDiffAt_dtilde {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    ContDiffAt ℝ 5 (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ))
      (dtilde P.X r (a : ℝ)) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hshift : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
        have h := neg_abs_le (j : ℝ)
        nlinarith
      nlinarith
    · rw [sec7_cWin, hFd]
      have hjhi : (j : ℝ) ≤ S.F / 1000 := by
        have h := le_abs_self (j : ℝ)
        nlinarith
      nlinarith
  set t : ℝ := Ffun P.X (a : ℝ) d + (j : ℝ)
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t)
      hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      (by simpa [t] using hshift)
  have hdb :=
    sec7_dBreve'_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t) P.X_pos haR dBreve_pos
  have hdb_at : ContDiffAt ℝ 5 (dBreve' P.X (a : ℝ)) t := by
    simpa [himg] using hdb
  have hFbase : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y) d :=
    sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := d)
      (ne_of_gt hdpos) (by positivity)
  have harg : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y + (j : ℝ)) d :=
    hFbase.add contDiffAt_const
  have hB : ContDiffAt ℝ 5
      (fun y : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y + (j : ℝ))) d := by
    simpa [t] using (hdb_at.comp d harg).neg
  have hmono : ContDiffAt ℝ 5
      (fun y : ℝ => y ^ 2 * (y + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d := by
    fun_prop
  simpa [sec7_ra_rho1Fun, d, hd_def] using (hB.sub hmono)

/-- Graded expansion error for `f₁`, defined as derivatives of the genuine grade-0 residual. -/
noncomputable def sec7_phase_ra_e₁D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ := fun j m =>
  iteratedDeriv m
    (fun t => sec7_phase_f1D P S a j 0 t
        - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ))
    )

/-- Graded expansion error for `f₂`, defined as derivatives of the genuine grade-0 residual. -/
noncomputable def sec7_phase_ra_e₂D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ := fun j m =>
  iteratedDeriv m
    (fun t => sec7_phase_f2D P S a 0 t
        - sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)
    )

private theorem sec7_phase_f2D_eq_powMonD_add_ra_e₂D {P : Globals} {S : Scale P}
    {W : ℝ} {a j : ℤ} {m : ℕ} {r : ℝ} (ha : 0 < a)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hm : m ≤ 5) (hr : r ∈ sec7_rWinWide S W) :
    sec7_phase_f2D P S a m r =
      sec7_powMonD S.R (sec7_phase_ra_c₂ P S a j * S.T₂) ((3 : ℝ) / 4) m r +
        sec7_phase_ra_e₂D P S a j m r := by
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hbase5 : ContDiffAt ℝ 5 (fun t => sec7_phase_f2D P S a 0 t) r := by
    have hftil : ContDiffAt ℝ 5 (sec7_phase_ftil P S a) r :=
      sec7_phase_ftil_contDiffAt5 (P := P) (S := S) (a := a) ha hr0
    simpa [sec7_phase_f2D] using hftil
  have hpow5 : ContDiffAt ℝ 5
      (fun t : ℝ => (t / S.R) ^ ((3 : ℝ) / 4)) r :=
    sec7_phase_rpow_div_contDiffAt5 (P := P) (S := S) (r := r)
      (α := ((3 : ℝ) / 4)) hr0
  have hmon5 : ContDiffAt ℝ 5
      (fun t : ℝ => sec7_phase_ra_c₂ P S a j * S.T₂ *
        (t / S.R) ^ ((3 : ℝ) / 4)) r := by
    simpa [mul_assoc] using
      ((contDiffAt_const :
        ContDiffAt ℝ 5 (fun _ : ℝ => sec7_phase_ra_c₂ P S a j * S.T₂) r).mul hpow5)
  have hsub := iteratedDeriv_fun_sub (n := m)
    (f := fun t : ℝ => sec7_phase_f2D P S a 0 t)
    (g := fun t : ℝ => sec7_phase_ra_c₂ P S a j * S.T₂ *
      (t / S.R) ^ ((3 : ℝ) / 4))
    (x := r) (hbase5.of_le (by exact_mod_cast hm)) (hmon5.of_le (by exact_mod_cast hm))
  have hmonDeriv :
      iteratedDeriv m
        (fun t : ℝ => sec7_phase_ra_c₂ P S a j * S.T₂ *
          (t / S.R) ^ ((3 : ℝ) / 4)) r =
        sec7_powMonD S.R (sec7_phase_ra_c₂ P S a j * S.T₂) ((3 : ℝ) / 4) m r :=
    sec7_phase_powMon_iteratedDeriv_eq (P := P) (S := S)
      (c := sec7_phase_ra_c₂ P S a j * S.T₂) (α := ((3 : ℝ) / 4)) m hr0
  have hres :
      sec7_phase_ra_e₂D P S a j m r =
        sec7_phase_f2D P S a m r -
          sec7_powMonD S.R (sec7_phase_ra_c₂ P S a j * S.T₂) ((3 : ℝ) / 4) m r := by
    calc
      sec7_phase_ra_e₂D P S a j m r =
          iteratedDeriv m
            (fun t : ℝ => sec7_phase_f2D P S a 0 t -
              sec7_phase_ra_c₂ P S a j * S.T₂ * (t / S.R) ^ ((3 : ℝ) / 4)) r := by
            rfl
      _ = iteratedDeriv m (fun t : ℝ => sec7_phase_f2D P S a 0 t) r -
          iteratedDeriv m
            (fun t : ℝ => sec7_phase_ra_c₂ P S a j * S.T₂ *
              (t / S.R) ^ ((3 : ℝ) / 4)) r := hsub
      _ = sec7_phase_f2D P S a m r -
          sec7_powMonD S.R (sec7_phase_ra_c₂ P S a j * S.T₂) ((3 : ℝ) / 4) m r := by
            rw [hmonDeriv]
            simp [sec7_phase_f2D]
  linarith

/-- Graded expansion error for `f₃`, defined as derivatives of the genuine grade-0 residual. -/
noncomputable def sec7_phase_ra_e₃D (P : Globals) (S : Scale P) (a : ℤ) :
    ℤ → ℕ → ℝ → ℝ := fun j m =>
  iteratedDeriv m
    (fun t => sec7_phase_f3D P S a j 0 t
        - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
            * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4)
    )

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

private theorem sec7_ra_rpow_neg_cancel_unit {D d : ℝ} {i : ℕ}
    (hD : 0 < D) (hdlo : D / 16 ≤ d) :
    D ^ i * d ^ (-(i : ℝ)) ≤ 16 ^ i := by
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity : 0 < D / 16) hdlo
  have hpow_lo : (D / 16) ^ i ≤ d ^ i :=
    pow_le_pow_left₀ (by positivity : 0 ≤ D / 16) hdlo i
  have hpow_pos : 0 < (D / 16) ^ i := by positivity
  have hinv : (d ^ i)⁻¹ ≤ ((D / 16) ^ i)⁻¹ :=
    inv_anti₀ hpow_pos hpow_lo
  have hrpow : d ^ (-(i : ℝ)) = (d ^ i)⁻¹ := by
    rw [show (-(i : ℝ)) = -(((i : ℕ) : ℝ)) by norm_num, Real.rpow_neg hdpos.le,
      Real.rpow_natCast]
  calc
    D ^ i * d ^ (-(i : ℝ)) ≤ D ^ i * ((D / 16) ^ i)⁻¹ := by
      rw [hrpow]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 16 ^ i := by
      rw [div_pow, inv_div]
      field_simp [ne_of_gt hD, pow_ne_zero _ (ne_of_gt hD)]

private theorem sec7_ra_pow_div_cancel_20 {D d : ℝ} {i : ℕ}
    (hD : 0 < D) (hdlo : D / 20 ≤ d) :
    D ^ i / d ^ i ≤ 20 ^ i := by
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity : 0 < D / 20) hdlo
  have hpow_lo : (D / 20) ^ i ≤ d ^ i :=
    pow_le_pow_left₀ (by positivity : 0 ≤ D / 20) hdlo i
  have hpow_pos : 0 < (D / 20) ^ i := by positivity
  have hinv : (d ^ i)⁻¹ ≤ ((D / 20) ^ i)⁻¹ :=
    inv_anti₀ hpow_pos hpow_lo
  calc
    D ^ i / d ^ i = D ^ i * (d ^ i)⁻¹ := by ring
    _ ≤ D ^ i * ((D / 20) ^ i)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 20 ^ i := by
      rw [div_pow, inv_div]
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

private theorem sec7_raC_ftilde_contDiffOn_wide {P : Globals} {S : Scale P} {W : ℝ}
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

private theorem sec7_raC_ftilde_FDeriv_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hr : r ∈ sec7_rWinWide S W) {i : ℕ} (hi₁ : 1 ≤ i) (hi₅ : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i (fun s => dtilde P.X s (a : ℝ) / S.D)
        (sec7_rWinWide S W) r‖ ≤ ((10 ^ 3 : ℝ) / S.R) ^ i := by
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
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 1 := by
            norm_num [sec7_ra_Cdt1]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
  · have hdt := sec7_ra_dtilde_wide_d2 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 2 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt2 * (S.D / S.R ^ 2)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 2 := by
            norm_num [sec7_ra_Cdt2]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d3 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 3 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt3 * (S.D / S.R ^ 3)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 3 := by
            norm_num [sec7_ra_Cdt3]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d4 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 4 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt4 * (S.D / S.R ^ 4)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 4 := by
            norm_num [sec7_ra_Cdt4]
            field_simp [ne_of_gt hDpos, ne_of_gt hRpos]
            ring
  · have hdt := sec7_ra_dtilde_wide_d5 (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr
    calc
      |iteratedDeriv 5 (fun s => dtilde P.X s (a : ℝ)) r| / S.D
          ≤ (sec7_ra_Cdt5 * (S.D / S.R ^ 5)) / S.D :=
            div_le_div_of_nonneg_right hdt hDpos.le
      _ = ((10 ^ 3 : ℝ) / S.R) ^ 5 := by
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

private theorem sec7_ra_T₃_relErrF_eq_A_G_U5 {P : Globals} (S : Scale P) :
    S.T₃ * sec7_relErrF P S = S.A * P.G * P.U ^ 5 := by
  have hH := P.H_pos
  unfold sec7_relErrF sec7_relErr sec7_cGU Scale.T₃ Scale.A
  field_simp [hH.ne']

private theorem sec7_ra_A_Dsq_div_X_eq_T₁_ΩH_sq {P : Globals} (S : Scale P) :
    S.A * S.D ^ 2 / P.X = S.T₁ * (S.Ω / P.H) ^ 2 := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.A Scale.D Scale.T₁ Scale.F
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp [hH.ne', hG.ne', hΔ.ne', hΩ.ne']

private theorem sec7_ra_D_cubed_div_XA_eq_invF {P : Globals} (S : Scale P) :
    S.D ^ 3 / (P.X * S.A) = 1 / S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.D Scale.A Scale.F
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp [hH.ne', hG.ne', hΔ.ne', hΩ.ne']

private theorem sec7_ra_D_seventh_div_XsqAsq_eq_T₁_div_F {P : Globals} (S : Scale P) :
    S.D ^ 7 / (P.X ^ 2 * S.A ^ 2) = S.T₁ / S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.D Scale.A Scale.T₁ Scale.F
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp [hH.ne', hG.ne', hΔ.ne', hΩ.ne']

private theorem sec7_ra_D_seventh_div_Xa_sq_le_T₁_div_F {P : Globals} {S : Scale P}
    {a : ℝ} (ha_lo : S.A ≤ a) :
    S.D ^ 7 / (P.X * a) ^ 2 ≤ S.T₁ / S.F := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hapos : 0 < a := lt_of_lt_of_le hApos ha_lo
  have hDpos : 0 < S.D := S.D_pos
  have hden_mono : P.X * S.A ≤ P.X * a :=
    mul_le_mul_of_nonneg_left ha_lo P.X_pos.le
  have hdenApos : 0 < P.X * S.A := mul_pos P.X_pos hApos
  have hden_sq : (P.X * S.A) ^ 2 ≤ (P.X * a) ^ 2 :=
    pow_le_pow_left₀ hdenApos.le hden_mono 2
  have hinv_den : ((P.X * a) ^ 2)⁻¹ ≤ ((P.X * S.A) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hdenApos 2) hden_sq
  calc
    S.D ^ 7 / (P.X * a) ^ 2
        = S.D ^ 7 * ((P.X * a) ^ 2)⁻¹ := by ring
    _ ≤ S.D ^ 7 * ((P.X * S.A) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv_den (pow_nonneg hDpos.le 7)
    _ = S.D ^ 7 / (P.X ^ 2 * S.A ^ 2) := by ring
    _ = S.T₁ / S.F := sec7_ra_D_seventh_div_XsqAsq_eq_T₁_div_F S

private theorem sec7_ra_D_fourth_div_Xa_le_T₃_div_F {P : Globals} {S : Scale P} {a : ℝ}
    (ha_lo : S.A ≤ a) :
    S.D ^ 4 / (P.X * a) ≤ S.T₃ / S.F := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hapos : 0 < a := lt_of_lt_of_le hApos ha_lo
  have hDpos : 0 < S.D := S.D_pos
  have hden_mono : P.X * S.A ≤ P.X * a :=
    mul_le_mul_of_nonneg_left ha_lo P.X_pos.le
  have hinv : (P.X * a)⁻¹ ≤ (P.X * S.A)⁻¹ :=
    inv_anti₀ (mul_pos P.X_pos hApos) hden_mono
  calc
    S.D ^ 4 / (P.X * a)
        = S.D * (S.D ^ 3 * (P.X * a)⁻¹) := by ring
    _ ≤ S.D * (S.D ^ 3 * (P.X * S.A)⁻¹) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinv (pow_nonneg hDpos.le 3)) hDpos.le
    _ = S.D * (S.D ^ 3 / (P.X * S.A)) := by ring
    _ = S.D * (1 / S.F) := by
          rw [sec7_ra_D_cubed_div_XA_eq_invF]
    _ = S.T₃ / S.F := by
          unfold Scale.D Scale.T₃
          ring

private noncomputable def sec7_ra_B1ComposeScale : ℕ → ℝ
  | 0 => 300
  | 1 => 1400
  | 2 => 152200
  | 3 => 18813600
  | 4 => 4000696000
  | 5 => 191061040000
  | _ => 0

private theorem sec7_ra_j_over_F_le_relErrF_small {P : Globals} {S : Scale P}
    {c₀ Cu : ℝ} {j : ℤ}
    (hsd : OnStripAux.StripData P S c₀ Cu) (hj : sec7_jBand P S j)
    (hG1 : 1 ≤ P.G) (hG10x : P.G * P.U ^ 10 ≤ S.x)
    (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    |(j : ℝ)| / S.F ≤ (1 / (10 : ℝ) ^ 5) * sec7_relErrF P S := by
  have hFpos : 0 < S.F := by
    have := P.H_pos
    have := P.G_pos
    have := S.Ω_pos
    have := S.Δ_pos
    unfold Scale.F
    positivity
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hxpos : 0 < S.x := by
    have := P.H_pos
    have := S.Δ_pos
    unfold Scale.x
    positivity
  have hU1 : (1 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
  have hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω := by
    have hbase_pos : 0 ≤ P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) := by positivity
    calc
      P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)
          = 1 * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) := by ring
      _ ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) :=
            mul_le_mul_of_nonneg_right hsd.hc₀ hbase_pos
      _ ≤ S.Ω := hsd.hΩlo
  have hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4 :=
    StripAux.regime_band_one P S hband6
  have hΩ2leU2 : S.Ω ^ 2 ≤ P.U ^ 2 :=
    pow_le_pow_left₀ hΩpos.le hsd.hΩhi 2
  have hband_to : P.G * P.U ^ 3 * S.Ω ^ 4 ≤ P.G * S.Ω ^ 2 * P.U ^ 5 := by
    calc
      P.G * P.U ^ 3 * S.Ω ^ 4
          = P.G * P.U ^ 3 * (S.Ω ^ 2 * S.Ω ^ 2) := by ring
      _ ≤ P.G * P.U ^ 3 * (S.Ω ^ 2 * P.U ^ 2) := by gcongr
      _ = P.G * S.Ω ^ 2 * P.U ^ 5 := by ring
  have hbaseΩ : 1 ≤ P.G * S.Ω ^ 2 * P.U ^ 5 := le_trans hband hband_to
  have hG2U8 : 1 ≤ P.G ^ 2 * P.U ^ 8 := by
    have hG2 : 1 ≤ P.G ^ 2 := one_le_pow₀ hG1
    have hU8 : 1 ≤ P.U ^ 8 := one_le_pow₀ hU1
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P.G ^ 2 * P.U ^ 8 := mul_le_mul hG2 hU8 zero_le_one (by positivity)
  have hΩfactor : 1 ≤ P.G ^ 3 * S.Ω ^ 2 * P.U ^ 13 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (P.G * S.Ω ^ 2 * P.U ^ 5) * (P.G ^ 2 * P.U ^ 8) :=
            mul_le_mul hbaseΩ hG2U8 zero_le_one (by positivity)
      _ = P.G ^ 3 * S.Ω ^ 2 * P.U ^ 13 := by ring
  set Den : ℝ := P.G ^ 2 * S.Ω ^ 4 * S.x * P.U ^ 5 with hDen
  have hDen_nonneg : 0 ≤ Den := by
    rw [hDen]
    positivity
  have hG_le_G2 : P.G ≤ P.G ^ 2 := by
    calc
      P.G = P.G * 1 := by ring
      _ ≤ P.G * P.G := mul_le_mul_of_nonneg_left hG1 P.G_pos.le
      _ = P.G ^ 2 := by ring
  have hG_le_G2 : P.G ≤ P.G ^ 2 := by
    calc
      P.G = P.G * 1 := by ring
      _ ≤ P.G * P.G := mul_le_mul_of_nonneg_left hG1 P.G_pos.le
      _ = P.G ^ 2 := by ring
  have hDenx : S.x * P.U ^ 2 ≤ Den := by
    have hfac : 1 ≤ P.G ^ 2 * S.Ω ^ 4 * P.U ^ 3 := by
      calc
        (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
        _ ≤ P.G ^ 2 * P.U ^ 3 * S.Ω ^ 4 := by gcongr
        _ = P.G ^ 2 * S.Ω ^ 4 * P.U ^ 3 := by ring
    calc
      S.x * P.U ^ 2 = 1 * (S.x * P.U ^ 2) := by ring
      _ ≤ (P.G ^ 2 * S.Ω ^ 4 * P.U ^ 3) * (S.x * P.U ^ 2) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = Den := by rw [hDen]; ring
  have hDenΩ : S.Ω ^ 2 * P.U ^ 2 ≤ Den := by
    have hmid : S.Ω ^ 2 * P.U ^ 2 ≤ P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15 := by
      calc
        S.Ω ^ 2 * P.U ^ 2 = 1 * (S.Ω ^ 2 * P.U ^ 2) := by ring
        _ ≤ (P.G ^ 3 * S.Ω ^ 2 * P.U ^ 13) * (S.Ω ^ 2 * P.U ^ 2) :=
              mul_le_mul_of_nonneg_right hΩfactor (by positivity)
        _ = P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15 := by ring
    have hden_ge : P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15 ≤ Den := by
      calc
        P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15
            = (P.G ^ 2 * S.Ω ^ 4 * P.U ^ 5) * (P.G * P.U ^ 10) := by ring
        _ ≤ (P.G ^ 2 * S.Ω ^ 4 * P.U ^ 5) * S.x :=
              mul_le_mul_of_nonneg_left hG10x (by positivity)
        _ = Den := by rw [hDen]; ring
    exact le_trans hmid hden_ge
  have hU2big : (10 : ℝ) ^ 66 ≤ P.U ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (10 : ℝ) ^ 33) hUbig 2
    norm_num at h ⊢
    exact h
  have hcJsmall : sec7_cJ ≤ (1 / (10 : ℝ) ^ 6) * P.U ^ 2 := by
    have hmul : sec7_cJ * (10 : ℝ) ^ 6 ≤ P.U ^ 2 :=
      le_trans (by norm_num [sec7_cJ]) hU2big
    calc
      sec7_cJ = (sec7_cJ * (10 : ℝ) ^ 6) / (10 : ℝ) ^ 6 := by field_simp
      _ ≤ P.U ^ 2 / (10 : ℝ) ^ 6 := div_le_div_of_nonneg_right hmul (by positivity)
      _ = (1 / (10 : ℝ) ^ 6) * P.U ^ 2 := by ring
  have hΩterm : sec7_cJ * S.Ω ^ 2 ≤ (1 / (10 : ℝ) ^ 6) * Den := by
    calc
      sec7_cJ * S.Ω ^ 2 ≤ ((1 / (10 : ℝ) ^ 6) * P.U ^ 2) * S.Ω ^ 2 := by gcongr
      _ = (1 / (10 : ℝ) ^ 6) * (S.Ω ^ 2 * P.U ^ 2) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 6) * Den := by gcongr
  have hxterm : sec7_cJ * S.x ≤ (1 / (10 : ℝ) ^ 6) * Den := by
    calc
      sec7_cJ * S.x ≤ ((1 / (10 : ℝ) ^ 6) * P.U ^ 2) * S.x := by gcongr
      _ = (1 / (10 : ℝ) ^ 6) * (S.x * P.U ^ 2) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 6) * Den := by gcongr
  have hkey : sec7_cJ * (S.Ω ^ 2 + S.x) ≤
      (1 / (10 : ℝ) ^ 5) * (P.G ^ 2 * S.Ω ^ 4 * S.x * P.U ^ 5) := by
    calc
      sec7_cJ * (S.Ω ^ 2 + S.x) = sec7_cJ * S.Ω ^ 2 + sec7_cJ * S.x := by ring
      _ ≤ (1 / (10 : ℝ) ^ 6) * Den + (1 / (10 : ℝ) ^ 6) * Den :=
            add_le_add hΩterm hxterm
      _ = (2 / (10 : ℝ) ^ 6) * Den := by ring
      _ ≤ (1 / (10 : ℝ) ^ 5) * Den :=
            mul_le_mul_of_nonneg_right (by norm_num) hDen_nonneg
      _ = (1 / (10 : ℝ) ^ 5) * (P.G ^ 2 * S.Ω ^ 4 * S.x * P.U ^ 5) := by
            rw [hDen]
  have hraw : sec7_cJ * (1 + P.H / S.A ^ 2) / S.F ≤
      (1 / (10 : ℝ) ^ 5) * sec7_relErrF P S := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΩ := S.Ω_pos
    have hΔ := S.Δ_pos
    unfold Scale.x at hkey
    unfold sec7_relErrF sec7_relErr sec7_cGU Scale.F Scale.A
    field_simp [hH.ne', hG.ne', hΩ.ne', hΔ.ne'] at hkey ⊢
    simpa [mul_comm, mul_left_comm, mul_assoc] using hkey
  have hj_abs : |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := by
    rw [← Int.cast_abs]
    simpa [sec7_jBand] using hj
  calc
    |(j : ℝ)| / S.F ≤ sec7_cJ * (1 + P.H / S.A ^ 2) / S.F :=
      div_le_div_of_nonneg_right hj_abs hFpos.le
    _ ≤ (1 / (10 : ℝ) ^ 5) * sec7_relErrF P S := hraw

private theorem sec7_ra_j_over_F_le_relErrF_tiny {P : Globals} {S : Scale P}
    {c₀ Cu : ℝ} {j : ℤ}
    (hsd : OnStripAux.StripData P S c₀ Cu) (hj : sec7_jBand P S j)
    (hG1 : 1 ≤ P.G) (hG10x : P.G * P.U ^ 10 ≤ S.x)
    (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    |(j : ℝ)| / S.F ≤ (1 / (10 : ℝ) ^ 9) * sec7_relErrF P S := by
  have hFpos : 0 < S.F := by
    have := P.H_pos
    have := P.G_pos
    have := S.Ω_pos
    have := S.Δ_pos
    unfold Scale.F
    positivity
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hxpos : 0 < S.x := by
    have := P.H_pos
    have := S.Δ_pos
    unfold Scale.x
    positivity
  have hU1 : (1 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
  have hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω := by
    have hbase_pos : 0 ≤ P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) := by positivity
    calc
      P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)
          = 1 * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) := by ring
      _ ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) :=
            mul_le_mul_of_nonneg_right hsd.hc₀ hbase_pos
      _ ≤ S.Ω := hsd.hΩlo
  have hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4 :=
    StripAux.regime_band_one P S hband6
  have hΩ2leU2 : S.Ω ^ 2 ≤ P.U ^ 2 :=
    pow_le_pow_left₀ hΩpos.le hsd.hΩhi 2
  have hband_to : P.G * P.U ^ 3 * S.Ω ^ 4 ≤ P.G * S.Ω ^ 2 * P.U ^ 5 := by
    calc
      P.G * P.U ^ 3 * S.Ω ^ 4
          = P.G * P.U ^ 3 * (S.Ω ^ 2 * S.Ω ^ 2) := by ring
      _ ≤ P.G * P.U ^ 3 * (S.Ω ^ 2 * P.U ^ 2) := by gcongr
      _ = P.G * S.Ω ^ 2 * P.U ^ 5 := by ring
  have hbaseΩ : 1 ≤ P.G * S.Ω ^ 2 * P.U ^ 5 := le_trans hband hband_to
  have hG2U8 : 1 ≤ P.G ^ 2 * P.U ^ 8 := by
    have hG2 : 1 ≤ P.G ^ 2 := one_le_pow₀ hG1
    have hU8 : 1 ≤ P.U ^ 8 := one_le_pow₀ hU1
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P.G ^ 2 * P.U ^ 8 := mul_le_mul hG2 hU8 zero_le_one (by positivity)
  have hΩfactor : 1 ≤ P.G ^ 3 * S.Ω ^ 2 * P.U ^ 13 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (P.G * S.Ω ^ 2 * P.U ^ 5) * (P.G ^ 2 * P.U ^ 8) :=
            mul_le_mul hbaseΩ hG2U8 zero_le_one (by positivity)
      _ = P.G ^ 3 * S.Ω ^ 2 * P.U ^ 13 := by ring
  set Den : ℝ := P.G ^ 2 * S.Ω ^ 4 * S.x * P.U ^ 5 with hDen
  have hDen_nonneg : 0 ≤ Den := by
    rw [hDen]
    positivity
  have hG_le_G2_tiny : P.G ≤ P.G ^ 2 := by
    calc
      P.G = P.G * 1 := by ring
      _ ≤ P.G * P.G := mul_le_mul_of_nonneg_left hG1 P.G_pos.le
      _ = P.G ^ 2 := by ring
  have hDenx : S.x * P.U ^ 2 ≤ Den := by
    have hfac : 1 ≤ P.G ^ 2 * S.Ω ^ 4 * P.U ^ 3 := by
      calc
        (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
        _ ≤ P.G ^ 2 * P.U ^ 3 * S.Ω ^ 4 := by gcongr
        _ = P.G ^ 2 * S.Ω ^ 4 * P.U ^ 3 := by ring
    calc
      S.x * P.U ^ 2 = 1 * (S.x * P.U ^ 2) := by ring
      _ ≤ (P.G ^ 2 * S.Ω ^ 4 * P.U ^ 3) * (S.x * P.U ^ 2) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = Den := by rw [hDen]; ring
  have hDenΩ : S.Ω ^ 2 * P.U ^ 2 ≤ Den := by
    have hmid : S.Ω ^ 2 * P.U ^ 2 ≤ P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15 := by
      calc
        S.Ω ^ 2 * P.U ^ 2 = 1 * (S.Ω ^ 2 * P.U ^ 2) := by ring
        _ ≤ (P.G ^ 3 * S.Ω ^ 2 * P.U ^ 13) * (S.Ω ^ 2 * P.U ^ 2) :=
              mul_le_mul_of_nonneg_right hΩfactor (by positivity)
        _ = P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15 := by ring
    have hden_ge : P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15 ≤ Den := by
      calc
        P.G ^ 3 * S.Ω ^ 4 * P.U ^ 15
            = (P.G ^ 2 * S.Ω ^ 4 * P.U ^ 5) * (P.G * P.U ^ 10) := by ring
        _ ≤ (P.G ^ 2 * S.Ω ^ 4 * P.U ^ 5) * S.x :=
              mul_le_mul_of_nonneg_left hG10x (by positivity)
        _ = Den := by rw [hDen]; ring
    exact le_trans hmid hden_ge
  have hU2big : (10 : ℝ) ^ 66 ≤ P.U ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (10 : ℝ) ^ 33) hUbig 2
    norm_num at h ⊢
    exact h
  have hcJsmall : sec7_cJ ≤ (1 / (10 : ℝ) ^ 10) * P.U ^ 2 := by
    have hmul : sec7_cJ * (10 : ℝ) ^ 10 ≤ P.U ^ 2 :=
      le_trans (by norm_num [sec7_cJ]) hU2big
    calc
      sec7_cJ = (sec7_cJ * (10 : ℝ) ^ 10) / (10 : ℝ) ^ 10 := by field_simp
      _ ≤ P.U ^ 2 / (10 : ℝ) ^ 10 := div_le_div_of_nonneg_right hmul (by positivity)
      _ = (1 / (10 : ℝ) ^ 10) * P.U ^ 2 := by ring
  have hΩterm : sec7_cJ * S.Ω ^ 2 ≤ (1 / (10 : ℝ) ^ 10) * Den := by
    calc
      sec7_cJ * S.Ω ^ 2 ≤ ((1 / (10 : ℝ) ^ 10) * P.U ^ 2) * S.Ω ^ 2 := by gcongr
      _ = (1 / (10 : ℝ) ^ 10) * (S.Ω ^ 2 * P.U ^ 2) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 10) * Den := by gcongr
  have hxterm : sec7_cJ * S.x ≤ (1 / (10 : ℝ) ^ 10) * Den := by
    calc
      sec7_cJ * S.x ≤ ((1 / (10 : ℝ) ^ 10) * P.U ^ 2) * S.x := by gcongr
      _ = (1 / (10 : ℝ) ^ 10) * (S.x * P.U ^ 2) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 10) * Den := by gcongr
  have hkey : sec7_cJ * (S.Ω ^ 2 + S.x) ≤
      (1 / (10 : ℝ) ^ 9) * (P.G ^ 2 * S.Ω ^ 4 * S.x * P.U ^ 5) := by
    calc
      sec7_cJ * (S.Ω ^ 2 + S.x) = sec7_cJ * S.Ω ^ 2 + sec7_cJ * S.x := by ring
      _ ≤ (1 / (10 : ℝ) ^ 10) * Den + (1 / (10 : ℝ) ^ 10) * Den :=
            add_le_add hΩterm hxterm
      _ = (2 / (10 : ℝ) ^ 10) * Den := by ring
      _ ≤ (1 / (10 : ℝ) ^ 9) * Den :=
            mul_le_mul_of_nonneg_right (by norm_num) hDen_nonneg
      _ = (1 / (10 : ℝ) ^ 9) * (P.G ^ 2 * S.Ω ^ 4 * S.x * P.U ^ 5) := by
            rw [hDen]
  have hraw : sec7_cJ * (1 + P.H / S.A ^ 2) / S.F ≤
      (1 / (10 : ℝ) ^ 9) * sec7_relErrF P S := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΩ := S.Ω_pos
    have hΔ := S.Δ_pos
    unfold Scale.x at hkey
    unfold sec7_relErrF sec7_relErr sec7_cGU Scale.F Scale.A
    field_simp [hH.ne', hG.ne', hΩ.ne', hΔ.ne'] at hkey ⊢
    simpa [mul_comm, mul_left_comm, mul_assoc] using hkey
  have hj_abs : |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := by
    rw [← Int.cast_abs]
    simpa [sec7_jBand] using hj
  calc
    |(j : ℝ)| / S.F ≤ sec7_cJ * (1 + P.H / S.A ^ 2) / S.F :=
      div_le_div_of_nonneg_right hj_abs hFpos.le
    _ ≤ (1 / (10 : ℝ) ^ 9) * sec7_relErrF P S := hraw

private theorem sec7_ra_rho3_A_rescaled_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) (hu0 : 0 < P.u)
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    S.D ^ i *
        |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ))))
          (dtilde P.X r (a : ℝ))|
      ≤ (10 ^ 8 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  have htWin : sec7_phase_ftil P S a r ∈ sec7_tWin S := by
    have hFpos : 0 < S.F := sec7_phase_F_pos S
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hdb_eq : dBreve P.X (a : ℝ) (sec7_phase_ftil P S a r) = d := by
    simpa [d, hd_def, sec7_phase_ftil] using dBreve_spec P.X_pos haR hdpos
  obtain ⟨_himg, hdlo16_raw, _hdhi30_raw⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ))
      (t := sec7_phase_ftil P S a r) hAD (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) htWin
  have hdlo16 : S.D / 16 ≤ d := by
    simpa [hdb_eq] using hdlo16_raw
  have hA3 :=
    sec7_ra_A3_bound_public (a := (a : ℝ)) (d := d) (d_lo := S.D / 16)
      (k := i) hi haR (by positivity) hdlo16
  have hcancel := sec7_ra_rpow_neg_cancel_unit (D := S.D) (d := d) (i := i)
    hDpos hdlo16
  have hmain :
      S.D ^ i *
          |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ)))) d|
        ≤ (10 ^ 8 : ℝ) * S.A := by
    calc
      S.D ^ i *
          |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ)))) d|
          ≤ S.D ^ i * ((30 : ℝ) * (a : ℝ) * d ^ (-(i : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = (30 : ℝ) * (a : ℝ) * (S.D ^ i * d ^ (-(i : ℝ))) := by ring
      _ ≤ (30 : ℝ) * (a : ℝ) * 16 ^ i := by
            exact mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ ≤ (30 : ℝ) * (2 * S.A) * 16 ^ i := by
            gcongr
      _ ≤ (10 ^ 8 : ℝ) * S.A := by
            have hconst : (30 : ℝ) * (2 : ℝ) * 16 ^ i ≤ 10 ^ 8 := by
              interval_cases i <;> norm_num
            calc
              (30 : ℝ) * (2 * S.A) * 16 ^ i =
                  ((30 : ℝ) * (2 : ℝ) * 16 ^ i) * S.A := by ring
              _ ≤ (10 ^ 8 : ℝ) * S.A :=
                  mul_le_mul_of_nonneg_right hconst hApos.le
  have hU1 : (1 : ℝ) ≤ P.U := by
    unfold Globals.U
    exact Real.one_le_rpow hsd.hX hu0.le
  have hGU : (1 : ℝ) ≤ P.G * P.U ^ 5 := by
    have hU5 : (1 : ℝ) ≤ P.U ^ 5 := one_le_pow₀ hU1
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P.G * P.U ^ 5 := mul_le_mul hG1 hU5 zero_le_one P.G_pos.le
  have hA_le : S.A ≤ S.A * P.G * P.U ^ 5 := by
    calc
      S.A = S.A * 1 := by ring
      _ ≤ S.A * (P.G * P.U ^ 5) := mul_le_mul_of_nonneg_left hGU hApos.le
      _ = S.A * P.G * P.U ^ 5 := by ring
  calc
    S.D ^ i *
        |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ))))
          (dtilde P.X r (a : ℝ))|
        = S.D ^ i *
          |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ)))) d| := by
            rw [hd_def]
    _ ≤ (10 ^ 8 : ℝ) * S.A := hmain
    _ ≤ (10 ^ 8 : ℝ) * (S.A * P.G * P.U ^ 5) :=
          mul_le_mul_of_nonneg_left hA_le (by positivity)
    _ = (10 ^ 8 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
          rw [sec7_ra_T₃_relErrF_eq_A_G_U5]

private theorem sec7_ra_rho1_A_rescaled_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    S.D ^ i *
        |iteratedDeriv i
          (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t) -
            t ^ 2 * (t + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ)))
          (dtilde P.X r (a : ℝ))|
      ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hT1pos : 0 < S.T₁ := sec7_T₁_pos S
  obtain ⟨hdlo20, hd_ge_a, hdhi40⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  have hdpos : 0 < d :=
    lt_of_lt_of_le (by positivity : 0 < S.D / 20) (by simpa [d, hd_def] using hdlo20)
  have hdhi : d ≤ 40 * S.D := by simpa [d, hd_def] using hdhi40
  have hAge : (a : ℝ) ≤ d := by simpa [d, hd_def] using hd_ge_a
  have hA1 :=
    sec7_ra_A1_bound (X := P.X) (a := (a : ℝ)) (d := d) (k := i)
      hi P.X_pos haR hdpos hAge
  have hscale_nonneg : 0 ≤ sec7_ra_A1Scale i := by
    interval_cases i <;> norm_num [sec7_ra_A1Scale]
  have hcancel : S.D ^ i / d ^ i ≤ 20 ^ i :=
    sec7_ra_pow_div_cancel_20 (D := S.D) (d := d) (i := i) hDpos
      (by simpa [d, hd_def] using hdlo20)
  have hd2 : d ^ 2 ≤ (40 * S.D) ^ 2 :=
    pow_le_pow_left₀ hdpos.le hdhi 2
  have hraw :
      S.D ^ i *
          |iteratedDeriv i
            (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t) -
              t ^ 2 * (t + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d|
        ≤ (10 ^ 13 : ℝ) * (S.T₁ * (S.Ω / P.H) ^ 2) := by
    calc
      S.D ^ i *
          |iteratedDeriv i
            (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t) -
              t ^ 2 * (t + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d|
          ≤ S.D ^ i * (sec7_ra_A1Scale i * (a : ℝ) * d ^ 2 / (P.X * d ^ i)) := by
            exact mul_le_mul_of_nonneg_left hA1 (pow_nonneg hDpos.le i)
      _ = sec7_ra_A1Scale i * (a : ℝ) * d ^ 2 / P.X * (S.D ^ i / d ^ i) := by
            field_simp [P.X_pos.ne', pow_ne_zero i hdpos.ne']
      _ ≤ sec7_ra_A1Scale i * (a : ℝ) * d ^ 2 / P.X * 20 ^ i := by
            have hcoef_nonneg : 0 ≤ sec7_ra_A1Scale i * (a : ℝ) * d ^ 2 / P.X := by
              exact div_nonneg
                (mul_nonneg (mul_nonneg hscale_nonneg haR.le) (pow_nonneg hdpos.le 2))
                P.X_pos.le
            exact mul_le_mul_of_nonneg_left hcancel hcoef_nonneg
      _ ≤ sec7_ra_A1Scale i * (2 * S.A) * (40 * S.D) ^ 2 / P.X * 20 ^ i := by
            gcongr
            exact P.X_pos.le
      _ = (sec7_ra_A1Scale i * 2 * 40 ^ 2 * 20 ^ i) * (S.A * S.D ^ 2 / P.X) := by
            ring
      _ ≤ (10 ^ 13 : ℝ) * (S.A * S.D ^ 2 / P.X) := by
            have hconst : sec7_ra_A1Scale i * 2 * 40 ^ 2 * 20 ^ i ≤ (10 ^ 13 : ℝ) := by
              interval_cases i <;> norm_num [sec7_ra_A1Scale]
            have hbase_nonneg : 0 ≤ S.A * S.D ^ 2 / P.X := by
              exact div_nonneg (mul_nonneg hApos.le (pow_nonneg hDpos.le 2)) P.X_pos.le
            exact mul_le_mul_of_nonneg_right hconst hbase_nonneg
      _ = (10 ^ 13 : ℝ) * (S.T₁ * (S.Ω / P.H) ^ 2) := by
            rw [sec7_ra_A_Dsq_div_X_eq_T₁_ΩH_sq]
  have hU1 : (1 : ℝ) ≤ P.U := by
    unfold Globals.U
    exact Real.one_le_rpow hsd.hX hu0.le
  have hΩH0 : 0 ≤ S.Ω / P.H := div_nonneg S.Ω_pos.le P.H_pos.le
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hrelF0 : 0 ≤ sec7_relErrF P S := (sec7_relErrF_pos P S).le
  have hΩH_le_rel : S.Ω / P.H ≤ sec7_relErr P S := by
    have hU3 : (1 : ℝ) ≤ P.U ^ 3 := one_le_pow₀ hU1
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
  have hrel_le_relF : sec7_relErr P S ≤ sec7_relErrF P S := by
    have hGU : (1 : ℝ) ≤ sec7_cGU P S := by
      unfold sec7_cGU
      have hU2 : (1 : ℝ) ≤ P.U ^ 2 := one_le_pow₀ hU1
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ P.G * P.U ^ 2 := mul_le_mul hG1 hU2 zero_le_one P.G_pos.le
    unfold sec7_relErrF
    calc
      sec7_relErr P S = sec7_relErr P S * 1 := by ring
      _ ≤ sec7_relErr P S * sec7_cGU P S := mul_le_mul_of_nonneg_left hGU hrel0
  have hsq :
      (S.Ω / P.H) ^ 2 ≤ (1 / (10 : ℝ) ^ 143) * sec7_relErrF P S := by
    calc
      (S.Ω / P.H) ^ 2 = (S.Ω / P.H) * (S.Ω / P.H) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 143) * (S.Ω / P.H) :=
          mul_le_mul hΩH_small le_rfl hΩH0 (by positivity)
      _ ≤ (1 / (10 : ℝ) ^ 143) * sec7_relErr P S := by
          exact mul_le_mul_of_nonneg_left hΩH_le_rel (by positivity)
      _ ≤ (1 / (10 : ℝ) ^ 143) * sec7_relErrF P S := by
          exact mul_le_mul_of_nonneg_left hrel_le_relF (by positivity)
  have hfinish :
      (10 ^ 13 : ℝ) * (S.T₁ * (S.Ω / P.H) ^ 2)
        ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
    calc
      (10 ^ 13 : ℝ) * (S.T₁ * (S.Ω / P.H) ^ 2)
          ≤ (10 ^ 13 : ℝ) * (S.T₁ * ((1 / (10 : ℝ) ^ 143) * sec7_relErrF P S)) := by
            gcongr
      _ = ((10 ^ 13 : ℝ) * (1 / (10 : ℝ) ^ 143)) * (S.T₁ * sec7_relErrF P S) := by ring
      _ ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
            exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hT1pos.le hrelF0)
  calc
    S.D ^ i *
        |iteratedDeriv i
          (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t) -
            t ^ 2 * (t + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ)))
          (dtilde P.X r (a : ℝ))|
        = S.D ^ i *
          |iteratedDeriv i
            (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t) -
              t ^ 2 * (t + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d| := by
            rw [hd_def]
    _ ≤ (10 ^ 13 : ℝ) * (S.T₁ * (S.Ω / P.H) ^ 2) := hraw
    _ ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := hfinish

private theorem sec7_ra_rho3_A_rescaled_bound_sharp {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu) (hu0 : 0 < P.u)
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    S.D ^ i *
        |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ))))
          (dtilde P.X r (a : ℝ))|
      ≤ (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  have htWin : sec7_phase_ftil P S a r ∈ sec7_tWin S := by
    have hFpos : 0 < S.F := sec7_phase_F_pos S
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hdb_eq : dBreve P.X (a : ℝ) (sec7_phase_ftil P S a r) = d := by
    simpa [d, hd_def, sec7_phase_ftil] using dBreve_spec P.X_pos haR hdpos
  obtain ⟨_himg, hdlo16_raw, _hdhi30_raw⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ))
      (t := sec7_phase_ftil P S a r) hAD (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) htWin
  have hdlo16 : S.D / 16 ≤ d := by
    simpa [hdb_eq] using hdlo16_raw
  have hA3 :=
    sec7_ra_A3_bound_public (a := (a : ℝ)) (d := d) (d_lo := S.D / 16)
      (k := i) hi haR (by positivity) hdlo16
  have hcancel := sec7_ra_rpow_neg_cancel_unit (D := S.D) (d := d) (i := i)
    hDpos hdlo16
  have hmain :
      S.D ^ i *
          |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ)))) d|
        ≤ (7 * 10 ^ 7 : ℝ) * S.A := by
    calc
      S.D ^ i *
          |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ)))) d|
          ≤ S.D ^ i * ((30 : ℝ) * (a : ℝ) * d ^ (-(i : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = (30 : ℝ) * (a : ℝ) * (S.D ^ i * d ^ (-(i : ℝ))) := by ring
      _ ≤ (30 : ℝ) * (a : ℝ) * 16 ^ i := by
            exact mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ ≤ (30 : ℝ) * (2 * S.A) * 16 ^ i := by
            gcongr
      _ ≤ (7 * 10 ^ 7 : ℝ) * S.A := by
            have hconst : (30 : ℝ) * (2 : ℝ) * 16 ^ i ≤ 7 * 10 ^ 7 := by
              interval_cases i <;> norm_num
            calc
              (30 : ℝ) * (2 * S.A) * 16 ^ i =
                  ((30 : ℝ) * (2 : ℝ) * 16 ^ i) * S.A := by ring
              _ ≤ (7 * 10 ^ 7 : ℝ) * S.A :=
                  mul_le_mul_of_nonneg_right hconst hApos.le
  have hU1 : (1 : ℝ) ≤ P.U := by
    unfold Globals.U
    exact Real.one_le_rpow hsd.hX hu0.le
  have hGU : (1 : ℝ) ≤ P.G * P.U ^ 5 := by
    have hU5 : (1 : ℝ) ≤ P.U ^ 5 := one_le_pow₀ hU1
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P.G * P.U ^ 5 := mul_le_mul hG1 hU5 zero_le_one P.G_pos.le
  have hA_le : S.A ≤ S.A * P.G * P.U ^ 5 := by
    calc
      S.A = S.A * 1 := by ring
      _ ≤ S.A * (P.G * P.U ^ 5) := mul_le_mul_of_nonneg_left hGU hApos.le
      _ = S.A * P.G * P.U ^ 5 := by ring
  calc
    S.D ^ i *
        |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ))))
          (dtilde P.X r (a : ℝ))|
        = S.D ^ i *
          |iteratedDeriv i (fun t : ℝ => t - Real.sqrt (t * (t + (a : ℝ)))) d| := by
            rw [hd_def]
    _ ≤ (7 * 10 ^ 7 : ℝ) * S.A := hmain
    _ ≤ (7 * 10 ^ 7 : ℝ) * (S.A * P.G * P.U ^ 5) :=
          mul_le_mul_of_nonneg_left hA_le (by positivity)
    _ = (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
          rw [sec7_ra_T₃_relErrF_eq_A_G_U5]

private theorem sec7_ra_B3_close_scale {P : Globals} {S : Scale P} {W : ℝ}
    {a d : ℝ} {j : ℤ} (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (ha_lo : S.A ≤ a) (hd0 : 0 ≤ d)
    (hd_hi : d ≤ 30 * S.D) :
    (10 ^ 20 : ℝ) * |(j : ℝ)| * d ^ 3 / (P.X * a) ≤ 1 / 100 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hapos : 0 < a := lt_of_lt_of_le hApos ha_lo
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have hDpos : 0 < S.D := S.D_pos
  have hden_le : P.X * S.A ≤ P.X * a :=
    mul_le_mul_of_nonneg_left ha_lo P.X_pos.le
  have hinv_den : (P.X * a)⁻¹ ≤ (P.X * S.A)⁻¹ :=
    inv_anti₀ (mul_pos P.X_pos hApos) hden_le
  have hd3 : d ^ 3 ≤ (30 * S.D) ^ 3 :=
    pow_le_pow_left₀ hd0 hd_hi 3
  have hfrac : d ^ 3 / (P.X * a) ≤ 30 ^ 3 / S.F := by
    calc
      d ^ 3 / (P.X * a) = d ^ 3 * (P.X * a)⁻¹ := by ring
      _ ≤ d ^ 3 * (P.X * S.A)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv_den (pow_nonneg hd0 3)
      _ ≤ (30 * S.D) ^ 3 * (P.X * S.A)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hd3 (inv_nonneg.mpr (mul_pos P.X_pos hApos).le)
      _ = 30 ^ 3 * (S.D ^ 3 / (P.X * S.A)) := by ring
      _ = 30 ^ 3 / S.F := by
            rw [sec7_ra_D_cubed_div_XA_eq_invF]
            ring
  have hj_abs : |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := by
    rw [← Int.cast_abs]
    simpa [sec7_jBand] using hj
  have hj_split : |(j : ℝ)| ≤ sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := by
    calc
      |(j : ℝ)| ≤ sec7_cJ * (1 + P.H / S.A ^ 2) := hj_abs
      _ = sec7_cJ + sec7_cJ * (P.H / S.A ^ 2) := by ring
  have hFlarge := sec7_phase_F_large_const (P := P) (S := S) (W := W) Env hW
  have hHA2large := sec7_phase_HA2_large (P := P) (S := S) (W := W)
    Env hW c₀ Cu hsd
  have hten100 : 0 < (10 : ℝ) ^ 100 := by positivity
  have hratio1 : sec7_cJ / S.F ≤ 1 / (10 : ℝ) ^ 100 := by
    rw [div_le_iff₀ hFpos]
    have hCJ : (10 : ℝ) ^ 100 * sec7_cJ ≤ S.F := by
      calc
        (10 : ℝ) ^ 100 * sec7_cJ
            ≤ (10 : ℝ) ^ 100 * (sec7_cJ + 1) := by
              gcongr
              norm_num
        _ ≤ S.F := hFlarge
    have hscale :
        sec7_cJ = ((10 : ℝ) ^ 100)⁻¹ * ((10 : ℝ) ^ 100 * sec7_cJ) := by
      field_simp [ne_of_gt hten100]
    rw [hscale]
    simpa [one_div] using
      mul_le_mul_of_nonneg_left hCJ (inv_nonneg.mpr hten100.le)
  have hratio2 : (sec7_cJ * (P.H / S.A ^ 2)) / S.F ≤ 1 / (10 : ℝ) ^ 100 := by
    rw [div_le_iff₀ hFpos]
    have hCJH :
        (10 : ℝ) ^ 100 * (sec7_cJ * (P.H / S.A ^ 2)) ≤ S.F := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hHA2large
    have hscale :
        sec7_cJ * (P.H / S.A ^ 2) =
          ((10 : ℝ) ^ 100)⁻¹ * ((10 : ℝ) ^ 100 *
            (sec7_cJ * (P.H / S.A ^ 2))) := by
      field_simp [ne_of_gt hten100]
    rw [hscale]
    simpa [one_div] using
      mul_le_mul_of_nonneg_left hCJH (inv_nonneg.mpr hten100.le)
  have hsum :
      (sec7_cJ + sec7_cJ * (P.H / S.A ^ 2)) / S.F ≤
        2 / (10 : ℝ) ^ 100 := by
    calc
      (sec7_cJ + sec7_cJ * (P.H / S.A ^ 2)) / S.F =
          sec7_cJ / S.F + (sec7_cJ * (P.H / S.A ^ 2)) / S.F := by ring
      _ ≤ 1 / (10 : ℝ) ^ 100 + 1 / (10 : ℝ) ^ 100 :=
            add_le_add hratio1 hratio2
      _ = 2 / (10 : ℝ) ^ 100 := by ring
  calc
    (10 ^ 20 : ℝ) * |(j : ℝ)| * d ^ 3 / (P.X * a)
        = (10 ^ 20 : ℝ) * |(j : ℝ)| * (d ^ 3 / (P.X * a)) := by ring
    _ ≤ (10 ^ 20 : ℝ) * |(j : ℝ)| * (30 ^ 3 / S.F) := by
          gcongr
    _ ≤ (10 ^ 20 : ℝ) *
          (sec7_cJ + sec7_cJ * (P.H / S.A ^ 2)) * (30 ^ 3 / S.F) := by
          gcongr
    _ = (10 ^ 20 : ℝ) * 30 ^ 3 *
          ((sec7_cJ + sec7_cJ * (P.H / S.A ^ 2)) / S.F) := by ring
    _ ≤ (10 ^ 20 : ℝ) * 30 ^ 3 * (2 / (10 : ℝ) ^ 100) := by
          gcongr
    _ ≤ 1 / 100 := by norm_num

private theorem sec7_ra_B3_dtilde_close {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) :
    |dBreve P.X (a : ℝ)
        (Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ)) + (j : ℝ))
      - dtilde P.X r (a : ℝ)| ≤ dtilde P.X r (a : ℝ) / 100 := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have htWin : sec7_phase_ftil P S a r ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin]
      nlinarith
    · rw [sec7_cWin]
      nlinarith
  have hdb_eq : dBreve P.X (a : ℝ) (sec7_phase_ftil P S a r) = d := by
    simpa [d, hd_def, sec7_phase_ftil] using dBreve_spec P.X_pos haR hdpos
  obtain ⟨_himg, hdlo16_raw, hdhi30_raw⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ))
      (t := sec7_phase_ftil P S a r) hAD (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) htWin
  have hdlo16 : S.D / 16 ≤ d := by
    simpa [hdb_eq] using hdlo16_raw
  have hdhi30 : d ≤ 30 * S.D := by
    simpa [hdb_eq] using hdhi30_raw
  have hpert0 :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hseg : ∀ s ∈ Set.uIcc (0 : ℝ) (j : ℝ),
      Ffun P.X (a : ℝ) d + s ∈ sec7_tWin S := by
    intro s hs
    have hsabs : |s| ≤ |(j : ℝ)| := by
      have h := Set.abs_sub_left_of_mem_uIcc hs
      simpa using h
    have hsF : |s| ≤ S.F / 1000 := le_trans hsabs hjF
    have hslo : -(S.F / 1000) ≤ s := by
      have h := neg_abs_le s
      nlinarith
    have hshi : s ≤ S.F / 1000 := by
      have h := le_abs_self s
      nlinarith
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      nlinarith
    · rw [sec7_cWin, hFd]
      nlinarith
  have hb0 :=
    sec7_ra_B3_bound_k0_public (P := P) (S := S) (a := (a : ℝ)) (d := d)
      (j := (j : ℝ)) hAD (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) hdlo16 hseg
  have hsmall1 :=
    sec7_ra_B3_close_scale (P := P) (S := S) (W := W) (a := (a : ℝ))
      (d := d) (j := j) Env hW c₀ Cu hsd hj ha_lo hdpos.le hdhi30
  have hsmall :
      (10 ^ 20 : ℝ) * |(j : ℝ)| * d ^ 4 / (P.X * (a : ℝ)) ≤ d / 100 := by
    calc
      (10 ^ 20 : ℝ) * |(j : ℝ)| * d ^ 4 / (P.X * (a : ℝ))
          = ((10 ^ 20 : ℝ) * |(j : ℝ)| * d ^ 3 /
              (P.X * (a : ℝ))) * d := by ring
      _ ≤ (1 / 100 : ℝ) * d :=
            mul_le_mul_of_nonneg_right hsmall1 hdpos.le
      _ = d / 100 := by ring
  have hmain := le_trans hb0 hsmall
  simpa [d, hd_def, iteratedDeriv_zero] using hmain

private theorem sec7_ra_rho3_B_rescaled_prebound {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    S.D ^ i *
        |iteratedDeriv i
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          (dtilde P.X r (a : ℝ))|
      ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have hdenpos : 0 < P.X * (a : ℝ) := mul_pos P.X_pos haR
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hdlo20, hd_ge_a, hdhi40⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hdpos : 0 < d := by
    exact lt_of_lt_of_le (by positivity : 0 < S.D / 20) (by simpa [d, hd_def] using hdlo20)
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hpert0 :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hshift : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
        have h := neg_abs_le (j : ℝ)
        nlinarith
      nlinarith
    · rw [sec7_cWin, hFd]
      have hjhi : (j : ℝ) ≤ S.F / 1000 := by
        have h := le_abs_self (j : ℝ)
        nlinarith
      nlinarith
  have hclose :
      |dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) d + (j : ℝ)) - d| ≤ d / 100 := by
    simpa [d, hd_def] using
      sec7_ra_B3_dtilde_close (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj hr
  have hb :=
    sec7_ra_B3_bound_sharp_aled (P := P) (S := S) (a := (a : ℝ)) (d := d)
      (j := (j : ℝ)) (k := i) hi hAD (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) hdpos (by simpa [d, hd_def] using hd_ge_a)
      hshift hclose
  have hD4scale :
      S.D ^ 4 / (P.X * (a : ℝ)) ≤ S.T₃ / S.F :=
    sec7_ra_D_fourth_div_Xa_le_T₃_div_F (P := P) (S := S) (a := (a : ℝ)) ha_lo
  have hscaled_nonneg : 0 ≤ (|(j : ℝ)| / S.F) * S.T₃ := by
    exact mul_nonneg (div_nonneg (abs_nonneg _) hFpos.le) (sec7_T₃_pos S).le
  have hfinish : ∀ {C : ℝ}, C ≤ 7 * 10 ^ 11 →
      C * (|(j : ℝ)| / S.F) * S.T₃
        ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by
    intro C hC
    calc
      C * (|(j : ℝ)| / S.F) * S.T₃ =
          C * ((|(j : ℝ)| / S.F) * S.T₃) := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * ((|(j : ℝ)| / S.F) * S.T₃) :=
          mul_le_mul_of_nonneg_right hC hscaled_nonneg
      _ = (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
  interval_cases i
  · have hb0 :
        |iteratedDeriv 0
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          d| ≤ 2 * |(j : ℝ)| * d ^ 4 / (P.X * (a : ℝ)) := by
      simpa using hb
    have hd4 : d ^ 4 ≤ (40 * S.D) ^ 4 :=
      pow_le_pow_left₀ hdpos.le (by simpa [d, hd_def] using hdhi40) 4
    calc
      S.D ^ 0 *
          |iteratedDeriv 0
            (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
            (dtilde P.X r (a : ℝ))|
          ≤ S.D ^ 0 * (2 * |(j : ℝ)| * d ^ 4 / (P.X * (a : ℝ))) := by
            simpa [d, hd_def] using hb0
      _ = 2 * |(j : ℝ)| * d ^ 4 / (P.X * (a : ℝ)) := by ring
      _ ≤ (2 * 40 ^ 4) * |(j : ℝ)| * S.D ^ 4 / (P.X * (a : ℝ)) := by
            have hnum :
                2 * |(j : ℝ)| * d ^ 4 ≤ (2 * 40 ^ 4) * |(j : ℝ)| * S.D ^ 4 := by
              calc
                2 * |(j : ℝ)| * d ^ 4 ≤ 2 * |(j : ℝ)| * (40 * S.D) ^ 4 := by gcongr
                _ = (2 * 40 ^ 4) * |(j : ℝ)| * S.D ^ 4 := by ring
            exact div_le_div_of_nonneg_right hnum hdenpos.le
      _ = (2 * 40 ^ 4) * |(j : ℝ)| * (S.D ^ 4 / (P.X * (a : ℝ))) := by ring
      _ ≤ (2 * 40 ^ 4) * |(j : ℝ)| * (S.T₃ / S.F) := by
            exact mul_le_mul_of_nonneg_left hD4scale (by positivity)
      _ = (2 * 40 ^ 4) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ :=
            hfinish (by norm_num)
  · have hb1 :
        |iteratedDeriv 1
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          d| ≤ 120 * |(j : ℝ)| * d ^ 3 / (P.X * (a : ℝ)) := by
      simpa using hb
    have hD_d3 : S.D * d ^ 3 ≤ 40 ^ 3 * S.D ^ 4 := by
      calc
        S.D * d ^ 3 ≤ S.D * (40 * S.D) ^ 3 := by gcongr
        _ = 40 ^ 3 * S.D ^ 4 := by ring
    calc
      S.D ^ 1 *
          |iteratedDeriv 1
            (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
            (dtilde P.X r (a : ℝ))|
          ≤ S.D ^ 1 * (120 * |(j : ℝ)| * d ^ 3 / (P.X * (a : ℝ))) := by
            simpa [d, hd_def] using mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = 120 * |(j : ℝ)| * (S.D * d ^ 3) / (P.X * (a : ℝ)) := by ring
      _ ≤ (120 * 40 ^ 3) * |(j : ℝ)| * S.D ^ 4 / (P.X * (a : ℝ)) := by
            have hnum :
                120 * |(j : ℝ)| * (S.D * d ^ 3) ≤
                  (120 * 40 ^ 3) * |(j : ℝ)| * S.D ^ 4 := by
              calc
                120 * |(j : ℝ)| * (S.D * d ^ 3) ≤
                    120 * |(j : ℝ)| * (40 ^ 3 * S.D ^ 4) := by gcongr
                _ = (120 * 40 ^ 3) * |(j : ℝ)| * S.D ^ 4 := by ring
            exact div_le_div_of_nonneg_right hnum hdenpos.le
      _ = (120 * 40 ^ 3) * |(j : ℝ)| * (S.D ^ 4 / (P.X * (a : ℝ))) := by ring
      _ ≤ (120 * 40 ^ 3) * |(j : ℝ)| * (S.T₃ / S.F) := by
            exact mul_le_mul_of_nonneg_left hD4scale (by positivity)
      _ = (120 * 40 ^ 3) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ :=
            hfinish (by norm_num)
  · have hb2 :
        |iteratedDeriv 2
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          d| ≤ 17600 * |(j : ℝ)| * d ^ 2 / (P.X * (a : ℝ)) := by
      simpa using hb
    have hD2_d2 : S.D ^ 2 * d ^ 2 ≤ 40 ^ 2 * S.D ^ 4 := by
      calc
        S.D ^ 2 * d ^ 2 ≤ S.D ^ 2 * (40 * S.D) ^ 2 := by gcongr
        _ = 40 ^ 2 * S.D ^ 4 := by ring
    calc
      S.D ^ 2 *
          |iteratedDeriv 2
            (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
            (dtilde P.X r (a : ℝ))|
          ≤ S.D ^ 2 * (17600 * |(j : ℝ)| * d ^ 2 / (P.X * (a : ℝ))) := by
            simpa [d, hd_def] using mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = 17600 * |(j : ℝ)| * (S.D ^ 2 * d ^ 2) / (P.X * (a : ℝ)) := by ring
      _ ≤ (17600 * 40 ^ 2) * |(j : ℝ)| * S.D ^ 4 / (P.X * (a : ℝ)) := by
            have hnum :
                17600 * |(j : ℝ)| * (S.D ^ 2 * d ^ 2) ≤
                  (17600 * 40 ^ 2) * |(j : ℝ)| * S.D ^ 4 := by
              calc
                17600 * |(j : ℝ)| * (S.D ^ 2 * d ^ 2) ≤
                    17600 * |(j : ℝ)| * (40 ^ 2 * S.D ^ 4) := by gcongr
                _ = (17600 * 40 ^ 2) * |(j : ℝ)| * S.D ^ 4 := by ring
            exact div_le_div_of_nonneg_right hnum hdenpos.le
      _ = (17600 * 40 ^ 2) * |(j : ℝ)| * (S.D ^ 4 / (P.X * (a : ℝ))) := by ring
      _ ≤ (17600 * 40 ^ 2) * |(j : ℝ)| * (S.T₃ / S.F) := by
            exact mul_le_mul_of_nonneg_left hD4scale (by positivity)
      _ = (17600 * 40 ^ 2) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ :=
            hfinish (by norm_num)
  · have hb3 :
        |iteratedDeriv 3
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          d| ≤ 1176600 * |(j : ℝ)| * d / (P.X * (a : ℝ)) := by
      simpa using hb
    have hD3_d : S.D ^ 3 * d ≤ 40 * S.D ^ 4 := by
      calc
        S.D ^ 3 * d ≤ S.D ^ 3 * (40 * S.D) := by gcongr
        _ = 40 * S.D ^ 4 := by ring
    calc
      S.D ^ 3 *
          |iteratedDeriv 3
            (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
            (dtilde P.X r (a : ℝ))|
          ≤ S.D ^ 3 * (1176600 * |(j : ℝ)| * d / (P.X * (a : ℝ))) := by
            simpa [d, hd_def] using mul_le_mul_of_nonneg_left hb3 (by positivity)
      _ = 1176600 * |(j : ℝ)| * (S.D ^ 3 * d) / (P.X * (a : ℝ)) := by ring
      _ ≤ (1176600 * 40) * |(j : ℝ)| * S.D ^ 4 / (P.X * (a : ℝ)) := by
            have hnum :
                1176600 * |(j : ℝ)| * (S.D ^ 3 * d) ≤
                  (1176600 * 40) * |(j : ℝ)| * S.D ^ 4 := by
              calc
                1176600 * |(j : ℝ)| * (S.D ^ 3 * d) ≤
                    1176600 * |(j : ℝ)| * (40 * S.D ^ 4) := by gcongr
                _ = (1176600 * 40) * |(j : ℝ)| * S.D ^ 4 := by ring
            exact div_le_div_of_nonneg_right hnum hdenpos.le
      _ = (1176600 * 40) * |(j : ℝ)| * (S.D ^ 4 / (P.X * (a : ℝ))) := by ring
      _ ≤ (1176600 * 40) * |(j : ℝ)| * (S.T₃ / S.F) := by
            exact mul_le_mul_of_nonneg_left hD4scale (by positivity)
      _ = (1176600 * 40) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ :=
            hfinish (by norm_num)
  · have hb4 :
        |iteratedDeriv 4
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          d| ≤ 144344400 * |(j : ℝ)| / (P.X * (a : ℝ)) := by
      simpa using hb
    calc
      S.D ^ 4 *
          |iteratedDeriv 4
            (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
            (dtilde P.X r (a : ℝ))|
          ≤ S.D ^ 4 * (144344400 * |(j : ℝ)| / (P.X * (a : ℝ))) := by
            simpa [d, hd_def] using mul_le_mul_of_nonneg_left hb4 (by positivity)
      _ = 144344400 * |(j : ℝ)| * (S.D ^ 4 / (P.X * (a : ℝ))) := by ring
      _ ≤ 144344400 * |(j : ℝ)| * (S.T₃ / S.F) := by
            exact mul_le_mul_of_nonneg_left hD4scale (by positivity)
      _ = 144344400 * (|(j : ℝ)| / S.F) * S.T₃ := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ :=
            hfinish (by norm_num)
  · have hb5 :
        |iteratedDeriv 5
          (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
          d| ≤ 30084656000 * |(j : ℝ)| / (d * (P.X * (a : ℝ))) := by
      simpa using hb
    have hDle : S.D ≤ 20 * d := by nlinarith [hdlo20]
    have hD5le : S.D ^ 5 ≤ (20 * S.D ^ 4) * d := by
      calc
        S.D ^ 5 = S.D ^ 4 * S.D := by ring
        _ ≤ S.D ^ 4 * (20 * d) := by gcongr
        _ = (20 * S.D ^ 4) * d := by ring
    have hD5div : S.D ^ 5 / d ≤ 20 * S.D ^ 4 := by
      rw [div_le_iff₀ hdpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hD5le
    calc
      S.D ^ 5 *
          |iteratedDeriv 5
            (fun t : ℝ => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t)
            (dtilde P.X r (a : ℝ))|
          ≤ S.D ^ 5 * (30084656000 * |(j : ℝ)| / (d * (P.X * (a : ℝ)))) := by
            simpa [d, hd_def] using mul_le_mul_of_nonneg_left hb5 (by positivity)
      _ = 30084656000 * |(j : ℝ)| * (S.D ^ 5 / d) / (P.X * (a : ℝ)) := by
            field_simp [hdpos.ne', hdenpos.ne']
      _ ≤ (30084656000 * 20) * |(j : ℝ)| * S.D ^ 4 / (P.X * (a : ℝ)) := by
            have hnum :
                30084656000 * |(j : ℝ)| * (S.D ^ 5 / d) ≤
                  (30084656000 * 20) * |(j : ℝ)| * S.D ^ 4 := by
              calc
                30084656000 * |(j : ℝ)| * (S.D ^ 5 / d) ≤
                    30084656000 * |(j : ℝ)| * (20 * S.D ^ 4) := by gcongr
                _ = (30084656000 * 20) * |(j : ℝ)| * S.D ^ 4 := by ring
            exact div_le_div_of_nonneg_right hnum hdenpos.le
      _ = (30084656000 * 20) * |(j : ℝ)| * (S.D ^ 4 / (P.X * (a : ℝ))) := by ring
      _ ≤ (30084656000 * 20) * |(j : ℝ)| * (S.T₃ / S.F) := by
            exact mul_le_mul_of_nonneg_left hD4scale (by positivity)
      _ = (30084656000 * 20) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ :=
            hfinish (by norm_num)

private theorem sec7_ra_rho1_B_rescaled_prebound {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    {c₀ Cu : ℝ} (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    S.D ^ i *
        |iteratedDeriv i
          (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) +
            dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t))
          (dtilde P.X r (a : ℝ))|
      ≤ (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := sec7_phase_F_pos S
  have hdenpos : 0 < (P.X * (a : ℝ)) ^ 2 := pow_pos (mul_pos P.X_pos haR) 2
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  obtain ⟨hdlo20, hd_ge_a, hdhi40⟩ :=
    sec7_ra_dtilde_wide_image (P := P) (S := S) (W := W) (a := a) (r := r)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hdpos : 0 < d :=
    lt_of_lt_of_le (by positivity : 0 < S.D / 20) (by simpa [d, hd_def] using hdlo20)
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hpert0 :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hshift : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
        have h := neg_abs_le (j : ℝ)
        nlinarith
      nlinarith
    · rw [sec7_cWin, hFd]
      have hjhi : (j : ℝ) ≤ S.F / 1000 := by
        have h := le_abs_self (j : ℝ)
        nlinarith
      nlinarith
  have hclose :
      |dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) d + (j : ℝ)) - d| ≤ d / 100 := by
    simpa [d, hd_def] using
      sec7_ra_B3_dtilde_close (P := P) (S := S) (W := W) (a := a) (j := j)
        (r := r) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj hr
  have hb :=
    sec7_ra_B1_bound_sharp_aled (P := P) (S := S) (a := (a : ℝ)) (d := d)
      (j := (j : ℝ)) (k := i) hi hAD (sec7_phase_a_lo_wide ha_lo)
      (sec7_phase_a_hi_wide ha_hi) hdpos (by simpa [d, hd_def] using hd_ge_a)
      hshift hclose
  have hC_nonneg : 0 ≤ sec7_ra_B1ComposeScale i := by
    interval_cases i <;> norm_num [sec7_ra_B1ComposeScale]
  have hbC :
      |iteratedDeriv i
          (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) +
            dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t)) d|
        ≤ sec7_ra_B1ComposeScale i * |(j : ℝ)| * d ^ (7 - i) /
          (P.X * (a : ℝ)) ^ 2 := by
    interval_cases i <;> simpa [sec7_ra_B1ComposeScale] using hb
  have hdhi : d ≤ 40 * S.D := by
    simpa [d, hd_def] using hdhi40
  have hDpow : S.D ^ i * d ^ (7 - i) ≤ 40 ^ (7 - i) * S.D ^ 7 := by
    interval_cases i
    · calc
        S.D ^ 0 * d ^ (7 - 0) = d ^ 7 := by ring
        _ ≤ (40 * S.D) ^ 7 := pow_le_pow_left₀ hdpos.le hdhi 7
        _ = 40 ^ (7 - 0) * S.D ^ 7 := by ring
    · calc
        S.D ^ 1 * d ^ (7 - 1) = S.D * d ^ 6 := by ring
        _ ≤ S.D * (40 * S.D) ^ 6 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdpos.le hdhi 6) hDpos.le
        _ = 40 ^ (7 - 1) * S.D ^ 7 := by ring
    · calc
        S.D ^ 2 * d ^ (7 - 2) = S.D ^ 2 * d ^ 5 := by ring
        _ ≤ S.D ^ 2 * (40 * S.D) ^ 5 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdpos.le hdhi 5)
            (pow_nonneg hDpos.le 2)
        _ = 40 ^ (7 - 2) * S.D ^ 7 := by ring
    · calc
        S.D ^ 3 * d ^ (7 - 3) = S.D ^ 3 * d ^ 4 := by ring
        _ ≤ S.D ^ 3 * (40 * S.D) ^ 4 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdpos.le hdhi 4)
            (pow_nonneg hDpos.le 3)
        _ = 40 ^ (7 - 3) * S.D ^ 7 := by ring
    · calc
        S.D ^ 4 * d ^ (7 - 4) = S.D ^ 4 * d ^ 3 := by ring
        _ ≤ S.D ^ 4 * (40 * S.D) ^ 3 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdpos.le hdhi 3)
            (pow_nonneg hDpos.le 4)
        _ = 40 ^ (7 - 4) * S.D ^ 7 := by ring
    · calc
        S.D ^ 5 * d ^ (7 - 5) = S.D ^ 5 * d ^ 2 := by ring
        _ ≤ S.D ^ 5 * (40 * S.D) ^ 2 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdpos.le hdhi 2)
            (pow_nonneg hDpos.le 5)
        _ = 40 ^ (7 - 5) * S.D ^ 7 := by ring
  have hD7scale :
      S.D ^ 7 / (P.X * (a : ℝ)) ^ 2 ≤ S.T₁ / S.F :=
    sec7_ra_D_seventh_div_Xa_sq_le_T₁_div_F (P := P) (S := S) (a := (a : ℝ)) ha_lo
  have hscaled_nonneg : 0 ≤ (|(j : ℝ)| / S.F) * S.T₁ := by
    exact mul_nonneg (div_nonneg (abs_nonneg _) hFpos.le) (sec7_T₁_pos S).le
  have hfinish : sec7_ra_B1ComposeScale i * 40 ^ (7 - i) *
        (|(j : ℝ)| / S.F) * S.T₁
      ≤ (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by
    have hCscale :
        sec7_ra_B1ComposeScale i * 40 ^ (7 - i) ≤ (8 * 10 ^ 15 : ℝ) := by
      interval_cases i <;> norm_num [sec7_ra_B1ComposeScale]
    calc
      sec7_ra_B1ComposeScale i * 40 ^ (7 - i) * (|(j : ℝ)| / S.F) * S.T₁ =
          (sec7_ra_B1ComposeScale i * 40 ^ (7 - i)) *
            ((|(j : ℝ)| / S.F) * S.T₁) := by ring
      _ ≤ (8 * 10 ^ 15 : ℝ) * ((|(j : ℝ)| / S.F) * S.T₁) :=
          mul_le_mul_of_nonneg_right hCscale hscaled_nonneg
      _ = (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by ring
  calc
    S.D ^ i *
        |iteratedDeriv i
          (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) +
            dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t))
          (dtilde P.X r (a : ℝ))|
        = S.D ^ i *
          |iteratedDeriv i
            (fun t : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) +
              dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t)) d| := by
          rw [hd_def]
    _ ≤ S.D ^ i * (sec7_ra_B1ComposeScale i * |(j : ℝ)| * d ^ (7 - i) /
          (P.X * (a : ℝ)) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hbC (pow_nonneg hDpos.le i)
    _ = sec7_ra_B1ComposeScale i * |(j : ℝ)| * (S.D ^ i * d ^ (7 - i)) /
          (P.X * (a : ℝ)) ^ 2 := by ring
    _ ≤ (sec7_ra_B1ComposeScale i * 40 ^ (7 - i)) * |(j : ℝ)| * S.D ^ 7 /
          (P.X * (a : ℝ)) ^ 2 := by
          have hnum :
              sec7_ra_B1ComposeScale i * |(j : ℝ)| * (S.D ^ i * d ^ (7 - i)) ≤
                (sec7_ra_B1ComposeScale i * 40 ^ (7 - i)) *
                  |(j : ℝ)| * S.D ^ 7 := by
            calc
              sec7_ra_B1ComposeScale i * |(j : ℝ)| * (S.D ^ i * d ^ (7 - i))
                  ≤ sec7_ra_B1ComposeScale i * |(j : ℝ)| *
                    (40 ^ (7 - i) * S.D ^ 7) := by
                    gcongr
              _ = (sec7_ra_B1ComposeScale i * 40 ^ (7 - i)) *
                    |(j : ℝ)| * S.D ^ 7 := by ring
          exact div_le_div_of_nonneg_right hnum hdenpos.le
    _ = (sec7_ra_B1ComposeScale i * 40 ^ (7 - i)) * |(j : ℝ)| *
          (S.D ^ 7 / (P.X * (a : ℝ)) ^ 2) := by ring
    _ ≤ (sec7_ra_B1ComposeScale i * 40 ^ (7 - i)) *
          |(j : ℝ)| * (S.T₁ / S.F) := by
          exact mul_le_mul_of_nonneg_left hD7scale
            (mul_nonneg (mul_nonneg hC_nonneg (pow_nonneg (by norm_num) (7 - i)))
              (abs_nonneg _))
    _ = sec7_ra_B1ComposeScale i * 40 ^ (7 - i) *
          (|(j : ℝ)| / S.F) * S.T₁ := by ring
    _ ≤ (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := hfinish

private theorem sec7_ra_rho3_rescaled_FDeriv_prebound {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hu0 : 0 < P.u)
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ))
        (dtilde P.X r (a : ℝ) / S.D)‖
      ≤ (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) +
          (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  set u : ℝ := d / S.D with hu_def
  have hSDu : S.D * u = d := by
    rw [hu_def]
    field_simp [ne_of_gt hDpos]
  have humem : u ∈ sec7_ra_rho3Target P S (a : ℝ) := by
    rw [hu_def]
    exact sec7_ra_ftilde_mapsTo_rho3Target (P := P) (S := S) (W := W) (a := a)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hdmem : S.D * u ∈ sec7_ra_rho3DTarget P S (a : ℝ) :=
    sec7_ra_rho3Target_mulD_mapsTo (P := P) (S := S) (a := (a : ℝ)) humem
  have hrho_on :
      ContDiffOn ℝ 5 (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ))
        (sec7_ra_rho3DTarget P S (a : ℝ)) :=
    sec7_ra_rho3_contDiffOn_DTarget (P := P) (S := S) (W := W)
      (a := a) (j := j) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj
  have hrho_at :
      ContDiffAt ℝ 5 (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) (S.D * u) := by
    simpa [hSDu, d, hd_def] using
      sec7_ra_rho3_contDiffAt_dtilde (P := P) (S := S) (W := W)
        (a := a) (j := j) (r := r) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj hr
  have hlin_cd : ContDiffAt ℝ 5 (fun y : ℝ => S.D * y) u :=
    contDiffAt_const.mul contDiffAt_id
  have hg_at : ContDiffAt ℝ 5
      (fun y : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * y)) u :=
    hrho_at.comp u hlin_cd
  have hwithin :
      iteratedDerivWithin i
          (fun y : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * y))
          (sec7_ra_rho3Target P S (a : ℝ)) u =
        iteratedDeriv i
          (fun y : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * y)) u :=
    iteratedDerivWithin_eq_iteratedDeriv
      (sec7_ra_rho3Target_uniqueDiffOn (P := P) (S := S) (a := (a : ℝ))
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi))
      (hg_at.of_le (by exact_mod_cast hi)) humem
  have hscale :
      iteratedDeriv i
          (fun y : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * y)) u =
        S.D ^ i * iteratedDeriv i (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) (S.D * u) :=
    sec7_iteratedDeriv_comp_const_mul_at5 (f := sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ))
      (x := u) (c := S.D) hi hrho_at
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hshift : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
        have h := neg_abs_le (j : ℝ)
        nlinarith
      nlinarith
    · rw [sec7_cWin, hFd]
      have hjhi : (j : ℝ) ≤ S.F / 1000 := by
        have h := le_abs_self (j : ℝ)
        nlinarith
      nlinarith
  set Bfun : ℝ → ℝ :=
    fun t => dBreve P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) - t
  set Afun : ℝ → ℝ := fun t => t - Real.sqrt (t * (t + (a : ℝ)))
  have hBcd : ContDiffAt ℝ i Bfun d := by
    set t₀ : ℝ := Ffun P.X (a : ℝ) d + (j : ℝ)
    obtain ⟨himg, _hlo, _hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t₀)
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
        (by simpa [t₀] using hshift)
    have hdb :=
      sec7_dBreve_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
        (d := dBreve P.X (a : ℝ) t₀) P.X_pos haR dBreve_pos
    have hdb_at : ContDiffAt ℝ 5 (dBreve P.X (a : ℝ)) t₀ := by
      simpa [himg] using hdb
    have hFbase : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y) d :=
      sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := d)
        (ne_of_gt hdpos) (by positivity)
    have harg : ContDiffAt ℝ 5
        (fun y : ℝ => Ffun P.X (a : ℝ) y + (j : ℝ)) d :=
      hFbase.add contDiffAt_const
    have hB : ContDiffAt ℝ 5
        (fun y : ℝ => dBreve P.X (a : ℝ)
          (Ffun P.X (a : ℝ) y + (j : ℝ)) - y) d := by
      exact (hdb_at.comp d harg).sub contDiffAt_id
    simpa [Bfun] using hB.of_le (by exact_mod_cast hi)
  have hAcd : ContDiffAt ℝ i Afun d := by
    have hrad : ContDiffAt ℝ 5 (fun y : ℝ => y * (y + (a : ℝ))) d :=
      contDiffAt_id.mul (contDiffAt_id.add contDiffAt_const)
    have hsqrt : ContDiffAt ℝ 5 (fun y : ℝ => Real.sqrt (y * (y + (a : ℝ)))) d := by
      refine ContDiffAt.sqrt hrad ?_
      positivity
    have hA : ContDiffAt ℝ 5 (fun y : ℝ => y - Real.sqrt (y * (y + (a : ℝ)))) d :=
      contDiffAt_id.sub hsqrt
    simpa [Afun] using hA.of_le (by exact_mod_cast hi)
  have hsplit :
      iteratedDeriv i (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) d =
        iteratedDeriv i Bfun d + iteratedDeriv i Afun d := by
    have hfun :
        sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) =
          fun t : ℝ => Bfun t + Afun t := by
      funext t
      simp [sec7_ra_rho3Fun, Bfun, Afun]
    rw [hfun]
    exact iteratedDeriv_fun_add (x := d) hBcd hAcd
  have hA_bound :=
    sec7_ra_rho3_A_rescaled_bound_sharp (P := P) (S := S) (W := W)
      (a := a) (r := r) (i := i) ha hAD hG1 ha_lo ha_hi Env hW hsd hu0 hr hi
  have hB_bound :=
    sec7_ra_rho3_B_rescaled_prebound (P := P) (S := S) (W := W)
      (a := a) (j := j) (r := r) (i := i) ha hAD ha_lo ha_hi Env hW hsd hj hr hi
  have hmain :
      S.D ^ i * |iteratedDeriv i (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) d|
        ≤ (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) +
          (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by
    have htri :
        |iteratedDeriv i (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) d|
          ≤ |iteratedDeriv i Bfun d| + |iteratedDeriv i Afun d| := by
      rw [hsplit]
      exact abs_add_le _ _
    calc
      S.D ^ i * |iteratedDeriv i (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) d|
          ≤ S.D ^ i * (|iteratedDeriv i Bfun d| + |iteratedDeriv i Afun d|) := by
            exact mul_le_mul_of_nonneg_left htri (pow_nonneg hDpos.le i)
      _ = S.D ^ i * |iteratedDeriv i Bfun d| +
          S.D ^ i * |iteratedDeriv i Afun d| := by ring
      _ ≤ (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ +
          (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
            exact add_le_add
              (by simpa [Bfun, d, hd_def] using hB_bound)
              (by simpa [Afun, d, hd_def] using hA_bound)
      _ = (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) +
          (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by ring
  have hmain' :
      S.D ^ i * |iteratedDeriv i (sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ)) (S.D * u)|
        ≤ (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) +
          (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := by
    simpa [hSDu] using hmain
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs]
  rw [hwithin, hscale]
  simpa [abs_mul,
    abs_of_nonneg (pow_nonneg hDpos.le i)] using hmain'

private theorem sec7_ra_rho1_rescaled_FDeriv_prebound {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    (hj : sec7_jBand P S j)
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ))
        (dtilde P.X r (a : ℝ) / S.D)‖
      ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) +
          (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hDpos : 0 < S.D := S.D_pos
  set d : ℝ := dtilde P.X r (a : ℝ) with hd_def
  set u : ℝ := d / S.D with hu_def
  have hSDu : S.D * u = d := by
    rw [hu_def]
    field_simp [ne_of_gt hDpos]
  have humem : u ∈ sec7_ra_rho3Target P S (a : ℝ) := by
    rw [hu_def]
    exact sec7_ra_ftilde_mapsTo_rho3Target (P := P) (S := S) (W := W) (a := a)
      ha hAD ha_lo ha_hi Env hW hsd hr
  have hrho_at :
      ContDiffAt ℝ 5 (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) (S.D * u) := by
    simpa [hSDu, d, hd_def] using
      sec7_ra_rho1_contDiffAt_dtilde (P := P) (S := S) (W := W)
        (a := a) (j := j) (r := r) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj hr
  have hlin_cd : ContDiffAt ℝ 5 (fun y : ℝ => S.D * y) u :=
    contDiffAt_const.mul contDiffAt_id
  have hg_at : ContDiffAt ℝ 5
      (fun y : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * y)) u :=
    hrho_at.comp u hlin_cd
  have hwithin :
      iteratedDerivWithin i
          (fun y : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * y))
          (sec7_ra_rho3Target P S (a : ℝ)) u =
        iteratedDeriv i
          (fun y : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * y)) u :=
    iteratedDerivWithin_eq_iteratedDeriv
      (sec7_ra_rho3Target_uniqueDiffOn (P := P) (S := S) (a := (a : ℝ))
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi))
      (hg_at.of_le (by exact_mod_cast hi)) humem
  have hscale :
      iteratedDeriv i
          (fun y : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * y)) u =
        S.D ^ i * iteratedDeriv i (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) (S.D * u) :=
    sec7_iteratedDeriv_comp_const_mul_at5 (f := sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ))
      (x := u) (c := S.D) hi hrho_at
  have hrcore := sec7_phase_rWinWide_core Env hW c₀ Cu hsd hr
  obtain ⟨hft_lo, hft_hi⟩ :=
    sec7_phase_ftil_scale (P := P) (S := S) (r := r) (a := a)
      ha hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      hrcore.1 hrcore.2
  have hr0 : 0 < r := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd r hr
  have hdpos : 0 < d := by
    simpa [d, hd_def] using dtilde_pos P.X_pos haR hr0
  have hFd : Ffun P.X (a : ℝ) d = sec7_phase_ftil P S a r := by
    simp [d, sec7_phase_ftil]
  have hpert :=
    sec7_phase_shift_error_bound (P := P) (S := S) (W := W) (θ := 0) (j := j)
      Env hW c₀ Cu hsd hj (by norm_num)
  have hjF : |(j : ℝ)| ≤ S.F / 1000 := by nlinarith
  have hshift : Ffun P.X (a : ℝ) d + (j : ℝ) ∈ sec7_tWin S := by
    simp only [sec7_tWin, Set.mem_Icc]
    constructor
    · rw [sec7_cWin, hFd]
      have hjlo : -(S.F / 1000) ≤ (j : ℝ) := by
        have h := neg_abs_le (j : ℝ)
        nlinarith
      nlinarith
    · rw [sec7_cWin, hFd]
      have hjhi : (j : ℝ) ≤ S.F / 1000 := by
        have h := le_abs_self (j : ℝ)
        nlinarith
      nlinarith
  have hFbase : ContDiffAt ℝ 5 (fun y : ℝ => Ffun P.X (a : ℝ) y) d :=
    sec7_Ffun_contDiffAt (n := 5) (X := P.X) (a := (a : ℝ)) (d := d)
      (ne_of_gt hdpos) (by positivity)
  have hdb_un : ContDiffAt ℝ 5 (dBreve' P.X (a : ℝ)) (Ffun P.X (a : ℝ) d) :=
    sec7_dBreve'_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := d) P.X_pos haR hdpos
  have hun : ContDiffAt ℝ 5
      (fun y : ℝ => dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y)) d :=
    hdb_un.comp d hFbase
  set t₀ : ℝ := Ffun P.X (a : ℝ) d + (j : ℝ) with ht₀
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := (a : ℝ)) (t := t₀)
      hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi)
      (by simpa [t₀, ht₀] using hshift)
  have hdb_shift :=
    sec7_dBreve'_contDiffAt5_Ffun (X := P.X) (a := (a : ℝ))
      (d := dBreve P.X (a : ℝ) t₀) P.X_pos haR dBreve_pos
  have hdb_shift_at : ContDiffAt ℝ 5 (dBreve' P.X (a : ℝ)) t₀ := by
    simpa [himg] using hdb_shift
  have harg : ContDiffAt ℝ 5
      (fun y : ℝ => Ffun P.X (a : ℝ) y + (j : ℝ)) d :=
    hFbase.add contDiffAt_const
  have hshifted : ContDiffAt ℝ 5
      (fun y : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y + (j : ℝ))) d := by
    simpa [t₀, ht₀] using (hdb_shift_at.comp d harg).neg
  set Bfun : ℝ → ℝ :=
    fun t => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t + (j : ℝ)) +
      dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t)
  set Afun : ℝ → ℝ :=
    fun t => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) t) -
      t ^ 2 * (t + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))
  have hBcd : ContDiffAt ℝ i Bfun d := by
    have hB : ContDiffAt ℝ 5
        (fun y : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y + (j : ℝ)) +
          dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y)) d :=
      hshifted.add hun
    simpa [Bfun] using hB.of_le (by exact_mod_cast hi)
  have hAcd : ContDiffAt ℝ i Afun d := by
    have hmono : ContDiffAt ℝ 5
        (fun y : ℝ => y ^ 2 * (y + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d := by
      fun_prop
    have hA : ContDiffAt ℝ 5
        (fun y : ℝ => -dBreve' P.X (a : ℝ) (Ffun P.X (a : ℝ) y) -
          y ^ 2 * (y + (a : ℝ)) ^ 2 / (6 * P.X * (a : ℝ))) d :=
      hun.neg.sub hmono
    simpa [Afun] using hA.of_le (by exact_mod_cast hi)
  have hsplit :
      iteratedDeriv i (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) d =
        iteratedDeriv i Bfun d + iteratedDeriv i Afun d := by
    have hfun :
        sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) =
          fun t : ℝ => Bfun t + Afun t := by
      funext t
      simp [sec7_ra_rho1Fun, Bfun, Afun]
      ring
    rw [hfun]
    exact iteratedDeriv_fun_add (x := d) hBcd hAcd
  have hA_bound :=
    sec7_ra_rho1_A_rescaled_bound (P := P) (S := S) (W := W)
      (a := a) (r := r) (i := i) ha hAD hG1 ha_lo ha_hi Env hW hsd
      hbud hg0 hu0 hX24 hr hi
  have hB_bound :=
    sec7_ra_rho1_B_rescaled_prebound (P := P) (S := S) (W := W)
      (a := a) (j := j) (r := r) (i := i) ha hAD ha_lo ha_hi Env hW hsd hj hr hi
  have hmain :
      S.D ^ i * |iteratedDeriv i (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) d|
        ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) +
          (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by
    have htri :
        |iteratedDeriv i (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) d|
          ≤ |iteratedDeriv i Bfun d| + |iteratedDeriv i Afun d| := by
      rw [hsplit]
      exact abs_add_le _ _
    calc
      S.D ^ i * |iteratedDeriv i (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) d|
          ≤ S.D ^ i * (|iteratedDeriv i Bfun d| + |iteratedDeriv i Afun d|) := by
            exact mul_le_mul_of_nonneg_left htri (pow_nonneg hDpos.le i)
      _ = S.D ^ i * |iteratedDeriv i Bfun d| +
          S.D ^ i * |iteratedDeriv i Afun d| := by ring
      _ ≤ (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ +
          (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
            exact add_le_add
              (by simpa [Bfun, d, hd_def] using hB_bound)
              (by simpa [Afun, d, hd_def] using hA_bound)
      _ = (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) +
          (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by ring
  have hmain' :
      S.D ^ i * |iteratedDeriv i (sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ)) (S.D * u)|
        ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) +
          (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := by
    simpa [hSDu] using hmain
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs]
  rw [hwithin, hscale]
  simpa [abs_mul,
    abs_of_nonneg (pow_nonneg hDpos.le i)] using hmain'

private theorem sec7_ra_rho1_B_budget_absorb {P : Globals} {S : Scale P}
    {c₀ Cu : ℝ} {j : ℤ}
    (hsd : OnStripAux.StripData P S c₀ Cu) (hj : sec7_jBand P S j)
    (hG1 : 1 ≤ P.G) (hG10x : P.G * P.U ^ 10 ≤ S.x)
    (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁
      ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
  have hJ :=
    sec7_ra_j_over_F_le_relErrF_tiny (P := P) (S := S) (c₀ := c₀) (Cu := Cu)
      (j := j) hsd hj hG1 hG10x hUbig
  have hT0 : 0 ≤ S.T₁ := (sec7_T₁_pos S).le
  have hcoef0 : 0 ≤ (8 * 10 ^ 15 : ℝ) := by norm_num
  have hbase0 : 0 ≤ S.T₁ * sec7_relErrF P S :=
    mul_nonneg hT0 (sec7_relErrF_pos P S).le
  calc
    (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁
        = (8 * 10 ^ 15 : ℝ) * ((|(j : ℝ)| / S.F) * S.T₁) := by ring
    _ ≤ (8 * 10 ^ 15 : ℝ) * (((1 / (10 : ℝ) ^ 9) * sec7_relErrF P S) * S.T₁) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hJ hT0) hcoef0
    _ = (8 * 10 ^ 15 : ℝ) * ((1 / (10 : ℝ) ^ 9) * sec7_relErrF P S) * S.T₁ := by ring
    _ = (8 * 10 ^ 6 : ℝ) * (S.T₁ * sec7_relErrF P S) := by ring
    _ ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hbase0

private theorem sec7_ra_rho1_rescaled_FDeriv_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    (hj : sec7_jBand P S j)
    (hG10x : P.G * P.U ^ 10 ≤ S.x) (hUbig : (10 : ℝ) ^ 33 ≤ P.U)
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ))
        (dtilde P.X r (a : ℝ) / S.D)‖
      ≤ (8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
  have hpre :=
    sec7_ra_rho1_rescaled_FDeriv_prebound (P := P) (S := S) (W := W)
      (a := a) (j := j) (r := r) (i := i) ha hAD hG1 ha_lo ha_hi
      Env hW c₀ Cu hsd hbud hg0 hu0 hX24 hj hr hi
  have hB :=
    sec7_ra_rho1_B_budget_absorb (P := P) (S := S) (c₀ := c₀) (Cu := Cu)
      (j := j) hsd hj hG1 hG10x hUbig
  have hbase0 : 0 ≤ S.T₁ * sec7_relErrF P S :=
    mul_nonneg (sec7_T₁_pos S).le (sec7_relErrF_pos P S).le
  calc
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ))
        (dtilde P.X r (a : ℝ) / S.D)‖
        ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) +
            (8 * 10 ^ 15 : ℝ) * (|(j : ℝ)| / S.F) * S.T₁ := hpre
    _ ≤ (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) +
          (10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
          exact add_le_add le_rfl hB
    _ = (2 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by ring
    _ ≤ (8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hbase0

private theorem sec7_ra_rho3_B_budget_absorb {P : Globals} {S : Scale P}
    {c₀ Cu : ℝ} {j : ℤ}
    (hsd : OnStripAux.StripData P S c₀ Cu) (hj : sec7_jBand P S j)
    (hG1 : 1 ≤ P.G) (hG10x : P.G * P.U ^ 10 ≤ S.x)
    (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃
      ≤ (10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
  have hJ :=
    sec7_ra_j_over_F_le_relErrF_small (P := P) (S := S) (c₀ := c₀) (Cu := Cu)
      (j := j) hsd hj hG1 hG10x hUbig
  have hT0 : 0 ≤ S.T₃ := (sec7_T₃_pos S).le
  have hcoef0 : 0 ≤ (7 * 10 ^ 11 : ℝ) := by norm_num
  have hbase0 : 0 ≤ S.T₃ * sec7_relErrF P S :=
    mul_nonneg hT0 (sec7_relErrF_pos P S).le
  calc
    (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃
        = (7 * 10 ^ 11 : ℝ) * ((|(j : ℝ)| / S.F) * S.T₃) := by ring
    _ ≤ (7 * 10 ^ 11 : ℝ) * (((1 / (10 : ℝ) ^ 5) * sec7_relErrF P S) * S.T₃) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hJ hT0) hcoef0
    _ = (7 * 10 ^ 11 : ℝ) * ((1 / (10 : ℝ) ^ 5) * sec7_relErrF P S) * S.T₃ := by ring
    _ = (7 * 10 ^ 6 : ℝ) * (S.T₃ * sec7_relErrF P S) := by ring
    _ ≤ (10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hbase0

private theorem sec7_ra_rho3_rescaled_FDeriv_bound {P : Globals} {S : Scale P} {W : ℝ}
    {a j : ℤ} {r : ℝ} {i : ℕ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hG1 : 1 ≤ P.G) (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hj : sec7_jBand P S j) (hu0 : 0 < P.u)
    (hG10x : P.G * P.U ^ 10 ≤ S.x) (hUbig : (10 : ℝ) ^ 33 ≤ P.U)
    (hr : r ∈ sec7_rWinWide S W) (hi : i ≤ 5) :
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ))
        (dtilde P.X r (a : ℝ) / S.D)‖
      ≤ (8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
  have hpre :=
    sec7_ra_rho3_rescaled_FDeriv_prebound (P := P) (S := S) (W := W)
      (a := a) (j := j) (r := r) (i := i) ha hAD hG1 ha_lo ha_hi
      Env hW c₀ Cu hsd hj hu0 hr hi
  have hB :=
    sec7_ra_rho3_B_budget_absorb (P := P) (S := S) (c₀ := c₀) (Cu := Cu)
      (j := j) hsd hj hG1 hG10x hUbig
  calc
    ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ))
        (dtilde P.X r (a : ℝ) / S.D)‖
        ≤ (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) +
            (7 * 10 ^ 11 : ℝ) * (|(j : ℝ)| / S.F) * S.T₃ := hpre
    _ ≤ (7 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) +
          (10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
          exact add_le_add le_rfl hB
    _ = (8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by ring

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
        (((10 ^ 3 : ℝ) / S.R) ^ m)
      ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by
  have hRpos : 0 < S.R := sec7_R_pos S
  have hscale := sec7_ra_residual_scale_le (P := P) (S := S) (a := a) ha0 ha_hi
  have hscale_nonneg : 0 ≤ S.T₂ * (S.Ω / P.H) ^ 2 :=
    mul_nonneg (sec7_T₂_pos S).le (sq_nonneg _)
  calc
    (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * a ^ 3 / S.D ^ 5)) *
        (((10 ^ 3 : ℝ) / S.R) ^ m)
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) *
            (8 * (S.T₂ * (S.Ω / P.H) ^ 2))) *
              (((10 ^ 3 : ℝ) / S.R) ^ m) := by
          gcongr
    _ = ((m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 3 : ℝ) ^ m) *
          (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by
          rw [div_pow]
          field_simp [ne_of_gt hRpos]
          rw [div_pow]
          field_simp [ne_of_gt hRpos]
    _ ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by
          have hconst :
              (m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 3 : ℝ) ^ m
                ≤ (10 ^ 80 : ℝ) := by
            interval_cases m <;> norm_num
          have hB : 0 ≤ (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 :=
            mul_nonneg
              (div_nonneg (sec7_T₂_pos S).le (pow_nonneg hRpos.le m))
              (sq_nonneg _)
          calc
            ((m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 3 : ℝ) ^ m) *
                (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2
                = ((m.factorial : ℝ) * 8 * (10 ^ 20 : ℝ) * (10 ^ 3 : ℝ) ^ m) *
                    ((S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2) := by ring
            _ ≤ (10 ^ 80 : ℝ) * ((S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2) :=
                mul_le_mul_of_nonneg_right hconst hB
            _ = (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 := by ring

private theorem sec7_ra_e₁D_comp_scale_absorb {P : Globals} {S : Scale P} {m : ℕ}
    (hm : m ≤ 5) :
    (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S)) *
        (((10 ^ 3 : ℝ) / S.R) ^ m)
      ≤ sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S := by
  have hRpos : 0 < S.R := sec7_R_pos S
  have hbase : 0 ≤ (S.T₁ / S.R ^ m) * sec7_relErrF P S := by
    exact mul_nonneg
      (div_nonneg (sec7_T₁_pos S).le (pow_nonneg hRpos.le m))
      (sec7_relErrF_pos P S).le
  calc
    (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S)) *
        (((10 ^ 3 : ℝ) / S.R) ^ m)
        = ((m.factorial : ℝ) * (8 * 10 ^ 7 : ℝ) * (10 ^ 3 : ℝ) ^ m) *
            ((S.T₁ / S.R ^ m) * sec7_relErrF P S) := by
          rw [div_pow]
          field_simp [ne_of_gt hRpos]
    _ ≤ sec7_cExpIn * ((S.T₁ / S.R ^ m) * sec7_relErrF P S) := by
          have hconst :
              (m.factorial : ℝ) * (8 * 10 ^ 7 : ℝ) * (10 ^ 3 : ℝ) ^ m
                ≤ sec7_cExpIn := by
            interval_cases m <;> norm_num [sec7_cExpIn]
          exact mul_le_mul_of_nonneg_right hconst hbase
    _ = sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S := by ring

private theorem sec7_ra_e₃D_comp_scale_absorb {P : Globals} {S : Scale P} {m : ℕ}
    (hm : m ≤ 5) :
    (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S)) *
        (((10 ^ 3 : ℝ) / S.R) ^ m)
      ≤ sec7_cExpIn * (S.T₃ / S.R ^ m) * sec7_relErrF P S := by
  have hRpos : 0 < S.R := sec7_R_pos S
  have hbase : 0 ≤ (S.T₃ / S.R ^ m) * sec7_relErrF P S := by
    exact mul_nonneg
      (div_nonneg (sec7_T₃_pos S).le (pow_nonneg hRpos.le m))
      (sec7_relErrF_pos P S).le
  calc
    (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S)) *
        (((10 ^ 3 : ℝ) / S.R) ^ m)
        = ((m.factorial : ℝ) * (8 * 10 ^ 7 : ℝ) * (10 ^ 3 : ℝ) ^ m) *
            ((S.T₃ / S.R ^ m) * sec7_relErrF P S) := by
          rw [div_pow]
          field_simp [ne_of_gt hRpos]
    _ ≤ sec7_cExpIn * ((S.T₃ / S.R ^ m) * sec7_relErrF P S) := by
          have hconst :
              (m.factorial : ℝ) * (8 * 10 ^ 7 : ℝ) * (10 ^ 3 : ℝ) ^ m
                ≤ sec7_cExpIn := by
            interval_cases m <;> norm_num [sec7_cExpIn]
          exact mul_le_mul_of_nonneg_right hconst hbase
    _ = sec7_cExpIn * (S.T₃ / S.R ^ m) * sec7_relErrF P S := by ring

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
          (sec7_rWinWide S W) r‖ ≤ (((10 ^ 3 : ℝ) / S.R) ^ i) := by
    intro i hi₁ hi
    exact sec7_ra_ftilde_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr hi₁ (le_trans hi hm)
  have hcomp :
      ‖iteratedFDerivWithin ℝ m
          ((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))
          (sec7_rWinWide S W) r‖
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) :=
    norm_iteratedFDerivWithin_comp_le hgtilde_cd hftilde_cd
      (by exact_mod_cast hm) htOpen.uniqueDiffOn hwideOpen.uniqueDiffOn hmaps hr hC hD
  have hcomp_deriv :
      |iteratedDeriv m
          (((fun u : ℝ => sec7_ra_rhoFun P.X (a : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r|
        ≤ (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) := by
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
            (((10 ^ 3 : ℝ) / S.R) ^ m) := by
    simpa [sec7_phase_ra_e₂D, hres_deriv] using hcomp_deriv
  have hscale :
      (m.factorial : ℝ) * ((10 ^ 20 : ℝ) * (P.X * (a : ℝ) ^ 3 / S.D ^ 5)) *
          (((10 ^ 3 : ℝ) / S.R) ^ m)
        ≤ (10 ^ 80 : ℝ) * (S.T₂ / S.R ^ m) * (S.Ω / P.H) ^ 2 :=
    sec7_ra_e₂D_comp_scale_absorb (P := P) (S := S) (a := (a : ℝ)) (m := m)
      hm haR ha_hi
  exact le_trans hnative (le_trans hscale
    (sec7_phase_ra_e₂D_budget_absorb (P := P) (S := S) (W := W)
      Env hW hsd hbud hg0 hu0 hX24 m))

theorem sec7_ra_e₃D_core (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hu0 : 0 < P.u) (hG10x : P.G * P.U ^ 10 ≤ S.x)
    (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    ∀ j, sec7_jBand P S j → ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
      |sec7_phase_ra_e₃D P S a j m r| ≤
        sec7_cExpIn * (S.T₃ / S.R ^ m) * sec7_relErrF P S := by
  intro j hj m hm r hr
  have hwideOpen : IsOpen (sec7_rWinWide S W) := by
    simpa [sec7_rWinWide] using (isOpen_Ioo : IsOpen (Set.Ioo
      (S.R / 144 - 6 * (W + W ^ 2 + W ^ 4))
      (40 * S.R + 6 * (W + W ^ 2 + W ^ 4))))
  have hftilde_cd :
      ContDiffOn ℝ 5 (fun s => dtilde P.X s (a : ℝ) / S.D) (sec7_rWinWide S W) :=
    sec7_ra_ftilde_contDiffOn_wide (P := P) (S := S) (W := W) (a := a)
      ha Env hW hsd
  have hgtilde_cd :
      ContDiffOn ℝ 5
        (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ)) :=
    sec7_ra_gtilde3_contDiffOn_target (P := P) (S := S) (W := W)
      (a := a) (j := j) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj
  have hmaps : Set.MapsTo (fun s => dtilde P.X s (a : ℝ) / S.D)
      (sec7_rWinWide S W) (sec7_ra_rho3Target P S (a : ℝ)) :=
    sec7_ra_ftilde_mapsTo_rho3Target (P := P) (S := S) (W := W)
      (a := a) ha hAD ha_lo ha_hi Env hW hsd
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i
          (fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
          (sec7_ra_rho3Target P S (a : ℝ))
          ((fun s => dtilde P.X s (a : ℝ) / S.D) r)‖
        ≤ (8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S) := by
    intro i hi
    exact sec7_ra_rho3_rescaled_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (j := j) (r := r) (i := i) ha hAD hG1 ha_lo ha_hi
      Env hW c₀ Cu hsd hj hu0 hG10x hUbig hr (le_trans hi hm)
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i (fun s => dtilde P.X s (a : ℝ) / S.D)
          (sec7_rWinWide S W) r‖ ≤ (((10 ^ 3 : ℝ) / S.R) ^ i) := by
    intro i hi₁ hi
    exact sec7_ra_ftilde_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr hi₁ (le_trans hi hm)
  have hcomp :
      ‖iteratedFDerivWithin ℝ m
          ((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))
          (sec7_rWinWide S W) r‖
        ≤ (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) :=
    norm_iteratedFDerivWithin_comp_le hgtilde_cd hftilde_cd
      (by exact_mod_cast hm)
      (sec7_ra_rho3Target_uniqueDiffOn (P := P) (S := S) (a := (a : ℝ))
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi))
      hwideOpen.uniqueDiffOn hmaps hr hC hD
  have hcomp_deriv :
      |iteratedDeriv m
          (((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r|
        ≤ (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) := by
    have hwithin :
        iteratedFDerivWithin ℝ m
          (((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D)))
          (sec7_rWinWide S W) r =
        iteratedFDeriv ℝ m
          (((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := m)
        (f := ((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
          (fun s => dtilde P.X s (a : ℝ) / S.D))) hwideOpen) hr
    rw [hwithin, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hcomp
    simpa [Real.norm_eq_abs] using hcomp
  have hres_eq : (fun t =>
      sec7_phase_f3D P S a j 0 t
        - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
            * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4))
        =ᶠ[𝓝 r]
      (((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
        (fun s => dtilde P.X s (a : ℝ) / S.D))) := by
    filter_upwards [hwideOpen.mem_nhds hr] with t ht
    have ht0 : 0 < t := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd t ht
    have hbridge := sec7_ra_e₃D_residual_bridge_point (P := P) (S := S)
      (a := a) (j := j) (r := t) ha ht0
    have hDpos : 0 < S.D := S.D_pos
    simpa [Function.comp_def, sec7_ra_rho3Fun, mul_div_cancel₀, hDpos.ne'] using hbridge
  have hres_deriv :
      iteratedDeriv m
        (fun t =>
          sec7_phase_f3D P S a j 0 t
            - 3 * sec7_phase_ra_c₁ P S a j * sec7_phase_ra_c₂ P S a j
                * S.T₃ * (t / S.R) ^ (-(1 : ℝ) / 4)) r
      =
      iteratedDeriv m
        (((fun u : ℝ => sec7_ra_rho3Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
          (fun s => dtilde P.X s (a : ℝ) / S.D))) r :=
    Filter.EventuallyEq.iteratedDeriv_eq m hres_eq
  have hnative :
      |sec7_phase_ra_e₃D P S a j m r|
        ≤ (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₃ * sec7_relErrF P S)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) := by
    simpa [sec7_phase_ra_e₃D, hres_deriv] using hcomp_deriv
  exact le_trans hnative (sec7_ra_e₃D_comp_scale_absorb (P := P) (S := S) (m := m) hm)

theorem sec7_ra_e₁D_core (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    (hG10x : P.G * P.U ^ 10 ≤ S.x) (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    ∀ j, sec7_jBand P S j → ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
      |sec7_phase_ra_e₁D P S a j m r| ≤
        sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S := by
  intro j hj m hm r hr
  have hwideOpen : IsOpen (sec7_rWinWide S W) := by
    simpa [sec7_rWinWide] using (isOpen_Ioo : IsOpen (Set.Ioo
      (S.R / 144 - 6 * (W + W ^ 2 + W ^ 4))
      (40 * S.R + 6 * (W + W ^ 2 + W ^ 4))))
  have hftilde_cd :
      ContDiffOn ℝ 5 (fun s => dtilde P.X s (a : ℝ) / S.D) (sec7_rWinWide S W) :=
    sec7_ra_ftilde_contDiffOn_wide (P := P) (S := S) (W := W) (a := a)
      ha Env hW hsd
  have hgtilde_cd :
      ContDiffOn ℝ 5
        (fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
        (sec7_ra_rho3Target P S (a : ℝ)) :=
    sec7_raC_gtilde1_contDiffOn_target (P := P) (S := S) (W := W)
      (a := a) (j := j) ha hAD ha_lo ha_hi Env hW c₀ Cu hsd hj
  have hmaps : Set.MapsTo (fun s => dtilde P.X s (a : ℝ) / S.D)
      (sec7_rWinWide S W) (sec7_ra_rho3Target P S (a : ℝ)) :=
    sec7_ra_ftilde_mapsTo_rho3Target (P := P) (S := S) (W := W)
      (a := a) ha hAD ha_lo ha_hi Env hW hsd
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i
          (fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u))
          (sec7_ra_rho3Target P S (a : ℝ))
          ((fun s => dtilde P.X s (a : ℝ) / S.D) r)‖
        ≤ (8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S) := by
    intro i hi
    exact sec7_ra_rho1_rescaled_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (j := j) (r := r) (i := i) ha hAD hG1 ha_lo ha_hi
      Env hW c₀ Cu hsd hbud hg0 hu0 hX24 hj hG10x hUbig hr (le_trans hi hm)
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i (fun s => dtilde P.X s (a : ℝ) / S.D)
          (sec7_rWinWide S W) r‖ ≤ (((10 ^ 3 : ℝ) / S.R) ^ i) := by
    intro i hi₁ hi
    exact sec7_ra_ftilde_FDeriv_bound (P := P) (S := S) (W := W)
      (a := a) (r := r) ha hAD ha_lo ha_hi Env hW hsd hr hi₁ (le_trans hi hm)
  have hcomp :
      ‖iteratedFDerivWithin ℝ m
          ((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))
          (sec7_rWinWide S W) r‖
        ≤ (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) :=
    norm_iteratedFDerivWithin_comp_le hgtilde_cd hftilde_cd
      (by exact_mod_cast hm)
      (sec7_ra_rho3Target_uniqueDiffOn (P := P) (S := S) (a := (a : ℝ))
        hAD (sec7_phase_a_lo_wide ha_lo) (sec7_phase_a_hi_wide ha_hi))
      hwideOpen.uniqueDiffOn hmaps hr hC hD
  have hcomp_deriv :
      |iteratedDeriv m
          (((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r|
        ≤ (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) := by
    have hwithin :
        iteratedFDerivWithin ℝ m
          (((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D)))
          (sec7_rWinWide S W) r =
        iteratedFDeriv ℝ m
          (((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
            (fun s => dtilde P.X s (a : ℝ) / S.D))) r :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := m)
        (f := ((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
          (fun s => dtilde P.X s (a : ℝ) / S.D))) hwideOpen) hr
    rw [hwithin, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hcomp
    simpa [Real.norm_eq_abs] using hcomp
  have hres_eq : (fun t =>
      sec7_phase_f1D P S a j 0 t
        - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ)))
        =ᶠ[𝓝 r]
      (((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
        (fun s => dtilde P.X s (a : ℝ) / S.D))) := by
    filter_upwards [hwideOpen.mem_nhds hr] with t ht
    have ht0 : 0 < t := sec7_phase_rWinWide_pos Env hW c₀ Cu hsd t ht
    have hbridge := sec7_ra_e₁D_residual_bridge_point (P := P) (S := S)
      (a := a) (j := j) (r := t) ha ht0
    have hDpos : 0 < S.D := S.D_pos
    simpa [Function.comp_def, sec7_ra_rho1Fun, mul_div_cancel₀, hDpos.ne'] using hbridge
  have hres_deriv :
      iteratedDeriv m
        (fun t =>
          sec7_phase_f1D P S a j 0 t
            - sec7_phase_ra_c₁ P S a j * S.T₁ * (t / S.R) ^ (-(1 : ℝ))) r
      =
      iteratedDeriv m
        (((fun u : ℝ => sec7_ra_rho1Fun P.X (a : ℝ) (j : ℝ) (S.D * u)) ∘
          (fun s => dtilde P.X s (a : ℝ) / S.D))) r :=
    Filter.EventuallyEq.iteratedDeriv_eq m hres_eq
  have hnative :
      |sec7_phase_ra_e₁D P S a j m r|
        ≤ (m.factorial : ℝ) * ((8 * 10 ^ 7 : ℝ) * (S.T₁ * sec7_relErrF P S)) *
            (((10 ^ 3 : ℝ) / S.R) ^ m) := by
    simpa [sec7_phase_ra_e₁D, hres_deriv] using hcomp_deriv
  exact le_trans hnative (sec7_ra_e₁D_comp_scale_absorb (P := P) (S := S) (m := m) hm)

private theorem sec7_phase_ra_e₂D_tiny {P : Globals} {S : Scale P} {W : ℝ}
    {a : ℤ} (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    {m : ℕ} {r : ℝ} (hm : m ≤ 5) (hr : r ∈ sec7_rWinWide S W) :
    |sec7_phase_ra_e₂D P S a 0 m r| ≤
      (1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m) := by
  have hj0 : sec7_jBand P S 0 := by
    unfold sec7_jBand
    have hApos : 0 < S.A := by
      unfold Scale.A
      exact mul_pos S.Δ_pos S.Ω_pos
    simpa using (mul_nonneg (by norm_num [sec7_cJ])
      (add_nonneg zero_le_one (div_nonneg P.H_pos.le (pow_nonneg hApos.le 2)))
      : (0 : ℝ) ≤ sec7_cJ * (1 + P.H / S.A ^ 2))
  have hcore := sec7_ra_e₂D_core P S W a ha hAD hG1 ha_lo ha_hi
    Env hW c₀ Cu hsd hbud hg0 hu0 hX24 0 hj0 m hm r hr
  have hrel143 : sec7_relErr P S * 10 ^ 143 ≤ 1 :=
    sec7_relErr_le Env hW hsd hbud hg0 hu0 hX24
  have hrel_le : sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (10 : ℝ) ^ 143)]
    simpa [mul_comm] using hrel143
  have hsmall : sec7_cExpIn * sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 100 := by
    calc
      sec7_cExpIn * sec7_relErr P S
          ≤ (10 ^ 25 : ℝ) * (1 / (10 : ℝ) ^ 143) := by
            rw [sec7_cExpIn]
            exact mul_le_mul_of_nonneg_left hrel_le (by positivity)
      _ ≤ 1 / (10 : ℝ) ^ 100 := by norm_num
  have hB0 : 0 ≤ S.T₂ / S.R ^ m :=
    div_nonneg (sec7_T₂_pos S).le (pow_nonneg (sec7_R_pos S).le m)
  calc
    |sec7_phase_ra_e₂D P S a 0 m r|
        ≤ sec7_cExpIn * (S.T₂ / S.R ^ m) * sec7_relErr P S := hcore
    _ = (sec7_cExpIn * sec7_relErr P S) * (S.T₂ / S.R ^ m) := by ring
    _ ≤ (1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m) :=
        mul_le_mul_of_nonneg_right hsmall hB0

/-- Concrete phase bundle assembled from the definitions above.

The analytic fields that require substantial scale or §3 expansion bookkeeping are left as
localized stubs in this constructor file; no upstream file is modified. -/
noncomputable def sec7_phase_concrete (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ)
    (ha : 0 < a) (hAD : 10 * S.A ≤ S.D) (_hG1 : 1 ≤ P.G)
    (ha_lo : S.A ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 2 * S.A)
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W)
    (c₀ Cu : ℝ) (hsd : OnStripAux.StripData P S c₀ Cu)
    (hbud : OnStripAux.Budget P.g P.u Cu) (hg0 : 0 ≤ P.g) (hu0 : 0 < P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    (hG10x : P.G * P.U ^ 10 ≤ S.x) (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
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
    intro m hm r hr
    have hmid : r ∈ sec7_rWinMid S W :=
      sec7_rWin_subset_mid S (lt_of_lt_of_le zero_lt_one hW) hr
    have hrwide : r ∈ sec7_rWinWide S W := by
      have hshift : |(0 : ℝ)| ≤ 3 * (W + W ^ 2 + W ^ 4) := by
        simp
        positivity
      simpa using sec7_mid_add_mem_wide (S := S) (W := W) (r := r) (s := 0) hmid hshift
    let M : ℝ :=
      sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂) ((3 : ℝ) / 4) m r
    let E : ℝ := sec7_phase_ra_e₂D P S a 0 m r
    have hsplit : sec7_phase_f2D P S a m r = M + E := by
      simpa [M, E] using
        sec7_phase_f2D_eq_powMonD_add_ra_e₂D (P := P) (S := S)
          (W := W) (a := a) (j := 0) (m := m) (r := r) ha Env hW c₀ Cu hsd
          (le_trans hm (by norm_num)) hrwide
    have hmono := (sec7_phase_f2D_monomial_scale (P := P) (S := S) (W := W)
      (a := a) (m := m) (r := r) ha_lo ha_hi Env hW c₀ Cu hsd hm hr).1
    have hres := sec7_phase_ra_e₂D_tiny (P := P) (S := S) (W := W) (a := a)
      ha hAD _hG1 ha_lo ha_hi Env hW c₀ Cu hsd hbud hg0 hu0 hX24
      (m := m) (r := r) (le_trans hm (by norm_num)) hrwide
    have hB0 : 0 ≤ S.T₂ / S.R ^ m :=
      div_nonneg (sec7_T₂_pos S).le (pow_nonneg (sec7_R_pos S).le m)
    have htri : |M| ≤ |sec7_phase_f2D P S a m r| + |E| := by
      have hM : M = sec7_phase_f2D P S a m r + (-E) := by
        linarith [hsplit]
      calc
        |M| = |sec7_phase_f2D P S a m r + (-E)| := by rw [hM]
        _ ≤ |sec7_phase_f2D P S a m r| + |-E| := abs_add_le _ _
        _ = |sec7_phase_f2D P S a m r| + |E| := by rw [abs_neg]
    have hpre :
        (1 / (10 : ℝ) ^ 9) * (S.T₂ / S.R ^ m) +
          (1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m) ≤
        (1 / (10 : ℝ) ^ 8) * (S.T₂ / S.R ^ m) := by
      calc
        (1 / (10 : ℝ) ^ 9) * (S.T₂ / S.R ^ m) +
            (1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m)
            = (1 / (10 : ℝ) ^ 9 + 1 / (10 : ℝ) ^ 100) *
                (S.T₂ / S.R ^ m) := by ring
        _ ≤ (1 / (10 : ℝ) ^ 8) * (S.T₂ / S.R ^ m) :=
              mul_le_mul_of_nonneg_right (by norm_num) hB0
    have hf_lower :
        (1 / (10 : ℝ) ^ 9) * (S.T₂ / S.R ^ m) ≤
          |sec7_phase_f2D P S a m r| := by
      have hmono' : (1 / (10 : ℝ) ^ 8) * (S.T₂ / S.R ^ m) ≤ |M| := by
        simpa [M] using hmono
      have hres' : |E| ≤ (1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m) := by
        simpa [E] using hres
      nlinarith [hmono', hres', htri, hpre]
    calc
      S.T₂ / S.R ^ m =
          (10 : ℝ) ^ 9 * ((1 / (10 : ℝ) ^ 9) * (S.T₂ / S.R ^ m)) := by ring
      _ ≤ (10 : ℝ) ^ 9 * |sec7_phase_f2D P S a m r| :=
            mul_le_mul_of_nonneg_left hf_lower (by positivity)
      _ ≤ sec7_cPh * |sec7_phase_f2D P S a m r| :=
            mul_le_mul_of_nonneg_right (by norm_num [sec7_cPh]) (abs_nonneg _)
  f2D_hi := by
    intro m hm r hr
    have hmid : r ∈ sec7_rWinMid S W :=
      sec7_rWin_subset_mid S (lt_of_lt_of_le zero_lt_one hW) hr
    have hrwide : r ∈ sec7_rWinWide S W := by
      have hshift : |(0 : ℝ)| ≤ 3 * (W + W ^ 2 + W ^ 4) := by
        simp
        positivity
      simpa using sec7_mid_add_mem_wide (S := S) (W := W) (r := r) (s := 0) hmid hshift
    have hsplit := sec7_phase_f2D_eq_powMonD_add_ra_e₂D (P := P) (S := S)
      (W := W) (a := a) (j := 0) (m := m) (r := r) ha Env hW c₀ Cu hsd
      (le_trans hm (by norm_num)) hrwide
    have hmono := (sec7_phase_f2D_monomial_scale (P := P) (S := S) (W := W)
      (a := a) (m := m) (r := r) ha_lo ha_hi Env hW c₀ Cu hsd hm hr).2
    have hres := sec7_phase_ra_e₂D_tiny (P := P) (S := S) (W := W) (a := a)
      ha hAD _hG1 ha_lo ha_hi Env hW c₀ Cu hsd hbud hg0 hu0 hX24
      (m := m) (r := r) (le_trans hm (by norm_num)) hrwide
    have hB0 : 0 ≤ S.T₂ / S.R ^ m :=
      div_nonneg (sec7_T₂_pos S).le (pow_nonneg (sec7_R_pos S).le m)
    calc
      |sec7_phase_f2D P S a m r|
          = |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
              ((3 : ℝ) / 4) m r + sec7_phase_ra_e₂D P S a 0 m r| := by
            rw [hsplit]
      _ ≤ |sec7_powMonD S.R (sec7_phase_ra_c₂ P S a 0 * S.T₂)
              ((3 : ℝ) / 4) m r| + |sec7_phase_ra_e₂D P S a 0 m r| := abs_add_le _ _
      _ ≤ (10 : ℝ) ^ 8 * (S.T₂ / S.R ^ m) +
            (1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m) := add_le_add hmono hres
      _ = ((10 : ℝ) ^ 8 + 1 / (10 : ℝ) ^ 100) * (S.T₂ / S.R ^ m) := by ring
      _ ≤ sec7_cPh * (S.T₂ / S.R ^ m) :=
            mul_le_mul_of_nonneg_right (by norm_num [sec7_cPh]) hB0
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
    intro j hj m hm r hr
    exact sec7_ra_e₁D_core P S W a ha hAD _hG1 ha_lo ha_hi Env hW c₀ Cu hsd
      hbud hg0 hu0 hX24 hG10x hUbig j hj m hm r hr
  ra_e₂D_bound := by
    intro j hj m hm r hr
    exact sec7_ra_e₂D_core P S W a ha hAD _hG1 ha_lo ha_hi Env hW c₀ Cu hsd
      hbud hg0 hu0 hX24 j hj m hm r hr
  ra_e₃D_bound := by
    intro j hj m hm r hr
    exact sec7_ra_e₃D_core P S W a ha hAD _hG1 ha_lo ha_hi Env hW c₀ Cu hsd
      hu0 hG10x hUbig j hj m hm r hr
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
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1 / 100 : ℝ))
    (hG10x : P.G * P.U ^ 10 ≤ S.x) (hUbig : (10 : ℝ) ^ 33 ≤ P.U) :
    ∃ Ph : Sec7Phase P S W a,
      (∀ {r : ℝ}, (1/72) * S.R ≤ r → r ≤ 16 * S.R →
        Ph.ftil r = Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))) ∧
      (∀ {d f : ℤ}, S.D ≤ (d : ℝ) → (d : ℝ) ≤ 2 * S.D →
        f = round (Ffun P.X (a : ℝ) (d : ℝ)) →
        |(d : ℝ) - Ph.dBreve (f : ℝ)| ≤
          sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A))) := by
  refine ⟨sec7_phase_concrete P S W a ha hAD hG1 ha_lo ha_hi Env hW c₀ Cu hsd
    hbud hg0 hu0 hX24 hG10x hUbig, ?_, ?_⟩
  · intro r hrlo hrhi
    rfl
  · intro d f hdD hd2D hf
    exact sec7_phase_round_inverse_margin P S a ha hAD hG1 ha_lo ha_hi hdD hd2D hf

end Squarefree
