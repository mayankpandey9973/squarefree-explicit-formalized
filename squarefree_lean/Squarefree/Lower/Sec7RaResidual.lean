import Squarefree.Lower.DefectDeriv5

/-!
# §7 residual helpers

Lower-level analytic facts for the §7 `f₂` residual expansion.
-/

namespace Squarefree

open Set

set_option maxHeartbeats 4000000

private noncomputable def sec7_ra_hCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 2
  | 2 => -1 / 4
  | 3 => 3 / 8
  | 4 => -15 / 16
  | 5 => 105 / 32
  | _ => 0

private noncomputable def sec7_ra_hScale : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 4
  | 2 => 3 / 8
  | 3 => 15 / 16
  | 4 => 105 / 32
  | 5 => 945 / 64
  | _ => 0

private noncomputable def sec7_ra_inv2Scale : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 24
  | 4 => 120
  | 5 => 720
  | _ => 0

private noncomputable def sec7_ra_hsqScale : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => 1 / 4
  | 2 => 1 / 2
  | 3 => 3 / 2
  | 4 => 6
  | 5 => 30
  | _ => 0

private noncomputable def sec7_ra_hsqInvScale : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => 3 / 4
  | 2 => 3
  | 3 => 15
  | 4 => 90
  | 5 => 630
  | _ => 0

noncomputable def sec7_ra_rhoScale : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => 5 / 4
  | 2 => 15 / 2
  | 3 => 105 / 2
  | 4 => 420
  | 5 => 3780
  | _ => 0

private theorem sec7_ra_residual_rho_factor {X a d : ℝ} (hd : 0 < d) (ha : 0 < a) :
    Ffun X a d - 2 * X * a / (d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2)) =
      X * a * (Real.sqrt (d + a) - Real.sqrt d) ^ 2 / (d ^ 2 * (d + a) ^ 2) := by
  have hda : 0 < d + a := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd
  have hdane : d + a ≠ 0 := ne_of_gt hda
  have hsqrtd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hsqrtda : 0 < Real.sqrt (d + a) := Real.sqrt_pos.2 hda
  have hd32 : d ^ ((3 : ℝ) / 2) = d * Real.sqrt d := by
    rw [Real.rpow_div_two_eq_sqrt (x := d) (r := 3) hd.le]
    rw [show Real.sqrt d ^ (3 : ℝ) = d * Real.sqrt d by
      rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hsqrtd,
        Real.rpow_two, Real.rpow_one, Real.sq_sqrt hd.le]]
  have hda32 : (d + a) ^ ((3 : ℝ) / 2) = (d + a) * Real.sqrt (d + a) := by
    rw [Real.rpow_div_two_eq_sqrt (x := d + a) (r := 3) hda.le]
    rw [show Real.sqrt (d + a) ^ (3 : ℝ) = (d + a) * Real.sqrt (d + a) by
      rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hsqrtda,
        Real.rpow_two, Real.rpow_one, Real.sq_sqrt hda.le]]
  rw [Ffun_factor' X a d hdne hdane, hd32, hda32]
  field_simp [hdne, hdane, ne_of_gt hsqrtd, ne_of_gt hsqrtda]
  set p := Real.sqrt d
  set q := Real.sqrt (d + a)
  have hp2 : p ^ 2 = d := by simpa [p] using Real.sq_sqrt hd.le
  have hq2 : q ^ 2 = d + a := by simpa [q] using Real.sq_sqrt hda.le
  have ha_pq : a = q ^ 2 - p ^ 2 := by rw [hq2, hp2]; ring
  rw [← hq2, ← hp2, ha_pq]
  ring

private theorem sec7_ra_residual_rho_factor_rpow {X a d : ℝ} (hd : 0 < d) (ha : 0 < a) :
    Ffun X a d - 2 * X * a / (d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2)) =
      X * a * (((Real.sqrt (d + a) - Real.sqrt d) ^ 2 * d ^ (-2 : ℝ))
        * (d + a) ^ (-2 : ℝ)) := by
  have hda : 0 < d + a := by linarith
  rw [sec7_ra_residual_rho_factor (X := X) (a := a) (d := d) hd ha]
  have hdneg : d ^ (-2 : ℝ) = (d ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hd.le]
    rw [show d ^ (2 : ℝ) = d ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  have hdaneg : (d + a) ^ (-2 : ℝ) = ((d + a) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hda.le]
    rw [show (d + a) ^ (2 : ℝ) = (d + a) ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  rw [hdneg, hdaneg]
  field_simp [ne_of_gt hd, ne_of_gt hda]

private theorem sec7_ra_h_iteratedDeriv_eq {a d : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hd : 0 < d) :
    iteratedDeriv k (fun t => Real.sqrt (t + a) - Real.sqrt t) d =
      sec7_ra_hCoeff k * ((d + a) ^ ((1 : ℝ) / 2 - k) - d ^ ((1 : ℝ) / 2 - k)) := by
  have hda : 0 < d + a := by linarith
  have hfun :
      (fun t : ℝ => Real.sqrt (t + a) - Real.sqrt t)
        = fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2) - t ^ ((1 : ℝ) / 2) := by
    funext t
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hfun]
  have hshift :
      iteratedDeriv k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d =
        (descPochhammer ℝ k).eval ((1 : ℝ) / 2) * (d + a) ^ ((1 : ℝ) / 2 - k) := by
    rw [show iteratedDeriv k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d =
        iteratedDeriv k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (d + a) by
      simpa using congrFun
        (iteratedDeriv_comp_add_const k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) a) d]
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const ((1 : ℝ) / 2) (d + a) k
  have hid :
      iteratedDeriv k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) d =
        (descPochhammer ℝ k).eval ((1 : ℝ) / 2) * d ^ ((1 : ℝ) / 2 - k) := by
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const ((1 : ℝ) / 2) d k
  have hf : ContDiffAt ℝ k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d :=
    (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (ne_of_gt hda)
  have hg : ContDiffAt ℝ k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) d :=
    contDiffAt_id.rpow_const_of_ne (ne_of_gt hd)
  rw [iteratedDeriv_fun_sub hf hg, hshift, hid]
  have hcoeff : (descPochhammer ℝ k).eval ((1 : ℝ) / 2) = sec7_ra_hCoeff k := by
    interval_cases k <;>
      simp [sec7_ra_hCoeff, descPochhammer_eval_eq_prod_range] <;> norm_num
  rw [hcoeff]
  ring

private theorem sec7_ra_rpow_forward_abs_le {p a d : ℝ}
    (hd : 0 < d) (ha : 0 ≤ a) (hp : p - 1 ≤ 0) :
    |(d + a) ^ p - d ^ p| ≤ |p| * d ^ (p - 1) * a := by
  have hdd : d ≤ d + a := by linarith
  have hderiv : ∀ x ∈ Icc d (d + a),
      HasDerivAt (fun y : ℝ => y ^ p) (p * x ^ (p - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le hd hx.1)))
  have hbnd : ∀ x ∈ Icc d (d + a), |p * x ^ (p - 1)| ≤ |p| * d ^ (p - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hd hx.1
    have hxpow_nonneg : 0 ≤ x ^ (p - 1) := (Real.rpow_pos_of_pos hx0 _).le
    have hpow : x ^ (p - 1) ≤ d ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos hd hx.1 hp
    calc
      |p * x ^ (p - 1)| = |p| * x ^ (p - 1) := by
        rw [abs_mul, abs_of_nonneg hxpow_nonneg]
      _ ≤ |p| * d ^ (p - 1) := mul_le_mul_of_nonneg_left hpow (abs_nonneg p)
  have hmvt := (convex_Icc d (d + a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => y ^ p) (f' := fun x : ℝ => p * x ^ (p - 1))
    (C := |p| * d ^ (p - 1))
    (fun x hx => (hderiv x hx).hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hbnd x hx)
    (left_mem_Icc.mpr hdd) (right_mem_Icc.mpr hdd)
  simpa [Real.norm_eq_abs, abs_of_nonneg ha, add_sub_cancel_left] using hmvt

theorem sec7_ra_h_atomic_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    iteratedDeriv k (fun t => Real.sqrt (t + a) - Real.sqrt t) d =
        sec7_ra_hCoeff k * ((d + a) ^ ((1 : ℝ) / 2 - k) - d ^ ((1 : ℝ) / 2 - k))
      ∧ |iteratedDeriv k (fun t => Real.sqrt (t + a) - Real.sqrt t) d|
        ≤ sec7_ra_hScale k * a * d ^ ((-1 : ℝ) / 2 - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have heq := sec7_ra_h_iteratedDeriv_eq (a := a) (d := d) hk ha hd
  constructor
  · exact heq
  · rw [heq]
    set p : ℝ := (1 : ℝ) / 2 - k with hp_def
    set Δ : ℝ := (d + a) ^ p - d ^ p with hΔ_def
    have hp : p - 1 ≤ 0 := by
      rw [hp_def]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hdiff : |Δ| ≤ |p| * d ^ (p - 1) * a := by
      rw [hΔ_def]
      exact sec7_ra_rpow_forward_abs_le (p := p) hd ha.le hp
    have hscale : |sec7_ra_hCoeff k| * |p| = sec7_ra_hScale k := by
      rw [hp_def]
      interval_cases k <;> norm_num [sec7_ra_hCoeff, sec7_ra_hScale]
    have hexp : p - 1 = (-1 : ℝ) / 2 - k := by
      rw [hp_def]
      ring
    calc
      |sec7_ra_hCoeff k * Δ| = |sec7_ra_hCoeff k| * |Δ| := by rw [abs_mul]
      _ ≤ |sec7_ra_hCoeff k| * (|p| * d ^ (p - 1) * a) :=
          mul_le_mul_of_nonneg_left hdiff (abs_nonneg (sec7_ra_hCoeff k))
      _ = sec7_ra_hScale k * a * d ^ ((-1 : ℝ) / 2 - k) := by
          rw [← hscale, hexp]
          ring

private theorem sec7_ra_inv2_bound {d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t : ℝ => t ^ (-2 : ℝ)) d|
      ≤ sec7_ra_inv2Scale k * d ^ ((-2 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  have hcoeff : |(descPochhammer ℝ k).eval (-2 : ℝ)| = sec7_ra_inv2Scale k := by
    interval_cases k <;>
      simp [sec7_ra_inv2Scale, descPochhammer_eval_eq_prod_range] <;> norm_num
  have hpow_nonneg : 0 ≤ d ^ ((-2 : ℝ) - k) := (Real.rpow_pos_of_pos hd _).le
  rw [abs_mul, hcoeff, abs_of_nonneg hpow_nonneg]

private theorem sec7_ra_shift_inv2_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t : ℝ => (t + a) ^ (-2 : ℝ)) d|
      ≤ sec7_ra_inv2Scale k * d ^ ((-2 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have hda : 0 < d + a := by linarith
  have hle : d ≤ d + a := by linarith
  have hq : (-2 : ℝ) - k ≤ 0 := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hpow_le : (d + a) ^ ((-2 : ℝ) - k) ≤ d ^ ((-2 : ℝ) - k) :=
    Real.rpow_le_rpow_of_nonpos hd hle hq
  rw [show iteratedDeriv k (fun t : ℝ => (t + a) ^ (-2 : ℝ)) d =
      iteratedDeriv k (fun t : ℝ => t ^ (-2 : ℝ)) (d + a) by
    simpa using congrFun
      (iteratedDeriv_comp_add_const k (fun t : ℝ => t ^ (-2 : ℝ)) a) d]
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  have hcoeff : |(descPochhammer ℝ k).eval (-2 : ℝ)| = sec7_ra_inv2Scale k := by
    interval_cases k <;>
      simp [sec7_ra_inv2Scale, descPochhammer_eval_eq_prod_range] <;> norm_num
  have hpow_nonneg : 0 ≤ (d + a) ^ ((-2 : ℝ) - k) := (Real.rpow_pos_of_pos hda _).le
  calc
    |(descPochhammer ℝ k).eval (-2 : ℝ) * (d + a) ^ ((-2 : ℝ) - k)|
        = sec7_ra_inv2Scale k * (d + a) ^ ((-2 : ℝ) - k) := by
          rw [abs_mul, hcoeff, abs_of_nonneg hpow_nonneg]
    _ ≤ sec7_ra_inv2Scale k * d ^ ((-2 : ℝ) - k) :=
        mul_le_mul_of_nonneg_left hpow_le (by
          interval_cases k <;> norm_num [sec7_ra_inv2Scale])

private theorem sec7_ra_h_contDiffAt {a d : ℝ} {k : ℕ} (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ k (fun t => Real.sqrt (t + a) - Real.sqrt t) d := by
  have hda : 0 < d + a := by linarith
  have h1 : ContDiffAt ℝ k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d :=
    (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (ne_of_gt hda)
  have h2 : ContDiffAt ℝ k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) d :=
    contDiffAt_id.rpow_const_of_ne (ne_of_gt hd)
  have hsub := h1.sub h2
  have hfun :
      (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2) - t ^ ((1 : ℝ) / 2))
        = fun t : ℝ => Real.sqrt (t + a) - Real.sqrt t := by
    funext t
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rwa [hfun] at hsub

private theorem sec7_ra_hsq_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2) d|
      ≤ sec7_ra_hsqScale k * a ^ 2 * d ^ ((-1 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set h : ℝ → ℝ := fun t => Real.sqrt (t + a) - Real.sqrt t
  have hh : ContDiffAt ℝ k h d := by
    simpa [h] using sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
  have hpow_eq : (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2) =
      fun t => h t * h t := by
    funext t
    simp [h, sq]
  rw [hpow_eq, iteratedDeriv_fun_mul hh hh]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d|
        ≤ (k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i)
            * a ^ 2 * d ^ ((-1 : ℝ) - k) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 5 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 5 := le_trans (Nat.sub_le k i) hk
    have hb_i := (sec7_ra_h_atomic_bound (a := a) (d := d) (d_lo := d_lo)
      (k := i) hi5 ha hdlo hlo).2
    have hb_ki := (sec7_ra_h_atomic_bound (a := a) (d := d) (d_lo := d_lo)
      (k := k - i) hki5 ha hdlo hlo).2
    have hb_i' : |iteratedDeriv i h d| ≤ sec7_ra_hScale i * a * d ^ ((-1 : ℝ) / 2 - i) := by
      simpa [h] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) h d|
          ≤ sec7_ra_hScale (k - i) * a * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [h, hcast] using hb_ki
    have hpow :
        d ^ (((-1 : ℝ) / 2 - i) + ((-1 : ℝ) / 2 - ((k : ℝ) - i))) =
          d ^ ((-1 : ℝ) - k) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((-1 : ℝ) / 2 - i) * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)) =
          d ^ ((-1 : ℝ) - k) := by
      rw [← Real.rpow_add hd, hpow]
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) (by
      have hscale_i_nonneg : 0 ≤ sec7_ra_hScale i := by
        interval_cases i <;> norm_num [sec7_ra_hScale]
      have hnon : 0 ≤ sec7_ra_hScale i * a * d ^ ((-1 : ℝ) / 2 - i) := by
        exact mul_nonneg (mul_nonneg hscale_i_nonneg ha.le) (Real.rpow_pos_of_pos hd _).le
      exact hnon)
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d|
          = (k.choose i : ℝ) * (|iteratedDeriv i h d| * |iteratedDeriv (k - i) h d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_hScale i * a * d ^ ((-1 : ℝ) / 2 - i)) *
              (sec7_ra_hScale (k - i) * a * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i) * a ^ 2) *
            (d ^ ((-1 : ℝ) / 2 - i) * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i)
            * a ^ 2 * d ^ ((-1 : ℝ) - k) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i))
        = sec7_ra_hsqScale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_hScale, sec7_ra_hsqScale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

private theorem sec7_ra_hsq_inv_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k
        (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ)) d|
      ≤ sec7_ra_hsqInvScale k * a ^ 2 * d ^ ((-3 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set f : ℝ → ℝ := fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2
  set g : ℝ → ℝ := fun t => t ^ (-2 : ℝ)
  have hf : ContDiffAt ℝ k f d := by
    have hh := sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
    simpa [f, sq] using hh.mul hh
  have hg : ContDiffAt ℝ k g d := by
    simpa [g] using contDiffAt_id.rpow_const_of_ne (n := k) (p := (-2 : ℝ)) (ne_of_gt hd)
  have hfun :
      (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ)) =
        fun t => f t * g t := by
    funext t
    simp [f, g]
  rw [hfun, iteratedDeriv_fun_mul hf hg]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ (k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-3 : ℝ) - k) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 5 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 5 := le_trans (Nat.sub_le k i) hk
    have hb_i := sec7_ra_hsq_bound (a := a) (d := d) (d_lo := d_lo)
      (k := i) hi5 ha hdlo hlo
    have hb_ki := sec7_ra_inv2_bound (d := d) (d_lo := d_lo)
      (k := k - i) hki5 hdlo hlo
    have hb_i' : |iteratedDeriv i f d| ≤ sec7_ra_hsqScale i * a ^ 2 * d ^ ((-1 : ℝ) - i) := by
      simpa [f] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) g d|
          ≤ sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [g, hcast] using hb_ki
    have hpow :
        d ^ (((-1 : ℝ) - i) + ((-2 : ℝ) - ((k : ℝ) - i))) =
          d ^ ((-3 : ℝ) - k) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((-1 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) =
          d ^ ((-3 : ℝ) - k) := by
      rw [← Real.rpow_add hd, hpow]
    have hleft_nonneg : 0 ≤ sec7_ra_hsqScale i * a ^ 2 * d ^ ((-1 : ℝ) - i) := by
      have hscale : 0 ≤ sec7_ra_hsqScale i := by
        interval_cases i <;> norm_num [sec7_ra_hsqScale]
      exact mul_nonneg (mul_nonneg hscale (sq_nonneg a)) (Real.rpow_pos_of_pos hd _).le
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) hleft_nonneg
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
          = (k.choose i : ℝ) * (|iteratedDeriv i f d| * |iteratedDeriv (k - i) g d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_hsqScale i * a ^ 2 * d ^ ((-1 : ℝ) - i)) *
              (sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i) * a ^ 2) *
            (d ^ ((-1 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-3 : ℝ) - k) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i))
        = sec7_ra_hsqInvScale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_hsqScale, sec7_ra_inv2Scale,
        sec7_ra_hsqInvScale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

private theorem sec7_ra_rho_model_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k
        (fun t => ((Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ))
          * (t + a) ^ (-2 : ℝ)) d|
      ≤ sec7_ra_rhoScale k * a ^ 2 * d ^ ((-5 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have hda : 0 < d + a := by linarith
  set f : ℝ → ℝ := fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ)
  set g : ℝ → ℝ := fun t => (t + a) ^ (-2 : ℝ)
  have hf : ContDiffAt ℝ k f d := by
    have hh := sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
    have hhsq : ContDiffAt ℝ k (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2) d := by
      simpa [sq] using hh.mul hh
    have hinv : ContDiffAt ℝ k (fun t : ℝ => t ^ (-2 : ℝ)) d :=
      contDiffAt_id.rpow_const_of_ne (n := k) (p := (-2 : ℝ)) (ne_of_gt hd)
    simpa [f] using hhsq.mul hinv
  have hg : ContDiffAt ℝ k g d := by
    simpa [g] using
      (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (n := k) (p := (-2 : ℝ))
        (ne_of_gt hda)
  rw [show (fun t => ((Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ))
          * (t + a) ^ (-2 : ℝ)) = fun t => f t * g t by
    funext t
    simp [f, g]]
  rw [iteratedDeriv_fun_mul hf hg]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ (k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-5 : ℝ) - k) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 5 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 5 := le_trans (Nat.sub_le k i) hk
    have hb_i := sec7_ra_hsq_inv_bound (a := a) (d := d) (d_lo := d_lo)
      (k := i) hi5 ha hdlo hlo
    have hb_ki := sec7_ra_shift_inv2_bound (a := a) (d := d) (d_lo := d_lo)
      (k := k - i) hki5 ha hdlo hlo
    have hb_i' : |iteratedDeriv i f d| ≤ sec7_ra_hsqInvScale i * a ^ 2 * d ^ ((-3 : ℝ) - i) := by
      simpa [f] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) g d|
          ≤ sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [g, hcast] using hb_ki
    have hpow :
        d ^ (((-3 : ℝ) - i) + ((-2 : ℝ) - ((k : ℝ) - i))) =
          d ^ ((-5 : ℝ) - k) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((-3 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) =
          d ^ ((-5 : ℝ) - k) := by
      rw [← Real.rpow_add hd, hpow]
    have hleft_nonneg : 0 ≤ sec7_ra_hsqInvScale i * a ^ 2 * d ^ ((-3 : ℝ) - i) := by
      have hscale : 0 ≤ sec7_ra_hsqInvScale i := by
        interval_cases i <;> norm_num [sec7_ra_hsqInvScale]
      exact mul_nonneg (mul_nonneg hscale (sq_nonneg a)) (Real.rpow_pos_of_pos hd _).le
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) hleft_nonneg
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
          = (k.choose i : ℝ) * (|iteratedDeriv i f d| * |iteratedDeriv (k - i) g d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_hsqInvScale i * a ^ 2 * d ^ ((-3 : ℝ) - i)) *
              (sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i) * a ^ 2) *
            (d ^ ((-3 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-5 : ℝ) - k) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i))
        = sec7_ra_rhoScale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_hsqInvScale, sec7_ra_inv2Scale,
        sec7_ra_rhoScale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

theorem sec7_ra_rho_tower {X a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (hX : 0 < X) (ha : 0 < a) (hdlo : 0 < d_lo)
    (hlo : d_lo ≤ d) (_had : a ≤ d) :
    |iteratedDeriv k
        (fun t => Ffun X a t
          - 2 * X * a / (t ^ ((3 : ℝ) / 2) * (t + a) ^ ((3 : ℝ) / 2))) d|
      ≤ sec7_ra_rhoScale k * X * a ^ 3 * d ^ ((-5 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set model : ℝ → ℝ :=
    fun t => ((Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ))
      * (t + a) ^ (-2 : ℝ)
  have heqv :
      (fun t => Ffun X a t
          - 2 * X * a / (t ^ ((3 : ℝ) / 2) * (t + a) ^ ((3 : ℝ) / 2)))
        =ᶠ[nhds d] fun t => X * a * model t := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    simpa [model] using sec7_ra_residual_rho_factor_rpow (X := X) (a := a) (d := t) ht ha
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heqv]
  rw [iteratedDeriv_const_mul_field]
  have hmodel := sec7_ra_rho_model_bound (a := a) (d := d) (d_lo := d_lo)
    (k := k) hk ha hdlo hlo
  have hXa_nonneg : 0 ≤ X * a := (mul_pos hX ha).le
  calc
    |X * a * iteratedDeriv k model d| = X * a * |iteratedDeriv k model d| := by
      rw [abs_mul, abs_of_nonneg hXa_nonneg]
    _ ≤ X * a * (sec7_ra_rhoScale k * a ^ 2 * d ^ ((-5 : ℝ) - k)) :=
      mul_le_mul_of_nonneg_left hmodel hXa_nonneg
    _ = sec7_ra_rhoScale k * X * a ^ 3 * d ^ ((-5 : ℝ) - k) := by
      ring

end Squarefree
