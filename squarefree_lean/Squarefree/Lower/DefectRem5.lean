import Mathlib

/-!
# §5 Step-4: the order-5 Taylor remainder of `1/(d+x)²`

This file extends the order-4 `rem`/`rem1`/`rem2` chain of `Squarefree/Lower/DefectExpand.lean`
by one polynomial term (keeping the Taylor polynomial through `x⁴/d⁶`), giving the order-5
remainder `rem3` of `1/(d+x)²`.  This is the analytic foundation for the `Ŝ_{a,b}` expansion
(writeup §5 Step-4).

`rem3 d x := 1/(d+x)² − (1/d² − 2x/d³ + 3x²/d⁴ − 4x³/d⁵ + 5x⁴/d⁶)`.

We compute its successive derivatives `rem3_1`, `rem3_2`, `rem3_3` via `HasDerivAt` (so the
signs are forced by the proofs, not asserted), establish that `rem3`, `rem3_1`, `rem3_2` all
vanish at `x = 0`, bound `|rem3_3 ζ| ≤ 160/d⁵` on the window `4|ζ| ≤ d`, and conclude the
pointwise remainder bound via a triple mean-value argument:

`|rem3 ζ| ≤ 160·|ζ|³/d⁵`   for `0 < d`, `4|ζ| ≤ d`.

(Only three derivatives vanish at `0`, so the gain is `|ζ|³`, not `|ζ|⁵`.)
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

section Expand5

variable {d x : ℝ}

/-- Order-5 Taylor remainder of `1/(d+x)²` at the base point `d` (Taylor polynomial through
`x⁴/d⁶`). -/
private noncomputable def rem3 (d x : ℝ) : ℝ :=
  1 / (d + x) ^ 2 -
    (1 / d ^ 2 - 2 * x / d ^ 3 + 3 * x ^ 2 / d ^ 4 - 4 * x ^ 3 / d ^ 5 + 5 * x ^ 4 / d ^ 6)

/-- First derivative of `rem3 d ·`. -/
private noncomputable def rem3_1 (d x : ℝ) : ℝ :=
  -2 / (d + x) ^ 3 + 2 / d ^ 3 - 6 * x / d ^ 4 + 12 * x ^ 2 / d ^ 5 - 20 * x ^ 3 / d ^ 6

/-- Second derivative of `rem3 d ·`. -/
private noncomputable def rem3_2 (d x : ℝ) : ℝ :=
  6 / (d + x) ^ 4 - 6 / d ^ 4 + 24 * x / d ^ 5 - 60 * x ^ 2 / d ^ 6

/-- Third derivative of `rem3 d ·`. -/
private noncomputable def rem3_3 (d x : ℝ) : ℝ :=
  -24 / (d + x) ^ 5 + 24 / d ^ 5 - 120 * x / d ^ 6

/-- `rem3` vanishes at `x = 0`. -/
private theorem rem3_zero : rem3 d 0 = 0 := by
  simp only [rem3, add_zero]
  ring

/-- `rem3_1` vanishes at `x = 0`. -/
private theorem rem3_1_zero : rem3_1 d 0 = 0 := by
  simp only [rem3_1, add_zero]
  ring

/-- `rem3_2` vanishes at `x = 0`. -/
private theorem rem3_2_zero : rem3_2 d 0 = 0 := by
  simp only [rem3_2, add_zero]
  ring

/-- `HasDerivAt (rem3 d ·) (rem3_1 d x) x` whenever `d ≠ 0` and `d + x ≠ 0`. -/
private theorem rem3_hasDerivAt (hd : d ≠ 0) (hdx : d + x ≠ 0) :
    HasDerivAt (fun y => rem3 d y) (rem3_1 d x) x := by
  have hbase : HasDerivAt (fun y => (d + y)) 1 x := by
    simpa using (hasDerivAt_id x).const_add d
  have hsq : HasDerivAt (fun y => (d + y) ^ 2) (2 * (d + x) ^ 1 * 1) x :=
    hbase.pow 2
  have hsqne : (d + x) ^ 2 ≠ 0 := pow_ne_zero 2 hdx
  have hinv : HasDerivAt (fun y => 1 / (d + y) ^ 2)
      (-(2 * (d + x) ^ 1 * 1) / ((d + x) ^ 2) ^ 2) x := by
    simpa [one_div] using hsq.inv hsqne
  -- the polynomial part
  have hx2 : HasDerivAt (fun y => y ^ 2) (2 * x ^ 1 * 1) x := (hasDerivAt_id x).pow 2
  have hx3 : HasDerivAt (fun y => y ^ 3) (3 * x ^ 2 * 1) x := (hasDerivAt_id x).pow 3
  have hx4 : HasDerivAt (fun y => y ^ 4) (4 * x ^ 3 * 1) x := (hasDerivAt_id x).pow 4
  have hpoly : HasDerivAt
      (fun y => 1 / d ^ 2 - 2 * y / d ^ 3 + 3 * y ^ 2 / d ^ 4 - 4 * y ^ 3 / d ^ 5
        + 5 * y ^ 4 / d ^ 6)
      (-2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5 + 20 * x ^ 3 / d ^ 6) x := by
    have t1 : HasDerivAt (fun y => 2 * y / d ^ 3) (2 / d ^ 3) x := by
      have := ((hasDerivAt_id x).const_mul (2 : ℝ)).div_const (d ^ 3)
      simpa using this
    have t2 : HasDerivAt (fun y => 3 * y ^ 2 / d ^ 4) (6 * x / d ^ 4) x := by
      have := (hx2.const_mul (3 : ℝ)).div_const (d ^ 4)
      have h2 : (3 : ℝ) * (2 * x ^ 1 * 1) / d ^ 4 = 6 * x / d ^ 4 := by ring
      rw [h2] at this; exact this
    have t3 : HasDerivAt (fun y => 4 * y ^ 3 / d ^ 5) (12 * x ^ 2 / d ^ 5) x := by
      have := (hx3.const_mul (4 : ℝ)).div_const (d ^ 5)
      have h3 : (4 : ℝ) * (3 * x ^ 2 * 1) / d ^ 5 = 12 * x ^ 2 / d ^ 5 := by ring
      rw [h3] at this; exact this
    have t4 : HasDerivAt (fun y => 5 * y ^ 4 / d ^ 6) (20 * x ^ 3 / d ^ 6) x := by
      have := (hx4.const_mul (5 : ℝ)).div_const (d ^ 6)
      have h4 : (5 : ℝ) * (4 * x ^ 3 * 1) / d ^ 6 = 20 * x ^ 3 / d ^ 6 := by ring
      rw [h4] at this; exact this
    have hc : HasDerivAt (fun _ : ℝ => 1 / d ^ 2) 0 x := hasDerivAt_const x _
    have hraw := (((hc.sub t1).add t2).sub t3).add t4
    have hde : (0 : ℝ) - 2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5 + 20 * x ^ 3 / d ^ 6
        = -2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5 + 20 * x ^ 3 / d ^ 6 := by ring
    rw [hde] at hraw
    exact hraw
  have hraw := hinv.sub hpoly
  have hde : -(2 * (d + x) ^ 1 * 1) / ((d + x) ^ 2) ^ 2 -
        (-2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5 + 20 * x ^ 3 / d ^ 6) = rem3_1 d x := by
    simp only [rem3_1]
    field_simp
    ring
  rw [hde] at hraw
  exact hraw

/-- `HasDerivAt (rem3_1 d ·) (rem3_2 d x) x` whenever `d ≠ 0` and `d + x ≠ 0`. -/
private theorem rem3_1_hasDerivAt (hd : d ≠ 0) (hdx : d + x ≠ 0) :
    HasDerivAt (fun y => rem3_1 d y) (rem3_2 d x) x := by
  have hbase : HasDerivAt (fun y => (d + y)) 1 x := by
    simpa using (hasDerivAt_id x).const_add d
  have hcube : HasDerivAt (fun y => (d + y) ^ 3) (3 * (d + x) ^ 2 * 1) x :=
    hbase.pow 3
  have hcubene : (d + x) ^ 3 ≠ 0 := pow_ne_zero 3 hdx
  have h1 : HasDerivAt (fun y => 1 / (d + y) ^ 3)
      (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2) x := by
    simpa [one_div] using hcube.inv hcubene
  have hinv : HasDerivAt (fun y => -2 / (d + y) ^ 3)
      (-2 * (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2)) x := by
    have hraw := h1.const_mul (-2 : ℝ)
    have hfe : (fun y => -2 * (1 / (d + y) ^ 3)) = (fun y => -2 / (d + y) ^ 3) := by
      ext y; rw [mul_one_div]
    rw [hfe] at hraw
    exact hraw
  have hx2 : HasDerivAt (fun y => y ^ 2) (2 * x ^ 1 * 1) x := (hasDerivAt_id x).pow 2
  have hx3 : HasDerivAt (fun y => y ^ 3) (3 * x ^ 2 * 1) x := (hasDerivAt_id x).pow 3
  have hpoly : HasDerivAt
      (fun y => 2 / d ^ 3 - 6 * y / d ^ 4 + 12 * y ^ 2 / d ^ 5 - 20 * y ^ 3 / d ^ 6)
      (-6 / d ^ 4 + 24 * x / d ^ 5 - 60 * x ^ 2 / d ^ 6) x := by
    have t1 : HasDerivAt (fun y => 6 * y / d ^ 4) (6 / d ^ 4) x := by
      have := ((hasDerivAt_id x).const_mul (6 : ℝ)).div_const (d ^ 4)
      simpa using this
    have t2 : HasDerivAt (fun y => 12 * y ^ 2 / d ^ 5) (24 * x / d ^ 5) x := by
      have := (hx2.const_mul (12 : ℝ)).div_const (d ^ 5)
      have h2 : (12 : ℝ) * (2 * x ^ 1 * 1) / d ^ 5 = 24 * x / d ^ 5 := by ring
      rw [h2] at this; exact this
    have t3 : HasDerivAt (fun y => 20 * y ^ 3 / d ^ 6) (60 * x ^ 2 / d ^ 6) x := by
      have := (hx3.const_mul (20 : ℝ)).div_const (d ^ 6)
      have h3 : (20 : ℝ) * (3 * x ^ 2 * 1) / d ^ 6 = 60 * x ^ 2 / d ^ 6 := by ring
      rw [h3] at this; exact this
    have hc : HasDerivAt (fun _ : ℝ => 2 / d ^ 3) 0 x := hasDerivAt_const x _
    have hraw := ((hc.sub t1).add t2).sub t3
    have hde : (0 : ℝ) - 6 / d ^ 4 + 24 * x / d ^ 5 - 60 * x ^ 2 / d ^ 6
        = -6 / d ^ 4 + 24 * x / d ^ 5 - 60 * x ^ 2 / d ^ 6 := by ring
    rw [hde] at hraw
    exact hraw
  have hcombined : HasDerivAt
      (fun y => -2 / (d + y) ^ 3
        + (2 / d ^ 3 - 6 * y / d ^ 4 + 12 * y ^ 2 / d ^ 5 - 20 * y ^ 3 / d ^ 6))
      (-2 * (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2) +
        (-6 / d ^ 4 + 24 * x / d ^ 5 - 60 * x ^ 2 / d ^ 6)) x := hinv.add hpoly
  have hfun_eq : (fun y => -2 / (d + y) ^ 3
        + (2 / d ^ 3 - 6 * y / d ^ 4 + 12 * y ^ 2 / d ^ 5 - 20 * y ^ 3 / d ^ 6))
      = (fun y => rem3_1 d y) := by
    ext y; simp only [rem3_1]; ring
  have hderiv_eq : -2 * (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2) +
        (-6 / d ^ 4 + 24 * x / d ^ 5 - 60 * x ^ 2 / d ^ 6) = rem3_2 d x := by
    simp only [rem3_2]
    field_simp
    ring
  rw [hfun_eq, hderiv_eq] at hcombined
  exact hcombined

/-- `HasDerivAt (rem3_2 d ·) (rem3_3 d x) x` whenever `d ≠ 0` and `d + x ≠ 0`. -/
private theorem rem3_2_hasDerivAt (hd : d ≠ 0) (hdx : d + x ≠ 0) :
    HasDerivAt (fun y => rem3_2 d y) (rem3_3 d x) x := by
  have hbase : HasDerivAt (fun y => (d + y)) 1 x := by
    simpa using (hasDerivAt_id x).const_add d
  have hq : HasDerivAt (fun y => (d + y) ^ 4) (4 * (d + x) ^ 3 * 1) x :=
    hbase.pow 4
  have hqne : (d + x) ^ 4 ≠ 0 := pow_ne_zero 4 hdx
  have h1 : HasDerivAt (fun y => 1 / (d + y) ^ 4)
      (-(4 * (d + x) ^ 3 * 1) / ((d + x) ^ 4) ^ 2) x := by
    simpa [one_div] using hq.inv hqne
  have hinv : HasDerivAt (fun y => 6 / (d + y) ^ 4)
      (6 * (-(4 * (d + x) ^ 3 * 1) / ((d + x) ^ 4) ^ 2)) x := by
    have hraw := h1.const_mul (6 : ℝ)
    have hfe : (fun y => 6 * (1 / (d + y) ^ 4)) = (fun y => 6 / (d + y) ^ 4) := by
      ext y; rw [mul_one_div]
    rw [hfe] at hraw
    exact hraw
  have hx2 : HasDerivAt (fun y => y ^ 2) (2 * x ^ 1 * 1) x := (hasDerivAt_id x).pow 2
  have hpoly : HasDerivAt
      (fun y => -6 / d ^ 4 + 24 * y / d ^ 5 - 60 * y ^ 2 / d ^ 6)
      (24 / d ^ 5 - 120 * x / d ^ 6) x := by
    have t1 : HasDerivAt (fun y => 24 * y / d ^ 5) (24 / d ^ 5) x := by
      have := ((hasDerivAt_id x).const_mul (24 : ℝ)).div_const (d ^ 5)
      simpa using this
    have t2 : HasDerivAt (fun y => 60 * y ^ 2 / d ^ 6) (120 * x / d ^ 6) x := by
      have := (hx2.const_mul (60 : ℝ)).div_const (d ^ 6)
      have h2 : (60 : ℝ) * (2 * x ^ 1 * 1) / d ^ 6 = 120 * x / d ^ 6 := by ring
      rw [h2] at this; exact this
    have hc : HasDerivAt (fun _ : ℝ => -6 / d ^ 4) 0 x := hasDerivAt_const x _
    have hraw := (hc.add t1).sub t2
    have hde : (0 : ℝ) + 24 / d ^ 5 - 120 * x / d ^ 6 = 24 / d ^ 5 - 120 * x / d ^ 6 := by ring
    rw [hde] at hraw
    exact hraw
  have hcombined : HasDerivAt
      (fun y => 6 / (d + y) ^ 4 + (-6 / d ^ 4 + 24 * y / d ^ 5 - 60 * y ^ 2 / d ^ 6))
      (6 * (-(4 * (d + x) ^ 3 * 1) / ((d + x) ^ 4) ^ 2) +
        (24 / d ^ 5 - 120 * x / d ^ 6)) x := hinv.add hpoly
  have hfun_eq : (fun y => 6 / (d + y) ^ 4 + (-6 / d ^ 4 + 24 * y / d ^ 5 - 60 * y ^ 2 / d ^ 6))
      = (fun y => rem3_2 d y) := by
    ext y; simp only [rem3_2]; ring
  have hderiv_eq : 6 * (-(4 * (d + x) ^ 3 * 1) / ((d + x) ^ 4) ^ 2) +
        (24 / d ^ 5 - 120 * x / d ^ 6) = rem3_3 d x := by
    simp only [rem3_3]
    field_simp
    ring
  rw [hfun_eq, hderiv_eq] at hcombined
  exact hcombined

end Expand5

/-- If `t` lies in the unordered interval `[[0, a]]` then `|t| ≤ |a|`. -/
private theorem abs_le_of_mem_uIcc_zero {a t : ℝ} (ht : t ∈ Set.uIcc (0:ℝ) a) :
    |t| ≤ |a| := by
  rw [Set.uIcc, Set.mem_Icc] at ht
  rcases le_total 0 a with ha | ha
  · rw [inf_eq_left.mpr ha, sup_eq_right.mpr ha] at ht
    rw [abs_of_nonneg ha, abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
  · rw [inf_eq_right.mpr ha, sup_eq_left.mpr ha] at ht
    rw [abs_of_nonpos ha, abs_le]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- A single mean-value step on the window between `0` and `a`: if `f 0 = 0`, `f` has
derivative `f' t` at every `t` with `|t| ≤ |a|`, and `|f' t| ≤ M` there, then `|f a| ≤ M·|a|`. -/
private theorem mvt_window {f f' : ℝ → ℝ} {a M : ℝ} (hf0 : f 0 = 0)
    (hderiv : ∀ t, |t| ≤ |a| → HasDerivAt f (f' t) t)
    (hbound : ∀ t, |t| ≤ |a| → |f' t| ≤ M) :
    |f a| ≤ M * |a| := by
  have hsub : ∀ t ∈ Set.uIcc (0:ℝ) a, HasDerivWithinAt f (f' t) (Set.uIcc (0:ℝ) a) t :=
    fun t ht => (hderiv t (abs_le_of_mem_uIcc_zero ht)).hasDerivWithinAt
  have hbnd : ∀ t ∈ Set.uIcc (0:ℝ) a, ‖f' t‖ ≤ M := by
    intro t ht
    simpa [Real.norm_eq_abs] using hbound t (abs_le_of_mem_uIcc_zero ht)
  have := (convex_uIcc (0:ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le hsub hbnd
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  rw [hf0, sub_zero, sub_zero] at this
  simpa [Real.norm_eq_abs] using this

/-- Bound on the third-derivative remainder `rem3_3`, valid for any `ζ` with `4·|ζ| ≤ d`
(so `d + ζ > 0` and `d + ζ ∈ [3d/4, 5d/4]`).  Constant `160` is non-sharp but explicit. -/
private theorem rem3_3_abs_bound {d ζ : ℝ} (hd : 0 < d) (hζd : 4 * |ζ| ≤ d) :
    |rem3_3 d ζ| ≤ 160 / d ^ 5 := by
  have hpair := abs_le.mp (by linarith [hζd] : |ζ| ≤ d / 4)
  have hζhi : ζ ≤ d / 4 := hpair.2
  have hζlo : -(d / 4) ≤ ζ := hpair.1
  have hdz : 0 < d + ζ := by linarith
  have hdz5 : (0:ℝ) < (d + ζ) ^ 5 := by positivity
  have hd5 : (0:ℝ) < d ^ 5 := by positivity
  have hd6 : (0:ℝ) < d ^ 6 := by positivity
  have hcd : (0:ℝ) < d ^ 6 * (d + ζ) ^ 5 := by positivity
  -- write rem3_3 over the common denominator d⁶·(d+ζ)⁵
  have hrw : rem3_3 d ζ
      = (-24 * d ^ 6 + 24 * d * (d + ζ) ^ 5 - 120 * ζ * (d + ζ) ^ 5)
        / (d ^ 6 * (d + ζ) ^ 5) := by
    simp only [rem3_3]
    field_simp
  have hbnd : (160 : ℝ) / d ^ 5
      = (160 * d * (d + ζ) ^ 5) / (d ^ 6 * (d + ζ) ^ 5) := by
    rw [eq_div_iff (ne_of_gt hcd)]
    field_simp
  -- a lower bound `d + ζ ≥ 3d/4 > 0` and upper bound `d + ζ ≤ 5d/4`
  have hlo : 3 * d / 4 ≤ d + ζ := by linarith
  have hhi : d + ζ ≤ 5 * d / 4 := by linarith
  -- (d+ζ)⁵ is between (3d/4)⁵ and (5d/4)⁵
  have h34 : (0:ℝ) ≤ 3 * d / 4 := by linarith
  have hpow_lo : (3 * d / 4) ^ 5 ≤ (d + ζ) ^ 5 := by gcongr
  have hpow_hi : (d + ζ) ^ 5 ≤ (5 * d / 4) ^ 5 := by gcongr
  rw [hrw, hbnd, abs_div, abs_of_pos hcd, div_le_div_iff_of_pos_right hcd, abs_le]
  -- N := -24d⁶ + 24d(d+ζ)⁵ - 120ζ(d+ζ)⁵, B := 160d(d+ζ)⁵.  Show -B ≤ N ≤ B.
  refine ⟨?_, ?_⟩
  · -- -B ≤ N  ⟺  0 ≤ N + B = -24d⁶ + 184d(d+ζ)⁵ - 120ζ(d+ζ)⁵
    nlinarith [hpow_lo, hpow_hi, hdz5, hd5, hd6, hd, hζlo, hζhi,
      mul_nonneg hd5.le (sub_nonneg.mpr hpow_lo),
      mul_nonneg (sub_nonneg.mpr hpow_lo) (sub_nonneg.mpr (le_of_lt hd))]
  · -- N ≤ B  ⟺  0 ≤ B - N = 24d⁶ + 136d(d+ζ)⁵ + 120ζ(d+ζ)⁵
    nlinarith [hpow_lo, hpow_hi, hdz5, hd5, hd6, hd, hζlo, hζhi,
      mul_nonneg hd5.le (sub_nonneg.mpr hpow_lo),
      mul_nonneg (sub_nonneg.mpr hpow_lo) (sub_nonneg.mpr (le_of_lt hd))]

/-- **Pointwise order-5 remainder bound** (writeup §5 Step-4 foundation).  Since `rem3`,
`rem3_1`, `rem3_2` all vanish at `0` and `|rem3_3| ≤ 160/d⁵` on the window `4|ζ| ≤ d`, a
triple mean-value argument gives `|rem3 ζ| ≤ 160·|ζ|³/d⁵`. -/
theorem rem3_abs_le {d ζ : ℝ} (hd : 0 < d) (hζd : 4 * |ζ| ≤ d) :
    |rem3 d ζ| ≤ 160 * |ζ| ^ 3 / d ^ 5 := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hd5 : (0:ℝ) < d ^ 5 := by positivity
  have hpair := abs_le.mp (by linarith [hζd] : |ζ| ≤ d / 4)
  have hζhi : ζ ≤ d / 4 := hpair.2
  have hζlo : -(d / 4) ≤ ζ := hpair.1
  -- on the closed interval between 0 and ζ, every point `t` has `4|t| ≤ d` (so `d + t > 0`).
  -- We package the window bound for any `t` lying between 0 and ζ.
  have hwin : ∀ t : ℝ, |t| ≤ |ζ| → 4 * |t| ≤ d := fun t ht => le_trans (by linarith [ht]) hζd
  have hposwin : ∀ t : ℝ, |t| ≤ |ζ| → d + t ≠ 0 := by
    intro t ht
    have := hwin t ht
    have htp := abs_le.mp (by linarith [this] : |t| ≤ d / 4)
    exact ne_of_gt (by linarith [htp.1])
  -- A reusable single-MVT step: for g vanishing at 0 with |g'| bounded by M/d^k on the window
  -- between 0 and ζ, |g ζ| ≤ (M/d^k)·|ζ|.  We instantiate it three times.
  -- Step A: |rem3_2 ζ| ≤ 160/d⁵ · |ζ|  (rem3_2 0 = 0, deriv rem3_3 bounded by 160/d⁵).
  have stepA : |rem3_2 d ζ| ≤ (160 / d ^ 5) * |ζ| := by
    rcases eq_or_lt_of_le (abs_nonneg ζ) with hz0 | hzpos
    · -- ζ = 0
      have : ζ = 0 := abs_eq_zero.mp hz0.symm
      simp [this, rem3_2_zero]
    · -- general: MVT on the interval between 0 and ζ
      have key : ∀ t, |t| ≤ |ζ| → HasDerivAt (fun y => rem3_2 d y) (rem3_3 d t) t :=
        fun t ht => rem3_2_hasDerivAt hd0 (hposwin t ht)
      -- bound on |rem3_3| over the window
      have hbnd : ∀ t, |t| ≤ |ζ| → |rem3_3 d t| ≤ 160 / d ^ 5 :=
        fun t ht => rem3_3_abs_bound hd (hwin t ht)
      have := mvt_window (f := fun y => rem3_2 d y) (f' := fun y => rem3_3 d y)
        (a := ζ) (M := 160 / d ^ 5) (by simpa using rem3_2_zero) key hbnd
      simpa using this
  -- Step B: |rem3_1 ζ| ≤ 160/d⁵ · |ζ|²  via MVT with deriv rem3_2, bounded by stepA-type bound.
  have stepB : |rem3_1 d ζ| ≤ (160 / d ^ 5) * |ζ| ^ 2 := by
    rcases eq_or_lt_of_le (abs_nonneg ζ) with hz0 | hzpos
    · have : ζ = 0 := abs_eq_zero.mp hz0.symm
      simp [this, rem3_1_zero]
    · have key : ∀ t, |t| ≤ |ζ| → HasDerivAt (fun y => rem3_1 d y) (rem3_2 d t) t :=
        fun t ht => rem3_1_hasDerivAt hd0 (hposwin t ht)
      -- |rem3_2 t| ≤ (160/d⁵)·|t| ≤ (160/d⁵)·|ζ| over the window
      have hbnd : ∀ t, |t| ≤ |ζ| → |rem3_2 d t| ≤ (160 / d ^ 5) * |ζ| := by
        intro t ht
        have h1 : |rem3_2 d t| ≤ (160 / d ^ 5) * |t| := by
          rcases eq_or_lt_of_le (abs_nonneg t) with ht0 | htpos
          · have : t = 0 := abs_eq_zero.mp ht0.symm
            simp [this, rem3_2_zero]
          · have keyt : ∀ s, |s| ≤ |t| → HasDerivAt (fun y => rem3_2 d y) (rem3_3 d s) s :=
              fun s hs => rem3_2_hasDerivAt hd0 (hposwin s (le_trans hs ht))
            have hbt : ∀ s, |s| ≤ |t| → |rem3_3 d s| ≤ 160 / d ^ 5 :=
              fun s hs => rem3_3_abs_bound hd (hwin s (le_trans hs ht))
            simpa using mvt_window (f := fun y => rem3_2 d y) (f' := fun y => rem3_3 d y)
              (a := t) (M := 160 / d ^ 5) (by simpa using rem3_2_zero) keyt hbt
        have hM : (0:ℝ) ≤ 160 / d ^ 5 := by positivity
        exact le_trans h1 (by gcongr)
      have := mvt_window (f := fun y => rem3_1 d y) (f' := fun y => rem3_2 d y)
        (a := ζ) (M := (160 / d ^ 5) * |ζ|) (by simpa using rem3_1_zero) key hbnd
      calc |rem3_1 d ζ| ≤ (160 / d ^ 5) * |ζ| * |ζ| := by simpa using this
        _ = (160 / d ^ 5) * |ζ| ^ 2 := by ring
  -- Step C: |rem3 ζ| ≤ 160/d⁵ · |ζ|³  via MVT with deriv rem3_1, bounded by stepB-type bound.
  have stepC : |rem3 d ζ| ≤ (160 / d ^ 5) * |ζ| ^ 3 := by
    rcases eq_or_lt_of_le (abs_nonneg ζ) with hz0 | hzpos
    · have : ζ = 0 := abs_eq_zero.mp hz0.symm
      simp [this, rem3_zero]
    · have key : ∀ t, |t| ≤ |ζ| → HasDerivAt (fun y => rem3 d y) (rem3_1 d t) t :=
        fun t ht => rem3_hasDerivAt hd0 (hposwin t ht)
      have hbnd : ∀ t, |t| ≤ |ζ| → |rem3_1 d t| ≤ (160 / d ^ 5) * |ζ| ^ 2 := by
        intro t ht
        have h1 : |rem3_1 d t| ≤ (160 / d ^ 5) * |t| ^ 2 := by
          rcases eq_or_lt_of_le (abs_nonneg t) with ht0 | htpos
          · have : t = 0 := abs_eq_zero.mp ht0.symm
            simp [this, rem3_1_zero]
          · have keyt : ∀ s, |s| ≤ |t| → HasDerivAt (fun y => rem3_1 d y) (rem3_2 d s) s :=
              fun s hs => rem3_1_hasDerivAt hd0 (hposwin s (le_trans hs ht))
            have hbt : ∀ s, |s| ≤ |t| → |rem3_2 d s| ≤ (160 / d ^ 5) * |t| := by
              intro s hs
              have h2 : |rem3_2 d s| ≤ (160 / d ^ 5) * |s| := by
                rcases eq_or_lt_of_le (abs_nonneg s) with hs0 | hspos
                · have : s = 0 := abs_eq_zero.mp hs0.symm
                  simp [this, rem3_2_zero]
                · have keys : ∀ r, |r| ≤ |s| → HasDerivAt (fun y => rem3_2 d y) (rem3_3 d r) r :=
                    fun r hr => rem3_2_hasDerivAt hd0
                      (hposwin r (le_trans hr (le_trans hs ht)))
                  have hbs : ∀ r, |r| ≤ |s| → |rem3_3 d r| ≤ 160 / d ^ 5 :=
                    fun r hr => rem3_3_abs_bound hd (hwin r (le_trans hr (le_trans hs ht)))
                  simpa using mvt_window (f := fun y => rem3_2 d y) (f' := fun y => rem3_3 d y)
                    (a := s) (M := 160 / d ^ 5) (by simpa using rem3_2_zero) keys hbs
              have hM : (0:ℝ) ≤ 160 / d ^ 5 := by positivity
              exact le_trans h2 (by gcongr)
            have := mvt_window (f := fun y => rem3_1 d y) (f' := fun y => rem3_2 d y)
              (a := t) (M := (160 / d ^ 5) * |t|) (by simpa using rem3_1_zero) keyt hbt
            calc |rem3_1 d t| ≤ (160 / d ^ 5) * |t| * |t| := by simpa using this
              _ = (160 / d ^ 5) * |t| ^ 2 := by ring
        have hM : (0:ℝ) ≤ 160 / d ^ 5 := by positivity
        have hsq : |t| ^ 2 ≤ |ζ| ^ 2 := by gcongr
        calc |rem3_1 d t| ≤ (160 / d ^ 5) * |t| ^ 2 := h1
          _ ≤ (160 / d ^ 5) * |ζ| ^ 2 := by gcongr
      have := mvt_window (f := fun y => rem3 d y) (f' := fun y => rem3_1 d y)
        (a := ζ) (M := (160 / d ^ 5) * |ζ| ^ 2) (by simpa using rem3_zero) key hbnd
      calc |rem3 d ζ| ≤ (160 / d ^ 5) * |ζ| ^ 2 * |ζ| := by simpa using this
        _ = (160 / d ^ 5) * |ζ| ^ 3 := by ring
  -- repackage
  calc |rem3 d ζ| ≤ (160 / d ^ 5) * |ζ| ^ 3 := stepC
    _ = 160 * |ζ| ^ 3 / d ^ 5 := by ring

end Squarefree
