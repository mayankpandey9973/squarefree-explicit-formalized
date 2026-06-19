import Squarefree.Geometry.NearCurveStrip
import Mathlib

/-!
# §4.3 convex-arc height bound (writeup 624–642)

The generic analytic lemma behind the convex-argmin `b`-localization.

**Statement.**  Let `H` be convex on `[A, B]` with `H'' ≥ λ > 0` on the interior, attaining
its minimum `M = H x₀` at `x₀ ∈ [A, B]`.  Suppose a *long* strip-arc `[lo, hi] ⊆ [A, B]`
(length `> δ√(q/λ)`) satisfies `|H − w| ≤ δ` for some real height `w`.  Then the height is
forced near the minimum:
```
  w ≤ M + δ + 4/q.
```
(The companion lower bound `M − δ ≤ w` is trivial: `M = H x₀ ≤ H lo ≤ w + δ` since `x₀` is the
minimum and `lo` lies in the arc; we prove it inline at the call site.)

This is the convex Taylor estimate of writeup 626–642, packaged generically so the host
`NearCurveTypeII` module can apply it to `H := lineSign' • lineRes f D₀`.  It imports only
`NearCurveStrip` and `Mathlib`; it does **not** import `NearCurveTypeII`, so there is no cycle.
-/

open Set

namespace Squarefree.Geometry

/-- **At a global minimum `x₀` with a point to its right (`x₀ < B`), the derivative is
nonnegative.**  Standard Fermat-at-a-boundary fact via the positive tangent cone of the
interval (the Darboux-file pattern):  `0 ≤ (B−x₀)·H'(x₀)` and `B−x₀ > 0`. -/
private theorem deriv_nonneg_at_min_left {H : ℝ → ℝ} {A B x₀ : ℝ}
    (hx₀mem : x₀ ∈ Set.Icc A B) (hx₀min : IsMinOn H (Set.Icc A B) x₀)
    (hHdx₀ : DifferentiableAt ℝ H x₀) (hx₀B : x₀ < B) :
    0 ≤ deriv H x₀ := by
  have hsub : segment ℝ x₀ B ⊆ Set.Icc A B := by
    rw [segment_eq_Icc hx₀mem.2]
    exact Set.Icc_subset_Icc hx₀mem.1 le_rfl
  have hcone : B - x₀ ∈ posTangentConeAt (Set.Icc A B) x₀ :=
    sub_mem_posTangentConeAt_of_segment_subset hsub
  have hfd : HasFDerivWithinAt H (ContinuousLinearMap.smulRight 1 (deriv H x₀))
      (Set.Icc A B) x₀ := hHdx₀.hasDerivAt.hasDerivWithinAt
  have hnn := hx₀min.localize.hasFDerivWithinAt_nonneg hfd hcone
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul] at hnn
  -- `0 ≤ (B − x₀) · deriv H x₀` with `B − x₀ > 0`.
  exact nonneg_of_mul_nonneg_right hnn (by linarith)

/-- **At a global minimum `x₀` with a point to its left (`A < x₀`), the derivative is
nonpositive** (mirror of `deriv_nonneg_at_min_left`). -/
private theorem deriv_nonpos_at_min_right {H : ℝ → ℝ} {A B x₀ : ℝ}
    (hx₀mem : x₀ ∈ Set.Icc A B) (hx₀min : IsMinOn H (Set.Icc A B) x₀)
    (hHdx₀ : DifferentiableAt ℝ H x₀) (hAx₀ : A < x₀) :
    deriv H x₀ ≤ 0 := by
  have hsub : segment ℝ x₀ A ⊆ Set.Icc A B := by
    rw [segment_symm, segment_eq_Icc hx₀mem.1]
    exact Set.Icc_subset_Icc le_rfl hx₀mem.2
  have hcone : A - x₀ ∈ posTangentConeAt (Set.Icc A B) x₀ :=
    sub_mem_posTangentConeAt_of_segment_subset hsub
  have hfd : HasFDerivWithinAt H (ContinuousLinearMap.smulRight 1 (deriv H x₀))
      (Set.Icc A B) x₀ := hHdx₀.hasDerivAt.hasDerivWithinAt
  have hnn := hx₀min.localize.hasFDerivWithinAt_nonneg hfd hcone
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul] at hnn
  -- `0 ≤ (A − x₀) · deriv H x₀` with `A − x₀ < 0` ⟹ `deriv H x₀ ≤ 0`.
  by_contra hpos
  push Not at hpos
  have : (A - x₀) * deriv H x₀ < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
  linarith [hnn, this]

/-- **Strong-convexity bound on the derivative gap** (`λ·(y−x) ≤ H'(y) − H'(x)`).  Packaged
from `Convex.mul_sub_le_image_sub_of_le_deriv` applied to `g := deriv H`, whose derivative is
`H'' ≥ λ` on the interior. -/
private theorem deriv_gap_lower {H : ℝ → ℝ} {A B lam : ℝ}
    (hHc' : ContinuousOn (deriv H) (Set.Icc A B))
    (hHd' : DifferentiableOn ℝ (deriv H) (Set.Ioo A B))
    (hH'' : ∀ x ∈ Set.Ioo A B, lam ≤ deriv (deriv H) x)
    {x y : ℝ} (hx : x ∈ Set.Icc A B) (hy : y ∈ Set.Icc A B) (hxy : x ≤ y) :
    lam * (y - x) ≤ deriv H y - deriv H x := by
  have hconv : Convex ℝ (Set.Icc A B) := convex_Icc A B
  have hd' : DifferentiableOn ℝ (deriv H) (interior (Set.Icc A B)) := by
    rw [interior_Icc]; exact hHd'
  have hge : ∀ x ∈ interior (Set.Icc A B), lam ≤ deriv (deriv H) x := by
    rw [interior_Icc]; exact hH''
  exact hconv.mul_sub_le_image_sub_of_le_deriv hHc' hd' hge x hx y hy hxy

/-- **A long strip-arc of a strongly convex function sits near its minimum** (writeup
624–642).  With `H` convex on `[A,B]`, `H'' ≥ λ > 0` on the interior, minimum `M = H x₀`,
and a long arc `[lo,hi] ⊆ [A,B]` whose length exceeds the *tightened* split scale
`δ√(q/μ)` (with the split curvature `μ ≥ λ`) on which `|H − w| ≤ δ`, the height `w`
cannot exceed the minimum by more than `δ + 4·(μ/λ)/q`.  The genuine lower bound is `λ`
(used in the Taylor/argmin step), while the long-arc scale uses `μ` (the §4.3 upper
curvature `256λ`); they are decoupled so that `μ > λ` costs only the constant `μ/λ`. -/
theorem convex_arc_height_le_min {H : ℝ → ℝ} {A B x₀ M w lo hi δ lam mu q : ℝ}
    (hHc : ContinuousOn H (Set.Icc A B))
    (hHd : ∀ x ∈ Set.Icc A B, DifferentiableAt ℝ H x)
    (hHc' : ContinuousOn (deriv H) (Set.Icc A B))
    (hHd' : DifferentiableOn ℝ (deriv H) (Set.Ioo A B))
    (hconv : ConvexOn ℝ (Set.Icc A B) H)
    (hH'' : ∀ x ∈ Set.Ioo A B, lam ≤ deriv (deriv H) x)
    (hx₀mem : x₀ ∈ Set.Icc A B) (hx₀min : IsMinOn H (Set.Icc A B) x₀) (hM : M = H x₀)
    (hlo : lo ∈ Set.Icc A B) (hhi : hi ∈ Set.Icc A B) (hlohi : lo < hi)
    (hstrip : ∀ x ∈ Set.Icc lo hi, |H x - w| ≤ δ)
    (hlong : δ * Real.sqrt (q / mu) < hi - lo) (hq : 0 < q) (hlam : 0 < lam)
    (hmu : lam ≤ mu) (hδ : 0 < δ) :
    w ≤ M + δ + 4 * (mu / lam) / q := by
  classical
  have hmupos : 0 < mu := lt_of_lt_of_le hlam hmu
  set L : ℝ := hi - lo with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  -- Endpoints of the arc are in the strip.
  have hstrip_lo : |H lo - w| ≤ δ := hstrip lo ⟨le_rfl, hlohi.le⟩
  have hstrip_hi : |H hi - w| ≤ δ := hstrip hi ⟨hlohi.le, le_rfl⟩
  have hMlo : M ≤ H lo := by rw [hM]; exact hx₀min hlo
  have hMhi : M ≤ H hi := by rw [hM]; exact hx₀min hhi
  -- The "long-arc kills the Taylor term" arithmetic:  4δ²/(λL²) < 4·(μ/λ)/q.
  -- (`δ√(q/μ) < L ⟹ μL² > δ²q ⟹ λL² > (λ/μ)δ²q ⟹ 4δ²/(λL²) < 4μ/(λq)`.)
  have hkey_long : 4 * δ ^ 2 / (lam * L ^ 2) < 4 * (mu / lam) / q := by
    -- From `δ√(q/μ) < L` and positivity, `L² > δ²·q/μ`, hence `μL² > δ²q`.
    have hsqrt_pos : 0 < Real.sqrt (q / mu) := Real.sqrt_pos.mpr (by positivity)
    have hWpos : 0 < δ * Real.sqrt (q / mu) := by positivity
    have hsq : (δ * Real.sqrt (q / mu)) ^ 2 < L ^ 2 := by
      have := sq_lt_sq' (by linarith only [hWpos.le, hLpos] : -(L) < δ * Real.sqrt (q / mu)) hlong
      linarith only [this]
    have hsqrtsq : Real.sqrt (q / mu) * Real.sqrt (q / mu) = q / mu :=
      Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ q / mu)
    have hexpand : (δ * Real.sqrt (q / mu)) ^ 2 = δ ^ 2 * (q / mu) := by
      rw [mul_pow]; rw [sq (Real.sqrt (q / mu)), hsqrtsq]
    rw [hexpand] at hsq
    -- `δ²·q/μ < L²` ⟹ `δ²q < μL²` ⟹ `4δ²/(λL²) < 4μ/(λq)`.
    have hδ2q : δ ^ 2 * q < mu * L ^ 2 := by
      have hql : δ ^ 2 * (q / mu) * mu < L ^ 2 * mu :=
        mul_lt_mul_of_pos_right hsq hmupos
      have hcancel : δ ^ 2 * (q / mu) * mu = δ ^ 2 * q := by
        field_simp
      linarith only [hql, hcancel]
    rw [div_lt_div_iff₀ (by positivity) hq]
    -- Goal: `4δ²·q < 4(μ/λ)·(λL²)`.  RHS `= 4μL²`; from `δ²q < μL²`.
    have hexp : 4 * (mu / lam) * (lam * L ^ 2) = 4 * (mu * L ^ 2) := by
      field_simp
    rw [hexp]
    linarith only [hδ2q]
  -- Convenient closed-interval differentiability facts.
  have hHdIcc : ∀ x ∈ Set.Icc lo hi, DifferentiableAt ℝ H x := fun x hx =>
    hHd x ⟨le_trans hlo.1 hx.1, le_trans hx.2 hhi.2⟩
  have harc_sub : Set.Icc lo hi ⊆ Set.Icc A B := fun x hx =>
    ⟨le_trans hlo.1 hx.1, le_trans hx.2 hhi.2⟩
  -- MVT on `[lo, hi]`: `∃ ξ ∈ (lo, hi)`, `deriv H ξ = (H hi − H lo)/L`, and `|deriv H ξ| ≤ 2δ/L`.
  have hHdOn_arc : DifferentiableOn ℝ H (Set.Ioo lo hi) := fun x hx =>
    (hHd x ⟨(lt_of_le_of_lt hlo.1 hx.1).le, (lt_of_lt_of_le hx.2 hhi.2).le⟩).differentiableWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope H hlohi (hHc.mono harc_sub) hHdOn_arc
  have hξIcc : ξ ∈ Set.Icc A B := harc_sub ⟨hξ.1.le, hξ.2.le⟩
  have hξloR : lo ≤ ξ := hξ.1.le
  have hξhiR : ξ ≤ hi := hξ.2.le
  -- `|H hi − H lo| ≤ 2δ`.
  have hHhilo : |H hi - H lo| ≤ 2 * δ := by
    calc |H hi - H lo| ≤ |H hi - w| + |H lo - w| := by
          rw [show H hi - H lo = (H hi - w) - (H lo - w) by ring]; exact abs_sub _ _
      _ ≤ δ + δ := by linarith [hstrip_hi, hstrip_lo]
      _ = 2 * δ := by ring
  have hderivξ_le : deriv H ξ ≤ 2 * δ / L := by
    rw [hξeq, hLdef]
    rw [div_le_div_iff_of_pos_right hLpos]
    calc H hi - H lo ≤ |H hi - H lo| := le_abs_self _
      _ ≤ 2 * δ := hHhilo
  have hderivξ_ge : -(2 * δ / L) ≤ deriv H ξ := by
    rw [hξeq, hLdef]
    rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right hLpos]
    calc -(H hi - H lo) ≤ |H hi - H lo| := neg_le_abs _
      _ ≤ 2 * δ := hHhilo
  -- Trichotomy on the position of `x₀` relative to the arc.
  rcases le_or_gt lo x₀ with hlox₀ | hx₀lt
  · rcases le_or_gt x₀ hi with hx₀hi | hhilt
    · -- CASE x₀ ∈ [lo, hi]:  |H x₀ − w| ≤ δ ⟹ w ≤ M + δ.
      have hd := hstrip x₀ ⟨hlox₀, hx₀hi⟩
      rw [abs_le] at hd
      rw [hM]
      have h4q : (0 : ℝ) ≤ 4 * (mu / lam) / q := by positivity
      linarith [hd.1]
    · -- CASE hi < x₀:  arc to the LEFT of x₀.  Mirror of the right-arc case.
      have hhix₀ : hi < x₀ := hhilt
      have hx₀hi : 0 < x₀ - hi := by linarith
      -- Tangent at `hi` (right point `x₀`): `deriv H hi ≤ slope H hi x₀`.
      have htang : deriv H hi ≤ slope H hi x₀ :=
        hconv.deriv_le_slope hhi hx₀mem hhix₀ (hHd hi hhi)
      have hslope_eq : slope H hi x₀ = (H x₀ - H hi) / (x₀ - hi) := slope_def_field H hi x₀
      -- `slope ≤ 0` (since `H x₀ = M ≤ H hi`), hence `deriv H hi ≤ 0`.
      have hslope_np : slope H hi x₀ ≤ 0 := by
        rw [hslope_eq]; apply div_nonpos_of_nonpos_of_nonneg _ hx₀hi.le
        rw [← hM]; linarith [hMhi]
      have hderivhi_np : deriv H hi ≤ 0 := le_trans htang hslope_np
      -- `-2δ/L ≤ deriv H ξ ≤ deriv H hi ≤ 0` (strong-convexity gap, `ξ ≤ hi`).
      have hgapξhi : lam * (hi - ξ) ≤ deriv H hi - deriv H ξ :=
        deriv_gap_lower hHc' hHd' hH'' hξIcc hhi hξhiR
      have hderivhi_ge : -(2 * δ / L) ≤ deriv H hi := by
        have h0 : 0 ≤ lam * (hi - ξ) := mul_nonneg hlam.le (by linarith [hξhiR])
        linarith [hgapξhi, hderivξ_ge, h0]
      -- `deriv H x₀ ≤ 0` (min, point `hi < x₀` to the left ⟹ `A < x₀`).
      have hAx₀ : A < x₀ := lt_of_le_of_lt hhi.1 hhix₀
      have hderivx₀_np : deriv H x₀ ≤ 0 :=
        deriv_nonpos_at_min_right hx₀mem hx₀min (hHd x₀ hx₀mem) hAx₀
      -- Strong-convexity gap `hi ≤ x₀`: `lam·(x₀ − hi) ≤ deriv H x₀ − deriv H hi ≤ −deriv H hi`.
      have hgaphix₀ : lam * (x₀ - hi) ≤ deriv H x₀ - deriv H hi :=
        deriv_gap_lower hHc' hHd' hH'' hhi hx₀mem hhix₀.le
      have hhi_x₀_bound : lam * (x₀ - hi) ≤ 2 * δ / L := by
        linarith [hgaphix₀, hderivx₀_np, hderivhi_ge]
      -- Tangent at `hi`: `H hi − M ≤ (−deriv H hi)·(x₀ − hi)`.
      have htaylor : H hi - M ≤ (-deriv H hi) * (x₀ - hi) := by
        have hh := htang
        rw [hslope_eq, le_div_iff₀ hx₀hi] at hh
        have hring : (-deriv H hi) * (x₀ - hi) = -(deriv H hi * (x₀ - hi)) := by ring
        rw [hM, hring]; linarith [hh]
      -- `lam·(H hi − M) ≤ (−deriv H hi)·(lam·(x₀ − hi)) ≤ (2δ/L)² = 4δ²/L²`.
      have hH2δ : (0 : ℝ) ≤ 2 * δ / L := by positivity
      have hnegderiv_nn : 0 ≤ -deriv H hi := by linarith [hderivhi_np]
      have hnegderiv_le : -deriv H hi ≤ 2 * δ / L := by linarith [hderivhi_ge]
      have hlamHhi : lam * (H hi - M) ≤ 4 * δ ^ 2 / L ^ 2 := by
        have h1 : lam * (H hi - M) ≤ lam * ((-deriv H hi) * (x₀ - hi)) :=
          mul_le_mul_of_nonneg_left htaylor hlam.le
        have h3 : (-deriv H hi) * (lam * (x₀ - hi)) ≤ (2 * δ / L) * (2 * δ / L) :=
          mul_le_mul hnegderiv_le hhi_x₀_bound (mul_nonneg hlam.le hx₀hi.le) hH2δ
        have h4 : (2 * δ / L) * (2 * δ / L) = 4 * δ ^ 2 / L ^ 2 := by
          rw [div_mul_div_comm]; congr 1 <;> ring
        calc lam * (H hi - M) ≤ lam * ((-deriv H hi) * (x₀ - hi)) := h1
          _ = (-deriv H hi) * (lam * (x₀ - hi)) := by ring
          _ ≤ (2 * δ / L) * (2 * δ / L) := h3
          _ = 4 * δ ^ 2 / L ^ 2 := h4
      have hHhiM : H hi - M < 4 * (mu / lam) / q := by
        have hdiv : H hi - M ≤ 4 * δ ^ 2 / (lam * L ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          have hstep := mul_le_mul_of_nonneg_right hlamHhi (sq_nonneg L)
          rw [div_mul_cancel₀ _ (by positivity : (L:ℝ) ^ 2 ≠ 0)] at hstep
          linear_combination hstep
        linarith [hdiv, hkey_long]
      -- `w ≤ H hi + δ ≤ M + 4/q + δ`.
      rw [abs_le] at hstrip_hi
      linarith [hstrip_hi.1, hHhiM]
  · -- CASE x₀ < lo:  arc to the RIGHT of x₀.
    -- `slope H x₀ lo = (H lo − M)/(lo − x₀) ≥ 0` since `H lo ≥ M`.
    have hx₀lo : x₀ < lo := hx₀lt
    have hloMx₀ : 0 < lo - x₀ := by linarith
    -- Tangent at `lo` (left point `x₀`): `slope H x₀ lo ≤ deriv H lo`.
    have htang : slope H x₀ lo ≤ deriv H lo :=
      hconv.slope_le_deriv hx₀mem hlo hx₀lo (hHd lo hlo)
    have hslope_eq : slope H x₀ lo = (H lo - H x₀) / (lo - x₀) := slope_def_field H x₀ lo
    -- `0 ≤ slope`, hence `0 ≤ deriv H lo`.
    have hslope_nn : 0 ≤ slope H x₀ lo := by
      rw [hslope_eq]; apply div_nonneg _ hloMx₀.le; rw [← hM]; linarith [hMlo]
    have hderivlo_nn : 0 ≤ deriv H lo := le_trans hslope_nn htang
    -- `deriv H lo ≤ deriv H ξ ≤ 2δ/L` (strong-convexity gap, `lo ≤ ξ`).
    have hgaploξ : lam * (ξ - lo) ≤ deriv H ξ - deriv H lo :=
      deriv_gap_lower hHc' hHd' hH'' hlo hξIcc hξloR
    have hderivlo_le : deriv H lo ≤ 2 * δ / L := by
      have h0 : 0 ≤ lam * (ξ - lo) := mul_nonneg hlam.le (by linarith [hξloR])
      linarith [hgaploξ, hderivξ_le, h0]
    -- `0 ≤ deriv H x₀` (min, point `lo > x₀` to the right ⟹ `x₀ < B`).
    have hx₀B : x₀ < B := lt_of_lt_of_le hx₀lo hlo.2
    have hderivx₀_nn : 0 ≤ deriv H x₀ :=
      deriv_nonneg_at_min_left hx₀mem hx₀min (hHd x₀ hx₀mem) hx₀B
    -- Strong-convexity gap `x₀ ≤ lo`: `lam·(lo − x₀) ≤ deriv H lo − deriv H x₀ ≤ deriv H lo`.
    have hgapx₀lo : lam * (lo - x₀) ≤ deriv H lo - deriv H x₀ :=
      deriv_gap_lower hHc' hHd' hH'' hx₀mem hlo hx₀lo.le
    have hlo_x₀_bound : lam * (lo - x₀) ≤ 2 * δ / L := by
      linarith [hgapx₀lo, hderivx₀_nn, hderivlo_le]
    -- Tangent at `lo`: `H lo − M ≤ deriv H lo · (lo − x₀)`.
    have htaylor : H lo - M ≤ deriv H lo * (lo - x₀) := by
      have := htang
      rw [hslope_eq] at this
      rw [div_le_iff₀ hloMx₀] at this
      rw [hM]; linarith [this]
    -- `H lo − M ≤ (2δ/L)·(lo − x₀)` and `lam·(lo−x₀) ≤ 2δ/L`.
    -- Multiply: `lam·(H lo − M) ≤ (2δ/L)·lam·(lo − x₀) ≤ (2δ/L)² = 4δ²/L²`.
    have hH2δ : (0 : ℝ) ≤ 2 * δ / L := by positivity
    have hlamHlo : lam * (H lo - M) ≤ 4 * δ ^ 2 / L ^ 2 := by
      have h1 : lam * (H lo - M) ≤ lam * (deriv H lo * (lo - x₀)) :=
        mul_le_mul_of_nonneg_left htaylor hlam.le
      have h3 : deriv H lo * (lam * (lo - x₀)) ≤ (2 * δ / L) * (2 * δ / L) :=
        mul_le_mul hderivlo_le hlo_x₀_bound (mul_nonneg hlam.le hloMx₀.le) hH2δ
      have h4 : (2 * δ / L) * (2 * δ / L) = 4 * δ ^ 2 / L ^ 2 := by
        rw [div_mul_div_comm]; congr 1 <;> ring
      calc lam * (H lo - M) ≤ lam * (deriv H lo * (lo - x₀)) := h1
        _ = deriv H lo * (lam * (lo - x₀)) := by ring
        _ ≤ (2 * δ / L) * (2 * δ / L) := h3
        _ = 4 * δ ^ 2 / L ^ 2 := h4
    -- `H lo − M ≤ 4δ²/(λL²) < 4/q`.
    have hHloM : H lo - M < 4 * (mu / lam) / q := by
      have hdiv : H lo - M ≤ 4 * δ ^ 2 / (lam * L ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        -- `(H lo − M)·(λL²) ≤ 4δ²`:  from `λ·(H lo − M) ≤ 4δ²/L²` times `L²`.
        have hstep := mul_le_mul_of_nonneg_right hlamHlo (sq_nonneg L)
        rw [div_mul_cancel₀ _ (by positivity : (L:ℝ) ^ 2 ≠ 0)] at hstep
        linear_combination hstep
      linarith [hdiv, hkey_long]
    -- Finally `w ≤ H lo + δ ≤ M + 4/q + δ`.
    rw [abs_le] at hstrip_lo
    linarith [hstrip_lo.1, hHloM]
