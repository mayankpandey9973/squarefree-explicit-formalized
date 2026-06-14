import Squarefree.Geometry.NearCurveProof
import Squarefree.Geometry.NearCurveSpacing
import Mathlib

/-!
# §4.3 Type I: off-line spacing core and disjoint-interval packing (writeup 534–606)

This module isolates the analytic core of the §4.3 major-arc spacing argument,
the **off-line spacing lemma** `offLine_spacing` (writeup 534–562), and uses it
to bound the Type I total (writeup 581–605, `#typeISet ≤ 8(Nδ+1)`).

`offLine_spacing` is the reusable lemma (Type II needs it too): for a near-set
base point `m₀` ON a small-denominator line `D` and a near-set point `m` NOT on
`D`, the gap `|m − m₀|` satisfies the quadratic lower bound (writeup 560)
`1/(4q) ≤ |m−m₀|·(δ/L + 2λL) + λ(m−m₀)²`, where `L` is the projected span of the
arc and `q = D.denom`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

/-! ## The affine line value `P(x) = (p·x + shift)/q` -/

/-- The real value of the rational line `D` at `x`: `P(x) = (p·x + shift)/q`. -/
noncomputable def lineVal (D : MajorLine) (x : ℝ) : ℝ :=
  ((D.slope.num : ℝ) * x + (D.shift : ℝ)) / (D.denom : ℝ)

/-- On-line points: `P(n) = ℓ_n` (cast of the integer `OnLine` relation). -/
theorem lineVal_eq_latticeY {f : ℝ → ℝ} {D : MajorLine} {n : ℤ}
    (hn : OnLine f D n) : lineVal D (n : ℝ) = (latticeY f n : ℝ) := by
  have hq : (D.denom : ℝ) ≠ 0 := by
    have := D.denom_pos; positivity
  rw [lineVal, div_eq_iff hq]
  have : (D.denom : ℝ) * (latticeY f n : ℝ)
      = (D.slope.num : ℝ) * (n : ℝ) + (D.shift : ℝ) := by
    have h := hn
    simp only [OnLine] at h
    have : ((D.denom * latticeY f n : ℤ) : ℝ)
        = ((D.slope.num * n + D.shift : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  linarith [this]

/-- `P` has constant derivative `p/q` everywhere. -/
theorem hasDerivAt_lineVal (D : MajorLine) (x : ℝ) :
    HasDerivAt (lineVal D) ((D.slope.num : ℝ) / (D.denom : ℝ)) x := by
  have hq : (D.denom : ℝ) ≠ 0 := by have := D.denom_pos; positivity
  unfold lineVal
  have h1 : HasDerivAt (fun x : ℝ => (D.slope.num : ℝ) * x + (D.shift : ℝ))
      ((D.slope.num : ℝ)) x := by
    simpa using ((hasDerivAt_id x).const_mul (D.slope.num : ℝ)).add_const (D.shift : ℝ)
  have := h1.div_const (D.denom : ℝ)
  simpa [div_eq_mul_inv] using this

/-- **Off-line distance.**  If the lattice point `(m, ℓ_m)` does NOT lie on `D`,
then `P(m)` is at integer-distance `≥ 1/q` from `ℓ_m`:
`1/q ≤ |P(m) − ℓ_m|`.  Reason: `q·(P(m) − ℓ_m) = (p·m + shift) − q·ℓ_m` is a
nonzero integer. -/
theorem one_div_denom_le_of_not_onLine {f : ℝ → ℝ} {D : MajorLine} {m : ℤ}
    (hm : ¬ OnLine f D m) :
    1 / (D.denom : ℝ) ≤ |lineVal D (m : ℝ) - (latticeY f m : ℝ)| := by
  have hqpos : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  have hqne : (D.denom : ℝ) ≠ 0 := ne_of_gt hqpos
  -- The integer `k := p·m + shift − q·ℓ_m` is nonzero (else `OnLine`).
  set k : ℤ := D.slope.num * m + D.shift - D.denom * latticeY f m with hk
  have hkne : k ≠ 0 := by
    intro h0
    apply hm
    simp only [OnLine]
    have : D.slope.num * m + D.shift = D.denom * latticeY f m := by
      have : k = 0 := h0; omega
    omega
  -- `q·(P(m) − ℓ_m) = k` as reals.
  have hkeq : (D.denom : ℝ) * (lineVal D (m : ℝ) - (latticeY f m : ℝ)) = (k : ℝ) := by
    rw [lineVal]
    field_simp
    push_cast [hk]; ring
  -- `|k| ≥ 1`, so `|P(m)−ℓ_m| = |k|/q ≥ 1/q`.
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hkne
    have : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_one, Int.cast_abs] at this
  have : (D.denom : ℝ) * |lineVal D (m : ℝ) - (latticeY f m : ℝ)| = |(k : ℝ)| := by
    rw [← abs_of_pos hqpos, ← abs_mul, hkeq]
  rw [div_le_iff₀ hqpos]
  calc (1 : ℝ) ≤ |(k : ℝ)| := hk1
    _ = (D.denom : ℝ) * |lineVal D (m : ℝ) - (latticeY f m : ℝ)| := this.symm
    _ = |lineVal D (m : ℝ) - (latticeY f m : ℝ)| * (D.denom : ℝ) := by ring

/-! ## The residual `g = f − P` and its derivative facts -/

/-- The line-residual `g = f − P`. -/
noncomputable def lineRes (f : ℝ → ℝ) (D : MajorLine) (x : ℝ) : ℝ :=
  f x - lineVal D x

/-- `g = f − P` has derivative `f'(x) − p/q` wherever `f` is differentiable. -/
theorem hasDerivAt_lineRes {f : ℝ → ℝ} {D : MajorLine} {x : ℝ}
    (hf : HasDerivAt f (deriv f x) x) :
    HasDerivAt (lineRes f D) (deriv f x - (D.slope.num : ℝ) / (D.denom : ℝ)) x := by
  exact hf.sub (hasDerivAt_lineVal D x)

/-- `iteratedDeriv 2 f x = deriv (deriv f) x`. -/
theorem iteratedDeriv_two_eq {f : ℝ → ℝ} {x : ℝ} :
    iteratedDeriv 2 f x = deriv (deriv f) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- `f' = deriv f` has derivative `f''` everywhere when `f ∈ C²`. -/
theorem hasDerivAt_deriv_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
  have h1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (h1.differentiable one_ne_zero).differentiableAt.hasDerivAt
  rwa [← iteratedDeriv_two_eq] at this

/-- `f` has derivative `deriv f x` everywhere when `f ∈ C²`. -/
theorem hasDerivAt_self_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt

/-- **Lipschitz bound on `f'` between two points.**  If `|f''| ≤ Λ` on `[A, B]`
and `s, t ∈ [A, B]`, then `|f'(s) − f'(t)| ≤ Λ·|s − t|`. -/
theorem abs_deriv_sub_le {f : ℝ → ℝ} {Λ A B : ℝ} (hf : ContDiff ℝ 2 f)
    (hΛ : ∀ x ∈ Set.Icc A B, |iteratedDeriv 2 f x| ≤ Λ) {s t : ℝ}
    (hs : s ∈ Set.Icc A B) (ht : t ∈ Set.Icc A B) :
    |deriv f s - deriv f t| ≤ Λ * |s - t| := by
  -- Apply the segment MVT bound to `deriv f` with derivative `f''`.
  have hconv : Convex ℝ (Set.Icc A B) := convex_Icc A B
  have hderiv : ∀ x ∈ Set.Icc A B,
      HasDerivWithinAt (deriv f) (iteratedDeriv 2 f x) (Set.Icc A B) x :=
    fun x _ => (hasDerivAt_deriv_of_contDiff hf x).hasDerivWithinAt
  have hbound := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun x hx => by rw [Real.norm_eq_abs]; exact hΛ x hx) ht hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hbound
  exact hbound

/-- **MVT for `g = f − P` between two points.**  For `p < r`, there is `η ∈ (p, r)`
with `g(r) − g(p) = (r − p)·(f'(η) − p/q)`. -/
theorem lineRes_mvt {f : ℝ → ℝ} {D : MajorLine} (hf : ContDiff ℝ 2 f) {p r : ℝ}
    (hpr : p < r) :
    ∃ η ∈ Set.Ioo p r, lineRes f D r - lineRes f D p
      = (r - p) * (deriv f η - (D.slope.num : ℝ) / (D.denom : ℝ)) := by
  set gd : ℝ → ℝ := fun x => deriv f x - (D.slope.num : ℝ) / (D.denom : ℝ) with hgd
  have hcont : ContinuousOn (lineRes f D) (Set.Icc p r) := by
    apply Continuous.continuousOn
    exact (hf.continuous).sub (by unfold lineVal; fun_prop)
  have hderiv : ∀ x ∈ Set.Ioo p r, HasDerivAt (lineRes f D) (gd x) x := by
    intro x _
    exact hasDerivAt_lineRes (hasDerivAt_self_of_contDiff hf x)
  obtain ⟨η, hη, hslope⟩ := exists_hasDerivAt_eq_slope (lineRes f D) gd hpr hcont hderiv
  refine ⟨η, hη, ?_⟩
  have hne : r - p ≠ 0 := by linarith
  have : deriv f η - (D.slope.num : ℝ) / (D.denom : ℝ)
      = (lineRes f D r - lineRes f D p) / (r - p) := hslope
  rw [this]
  field_simp

/-- **Slope bound at the base point** (writeup 538–540).  If `|g| ≤ δ` at the arc
endpoints `A < B`, the base point `m₀ ∈ [A, B]`, and `|f''| ≤ 2λ` on `[A, B]`, then
`|g'(m₀)| ≤ 2δ/L + 2λL` where `L = B − A`.  Proof: MVT gives `ξ` on the arc with
`|g'(ξ)| ≤ 2δ/L`, then transfer to `m₀` by the `f''`-Lipschitz bound. -/
theorem lineRes_deriv_base_bound {f : ℝ → ℝ} {D : MajorLine} {lam δ A B m₀ : ℝ}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hAB : A < B)
    (hupper : ∀ x ∈ Set.Icc A B, |iteratedDeriv 2 f x| ≤ 256 * lam)
    (hgA : |lineRes f D A| ≤ δ) (hgB : |lineRes f D B| ≤ δ)
    (hm₀ : m₀ ∈ Set.Icc A B) :
    |deriv f m₀ - (D.slope.num : ℝ) / (D.denom : ℝ)|
      ≤ 2 * δ / (B - A) + 256 * lam * (B - A) := by
  set L : ℝ := B - A with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  -- MVT for `g` on `[A, B]`.
  obtain ⟨ξ, hξ, hξeq⟩ := lineRes_mvt (D := D) hf hAB
  have hξIcc : ξ ∈ Set.Icc A B := ⟨hξ.1.le, hξ.2.le⟩
  -- `|g'(ξ)| ≤ 2δ/L`.
  have hgξ : |deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ)| ≤ 2 * δ / L := by
    have hval : deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ)
        = (lineRes f D B - lineRes f D A) / (B - A) := by
      rw [hξeq, mul_comm, mul_div_assoc, div_self (by rw [← hLdef]; exact hLpos.ne'),
        mul_one]
    rw [hval, abs_div, abs_of_pos (by rw [← hLdef]; exact hLpos : (0:ℝ) < B - A)]
    rw [div_le_div_iff_of_pos_right (by rw [← hLdef]; exact hLpos)]
    calc |lineRes f D B - lineRes f D A|
        ≤ |lineRes f D B| + |lineRes f D A| := abs_sub _ _
      _ ≤ δ + δ := by linarith [hgA, hgB]
      _ = 2 * δ := by ring
  -- transfer to `m₀`: `|f'(m₀) − f'(ξ)| ≤ 2λ·|m₀ − ξ| ≤ 2λ·L`.
  have htrans : |deriv f m₀ - deriv f ξ| ≤ 256 * lam * L := by
    have h1 := abs_deriv_sub_le hf hupper hm₀ hξIcc
    have h2 : |m₀ - ξ| ≤ L := by
      rw [hLdef]
      rw [abs_le]; constructor <;> [linarith [hm₀.1, hξIcc.2]; linarith [hm₀.2, hξIcc.1]]
    calc |deriv f m₀ - deriv f ξ| ≤ 256 * lam * |m₀ - ξ| := h1
      _ ≤ 256 * lam * L := by apply mul_le_mul_of_nonneg_left h2 (by positivity)
  -- combine.
  calc |deriv f m₀ - (D.slope.num : ℝ) / (D.denom : ℝ)|
      = |(deriv f m₀ - deriv f ξ) + (deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ))| := by
        ring_nf
    _ ≤ |deriv f m₀ - deriv f ξ| + |deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ)| :=
        abs_add_le _ _
    _ ≤ 256 * lam * L + 2 * δ / L := by linarith [htrans, hgξ]
    _ = 2 * δ / (B - A) + 256 * lam * (B - A) := by rw [← hLdef]; ring

/-! ## The off-line spacing lemma (writeup 534–562) -/

/-- **Off-line spacing** (writeup 534–562).  Let `D` be a line with denominator
`q ≤ 1/(4δ)`, let the arc have real endpoints `A < B` with `|g| ≤ δ` at both
(here `g = f − P`), let `m₀ ∈ [A, B]` be the base point with `|g(m₀)| ≤ δ`, and
let `m` be an integer with `(m, ℓ_m)` NOT on `D`.  With `|f''| ≤ 2λ` on the
convex hull `[A ∧ m, B ∨ m]`, the gap satisfies the quadratic lower bound
`1/(4q) ≤ |m − m₀|·(2δ/L + 2λL) + 2λ·(m − m₀)²` where `L = B − A`. -/
theorem offLine_spacing {f : ℝ → ℝ} {D : MajorLine} {lam δ A B m₀ : ℝ} {m : ℤ}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ) (hAB : A < B)
    (hq : (D.denom : ℝ) ≤ 1 / (4 * δ))
    (hdom : ∀ x ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)),
      |iteratedDeriv 2 f x| ≤ 256 * lam)
    (hgA : |lineRes f D A| ≤ δ) (hgB : |lineRes f D B| ≤ δ)
    (hm₀ : m₀ ∈ Set.Icc A B) (hgm₀ : |lineRes f D m₀| ≤ δ)
    (hmne : (m : ℝ) ≠ m₀)
    (hmoff : ¬ OnLine f D m) (hfm : |f (m : ℝ) - (latticeY f m : ℝ)| ≤ δ) :
    1 / (4 * (D.denom : ℝ))
      ≤ |(m : ℝ) - m₀| * (2 * δ / (B - A) + 256 * lam * (B - A))
        + 256 * lam * |(m : ℝ) - m₀| ^ 2 := by
  set L : ℝ := B - A with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hqpos : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  -- `δ ≤ 1/(4q)` from `q ≤ 1/(4δ)`.
  have hδq : δ ≤ 1 / (4 * (D.denom : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hq' : (D.denom : ℝ) * (4 * δ) ≤ (1 / (4 * δ)) * (4 * δ) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    rw [one_div_mul_cancel (by positivity : (4 * δ : ℝ) ≠ 0)] at hq'
    nlinarith [hq', hqpos, hδ]
  -- `Icc A B ⊆ Icc (min A m) (max B m)`, base & endpoints in the big domain.
  have hbigsub : Set.Icc A B ⊆ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)) :=
    Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)
  have hupperAB : ∀ x ∈ Set.Icc A B, |iteratedDeriv 2 f x| ≤ 256 * lam :=
    fun x hx => hdom x (hbigsub hx)
  -- Step 1: slope bound at base point.
  have hbase := lineRes_deriv_base_bound (D := D) hf hlam hAB hupperAB hgA hgB hm₀
  rw [← hLdef] at hbase
  -- Step 2: lower bound `|g(m) − g(m₀)| ≥ 1/(2q)`.
  have hgm_lo : 1 / (D.denom : ℝ) - δ ≤ |lineRes f D (m : ℝ)| := by
    -- `|g(m)| = |f(m) − P(m)| ≥ |P(m) − ℓ_m| − |f(m) − ℓ_m| ≥ 1/q − δ`.
    have hPdist := one_div_denom_le_of_not_onLine (f := f) hmoff
    -- `g(m) = (f(m) − ℓ) − (P(m) − ℓ)`, reverse triangle.
    have hgeq : |lineRes f D (m : ℝ)|
        = |(lineVal D (m : ℝ) - (latticeY f m : ℝ)) - (f (m : ℝ) - (latticeY f m : ℝ))| := by
      rw [abs_sub_comm]; congr 1; unfold lineRes; ring
    have hrev : |lineVal D (m : ℝ) - (latticeY f m : ℝ)| - |f (m : ℝ) - (latticeY f m : ℝ)|
        ≤ |lineRes f D (m : ℝ)| := by
      rw [hgeq]
      exact abs_sub_abs_le_abs_sub (lineVal D (m : ℝ) - (latticeY f m : ℝ))
        (f (m : ℝ) - (latticeY f m : ℝ))
    linarith [hrev, hPdist, hfm]
  have hgdiff_lo : 1 / (2 * (D.denom : ℝ)) ≤ |lineRes f D (m : ℝ) - lineRes f D m₀| := by
    have htri : |lineRes f D (m : ℝ)| - |lineRes f D m₀|
        ≤ |lineRes f D (m : ℝ) - lineRes f D m₀| := by
      have := abs_sub_abs_le_abs_sub (lineRes f D (m : ℝ)) (lineRes f D m₀)
      linarith [this]
    have h1q : 1 / (D.denom : ℝ) - 2 * δ ≤ |lineRes f D (m : ℝ) - lineRes f D m₀| := by
      linarith [htri, hgm_lo, hgm₀]
    -- `1/q − 2δ ≥ 1/q − 1/(2q) = 1/(2q)`.
    have h2δ : 2 * δ ≤ 1 / (2 * (D.denom : ℝ)) := by
      have : (2 : ℝ) * (1 / (4 * (D.denom : ℝ))) = 1 / (2 * (D.denom : ℝ)) := by
        field_simp; ring
      calc 2 * δ ≤ 2 * (1 / (4 * (D.denom : ℝ))) := by linarith [hδq]
        _ = 1 / (2 * (D.denom : ℝ)) := this
    have hhalf : 1 / (D.denom : ℝ) - 1 / (2 * (D.denom : ℝ)) = 1 / (2 * (D.denom : ℝ)) := by
      field_simp; ring
    linarith [h1q, h2δ, hhalf]
  -- Step 3: MVT for `g` between `m₀` and `m`, with `gd η` bounded.
  -- Work on the ordered interval `[p, r]` and bound `|gd η|`.
  have hgmvt : ∃ η, |(m : ℝ) - m₀| * |deriv f η - (D.slope.num : ℝ) / (D.denom : ℝ)|
      = |lineRes f D (m : ℝ) - lineRes f D m₀|
      ∧ η ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ))
      ∧ |deriv f η - deriv f m₀| ≤ 256 * lam * |(m : ℝ) - m₀| := by
    rcases lt_or_gt_of_ne hmne with hlt | hgt
    · -- m < m₀
      obtain ⟨η, hη, heq⟩ := lineRes_mvt (D := D) hf hlt
      refine ⟨η, ?_, ?_, ?_⟩
      · -- `|↑m − m₀|·|gd η| = |g m₀ − g m| = |g m − g m₀|`.
        rw [abs_sub_comm (lineRes f D (m : ℝ)) (lineRes f D m₀), heq, abs_mul,
          abs_of_pos (by linarith : (0:ℝ) < m₀ - (m:ℝ)),
          abs_of_neg (by linarith : (m:ℝ) - m₀ < 0)]
        ring
      · refine ⟨?_, ?_⟩
        · exact le_trans (min_le_right _ _) (by linarith [hη.1] : (m:ℝ) ≤ η)
        · exact le_trans (by linarith [hη.2, hm₀.2] : η ≤ B) (le_max_left _ _)
      · have hηIcc : η ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)) :=
          ⟨le_trans (min_le_right _ _) (by linarith [hη.1] : (m:ℝ) ≤ η),
           le_trans (by linarith [hη.2, hm₀.2] : η ≤ B) (le_max_left _ _)⟩
        have hm₀Icc : m₀ ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)) := hbigsub hm₀
        calc |deriv f η - deriv f m₀| ≤ 256 * lam * |η - m₀| := abs_deriv_sub_le hf hdom hηIcc hm₀Icc
          _ ≤ 256 * lam * |(m : ℝ) - m₀| := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [abs_of_nonpos (by linarith [hη.2, hm₀.2] : η - m₀ ≤ 0),
                abs_of_nonpos (by linarith : (m:ℝ) - m₀ ≤ 0)]
              linarith [hη.1]
    · -- m₀ < m
      obtain ⟨η, hη, heq⟩ := lineRes_mvt (D := D) hf hgt
      refine ⟨η, ?_, ?_, ?_⟩
      · rw [heq, abs_mul, abs_of_pos (by linarith : (0:ℝ) < (m:ℝ) - m₀)]
      · refine ⟨?_, ?_⟩
        · exact le_trans (min_le_left _ _) (le_trans hm₀.1 (by linarith [hη.1] : m₀ ≤ η))
        · exact le_trans (by linarith [hη.2] : η ≤ (m:ℝ)) (le_max_right _ _)
      · have hηIcc : η ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)) :=
          ⟨le_trans (min_le_left _ _) (le_trans hm₀.1 (by linarith [hη.1] : m₀ ≤ η)),
           le_trans (by linarith [hη.2] : η ≤ (m:ℝ)) (le_max_right _ _)⟩
        have hm₀Icc : m₀ ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)) := hbigsub hm₀
        calc |deriv f η - deriv f m₀| ≤ 256 * lam * |η - m₀| := abs_deriv_sub_le hf hdom hηIcc hm₀Icc
          _ ≤ 256 * lam * |(m : ℝ) - m₀| := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [abs_of_nonneg (by linarith [hη.1, hm₀.1] : (0:ℝ) ≤ η - m₀),
                abs_of_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ) - m₀)]
              linarith [hη.2]
  obtain ⟨η, heq, _hηIcc, hηbound⟩ := hgmvt
  -- `|gd η| ≤ |gd m₀| + |f'(η) − f'(m₀)| ≤ (2δ/L + 2λL) + 2λ|m−m₀|`.
  have hgdη : |deriv f η - (D.slope.num : ℝ) / (D.denom : ℝ)|
      ≤ (2 * δ / L + 256 * lam * L) + 256 * lam * |(m : ℝ) - m₀| := by
    have hsplit : deriv f η - (D.slope.num : ℝ) / (D.denom : ℝ)
        = (deriv f η - deriv f m₀) + (deriv f m₀ - (D.slope.num : ℝ) / (D.denom : ℝ)) := by ring
    rw [hsplit]
    calc |(deriv f η - deriv f m₀) + (deriv f m₀ - (D.slope.num : ℝ) / (D.denom : ℝ))|
        ≤ |deriv f η - deriv f m₀| + |deriv f m₀ - (D.slope.num : ℝ) / (D.denom : ℝ)| :=
          abs_add_le _ _
      _ ≤ 256 * lam * |(m : ℝ) - m₀| + (2 * δ / L + 256 * lam * L) := by linarith [hηbound, hbase]
      _ = (2 * δ / L + 256 * lam * L) + 256 * lam * |(m : ℝ) - m₀| := by ring
  -- Combine: `1/(2q) ≤ |g(m)−g(m₀)| = |m−m₀|·|gd η| ≤ |m−m₀|(2δ/L+2λL) + 2λ(m−m₀)²`.
  have hmabs_nonneg : (0 : ℝ) ≤ |(m : ℝ) - m₀| := abs_nonneg _
  have hchain : |lineRes f D (m : ℝ) - lineRes f D m₀|
      ≤ |(m : ℝ) - m₀| * (2 * δ / L + 256 * lam * L) + 256 * lam * |(m : ℝ) - m₀| ^ 2 := by
    rw [← heq]
    calc |(m : ℝ) - m₀| * |deriv f η - (D.slope.num : ℝ) / (D.denom : ℝ)|
        ≤ |(m : ℝ) - m₀| * ((2 * δ / L + 256 * lam * L) + 256 * lam * |(m : ℝ) - m₀|) :=
          mul_le_mul_of_nonneg_left hgdη hmabs_nonneg
      _ = |(m : ℝ) - m₀| * (2 * δ / L + 256 * lam * L) + 256 * lam * |(m : ℝ) - m₀| ^ 2 := by ring
  -- `1/(4q) ≤ 1/(2q) ≤ |g(m)−g(m₀)| ≤ RHS`.
  have h4q2q : 1 / (4 * (D.denom : ℝ)) ≤ 1 / (2 * (D.denom : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity); linarith [hqpos]
  linarith [h4q2q, hgdiff_lo, hchain]

/-! ## Type I gap: the first term `d(A) = L/(qδ)` is the smallest (writeup 587–598) -/

/-- **Type I gap bound** (writeup 587–598).  For a *Type I* arc — one with
`L ≤ δ·√(q/λ)` — every off-line near-set point `m` is at distance
`≥ d(A)/24` from the base point `m₀`, where `d(A) := L/(qδ)`.  Derived from
`offLine_spacing`: under the Type I constraint, the linear term's coefficient is
`≤ 3δ/L` and the quadratic root term `1/(4√(λq))` dominates `d(A)/4`, so the
quadratic lower bound forces `|m − m₀| ≥ d(A)/24`. -/
theorem typeI_offLine_gap {f : ℝ → ℝ} {D : MajorLine} {lam δ A B m₀ : ℝ} {m : ℤ}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ) (hAB : A < B)
    (hq : (D.denom : ℝ) ≤ 1 / (4 * δ))
    (hdom : ∀ x ∈ Set.Icc (min A (m : ℝ)) (max B (m : ℝ)),
      |iteratedDeriv 2 f x| ≤ 256 * lam)
    (hgA : |lineRes f D A| ≤ δ) (hgB : |lineRes f D B| ≤ δ)
    (hm₀ : m₀ ∈ Set.Icc A B) (hgm₀ : |lineRes f D m₀| ≤ δ)
    (hmne : (m : ℝ) ≠ m₀)
    (hmoff : ¬ OnLine f D m) (hfm : |f (m : ℝ) - (latticeY f m : ℝ)| ≤ δ)
    (htypeI : (B - A) ≤ δ * Real.sqrt ((D.denom : ℝ) / (256 * lam))) :
    (B - A) / ((D.denom : ℝ) * δ) / 24 ≤ |(m : ℝ) - m₀| := by
  set L : ℝ := B - A with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hqpos : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  set q : ℝ := (D.denom : ℝ) with hqdef
  set g : ℝ := |(m : ℝ) - m₀| with hgdef
  have hgnn : 0 ≤ g := abs_nonneg _
  -- The quadratic spacing bound.
  have hspace := offLine_spacing hf hlam hδ hAB hq hdom hgA hgB hm₀ hgm₀ hmne hmoff hfm
  rw [← hLdef, ← hqdef, ← hgdef] at hspace
  -- `λL² ≤ δ/4`: from `L ≤ δ√(q/λ)` and `q ≤ 1/(4δ)`.
  have hδq : δ * q ≤ 1 / 4 := by
    rw [hqdef]
    have : (D.denom : ℝ) * (4 * δ) ≤ (1 / (4 * δ)) * (4 * δ) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    rw [one_div_mul_cancel (by positivity : (4 * δ : ℝ) ≠ 0)] at this
    nlinarith [this, hqpos, hδ]
  have hlamL2 : 256 * lam * L ^ 2 ≤ δ ^ 2 * q := by
    -- `L ≤ δ√(q/(256λ))` ⟹ `L² ≤ δ²·q/(256λ)` ⟹ `256λL² ≤ δ²q`.
    have hsq_nn : 0 ≤ δ * Real.sqrt (q / (256 * lam)) := by positivity
    have hL2 : L ^ 2 ≤ (δ * Real.sqrt (q / (256 * lam))) ^ 2 := by
      rw [hqdef] at htypeI ⊢
      exact pow_le_pow_left₀ hLpos.le htypeI 2
    have hsqsq : (δ * Real.sqrt (q / (256 * lam))) ^ 2 = δ ^ 2 * (q / (256 * lam)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsqsq] at hL2
    have : 256 * lam * L ^ 2 ≤ 256 * lam * (δ ^ 2 * (q / (256 * lam))) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    rw [show 256 * lam * (δ ^ 2 * (q / (256 * lam))) = δ ^ 2 * q by field_simp] at this
    exact this
  have hlamL2x : 256 * lam * L ^ 2 ≤ δ / 4 := by
    -- `δ²q = δ·(δq) ≤ δ·(1/4)`.
    have heq : δ ^ 2 * q = δ * (δ * q) := by ring
    rw [heq] at hlamL2
    have h2 : δ * (δ * q) ≤ δ * (1 / 4) := mul_le_mul_of_nonneg_left hδq hδ.le
    linarith [hlamL2, h2]
  -- coefficient bound: `256λL ≤ δ/(2L)`, so linear coeff `≤ 3δ/L`.
  have h2lamL : 256 * lam * L ≤ δ / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hlamL2x, hLpos]
  have hcoeff : 2 * δ / L + 256 * lam * L ≤ 3 * δ / L := by
    -- `2λL ≤ δ/(2L) ≤ δ/L`, and `2δ/L + δ/L = 3δ/L`.
    have hhalf : δ / (2 * L) ≤ δ / L := by
      apply div_le_div_of_nonneg_left hδ.le hLpos (by linarith)
    have hsum : 2 * δ / L + δ / L = 3 * δ / L := by
      field_simp; ring
    linarith [h2lamL, hhalf, hsum]
  -- Reformulate: `1/(4q) ≤ g·(3δ/L) + 2λg²`.
  have hspace2 : 1 / (4 * q) ≤ g * (3 * δ / L) + 256 * lam * g ^ 2 := by
    have hmono : g * (2 * δ / L + 256 * lam * L) ≤ g * (3 * δ / L) :=
      mul_le_mul_of_nonneg_left hcoeff hgnn
    linarith [hspace, hmono]
  -- Dichotomy: either linear term ≥ 1/(8q) or quadratic term ≥ 1/(8q).
  by_contra hcon
  push_neg at hcon
  -- `g < d(A)/24 = L/(24 q δ)`.
  have hg_small : g < L / (q * δ) / 24 := hcon
  -- Bound linear: `g·(3δ/L) < (L/(24qδ))·(3δ/L) = 1/(8q)`.
  have hlin : g * (3 * δ / L) < 1 / (8 * q) := by
    have : g * (3 * δ / L) < (L / (q * δ) / 24) * (3 * δ / L) := by
      apply mul_lt_mul_of_pos_right hg_small (by positivity)
    rw [show (L / (q * δ) / 24) * (3 * δ / L) = 1 / (8 * q) by
      field_simp; ring] at this
    exact this
  -- Bound quadratic: `g² < (L/(24qδ))²`, and `256λg² < ...`.
  -- `256λg² ≤ 256λ·(L/(24qδ))² = (256λL²)/(576 q²δ²) ≤ (δ²q)/(576 q²δ²) = 1/(576 q) ≤ 1/(8q)`.
  -- (The tightened Type I split `256λL² ≤ δ²q` keeps this curvature-independent.)
  have hquad : 256 * lam * g ^ 2 < 1 / (8 * q) := by
    have hg2 : g ^ 2 < (L / (q * δ) / 24) ^ 2 := by
      apply pow_lt_pow_left₀ hg_small hgnn (by norm_num)
    have h2lamg2 : 256 * lam * g ^ 2 < 256 * lam * (L / (q * δ) / 24) ^ 2 :=
      mul_lt_mul_of_pos_left hg2 (by positivity)
    -- `256λ·(L/(24qδ))² = (256 λL²)/(576 q²δ²)`.
    have hrw : 256 * lam * (L / (q * δ) / 24) ^ 2
        = (256 * lam * L ^ 2) / (576 * q ^ 2 * δ ^ 2) := by
      field_simp; ring
    rw [hrw] at h2lamg2
    -- `256λL² ≤ δ²q` ⟹ ratio ≤ δ²q/(576 q²δ²) = 1/(576 q) ≤ 1/(8q)`.
    have hden : (0 : ℝ) < 576 * q ^ 2 * δ ^ 2 := by positivity
    have hfrac : (256 * lam * L ^ 2) / (576 * q ^ 2 * δ ^ 2)
        ≤ (δ ^ 2 * q) / (576 * q ^ 2 * δ ^ 2) := by
      rw [div_le_div_iff_of_pos_right hden]; exact hlamL2
    have hsimp : (δ ^ 2 * q) / (576 * q ^ 2 * δ ^ 2) = 1 / (576 * q) := by
      field_simp
    rw [hsimp] at hfrac
    have h576 : 1 / (576 * q) ≤ 1 / (8 * q) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [hqpos]
    linarith [h2lamg2, hfrac, h576]
  -- contradiction: `1/(4q) ≤ lin + quad < 1/(8q) + 1/(8q) = 1/(4q)`.
  have : 1 / (4 * q) < 1 / (4 * q) := by
    calc 1 / (4 * q) ≤ g * (3 * δ / L) + 256 * lam * g ^ 2 := hspace2
      _ < 1 / (8 * q) + 1 / (8 * q) := by linarith [hlin, hquad]
      _ = 1 / (4 * q) := by field_simp; ring
  exact lt_irrefl _ this

/-- The Type I "arc-density" `d(A) = (b−a)/(qδ)` of a witness with endpoints
`a < b`, line denominator `q`, and the working `δ`.  (Moved here from
`NearCurvePacking` so the strip module `NearCurveStrip` can reference it without
importing the packing layer — see the §4.3 import restructure.) -/
noncomputable def arcDensity (D : MajorLine) (δ : ℝ) (a b : ℤ) : ℝ :=
  ((b : ℝ) - (a : ℝ)) / ((D.denom : ℝ) * δ)

end Squarefree.Geometry
