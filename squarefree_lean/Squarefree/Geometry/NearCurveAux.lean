/-
Auxiliary analysis for the §4.3 non-collinear-triple spacing bound.

Main result: the second divided-difference mean-value theorem
`secondDividedDiff_eq_half_secondDeriv`, proved by Rolle's theorem applied twice
to the Newton interpolation error.
-/
import Mathlib

namespace Squarefree

open Set

/-- **Second divided-difference mean-value theorem.**
For `f` twice continuously differentiable on `[x₀, x₂]` and three ordered nodes
`x₀ < x₁ < x₂`, the second divided difference of `f` equals half the second
derivative at some interior point `ξ`.  This is the engine of the §4.3
non-collinear-triple spacing bound.  The second derivative is written as
`iteratedDeriv 2 f`. -/
theorem secondDividedDiff_eq_half_secondDeriv {f : ℝ → ℝ} {x₀ x₁ x₂ : ℝ}
    (h01 : x₀ < x₁) (h12 : x₁ < x₂)
    (hf : ContDiffOn ℝ 2 f (Set.Icc x₀ x₂)) :
    ∃ ξ ∈ Set.Ioo x₀ x₂,
      f x₀ / ((x₀ - x₁) * (x₀ - x₂)) + f x₁ / ((x₁ - x₀) * (x₁ - x₂))
        + f x₂ / ((x₂ - x₀) * (x₂ - x₁)) = iteratedDeriv 2 f ξ / 2 := by
  have h02 : x₀ < x₂ := h01.trans h12
  -- positive denominators
  have d10 : x₁ - x₀ > 0 := by linarith
  have d20 : x₂ - x₀ > 0 := by linarith
  have d21 : x₂ - x₁ > 0 := by linarith
  have n10 : x₁ - x₀ ≠ 0 := by linarith
  have n01 : x₀ - x₁ ≠ 0 := by linarith
  have n20 : x₂ - x₀ ≠ 0 := by linarith
  have n02 : x₀ - x₂ ≠ 0 := by linarith
  have n21 : x₂ - x₁ ≠ 0 := by linarith
  have n12 : x₁ - x₂ ≠ 0 := by linarith
  -- abbreviations
  set L : ℝ := f x₀ / ((x₀ - x₁) * (x₀ - x₂)) + f x₁ / ((x₁ - x₀) * (x₁ - x₂))
      + f x₂ / ((x₂ - x₀) * (x₂ - x₁)) with hL
  set s : ℝ := (f x₁ - f x₀) / (x₁ - x₀) with hs
  -- the Newton interpolation error
  set g : ℝ → ℝ := fun x => f x - (f x₀ + s * (x - x₀) + L * (x - x₀) * (x - x₁))
    with hg
  -- first derivative of `g`
  set g' : ℝ → ℝ := fun x => deriv f x - (s + L * ((x - x₁) + (x - x₀))) with hg'
  -- second derivative of `g'`
  set g₂ : ℝ → ℝ := fun x => deriv (deriv f) x - 2 * L with hg₂
  -- `g` vanishes at the three nodes
  have hgx₀ : g x₀ = 0 := by simp [hg]
  have hgx₁ : g x₁ = 0 := by
    simp only [hg, hs]
    field_simp [n10]
    ring
  have hgx₂ : g x₂ = 0 := by
    simp only [hg, hs, hL]
    field_simp [n10, n01, n20, n02, n21, n12]
    ring
  -- ContDiffAt facts at interior points
  have hcda : ∀ x ∈ Ioo x₀ x₂, ContDiffAt ℝ 2 f x := by
    intro x hx
    exact hf.contDiffAt (Icc_mem_nhds hx.1 hx.2)
  -- `f` has derivative `deriv f x` at interior points
  have hfderiv : ∀ x ∈ Ioo x₀ x₂, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((hcda x hx).differentiableAt (by norm_num)).hasDerivAt
  -- `deriv f` has derivative `deriv (deriv f) x` at interior points
  have hf2deriv : ∀ x ∈ Ioo x₀ x₂, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x hx
    have : ContDiffAt ℝ 1 (deriv f) x := (hcda x hx).derivWithin (m := 1) (by norm_num)
    exact (this.differentiableAt (by norm_num)).hasDerivAt
  -- `HasDerivAt g (g' x) x` at interior points
  have hgderiv : ∀ x ∈ Ioo x₀ x₂, HasDerivAt g (g' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => x - x₀) 1 x := (hasDerivAt_id x).sub_const x₀
    have h2 : HasDerivAt (fun x : ℝ => x - x₁) 1 x := (hasDerivAt_id x).sub_const x₁
    have hs_part : HasDerivAt (fun x : ℝ => s * (x - x₀)) (s * 1) x := h1.const_mul s
    have hmul : HasDerivAt (fun x : ℝ => (x - x₀) * (x - x₁))
        (1 * (x - x₁) + (x - x₀) * 1) x := h1.mul h2
    have hL_part :
        HasDerivAt (fun x : ℝ => L * ((x - x₀) * (x - x₁)))
          (L * (1 * (x - x₁) + (x - x₀) * 1)) x := hmul.const_mul L
    -- sum of the two non-constant terms, as a single lambda
    have hadd : HasDerivAt
        (fun x : ℝ => s * (x - x₀) + L * ((x - x₀) * (x - x₁)))
        (s * 1 + L * (1 * (x - x₁) + (x - x₀) * 1)) x := hs_part.add hL_part
    have hpoly : HasDerivAt
        (fun x : ℝ => f x₀ + (s * (x - x₀) + L * ((x - x₀) * (x - x₁))))
        (s * 1 + L * (1 * (x - x₁) + (x - x₀) * 1)) x := hadd.const_add (f x₀)
    have hsub := (hfderiv x hx).sub hpoly
    -- reconcile to `g` and `g' x`
    have hfun : (f - fun x : ℝ => f x₀ + (s * (x - x₀) + L * ((x - x₀) * (x - x₁))))
        = g := by funext y; simp only [hg, Pi.sub_apply]; ring
    have hval : deriv f x - (s * 1 + L * (1 * (x - x₁) + (x - x₀) * 1)) = g' x := by
      simp only [hg']; ring
    rw [hfun, hval] at hsub
    exact hsub
  -- `HasDerivAt g' (g₂ x) x` at interior points
  have hg'deriv : ∀ x ∈ Ioo x₀ x₂, HasDerivAt g' (g₂ x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => x - x₁) 1 x := (hasDerivAt_id x).sub_const x₁
    have h2 : HasDerivAt (fun x : ℝ => x - x₀) 1 x := (hasDerivAt_id x).sub_const x₀
    have hpoly :
        HasDerivAt (fun x : ℝ => s + L * ((x - x₁) + (x - x₀))) (L * (1 + 1)) x := by
      have hsum : HasDerivAt (fun y : ℝ => (y - x₁) + (y - x₀)) (1 + 1) x := h1.add h2
      have h3 : HasDerivAt (fun y : ℝ => L * ((y - x₁) + (y - x₀))) (L * (1 + 1)) x :=
        hsum.const_mul L
      exact h3.const_add s
    have hsub := (hf2deriv x hx).sub hpoly
    have hval : deriv (deriv f) x - L * (1 + 1) = g₂ x := by simp only [hg₂]; ring
    rw [hval] at hsub
    simpa [hg'] using hsub
  -- continuity of `g` on the two closed sub-intervals via continuity on `Icc x₀ x₂`
  have hgcontIcc : ContinuousOn g (Icc x₀ x₂) := by
    have hfcont : ContinuousOn f (Icc x₀ x₂) := hf.continuousOn
    have hpolycont : ContinuousOn
        (fun x => f x₀ + s * (x - x₀) + L * (x - x₀) * (x - x₁)) (Icc x₀ x₂) := by
      fun_prop
    exact hfcont.sub hpolycont
  -- Rolle on `[x₀, x₁]`
  have hsub01 : Icc x₀ x₁ ⊆ Icc x₀ x₂ := Icc_subset_Icc le_rfl h12.le
  have hsub12 : Icc x₁ x₂ ⊆ Icc x₀ x₂ := Icc_subset_Icc h01.le le_rfl
  obtain ⟨y₁, hy₁mem, hy₁⟩ : ∃ y ∈ Ioo x₀ x₁, g' y = 0 := by
    apply exists_hasDerivAt_eq_zero h01 (hgcontIcc.mono hsub01) (by rw [hgx₀, hgx₁])
    intro x hx
    exact hgderiv x ⟨hx.1, hx.2.trans h12⟩
  obtain ⟨y₂, hy₂mem, hy₂⟩ : ∃ y ∈ Ioo x₁ x₂, g' y = 0 := by
    apply exists_hasDerivAt_eq_zero h12 (hgcontIcc.mono hsub12) (by rw [hgx₁, hgx₂])
    intro x hx
    exact hgderiv x ⟨h01.trans hx.1, hx.2⟩
  -- `[y₁, y₂] ⊆ Ioo x₀ x₂`
  have hy₁lt : y₁ < y₂ := lt_trans hy₁mem.2 hy₂mem.1
  have hy₁pos : x₀ < y₁ := hy₁mem.1
  have hy₂lt : y₂ < x₂ := hy₂mem.2
  have hIcc_y_sub : Icc y₁ y₂ ⊆ Ioo x₀ x₂ := by
    intro x hx
    exact ⟨lt_of_lt_of_le hy₁pos hx.1, lt_of_le_of_lt hx.2 hy₂lt⟩
  -- continuity of `g'` on `[y₁, y₂]` (interior, so `ContinuousAt` at each point)
  have hg'contIcc : ContinuousOn g' (Icc y₁ y₂) := by
    intro x hx
    exact ((hg'deriv x (hIcc_y_sub hx)).continuousAt).continuousWithinAt
  -- Rolle on `[y₁, y₂]` for `g'`
  obtain ⟨ξ, hξmem, hξ⟩ : ∃ ξ ∈ Ioo y₁ y₂, g₂ ξ = 0 := by
    apply exists_hasDerivAt_eq_zero hy₁lt hg'contIcc (by rw [hy₁, hy₂])
    intro x hx
    exact hg'deriv x (hIcc_y_sub (Ioo_subset_Icc_self hx))
  -- `ξ ∈ Ioo x₀ x₂`
  refine ⟨ξ, hIcc_y_sub (Ioo_subset_Icc_self hξmem), ?_⟩
  -- from `g₂ ξ = 0`: `deriv (deriv f) ξ = 2 * L`
  have hderiv2 : deriv (deriv f) ξ = 2 * L := by
    have := hξ; simp only [hg₂] at this; linarith
  -- relate to `iteratedDeriv 2 f`
  have hiter : iteratedDeriv 2 f ξ = deriv (deriv f) ξ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter, hderiv2]
  ring

/-- **§4.3 non-collinear-triple spacing bound.**
If `n₀ < n₁ < n₂` are integers, `f` is twice continuously differentiable with
`|f''| ≤ Λ` on `[n₀, n₂]`, each `f(nᵢ)` is within `δ` of an integer `ℓᵢ`, and the
three lattice points `(nᵢ, ℓᵢ)` are non-collinear (the integer
`u := ℓ₀(n₂-n₁) + ℓ₁(n₀-n₂) + ℓ₂(n₁-n₀)` is nonzero), then
`1 ≤ Λ·L³ + 2δ·L` where `L = n₂ - n₀`. -/
theorem noncollinear_span_lower {f : ℝ → ℝ} {Λ δ : ℝ} {n₀ n₁ n₂ ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (_hδ : 0 ≤ δ) (h01 : n₀ < n₁) (h12 : n₁ < n₂)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (n₀ : ℝ) (n₂ : ℝ)))
    (hf2 : ∀ x ∈ Set.Icc (n₀ : ℝ) (n₂ : ℝ), |iteratedDeriv 2 f x| ≤ Λ)
    (hd0 : |f (n₀ : ℝ) - (ℓ₀ : ℝ)| ≤ δ) (hd1 : |f (n₁ : ℝ) - (ℓ₁ : ℝ)| ≤ δ)
    (hd2 : |f (n₂ : ℝ) - (ℓ₂ : ℝ)| ≤ δ)
    (hncol : ℓ₀ * (n₂ - n₁) + ℓ₁ * (n₀ - n₂) + ℓ₂ * (n₁ - n₀) ≠ 0) :
    (1 : ℝ) ≤ Λ * ((n₂ : ℝ) - (n₀ : ℝ)) ^ 3 + 2 * δ * ((n₂ : ℝ) - (n₀ : ℝ)) := by
  -- Real casts of the strict orderings.
  have c01 : (n₀ : ℝ) < (n₁ : ℝ) := by exact_mod_cast h01
  have c12 : (n₁ : ℝ) < (n₂ : ℝ) := by exact_mod_cast h12
  have c02 : (n₀ : ℝ) < (n₂ : ℝ) := c01.trans c12
  -- Gaps as reals.
  set L : ℝ := (n₂ : ℝ) - (n₀ : ℝ) with hLdef
  set g01 : ℝ := (n₁ : ℝ) - (n₀ : ℝ) with hg01def
  set g12 : ℝ := (n₂ : ℝ) - (n₁ : ℝ) with hg12def
  have hg01pos : 0 < g01 := by simp only [hg01def]; linarith
  have hg12pos : 0 < g12 := by simp only [hg12def]; linarith
  have hLpos : 0 < L := by simp only [hLdef]; linarith
  have hg01leL : g01 ≤ L := by simp only [hg01def, hLdef]; linarith
  have hg12leL : g12 ≤ L := by simp only [hg12def, hLdef]; linarith
  have hsum : g01 + g12 = L := by simp only [hg01def, hg12def, hLdef]; ring
  -- Nonzero denominators (signed differences).
  have n01 : (n₀ : ℝ) - (n₁ : ℝ) ≠ 0 := by intro h; linarith
  have n02 : (n₀ : ℝ) - (n₂ : ℝ) ≠ 0 := by intro h; linarith
  have n10 : (n₁ : ℝ) - (n₀ : ℝ) ≠ 0 := by intro h; linarith
  have n12 : (n₁ : ℝ) - (n₂ : ℝ) ≠ 0 := by intro h; linarith
  have n20 : (n₂ : ℝ) - (n₀ : ℝ) ≠ 0 := by intro h; linarith
  have n21 : (n₂ : ℝ) - (n₁ : ℝ) ≠ 0 := by intro h; linarith
  -- The integer numerator `u` and its cast.
  set u : ℤ := ℓ₀ * (n₂ - n₁) + ℓ₁ * (n₀ - n₂) + ℓ₂ * (n₁ - n₀) with hudef
  have hu_ne : u ≠ 0 := hncol
  -- `1 ≤ |(u : ℝ)|`.
  have hu_abs : (1 : ℝ) ≤ |(u : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |u| := Int.one_le_abs hu_ne
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|u| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_one, Int.cast_abs] at h2
  -- Apply the second-divided-difference MVT.
  obtain ⟨ξ, hξmem, hξeq⟩ := secondDividedDiff_eq_half_secondDeriv c01 c12 hf
  -- ξ lies in the closed interval, so `|f''(ξ)| ≤ Λ`.
  have hξIcc : ξ ∈ Set.Icc (n₀ : ℝ) (n₂ : ℝ) :=
    ⟨hξmem.1.le, hξmem.2.le⟩
  have hΛbound : |iteratedDeriv 2 f ξ| ≤ Λ := hf2 ξ hξIcc
  -- `0 ≤ Λ` (forced by `|f''| ≤ Λ` at `n₀`).
  have hΛnonneg : 0 ≤ Λ :=
    le_trans (abs_nonneg _) (hf2 (n₀ : ℝ) ⟨le_rfl, c02.le⟩)
  -- Write `f(nᵢ) = ℓᵢ + εᵢ`.
  set ε₀ : ℝ := f (n₀ : ℝ) - (ℓ₀ : ℝ) with hε₀def
  set ε₁ : ℝ := f (n₁ : ℝ) - (ℓ₁ : ℝ) with hε₁def
  set ε₂ : ℝ := f (n₂ : ℝ) - (ℓ₂ : ℝ) with hε₂def
  have hfn0 : f (n₀ : ℝ) = (ℓ₀ : ℝ) + ε₀ := by simp only [hε₀def]; ring
  have hfn1 : f (n₁ : ℝ) = (ℓ₁ : ℝ) + ε₁ := by simp only [hε₁def]; ring
  have hfn2 : f (n₂ : ℝ) = (ℓ₂ : ℝ) + ε₂ := by simp only [hε₂def]; ring
  -- The error divided difference.
  set E : ℝ := ε₀ / (((n₀ : ℝ) - n₁) * ((n₀ : ℝ) - n₂))
      + ε₁ / (((n₁ : ℝ) - n₀) * ((n₁ : ℝ) - n₂))
      + ε₂ / (((n₂ : ℝ) - n₀) * ((n₂ : ℝ) - n₁)) with hEdef
  -- Algebraic identity: the integer divided difference equals `u / (g01·g12·L)`.
  have hint_id :
      (ℓ₀ : ℝ) / (((n₀ : ℝ) - n₁) * ((n₀ : ℝ) - n₂))
        + (ℓ₁ : ℝ) / (((n₁ : ℝ) - n₀) * ((n₁ : ℝ) - n₂))
        + (ℓ₂ : ℝ) / (((n₂ : ℝ) - n₀) * ((n₂ : ℝ) - n₁))
        = (u : ℝ) / (g01 * g12 * L) := by
    simp only [hudef, hg01def, hg12def, hLdef]
    push_cast
    field_simp
    ring
  -- Decompose the `f`-divided-difference into the integer part plus `E`.
  -- `hξeq` LHS, after substituting `f(nᵢ) = ℓᵢ + εᵢ`, splits as `u/(g01 g12 L) + E`.
  have hsplit :
      (u : ℝ) / (g01 * g12 * L) + E = iteratedDeriv 2 f ξ / 2 := by
    rw [← hint_id, ← hξeq, hfn0, hfn1, hfn2, hEdef]
    field_simp
    ring
  -- Multiply by `g01*g12*L > 0` to clear denominators.
  have hprodpos : 0 < g01 * g12 * L := by positivity
  have hprodne : g01 * g12 * L ≠ 0 := ne_of_gt hprodpos
  -- Scaled identity for `u`: from `hsplit`, `u/(P) = D/2 - E`, so `u = P*(D/2 - E)`.
  have hu_eq : (u : ℝ) = g01 * g12 * L * (iteratedDeriv 2 f ξ / 2 - E) := by
    have hdiv : (u : ℝ) / (g01 * g12 * L) = iteratedDeriv 2 f ξ / 2 - E :=
      eq_sub_of_add_eq hsplit
    have := congrArg (fun t => g01 * g12 * L * t) hdiv
    simp only [mul_div_cancel₀ _ hprodne] at this ⊢
    rw [this]
  -- Bound the scaled error term `g01*g12*L*E`.
  -- `g01*g12*L * E = ε₀·g12 - ε₁·L + ε₂·g01` (signed), with each |εᵢ| ≤ δ.
  have hscaledE : g01 * g12 * L * E = ε₀ * g12 + ε₁ * (-L) + ε₂ * g01 := by
    simp only [hEdef, hg01def, hg12def, hLdef]
    field_simp
    ring
  have habsE : |g01 * g12 * L * E| ≤ δ * (2 * L) := by
    rw [hscaledE]
    have hb0 : |ε₀| ≤ δ := hd0
    have hb1 : |ε₁| ≤ δ := hd1
    have hb2 : |ε₂| ≤ δ := hd2
    calc |ε₀ * g12 + ε₁ * (-L) + ε₂ * g01|
        ≤ |ε₀ * g12| + |ε₁ * (-L)| + |ε₂ * g01| := by
          exact (abs_add_three _ _ _)
      _ = |ε₀| * g12 + |ε₁| * L + |ε₂| * g01 := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hg12pos, abs_neg,
            abs_of_pos hLpos, abs_of_pos hg01pos]
      _ ≤ δ * g12 + δ * L + δ * g01 := by
          gcongr
      _ = δ * (2 * L) := by rw [← hsum]; ring
  -- Bound `g01*g12*L ≤ L³`.
  have hprodleL3 : g01 * g12 * L ≤ L ^ 3 := by
    have : g01 * g12 * L ≤ L * L * L := by
      apply mul_le_mul_of_nonneg_right _ hLpos.le
      exact mul_le_mul hg01leL hg12leL hg12pos.le hLpos.le
    calc g01 * g12 * L ≤ L * L * L := this
      _ = L ^ 3 := by ring
  -- Bound `|u| ≤ (g01*g12*L)*|f''/2| + |(g01*g12*L)*E|`.
  have hu_split : |(u : ℝ)|
      ≤ g01 * g12 * L * |iteratedDeriv 2 f ξ / 2| + |g01 * g12 * L * E| := by
    rw [hu_eq, mul_sub]
    calc |g01 * g12 * L * (iteratedDeriv 2 f ξ / 2) - g01 * g12 * L * E|
        ≤ |g01 * g12 * L * (iteratedDeriv 2 f ξ / 2)| + |g01 * g12 * L * E| :=
          abs_sub _ _
      _ = g01 * g12 * L * |iteratedDeriv 2 f ξ / 2| + |g01 * g12 * L * E| := by
          rw [abs_mul, abs_of_pos hprodpos]
  -- `|f''(ξ)/2| ≤ Λ/2`.
  have hhalf : |iteratedDeriv 2 f ξ / 2| ≤ Λ / 2 := by
    rw [abs_div]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    linarith [hΛbound]
  -- Assemble: `|u| ≤ (g01 g12 L)·Λ/2 + δ·2L ≤ L³·Λ/2 + 2δL ≤ Λ L³ + 2δL`.
  have hstep1 : g01 * g12 * L * |iteratedDeriv 2 f ξ / 2| ≤ L ^ 3 * (Λ / 2) := by
    apply mul_le_mul hprodleL3 hhalf (abs_nonneg _)
    positivity
  have hfinal : |(u : ℝ)| ≤ L ^ 3 * (Λ / 2) + δ * (2 * L) :=
    le_trans hu_split (add_le_add hstep1 habsE)
  have hbound : |(u : ℝ)| ≤ Λ * L ^ 3 + 2 * δ * L := by
    have hL3pos : (0 : ℝ) ≤ L ^ 3 := by positivity
    have hΛL3 : (0 : ℝ) ≤ Λ * L ^ 3 := mul_nonneg hΛnonneg hL3pos
    have heq1 : Λ * L ^ 3 - L ^ 3 * (Λ / 2) = (Λ * L ^ 3) / 2 := by ring
    have hhalfL3 : L ^ 3 * (Λ / 2) ≤ Λ * L ^ 3 := by linarith only [heq1, hΛL3]
    have hδL : δ * (2 * L) = 2 * δ * L := by ring
    linarith only [hfinal, hhalfL3, hδL]
  calc (1 : ℝ) ≤ |(u : ℝ)| := hu_abs
    _ ≤ Λ * L ^ 3 + 2 * δ * L := hbound
    _ = Λ * ((n₂ : ℝ) - (n₀ : ℝ)) ^ 3 + 2 * δ * ((n₂ : ℝ) - (n₀ : ℝ)) := by
        rw [hLdef]

/-- **§4.3 major-arc length bound.**
If `g` is twice continuously differentiable on `[a, a+L]` with `|g''| ≥ Λlo` and
`|g| ≤ δ` throughout, then `Λlo · L² ≤ 16δ`.  This is the third spacing fact
`L ≪ √(δ/λ)` from the writeup: applying the second divided-difference MVT at the
equally-spaced nodes `a, a+L/2, a+L` gives
`g(a) - 2g(a+L/2) + g(a+L) = (L²/4)·g''(ξ)`, whose LHS is `O(δ)`. -/
theorem majorArc_length_bound {g : ℝ → ℝ} {a L δ Λlo : ℝ} (hL : 0 < L) (_hδ : 0 ≤ δ)
    (hg : ContDiffOn ℝ 2 g (Set.Icc a (a + L)))
    (hg2 : ∀ x ∈ Set.Icc a (a + L), Λlo ≤ |iteratedDeriv 2 g x|)
    (hgδ : ∀ x ∈ Set.Icc a (a + L), |g x| ≤ δ) :
    Λlo * L ^ 2 ≤ 16 * δ := by
  -- Equally-spaced nodes `a < a + L/2 < a + L`.
  have h01 : a < a + L / 2 := by linarith
  have h12 : a + L / 2 < a + L := by linarith
  -- The `ContDiffOn` domain `Icc a (a+L)` matches `hg` (since `x₂ = a + L`).
  obtain ⟨ξ, hξmem, hξeq⟩ := secondDividedDiff_eq_half_secondDeriv h01 h12 hg
  -- Central identity: clear the three explicit denominators.
  have hcentral : g a - 2 * g (a + L / 2) + g (a + L)
      = L ^ 2 / 4 * iteratedDeriv 2 g ξ := by
    have hLne : L ≠ 0 := hL.ne'
    -- Rewrite the divided-difference identity into the central second difference.
    have key : g a / ((a - (a + L / 2)) * (a - (a + L)))
        + g (a + L / 2) / (((a + L / 2) - a) * ((a + L / 2) - (a + L)))
        + g (a + L) / (((a + L) - a) * ((a + L) - (a + L / 2)))
        = iteratedDeriv 2 g ξ / 2 := hξeq
    rw [show (a - (a + L / 2)) * (a - (a + L)) = L ^ 2 / 2 by ring,
        show ((a + L / 2) - a) * ((a + L / 2) - (a + L)) = -(L ^ 2 / 4) by ring,
        show ((a + L) - a) * ((a + L) - (a + L / 2)) = L ^ 2 / 2 by ring] at key
    have hL2ne : L ^ 2 ≠ 0 := pow_ne_zero 2 hLne
    field_simp at key
    rw [show (2 * a + L) / 2 = a + L / 2 by ring] at key
    nlinarith [key]
  -- Memberships needed to invoke `hg2`/`hgδ`.
  have hξIcc : ξ ∈ Set.Icc a (a + L) := ⟨hξmem.1.le, hξmem.2.le⟩
  have hmemA : a ∈ Set.Icc a (a + L) := ⟨le_rfl, by linarith⟩
  have hmemM : a + L / 2 ∈ Set.Icc a (a + L) := ⟨by linarith, by linarith⟩
  have hmemB : a + L ∈ Set.Icc a (a + L) := ⟨by linarith, le_rfl⟩
  -- Triangle inequality: LHS is `≤ 4δ`.
  have htri : |g a - 2 * g (a + L / 2) + g (a + L)| ≤ 4 * δ := by
    have e0 := hgδ a hmemA
    have eM := hgδ (a + L / 2) hmemM
    have eB := hgδ (a + L) hmemB
    calc |g a - 2 * g (a + L / 2) + g (a + L)|
        = |g a + (-(2 * g (a + L / 2))) + g (a + L)| := by ring_nf
      _ ≤ |g a| + |(-(2 * g (a + L / 2)))| + |g (a + L)| := abs_add_three _ _ _
      _ = |g a| + 2 * |g (a + L / 2)| + |g (a + L)| := by
          rw [abs_neg, abs_mul]; norm_num
      _ ≤ δ + 2 * δ + δ := by gcongr
      _ = 4 * δ := by ring
  -- Lower bound on the same LHS via `hcentral` and `|g''(ξ)| ≥ Λlo`.
  have hL2 : (0 : ℝ) ≤ L ^ 2 / 4 := by positivity
  have hlow : L ^ 2 / 4 * Λlo ≤ |g a - 2 * g (a + L / 2) + g (a + L)| := by
    rw [hcentral, abs_mul, abs_of_nonneg hL2]
    exact mul_le_mul_of_nonneg_left (hg2 ξ hξIcc) hL2
  -- Combine `L²/4·Λlo ≤ 4δ`  ⟹  `Λlo·L² ≤ 16δ`.
  nlinarith [hlow.trans htri]

/-- **Lattice points on a line of denominator `q`: count bound.**
If every element `n` of a finite set `S ⊆ ℤ` lies in the (well-formed) interval
`[lo, hi]` and satisfies `q ∣ (n - r)`, then `S` has at most `(hi - lo)/q + 1`
elements.  The `x`-coordinates of lattice points on a line `y = (a/q) x + b`
(with `gcd(a,q)=1`) lie in a single residue class mod `q`, so they are
`q`-separated.  The hypothesis `lo ≤ hi` is the interval well-formedness assumption
(needed only for the empty-`S` corner, where the count is `0`). -/
theorem residueClass_card_le {q : ℤ} (hq : 0 < q) (r : ℤ) (lo hi : ℝ)
    (hlohi : lo ≤ hi) (S : Finset ℤ)
    (hmem : ∀ n ∈ S, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ (q : ℤ) ∣ (n - r)) :
    (S.card : ℝ) ≤ (hi - lo) / (q : ℝ) + 1 := by
  -- The map `t n = (n - r) / q` is injective on `S` and lands in an integer `Icc`.
  classical
  -- Split off the empty set: then the count is `0` and the bound is `0 ≤ (hi-lo)/q + 1`,
  -- which holds since `lo ≤ hi` and `q > 0`.
  rcases S.eq_empty_or_nonempty with hSempty | hSne
  · subst hSempty
    simp only [Finset.card_empty, Nat.cast_zero]
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have : (0 : ℝ) ≤ (hi - lo) / (q : ℝ) := div_nonneg (by linarith) hqR.le
    linarith
  set t : ℤ → ℤ := fun n => (n - r) / q with ht
  -- For `n ∈ S`, `n = r + q * t n`.
  have hrecon : ∀ n ∈ S, n = r + q * t n := by
    intro n hn
    have hd : (q : ℤ) ∣ (n - r) := (hmem n hn).2.2
    have : q * t n = n - r := by
      rw [ht]; exact Int.mul_ediv_cancel' hd
    linarith [this]
  -- Injectivity on `S`.
  have hinj : Set.InjOn t S := by
    intro a ha b hb hab
    have e1 := hrecon a ha
    have e2 := hrecon b hb
    rw [e1, e2, hab]
  -- The image bounds: `⌈(lo-r)/q⌉ ≤ t n ≤ ⌊(hi-r)/q⌋`.
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set a : ℤ := ⌈(lo - r) / (q : ℝ)⌉ with hadef
  set b : ℤ := ⌊(hi - r) / (q : ℝ)⌋ with hbdef
  have hmapsto : Set.MapsTo t S (Finset.Icc a b) := by
    intro n hn
    obtain ⟨hlo, hhi, _⟩ := hmem n hn
    have hnval : (n : ℝ) = (r : ℝ) + (q : ℝ) * (t n : ℝ) := by
      have := hrecon n hn
      have : ((n : ℤ) : ℝ) = ((r + q * t n : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith [this]
    -- lower bound: a = ⌈(lo-r)/q⌉ ≤ t n
    have hlower : a ≤ t n := by
      rw [hadef, Int.ceil_le]
      have : (lo - r) / (q : ℝ) ≤ (t n : ℝ) := by
        rw [div_le_iff₀ hqR]
        nlinarith [hnval, hlo]
      exact_mod_cast this
    -- upper bound: t n ≤ ⌊(hi-r)/q⌋ = b
    have hupper : t n ≤ b := by
      rw [hbdef, Int.le_floor]
      have : (t n : ℝ) ≤ (hi - r) / (q : ℝ) := by
        rw [le_div_iff₀ hqR]
        nlinarith [hnval, hhi]
      exact_mod_cast this
    have : t n ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨hlower, hupper⟩
    exact this
  -- Cardinality bound from injection into the Icc.
  have hcard : S.card ≤ (Finset.Icc a b).card :=
    Finset.card_le_card_of_injOn t hmapsto hinj
  -- Now bound `(Finset.Icc a b).card` as a real.
  -- Real bounds: `a ≥ (lo-r)/q` and `b ≤ (hi-r)/q`.
  have hb_real : (b : ℝ) ≤ (hi - r) / (q : ℝ) := by
    rw [hbdef]; exact Int.floor_le _
  have ha_real : (lo - r) / (q : ℝ) ≤ (a : ℝ) := by
    rw [hadef]; exact Int.le_ceil _
  -- Case on whether the Icc is empty.
  by_cases hab : a ≤ b
  · have hcard_eq : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
      Int.card_Icc_of_le (a := a) (b := b) (by omega)
    have hcard_eqR : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      have : (((Finset.Icc a b).card : ℤ) : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by
        exact_mod_cast hcard_eq
      push_cast at this; linarith [this]
    have hScardR : (S.card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by
      exact_mod_cast hcard
    rw [hcard_eqR] at hScardR
    -- `(b - a) ≤ (hi - lo)/q`, so `b + 1 - a ≤ (hi-lo)/q + 1`.
    have hba : (b : ℝ) - (a : ℝ) ≤ (hi - lo) / (q : ℝ) := by
      have : (b : ℝ) - (a : ℝ) ≤ (hi - r) / (q : ℝ) - (lo - r) / (q : ℝ) := by
        linarith [hb_real, ha_real]
      rw [div_sub_div_same] at this
      have heq : (hi - r) - (lo - r) = hi - lo := by ring
      rwa [heq] at this
    linarith [hScardR, hba]
  · -- Icc empty ⟹ `S` maps into `∅`, contradicting `S` nonempty.
    exfalso
    have hba : b < a := lt_of_not_ge hab
    have hIccempty : Finset.Icc a b = ∅ := by
      rw [Finset.Icc_eq_empty]; omega
    obtain ⟨n, hn⟩ := hSne
    have hmem' : t n ∈ Finset.Icc a b := hmapsto hn
    rw [hIccempty] at hmem'
    exact absurd hmem' (by simp)

/-- **Lattice points on a line of denominator `q`: denominator bound.**
If at least two elements of a finite set `S ⊆ ℤ` lie in `[lo, hi]` and satisfy
`q ∣ (n - r)`, then `q ≤ hi - lo`: two points in the same residue class mod `q`
are at least `q` apart, so the span of `S` is at least `q`. -/
theorem residueClass_denom_le {q : ℤ} (_hq : 0 < q) (r : ℤ) (lo hi : ℝ) (S : Finset ℤ)
    (h2 : 2 ≤ S.card)
    (hmem : ∀ n ∈ S, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ (q : ℤ) ∣ (n - r)) :
    (q : ℝ) ≤ hi - lo := by
  -- Extract two distinct elements.
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨hloa, hhia, hda⟩ := hmem a ha
  obtain ⟨hlob, hhib, hdb⟩ := hmem b hb
  -- `q ∣ (a - b)` since both `≡ r mod q`.
  have hdab : (q : ℤ) ∣ (a - b) := by
    have : (a - b) = (a - r) - (b - r) := by ring
    rw [this]; exact dvd_sub hda hdb
  -- WLOG order the two and take the positive difference.
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b, so b - a > 0, and q ∣ (b - a).
    have hpos : 0 < b - a := by omega
    have hdba : (q : ℤ) ∣ (b - a) := by
      have : b - a = -(a - b) := by ring
      rw [this]; exact Dvd.dvd.neg_right hdab
    have hqle : q ≤ b - a := Int.le_of_dvd hpos hdba
    have : (q : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
      have : ((q : ℤ) : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hqle
      push_cast at this; linarith [this]
    linarith [this, hloa, hhib]
  · -- b < a, so a - b > 0, and q ∣ (a - b).
    have hpos : 0 < a - b := by omega
    have hqle : q ≤ a - b := Int.le_of_dvd hpos hdab
    have : (q : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
      have : ((q : ℤ) : ℝ) ≤ ((a - b : ℤ) : ℝ) := by exact_mod_cast hqle
      push_cast at this; linarith [this]
    linarith [this, hlob, hhia]

end Squarefree
