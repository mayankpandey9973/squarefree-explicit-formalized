import Squarefree.FiniteDiff
import Mathlib

/-!
# §7 N9′ constructor machinery (graded chains, MVT, power monomials)

Generic helpers for `Sec7MonExpBuild.lean` (A3 gate ruling: the `Sec7MonExp` bundle is
BUILT at the §3 site, md 326–344 / 1589–1633).  Three groups:
* graded derivative chains: `iteratedDeriv` of a function from a `HasDerivAt` chain on an
  open set (`sec7_iteratedDeriv_eq_of_chain`), no `ContDiff` bookkeeping;
* mean-value tools on `Icc` (inequality, exact, and an order-2 Taylor remainder);
* the explicit power monomials `c·(t/R)^α` with their graded derivative families
  (`sec7_powMonD`), falling-factorial coefficients `sec7_aprod`, and window sup-bounds.
-/

open Real Set Squarefree.FiniteDiff

namespace Squarefree

/-- Falling-factorial coefficient `∏_{i<m} (α − i)` of the `m`-th derivative of `y^α`. -/
def sec7_aprod (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => sec7_aprod α m * (α - m)

/-- **Graded chain ⟹ `iteratedDeriv`.**  If `F (m+1)` is the derivative of `F m` on an
open set `s` (for `m < n`), then `iteratedDeriv m (F 0) = F m` on `s` for `m ≤ n`. -/
theorem sec7_iteratedDeriv_eq_of_chain {F : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {n : ℕ}
    (hd : ∀ m < n, ∀ r ∈ s, HasDerivAt (F m) (F (m + 1) r) r) :
    ∀ m ≤ n, ∀ r ∈ s, iteratedDeriv m (F 0) r = F m r := by
  intro m
  induction m with
  | zero => intro _ r _; simp
  | succ m ih =>
    intro hm r hr
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (F 0) =ᶠ[nhds r] F m :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hr)
        (fun x hx => ih (le_of_lt (Nat.lt_of_succ_le hm)) x hx)
    rw [hev.deriv_eq]
    exact (hd m (Nat.lt_of_succ_le hm) r hr).deriv

/-- **MVT inequality on `Icc`.**  `|g b − g a| ≤ B·(b − a)` from a derivative bound. -/
theorem sec7_abs_sub_le_of_deriv {g g' : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hB : ∀ x ∈ Icc a b, |g' x| ≤ B) :
    |g b - g a| ≤ B * (b - a) := by
  have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := B)
    (fun x hx => (hg x hx).hasDerivWithinAt) (fun x hx => by simpa using hB x hx)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using this

/-- **Exact MVT for one forward difference**: `g(s+h) − g(s) = h·g'(ζ)`, `ζ ∈ Ioo s (s+h)`. -/
theorem sec7_diff_eq_mul_deriv {g g' : ℝ → ℝ} {s h : ℝ} (hh : 0 < h)
    (hg : ∀ x ∈ Icc s (s + h), HasDerivAt g (g' x) x) :
    ∃ ζ ∈ Ioo s (s + h), g (s + h) - g s = h * g' ζ := by
  have hlt : s < s + h := by linarith
  have hcont : ContinuousOn g (Icc s (s + h)) :=
    fun x hx => ((hg x hx).continuousAt).continuousWithinAt
  obtain ⟨ζ, hζ, hsl⟩ := exists_hasDerivAt_eq_slope g g' hlt hcont
    (fun x hx => hg x (Ioo_subset_Icc_self hx))
  refine ⟨ζ, hζ, ?_⟩
  rw [hsl, show s + h - s = h from by ring]
  field_simp

/-- **Order-2 Taylor remainder bound on `Icc`**: `|g(s+h) − g(s) − h·g'(s)| ≤ B·h²` from a
bound on the second derivative (no `1/2`, by two nested MVT inequalities). -/
theorem sec7_taylor2_le {g g' g'' : ℝ → ℝ} {s h B : ℝ} (hh : 0 ≤ h) (hB0 : 0 ≤ B)
    (hg : ∀ x ∈ Icc s (s + h), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc s (s + h), HasDerivAt g' (g'' x) x)
    (hB : ∀ x ∈ Icc s (s + h), |g'' x| ≤ B) :
    |g (s + h) - g s - h * g' s| ≤ B * h ^ 2 := by
  set ψ : ℝ → ℝ := fun u => g (s + u) - g s - u * g' s with hψ
  have hψd : ∀ u ∈ Icc (0:ℝ) h, HasDerivAt ψ (g' (s + u) - g' s) u := by
    intro u hu
    have hmem : s + u ∈ Icc s (s + h) := by
      constructor <;> [linarith [hu.1]; linarith [hu.2]]
    have h1 : HasDerivAt (fun u => g (s + u)) (g' (s + u)) u := by
      simpa using (hg (s + u) hmem).comp u ((hasDerivAt_id u).const_add s)
    simpa [hψ] using (h1.sub_const (g s)).sub
      ((hasDerivAt_id u).mul_const (g' s))
  have hψ'B : ∀ u ∈ Icc (0:ℝ) h, |g' (s + u) - g' s| ≤ B * h := by
    intro u hu
    have hmvt := sec7_abs_sub_le_of_deriv (g := g') (g' := g'') (a := s) (b := s + u)
      (by linarith [hu.1])
      (fun x hx => hg' x ⟨hx.1, by linarith [hx.2, hu.2]⟩)
      (fun x hx => hB x ⟨hx.1, by linarith [hx.2, hu.2]⟩)
    calc |g' (s + u) - g' s| ≤ B * (s + u - s) := hmvt
      _ ≤ B * h := by have := hu.1; have := hu.2; nlinarith
  have hfin := sec7_abs_sub_le_of_deriv (g := ψ) (g' := fun u => g' (s + u) - g' s)
    (a := 0) (b := h) hh hψd hψ'B
  calc |g (s + h) - g s - h * g' s| = |ψ h - ψ 0| := by simp [hψ]
    _ ≤ B * h * (h - 0) := hfin
    _ = B * h ^ 2 := by ring

/-! ## Power monomials `c·(t/R)^α` and their graded derivative families -/

/-- The power monomial `t ↦ c·(t/R)^α` (real power). -/
noncomputable def sec7_powMon (R c α : ℝ) : ℝ → ℝ := fun t => c * (t / R) ^ α

/-- The graded derivative family of `sec7_powMon R c α`:
`m`-th member `c·(∏_{i<m}(α−i))/Rᵐ · (t/R)^{α−m}`. -/
noncomputable def sec7_powMonD (R c α : ℝ) (m : ℕ) : ℝ → ℝ :=
  sec7_powMon R (c * sec7_aprod α m / R ^ m) (α - m)

@[simp] theorem sec7_powMonD_zero (R c α : ℝ) : sec7_powMonD R c α 0 = sec7_powMon R c α := by
  unfold sec7_powMonD
  simp [sec7_aprod]

/-- The graded family is a genuine derivative chain on `t > 0` (for `R > 0`). -/
theorem sec7_powMonD_hasDerivAt {R : ℝ} (hR : 0 < R) (c α : ℝ) (m : ℕ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (sec7_powMonD R c α m) (sec7_powMonD R c α (m + 1) t) t := by
  have htR : 0 < t / R := div_pos ht hR
  have hbase : HasDerivAt (fun s : ℝ => s / R) (1 / R) t := by
    simpa using (hasDerivAt_id t).div_const R
  have hpow : HasDerivAt (fun y : ℝ => y ^ (α - m)) ((α - m) * (t / R) ^ (α - m - 1))
      (t / R) := Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htR))
  have hcomp := (hpow.comp t hbase).const_mul (c * sec7_aprod α m / R ^ m)
  have harg : α - m - 1 = α - ((m : ℕ) + 1 : ℕ) := by push_cast; ring
  have haprod : sec7_aprod α (m + 1) = sec7_aprod α m * (α - m) := rfl
  have hval : c * sec7_aprod α m / R ^ m * ((α - ↑m) * (t / R) ^ (α - ↑m - 1) * (1 / R))
      = c * sec7_aprod α (m + 1) / R ^ (m + 1) * (t / R) ^ (α - ((m : ℕ) + 1 : ℕ)) := by
    rw [harg, haprod]
    have hRne : R ≠ 0 := ne_of_gt hR
    field_simp
    ring
  unfold sec7_powMonD sec7_powMon
  rw [← hval]
  simpa [Function.comp] using hcomp

/-- Window sup-bound for nonpositive exponents: on `1/K ≤ t/R` (with `t/R > 0`),
`|sec7_powMon R c α t| ≤ |c| · K^{−α}` for `α ≤ 0`, `1 ≤ K`. -/
theorem sec7_powMon_abs_le {R c α K t : ℝ} (hK : 1 ≤ K) (hα : α ≤ 0)
    (ht0 : 0 < t / R) (ht : 1 / K ≤ t / R) :
    |sec7_powMon R c α t| ≤ |c| * K ^ (-α) := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hinv : 0 < 1 / K := by positivity
  have h1 : (t / R) ^ α ≤ (1 / K) ^ α := Real.rpow_le_rpow_of_nonpos hinv ht hα
  have h2 : (1 / K) ^ α = K ^ (-α) := by
    rw [one_div, ← Real.rpow_neg_one K, ← Real.rpow_mul hK0.le]
    ring_nf
  have h3 : 0 < (t / R) ^ α := Real.rpow_pos_of_pos ht0 α
  have habs : |sec7_powMon R c α t| = |c| * (t / R) ^ α := by
    unfold sec7_powMon
    rw [abs_mul, abs_of_pos h3]
  rw [habs]
  have : |c| * (t / R) ^ α ≤ |c| * (1 / K) ^ α :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
  rwa [h2] at this

/-! ## First-difference helpers -/

/-- `diff1 h g` differentiates to `diff1 h g'` (pointwise). -/
theorem sec7_diff1_hasDerivAt {g g' : ℝ → ℝ} {h x : ℝ}
    (h1 : HasDerivAt g (g' (x + h)) (x + h)) (h2 : HasDerivAt g (g' x) x) :
    HasDerivAt (diff1 h g) (diff1 h g' x) x := by
  have := (h1.comp x ((hasDerivAt_id x).add_const h)).sub h2
  simpa [diff1, Function.comp] using this

/-- Bound for one forward difference from a derivative bound on `Icc s (s+h)`. -/
theorem sec7_diff1_abs_le {g g' : ℝ → ℝ} {s h B : ℝ} (hh : 0 ≤ h)
    (hg : ∀ x ∈ Icc s (s + h), HasDerivAt g (g' x) x)
    (hB : ∀ x ∈ Icc s (s + h), |g' x| ≤ B) :
    |diff1 h g s| ≤ B * h := by
  have := sec7_abs_sub_le_of_deriv (g := g) (g' := g') (a := s) (b := s + h) (by linarith)
    hg hB
  simpa [diff1] using this

end Squarefree
