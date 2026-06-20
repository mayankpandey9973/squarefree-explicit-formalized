import Squarefree.Counting.Preimage
import Squarefree.Geometry.NearCurveAux
import Squarefree.Geometry.NearCurveResidual
import Mathlib

/-!
# §4 integer points near a curve (Prop 4.3)

Faithful statement of the integer-points-near-a-curve proposition from
`../explicit_writeup.md` (lines 463–469), reduced (a real proof of the §4.3
substitution `f = T·F(·/N)`, `λ = T/N²`) to the `λ`-normalized core
`prop43_local` (writeup line 482), which carries the Bombieri–Pila major-arc
argument and remains a tracked stub. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree.Counting

/-- The pinned constant in `nearCurve_count` / `nearCurve_count_explicit`. -/
noncomputable def C_nearCurveCount : ℝ := C_prop43local

/-- **Prop 4.3** (writeup 463–469) with the pinned constant: integer points near a curve,
`|F''| ≍ 1` normalized to `1 ≤ |F''| ≤ 256` on `[1/2, 5/2]` (curvature ratio up to 256,
faithful to `|F''| ≍ 1`); count over `(N,2N]`. -/
theorem nearCurve_count_explicit :
    ∀ (N T δ : ℝ) (F : ℝ → ℝ),
      1 < N → 1 < T → 0 < δ → δ < 1 → ContDiff ℝ 2 F →
      (∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), 1 ≤ |iteratedDeriv 2 F x|) →
      (∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), |iteratedDeriv 2 F x| ≤ 256) →
      (((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter
          (fun n => distInt (T * F ((n : ℝ) / N)) ≤ δ)).card : ℝ)
        ≤ C_nearCurveCount * ((N * T) ^ (1/3 : ℝ) + N * δ
               + N * Real.sqrt (δ / T) * Real.log (2 + N * Real.sqrt (δ / T)) + 1) := by
  unfold C_nearCurveCount
  have hloc := prop43_local_explicit
  intro N T δ F hN hT hδ hδ1 hF hF1 hF2
  -- Basic positivity.
  have hN0 : (0 : ℝ) < N := lt_trans one_pos hN
  have hT0 : (0 : ℝ) < T := lt_trans one_pos hT
  have hNne : N ≠ 0 := hN0.ne'
  -- The substituted curve and curvature.
  set f : ℝ → ℝ := fun x => T * F (x / N) with hfdef
  set lam : ℝ := T / N ^ 2 with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  -- `f` is `ContDiff ℝ 2`.
  have hFcomp : ContDiff ℝ 2 (fun x : ℝ => F (x / N)) := by
    have hdiv : ContDiff ℝ 2 (fun x : ℝ => x / N) := by
      simpa [div_eq_mul_inv] using (contDiff_id.mul contDiff_const : ContDiff ℝ 2 _)
    exact hF.comp hdiv
  have hf : ContDiff ℝ 2 f := by
    rw [hfdef]
    simpa only [smul_eq_mul] using hFcomp.const_smul T
  -- Second derivative of `f`: `f'' x = lam * F'' (x/N)`.
  have hf2eq : ∀ x : ℝ, iteratedDeriv 2 f x = lam * iteratedDeriv 2 F (x / N) := by
    intro x
    -- Write the inner reparametrization as `c * x` with `c = 1/N`.
    have hcompmul : (fun x : ℝ => F (x / N)) = (fun x : ℝ => F ((1 / N) * x)) := by
      funext y; rw [one_div, inv_mul_eq_div]
    have hcomp2 : iteratedDeriv 2 (fun x : ℝ => F ((1 / N) * x))
        = fun x => (1 / N) ^ 2 * iteratedDeriv 2 F ((1 / N) * x) :=
      iteratedDeriv_comp_const_mul hF (1 / N)
    -- `f = T • (F ∘ (·/N))`, pull out the constant.
    have hfmul : f = fun x => T * (fun x : ℝ => F (x / N)) x := by
      funext y; rfl
    rw [hfmul, iteratedDeriv_const_mul_field, hcompmul, hcomp2]
    simp only
    have hxN : (1 / N) * x = x / N := by rw [one_div, inv_mul_eq_div]
    rw [hxN, hlamdef]
    rw [show (1 / N : ℝ) ^ 2 = 1 / N ^ 2 by rw [div_pow, one_pow]]
    ring
  -- Transfer the curvature bounds from `[1/2,5/2]` to `[N/2,5N/2]`.
  have hmem_div : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), x / N ∈ Set.Icc (1/2 : ℝ) (5/2) := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    constructor
    · rw [le_div_iff₀ hN0]; linarith
    · rw [div_le_iff₀ hN0]; linarith
  have hloc_lower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x| := by
    intro x hx
    rw [hf2eq, abs_mul, abs_of_pos hlam0]
    have h1 := hF1 (x / N) (hmem_div x hx)
    calc lam = lam * 1 := by ring
      _ ≤ lam * |iteratedDeriv 2 F (x / N)| :=
          mul_le_mul_of_nonneg_left h1 hlam0.le
  have hloc_upper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam := by
    intro x hx
    rw [hf2eq, abs_mul, abs_of_pos hlam0]
    have h2 := hF2 (x / N) (hmem_div x hx)
    calc lam * |iteratedDeriv 2 F (x / N)| ≤ lam * 256 :=
          mul_le_mul_of_nonneg_left h2 hlam0.le
      _ = 256 * lam := by ring
  -- Curvature floor `N²·λ = T ≥ 1` (from `λ = T/N²`, `T > 1`).
  have hfloor : 1 ≤ N ^ 2 * lam := by
    rw [hlamdef]
    have hN2ne : (N : ℝ) ^ 2 ≠ 0 := by positivity
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hN2ne, mul_one]
    linarith
  -- Apply the core lemma.
  have hcore := hloc N lam δ f hN0 hlam0 hδ hδ1 hf hfloor hloc_lower hloc_upper
  -- The integer interval `Ioc ⊆ Icc`, hence after the `ℝ`-coercion the filtered cards compare.
  have hsubset :
      ((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).image (Int.cast : ℤ → ℝ)).filter
          (fun (n : ℝ) => distInt (f n) ≤ δ)
        ⊆ ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).image (Int.cast : ℤ → ℝ)).filter
          (fun (n : ℝ) => distInt (f n) ≤ δ) := by
    apply Finset.filter_subset_filter
    apply Finset.image_subset_image
    exact Finset.Ioc_subset_Icc_self
  have hcard_le :
      ((((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).image (Int.cast : ℤ → ℝ)).filter
          (fun (n : ℝ) => distInt (f n) ≤ δ)).card : ℝ)
        ≤ ((((Finset.Icc ⌊N⌋ ⌊2 * N⌋).image (Int.cast : ℤ → ℝ)).filter
          (fun (n : ℝ) => distInt (f n) ≤ δ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  -- RHS translation: `N * lam^(1/3) = (N*T)^(1/3)` and `sqrt (δ/lam) = N * sqrt (δ/T)`.
  have h13 : (1/3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  have hrpow : N * lam ^ (1/3 : ℝ) = (N * T) ^ (1/3 : ℝ) := by
    -- `N = (N^3)^(1/3)`, then merge the two cube roots; `N^3 * lam = N * T`.
    have hNcube : ((N ^ 3) ^ (1/3 : ℝ) : ℝ) = N := by
      rw [h13]; exact Real.pow_rpow_inv_natCast hN0.le (by norm_num)
    have hbase : N ^ 3 * lam = N * T := by
      rw [hlamdef]
      rw [mul_div_assoc']
      rw [show N ^ 3 * T = N * T * N ^ 2 by ring]
      rw [mul_div_assoc, div_self (by positivity : (N : ℝ) ^ 2 ≠ 0), mul_one]
    calc N * lam ^ (1/3 : ℝ)
        = (N ^ 3) ^ (1/3 : ℝ) * lam ^ (1/3 : ℝ) := by rw [hNcube]
      _ = (N ^ 3 * lam) ^ (1/3 : ℝ) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
      _ = (N * T) ^ (1/3 : ℝ) := by rw [hbase]
  have hsqrt : Real.sqrt (δ / lam) = N * Real.sqrt (δ / T) := by
    rw [hlamdef]
    -- δ / (T/N²) = N² * (δ/T)
    have hrw : δ / (T / N ^ 2) = N ^ 2 * (δ / T) := by
      rw [div_div_eq_mul_div]; ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq hN0.le]
  -- Assemble: rewrite the core bound's RHS to match the target.
  rw [hrpow, hsqrt] at hcore
  -- Normalize the `do`-block Finsets (`bind`/`pure`) into `.image Int.cast` in goal and `hcore`.
  simp only [bind_pure_comp, Finset.fmap_def] at hcore ⊢
  -- The goal's predicate `distInt (T·F(·/N))` is defeq to `distInt (f ·)`; so `hcard_le` applies.
  exact le_trans hcard_le hcore

/-- **Prop 4.3** (writeup 463–469): integer points near a curve, `|F''| ≍ 1` normalized to
`1 ≤ |F''| ≤ 256` on `[1/2, 5/2]` (curvature ratio up to 256, faithful to `|F''| ≍ 1`);
count over `(N,2N]`. -/
theorem nearCurve_count : ∃ C : ℝ, 0 < C ∧
    ∀ (N T δ : ℝ) (F : ℝ → ℝ),
      1 < N → 1 < T → 0 < δ → δ < 1 → ContDiff ℝ 2 F →
      (∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), 1 ≤ |iteratedDeriv 2 F x|) →
      (∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), |iteratedDeriv 2 F x| ≤ 256) →
      (((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter
          (fun n => distInt (T * F ((n : ℝ) / N)) ≤ δ)).card : ℝ)
        ≤ C * ((N * T) ^ (1/3 : ℝ) + N * δ
               + N * Real.sqrt (δ / T) * Real.log (2 + N * Real.sqrt (δ / T)) + 1) :=
  ⟨C_nearCurveCount, by unfold C_nearCurveCount C_prop43local; norm_num, nearCurve_count_explicit⟩
