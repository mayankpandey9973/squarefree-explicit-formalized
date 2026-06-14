import Squarefree.Lower.Step3Model
import Squarefree.Lower.Step3Witness
import Squarefree.Lower.Step2Bands
import Squarefree.Lower.Step2Curvature
import Squarefree.Lower.Step2Curvature3

/-!
# §5 Step-2 per-`f` count infrastructure (writeup, BANDS regime)

`step2_subset_count_cal`: the `T`-parametric (and regime-agnostic) version of
`step2_subset_count` (`Step2Bands.lean`, which hardcodes `T = |f|·D⁴/(XA)` and assumes the active
regime `4δ < T`).  For the phase `φ_f` over a band window `[r₀,r₁] ⊆ [S.R,3S.R]`, given the four
analytic facts for a *free* variation scale `T`, the near-`φ_f`-integer count is
`≤ 112·(R·(δ+√(δ/T)) + T + 1)`.  It case-splits internally on `4δ < T` (`bands_count_mono`) vs
`T ≤ 4δ` (`bands_count_trivial`), so no active-regime hypothesis is needed.

This is the reusable engine for the intended `Ra_step2_count` (BANDS analogue of `Ra_step3_count`).

## BLOCKER (Ra_step2_count not yet provable — see report)
Wiring `Ra_step2_count` requires a *single* variation scale `T` satisfying both `hd1`
(`|φ_f'| ≤ T/R`) and `hlower` (`T/R ≤ |φ_f'| + R·|φ_f''|`).  The available curvature machinery gives
`phif_deriv_ub : |φ_f'| ≤ 10¹⁴·T₀/R` (so `hd1` needs `T ≥ 10¹⁴·T₀`) and
`phif_curvature_lower : (1/10¹⁶)·T₀/R ≤ |φ_f'| + R·|φ_f''|` (so the provable lower bound only gives
`hlower` for `T ≤ 10⁻¹⁶·T₀`).  These ranges are disjoint by `~10³⁰`, so no `T` discharges both.
Even with the proof-internal (tighter) constants the gap is `≳ 10²²`, rooted in the `10⁶`
two-sided slack of `dtilde_d1_bounds` (`|d̃'| ∈ [B/10⁶, 10⁶·B]`), squared in `φ_f''` (curvature LB)
but linear in `φ_f'` (derivative UB).  Fixing it requires recalibrating `dtilde_d1_bounds` /
`phif_iteratedDeriv2_lb` / `phif_deriv_ub` (in `Defect*` / `Step2Curvature*`), out of scope here.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

open Metric in
/-- Bump-extension of a `ContDiffOn ℝ 2` function on `Ioo (r₀-1) (r₁+1)` to a global `C²`
function agreeing with it near every point of `[r₀,r₁]` (private copy of `Step2Bands`'s
`exists_global_extension`, reused for the calibrated subset count). -/
private theorem exists_global_extension2 {g : ℝ → ℝ} {r₀ r₁ : ℝ} (hr0r1 : r₀ < r₁)
    (hcdO : ContDiffOn ℝ 2 g (Set.Ioo (r₀ - 1) (r₁ + 1))) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ ∧ ∀ x ∈ Set.Icc r₀ r₁, ψ =ᶠ[nhds x] g := by
  classical
  set c : ℝ := (r₀ + r₁) / 2 with hc_def
  set η : ContDiffBump c :=
    { rIn := (r₁ - r₀) / 2 + 1 / 2
      rOut := (r₁ - r₀) / 2 + 3 / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith } with hη_def
  have hηIn : η.rIn = (r₁ - r₀) / 2 + 1 / 2 := rfl
  have hηOut : η.rOut = (r₁ - r₀) / 2 + 3 / 4 := rfl
  refine ⟨fun s => η s * g s, ?_, ?_⟩
  · rw [← contDiffOn_univ]
    intro x _
    rw [contDiffWithinAt_univ]
    by_cases hx : x ∈ Set.Ioo (r₀ - 1) (r₁ + 1)
    · have hxnhds : Set.Ioo (r₀ - 1) (r₁ + 1) ∈ nhds x :=
        (isOpen_Ioo).mem_nhds hx
      have hg : ContDiffAt ℝ 2 g x := hcdO.contDiffAt hxnhds
      have hηcd : ContDiff ℝ (2 : ℕ∞) (fun s => η s) := η.contDiff
      have hη : ContDiffAt ℝ 2 (fun s => η s) x := hηcd.contDiffAt
      exact hη.mul hg
    · have hxout : η.rOut < dist x c := by
        rw [Real.dist_eq, hηOut, hc_def]
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
        rcases hx with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      have hopen : IsOpen {y : ℝ | η.rOut < dist y c} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hzero : (fun s => η s * g s) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hxout] with y hy
        have : η y = 0 := η.zero_of_le_dist (le_of_lt hy)
        rw [this, zero_mul]
      exact (contDiffAt_const).congr_of_eventuallyEq hzero
  · intro x hx
    have hxball : x ∈ ball c η.rIn := by
      rw [Real.ball_eq_Ioo, hηIn, hc_def, Set.mem_Ioo]
      rw [Set.mem_Icc] at hx
      constructor <;> [linarith [hx.1, hx.2]; linarith [hx.1, hx.2]]
    have hη1 : (fun s => η s) =ᶠ[nhds x] (fun _ => (1 : ℝ)) :=
      η.eventuallyEq_one_of_mem_ball hxball
    filter_upwards [hη1] with y hy
    simp only [hy, one_mul]

/-- **Calibrated Step-2 BANDS subset → count, at band scale `N`.**  The `T`-parametric (and
`N`-parametric) version of `step2_subset_count`.  For the phase `φ_f` over a band window
`[r₀,r₁] ⊆ [N,3N]`, with the four analytic facts stated for a *free* variation scale `T` and
*band scale* `N`, the near-`φ_f`-integer count is `≤ 112·(N·(δ+√(δ/T)) + T + 1)`.  This lets the
genuine constants of `phif_deriv_ub`/`phif_curvature_lower` be absorbed into `T`, and the
narrow-band normalization into `N`. -/
theorem step2_subset_count_cal {a ℓ₁ ℓ₂ f r₀ r₁ δ T N : ℝ}
    (hNpos : 0 < N) (hr_band_lo : N ≤ r₀) (hr_band_hi : r₁ ≤ 3 * N)
    (hδ : 0 < δ) (hT : 0 < T) (hr0r1 : r₀ < r₁)
    (hcdO : ContDiffOn ℝ 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) (Set.Ioo (r₀ - 1) (r₁ + 1)))
    (hd1 : ∀ x ∈ Set.Icc r₀ r₁, |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| ≤ T / N)
    (hlower : ∀ x ∈ Set.Icc r₀ r₁,
      T / N ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
        + N * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|)
    (hmono : MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁))
    (𝒯 : Finset ℕ)
    (hsubT : ∀ r ∈ 𝒯, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    (𝒯.card : ℝ) ≤ 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  set φ : ℝ → ℝ := fun s => phif P.X a ℓ₁ ℓ₂ f s with hφ_def
  obtain ⟨ψ, hψcd, hψeq⟩ := exists_global_extension2 hr0r1 hcdO
  have hderiv : ∀ x ∈ Set.Icc r₀ r₁, deriv ψ x = deriv φ x :=
    fun x hx => (hψeq x hx).deriv_eq
  have hiter : ∀ x ∈ Set.Icc r₀ r₁, iteratedDeriv 2 ψ x = iteratedDeriv 2 φ x :=
    fun x hx => Filter.EventuallyEq.iteratedDeriv_eq 2 (hψeq x hx)
  have hd1' : ∀ x ∈ Set.Icc r₀ r₁, |deriv ψ x| ≤ T / N := by
    intro x hx; rw [hderiv x hx]; exact hd1 x hx
  have hlower' : ∀ x ∈ Set.Icc r₀ r₁,
      T / N ≤ |deriv ψ x| + N * |iteratedDeriv 2 ψ x| := by
    intro x hx; rw [hderiv x hx, hiter x hx]; exact hlower x hx
  have hmono' : MonotoneOn (deriv ψ) (Set.Icc r₀ r₁) ∨ AntitoneOn (deriv ψ) (Set.Icc r₀ r₁) := by
    rcases hmono with h | h
    · exact Or.inl ((h.congr (fun x hx => (hderiv x hx).symm)))
    · exact Or.inr ((h.congr (fun x hx => (hderiv x hx).symm)))
  have hψn : ∀ n : ℤ, ⌈r₀⌉ ≤ n → n ≤ ⌊r₁⌋ → ψ (n : ℝ) = φ (n : ℝ) := by
    intro n hlo hhi
    have hnmem : (n : ℝ) ∈ Set.Icc r₀ r₁ := by
      refine ⟨?_, ?_⟩
      · exact le_trans (Int.le_ceil r₀) (by exact_mod_cast hlo)
      · exact le_trans (by exact_mod_cast hhi) (Int.floor_le r₁)
    exact (hψeq (n : ℝ) hnmem).eq_of_nhds
  set Q : Finset ℤ := (Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
    (fun (n : ℤ) => Counting.distInt (ψ (n : ℝ)) ≤ δ) with hQ_def
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun a b h => by simpa using h
  have hsubset : 𝒯.image (fun n : ℕ => (n : ℤ)) ⊆ Q := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hr𝒯, rfl⟩ := hz
    obtain ⟨hlo, hhi, hdist⟩ := hsubT r hr𝒯
    rw [hQ_def, Finset.mem_filter, Finset.mem_Icc]
    have hclo : ⌈r₀⌉ ≤ (r : ℤ) := by rw [Int.ceil_le]; push_cast; exact hlo
    have hchi : (r : ℤ) ≤ ⌊r₁⌋ := by rw [Int.le_floor]; push_cast; exact hhi
    refine ⟨⟨hclo, hchi⟩, ?_⟩
    have hcast : (((r : ℤ) : ℝ)) = (r : ℝ) := by push_cast; ring
    rw [hψn (r : ℤ) hclo hchi, hcast]; exact hdist
  have hcard : 𝒯.card ≤ Q.card := by
    calc 𝒯.card = (𝒯.image (fun n : ℕ => (n : ℤ))).card :=
          (Finset.card_image_of_injective 𝒯 hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  have hsub_band : Set.Icc r₀ r₁ ⊆ Set.Icc N (3 * N) :=
    Set.Icc_subset_Icc hr_band_lo hr_band_hi
  -- `Q.card` bounded by the BANDS shape, case-splitting on the active/trivial regime.
  have hRHS_nn : 0 ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
    have : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
    nlinarith [hNpos.le, hδ.le, hT.le]
  have hQbound : (Q.card : ℝ) ≤ 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
    rw [hQ_def]
    by_cases hactive : 4 * δ < T
    · exact Counting.bands_count_mono N T δ r₀ r₁ r₀ r₁
        ψ hNpos hT hδ hactive hψcd hsub_band (le_refl _) hd1' hlower' hmono'
    · have htriv : T ≤ 4 * δ := not_lt.mp hactive
      have hbase := Counting.bands_count_trivial N T δ r₀ r₁ ψ hNpos hT hδ hsub_band htriv
      calc (((Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
              (fun (n : ℤ) => Counting.distInt (ψ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 4 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := hbase
        _ ≤ 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by nlinarith [hRHS_nn]
  calc (𝒯.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ ≤ 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := hQbound

end Squarefree
