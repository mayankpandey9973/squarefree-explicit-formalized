import Squarefree.Lower.Step23Phase
import Squarefree.Counting.Bands

/-!
# §5 Step-2 subset → BANDS count step

The Step-2 analogue of `step3_subset_count` (Step3Count2.lean), but using the BANDS method
(Lemma 4.2, the `√(δ/T)` form, `bands_count_mono` in `Counting/Bands.lean`) instead of the
monotone-preimage count.

A subset `T` of Step-2 triples (`r` in the band window `[r₀,r₁]` with `‖φ_f(r)‖ ≤ δ` for the
fixed integer `f`) injects (ℕ → ℤ) into the smooth-count filter, so `#T ≤` the bands count.
The bands count over the band window `[r₀,r₁] ⊆ [S.R, 3·S.R]` is supplied by `bands_count_mono`,
which gives exactly the `112·(N·(δ+√(δ/T)) + T + 1)` shape with `N := S.R`.

`bands_count_mono` needs the per-piece analytic content of `φ_f` on the band window:
`ContDiff ℝ 2 φ_f`, the derivative upper bound `|φ_f'| ≤ T/N`, the curvature lower bound
`T/N ≤ |φ_f'| + N·|φ_f''|`, and the monotonicity of `φ_f'` (`MonotoneOn`/`AntitoneOn`,
i.e. the constant-sign-`φ_f''` fact). These four facts about `φ_f` on `[r₀,r₁]` are threaded as
explicit hypotheses; the writeup's finding is that `(d̃⁴)'' > 0` unconditionally, so `φ_f''` is
sign-definite and `φ_f'` is monotone on the whole band window (one piece, no split).
-/

namespace Squarefree

open Squarefree.Counting

set_option maxHeartbeats 1600000

open Metric in
/-- **Bump extension of a `ContDiffOn`-function to a global `C²`-function.**  Given `g`
with `ContDiffOn ℝ 2 g (Ioo (r₀-1) (r₁+1))` and `r₀ < r₁`, there is a global `ContDiff ℝ 2`
function `ψ` (built as `η · g` with `η` a smooth bump supported in `Ioo (r₀-1) (r₁+1)`,
equal to `1` on a neighborhood of `[r₀,r₁]`) that agrees with `g` on a neighborhood of every
point of `Icc r₀ r₁`.  This lets `bands_count_mono` (which needs *global* `ContDiff`) be applied
even though `g` is only `C²` on the window. -/
private theorem exists_global_extension {g : ℝ → ℝ} {r₀ r₁ : ℝ} (hr0r1 : r₀ < r₁)
    (hcdO : ContDiffOn ℝ 2 g (Set.Ioo (r₀ - 1) (r₁ + 1))) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ ∧ ∀ x ∈ Set.Icc r₀ r₁, ψ =ᶠ[nhds x] g := by
  classical
  set c : ℝ := (r₀ + r₁) / 2 with hc_def
  -- the smooth bump: `= 1` on `closedBall c rIn = Icc (r₀-1/2) (r₁+1/2)`,
  -- supported in `ball c rOut = Ioo (r₀-3/4) (r₁+3/4) ⊆ Ioo (r₀-1) (r₁+1)`.
  set η : ContDiffBump c :=
    { rIn := (r₁ - r₀) / 2 + 1 / 2
      rOut := (r₁ - r₀) / 2 + 3 / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith } with hη_def
  have hηIn : η.rIn = (r₁ - r₀) / 2 + 1 / 2 := rfl
  have hηOut : η.rOut = (r₁ - r₀) / 2 + 3 / 4 := rfl
  refine ⟨fun s => η s * g s, ?_, ?_⟩
  · -- global `C²`: pointwise.
    rw [← contDiffOn_univ]
    intro x _
    rw [contDiffWithinAt_univ]
    by_cases hx : x ∈ Set.Ioo (r₀ - 1) (r₁ + 1)
    · -- inside the open window: product of two `C²` functions.
      have hxnhds : Set.Ioo (r₀ - 1) (r₁ + 1) ∈ nhds x :=
        (isOpen_Ioo).mem_nhds hx
      have hg : ContDiffAt ℝ 2 g x := hcdO.contDiffAt hxnhds
      have hηcd : ContDiff ℝ (2 : ℕ∞) (fun s => η s) := η.contDiff
      have hη : ContDiffAt ℝ 2 (fun s => η s) x := hηcd.contDiffAt
      exact hη.mul hg
    · -- outside the open window: `η x = 0` on the open nbhd `{y | η.rOut < dist y c}`,
      -- so `η · g ≡ 0` there.
      have hxout : η.rOut < dist x c := by
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
  · -- agreement on a nbhd of every point of `[r₀,r₁]`: there `η = 1`.
    intro x hx
    have hxball : x ∈ ball c η.rIn := by
      rw [Real.ball_eq_Ioo, hηIn, hc_def, Set.mem_Ioo]
      rw [Set.mem_Icc] at hx
      constructor <;> [linarith [hx.1, hx.2]; linarith [hx.1, hx.2]]
    have hη1 : (fun s => η s) =ᶠ[nhds x] (fun _ => (1 : ℝ)) :=
      η.eventuallyEq_one_of_mem_ball hxball
    filter_upwards [hη1] with y hy
    simp only [hy, one_mul]

/-- §5 Step-2 BANDS subset → count.  For the phase `φ_f = phif P.X a ℓ₁ ℓ₂ f` over a *band*
r-window `[r₀,r₁] ⊆ [S.R, 3·S.R]` (so the BANDS geometry constraint `Icc r₀ r₁ ⊆ Icc N (3N)`
holds with `N := S.R`), in the `f`-large regime with the BANDS active condition `4δ < T`
(`T := |f|·S.D⁴/(P.X·S.A)`), the near-`φ_f`-integer count is bounded by the `√(δ/T)` BANDS shape

  `112·(S.R·(δ + √(δ/T)) + T + 1)`.

The four per-piece analytic facts about `φ_f` on `[r₀,r₁]` required by `bands_count_mono` are
threaded as hypotheses: `ContDiffOn ℝ 2 φ_f (Ioo (r₀-1) (r₁+1))` (`hcdO`; the *global*
`ContDiff` is false — `φ_f` has poles where `d̃` vanishes — so only `C²` on an open
neighborhood of the window is assumed, which is then bump-extended to a global `C²` function
internally), the derivative upper bound `|φ_f'| ≤ T/S.R` (`hd1`), the curvature lower bound
`T/S.R ≤ |φ_f'| + S.R·|φ_f''|` (`hlower`), and the monotonicity of `φ_f'` (`hmono`, the
constant-sign-`φ_f''` fact `(d̃⁴)'' > 0`). -/
theorem step2_subset_count {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ f r₀ r₁ δ : ℝ}
    (hRpos : 0 < S.R) (hr_band_lo : S.R ≤ r₀) (hr_band_hi : r₁ ≤ 3 * S.R)
    (hδ : 0 < δ)
    (hT : 0 < |f| * S.D ^ 4 / (P.X * S.A))
    (hactive : 4 * δ < |f| * S.D ^ 4 / (P.X * S.A))
    (hr0r1 : r₀ < r₁)
    (hcdO : ContDiffOn ℝ 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) (Set.Ioo (r₀ - 1) (r₁ + 1)))
    (hd1 : ∀ x ∈ Set.Icc r₀ r₁,
      |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
        ≤ (|f| * S.D ^ 4 / (P.X * S.A)) / S.R)
    (hlower : ∀ x ∈ Set.Icc r₀ r₁,
      (|f| * S.D ^ 4 / (P.X * S.A)) / S.R
        ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
          + S.R * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|)
    (hmono : MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁))
    (T : Finset ℕ)
    (hsubT : ∀ r ∈ T, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    (T.card : ℝ)
      ≤ 112 * (S.R * (δ + Real.sqrt (δ / (|f| * S.D ^ 4 / (P.X * S.A))))
          + (|f| * S.D ^ 4 / (P.X * S.A)) + 1) := by
  -- abbreviate the variation scale `T`
  set Tvar : ℝ := |f| * S.D ^ 4 / (P.X * S.A) with hTvar_def
  set φ : ℝ → ℝ := fun s => phif P.X a ℓ₁ ℓ₂ f s with hφ_def
  -- global `C²` bump-extension `ψ` of `φ`, agreeing with `φ` near every point of `[r₀,r₁]`.
  obtain ⟨ψ, hψcd, hψeq⟩ := exists_global_extension hr0r1 hcdO
  -- on `[r₀,r₁]`, `deriv` and `iteratedDeriv 2` of `ψ` and `φ` agree.
  have hderiv : ∀ x ∈ Set.Icc r₀ r₁, deriv ψ x = deriv φ x :=
    fun x hx => (hψeq x hx).deriv_eq
  have hiter : ∀ x ∈ Set.Icc r₀ r₁, iteratedDeriv 2 ψ x = iteratedDeriv 2 φ x :=
    fun x hx => Filter.EventuallyEq.iteratedDeriv_eq 2 (hψeq x hx)
  -- transfer the three analytic facts from `φ` to `ψ`.
  have hd1' : ∀ x ∈ Set.Icc r₀ r₁, |deriv ψ x| ≤ Tvar / S.R := by
    intro x hx; rw [hderiv x hx]; exact hd1 x hx
  have hlower' : ∀ x ∈ Set.Icc r₀ r₁,
      Tvar / S.R ≤ |deriv ψ x| + S.R * |iteratedDeriv 2 ψ x| := by
    intro x hx; rw [hderiv x hx, hiter x hx]; exact hlower x hx
  have hmono' : MonotoneOn (deriv ψ) (Set.Icc r₀ r₁) ∨ AntitoneOn (deriv ψ) (Set.Icc r₀ r₁) := by
    rcases hmono with h | h
    · exact Or.inl ((h.congr (fun x hx => (hderiv x hx).symm)))
    · exact Or.inr ((h.congr (fun x hx => (hderiv x hx).symm)))
  -- integer values agree: for `n` in the count base, `ψ n = φ n`.
  have hψn : ∀ n : ℤ, ⌈r₀⌉ ≤ n → n ≤ ⌊r₁⌋ → ψ (n : ℝ) = φ (n : ℝ) := by
    intro n hlo hhi
    have hnmem : (n : ℝ) ∈ Set.Icc r₀ r₁ := by
      refine ⟨?_, ?_⟩
      · exact le_trans (Int.le_ceil r₀) (by exact_mod_cast hlo)
      · exact le_trans (by exact_mod_cast hhi) (Int.floor_le r₁)
    exact (hψeq (n : ℝ) hnmem).eq_of_nhds
  -- the integer-filter count over the band window `[r₀,r₁]`, stated for `ψ`.
  set Q : Finset ℤ := (Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
    (fun (n : ℤ) => Counting.distInt (ψ (n : ℝ)) ≤ δ) with hQ_def
  -- the subset `T` injects into `Q` (`ψ n = φ n` on the base).
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun a b h => by simpa using h
  have hsubset : T.image (fun n : ℕ => (n : ℤ)) ⊆ Q := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hrT, rfl⟩ := hz
    obtain ⟨hlo, hhi, hdist⟩ := hsubT r hrT
    rw [hQ_def, Finset.mem_filter, Finset.mem_Icc]
    have hclo : ⌈r₀⌉ ≤ (r : ℤ) := by rw [Int.ceil_le]; push_cast; exact hlo
    have hchi : (r : ℤ) ≤ ⌊r₁⌋ := by rw [Int.le_floor]; push_cast; exact hhi
    refine ⟨⟨hclo, hchi⟩, ?_⟩
    have hcast : (((r : ℤ) : ℝ)) = (r : ℝ) := by push_cast; ring
    rw [hψn (r : ℤ) hclo hchi, hcast]; exact hdist
  have hcard : T.card ≤ Q.card := by
    calc T.card = (T.image (fun n : ℕ => (n : ℤ))).card :=
          (Finset.card_image_of_injective T hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  -- the BANDS bound on `Q`, via `bands_count_mono ψ` with `N := S.R`, one monotone piece.
  have hsub_band : Set.Icc r₀ r₁ ⊆ Set.Icc S.R (3 * S.R) :=
    Set.Icc_subset_Icc hr_band_lo hr_band_hi
  have hbands := Counting.bands_count_mono S.R Tvar δ r₀ r₁ r₀ r₁
    ψ hRpos hT hδ hactive hψcd hsub_band
    (le_refl _) hd1' hlower' hmono'
  calc (T.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ ≤ 112 * (S.R * (δ + Real.sqrt (δ / Tvar)) + Tvar + 1) := hbands

end Squarefree
