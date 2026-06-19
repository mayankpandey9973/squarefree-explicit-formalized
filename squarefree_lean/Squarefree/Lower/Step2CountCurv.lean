import Squarefree.Lower.Step2Model
import Squarefree.Lower.Step2Curvature
import Squarefree.Lower.Step2Curvature3
import Squarefree.Lower.Step2CurvCurv3

/-!
# §5 Step-2 curvature-regime per-band count (SLACK bands engine)

This file builds the curvature-regime analogue of `step2_band_count` (`Step2CountBand`), using the
**slack** bands engine `bands_count_mono_slack` (`Squarefree/Counting/Bands.lean`).  The slack
engine carries an upper slack `cu ≥ 1` and a lower/curvature slack `cl ∈ (0,1]`, degrading the
count by `cu/cl`.  This removes the tight-calibration wall that blocked the all-`f` Step-2 count:
LOOSE constants `cu`, `cl` suffice.

Pieces:
* `step2_subset_count_cal_slack` — the `N`/`T`-parametric subset→count via `bands_count_mono_slack`
  (the "repaired invocation"), handling all three threshold regimes;
* `phif_deriv_ub_allf` — the **all-`f`** loose derivative upper bound (no `f`-largeness);
* `phif_curvature_lower_band` — the **all-`f`** curvature lower bound repackaged at band scale `N`.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}


open Metric in
/-- Bump-extension of a `ContDiffOn ℝ 2` function on `Ioo (r₀-1) (r₁+1)` to a global `C²` function
agreeing with it near every point of `[r₀,r₁]` (private copy of `Step2Model`'s
`exists_global_extension2`). -/
private theorem exists_global_extension_slack {g : ℝ → ℝ} {r₀ r₁ : ℝ} (hr0r1 : r₀ < r₁)
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

/-- **Calibrated Step-2 SLACK subset → count, at band scale `N`.**  The slack analogue of
`step2_subset_count_cal`: for the phase `φ_f` over a band window `[r₀,r₁] ⊆ [N,3N]` (with `1 ≤ N`),
with the four analytic facts stated for a *free* variation scale `T`, *band scale* `N`, *upper
slack* `cu ≥ 1` and *curvature slack* `cl ∈ (0,1]`, the near-`φ_f`-integer count is
`≤ 112·(cu/cl)·(N·(δ+√(δ/T)) + T + 1)`.  Handles all three threshold regimes (active
`4δ < cl²·T`, trivial `T ≤ 4δ`, and the gap `cl²·T ≤ 4δ < T`). -/
theorem step2_subset_count_cal_slack {a ℓ₁ ℓ₂ f r₀ r₁ δ T N cu cl : ℝ}
    (hN1 : 1 ≤ N) (hr_band_lo : N ≤ r₀) (hr_band_hi : r₁ ≤ 3 * N)
    (hδ : 0 < δ) (hT : 0 < T) (hr0r1 : r₀ < r₁)
    (hcu : 1 ≤ cu) (hcl : 0 < cl) (hcl1 : cl ≤ 1)
    (hcdO : ContDiffOn ℝ 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) (Set.Ioo (r₀ - 1) (r₁ + 1)))
    (hd1 : ∀ x ∈ Set.Icc r₀ r₁, |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| ≤ cu * (T / N))
    (hlower : ∀ x ∈ Set.Icc r₀ r₁,
      cl * (T / N) ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
        + N * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|)
    (hmono : MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁))
    (𝒯 : Finset ℕ)
    (hsubT : ∀ r ∈ 𝒯, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    (𝒯.card : ℝ) ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN1
  have hcucl1 : 1 ≤ cu / cl := by
    rw [le_div_iff₀ hcl]; linarith [hcu, hcl1]
  set φ : ℝ → ℝ := fun s => phif P.X a ℓ₁ ℓ₂ f s with hφ_def
  obtain ⟨ψ, hψcd, hψeq⟩ := exists_global_extension_slack hr0r1 hcdO
  have hderiv : ∀ x ∈ Set.Icc r₀ r₁, deriv ψ x = deriv φ x :=
    fun x hx => (hψeq x hx).deriv_eq
  have hiter : ∀ x ∈ Set.Icc r₀ r₁, iteratedDeriv 2 ψ x = iteratedDeriv 2 φ x :=
    fun x hx => Filter.EventuallyEq.iteratedDeriv_eq 2 (hψeq x hx)
  have hd1' : ∀ x ∈ Set.Icc r₀ r₁, |deriv ψ x| ≤ cu * (T / N) := by
    intro x hx; rw [hderiv x hx]; exact hd1 x hx
  have hlower' : ∀ x ∈ Set.Icc r₀ r₁,
      cl * (T / N) ≤ |deriv ψ x| + N * |iteratedDeriv 2 ψ x| := by
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
  have hsqnn : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
  have hshape_nn : 0 ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
    nlinarith [hNpos.le, hδ.le, hT.le, hsqnn]
  have hQbound : (Q.card : ℝ) ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
    rw [hQ_def]
    by_cases hactive : 4 * δ < cl ^ 2 * T
    · exact Counting.bands_count_mono_slack N T δ r₀ r₁ r₀ r₁ cu cl
        ψ hNpos hT hδ hcu hcl hcl1 hactive hψcd hsub_band (le_refl _) hd1' hlower' hmono'
    · -- not active.  Either trivial (`T ≤ 4δ`) or the gap (`cl²T ≤ 4δ < T`).
      by_cases htriv : T ≤ 4 * δ
      · have hbase := Counting.bands_count_trivial N T δ r₀ r₁ ψ hNpos hT hδ hsub_band htriv
        calc (((Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
                (fun (n : ℤ) => Counting.distInt (ψ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ 4 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := hbase
          _ ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
              have : (4:ℝ) ≤ 112 * (cu / cl) := by nlinarith [hcucl1]
              nlinarith [this, hshape_nn]
      · -- gap regime:  `cl²T ≤ 4δ`, so `√(δ/T) ≥ cl/2`; crude length bound closes.
        push Not at htriv hactive
        have hsqrt_lb : cl / 2 ≤ Real.sqrt (δ / T) := by
          have hratio : (cl / 2) ^ 2 ≤ δ / T := by
            rw [le_div_iff₀ hT]; nlinarith [hactive]
          have h := Real.sqrt_le_sqrt hratio
          rwa [Real.sqrt_sq (by positivity)] at h
        -- crude bound on the filtered count
        have hr0r1le : r₀ ≤ r₁ := le_of_lt hr0r1
        have hlen := card_filter_le_length r₀ r₁ δ ψ hr0r1le
        have hr0N : N ≤ r₀ := hr_band_lo
        have hr13N : r₁ ≤ 3 * N := hr_band_hi
        have hcrude : (((Finset.Icc ⌈r₀⌉ ⌊r₁⌋).filter
            (fun (n : ℤ) => Counting.distInt (ψ (n : ℝ)) ≤ δ)).card : ℝ) ≤ 2 * N + 1 := by
          calc _ ≤ (r₁ - r₀) + 1 := hlen
            _ ≤ 2 * N + 1 := by linarith
        refine le_trans hcrude ?_
        -- 112·(cu/cl)·N·√(δ/T) ≥ 112·(cu/cl)·N·(cl/2) = 56·cu·N ≥ 56N ≥ 2N+1
        have hmid : 112 * (cu / cl) * (N * Real.sqrt (δ / T))
            ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
          have hcuclnn : 0 ≤ 112 * (cu / cl) := by positivity
          apply mul_le_mul_of_nonneg_left _ hcuclnn
          nlinarith [hNpos.le, hδ.le, hT.le, hsqnn]
        refine le_trans ?_ hmid
        have hcukey : 112 * (cu / cl) * (N * Real.sqrt (δ / T))
            ≥ 56 * cu * N := by
          have h1 : N * (cl / 2) ≤ N * Real.sqrt (δ / T) :=
            mul_le_mul_of_nonneg_left hsqrt_lb hNpos.le
          have hclne : cl ≠ 0 := ne_of_gt hcl
          have hexp : 112 * (cu / cl) * (N * (cl / 2)) = 56 * cu * N := by
            field_simp; ring
          calc 56 * cu * N = 112 * (cu / cl) * (N * (cl / 2)) := hexp.symm
            _ ≤ 112 * (cu / cl) * (N * Real.sqrt (δ / T)) := by
                apply mul_le_mul_of_nonneg_left h1 (by positivity)
        have : 2 * N + 1 ≤ 56 * cu * N := by nlinarith [hcu, hN1, hNpos.le]
        linarith [this, hcukey]
  calc (𝒯.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := hQbound

/-- **§5 Step-2 ALL-`f` derivative upper bound.**  Without any `f`-largeness, the phase derivative
is bounded by the LOOSE combination of the two variation scales `T₀ = |f|·D⁴/(XA)` and
`T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`:
`|φ_f'(r)| ≤ 10⁴¹·(T₀ + T_curv)/R`.  (The `f`-large companion `phif_deriv_ub` keeps only `T₀`; here
the curvature scale `T_curv` absorbs the `φ`-terms that dominate for small `f`.) -/
theorem phif_deriv_ub_allf {a ℓ₁ ℓ₂ f r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R) :
    |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r|
      ≤ 10 ^ 41 * (|f| * S.D ^ 4 / (P.X * S.A)
          + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / S.R := by
  have hGpos : 0 < P.G := P.G_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := S.Δ_pos; positivity
  have hΔpos : 0 < S.Δ := S.Δ_pos
  -- window facts
  have hr0 : 0 < r := by nlinarith [hr_lo, hRpos]
  have hrl : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1.le]
  have hℓne : ℓ₁ ≠ 0 := ne_of_gt hℓ1
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  -- the L-scale and W-scale
  set L := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  set W := S.D ^ 4 / (P.X * S.A * S.R) with hW_def
  have hWpos : 0 < W := by rw [hW_def]; positivity
  have hBR : S.B * S.R = S.D := by rw [Scale.B_eq_D_div_R]; field_simp
  have hDB : S.D ^ 3 * S.B / (P.X * S.A) = W := by
    rw [hW_def, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S.D ^ 3 * P.X * S.A) * hBR
  have hD4 : S.D ^ 4 / (P.X * S.A) = W * S.R := by rw [hW_def]; field_simp
  -- d̃ bounds and positivity
  obtain ⟨hd_lo, hd_hi⟩ := dtilde_asymp_D hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  have hd_pos : 0 < dtilde P.X r a := dtilde_pos hXpos ha0 hr0
  obtain ⟨hd1_lo, hd1_hi⟩ := dtilde_d1_bounds hAD ha0 hr0 ha_lo ha_hi hr_lo hr_hi
  obtain ⟨hphi_nn, hphi_ub⟩ := phi_abs_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  have hphi'_ub := phi_deriv_ub hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi
  have hPD := phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r)
    ha0 hr0 hrl hℓne
  rw [hPD.deriv]
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun s => dtilde P.X s a) r with hd1_def
  set φ := phi P.X a ℓ₁ ℓ₂ r with hφ_def
  set φ1 := deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r with hφ1_def
  set c3 := 4 * d ^ 3 * d1 / (6 * P.X * a) with hc3_def
  set c4 := d ^ 4 / (6 * P.X * a) with hc4_def
  have hd3_pos : 0 < d ^ 3 := by positivity
  have hd4_pos : 0 < d ^ 4 := by positivity
  have h6Xa_pos : 0 < 6 * P.X * a := by positivity
  have hc3_abs : |c3| = 4 * d ^ 3 * |d1| / (6 * P.X * a) := by
    rw [hc3_def, abs_div, abs_of_pos h6Xa_pos, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos hd3_pos]
  have hc4_pos : 0 < c4 := by rw [hc4_def]; positivity
  -- |f + φ| ≤ |f| + 10²⁰·L
  have hfphi : |f + φ| ≤ |f| + 10 ^ 20 * L := by
    calc |f + φ| ≤ |f| + |φ| := abs_add_le _ _
      _ = |f| + φ := by rw [abs_of_nonneg hphi_nn]
      _ ≤ |f| + 10 ^ 20 * L := by rw [hL_def]; linarith [hphi_ub]
  have htri : |c3 * (f + φ) + c4 * φ1| ≤ |c3| * |f + φ| + c4 * |φ1| := by
    calc |c3 * (f + φ) + c4 * φ1| ≤ |c3 * (f + φ)| + |c4 * φ1| := abs_add_le _ _
      _ = |c3| * |f + φ| + |c4| * |φ1| := by rw [abs_mul, abs_mul]
      _ = |c3| * |f + φ| + c4 * |φ1| := by rw [abs_of_pos hc4_pos]
  refine le_trans htri ?_
  -- |c3| ≤ C_3·W with C_3 = 4·18³·10⁶·5/6
  have hc3hi : |c3| ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6) * W := by
    rw [hc3_abs]
    have hnum_hi : 4 * d ^ 3 * |d1| ≤ 4 * (18 * S.D) ^ 3 * (1000000 * S.B) := by
      have hp1 : d ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hd_pos.le hd_hi 3
      have h1 : 4 * d ^ 3 ≤ 4 * (18 * S.D) ^ 3 := by linarith [hp1]
      have h2 : (0:ℝ) ≤ 4 * d ^ 3 := by positivity
      exact mul_le_mul h1 hd1_hi (abs_nonneg _) (le_trans h2 h1)
    have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
      apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
    have hstep : 4 * d ^ 3 * |d1| / (6 * P.X * a)
        ≤ 4 * (18 * S.D) ^ 3 * (1000000 * S.B) / (6 * P.X * (S.A / 5)) :=
      div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
    refine le_trans hstep ?_
    have hreq : 4 * (18 * S.D) ^ 3 * (1000000 * S.B) / (6 * P.X * (S.A / 5))
        = (4 * 18 ^ 3 * 1000000 * 5 / 6) * (S.D ^ 3 * S.B / (P.X * S.A)) := by
      field_simp
    rw [hreq, hDB]
  -- term1: |c3|·|f+φ| ≤ C_3·W·|f| + C_3·10²⁰·W·L
  have hC3W_nn : 0 ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6) * W := by positivity
  have hterm1 : |c3| * |f + φ|
      ≤ (4 * 18 ^ 3 * 1000000 * 5 / 6) * (W * |f|)
        + (4 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 20 * (W * L) := by
    calc |c3| * |f + φ|
        ≤ ((4 * 18 ^ 3 * 1000000 * 5 / 6) * W) * (|f| + 10 ^ 20 * L) :=
          mul_le_mul hc3hi hfphi (abs_nonneg _) hC3W_nn
      _ = (4 * 18 ^ 3 * 1000000 * 5 / 6) * (W * |f|)
            + (4 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 20 * (W * L) := by ring
  -- term2: c4·|φ1| ≤ 10⁴⁰·W·L
  have hterm2 : c4 * |φ1| ≤ 10 ^ 40 * (W * L) := by
    have hc4hi : c4 ≤ (18 ^ 4 * 5 / 6) * (W * S.R) := by
      rw [hc4_def]
      have hnum_hi : d ^ 4 ≤ (18 * S.D) ^ 4 := pow_le_pow_left₀ hd_pos.le hd_hi 4
      have hden_ge : 6 * P.X * (S.A / 5) ≤ 6 * P.X * a := by
        apply mul_le_mul_of_nonneg_left ha_lo (by positivity)
      have hstep : d ^ 4 / (6 * P.X * a) ≤ (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5)) :=
        div_le_div₀ (by positivity) hnum_hi (by positivity) hden_ge
      refine le_trans hstep ?_
      have hreq : (18 * S.D) ^ 4 / (6 * P.X * (S.A / 5))
          = (18 ^ 4 * 5 / 6) * (S.D ^ 4 / (P.X * S.A)) := by field_simp
      rw [hreq, hD4]
    have hphi1 : |φ1| ≤ 10 ^ 35 * (L / S.R) := by
      rw [hφ1_def, hL_def]
      calc |deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) r|
          ≤ 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5 * S.R)) := hphi'_ub
        _ = 10 ^ 35 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5) / S.R) := by rw [div_div]
    calc c4 * |φ1|
        ≤ ((18 ^ 4 * 5 / 6) * (W * S.R)) * (10 ^ 35 * (L / S.R)) :=
          mul_le_mul hc4hi hphi1 (abs_nonneg _) (by positivity)
      _ = ((18 ^ 4 * 5 / 6) * 10 ^ 35) * (W * L) := by field_simp
      _ ≤ 10 ^ 40 * (W * L) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
  -- the two scale identities `T₀/R = W·|f|`, `T_curv/R = W·L`.
  have hT0R : |f| * S.D ^ 4 / (P.X * S.A) / S.R = W * |f| := by
    rw [hW_def]; field_simp
  have hTcR : ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D / S.R = W * L := by
    rw [hW_def, hL_def]
    unfold Scale.B Scale.D Scale.A Scale.R
    rw [P.X_eq_G_mul_H_pow_five]
    field_simp
  -- assemble.
  have hWfnn : 0 ≤ W * |f| := by positivity
  have hWLnn : 0 ≤ W * L := by positivity
  have htarget_eq : 10 ^ 41 * (|f| * S.D ^ 4 / (P.X * S.A)
        + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / S.R
      = 10 ^ 41 * (W * |f| + W * L) := by
    rw [mul_div_assoc, add_div, hT0R, hTcR]
  rw [htarget_eq]
  calc |c3| * |f + φ| + c4 * |φ1|
      ≤ ((4 * 18 ^ 3 * 1000000 * 5 / 6) * (W * |f|)
          + (4 * 18 ^ 3 * 1000000 * 5 / 6) * 10 ^ 20 * (W * L)) + 10 ^ 40 * (W * L) :=
        add_le_add hterm1 hterm2
    _ ≤ 10 ^ 41 * (W * |f| + W * L) := by linarith only [hWfnn, hWLnn]

/-- **§5 Step-2 ALL-`f` curvature lower bound, at band scale `N`.**  The keystone
`phif_curvature_lower_curv` (curvature lower bound at scale `R`) repackaged to a band scale
`N` with `R ≤ 72·N` (i.e. `N ≥ R/72`, true for `N = r₀` in the window).  For **all** `f`:
`(1/(5184·10⁷²))·(T_curv/N) ≤ |φ_f'(r)| + N·|φ_f''(r)|`, with `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`.  The
`5184 = 72²` factor absorbs the `R ↔ N` rescaling (one `1/72` from `N·|φ''| ≥ (R/72)|φ''|`, one
from `T_curv/N ≤ 72·T_curv/R`). -/
theorem phif_curvature_lower_band {a ℓ₁ ℓ₂ f r N : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_lo : (1 / 72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10 : ℝ) ^ 78 * ℓ₁ ≤ S.R)
    (hRN : S.R ≤ 72 * N) :
    (1 / (5184 * 10 ^ 72)) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) / N
      ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r|
        + N * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  set Tc : ℝ := ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D with hTc_def
  have hTc_pos : 0 < Tc := by rw [hTc_def]; positivity
  set A := |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| with hA_def
  set Bv := |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) r| with hBv_def
  have hAnn : 0 ≤ A := abs_nonneg _
  have hBvnn : 0 ≤ Bv := abs_nonneg _
  -- keystone at scale R
  have key : (1 / 10 ^ 72) * Tc / S.R ≤ A + S.R * Bv := by
    rw [hTc_def, hA_def, hBv_def]
    exact phif_curvature_lower_curv hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hr_lo hrl_hi hsmall
  -- N ≥ R/72:  N·Bv ≥ (R/72)·Bv, and A ≥ (1/72)A.
  have hstep1 : (1 / 72) * (A + S.R * Bv) ≤ A + N * Bv := by
    have hNBv : (S.R / 72) * Bv ≤ N * Bv :=
      mul_le_mul_of_nonneg_right (by linarith [hRN]) hBvnn
    nlinarith [hNBv, hAnn]
  -- the rescaled curvature floor
  have hchain : (1 / 72) * ((1 / 10 ^ 72) * Tc / S.R) ≤ A + N * Bv := by
    refine le_trans ?_ hstep1
    have : (1 / 72) * ((1 / 10 ^ 72) * Tc / S.R) ≤ (1 / 72) * (A + S.R * Bv) :=
      mul_le_mul_of_nonneg_left key (by norm_num)
    exact this
  refine le_trans ?_ hchain
  -- (1/(5184·10⁷²))·Tc/N ≤ (1/72)·(1/10⁷²)·Tc/R
  have e1 : (1 / (5184 * 10 ^ 72)) * Tc / N = Tc / (5184 * 10 ^ 72 * N) := by ring
  have e2 : (1 / 72) * ((1 / 10 ^ 72) * Tc / S.R) = Tc / (72 * 10 ^ 72 * S.R) := by ring
  rw [e1, e2]
  have hden : (72 : ℝ) * 10 ^ 72 * S.R ≤ 5184 * 10 ^ 72 * N := by nlinarith [hRN]
  gcongr

end Squarefree
