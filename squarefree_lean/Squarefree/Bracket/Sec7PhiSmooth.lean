import Squarefree.Bracket.Sec7Defs
import Squarefree.Geometry.NearCurveResidual

/-!
# §7 phase smoothness foundation

The branch phase `Φ_{ρ,u}` (`sec7_Phi`) is **not** globally `C²`: it is built from
`Ffun ∘ dtilde` and the `dBreve` tower, which are only smooth on the count window (the
`Sec7Phase` structure supplies `HasDerivAt` chains only on `sec7_rWin`/`sec7_tWin`).  The
faithful regularity statement is therefore `ContDiffOn ℝ 2 Φ U` for an **open** `U` inside
the window.

This file provides the generic engine for that: from a finite chain of `HasDerivAt`
relations `(g m)' = g (m+1)` on an open set `U`, the head `g 0` is `Cᴺ` on `U`.
-/

namespace Squarefree

open scoped Topology

/-- **Chain → `ContDiffOn`.**  If, on an open set `U`, each `g m` (for `m ≤ N`) has derivative
`g (m+1)`, then `g 0` is `Cᴺ` on `U`.  (The `m = N` link only furnishes differentiability of
`g N`, which is exactly the continuity needed at the base of the induction.) -/
theorem sec7_contDiffOn_of_hasDerivAt_chain {U : Set ℝ} (hU : IsOpen U) :
    ∀ (N : ℕ) (g : ℕ → ℝ → ℝ),
      (∀ m, m ≤ N → ∀ x ∈ U, HasDerivAt (g m) (g (m + 1) x) x) →
      ContDiffOn ℝ N (g 0) U := by
  intro N
  induction N with
  | zero =>
    intro g hch
    have hdiff : DifferentiableOn ℝ (g 0) U := fun x hx =>
      ((hch 0 (le_refl 0) x hx).differentiableAt).differentiableWithinAt
    simpa [contDiffOn_zero] using hdiff.continuousOn
  | succ n ih =>
    intro g hch
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      push_cast; ring
    rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨?_, ?_, ?_⟩
    · exact fun x hx => ((hch 0 (Nat.zero_le _) x hx).differentiableAt).differentiableWithinAt
    · intro hω
      exact absurd hω (by simp)
    · have hderiv_eq : ∀ x ∈ U, deriv (g 0) x = g 1 x := fun x hx =>
        (hch 0 (Nat.zero_le _) x hx).deriv
      have hshift : ContDiffOn ℝ n (fun x => g (1) x) U :=
        ih (fun m => g (m + 1)) (fun m hm x hx => hch (m + 1) (by omega) x hx)
      exact (contDiffOn_congr hderiv_eq).mpr hshift

section FPieces

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}

/-- The open window on which the `f`-pieces are `C²` (the interior of `sec7_rWin`). -/
theorem sec7_rWinInt_isOpen : IsOpen (interior (sec7_rWin S W)) := isOpen_interior

/-- `f₂` is `C²` on the open window, from the structure's `HasDerivAt` chain. -/
theorem sec7_f2D_contDiffOn (Ph : Sec7Phase P S W a) :
    ContDiffOn ℝ 2 (Ph.f2D 0) (interior (sec7_rWin S W)) := by
  refine sec7_contDiffOn_of_hasDerivAt_chain isOpen_interior 2 (fun m => Ph.f2D m) ?_
  intro m hm x hx
  exact Ph.f2D_hasDeriv m (by omega) x (interior_subset hx)

/-- `f₁` (branch `j`) is `C²` on the open window. -/
theorem sec7_f1D_contDiffOn (Ph : Sec7Phase P S W a) {j : ℤ} (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 2 (Ph.f1D j 0) (interior (sec7_rWin S W)) := by
  refine sec7_contDiffOn_of_hasDerivAt_chain isOpen_interior 2 (fun m => Ph.f1D j m) ?_
  intro m hm x hx
  exact Ph.f1D_hasDeriv j hj m (by omega) x (interior_subset hx)

/-- `f₃` (branch `j`) is `C²` on the open window. -/
theorem sec7_f3D_contDiffOn (Ph : Sec7Phase P S W a) {j : ℤ} (hj : sec7_jBand P S j) :
    ContDiffOn ℝ 2 (Ph.f3D j 0) (interior (sec7_rWin S W)) := by
  refine sec7_contDiffOn_of_hasDerivAt_chain isOpen_interior 2 (fun m => Ph.f3D j m) ?_
  intro m hm x hx
  exact Ph.f3D_hasDeriv j hj m (by omega) x (interior_subset hx)

end FPieces

section Compose

open Squarefree.FiniteDiff

/-- A pure shift `x ↦ f (x + c)` keeps `ContDiffOn`, provided the shift maps the domain into
the smoothness window. -/
theorem sec7_contDiffOn_shift {n : WithTop ℕ∞} {f : ℝ → ℝ} {V DOM : Set ℝ} (c : ℝ)
    (hf : ContDiffOn ℝ n f V) (hmap : Set.MapsTo (fun x => x + c) DOM V) :
    ContDiffOn ℝ n (fun x => f (x + c)) DOM :=
  hf.comp (contDiffOn_id.add contDiffOn_const) hmap

/-- `diff1 h f` is `Cⁿ` on `DOM` when `f` is `Cⁿ` on a window `V` containing both `DOM`
and its `h`-shift. -/
theorem sec7_contDiffOn_diff1 {n : WithTop ℕ∞} {f : ℝ → ℝ} {V DOM : Set ℝ} (h : ℝ)
    (hf : ContDiffOn ℝ n f V) (hsub : DOM ⊆ V) (hmap : Set.MapsTo (fun x => x + h) DOM V) :
    ContDiffOn ℝ n (diff1 h f) DOM := by
  have hshift : ContDiffOn ℝ n (fun x => f (x + h)) DOM := sec7_contDiffOn_shift h hf hmap
  have hbase : ContDiffOn ℝ n f DOM := hf.mono hsub
  simpa [diff1] using hshift.sub hbase

/-- `diff3 h₁ h₂ h₃ f = diff1 h₁ (diff1 h₂ (diff1 h₃ f))` is `Cⁿ` on `DOM`, threaded through
two intermediate windows `V₁ ⊇ V₂ ⊇ DOM` (each absorbing one shift). -/
theorem sec7_contDiffOn_diff3 {n : WithTop ℕ∞} {f : ℝ → ℝ} {W V₂ V₁ DOM : Set ℝ}
    (h₁ h₂ h₃ : ℝ) (hf : ContDiffOn ℝ n f W)
    (hsub2 : V₂ ⊆ W) (hmap2 : Set.MapsTo (fun x => x + h₃) V₂ W)
    (hsub1 : V₁ ⊆ V₂) (hmap1 : Set.MapsTo (fun x => x + h₂) V₁ V₂)
    (hsub0 : DOM ⊆ V₁) (hmap0 : Set.MapsTo (fun x => x + h₁) DOM V₁) :
    ContDiffOn ℝ n (diff3 h₁ h₂ h₃ f) DOM := by
  have hd3 : ContDiffOn ℝ n (diff1 h₃ f) V₂ := sec7_contDiffOn_diff1 h₃ hf hsub2 hmap2
  have hd2 : ContDiffOn ℝ n (diff1 h₂ (diff1 h₃ f)) V₁ :=
    sec7_contDiffOn_diff1 h₂ hd3 hsub1 hmap1
  exact sec7_contDiffOn_diff1 h₁ hd2 hsub0 hmap0

/-- `diff1 h f` on an explicit interval window: shrink by `|h|` on each side. -/
theorem sec7_contDiffOn_diff1_win {n : WithTop ℕ∞} {f : ℝ → ℝ} {lo hi : ℝ} (h : ℝ)
    (hf : ContDiffOn ℝ n f (Set.Ioo lo hi)) :
    ContDiffOn ℝ n (diff1 h f) (Set.Ioo (lo + |h|) (hi - |h|)) := by
  refine sec7_contDiffOn_diff1 h hf ?_ ?_
  · intro x hx; simp only [Set.mem_Ioo] at hx ⊢
    exact ⟨by linarith [abs_nonneg h], by linarith [abs_nonneg h]⟩
  · intro x hx; simp only [Set.mem_Ioo] at hx ⊢
    exact ⟨by linarith [neg_abs_le h], by linarith [le_abs_self h]⟩

/-- `diff3` on an explicit interval window: shrink by `|h₁|+|h₂|+|h₃|` on each side (cumulative
margins down the three nested first differences). -/
theorem sec7_contDiffOn_diff3_win {n : WithTop ℕ∞} {f : ℝ → ℝ} {lo hi : ℝ} (h₁ h₂ h₃ : ℝ)
    (hf : ContDiffOn ℝ n f (Set.Ioo lo hi)) :
    ContDiffOn ℝ n (diff3 h₁ h₂ h₃ f)
      (Set.Ioo (lo + |h₃| + |h₂| + |h₁|) (hi - |h₃| - |h₂| - |h₁|)) := by
  have h3 := sec7_contDiffOn_diff1_win (f := f) h₃ hf
  have h2 := sec7_contDiffOn_diff1_win (f := diff1 h₃ f) h₂ h3
  have h1 := sec7_contDiffOn_diff1_win (f := diff1 h₂ (diff1 h₃ f)) h₁ h2
  have hwlo : lo + |h₃| + |h₂| + |h₁| = lo + |h₃| + |h₂| + |h₁| := rfl
  simpa only [diff3, add_assoc, sub_sub] using h1

/-- The 2-fold difference `diff1 h₂ (diff1 h₃ f)` on an explicit window: shrink by `|h₂|+|h₃|`. -/
theorem sec7_contDiffOn_diff2_win {n : WithTop ℕ∞} {f : ℝ → ℝ} {lo hi : ℝ} (h₂ h₃ : ℝ)
    (hf : ContDiffOn ℝ n f (Set.Ioo lo hi)) :
    ContDiffOn ℝ n (diff1 h₂ (diff1 h₃ f))
      (Set.Ioo (lo + |h₃| + |h₂|) (hi - |h₃| - |h₂|)) := by
  have h3 := sec7_contDiffOn_diff1_win (f := f) h₃ hf
  simpa only [add_assoc, sub_sub] using sec7_contDiffOn_diff1_win (f := diff1 h₃ f) h₂ h3

/-- **Phase assembly.**  The branch-phase expression (the `phiContDiff`-field shape, `g1=f₁`,
`g2=f₂`, `g3=f₃`) is `C²` on the count window `Ioo (flo+M) (fhi-M)`, where `M` is the total
shift budget `|h₁|+|h₂|+|h₃|+|ξ₁|+|ξ₂|+|ξ₃|`, given the three pieces are `C²` on `Ioo flo fhi`. -/
theorem sec7_phi_expanded_contDiffOn {g1 g2 g3 : ℝ → ℝ} {flo fhi : ℝ}
    (h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℝ)
    (hg1 : ContDiffOn ℝ 2 g1 (Set.Ioo flo fhi))
    (hg2 : ContDiffOn ℝ 2 g2 (Set.Ioo flo fhi))
    (hg3 : ContDiffOn ℝ 2 g3 (Set.Ioo flo fhi)) :
    ContDiffOn ℝ 2 (fun r =>
        diff3 h₁ h₂ h₃ g3 r
          + g1 (r + (h₁ + h₂ + h₃)) * (diff3 h₁ h₂ h₃ g2 r + ρ₀)
          + diff1 h₁ g1 (r + (h₁ + h₂ + h₃) - h₁) *
              (diff1 h₂ (diff1 h₃ g2) (r + ξ₁) - u₁ + ρ₁)
          + diff1 h₂ g1 (r + (h₁ + h₂ + h₃) - h₂) *
              (diff1 h₁ (diff1 h₃ g2) (r + ξ₂) - u₂ + ρ₂)
          + diff1 h₃ g1 (r + (h₁ + h₂ + h₃) - h₃) *
              (diff1 h₁ (diff1 h₂ g2) (r + ξ₃) - u₃ + ρ₃))
      (Set.Ioo (flo + (|h₁| + |h₂| + |h₃| + |ξ₁| + |ξ₂| + |ξ₃|))
               (fhi - (|h₁| + |h₂| + |h₃| + |ξ₁| + |ξ₂| + |ξ₃|))) := by
  set M : ℝ := |h₁| + |h₂| + |h₃| + |ξ₁| + |ξ₂| + |ξ₃| with hM
  set U : Set ℝ := Set.Ioo (flo + M) (fhi - M) with hU
  -- all the abs facts, for the `linarith`s below
  have a1 := abs_nonneg h₁; have a2 := abs_nonneg h₂; have a3 := abs_nonneg h₃
  have b1 := abs_nonneg ξ₁; have b2 := abs_nonneg ξ₂; have b3 := abs_nonneg ξ₃
  have l1 := le_abs_self h₁; have l2 := le_abs_self h₂; have l3 := le_abs_self h₃
  have m1 := neg_abs_le h₁; have m2 := neg_abs_le h₂; have m3 := neg_abs_le h₃
  have lx1 := le_abs_self ξ₁; have lx2 := le_abs_self ξ₂; have lx3 := le_abs_self ξ₃
  have mx1 := neg_abs_le ξ₁; have mx2 := neg_abs_le ξ₂; have mx3 := neg_abs_le ξ₃
  -- shift `x ↦ x+c` maps `U` into any `Ioo lo' hi'` covering the displaced window.
  have mapsto : ∀ (c lo' hi' : ℝ), lo' ≤ flo + M + c → fhi - M + c ≤ hi' →
      Set.MapsTo (fun x => x + c) U (Set.Ioo lo' hi') := by
    intro c lo' hi' h1 h2 x hx
    simp only [hU, Set.mem_Ioo] at hx
    simp only [Set.mem_Ioo]
    exact ⟨by linarith, by linarith⟩
  have subU : ∀ (lo' hi' : ℝ), lo' ≤ flo + M → fhi - M ≤ hi' → U ⊆ Set.Ioo lo' hi' := by
    intro lo' hi' h1 h2 x hx
    simp only [hU, Set.mem_Ioo] at hx
    simp only [Set.mem_Ioo]
    exact ⟨by linarith, by linarith⟩
  -- TERM 1: diff3 h₁ h₂ h₃ g3
  have T1 : ContDiffOn ℝ 2 (fun r => diff3 h₁ h₂ h₃ g3 r) U :=
    (sec7_contDiffOn_diff3_win h₁ h₂ h₃ hg3).mono (subU _ _ (by linarith) (by linarith))
  -- TERM 2: g1(r+hΣ) · (diff3 g2 + ρ₀)
  have T2a : ContDiffOn ℝ 2 (fun r => g1 (r + (h₁ + h₂ + h₃))) U :=
    sec7_contDiffOn_shift (h₁ + h₂ + h₃) hg1 (mapsto _ _ _ (by linarith) (by linarith))
  have T2b : ContDiffOn ℝ 2 (fun r => diff3 h₁ h₂ h₃ g2 r + ρ₀) U :=
    ((sec7_contDiffOn_diff3_win h₁ h₂ h₃ hg2).mono
      (subU _ _ (by linarith) (by linarith))).add contDiffOn_const
  have T2 : ContDiffOn ℝ 2
      (fun r => g1 (r + (h₁ + h₂ + h₃)) * (diff3 h₁ h₂ h₃ g2 r + ρ₀)) U := T2a.mul T2b
  -- TERM 3: diff1 h₁ g1 (r+hΣ-h₁) · (diff1 h₂ (diff1 h₃ g2) (r+ξ₁) - u₁ + ρ₁)
  have T3a : ContDiffOn ℝ 2 (fun r => diff1 h₁ g1 (r + (h₁ + h₂ + h₃) - h₁)) U := by
    have hd := sec7_contDiffOn_diff1_win (f := g1) h₁ hg1
    have hs := sec7_contDiffOn_shift (h₂ + h₃) hd (mapsto _ _ _ (by linarith) (by linarith))
    refine hs.congr ?_
    intro x _; rw [show x + (h₁ + h₂ + h₃) - h₁ = x + (h₂ + h₃) from by ring]
  have T3b : ContDiffOn ℝ 2
      (fun r => diff1 h₂ (diff1 h₃ g2) (r + ξ₁) - u₁ + ρ₁) U := by
    have hd := sec7_contDiffOn_diff2_win (f := g2) h₂ h₃ hg2
    have hs := sec7_contDiffOn_shift ξ₁ hd (mapsto _ _ _ (by linarith) (by linarith))
    exact (hs.sub contDiffOn_const).add contDiffOn_const
  have T3 : ContDiffOn ℝ 2
      (fun r => diff1 h₁ g1 (r + (h₁ + h₂ + h₃) - h₁) *
        (diff1 h₂ (diff1 h₃ g2) (r + ξ₁) - u₁ + ρ₁)) U := T3a.mul T3b
  -- TERM 4: diff1 h₂ g1 (r+hΣ-h₂) · (diff1 h₁ (diff1 h₃ g2) (r+ξ₂) - u₂ + ρ₂)
  have T4a : ContDiffOn ℝ 2 (fun r => diff1 h₂ g1 (r + (h₁ + h₂ + h₃) - h₂)) U := by
    have hd := sec7_contDiffOn_diff1_win (f := g1) h₂ hg1
    have hs := sec7_contDiffOn_shift (h₁ + h₃) hd (mapsto _ _ _ (by linarith) (by linarith))
    refine hs.congr ?_
    intro x _; rw [show x + (h₁ + h₂ + h₃) - h₂ = x + (h₁ + h₃) from by ring]
  have T4b : ContDiffOn ℝ 2
      (fun r => diff1 h₁ (diff1 h₃ g2) (r + ξ₂) - u₂ + ρ₂) U := by
    have hd := sec7_contDiffOn_diff2_win (f := g2) h₁ h₃ hg2
    have hs := sec7_contDiffOn_shift ξ₂ hd (mapsto _ _ _ (by linarith) (by linarith))
    exact (hs.sub contDiffOn_const).add contDiffOn_const
  have T4 : ContDiffOn ℝ 2
      (fun r => diff1 h₂ g1 (r + (h₁ + h₂ + h₃) - h₂) *
        (diff1 h₁ (diff1 h₃ g2) (r + ξ₂) - u₂ + ρ₂)) U := T4a.mul T4b
  -- TERM 5: diff1 h₃ g1 (r+hΣ-h₃) · (diff1 h₁ (diff1 h₂ g2) (r+ξ₃) - u₃ + ρ₃)
  have T5a : ContDiffOn ℝ 2 (fun r => diff1 h₃ g1 (r + (h₁ + h₂ + h₃) - h₃)) U := by
    have hd := sec7_contDiffOn_diff1_win (f := g1) h₃ hg1
    have hs := sec7_contDiffOn_shift (h₁ + h₂) hd (mapsto _ _ _ (by linarith) (by linarith))
    refine hs.congr ?_
    intro x _; rw [show x + (h₁ + h₂ + h₃) - h₃ = x + (h₁ + h₂) from by ring]
  have T5b : ContDiffOn ℝ 2
      (fun r => diff1 h₁ (diff1 h₂ g2) (r + ξ₃) - u₃ + ρ₃) U := by
    have hd := sec7_contDiffOn_diff2_win (f := g2) h₁ h₂ hg2
    have hs := sec7_contDiffOn_shift ξ₃ hd (mapsto _ _ _ (by linarith) (by linarith))
    exact (hs.sub contDiffOn_const).add contDiffOn_const
  have T5 : ContDiffOn ℝ 2
      (fun r => diff1 h₃ g1 (r + (h₁ + h₂ + h₃) - h₃) *
        (diff1 h₁ (diff1 h₂ g2) (r + ξ₃) - u₃ + ρ₃)) U := T5a.mul T5b
  exact ((((T1.add T2).add T3).add T4).add T5)

end Compose

section GlobalExtension

open Metric

/-- **Bump extension of a `ContDiffOn`-function to a global `C²`-function.**  Given `g` with
`ContDiffOn ℝ 2 g (Ioo (r₀-1) (r₁+1))` and `r₀ < r₁`, there is a global `ContDiff ℝ 2`
function `ψ` (built as `η · g`, `η` a smooth bump supported in `Ioo (r₀-1) (r₁+1)`, equal to
`1` on a neighborhood of `[r₀,r₁]`) agreeing with `g` on a neighborhood of every point of
`Icc r₀ r₁`.  This lets the count engines (which need *global* `ContDiff`) be applied even
though `g` is only `C²` on the window.

NOTE: this duplicates §5's `Squarefree.exists_global_extension` (`Lower/Step2Bands.lean`); the
two should be unified into a shared analysis helper during cleanup (it is fully generic). -/
theorem sec7_exists_global_extension {g : ℝ → ℝ} {r₀ r₁ : ℝ} (hr0r1 : r₀ < r₁)
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

end GlobalExtension

section Prop43Adapter

open Counting
open Classical

/-- **`ContDiffOn` adapter for the local Prop 4.3 count.**  `Geometry.prop43_local_explicit`
needs the phase to be *globally* `C²`, but the §7 phase is only `ContDiffOn` an open window
around `[N/2, 5N/2]` (it is `Function.invFun`-built).  This adapter bridges the gap exactly as
§5's `step2_subset_count` does: bump-extend `f` to a global `C²` function `ψ`, transfer the
curvature data to `ψ`, count `ψ` (which agrees with `f` on every integer of `[⌊N⌋, ⌊2N⌋] ⊆
[N/2, 5N/2]`), and read the bound back on `f`.  The `2 ≤ N` hypothesis ensures `⌊N⌋ ≥ N/2`. -/
theorem sec7_prop43_local_contDiffOn (N lam δ : ℝ) (f : ℝ → ℝ)
    (hN : 0 < N) (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ < 1) (hN2 : 2 ≤ N)
    (hcdO : ContDiffOn ℝ 2 f (Set.Ioo (N / 2 - 1) (5 * N / 2 + 1)))
    (hNlam : 1 ≤ N ^ 2 * lam)
    (hfloor : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    (((Finset.Icc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 109159296 * (N * lam ^ (1 / 3 : ℝ) + N * δ
             + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1) := by
  have hr0r1 : N / 2 < 5 * N / 2 := by linarith
  obtain ⟨ψ, hψcd, hψeq⟩ := sec7_exists_global_extension hr0r1 hcdO
  -- `iteratedDeriv 2 ψ = iteratedDeriv 2 f` on `[N/2, 5N/2]`, hence the curvature transfers.
  have hiter : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2),
      iteratedDeriv 2 ψ x = iteratedDeriv 2 f x :=
    fun x hx => Filter.EventuallyEq.iteratedDeriv_eq 2 (hψeq x hx)
  have hfloor' : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 ψ x| := by
    intro x hx; rw [hiter x hx]; exact hfloor x hx
  have hupper' : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 ψ x| ≤ 256 * lam := by
    intro x hx; rw [hiter x hx]; exact hupper x hx
  -- `ψ = f` on integers of `[⌊N⌋, ⌊2N⌋]` (which sit inside `[N/2, 5N/2]`).
  have hψn : ∀ n : ℤ, ⌊N⌋ ≤ n → n ≤ ⌊2 * N⌋ → ψ (n : ℝ) = f (n : ℝ) := by
    intro n hlo hhi
    have hnmem : (n : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := by
      constructor
      · have h1 : (⌊N⌋ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
        have h2 : N - 1 < (⌊N⌋ : ℝ) := Int.sub_one_lt_floor N
        linarith
      · have h1 : (n : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by exact_mod_cast hhi
        have h2 : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le _
        linarith
    exact (hψeq (n : ℝ) hnmem).eq_of_nhds
  -- rewrite the `f`-image-filter as the `ψ`-image-filter, then apply the global Prop 4.3.
  -- (The `(n : ℝ)`-coercion makes the index set the `ℝ`-image of `Finset.Icc ⌊N⌋ ⌊2N⌋`.)
  have hfilt : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ))
      = ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (ψ (n : ℝ)) ≤ δ)) := by
    simp only [bind_pure_comp, Finset.fmap_def]
    apply Finset.filter_congr
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Finset.mem_Icc] at ha
    rw [hψn a ha.1 ha.2]
  rw [hfilt]
  exact Geometry.prop43_local_explicit N lam δ ψ hN hlam hδ hδ1 hψcd hNlam hfloor' hupper'

end Prop43Adapter

end Squarefree
