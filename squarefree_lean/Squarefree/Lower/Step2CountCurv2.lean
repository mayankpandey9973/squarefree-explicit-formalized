import Squarefree.Lower.Step2LowerMax
import Squarefree.Lower.Step2RoundDist
import Squarefree.Lower.Step2D2Zero

/-!
# §5 Step-2 curvature-regime per-`f` count (`Ra_step2_count_curv`)

The curvature-regime (all-`f`, NO `f`-largeness) analogue of `Ra_step2_count`.  The engine is the
SLACK bands count `step2_subset_count_cal_slack` (loose `cu = 10⁴³`, `cl = 1/(5184·10¹²⁸)`) at the
full variation scale `T = T₀ + T_curv` (`T₀ = |f|·D⁴/(X·A)`, `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`), fed by:

* `phif_deriv_ub_allf` — the all-`f` derivative upper bound (`cu`);
* `phif_lower_max` — the all-`f` lower bound at the FULL scale `T` (`cl`);
* `phif_d2_zero_le_one` — the ≤2-piece monotone split of `deriv φ_f`;
* `phif_round_distInt` — the per-`r` near-integer reduction.

The window `[(1/72)S.R, 16 S.R]` is tiled by `K = 7` ratio-`3` bands; `phif_d2_zero_le_one` cuts the
window into a `MonotoneOn` half `[lo,z]` and an `AntitoneOn` half `[z,hi]`, each tiled separately.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- Split a `[a,b]`-restricted `ℕ`-filter at a real breakpoint `s`. -/
private theorem filter_split_curv (F : Finset ℕ) (a b s : ℝ) :
    ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ)
      ≤ ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s)).card : ℝ)
        + ((F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ) := by
  classical
  have hsub : F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)
      ⊆ (F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s))
        ∪ (F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrF, ha, hb⟩ := hr
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt (r:ℝ) s with hle | hgt
    · exact Or.inl ⟨hrF, ha, hle⟩
    · exact Or.inr ⟨hrF, le_of_lt hgt, hb⟩
  calc ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ)
      ≤ (((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s))
          ∪ (F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by exact_mod_cast Finset.card_union_le _ _

/-- A `[a,b]`-restricted `ℕ`-filter with `b < a + 1` has card `≤ 1`. -/
private theorem filter_degen_curv (F : Finset ℕ) (a b : ℝ) (hba : b < a + 1) :
    ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ) ≤ 1 := by
  classical
  have hsub : (F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨_, hax, hxb⟩ := hx
    obtain ⟨_, hay, hyb⟩ := hy
    have hxy : x < y + 1 := by exact_mod_cast (by linarith [lt_of_le_of_lt hxb hba, hay] :
      (x:ℝ) < (y:ℝ) + 1)
    have hyx : y < x + 1 := by exact_mod_cast (by linarith [lt_of_le_of_lt hyb hba, hax] :
      (y:ℝ) < (x:ℝ) + 1)
    omega
  exact_mod_cast hsub

/-- **Per-band curvature count.**  For a single ratio-`3` band `[r₀,r₁]` (`r₁ ≤ 3·r₀`) inside the §5
window, with `deriv φ_f` `MonotoneOn`/`AntitoneOn` over `[r₀,r₁]`, the near-`φ_f`-integer count is
`≤ 112·(cu/cl)·(16·R·(δ+√(δ/T)) + T + 1)`, with `T = T₀ + T_curv`, `cu = 10⁴³`,
`cl = 1/(5184·10¹²⁸)`. -/
private theorem step2_band_curv_one {a ℓ₁ ℓ₂ f r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hr_band_lo : (1/72) * S.R ≤ r₀) (hr0r1 : r₀ < r₁)
    (hnarrow : r₁ ≤ 3 * r₀) (hwin : r₁ + ℓ₁ ≤ 16 * S.R)
    (hsmall : (10:ℝ) ^ 110 * ℓ₁ ≤ S.R) (hδ : 0 < δ)
    (hmono : MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc r₀ r₁))
    (𝒯 : Finset ℕ)
    (hsubT : ∀ r ∈ 𝒯, r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
      Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    (𝒯.card : ℝ) ≤ 112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))
        * (16 * S.R * (δ + Real.sqrt (δ /
              (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D)))
          + (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) + 1) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hXpos : 0 < P.X := P.X_pos
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  have hr0pos : 0 < r₀ := lt_of_lt_of_le (by positivity) hr_band_lo
  have hr0_16R : r₀ ≤ 16 * S.R := by linarith [hr0r1, hwin, hℓ1.le]
  have hsmall78 : (10:ℝ) ^ 78 * ℓ₁ ≤ S.R :=
    le_trans (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 78, hℓ1.le]) hsmall
  have hRN : S.R ≤ 72 * r₀ := by linarith [hr_band_lo]
  -- the full variation scale `T = T₀ + T_curv`
  set T : ℝ := |f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D with hT_def
  have hTpos : 0 < T := by
    rw [hT_def]
    have : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D := by positivity
    have h0 : 0 ≤ |f| * S.D ^ 4 / (P.X * S.A) := by positivity
    linarith
  set cu : ℝ := (10:ℝ) ^ 43 with hcu_def
  set cl : ℝ := 1 / (5184 * 10 ^ 128) with hcl_def
  have hcu1 : (1:ℝ) ≤ cu := by rw [hcu_def]; norm_num
  have hclpos : 0 < cl := by rw [hcl_def]; norm_num
  have hcl1 : cl ≤ 1 := by rw [hcl_def]; norm_num
  -- contDiff on the band's open neighbourhood
  have hr0m1 : 0 < r₀ - 1 := by
    have hRbig : (10:ℝ) ^ 110 ≤ S.R := by nlinarith [hsmall, hℓ1_lo]
    nlinarith [hr_band_lo, hRbig]
  have hN1 : (1:ℝ) ≤ r₀ := by linarith [hr0m1]
  have hcdO : ContDiffOn ℝ 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) (Set.Ioo (r₀ - 1) (r₁ + 1)) :=
    (phif_contDiffOn hXpos ha0 hr0m1 hℓ1.le).mono Set.Ioo_subset_Icc_self
  -- the upper bound `hd1`
  have hd1 : ∀ x ∈ Set.Icc r₀ r₁, |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| ≤ cu * (T / r₀) := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    have hub := phif_deriv_ub_allf (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := x)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 (by linarith [hr_band_lo]) (by linarith [hwin])
    rw [← hT_def] at hub
    refine le_trans hub ?_
    rw [hcu_def]
    have hTnn : 0 ≤ T := hTpos.le
    have hratio : (10:ℝ) ^ 41 / S.R ≤ (10:ℝ) ^ 43 / r₀ := by
      rw [div_le_div_iff₀ hRpos hr0pos]; nlinarith [hr0_16R, hRpos]
    calc (10:ℝ) ^ 41 * T / S.R = ((10:ℝ) ^ 41 / S.R) * T := by ring
      _ ≤ ((10:ℝ) ^ 43 / r₀) * T := mul_le_mul_of_nonneg_right hratio hTnn
      _ = (10:ℝ) ^ 43 * (T / r₀) := by ring
  -- the lower bound `hlower`
  have hlower : ∀ x ∈ Set.Icc r₀ r₁,
      cl * (T / r₀) ≤ |deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) x|
        + r₀ * |iteratedDeriv 2 (fun s => phif P.X a ℓ₁ ℓ₂ f s) x| := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    have hlm := phif_lower_max (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := x)
      (N := r₀) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 (by linarith [hr_band_lo]) (by linarith [hwin])
      hsmall78 hr0pos hRN
    rw [← hT_def] at hlm
    rw [hcl_def]
    exact hlm
  -- the slack engine, band scale `N = r₀`
  have hcount := step2_subset_count_cal_slack (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    (r₀ := r₀) (r₁ := r₁) (δ := δ) (T := T) (N := r₀) (cu := cu) (cl := cl)
    hN1 (le_refl r₀) hnarrow hδ hTpos hr0r1 hcu1 hclpos hcl1 hcdO hd1 hlower hmono
    𝒯 hsubT
  -- rescale `N = r₀ ≤ 16R`
  refine le_trans hcount ?_
  have hsqnn : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
  have hcucl_nn : 0 ≤ 112 * (cu / cl) := by positivity
  apply mul_le_mul_of_nonneg_left _ hcucl_nn
  have h1 : r₀ * (δ + Real.sqrt (δ / T)) ≤ 16 * S.R * (δ + Real.sqrt (δ / T)) := by
    apply mul_le_mul_of_nonneg_right hr0_16R; positivity
  linarith [h1]

/-- **Window-tiling for the curvature count.**  On a `MonotoneOn`/`AntitoneOn` sub-window `[lo,hi]`,
the `[p,q]`-restricted near-`φ_f`-integer count is `≤ (k+1)·Cq` whenever `[p,q] ⊆ [lo,hi]` fits in
`k` ratio-`3` bands (`q ≤ 3^k·p`), where `Cq` is `step2_band_curv_one`'s per-band budget.  Induction
on `k`, peeling the bottom band `[p, min(q,3p)]`. -/
private theorem count_window_curv {a ℓ₁ ℓ₂ f δ lo hi : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hsmall : (10:ℝ) ^ 110 * ℓ₁ ≤ S.R) (hδ : 0 < δ)
    (hmono_win : MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc lo hi)
      ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc lo hi))
    (F : Finset ℕ)
    (hFdist : ∀ r ∈ F, Counting.distInt (phif P.X a ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    ∀ (k : ℕ) (p q : ℝ), (1/72) * S.R ≤ p → lo ≤ p → q ≤ hi → p ≤ q →
      q + ℓ₁ ≤ 16 * S.R → q ≤ 3 ^ k * p →
      ((F.filter (fun (r:ℕ) => p ≤ (r:ℝ) ∧ (r:ℝ) ≤ q)).card : ℝ)
        ≤ ((k : ℝ) + 1) * (112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))
            * (16 * S.R * (δ + Real.sqrt (δ /
                  (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D)))
              + (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) + 1)) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hXpos : 0 < P.X := P.X_pos
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  have hℓ2 : 0 < ℓ₂ := by linarith
  set Cq : ℝ := 112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))
      * (16 * S.R * (δ + Real.sqrt (δ /
            (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D)))
        + (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) + 1) with hCq_def
  have hTexpr_pos : 0 < |f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D := by
    have h0 : 0 ≤ |f| * S.D ^ 4 / (P.X * S.A) := by positivity
    have h1 : 0 < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D := by positivity
    linarith
  have hsqnn : 0 ≤ Real.sqrt (δ /
      (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D)) := Real.sqrt_nonneg _
  have hCq_ge1 : (1:ℝ) ≤ Cq := by
    rw [hCq_def]
    have hdiv : (1:ℝ) ≤ (10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)) := by
      rw [le_div_iff₀ (by norm_num)]; norm_num
    have hshape : (1:ℝ) ≤ 16 * S.R * (δ + Real.sqrt (δ /
          (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D)))
        + (|f| * S.D ^ 4 / (P.X * S.A) + ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * S.B ^ 2 / S.D) + 1 := by
      nlinarith [hRpos.le, hδ.le, hsqnn, hTexpr_pos.le]
    nlinarith [hdiv, hshape]
  have hCq_nn : 0 ≤ Cq := le_trans (by norm_num) hCq_ge1
  intro k
  induction k with
  | zero =>
    intro p q hp72 hlop hqhi hpq hqwin hgeo
    simp only [pow_zero, one_mul] at hgeo
    have hdeg : ((F.filter (fun (r:ℕ) => p ≤ (r:ℝ) ∧ (r:ℝ) ≤ q)).card : ℝ) ≤ 1 :=
      filter_degen_curv F p q (by linarith [hgeo])
    rw [Nat.cast_zero, zero_add, one_mul]
    exact le_trans hdeg hCq_ge1
  | succ k ih =>
    intro p q hp72 hlop hqhi hpq hqwin hgeo
    set s : ℝ := min q (3 * p) with hs_def
    have hppos : 0 < p := lt_of_lt_of_le (by positivity) hp72
    have hs_le_q : s ≤ q := min_le_left _ _
    have hp_le_s : p ≤ s := by rw [hs_def, le_min_iff]; exact ⟨hpq, by linarith [hppos]⟩
    have hs_narrow : s ≤ 3 * p := min_le_right _ _
    have hswin : s + ℓ₁ ≤ 16 * S.R := by linarith [hs_le_q, hqwin]
    have hs_hi : s ≤ hi := le_trans hs_le_q hqhi
    have hsplit := filter_split_curv F p q s
    -- BOTTOM band `[p,s]`
    have hbot : ((F.filter (fun (r:ℕ) => p ≤ (r:ℝ) ∧ (r:ℝ) ≤ s)).card : ℝ) ≤ Cq := by
      rcases eq_or_lt_of_le hp_le_s with hdeg | hlt
      · have := filter_degen_curv F p s (by rw [← hdeg]; linarith)
        exact le_trans this hCq_ge1
      · rw [hCq_def]
        have hmono_band : MonotoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc p s)
            ∨ AntitoneOn (deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s)) (Set.Icc p s) :=
          hmono_win.imp (fun h => h.mono (Set.Icc_subset_Icc hlop hs_hi))
            (fun h => h.mono (Set.Icc_subset_Icc hlop hs_hi))
        apply step2_band_curv_one (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
          (r₀ := p) (r₁ := s) (δ := δ)
          hAD ha0 ha_lo ha_hi hℓ1 hℓ1_lo hℓ12 hp72 hlt hs_narrow hswin hsmall hδ hmono_band _
        intro r hr
        rw [Finset.mem_filter] at hr
        exact ⟨hr.2.1, hr.2.2, hFdist r hr.1⟩
    -- TOP band `[s,q]`
    have htop : ((F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ q)).card : ℝ) ≤ ((k:ℝ)+1) * Cq := by
      by_cases hqs : q ≤ s
      · have := filter_degen_curv F s q (by linarith [hqs])
        calc _ ≤ (1:ℝ) := this
          _ ≤ ((k:ℝ)+1) * Cq := by nlinarith [hCq_ge1, (by positivity : (0:ℝ) ≤ (k:ℝ))]
      · push_neg at hqs
        have h3pq : 3 * p ≤ q := by
          have hmlt : min q (3 * p) < q := by rw [← hs_def]; exact hqs
          rcases min_lt_iff.mp hmlt with h | h
          · exact absurd h (lt_irrefl q)
          · exact le_of_lt h
        have hs_eq : s = 3 * p := by rw [hs_def, min_eq_right h3pq]
        have hgeo' : q ≤ 3 ^ k * s := by
          rw [hs_eq]
          have hpow : (3:ℝ) ^ (k + 1) = 3 ^ k * 3 := by rw [pow_succ]
          rw [hpow] at hgeo
          calc q ≤ 3 ^ k * 3 * p := hgeo
            _ = 3 ^ k * (3 * p) := by ring
        have hs72 : (1/72) * S.R ≤ s := le_trans hp72 hp_le_s
        have hlos : lo ≤ s := le_trans hlop hp_le_s
        exact ih s q hs72 hlos hqhi (le_of_lt hqs) hqwin hgeo'
    calc ((F.filter (fun (r:ℕ) => p ≤ (r:ℝ) ∧ (r:ℝ) ≤ q)).card : ℝ)
        ≤ ((F.filter (fun (r:ℕ) => p ≤ (r:ℝ) ∧ (r:ℝ) ≤ s)).card : ℝ)
          + ((F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ q)).card : ℝ) := hsplit
      _ ≤ Cq + ((k:ℝ)+1) * Cq := by linarith [hbot, htop]
      _ = ((((k : ℕ) + 1 : ℕ) : ℝ) + 1) * Cq := by push_cast; ring

/-- **§5 Step-2 curvature-regime per-`f` count.**  For ANY integer `f` (no `f`-largeness), the set
of triples `r ∈ Ra` (with `r+ℓ₁,r+ℓ₂ ∈ Ra`) whose defect rounds to `f` has card
`≤ 10²⁰⁰·(R·(δ + √(δ/T)) + T + 1)`, with `δ = 4·δ₂₃`, `T = T₀ + T_curv`
(`T₀ = |f|·D⁴/(X·A)`, `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`).  The ≤2-piece split `phif_d2_zero_le_one`
cuts the window into a monotone and an antitone half, each tiled by `count_window_curv`. -/
theorem Ra_step2_count_curv {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    {f : ℤ}
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hsmall : (10:ℝ) ^ 110 * ((ℓ₁ : ℤ) : ℝ) ≤ S.R)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ)
      ≤ 10 ^ 200 * (S.R * (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
            + Real.sqrt (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
              / (|(f:ℝ)| * S.D ^ 4 / (P.X * S.A)
                + ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D)))
          + (|(f:ℝ)| * S.D ^ 4 / (P.X * S.A)
              + ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D) + 1) := by
  classical
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1r : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  -- δ and the variation scale `T`
  set δ : ℝ := 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) with hδ_def
  have hδpos : 0 < δ := by rw [hδ_def]; have := S.Ω_pos; have := P.G_pos; have := S.Δ_pos; positivity
  -- the filter set `F`
  set F : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
      round (Qval P a dStar ℓ₁ ℓ₂ r) = f) with hF_def
  -- `distInt(φ_f r) ≤ δ` for every `r ∈ F`
  have hFdist : ∀ r ∈ F, Counting.distInt
      (phif P.X (a:ℝ) ((ℓ₁:ℤ):ℝ) ((ℓ₂:ℤ):ℝ) (f:ℝ) (r : ℝ)) ≤ δ := by
    intro r hr
    rw [hF_def, Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1Ra, hr2Ra, hround⟩ := hr
    obtain ⟨hin0, hlo0, hhi0, hRd0, hwlo0, _⟩ := hdStar r hrRa
    obtain ⟨hin1, hlo1, hhi1, hRd1, _, hwhi1⟩ := hdStar (r + ℓ₁) hr1Ra
    obtain ⟨hin2, hlo2, hhi2, hRd2, _, hwhi2⟩ := hdStar (r + ℓ₂) hr2Ra
    have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
    have hcast2 : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast1] at hRd1 hwhi1
    rw [hcast2] at hRd2 hwhi2
    rw [hδ_def]
    exact phif_round_distInt (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) (r := r)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hin0 hlo0 hhi0 hRd0 hwlo0
      hin1 hlo1 hhi1 hRd1 hwhi1 hin2 hlo2 hhi2 hRd2 hwhi2 hround
      h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg
  -- the window `[lo,hi] = [(1/72)R, 16R − ℓ₁]`
  set lo : ℝ := (1/72) * S.R with hlo_def
  set hi : ℝ := 16 * S.R - ((ℓ₁:ℤ):ℝ) with hhi_def
  have hℓ1leR : ((ℓ₁:ℤ):ℝ) ≤ S.R := by
    have : ((ℓ₁:ℤ):ℝ) ≤ (10:ℝ)^110 * ((ℓ₁:ℤ):ℝ) := by nlinarith [hℓ1R]
    linarith [hsmall, this]
  have hlohi : lo ≤ hi := by rw [hlo_def, hhi_def]; linarith [hℓ1leR, hRpos]
  -- the ≤2-piece split
  obtain ⟨z, hzmem, hzmono, hzanti⟩ := phif_d2_zero_le_one (P := P) (S := S) (a := (a:ℝ))
    (ℓ₁ := ((ℓ₁:ℤ):ℝ)) (ℓ₂ := ((ℓ₂:ℤ):ℝ)) (f := (f:ℝ)) (r₀ := lo) (r₁ := hi)
    hAD ha0R ha_lo ha_hi hℓ1r hℓ12R hlohi (by rw [hlo_def]) (by rw [hhi_def]; linarith) hsmall
  obtain ⟨hzlo, hzhi⟩ := Set.mem_Icc.mp hzmem
  -- every `r ∈ F` lies in `[lo,hi]`
  have hFsub : F.filter (fun (r:ℕ) => lo ≤ (r:ℝ) ∧ (r:ℝ) ≤ hi) = F := by
    apply Finset.filter_true_of_mem
    intro r hr
    rw [hF_def, Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1Ra, _, _⟩ := hr
    obtain ⟨_, _, _, _, hwlo0, _⟩ := hdStar r hrRa
    obtain ⟨_, _, _, _, _, hwhi1⟩ := hdStar (r + ℓ₁) hr1Ra
    have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast1] at hwhi1
    exact ⟨by rw [hlo_def]; exact hwlo0, by rw [hhi_def]; linarith [hwhi1]⟩
  -- geometric covers of the two halves by `k = 7` ratio-3 bands
  have h3pow : (16 : ℝ) * S.R ≤ 3 ^ 7 * ((1/72) * S.R) := by
    have : (3:ℝ) ^ 7 * ((1/72) * S.R) = (2187/72) * S.R := by norm_num; ring
    rw [this]; linarith [hRpos]
  have hzwin : z + ((ℓ₁:ℤ):ℝ) ≤ 16 * S.R := by rw [hhi_def] at hzhi; linarith [hzhi]
  have hlo72 : (1/72) * S.R ≤ lo := by rw [hlo_def]
  have hz72 : (1/72) * S.R ≤ z := le_trans (by rw [← hlo_def]) hzlo
  -- monotone half `[lo,z]`
  have hcountL := count_window_curv (P := P) (S := S) (a := (a:ℝ)) (ℓ₁ := ((ℓ₁:ℤ):ℝ))
    (ℓ₂ := ((ℓ₂:ℤ):ℝ)) (f := (f:ℝ)) (δ := δ) (lo := lo) (hi := z)
    hAD ha0R ha_lo ha_hi hℓ1r hℓ1R hℓ12R hsmall hδpos (Or.inl hzmono) F hFdist
    7 lo z hlo72 (le_refl lo) (le_refl z) hzlo hzwin
    (by rw [hlo_def]; calc z ≤ hi := hzhi
          _ ≤ 16 * S.R := by rw [hhi_def]; linarith [hℓ1r]
          _ ≤ 3 ^ 7 * ((1/72) * S.R) := h3pow)
  -- antitone half `[z,hi]`
  have hcountR := count_window_curv (P := P) (S := S) (a := (a:ℝ)) (ℓ₁ := ((ℓ₁:ℤ):ℝ))
    (ℓ₂ := ((ℓ₂:ℤ):ℝ)) (f := (f:ℝ)) (δ := δ) (lo := z) (hi := hi)
    hAD ha0R ha_lo ha_hi hℓ1r hℓ1R hℓ12R hsmall hδpos (Or.inr hzanti) F hFdist
    7 z hi hz72 (le_refl z) (le_refl hi) hzhi (by rw [hhi_def]; linarith)
    (calc hi ≤ 16 * S.R := by rw [hhi_def]; linarith [hℓ1r]
        _ ≤ 3 ^ 7 * ((1/72) * S.R) := h3pow
        _ ≤ 3 ^ 7 * z := by apply mul_le_mul_of_nonneg_left hz72 (by positivity))
  -- assemble:  card F ≤ 16·Cq ≤ 10²⁰⁰·(R(δ+√(δ/T))+T+1)
  set Texpr : ℝ := |(f:ℝ)| * S.D ^ 4 / (P.X * S.A)
      + ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D with hTexpr_def
  set Cq : ℝ := 112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))
      * (16 * S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1) with hCq_def
  have hsplit := filter_split_curv F lo hi z
  have h7 : ((7:ℕ):ℝ) + 1 = 8 := by norm_num
  have hcardF : ((F.card : ℝ)) ≤ ((8:ℝ) * Cq) + ((8:ℝ) * Cq) := by
    have hL : ((F.filter (fun (r:ℕ) => lo ≤ (r:ℝ) ∧ (r:ℝ) ≤ z)).card : ℝ) ≤ 8 * Cq := by
      rw [h7] at hcountL; exact hcountL
    have hR : ((F.filter (fun (r:ℕ) => z ≤ (r:ℝ) ∧ (r:ℝ) ≤ hi)).card : ℝ) ≤ 8 * Cq := by
      rw [h7] at hcountR; exact hcountR
    calc ((F.card : ℝ)) = ((F.filter (fun (r:ℕ) => lo ≤ (r:ℝ) ∧ (r:ℝ) ≤ hi)).card : ℝ) := by
          rw [hFsub]
      _ ≤ ((F.filter (fun (r:ℕ) => lo ≤ (r:ℝ) ∧ (r:ℝ) ≤ z)).card : ℝ)
          + ((F.filter (fun (r:ℕ) => z ≤ (r:ℝ) ∧ (r:ℝ) ≤ hi)).card : ℝ) := hsplit
      _ ≤ 8 * Cq + 8 * Cq := by linarith [hL, hR]
  -- fold `16·Cq ≤ 10²⁰⁰·(R(δ+√(δ/T))+T+1)`
  have hTexpr_pos : 0 < Texpr := by
    rw [hTexpr_def]
    have h0 : 0 ≤ |(f:ℝ)| * S.D ^ 4 / (P.X * S.A) := by
      have := P.X_pos; have := S.Δ_pos; have := S.Ω_pos
      have hApos : 0 < S.A := by unfold Scale.A; positivity
      positivity
    have h1' : 0 < ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D := by
      have hBpos : 0 < S.B := by unfold Scale.B; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
      have hdiff : 0 < ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by linarith [hℓ12R]
      have hℓ2pos : 0 < ((ℓ₂:ℤ):ℝ) := by linarith [hℓ12R, hℓ1r]
      have hnum : 0 < ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 :=
        mul_pos (mul_pos (mul_pos hℓ1r hℓ2pos) hdiff) (by positivity)
      exact div_pos hnum hDpos
    linarith
  have hsqnn : 0 ≤ Real.sqrt (δ / Texpr) := Real.sqrt_nonneg _
  have hfold : (16:ℝ) * Cq ≤ 10 ^ 200 * (S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1) := by
    rw [hCq_def]
    have hshape : 16 * S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1
        ≤ 16 * (S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1) := by
      nlinarith [hRpos.le, hδpos.le, hsqnn, hTexpr_pos.le]
    have hbase : 0 ≤ S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1 := by
      nlinarith [hRpos.le, hδpos.le, hsqnn, hTexpr_pos.le]
    have hconst : 16 * (112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))) * 16 ≤ 10 ^ 200 := by
      norm_num
    calc 16 * (112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))
          * (16 * S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1))
        ≤ 16 * (112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))
          * (16 * (S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left hshape (by positivity)
      _ = (16 * (112 * ((10:ℝ) ^ 43 / (1 / (5184 * 10 ^ 128)))) * 16)
          * (S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1) := by ring
      _ ≤ 10 ^ 200 * (S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1) :=
          mul_le_mul_of_nonneg_right hconst hbase
  calc ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
          round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ)
      = (F.card : ℝ) := by rw [hF_def]
    _ ≤ 16 * Cq := by rw [show (16:ℝ) * Cq = 8 * Cq + 8 * Cq by ring]; exact hcardF
    _ ≤ 10 ^ 200 * (S.R * (δ + Real.sqrt (δ / Texpr)) + Texpr + 1) := hfold

end Squarefree
