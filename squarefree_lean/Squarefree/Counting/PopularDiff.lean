import Mathlib.Tactic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Lemma 2.2 — popular small difference (layer L1, parameter-free)

A finite set of `m ≥ 2` integers inside an interval of length `N` has a difference
`1 ≤ h ≲ N/m` realised `≳ m²/N` times.  Used by Lemma 2.1 (`Counting/FourthDeriv`).
Faithful to `explicit_writeup.md` lines 108–123.  The constant `16` is not load-bearing
downstream (Lemma 2.1 only needs `≳ m²/N`), so it may be relaxed if the tight form resists.
-/

namespace Squarefree.Counting

open Finset

/-- `rcount A h = #{ n ∈ A : n + h ∈ A }`. -/
def rcount (A : Finset ℤ) (h : ℤ) : ℕ := (A.filter (fun n => n + h ∈ A)).card

/-- **Lemma 2.2.** If `A` is a set of `m ≥ 2` integers in a half-open interval `(lo, lo+N]`,
then some `1 ≤ h ≤ 4N/m + 1` has `rcount A h ≥ m²/(16N)`. -/
theorem popular_diff (N : ℝ) (A : Finset ℤ) (lo : ℤ)
    (hA : ∀ n ∈ A, (lo : ℝ) < n ∧ (n : ℝ) ≤ lo + N)
    (hm : 2 ≤ A.card) :
    ∃ h : ℤ, 1 ≤ h ∧ (h : ℝ) ≤ 4 * N / A.card + 1 ∧
      (A.card : ℝ) ^ 2 / (16 * N) ≤ (rcount A h : ℝ) := by
  classical
  -- Basic cardinality facts.
  set m := A.card with hm_def
  have hm1 : 1 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hmr_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  -- The strictly increasing enumeration of `A`.
  set e := A.orderEmbOfFin (rfl : A.card = m) with he_def
  -- Extend `e` to all naturals by clamping the index to `[0, m-1]`.
  have hclamp : ∀ i : ℕ, min i (m - 1) < m := by
    intro i; omega
  set a : ℕ → ℤ := fun i => e ⟨min i (m - 1), hclamp i⟩ with ha_def
  -- `a` is monotone, and strictly increasing on `[0, m-1]`.
  have ha_mem : ∀ i, a i ∈ A := by
    intro i; rw [ha_def]; exact A.orderEmbOfFin_mem rfl _
  have ha_strict : ∀ i, i < m - 1 → a i < a (i + 1) := by
    intro i hi
    rw [ha_def]
    apply e.strictMono
    simp only [Fin.mk_lt_mk]
    omega
  -- Gaps.
  set g : ℕ → ℤ := fun i => a (i + 1) - a i with hg_def
  have hg_pos : ∀ i, i < m - 1 → 1 ≤ g i := by
    intro i hi
    have := ha_strict i hi
    simp only [hg_def]; omega
  -- Telescoping: total span of the first `m-1` gaps.
  have htel : ∑ i ∈ range (m - 1), g i = a (m - 1) - a 0 := by
    simpa [hg_def] using Finset.sum_range_sub a (m - 1)
  -- The span is `< N`.
  have hspan_lt : (a (m - 1) : ℝ) - a 0 < N := by
    have h1 := (hA _ (ha_mem (m - 1))).2
    have h2 := (hA _ (ha_mem 0)).1
    have : (a (m - 1) : ℝ) ≤ lo + N := h1
    have : (lo : ℝ) < a 0 := h2
    linarith [h1, h2]
  -- Lower bound on the total span: sum of `m-1` gaps, each `≥ 1`.
  have hspan_ge : ((m : ℤ) - 1) ≤ a (m - 1) - a 0 := by
    rw [← htel]
    have hconst : ∑ _j ∈ range (m - 1), (1 : ℤ) = (m : ℤ) - 1 := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
      omega
    calc ((m : ℤ) - 1) = ∑ _j ∈ range (m - 1), (1 : ℤ) := hconst.symm
      _ ≤ ∑ j ∈ range (m - 1), g j :=
          sum_le_sum (fun j hj => hg_pos j (mem_range.mp hj))
  have hspan_ge_r : ((m : ℝ) - 1) ≤ (a (m - 1) : ℝ) - a 0 := by
    have : ((m : ℝ) - 1) = (((m : ℤ) - 1 : ℤ) : ℝ) := by push_cast; ring
    rw [this]; exact_mod_cast hspan_ge
  have hN_pos : 0 < N := by
    have hmr1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    linarith [hspan_ge_r, hspan_lt]
  -- The threshold `4N/m` and its floor `H`.
  set thr : ℝ := 4 * N / (m : ℝ) with hthr_def
  have hthr_pos : 0 < thr := by
    rw [hthr_def]; positivity
  -- `m ≤ N + 1`, so `m < 4N`, so `thr > 1` and the floor `H ≥ 1`.
  have hm_le : (m : ℝ) - 1 < N := by
    linarith [hspan_ge_r, hspan_lt]
  have hthr_gt_one : 1 < thr := by
    rw [hthr_def, lt_div_iff₀ hmr_pos]
    -- goal `1 * m < 4 * N`; use `m - 1 < N` and `m ≥ 2`.
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [hm_le, h2]
  set H : ℤ := ⌊thr⌋ with hH_def
  have hH_ge1 : 1 ≤ H := by
    rw [hH_def, Int.le_floor]; exact_mod_cast le_of_lt hthr_gt_one
  have hH_le : (H : ℝ) ≤ thr := by rw [hH_def]; exact Int.floor_le thr
  -- The index set of admissible differences.
  set T : Finset ℤ := Finset.Icc 1 H with hT_def
  have hT_card : (T.card : ℤ) = H := by
    rw [hT_def, Int.card_Icc]; omega
  have hT_nonempty : T.Nonempty := by
    rw [hT_def]; exact ⟨1, by simp [Finset.mem_Icc]; exact hH_ge1⟩
  have hT_card_pos : 0 < T.card := by
    rw [← @Nat.cast_pos ℤ]; rw [hT_card]; omega
  -- Small gaps: indices `i < m-1` whose gap is `≤ thr`.
  set S : Finset ℕ := (range (m - 1)).filter (fun i => (g i : ℝ) ≤ thr) with hS_def
  -- Large gaps count.
  set L : Finset ℕ := (range (m - 1)).filter (fun i => ¬ (g i : ℝ) ≤ thr) with hL_def
  have hSL : S.card + L.card = m - 1 := by
    rw [hS_def, hL_def, Finset.card_filter_add_card_filter_not, card_range]
  -- Each large gap exceeds `thr`.
  have hL_gap : ∀ i ∈ L, thr < (g i : ℝ) := by
    intro i hi
    rw [hL_def, mem_filter] at hi
    exact lt_of_not_ge hi.2
  -- Sum over large gaps bounded by the total span (< N).
  have hL_sum : (L.card : ℝ) * thr < N := by
    have hsub : L ⊆ range (m - 1) := by rw [hL_def]; exact filter_subset _ _
    have hcard_thr : (L.card : ℝ) * thr ≤ ∑ i ∈ L, (g i : ℝ) := by
      rw [← nsmul_eq_mul]
      rw [← Finset.sum_const]
      exact Finset.sum_le_sum (fun i hi => le_of_lt (hL_gap i hi))
    have hsum_le : ∑ i ∈ L, (g i : ℝ) ≤ ∑ i ∈ range (m - 1), (g i : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j hj _
      have : (1 : ℤ) ≤ g j := hg_pos j (mem_range.mp hj)
      have : (0 : ℝ) ≤ (g j : ℝ) := by exact_mod_cast (by omega : (0:ℤ) ≤ g j)
      linarith
    have htot : ∑ i ∈ range (m - 1), (g i : ℝ) = (a (m - 1) : ℝ) - a 0 := by
      have := htel
      have : ((∑ i ∈ range (m - 1), g i : ℤ) : ℝ) = ((a (m - 1) - a 0 : ℤ) : ℝ) := by
        exact_mod_cast congrArg (Int.cast : ℤ → ℝ) htel
      push_cast at this
      simpa using this
    calc (L.card : ℝ) * thr ≤ ∑ i ∈ L, (g i : ℝ) := hcard_thr
      _ ≤ ∑ i ∈ range (m - 1), (g i : ℝ) := hsum_le
      _ = (a (m - 1) : ℝ) - a 0 := htot
      _ < N := hspan_lt
  -- Hence `L.card < m/4`.
  have hL_lt : (L.card : ℝ) < (m : ℝ) / 4 := by
    -- `L.card * (4N/m) < N`, clear denominators: `L.card * 4N < N * m`.
    have hkey : (L.card : ℝ) * (4 * N) < N * (m : ℝ) := by
      have h1 : (L.card : ℝ) * (4 * N / (m : ℝ)) < N := by
        rw [hthr_def] at hL_sum; exact hL_sum
      have h2 : (L.card : ℝ) * (4 * N / (m : ℝ)) * (m : ℝ)
          = (L.card : ℝ) * (4 * N) := by
        field_simp
      nlinarith [mul_lt_mul_of_pos_right h1 hmr_pos, h2]
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [hkey, hN_pos]
  -- So `S.card > 3m/4 - 1`.
  have hScard_gt : (3 * (m : ℝ)) / 4 - 1 < (S.card : ℝ) := by
    have hSLr : (S.card : ℝ) + (L.card : ℝ) = (m : ℝ) - 1 := by
      have : ((S.card + L.card : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hSL
      push_cast at this
      have hm1' : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have : 1 ≤ m := hm1
        push_cast [Nat.cast_sub this]; ring
      rw [hm1'] at this
      linarith
    nlinarith [hL_lt, hSLr]
  -- Double counting: `∑_{h ∈ T} rcount A h ≥ S.card`.
  have hdc : (S.card : ℝ) ≤ ∑ h ∈ T, (rcount A h : ℝ) := by
    -- realise the sum as a sigma-cardinality.
    have hsigma : (T.sigma (fun h => A.filter (fun n => n + h ∈ A))).card
        = ∑ h ∈ T, rcount A h := by
      rw [Finset.card_sigma]; rfl
    -- injection from `S` into the sigma set via `i ↦ ⟨g i, a i⟩`.
    have hinj : S.card ≤ (T.sigma (fun h => A.filter (fun n => n + h ∈ A))).card := by
      apply Finset.card_le_card_of_injOn (fun i => (⟨g i, a i⟩ : Σ _ : ℤ, ℤ))
      · intro i hi
        simp only [hS_def, Finset.coe_filter, Set.mem_setOf_eq, mem_range] at hi
        obtain ⟨hi_range, hi_small⟩ := hi
        simp only [Finset.mem_coe, Finset.mem_sigma, mem_filter]
        refine ⟨?_, ha_mem i, ?_⟩
        · -- g i ∈ T
          rw [hT_def, mem_Icc]
          refine ⟨hg_pos i hi_range, ?_⟩
          rw [hH_def, Int.le_floor]
          exact hi_small
        · -- a i + g i ∈ A
          have : a i + g i = a (i + 1) := by rw [hg_def]; ring
          rw [this]; exact ha_mem (i + 1)
      · -- injectivity on S
        intro i hi j hj hij
        simp only [hS_def, Finset.coe_filter, Set.mem_setOf_eq, mem_range] at hi hj
        simp only [Sigma.mk.injEq] at hij
        -- second component equality: a i = a j (from HEq)
        have haij : a i = a j := eq_of_heq hij.2
        -- a is injective on indices `< m`, hence injective there.
        rw [ha_def] at haij
        have hmin := e.injective haij
        simp only [Fin.mk.injEq] at hmin
        -- both `i, j < m-1`, so the clamping `min · (m-1)` is the identity.
        omega
    calc (S.card : ℝ) ≤ ((T.sigma (fun h => A.filter (fun n => n + h ∈ A))).card : ℝ) := by
          exact_mod_cast hinj
      _ = ((∑ h ∈ T, rcount A h : ℕ) : ℝ) := by rw [hsigma]
      _ = ∑ h ∈ T, (rcount A h : ℝ) := by push_cast; rfl
  -- Pigeonhole: some `h ∈ T` has `rcount A h ≥ S.card / T.card`.
  have havg : ∃ h ∈ T, (S.card : ℝ) / (T.card : ℝ) ≤ (rcount A h : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hsum_lt : ∑ h ∈ T, (rcount A h : ℝ) < ∑ _h ∈ T, (S.card : ℝ) / (T.card : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hT_nonempty
      intro h hh; exact hcon h hh
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_lt
    have hTc : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hT_card_pos
    rw [mul_div_cancel₀ _ (ne_of_gt hTc)] at hsum_lt
    linarith [hdc, hsum_lt]
  obtain ⟨h, hhT, hh_ge⟩ := havg
  refine ⟨h, ?_, ?_, ?_⟩
  · -- 1 ≤ h
    rw [hT_def, mem_Icc] at hhT; exact hhT.1
  · -- h ≤ 4N/m + 1
    rw [hT_def, mem_Icc] at hhT
    have : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hhT.2
    have : (h : ℝ) ≤ thr := le_trans this hH_le
    rw [hthr_def] at this
    linarith
  · -- the count bound
    -- rcount ≥ S.card / T.card ≥ S.card * m / (4N) > (3m/4 - 1) * m / (4N) ≥ m²/(16N)
    have hTcr : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hT_card_pos
    have hScard_nonneg : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    -- T.card ≤ thr = 4N/m
    have hTcard_le_thr : (T.card : ℝ) ≤ thr := by
      have : ((T.card : ℤ) : ℝ) = (H : ℝ) := by rw [hT_card]
      have h1 : (T.card : ℝ) = (H : ℝ) := by exact_mod_cast hT_card
      rw [h1]; exact hH_le
    -- S.card / T.card ≥ S.card / thr = S.card * m / (4N)
    have hstep1 : (S.card : ℝ) / thr ≤ (S.card : ℝ) / (T.card : ℝ) :=
      div_le_div_of_nonneg_left hScard_nonneg hTcr hTcard_le_thr
    have hSthr : (S.card : ℝ) / thr = (S.card : ℝ) * (m : ℝ) / (4 * N) := by
      rw [hthr_def, div_div_eq_mul_div]
    -- combine: rcount ≥ S.card * m / (4N)
    have hrc_ge : (S.card : ℝ) * (m : ℝ) / (4 * N) ≤ (rcount A h : ℝ) := by
      calc (S.card : ℝ) * (m : ℝ) / (4 * N) = (S.card : ℝ) / thr := hSthr.symm
        _ ≤ (S.card : ℝ) / (T.card : ℝ) := hstep1
        _ ≤ (rcount A h : ℝ) := hh_ge
    -- now show m²/(16N) ≤ S.card * m / (4N)
    have h4N_pos : (0 : ℝ) < 4 * N := by positivity
    have h16N_pos : (0 : ℝ) < 16 * N := by positivity
    have hfinal : (m : ℝ) ^ 2 / (16 * N) ≤ (S.card : ℝ) * (m : ℝ) / (4 * N) := by
      rw [div_le_div_iff₀ h16N_pos h4N_pos]
      -- m² * (4N) ≤ S.card * m * (16N)  ⟺  m * (after /4N) ... use S.card > 3m/4 - 1
      -- equivalently m² ≤ 4 * S.card * m, i.e. m ≤ 4 S.card (since m>0)
      -- We have S.card > 3m/4 - 1 ≥ m/4 (since m ≥ 2 ⇒ 3m/4 - 1 ≥ m/4 ⇔ m/2 ≥ 1)
      have hm_le_4S : (m : ℝ) ≤ 4 * (S.card : ℝ) := by
        have h2 : (m : ℝ) / 4 ≤ (3 * (m : ℝ)) / 4 - 1 := by
          have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        linarith [hScard_gt, h2]
      have hmN : (0 : ℝ) ≤ (m : ℝ) * N := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hm_le_4S hmN, hmr_pos, hN_pos]
    linarith [hfinal, hrc_ge]

end Squarefree.Counting
