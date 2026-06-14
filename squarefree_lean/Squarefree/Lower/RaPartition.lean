import Mathlib

/-!
# §5 the consecutive-triple partition of `ℛ_a` (writeup 681, 744–748)

`Ra_card_le`: bounds `#ℛ_a` by `W²·B + (large-gap Markov) + 2`, where `B` is a uniform bound
on the per-pair count `#{r∈Ra : r+ℓ₁,r+ℓ₂∈Ra}` over small gap pairs `ℓ₂≤W`.

Mechanism (replaces the writeup's pigeonhole with a direct partition): each element of `Ra`
except the two largest is the START of a unique consecutive triple `(r, succ r, succ²r)` with
gap-pair `(ℓ₁,ℓ₂)=(succ r−r, succ²r−r)`. Partition the triple-starts by gap-pair
(`Finset.card_eq_sum_card_fiberwise`). The small-gap fibers (`ℓ₂≤W`) inject into
`{r:r+ℓ₁,r+ℓ₂∈Ra}` so each has card `≤ B`, and there are `≤ W²` such pairs ⟹ `≤ W²·B`.
The large-gap starts (`ℓ₂>W`) number `≤ 2(M−m)/W` by Markov on `Σ(succ²r−r) ≤ 2(max−min)`.
-/

namespace Squarefree

open Finset

/-- The successor of `r` within `Ra`: the least element of `Ra` strictly greater than `r`
(or `r` itself if there is none). -/
private noncomputable def gsucc (Ra : Finset ℕ) (r : ℕ) : ℕ :=
  if h : (Ra.filter (fun x => r < x)).Nonempty then (Ra.filter (fun x => r < x)).min' h else r

/-- If `r` has a strictly larger element in `Ra`, then `gsucc Ra r ∈ Ra` and `r < gsucc Ra r`. -/
private lemma gsucc_spec {Ra : Finset ℕ} {r : ℕ}
    (h : (Ra.filter (fun x => r < x)).Nonempty) :
    gsucc Ra r ∈ Ra ∧ r < gsucc Ra r := by
  unfold gsucc
  rw [dif_pos h]
  have hmem := Finset.min'_mem (Ra.filter (fun x => r < x)) h
  simp only [mem_filter] at hmem
  exact ⟨hmem.1, hmem.2⟩

/-- `gsucc Ra r` is the least: any element of `Ra` strictly above `r` is `≥ gsucc Ra r`. -/
private lemma gsucc_le {Ra : Finset ℕ} {r y : ℕ} (hy : y ∈ Ra) (hyr : r < y) :
    gsucc Ra r ≤ y := by
  have hne : (Ra.filter (fun x => r < x)).Nonempty :=
    ⟨y, by simp only [mem_filter]; exact ⟨hy, hyr⟩⟩
  unfold gsucc
  rw [dif_pos hne]
  apply Finset.min'_le
  simp only [mem_filter]; exact ⟨hy, hyr⟩

/-- From `2 ≤ #{x∈Ra : r<x}`, the successor `gsucc Ra r` itself has a strictly larger
element in `Ra` (so the *second* successor is well-defined). -/
private lemma gsucc_has_succ {Ra : Finset ℕ} {r : ℕ}
    (h2 : 2 ≤ (Ra.filter (fun x => r < x)).card) :
    ∃ y ∈ Ra, gsucc Ra r < y := by
  classical
  set F := Ra.filter (fun x => r < x) with hF
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  -- `gsucc Ra r ∈ F` (it is in `Ra` and strictly above `r`).
  obtain ⟨hgmem, hglt⟩ := gsucc_spec (Ra := Ra) (r := r) hne
  have hgF : gsucc Ra r ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨hgmem, hglt⟩
  -- erase it; ≥ 2 elements means something remains.
  have herase : (F.erase (gsucc Ra r)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hgF]; omega
  obtain ⟨y, hy⟩ := herase
  rw [Finset.mem_erase] at hy
  have hyne : y ≠ gsucc Ra r := hy.1
  have hyF := hy.2
  rw [hF, Finset.mem_filter] at hyF
  -- `gsucc Ra r ≤ y` by leastness, and `y ≠ gsucc Ra r`, so `gsucc Ra r < y`.
  have hge : gsucc Ra r ≤ y := gsucc_le hyF.1 hyF.2
  exact ⟨y, hyF.1, lt_of_le_of_ne hge (fun hc => hyne hc.symm)⟩

/-- **Per-pair consecutive-triple partition bound for `#ℛ_a`.** Generalizes `Ra_card_le` to a
per-gap-pair bound `B : ℕ → ℕ → ℝ`; the uniform version is recovered as a corollary below. -/
theorem Ra_card_le_perpair {Ra : Finset ℕ} {Wnat : ℕ} {m M : ℝ} {B : ℕ → ℕ → ℝ}
    (hW : 0 < Wnat) (hBnn : ∀ ℓ₁ ℓ₂, 0 ≤ B ℓ₁ ℓ₂) (hmM : m ≤ M)
    (hm : ∀ r ∈ Ra, m ≤ (r : ℝ)) (hM : ∀ r ∈ Ra, (r : ℝ) ≤ M)
    (hpair : ∀ ℓ₁ ℓ₂ : ℕ, 0 < ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ Wnat →
        ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ) ≤ B ℓ₁ ℓ₂) :
    (Ra.card : ℝ)
      ≤ (∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2)
        + 2 * (M - m) / (Wnat : ℝ) + 2 := by
  classical
  -- Edge case: `Ra = ∅`.  The whole proof below only needs `Ra` nonempty (to take min'/max'
  -- and run the successor argument).  But the conclusion is FALSE for `Ra = ∅` when `m > M`:
  -- then `Ra.card = 0` while the RHS `= 2*(M-m)/Wnat + 2 + Wnat²·B` can be negative, and the
  -- hypotheses `hm`/`hM` are vacuous so they impose no `m ≤ M` constraint.  (Concrete:
  -- `Wnat=1, B=0, m=1000, M=0` ⟹ RHS = -1998 < 0 = #Ra.)  The fix is to add `m ≤ M` (or
  -- `Ra.Nonempty`) to the statement — both hold in every intended application.  Reported.
  rcases Ra.eq_empty_or_nonempty with hEmpty | hNE
  · subst hEmpty
    simp only [Finset.card_empty, Nat.cast_zero]
    have h1 : (0:ℝ) ≤ ∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2 :=
      Finset.sum_nonneg (fun p _ => hBnn p.1 p.2)
    have h2 : (0:ℝ) ≤ 2 * (M - m) / (Wnat : ℝ) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  -- `Ra` nonempty: define min/max and successor.
  have hmle : (Ra.min' hNE : ℝ) ≤ (Ra.max' hNE : ℝ) := by
    exact_mod_cast Finset.min'_le_max' Ra hNE
  set g : ℕ → ℕ := gsucc Ra with hg
  set minR := Ra.min' hNE with hminR
  set maxR := Ra.max' hNE with hmaxR
  have hmin : ∀ r ∈ Ra, minR ≤ r := fun r hr => Finset.min'_le Ra r hr
  have hmax : ∀ r ∈ Ra, r ≤ maxR := fun r hr => Finset.le_max' Ra r hr
  have hleast : ∀ r y, y ∈ Ra → r < y → g r ≤ y := fun r y hy hyr => gsucc_le hy hyr
  -- The triple-starts.
  set S := Ra.filter (fun r => 2 ≤ (Ra.filter (fun x => r < x)).card) with hS
  have hSsub : S ⊆ Ra := Finset.filter_subset _ _
  -- Properties of `g` on triple-starts.
  have hSprop : ∀ r ∈ S, r < g r ∧ g r ∈ Ra ∧ g r < g (g r) ∧ g (g r) ∈ Ra := by
    intro r hr
    rw [hS, mem_filter] at hr
    have h2 : 2 ≤ (Ra.filter (fun x => r < x)).card := hr.2
    have hne : (Ra.filter (fun x => r < x)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hgmem, hglt⟩ := gsucc_spec (Ra := Ra) (r := r) hne
    obtain ⟨y, hyRa, hylt⟩ := gsucc_has_succ (Ra := Ra) (r := r) h2
    -- g r has a strictly larger element y in Ra ⟹ second successor exists
    have hne2 : (Ra.filter (fun x => g r < x)).Nonempty :=
      ⟨y, by simp only [mem_filter]; exact ⟨hyRa, hylt⟩⟩
    obtain ⟨hggmem, hgglt⟩ := gsucc_spec (Ra := Ra) (r := g r) hne2
    exact ⟨hglt, hgmem, hgglt, hggmem⟩
  -- ===== Part 1: Ra.card ≤ S.card + 2 =====
  have hpart1 : Ra.card ≤ S.card + 2 := by
    set f : ℕ → ℕ := fun r => (Ra.filter (fun x => r < x)).card with hf
    have hinj : Set.InjOn f Ra := by
      intro a ha b hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hsub : Ra.filter (fun x => b < x) ⊂ Ra.filter (fun x => a < x) := by
          constructor
          · intro x hx; simp only [mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans h hx.2⟩
          · intro hsub
            have : b ∈ Ra.filter (fun x => b < x) := by
              apply hsub; simp only [mem_filter]; exact ⟨hb, h⟩
            simp only [mem_filter] at this; exact lt_irrefl b this.2
        have hlt := Finset.card_lt_card hsub
        rw [hf] at hab; simp only at hab; omega
      · have hsub : Ra.filter (fun x => a < x) ⊂ Ra.filter (fun x => b < x) := by
          constructor
          · intro x hx; simp only [mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans h hx.2⟩
          · intro hsub
            have : a ∈ Ra.filter (fun x => a < x) := by
              apply hsub; simp only [mem_filter]; exact ⟨ha, h⟩
            simp only [mem_filter] at this; exact lt_irrefl a this.2
        have hlt := Finset.card_lt_card hsub
        rw [hf] at hab; simp only at hab; omega
    have hcompl : (Ra \ S).card ≤ 2 := by
      have hmap : ∀ r ∈ Ra \ S, f r ∈ ({0, 1} : Finset ℕ) := by
        intro r hr
        simp only [mem_sdiff, hS, mem_filter, not_and] at hr
        have : ¬ (2 ≤ f r) := fun h2 => (hr.2 hr.1) h2
        simp only [mem_insert, mem_singleton]; omega
      have hinj' : Set.InjOn f ((Ra \ S) : Finset ℕ) := by
        apply hinj.mono
        intro x hx; simp only [Finset.coe_sdiff, Set.mem_diff] at hx; exact hx.1
      calc (Ra \ S).card = ((Ra \ S).image f).card := (Finset.card_image_of_injOn hinj').symm
        _ ≤ ({0,1} : Finset ℕ).card := by
            apply Finset.card_le_card; intro x hx; simp only [mem_image] at hx
            obtain ⟨r, hr, rfl⟩ := hx; exact hmap r hr
        _ ≤ 2 := by decide
    have heq := Finset.card_sdiff_add_card_eq_card hSsub
    omega
  -- ===== Split S into small / large by second gap =====
  set Ssmall := S.filter (fun r => g (g r) - r ≤ Wnat) with hSsmall
  set Slarge := S.filter (fun r => ¬ (g (g r) - r ≤ Wnat)) with hSlarge
  have hSsplit : S.card = Ssmall.card + Slarge.card := by
    rw [hSsmall, hSlarge]
    rw [Finset.card_filter_add_card_filter_not]
  -- gap-pair map
  set gp : ℕ → ℕ × ℕ := fun r => (g r - r, g (g r) - r) with hgp
  -- ===== Part: small bound  (Ssmall.card : ℝ) ≤ Σ_t B p.1 p.2 =====
  set t := (Finset.Icc 1 Wnat) ×ˢ (Finset.Icc 1 Wnat) with ht
  have hsmall : (Ssmall.card : ℝ) ≤ ∑ p ∈ t, B p.1 p.2 := by
    -- gp lands in t on Ssmall
    have hgpmem : ∀ r ∈ Ssmall, gp r ∈ t := by
      intro r hr
      rw [hSsmall, mem_filter] at hr
      obtain ⟨hrS, hle⟩ := hr
      obtain ⟨hglt, hgmem, hgglt, hggmem⟩ := hSprop r hrS
      simp only [hgp, ht, Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · omega
      · -- g r - r ≤ g (g r) - r ≤ Wnat
        omega
      · omega
      · exact hle
    -- each fiber ⊆ pair-count set
    have hfib : ∀ ℓ₁ ℓ₂ : ℕ, Ssmall.filter (fun r => gp r = (ℓ₁, ℓ₂)) ⊆
        Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra) := by
      intro ℓ₁ ℓ₂ r hr
      rw [mem_filter] at hr
      obtain ⟨hrSs, hgpr⟩ := hr
      have hrS : r ∈ S := (Finset.filter_subset _ _) hrSs
      obtain ⟨hglt, hgmem, hgglt, hggmem⟩ := hSprop r hrS
      simp only [hgp, Prod.mk.injEq] at hgpr
      obtain ⟨he1, he2⟩ := hgpr
      rw [mem_filter]
      refine ⟨hSsub hrS, ?_, ?_⟩
      · -- r + ℓ₁ = g r ∈ Ra
        have : r + ℓ₁ = g r := by omega
        rw [this]; exact hgmem
      · have : r + ℓ₂ = g (g r) := by omega
        rw [this]; exact hggmem
    -- structural: nonempty fiber ⟹ 0<ℓ₁<ℓ₂≤W
    have hstruct : ∀ ℓ₁ ℓ₂ : ℕ, (Ssmall.filter (fun r => gp r = (ℓ₁, ℓ₂))).Nonempty →
        0 < ℓ₁ ∧ ℓ₁ < ℓ₂ ∧ ℓ₂ ≤ Wnat := by
      intro ℓ₁ ℓ₂ ⟨r, hr⟩
      rw [mem_filter] at hr
      obtain ⟨hrSs, hgpr⟩ := hr
      have hrS : r ∈ S := (Finset.filter_subset _ _) hrSs
      obtain ⟨hglt, hgmem, hgglt, hggmem⟩ := hSprop r hrS
      rw [hSsmall, mem_filter] at hrSs
      have hle := hrSs.2
      simp only [hgp, Prod.mk.injEq] at hgpr
      obtain ⟨he1, he2⟩ := hgpr
      refine ⟨?_, ?_, ?_⟩ <;> omega
    have hcard : Ssmall.card = ∑ p ∈ t, (Ssmall.filter (fun r => gp r = p)).card :=
      Finset.card_eq_sum_card_fiberwise hgpmem
    have hbound : ∀ p ∈ t, ((Ssmall.filter (fun r => gp r = p)).card : ℝ) ≤ B p.1 p.2 := by
      rintro ⟨ℓ₁, ℓ₂⟩ _
      by_cases hne : (Ssmall.filter (fun r => gp r = (ℓ₁, ℓ₂))).Nonempty
      · obtain ⟨h1, h2, h3⟩ := hstruct ℓ₁ ℓ₂ hne
        have hsub := hfib ℓ₁ ℓ₂
        have hc : (Ssmall.filter (fun r => gp r = (ℓ₁, ℓ₂))).card ≤
            (Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card := Finset.card_le_card hsub
        calc ((Ssmall.filter (fun r => gp r = (ℓ₁, ℓ₂))).card : ℝ)
            ≤ ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ) := by exact_mod_cast hc
          _ ≤ B ℓ₁ ℓ₂ := hpair ℓ₁ ℓ₂ h1 h2 h3
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]; simp only [Finset.card_empty, Nat.cast_zero]; exact hBnn ℓ₁ ℓ₂
    calc (Ssmall.card : ℝ) = ∑ p ∈ t, ((Ssmall.filter (fun r => gp r = p)).card : ℝ) := by
          rw [hcard]; push_cast; ring
      _ ≤ ∑ p ∈ t, B p.1 p.2 := Finset.sum_le_sum hbound
  -- ===== Part: telescoping sums  Σ_S (g r - r) ≤ maxR-minR  and  Σ_S (g(g r)-g r) ≤ maxR-minR =====
  have htel1 : ∑ r ∈ S, (g r - r) ≤ maxR - minR := by
    have hdisj : (S : Set ℕ).PairwiseDisjoint (fun r => Finset.Ico r (g r)) := by
      intro a ha b hb hab
      simp only [Function.onFun, Finset.disjoint_left]
      intro x hxa hxb
      simp only [Finset.mem_Ico] at hxa hxb
      rcases lt_or_gt_of_ne hab with h | h
      · have : g a ≤ b := hleast a b (hSsub hb) h; omega
      · have : g b ≤ a := hleast b a (hSsub ha) h; omega
    have hcardbu : (S.biUnion (fun r => Finset.Ico r (g r))).card = ∑ r ∈ S, (g r - r) := by
      rw [Finset.card_biUnion (fun a ha b hb hab => hdisj ha hb hab)]
      apply Finset.sum_congr rfl; intro r _; rw [Nat.card_Ico]
    rw [← hcardbu]
    have hsub : S.biUnion (fun r => Finset.Ico r (g r)) ⊆ Finset.Ico minR maxR := by
      intro x hx; simp only [Finset.mem_biUnion] at hx
      obtain ⟨r, hr, hxr⟩ := hx
      obtain ⟨hglt, hgmem, _, _⟩ := hSprop r hr
      simp only [Finset.mem_Ico] at hxr ⊢
      exact ⟨le_trans (hmin r (hSsub hr)) hxr.1, lt_of_lt_of_le hxr.2 (hmax (g r) hgmem)⟩
    calc (S.biUnion (fun r => Finset.Ico r (g r))).card
        ≤ (Finset.Ico minR maxR).card := Finset.card_le_card hsub
      _ = maxR - minR := Nat.card_Ico minR maxR
  have htel2 : ∑ r ∈ S, (g (g r) - g r) ≤ maxR - minR := by
    have hdisj : (S : Set ℕ).PairwiseDisjoint (fun r => Finset.Ico (g r) (g (g r))) := by
      intro a ha b hb hab
      simp only [Function.onFun, Finset.disjoint_left]
      intro x hxa hxb
      simp only [Finset.mem_Ico] at hxa hxb
      obtain ⟨hglta, hgmema, _, _⟩ := hSprop a ha
      obtain ⟨hgltb, hgmemb, _, _⟩ := hSprop b hb
      rcases lt_or_gt_of_ne hab with h | h
      · have hab1 : g a ≤ b := hleast a b (hSsub hb) h
        have hgab : g a < g b := lt_of_le_of_lt hab1 hgltb
        have : g (g a) ≤ g b := hleast (g a) (g b) hgmemb hgab
        omega
      · have hab1 : g b ≤ a := hleast b a (hSsub ha) h
        have hgba : g b < g a := lt_of_le_of_lt hab1 hglta
        have : g (g b) ≤ g a := hleast (g b) (g a) hgmema hgba
        omega
    have hcardbu : (S.biUnion (fun r => Finset.Ico (g r) (g (g r)))).card
        = ∑ r ∈ S, (g (g r) - g r) := by
      rw [Finset.card_biUnion (fun a ha b hb hab => hdisj ha hb hab)]
      apply Finset.sum_congr rfl; intro r _; rw [Nat.card_Ico]
    rw [← hcardbu]
    have hsub : S.biUnion (fun r => Finset.Ico (g r) (g (g r))) ⊆ Finset.Ico minR maxR := by
      intro x hx; simp only [Finset.mem_biUnion] at hx
      obtain ⟨r, hr, hxr⟩ := hx
      obtain ⟨_, hgmem, _, hggmem⟩ := hSprop r hr
      simp only [Finset.mem_Ico] at hxr ⊢
      exact ⟨le_trans (hmin (g r) hgmem) hxr.1, lt_of_lt_of_le hxr.2 (hmax (g (g r)) hggmem)⟩
    calc (S.biUnion (fun r => Finset.Ico (g r) (g (g r)))).card
        ≤ (Finset.Ico minR maxR).card := Finset.card_le_card hsub
      _ = maxR - minR := Nat.card_Ico minR maxR
  -- ===== Markov for S_large =====
  -- Σ_S (g(g r) - r) = Σ_S (g r - r) + Σ_S (g(g r) - g r)  ≤ 2(maxR-minR)
  have hsumS : ∑ r ∈ S, (g (g r) - r) = ∑ r ∈ S, (g r - r) + ∑ r ∈ S, (g (g r) - g r) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨hglt, _, hgglt, _⟩ := hSprop r hr
    omega
  have hsumbound : ∑ r ∈ S, (g (g r) - r) ≤ 2 * (maxR - minR) := by
    rw [hsumS]; omega
  have hmarkov : Wnat * Slarge.card ≤ 2 * (maxR - minR) := by
    have hbig : ∀ r ∈ Slarge, Wnat < g (g r) - r := by
      intro r hr; rw [hSlarge, mem_filter] at hr; omega
    have hstep1 : Wnat * Slarge.card ≤ ∑ r ∈ Slarge, (g (g r) - r) := by
      calc Wnat * Slarge.card = ∑ _r ∈ Slarge, Wnat := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ Slarge, (g (g r) - r) := by
            apply Finset.sum_le_sum; intro r hr; exact le_of_lt (hbig r hr)
    have hSlargesub : Slarge ⊆ S := Finset.filter_subset _ _
    have hstep2 : ∑ r ∈ Slarge, (g (g r) - r) ≤ ∑ r ∈ S, (g (g r) - r) :=
      Finset.sum_le_sum_of_subset hSlargesub
    omega
  -- ===== Real combination =====
  have hWR : (0 : ℝ) < (Wnat : ℝ) := by exact_mod_cast hW
  -- span: (maxR - minR : ℝ) ≤ M - m
  have hspan : (maxR : ℝ) - (minR : ℝ) ≤ M - m := by
    have h1 : (maxR : ℝ) ≤ M := hM maxR (Finset.max'_mem Ra hNE)
    have h2 : m ≤ (minR : ℝ) := hm minR (Finset.min'_mem Ra hNE)
    linarith
  have hmleNat : minR ≤ maxR := by
    have := Finset.min'_le_max' Ra hNE; rw [← hminR, ← hmaxR] at this; exact this
  have hmarkovR : (Wnat : ℝ) * (Slarge.card : ℝ) ≤ 2 * ((maxR : ℝ) - (minR : ℝ)) := by
    have hc : ((Wnat * Slarge.card : ℕ) : ℝ) ≤ ((2 * (maxR - minR) : ℕ) : ℝ) := by
      exact_mod_cast hmarkov
    push_cast at hc
    rw [Nat.cast_sub hmleNat] at hc
    convert hc using 2
  have hlarge : (Slarge.card : ℝ) ≤ 2 * (M - m) / (Wnat : ℝ) := by
    rw [le_div_iff₀ hWR]
    calc (Slarge.card : ℝ) * (Wnat : ℝ) = (Wnat : ℝ) * (Slarge.card : ℝ) := by ring
      _ ≤ 2 * ((maxR : ℝ) - (minR : ℝ)) := hmarkovR
      _ ≤ 2 * (M - m) := by linarith [hspan]
  have hScardR : (S.card : ℝ) = (Ssmall.card : ℝ) + (Slarge.card : ℝ) := by
    rw [hSsplit]; push_cast; ring
  have hRaR : (Ra.card : ℝ) ≤ (S.card : ℝ) + 2 := by
    have : ((Ra.card : ℕ) : ℝ) ≤ ((S.card + 2 : ℕ) : ℝ) := by exact_mod_cast hpart1
    push_cast at this; linarith
  calc (Ra.card : ℝ) ≤ (S.card : ℝ) + 2 := hRaR
    _ = (Ssmall.card : ℝ) + (Slarge.card : ℝ) + 2 := by rw [hScardR]
    _ ≤ (∑ p ∈ t, B p.1 p.2) + 2 * (M - m) / (Wnat : ℝ) + 2 := by linarith [hsmall, hlarge]

/-- **Consecutive-triple partition bound for `#ℛ_a`** (uniform per-pair bound `B`). Thin
corollary of `Ra_card_le_perpair` specialized to a constant `B`. -/
theorem Ra_card_le {Ra : Finset ℕ} {Wnat : ℕ} {m M B : ℝ}
    (hW : 0 < Wnat) (hB : 0 ≤ B) (hmM : m ≤ M)
    (hm : ∀ r ∈ Ra, m ≤ (r : ℝ)) (hM : ∀ r ∈ Ra, (r : ℝ) ≤ M)
    (hpair : ∀ ℓ₁ ℓ₂ : ℕ, 0 < ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ Wnat →
        ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ) ≤ B) :
    (Ra.card : ℝ) ≤ (Wnat : ℝ) ^ 2 * B + 2 * (M - m) / (Wnat : ℝ) + 2 := by
  have hkey := Ra_card_le_perpair (Ra := Ra) (Wnat := Wnat) (m := m) (M := M)
    (B := fun _ _ => B) hW (fun _ _ => hB) hmM hm hM hpair
  -- The per-pair sum collapses to `Wnat² · B`.
  have hsum : (∑ _p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B) = (Wnat : ℝ) ^ 2 * B := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have htc : (Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat).card = Wnat ^ 2 := by
      rw [Finset.card_product, Nat.card_Icc]
      have hh : Wnat + 1 - 1 = Wnat := by omega
      rw [hh, pow_two]
    rw [htc]; push_cast; ring
  rw [hsum] at hkey
  exact hkey

/-- **Popularity corollary.** If the Markov "large-gap" term `2(M−m)/W + 2` is at most half of
`#ℛ_a` (the popularity threshold; discharged in the application from `#ℛ_a ≥ K·R/W` together with
`M − m ≤ c·R`), it folds into `#ℛ_a` and the count is bounded by `2·Σ B(ℓ₁,ℓ₂)`.  This is the
pigeonhole-free version of the writeup's "sum over the `O(W²)` pairs" step (writeup 744–748). -/
theorem Ra_card_le_popular {Ra : Finset ℕ} {Wnat : ℕ} {m M : ℝ} {B : ℕ → ℕ → ℝ}
    (hW : 0 < Wnat) (hBnn : ∀ ℓ₁ ℓ₂, 0 ≤ B ℓ₁ ℓ₂) (hmM : m ≤ M)
    (hm : ∀ r ∈ Ra, m ≤ (r : ℝ)) (hM : ∀ r ∈ Ra, (r : ℝ) ≤ M)
    (hpair : ∀ ℓ₁ ℓ₂ : ℕ, 0 < ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ Wnat →
        ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ) ≤ B ℓ₁ ℓ₂)
    (hpop : 2 * (M - m) / (Wnat : ℝ) + 2 ≤ (Ra.card : ℝ) / 2) :
    (Ra.card : ℝ) ≤ 2 * (∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2) := by
  have hkey := Ra_card_le_perpair (Ra := Ra) (Wnat := Wnat) (m := m) (M := M)
    (B := B) hW hBnn hmM hm hM hpair
  linarith

end Squarefree
