import Squarefree.Counting.Preimage
import Squarefree.Counting.PopularDiff
import Squarefree.Counting.FourthDerivAux
import Squarefree.FiniteDiff
import Mathlib

/-!
# §2 fourth-derivative counting (Lemma 2.1)

The 4th-derivative counting lemma from `../explicit_writeup.md` (lines 84–194): a `C⁴`
function with `|f⁗| ≍ Λ` on `[N,3N]` is within `δ` of `ℤ` at few integers of `(N,2N]`.
The 3-fold differencing engine.  See `CLAUDE.md` §3/§4.

The smoothness hypothesis is `ContDiffOn ℝ 4 f (Ioo 0 (4N))` — `f` is `C⁴` on an open
interval containing `[N,3N]`, which is the faithful form of the writeup's `f ∈ C⁴([N,3N])`
that admits the downstream application `f = X/x²` (smooth on `(0,∞)`).
-/

open Classical Finset Squarefree.FiniteDiff Set

namespace Squarefree.Counting

set_option maxHeartbeats 1600000 in
/-- **Lemma 2.1** (writeup 84–194): 4th-derivative counting via 3-fold differencing.
Generalized from `|f⁗| ≤ 2Λ` to `|f⁗| ≤ K·Λ`; the constant `C` may depend on `K` (the
cross-term genuinely carries `K`, so a single absolute constant is impossible). -/
theorem fourthDeriv_count : ∀ (K : ℝ), 1 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ (N Λ δ : ℝ) (f : ℝ → ℝ),
      2 ≤ N → 0 < δ → δ < 1/4 → 0 < Λ → ContDiffOn ℝ 4 f (Set.Ioo 0 (4 * N)) →
      (∀ x ∈ Set.Icc N (3 * N), Λ ≤ |iteratedDeriv 4 f x|) →
      (∀ x ∈ Set.Icc N (3 * N), |iteratedDeriv 4 f x| ≤ K * Λ) →
      (((Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter (fun (n : ℤ) => distInt (f (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
               + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
  intro K hK1
  -- The combined budget multiplier for `four_case_bound`: `2^70 · K` (final_combine gives
  -- budget `(2^70·K)·(…)`).
  set Kfc : ℝ := 2 ^ 70 * K with hKfcdef
  have hKfc1 : (1 : ℝ) ≤ Kfc := by
    rw [hKfcdef]; calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ 2 ^ 70 * K := by
          apply mul_le_mul (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hK1 (by norm_num) (by positivity)
  obtain ⟨C₀, hC₀pos, hC₀⟩ :
      ∃ C : ℝ, 0 < C ∧ ∀ M N Λ δ : ℝ, 0 < M → 1 ≤ N → 0 < Λ → 0 < δ →
        M ^ 8 ≤ Kfc * (N ^ 7 + Λ * N ^ 15 / M ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ) →
        M ≤ C * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
               + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
    refine ⟨(4*Kfc) ^ (1/8 : ℝ) + (4*Kfc) ^ (1/15 : ℝ), by positivity, ?_⟩
    exact four_case_bound Kfc hKfc1
  refine ⟨max C₀ 1, by positivity, ?_⟩
  intro N Λ δ f hN hδ hδ4 hΛ hf hlb hub
  have hNpos : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  -- Notation.
  set S : Finset ℤ := (Finset.Ioc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ)
    with hSdef
  set M : ℕ := S.card with hMdef
  show (M : ℝ) ≤ _
  -- target sum is ≥ 1 (since N ≥ 2 ⟹ N^{7/8} ≥ 1) and ≥ 0.
  have hsum_ge1 : (1:ℝ) ≤ N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
      + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N := by
    have h1 : (1:ℝ) ≤ N ^ (7/8 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have h2 : (0:ℝ) ≤ N * δ ^ (1/8 : ℝ) := by positivity
    have h3 : (0:ℝ) ≤ N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) := by positivity
    have h4 : (0:ℝ) ≤ Λ ^ (1/15 : ℝ) * N := by positivity
    linarith
  have hsum0 : (0:ℝ) ≤ N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
      + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N := by linarith
  -- The goal's LHS is `(M : ℝ)`.
  rcases Nat.lt_or_ge M 2 with hMbig' | hMbig
  · have hMsmall : M ≤ 1 := by omega
    -- M ≤ 1: card ≤ 1 ≤ (max C₀ 1)·sum.
    have : (M : ℝ) ≤ 1 := by exact_mod_cast hMsmall
    calc (M : ℝ) ≤ 1 := this
      _ ≤ max C₀ 1 * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
            + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) := by
          have hm1 : (1:ℝ) ≤ max C₀ 1 := le_max_right _ _
          nlinarith [hsum_ge1, hm1, le_max_left C₀ 1, hC₀pos]
  · -- M ≥ 2: the main argument.
    have hM2 : 2 ≤ M := hMbig
    have hMbig : 1 < M := by omega
    -- Reduce to: M ≤ C₀·sum  (then ≤ max C₀ 1·sum).
    have hMreal : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    suffices hfin : (M:ℝ) ≤ C₀ * (N ^ (7/8 : ℝ) + N * δ ^ (1/8 : ℝ)
        + N ^ (7/8 : ℝ) * (δ / Λ) ^ (1/8 : ℝ) + Λ ^ (1/15 : ℝ) * N) by
      refine le_trans hfin ?_
      apply mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
    -- It now suffices to establish the combined inequality and invoke `hC₀`.
    apply hC₀ (M:ℝ) N Λ δ hMreal hN1 hΛ hδ
    -- ===== Popular cube (writeup 125–148) =====
    set lo : ℤ := ⌊N⌋ with hlo
    set Ñ : ℝ := N + 1 with hÑ
    have hÑpos : (0:ℝ) < Ñ := by rw [hÑ]; linarith
    have hÑ16 : (0:ℝ) < 16 * Ñ := by positivity
    have hfloorN : (⌊N⌋ : ℝ) ≤ N := Int.floor_le N
    have hNfloor : N - 1 < (⌊N⌋ : ℝ) := by have := Int.sub_one_lt_floor N; linarith
    -- membership: any subset `A ⊆ S` sits in `(lo, lo+Ñ]`.
    have hmemAux : ∀ (A : Finset ℤ), A ⊆ S → ∀ n ∈ A,
        (lo : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (lo : ℝ) + Ñ := by
      intro A hAS n hn
      have hnS : n ∈ S := hAS hn
      rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hnS
      obtain ⟨⟨h1, h2⟩, _⟩ := hnS
      constructor
      · exact_mod_cast h1
      · have hn2N : (n : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by exact_mod_cast h2
        have : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
        rw [hlo, hÑ]; linarith
    -- budget lower bound abbreviation
    have hbudget0 : (0:ℝ) ≤ N ^ 7 + Λ * N ^ 15 / (M:ℝ) ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ := by
      positivity
    -- `16Ñ ≤ 32 N`.
    have hÑ32 : 16 * Ñ ≤ 32 * N := by rw [hÑ]; linarith
    -- `2^20 ≤ Kfc` and `2^30 ≤ Kfc` (since `Kfc = 2^70·K ≥ 2^70`).
    have hKfcge70 : (2:ℝ) ^ 70 ≤ Kfc := by
      rw [hKfcdef]; calc (2:ℝ) ^ 70 = 2 ^ 70 * 1 := by ring
        _ ≤ 2 ^ 70 * K := by apply mul_le_mul_of_nonneg_left hK1 (by positivity)
    -- the "collapse" target: M² ≤ 16Ñ ⟹ M⁸ ≤ Kfc·budget.
    have collapse1 : (M:ℝ) ^ 2 ≤ 16 * Ñ →
        (M:ℝ) ^ 8 ≤ Kfc * (N ^ 7 + Λ * N ^ 15 / (M:ℝ) ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ) := by
      intro hcol
      have h1 : (M:ℝ) ^ 2 ≤ 32 * N := le_trans hcol hÑ32
      have h2 : (M:ℝ) ^ 8 ≤ (32 * N) ^ 4 := by
        have : ((M:ℝ) ^ 2) ^ 4 ≤ (32 * N) ^ 4 := by
          apply pow_le_pow_left₀ (by positivity) h1
        calc (M:ℝ) ^ 8 = ((M:ℝ) ^ 2) ^ 4 := by ring
          _ ≤ (32 * N) ^ 4 := this
      have h3 : (32 * N) ^ 4 ≤ Kfc * N ^ 7 := by
        have hNle : N ^ 4 ≤ N ^ 7 := by
          apply pow_le_pow_right₀ hN1 (by norm_num)
        have hKge : (2:ℝ) ^ 20 ≤ Kfc :=
          le_trans (by norm_num) hKfcge70
        calc (32 * N) ^ 4 = 2 ^ 20 * N ^ 4 := by norm_num; ring
          _ ≤ Kfc * N ^ 7 := by
              apply mul_le_mul hKge hNle (by positivity) (le_trans (by positivity) hKge)
      have : (M:ℝ) ^ 8 ≤ Kfc * N ^ 7 := le_trans h2 h3
      nlinarith [this, hbudget0, mul_nonneg (le_of_lt (by linarith : (0:ℝ) < Kfc))
        (by positivity : (0:ℝ) ≤ Λ * N ^ 15 / (M:ℝ) ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ)]
    have collapse2 : (M:ℝ) ^ 4 ≤ (16 * Ñ) ^ 3 →
        (M:ℝ) ^ 8 ≤ Kfc * (N ^ 7 + Λ * N ^ 15 / (M:ℝ) ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ) := by
      intro hcol
      have h1 : (M:ℝ) ^ 4 ≤ (32 * N) ^ 3 := by
        refine le_trans hcol ?_
        apply pow_le_pow_left₀ (by positivity) hÑ32
      have h2 : (M:ℝ) ^ 8 ≤ ((32 * N) ^ 3) ^ 2 := by
        calc (M:ℝ) ^ 8 = ((M:ℝ) ^ 4) ^ 2 := by ring
          _ ≤ ((32 * N) ^ 3) ^ 2 := by apply pow_le_pow_left₀ (by positivity) h1
      have h3 : ((32 * N) ^ 3) ^ 2 ≤ Kfc * N ^ 7 := by
        have hNle : N ^ 6 ≤ N ^ 7 := by apply pow_le_pow_right₀ hN1 (by norm_num)
        have hKge : (2:ℝ) ^ 30 ≤ Kfc :=
          le_trans (by norm_num) hKfcge70
        calc ((32 * N) ^ 3) ^ 2 = 2 ^ 30 * N ^ 6 := by norm_num; ring
          _ ≤ Kfc * N ^ 7 := by
              apply mul_le_mul hKge hNle (by positivity) (le_trans (by positivity) hKge)
      have : (M:ℝ) ^ 8 ≤ Kfc * N ^ 7 := le_trans h2 h3
      nlinarith [this, hbudget0, mul_nonneg (le_of_lt (by linarith : (0:ℝ) < Kfc))
        (by positivity : (0:ℝ) ≤ Λ * N ^ 15 / (M:ℝ) ^ 7 + N ^ 8 * δ + N ^ 7 * δ / Λ)]
    -- ===== First popular difference =====
    obtain ⟨h₁, hh₁lo, hh₁hi, hrc₁⟩ := popular_diff Ñ S lo (hmemAux S (subset_refl S))
      (show 2 ≤ S.card from hM2)
    set A₁ : Finset ℤ := S.filter (fun n => n + h₁ ∈ S) with hA₁def
    have hA₁card : (A₁.card : ℝ) = (rcount S h₁ : ℝ) := by rw [hA₁def, rcount]
    have hA₁S : A₁ ⊆ S := Finset.filter_subset _ _
    -- #A₁ ≥ M²/(16Ñ)
    have hA₁lb : (M:ℝ) ^ 2 / (16 * Ñ) ≤ (A₁.card : ℝ) := by
      rw [hA₁card]
      have : (M:ℝ) = (S.card : ℝ) := by rw [hMdef]
      rw [this]; exact hrc₁
    rcases Nat.lt_or_ge A₁.card 2 with hA₁small | hA₁2
    · -- collapse 1
      apply collapse1
      have : (A₁.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : A₁.card ≤ 1)
      have hle : (M:ℝ) ^ 2 / (16 * Ñ) ≤ 1 := le_trans hA₁lb this
      rw [div_le_one hÑ16] at hle; exact hle
    -- ===== Second popular difference =====
    obtain ⟨h₂, hh₂lo, hh₂hi, hrc₂⟩ := popular_diff Ñ A₁ lo (hmemAux A₁ hA₁S) hA₁2
    set A₂ : Finset ℤ := A₁.filter (fun n => n + h₂ ∈ A₁) with hA₂def
    have hA₂card : (A₂.card : ℝ) = (rcount A₁ h₂ : ℝ) := by rw [hA₂def, rcount]
    have hA₂A₁ : A₂ ⊆ A₁ := Finset.filter_subset _ _
    have hA₂S : A₂ ⊆ S := hA₂A₁.trans hA₁S
    have hA₂lb : (A₁.card : ℝ) ^ 2 / (16 * Ñ) ≤ (A₂.card : ℝ) := by
      rw [hA₂card]; exact hrc₂
    rcases Nat.lt_or_ge A₂.card 2 with hA₂small | hA₂2
    · -- collapse 2
      apply collapse2
      have hA₂le1 : (A₂.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : A₂.card ≤ 1)
      -- (#A₁)² ≤ 16Ñ
      have hA₁sq : (A₁.card : ℝ) ^ 2 ≤ 16 * Ñ := by
        have : (A₁.card : ℝ) ^ 2 / (16 * Ñ) ≤ 1 := le_trans hA₂lb hA₂le1
        rwa [div_le_one hÑ16] at this
      -- M²/(16Ñ) ≤ #A₁, both nonneg ⟹ (M²/(16Ñ))² ≤ (#A₁)²
      have hMsqnn : (0:ℝ) ≤ (M:ℝ) ^ 2 / (16 * Ñ) := by positivity
      have hsq : ((M:ℝ) ^ 2 / (16 * Ñ)) ^ 2 ≤ (A₁.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ hMsqnn hA₁lb 2
      have hchain : ((M:ℝ) ^ 2 / (16 * Ñ)) ^ 2 ≤ 16 * Ñ := le_trans hsq hA₁sq
      -- ⟹ M⁴ ≤ (16Ñ)³
      have : (M:ℝ) ^ 4 ≤ (16 * Ñ) ^ 3 := by
        have e : ((M:ℝ) ^ 2 / (16 * Ñ)) ^ 2 = (M:ℝ) ^ 4 / (16 * Ñ) ^ 2 := by
          rw [div_pow]; ring_nf
        rw [e, div_le_iff₀ (by positivity)] at hchain
        calc (M:ℝ) ^ 4 ≤ 16 * Ñ * (16 * Ñ) ^ 2 := hchain
          _ = (16 * Ñ) ^ 3 := by ring
      exact this
    -- ===== Third popular difference =====
    obtain ⟨h₃, hh₃lo, hh₃hi, hrc₃⟩ := popular_diff Ñ A₂ lo (hmemAux A₂ hA₂S) hA₂2
    set A₃ : Finset ℤ := A₂.filter (fun n => n + h₃ ∈ A₂) with hA₃def
    have hA₃card : (A₃.card : ℝ) = (rcount A₂ h₃ : ℝ) := by rw [hA₃def, rcount]
    have hA₃A₂ : A₃ ⊆ A₂ := Finset.filter_subset _ _
    have hA₃S : A₃ ⊆ S := hA₃A₂.trans hA₂S
    have hA₃lb : (A₂.card : ℝ) ^ 2 / (16 * Ñ) ≤ (A₃.card : ℝ) := by
      rw [hA₃card]; exact hrc₃
    -- ===== Lower bound chain: #A₃ ≥ M⁸/(16Ñ)⁷ =====
    have hA₁nn : (0:ℝ) ≤ (A₁.card : ℝ) := by positivity
    have hA₂nn : (0:ℝ) ≤ (A₂.card : ℝ) := by positivity
    have hMsqnn : (0:ℝ) ≤ (M:ℝ) ^ 2 / (16 * Ñ) := by positivity
    have hA₂chain : (M:ℝ) ^ 4 / (16 * Ñ) ^ 3 ≤ (A₂.card : ℝ) := by
      have hsq : ((M:ℝ) ^ 2 / (16 * Ñ)) ^ 2 ≤ (A₁.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ hMsqnn hA₁lb 2
      have hstep : ((M:ℝ) ^ 2 / (16 * Ñ)) ^ 2 / (16 * Ñ) ≤ (A₂.card : ℝ) := by
        refine le_trans ?_ hA₂lb
        gcongr
      have e : ((M:ℝ) ^ 2 / (16 * Ñ)) ^ 2 / (16 * Ñ) = (M:ℝ) ^ 4 / (16 * Ñ) ^ 3 := by
        rw [div_pow]; rw [div_div]; ring_nf
      rwa [e] at hstep
    have hA₃chain : (M:ℝ) ^ 8 / (16 * Ñ) ^ 7 ≤ (A₃.card : ℝ) := by
      have hM4nn : (0:ℝ) ≤ (M:ℝ) ^ 4 / (16 * Ñ) ^ 3 := by positivity
      have hsq : ((M:ℝ) ^ 4 / (16 * Ñ) ^ 3) ^ 2 ≤ (A₂.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ hM4nn hA₂chain 2
      have hstep : ((M:ℝ) ^ 4 / (16 * Ñ) ^ 3) ^ 2 / (16 * Ñ) ≤ (A₃.card : ℝ) := by
        refine le_trans ?_ hA₃lb
        gcongr
      have e : ((M:ℝ) ^ 4 / (16 * Ñ) ^ 3) ^ 2 / (16 * Ñ) = (M:ℝ) ^ 8 / (16 * Ñ) ^ 7 := by
        rw [div_pow]; rw [div_div]; ring_nf
      rwa [e] at hstep
    have hA₃pos : (0:ℝ) < (A₃.card : ℝ) := by
      have : (0:ℝ) < (M:ℝ) ^ 8 / (16 * Ñ) ^ 7 := by positivity
      linarith
    have hA₃ne : A₃.Nonempty := by
      rw [← Finset.card_pos]; exact_mod_cast hA₃pos
    -- membership in S gives distInt bound on f
    have hSdist : ∀ m : ℤ, m ∈ S → distInt (f (m : ℝ)) ≤ δ := by
      intro m hm
      rw [hSdef, Finset.mem_filter] at hm; exact hm.2
    -- corner membership: from `n ∈ A₃`, 8 integer corners lie in `S`.
    have hcorners : ∀ n ∈ A₃,
        n ∈ S ∧ n + h₁ ∈ S ∧ n + h₂ ∈ S ∧ n + h₁ + h₂ ∈ S ∧
        n + h₃ ∈ S ∧ n + h₁ + h₃ ∈ S ∧ n + h₂ + h₃ ∈ S ∧ n + h₁ + h₂ + h₃ ∈ S := by
      intro n hn
      rw [hA₃def, Finset.mem_filter] at hn
      obtain ⟨hnA₂, hn3A₂⟩ := hn
      rw [hA₂def, Finset.mem_filter] at hnA₂ hn3A₂
      obtain ⟨hnA₁, hn2A₁⟩ := hnA₂
      obtain ⟨hn3A₁, hn32A₁⟩ := hn3A₂
      rw [hA₁def, Finset.mem_filter] at hnA₁ hn2A₁ hn3A₁ hn32A₁
      obtain ⟨hnS, hn1S⟩ := hnA₁
      obtain ⟨hn2S, hn21S⟩ := hn2A₁
      obtain ⟨hn3S, hn31S⟩ := hn3A₁
      obtain ⟨hn32S, hn321S⟩ := hn32A₁
      refine ⟨hnS, hn1S, hn2S, ?_, hn3S, ?_, ?_, ?_⟩
      · -- n + h₂ + h₁ ∈ S  vs need n + h₁ + h₂
        have : n + h₂ + h₁ = n + h₁ + h₂ := by ring
        rwa [this] at hn21S
      · have : n + h₃ + h₁ = n + h₁ + h₃ := by ring
        rwa [this] at hn31S
      · have : n + h₃ + h₂ = n + h₂ + h₃ := by ring
        rwa [this] at hn32S
      · have : n + h₃ + h₂ + h₁ = n + h₁ + h₂ + h₃ := by ring
        rwa [this] at hn321S
    -- `h₁ + h₂ + h₃ ≤ N` (top corner of any `n₀ ∈ A₃` stays in S ⊆ (⌊N⌋, ⌊2N⌋]).
    obtain ⟨n₀, hn₀⟩ := hA₃ne
    have hsumle : (h₁ : ℝ) + (h₂ : ℝ) + (h₃ : ℝ) ≤ N := by
      obtain ⟨hn₀S, _, _, _, _, _, _, htop⟩ := hcorners n₀ hn₀
      rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hn₀S htop
      obtain ⟨⟨hlo₀, _⟩, _⟩ := hn₀S
      obtain ⟨⟨_, htop2⟩, _⟩ := htop
      -- ⌊N⌋ + 1 ≤ n₀  and  n₀ + h₁+h₂+h₃ ≤ ⌊2N⌋  (integers)
      have e1 : ⌊N⌋ + 1 ≤ n₀ := hlo₀
      have e1r : (⌊N⌋ : ℝ) + 1 ≤ (n₀ : ℝ) := by exact_mod_cast e1
      have e2 : (n₀ : ℝ) + (h₁:ℝ) + (h₂:ℝ) + (h₃:ℝ) ≤ (⌊2 * N⌋ : ℝ) := by
        have : ((n₀ + h₁ + h₂ + h₃ : ℤ) : ℝ) ≤ ((⌊2 * N⌋ : ℤ) : ℝ) := by exact_mod_cast htop2
        push_cast at this; linarith
      have e3 : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
      linarith [hNfloor]
    have hh1r : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁lo
    have hh2r : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂lo
    have hh3r : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃lo
    -- ===== Calculus: g = Δ f is F-expanding with variation V on [N,2N] =====
    set g : ℝ → ℝ := diff3 (h₁:ℝ) (h₂:ℝ) (h₃:ℝ) f with hgdef
    set P : ℝ := (h₁:ℝ) * (h₂:ℝ) * (h₃:ℝ) with hPdef
    have hPpos : (0:ℝ) < P := by rw [hPdef]; positivity
    have hP1 : (1:ℝ) ≤ P := by
      rw [hPdef]
      have h12 : (1:ℝ) ≤ (h₁:ℝ) * (h₂:ℝ) := by nlinarith [hh1r, hh2r]
      nlinarith [h12, hh3r]
    have hFpos : (0:ℝ) < P * Λ := by positivity
    obtain ⟨hexp, hvar⟩ := expanding_and_variation (N := N) (Λ := Λ) (K := K)
      (h₁ := (h₁:ℝ)) (h₂ := (h₂:ℝ)) (h₃ := (h₃:ℝ)) (f := f)
      hN hΛ hK1 hh1r hh2r hh3r hsumle hf hlb hub
    -- ===== Apply preimage_count to g on [N,2N], tolerance 8δ =====
    have hVnn : (0:ℝ) ≤ K * (P * Λ) * N := by
      have hK0 : (0:ℝ) ≤ K := by linarith
      positivity
    have hpc := preimage_count N (2 * N) (K * (P * Λ) * N) (P * Λ) (8 * δ) g hFpos
      (by positivity) hVnn
      (by
        intro x hx y hy
        have he := hexp x hx y hy
        have heqF : P * Λ * |x - y| = (h₁:ℝ) * (h₂:ℝ) * (h₃:ℝ) * Λ * |x - y| := by
          rw [hPdef]
        rw [heqF]; exact he)
      (by
        intro x hx y hy
        have hv := hvar x hx y hy
        have heqV : K * (P * Λ) * N = K * ((h₁:ℝ) * (h₂:ℝ) * (h₃:ℝ) * Λ) * N := by
          rw [hPdef]
        rw [heqV]; exact hv)
    -- hpc : #((Icc ⌈N⌉ ⌊2N⌋).filter (distInt (g ↑n) ≤ 8δ)) ≤ (V+16δ+1)(16δ/(PΛ)+1)
    -- ===== A₃ ⊆ that filtered set =====
    have hA₃sub : A₃ ⊆ (Finset.Icc ⌈N⌉ ⌊2 * N⌋).filter (fun n => distInt (g (n : ℝ)) ≤ 8 * δ) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      obtain ⟨c000, c100, c010, c110, c001, c101, c011, c111⟩ := hcorners n hn
      have hnS : n ∈ S := hA₃S hn
      rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hnS
      obtain ⟨⟨hlon, hhin⟩, _⟩ := hnS
      refine ⟨⟨?_, hhin⟩, ?_⟩
      · have h1 : ⌈N⌉ ≤ ⌊N⌋ + 1 := Int.ceil_le_floor_add_one N
        omega
      · have d000 := hSdist n c000
        have d100 := hSdist (n + h₁) c100
        have d010 := hSdist (n + h₂) c010
        have d110 := hSdist (n + h₁ + h₂) c110
        have d001 := hSdist (n + h₃) c001
        have d101 := hSdist (n + h₁ + h₃) c101
        have d011 := hSdist (n + h₂ + h₃) c011
        have d111 := hSdist (n + h₁ + h₂ + h₃) c111
        rw [hgdef]
        apply distInt_diff3_le
        · exact d000
        · have e : ((n + h₃ : ℤ) : ℝ) = (n : ℝ) + (h₃ : ℝ) := by push_cast; ring
          rwa [e] at d001
        · have e : ((n + h₂ : ℤ) : ℝ) = (n : ℝ) + (h₂ : ℝ) := by push_cast; ring
          rwa [e] at d010
        · have e : ((n + h₂ + h₃ : ℤ) : ℝ) = (n : ℝ) + (h₂ : ℝ) + (h₃ : ℝ) := by push_cast; ring
          rwa [e] at d011
        · have e : ((n + h₁ : ℤ) : ℝ) = (n : ℝ) + (h₁ : ℝ) := by push_cast; ring
          rwa [e] at d100
        · have e : ((n + h₁ + h₃ : ℤ) : ℝ) = (n : ℝ) + (h₁ : ℝ) + (h₃ : ℝ) := by push_cast; ring
          rwa [e] at d101
        · have e : ((n + h₁ + h₂ : ℤ) : ℝ) = (n : ℝ) + (h₁ : ℝ) + (h₂ : ℝ) := by push_cast; ring
          rwa [e] at d110
        · have e : ((n + h₁ + h₂ + h₃ : ℤ) : ℝ)
              = (n : ℝ) + (h₁ : ℝ) + (h₂ : ℝ) + (h₃ : ℝ) := by push_cast; ring
          rwa [e] at d111
    have hA₃ub : (A₃.card : ℝ)
        ≤ (K * (P * Λ) * N + 2 * (8 * δ) + 1) * (2 * (8 * δ) / (P * Λ) + 1) := by
      refine le_trans ?_ hpc
      exact_mod_cast Finset.card_le_card hA₃sub
    -- ===== Bound P ≤ C_P · Ñ⁷/M⁷ =====
    -- cardinalities: #A₁, #A₂ ≤ M ≤ Ñ.
    have hMleÑ : (M:ℝ) ≤ Ñ := by
      have : S ⊆ Finset.Ioc ⌊N⌋ ⌊2 * N⌋ := Finset.filter_subset _ _
      have hcard : M ≤ (Finset.Ioc ⌊N⌋ ⌊2 * N⌋).card := Finset.card_le_card this
      rw [Int.card_Ioc] at hcard
      have h2N : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
      have : (M:ℝ) ≤ ((⌊2 * N⌋ - ⌊N⌋).toNat : ℝ) := by exact_mod_cast hcard
      have hnn : (0:ℤ) ≤ ⌊2 * N⌋ - ⌊N⌋ := by
        have : ⌊N⌋ ≤ ⌊2 * N⌋ := Int.floor_le_floor (by linarith)
        omega
      have htoNat : ((⌊2 * N⌋ - ⌊N⌋).toNat : ℝ) = (⌊2 * N⌋ : ℝ) - (⌊N⌋ : ℝ) := by
        have : (((⌊2 * N⌋ - ⌊N⌋).toNat : ℤ) : ℝ) = ((⌊2 * N⌋ - ⌊N⌋ : ℤ) : ℝ) := by
          rw [Int.toNat_of_nonneg hnn]
        push_cast at this ⊢; linarith
      have hfin : (M:ℝ) ≤ N + 1 := by linarith [hNfloor]
      linarith [hÑ]
    have hA₁leM : (A₁.card : ℝ) ≤ (M:ℝ) := by
      have := Finset.card_le_card hA₁S; rw [hMdef]; exact_mod_cast this
    have hA₂leM : (A₂.card : ℝ) ≤ (M:ℝ) := by
      have := Finset.card_le_card hA₂S; rw [hMdef]; exact_mod_cast this
    -- positivity of cardinalities (as reals)
    have hA₁posR : (0:ℝ) < (A₁.card : ℝ) := by
      have : 0 < A₁.card := by omega
      exact_mod_cast this
    have hA₂posR : (0:ℝ) < (A₂.card : ℝ) := by
      have : 0 < A₂.card := by omega
      exact_mod_cast this
    have hA₁leÑ : (A₁.card : ℝ) ≤ Ñ := le_trans hA₁leM hMleÑ
    have hA₂leÑ : (A₂.card : ℝ) ≤ Ñ := le_trans hA₂leM hMleÑ
    -- individual h-bounds: hᵢ ≤ 5Ñ/(card)
    have hh₁bd : (h₁:ℝ) ≤ 5 * Ñ / (M:ℝ) := by
      have hSc : (S.card : ℝ) = (M:ℝ) := by rw [hMdef]
      rw [hSc] at hh₁hi
      have h1le : (1:ℝ) ≤ Ñ / (M:ℝ) := by
        rw [le_div_iff₀ hMreal]; linarith [hMleÑ]
      calc (h₁:ℝ) ≤ 4 * Ñ / (M:ℝ) + 1 := hh₁hi
        _ ≤ 4 * Ñ / (M:ℝ) + Ñ / (M:ℝ) := by linarith
        _ = 5 * Ñ / (M:ℝ) := by ring
    have hh₂bd : (h₂:ℝ) ≤ 5 * Ñ / (A₁.card : ℝ) := by
      have h1le : (1:ℝ) ≤ Ñ / (A₁.card : ℝ) := by
        rw [le_div_iff₀ hA₁posR]; linarith [hA₁leÑ]
      calc (h₂:ℝ) ≤ 4 * Ñ / (A₁.card : ℝ) + 1 := hh₂hi
        _ ≤ 4 * Ñ / (A₁.card : ℝ) + Ñ / (A₁.card : ℝ) := by linarith
        _ = 5 * Ñ / (A₁.card : ℝ) := by ring
    have hh₃bd : (h₃:ℝ) ≤ 5 * Ñ / (A₂.card : ℝ) := by
      have h1le : (1:ℝ) ≤ Ñ / (A₂.card : ℝ) := by
        rw [le_div_iff₀ hA₂posR]; linarith [hA₂leÑ]
      calc (h₃:ℝ) ≤ 4 * Ñ / (A₂.card : ℝ) + 1 := hh₃hi
        _ ≤ 4 * Ñ / (A₂.card : ℝ) + Ñ / (A₂.card : ℝ) := by linarith
        _ = 5 * Ñ / (A₂.card : ℝ) := by ring
    -- combine with lower bounds on cards
    have hMsq_pos : (0:ℝ) < (M:ℝ) ^ 2 / (16 * Ñ) := by positivity
    have hM4_pos : (0:ℝ) < (M:ℝ) ^ 4 / (16 * Ñ) ^ 3 := by positivity
    have hh₂bd2 : (h₂:ℝ) ≤ 5 * Ñ / ((M:ℝ) ^ 2 / (16 * Ñ)) := by
      refine le_trans hh₂bd ?_
      apply div_le_div_of_nonneg_left (by positivity) hMsq_pos hA₁lb
    have hh₃bd2 : (h₃:ℝ) ≤ 5 * Ñ / ((M:ℝ) ^ 4 / (16 * Ñ) ^ 3) := by
      refine le_trans hh₃bd ?_
      apply div_le_div_of_nonneg_left (by positivity) hM4_pos hA₂chain
    -- explicit forms
    have hh₂bd3 : (h₂:ℝ) ≤ 80 * Ñ ^ 2 / (M:ℝ) ^ 2 := by
      have e : 5 * Ñ / ((M:ℝ) ^ 2 / (16 * Ñ)) = 80 * Ñ ^ 2 / (M:ℝ) ^ 2 := by
        rw [div_div_eq_mul_div]; field_simp; ring
      rwa [e] at hh₂bd2
    have hh₃bd3 : (h₃:ℝ) ≤ 5 * (16 : ℝ) ^ 3 * Ñ ^ 4 / (M:ℝ) ^ 4 := by
      have e : 5 * Ñ / ((M:ℝ) ^ 4 / (16 * Ñ) ^ 3) = 5 * (16 : ℝ) ^ 3 * Ñ ^ 4 / (M:ℝ) ^ 4 := by
        rw [div_div_eq_mul_div]; field_simp
      rwa [e] at hh₃bd2
    -- multiply: P ≤ C_P · Ñ⁷/M⁷
    have hh₁nn : (0:ℝ) ≤ (h₁:ℝ) := by positivity
    have hh₂nn : (0:ℝ) ≤ (h₂:ℝ) := by positivity
    have hh₃nn : (0:ℝ) ≤ (h₃:ℝ) := by positivity
    have hPbd : P ≤ 8192000 * Ñ ^ 7 / (M:ℝ) ^ 7 := by
      rw [hPdef]
      have hb1 : (0:ℝ) ≤ 5 * Ñ / (M:ℝ) := by positivity
      have hb2 : (0:ℝ) ≤ 80 * Ñ ^ 2 / (M:ℝ) ^ 2 := by positivity
      have hp12 : (h₁:ℝ) * (h₂:ℝ) ≤ (5 * Ñ / (M:ℝ)) * (80 * Ñ ^ 2 / (M:ℝ) ^ 2) :=
        mul_le_mul hh₁bd hh₂bd3 hh₂nn hb1
      have hp12nn : (0:ℝ) ≤ (5 * Ñ / (M:ℝ)) * (80 * Ñ ^ 2 / (M:ℝ) ^ 2) := by positivity
      have hp123 : (h₁:ℝ) * (h₂:ℝ) * (h₃:ℝ)
          ≤ (5 * Ñ / (M:ℝ)) * (80 * Ñ ^ 2 / (M:ℝ) ^ 2) * (5 * (16:ℝ) ^ 3 * Ñ ^ 4 / (M:ℝ) ^ 4) :=
        mul_le_mul hp12 hh₃bd3 hh₃nn hp12nn
      refine le_trans hp123 (le_of_eq ?_)
      field_simp
      ring
    -- ===== Final combine =====
    have hÑ7pos : (0:ℝ) < (16 * Ñ) ^ 7 := by positivity
    have hM8le : (M:ℝ) ^ 8 ≤ (16 * Ñ) ^ 7 * (A₃.card : ℝ) := by
      rw [div_le_iff₀ hÑ7pos] at hA₃chain; linarith [hA₃chain]
    have hM8ub : (M:ℝ) ^ 8
        ≤ (16 * Ñ) ^ 7 * ((K * (P * Λ) * N + 16 * δ + 1) * (16 * δ / (P * Λ) + 1)) := by
      refine le_trans hM8le ?_
      have h16 : (2 * (8 * δ)) = 16 * δ := by ring
      rw [show (K * (P * Λ) * N + 2 * (8 * δ) + 1) * (2 * (8 * δ) / (P * Λ) + 1)
        = (K * (P * Λ) * N + 16 * δ + 1) * (16 * δ / (P * Λ) + 1) from by rw [h16]] at hA₃ub
      apply mul_le_mul_of_nonneg_left hA₃ub (le_of_lt hÑ7pos)
    have hÑ2N : Ñ ≤ 2 * N := by rw [hÑ]; linarith
    -- `hPbd : P ≤ 8192000·Ñ⁷/M⁷` is in terms of Ñ; convert to abstract form.
    have := final_combine (M := (M:ℝ)) (N := N) (Λ := Λ) (δ := δ) (P := P) (Ñ := Ñ) (K := K)
      hMreal hN1 hΛ hδ (by linarith) hK1 hÑpos hÑ2N hP1 hPbd hM8ub
    -- `final_combine` gives the budget multiplier `2^70·K = Kfc`.
    rw [hKfcdef]; exact this

end Squarefree.Counting
