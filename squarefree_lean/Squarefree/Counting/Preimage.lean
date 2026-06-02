import Squarefree.Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

/-!
# §2/§4 preimage counting (Lemma 4.1 / 2.3)

Proof of the preimage-count lemma from `../explicit_writeup.md`
(lines 196–207, 413–421). See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree.Counting

/-- Distance from a real to the nearest integer, `‖t‖`. -/
noncomputable def distInt (t : ℝ) : ℝ := |t - round t|

/-- A finite set of integers whose elements pairwise differ by at most a real `D ≥ 0` has
cardinality at most `D + 1`. -/
private theorem card_le_of_pairwise_dist (S : Finset ℤ) (D : ℝ) (hD : 0 ≤ D)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, |(x : ℝ) - (y : ℝ)| ≤ D) :
    (S.card : ℝ) ≤ D + 1 := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]; linarith
  · set m : ℤ := S.min' hSne with hm
    have hsub : S ⊆ Finset.Icc m (m + ⌊D⌋) := by
      intro n hnS
      have hmS : m ∈ S := Finset.min'_mem S hSne
      have hmle : m ≤ n := Finset.min'_le S n hnS
      have hd : |(n : ℝ) - (m : ℝ)| ≤ D := hpair n hnS m hmS
      rw [Finset.mem_Icc]
      refine ⟨hmle, ?_⟩
      have hnm : ((n - m : ℤ) : ℝ) ≤ D := by
        have := (abs_le.mp hd).2; push_cast; linarith
      have : (n - m : ℤ) ≤ ⌊D⌋ := Int.le_floor.mpr hnm
      linarith
    have hcard : S.card ≤ (Finset.Icc m (m + ⌊D⌋)).card := Finset.card_le_card hsub
    have hfl : (0 : ℤ) ≤ ⌊D⌋ := Int.le_floor.mpr (by push_cast; linarith)
    have hIcc : ((Finset.Icc m (m + ⌊D⌋)).card : ℝ) ≤ D + 1 := by
      have hcardeq : (Finset.Icc m (m + ⌊D⌋)).card = (⌊D⌋ + 1).toNat := by
        rw [Int.card_Icc]; congr 1; ring
      have hreal : (((⌊D⌋ + 1).toNat : ℕ) : ℝ) = (⌊D⌋ : ℝ) + 1 := by
        have : ((⌊D⌋ + 1).toNat : ℤ) = ⌊D⌋ + 1 := Int.toNat_of_nonneg (by linarith)
        have := congrArg (fun z : ℤ => (z : ℝ)) this
        push_cast at this ⊢
        linarith [this]
      rw [hcardeq, hreal]
      have := Int.floor_le D
      linarith
    calc (S.card : ℝ) ≤ ((Finset.Icc m (m + ⌊D⌋)).card : ℝ) := by exact_mod_cast hcard
      _ ≤ D + 1 := hIcc

/-- **Lemma 4.1 / 2.3** (writeup 196–207, 413–421): an `F`-expanding map of total variation
`≤ V` is within `δ` of an integer at few integer points.  The explicit, fully faithful
constant is `(V + 2δ + 1)(2δ/F + 1)` (for `0 ≤ δ ≤ 1` this is `≤ (V+2)(2δ/F+1)` from the md;
we keep the honest explicit form which needs no upper bound on `δ`). -/
theorem preimage_count (a b V F δ : ℝ) (φ : ℝ → ℝ) (hF : 0 < F) (hδ : 0 ≤ δ) (hV : 0 ≤ V)
    (hexp : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, F * |x - y| ≤ |φ x - φ y|)
    (hvar : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |φ x - φ y| ≤ V) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (V + 2 * δ + 1) * (2 * δ / F + 1) := by
  classical
  set Q : Finset ℤ := (Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)
    with hQ
  -- The rounding map `n ↦ round (φ n)`.
  set k : ℤ → ℤ := fun n => round (φ (n : ℝ)) with hk
  -- Two useful nonnegativity facts about the constants.
  have h2dF : (0 : ℝ) ≤ 2 * δ / F := by positivity
  have hVar2 : (0 : ℝ) ≤ V + 2 * δ := by linarith
  -- Membership facts: every `n ∈ Q` lies in `[a,b]` (as a real) and is within `δ` of `k n`.
  have hmemIcc : ∀ n ∈ Q, (n : ℝ) ∈ Set.Icc a b := by
    intro n hn
    rw [hQ, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, _⟩ := hn
    exact ⟨Int.ceil_le.mp h1, Int.le_floor.mp h2⟩
  have hclose : ∀ n ∈ Q, |φ (n : ℝ) - (k n : ℝ)| ≤ δ := by
    intro n hn
    rw [hQ, Finset.mem_filter] at hn
    simpa [distInt, hk] using hn.2
  -- Step 2: fiber bound.  Two points in the same fiber are within `2δ/F` of each other.
  have hfiberdist : ∀ n ∈ Q, ∀ n' ∈ Q, k n = k n' → |(n : ℝ) - (n' : ℝ)| ≤ 2 * δ / F := by
    intro n hn n' hn' hkk
    have hφ : |φ (n : ℝ) - φ (n' : ℝ)| ≤ 2 * δ := by
      have e1 := hclose n hn
      have e2 := hclose n' hn'
      have heq : φ (n : ℝ) - φ (n' : ℝ)
          = (φ (n : ℝ) - (k n : ℝ)) - (φ (n' : ℝ) - (k n' : ℝ)) := by
        rw [hkk]; ring
      calc |φ (n : ℝ) - φ (n' : ℝ)|
          = |(φ (n : ℝ) - (k n : ℝ)) - (φ (n' : ℝ) - (k n' : ℝ))| := by rw [heq]
        _ ≤ |φ (n : ℝ) - (k n : ℝ)| + |φ (n' : ℝ) - (k n' : ℝ)| := abs_sub _ _
        _ ≤ δ + δ := add_le_add e1 e2
        _ = 2 * δ := by ring
    have hF' : F * |(n : ℝ) - (n' : ℝ)| ≤ 2 * δ :=
      le_trans (hexp _ (hmemIcc n hn) _ (hmemIcc n' hn')) hφ
    rw [le_div_iff₀ hF, mul_comm]
    linarith [hF']
  -- Each fiber has cardinality `≤ 2δ/F + 1`, via the pairwise-distance helper.
  set nFib : ℕ := (⌊2 * δ / F⌋ + 1).toNat with hnFib
  have hnFibcast : (nFib : ℝ) ≤ 2 * δ / F + 1 := by
    have hfl : (0 : ℤ) ≤ ⌊2 * δ / F⌋ := Int.le_floor.mpr (by push_cast; linarith)
    have hreal : ((nFib : ℕ) : ℝ) = (⌊2 * δ / F⌋ : ℝ) + 1 := by
      have h1 : ((nFib : ℤ)) = ⌊2 * δ / F⌋ + 1 := by
        rw [hnFib]; exact Int.toNat_of_nonneg (by linarith)
      have := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at this ⊢
      linarith [this]
    rw [hreal]
    have := Int.floor_le (2 * δ / F)
    linarith
  have hfibercard : ∀ v ∈ Q.image k, (Q.filter (fun n => k n = v)).card ≤ nFib := by
    intro v _
    set S : Finset ℤ := Q.filter (fun n => k n = v) with hS
    have hpair : ∀ x ∈ S, ∀ y ∈ S, |(x : ℝ) - (y : ℝ)| ≤ 2 * δ / F := by
      intro x hx y hy
      have hxQ : x ∈ Q := (Finset.mem_filter.mp hx).1
      have hxk : k x = v := (Finset.mem_filter.mp hx).2
      have hyQ : y ∈ Q := (Finset.mem_filter.mp hy).1
      have hyk : k y = v := (Finset.mem_filter.mp hy).2
      exact hfiberdist x hxQ y hyQ (by rw [hxk, hyk])
    -- `S ⊆ Finset.Icc m (m + ⌊2δ/F⌋)`, card `≤ ⌊2δ/F⌋ + 1 = nFib`.
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · simp [hSe]
    · set m : ℤ := S.min' hSne with hm
      have hSsub : S ⊆ Finset.Icc m (m + ⌊2 * δ / F⌋) := by
        intro n hnS
        have hmle : m ≤ n := Finset.min'_le S n hnS
        have hdist : |(n : ℝ) - (m : ℝ)| ≤ 2 * δ / F :=
          hpair n hnS m (Finset.min'_mem S hSne)
        rw [Finset.mem_Icc]
        refine ⟨hmle, ?_⟩
        have hnm : ((n - m : ℤ) : ℝ) ≤ 2 * δ / F := by
          have := (abs_le.mp hdist).2; push_cast; linarith
        have : (n - m : ℤ) ≤ ⌊2 * δ / F⌋ := Int.le_floor.mpr hnm
        linarith
      calc S.card ≤ (Finset.Icc m (m + ⌊2 * δ / F⌋)).card := Finset.card_le_card hSsub
        _ = nFib := by
            rw [Int.card_Icc, hnFib]; congr 1; omega
  -- Step 1 application: `#Q ≤ nFib * #(image)`.
  have hcardmul : Q.card ≤ nFib * (Q.image k).card :=
    Finset.card_le_mul_card_image_of_maps_to
      (fun a ha => Finset.mem_image_of_mem k ha) nFib hfibercard
  -- Step 3: the image lies in an interval of length `≤ V + 2δ`, so `#(image) ≤ V + 2δ + 1`.
  have himgcard : ((Q.image k).card : ℝ) ≤ V + 2 * δ + 1 := by
    apply card_le_of_pairwise_dist _ _ hVar2
    intro u hu w hw
    rw [Finset.mem_image] at hu hw
    obtain ⟨n, hnQ, rfl⟩ := hu
    obtain ⟨n', hn'Q, rfl⟩ := hw
    -- `|k n - k n'| ≤ |φ n - k n| + |φ n - φ n'| + |φ n' - k n'| ≤ δ + V + δ`.
    have hφV : |φ (n : ℝ) - φ (n' : ℝ)| ≤ V := hvar _ (hmemIcc n hnQ) _ (hmemIcc n' hn'Q)
    have e1 := hclose n hnQ
    have e2 := hclose n' hn'Q
    have heq : ((k n : ℝ) - (k n' : ℝ))
        = (-(φ (n : ℝ) - (k n : ℝ))) + (φ (n : ℝ) - φ (n' : ℝ)) + (φ (n' : ℝ) - (k n' : ℝ)) := by
      ring
    calc |(k n : ℝ) - (k n' : ℝ)|
        = |(-(φ (n : ℝ) - (k n : ℝ))) + (φ (n : ℝ) - φ (n' : ℝ))
            + (φ (n' : ℝ) - (k n' : ℝ))| := by rw [heq]
      _ ≤ |(-(φ (n : ℝ) - (k n : ℝ))) + (φ (n : ℝ) - φ (n' : ℝ))|
            + |φ (n' : ℝ) - (k n' : ℝ)| := abs_add_le _ _
      _ ≤ (|(-(φ (n : ℝ) - (k n : ℝ)))| + |φ (n : ℝ) - φ (n' : ℝ)|)
            + |φ (n' : ℝ) - (k n' : ℝ)| := by gcongr; exact abs_add_le _ _
      _ ≤ (δ + V) + δ := by rw [abs_neg]; gcongr
      _ = V + 2 * δ := by ring
  -- Combine: `#Q ≤ nFib * #image ≤ (2δ/F+1)(V+2δ+1)`.
  have hcast : (Q.card : ℝ) ≤ (nFib : ℝ) * ((Q.image k).card : ℝ) := by
    calc (Q.card : ℝ) ≤ ((nFib * (Q.image k).card : ℕ) : ℝ) := by exact_mod_cast hcardmul
      _ = (nFib : ℝ) * ((Q.image k).card : ℝ) := by push_cast; ring
  have himgnn : (0 : ℝ) ≤ ((Q.image k).card : ℝ) := by positivity
  show (Q.card : ℝ) ≤ (V + 2 * δ + 1) * (2 * δ / F + 1)
  calc (Q.card : ℝ)
      ≤ (nFib : ℝ) * ((Q.image k).card : ℝ) := hcast
    _ ≤ (2 * δ / F + 1) * (V + 2 * δ + 1) := by
        apply mul_le_mul hnFibcast himgcard himgnn
        linarith
    _ = (V + 2 * δ + 1) * (2 * δ / F + 1) := by ring

end Squarefree.Counting
