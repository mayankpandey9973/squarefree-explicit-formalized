import Mathlib

/-!
# §4.3 general combinatorial spacing → cardinality helper

If every 5-element subset of `S ⊆ [lo,hi] ∩ ℤ` spans `≥ d > 0`, then bucketing by
`⌊(n−lo)/d⌋` is at-most-4-to-one, so `#S ≤ 4·((hi−lo)/d + 1)`.  This is the clean
combinatorial core behind the §4.3 residual bound (`../explicit_writeup.md`
lines 576–578).  Kept separate from `NearCurveProof` so each file stays small.
-/

open Classical Finset

namespace Squarefree.Geometry

/-- The bucket index of `n` relative to origin `lo`, scale `d`. -/
noncomputable def bucket (lo d : ℝ) (n : ℤ) : ℤ := ⌊((n : ℝ) - lo) / d⌋

/-- Two points in the same bucket are within `d` of each other. -/
theorem bucket_close {lo d : ℝ} (hd : 0 < d) {n m : ℤ}
    (h : bucket lo d n = bucket lo d m) : |(n : ℝ) - (m : ℝ)| < d := by
  have hn := Int.lt_floor_add_one (((n : ℝ) - lo) / d)
  have hm := Int.lt_floor_add_one (((m : ℝ) - lo) / d)
  have hnf := Int.floor_le (((n : ℝ) - lo) / d)
  have hmf := Int.floor_le (((m : ℝ) - lo) / d)
  simp only [bucket] at h
  rw [← h] at hm hmf
  -- both `(n-lo)/d` and `(m-lo)/d` lie in `[k, k+1)` where `k = ⌊(n-lo)/d⌋`.
  set k : ℤ := ⌊((n : ℝ) - lo) / d⌋
  have hub : ((n : ℝ) - lo) < ((k : ℝ) + 1) * d := by
    rw [← div_lt_iff₀ hd]; exact hn
  have hlb : (k : ℝ) * d ≤ ((n : ℝ) - lo) := by
    rw [← le_div_iff₀ hd]; exact hnf
  have hub' : ((m : ℝ) - lo) < ((k : ℝ) + 1) * d := by
    rw [← div_lt_iff₀ hd]; exact hm
  have hlb' : (k : ℝ) * d ≤ ((m : ℝ) - lo) := by
    rw [← le_div_iff₀ hd]; exact hmf
  rw [abs_sub_lt_iff]
  constructor <;> nlinarith [hub, hlb, hub', hlb']

/-- **Spacing → card.**  If every 5-subset of `S` spans `≥ d` and `S ⊆ [lo,hi]`,
then `#S ≤ 4·((hi−lo)/d + 1)`. -/
theorem card_le_of_five_span {S : Finset ℤ} {lo hi d : ℝ}
    (hd : 0 < d) (hlohi : lo ≤ hi)
    (hmem : ∀ n ∈ S, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi)
    (hspan : ∀ t ⊆ S, t.card = 5 → ∃ x ∈ t, ∃ y ∈ t, d ≤ (y : ℝ) - (x : ℝ)) :
    (S.card : ℝ) ≤ 4 * ((hi - lo) / d + 1) := by
  classical
  -- Bucket map into `Icc 0 ⌊(hi-lo)/d⌋`.
  have hmaps : ∀ n ∈ S, bucket lo d n ∈ Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋ := by
    intro n hn
    obtain ⟨hl, hh⟩ := hmem n hn
    rw [Finset.mem_Icc]
    constructor
    · rw [bucket, Int.le_floor]; push_cast
      exact div_nonneg (by linarith) hd.le
    · apply Int.floor_le_floor
      apply div_le_div_of_nonneg_right (by linarith) hd.le
  -- each fiber has ≤ 4 elements.
  have hfiber : ∀ b ∈ Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋,
      (S.filter (fun n => bucket lo d n = b)).card ≤ 4 := by
    intro b _
    by_contra hcon
    push Not at hcon
    -- 5 ≤ fiber card ⟹ a 5-subset all in bucket `b`, spanning < d, contradicting hspan.
    obtain ⟨t, htsub, htcard⟩ :=
      Finset.exists_subset_card_eq (n := 5) (s := S.filter (fun n => bucket lo d n = b))
        (by omega)
    have htS : t ⊆ S := htsub.trans (Finset.filter_subset _ _)
    have htb : ∀ n ∈ t, bucket lo d n = b := fun n hn => (Finset.mem_filter.mp (htsub hn)).2
    obtain ⟨x, hx, y, hy, hxy⟩ := hspan t htS htcard
    have : |(x : ℝ) - (y : ℝ)| < d := bucket_close hd (by rw [htb x hx, htb y hy])
    have hle : (y : ℝ) - (x : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  -- card_le_mul_card_image_of_maps_to.
  have hcard : S.card ≤ 4 * (Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 4 hfiber
  -- bound #(Icc 0 ⌊(hi-lo)/d⌋) ≤ (hi-lo)/d + 1.
  have hICCcard : ((Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card : ℝ) ≤ (hi - lo) / d + 1 := by
    by_cases hlast : 0 ≤ ⌊(hi - lo) / d⌋
    · have hcard_eq : ((Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card : ℤ)
          = ⌊(hi - lo) / d⌋ + 1 - 0 := Int.card_Icc_of_le 0 _ (by omega)
      have hcard_eqR : ((Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card : ℝ)
          = (⌊(hi - lo) / d⌋ : ℝ) + 1 := by
        have : (((Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card : ℤ) : ℝ)
            = ((⌊(hi - lo) / d⌋ + 1 - 0 : ℤ) : ℝ) := by exact_mod_cast hcard_eq
        push_cast at this; linarith
      rw [hcard_eqR]
      have := Int.floor_le ((hi - lo) / d)
      linarith
    · push Not at hlast
      have : Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋ = ∅ := by
        rw [Finset.Icc_eq_empty]; omega
      rw [this]
      simp only [Finset.card_empty, Nat.cast_zero]
      have h0 : (0 : ℝ) ≤ (hi - lo) / d := div_nonneg (by linarith) hd.le
      linarith
  calc (S.card : ℝ) ≤ (4 * (Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card : ℕ) := by
        exact_mod_cast hcard
    _ = 4 * ((Finset.Icc (0 : ℤ) ⌊(hi - lo) / d⌋).card : ℝ) := by push_cast; ring
    _ ≤ 4 * ((hi - lo) / d + 1) := by linarith [hICCcard]

/-- Extract five strictly increasing elements from a 5-element subset. -/
theorem exists_five_sorted {t : Finset ℤ} (htcard : t.card = 5) :
    ∃ n₀ n₁ n₂ n₃ n₄ : ℤ, n₀ ∈ t ∧ n₁ ∈ t ∧ n₂ ∈ t ∧ n₃ ∈ t ∧ n₄ ∈ t ∧
      n₀ < n₁ ∧ n₁ < n₂ ∧ n₂ < n₃ ∧ n₃ < n₄ := by
  classical
  let e := t.orderEmbOfFin htcard
  have hmem : ∀ i : Fin 5, e i ∈ t := fun i => t.orderEmbOfFin_mem htcard i
  have hmono : StrictMono e := e.strictMono
  exact ⟨e 0, e 1, e 2, e 3, e 4,
    hmem 0, hmem 1, hmem 2, hmem 3, hmem 4,
    hmono (by decide), hmono (by decide), hmono (by decide), hmono (by decide)⟩

end Squarefree.Geometry
