import Squarefree.Mobius
import Squarefree.DCard
import Squarefree.DyadicAssembly
import Mathlib.Data.Finset.Functor

/-!
# §1 analytic assembly — squarefree count in a short interval

Mechanical assembly of `squarefree_count_short_interval`: starting from the Möbius reduction
`interval_sqf_eq` (`Squarefree.Mob`), split the `d`-sum at `D₁ ≈ √H`.

* SMALL `d ≤ D₁`: each inner count `N_d = #{n∈[a,b]:d²∣n}` is within `O(1)` of `H/d²`, so
  `∑_{d≤D₁} μ(d) N_d = H·∑_{d≤D₁} μ(d)/d² + O(D₁)`, and `∑_{d≤D₁} μ(d)/d²` is `6/π²` up to a tail
  `O(1/D₁)` (via `sum_Ioc_inv_sq_le_sub` and `tsum_moebius_div_sq`).
* LARGE `d > D₁`: `d² > H ⇒ N_d ≤ 1`, so the contribution is bounded by a dyadic cover of
  `(D₁, √b]` into `O(log X)` blocks, each `≤ dCard X H D_j ≤ C_k·H/X^{u_k}` (`key_dyadic_estimate`)
  or trivially `≤ 2 D_j + 1`.

The single public result is `squarefree_count_short_interval` in `Squarefree.Main`; this module
only exposes private helpers used there.
-/

open Classical Finset
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Squarefree.Mob

/-! ## Nat-division vs real-division bounds -/

/-- `(m / n : ℕ)` casts within `[m/n − 1, m/n]` (real division), for `0 < n`. -/
private lemma cast_div_bounds (m n : ℕ) (hn : 0 < n) :
    (m : ℝ) / n - 1 < ((m / n : ℕ) : ℝ) ∧ ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / n := by
  refine ⟨?_, Nat.cast_div_le⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hnR]
  have hdm : m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
  have hmod : m % n < n := Nat.mod_lt _ hn
  have : (m : ℝ) = n * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by
    rw [show ((m % n : ℕ) : ℝ) = (m : ℝ) - n * ((m / n : ℕ) : ℝ) from ?_]; · ring
    have := congrArg (fun k : ℕ => (k : ℝ)) hdm
    push_cast at this; linarith
  rw [this]
  have hmodR : ((m % n : ℕ) : ℝ) < n := by exact_mod_cast hmod
  nlinarith [hmodR]

/-- Per-`d` count error: for `1 ≤ a`, `1 ≤ q`, the count of multiples of `q` in `[a,b]` is within
`O(1)` of `len/q` where `len = b − a + 1 ≥ 0` is the real interval length. -/
private lemma count_close (a b q : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hq : 1 ≤ q) :
    |((b / q - (a - 1) / q : ℕ) : ℝ) - ((b : ℝ) - (a : ℝ) + 1) / q| ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hb1, hb2⟩ := cast_div_bounds b q (by omega)
  obtain ⟨ha1, ha2⟩ := cast_div_bounds (a - 1) q (by omega)
  -- `((a-1):ℕ : ℝ) = (a:ℝ) - 1` since `a ≥ 1`
  have hca : (((a - 1 : ℕ) : ℝ)) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha]; push_cast; ring
  rw [hca] at ha1 ha2
  -- Nat subtraction `b/q - (a-1)/q`: it is the genuine difference since `(a-1)/q ≤ b/q`.
  have hdivle : (a - 1) / q ≤ b / q := Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hdivle]
  have e1 : ((b : ℝ) - (a : ℝ) + 1) / q = (b : ℝ) / q - ((a : ℝ) - 1) / q := by
    field_simp; ring
  rw [e1, abs_le]
  constructor <;> linarith

/-! ## Möbius partial sum vs `6/π²` -/

private lemma abs_moebius_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num

/-- `∑' 1/d²` over ℕ (reals) is summable. -/
private lemma summable_inv_sq : Summable (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

/-- `μ(d)/d²` is summable over ℕ (reals). -/
private lemma summable_moebius_div_sq :
    Summable (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) := by
  apply Summable.of_norm_bounded summable_inv_sq
  intro d
  rw [Real.norm_eq_abs, abs_div]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [hd]
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [abs_of_pos (by positivity : (0:ℝ) < (d : ℝ) ^ 2)]
    exact div_le_div_of_nonneg_right (abs_moebius_le_one d) (by positivity)

/-- Tail bound for `∑_{d > N} 1/d²`: for `N ≥ 1`, `∑'_{i} 1/(i+N+1)² ≤ 1/N`. -/
private lemma tail_inv_sq_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' i : ℕ, (1 : ℝ) / ((i + (N + 1) : ℕ) : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro n
  -- ∑_{i<n} 1/(i+N+1)² = ∑_{j ∈ Ioc N (N+n)} 1/j²  ≤ 1/N − 1/(N+n) ≤ 1/N
  have hicoioc : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioc N (N + n) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  have hre : (∑ i ∈ Finset.range n, (1 : ℝ) / ((i + (N + 1) : ℕ) : ℝ) ^ 2)
      = ∑ j ∈ Finset.Ioc N (N + n), ((j : ℝ) ^ 2)⁻¹ := by
    rw [← hicoioc, Finset.sum_Ico_eq_sum_range
      (fun k => ((k : ℝ) ^ 2)⁻¹) (N + 1) (N + 1 + n)]
    rw [show (N + 1 + n) - (N + 1) = n by omega]
    apply Finset.sum_congr rfl
    intro i _; rw [one_div]; congr 2; push_cast; ring
  rw [hre]
  have hbnd : (∑ j ∈ Finset.Ioc N (N + n), ((j : ℝ) ^ 2)⁻¹) ≤ (N : ℝ)⁻¹ - ((N + n : ℕ) : ℝ)⁻¹ :=
    sum_Ioc_inv_sq_le_sub (by omega) (by omega)
  rw [one_div]
  have hpos : (0 : ℝ) ≤ ((N + n : ℕ) : ℝ)⁻¹ := by positivity
  linarith

/-- Partial Möbius sum is within `1/N` of `6/π²`: for `N ≥ 1`,
`|∑_{d=1}^{N} μ(d)/d² − 6/π²| ≤ 1/N`. -/
private lemma moebius_partial_close (N : ℕ) (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤ 1 / (N : ℝ) := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2 with hfdef
  have hsum : Summable f := summable_moebius_div_sq
  -- split at k = N+1: ∑_{i<N+1} f i + ∑'_i f(i+N+1) = 6/π²
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  rw [tsum_moebius_div_sq] at hsplit
  -- ∑_{i ∈ range (N+1)} f i = ∑_{d ∈ Icc 1 N} f d (since f 0 = 0)
  have hrange : (∑ i ∈ Finset.range (N + 1), f i) = ∑ d ∈ Finset.Icc 1 N, f d := by
    rw [Finset.sum_range_succ' f N]
    have hf0 : f 0 = 0 := by simp [hfdef]
    rw [hf0, add_zero]
    have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range f 1 (N + 1)]
    rw [show (N + 1) - 1 = N by omega]
    apply Finset.sum_congr rfl
    intro k _; congr 1; omega
  rw [hrange] at hsplit
  -- so 6/π² − ∑_{Icc} f = ∑'_i f(i+N+1)
  have heq : (∑ d ∈ Finset.Icc 1 N, f d) - 6 / Real.pi ^ 2 = - (∑' i : ℕ, f (i + (N + 1))) := by
    linarith [hsplit]
  rw [heq, abs_neg]
  -- bound the tail tsum in absolute value
  have htailsum : Summable (fun i : ℕ => f (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hsum
  calc |∑' i : ℕ, f (i + (N + 1))|
      ≤ ∑' i : ℕ, |f (i + (N + 1))| := by
        rw [← Real.norm_eq_abs]
        apply norm_tsum_le_tsum_norm
        simpa [Real.norm_eq_abs] using htailsum.abs
    _ ≤ ∑' i : ℕ, (1 : ℝ) / ((i + (N + 1) : ℕ) : ℝ) ^ 2 := by
        apply Summable.tsum_le_tsum ?_ (htailsum.abs)
          ((summable_nat_add_iff (N + 1)).mpr summable_inv_sq)
        intro i
        rw [hfdef]; simp only
        rw [abs_div]
        rcases Nat.eq_zero_or_pos (i + (N + 1)) with hz | hz
        · omega
        · rw [abs_of_pos (by positivity : (0:ℝ) < ((i + (N + 1) : ℕ) : ℝ) ^ 2)]
          exact div_le_div_of_nonneg_right (abs_moebius_le_one _) (by positivity)
    _ ≤ 1 / (N : ℝ) := tail_inv_sq_le N hN

/-! ## Large-`d` block bound via `dCard` -/

/-- If the interval `[a,b]` is shorter than `q`, it contains at most one multiple of `q`. -/
private lemma count_le_one (a b q : ℕ) (hq : b - a < q) :
    (#{n ∈ Finset.Icc a b | q ∣ n}) ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
  obtain ⟨⟨hxa, hxb⟩, hdx⟩ := hx
  obtain ⟨⟨hya, hyb⟩, hdy⟩ := hy
  by_contra hne
  rcases Nat.lt_or_ge x y with hlt | hge
  · have hge2 : q ≤ y - x := Nat.le_of_dvd (by omega) (Nat.dvd_sub hdy hdx)
    omega
  · have hge2 : q ≤ x - y := Nat.le_of_dvd (by omega) (Nat.dvd_sub hdx hdy)
    omega

/-- A nonempty `[a,b]` containing a multiple of `q` yields an integer multiple of `q` in `[X, X+H]`,
provided `(a:ℝ) ≥ X` and `(b:ℝ) ≤ X+H`. -/
private lemma exists_mult_of_count_pos {a b q : ℕ} {X H : ℝ}
    (haX : X ≤ (a : ℝ)) (hbX : (b : ℝ) ≤ X + H)
    (hpos : 1 ≤ (#{n ∈ Finset.Icc a b | q ∣ n})) :
    ∃ m : ℤ, X ≤ (m : ℝ) * (q : ℝ) ∧ (m : ℝ) * (q : ℝ) ≤ X + H := by
  rw [Finset.one_le_card] at hpos
  obtain ⟨n, hn⟩ := hpos
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hna, hnb⟩, k, hk⟩ := hn
  refine ⟨(k : ℤ), ?_, ?_⟩
  · have haR : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hna
    have hkc : ((k : ℤ) : ℝ) * (q : ℝ) = (n : ℝ) := by
      rw [hk]; push_cast; ring
    rw [hkc]; linarith
  · have hbR : (n : ℝ) ≤ (b : ℝ) := by exact_mod_cast hnb
    have hkc : ((k : ℤ) : ℝ) * (q : ℝ) = (n : ℝ) := by
      rw [hk]; push_cast; ring
    rw [hkc]; linarith

/-- `dCard` rewritten as a `Finset ℤ` filter cardinality (its underlying definition coerces the
integer `Icc` into `Finset ℝ`). -/
private lemma dCard_eq_intCard (X H D : ℝ) :
    (Squarefree.dCard X H D : ℝ)
      = (((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
          (fun d : ℤ => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)).card
          : ℝ) := by
  rw [Squarefree.dCard]
  norm_cast
  have hbind : (do let a ← Finset.Icc ⌈D⌉ ⌊2 * D⌋; pure (↑a : ℝ))
      = (Finset.Icc ⌈D⌉ ⌊2 * D⌋).image (Int.cast : ℤ → ℝ) := by
    rw [bind_pure_comp, Finset.fmap_def]
  rw [hbind, Finset.filter_image,
    Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h)]
  congr 1
  apply Finset.filter_congr
  intro d _
  constructor <;> rintro ⟨m, h1, h2⟩ <;>
    exact ⟨m, by push_cast at h1 ⊢; linarith, by push_cast at h2 ⊢; linarith⟩

/-- Trivial linear bound: `dCard X H D ≤ D + 1` for `D ≥ 0`. -/
private lemma dCard_le_lin (X H D : ℝ) (hD : 0 ≤ D) :
    (Squarefree.dCard X H D : ℝ) ≤ D + 1 := by
  have hcard : (Squarefree.dCard X H D : ℝ) ≤ ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).card : ℝ) := by
    rw [dCard_eq_intCard]
    exact_mod_cast Finset.card_filter_le _ _
  refine le_trans hcard ?_
  rw [Int.card_Icc]
  rcases le_or_gt ⌈D⌉ ⌊2 * D⌋ with h | h
  · have hz : (0:ℤ) ≤ ⌊2 * D⌋ + 1 - ⌈D⌉ := by omega
    have hc : (((⌊2 * D⌋ + 1 - ⌈D⌉).toNat : ℕ) : ℝ) = ((⌊2 * D⌋ + 1 - ⌈D⌉ : ℤ) : ℝ) := by
      rw [show (((⌊2 * D⌋ + 1 - ⌈D⌉).toNat : ℕ) : ℝ)
          = (((⌊2 * D⌋ + 1 - ⌈D⌉).toNat : ℤ) : ℝ) from by push_cast; ring, Int.toNat_of_nonneg hz]
    rw [hc]
    have h1 : (⌊2 * D⌋ : ℝ) ≤ 2 * D := Int.floor_le _
    have h2 : (D : ℝ) ≤ (⌈D⌉ : ℝ) := Int.le_ceil _
    push_cast; linarith
  · rw [Int.toNat_of_nonpos (by omega)]; push_cast; linarith

/-- Cast of `(d.toNat)²` to real equals `(d:ℝ)²` for `0 ≤ d`. -/
private lemma toNat_sq_cast {d : ℤ} (hd : 0 ≤ d) :
    (((d.toNat) ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by
  have hi : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd
  have hc : ((d.toNat : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hi
  rw [Nat.cast_pow, hc]

/-- Single dyadic block, bounded by `dCard`.  For a real scale `t` whose integers all satisfy
`d² > b − a` (so each inner count is `≤ 1`), the block sum of the inner counts is at most
`dCard X H t`, because each `d` with positive count lies in the `dCard` filter. -/
private lemma block_count_le_dCard (a b : ℕ) (X H t : ℝ) (ha : 1 ≤ a)
    (haX : X ≤ (a : ℝ)) (hbX : (b : ℝ) ≤ X + H)
    (hlen : ∀ d : ℤ, ⌈t⌉ ≤ d → d ≤ ⌊2 * t⌋ → 1 ≤ d → (b : ℤ) - (a : ℤ) < (d.toNat) ^ 2) :
    (∑ d ∈ Finset.Icc ⌈t⌉ ⌊2 * t⌋,
        ((#{n ∈ Finset.Icc a b | (d.toNat) ^ 2 ∣ n} : ℕ) : ℝ))
      ≤ (Squarefree.dCard X H t : ℝ) := by
  set pred : ℤ → Prop :=
    fun d => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H with hpreddef
  set Nf : ℤ → ℝ := fun d => ((#{n ∈ Finset.Icc a b | (d.toNat) ^ 2 ∣ n} : ℕ) : ℝ) with hNfdef
  -- per term: Nf d ≤ (if pred d then 1 else 0)
  have hterm : ∀ d ∈ Finset.Icc ⌈t⌉ ⌊2 * t⌋, Nf d ≤ (if pred d then (1 : ℝ) else 0) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    obtain ⟨hd1, hd2⟩ := hd
    simp only [hNfdef]
    set N := (#{n ∈ Finset.Icc a b | (d.toNat) ^ 2 ∣ n} : ℕ) with hNdef
    by_cases hd0 : 1 ≤ d
    · have hlenq : (b : ℤ) - (a : ℤ) < (d.toNat) ^ 2 := hlen d hd1 hd2 hd0
      have hbalt : b - a < (d.toNat) ^ 2 := by
        rcases le_or_gt a b with hab | hab
        · have : ((b - a : ℕ) : ℤ) < ((d.toNat) ^ 2 : ℕ) := by
            rw [Nat.cast_sub hab]; push_cast; push_cast at hlenq; omega
          exact_mod_cast this
        · have hdn : 1 ≤ d.toNat := by omega
          simp only [Nat.sub_eq_zero_of_le (le_of_lt hab)]
          have : 0 < (d.toNat) ^ 2 := by positivity
          omega
      have hNle1 : N ≤ 1 := count_le_one a b _ hbalt
      by_cases hN0 : N = 0
      · rw [hN0]; simp only [Nat.cast_zero]; split_ifs <;> norm_num
      · have hN1 : N = 1 := by omega
        have hposN : 1 ≤ N := by omega
        have hpred : pred d := by
          obtain ⟨m, hm1, hm2⟩ := exists_mult_of_count_pos haX hbX hposN
          refine ⟨m, ?_, ?_⟩
          · rwa [toNat_sq_cast (by omega : (0:ℤ) ≤ d)] at hm1
          · rwa [toNat_sq_cast (by omega : (0:ℤ) ≤ d)] at hm2
        rw [if_pos hpred, hN1]; norm_num
    · have hd0' : d.toNat = 0 := by omega
      have hNzero : N = 0 := by
        rw [hNdef, hd0']
        simp only [Finset.card_eq_zero]
        rw [Finset.filter_eq_empty_iff]
        intro n hn
        simp only [Finset.mem_Icc] at hn
        simp only [pow_two, mul_zero, Nat.zero_dvd]
        omega
      rw [hNzero]; simp only [Nat.cast_zero]; split_ifs <;> norm_num
  -- sum the bound, then identify the indicator sum with dCard
  rw [dCard_eq_intCard]
  calc (∑ d ∈ Finset.Icc ⌈t⌉ ⌊2 * t⌋, Nf d)
      ≤ ∑ d ∈ Finset.Icc ⌈t⌉ ⌊2 * t⌋, (if pred d then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Icc ⌈t⌉ ⌊2 * t⌋).filter pred).card : ℝ) := by
        rw [Finset.sum_boole]

open Squarefree.DyadicAssembly in
/-- Part A of the large-`d` sum.  With `t = D₁+1` and the dyadic cover of `[t, X^{1/2}]`, the sum of
the inner counts over `[D₁+1, ⌊X^{1/2}⌋]` is at most `(J+1)·B`, where `B` bounds each block's
`dCard` and `J` is the number of dyadic blocks (from `exists_cover_exp`). -/
private lemma large_part_A (a b : ℕ) (X H B : ℝ) (D₁ : ℕ)
    (ha : 1 ≤ a) (haX : X ≤ (a : ℝ)) (hbX : (b : ℝ) ≤ X + H)
    (hX1 : 1 ≤ X) (hD1pos : 1 ≤ D₁) (hHlt : H < ((D₁ : ℝ) + 1) ^ 2)
    (hB0 : 0 ≤ B)
    (hcov : ∀ k : ℕ, ((D₁ : ℝ) + 1) * 2 ^ k ≤ X ^ (1/2 : ℝ) →
        (Squarefree.dCard X H (((D₁ : ℝ) + 1) * 2 ^ k) : ℝ) ≤ B) :
    ∃ J : ℕ, ((J : ℝ) + 1) ≤ 1 + Real.log X / (2 * Real.log 2) ∧
      (∑ d ∈ Finset.Icc (D₁ + 1) (⌊X ^ (1/2 : ℝ)⌋.toNat),
          ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ)) ≤ ((J : ℝ) + 1) * B := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  set t : ℝ := (D₁ : ℝ) + 1 with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : 1 ≤ t := by
    rw [htdef]; have hd1R : (1:ℝ) ≤ (D₁:ℝ) := by exact_mod_cast hD1pos
    linarith
  set bb : ℝ := X ^ (1/2 : ℝ) with hbbdef
  have hbbpos : 0 < bb := Real.rpow_pos_of_pos hX0 _
  -- define f : ℤ → ℝ (the extended inner count)
  set f : ℤ → ℝ := fun d => ((#{n ∈ Finset.Icc a b | (d.toNat) ^ 2 ∣ n} : ℕ) : ℝ) with hfdef
  have hf0 : ∀ d, 0 ≤ f d := fun d => by rw [hfdef]; positivity
  -- t ≤ bb? if not, the range is empty and we can take J = 0
  rcases le_or_gt t bb with htbb | htbb
  · obtain ⟨J, hJ1, hJ2, hJ3⟩ := exists_cover_exp t bb htpos htbb
    -- bound J+1 by 1 + logX/(2 log2):  2^{J+1} ≤ 2bb/t ≤ 2bb
    have hJbound : ((J : ℝ) + 1) ≤ 1 + Real.log X / (2 * Real.log 2) := by
      have h2bb : (2 : ℝ) ^ (J + 1) ≤ 2 * bb := by
        have : 2 * bb / t ≤ 2 * bb := by
          rw [div_le_iff₀ htpos]; nlinarith [hbbpos, ht1]
        linarith [hJ3]
      have hlogJ : ((J : ℝ) + 1) * Real.log 2 ≤ Real.log (2 * bb) := by
        have e1 : Real.log ((2:ℝ) ^ (J + 1)) = ((J : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_pow]; push_cast; ring
        have := Real.log_le_log (by positivity) h2bb
        rwa [e1] at this
      have hlog2bb : Real.log (2 * bb) = Real.log 2 + (1/2) * Real.log X := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hbbpos), hbbdef, Real.log_rpow hX0]
      rw [hlog2bb] at hlogJ
      have hrw : 1 + Real.log X / (2 * Real.log 2)
          = (Real.log 2 + (1/2) * Real.log X) / Real.log 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hlog2]
      linarith [hlogJ]
    refine ⟨J, hJbound, ?_⟩
    -- per-block bound: ∑_{block k} f ≤ B  (via block_count_le_dCard + hcov)
    have hblock : ∀ k ∈ Finset.range (J + 1),
        ∑ d ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f d ≤ B := by
      intro k hk
      rw [Finset.mem_range] at hk
      -- t·2^k ≤ t·2^J ≤ bb  (from t·2^{J+1} ≤ 2bb)
      have hDk_le : t * 2 ^ k ≤ bb := by
        have h2kJ : (2:ℝ) ^ k ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) (by omega)
        have hle : t * 2 ^ k ≤ t * 2 ^ J := mul_le_mul_of_nonneg_left h2kJ htpos.le
        have hexp : t * 2 ^ (J + 1) = 2 * (t * 2 ^ J) := by ring
        linarith [hJ2, hexp ▸ hJ2]
      have hscale : t * 2 ^ (k + 1) = 2 * (t * 2 ^ k) := by ring
      have hlenk : ∀ d : ℤ, ⌈t * 2 ^ k⌉ ≤ d → d ≤ ⌊2 * (t * 2 ^ k)⌋ → 1 ≤ d →
          (b : ℤ) - (a : ℤ) < (d.toNat) ^ 2 := by
        intro d hd1 _ hd1pos
        -- d ≥ ⌈t·2^k⌉ ≥ t·2^k ≥ t = D₁+1 > √(b-a) hence d² > H ≥ b - a
        have hdR : t ≤ (d : ℝ) := by
          have h1 : t ≤ t * 2 ^ k := by
            have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
            nlinarith [htpos]
          have h2 : (t * 2 ^ k : ℝ) ≤ (⌈t * 2 ^ k⌉ : ℝ) := Int.le_ceil _
          have h3 : ((⌈t * 2 ^ k⌉ : ℤ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
          linarith
        have hdsq : H < (d : ℝ) ^ 2 := by
          have : ((D₁ : ℝ) + 1) ^ 2 ≤ (d : ℝ) ^ 2 := by
            apply pow_le_pow_left₀ (by rw [htdef] at htpos; positivity) (by rw [htdef] at hdR; exact hdR)
          linarith
        -- b - a ≤ H < d²
        have hba : (b : ℝ) - (a : ℝ) ≤ H := by linarith [haX, hbX]
        have hreal : (b : ℝ) - (a : ℝ) < (d : ℝ) ^ 2 := by linarith
        -- convert to ℤ inequality
        have hltZ : (((b : ℤ) - (a : ℤ) : ℤ) : ℝ) < (((d.toNat) ^ 2 : ℕ) : ℝ) := by
          rw [toNat_sq_cast (by omega : (0:ℤ) ≤ d)]
          push_cast; linarith
        exact_mod_cast hltZ
      calc ∑ d ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f d
          = ∑ d ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊2 * (t * 2 ^ k)⌋, f d := by rw [hscale]
        _ ≤ (Squarefree.dCard X H (t * 2 ^ k) : ℝ) :=
            block_count_le_dCard a b X H (t * 2 ^ k) ha haX hbX hlenk
        _ ≤ B := by
            have := hcov k (by rw [htdef] at hDk_le ⊢; rw [hbbdef] at hDk_le; exact hDk_le)
            rw [htdef] at this ⊢; exact this
    have hcover := cover_sum_le f hf0 t bb B htpos J hJ1 hB0 hblock
    -- bridge: ∑_{ℤ.Icc ⌈t⌉ ⌊bb⌋} f = ∑_{Nat.Icc (D₁+1) ⌊bb⌋.toNat} count
    have hceilt : ⌈t⌉ = (D₁ : ℤ) + 1 := by
      rw [htdef]; rw [show ((D₁ : ℝ) + 1) = ((D₁ + 1 : ℤ) : ℝ) from by push_cast; ring]
      exact Int.ceil_intCast _
    have hbridge : (∑ d ∈ Finset.Icc (D₁ + 1) (⌊bb⌋.toNat),
          ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ))
        = ∑ d ∈ Finset.Icc ⌈t⌉ ⌊bb⌋, f d := by
      rw [hceilt, hfdef]
      apply Finset.sum_nbij' (i := fun (m:ℕ) => (m:ℤ)) (j := fun (d:ℤ) => d.toNat)
      · intro m hm; simp only [Finset.mem_Icc] at hm ⊢
        refine ⟨by exact_mod_cast hm.1, ?_⟩
        calc (m : ℤ) ≤ (⌊bb⌋.toNat : ℤ) := by exact_mod_cast hm.2
          _ = ⌊bb⌋ := Int.toNat_of_nonneg (by rw [Int.le_floor]; push_cast; linarith [hbbpos])
      · intro d hd; simp only [Finset.mem_Icc] at hd ⊢
        constructor
        · omega
        · have : ((⌊bb⌋ : ℤ)) = (⌊bb⌋.toNat : ℤ) :=
            (Int.toNat_of_nonneg (by rw [Int.le_floor]; push_cast; linarith [hbbpos])).symm
          omega
      · intro m _; simp
      · intro d hd; simp only [Finset.mem_Icc] at hd; omega
      · intro m _; simp only [hfdef, Int.toNat_natCast]; rfl
    rw [hbbdef] at hbridge ⊢
    rw [hbridge]; exact hcover
  · -- t > bb: empty range, take J = 0
    refine ⟨0, ?_, ?_⟩
    · push_cast
      have : 0 ≤ Real.log X / (2 * Real.log 2) := by positivity
      linarith
    · have hempty : Finset.Icc (D₁ + 1) (⌊X ^ (1/2:ℝ)⌋.toNat) = ∅ := by
        rw [Finset.Icc_eq_empty]
        intro hle
        -- D₁+1 ≤ ⌊bb⌋.toNat ⟹ (D₁+1:ℝ) ≤ bb, contradicting htbb
        have : (D₁ + 1 : ℝ) ≤ X ^ (1/2:ℝ) := by
          have h1 : (D₁ + 1 : ℕ) ≤ ⌊X^(1/2:ℝ)⌋.toNat := hle
          have h2 : ((D₁ + 1 : ℕ) : ℝ) ≤ (⌊X^(1/2:ℝ)⌋.toNat : ℝ) := by exact_mod_cast h1
          have hfl0 : (0:ℤ) ≤ ⌊X^(1/2:ℝ)⌋ := by rw [Int.le_floor]; push_cast; linarith [hbbpos]
          have h3 : ((⌊X^(1/2:ℝ)⌋.toNat : ℕ) : ℝ) ≤ X^(1/2:ℝ) := by
            have hle' : ((⌊X^(1/2:ℝ)⌋.toNat : ℤ)) = ⌊X^(1/2:ℝ)⌋ := Int.toNat_of_nonneg hfl0
            have h4 : ((⌊X^(1/2:ℝ)⌋.toNat : ℤ) : ℝ) = (⌊X^(1/2:ℝ)⌋ : ℝ) := by exact_mod_cast hle'
            have h5 : (⌊X^(1/2:ℝ)⌋ : ℝ) ≤ X^(1/2:ℝ) := Int.floor_le _
            have h6 : ((⌊X^(1/2:ℝ)⌋.toNat : ℕ) : ℝ) = ((⌊X^(1/2:ℝ)⌋.toNat : ℤ) : ℝ) := by push_cast; ring
            rw [h6, h4]; exact h5
          push_cast at h2; linarith
        rw [htdef, hbbdef] at htbb; linarith
      rw [hempty, Finset.sum_empty]; positivity

/-- Part B of the large-`d` sum (the boundary `(⌊X^{1/2}⌋, √b]`).  Each inner count is `≤ 1`
(because `d > X^{1/2} ⇒ d² > X ≥ b − a`), so the sum is at most the interval cardinality. -/
private lemma large_part_B (a b : ℕ) (X H : ℝ) (lo hi : ℕ)
    (hbaX : (b : ℝ) - (a : ℝ) ≤ X) (hlo : X ^ (1/2 : ℝ) < (lo : ℝ)) (hX0 : 0 < X)
    (hlohi : lo ≤ hi + 1) :
    (∑ d ∈ Finset.Icc lo hi, ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ))
      ≤ ((hi : ℝ) - (lo : ℝ) + 1) := by
  -- each term ≤ 1, and #(Icc lo hi) ≤ hi - lo + 1
  have hterm : ∀ d ∈ Finset.Icc lo hi, ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) ≤ 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    -- d ≥ lo ≥ X^{1/2}, so d² ≥ X > b - a ⟹ N_d ≤ 1
    have hdR : X ^ (1/2 : ℝ) < (d : ℝ) := lt_of_lt_of_le hlo (by exact_mod_cast hd.1)
    have hdsq : X < (d : ℝ) ^ 2 := by
      have hsq : (X ^ (1/2:ℝ)) ^ 2 = X := by
        rw [← Real.rpow_natCast (X ^ (1/2:ℝ)) 2, ← Real.rpow_mul hX0.le]; norm_num
      have h := pow_lt_pow_left₀ hdR (Real.rpow_nonneg hX0.le _) (n := 2) (by norm_num)
      rwa [hsq] at h
    have hba : (b : ℝ) - (a : ℝ) < (d : ℝ) ^ 2 := by linarith
    -- d > 0 since (d:ℝ)² ≥ X > 0
    have hdpos : 0 < d := by
      by_contra h; push Not at h
      interval_cases d
      simp at hdsq; linarith
    have hbalt : b - a < d ^ 2 := by
      rcases le_or_gt a b with hab | hab
      · have hlt2 : ((b - a : ℕ) : ℝ) < ((d ^ 2 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hab, Nat.cast_pow]; linarith
        exact_mod_cast hlt2
      · simp only [Nat.sub_eq_zero_of_le (le_of_lt hab)]
        have : 0 < d ^ 2 := by positivity
        omega
    have := count_le_one a b _ hbalt
    exact_mod_cast this
  calc (∑ d ∈ Finset.Icc lo hi, ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ))
      ≤ ∑ _d ∈ Finset.Icc lo hi, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (#(Finset.Icc lo hi) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((hi : ℝ) - (lo : ℝ) + 1) := by
        rw [Nat.card_Icc]
        rcases le_or_gt lo hi with h | h
        · have : (hi + 1 - lo : ℕ) ≤ hi - lo + 1 := by omega
          have hc : ((hi + 1 - lo : ℕ) : ℝ) ≤ (hi : ℝ) - (lo : ℝ) + 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; linarith
          exact hc
        · rw [Nat.sub_eq_zero_of_le (by omega)]; push_cast
          have hlc : (lo : ℝ) ≤ (hi : ℝ) + 1 := by exact_mod_cast hlohi
          linarith

/-! ## Small-`d` main term -/

/-- Small-`d` block.  `∑_{d≤D₁} μ(d)·N_d = (6/π²)·H + O(D₁ + H/D₁)`: replacing each count by
`H/d²` costs `≤ 2` per term (via `count_close`, `count_multiples`, and `|len − H| ≤ 1`), and the
truncated Möbius sum is `6/π²` up to `1/D₁` (via `moebius_partial_close`). -/
private lemma small_part (a b : ℕ) (X H : ℝ) (D₁ : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hD1 : 1 ≤ D₁)
    (hlen : |((b : ℝ) - (a : ℝ) + 1) - H| ≤ 1) :
    |(∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) * ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ))
        - 6 / Real.pi ^ 2 * H|
      ≤ 2 * (D₁ : ℝ) + H / (D₁ : ℝ) := by
  set len : ℝ := (b : ℝ) - (a : ℝ) + 1 with hlendef
  -- rewrite N_d via count_multiples to (b/d² - (a-1)/d² : ℕ)
  have hNeq : ∀ d ∈ Finset.Icc 1 D₁,
      ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ)
        = ((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) := by
    intro d _; rw [count_multiples a b (d ^ 2) ha]
  rw [Finset.sum_congr rfl (fun d hd => by rw [hNeq d hd])]
  -- main term H·∑ μ/d²
  set S : ℝ := ∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) * ((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) with hSdef
  set T : ℝ := ∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) * (H / (d : ℝ) ^ 2) with hTdef
  -- triangle: |S - (6/π²)H| ≤ |S - T| + |T - (6/π²)H|
  have htri : |S - 6 / Real.pi ^ 2 * H| ≤ |S - T| + |T - 6 / Real.pi ^ 2 * H| := by
    have hh := abs_add_le (S - T) (T - 6 / Real.pi ^ 2 * H)
    have he : (S - T) + (T - 6 / Real.pi ^ 2 * H) = S - 6 / Real.pi ^ 2 * H := by ring
    rw [he] at hh; exact hh
  -- bound |S - T| ≤ 2·D₁
  have hST : |S - T| ≤ 2 * (D₁ : ℝ) := by
    rw [hSdef, hTdef, ← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 D₁,
            ((μ d : ℝ) * ((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - (μ d : ℝ) * (H / (d : ℝ) ^ 2))|
        ≤ ∑ d ∈ Finset.Icc 1 D₁,
            |(μ d : ℝ) * ((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - (μ d : ℝ) * (H / (d : ℝ) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 D₁, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd1 : 1 ≤ d := hd.1
          have hq : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
          rw [← mul_sub, abs_mul]
          have hμ : |(μ d : ℝ)| ≤ 1 := abs_moebius_le_one d
          -- |N_d - H/d²| ≤ |N_d - len/d²| + |len/d² - H/d²| ≤ 1 + 1/d² ≤ 2
          have hclose := count_close a b (d ^ 2) ha hab hq
          have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
          have hd2R : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith [hdR]
          have hlencast : ((d ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
          rw [hlencast] at hclose
          -- |len/d² - H/d²| = |len - H|/d² ≤ 1/d² ≤ 1
          have hsecond : |len / (d : ℝ) ^ 2 - H / (d : ℝ) ^ 2| ≤ 1 := by
            rw [div_sub_div_same, abs_div]
            rw [abs_of_pos (by positivity : (0:ℝ) < (d:ℝ)^2)]
            rw [div_le_one (by positivity)]
            calc |len - H| ≤ 1 := hlen
              _ ≤ (d : ℝ) ^ 2 := hd2R
          have hdiff : |((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - H / (d : ℝ) ^ 2| ≤ 2 := by
            calc |((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - H / (d : ℝ) ^ 2|
                ≤ |((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - len / (d : ℝ) ^ 2|
                  + |len / (d : ℝ) ^ 2 - H / (d : ℝ) ^ 2| := by
                  have htri2 := abs_add_le
                    (((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - len / (d : ℝ) ^ 2)
                    (len / (d : ℝ) ^ 2 - H / (d : ℝ) ^ 2)
                  have he : (((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - len / (d : ℝ) ^ 2)
                      + (len / (d : ℝ) ^ 2 - H / (d : ℝ) ^ 2)
                      = ((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - H / (d : ℝ) ^ 2 := by ring
                  rw [he] at htri2; exact htri2
              _ ≤ 1 + 1 := by
                  apply add_le_add _ hsecond
                  rw [hlendef]; exact hclose
              _ = 2 := by norm_num
          calc |(μ d : ℝ)| * |((b / d ^ 2 - (a - 1) / d ^ 2 : ℕ) : ℝ) - H / (d : ℝ) ^ 2|
              ≤ 1 * 2 := by
                apply mul_le_mul hμ hdiff (abs_nonneg _) (by norm_num)
            _ = 2 := by norm_num
      _ = 2 * (D₁ : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          rw [show D₁ + 1 - 1 = D₁ by omega]; ring
  -- bound |T - (6/π²)H| = H·|∑ μ/d² - 6/π²| ≤ H/D₁
  have hTval : T = H * (∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) / (d : ℝ) ^ 2) := by
    rw [hTdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _; rw [mul_div_assoc']; ring
  have hHnn : 0 ≤ H := by
    have := abs_le.mp hlen
    -- len = b - a + 1 ≥ 1 (a ≤ b), so H ≥ len - 1 ≥ 0
    have hlenge : (1 : ℝ) ≤ len := by
      rw [hlendef]; have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    linarith [this.1, this.2]
  have hT2 : |T - 6 / Real.pi ^ 2 * H| ≤ H / (D₁ : ℝ) := by
    rw [hTval]
    have hmp := moebius_partial_close D₁ hD1
    have : H * (∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2 * H
        = H * ((∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2) := by ring
    rw [this, abs_mul, abs_of_nonneg hHnn]
    calc H * |(∑ d ∈ Finset.Icc 1 D₁, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2|
        ≤ H * (1 / (D₁ : ℝ)) := by apply mul_le_mul_of_nonneg_left hmp hHnn
      _ = H / (D₁ : ℝ) := by ring
  -- combine
  linarith [htri, hST, hT2]

/-! ## Interval cast -/

/-- The target ℤ-`Icc` indicator sum equals the ℕ-`Icc` squarefree count cast to `ℝ`. -/
private lemma target_eq_natSum (X H : ℝ) (hX : 1 ≤ X) (hH : 0 ≤ H) :
    (∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + H⌋, (if Squarefree n.toNat then (1 : ℝ) else 0))
      = ((∑ m ∈ Finset.Icc ⌈X⌉.toNat ⌊X + H⌋.toNat,
          (if Squarefree m then (1 : ℤ) else 0) : ℤ) : ℝ) := by
  have hceil : (1:ℤ) ≤ ⌈X⌉ := by rw [Int.one_le_ceil_iff]; linarith
  have hfloor : (0:ℤ) ≤ ⌊X + H⌋ := by rw [Int.le_floor]; push_cast; linarith
  push_cast
  apply Finset.sum_nbij' (fun (n:ℤ) => n.toNat) (fun (m:ℕ) => (m:ℤ))
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨Int.toNat_le_toNat hn.1, Int.toNat_le_toNat hn.2⟩
  · intro m hm; simp only [Finset.mem_Icc] at hm ⊢
    refine ⟨?_, ?_⟩
    · calc (⌈X⌉:ℤ) = (⌈X⌉.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        _ ≤ (m:ℤ) := by exact_mod_cast hm.1
    · calc (m:ℤ) ≤ (⌊X+H⌋.toNat : ℤ) := by exact_mod_cast hm.2
        _ = ⌊X+H⌋ := Int.toNat_of_nonneg hfloor
  · intro n hn; simp only [Finset.mem_Icc] at hn
    rw [Int.toNat_of_nonneg (le_trans (by omega) hn.1)]
  · intro m _; simp
  · intro n hn; simp only [Finset.mem_Icc] at hn; rfl

/-! ## Structural master bound -/

/-- The structural heart: assemble `interval_sqf_eq` + the small/large parts into a single
`O(D₁ + H/D₁ + (J+1)·B + boundary)` bound on `|S − (6/π²)H|`, where `S` is the squarefree count
over `[a,b] = [⌈X⌉, ⌊X+H⌋]`.  The per-block `dCard` bound `B` and the dyadic-block geometry are
supplied by the caller (via `key_dyadic_estimate`); the numeric `rpow` shrinking is done there. -/
private lemma count_master (X H : ℝ) (D₁ : ℕ) (B : ℝ)
    (hX1 : 1 ≤ X) (hH1 : 1 ≤ H) (hHX : H ≤ X) (hD1 : 1 ≤ D₁)
    (hD1lt : H < ((D₁ : ℝ) + 1) ^ 2) (hD1up : (D₁ : ℝ) ≤ X ^ (1/2 : ℝ)) (hB0 : 0 ≤ B)
    (hcov : ∀ k : ℕ, ((D₁ : ℝ) + 1) * 2 ^ k ≤ X ^ (1/2 : ℝ) →
        (Squarefree.dCard X H (((D₁ : ℝ) + 1) * 2 ^ k) : ℝ) ≤ B) :
    ∃ J : ℕ, ((J : ℝ) + 1) ≤ 1 + Real.log X / (2 * Real.log 2) ∧
      |(∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + H⌋, (if Squarefree n.toNat then (1 : ℝ) else 0))
          - 6 / Real.pi ^ 2 * H|
        ≤ 2 * (D₁ : ℝ) + H / (D₁ : ℝ) + ((J : ℝ) + 1) * B
          + ((X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ) + 2) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hHpos : 0 < H := lt_of_lt_of_le one_pos hH1
  set a : ℕ := ⌈X⌉.toNat with hadef
  set b : ℕ := ⌊X + H⌋.toNat with hbdef
  -- basic facts: 1 ≤ a, a ≤ b, casts
  have hceil : (1 : ℤ) ≤ ⌈X⌉ := by rw [Int.one_le_ceil_iff]; exact hX0
  have ha1 : 1 ≤ a := by rw [hadef]; omega
  have hacast : ((a : ℕ) : ℝ) = (⌈X⌉ : ℝ) := by
    rw [hadef]; norm_cast; rw [Int.toNat_of_nonneg (by omega)]
  have hflnn : (0 : ℤ) ≤ ⌊X + H⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hbcast : ((b : ℕ) : ℝ) = (⌊X + H⌋ : ℝ) := by
    rw [hbdef]; norm_cast; rw [Int.toNat_of_nonneg hflnn]
  have haR : X ≤ (a : ℝ) := by rw [hacast]; exact Int.le_ceil X
  have haR' : (a : ℝ) < X + 1 := by rw [hacast]; have := Int.ceil_lt_add_one X; linarith
  have hbR : (b : ℝ) ≤ X + H := by rw [hbcast]; exact Int.floor_le (X + H)
  have hbR' : X + H - 1 < (b : ℝ) := by
    rw [hbcast]; have := Int.sub_one_lt_floor (X + H); linarith
  have hab : a ≤ b := by
    -- ⌈X⌉ ≤ ⌊X+H⌋ since (⌈X⌉:ℝ) < X+1 ≤ X+H
    have hcf : ⌈X⌉ ≤ ⌊X + H⌋ := by
      rw [Int.le_floor]
      have := Int.ceil_lt_add_one X
      push_cast; linarith [hH1]
    rw [hadef, hbdef]; omega
  -- the squarefree count over the ℕ interval, cast to ℝ
  rw [target_eq_natSum X H hX1 hHpos.le, ← hadef, ← hbdef]
  -- Möbius reduction (in ℤ, then cast)
  have hred : ((∑ m ∈ Finset.Icc a b, (if Squarefree m then (1 : ℤ) else 0) : ℤ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (μ d : ℝ) * ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by
    rw [interval_sqf_eq a b ha1]; push_cast; rfl
  rw [hred]
  -- split the d-sum at D₁ and P := ⌊X^{1/2}⌋
  set M : ℕ := Nat.sqrt b with hMdef
  set P : ℕ := ⌊X ^ (1/2 : ℝ)⌋.toNat with hPdef
  -- index relations: D₁ ≤ P ≤ M
  have hPnn : (0 : ℤ) ≤ ⌊X ^ (1/2 : ℝ)⌋ := by
    rw [Int.le_floor]; push_cast; positivity
  have hD1P : D₁ ≤ P := by
    rw [hPdef]
    have hfl : (D₁ : ℤ) ≤ ⌊X ^ (1/2 : ℝ)⌋ := by rw [Int.le_floor]; push_cast; exact hD1up
    omega
  have hPcast : ((P : ℕ) : ℝ) ≤ X ^ (1/2 : ℝ) := by
    rw [hPdef]
    have he : ((⌊X ^ (1/2:ℝ)⌋.toNat : ℕ) : ℝ) = (⌊X ^ (1/2:ℝ)⌋ : ℝ) := by
      rw [show ((⌊X ^ (1/2:ℝ)⌋.toNat : ℕ) : ℝ) = ((⌊X ^ (1/2:ℝ)⌋.toNat : ℤ) : ℝ) from by
        push_cast; ring, Int.toNat_of_nonneg hPnn]
    rw [he]; exact Int.floor_le _
  have hPM : P ≤ M := by
    rw [hMdef, Nat.le_sqrt']
    have hPsq : ((P : ℝ)) ^ 2 ≤ X := by
      have h := pow_le_pow_left₀ (by positivity) hPcast 2
      rwa [← Real.rpow_natCast (X ^ (1/2:ℝ)) 2, ← Real.rpow_mul hX0.le, Nat.cast_ofNat,
        show (1/2:ℝ) * 2 = 1 by norm_num, Real.rpow_one] at h
    have hXb : X ≤ (b : ℝ) := by linarith [hbR']
    have hP2 : ((P ^ 2 : ℕ) : ℝ) ≤ (b : ℝ) := by push_cast; linarith
    exact_mod_cast hP2
  -- split: Icc 1 M = Icc 1 D₁ ∪ Icc (D₁+1) P ∪ Icc (P+1) M
  set F : ℕ → ℝ := fun d => (μ d : ℝ) * ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) with hFdef
  have hsplit : (∑ d ∈ Finset.Icc 1 M, F d)
      = (∑ d ∈ Finset.Icc 1 D₁, F d) + (∑ d ∈ Finset.Icc (D₁ + 1) P, F d)
        + (∑ d ∈ Finset.Icc (P + 1) M, F d) := by
    have e1 : Finset.Icc 1 M = Finset.Icc 1 P ∪ Finset.Icc (P + 1) M := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have e2 : Finset.Icc 1 P = Finset.Icc 1 D₁ ∪ Finset.Icc (D₁ + 1) P := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj1 : Disjoint (Finset.Icc 1 P) (Finset.Icc (P + 1) M) := by
      rw [Finset.disjoint_left]; intro x hx hx2
      simp only [Finset.mem_Icc] at hx hx2; omega
    have hdisj2 : Disjoint (Finset.Icc 1 D₁) (Finset.Icc (D₁ + 1) P) := by
      rw [Finset.disjoint_left]; intro x hx hx2
      simp only [Finset.mem_Icc] at hx hx2; omega
    rw [e1, Finset.sum_union hdisj1, e2, Finset.sum_union hdisj2, add_assoc]
  rw [hsplit]
  -- SMALL bound
  have hlenbd : |((b : ℝ) - (a : ℝ) + 1) - H| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [haR, haR', hbR, hbR']
  have hSmall := small_part a b X H D₁ ha1 hab hD1 hlenbd
  rw [← hFdef] at hSmall
  -- LARGE A: |∑ μ N_d| ≤ ∑ N_d ≤ (J+1)·B
  have hLA := large_part_A a b X H B D₁ ha1 haR hbR hX1 hD1 hD1lt hB0 hcov
  obtain ⟨J, hJlog, hJsum⟩ := hLA
  refine ⟨J, hJlog, ?_⟩
  have hLAabs : |∑ d ∈ Finset.Icc (D₁ + 1) P, F d| ≤ ((J : ℝ) + 1) * B := by
    rw [hPdef]
    calc |∑ d ∈ Finset.Icc (D₁ + 1) (⌊X ^ (1/2:ℝ)⌋.toNat), F d|
        ≤ ∑ d ∈ Finset.Icc (D₁ + 1) (⌊X ^ (1/2:ℝ)⌋.toNat), |F d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc (D₁ + 1) (⌊X ^ (1/2:ℝ)⌋.toNat),
            ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by
          apply Finset.sum_le_sum; intro d _
          rw [hFdef, abs_mul]
          calc |(μ d : ℝ)| * |((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ)|
              ≤ 1 * ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by
                apply mul_le_mul (abs_moebius_le_one d) (le_of_eq (abs_of_nonneg (by positivity)))
                  (abs_nonneg _) (by norm_num)
            _ = ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by ring
      _ ≤ ((J : ℝ) + 1) * B := hJsum
  -- LARGE B: |∑_{Icc (P+1) M} μ N_d| ≤ ∑ N_d ≤ (M - P + 1) ≤ √(X+H) - X^{1/2} + 1
  have hbaX : (b : ℝ) - (a : ℝ) ≤ X := by linarith [hbR, haR, hHX]
  have hPgt : X ^ (1/2 : ℝ) < ((P + 1 : ℕ) : ℝ) := by
    rw [hPdef]
    have he : ((⌊X ^ (1/2:ℝ)⌋.toNat : ℕ) : ℝ) = (⌊X ^ (1/2:ℝ)⌋ : ℝ) := by
      rw [show ((⌊X ^ (1/2:ℝ)⌋.toNat : ℕ) : ℝ) = ((⌊X ^ (1/2:ℝ)⌋.toNat : ℤ) : ℝ) from by
        push_cast; ring, Int.toNat_of_nonneg hPnn]
    have hlt : X ^ (1/2:ℝ) < (⌊X ^ (1/2:ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    push_cast [he]; linarith
  have hPMle : P + 1 ≤ M + 1 := by omega
  have hLB := large_part_B a b X H (P + 1) M hbaX hPgt hX0 hPMle
  have hLBabs : |∑ d ∈ Finset.Icc (P + 1) M, F d| ≤ ((M : ℝ) - (P : ℝ) + 1) := by
    calc |∑ d ∈ Finset.Icc (P + 1) M, F d|
        ≤ ∑ d ∈ Finset.Icc (P + 1) M, |F d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc (P + 1) M,
            ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by
          apply Finset.sum_le_sum; intro d _
          rw [hFdef, abs_mul]
          calc |(μ d : ℝ)| * |((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ)|
              ≤ 1 * ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by
                apply mul_le_mul (abs_moebius_le_one d) (le_of_eq (abs_of_nonneg (by positivity)))
                  (abs_nonneg _) (by norm_num)
            _ = ((#{n ∈ Finset.Icc a b | d ^ 2 ∣ n} : ℕ) : ℝ) := by ring
      _ ≤ ((M : ℝ) - ((P + 1 : ℕ) : ℝ) + 1) := hLB
      _ ≤ ((M : ℝ) - (P : ℝ) + 1) := by push_cast; linarith
  -- M - P ≤ √(X+H) - X^{1/2}:  M = √b ≤ √(X+H), P ≥ X^{1/2} - 1 ... use P ≥ X^{1/2} (strict via hPgt-1)
  have hMle : (M : ℝ) ≤ (X + H) ^ (1/2 : ℝ) := by
    rw [hMdef]
    -- Nat.sqrt b ≤ √b ≤ √(X+H)
    have hsq : ((Nat.sqrt b : ℕ) : ℝ) ^ 2 ≤ (b : ℝ) := by
      have := Nat.sqrt_le' b; exact_mod_cast this
    have hb_le : (b : ℝ) ≤ X + H := hbR
    have h1 : ((Nat.sqrt b : ℕ) : ℝ) ^ 2 ≤ X + H := le_trans hsq hb_le
    -- so Nat.sqrt b ≤ (X+H)^{1/2}
    have h2 : ((Nat.sqrt b : ℕ) : ℝ) = (((Nat.sqrt b : ℕ) : ℝ) ^ 2) ^ (1/2 : ℝ) := by
      rw [← Real.rpow_natCast (((Nat.sqrt b : ℕ) : ℝ)) 2, ← Real.rpow_mul (by positivity),
        Nat.cast_ofNat, show (2:ℝ) * (1/2) = 1 by norm_num, Real.rpow_one]
    rw [h2]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hPgtR : X ^ (1/2 : ℝ) < (P : ℝ) + 1 := by
    have := hPgt; push_cast at this; linarith
  -- assemble
  have hPgeP : X ^ (1/2 : ℝ) - 1 ≤ (P : ℝ) := by linarith [hPgtR]
  have hbound : ((M : ℝ) - (P : ℝ) + 1) ≤ (X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ) + 1 + 1 := by
    linarith [hMle, hPgeP]
  -- triangle on the three blocks
  have htri : |(∑ d ∈ Finset.Icc 1 D₁, F d) + (∑ d ∈ Finset.Icc (D₁ + 1) P, F d)
        + (∑ d ∈ Finset.Icc (P + 1) M, F d) - 6 / Real.pi ^ 2 * H|
      ≤ |(∑ d ∈ Finset.Icc 1 D₁, F d) - 6 / Real.pi ^ 2 * H|
        + |∑ d ∈ Finset.Icc (D₁ + 1) P, F d| + |∑ d ∈ Finset.Icc (P + 1) M, F d| := by
    have h := abs_add_le ((∑ d ∈ Finset.Icc 1 D₁, F d) - 6 / Real.pi ^ 2 * H
        + ∑ d ∈ Finset.Icc (D₁ + 1) P, F d) (∑ d ∈ Finset.Icc (P + 1) M, F d)
    have h2 := abs_add_le ((∑ d ∈ Finset.Icc 1 D₁, F d) - 6 / Real.pi ^ 2 * H)
        (∑ d ∈ Finset.Icc (D₁ + 1) P, F d)
    have he : (∑ d ∈ Finset.Icc 1 D₁, F d) - 6 / Real.pi ^ 2 * H
        + ∑ d ∈ Finset.Icc (D₁ + 1) P, F d + ∑ d ∈ Finset.Icc (P + 1) M, F d
        = (∑ d ∈ Finset.Icc 1 D₁, F d) + (∑ d ∈ Finset.Icc (D₁ + 1) P, F d)
          + (∑ d ∈ Finset.Icc (P + 1) M, F d) - 6 / Real.pi ^ 2 * H := by ring
    rw [he] at h
    linarith [h, h2]
  -- the boundary in the goal is exactly (X+H)^{1/2} - X^{1/2} + 1; we have an extra +1 slack ≤ ...
  -- but the goal RHS only has one boundary term; fold the extra +1 into 2D₁ generously
  have hfinal := htri
  -- combine all bounds; note 2D₁ + H/D₁ already covers small, and boundary slack ≤ 2D₁
  have hD1ge1 : (1 : ℝ) ≤ (D₁ : ℝ) := by exact_mod_cast hD1
  linarith [hSmall, hLAabs, hLBabs, hbound, htri, hD1ge1]

/-! ## Numeric assembly: the final short-interval estimate -/

/-- `(X+H)^{1/2} − X^{1/2} ≤ H / X^{1/2}` for `0 < X`, `0 ≤ H`. -/
private lemma sqrt_diff_le (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H) :
    (X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ) ≤ H / X ^ (1/2 : ℝ) := by
  have hXH : 0 < X + H := by linarith
  have hsX : 0 < X ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hsXH : 0 ≤ (X + H) ^ (1/2 : ℝ) := Real.rpow_nonneg hXH.le _
  have hsqXH : ((X + H) ^ (1/2 : ℝ)) ^ 2 = X + H := by
    rw [← Real.rpow_natCast ((X + H) ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hXH.le]; norm_num
  have hsqX : (X ^ (1/2 : ℝ)) ^ 2 = X := by
    rw [← Real.rpow_natCast (X ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hX.le]; norm_num
  rw [le_div_iff₀ hsX]
  have hfac : ((X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ))
        * ((X + H) ^ (1/2 : ℝ) + X ^ (1/2 : ℝ)) = H := by
    have hexp : ((X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ))
        * ((X + H) ^ (1/2 : ℝ) + X ^ (1/2 : ℝ))
        = ((X + H) ^ (1/2 : ℝ)) ^ 2 - (X ^ (1/2 : ℝ)) ^ 2 := by ring
    rw [hexp, hsqXH, hsqX]; ring
  have hnn : 0 ≤ (X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ) := by
    have := Real.rpow_le_rpow hX.le (by linarith : X ≤ X + H) (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  nlinarith [hnn, hsXH, hsX, hfac]

set_option maxHeartbeats 1600000 in
/-- **Final short-interval estimate.**  Assembles `count_master` with `H = X^{(1-g)/5}`,
`D₁ = ⌊X^{(1-g)/10}⌋ ≈ √H`, and the per-block bound `B = (C_k+1)·H/X^{u_k}+1` (`C_k, u_k` from
`key_dyadic_assembly`) into the headline bound `|S − (6/π²)H| ≤ C·H/X^u`. -/
theorem count_short_interval (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      |(∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + X ^ ((1 - g) / 5)⌋,
            (if Squarefree n.toNat then (1 : ℝ) else 0))
          - 6 / Real.pi ^ 2 * X ^ ((1 - g) / 5)|
        ≤ C * X ^ ((1 - g) / 5) / X ^ u := by
  classical
  obtain ⟨uk, huk, Ck, hCk, Xk, hkey⟩ := Squarefree.key_dyadic_assembly g hg hg'
  set e : ℝ := (1 - g) / 5 with hedef
  have he0 : 0 < e := by rw [hedef]; nlinarith [hg']
  have he12 : e < 1/2 := by rw [hedef]; nlinarith [hg]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- target shrink exponent
  set u : ℝ := min uk (e/2) / 2 with hudef
  have hu0 : 0 < u := by
    rw [hudef]; have := lt_min huk (by linarith : 0 < e/2); linarith
  have huuk : u < uk := by
    rw [hudef]; have h := min_le_left uk (e/2); nlinarith [huk, h]
  have hue2 : u < e/2 := by
    rw [hudef]; have h := min_le_right uk (e/2); nlinarith [he0, h]
  have hue : u < e := by linarith
  have hu12 : u < 1/2 := by linarith
  have hduk : 0 < uk - u := by linarith
  have hdeu : 0 < e - u := by linarith
  -- the assembled constant
  set C : ℝ := 2 + 2 + 3
      + ((Ck + 1) * (1 + (uk - u)⁻¹ / (2 * Real.log 2))
          + (e - u)⁻¹ / (2 * Real.log 2) + 1) with hCdef
  have hC0 : 0 < C := by
    rw [hCdef]
    have h1 : 0 ≤ (Ck + 1) * (1 + (uk - u)⁻¹ / (2 * Real.log 2)) := by positivity
    have h2 : 0 ≤ (e - u)⁻¹ / (2 * Real.log 2) := by positivity
    linarith
  -- X₀: large enough for all elementary bounds
  set X₀ : ℝ := max (max Xk 1) (2 ^ (2 / e)) with hX0def
  refine ⟨u, hu0, C, hC0, X₀, fun X hX => ?_⟩
  have hXk : Xk ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2e : (2 : ℝ) ^ (2 / e) ≤ X := le_trans (le_max_right _ _) hX
  have hX0pos : 0 < X := lt_of_lt_of_le one_pos hX1
  set H : ℝ := X ^ e with hHdef
  have hHpos : 0 < H := Real.rpow_pos_of_pos hX0pos _
  have hH1 : 1 ≤ H := Real.one_le_rpow hX1 he0.le
  have hHX : H ≤ X := by
    rw [hHdef]; calc X ^ e ≤ X ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  -- D₁ := ⌊X^{e/2}⌋
  set s : ℝ := X ^ (e/2 : ℝ) with hsdef
  have hspos : 0 < s := Real.rpow_pos_of_pos hX0pos _
  have hs1 : 1 ≤ s := Real.one_le_rpow hX1 (by linarith)
  set D₁ : ℕ := ⌊s⌋.toNat with hD1def
  have hflnn : (0 : ℤ) ≤ ⌊s⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hD1cast : ((D₁ : ℕ) : ℝ) = (⌊s⌋ : ℝ) := by
    rw [hD1def]; norm_cast; rw [Int.toNat_of_nonneg hflnn]
  have hD1le : (D₁ : ℝ) ≤ s := by rw [hD1cast]; exact Int.floor_le s
  have hD1gt : s - 1 < (D₁ : ℝ) := by rw [hD1cast]; have := Int.sub_one_lt_floor s; linarith
  have hD1pos : 1 ≤ D₁ := by
    rw [hD1def]
    have : (1 : ℤ) ≤ ⌊s⌋ := by rw [Int.le_floor]; push_cast; exact hs1
    omega
  have hD1geR : (1 : ℝ) ≤ (D₁ : ℝ) := by exact_mod_cast hD1pos
  -- s² = H  (since (e/2)*2 = e)
  have hs2 : s ^ 2 = H := by
    rw [hsdef, hHdef, ← Real.rpow_natCast (X ^ (e/2:ℝ)) 2, ← Real.rpow_mul hX0pos.le]
    norm_num
  -- hypotheses of count_master
  have hD1lt : H < ((D₁ : ℝ) + 1) ^ 2 := by
    have hs_lt : s < (D₁ : ℝ) + 1 := by linarith [hD1gt]
    have := pow_lt_pow_left₀ hs_lt hspos.le (n := 2) (by norm_num)
    rw [hs2] at this; exact this
  have hsX12 : s ≤ X ^ (1/2 : ℝ) := by
    rw [hsdef]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hD1up : (D₁ : ℝ) ≤ X ^ (1/2 : ℝ) := le_trans hD1le hsX12
  -- per-block bound B
  set B : ℝ := (Ck + 1) * H / X ^ uk + 1 with hBdef
  have hXuk : 0 < X ^ uk := Real.rpow_pos_of_pos hX0pos _
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  -- hcov: each block dCard ≤ B
  have hcov : ∀ k : ℕ, ((D₁ : ℝ) + 1) * 2 ^ k ≤ X ^ (1/2 : ℝ) →
      (Squarefree.dCard X H (((D₁ : ℝ) + 1) * 2 ^ k) : ℝ) ≤ B := by
    intro k hk
    set D : ℝ := ((D₁ : ℝ) + 1) * 2 ^ k with hDdef
    have hDnn : 0 ≤ D := by rw [hDdef]; positivity
    have hHpow : H = X ^ ((1 - g) / 5) := by rw [hHdef, hedef]
    by_cases hge : X ^ ((1 - g) / 5) / X ^ uk ≤ D
    · -- use key estimate
      have hkk := hkey X hXk D (by rw [← hHpow] at hge; exact hge) hk
      rw [← hHpow] at hkk
      -- C_k·H/X^{uk} ≤ B
      have : Ck * H / X ^ uk ≤ B := by
        rw [hBdef]
        have hHXuk : 0 ≤ H / X ^ uk := by positivity
        have : Ck * H / X ^ uk ≤ (Ck + 1) * H / X ^ uk := by
          rw [div_le_div_iff_of_pos_right hXuk]; nlinarith [hHpos]
        linarith
      linarith [hkk]
    · -- trivial bound dCard ≤ D + 1 < H/X^{uk} + 1 ≤ B
      push Not at hge
      rw [← hHpow] at hge
      have htriv := dCard_le_lin X H D hDnn
      have : D + 1 ≤ B := by
        rw [hBdef]
        have hHle : H / X ^ uk ≤ (Ck + 1) * H / X ^ uk := by
          rw [div_le_div_iff_of_pos_right hXuk]; nlinarith [hHpos, hCk]
        linarith [le_of_lt hge, hHle]
      linarith [htriv]
  -- invoke count_master
  obtain ⟨J, hJlog, hbnd⟩ := count_master X H D₁ B hX1 hH1 hHX hD1pos hD1lt hD1up hB0 hcov
  -- now bound the RHS of count_master by C·H/X^u
  set R : ℝ := H / X ^ u with hRdef
  have hXu : 0 < X ^ u := Real.rpow_pos_of_pos hX0pos _
  have hRpos : 0 < R := by rw [hRdef]; positivity
  -- R = X^{e-u}
  have hRval : R = X ^ (e - u) := by
    rw [hRdef, hHdef, Real.rpow_sub hX0pos]
  -- (iv) 1 ≤ R
  have hR1 : (1 : ℝ) ≤ R := by rw [hRval]; exact Real.one_le_rpow hX1 hdeu.le
  -- (ii) s ≤ R   (s = X^{e/2}, R = X^{e-u}, e/2 ≤ e-u)
  have hsR : s ≤ R := by
    rw [hsdef, hRval]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  -- 2·D₁ ≤ 2·R
  have hT1 : 2 * (D₁ : ℝ) ≤ 2 * R := by nlinarith [hD1le, hsR]
  -- H/D₁ ≤ 2·R   (needs D₁ ≥ s/2, i.e. s ≥ 2)
  have hs_ge2 : (2 : ℝ) ≤ s := by
    rw [hsdef]
    have hmono : ((2 : ℝ) ^ (2 / e)) ^ (e/2 : ℝ) ≤ X ^ (e/2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hX2e (by linarith)
    have heq : ((2 : ℝ) ^ (2 / e)) ^ (e/2 : ℝ) = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (2 / e) * (e/2) = 1 by field_simp]
      norm_num
    linarith [heq ▸ hmono]
  -- D₁ ≥ s - 1 ≥ s/2  (since s ≥ 2)
  have hD1ge_half : s / 2 ≤ (D₁ : ℝ) := by linarith [hD1gt, hs_ge2]
  have hT2 : H / (D₁ : ℝ) ≤ 2 * R := by
    rw [← hs2]
    -- s²/D₁ ≤ s²/(s/2) = 2s ≤ 2R
    have hD1posR : 0 < (D₁ : ℝ) := by linarith [hD1geR]
    have hstep : s ^ 2 / (D₁ : ℝ) ≤ 2 * s := by
      rw [div_le_iff₀ hD1posR]
      nlinarith [hD1ge_half, hspos]
    linarith [hstep, hsR]
  -- boundary: (X+H)^{1/2} - X^{1/2} + 2 ≤ 3·R
  have hbdry : (X + H) ^ (1/2 : ℝ) - X ^ (1/2 : ℝ) + 2 ≤ 3 * R := by
    have hd := sqrt_diff_le X H hX0pos hHpos.le
    -- H/X^{1/2} = X^{e-1/2} ≤ R   (e - 1/2 ≤ e - u since u ≤ 1/2)
    have hHX12 : H / X ^ (1/2 : ℝ) = X ^ (e - 1/2) := by rw [hHdef, Real.rpow_sub hX0pos]
    have hle : H / X ^ (1/2 : ℝ) ≤ R := by
      rw [hHX12, hRval]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith [hd, hle, hR1]
  -- the per-block factor: bound (J+1)·B
  -- abbreviations
  set L : ℝ := Real.log X / (2 * Real.log 2) with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]; apply div_nonneg (Real.log_nonneg hX1); positivity
  -- B = (Ck+1)·X^{e-uk} + 1
  have hHXuk : H / X ^ uk = X ^ (e - uk) := by rw [hHdef, Real.rpow_sub hX0pos]
  have hBval : B = (Ck + 1) * X ^ (e - uk) + 1 := by
    rw [hBdef, mul_div_assoc, hHXuk]
  -- (a) X^{e-uk} ≤ R   (since e-uk ≤ e-u as u < uk)
  have heuk : X ^ (e - uk) ≤ R := by
    rw [hRval]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  -- (b) X^{e-uk} · log X ≤ (uk-u)⁻¹ · R
  --   log X ≤ (uk-u)⁻¹ · X^{uk-u}, and X^{e-uk}·X^{uk-u} = X^{e-u} = R
  have hprod1 : X ^ (e - uk) * X ^ (uk - u) = R := by
    rw [hRval, ← Real.rpow_add hX0pos]; ring_nf
  have hloguk : Real.log X ≤ (uk - u)⁻¹ * X ^ (uk - u) :=
    Squarefree.DyadicAssembly.log_le_rpow hduk hX1
  have heuk_pos : 0 < X ^ (e - uk) := Real.rpow_pos_of_pos hX0pos _
  have huk_pos : 0 < X ^ (uk - u) := Real.rpow_pos_of_pos hX0pos _
  have hb : X ^ (e - uk) * Real.log X ≤ (uk - u)⁻¹ * R := by
    calc X ^ (e - uk) * Real.log X
        ≤ X ^ (e - uk) * ((uk - u)⁻¹ * X ^ (uk - u)) := by
          apply mul_le_mul_of_nonneg_left hloguk heuk_pos.le
      _ = (uk - u)⁻¹ * (X ^ (e - uk) * X ^ (uk - u)) := by ring
      _ = (uk - u)⁻¹ * R := by rw [hprod1]
  -- (c) log X ≤ (e-u)⁻¹ · R
  have hprod2 : X ^ (e - u) = R := hRval.symm
  have hlogeu : Real.log X ≤ (e - u)⁻¹ * X ^ (e - u) :=
    Squarefree.DyadicAssembly.log_le_rpow hdeu hX1
  have hc : Real.log X ≤ (e - u)⁻¹ * R := by rw [← hprod2]; exact hlogeu
  -- assemble: (1 + L)·B ≤ ((Ck+1)·(1 + (uk-u)⁻¹/(2 log2)) + (e-u)⁻¹/(2 log2) + 1)·R
  set Cblk : ℝ := (Ck + 1) * (1 + (uk - u)⁻¹ / (2 * Real.log 2))
      + (e - u)⁻¹ / (2 * Real.log 2) + 1 with hCblkdef
  have hlog2' : 0 < 2 * Real.log 2 := by linarith
  have hfac : (1 + L) * B ≤ Cblk * R := by
    rw [hBval, hCblkdef]
    -- (1+L)·((Ck+1)·X^{e-uk} + 1)
    --   = (Ck+1)·X^{e-uk} + (Ck+1)·X^{e-uk}·L + 1 + L
    -- bound each: (Ck+1)·X^{e-uk} ≤ (Ck+1)·R ; 1 ≤ R ;
    --   (Ck+1)·X^{e-uk}·L ≤ (Ck+1)·(uk-u)⁻¹/(2log2)·R ; L ≤ (e-u)⁻¹/(2log2)·R
    have hCk1 : 0 < Ck + 1 := by linarith
    -- term1: (Ck+1)·X^{e-uk} ≤ (Ck+1)·R
    have ht1 : (Ck + 1) * X ^ (e - uk) ≤ (Ck + 1) * R :=
      mul_le_mul_of_nonneg_left heuk hCk1.le
    -- term2: (Ck+1)·X^{e-uk}·L ≤ (Ck+1)·((uk-u)⁻¹/(2log2))·R
    -- L = log X/(2log2); X^{e-uk}·L = (X^{e-uk}·log X)/(2log2) ≤ ((uk-u)⁻¹·R)/(2log2)
    have hXL : X ^ (e - uk) * L ≤ (uk - u)⁻¹ / (2 * Real.log 2) * R := by
      rw [hLdef]
      rw [show X ^ (e - uk) * (Real.log X / (2 * Real.log 2))
            = (X ^ (e - uk) * Real.log X) / (2 * Real.log 2) by ring]
      rw [show (uk - u)⁻¹ / (2 * Real.log 2) * R
            = ((uk - u)⁻¹ * R) / (2 * Real.log 2) by ring]
      exact div_le_div_of_nonneg_right hb hlog2'.le
    have ht2 : (Ck + 1) * X ^ (e - uk) * L
        ≤ (Ck + 1) * ((uk - u)⁻¹ / (2 * Real.log 2)) * R := by
      have := mul_le_mul_of_nonneg_left hXL hCk1.le
      calc (Ck + 1) * X ^ (e - uk) * L
          = (Ck + 1) * (X ^ (e - uk) * L) := by ring
        _ ≤ (Ck + 1) * ((uk - u)⁻¹ / (2 * Real.log 2) * R) := this
        _ = (Ck + 1) * ((uk - u)⁻¹ / (2 * Real.log 2)) * R := by ring
    -- term3: L ≤ (e-u)⁻¹/(2log2)·R
    have ht3 : L ≤ (e - u)⁻¹ / (2 * Real.log 2) * R := by
      rw [hLdef]
      rw [show (e - u)⁻¹ / (2 * Real.log 2) * R
            = ((e - u)⁻¹ * R) / (2 * Real.log 2) by ring]
      exact div_le_div_of_nonneg_right hc hlog2'.le
    -- term4: 1 ≤ R
    nlinarith [ht1, ht2, ht3, hR1, hCk1, heuk_pos, hLnn]
  -- (J+1)·B ≤ (1+L)·B
  have hJB : ((J : ℝ) + 1) * B ≤ Cblk * R := by
    have hstep : ((J : ℝ) + 1) * B ≤ (1 + L) * B := by
      apply mul_le_mul_of_nonneg_right _ hB0
      rw [hLdef]; exact hJlog
    linarith [hstep, hfac]
  -- final combine
  -- C = 2 + 2 + 3 + Cblk, so C·R = 2R + 2R + 3R + Cblk·R
  have hCR : C * R = 2 * R + 2 * R + 3 * R + Cblk * R := by
    rw [hCdef, hCblkdef]; ring
  have hgoal : C * H / X ^ u = C * R := by rw [hRdef]; ring
  rw [hgoal, hCR]
  -- hbnd : |…| ≤ 2·D₁ + H/D₁ + (J+1)·B + boundary
  -- and 2·D₁ ≤ 2R, H/D₁ ≤ 2R, boundary ≤ 3R, (J+1)·B ≤ Cblk·R
  linarith [hbnd, hT1, hT2, hbdry, hJB]

end Squarefree.Mob
