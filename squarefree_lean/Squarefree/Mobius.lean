import Mathlib

/-!
# §1 Möbius reduction — foundational identities

This module collects the two API-heavy number-theoretic facts underlying the §1 reduction
(`explicit_writeup.md` lines 44–72):

* `Squarefree.Mob.sqf_eq_sum` — the squarefree indicator as a sum of `μ` over square divisors,
  `[n squarefree] = ∑_{e ∣ n} r e` where `r` picks out `μ(√e)` on perfect squares.
* `Squarefree.Mob.tsum_moebius_div_sq` — `∑' d, μ(d)/d² = 6/π²` (the `1/ζ(2)` evaluation),
  obtained from `LSeries_zeta_mul_Lseries_moebius` at `s = 2` together with `riemannZeta_two`.

Both feed the interval-level reduction in `Squarefree.Main`.
-/

open ArithmeticFunction Finset Nat Complex
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace Squarefree.Mob

/-! ## The squarefree indicator as a square-divisor sum -/

/-- `r e = μ(√e)` if `e` is a perfect square, else `0`. -/
noncomputable def r : ArithmeticFunction ℤ :=
  ⟨fun e => if IsSquare e then (μ (Nat.sqrt e)) else 0, by simp⟩

theorem r_apply (e : ℕ) : r e = if IsSquare e then (μ (Nat.sqrt e)) else 0 := rfl

private lemma isSquare_prime_pow_iff (p x : ℕ) (hp : p.Prime) :
    IsSquare (p ^ x) ↔ Even x := by
  rw [isSquare_iff_exists_sq]
  constructor
  · rintro ⟨c, hc⟩
    have hpx : (p ^ x).factorization p = x := by rw [Nat.Prime.factorization_pow hp]; simp
    have hc2 : ((c ^ 2).factorization) p = 2 * (c.factorization p) := by
      rw [Nat.factorization_pow]; simp [two_mul]
    rw [hc, hc2] at hpx
    exact ⟨c.factorization p, by omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨p ^ k, by rw [← pow_mul]; ring_nf⟩

private theorem r_prime_pow (p x : ℕ) (hp : p.Prime) :
    r (p ^ x) = if Even x then μ (p ^ (x / 2)) else 0 := by
  rw [r_apply]
  by_cases hx : Even x
  · rw [if_pos ((isSquare_prime_pow_iff p x hp).mpr hx), if_pos hx]
    obtain ⟨k, rfl⟩ := hx
    congr 1
    have : p ^ (k + k) = (p ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
    rw [this, Nat.sqrt_eq']; congr 1; omega
  · rw [if_neg (fun h => hx ((isSquare_prime_pow_iff p x hp).mp h)), if_neg hx]

private lemma coprime_sq_decomp {m n c : ℕ} (h : m * n = c ^ 2) (hc : Nat.Coprime m n) :
    ∃ a, m = a ^ 2 := by
  have hab : IsUnit (GCDMonoid.gcd m n) := by
    rw [show GCDMonoid.gcd m n = Nat.gcd m n from rfl, Nat.isUnit_iff]; exact hc
  exact exists_eq_pow_of_mul_eq_pow hab h

theorem isMult_r : r.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [r_apply, Nat.sqrt_one], ?_⟩
  intro m n hm hn hmn
  rw [r_apply, r_apply, r_apply]
  by_cases hsq : IsSquare (m * n)
  · obtain ⟨c, hc⟩ := hsq
    have hc2 : m * n = c ^ 2 := by rw [hc]; ring
    obtain ⟨a, ha⟩ := coprime_sq_decomp hc2 hmn
    obtain ⟨b, hb⟩ := coprime_sq_decomp (by rw [mul_comm]; exact hc2) hmn.symm
    have hsqm : IsSquare m := ⟨a, by rw [ha]; ring⟩
    have hsqn : IsSquare n := ⟨b, by rw [hb]; ring⟩
    rw [if_pos ⟨c, hc⟩, if_pos hsqm, if_pos hsqn]
    have hsm : Nat.sqrt m = a := by rw [ha, Nat.sqrt_eq']
    have hsn : Nat.sqrt n = b := by rw [hb, Nat.sqrt_eq']
    have hsmn : Nat.sqrt (m * n) = a * b := by
      rw [ha, hb, show a ^ 2 * b ^ 2 = (a * b) ^ 2 by ring, Nat.sqrt_eq']
    rw [hsm, hsn, hsmn]
    have hab_cop : Nat.Coprime a b := by
      have hcop2 : Nat.Coprime (a ^ 2) (b ^ 2) := by rw [← ha, ← hb]; exact hmn
      have h1 : Nat.Coprime (a ^ 2) b := (Nat.coprime_pow_right_iff (by norm_num) _ _).mp hcop2
      exact (Nat.coprime_pow_left_iff (by norm_num) _ _).mp h1
    exact isMultiplicative_moebius.map_mul_of_coprime hab_cop
  · rw [if_neg hsq]
    have hns : ¬ (IsSquare m ∧ IsSquare n) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; exact hsq ⟨a * b, by rw [ha, hb]; ring⟩
    rcases not_and_or.mp hns with h1 | h1
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h1, mul_zero]

private theorem moebius_prime_pow' (p k : ℕ) (hp : p.Prime) :
    μ (p ^ k) = if k = 0 then 1 else if k = 1 then -1 else 0 := by
  rcases k with _ | _ | k
  · simp
  · simp [ArithmeticFunction.moebius_apply_prime hp]
  · rw [if_neg (by omega), if_neg (by omega)]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    push Not; intro _; omega

private theorem zr_prime_pow (p i : ℕ) (hp : p.Prime) :
    (((↑zeta : ArithmeticFunction ℤ)) * r) (p ^ i) = if i ≤ 1 then 1 else 0 := by
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  have hsum : ∀ x ∈ range (i + 1), r (p ^ x) = if Even x then μ (p ^ (x / 2)) else 0 :=
    fun x _ => r_prime_pow p x hp
  rw [Finset.sum_congr rfl hsum]
  have hterm : ∀ x, (if Even x then μ (p ^ (x / 2)) else 0)
      = (if x = 0 then (1 : ℤ) else if x = 2 then -1 else 0) := by
    intro x
    by_cases hx : Even x
    · rw [if_pos hx, moebius_prime_pow' _ _ hp]
      rcases x with _ | _ | _ | x
      · simp
      · exact absurd hx (by decide)
      · simp
      · obtain ⟨k, hk⟩ := hx
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hx, if_neg (by rintro rfl; exact hx (by decide)),
          if_neg (by rintro rfl; exact hx (by decide))]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · rw [if_pos (by omega)]
    interval_cases i
    · simp
    · decide
  · rw [if_neg (by omega)]
    have h02 : ({0, 2} : Finset ℕ) ⊆ range (i + 1) := by
      intro x hx; simp at hx; simp; omega
    rw [← Finset.sum_subset h02]
    · rw [Finset.sum_pair (by norm_num)]; norm_num
    · intro x _ hx
      rw [if_neg (by simp at hx; tauto), if_neg (by simp at hx; tauto)]

/-- `(↑ζ) * r = μ ⬝ μ` (pointwise product), i.e. the convolution of `r` with `ζ`
reproduces `μ²`. -/
theorem zr_eq : ((↑zeta : ArithmeticFunction ℤ)) * r = ArithmeticFunction.pmul μ μ := by
  have hZR : (((↑zeta : ArithmeticFunction ℤ)) * r).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul isMult_r
  have hMM : ((ArithmeticFunction.pmul μ μ : ArithmeticFunction ℤ)).IsMultiplicative :=
    isMultiplicative_moebius.pmul isMultiplicative_moebius
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hZR _ hMM]
  intro p i hp
  rw [zr_prime_pow p i hp, pmul_apply, moebius_prime_pow' p i hp]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i <;> norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; norm_num

/-- The squarefree indicator equals the sum of `r` over the divisors of `n`. -/
theorem sqf_eq_sum (n : ℕ) :
    (if Squarefree n then (1 : ℤ) else 0) = ∑ e ∈ n.divisors, r e := by
  have h1 : (ArithmeticFunction.pmul μ μ) n = if Squarefree n then (1 : ℤ) else 0 := by
    rw [pmul_apply, ← sq]; exact ArithmeticFunction.moebius_sq
  rw [← h1, ← zr_eq, coe_zeta_mul_apply]

/-- **Möbius reduction at interval level.** For `1 ≤ a`, summing the squarefree indicator over
`[a,b]` equals `∑_{d ≤ √b} μ(d) · #{n ∈ [a,b] : d² ∣ n}` (swap the order of `∑_{n} ∑_{e∣n} r e`
and reindex the perfect squares `e = d²`). -/
theorem interval_sqf_eq (a b : ℕ) (ha : 1 ≤ a) :
    (∑ n ∈ Icc a b, (if Squarefree n then (1 : ℤ) else 0))
      = ∑ d ∈ Icc 1 (Nat.sqrt b), (μ d) * (#{n ∈ Icc a b | d ^ 2 ∣ n} : ℤ) := by
  have h1 : (∑ n ∈ Icc a b, (if Squarefree n then (1 : ℤ) else 0))
      = ∑ n ∈ Icc a b, ∑ e ∈ n.divisors, r e :=
    Finset.sum_congr rfl (fun n _ => sqf_eq_sum n)
  rw [h1]
  have hswap : (∑ n ∈ Icc a b, ∑ e ∈ n.divisors, r e)
      = ∑ e ∈ Icc 1 b, r e * (#{n ∈ Icc a b | e ∣ n} : ℤ) := by
    have hinner : ∀ n ∈ Icc a b, (∑ e ∈ n.divisors, r e)
        = ∑ e ∈ Icc 1 b, (if e ∣ n then r e else 0) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext e
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hed, hn0⟩
        refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, le_trans (Nat.le_of_dvd (by omega) hed) hn.2⟩, hed⟩
        rintro rfl; simp at hed; omega
      · rintro ⟨⟨he1, heb⟩, hed⟩; exact ⟨hed, by omega⟩
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap]
  have hterm : ∀ e ∈ Icc 1 b, r e * (#{n ∈ Icc a b | e ∣ n} : ℤ)
      = (if IsSquare e then (μ (Nat.sqrt e)) * (#{n ∈ Icc a b | e ∣ n} : ℤ) else 0) := by
    intro e _
    rw [r_apply]; split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun e => Nat.sqrt e) (fun d => d ^ 2)
  · intro e he
    simp only [mem_filter, mem_Icc] at he
    obtain ⟨⟨he1, heb⟩, ⟨c, hc⟩⟩ := he
    simp only [mem_Icc]
    refine ⟨?_, Nat.sqrt_le_sqrt heb⟩
    rw [Nat.one_le_iff_ne_zero]; rintro h; rw [Nat.sqrt_eq_zero] at h; omega
  · intro d hd
    simp only [mem_Icc] at hd
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨d, by ring⟩⟩
    · nlinarith [hd.1]
    · calc d ^ 2 ≤ (Nat.sqrt b) ^ 2 := by nlinarith [hd.2]
        _ ≤ b := Nat.sqrt_le' b
  · intro e he
    simp only [mem_filter, mem_Icc] at he
    obtain ⟨_, ⟨c, hc⟩⟩ := he
    rw [hc, show c * c = c ^ 2 by ring, Nat.sqrt_eq']
  · intro d _
    exact Nat.sqrt_eq' d
  · intro e he
    simp only [mem_filter, mem_Icc] at he
    obtain ⟨_, hsq⟩ := he
    have hsqe : (Nat.sqrt e) ^ 2 = e := by
      obtain ⟨c, hc⟩ := hsq; rw [hc, show c * c = c ^ 2 by ring, Nat.sqrt_eq']
    rw [hsqe]

/-! ## Counting multiples in an interval -/

/-- Exact count of multiples of `q` in `[a,b]` (for `1 ≤ a`): `⌊b/q⌋ - ⌊(a-1)/q⌋`. -/
theorem count_multiples (a b q : ℕ) (ha : 1 ≤ a) :
    (#{n ∈ Icc a b | q ∣ n} : ℕ) = b / q - (a - 1) / q := by
  rcases le_or_gt a b with hab | hab
  · have key : #{n ∈ Ioc 0 b | q ∣ n}
        = #{n ∈ Ioc 0 (a - 1) | q ∣ n} + #{n ∈ Icc a b | q ∣ n} := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext x; simp only [mem_filter, mem_union, mem_Ioc, mem_Icc]; constructor
        · rintro ⟨⟨hx0, hxb⟩, hd⟩
          rcases le_or_gt x (a - 1) with h | h
          · exact Or.inl ⟨⟨hx0, h⟩, hd⟩
          · exact Or.inr ⟨⟨by omega, hxb⟩, hd⟩
        · rintro (⟨⟨hx0, hx⟩, hd⟩ | ⟨⟨hx, hxb⟩, hd⟩)
          · exact ⟨⟨hx0, by omega⟩, hd⟩
          · exact ⟨⟨by omega, hxb⟩, hd⟩
      · rw [Finset.disjoint_left]
        rintro x hx1 hx2
        simp only [mem_filter, mem_Ioc, mem_Icc] at hx1 hx2
        omega
    rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at key
    omega
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.filter_empty, Finset.card_empty]
    have : b / q ≤ (a - 1) / q := Nat.div_le_div_right (by omega)
    omega

/-! ## `∑' μ(d)/d² = 6/π²` -/

/-- The Möbius–zeta inversion at `s = 2`: `∑' d, μ(d)/d² = 6/π²`. -/
theorem tsum_moebius_div_sq :
    (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have h := LSeries_zeta_mul_Lseries_moebius (s := 2) hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h
  have hz : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hLval : LSeries ↗μ 2 = 1 / riemannZeta 2 := by
    field_simp; linear_combination h
  rw [riemannZeta_two] at hLval
  have hterm : ∀ n : ℕ, LSeries.term ↗μ 2 n
      = (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hpow : (n : ℂ) ^ (2 : ℂ) = ((n : ℝ) ^ 2 : ℝ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
        push_cast; ring
      rw [hpow]; push_cast; ring
  have hLeq : LSeries ↗μ 2
      = ((∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, tsum_congr hterm, ← Complex.ofReal_tsum]
  rw [hLeq] at hLval
  have hfin : ((∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ)
      = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    rw [hLval]; push_cast; field_simp
  exact_mod_cast hfin

end Squarefree.Mob
