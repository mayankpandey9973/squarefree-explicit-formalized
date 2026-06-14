import Mathlib

/-!
# §7 elementary box power-sum bounds

Self-contained, design-independent estimates feeding Prop 7.1
(writeup `../explicit_writeup.md`, lines 1800–1819 and 1955–1957).

Shifts range over the rectangular box
`1 ≤ h₁ ≤ ⌊W⌋`, `1 ≤ h₂ ≤ ⌊W²⌋`, `1 ≤ h₃ ≤ ⌊W⁴⌋` with `W : ℝ`, `W ≥ 1`,
each modelled as `Finset.Icc 1 ⌊W^k⌋₊` over `ℕ`. We set
`S = h₁h₂ + h₁h₃ + h₂h₃`, `P = h₁h₂h₃`, `hΣ = h₁+h₂+h₃`, sum the monomials over
the triple product and cast to `ℝ`.

Strategy: every monomial is `h₁^a h₂^b h₃^c`, so the box sum factors as a product
of single-variable power sums `Σ_{h=1}^N h^m`, each bounded by `N^(m+1)`; with
`(⌊W^k⌋₊ : ℝ) ≤ W^k` and `W^a·W^b = W^(a+b)` the stated `W`-powers follow.
-/

open Finset

namespace Squarefree

/-- The box `Finset.Icc 1 ⌊W⌋₊ ×ˢ Finset.Icc 1 ⌊W²⌋₊ ×ˢ Finset.Icc 1 ⌊W⁴⌋₊` over `ℕ³`
(public: the §7 N14/N21/N15/N22 statements in `Sec7BoxSums`/`Sec7Harvest` quantify over it). -/
noncomputable def box (W : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 ⌊W⌋₊) ×ˢ (Finset.Icc 1 ⌊W ^ 2⌋₊) ×ˢ (Finset.Icc 1 ⌊W ^ 4⌋₊)

/-- `S = h₁h₂ + h₁h₃ + h₂h₃` over `ℕ`. -/
def Sbox (h₁ h₂ h₃ : ℕ) : ℕ := h₁ * h₂ + h₁ * h₃ + h₂ * h₃

/-- `P = h₁h₂h₃` over `ℕ`. -/
def Pbox (h₁ h₂ h₃ : ℕ) : ℕ := h₁ * h₂ * h₃

/-- `hΣ = h₁ + h₂ + h₃` over `ℕ`. -/
def HSbox (h₁ h₂ h₃ : ℕ) : ℕ := h₁ + h₂ + h₃

/-- Single-variable power sum bound: `Σ_{h=1}^N h^m ≤ N^(m+1)` (over `ℕ`, cast to `ℝ`). -/
private lemma sum_pow_le (N m : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ((h : ℝ) ^ m)) ≤ (N : ℝ) ^ (m + 1) := by
  calc (∑ h ∈ Finset.Icc 1 N, ((h : ℝ) ^ m))
      ≤ ∑ _h ∈ Finset.Icc 1 N, ((N : ℝ) ^ m) := by
        apply Finset.sum_le_sum
        intro h hh
        have h_le : h ≤ N := (Finset.mem_Icc.mp hh).2
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h_le) m
    _ = (Finset.Icc 1 N).card • ((N : ℝ) ^ m) := by rw [Finset.sum_const]
    _ = (N : ℝ) * (N : ℝ) ^ m := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = (N : ℝ) ^ (m + 1) := by ring

/-- `(⌊W^k⌋₊ : ℝ) ≤ W^k` for `W ≥ 1` (shared with `BoxNegPowerSums`). -/
lemma floor_pow_le (W : ℝ) (hW : 1 ≤ W) (k : ℕ) :
    ((⌊W ^ k⌋₊ : ℝ)) ≤ W ^ k :=
  Nat.floor_le (by positivity)

/-- Single-variable bound over the `k`-th edge of the box:
`Σ_{h=1}^{⌊W^k⌋₊} h^m ≤ W^(k*(m+1))` for `W ≥ 1`. -/
private lemma single_le (W : ℝ) (hW : 1 ≤ W) (k m : ℕ) :
    (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ m)) ≤ W ^ (k * (m + 1)) := by
  calc (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ m))
      ≤ ((⌊W ^ k⌋₊ : ℝ)) ^ (m + 1) := sum_pow_le _ _
    _ ≤ (W ^ k) ^ (m + 1) := by
        apply pow_le_pow_left₀ (by positivity) (floor_pow_le W hW k)
    _ = W ^ (k * (m + 1)) := by rw [← pow_mul]

/-- Box sum of a single monomial `h₁^a h₂^b h₃^c` factors and is bounded by
`W^(a+1) · W^(2(b+1)) · W^(4(c+1))`. -/
private lemma box_monomial_le (W : ℝ) (hW : 1 ≤ W) (a b c : ℕ) :
    (∑ p ∈ box W, ((p.1 : ℝ) ^ a * (p.2.1 : ℝ) ^ b * (p.2.2 : ℝ) ^ c))
      ≤ W ^ (1 * (a + 1)) * W ^ (2 * (b + 1)) * W ^ (4 * (c + 1)) := by
  have hfac :
      (∑ p ∈ box W, ((p.1 : ℝ) ^ a * (p.2.1 : ℝ) ^ b * (p.2.2 : ℝ) ^ c))
        = (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ a)
          * ((∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ b)
            * (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ c)) := by
    unfold box
    rw [Finset.sum_product]
    conv_rhs => rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun h₁ _ => ?_)
    rw [Finset.sum_product]
    conv_rhs => rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h₂ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h₃ _ => ?_)
    ring
  rw [hfac]
  have e1 : (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ a) ≤ W ^ (1 * (a + 1)) := by
    have := single_le W hW 1 a; simpa using this
  have e2 : (∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ b) ≤ W ^ (2 * (b + 1)) :=
    single_le W hW 2 b
  have e3 : (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ c) ≤ W ^ (4 * (c + 1)) :=
    single_le W hW 4 c
  have hnn1 : (0 : ℝ) ≤ ∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ a := by positivity
  have hnn2 : (0 : ℝ) ≤ ∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ b := by positivity
  have hnn3 : (0 : ℝ) ≤ ∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ c := by positivity
  have hpow1 : (0 : ℝ) ≤ W ^ (1 * (a + 1)) := by positivity
  have hpow23 : (0 : ℝ) ≤ W ^ (2 * (b + 1)) * W ^ (4 * (c + 1)) := by positivity
  calc (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ a)
        * ((∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ b)
          * (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ c))
      ≤ W ^ (1 * (a + 1)) * (W ^ (2 * (b + 1)) * W ^ (4 * (c + 1))) := by
        apply mul_le_mul e1 _ (by positivity) hpow1
        exact mul_le_mul e2 e3 hnn3 (by positivity)
    _ = W ^ (1 * (a + 1)) * W ^ (2 * (b + 1)) * W ^ (4 * (c + 1)) := by ring

/-- A single monomial box sum is bounded by `W^k` whenever its weighted degree
`a + 2b + 4c + 7` does not exceed `k` (using `W ≥ 1`). -/
private lemma box_monomial_le' (W : ℝ) (hW : 1 ≤ W) (a b c k : ℕ)
    (hk : a + 2 * b + 4 * c + 7 ≤ k) :
    (∑ p ∈ box W, ((p.1 : ℝ) ^ a * (p.2.1 : ℝ) ^ b * (p.2.2 : ℝ) ^ c)) ≤ W ^ k := by
  refine (box_monomial_le W hW a b c).trans ?_
  have hcollapse :
      W ^ (1 * (a + 1)) * W ^ (2 * (b + 1)) * W ^ (4 * (c + 1))
        = W ^ (a + 2 * b + 4 * c + 7) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [hcollapse]
  exact pow_le_pow_right₀ hW hk

/-- Single-variable rpow sum bound for a nonnegative real exponent `s`:
`Σ_{h=1}^N h^s ≤ N^(s+1)` (over `ℝ`, with `^` the real power). -/
private lemma sum_rpow_le (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∑ h ∈ Finset.Icc 1 N, ((h : ℝ) ^ s)) ≤ (N : ℝ) ^ (s + 1) := by
  calc (∑ h ∈ Finset.Icc 1 N, ((h : ℝ) ^ s))
      ≤ ∑ _h ∈ Finset.Icc 1 N, ((N : ℝ) ^ s) := by
        apply Finset.sum_le_sum
        intro h hh
        have h_le : h ≤ N := (Finset.mem_Icc.mp hh).2
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h_le) hs
    _ = (Finset.Icc 1 N).card • ((N : ℝ) ^ s) := by rw [Finset.sum_const]
    _ = (N : ℝ) * (N : ℝ) ^ s := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (s + 1) := by
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN
          have hne : s + (1:ℝ) ≠ 0 := by positivity
          simp [Real.zero_rpow hne]
        · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
          rw [Real.rpow_add hNpos, Real.rpow_one, mul_comm]

/-- Single-variable rpow bound over the `k`-th edge of the box:
`Σ_{h=1}^{⌊W^k⌋₊} h^s ≤ W^(k·(s+1))` for `W ≥ 1` and `s ≥ 0` (shared with
`BoxNegPowerSums`). -/
lemma single_rpow_le (W : ℝ) (hW : 1 ≤ W) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ s)) ≤ W ^ ((k : ℝ) * (s + 1)) := by
  calc (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ s))
      ≤ ((⌊W ^ k⌋₊ : ℝ)) ^ (s + 1) := sum_rpow_le _ hs
    _ ≤ (W ^ k) ^ (s + 1) :=
        Real.rpow_le_rpow (by positivity) (floor_pow_le W hW k) (by positivity)
    _ = W ^ ((k : ℝ) * (s + 1)) := by
        rw [← Real.rpow_natCast W k, ← Real.rpow_mul (by linarith)]

/-- Box sum of a single rpow monomial `h₁^sa h₂^sb h₃^sc` (nonneg real exponents)
factors and is bounded by `W^(1·(sa+1)) · W^(2·(sb+1)) · W^(4·(sc+1))`. -/
private lemma box_rpow_monomial_le (W : ℝ) (hW : 1 ≤ W) {sa sb sc : ℝ}
    (ha : 0 ≤ sa) (hb : 0 ≤ sb) (hc : 0 ≤ sc) :
    (∑ p ∈ box W, ((p.1 : ℝ) ^ sa * (p.2.1 : ℝ) ^ sb * (p.2.2 : ℝ) ^ sc))
      ≤ W ^ ((1 : ℝ) * (sa + 1)) * W ^ ((2 : ℝ) * (sb + 1)) * W ^ ((4 : ℝ) * (sc + 1)) := by
  have hfac :
      (∑ p ∈ box W, ((p.1 : ℝ) ^ sa * (p.2.1 : ℝ) ^ sb * (p.2.2 : ℝ) ^ sc))
        = (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ sa)
          * ((∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ sb)
            * (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc)) := by
    unfold box
    rw [Finset.sum_product]
    conv_rhs => rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun h₁ _ => ?_)
    rw [Finset.sum_product]
    conv_rhs => rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h₂ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h₃ _ => ?_)
    ring
  rw [hfac]
  have e1 : (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ sa) ≤ W ^ ((1 : ℝ) * (sa + 1)) := by
    have := single_rpow_le W hW 1 ha; simpa using this
  have e2 : (∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ sb) ≤ W ^ ((2 : ℝ) * (sb + 1)) := by
    have := single_rpow_le W hW 2 hb; simpa using this
  have e3 : (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc) ≤ W ^ ((4 : ℝ) * (sc + 1)) := by
    have := single_rpow_le W hW 4 hc; simpa using this
  have hnn2 : (0 : ℝ) ≤ ∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ sb := by positivity
  have hnn3 : (0 : ℝ) ≤ ∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc := by positivity
  calc (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ sa)
        * ((∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ sb)
          * (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc))
      ≤ W ^ ((1 : ℝ) * (sa + 1)) * (W ^ ((2 : ℝ) * (sb + 1)) * W ^ ((4 : ℝ) * (sc + 1))) := by
        apply mul_le_mul e1 _ (by positivity) (by positivity)
        exact mul_le_mul e2 e3 hnn3 (by positivity)
    _ = W ^ ((1 : ℝ) * (sa + 1)) * W ^ ((2 : ℝ) * (sb + 1)) * W ^ ((4 : ℝ) * (sc + 1)) := by
        ring

/-- An rpow monomial box sum is bounded by `W^k` (`k : ℝ`) whenever its weighted degree
`(sa+1) + 2(sb+1) + 4(sc+1)` does not exceed `k` (using `W ≥ 1`, nonneg exponents). -/
private lemma box_rpow_monomial_le' (W : ℝ) (hW : 1 ≤ W) {sa sb sc k : ℝ}
    (ha : 0 ≤ sa) (hb : 0 ≤ sb) (hc : 0 ≤ sc)
    (hk : (sa + 1) + 2 * (sb + 1) + 4 * (sc + 1) ≤ k) :
    (∑ p ∈ box W, ((p.1 : ℝ) ^ sa * (p.2.1 : ℝ) ^ sb * (p.2.2 : ℝ) ^ sc)) ≤ W ^ k := by
  refine (box_rpow_monomial_le W hW ha hb hc).trans ?_
  have hcollapse :
      W ^ ((1 : ℝ) * (sa + 1)) * W ^ ((2 : ℝ) * (sb + 1)) * W ^ ((4 : ℝ) * (sc + 1))
        = W ^ ((sa + 1) + 2 * (sb + 1) + 4 * (sc + 1)) := by
    rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
    congr 1; ring
  rw [hcollapse]
  exact Real.rpow_le_rpow_of_exponent_le hW hk

/-- `Σ_{box} 1 ≤ C·W^7`. -/
theorem box_sum_one : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W → (∑ _p ∈ box W, (1 : ℝ)) ≤ C * W ^ 7 := by
  refine ⟨1, one_pos, by norm_num, fun W hW => ?_⟩
  rw [one_mul]
  have hrw : (∑ _p ∈ box W, (1 : ℝ))
      = ∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 0) := by
    refine Finset.sum_congr rfl (fun p _ => by simp)
  rw [hrw]
  exact box_monomial_le' W hW 0 0 0 7 (by norm_num)

/-- `Σ_{box} hΣ ≤ C·W^11`. -/
theorem box_sum_HS : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W → (∑ p ∈ box W, (HSbox p.1 p.2.1 p.2.2 : ℝ)) ≤ C * W ^ 11 := by
  refine ⟨3, by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W, (HSbox p.1 p.2.1 p.2.2 : ℝ))
      = (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 0))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 0))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by simp only [HSbox]; push_cast; ring)
  rw [hrw]
  have b1 := box_monomial_le' W hW 1 0 0 11 (by norm_num)
  have b2 := box_monomial_le' W hW 0 1 0 11 (by norm_num)
  have b3 := box_monomial_le' W hW 0 0 1 11 (by norm_num)
  have : (3 : ℝ) * W ^ 11 = W ^ 11 + W ^ 11 + W ^ 11 := by ring
  rw [this]
  exact add_le_add (add_le_add b1 b2) b3

/-- `Σ_{box} P ≤ C·W^14`. -/
theorem box_sum_P : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W → (∑ p ∈ box W, (Pbox p.1 p.2.1 p.2.2 : ℝ)) ≤ C * W ^ 14 := by
  refine ⟨1, one_pos, by norm_num, fun W hW => ?_⟩
  rw [one_mul]
  have hrw : (∑ p ∈ box W, (Pbox p.1 p.2.1 p.2.2 : ℝ))
      = ∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1) := by
    refine Finset.sum_congr rfl (fun p _ => by simp only [Pbox]; push_cast; ring)
  rw [hrw]
  exact box_monomial_le' W hW 1 1 1 14 (by norm_num)

/-- `Σ_{box} S ≤ C·W^13`. -/
theorem box_sum_S : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W → (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ)) ≤ C * W ^ 13 := by
  refine ⟨3, by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ))
      = (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 0))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by simp only [Sbox]; push_cast; ring)
  rw [hrw]
  -- weighted degrees: h₁h₂ → 10, h₁h₃ → 12, h₂h₃ → 13
  have b1 := box_monomial_le' W hW 1 1 0 13 (by norm_num)
  have b2 := box_monomial_le' W hW 1 0 1 13 (by norm_num)
  have b3 := box_monomial_le' W hW 0 1 1 13 (by norm_num)
  have : (3 : ℝ) * W ^ 13 = W ^ 13 + W ^ 13 + W ^ 13 := by ring
  rw [this]
  exact add_le_add (add_le_add b1 b2) b3

/-- `Σ_{box} S² ≤ C·W^19`. `S² = h₁²h₂²+h₁²h₃²+h₂²h₃²+2h₁²h₂h₃+2h₁h₂²h₃+2h₁h₂h₃²`,
written as nine unit-coefficient monomials (the three cross terms counted twice). -/
theorem box_sum_S_sq : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W → (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2)) ≤ C * W ^ 19 := by
  refine ⟨9, by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2))
      = (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 0))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 2))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 2))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 2))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 2)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by simp only [Sbox]; push_cast; ring)
  rw [hrw]
  -- degrees: 13,17,19,15,15,16,16,18,18  (all ≤ 19)
  have b1 := box_monomial_le' W hW 2 2 0 19 (by norm_num)
  have b2 := box_monomial_le' W hW 2 0 2 19 (by norm_num)
  have b3 := box_monomial_le' W hW 0 2 2 19 (by norm_num)
  have b4 := box_monomial_le' W hW 2 1 1 19 (by norm_num)
  have b5 := box_monomial_le' W hW 1 2 1 19 (by norm_num)
  have b6 := box_monomial_le' W hW 1 1 2 19 (by norm_num)
  have hC : (9 : ℝ) * W ^ 19
      = W ^ 19 + W ^ 19 + W ^ 19 + W ^ 19 + W ^ 19 + W ^ 19 + W ^ 19 + W ^ 19 + W ^ 19 := by
    ring
  rw [hC]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add b1 b2) b3) b4) b4) b5) b5) b6) b6

/-- `Σ_{box} S·P ≤ C·W^20`. `SP = h₁²h₂²h₃ + h₁²h₂h₃² + h₁h₂²h₃²`. -/
theorem box_sum_SP : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ)))
        ≤ C * W ^ 20 := by
  refine ⟨3, by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ)))
      = (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 2))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 2)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by simp only [Sbox, Pbox]; push_cast; ring)
  rw [hrw]
  -- degrees: 17, 19, 20  (all ≤ 20)
  have b1 := box_monomial_le' W hW 2 2 1 20 (by norm_num)
  have b2 := box_monomial_le' W hW 2 1 2 20 (by norm_num)
  have b3 := box_monomial_le' W hW 1 2 2 20 (by norm_num)
  have : (3 : ℝ) * W ^ 20 = W ^ 20 + W ^ 20 + W ^ 20 := by ring
  rw [this]
  exact add_le_add (add_le_add b1 b2) b3

/-- `Σ_{box} S·hΣ ≤ C·W^17`. Expanding `(h₁h₂+h₁h₃+h₂h₃)(h₁+h₂+h₃)` gives nine
monomials (three of them the common term `h₁h₂h₃`). -/
theorem box_sum_S_HS : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (HSbox p.1 p.2.1 p.2.2 : ℝ)))
        ≤ C * W ^ 17 := by
  refine ⟨9, by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (HSbox p.1 p.2.1 p.2.2 : ℝ)))
      = (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 0))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 0))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 0 * (p.2.2 : ℝ) ^ 2))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 2 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 0 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 2))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1))
        + (∑ p ∈ box W, ((p.1 : ℝ) ^ 1 * (p.2.1 : ℝ) ^ 1 * (p.2.2 : ℝ) ^ 1)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by simp only [Sbox, HSbox]; push_cast; ring)
  rw [hrw]
  -- degrees: 11,12,13,16,15,17,14,14,14  (all ≤ 17)
  have a1 := box_monomial_le' W hW 2 1 0 17 (by norm_num)
  have a2 := box_monomial_le' W hW 1 2 0 17 (by norm_num)
  have a3 := box_monomial_le' W hW 2 0 1 17 (by norm_num)
  have a4 := box_monomial_le' W hW 1 0 2 17 (by norm_num)
  have a5 := box_monomial_le' W hW 0 2 1 17 (by norm_num)
  have a6 := box_monomial_le' W hW 0 1 2 17 (by norm_num)
  have a7 := box_monomial_le' W hW 1 1 1 17 (by norm_num)
  have hC : (9 : ℝ) * W ^ 17
      = W ^ 17 + W ^ 17 + W ^ 17 + W ^ 17 + W ^ 17 + W ^ 17 + W ^ 17 + W ^ 17 + W ^ 17 := by
    ring
  rw [hC]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add a1 a2) a3) a4) a5) a6) a7) a7) a7

/-! ## Stretch: fractional-power box sums (writeup 1806–1811, 1955–1957) -/

/-- `Σ_{box} S^(1/2) ≤ C·W^10` (writeup 1956). Uses subadditivity
`(a+b+c)^(1/2) ≤ a^(1/2)+b^(1/2)+c^(1/2)` then factors each `(h_ih_j)^(1/2)`. -/
theorem box_sum_S_sqrt : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (1/2 : ℝ))) ≤ C * W ^ (10 : ℝ) := by
  refine ⟨3, by norm_num, by norm_num, fun W hW => ?_⟩
  -- termwise subadditivity bound
  have hpt : ∀ p ∈ box W,
      ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (1/2 : ℝ))
        ≤ ((p.1 : ℝ) ^ (1/2 : ℝ) * (p.2.1 : ℝ) ^ (1/2 : ℝ) * (p.2.2 : ℝ) ^ (0 : ℝ))
          + ((p.1 : ℝ) ^ (1/2 : ℝ) * (p.2.1 : ℝ) ^ (0 : ℝ) * (p.2.2 : ℝ) ^ (1/2 : ℝ))
          + ((p.1 : ℝ) ^ (0 : ℝ) * (p.2.1 : ℝ) ^ (1/2 : ℝ) * (p.2.2 : ℝ) ^ (1/2 : ℝ)) := by
    intro p _
    have hS : (Sbox p.1 p.2.1 p.2.2 : ℝ)
        = (p.1 : ℝ) * p.2.1 + (p.1 : ℝ) * p.2.2 + (p.2.1 : ℝ) * p.2.2 := by
      simp only [Sbox]; push_cast; ring
    rw [hS]
    have h12 : (0 : ℝ) ≤ (p.1 : ℝ) * p.2.1 := by positivity
    have h13 : (0 : ℝ) ≤ (p.1 : ℝ) * p.2.2 := by positivity
    have h23 : (0 : ℝ) ≤ (p.2.1 : ℝ) * p.2.2 := by positivity
    calc ((p.1 : ℝ) * p.2.1 + (p.1 : ℝ) * p.2.2 + (p.2.1 : ℝ) * p.2.2) ^ (1/2 : ℝ)
        ≤ ((p.1 : ℝ) * p.2.1 + (p.1 : ℝ) * p.2.2) ^ (1/2 : ℝ)
          + ((p.2.1 : ℝ) * p.2.2) ^ (1/2 : ℝ) :=
          Real.rpow_add_le_add_rpow (by positivity) h23 (by norm_num) (by norm_num)
      _ ≤ (((p.1 : ℝ) * p.2.1) ^ (1/2 : ℝ) + ((p.1 : ℝ) * p.2.2) ^ (1/2 : ℝ))
            + ((p.2.1 : ℝ) * p.2.2) ^ (1/2 : ℝ) := by
          gcongr
          exact Real.rpow_add_le_add_rpow h12 h13 (by norm_num) (by norm_num)
      _ = ((p.1 : ℝ) ^ (1/2 : ℝ) * (p.2.1 : ℝ) ^ (1/2 : ℝ) * (p.2.2 : ℝ) ^ (0 : ℝ))
            + ((p.1 : ℝ) ^ (1/2 : ℝ) * (p.2.1 : ℝ) ^ (0 : ℝ) * (p.2.2 : ℝ) ^ (1/2 : ℝ))
            + ((p.1 : ℝ) ^ (0 : ℝ) * (p.2.1 : ℝ) ^ (1/2 : ℝ) * (p.2.2 : ℝ) ^ (1/2 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
          simp [Real.rpow_zero]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have b1 := box_rpow_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (1/2:ℝ)) (sc := (0:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (10:ℝ)) (by norm_num)
  have b2 := box_rpow_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (0:ℝ)) (sc := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (10:ℝ)) (by norm_num)
  have b3 := box_rpow_monomial_le' W hW (sa := (0:ℝ)) (sb := (1/2:ℝ)) (sc := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (10:ℝ)) (by norm_num)
  have hC : (3 : ℝ) * W ^ (10:ℝ) = W ^ (10:ℝ) + W ^ (10:ℝ) + W ^ (10:ℝ) := by ring
  rw [hC]
  exact add_le_add (add_le_add b1 b2) b3

/-- `Σ_{box} S^(3/2) ≤ C·W^16` (writeup 1956). Bounds `S^(3/2) = S·S^(1/2) ≤
(a+b+c)(√a+√b+√c)` with `a=h₁h₂, b=h₁h₃, c=h₂h₃`, expands into nine rpow monomials. -/
theorem box_sum_S_thalf : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (3/2 : ℝ))) ≤ C * W ^ (16 : ℝ) := by
  refine ⟨9, by norm_num, by norm_num, fun W hW => ?_⟩
  have hpt : ∀ p ∈ box W,
      ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (3/2 : ℝ))
        ≤ ((p.1 : ℝ) ^ (3/2:ℝ) * (p.2.1 : ℝ) ^ (3/2:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ))
          + ((p.1 : ℝ) ^ (3/2:ℝ) * (p.2.1 : ℝ) ^ (1:ℝ) * (p.2.2 : ℝ) ^ (1/2:ℝ))
          + ((p.1 : ℝ) ^ (1:ℝ) * (p.2.1 : ℝ) ^ (3/2:ℝ) * (p.2.2 : ℝ) ^ (1/2:ℝ))
          + ((p.1 : ℝ) ^ (3/2:ℝ) * (p.2.1 : ℝ) ^ (1/2:ℝ) * (p.2.2 : ℝ) ^ (1:ℝ))
          + ((p.1 : ℝ) ^ (3/2:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (3/2:ℝ))
          + ((p.1 : ℝ) ^ (1:ℝ) * (p.2.1 : ℝ) ^ (1/2:ℝ) * (p.2.2 : ℝ) ^ (3/2:ℝ))
          + ((p.1 : ℝ) ^ (1/2:ℝ) * (p.2.1 : ℝ) ^ (3/2:ℝ) * (p.2.2 : ℝ) ^ (1:ℝ))
          + ((p.1 : ℝ) ^ (1/2:ℝ) * (p.2.1 : ℝ) ^ (1:ℝ) * (p.2.2 : ℝ) ^ (3/2:ℝ))
          + ((p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (3/2:ℝ) * (p.2.2 : ℝ) ^ (3/2:ℝ)) := by
    intro p hp
    have hmem := Finset.mem_product.mp (by rwa [box] at hp)
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hmem2 := Finset.mem_product.mp hmem.2
    have hp2 : 1 ≤ p.2.1 := (Finset.mem_Icc.mp hmem2.1).1
    have hp3 : 1 ≤ p.2.2 := (Finset.mem_Icc.mp hmem2.2).1
    set x := (p.1 : ℝ) with hxdef
    set y := (p.2.1 : ℝ) with hydef
    set z := (p.2.2 : ℝ) with hzdef
    have hx0 : (0:ℝ) ≤ x := by rw [hxdef]; positivity
    have hy0 : (0:ℝ) ≤ y := by rw [hydef]; positivity
    have hz0 : (0:ℝ) ≤ z := by rw [hzdef]; positivity
    have hxp : (0:ℝ) < x := by rw [hxdef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp1
    have hyp : (0:ℝ) < y := by rw [hydef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp2
    have hzp : (0:ℝ) < z := by rw [hzdef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp3
    set a := x * y with hadef
    set b := x * z with hbdef
    set c := y * z with hcdef
    have ha0 : (0:ℝ) ≤ a := by positivity
    have hb0 : (0:ℝ) ≤ b := by positivity
    have hc0 : (0:ℝ) ≤ c := by positivity
    have hS : (Sbox p.1 p.2.1 p.2.2 : ℝ) = a + b + c := by
      simp only [Sbox, hadef, hbdef, hcdef, hxdef, hydef, hzdef]; push_cast; ring
    -- S^(1/2) ≤ √a + √b + √c
    have hsqrt : (a + b + c) ^ (1/2:ℝ) ≤ a ^ (1/2:ℝ) + b ^ (1/2:ℝ) + c ^ (1/2:ℝ) := by
      calc (a + b + c) ^ (1/2:ℝ)
          ≤ (a + b) ^ (1/2:ℝ) + c ^ (1/2:ℝ) :=
            Real.rpow_add_le_add_rpow (by positivity) hc0 (by norm_num) (by norm_num)
        _ ≤ (a ^ (1/2:ℝ) + b ^ (1/2:ℝ)) + c ^ (1/2:ℝ) := by
            gcongr
            exact Real.rpow_add_le_add_rpow ha0 hb0 (by norm_num) (by norm_num)
    have habc : (0:ℝ) < a + b + c := by rw [hadef, hbdef, hcdef]; positivity
    -- S^(3/2) = S · S^(1/2)
    have hsplit : (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (3/2:ℝ)
        = (a + b + c) * (a + b + c) ^ (1/2:ℝ) := by
      rw [hS]
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add habc, Real.rpow_one]
    rw [hsplit]
    have hbound : (a + b + c) * (a + b + c) ^ (1/2:ℝ)
        ≤ (a + b + c) * (a ^ (1/2:ℝ) + b ^ (1/2:ℝ) + c ^ (1/2:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hsqrt (by positivity)
    refine hbound.trans ?_
    -- Substitute half-power atoms X=√x, Y=√y, Z=√z; everything becomes polynomial.
    set X := x ^ (1/2:ℝ) with hXdef
    set Y := y ^ (1/2:ℝ) with hYdef
    set Z := z ^ (1/2:ℝ) with hZdef
    have hX2 : X ^ 2 = x := by
      rw [hXdef, ← Real.rpow_natCast (x ^ (1/2:ℝ)) 2, ← Real.rpow_mul hx0]; norm_num
    have hY2 : Y ^ 2 = y := by
      rw [hYdef, ← Real.rpow_natCast (y ^ (1/2:ℝ)) 2, ← Real.rpow_mul hy0]; norm_num
    have hZ2 : Z ^ 2 = z := by
      rw [hZdef, ← Real.rpow_natCast (z ^ (1/2:ℝ)) 2, ← Real.rpow_mul hz0]; norm_num
    have hXh : x ^ (3/2:ℝ) = X ^ 3 := by
      rw [hXdef, ← Real.rpow_natCast (x ^ (1/2:ℝ)) 3, ← Real.rpow_mul hx0]; norm_num
    have hYh : y ^ (3/2:ℝ) = Y ^ 3 := by
      rw [hYdef, ← Real.rpow_natCast (y ^ (1/2:ℝ)) 3, ← Real.rpow_mul hy0]; norm_num
    have hZh : z ^ (3/2:ℝ) = Z ^ 3 := by
      rw [hZdef, ← Real.rpow_natCast (z ^ (1/2:ℝ)) 3, ← Real.rpow_mul hz0]; norm_num
    have sa : a ^ (1/2:ℝ) = X * Y := by rw [hadef, Real.mul_rpow hx0 hy0]
    have sb : b ^ (1/2:ℝ) = X * Z := by rw [hbdef, Real.mul_rpow hx0 hz0]
    have sc : c ^ (1/2:ℝ) = Y * Z := by rw [hcdef, Real.mul_rpow hy0 hz0]
    have key :
        (a + b + c) * (a ^ (1/2:ℝ) + b ^ (1/2:ℝ) + c ^ (1/2:ℝ))
          = (x ^ (3/2:ℝ) * y ^ (3/2:ℝ) * z ^ (0:ℝ))
            + (x ^ (3/2:ℝ) * y ^ (1:ℝ) * z ^ (1/2:ℝ))
            + (x ^ (1:ℝ) * y ^ (3/2:ℝ) * z ^ (1/2:ℝ))
            + (x ^ (3/2:ℝ) * y ^ (1/2:ℝ) * z ^ (1:ℝ))
            + (x ^ (3/2:ℝ) * y ^ (0:ℝ) * z ^ (3/2:ℝ))
            + (x ^ (1:ℝ) * y ^ (1/2:ℝ) * z ^ (3/2:ℝ))
            + (x ^ (1/2:ℝ) * y ^ (3/2:ℝ) * z ^ (1:ℝ))
            + (x ^ (1/2:ℝ) * y ^ (1:ℝ) * z ^ (3/2:ℝ))
            + (x ^ (0:ℝ) * y ^ (3/2:ℝ) * z ^ (3/2:ℝ)) := by
      have xXX : x = X * X := by rw [← hX2]; ring
      have yYY : y = Y * Y := by rw [← hY2]; ring
      have zZZ : z = Z * Z := by rw [← hZ2]; ring
      have collX : (X * X) ^ (1/2:ℝ) = X := by rw [← sq, hX2, ← hXdef]
      have collY : (Y * Y) ^ (1/2:ℝ) = Y := by rw [← sq, hY2, ← hYdef]
      have collZ : (Z * Z) ^ (1/2:ℝ) = Z := by rw [← sq, hZ2, ← hZdef]
      rw [hadef, hbdef, hcdef, sa, sb, sc, hXh, hYh, hZh,
        Real.rpow_zero, Real.rpow_zero, Real.rpow_zero,
        Real.rpow_one, Real.rpow_one, Real.rpow_one]
      rw [xXX, yYY, zZZ, collX, collY, collZ]
      ring
    exact key.le
  -- assembly: each of the nine rpow monomials has weighted degree ≤ 16
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have m1 := box_rpow_monomial_le' W hW (sa := (3/2:ℝ)) (sb := (3/2:ℝ)) (sc := (0:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m2 := box_rpow_monomial_le' W hW (sa := (3/2:ℝ)) (sb := (1:ℝ)) (sc := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m3 := box_rpow_monomial_le' W hW (sa := (1:ℝ)) (sb := (3/2:ℝ)) (sc := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m4 := box_rpow_monomial_le' W hW (sa := (3/2:ℝ)) (sb := (1/2:ℝ)) (sc := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m5 := box_rpow_monomial_le' W hW (sa := (3/2:ℝ)) (sb := (0:ℝ)) (sc := (3/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m6 := box_rpow_monomial_le' W hW (sa := (1:ℝ)) (sb := (1/2:ℝ)) (sc := (3/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m7 := box_rpow_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (3/2:ℝ)) (sc := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m8 := box_rpow_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (1:ℝ)) (sc := (3/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have m9 := box_rpow_monomial_le' W hW (sa := (0:ℝ)) (sb := (3/2:ℝ)) (sc := (3/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (k := (16:ℝ)) (by norm_num)
  have hC : (9 : ℝ) * W ^ (16:ℝ)
      = W ^ (16:ℝ) + W ^ (16:ℝ) + W ^ (16:ℝ) + W ^ (16:ℝ) + W ^ (16:ℝ) + W ^ (16:ℝ)
        + W ^ (16:ℝ) + W ^ (16:ℝ) + W ^ (16:ℝ) := by ring
  rw [hC]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add m1 m2) m3) m4) m5) m6) m7) m8) m9

/-! The four negative-power box sums (writeup 1806–1811: `Σ P^(-1/2)`, `Σ S·P^(-1/2)`,
`Σ (S/P)^(1/2)`, `Σ S·(S/P)^(1/2)`) live in `Bracket/BoxNegPowerSums.lean`, which adds
the decreasing-summand estimate `Σ_{h≤N} h^(-1/2) ≤ 2√N` on top of this file. -/

end Squarefree
