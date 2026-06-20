import Squarefree.Bracket.BoxPowerSums
import Squarefree.Lower.Step4Sum

/-!
# §7 negative-power box sums (writeup 1806–1811)

The four box sums involving `P^(-1/2)`: `Σ P^(-1/2) ≪ W^(7/2)`, `Σ S·P^(-1/2) ≪ W^(19/2)`,
`Σ (S/P)^(1/2) ≪ W^(13/2)`, `Σ S·(S/P)^(1/2) ≪ W^(25/2)`, over the box of
`Bracket/BoxPowerSums.lean` (`1 ≤ h₁ ≤ ⌊W⌋, 1 ≤ h₂ ≤ ⌊W²⌋, 1 ≤ h₃ ≤ ⌊W⁴⌋`).

Strategy: each integrand splits into monomials `h₁^sa h₂^sb h₃^sc` with every exponent
either `-1/2` or nonnegative (using `(S/P)^(1/2) ≤ h₁^(-1/2)+h₂^(-1/2)+h₃^(-1/2)` by
subadditivity). The box sum factors into 1-D sums; the `-1/2` edges are handled by the
decreasing-summand estimate `Σ_{h≤N} h^(-1/2) ≤ 2√N` (`sum_inv_sqrt_le`,
`Lower/Step4Sum.lean`), the rest by `single_rpow_le`. Exponent rule:
`(sa,sb,sc) ↦ W^((sa+1)+2(sb+1)+4(sc+1))`.
-/

open Finset

namespace Squarefree

/-- The `-1/2` edge sum: `Σ_{h=1}^{⌊W^k⌋₊} h^(-1/2) ≤ 2·W^(k·(-1/2+1))` (via
`sum_inv_sqrt_le`). -/
private lemma single_neghalf_le (W : ℝ) (hW : 1 ≤ W) (k : ℕ) :
    (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ (-1/2 : ℝ)))
      ≤ 2 * W ^ ((k : ℝ) * (-1/2 + 1 : ℝ)) := by
  have hW0 : (0:ℝ) < W := lt_of_lt_of_le one_pos hW
  have hrw : (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ (-1/2 : ℝ)))
      = ∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, (1 : ℝ) / Real.sqrt (h : ℝ) := by
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [show (-1/2 : ℝ) = -(1/2) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg h), ← Real.sqrt_eq_rpow, one_div]
  rw [hrw]
  refine (sum_inv_sqrt_le _).trans ?_
  have h1 : Real.sqrt (⌊W ^ k⌋₊ : ℝ) ≤ Real.sqrt (W ^ k) :=
    Real.sqrt_le_sqrt (floor_pow_le W hW k)
  have h2 : Real.sqrt (W ^ k) = W ^ ((k : ℝ) * (-1/2 + 1 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast W k, ← Real.rpow_mul hW0.le]
    norm_num
  rw [← h2]
  linarith

/-- Uniform 1-D edge bound for a signed exponent (`s = -1/2` or `s ≥ 0`):
`Σ_{h=1}^{⌊W^k⌋₊} h^s ≤ 2·W^(k·(s+1))`. -/
private lemma single_signed_le (W : ℝ) (hW : 1 ≤ W) (k : ℕ) {s : ℝ}
    (hs : s = -1/2 ∨ 0 ≤ s) :
    (∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((h : ℝ) ^ s)) ≤ 2 * W ^ ((k : ℝ) * (s + 1)) := by
  have hW0 : (0:ℝ) < W := lt_of_lt_of_le one_pos hW
  rcases hs with hs | hs
  · subst hs; exact single_neghalf_le W hW k
  · have h1 := single_rpow_le W hW k hs
    have h2 : (0:ℝ) < W ^ ((k : ℝ) * (s + 1)) := Real.rpow_pos_of_pos hW0 _
    linarith

/-- Signed-exponent monomial box-sum bound: if every exponent is `-1/2` or nonnegative
and the weighted degree `(sa+1) + 2(sb+1) + 4(sc+1)` is at most `k`, then
`Σ_{box} h₁^sa h₂^sb h₃^sc ≤ 8·W^k`. -/
private lemma box_signed_monomial_le' (W : ℝ) (hW : 1 ≤ W) {sa sb sc k : ℝ}
    (ha : sa = -1/2 ∨ 0 ≤ sa) (hb : sb = -1/2 ∨ 0 ≤ sb) (hc : sc = -1/2 ∨ 0 ≤ sc)
    (hk : (sa + 1) + 2 * (sb + 1) + 4 * (sc + 1) ≤ k) :
    (∑ p ∈ box W, ((p.1 : ℝ) ^ sa * (p.2.1 : ℝ) ^ sb * (p.2.2 : ℝ) ^ sc))
      ≤ 8 * W ^ k := by
  have hW0 : (0:ℝ) < W := lt_of_lt_of_le one_pos hW
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
  have e1 : (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ sa)
      ≤ 2 * W ^ ((1 : ℝ) * (sa + 1)) := by
    have := single_signed_le W hW 1 ha; simpa using this
  have e2 : (∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ sb)
      ≤ 2 * W ^ ((2 : ℝ) * (sb + 1)) := by
    have := single_signed_le W hW 2 hb; simpa using this
  have e3 : (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc)
      ≤ 2 * W ^ ((4 : ℝ) * (sc + 1)) := by
    have := single_signed_le W hW 4 hc; simpa using this
  have hnn1 : (0 : ℝ) ≤ ∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ sa :=
    Finset.sum_nonneg fun h _ => Real.rpow_nonneg (Nat.cast_nonneg h) _
  have hnn3 : (0 : ℝ) ≤ ∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc :=
    Finset.sum_nonneg fun h _ => Real.rpow_nonneg (Nat.cast_nonneg h) _
  calc (∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, (h₁ : ℝ) ^ sa)
        * ((∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, (h₂ : ℝ) ^ sb)
          * (∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, (h₃ : ℝ) ^ sc))
      ≤ (2 * W ^ ((1 : ℝ) * (sa + 1)))
          * ((2 * W ^ ((2 : ℝ) * (sb + 1))) * (2 * W ^ ((4 : ℝ) * (sc + 1)))) := by
        apply mul_le_mul e1 _ (by positivity) (by positivity)
        exact mul_le_mul e2 e3 hnn3 (by positivity)
    _ = 8 * (W ^ ((1 : ℝ) * (sa + 1)) * W ^ ((2 : ℝ) * (sb + 1))
          * W ^ ((4 : ℝ) * (sc + 1))) := by ring_nf
    _ = 8 * W ^ ((sa + 1) + 2 * (sb + 1) + 4 * (sc + 1)) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
        ring_nf
    _ ≤ 8 * W ^ k := by
        have := Real.rpow_le_rpow_of_exponent_le hW hk
        linarith

/-- `x · x^(-1/2) = x^(1/2)` for `x > 0` (atom collapse for the pointwise algebra). -/
private lemma mul_rpow_neghalf_self {x : ℝ} (hx : 0 < x) :
    x * x ^ (-1/2 : ℝ) = x ^ (1/2 : ℝ) := by
  nth_rewrite 1 [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  norm_num

/-- `x⁻¹ ^ (1/2) = x^(-1/2)` for `x ≥ 0`. -/
private lemma inv_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    x⁻¹ ^ (1/2 : ℝ) = x ^ (-1/2 : ℝ) := by
  rw [Real.inv_rpow hx, ← Real.rpow_neg hx]
  norm_num

/-- Coordinates of a box point are positive (as reals). -/
private lemma box_mem_pos {W : ℝ} {p : ℕ × ℕ × ℕ} (hp : p ∈ box W) :
    (0:ℝ) < p.1 ∧ (0:ℝ) < p.2.1 ∧ (0:ℝ) < p.2.2 := by
  have hmem := Finset.mem_product.mp (by rwa [box] at hp)
  have hmem2 := Finset.mem_product.mp hmem.2
  have h1 := (Finset.mem_Icc.mp hmem.1).1
  have h2 := (Finset.mem_Icc.mp hmem2.1).1
  have h3 := (Finset.mem_Icc.mp hmem2.2).1
  exact ⟨Nat.cast_pos.mpr h1, Nat.cast_pos.mpr h2, Nat.cast_pos.mpr h3⟩

/-- The explicit constant in `box_sum_P_neghalf`. -/
noncomputable def C_boxPneghalf : ℝ := 8

/-- Explicit-constant form of `box_sum_P_neghalf` (writeup 1806). -/
theorem box_sum_P_neghalf_explicit : 0 < C_boxPneghalf ∧ C_boxPneghalf ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W, ((Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)))
        ≤ C_boxPneghalf * W ^ (7/2 : ℝ) := by
  unfold C_boxPneghalf
  refine ⟨by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W, ((Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)))
      = ∑ p ∈ box W,
          ((p.1 : ℝ) ^ (-1/2 : ℝ) * (p.2.1 : ℝ) ^ (-1/2 : ℝ) * (p.2.2 : ℝ) ^ (-1/2 : ℝ)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hP : (Pbox p.1 p.2.1 p.2.2 : ℝ) = (p.1 : ℝ) * (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
      simp only [Pbox]; push_cast; ring
    rw [hP, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
  rw [hrw]
  exact box_signed_monomial_le' W hW (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (by norm_num)

/-- `Σ_{box} P^(-1/2) ≤ C·W^(7/2)` (writeup 1806). -/
theorem box_sum_P_neghalf : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W, ((Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ))) ≤ C * W ^ (7/2 : ℝ) :=
  ⟨C_boxPneghalf, box_sum_P_neghalf_explicit⟩

/-- `Σ_{box} S·P^(-1/2) ≤ C·W^(19/2)` (writeup 1807). The three monomials
`(1/2,1/2,-1/2)`, `(1/2,-1/2,1/2)`, `(-1/2,1/2,1/2)` have weighted degrees
`13/2, 17/2, 19/2`. -/
noncomputable def C_boxSPneghalf : ℝ := 24

/-- Explicit-constant form of `box_sum_SP_neghalf` (writeup 1807). -/
theorem box_sum_SP_neghalf_explicit : 0 < C_boxSPneghalf ∧ C_boxSPneghalf ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W,
          ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)))
        ≤ C_boxSPneghalf * W ^ (19/2 : ℝ) := by
  unfold C_boxSPneghalf
  refine ⟨by norm_num, by norm_num, fun W hW => ?_⟩
  have hrw : (∑ p ∈ box W,
        ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)))
      = (∑ p ∈ box W,
          ((p.1 : ℝ) ^ (1/2:ℝ) * (p.2.1 : ℝ) ^ (1/2:ℝ) * (p.2.2 : ℝ) ^ (-1/2:ℝ)))
        + (∑ p ∈ box W,
          ((p.1 : ℝ) ^ (1/2:ℝ) * (p.2.1 : ℝ) ^ (-1/2:ℝ) * (p.2.2 : ℝ) ^ (1/2:ℝ)))
        + (∑ p ∈ box W,
          ((p.1 : ℝ) ^ (-1/2:ℝ) * (p.2.1 : ℝ) ^ (1/2:ℝ) * (p.2.2 : ℝ) ^ (1/2:ℝ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hx, hy, hz⟩ := box_mem_pos hp
    have hS : (Sbox p.1 p.2.1 p.2.2 : ℝ)
        = (p.1 : ℝ) * (p.2.1 : ℝ) + (p.1 : ℝ) * (p.2.2 : ℝ)
          + (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
      simp only [Sbox]; push_cast; ring
    have hP : (Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)
        = (p.1 : ℝ) ^ (-1/2:ℝ) * (p.2.1 : ℝ) ^ (-1/2:ℝ) * (p.2.2 : ℝ) ^ (-1/2:ℝ) := by
      have h : (Pbox p.1 p.2.1 p.2.2 : ℝ) = (p.1 : ℝ) * (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
        simp only [Pbox]; push_cast; ring
      rw [h, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    rw [hS, hP, ← mul_rpow_neghalf_self hx, ← mul_rpow_neghalf_self hy,
      ← mul_rpow_neghalf_self hz]
    ring
  rw [hrw]
  have b1 := box_signed_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (1/2:ℝ)) (sc := (-1/2:ℝ))
    (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inl rfl) (k := (19/2:ℝ)) (by norm_num)
  have b2 := box_signed_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (-1/2:ℝ)) (sc := (1/2:ℝ))
    (Or.inr (by norm_num)) (Or.inl rfl) (Or.inr (by norm_num)) (k := (19/2:ℝ)) (by norm_num)
  have b3 := box_signed_monomial_le' W hW (sa := (-1/2:ℝ)) (sb := (1/2:ℝ)) (sc := (1/2:ℝ))
    (Or.inl rfl) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (k := (19/2:ℝ)) (by norm_num)
  have hC : (24:ℝ) * W ^ (19/2:ℝ)
      = 8 * W ^ (19/2:ℝ) + 8 * W ^ (19/2:ℝ) + 8 * W ^ (19/2:ℝ) := by ring
  rw [hC]
  exact add_le_add (add_le_add b1 b2) b3

/-- `Σ_{box} S·P^(-1/2) ≤ C·W^(19/2)` (writeup 1807). The three monomials
`(1/2,1/2,-1/2)`, `(1/2,-1/2,1/2)`, `(-1/2,1/2,1/2)` have weighted degrees
`13/2, 17/2, 19/2`. -/
theorem box_sum_SP_neghalf : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W,
          ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)))
        ≤ C * W ^ (19/2 : ℝ) :=
  ⟨C_boxSPneghalf, box_sum_SP_neghalf_explicit⟩

/-- `Σ_{box} (S/P)^(1/2) ≤ C·W^(13/2)` (writeup 1810). Pointwise
`S/P = h₁⁻¹ + h₂⁻¹ + h₃⁻¹`, so by subadditivity
`(S/P)^(1/2) ≤ h₁^(-1/2) + h₂^(-1/2) + h₃^(-1/2)` (degrees `13/2, 6, 5`). -/
noncomputable def C_boxSoverPhalf : ℝ := 24

/-- Explicit-constant form of `box_sum_SoverP_half` (writeup 1810). -/
theorem box_sum_SoverP_half_explicit : 0 < C_boxSoverPhalf ∧ C_boxSoverPhalf ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W,
          ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ))
        ≤ C_boxSoverPhalf * W ^ (13/2 : ℝ) := by
  unfold C_boxSoverPhalf
  refine ⟨by norm_num, by norm_num, fun W hW => ?_⟩
  have hpt : ∀ p ∈ box W,
      ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ)
        ≤ (p.1 : ℝ) ^ (-1/2:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ)
          + (p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (-1/2:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ)
          + (p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (-1/2:ℝ) := by
    intro p hp
    obtain ⟨hx, hy, hz⟩ := box_mem_pos hp
    have hSP : (Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)
        = (p.1 : ℝ)⁻¹ + (p.2.1 : ℝ)⁻¹ + (p.2.2 : ℝ)⁻¹ := by
      have hS : (Sbox p.1 p.2.1 p.2.2 : ℝ)
          = (p.1 : ℝ) * (p.2.1 : ℝ) + (p.1 : ℝ) * (p.2.2 : ℝ)
            + (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
        simp only [Sbox]; push_cast; ring
      have hP : (Pbox p.1 p.2.1 p.2.2 : ℝ) = (p.1 : ℝ) * (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
        simp only [Pbox]; push_cast; ring
      rw [hS, hP]
      field_simp
      ring
    have hmono : (p.1 : ℝ) ^ (-1/2:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ)
          + (p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (-1/2:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ)
          + (p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (-1/2:ℝ)
        = ((p.1 : ℝ)⁻¹) ^ (1/2:ℝ) + ((p.2.1 : ℝ)⁻¹) ^ (1/2:ℝ)
          + ((p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ) := by
      rw [inv_rpow_half hx.le, inv_rpow_half hy.le, inv_rpow_half hz.le]
      simp [Real.rpow_zero]
    rw [hSP, hmono]
    calc ((p.1 : ℝ)⁻¹ + (p.2.1 : ℝ)⁻¹ + (p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ)
        ≤ ((p.1 : ℝ)⁻¹ + (p.2.1 : ℝ)⁻¹) ^ (1/2:ℝ) + ((p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ) :=
          Real.rpow_add_le_add_rpow (by positivity) (by positivity)
            (by norm_num) (by norm_num)
      _ ≤ (((p.1 : ℝ)⁻¹) ^ (1/2:ℝ) + ((p.2.1 : ℝ)⁻¹) ^ (1/2:ℝ))
            + ((p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ) := by
          gcongr
          exact Real.rpow_add_le_add_rpow (by positivity) (by positivity)
            (by norm_num) (by norm_num)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have b1 := box_signed_monomial_le' W hW (sa := (-1/2:ℝ)) (sb := (0:ℝ)) (sc := (0:ℝ))
    (Or.inl rfl) (Or.inr le_rfl) (Or.inr le_rfl) (k := (13/2:ℝ)) (by norm_num)
  have b2 := box_signed_monomial_le' W hW (sa := (0:ℝ)) (sb := (-1/2:ℝ)) (sc := (0:ℝ))
    (Or.inr le_rfl) (Or.inl rfl) (Or.inr le_rfl) (k := (13/2:ℝ)) (by norm_num)
  have b3 := box_signed_monomial_le' W hW (sa := (0:ℝ)) (sb := (0:ℝ)) (sc := (-1/2:ℝ))
    (Or.inr le_rfl) (Or.inr le_rfl) (Or.inl rfl) (k := (13/2:ℝ)) (by norm_num)
  have hC : (24:ℝ) * W ^ (13/2:ℝ)
      = 8 * W ^ (13/2:ℝ) + 8 * W ^ (13/2:ℝ) + 8 * W ^ (13/2:ℝ) := by ring
  rw [hC]
  exact add_le_add (add_le_add b1 b2) b3

/-- `Σ_{box} (S/P)^(1/2) ≤ C·W^(13/2)` (writeup 1810). Pointwise
`S/P = h₁⁻¹ + h₂⁻¹ + h₃⁻¹`, so by subadditivity
`(S/P)^(1/2) ≤ h₁^(-1/2) + h₂^(-1/2) + h₃^(-1/2)` (degrees `13/2, 6, 5`). -/
theorem box_sum_SoverP_half : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W,
          ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ))
        ≤ C * W ^ (13/2 : ℝ) :=
  ⟨C_boxSoverPhalf, box_sum_SoverP_half_explicit⟩

/-- `Σ_{box} S·(S/P)^(1/2) ≤ C·W^(25/2)` (writeup 1811). Pointwise
`S·(S/P)^(1/2) ≤ (h₁h₂+h₁h₃+h₂h₃)·(h₁^(-1/2)+h₂^(-1/2)+h₃^(-1/2))`, nine monomials of
weighted degrees `19/2, 9, 8, 23/2, 11, 10, 25/2, 12, 11`. -/
noncomputable def C_boxSSoverPhalf : ℝ := 72

/-- Explicit-constant form of `box_sum_S_SoverP_half` (writeup 1811). -/
theorem box_sum_S_SoverP_half_explicit : 0 < C_boxSSoverPhalf ∧ C_boxSSoverPhalf ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W,
          ((Sbox p.1 p.2.1 p.2.2 : ℝ)
            * ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ)))
        ≤ C_boxSSoverPhalf * W ^ (25/2 : ℝ) := by
  unfold C_boxSSoverPhalf
  refine ⟨by norm_num, by norm_num, fun W hW => ?_⟩
  have hpt : ∀ p ∈ box W,
      ((Sbox p.1 p.2.1 p.2.2 : ℝ)
          * ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ))
        ≤ (p.1 : ℝ) ^ (1/2:ℝ) * (p.2.1 : ℝ) ^ (1:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ)
          + (p.1 : ℝ) ^ (1:ℝ) * (p.2.1 : ℝ) ^ (1/2:ℝ) * (p.2.2 : ℝ) ^ (0:ℝ)
          + (p.1 : ℝ) ^ (1:ℝ) * (p.2.1 : ℝ) ^ (1:ℝ) * (p.2.2 : ℝ) ^ (-1/2:ℝ)
          + (p.1 : ℝ) ^ (1/2:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (1:ℝ)
          + (p.1 : ℝ) ^ (1:ℝ) * (p.2.1 : ℝ) ^ (-1/2:ℝ) * (p.2.2 : ℝ) ^ (1:ℝ)
          + (p.1 : ℝ) ^ (1:ℝ) * (p.2.1 : ℝ) ^ (0:ℝ) * (p.2.2 : ℝ) ^ (1/2:ℝ)
          + (p.1 : ℝ) ^ (-1/2:ℝ) * (p.2.1 : ℝ) ^ (1:ℝ) * (p.2.2 : ℝ) ^ (1:ℝ)
          + (p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (1/2:ℝ) * (p.2.2 : ℝ) ^ (1:ℝ)
          + (p.1 : ℝ) ^ (0:ℝ) * (p.2.1 : ℝ) ^ (1:ℝ) * (p.2.2 : ℝ) ^ (1/2:ℝ) := by
    intro p hp
    obtain ⟨hx, hy, hz⟩ := box_mem_pos hp
    have hS : (Sbox p.1 p.2.1 p.2.2 : ℝ)
        = (p.1 : ℝ) * (p.2.1 : ℝ) + (p.1 : ℝ) * (p.2.2 : ℝ)
          + (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
      simp only [Sbox]; push_cast; ring
    have hhalf : ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ)
        ≤ (p.1 : ℝ) ^ (-1/2:ℝ) + (p.2.1 : ℝ) ^ (-1/2:ℝ) + (p.2.2 : ℝ) ^ (-1/2:ℝ) := by
      have hSP : (Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)
          = (p.1 : ℝ)⁻¹ + (p.2.1 : ℝ)⁻¹ + (p.2.2 : ℝ)⁻¹ := by
        have hP : (Pbox p.1 p.2.1 p.2.2 : ℝ)
            = (p.1 : ℝ) * (p.2.1 : ℝ) * (p.2.2 : ℝ) := by
          simp only [Pbox]; push_cast; ring
        rw [hS, hP]
        field_simp
        ring
      rw [hSP, ← inv_rpow_half hx.le, ← inv_rpow_half hy.le, ← inv_rpow_half hz.le]
      calc ((p.1 : ℝ)⁻¹ + (p.2.1 : ℝ)⁻¹ + (p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ)
          ≤ ((p.1 : ℝ)⁻¹ + (p.2.1 : ℝ)⁻¹) ^ (1/2:ℝ) + ((p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ) :=
            Real.rpow_add_le_add_rpow (by positivity) (by positivity)
              (by norm_num) (by norm_num)
        _ ≤ (((p.1 : ℝ)⁻¹) ^ (1/2:ℝ) + ((p.2.1 : ℝ)⁻¹) ^ (1/2:ℝ))
              + ((p.2.2 : ℝ)⁻¹) ^ (1/2:ℝ) := by
            gcongr
            exact Real.rpow_add_le_add_rpow (by positivity) (by positivity)
              (by norm_num) (by norm_num)
    have hS0 : (0:ℝ) ≤ (Sbox p.1 p.2.1 p.2.2 : ℝ) := Nat.cast_nonneg _
    refine (mul_le_mul_of_nonneg_left hhalf hS0).trans_eq ?_
    rw [hS]
    simp only [Real.rpow_one, Real.rpow_zero]
    rw [← mul_rpow_neghalf_self hx, ← mul_rpow_neghalf_self hy,
      ← mul_rpow_neghalf_self hz]
    ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have m1 := box_signed_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (1:ℝ)) (sc := (0:ℝ))
    (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr le_rfl)
    (k := (25/2:ℝ)) (by norm_num)
  have m2 := box_signed_monomial_le' W hW (sa := (1:ℝ)) (sb := (1/2:ℝ)) (sc := (0:ℝ))
    (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr le_rfl)
    (k := (25/2:ℝ)) (by norm_num)
  have m3 := box_signed_monomial_le' W hW (sa := (1:ℝ)) (sb := (1:ℝ)) (sc := (-1/2:ℝ))
    (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inl rfl)
    (k := (25/2:ℝ)) (by norm_num)
  have m4 := box_signed_monomial_le' W hW (sa := (1/2:ℝ)) (sb := (0:ℝ)) (sc := (1:ℝ))
    (Or.inr (by norm_num)) (Or.inr le_rfl) (Or.inr (by norm_num))
    (k := (25/2:ℝ)) (by norm_num)
  have m5 := box_signed_monomial_le' W hW (sa := (1:ℝ)) (sb := (-1/2:ℝ)) (sc := (1:ℝ))
    (Or.inr (by norm_num)) (Or.inl rfl) (Or.inr (by norm_num))
    (k := (25/2:ℝ)) (by norm_num)
  have m6 := box_signed_monomial_le' W hW (sa := (1:ℝ)) (sb := (0:ℝ)) (sc := (1/2:ℝ))
    (Or.inr (by norm_num)) (Or.inr le_rfl) (Or.inr (by norm_num))
    (k := (25/2:ℝ)) (by norm_num)
  have m7 := box_signed_monomial_le' W hW (sa := (-1/2:ℝ)) (sb := (1:ℝ)) (sc := (1:ℝ))
    (Or.inl rfl) (Or.inr (by norm_num)) (Or.inr (by norm_num))
    (k := (25/2:ℝ)) (by norm_num)
  have m8 := box_signed_monomial_le' W hW (sa := (0:ℝ)) (sb := (1/2:ℝ)) (sc := (1:ℝ))
    (Or.inr le_rfl) (Or.inr (by norm_num)) (Or.inr (by norm_num))
    (k := (25/2:ℝ)) (by norm_num)
  have m9 := box_signed_monomial_le' W hW (sa := (0:ℝ)) (sb := (1:ℝ)) (sc := (1/2:ℝ))
    (Or.inr le_rfl) (Or.inr (by norm_num)) (Or.inr (by norm_num))
    (k := (25/2:ℝ)) (by norm_num)
  have hC : (72:ℝ) * W ^ (25/2:ℝ)
      = 8 * W ^ (25/2:ℝ) + 8 * W ^ (25/2:ℝ) + 8 * W ^ (25/2:ℝ) + 8 * W ^ (25/2:ℝ)
        + 8 * W ^ (25/2:ℝ) + 8 * W ^ (25/2:ℝ) + 8 * W ^ (25/2:ℝ) + 8 * W ^ (25/2:ℝ)
        + 8 * W ^ (25/2:ℝ) := by ring
  rw [hC]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add m1 m2) m3) m4) m5) m6) m7) m8) m9

/-- `Σ_{box} S·(S/P)^(1/2) ≤ C·W^(25/2)` (writeup 1811). Pointwise
`S·(S/P)^(1/2) ≤ (h₁h₂+h₁h₃+h₂h₃)·(h₁^(-1/2)+h₂^(-1/2)+h₃^(-1/2))`, nine monomials of
weighted degrees `19/2, 9, 8, 23/2, 11, 10, 25/2, 12, 11`. -/
theorem box_sum_S_SoverP_half : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ W : ℝ, 1 ≤ W →
      (∑ p ∈ box W,
          ((Sbox p.1 p.2.1 p.2.2 : ℝ)
            * ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ)))
        ≤ C * W ^ (25/2 : ℝ) :=
  ⟨C_boxSSoverPhalf, box_sum_S_SoverP_half_explicit⟩

end Squarefree
