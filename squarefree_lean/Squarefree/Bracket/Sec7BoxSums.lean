import Squarefree.Bracket.BoxNegPowerSums

/-!
# §7 elementary box sums (plan nodes N14, N21)

Bundled statements of the rectangular-shift-box power sums consumed by the §7 harvests
(`Bracket/Sec7Harvest.lean`, nodes N15/N22): the zero-top-carry list (md 1782–1803, N14)
and the nonzero-top-carry list (md 1938–41, N21). The individual monomial bounds live in
`Bracket/BoxPowerSums.lean` and (negative powers) `Bracket/BoxNegPowerSums.lean`, all
with per-entry constants ≤ 100, absorbed here into the pinned `sec7_cBox = 10⁴`.
Sums range over `box W` =
`1 ≤ h₁ ≤ ⌊W⌋, 1 ≤ h₂ ≤ ⌊W²⌋, 1 ≤ h₃ ≤ ⌊W⁴⌋`, with `S = h₁h₂+h₁h₃+h₂h₃`,
`P = h₁h₂h₃`, `hΣ = h₁+h₂+h₃` (defs `Sbox`, `Pbox`, `HSbox`).

AM-6: the box-sum constants are PINNED to `sec7_cBox = 10⁴` (ledger) — all fifteen
entries are crude monomial dominations on the box with small absolute constants
(the `BoxPowerSums` per-entry constants are far below `10⁴`).
-/

open Finset

namespace Squarefree

/-- Pinned uniform constant for the N14/N21 elementary box sums (AM-6; ledger). -/
def sec7_cBox : ℝ := 10 ^ 4

theorem sec7_cBox_pos : (0:ℝ) < sec7_cBox := by norm_num [sec7_cBox]

/-- Absorb a per-entry constant `C ≤ 100` into the pinned `sec7_cBox = 10⁴`. -/
private lemma absorb {x C e : ℝ} (hC : C ≤ 100) (he : 0 ≤ e) (h : x ≤ C * e) :
    x ≤ sec7_cBox * e :=
  h.trans (mul_le_mul_of_nonneg_right (hC.trans (by norm_num [sec7_cBox])) he)

/- md 1782–1803: "The required elementary sums are
   ∑1 ≪ W⁷,  ∑S ≪ W¹³,  ∑S² ≪ W¹⁹,
   ∑P ≪ W¹⁴,  ∑SP ≪ W²⁰,
   ∑P^{−1/2} ≪ W^{7/2},  ∑SP^{−1/2} ≪ W^{19/2},
   ∑(S/P)^{1/2} ≪ W^{13/2},  ∑S(S/P)^{1/2} ≪ W^{25/2},
   ∑h_Σ ≪ W^{11},  ∑Sh_Σ ≪ W^{17},
   where all sums are over 1 ≤ h₁ ≤ ⌊W⌋, 1 ≤ h₂ ≤ ⌊W²⌋, 1 ≤ h₃ ≤ ⌊W⁴⌋." -/
/-- **N14** (md 1782–1803): the eleven zero-top-carry elementary box sums with the one
pinned constant `sec7_cBox`. Entries 1–5, 10–11 are `box_sum_one/_S/_S_sq/_P/_SP/_HS/_S_HS`
(`BoxPowerSums`); entries 6–9 are the four `BoxNegPowerSums` negative-power bounds. -/
theorem sec7_box_sums_zero : ∀ W : ℝ, 1 ≤ W →
    (∑ _p ∈ box W, (1 : ℝ)) ≤ sec7_cBox * W ^ 7 ∧
    (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ)) ≤ sec7_cBox * W ^ 13 ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2)) ≤ sec7_cBox * W ^ 19 ∧
    (∑ p ∈ box W, (Pbox p.1 p.2.1 p.2.2 : ℝ)) ≤ sec7_cBox * W ^ 14 ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ)))
      ≤ sec7_cBox * W ^ 20 ∧
    (∑ p ∈ box W, ((Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ))) ≤ sec7_cBox * W ^ (7/2 : ℝ) ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ)))
      ≤ sec7_cBox * W ^ (19/2 : ℝ) ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ))
      ≤ sec7_cBox * W ^ (13/2 : ℝ) ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ)
        * ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)) ^ (1/2 : ℝ)))
      ≤ sec7_cBox * W ^ (25/2 : ℝ) ∧
    (∑ p ∈ box W, (HSbox p.1 p.2.1 p.2.2 : ℝ)) ≤ sec7_cBox * W ^ 11 ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (HSbox p.1 p.2.1 p.2.2 : ℝ)))
      ≤ sec7_cBox * W ^ 17 := by
  intro W hW
  have hW0 : (0:ℝ) ≤ W := le_trans zero_le_one hW
  obtain ⟨C1, -, hC1, h1⟩ := box_sum_one
  obtain ⟨C2, -, hC2, h2⟩ := box_sum_S
  obtain ⟨C3, -, hC3, h3⟩ := box_sum_S_sq
  obtain ⟨C4, -, hC4, h4⟩ := box_sum_P
  obtain ⟨C5, -, hC5, h5⟩ := box_sum_SP
  obtain ⟨C6, -, hC6, h6⟩ := box_sum_P_neghalf
  obtain ⟨C7, -, hC7, h7⟩ := box_sum_SP_neghalf
  obtain ⟨C8, -, hC8, h8⟩ := box_sum_SoverP_half
  obtain ⟨C9, -, hC9, h9⟩ := box_sum_S_SoverP_half
  obtain ⟨C10, -, hC10, h10⟩ := box_sum_HS
  obtain ⟨C11, -, hC11, h11⟩ := box_sum_S_HS
  exact ⟨absorb hC1 (pow_nonneg hW0 _) (h1 W hW),
    absorb hC2 (pow_nonneg hW0 _) (h2 W hW),
    absorb hC3 (pow_nonneg hW0 _) (h3 W hW),
    absorb hC4 (pow_nonneg hW0 _) (h4 W hW),
    absorb hC5 (pow_nonneg hW0 _) (h5 W hW),
    absorb hC6 (Real.rpow_nonneg hW0 _) (h6 W hW),
    absorb hC7 (Real.rpow_nonneg hW0 _) (h7 W hW),
    absorb hC8 (Real.rpow_nonneg hW0 _) (h8 W hW),
    absorb hC9 (Real.rpow_nonneg hW0 _) (h9 W hW),
    absorb hC10 (pow_nonneg hW0 _) (h10 W hW),
    absorb hC11 (pow_nonneg hW0 _) (h11 W hW)⟩

/- md 1938–41: "Summing (7.8) over the whole rectangular shift box, multiplying by the
   fiber count (7.2), using (7.6), and comparing with the averaged cube lower bound
   ≫ R/W, we use  ∑1 ≪ W⁷,  ∑S ≪ W¹³,  ∑S^{1/2} ≪ W¹⁰,  ∑S^{3/2} ≪ W¹⁶." -/
/-- **N21** (md 1938–41): the four nonzero-top-carry elementary box sums with the one
pinned constant `sec7_cBox` (`box_sum_one/_S/_S_sqrt/_S_thalf`, all proved in
`BoxPowerSums`). -/
theorem sec7_box_sums_nonzero : ∀ W : ℝ, 1 ≤ W →
    (∑ _p ∈ box W, (1 : ℝ)) ≤ sec7_cBox * W ^ 7 ∧
    (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ)) ≤ sec7_cBox * W ^ 13 ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (1/2 : ℝ))) ≤ sec7_cBox * W ^ (10 : ℝ) ∧
    (∑ p ∈ box W, ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (3/2 : ℝ))) ≤ sec7_cBox * W ^ (16 : ℝ) := by
  intro W hW
  have hW0 : (0:ℝ) ≤ W := le_trans zero_le_one hW
  obtain ⟨C1, -, hC1, h1⟩ := box_sum_one
  obtain ⟨C2, -, hC2, h2⟩ := box_sum_S
  obtain ⟨C3, -, hC3, h3⟩ := box_sum_S_sqrt
  obtain ⟨C4, -, hC4, h4⟩ := box_sum_S_thalf
  exact ⟨absorb hC1 (pow_nonneg hW0 _) (h1 W hW),
    absorb hC2 (pow_nonneg hW0 _) (h2 W hW),
    absorb hC3 (Real.rpow_nonneg hW0 _) (h3 W hW),
    absorb hC4 (Real.rpow_nonneg hW0 _) (h4 W hW)⟩

end Squarefree
