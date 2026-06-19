import Squarefree.Lower.DefectScales

/-!
# §5 Proposition 5.1 assembly — foundational scaling helpers (writeup §5 "F")

Low-risk, dependency-light helper lemmas for the final §5 pair-summation assembly:

* `sum_const_pairs` — `Σ_{[1,W]²} c = W²·c` (the constant-sum collapse used inside
  `Ra_card_le`, lifted to a standalone lemma).
* `R_ge_W` — `P.Wval ≤ S.R` in the working regime (from `U_mul_W_le_R` + `U ≥ 1`).
* `markov_discharge` — the popularity hypothesis `#ℛ_a ≥ 68·R/W` discharges the Markov
  "large-gap" term `2(M−m)/W + 2 ≤ ½·#ℛ_a` for the window `m = R/72`, `M = 16R`.
* `band_to_combine` — `1 ≤ G·U³·Ω⁴` ⟹ `1 ≤ G^{1/4}·U^{3/4}·Ω`, the form consumed by
  `step5_combine_core`.
-/

namespace Squarefree

open Finset

variable {P : Globals} {S : Scale P}

/-- **Constant pair-sum collapse.** `Σ_{(p)∈[1,W]²} c = W²·c`. Standalone form of the
computation appearing inside `Ra_card_le` (`RaPartition.lean`). -/
theorem sum_const_pairs (Wnat : ℕ) (c : ℝ) :
    (∑ _p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, c) = (Wnat : ℝ) ^ 2 * c := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have htc : (Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat).card = Wnat ^ 2 := by
    rw [Finset.card_product, Nat.card_Icc]
    have hh : Wnat + 1 - 1 = Wnat := by omega
    rw [hh, pow_two]
  rw [htc]; push_cast; ring

/-- **`W ≤ R` in the working regime.** From `U·W ≤ R` (`U_mul_W_le_R`) and `W ≤ U·W`
(since `U ≥ 1`, `W = G·U⁵ ≥ 0`). -/
theorem R_ge_W (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hΩU : S.Ω ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hU1 : 1 ≤ P.U) (hG1 : 1 ≤ P.G) :
    P.Wval ≤ S.R := by
  have hUW : P.U * P.Wval ≤ S.R := U_mul_W_le_R (S := S) h1 hband hΩU hΔ1 hU1
  have hWnn : 0 ≤ P.Wval := by
    rw [Globals.Wval]; positivity
  have hWUW : P.Wval ≤ P.U * P.Wval := by nlinarith [hWnn, hU1]
  linarith

/-- **Popularity discharges the Markov term (Wnat-route).** With window `m = R/72`, `M = 16R`,
the **constant-1** popularity bound `R/W ≤ #ℛ_a` (the `prop_5_1` hypothesis verbatim), and the
pair-window length `Wnat ≥ 128·W`, the large-gap Markov term obeys
`2(M−m)/Wnat + 2 ≤ ½·#ℛ_a`. Key facts: `2(M−m)/Wnat ≤ 32·R/(128·W) = ¼·(R/W)` and the
constant `+2` is absorbed by `¼·(R/W)` since `R ≥ 8·W`. -/
theorem markov_discharge {Ra : Finset ℕ} {Wnat : ℕ} (hRW : 8 * P.Wval ≤ S.R)
    (hWlo : 128 * P.Wval ≤ (Wnat : ℝ)) (hWpos : 0 < P.Wval)
    (hpop : S.R / P.Wval ≤ (Ra.card : ℝ)) :
    2 * ((16 * S.R) - (1/72) * S.R) / (Wnat : ℝ) + 2 ≤ (Ra.card : ℝ) / 2 := by
  have hRpos : 0 < S.R := by
    unfold Scale.R
    have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos
    positivity
  have hWnatpos : (0 : ℝ) < (Wnat : ℝ) := lt_of_lt_of_le (by positivity) hWlo
  -- `x := R/W ≥ 8`
  have hx8 : (8 : ℝ) ≤ S.R / P.Wval := (le_div_iff₀ hWpos).mpr (by linarith)
  -- `2(M−m)/Wnat ≤ 32R/Wnat`
  have hnum : 2 * ((16 * S.R) - (1/72) * S.R) ≤ 32 * S.R := by nlinarith [hRpos]
  have hstep1 : 2 * ((16 * S.R) - (1/72) * S.R) / (Wnat : ℝ) ≤ 32 * S.R / (Wnat : ℝ) :=
    div_le_div_of_nonneg_right hnum hWnatpos.le
  -- `32R/Wnat ≤ 32R/(128W) = ¼·(R/W)`
  have hstep2 : 32 * S.R / (Wnat : ℝ) ≤ 32 * S.R / (128 * P.Wval) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hWlo
  have hquarter : 32 * S.R / (128 * P.Wval) = (1/4) * (S.R / P.Wval) := by
    field_simp; ring
  -- `¼·x + 2 ≤ ½·x` for `x ≥ 8`, then `x ≤ #ℛ_a`.
  have hfold : (1/4) * (S.R / P.Wval) + 2 ≤ (S.R / P.Wval) / 2 := by linarith [hx8]
  have hhalf : (S.R / P.Wval) / 2 ≤ (Ra.card : ℝ) / 2 := by linarith [hpop]
  calc 2 * ((16 * S.R) - (1/72) * S.R) / (Wnat : ℝ) + 2
      ≤ 32 * S.R / (128 * P.Wval) + 2 := by linarith [hstep1, hstep2]
    _ = (1/4) * (S.R / P.Wval) + 2 := by rw [hquarter]
    _ ≤ (S.R / P.Wval) / 2 := hfold
    _ ≤ (Ra.card : ℝ) / 2 := hhalf

/-- **Band hypothesis to `step5_combine` form.** `1 ≤ G·U³·Ω⁴` ⟹ `1 ≤ G^{1/4}·U^{3/4}·Ω`,
obtained by raising both sides to the `1/4` rpow and collapsing
`(G·U³·Ω⁴)^{1/4} = G^{1/4}·U^{3/4}·Ω`. -/
theorem band_to_combine (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩpos : 0 < S.Ω) :
    1 ≤ P.G ^ ((1 : ℝ) / 4) * P.U ^ ((3 : ℝ) / 4) * S.Ω := by
  have hGnn : (0 : ℝ) ≤ P.G := le_trans zero_le_one hG1
  have hUnn : (0 : ℝ) ≤ P.U := le_trans zero_le_one hU1
  have hΩnn : (0 : ℝ) ≤ S.Ω := le_of_lt hΩpos
  -- Collapse `(G·U³·Ω⁴)^{1/4}` into the target product.
  have hU3 : (P.U ^ 3 : ℝ) ^ ((1 : ℝ) / 4) = P.U ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast P.U 3, ← Real.rpow_mul hUnn]; norm_num
  have hΩ4 : (S.Ω ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = S.Ω := by
    rw [← Real.rpow_natCast S.Ω 4, ← Real.rpow_mul hΩnn]; norm_num
  have hGU3nn : (0 : ℝ) ≤ P.G * P.U ^ 3 := mul_nonneg hGnn (by positivity)
  have hU3nn : (0 : ℝ) ≤ P.U ^ 3 := by positivity
  have hΩ4nn : (0 : ℝ) ≤ S.Ω ^ 4 := by positivity
  have hcollapse :
      (P.G * P.U ^ 3 * S.Ω ^ 4) ^ ((1 : ℝ) / 4)
        = P.G ^ ((1 : ℝ) / 4) * P.U ^ ((3 : ℝ) / 4) * S.Ω := by
    rw [Real.mul_rpow hGU3nn hΩ4nn, Real.mul_rpow hGnn hU3nn, hU3, hΩ4]
  -- `1 ≤ (G·U³·Ω⁴)^{1/4}`.
  have hstep : (1 : ℝ) ≤ (P.G * P.U ^ 3 * S.Ω ^ 4) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hband (by norm_num)
  rw [hcollapse] at hstep
  exact hstep

/-- **Harmless log term is dominated.** `Real.log N + 1 ≤ 2N` for `N ≥ 1`. Lets the Step-3
per-pair `(ρ/κ)(log N + 1)` term be bounded by `(ρ/κ)·2N`, i.e. the `ρN`-scale after the
`ρ/κ·N` comparison. -/
theorem log_absorb (N : ℝ) (hN : 1 ≤ N) : Real.log N + 1 ≤ 2 * N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlog : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos hNpos
  linarith

/-- **Step-3 `f`-cap envelope repackaging.** The admissible-`f` cap `N := ⌈envelope⌉` satisfies
`(N:ℝ) ≤ envelope + 1`; this exposes the `N ≤ envelope + 1` shape as a named lemma for the
assembly, where `envelope = 10³⁰·ℓ₁·(H·G·Ω/Δ³)·V₊ + 10³⁰·(G²·U¹⁵/Ω⁵)` is the
`Qval_abs_le_from_witness` bound. -/
theorem step3_N_bound {ℓ₁ : ℕ} (Vplus : ℝ) (Mbound : ℝ)
    (hM : Mbound ≤ 10 ^ 34 * ((ℓ₁ : ℝ)) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus
      + 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) :
    Mbound + 1 ≤ 10 ^ 34 * (ℓ₁ : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus
      + 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) + 1 := by
  linarith

/-- **Step-3 envelope at `V₊ = V₁`.** Substituting `Vplus := V₁ = (Δ³/H)·U¹⁰/Ω⁶` collapses the
first envelope term to `≍ ℓ₁·G·U¹⁰/Ω⁵`, via
`H·G·Ω/Δ³ · (Δ³/H)·U¹⁰/Ω⁶ = G·U¹⁰/Ω⁵`. Needs `H, Δ, Ω ≠ 0`. -/
theorem step3_N_at_V1 (ℓ₁ : ℝ) :
    10 ^ 34 * ℓ₁ * (P.H * P.G * S.Ω / S.Δ ^ 3) * ((S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6)
      = 10 ^ 34 * ℓ₁ * P.G * P.U ^ 10 / S.Ω ^ 5 := by
  have hH : P.H ≠ 0 := ne_of_gt P.H_pos
  have hΔ : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩ : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  field_simp

end Squarefree
