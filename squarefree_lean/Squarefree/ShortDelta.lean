import Squarefree.Params
import Squarefree.DCard
import Squarefree.ShortDeltaAux
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §2 short-Δ regime: Prop 2.4

Proof of Prop 2.4 from `../explicit_writeup.md` (lines 209–241): for `Δ = D/H ≤ X^{1/100}`,
`#𝒟[D,2D] ≪ H/U`.  This is an application of the 4th-derivative counting lemma
(`Squarefree.Counting.fourthDeriv_count`) to `f = X/x²`, a trivial small-`D` case, and the
`X^{O(u)}` budget arithmetic.  See `math_audit.md` §2 and `Squarefree/ShortDeltaAux.lean`.
-/

open Classical Finset Set Squarefree.Counting Squarefree.ShortDeltaAux Real

namespace Squarefree

set_option maxHeartbeats 1600000 in
/-- **Prop 2.4** (writeup 209–241): `Δ = D/H ≤ X^{1/100}` ⇒ `#𝒟[D,2D] ≪ H/U`. -/
theorem prop_2_4 (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℝ, 0 < D → D ≤ X ^ ((1 - g) / 5) * X ^ (1 / 100 : ℝ) →
        (dCard X (X ^ ((1 - g) / 5)) D : ℝ) ≤ C * X ^ ((1 - g) / 5) / X ^ u := by
  -- choices
  set a : ℝ := (1 - g) / 5 with ha
  have hapos : 0 < a := by
    rw [ha]; have hg1 : g < 1 := by linarith
    linarith
  refine ⟨1 / 200, by norm_num, ?_⟩
  obtain ⟨C₀, hC₀pos, hC₀⟩ := fourthDeriv_count 729 (by norm_num)
  refine ⟨C₀ * (3 + 7 ^ (1 / 8 : ℝ)) + 4, by positivity, 1, ?_⟩
  intro X hX1 D hDpos hDle
  set b : ℝ := a + 1 / 100 with hb
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  -- D ≤ X^b
  have hDb : D ≤ X ^ b := by
    refine le_trans hDle ?_
    rw [hb, Real.rpow_add hX0]
  -- H = X^a
  set H : ℝ := X ^ a with hH
  have hHpos : 0 < H := by rw [hH]; positivity
  have hH1 : 1 ≤ H := by rw [hH]; exact Real.one_le_rpow hX1 hapos.le
  -- exponent budget facts (g < 2/18977, u = 1/200)
  have hg1 : g < 1 := by linarith
  have he1 : b * (7 / 8) ≤ a - 1 / 200 := by rw [hb, ha]; nlinarith [hg, hg']
  have he2 : a * (1 / 8) + b * (3 / 4) ≤ a - 1 / 200 := by rw [hb, ha]; nlinarith [hg, hg']
  have he3 : -(1 / 8) + a * (1 / 8) + b * (11 / 8) ≤ a - 1 / 200 := by
    rw [hb, ha]; nlinarith [hg, hg']
  have he4 : (1 / 15 : ℝ) + b * (3 / 5) ≤ a - 1 / 200 := by rw [hb, ha]; nlinarith [hg, hg']
  -- the four term bounds
  have hT1 := term1_bound (X := X) (D := D) (a := a) (u := 1 / 200) hX1 b hDpos hDb he1
  have hT2 := term2_bound (X := X) (H := H) (D := D) (a := a) (u := 1 / 200) hX1 b hH hDpos hDb he2
  have hT3 := term3_bound (X := X) (H := H) (D := D) (a := a) (u := 1 / 200) hX1 b hH hDpos hDb he3
  have hT4 := term4_bound (X := X) (D := D) (a := a) (u := 1 / 200) hX1 b hDpos hDb he4
  -- `H/X^u ≥ 1` (since a - u ≥ 0) and `≥ 0`
  have hHU : (1 : ℝ) ≤ X ^ a / X ^ (1 / 200 : ℝ) := by
    rw [← Real.rpow_sub hX0]; exact Real.one_le_rpow hX1 (by rw [ha]; nlinarith [hg, hg'])
  have hHUpos : (0 : ℝ) < X ^ a / X ^ (1 / 200 : ℝ) := lt_of_lt_of_le one_pos hHU
  -- case split on δ = H/D² vs 1/4
  by_cases hcase : 1 / 4 ≤ H / D ^ 2
  · -- small D: D ≤ 2√H, dCard ≤ D + 1 ≤ 3√H ≤ 3·X^{a-u}
    have hDsq : D ^ 2 ≤ 4 * H := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < D ^ 2)] at hcase
      linarith [hcase]
    have hD2sqrt : D ≤ 2 * Real.sqrt H := by
      have hsq : D ^ 2 ≤ (2 * Real.sqrt H) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hHpos.le]; linarith [hDsq]
      have h1 : Real.sqrt (D ^ 2) ≤ Real.sqrt ((2 * Real.sqrt H) ^ 2) := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hDpos.le, Real.sqrt_sq (by positivity)] at h1
    -- √H = X^{a/2}, and 3√H ≤ 3 X^{a-u}
    have hsqrtH : Real.sqrt H = X ^ (a / 2 : ℝ) := by
      rw [hH, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
      congr 1; ring
    have hsqrtle : Real.sqrt H ≤ X ^ a / X ^ (1 / 200 : ℝ) := by
      rw [hsqrtH, ← Real.rpow_sub hX0]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by rw [ha]; nlinarith [hg, hg'])
    have hone : (1 : ℝ) ≤ Real.sqrt H := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt hH1
    calc (dCard X H D : ℝ) ≤ D + 1 := dCard_le_card X H D hDpos
      _ ≤ 3 * Real.sqrt H := by linarith [hD2sqrt, hone]
      _ ≤ 3 * (X ^ a / X ^ (1 / 200 : ℝ)) := by linarith [hsqrtle]
      _ ≤ (C₀ * (3 + 7 ^ (1 / 8 : ℝ)) + 4) * (X ^ a / X ^ (1 / 200 : ℝ)) := by
          gcongr
          nlinarith [hC₀pos, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 7) (1 / 8 : ℝ)]
      _ = (C₀ * (3 + 7 ^ (1 / 8 : ℝ)) + 4) * X ^ a / X ^ (1 / 200 : ℝ) := by ring
  · -- large D: δ < 1/4, apply fourthDeriv_count
    rw [not_le] at hcase
    have hδpos : 0 < H / D ^ 2 := by positivity
    -- D > 2√H ≥ 2, so 2 ≤ D
    have hDgt : 2 * Real.sqrt H < D := by
      by_contra hcon; rw [not_lt] at hcon
      have hDsq : D ^ 2 ≤ 4 * H := by nlinarith [Real.sq_sqrt hHpos.le, Real.sqrt_nonneg H, hcon]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < D ^ 2)] at hcase
      nlinarith [hcase, hDsq]
    have hone : (1 : ℝ) ≤ Real.sqrt H := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt hH1
    have hN2 : 2 ≤ D := by nlinarith [hDgt, hone, Real.sqrt_nonneg H]
    set Λ : ℝ := 120 * X / (729 * D ^ 6) with hΛ
    have hΛpos : 0 < Λ := by rw [hΛ]; positivity
    -- apply the counting lemma
    have hcount := hC₀ D Λ (H / D ^ 2) (fcurve X) hN2 hδpos hcase hΛpos
      (contDiffOn_fcurve X D)
      (fun x hx => lambda_le_absDeriv X D hX0 hDpos x hx)
      (fun x hx => absDeriv_le_K_lambda X D hX0 hDpos x hx)
    -- the distInt count
    have hbridge := dCard_le_distCount X H D hDpos hHpos.le
    -- combine: dCard ≤ count + 1 ≤ C₀·(T1+T2+T3+T4) + 1
    have hge1 : (1 : ℝ) ≤ X ^ a / X ^ (1 / 200 : ℝ) := hHU
    -- four term bounds in Λ-form (rewrite Λ back)
    have hT3' : D ^ (7 / 8 : ℝ) * ((H / D ^ 2) / Λ) ^ (1 / 8 : ℝ)
        ≤ 7 ^ (1 / 8 : ℝ) * (X ^ a / X ^ (1 / 200 : ℝ)) := by rw [hΛ]; exact hT3
    have hT4' : Λ ^ (1 / 15 : ℝ) * D ≤ 1 * (X ^ a / X ^ (1 / 200 : ℝ)) := by rw [hΛ]; exact hT4
    rw [one_mul] at hT1 hT2 hT4'
    set U : ℝ := X ^ a / X ^ (1 / 200 : ℝ) with hU
    -- the four-term sum bound
    have hsum : D ^ (7 / 8 : ℝ) + D * (H / D ^ 2) ^ (1 / 8 : ℝ)
          + D ^ (7 / 8 : ℝ) * ((H / D ^ 2) / Λ) ^ (1 / 8 : ℝ) + Λ ^ (1 / 15 : ℝ) * D
        ≤ (3 + 7 ^ (1 / 8 : ℝ)) * U := by
      have h7 : (1 : ℝ) ≤ 7 ^ (1 / 8 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      nlinarith [hT1, hT2, hT3', hT4', hHUpos, h7]
    have hcount' : (((Finset.Ioc ⌊D⌋ ⌊2 * D⌋).filter
            (fun n : ℤ => distInt (fcurve X (n : ℝ)) ≤ H / D ^ 2)).card : ℝ)
        ≤ C₀ * ((3 + 7 ^ (1 / 8 : ℝ)) * U) := by
      refine le_trans hcount ?_
      gcongr
    -- combine
    calc (dCard X H D : ℝ)
        ≤ (((Finset.Ioc ⌊D⌋ ⌊2 * D⌋).filter
            (fun n : ℤ => distInt (fcurve X (n : ℝ)) ≤ H / D ^ 2)).card : ℝ) + 1 := hbridge
      _ ≤ C₀ * ((3 + 7 ^ (1 / 8 : ℝ)) * U) + U := by linarith [hcount', hge1]
      _ = (C₀ * (3 + 7 ^ (1 / 8 : ℝ)) + 1) * U := by ring
      _ ≤ (C₀ * (3 + 7 ^ (1 / 8 : ℝ)) + 4) * U := by
          have h7 : (0 : ℝ) ≤ 7 ^ (1 / 8 : ℝ) := Real.rpow_nonneg (by norm_num) _
          nlinarith [hHUpos, hC₀pos.le, h7]
      _ = (C₀ * (3 + 7 ^ (1 / 8 : ℝ)) + 4) * X ^ a / X ^ (1 / 200 : ℝ) := by rw [hU]; ring

end Squarefree
