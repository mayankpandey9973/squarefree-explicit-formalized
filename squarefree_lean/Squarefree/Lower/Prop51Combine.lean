import Squarefree.Lower.Prop51Scale
import Squarefree.Lower.PairWeightSum
import Squarefree.Lower.Step5Combine
import Squarefree.Lower.RaPartition

/-!
# §5 assembly capstone — pair-sum + combine (writeup 1167–1224)

This module wires the per-pair count bound into Proposition 5.1's 3-term RHS.

`Bcombine` is the per-pair budget reconciled with the LANDED per-range conclusions (R7):
the common `10⁴⁰⁹·(H/Δ)` prefix (the explicit constant `C₀ = 10⁴⁰⁹` dominates the sum of the
Step constants `10¹¹⁵ + 10⁴⁰⁸ + 10²⁵⁸ + 160·10³¹²·C|_{C=10⁵⁷}`, sympy-verified) times the
seven landed monomials in substituted variables `g = G^{1/4}, u = U^{1/4}, dl = √Δ, ω = Ω`:

* `t1 = g¹⁶u⁶⁰/(dl²ω²)` carrying the Step-1 `ℓ`-weight `(1 + GΩ⁵/(ℓ₁ℓ₂(ℓ₂−ℓ₁)))`;
* `t2 = dl⁴g²⁰u¹⁸⁰/(Hω¹⁴)`, `t3 = g²⁰u¹⁴⁰/(dlω⁸)` (Step 2 at `G⁵`);
* `t4′ = dl⁴g³⁰u¹⁹⁰/(Hω⁸)`, `t5′ = g²⁸u¹⁴⁰/(dlω)` (Step 3 landed, payless hHbig-route);
* `t6′ = g⁶⁰u³⁰⁰/(dl²ω¹³)`, `t7′ = dl⁴g⁶⁰u³⁶⁰/(Hω²⁷)` (Step 4 capstone).

`prop51_combine` sums over the `O(W²)` pairs `[1,Wnat]²` with the TWO-SIDED window
`Wval ≤ Wnat ≤ 130·Wval` (the Wnat-route: the exact cast `Wnat = Wval` is unsatisfiable since
`Wval` is generically irrational), splits the `ℓ`-weight (`1/L ≤ 1` on the integer grid),
applies `step5_combine_core` (8 → 3 terms), and folds `Wnat² ≤ 130²·G²U¹⁰`, landing the
faithful `prop_5_1` RHS shape `10⁴¹⁵·(H/Δ)·( G⁹U⁵¹/(√ΔΩ) + G¹⁷U⁸⁵/(ΔΩ¹³)
+ (Δ²/H)·G¹⁷U¹⁰⁰/Ω²⁷ )` (terms 2,3 are the writeup's `U⁸⁵`/`U¹⁰⁰` `G¹⁷`-forms; term 1 is the
W²-fold of the landed `S1 = G⁷U⁴¹/(√ΔΩ)`, matching `prop_5_1`'s `G⁹` exactly).

The per-pair bound is a **hypothesis** here (the four Step per-pair counts feed it in R9).
-/

namespace Squarefree

open Finset

set_option maxHeartbeats 3200000

variable {P : Globals} {S : Scale P}

/-- The per-pair count budget `Bcombine` (writeup lines 1169–1177, landed exponents): the
explicit constant `10⁴⁰⁹` (≥ sum of the landed Step constants) times the common `H/Δ` prefix
times the seven landed monomials, written in substituted variables
`g = G^{1/4}, u = U^{1/4}, dl = √Δ, ω = Ω`; `t1` carries the Step-1 `ℓ`-weight. The four Step
per-pair lemmas (Steps 1–4) must produce a per-pair count `≤ Bcombine`. -/
noncomputable def Bcombine (P : Globals) (S : Scale P) (ℓ₁ ℓ₂ : ℕ) : ℝ :=
  let g := P.G ^ ((1 : ℝ) / 4)
  let u := P.U ^ ((1 : ℝ) / 4)
  let dl := S.Δ ^ ((1 : ℝ) / 2)
  let ω := S.Ω
  10 ^ 409 * (P.H / S.Δ) *
    ( g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
        * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
      + dl ^ 4 * g ^ 20 * u ^ 180 / (P.H * ω ^ 14)
      + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
      + dl ^ 4 * g ^ 30 * u ^ 190 / (P.H * ω ^ 8)
      + g ^ 28 * u ^ 140 / (dl * ω)
      + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
      + dl ^ 4 * g ^ 60 * u ^ 360 / (P.H * ω ^ 27) )

/-- **§5 capstone wiring.** From a per-pair count bound `B ℓ₁ ℓ₂ ≤ Bcombine P S ℓ₁ ℓ₂` (the
seven landed monomials with the `10⁴⁰⁹·H/Δ` prefix), the pair-sum `2·Σ_{[1,Wnat]²} B` over the
two-sided window `Wval ≤ Wnat ≤ 130·Wval` is bounded by the `prop_5_1` 3-term RHS. The `W²`
factor is `Wnat² ≤ 130²·(G·U⁵)² = 16900·G²·U¹⁰`; the sharp Step-4 monomials give
`S2,S3 = G¹⁵·…`, so `G²·G¹⁵ = G¹⁷` lands the prop's `G¹⁷` exactly. -/
theorem prop51_combine
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Wnat : ℕ) (hWcast : P.Wval ≤ (Wnat : ℝ) ∧ (Wnat : ℝ) ≤ 130 * P.Wval)
    (B : ℕ → ℕ → ℝ)
    (hBle : ∀ ℓ₁ ℓ₂, 0 < ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ Wnat → B ℓ₁ ℓ₂ ≤ Bcombine P S ℓ₁ ℓ₂)
    (hB0 : ∀ ℓ₁ ℓ₂, ¬(0 < ℓ₁ ∧ ℓ₁ < ℓ₂ ∧ ℓ₂ ≤ Wnat) → B ℓ₁ ℓ₂ = 0) :
    2 * (∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2)
      ≤ 10 ^ 415 * (P.H / S.Δ) *
        ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
        + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
        + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 ) := by
  -- positivity facts
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  -- substituted variables
  set g := P.G ^ ((1 : ℝ) / 4) with hgdef
  set u := P.U ^ ((1 : ℝ) / 4) with hudef
  set dl := S.Δ ^ ((1 : ℝ) / 2) with hdldef
  set ω := S.Ω with hωdef
  have hg0 : 0 < g := by rw [hgdef]; exact Real.rpow_pos_of_pos hGpos _
  have hu0 : 0 < u := by rw [hudef]; exact Real.rpow_pos_of_pos hUpos _
  have hdl0 : 0 < dl := by rw [hdldef]; exact Real.rpow_pos_of_pos hΔpos _
  have hω0 : 0 < ω := hΩpos
  have hg1 : 1 ≤ g := by rw [hgdef]; exact Real.one_le_rpow hG1 (by norm_num)
  have hu1 : 1 ≤ u := by rw [hudef]; exact Real.one_le_rpow hU1 (by norm_num)
  -- `g^4 = G`, `u^4 = U`, `dl^2 = Δ`
  have hg4 : g ^ 4 = P.G := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hGpos.le]; norm_num
  have hu4 : u ^ 4 = P.U := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hUpos.le]; norm_num
  have hdl2 : dl ^ 2 = S.Δ := by
    rw [hdldef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hΔpos.le]; norm_num
  -- `ω ≤ u^4` : `Ω ≤ U = u^4`
  have hΩu4 : ω ≤ u ^ 4 := by rw [hu4]; exact hΩU
  -- `hΔ : g^4 * u^10 ≤ dl` (combine form), from `G²U⁵ ≤ Δ`.
  have hΔ : g ^ 4 * u ^ 10 ≤ dl := by
    have hlhsnn : (0 : ℝ) ≤ g ^ 4 * u ^ 10 := by positivity
    have hsq : (g ^ 4 * u ^ 10) ^ 2 ≤ dl ^ 2 := by
      have e1 : (g ^ 4 * u ^ 10) ^ 2 = (g ^ 4) ^ 2 * (u ^ 4) ^ 5 := by ring
      rw [e1, hg4, hu4, hdl2]; exact hΔreg
    nlinarith [hsq, hlhsnn, hdl0.le, hlhsnn]
  -- band → combine form `1 ≤ g * u^3 * ω`
  have hband' : 1 ≤ g * u ^ 3 * ω := by
    have hbtc := band_to_combine (P := P) (S := S) hband hG1 hU1 hΩpos
    have hu3 : u ^ 3 = P.U ^ ((3 : ℝ) / 4) := by
      rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 3, ← Real.rpow_mul hUpos.le]; norm_num
    rw [hgdef, hu3, hωdef]; exact hbtc
  -- the 8-term core bracket `L` (ℓ-free)
  set L : ℝ := g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
    + g ^ 20 * u ^ 60 * ω ^ 3 / dl ^ 2
    + dl ^ 4 * g ^ 20 * u ^ 180 / (P.H * ω ^ 14)
    + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
    + dl ^ 4 * g ^ 30 * u ^ 190 / (P.H * ω ^ 8)
    + g ^ 28 * u ^ 140 / (dl * ω)
    + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
    + dl ^ 4 * g ^ 60 * u ^ 360 / (P.H * ω ^ 27) with hLdef
  set RHS3 : ℝ := g ^ 28 * u ^ 164 / (dl * ω)
    + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
    + dl ^ 4 * g ^ 60 * u ^ 360 / (P.H * ω ^ 27) with hRHS3def
  -- nonnegativity
  have hHΔnn : 0 ≤ P.H / S.Δ := by positivity
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  have hRHS3nn : 0 ≤ RHS3 := by rw [hRHS3def]; positivity
  -- ===== pointwise: `Bcombine ℓ₁ ℓ₂ ≤ 10⁴⁰⁹·((H/Δ)·L)` on the grid (ℓ₁,ℓ₂ ≥ 1) =====
  have hBpt : ∀ ℓ₁ ℓ₂ : ℕ, 1 ≤ ℓ₁ → 1 ≤ ℓ₂ →
      Bcombine P S ℓ₁ ℓ₂ ≤ 10 ^ 409 * ((P.H / S.Δ) * L) := by
    intro ℓ₁ ℓ₂ h1 h2
    have hBeq : Bcombine P S ℓ₁ ℓ₂ = 10 ^ 409 * (P.H / S.Δ) *
        ( g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
            * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
          + dl ^ 4 * g ^ 20 * u ^ 180 / (P.H * ω ^ 14)
          + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
          + dl ^ 4 * g ^ 30 * u ^ 190 / (P.H * ω ^ 8)
          + g ^ 28 * u ^ 140 / (dl * ω)
          + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
          + dl ^ 4 * g ^ 60 * u ^ 360 / (P.H * ω ^ 27) ) := rfl
    rw [hBeq]
    -- the ℓ-weight collapse: `GΩ⁵/L_ℓ ≤ GΩ⁵` on the integer grid
    have hGΩnn : (0 : ℝ) ≤ P.G * S.Ω ^ 5 := by positivity
    have hwle : P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)))
        ≤ P.G * S.Ω ^ 5 := by
      set Lp : ℝ := (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) with hLp
      rcases le_or_gt 1 Lp with h1L | hL1
      · exact div_le_self hGΩnn h1L
      · -- `Lp < 1` forces `Lp ≤ 0` on the integer grid
        have h1' : (1 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast h1
        have h2' : (1 : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast h2
        have hL0 : Lp ≤ 0 := by
          by_contra hpos
          push_neg at hpos
          have hprodpos : (0 : ℝ) < (ℓ₁ : ℝ) * (ℓ₂ : ℝ) := by nlinarith
          have hdiffpos : (0 : ℝ) < (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by
            by_contra hd
            push_neg at hd
            have : Lp ≤ 0 := by rw [hLp]; exact mul_nonpos_of_nonneg_of_nonpos hprodpos.le hd
            linarith
          have h12 : ℓ₁ < ℓ₂ := by exact_mod_cast (by linarith : (ℓ₁ : ℝ) < (ℓ₂ : ℝ))
          have h12' : ((ℓ₁ + 1 : ℕ) : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast h12
          have hd1 : (1 : ℝ) ≤ (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by push_cast at h12'; linarith
          have : (1 : ℝ) ≤ Lp := by rw [hLp]; nlinarith
          linarith
        calc P.G * S.Ω ^ 5 / Lp ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨hGΩnn, hL0⟩)
          _ ≤ P.G * S.Ω ^ 5 := hGΩnn
    -- `t1·(GΩ⁵) = t1b` exactly
    have ht1b : g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2) * (P.G * S.Ω ^ 5)
        = g ^ 20 * u ^ 60 * ω ^ 3 / dl ^ 2 := by
      rw [← hg4, hωdef]
      have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
      have hdlne : dl ≠ 0 := ne_of_gt hdl0
      field_simp
    have ht1pos : (0 : ℝ) ≤ g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2) := by positivity
    have hsplit : g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
          * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
        ≤ g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2) + g ^ 20 * u ^ 60 * ω ^ 3 / dl ^ 2 := by
      have hmul : g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
            * (P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
          ≤ g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2) * (P.G * S.Ω ^ 5) :=
        mul_le_mul_of_nonneg_left hwle ht1pos
      nlinarith [hmul, ht1b]
    have hbr : g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
            * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
          + dl ^ 4 * g ^ 20 * u ^ 180 / (P.H * ω ^ 14)
          + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
          + dl ^ 4 * g ^ 30 * u ^ 190 / (P.H * ω ^ 8)
          + g ^ 28 * u ^ 140 / (dl * ω)
          + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
          + dl ^ 4 * g ^ 60 * u ^ 360 / (P.H * ω ^ 27) ≤ L := by
      rw [hLdef]; linarith [hsplit]
    calc 10 ^ 409 * (P.H / S.Δ) *
        ( g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
            * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
          + dl ^ 4 * g ^ 20 * u ^ 180 / (P.H * ω ^ 14)
          + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
          + dl ^ 4 * g ^ 30 * u ^ 190 / (P.H * ω ^ 8)
          + g ^ 28 * u ^ 140 / (dl * ω)
          + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
          + dl ^ 4 * g ^ 60 * u ^ 360 / (P.H * ω ^ 27) )
        ≤ 10 ^ 409 * (P.H / S.Δ) * L := by
          apply mul_le_mul_of_nonneg_left hbr (by positivity)
      _ = 10 ^ 409 * ((P.H / S.Δ) * L) := by ring
  -- ===== `Σ B ≤ Wnat²·(10⁴⁰⁹·(H/Δ)·L)` =====
  have hsumB : (∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2)
      ≤ (Wnat : ℝ) ^ 2 * (10 ^ 409 * ((P.H / S.Δ) * L)) := by
    have hle : (∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2)
        ≤ (∑ _p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, 10 ^ 409 * ((P.H / S.Δ) * L)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have h1 := (Finset.mem_Icc.mp hp1).1
      have h2 := (Finset.mem_Icc.mp hp2).1
      by_cases hgood : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ Wnat
      · exact le_trans (hBle p.1 p.2 hgood.1 hgood.2.1 hgood.2.2) (hBpt p.1 p.2 h1 h2)
      · rw [hB0 p.1 p.2 hgood]
        exact mul_nonneg (by positivity) (mul_nonneg hHΔnn hLnn)
    rw [sum_const_pairs] at hle
    exact hle
  -- ===== core collapse + W²-fold =====
  have hcore := step5_combine_core g u dl ω P.H hg0 hu0 hdl0 hω0 hHpos hg1 hu1 hΩu4 hband' hΔ
  have hWsq_nn : 0 ≤ (Wnat : ℝ) ^ 2 := by positivity
  have hstep1 : 2 * (∑ p ∈ Finset.Icc 1 Wnat ×ˢ Finset.Icc 1 Wnat, B p.1 p.2)
      ≤ 6 * 10 ^ 409 * ((Wnat : ℝ) ^ 2 * ((P.H / S.Δ) * RHS3)) := by
    have hLR : (P.H / S.Δ) * L ≤ (P.H / S.Δ) * (3 * RHS3) :=
      mul_le_mul_of_nonneg_left hcore hHΔnn
    have hWLR : (Wnat : ℝ) ^ 2 * (10 ^ 409 * ((P.H / S.Δ) * L))
        ≤ (Wnat : ℝ) ^ 2 * (10 ^ 409 * ((P.H / S.Δ) * (3 * RHS3))) := by
      apply mul_le_mul_of_nonneg_left _ hWsq_nn
      apply mul_le_mul_of_nonneg_left hLR (by positivity)
    nlinarith [hsumB, hWLR]
  refine le_trans hstep1 ?_
  -- `Wnat² ≤ 130²·Wval² = 16900·G²U¹⁰`
  have hW2 : (Wnat : ℝ) ^ 2 ≤ 16900 * (P.G ^ 2 * P.U ^ 10) := by
    have hWnn : (0 : ℝ) ≤ (Wnat : ℝ) := Nat.cast_nonneg _
    have h130 : (Wnat : ℝ) ^ 2 ≤ (130 * P.Wval) ^ 2 := pow_le_pow_left₀ hWnn hWcast.2 2
    have he : (130 * P.Wval) ^ 2 = 16900 * (P.G ^ 2 * P.U ^ 10) := by
      rw [Globals.Wval]; ring
    linarith
  -- rpow translations of the three RHS3 monomials
  have hg28 : g ^ 28 = P.G ^ 7 := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 28, ← Real.rpow_mul hGpos.le,
      show ((1:ℝ)/4) * (28 : ℕ) = (7 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have hg60 : g ^ 60 = P.G ^ 15 := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 60, ← Real.rpow_mul hGpos.le,
      show ((1:ℝ)/4) * (60 : ℕ) = (15 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have hu164 : u ^ 164 = P.U ^ 41 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 164, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (164 : ℕ) = (41 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have hu300 : u ^ 300 = P.U ^ 75 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 300, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (300 : ℕ) = (75 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have hu360 : u ^ 360 = P.U ^ 90 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 360, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (360 : ℕ) = (90 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have hdleq : dl = S.Δ ^ (1/2 : ℝ) := hdldef
  have hdl4 : dl ^ 4 = S.Δ ^ 2 := by
    rw [hdldef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 4, ← Real.rpow_mul hΔpos.le,
      show ((1:ℝ)/2) * (4 : ℕ) = (2 : ℕ) by push_cast; ring, Real.rpow_natCast]
  -- RHS3 in `G,U,Δ,Ω`.  Rewrite `dl^4`,`dl^2` (compound) before the bare `dl`.
  have hRHS3_GU : RHS3 = P.G ^ 7 * P.U ^ 41 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
      + P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
      + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) := by
    rw [hRHS3def, hg28, hg60, hu164, hu300, hu360, hωdef, hdl4, hdl2, hdleq]
  rw [hRHS3_GU]
  -- abbreviate the translated `(H/Δ)·RHS3` body
  set X : ℝ := (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 41 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
      + P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
      + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)) with hXdef
  have hXnn : 0 ≤ X := by rw [hXdef]; positivity
  -- per-term translations (fold `G²U¹⁰`)
  have hΔ12pos : (0 : ℝ) < S.Δ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hΔpos _
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hd12ne : S.Δ ^ (1/2 : ℝ) ≠ 0 := ne_of_gt hΔ12pos
  have ht1 : P.G ^ 2 * P.U ^ 10 * ((P.H / S.Δ) * (P.G ^ 7 * P.U ^ 41 / (S.Δ ^ (1/2 : ℝ) * S.Ω)))
      = (P.H / S.Δ) * (P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)) := by
    field_simp
  have ht2 : P.G ^ 2 * P.U ^ 10 * ((P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
      = (P.H / S.Δ) * (P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)) := by
    field_simp
  have ht3 : P.G ^ 2 * P.U ^ 10
        * ((P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
      = (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27) := by
    field_simp
  have hbody : P.G ^ 2 * P.U ^ 10 * X
      = (P.H / S.Δ) * ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
        + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
        + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 ) := by
    have e1 : P.G ^ 2 * P.U ^ 10 * X
        = P.G ^ 2 * P.U ^ 10 * ((P.H / S.Δ) * (P.G ^ 7 * P.U ^ 41 / (S.Δ ^ (1/2 : ℝ) * S.Ω)))
          + P.G ^ 2 * P.U ^ 10 * ((P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
          + P.G ^ 2 * P.U ^ 10
            * ((P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27))) := by
      rw [hXdef]; ring
    rw [e1, ht1, ht2, ht3]; ring
  have hbodynn : 0 ≤ (P.H / S.Δ) * ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
      + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
      + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 ) := by positivity
  -- the constant absorb `101400·10⁴⁰⁹ ≤ 10⁴¹⁵`
  have hconst : (101400 : ℝ) * 10 ^ 409 ≤ 10 ^ 415 := by
    have h6 : (101400 : ℝ) ≤ 10 ^ 6 := by norm_num
    have hp : (10 : ℝ) ^ 6 * 10 ^ 409 = 10 ^ 415 := by rw [← pow_add]
    calc (101400 : ℝ) * 10 ^ 409 ≤ 10 ^ 6 * 10 ^ 409 :=
          mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = 10 ^ 415 := hp
  -- assemble
  have hW2X : (Wnat : ℝ) ^ 2 * X ≤ 16900 * (P.G ^ 2 * P.U ^ 10) * X :=
    mul_le_mul_of_nonneg_right hW2 hXnn
  calc 6 * 10 ^ 409 * ((Wnat : ℝ) ^ 2 * X)
      ≤ 6 * 10 ^ 409 * (16900 * (P.G ^ 2 * P.U ^ 10) * X) := by
        apply mul_le_mul_of_nonneg_left hW2X (by positivity)
    _ = 101400 * 10 ^ 409 * (P.G ^ 2 * P.U ^ 10 * X) := by ring
    _ = 101400 * 10 ^ 409 * ((P.H / S.Δ)
        * ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
          + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
          + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 )) := by rw [hbody]
    _ ≤ 10 ^ 415 * ((P.H / S.Δ)
        * ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
          + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
          + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 )) :=
        mul_le_mul_of_nonneg_right hconst hbodynn
    _ = 10 ^ 415 * (P.H / S.Δ)
        * ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
          + P.G ^ 17 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
          + (S.Δ ^ 2 / P.H) * (P.G ^ 17 * P.U ^ 100) / S.Ω ^ 27 ) := by ring

end Squarefree
