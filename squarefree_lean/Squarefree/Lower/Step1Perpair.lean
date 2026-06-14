import Squarefree.Lower.Step1Model
import Squarefree.Lower.CountTrivial
import Squarefree.Lower.DefectScales

/-!
# §5 Step-1 v=0 per-pair bound (writeup 681–846)

`Ra_step1_v0_perpair` converts the messy product bound of `Ra_step1_v0_count`
(in `Squarefree.Lower.Step1Model`) into the clean per-pair form

  `#F ≤ 10^55 · Rδ · (1 + GΩ⁵ / (ℓ₁ℓ₂(ℓ₂−ℓ₁)))`,

where `Rδ = S.R · δ` and `δ = 10^60 · (1/Δ) · G³U¹⁵/Ω⁵`. This is the shape consumed by
the §5 pair-summation assembly.

The proof case-splits on `δ < 1` (trivial interval count) vs `1 ≤ δ` (product bound),
after establishing the absorption fact `Lnum/(GΩ⁵) ≤ Rδ`.
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **Step-1 v=0 per-pair bound for the concrete triple set.** -/
theorem Ra_step1_v0_perpair {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U) (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        (ℓ₁ : ℤ) * (dStar (r + ℓ₂) - dStar r) = (ℓ₂ : ℤ) * (dStar (r + ℓ₁) - dStar r))).card : ℝ)
      ≤ (10:ℝ)^55 * (S.R * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5)))
          * (1 + P.G * S.Ω^5 / (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)))) := by
  -- abbreviations matching the statement
  set Lnum : ℝ := ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) with hLnum
  set δ : ℝ := (10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5) with hδdef
  set Rδ : ℝ := S.R * δ with hRδdef
  -- the filter set
  set F : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        (ℓ₁ : ℤ) * (dStar (r + ℓ₂) - dStar r) = (ℓ₂ : ℤ) * (dStar (r + ℓ₁) - dStar r)) with hF
  -- positivity facts
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  -- cast facts for ℓ₁ ≤ ℓ₂
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : (1 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_trans hℓ1R hℓ12R.le
  -- Lnum > 0
  have hLnum_pos : 0 < Lnum := by
    rw [hLnum]
    have hdiff : (0:ℝ) < ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by linarith
    have hℓ1pos : (0:ℝ) < ((ℓ₁:ℤ):ℝ) := by linarith
    have hℓ2pos : (0:ℝ) < ((ℓ₂:ℤ):ℝ) := by linarith
    positivity
  -- S.R > 0
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  -- δ > 0
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  -- Rδ > 0
  have hRδpos : 0 < Rδ := by rw [hRδdef]; positivity
  -- 1 ≤ S.R : from U·Wval ≤ R and U·Wval ≥ 1
  have hWval_ge1 : (1:ℝ) ≤ P.Wval := by
    rw [Globals.Wval]
    have : (1:ℝ) ≤ P.U ^ 5 := one_le_pow₀ hU1
    nlinarith [hG1, this]
  have hR1 : (1:ℝ) ≤ S.R := by
    have hUW := U_mul_W_le_R (P := P) (S := S) h1 hband hΩU hΔ1 hU1
    have : (1:ℝ) ≤ P.U * P.Wval := by nlinarith [hU1, hWval_ge1]
    linarith
  -- 1 ≤ Rδ.  Rδ = S.R*δ = 10^60 * (H/Δ²) * G^4 * U^15 / Ω^2 ≥ 10^60 * G^5 * U^23 ≥ 1.
  have hRδ1 : (1:ℝ) ≤ Rδ := by
    rw [hRδdef, hδdef]
    -- closed form: S.R * (10^60 * ((1/Δ) G^3 U^15 / Ω^5))
    --             = 10^60 * H * G^4 * U^15 / (Δ^2 * Ω^2)
    have hform : S.R * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5))
        = (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15 / S.Ω^2 := by
      unfold Scale.R
      field_simp
    rw [hform]
    -- lower bound: H/Δ² ≥ G U^10, Ω² ≤ U², so /Ω² ≥ /U²
    have hΩ2U2 : S.Ω ^ 2 ≤ P.U ^ 2 := by nlinarith [hΩpos, hΩU]
    have hGU : P.G * P.U ^ 10 ≤ P.H / S.Δ^2 := h1
    -- 10^60 * (H/Δ²) G^4 U^15 / Ω² ≥ 10^60 * (G U^10) G^4 U^15 / U² = 10^60 G^5 U^23
    have hbase : (1:ℝ) ≤ (10:ℝ)^60 * P.G^5 * P.U^23 := by
      have hG5 : (1:ℝ) ≤ P.G ^ 5 := one_le_pow₀ hG1
      have hU23 : (1:ℝ) ≤ P.U ^ 23 := one_le_pow₀ hU1
      nlinarith [hG5, hU23]
    -- monotonicity: replace H/Δ² by G U^10 (lower), Ω² by U² (upper)
    have hHpos' : (0:ℝ) < P.H / S.Δ^2 := by positivity
    have step : (10:ℝ)^60 * P.G^5 * P.U^23
        ≤ (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15 / S.Ω^2 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < S.Ω^2)]
      -- want: 10^60 G^5 U^23 * Ω² ≤ 10^60 (H/Δ²) G^4 U^15
      -- since Ω² ≤ U² and H/Δ² ≥ G U^10:
      have ha : (10:ℝ)^60 * P.G^5 * P.U^23 * S.Ω^2
          ≤ (10:ℝ)^60 * P.G^5 * P.U^23 * P.U^2 := by
        apply mul_le_mul_of_nonneg_left hΩ2U2 (by positivity)
      have hb : (10:ℝ)^60 * P.G^5 * P.U^23 * P.U^2
          ≤ (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15 := by
        have : (10:ℝ)^60 * P.G^5 * P.U^23 * P.U^2
            = (10:ℝ)^60 * P.G^4 * P.U^15 * (P.G * P.U^10) := by ring
        rw [this]
        have : (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15
            = (10:ℝ)^60 * P.G^4 * P.U^15 * (P.H / S.Δ^2) := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_left hGU (by positivity)
      linarith
    linarith
  -- Absorption: Lnum / (G Ω⁵) ≤ Rδ.
  have hL_le_Rδ : Lnum / (P.G * S.Ω ^ 5) ≤ Rδ := by
    -- Lnum ≤ Wval³
    have hℓ1pos : (0:ℝ) < ((ℓ₁:ℤ):ℝ) := by linarith
    have hℓ2pos : (0:ℝ) < ((ℓ₂:ℤ):ℝ) := by linarith
    have hℓ1W : ((ℓ₁:ℤ):ℝ) ≤ 130 * P.Wval := le_trans hℓ12R.le hℓ2W
    have hdiffW : ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) ≤ 130 * P.Wval := by linarith [hℓ2W, hℓ1pos]
    have hLW : Lnum ≤ 2197000 * P.Wval ^ 3 := by
      rw [hLnum]
      have hd0 : (0:ℝ) ≤ ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by linarith
      have hWpos : (0:ℝ) < P.Wval := lt_of_lt_of_le one_pos hWval_ge1
      have hW130 : (0:ℝ) ≤ 130 * P.Wval := by linarith [hWpos]
      calc ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
          ≤ (130 * P.Wval) * (130 * P.Wval) * (130 * P.Wval) := by
            apply mul_le_mul (mul_le_mul hℓ1W hℓ2W hℓ2pos.le hW130) hdiffW hd0
            positivity
        _ = 2197000 * P.Wval ^ 3 := by ring
    -- Wval³/(G Ω⁵) = G² U^15 / Ω⁵
    have hWval3 : P.Wval ^ 3 / (P.G * S.Ω ^ 5) = P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 := by
      rw [Globals.Wval]
      field_simp
    -- G² U^15 / Ω⁵ ≤ Rδ
    have hGUΩ_le_Rδ : 2197000 * (P.G ^ 2 * P.U ^ 15) / S.Ω ^ 5 ≤ Rδ := by
      rw [hRδdef, hδdef]
      -- Rδ = 10^60 H G^4 U^15 / (Δ² Ω²); want G² U^15 / Ω⁵ ≤ that
      have hform : S.R * ((10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5))
          = (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15 / S.Ω^2 := by
        unfold Scale.R
        field_simp
      rw [hform]
      -- clear denominators: multiply by Ω⁵ Ω²... use div_le_div form via le_div_iff
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- G² U^15 * (10^60 (H/Δ²) G^4 U^15 ... ) — easier: cross multiply
      -- LHS denominator Ω⁵, RHS denominator Ω²
      -- (G² U^15) * Ω² ≤ (10^60 (H/Δ²) G^4 U^15) * Ω⁵
      -- ⟺ G² U^15 Ω² ≤ 10^60 (H/Δ²) G^4 U^15 Ω⁵   (after grouping)
      -- divide both by U^15 (keep): need G² Ω² ≤ 10^60 (H/Δ²) G^4 Ω⁵
      -- i.e. Δ² ≤ 10^60 H G² Ω³ (using H/Δ² and dividing). We show via nlinarith.
      -- From h1: G U^10 ≤ H/Δ², i.e. G U^10 Δ² ≤ H.
      have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
        (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
      -- band lower bound on Ω: from hband, 1 ≤ G U³ Ω⁴, and Ω ≤ U ⟹ 10^60 G² U^6 ≤ 10^60 G³ U^10 Ω³
      -- Key sufficient fact: 1 ≤ 10^60 * G^2 * U^6   (true since G,U ≥ 1)
      -- and the band gives Ω³ * (G U^4) ≥ 1 hence enough slack.
      -- We aim to prove cross-multiplied inequality by nlinarith with positivity facts.
      -- First express target after rw div_le_div_iff:
      --   P.G^2 * P.U^15 * ((10:ℝ)^60 ... denominator? ) -- let nlinarith handle.
      -- band: Ω⁴ ≥ 1/(G U³), and Ω ≤ U ⟹ Ω³ ≥ 1/(G U⁴) (Ω³ = Ω⁴/Ω ≥ Ω⁴/U).
      have hΩ4 : (1:ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
      -- Ω³ * U ≥ Ω⁴  (since Ω ≤ U): Ω⁴ = Ω³ Ω ≤ Ω³ U
      have hΩ3U : S.Ω ^ 4 ≤ S.Ω ^ 3 * P.U := by
        have : S.Ω ^ 4 = S.Ω ^ 3 * S.Ω := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hΩU (by positivity)
      -- so G U³ * Ω³ U ≥ G U³ Ω⁴ ≥ 1, i.e. G U^4 Ω³ ≥ 1
      have hGU4Ω3 : (1:ℝ) ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := by
        have hchain : P.G * P.U ^ 3 * S.Ω ^ 4 ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := by
          have hrw : P.G * P.U ^ 4 * S.Ω ^ 3 = (P.G * P.U ^ 3 * S.Ω ^ 3) * P.U := by ring
          have hrw2 : P.G * P.U ^ 3 * S.Ω ^ 4 = (P.G * P.U ^ 3 * S.Ω ^ 3) * S.Ω := by ring
          rw [hrw, hrw2]
          exact mul_le_mul_of_nonneg_left hΩU (by positivity)
        linarith [hΩ4, hchain]
      -- Now cross-multiplied goal. Provide the algebraic identity helpers via nlinarith.
      -- target (after div_le_div_iff): P.G^2*P.U^15 * Ω² ≤ (10^60 (H/Δ²) G^4 U^15) * Ω⁵
      -- Substitute H ≥ G U^10 Δ², so 10^60 (H/Δ²) ≥ 10^60 G U^10.
      have hHΔ : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2 := h1
      -- RHS ≥ 10^60 * (G U^10) * G^4 U^15 * Ω⁵ = 10^60 G^5 U^25 Ω⁵
      -- LHS = G² U^15 Ω². Need G² U^15 Ω² ≤ 10^60 G^5 U^25 Ω⁵
      -- ⟺ 1 ≤ 10^60 G³ U^10 Ω³.  And G³ U^10 Ω³ ≥ (G U^4 Ω³) * G² U^6 ≥ 1*1 = 1.
      have hkey : (2197000:ℝ) ≤ (10:ℝ)^60 * (P.G ^ 3 * P.U ^ 10 * S.Ω ^ 3) := by
        have hG2U6 : (1:ℝ) ≤ P.G ^ 2 * P.U ^ 6 := by
          have hg2 := one_le_pow₀ (n := 2) hG1
          have hu6 := one_le_pow₀ (n := 6) hU1
          calc (1:ℝ) = 1 * 1 := by ring
            _ ≤ P.G ^ 2 * P.U ^ 6 := mul_le_mul hg2 hu6 (by norm_num) (by positivity)
        have hprod : (1:ℝ) ≤ P.G ^ 3 * P.U ^ 10 * S.Ω ^ 3 := by
          calc (1:ℝ) = 1 * 1 := by ring
            _ ≤ (P.G * P.U ^ 4 * S.Ω ^ 3) * (P.G ^ 2 * P.U ^ 6) :=
                mul_le_mul hGU4Ω3 hG2U6 (by norm_num) (by positivity)
            _ = P.G ^ 3 * P.U ^ 10 * S.Ω ^ 3 := by ring
        have h1060 : (2197000:ℝ) ≤ (10:ℝ)^60 := by norm_num
        calc (2197000:ℝ) = 2197000 * 1 := by ring
          _ ≤ (10:ℝ)^60 * (P.G ^ 3 * P.U ^ 10 * S.Ω ^ 3) :=
              mul_le_mul h1060 hprod (by norm_num) (by positivity)
      -- Now assemble cross-multiplied inequality.
      have hΩ5pos : (0:ℝ) < S.Ω ^ 5 := by positivity
      have hΩ2pos : (0:ℝ) < S.Ω ^ 2 := by positivity
      -- RHS_full := 10^60 (H/Δ²) G^4 U^15 ; goal: P.G^2 U^15 * Ω² ≤ RHS_full * Ω⁵
      -- RHS_full ≥ 10^60 (G U^10) G^4 U^15 = 10^60 G^5 U^25
      have hRHS_lb : (10:ℝ)^60 * P.G ^ 5 * P.U ^ 25
          ≤ (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15 := by
        have : (10:ℝ)^60 * P.G ^ 5 * P.U ^ 25
            = (10:ℝ)^60 * P.G^4 * P.U^15 * (P.G * P.U ^ 10) := by ring
        rw [this]
        have h2 : (10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15
            = (10:ℝ)^60 * P.G^4 * P.U^15 * (P.H / S.Δ^2) := by ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left hHΔ (by positivity)
      -- LHS goal ≤ 10^60 G^5 U^25 * Ω⁵
      have hLHS_ub : 2197000 * (P.G ^ 2 * P.U ^ 15) * S.Ω ^ 2
          ≤ (10:ℝ)^60 * P.G ^ 5 * P.U ^ 25 * S.Ω ^ 5 := by
        -- ⟺ G² U^15 Ω² ≤ 10^60 G^5 U^25 Ω⁵, factor G² U^15 Ω²:
        have hfac : (10:ℝ)^60 * P.G ^ 5 * P.U ^ 25 * S.Ω ^ 5
            = (P.G ^ 2 * P.U ^ 15 * S.Ω ^ 2) * ((10:ℝ)^60 * (P.G ^ 3 * P.U ^ 10 * S.Ω ^ 3)) := by
          ring
        rw [hfac]
        calc 2197000 * (P.G ^ 2 * P.U ^ 15) * S.Ω ^ 2
            = (P.G ^ 2 * P.U ^ 15 * S.Ω ^ 2) * 2197000 := by ring
          _ ≤ (P.G ^ 2 * P.U ^ 15 * S.Ω ^ 2) * ((10:ℝ)^60 * (P.G ^ 3 * P.U ^ 10 * S.Ω ^ 3)) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
      -- chain: P.G^2 U^15 Ω² ≤ 10^60 G^5 U^25 Ω⁵ ≤ RHS_full * Ω⁵
      calc 2197000 * (P.G ^ 2 * P.U ^ 15) * S.Ω ^ 2
          ≤ (10:ℝ)^60 * P.G ^ 5 * P.U ^ 25 * S.Ω ^ 5 := hLHS_ub
        _ = ((10:ℝ)^60 * P.G ^ 5 * P.U ^ 25) * S.Ω ^ 5 := by ring
        _ ≤ ((10:ℝ)^60 * (P.H / S.Δ^2) * P.G^4 * P.U^15) * S.Ω ^ 5 :=
            mul_le_mul_of_nonneg_right hRHS_lb hΩ5pos.le
    have hWval3' : 2197000 * P.Wval ^ 3 / (P.G * S.Ω ^ 5)
        = 2197000 * (P.G ^ 2 * P.U ^ 15) / S.Ω ^ 5 := by
      rw [Globals.Wval]; field_simp; try ring
    calc Lnum / (P.G * S.Ω ^ 5)
        ≤ 2197000 * P.Wval ^ 3 / (P.G * S.Ω ^ 5) := by
          gcongr
      _ = 2197000 * (P.G ^ 2 * P.U ^ 15) / S.Ω ^ 5 := hWval3'
      _ ≤ Rδ := hGUΩ_le_Rδ
  -- the term (1 + G Ω⁵ / Lnum) ≥ 1
  have hAddTerm : (1:ℝ) ≤ 1 + P.G * S.Ω^5 / Lnum := by
    have : (0:ℝ) ≤ P.G * S.Ω^5 / Lnum := by positivity
    linarith
  -- ===== case split on δ =====
  rcases lt_or_ge δ 1 with hδlt | hδge
  · -- Branch δ < 1: use the product bound from Ra_step1_v0_count.
    have hcount := Ra_step1_v0_count hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W h1 hband hG1 hU1 hΔ1
      hUH hΩU hUbig hΔreg Ra dStar hdStar
    -- rewrite the count RHS in terms of Lnum, δ, Rδ
    rw [← hF, ← hLnum, ← hδdef] at hcount
    -- Lc := Lnum / (G Ω⁵)
    set Lc : ℝ := Lnum / (P.G * S.Ω ^ 5) with hLc
    have hLcpos : 0 < Lc := by rw [hLc]; positivity
    -- the second factor denominator: Lnum / (G Ω⁵ R · 10^30) = Lc / (R · 10^30)
    have hden : Lnum / (P.G * S.Ω ^ 5 * S.R * 10 ^ 30) = Lc / (S.R * 10 ^ 30) := by
      rw [hLc]; field_simp
    rw [hden] at hcount
    -- so PRODUCT = (10^20 * Lc + 2δ + 1) * (2δ / (Lc/(R·10^30)) + 1)
    --            = (10^20 Lc + 2δ + 1) * (2·10^30·Rδ / Lc + 1)
    have hfac2 : 2 * δ / (Lc / (S.R * 10 ^ 30)) = 2 * 10^30 * Rδ / Lc := by
      rw [hRδdef]; field_simp
    rw [hfac2] at hcount
    -- Now bound PRODUCT ≤ 10^55 * Rδ * (1 + 1/Lc) and convert 1/Lc = GΩ⁵/Lnum.
    -- First: 1/Lc = G Ω⁵ / Lnum.
    have hinvLc : (1:ℝ) / Lc = P.G * S.Ω^5 / Lnum := by
      rw [hLc]; field_simp
    -- target RHS = 10^55 * Rδ * (1 + GΩ⁵/Lnum) = 10^55 * Rδ * (1 + 1/Lc)
    rw [← hinvLc]
    -- reduce to: PRODUCT ≤ 10^55 * Rδ * (1 + 1/Lc)
    refine le_trans hcount ?_
    -- Multiply through by Lc > 0; prove the cleared inequality, then divide back.
    -- Cleared LHS:  (10^20 Lc + 2δ + 1) * (2·10^30·Rδ + Lc)
    -- Cleared RHS:  10^55 Rδ * (Lc + 1)
    have hLHSeq : (10 ^ 20 * Lc + 2 * δ + 1) * (2 * 10 ^ 30 * Rδ / Lc + 1)
        = ((10 ^ 20 * Lc + 2 * δ + 1) * (2 * 10 ^ 30 * Rδ + Lc)) / Lc := by
      field_simp
    have hRHSeq : (10:ℝ)^55 * Rδ * (1 + 1 / Lc)
        = ((10:ℝ)^55 * Rδ * (Lc + 1)) / Lc := by
      field_simp
    rw [hLHSeq, hRHSeq]
    rw [div_le_div_iff_of_pos_right hLcpos]
    -- Goal: (10^20 Lc + 2δ + 1)*(2·10^30·Rδ + Lc) ≤ 10^55 Rδ (Lc + 1)
    -- Bound the four expanded terms explicitly (avoid nlinarith blow-up).
    have hδle : δ ≤ 1 := hδlt.le
    -- named nonneg / product facts
    have hLcRδ : (0:ℝ) ≤ Rδ * Lc := mul_nonneg hRδpos.le hLcpos.le
    have hLc2 : Lc * Lc ≤ Rδ * Lc := mul_le_mul_of_nonneg_right hL_le_Rδ hLcpos.le
    have hLcle : Lc ≤ Rδ := hL_le_Rδ
    -- the LHS expanded form
    have hexpand : (10 ^ 20 * Lc + 2 * δ + 1) * (2 * 10 ^ 30 * Rδ + Lc)
        = 2 * 10 ^ 50 * (Rδ * Lc) + 10 ^ 20 * (Lc * Lc)
          + (2 * δ + 1) * (2 * 10 ^ 30) * Rδ + (2 * δ + 1) * Lc := by ring
    rw [hexpand]
    -- bound each summand:
    -- numeric coefficient facts (computed once)
    have hcoef1 : (2 * 10 ^ 50 + 10 ^ 20 : ℝ) ≤ (10:ℝ)^55 := by norm_num
    have hcoef2 : (3 * (2 * 10 ^ 30) : ℝ) ≤ (10:ℝ)^55 / 2 := by norm_num
    have hcoef3 : (3 : ℝ) ≤ (10:ℝ)^55 / 2 := by norm_num
    -- (1) 2·10^50·(Rδ·Lc) + 10^20·(Lc·Lc) ≤ (2·10^50 + 10^20)·(Rδ·Lc) ≤ 10^55·(Rδ·Lc)
    have hb1 : 2 * 10 ^ 50 * (Rδ * Lc) + 10 ^ 20 * (Lc * Lc)
        ≤ (10:ℝ)^55 * (Rδ * Lc) := by
      have hYX : (10:ℝ) ^ 20 * (Lc * Lc) ≤ (10:ℝ)^20 * (Rδ * Lc) :=
        mul_le_mul_of_nonneg_left hLc2 (by positivity)
      have hcoef : (2 * 10 ^ 50 + 10 ^ 20 : ℝ) * (Rδ * Lc) ≤ (10:ℝ)^55 * (Rδ * Lc) :=
        mul_le_mul_of_nonneg_right hcoef1 hLcRδ
      have hrw : (2 * 10 ^ 50 + 10 ^ 20 : ℝ) * (Rδ * Lc)
          = 2 * 10 ^ 50 * (Rδ * Lc) + (10:ℝ)^20 * (Rδ * Lc) := by ring
      rw [hrw] at hcoef
      linarith [hYX, hcoef]
    -- (2) (2δ+1)·2·10^30·Rδ ≤ 3·2·10^30·Rδ ≤ (1/2)·10^55·Rδ
    have hb2 : (2 * δ + 1) * (2 * 10 ^ 30) * Rδ ≤ (10:ℝ)^55 / 2 * Rδ := by
      have h2δ1 : 2 * δ + 1 ≤ 3 := by linarith
      have hle : (2 * δ + 1) * (2 * 10 ^ 30) ≤ (10:ℝ)^55 / 2 := by
        have hstep : (2 * δ + 1) * (2 * 10 ^ 30) ≤ 3 * (2 * 10 ^ 30) :=
          mul_le_mul_of_nonneg_right h2δ1 (by norm_num)
        linarith [hstep, hcoef2]
      exact mul_le_mul_of_nonneg_right hle hRδpos.le
    -- (3) (2δ+1)·Lc ≤ 3·Rδ ≤ (1/2)·10^55·Rδ
    have hb3 : (2 * δ + 1) * Lc ≤ (10:ℝ)^55 / 2 * Rδ := by
      have h2δ1 : 2 * δ + 1 ≤ 3 := by linarith
      have hstep : (2 * δ + 1) * Lc ≤ 3 * Lc :=
        mul_le_mul_of_nonneg_right h2δ1 hLcpos.le
      have hstep2 : (3:ℝ) * Lc ≤ 3 * Rδ := by linarith [hLcle]
      have hstep3 : (3:ℝ) * Rδ ≤ (10:ℝ)^55 / 2 * Rδ :=
        mul_le_mul_of_nonneg_right hcoef3 hRδpos.le
      linarith [hstep, hstep2, hstep3]
    -- assemble
    have hRHSsplit : (10:ℝ)^55 * Rδ * (Lc + 1)
        = (10:ℝ)^55 * (Rδ * Lc) + ((10:ℝ)^55 / 2 * Rδ + (10:ℝ)^55 / 2 * Rδ) := by ring
    rw [hRHSsplit]
    linarith [hb1, hb2, hb3]
  · -- Branch 1 ≤ δ: trivial interval count.
    have hδ1 : (1:ℝ) ≤ δ := hδge
    -- every r in F has (r:ℝ) ≤ 16 S.R
    have hub : ∀ r ∈ F, (r:ℝ) ≤ 16 * S.R := by
      intro r hr
      rw [hF, Finset.mem_filter] at hr
      obtain ⟨hrRa, _⟩ := hr
      exact (hdStar r hrRa).2.2.2.2.2
    have hcard := card_le_of_real_ub (T := F) (B := 16 * S.R)
      (by positivity) hub
    -- 16 R + 1 ≤ 17 R ≤ 17 Rδ ≤ 10^55 Rδ (1 + GΩ⁵/Lnum)
    have h17R : 16 * S.R + 1 ≤ 17 * S.R := by linarith [hR1]
    have hRRδ : S.R ≤ Rδ := by
      rw [hRδdef]
      have hstep : S.R * 1 ≤ S.R * δ := mul_le_mul_of_nonneg_left hδ1 hRpos.le
      linarith [hstep]
    have h17Rδ : 17 * S.R ≤ 17 * Rδ := by linarith [hRRδ]
    have hfinal : 17 * Rδ ≤ (10:ℝ)^55 * Rδ * (1 + P.G * S.Ω^5 / Lnum) := by
      have h1055 : (17:ℝ) ≤ (10:ℝ)^55 := by norm_num
      have hstep1 : (17:ℝ) * Rδ ≤ (10:ℝ)^55 * Rδ :=
        mul_le_mul_of_nonneg_right h1055 hRδpos.le
      calc 17 * Rδ ≤ (10:ℝ)^55 * Rδ := hstep1
        _ = (10:ℝ)^55 * Rδ * 1 := by ring
        _ ≤ (10:ℝ)^55 * Rδ * (1 + P.G * S.Ω^5 / Lnum) :=
            mul_le_mul_of_nonneg_left hAddTerm (by positivity)
    linarith [hcard, h17R, h17Rδ, hfinal]

end Squarefree
