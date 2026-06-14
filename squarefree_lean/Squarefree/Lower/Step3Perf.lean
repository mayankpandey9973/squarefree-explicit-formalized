import Squarefree.Lower.Step3Model
import Squarefree.Lower.CountTrivial
import Squarefree.Lower.DefectScales

/-!
# §5 Step-3 per-`f` performance bound (writeup 975–984)

`Ra_step3_perf` converts the messy product bound of `Ra_step3_count`
(in `Squarefree.Lower.Step3Model`) into the clean per-`f` form

  `#F ≤ 10^58 · (T + Rδ₂₃ + Rδ₂₃ / T)`,

where `T = |f|·D⁴/(X·A)`, `δ₂₃ = Δ²·G·U²⁰/(H·Ω⁶)`, and `Rδ₂₃ = R·δ₂₃`. This is the shape
consumed by the §5 per-`f` summation assembly. It is the direct analogue of
`Ra_step1_v0_perpair`.

The proof case-splits on `δ₂₃ < 1` (product bound) vs `1 ≤ δ₂₃` (trivial interval count).
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **Step-3 per-`f` performance bound for the concrete triple set.** -/
theorem Ra_step3_perf {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    {f : ℤ}
    (hflarge : (10:ℝ) ^ 55 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
        / (P.G * S.Ω ^ 5)) ≤ |(f : ℝ)|)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ)
      ≤ (10:ℝ) ^ 58 * ((|(f : ℝ)| * S.D ^ 4 / (P.X * S.A))
          + S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
          + S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
              / (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A))) := by
  -- abbreviations matching the statement
  set T : ℝ := |(f : ℝ)| * S.D ^ 4 / (P.X * S.A) with hTdef
  set δ₂₃ : ℝ := S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6) with hδdef
  set Rδ : ℝ := S.R * δ₂₃ with hRδdef
  -- the filter set
  set F : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        round (Qval P a dStar ℓ₁ ℓ₂ r) = f) with hF
  -- positivity facts
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hXpos := P.X_pos
  have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
  have hApos : (0 : ℝ) < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  -- cast facts for ℓ₁ < ℓ₂
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : (1 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_trans hℓ1R hℓ12R.le
  -- |f| > 0 from hflarge
  have hfpos : 0 < |(f : ℝ)| := by
    have hℓ1pos : (0:ℝ) < ((ℓ₁:ℤ):ℝ) := by linarith
    have hℓ2pos : (0:ℝ) < ((ℓ₂:ℤ):ℝ) := by linarith
    have hdiff : (0:ℝ) < ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by linarith
    have hLpos : (0:ℝ) < (10:ℝ) ^ 55 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ)
        * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) / (P.G * S.Ω ^ 5)) := by positivity
    linarith [hflarge, hLpos]
  -- T > 0
  have hTpos : 0 < T := by rw [hTdef]; positivity
  -- δ₂₃ > 0
  have hδpos : 0 < δ₂₃ := by rw [hδdef]; positivity
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
  -- 1 ≤ Rδ.  Closed form: Rδ = S.R·δ₂₃ = G²·Δ·U²⁰/Ω³ ≥ G⁴·U²² ≥ 1.
  have hRδ1 : (1:ℝ) ≤ Rδ := by
    rw [hRδdef, hδdef]
    have hform : S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
        = P.G ^ 3 * S.Δ * P.U ^ 20 / S.Ω ^ 3 := by
      unfold Scale.R
      field_simp
    rw [hform]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < S.Ω ^ 3)]
    -- want: 1 * Ω³ ≤ G² Δ U²⁰, i.e. Ω³ ≤ G² Δ U²⁰
    have hΩ3U3 : S.Ω ^ 3 ≤ P.U ^ 3 := by
      apply pow_le_pow_left₀ hΩpos.le hΩU
    -- G² Δ U²⁰ ≥ G² (G²U⁵) U²⁰ = G⁴ U²⁵ ≥ U³ ≥ Ω³
    have hΔlb : P.G ^ 2 * P.U ^ 5 ≤ S.Δ := hΔreg
    have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
    have hU22 : (1:ℝ) ≤ P.U ^ 22 := one_le_pow₀ hU1
    -- chain: Ω³ ≤ U³ ≤ G⁴ U²⁵ = G² (G²U⁵) U²⁰ ≤ G² Δ U²⁰
    have hstep1 : P.U ^ 3 ≤ P.G ^ 2 * (P.G ^ 2 * P.U ^ 5) * P.U ^ 20 := by
      have heq : P.G ^ 2 * (P.G ^ 2 * P.U ^ 5) * P.U ^ 20 = P.U ^ 3 * (P.G ^ 4 * P.U ^ 22) := by
        ring
      rw [heq]
      have hge1 : (1:ℝ) ≤ P.G ^ 4 * P.U ^ 22 := by nlinarith [hG4, hU22]
      calc P.U ^ 3 = P.U ^ 3 * 1 := by ring
        _ ≤ P.U ^ 3 * (P.G ^ 4 * P.U ^ 22) :=
            mul_le_mul_of_nonneg_left hge1 (by positivity)
    have hstep2 : P.G ^ 2 * (P.G ^ 2 * P.U ^ 5) * P.U ^ 20 ≤ P.G ^ 2 * S.Δ * P.U ^ 20 := by
      have hc : (0:ℝ) ≤ P.G ^ 2 * P.U ^ 20 := by positivity
      nlinarith [hΔlb, hc]
    calc (1:ℝ) * S.Ω ^ 3 = S.Ω ^ 3 := by ring
      _ ≤ P.U ^ 3 := hΩ3U3
      _ ≤ P.G ^ 2 * (P.G ^ 2 * P.U ^ 5) * P.U ^ 20 := hstep1
      _ ≤ P.G ^ 2 * S.Δ * P.U ^ 20 := hstep2
      _ ≤ P.G ^ 3 * S.Δ * P.U ^ 20 := by
          nlinarith [hG1, mul_pos (mul_pos (pow_pos hGpos 2) hΔpos) (pow_pos hUpos 20)]
  -- ===== case split on δ₂₃ =====
  rcases lt_or_ge δ₂₃ 1 with hδlt | hδge
  · -- Branch δ₂₃ < 1: use the product bound from Ra_step3_count.
    have hcount := Ra_step3_count hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hflarge h1 hband hG1 hU1 hΔ1
      hH1 hUH hΩU hUbig hΔreg Ra dStar hdStar
    -- rewrite the count RHS in terms of T, δ₂₃, Rδ
    rw [← hF, ← hTdef, ← hδdef] at hcount
    -- the second factor denominator: |f|·D⁴/(X·A·R·10^50) = T/(R·10^50)
    have hden : |(f : ℝ)| * S.D ^ 4 / (P.X * S.A * S.R * 10 ^ 50) = T / (S.R * 10 ^ 50) := by
      rw [hTdef]; field_simp
    rw [hden] at hcount
    -- 2·(4·δ₂₃) / (T/(R·10^50)) = 8·δ₂₃·R·10^50 / T = 8·10^50·Rδ / T
    have hfac2 : 2 * (4 * δ₂₃) / (T / (S.R * 10 ^ 50)) = 8 * 10 ^ 50 * Rδ / T := by
      rw [hRδdef]; field_simp; ring
    rw [hfac2] at hcount
    refine le_trans hcount ?_
    -- PRODUCT = (10^6·T + 8·δ₂₃ + 1) · (8·10^50·Rδ/T + 1)
    -- Multiply through by T > 0; prove the cleared inequality, then divide back.
    have hLHSeq : (10 ^ 6 * T + 2 * (4 * δ₂₃) + 1) * (8 * 10 ^ 50 * Rδ / T + 1)
        = ((10 ^ 6 * T + 2 * (4 * δ₂₃) + 1) * (8 * 10 ^ 50 * Rδ + T)) / T := by
      field_simp
    have hRHSeq : (10:ℝ) ^ 58 * (T + Rδ + Rδ / T)
        = ((10:ℝ) ^ 58 * (T * T + Rδ * T + Rδ)) / T := by
      field_simp
    rw [hLHSeq, hRHSeq]
    rw [div_le_div_iff_of_pos_right hTpos]
    -- Goal: (10^6 T + 8δ₂₃ + 1)·(8·10^50·Rδ + T) ≤ 10^58·(T·T + Rδ·T + Rδ)
    have hδle : δ₂₃ ≤ 1 := hδlt.le
    -- named nonneg / product facts
    have hRδT : (0:ℝ) ≤ Rδ * T := mul_nonneg hRδpos.le hTpos.le
    have hTT : (0:ℝ) ≤ T * T := mul_nonneg hTpos.le hTpos.le
    -- δ₂₃ ≤ Rδ (since Rδ = R·δ₂₃ and R ≥ 1)
    have hδleRδ : δ₂₃ ≤ Rδ := by
      rw [hRδdef]
      have : 1 * δ₂₃ ≤ S.R * δ₂₃ := mul_le_mul_of_nonneg_right hR1 hδpos.le
      linarith
    -- expanded LHS form
    have hexpand : (10 ^ 6 * T + 2 * (4 * δ₂₃) + 1) * (8 * 10 ^ 50 * Rδ + T)
        = 8 * 10 ^ 56 * (Rδ * T) + 10 ^ 6 * (T * T)
          + (8 * δ₂₃ + 1) * (8 * 10 ^ 50) * Rδ + (8 * δ₂₃ + 1) * T := by ring
    rw [hexpand]
    -- bound each summand
    have h8δ1 : 8 * δ₂₃ + 1 ≤ 9 := by linarith
    -- numeric coefficient facts
    have hcoef1 : (8 * 10 ^ 56 + 10 ^ 6 : ℝ) ≤ (10:ℝ) ^ 58 := by norm_num
    have hcoef2 : (9 * (8 * 10 ^ 50) : ℝ) ≤ (10:ℝ) ^ 58 := by norm_num
    have hcoef3 : (9 : ℝ) ≤ (10:ℝ) ^ 58 := by norm_num
    -- (1) 8·10^56·(Rδ·T) + 10^6·(T·T) → into the T·T and Rδ·T slots.
    --     8·10^56·(Rδ·T) ≤ 10^58·(Rδ·T); 10^6·(T·T) ≤ 10^58·(T·T)
    have hb1a : 8 * 10 ^ 56 * (Rδ * T) ≤ (10:ℝ) ^ 58 * (Rδ * T) :=
      mul_le_mul_of_nonneg_right (by norm_num) hRδT
    have hb1b : 10 ^ 6 * (T * T) ≤ (10:ℝ) ^ 58 * (T * T) :=
      mul_le_mul_of_nonneg_right (by norm_num) hTT
    -- (2) (8δ₂₃+1)·(8·10^50)·Rδ ≤ 9·8·10^50·Rδ ≤ 10^58·Rδ
    have hb2 : (8 * δ₂₃ + 1) * (8 * 10 ^ 50) * Rδ ≤ (10:ℝ) ^ 58 * Rδ := by
      have hle : (8 * δ₂₃ + 1) * (8 * 10 ^ 50) ≤ (10:ℝ) ^ 58 := by
        have hstep : (8 * δ₂₃ + 1) * (8 * 10 ^ 50) ≤ 9 * (8 * 10 ^ 50) :=
          mul_le_mul_of_nonneg_right h8δ1 (by norm_num)
        linarith [hstep, hcoef2]
      exact mul_le_mul_of_nonneg_right hle hRδpos.le
    -- (3) (8δ₂₃+1)·T ≤ 9·T ≤ ... bound by Rδ·T slot: 9·T ≤ 10^58·Rδ·T? no — into Rδ slot.
    --     Actually (8δ₂₃+1)·T ≤ 9·T.  We want this ≤ a leftover of 10^58·(Rδ·T) slot.
    --     Since Rδ ≥ 1, T·1 ≤ T·Rδ = Rδ·T, so 9·T ≤ 9·(Rδ·T) ≤ 10^58·(Rδ·T) ... but Rδ·T
    --     already used.  Instead route (8δ₂₃+1)·T into the Rδ slot via: T ≤ ? No.
    --     Use: (8δ₂₃+1)·T ≤ 9·T and 9·T ≤ 9·Rδ·T (Rδ≥1) but Rδ·T slot. Keep budget split.
    have hb3 : (8 * δ₂₃ + 1) * T ≤ (10:ℝ) ^ 58 * (Rδ * T) := by
      have hstep : (8 * δ₂₃ + 1) * T ≤ 9 * T :=
        mul_le_mul_of_nonneg_right h8δ1 hTpos.le
      have hTRδT : T ≤ Rδ * T := by
        have : 1 * T ≤ Rδ * T := mul_le_mul_of_nonneg_right hRδ1 hTpos.le
        linarith
      have hstep2 : (9:ℝ) * T ≤ 9 * (Rδ * T) := by linarith [hTRδT]
      have hstep3 : (9:ℝ) * (Rδ * T) ≤ (10:ℝ) ^ 58 * (Rδ * T) :=
        mul_le_mul_of_nonneg_right hcoef3 hRδT
      linarith [hstep, hstep2, hstep3]
    -- assemble.  The RHS 10^58·(T·T + Rδ·T + Rδ) splits with two Rδ·T budgets.
    -- We have: 8·10^56·(Rδ·T) ≤ 10^58·(Rδ·T) [most of it], 10^6·(T·T) ≤ 10^58·(T·T),
    -- (8δ₂₃+1)·(8·10^50)·Rδ ≤ 10^58·Rδ, (8δ₂₃+1)·T ≤ 10^58·(Rδ·T).
    -- But 10^58·(Rδ·T) is needed twice; check coefficients: 8·10^56 + 9 (from hb3's used 9)
    -- ≤ 10^58.  Recompute hb1a/hb3 with shared budget via linarith on raw terms.
    have hRHSsplit : (10:ℝ) ^ 58 * (T * T + Rδ * T + Rδ)
        = (10:ℝ) ^ 58 * (T * T) + ((10:ℝ) ^ 58 * (Rδ * T)) + (10:ℝ) ^ 58 * Rδ := by ring
    rw [hRHSsplit]
    -- Combine the two Rδ·T contributions: 8·10^56·(Rδ·T) + (8δ₂₃+1)·T ≤ 10^58·(Rδ·T).
    have hRδT_combine : 8 * 10 ^ 56 * (Rδ * T) + (8 * δ₂₃ + 1) * T
        ≤ (10:ℝ) ^ 58 * (Rδ * T) := by
      have hstep : (8 * δ₂₃ + 1) * T ≤ 9 * (Rδ * T) := by
        have h1' : (8 * δ₂₃ + 1) * T ≤ 9 * T := mul_le_mul_of_nonneg_right h8δ1 hTpos.le
        have hTRδT : T ≤ Rδ * T := by
          have : 1 * T ≤ Rδ * T := mul_le_mul_of_nonneg_right hRδ1 hTpos.le
          linarith
        linarith [h1', hTRδT]
      have hcoef : (8 * 10 ^ 56 + 9 : ℝ) * (Rδ * T) ≤ (10:ℝ) ^ 58 * (Rδ * T) :=
        mul_le_mul_of_nonneg_right (by norm_num) hRδT
      have hrw : (8 * 10 ^ 56 + 9 : ℝ) * (Rδ * T)
          = 8 * 10 ^ 56 * (Rδ * T) + 9 * (Rδ * T) := by ring
      rw [hrw] at hcoef
      linarith [hstep, hcoef]
    linarith [hb1b, hb2, hRδT_combine]
  · -- Branch 1 ≤ δ₂₃: trivial interval count.
    have hδ1 : (1:ℝ) ≤ δ₂₃ := hδge
    -- every r in F has (r:ℝ) ≤ 16 S.R
    have hub : ∀ r ∈ F, (r:ℝ) ≤ 16 * S.R := by
      intro r hr
      rw [hF, Finset.mem_filter] at hr
      obtain ⟨hrRa, _⟩ := hr
      exact (hdStar r hrRa).2.2.2.2.2
    have hcard := card_le_of_real_ub (T := F) (B := 16 * S.R)
      (by positivity) hub
    -- 16 R + 1 ≤ 17 R ≤ 17 Rδ ≤ 10^58 (T + Rδ + Rδ/T)
    have h17R : 16 * S.R + 1 ≤ 17 * S.R := by linarith [hR1]
    have hRRδ : S.R ≤ Rδ := by
      rw [hRδdef]
      have hstep : S.R * 1 ≤ S.R * δ₂₃ := mul_le_mul_of_nonneg_left hδ1 hRpos.le
      linarith [hstep]
    have h17Rδ : 17 * S.R ≤ 17 * Rδ := by linarith [hRRδ]
    have hfinal : 17 * Rδ ≤ (10:ℝ) ^ 58 * (T + Rδ + Rδ / T) := by
      -- the other two summands T, Rδ/T are ≥ 0
      have hTnn : (0:ℝ) ≤ T := hTpos.le
      have hRδTnn : (0:ℝ) ≤ Rδ / T := by positivity
      have h1058 : (17:ℝ) ≤ (10:ℝ) ^ 58 := by norm_num
      calc 17 * Rδ ≤ (10:ℝ) ^ 58 * Rδ :=
            mul_le_mul_of_nonneg_right h1058 hRδpos.le
        _ ≤ (10:ℝ) ^ 58 * (T + Rδ + Rδ / T) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hTnn, hRδTnn]
    linarith [hcard, h17R, h17Rδ, hfinal]

end Squarefree
