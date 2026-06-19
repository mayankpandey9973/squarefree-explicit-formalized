import Squarefree.Lower.Prop51Combine
import Squarefree.Lower.Prop51Partition
import Squarefree.Lower.Prop51Bridges
import Squarefree.Lower.Prop51Step2
import Squarefree.Lower.Prop51Step3
import Squarefree.Lower.Step1Perpair
import Squarefree.Lower.Step4Capstone
import Squarefree.Lower.Step4WindowFacts
import Squarefree.Lower.Step3VBound
import Squarefree.Lower.Step4PhivWitness
import Squarefree.Lower.Prop51Witness
import Squarefree.Lower.Prop51Step4Pack
import Squarefree.Lower.Prop51PerpairSum

/-!
# §5 assembly — the per-pair count bound (writeup 1167–1224)

`prop51_perpair`: under the `prop_5_1` hypothesis pack, the per-pair fiber count
`#{r ∈ ℛ_a : r+ℓ₁ ∈ ℛ_a, r+ℓ₂ ∈ ℛ_a}` is at most the per-pair budget `Bcombine`.
Route: `fiber_le_sum_ranges` (v-partition at `V₁ = 10⁶⁵`-literal, `V₊ = 10⁶⁰·V₂`),
then the four landed per-range bounds (Steps 1–4), each dominated by its
`Bcombine` monomials.
-/

open Classical Finset Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 6400000

/-- **§5 per-pair bound.** Under the `prop_5_1` hypothesis pack and a pair
`1 ≤ ℓ₁ < ℓ₂ ≤ 130·Wval`, the fiber count is at most `Bcombine P S ℓ₁ ℓ₂`. -/
theorem prop51_perpair
    (P : Globals) (S : Scale P) (a : ℤ) (ha : 0 < a) (hAD : 10 * S.A ≤ S.D)
    (hGHΩ : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3) (Ra : Finset ℕ)
    (hwit : ∀ r ∈ Ra, RaWitness P S a r)
    (hreg1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hreg2 : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hpop : S.R / P.Wval ≤ (Ra.card : ℝ))
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hX : (10 : ℝ) ^ 33 ≤ P.U)
    (hUcal : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14)
    (hδbud : 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) ≤ 1 / 2)
    (haA1 : S.A / 5 ≤ (a : ℝ)) (haA2 : (a : ℝ) ≤ 11 * S.A)
    (hΩH : 60 * S.Ω ≤ P.H)
    (hlogcap : Real.log (10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
          + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
          + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) + 1
        ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω)
    (ℓ₁ ℓ₂ : ℕ) (hℓ : 1 ≤ ℓ₁ ∧ ℓ₁ < ℓ₂ ∧ (ℓ₂ : ℝ) ≤ 130 * P.Wval) :
    ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ)
      ≤ Bcombine P S ℓ₁ ℓ₂ := by
  classical
  have _ := hGHΩ; have _ := hpop; have _ := hΩH
  obtain ⟨hℓ1, hℓ12, hℓ2W⟩ := hℓ
  have hℓ1pos : 0 < ℓ₁ := hℓ1
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  -- shared regime derivations
  have hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 :=
    prop51_hreg (P := P) (S := S) hΩU hG1 hU1 hΔ1 hHbig
  have hRfloor : 10 ^ 113 * (P.G * P.U ^ 5) ≤ S.R :=
    prop51_R_floor (P := P) (S := S) hreg1 hband hΩU hG1 hU1 hX hDeW
  have hℓ2WZ : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval := by push_cast; exact hℓ2W
  have hℓ2GU : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    have h := hℓ2W; rwa [Globals.Wval] at h
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ1GU : (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hℓ1W130 : (ℓ₁ : ℝ) ≤ 130 * P.Wval := by rw [Globals.Wval]; exact hℓ1GU
  -- the witness choice and its bundles
  have hdStar := witness_hdStar (P := P) (S := S) hwit
  have hwin := witness_hwin (P := P) (S := S) hℓ1pos hℓ12 hG1 hU1 hDeW hwit
  -- ===== the v-range partition at V₁ (Step-2/3 boundary) and V₊ = 10⁶⁰·V₂ =====
  have hpart := fiber_le_sum_ranges (P := P) Ra a (dStarOf P S a) ℓ₁ ℓ₂
    (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6))) (10 ^ 60 * V₂ P S)
  -- ===== s₁ : the v = 0 range =====
  have hs1 : ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ vval P a (dStarOf P S a) ℓ₁ ℓ₂ r = 0)).card : ℝ)
      ≤ (10:ℝ) ^ 55 * (S.R * ((10:ℝ) ^ 60 * ((1/S.Δ) * P.G ^ 3 * P.U ^ 15 / S.Ω ^ 5)))
          * (1 + P.G * S.Ω ^ 5 / (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ)
              * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)))) := by
    have hbridge := step1_filter_bridge (P := P) Ra a (dStarOf P S a)
      (ℓ₂ := ℓ₂) hℓ1pos
    have hcount := Ra_step1_v0_perpair (P := P) (S := S) hAD ha haA1 haA2 hℓ1pos hℓ12 hℓ2WZ
      hreg1 hband hG1 hU1 hΔ1 hUcal hΩU hX hreg2 Ra (dStarOf P S a) hdStar
    exact le_trans (by exact_mod_cast hbridge) hcount
  -- ===== s₂ : the range 0 < |v| ≤ V₁ =====
  have hsmall : (10:ℝ) ^ 110 * ((ℓ₁ : ℤ) : ℝ) ≤ S.R := by
    have h130 : (10:ℝ) ^ 110 * ((ℓ₁ : ℤ) : ℝ) ≤ 10 ^ 110 * (130 * (P.G * P.U ^ 5)) := by
      have : ((ℓ₁ : ℤ) : ℝ) = (ℓ₁ : ℝ) := by push_cast; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hℓ1GU (by positivity)
    have hc : (10:ℝ) ^ 110 * (130 * (P.G * P.U ^ 5)) ≤ 10 ^ 113 * (P.G * P.U ^ 5) := by
      have hXnn : (0:ℝ) ≤ P.G * P.U ^ 5 := (mul_pos hGpos (pow_pos hUpos 5)).le
      rw [show (10:ℝ) ^ 110 * (130 * (P.G * P.U ^ 5))
          = (10 ^ 110 * 130) * (P.G * P.U ^ 5) from by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) hXnn
    linarith
  have hM2nn : (0:ℝ) ≤ Mbound P S ℓ₁ (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)))
      + 1 / 2 := by
    rw [Mbound]
    have hℓnn : (0:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by positivity
    positivity
  set N₂ : ℕ := ⌈Mbound P S ℓ₁ (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)))
      + 1 / 2⌉₊ with hN₂def
  have hNcap2 : Mbound P S ℓ₁ (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6))) + 1 / 2
      ≤ (N₂ : ℝ) := Nat.le_ceil _
  have hNenv2 : (N₂ : ℝ) ≤ 10 ^ 102 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    have hc := Nat.ceil_lt_add_one hM2nn
    have henv := mbound_step2_env (P := P) (S := S) hℓ1GU hG1 hU1 hΩU
    rw [← hN₂def] at hc
    linarith
  have hs2 := ra_step2_range_le (P := P) (S := S) hAD ha haA1 haA2 hℓ1pos hℓ12 hℓ2WZ
    hreg1 hband hG1 hU1 hΔ1 hH1 hUcal hΩU hX hreg2 hsmall Ra (dStarOf P S a) hdStar hwin
    N₂ hNcap2 hNenv2
  -- ===== s₃ : the range V₁ < |v| ≤ V₊ =====
  have hV2nn0 : (0:ℝ) ≤ V₂ P S := by rw [V₂]; positivity
  have hVpnn : (0:ℝ) ≤ 10 ^ 60 * V₂ P S := mul_nonneg (by positivity) hV2nn0
  have hM3nn : (0:ℝ) ≤ Mbound P S ℓ₁ (10 ^ 60 * V₂ P S) + 1 / 2 := by
    rw [Mbound]
    have hℓnn : (0:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by positivity
    have ht : (0:ℝ) ≤ 10 ^ 34 * ((ℓ₁ : ℤ) : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3)
        * (10 ^ 60 * V₂ P S) :=
      mul_nonneg (by positivity) hVpnn
    have ht2 : (0:ℝ) ≤ 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by positivity
    linarith
  set N₃ : ℕ := ⌈Mbound P S ℓ₁ (10 ^ 60 * V₂ P S) + 1 / 2⌉₊ with hN₃def
  have hNcap3 : Mbound P S ℓ₁ (10 ^ 60 * V₂ P S) + 1 / 2 ≤ (N₃ : ℝ) := Nat.le_ceil _
  have hNenv3 : (N₃ : ℝ) ≤ 10 ^ 97 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
      + 10 ^ 97 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
      + 10 ^ 97 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    have hc := Nat.ceil_lt_add_one hM3nn
    have henv := mbound_step3_env (P := P) (S := S) hℓ1GU hℓ1pos hG1 hU1 hΩU
    rw [← hN₃def] at hc
    linarith
  have hs3 := ra_step3_range_le (P := P) (S := S) hAD ha haA1 haA2 hℓ1pos hℓ12 hℓ2WZ
    hreg1 hband hG1 hU1 hΔ1 hH1 hUcal hΩU hX hreg2 hHbig hℓ1W130 Ra (dStarOf P S a)
    hdStar hwin N₃ (10 ^ 60 * V₂ P S) hVpnn hNcap3 hNenv3 hlogcap
  -- ===== s₄ : the range V₊ < |v| (capstone) =====
  have hbud := errB_quarter (P := P) (S := S) hreg1 hG1 hΩU hband hX hDeW hHbig
  -- the r-window: r₀ = R/72, r₁ = 16R − ℓ₁
  have hRpos : (0:ℝ) < S.R := by
    rw [Scale.R]; positivity
  have hℓ1leR : (ℓ₁ : ℝ) ≤ S.R := by
    have h1' : 130 * (P.G * P.U ^ 5) ≤ 10 ^ 113 * (P.G * P.U ^ 5) := by
      have hXnn : (0:ℝ) ≤ P.G * P.U ^ 5 := (mul_pos hGpos (pow_pos hUpos 5)).le
      exact mul_le_mul_of_nonneg_right (by norm_num) hXnn
    linarith
  have hr01 : (1/72) * S.R ≤ 16 * S.R - (ℓ₁ : ℝ) := by linarith
  have hr1hi : (16 * S.R - (ℓ₁ : ℝ)) + (ℓ₁ : ℝ) ≤ 16 * S.R := le_of_eq (by ring)
  -- the N₄ window
  have hX1 : (1:ℝ) ≤ 10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
      * P.U ^ 10 / S.Ω ^ 8 := by
    have hℓ1R : (1:ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
    have hd1 : (1:ℝ) ≤ (ℓ₂:ℝ) - (ℓ₁:ℝ) := by
      have : (ℓ₁:ℝ) + 1 ≤ (ℓ₂:ℝ) := by exact_mod_cast hℓ12
      linarith
    have hL : (1:ℝ) ≤ (ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) := by
      have h3 : (1:ℝ) ≤ (ℓ₁:ℝ) ^ 3 := one_le_pow₀ hℓ1R
      have hℓ2R : (1:ℝ) ≤ (ℓ₂ : ℝ) := by linarith
      have h31 : (1:ℝ) ≤ (ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) :=
        one_le_mul_of_one_le_of_one_le h3 hℓ2R
      exact one_le_mul_of_one_le_of_one_le h31 hd1
    have hUΩ : S.Ω ^ 8 ≤ P.U ^ 10 := by
      calc S.Ω ^ 8 ≤ P.U ^ 8 := pow_le_pow_left₀ hΩpos.le hΩU 8
        _ ≤ P.U ^ 10 := pow_le_pow_right₀ hU1 (by norm_num)
    rw [show 10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) * P.U ^ 10 / S.Ω ^ 8
        = 10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) * (P.U ^ 10 / S.Ω ^ 8)
        from by ring]
    have hquot : (1:ℝ) ≤ P.U ^ 10 / S.Ω ^ 8 := (one_le_div (by positivity)).mpr hUΩ
    have h56 : (1:ℝ) ≤ 10 ^ 56 := by norm_num
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h56 hL) hquot
  set N₄ : ℕ := ⌈10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
      * P.U ^ 10 / S.Ω ^ 8⌉₊ with hN₄def
  have hNlo4 : 10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) * P.U ^ 10 / S.Ω ^ 8
      ≤ (N₄ : ℝ) := Nat.le_ceil _
  have hNcap04 : (N₄ : ℝ) ≤ 10 ^ 57 * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
      * P.U ^ 10 / S.Ω ^ 8 := by
    have hc := Nat.ceil_lt_add_one (le_trans zero_le_one hX1)
    rw [← hN₄def] at hc
    calc (N₄ : ℝ)
        ≤ 10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) * P.U ^ 10 / S.Ω ^ 8 + 1 :=
          hc.le
      _ ≤ 10 * (10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
            * P.U ^ 10 / S.Ω ^ 8) := by linarith [hX1]
      _ = 10 ^ 57 * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
            * P.U ^ 10 / S.Ω ^ 8 := by ring
  -- per-r obligations from the witness pack
  have hfibre := step4_pack_bundle (P := P) (S := S) (V₂var := 10 ^ 60 * V₂ P S)
    hAD ha haA1 haA2 hℓ1pos hℓ12 hℓ2W hreg1 hband hG1 hU1 hΔ1 hΩU hX hDeW hReg
    le_rfl hwit
  have hb0box : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ 10 ^ 60 * V₂ P S < |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r|),
      |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / (ℓ₁ : ℝ)|
        ≤ 3000000000000 * S.B := by
    intro r hr
    rw [Finset.mem_filter] at hr
    exact step4_pack_b0box (ℓ₂ := ℓ₂) hAD ha haA1 haA2 hℓ1pos hℓ12 hG1 hΔ1 hwit
      hr.1 hr.2.1
  have hvmax : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ 10 ^ 60 * V₂ P S < |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r|),
      |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r| ≤ Vmax P S := by
    intro r hr
    rw [Finset.mem_filter] at hr
    exact step4_pack_vmax hAD ha haA1 haA2 hℓ1pos hℓ12 hℓ2WZ hreg1 hband hG1 hU1 hΔ1
      hΩU hX hwit hr.1 hr.2.1 hr.2.2.1
  have hb0gap : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ 10 ^ 60 * V₂ P S < |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r|),
      |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / (ℓ₁ : ℝ)
          - b1Model P.X (a : ℝ) (dtilde P.X (r : ℝ) (a : ℝ))|
        ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * (ℓ₁ : ℝ))
          + 10 ^ 13 * (ℓ₁ : ℝ) * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    exact step4_pack_hb0gap hAD ha haA1 haA2 hℓ1pos hwit hr.1 hr.2.1
  have hmem : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ 10 ^ 60 * V₂ P S < |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r|),
      (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R - (ℓ₁ : ℝ) ∧
      distInt (phiv P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ)
          (vval P a (dStarOf P S a) ℓ₁ ℓ₂ r) (r : ℝ))
        ≤ 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1, hr2, _⟩ := hr
    obtain ⟨_, _, _, _, hr_lo, _⟩ := dStarOf_spec (hwit r hrRa)
    obtain ⟨_, _, _, _, _, hr1hi'⟩ := dStarOf_spec (hwit (r + ℓ₁) hr1)
    refine ⟨hr_lo, ?_, ?_⟩
    · push_cast at hr1hi'; linarith
    · exact step4_pack_hmem hAD ha haA1 haA2 hℓ1pos hℓ12 hℓ2W hreg1 hreg2 hband
        hG1 hU1 hΔ1 hH1 hΩU hX hUcal hDeW hwit hrRa hr1 hr2
  have hs4 := ra_step4_range_complete (P := P) (S := S) a (dStarOf P S a)
    (r₀ := (1/72) * S.R) (r₁ := 16 * S.R - (ℓ₁ : ℝ))
    hAD ha haA1 haA2 hℓ1 hℓ12 hℓ2W hℓ2GU hG1 hU1 hX hΔ1 hH1 hΩU hband hreg1 hReg hDeW
    (by positivity) le_rfl le_rfl hr01 hr1hi rfl le_rfl hbud hδbud hHbig
    Ra N₄ ((10:ℝ) ^ 57) le_rfl (by norm_num) hNlo4 hNcap04 hfibre hb0box hvmax hb0gap hmem
  -- ===== summation =====
  have hsum := perpair_sum_le_Bcombine (P := P) (S := S) hℓ1pos hℓ12
  set_option exponentiation.threshold 410 in
  linarith [hpart, hs1, hs2, hs3, hs4, hsum]

end Squarefree
