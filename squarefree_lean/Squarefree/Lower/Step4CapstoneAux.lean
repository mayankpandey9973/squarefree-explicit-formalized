import Squarefree.Lower.Step4FibreCount
import Squarefree.Lower.Step4BandPay
import Squarefree.Lower.Step4RangeComplete
import Squarefree.Lower.Step4W5Mono
import Squarefree.Lower.Step4FitCubic
import Squarefree.Lower.Step4FitEACap
import Squarefree.Lower.Step4FitEBCap
import Squarefree.Lower.Step4FitCC

/-!
# §5 Step-4 capstone auxiliaries: `step4ErrU` and nonnegativity/bridge facts
The uniform near-integer budget `step4ErrU`, the ev-bridge into the frozen band slot,
and the hybrid-coefficient nonnegativity lemmas consumed by `ra_step4_range_complete`.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The uniform near-integer budget over the fibre: the `step4_fibre_window_data` budget with
`|d̃ₐ − dStar r|` capped by the `dtilde_close` tolerance `10¹²·Δ/(GΩ³)`. -/
noncomputable def step4ErrU (P : Globals) (S : Scale P) : ℝ :=
  10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S
    + 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
      * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))

theorem step4ErrU_nonneg : 0 ≤ step4ErrU P S := by
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hT : (0:ℝ) ≤ UpsT P S := by
    unfold UpsT; have := P.H_pos; have := S.Ω_pos; have := S.Δ_pos
    have := P.G_pos; have := P.U_pos; positivity
  have hW : (0:ℝ) ≤ 130 * P.Wval := by
    unfold Globals.Wval; have := P.G_pos; have := P.U_pos; positivity
  have := S.Δ_pos; have := S.Ω_pos; have := P.G_pos; have := P.U_pos
  unfold step4ErrU
  positivity

/-- **ev-bridge.**  The fibre band slot `8a·errU/√L` is dominated by `10¹²²` times the frozen
band slot `(G⁴U²⁰/Δ + Δ⁴G⁵U⁴⁵/(H²Ω¹⁴))·ΔΩ/√L` that `ra_step4_range_add5` consumes (the
post-sweep `errU` carries `10¹¹⁹·UpsT`, so `88·10¹¹⁹ ≤ 10¹²²`). -/
theorem step4_ev_bridge {a L : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) (hL1 : 1 ≤ L) :
    8 * a * step4ErrU P S / Real.sqrt L
      ≤ 10 ^ 122 * ((P.G ^ 4 * P.U ^ 20 / S.Δ
            + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
          * (S.Δ * S.Ω) / Real.sqrt L) := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hsL : (0:ℝ) < Real.sqrt L := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hL1)
  rw [show 10 ^ 122 * ((P.G ^ 4 * P.U ^ 20 / S.Δ
        + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
          * (S.Δ * S.Ω) / Real.sqrt L)
      = 10 ^ 122 * ((P.G ^ 4 * P.U ^ 20 / S.Δ
          + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
            * (S.Δ * S.Ω)) / Real.sqrt L from by ring]
  rw [div_le_div_iff_of_pos_right hsL]
  -- numerator inequality: 8a·errU ≤ 10¹²²·(G⁴U²⁰/Δ + T)·ΔΩ, via a ≤ 11ΔΩ
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_hi; exact ha_hi
  have hE0 := step4ErrU_nonneg (P := P) (S := S)
  have h8a : 8 * a * step4ErrU P S ≤ 88 * (S.Δ * S.Ω) * step4ErrU P S := by
    nlinarith [hE0, haA]
  refine h8a.trans ?_
  rw [show 10 ^ 122 * ((P.G ^ 4 * P.U ^ 20 / S.Δ
      + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14)) * (S.Δ * S.Ω))
    = (10 ^ 122 * (P.G ^ 4 * P.U ^ 20 / S.Δ
        + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))) * (S.Δ * S.Ω) from by ring,
    show 88 * (S.Δ * S.Ω) * step4ErrU P S = (88 * step4ErrU P S) * (S.Δ * S.Ω) from by ring]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  -- per-piece: 88·errU ≤ 10¹²²·(G⁴U²⁰/Δ + T)
  -- core monomial comparison: 616·10¹⁰⁶·U¹⁵·Δ ≤ H·Ω¹¹ — band-paid (`Ω⁻⁸ ≤ G²U⁶`)
  have hpay8 := band_pay8 (P := P) (S := S) hband
  have hΔ16 : 616 * 10 ^ 106 * (P.G ^ 2 * P.U ^ 16) ≤ S.Δ := by
    have hU4 : (616:ℝ) * 10 ^ 91 ≤ P.U ^ 4 := by
      calc (616:ℝ) * 10 ^ 91 ≤ (10:ℝ) ^ 94 := by norm_num
        _ ≤ (10:ℝ) ^ 132 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 4 := by rw [← pow_mul]
        _ ≤ P.U ^ 4 := pow_le_pow_left₀ (by norm_num) hUbig 4
    have hG24 : P.G ^ 2 ≤ P.G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
    calc 616 * 10 ^ 106 * (P.G ^ 2 * P.U ^ 16)
        = 10 ^ 15 * (616 * 10 ^ 91) * (P.G ^ 2 * P.U ^ 16) := by ring
      _ ≤ 10 ^ 15 * P.U ^ 4 * (P.G ^ 2 * P.U ^ 16) := by
          gcongr 10 ^ 15 * ?_ * (P.G ^ 2 * P.U ^ 16)
      _ = 10 ^ 15 * (P.G ^ 2 * P.U ^ 20) := by ring
      _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
          have h1' : P.G ^ 2 * P.U ^ 20 ≤ P.G ^ 4 * P.U ^ 20 :=
            mul_le_mul_of_nonneg_right hG24 (by positivity)
          have h2' : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 20 := by positivity
          linarith
      _ ≤ S.Δ := hDeW
  have ht3core : 616 * 10 ^ 106 * (P.U ^ 15 * S.Δ) ≤ P.H * S.Ω ^ 11 := by
    calc 616 * 10 ^ 106 * (P.U ^ 15 * S.Δ)
        = (616 * 10 ^ 106 * (P.U ^ 15 * S.Δ)) * 1 := (mul_one _).symm
      _ ≤ (616 * 10 ^ 106 * (P.U ^ 15 * S.Δ)) * (P.G ^ 2 * P.U ^ 6 * S.Ω ^ 8) :=
          mul_le_mul_of_nonneg_left hpay8 (by positivity)
      _ = (616 * 10 ^ 106 * (P.G ^ 2 * P.U ^ 16)) * (P.U ^ 5 * S.Δ) * S.Ω ^ 8 := by ring
      _ ≤ S.Δ * (P.U ^ 5 * S.Δ) * S.Ω ^ 8 := by
          gcongr ?_ * (P.U ^ 5 * S.Δ) * S.Ω ^ 8
      _ = S.Δ ^ 2 * P.U ^ 5 * S.Ω ^ 8 := by ring
      _ ≤ (P.H * S.Ω ^ 3) * S.Ω ^ 8 := mul_le_mul_of_nonneg_right hReg (by positivity)
      _ = P.H * S.Ω ^ 11 := by ring
  have ht3 : 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
        * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
      ≤ (1 / 88) * (P.G ^ 4 * P.U ^ 20 / S.Δ) := by
    rw [show S.D = P.H * S.Δ from rfl]
    have hLHSeq : 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / (P.H * S.Δ)
          * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        = 7 * 10 ^ 106 * (P.G ^ 4 * P.U ^ 35) / (P.H * S.Ω ^ 11) := by
      field_simp
      ring
    have hRHSeq : (1 / 88 : ℝ) * (P.G ^ 4 * P.U ^ 20 / S.Δ)
        = P.G ^ 4 * P.U ^ 20 / (88 * S.Δ) := by
      rw [div_mul_div_comm, one_mul]
    rw [hLHSeq, hRHSeq, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 7 * 10 ^ 106 * (P.G ^ 4 * P.U ^ 35) * (88 * S.Δ)
        = (P.G ^ 4 * P.U ^ 20) * (616 * 10 ^ 106 * (P.U ^ 15 * S.Δ)) := by ring
      _ ≤ (P.G ^ 4 * P.U ^ 20) * (P.H * S.Ω ^ 11) :=
          mul_le_mul_of_nonneg_left ht3core (by positivity)
      _ = P.G ^ 4 * P.U ^ 20 * (P.H * S.Ω ^ 11) := by ring
  have ht1 : 88 * (10 ^ 11 * P.Wval ^ 4 / S.Δ) = 88 * 10 ^ 11 * (P.G ^ 4 * P.U ^ 20 / S.Δ) := by
    rw [show P.Wval = P.G * P.U ^ 5 from rfl]
    ring
  have hTnn : (0:ℝ) ≤ S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14) := by positivity
  have hbnn : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 20 / S.Δ := by positivity
  have hUeq : UpsT P S = S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14) := rfl
  unfold step4ErrU
  rw [hUeq]
  linarith [ht3, ht1.le, ht1.ge, hTnn, hbnn]

/-- `cEhyb ≥ 0` (mirror of `Step4Band5`'s private `Ecap4_nonneg`, plus the two gap pieces). -/
theorem cEhyb_nonneg' {a ℓ₁ ℓ₂ gap : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hgap0 : 0 ≤ gap) :
    0 ≤ cEhyb P S a ℓ₁ ℓ₂ gap := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hB : (0:ℝ) < S.B := by unfold Scale.B; positivity
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hlt : ℓ₁ < ℓ₂ := by linarith
  have hEcap : (0:ℝ) ≤ Ecap4a P S a ℓ₁ ℓ₂ := Ecap4a_nonneg hℓ1 hℓ12
  have hL : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by
    have : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
    positivity
  unfold cEhyb
  have hnum : (0:ℝ) ≤ 10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2
      + 10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)
      + 4 * a * Ecap4a P S a ℓ₁ ℓ₂ := by
    have h1' : (0:ℝ) ≤ 10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2 := by positivity
    have h2' : (0:ℝ) ≤ 10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D) := by
      positivity
    have h3' : (0:ℝ) ≤ 4 * a * Ecap4a P S a ℓ₁ ℓ₂ := by
      have := mul_nonneg (by positivity : (0:ℝ) ≤ 4 * a) hEcap
      linarith [this]
    linarith
  exact div_nonneg hnum (Real.sqrt_nonneg _)

/-- `cE2hyb ≥ 0` and `cChyb ≥ 0`. -/
theorem cE2hyb_nonneg' {a ℓ₁ ℓ₂ : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) : 0 ≤ cE2hyb P S a ℓ₁ ℓ₂ := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have h2l : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  unfold cE2hyb
  positivity

theorem cChyb_nonneg' {a ℓ₁ ℓ₂ : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) : 0 ≤ cChyb P S a ℓ₁ ℓ₂ := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hB : (0:ℝ) < S.B := by unfold Scale.B; positivity
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hL : (0:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by
    have h2 : (0:ℝ) < ℓ₂ := by linarith
    have h3 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
    positivity
  have hE0 : (0:ℝ) ≤ Ecap4p3 P S ℓ₁ ℓ₂ := Ecap4p3_nonneg hℓ1 hℓ12
  unfold cChyb
  have hM0 : (0:ℝ) ≤ 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3
      / (S.Δ ^ 3 * S.D) := by positivity
  have hQ0 : (0:ℝ) ≤ 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) :=
    div_nonneg (by positivity) (Real.sqrt_nonneg _)
  linarith

end Squarefree
