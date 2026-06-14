import Squarefree.Lower.Step4Combine
import Squarefree.Lower.UpsilonWitness
import Squarefree.Lower.Step3VBound
import Squarefree.Lower.DefectClose
import Squarefree.Lower.DefectBt
import Squarefree.Lower.Step1Witness
import Squarefree.Lower.Prop51Partition

/-!
# §5 Step-4 per-`r` `s`-extraction from `dStar` witnesses (writeup 992–1043)

`sigma_s_extract_from_witness` is the §5 Step-4 analogue of `Qval_abs_le_from_witness`
(`Step3QWitness.lean`): given the three `D`-scale witnesses `dStar r, dStar (r+ℓ₁),
dStar (r+ℓ₂)` (the triple-set shape) it produces the nonzero integer `s` of writeup 1035 with
`1 ≤ |s| ≤ 10¹¹¹·G⁵U³⁵/Ω⁸` such that the second-difference closed form `Σ_closed`, evaluated at
the **integer witness** `d = dStar r`, `b₀ = (dStar(r+ℓ₁) − dStar r)/ℓ₁`, `v = vval r`, satisfies

```
distInt (Σ_closed P.X a b₀ (vval r) (dStar r) ℓ₁ ℓ₂ − s)
  ≤ 45·Wval⁴/Δ + 10¹¹⁰·UpsT.
```

Where Step-3's `Qval_abs_le_from_witness` threads the three `inDa`/d*-window witnesses into the
first-difference `Q_distInt_le`, this lemma threads the SAME witness bundle into the
second-difference near-integer keystone `Sigma_closed_near_int` (`Step4Combine.lean`) and then a
`round_extract_core`-style rounding extraction (the magnitude facts of `leading_abs_ge` /
`leading_abs_le`).

## The integer-witness identification (the genuinely-new connector)

The ten `inD`-facts of `Sigma_closed_near_int` are recognised from the three `inDa` witnesses by
the b/d telescoping: with `d := dStar r`, `d₁ := dStar (r+ℓ₁)`, `d₂ := dStar (r+ℓ₂)`,

  `b₁ℤ = ℓ₁b₀ = d₁ − d`,  `b₂ℤ = ℓ₂b₀ + v = d₂ − d`,  `b₃ℤ = (ℓ₂−ℓ₁)b₀ + v = d₂ − d₁`,
  `d'ℤ = d + ℓ₁b₀ = d₁`,

so the ten spacing points `{d, d+a, d+b₁, d+a+b₁, d+b₂, d+a+b₂, d', d'+a, d'+b₃, d'+a+b₃}` are
exactly `{d, d+a, d₁, d₁+a, d₂, d₂+a, d₁, d₁+a, d₂, d₂+a}`, each an `inD`-component of one of the
three `inDa P.X P.H a {d,d₁,d₂}` witnesses.

## Note on the SMOOTH `d̃ₐ`-form (surfaced, not faked)

`step4_confine_two` (piece 2) consumes `Σ_closed` at the **smooth** `d̃ₐ(r) = dtilde P.X r a`,
not the integer witness `dStar r`.  The bridge `|Σ_closed(d̃ₐ, b̃ₐ) − Σ_closed(dStar, b₀)| ≤ δ'`
(the second-difference analogue of Step-3's `phi_d_replace`/`v_replace_le` chain) is a SEPARATE
smoothing identity that does **not** currently exist for `Σ_closed`.  This file proves the
integer-witness `s`-extraction the available ingredients directly support.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000

/-- Combined Taylor window with the defect term `|v|`: `4(a + W·|b₀| + |v|) ≤ dd`, for `W = GU⁵`
the slope cap (so `(ℓ:ℝ) ≤ W` covers `ℓ₂`, `ℓ₂−ℓ₁`).  Same scale arithmetic as
`step1_window_bound` with the extra `4|v|` absorbed via `|v| ≤ 10²⁰·ΔU⁵/Ω³`. -/
private theorem window_with_v {Wc b₀ v dd : ℝ}
    (ha_hi : (0:ℝ) ≤ 11 * S.A) (haA : ∃ a : ℝ, a ≤ 11 * S.A ∧ 0 ≤ a) (hWc : Wc ≤ 130 * P.Wval)
    (hWcnn : 0 ≤ Wc) (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hdD : S.D ≤ dd) (hRUW : P.U * P.Wval ≤ S.R)
    (hΩU : S.Ω ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U) :
    ∀ a : ℝ, a ≤ 11 * S.A → 0 ≤ a → 4 * (a + Wc * |b₀| + |v|) ≤ dd := by
  intro a ha_hi' ha_nn
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hUpos := P.U_pos
  refine le_trans ?_ hdD
  -- cleared core: U⁶Δ ≤ HΩ³
  have hcore : P.U ^ 6 * S.Δ ≤ P.H * S.Ω ^ 3 := by
    have hRUW' : P.U * (P.G * P.U ^ 5) ≤ P.H * P.G * S.Ω ^ 3 / S.Δ := by
      simpa [Globals.Wval, Scale.R] using hRUW
    rw [le_div_iff₀ hΔ] at hRUW'
    have hcancel : P.G * (P.U ^ 6 * S.Δ) ≤ P.G * (P.H * S.Ω ^ 3) := by nlinarith [hRUW']
    exact le_of_mul_le_mul_left hcancel hG
  have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ (le_of_lt hΩ) hΩU 4
  have hΩ3pos : (0:ℝ) < S.Ω ^ 3 := by positivity
  -- slope: Wc·|b₀| ≤ 3e12·U⁵Δ²/Ω³
  have hWcW : Wc ≤ 130 * (P.G * P.U ^ 5) := by simpa [Globals.Wval] using hWc
  have hslope : Wc * |b₀| ≤ 130 * (P.G * P.U ^ 5) * (3000000000000 * S.B) := by
    apply mul_le_mul hWcW hb0 (abs_nonneg _); positivity
  have hslope2 : Wc * |b₀| ≤ 390000000000000 * P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 := by
    refine le_trans hslope ?_
    rw [Scale.B, le_div_iff₀ hΩ3pos]; field_simp; nlinarith [hΩ3pos, hG]
  -- the |v| bound, in Ω³-cleared form: |v|·Ω³ ≤ 1e20·ΔU⁵
  have hvΩ : |v| * S.Ω ^ 3 ≤ 10 ^ 20 * (S.Δ * P.U ^ 5) := by
    have h := mul_le_mul_of_nonneg_right hv (le_of_lt hΩ3pos)
    rw [show (10:ℝ) ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) * S.Ω ^ 3
        = 10 ^ 20 * (S.Δ * P.U ^ 5) by field_simp] at h
    exact h
  -- the slope, in Ω³-cleared form
  have hslope3 : Wc * |b₀| * S.Ω ^ 3 ≤ 390000000000000 * P.U ^ 5 * S.Δ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hslope2 (le_of_lt hΩ3pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hΩ3pos)] at this
  have ha_hi'' : a ≤ 11 * (S.Δ * S.Ω) := by simpa [Scale.A] using ha_hi'
  have ha3 : a * S.Ω ^ 3 ≤ 11 * (S.Δ * S.Ω) * S.Ω ^ 3 :=
    mul_le_mul_of_nonneg_right ha_hi'' (le_of_lt hΩ3pos)
  -- KEY: 44Ω⁴ + 12e12·U⁵Δ + 4e20·ΔU⁵ ≤ HΩ³ ; reduce to U⁶Δ ≤ HΩ³
  have hKEY : 44 * S.Ω ^ 4 + 1560000000000000 * P.U ^ 5 * S.Δ
        + 400000000000000000000 * (S.Δ * P.U ^ 5) ≤ P.H * S.Ω ^ 3 := by
    -- both U⁵-terms ≤ U⁶Δ/2 each (since 9e20 ≤ U) and 88Ω⁴ ≤ U⁶Δ
    have hU8 : (900000000000000000000:ℝ) ≤ P.U := by nlinarith [hUbig]
    have hUΔ : (0:ℝ) < P.U ^ 5 * S.Δ := by positivity
    have hb : 900000000000000000000 * P.U ^ 5 * S.Δ ≤ P.U ^ 6 * S.Δ := by
      have : 900000000000000000000 * P.U ^ 5 ≤ P.U * P.U ^ 5 :=
        mul_le_mul_of_nonneg_right hU8 (by positivity)
      nlinarith [this, hΔ]
    have hc : 88 * S.Ω ^ 4 ≤ P.U ^ 6 * S.Δ := by
      have hU2Δ : (88:ℝ) ≤ P.U ^ 2 * S.Δ := by nlinarith [hUbig, hΔ1]
      have h1 : 88 * P.U ^ 4 ≤ P.U ^ 6 * S.Δ := by
        nlinarith [hU2Δ, pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 4]
      nlinarith [hΩ4, h1, pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 4]
    nlinarith [hb, hc, hcore, hUΔ]
  rw [Scale.D, ← mul_le_mul_iff_of_pos_right hΩ3pos]
  -- target: 4(a + Wc|b₀| + |v|)·Ω³ ≤ H·Δ·Ω³
  have hKEYΔ : (44 * S.Ω ^ 4 + 1560000000000000 * P.U ^ 5 * S.Δ
        + 400000000000000000000 * (S.Δ * P.U ^ 5)) * S.Δ ≤ P.H * S.Ω ^ 3 * S.Δ :=
    mul_le_mul_of_nonneg_right hKEY (le_of_lt hΔ)
  -- the accumulated LHS bound:  4(a+Wc|b₀|+|v|)Ω³ ≤ 44ΔΩ⁴ + 12e12U⁵Δ² + 4e20Δ²U⁵
  have hsum : 4 * (a + Wc * |b₀| + |v|) * S.Ω ^ 3
      ≤ 4 * (11 * (S.Δ * S.Ω) * S.Ω ^ 3) + 4 * (390000000000000 * P.U ^ 5 * S.Δ ^ 2)
          + 4 * (10 ^ 20 * (S.Δ * P.U ^ 5)) := by nlinarith [ha3, hslope3, hvΩ, hΩ3pos]
  refine le_trans hsum ?_
  have hΔU : 400000000000000000000 * (S.Δ * P.U ^ 5)
      ≤ 400000000000000000000 * (S.Δ * P.U ^ 5) * S.Δ := by
    nlinarith [hΔ1, mul_pos hΔ (pow_pos hUpos 5)]
  nlinarith [hKEYΔ, hΔU]

/-- **§5 Step-4 per-`r` integer `s`-extraction from `dStar` witnesses** (writeup 1033–1043). -/
theorem sigma_s_extract_from_witness {a : ℤ} {ℓ₁ ℓ₂ r : ℕ} {dStar : ℕ → ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hr1_hi : (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
    (hr2_hi : (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
    (hinDa  : inDa P.X P.H a (dStar r))
    (hinDa1 : inDa P.X P.H a (dStar (r + ℓ₁)))
    (hinDa2 : inDa P.X P.H a (dStar (r + ℓ₂)))
    (hdwin : S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D)
    (hd1win : S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D)
    (hd2win : S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D)
    (hRd  : |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hRd1 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))|
        ≤ 14 * P.H / S.D)
    (hRd2 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))|
        ≤ 14 * P.H / S.D)
    (hd1ned : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ))
    (hd2ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
    (hd21ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar (r + ℓ₁) : ℝ))
    -- ★ the integer-witness SIGN/PLACEMENT data, now in the genuine `bᵢ ≤ 0` (decreasing-`d̃ₐ`)
    --   form consumed by the reflected keystone `Upsilon_near_int_neg`.  For the actual
    --   decreasing-`d̃ₐ` triples one has `d₂ ≤ d₁ ≤ d` (`b₀ ≤ 0`): the three shifts are
    --   `bᵢ ≤ 0`, and the placement is the reflected `a + |bᵢ| ≤ dᵢ+bᵢ` form (writeup-1001
    --   placement `a + 2|bᵢ| ≤ d`).  The window part `S.D ≤ dᵢ+bᵢ` is NOT a hypothesis: it is
    --   discharged from the `[D,2D]` windows `hd1win`/`hd2win` of the shifted `d*`-witnesses.
    (hb1sgn : dStar (r + ℓ₁) - dStar r ≤ (0:ℤ))
    (hb2sgn : dStar (r + ℓ₂) - dStar r ≤ (0:ℤ))
    (hb3sgn : dStar (r + ℓ₂) - dStar (r + ℓ₁) ≤ (0:ℤ))
    (hplace1 : a + (dStar r - dStar (r + ℓ₁)) ≤ dStar (r + ℓ₁))
    (hplace2 : a + (dStar r - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    (hplace3 : a + (dStar (r + ℓ₁) - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |vval P a dStar ℓ₁ ℓ₂ r|)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 55 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    ∃ s : ℤ, s ≠ 0
      ∧ (1 : ℝ) ≤ |(s : ℝ)|
      ∧ |(s : ℝ)| ≤ 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
      ∧ distInt (Sigma_closed P.X (a : ℝ)
            (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
            (vval P a dStar ℓ₁ ℓ₂ r) (dStar r : ℝ) ℓ₁ ℓ₂ - (s : ℝ))
          ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S := by
  -- ===== SETUP =====
  set d : ℤ := dStar r with hd_def
  set d₁ : ℤ := dStar (r + ℓ₁) with hd1_def
  set d₂ : ℤ := dStar (r + ℓ₂) with hd2_def
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hℓ1Z : (0 : ℤ) < (ℓ₁ : ℤ) := by exact_mod_cast hℓ1
  have hℓ12Z : (ℓ₁ : ℤ) < (ℓ₂ : ℤ) := by exact_mod_cast hℓ12
  have hℓ1_loZ : (1 : ℤ) ≤ (ℓ₁ : ℤ) := hℓ1Z
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12Z
  have hℓ2R : (0 : ℝ) < ((ℓ₂ : ℤ) : ℝ) := lt_trans hℓ1R hℓ12R
  have hℓ1_loR : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1_loZ
  have hℓ2_lo : (1 : ℤ) ≤ (ℓ₂ : ℤ) := le_of_lt (lt_of_le_of_lt hℓ1_loZ hℓ12Z)
  have hℓ1nn : (0 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := le_of_lt hℓ1R
  have hℓ2nn : (0 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_of_lt hℓ2R
  have hℓ1W : ((ℓ₁ : ℤ) : ℝ) ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12R) hℓ2W
  have hr_hi16 : (r : ℝ) ≤ 16 * S.R := le_trans (by linarith) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by linarith
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by linarith
  have ha_nn : (0:ℝ) ≤ (a:ℝ) := le_of_lt ha0R
  have h11Ann : (0:ℝ) ≤ 11 * S.A := by have := S.Δ_pos; have := S.Ω_pos; rw [Scale.A]; positivity
  -- ===== closeness ×3 =====
  have hd_close : |(d : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hd2_close : |(d₂ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2
  have hDS_pos : 0 < S.D := by rw [Scale.D]; have := P.H_pos; have := S.Δ_pos; positivity
  have hd_pos : 0 < (d : ℝ) := lt_of_lt_of_le hDS_pos hdwin.1
  -- ===== b₀ / v =====
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / ((ℓ₁ : ℤ) : ℝ) with hb₀_def
  set v : ℝ := ((d₂ : ℝ) - (d : ℝ)) - ((ℓ₂ : ℤ) : ℝ) * b₀ with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₁ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
  have hRUW : P.U * P.Wval ≤ S.R := U_mul_W_le_R (S := S) h1 hband hΩU hΔ1 hU1
  -- pinning
  have hb0def : ((ℓ₁ : ℤ) : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ) := by rw [hb₀_def]; field_simp
  have hvdef : ((ℓ₂ : ℤ) : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ) := by rw [hv_def]; ring
  have hb3def : (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v = (d₂ : ℝ) - (d₁ : ℝ) := by
    rw [hv_def, hb₀_def]; field_simp; ring
  have hd'def : (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ = (d₁ : ℝ) := by rw [hb0def]; ring
  -- the v bound `|v| ≤ 10²⁰·ΔU⁵/Ω³` via v_defect_le
  have hv_shape : v = ((d₂ : ℝ) - (d : ℝ))
      - (((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ)) * ((d₁ : ℝ) - (d : ℝ)) := by
    rw [hv_def, hb₀_def]; ring
  have hvd := v_defect_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) (d := d) (d₁ := d₁) (d₂ := d₂)
    hAD ha0 ha_lo ha_hi hℓ1Z hℓ1_loZ hℓ12Z hℓ2W hr_lo hr2_hi
    hd_close hd1_close hd2_close h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    rw [hv_shape]
    refine le_trans hvd ?_
    have hnn : (0 : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by positivity
    gcongr; norm_num
  -- the vval-shape identity (the function-form v equals the `vval` defect)
  have hvval_eq : vval P a dStar ℓ₁ ℓ₂ r = v := by
    rw [vval, hv_shape, hd_def, hd1_def, hd2_def]
  -- ===== windows: hwin (b₂) and hwin3 (b₃) via window_with_v =====
  have hwinv : ∀ a' : ℝ, a' ≤ 11 * S.A → 0 ≤ a'
      → 4 * (a' + ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v|) ≤ (d : ℝ) :=
    window_with_v (S := S) (Wc := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v) (dd := (d : ℝ))
      h11Ann ⟨(a:ℝ), ha_hi, ha_nn⟩ hℓ2W hℓ2nn hb0 hv hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin : 4 * ((a : ℝ) + ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v|) ≤ (d : ℝ) := hwinv (a:ℝ) ha_hi ha_nn
  have hwin3v : ∀ a' : ℝ, a' ≤ 11 * S.A → 0 ≤ a'
      → 4 * (a' + ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v|) ≤ (d₁ : ℝ) :=
    window_with_v (S := S) (Wc := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v) (dd := (d₁ : ℝ))
      h11Ann ⟨(a:ℝ), ha_hi, ha_nn⟩ hℓ2W hℓ2nn hb0 hv hd1win.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin3 : 4 * ((a : ℝ) + |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v|)
      ≤ (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ := by
    rw [hd'def]
    have hb3le : |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v|
        ≤ ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v| := by
      calc |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v|
          ≤ |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀| + |v| := abs_add_le _ _
        _ = |((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)| * |b₀| + |v| := by rw [abs_mul]
        _ ≤ ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v| := by
            have : |((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)| ≤ ((ℓ₂ : ℤ) : ℝ) := by
              rw [abs_of_nonneg (by linarith [hℓ12R] : (0:ℝ) ≤ ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))]
              linarith [hℓ1R]
            have hb0nn : (0:ℝ) ≤ |b₀| := abs_nonneg _
            nlinarith [this, hb0nn]
    have := hwin3v (a:ℝ) ha_hi ha_nn
    nlinarith [hb3le, this]
  have hshiftpos : 0 < (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ := by
    rw [hd'def]; exact lt_of_lt_of_le hDS_pos hd1win.1
  have hshift2 : (d : ℝ) / 2 ≤ (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ := by
    rw [hd'def]; nlinarith [hdwin.2, hd1win.1, hDS_pos]
  -- nonzero shift facts (from the distinctness of the witnesses)
  have hb1ne : ((ℓ₁ : ℤ) : ℝ) * b₀ ≠ 0 := by
    rw [hb0def]; intro h; exact hd1ned (by linarith [sub_eq_zero.mp h])
  have hb2ne : ((ℓ₂ : ℤ) : ℝ) * b₀ + v ≠ 0 := by
    rw [hvdef]; intro h; exact hd2ned (by linarith [sub_eq_zero.mp h])
  have hb3ne : (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v ≠ 0 := by
    rw [hb3def]; intro h; exact hd21ned (by linarith [sub_eq_zero.mp h])
  -- the band hypothesis for the magnitude lemmas: 1 ≤ G·U³·Ω⁴
  have hband4 : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
  -- ===== the integer-witness coherence (b/d telescoping) =====
  have hacoh : (a : ℝ) = ((a : ℤ) : ℝ) := rfl
  have hdcoh : (d : ℝ) = ((d : ℤ) : ℝ) := by norm_cast
  have hd'coh : (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ = ((d₁ : ℤ) : ℝ) := hd'def
  have hℓ1coh : ((ℓ₁ : ℤ) : ℝ) = (((ℓ₁ : ℤ)) : ℝ) := rfl
  have hℓ2coh : ((ℓ₂ : ℤ) : ℝ) = (((ℓ₂ : ℤ)) : ℝ) := rfl
  have hb1coh : ((ℓ₁ : ℤ) : ℝ) * b₀ = (((d₁ - d : ℤ)) : ℝ) := by rw [hb0def]; push_cast; ring
  have hb2coh : ((ℓ₂ : ℤ) : ℝ) * b₀ + v = (((d₂ - d : ℤ)) : ℝ) := by rw [hvdef]; push_cast; ring
  have hb3coh : (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v = (((d₂ - d₁ : ℤ)) : ℝ) := by
    rw [hb3def]; push_cast; ring
  -- sign facts `bᵢ ≤ 0` (decreasing `d̃ₐ`), cast to the `d,d₁,d₂` shape
  have hb1sgn' : (d₁ - d : ℤ) ≤ 0 := hb1sgn
  have hb2sgn' : (d₂ - d : ℤ) ≤ 0 := hb2sgn
  have hb3sgn' : (d₂ - d₁ : ℤ) ≤ 0 := hb3sgn
  -- reflected placement: `aℤ + (−bᵢℤ) ≤ dᵢ+bᵢ`, where `dᵢ+bᵢ` is the shifted base point.
  -- `d + (d₁−d) = d₁`, `d + (d₂−d) = d₂`, `d₁ + (d₂−d₁) = d₂`.
  have hab1 : ((a : ℤ) : ℝ) + ((-(d₁ - d) : ℤ) : ℝ) ≤ ((d + (d₁ - d) : ℤ) : ℝ) := by
    have h : (a : ℝ) + ((d : ℝ) - (d₁ : ℝ)) ≤ (d₁ : ℝ) := by exact_mod_cast hplace1
    rw [show d + (d₁ - d) = d₁ by ring]; push_cast; linarith
  have hab2 : ((a : ℤ) : ℝ) + ((-(d₂ - d) : ℤ) : ℝ) ≤ ((d + (d₂ - d) : ℤ) : ℝ) := by
    have h : (a : ℝ) + ((d : ℝ) - (d₂ : ℝ)) ≤ (d₂ : ℝ) := by exact_mod_cast hplace2
    rw [show d + (d₂ - d) = d₂ by ring]; push_cast; linarith
  have hab3 : ((a : ℤ) : ℝ) + ((-(d₂ - d₁) : ℤ) : ℝ) ≤ ((d₁ + (d₂ - d₁) : ℤ) : ℝ) := by
    have h : (a : ℝ) + ((d₁ : ℝ) - (d₂ : ℝ)) ≤ (d₂ : ℝ) := by exact_mod_cast hplace3
    rw [show d₁ + (d₂ - d₁) = d₂ by ring]; push_cast; linarith
  -- the 𝒟-membership facts (from the three `inDa` witnesses, telescoped)
  obtain ⟨_, hinD_d, hinD_da, _⟩ := hinDa
  obtain ⟨_, hinD_d1, hinD_d1a, _⟩ := hinDa1
  obtain ⟨_, hinD_d2, hinD_d2a, _⟩ := hinDa2
  -- the ten spacing points of `Sigma_closed_near_int`, recognised from the three witnesses
  have hS1_0 : inD P.X P.H d := hinD_d
  have hS1_1 : inD P.X P.H (d + a) := hinD_da
  have hS1_2 : inD P.X P.H (d + (d₁ - d)) := by rw [show d + (d₁ - d) = d₁ by ring]; exact hinD_d1
  have hS1_3 : inD P.X P.H (d + a + (d₁ - d)) := by
    rw [show d + a + (d₁ - d) = d₁ + a by ring]; exact hinD_d1a
  have hS2_2 : inD P.X P.H (d + (d₂ - d)) := by rw [show d + (d₂ - d) = d₂ by ring]; exact hinD_d2
  have hS2_3 : inD P.X P.H (d + a + (d₂ - d)) := by
    rw [show d + a + (d₂ - d) = d₂ + a by ring]; exact hinD_d2a
  have hS3_0 : inD P.X P.H d₁ := hinD_d1
  have hS3_1 : inD P.X P.H (d₁ + a) := hinD_d1a
  have hS3_2 : inD P.X P.H (d₁ + (d₂ - d₁)) := by
    rw [show d₁ + (d₂ - d₁) = d₂ by ring]; exact hinD_d2
  have hS3_3 : inD P.X P.H (d₁ + a + (d₂ - d₁)) := by
    rw [show d₁ + a + (d₂ - d₁) = d₂ + a by ring]; exact hinD_d2a
  -- window facts for the SHIFTED base points `d+bᵢ` (= the `d*`-witness `[D,2D]` windows):
  -- `d + (d₁−d) = d₁`, `d + (d₂−d) = d₂`, `d₁ + (d₂−d₁) = d₂`.
  have hDd1 : S.D ≤ ((d + (d₁ - d) : ℤ) : ℝ) := by
    rw [show d + (d₁ - d) = d₁ by ring]; exact_mod_cast hd1win.1
  have hDd2 : S.D ≤ ((d + (d₂ - d) : ℤ) : ℝ) := by
    rw [show d + (d₂ - d) = d₂ by ring]; exact_mod_cast hd2win.1
  have hDd3 : S.D ≤ ((d₁ + (d₂ - d₁) : ℤ) : ℝ) := by
    rw [show d₁ + (d₂ - d₁) = d₂ by ring]; exact_mod_cast hd2win.1
  -- ===== (1) the integer `Υ_Ŝ` near-integer bound (`Upsilon_near_int_neg`), with coherence =====
  set UpsSh : ℝ :=
    ((ℓ₂ : ℤ) : ℝ) ^ 2 * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) ^ 2 * Shat P.X (a : ℝ) (((ℓ₁ : ℤ) : ℝ) * b₀) (d : ℝ)
      - ((ℓ₁ : ℤ) : ℝ) ^ 2 * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) ^ 2 * Shat P.X (a : ℝ) (((ℓ₂ : ℤ) : ℝ) * b₀ + v) (d : ℝ)
      + ((ℓ₁ : ℤ) : ℝ) ^ 2 * ((ℓ₂ : ℤ) : ℝ) ^ 2 * Shat P.X (a : ℝ) ((((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v) ((d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀)
    with hUpsSh_def
  have hnearI := Upsilon_near_int_neg (P := P) S (a := a) (d := d) (d' := d₁)
    (b₁ := d₁ - d) (b₂ := d₂ - d) (b₃ := d₂ - d₁) (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ))
    (by exact_mod_cast le_of_lt ha0) hb1sgn' hb2sgn' hb3sgn'
    (by exact_mod_cast le_of_lt hℓ1Z) (le_of_lt hℓ12Z) (by exact_mod_cast hℓ2W)
    hDd1 hDd2 hDd3 hab1 hab2 hab3
    hS1_0 hS1_1 hS1_2 hS1_3 hS2_2 hS2_3 hS3_0 hS3_1 hS3_2 hS3_3
  -- rewrite the integer Υ to `UpsSh` via the coherence equalities
  have hUpsSh_eq :
      (((ℓ₂ ^ 2 * ((ℓ₂ : ℤ) - (ℓ₁ : ℤ)) ^ 2 : ℤ)) : ℝ) * Shat P.X (a : ℝ) (((d₁ - d : ℤ)) : ℝ) ((d : ℤ) : ℝ)
        - (((ℓ₁ ^ 2 * ((ℓ₂ : ℤ) - (ℓ₁ : ℤ)) ^ 2 : ℤ)) : ℝ) * Shat P.X (a : ℝ) (((d₂ - d : ℤ)) : ℝ) ((d : ℤ) : ℝ)
        + (((ℓ₁ ^ 2 * ℓ₂ ^ 2 : ℤ)) : ℝ) * Shat P.X (a : ℝ) (((d₂ - d₁ : ℤ)) : ℝ) ((d₁ : ℤ) : ℝ)
      = UpsSh := by
    rw [hUpsSh_def, ← hacoh, ← hdcoh, ← hd'coh, ← hb1coh, ← hb2coh, ← hb3coh]
    rw [show (((ℓ₂ : ℕ) ^ 2 * ((ℓ₂ : ℤ) - (ℓ₁ : ℤ)) ^ 2 : ℤ) : ℝ)
          = ((ℓ₂ : ℤ) : ℝ) ^ 2 * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) ^ 2 by push_cast; ring,
        show (((ℓ₁ : ℕ) ^ 2 * ((ℓ₂ : ℤ) - (ℓ₁ : ℤ)) ^ 2 : ℤ) : ℝ)
          = ((ℓ₁ : ℤ) : ℝ) ^ 2 * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) ^ 2 by push_cast; ring,
        show (((ℓ₁ : ℕ) ^ 2 * (ℓ₂ : ℕ) ^ 2 : ℤ) : ℝ)
          = ((ℓ₁ : ℤ) : ℝ) ^ 2 * ((ℓ₂ : ℤ) : ℝ) ^ 2 by push_cast; ring]
  rw [hUpsSh_eq] at hnearI
  -- convert `15·H·(Σ|c|)/D`-style RHS to `45·Wval⁴·H/D = 45·Wval⁴/Δ`
  have hDeq : 10 ^ 11 * P.Wval ^ 4 * P.H / S.D = 10 ^ 11 * P.Wval ^ 4 / S.Δ := by
    rw [Scale.D]; field_simp
  have hnearbd : distInt UpsSh ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ := by rw [← hDeq]; exact hnearI
  -- ===== (2) the expansion error `|UpsSh − Lval| ≤ 10¹¹⁰·UpsT` =====
  set Sc : ℝ := Sigma_closed P.X (a : ℝ) b₀ v (d : ℝ) ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) with hSc
  have hexp0 := Upsilon_expand (X := P.X) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
    (ℓ₁ := ((ℓ₁ : ℤ) : ℝ)) (ℓ₂ := ((ℓ₂ : ℤ) : ℝ)) hXpos ha0R hd_pos hℓ1R hℓ12R
    hb1ne hb2ne hb3ne hwin hwin3 hshiftpos
  rw [← hUpsSh_def] at hexp0
  have htgt_eq : (P.X * (a : ℝ) / (d : ℝ) ^ 5)
      * ((-4 + 10 * (a : ℝ) / (d : ℝ))
        * (Pone b₀ v ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ)
          + Ptwo b₀ v ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) / (d : ℝ)))
      = Sc := rfl
  rw [htgt_eq] at hexp0
  have herr := upsilon_err_le (P := P) (S := S) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
    (ℓ₁ := ((ℓ₁ : ℤ) : ℝ)) (ℓ₂ := ((ℓ₂ : ℤ) : ℝ))
    ha0R ha_hi hℓ1_loR hℓ12R hℓ2W hdwin hb0 hv hshift2 h1 hband4 hG1 hU1 hΔ1 hH1 hΩU hUbig
  have hexp : |UpsSh - Lval P.X (a : ℝ) (d : ℝ) b₀ v ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ)|
      ≤ 10 ^ 119 * UpsT P S := by
    have : Lval P.X (a : ℝ) (d : ℝ) b₀ v ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) = Sc := rfl
    rw [this]; exact le_trans hexp0 herr
  -- ===== (3) extract the nonzero integer `s` from `UpsSh` (the TIGHT near-int bound) =====
  obtain ⟨s, hs0, hsbd, hsnear⟩ :=
    Upsilon_s_extract_of_witness (P := P) (S := S) (a := (a : ℝ)) (ℓ₁ := ((ℓ₁ : ℤ) : ℝ))
      (ℓ₂ := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ)) (Υval := UpsSh)
      hexp hnearbd hAD ha0R ha_lo ha_hi hℓ1_loR hℓ12R hℓ2W hdwin hb0 hv h1 hband4
      hG1 hU1 hΔ1 hH1 hΩU hUbig hΩH hDeW (by rw [hvval_eq] at hv2; exact hv2)
  -- ===== (4) assemble: `distInt(Sc − s) ≤ |Sc − UpsSh| + |UpsSh − s| ≤ 10¹¹⁰·UpsT + 45Wval⁴/Δ`
  refine ⟨s, hs0, ?_, ?_, ?_⟩
  · -- 1 ≤ |s|  (s is a nonzero integer)
    have hsabs : (1 : ℤ) ≤ |s| := Int.one_le_abs hs0
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast hsabs
    rwa [Int.cast_abs, Int.cast_one] at h2
  · -- |s| ≤ 10¹¹¹·(G⁵U³⁵/Ω⁸)
    exact hsbd
  · -- the near-integer bound for `Sc` (= the goal's `Sigma_closed`, up to coercions)
    have hScs : |Sc - (s : ℝ)| ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S := by
      have hSU : |Sc - UpsSh| ≤ 10 ^ 119 * UpsT P S := by
        rw [abs_sub_comm]; exact hexp
      calc |Sc - (s : ℝ)| = |(Sc - UpsSh) + (UpsSh - (s : ℝ))| := by ring_nf
        _ ≤ |Sc - UpsSh| + |UpsSh - (s : ℝ)| := abs_add_le _ _
        _ ≤ 10 ^ 119 * UpsT P S + 10 ^ 11 * P.Wval ^ 4 / S.Δ := add_le_add hSU hsnear
        _ = 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S := by ring
    have hdist : distInt (Sc - (s : ℝ)) ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S := by
      refine le_trans (distInt_le_intDist _ 0) ?_
      rw [Int.cast_zero, sub_zero]; exact hScs
    -- rewrite the goal's `Sigma_closed` into `Sc`
    have hgoal_eq : Sigma_closed P.X (a : ℝ)
          (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
          (vval P a dStar ℓ₁ ℓ₂ r) (dStar r : ℝ) ℓ₁ ℓ₂ = Sc := by
      rw [hSc, Sigma_closed, Sigma_closed, hvval_eq, ← hd_def, ← hd1_def, hb₀_def]
      push_cast
      ring
    rw [hgoal_eq]; exact hdist

end Squarefree
