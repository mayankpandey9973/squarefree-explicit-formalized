import Squarefree.Lower.Step4Magnitude
import Squarefree.Lower.Step4BandPay
import Squarefree.Lower.Step4Enum
import Squarefree.Lower.Step4Smooth
import Squarefree.Lower.Step4SWitness

/-!
# §5 Step-4 large-defect per-`r` `s`-extraction at the SMOOTH point (writeup 1025–1052)

`step4_fiber_extract` is the first focused piece of the §5 large-defect connecting layer.  For a
filtered large-defect triple `r` (`r, r+ℓ₁, r+ℓ₂ ∈ ℛ_a`, `V₂ < |v(r)|`, `|v(r)| ≤ M`) it threads
the per-`r` `dStar`-witness bundle through the SOUND pieces to produce the nonzero integer `s` of
writeup 1035 with `1 ≤ |s| ≤ C·G⁵U³⁵/Ω⁸` such that, at the **smooth** defect `d̃ₐ(r)` (keeping the
witness slope `b₀ = (dStar(r+ℓ₁) − dStar r)/ℓ₁` and defect `v = vval r`),

```
round (Σ_closed P.X a b₀ (vval r) (d̃ₐ r) ℓ₁ ℓ₂) = s.
```

## The sound chain (no vacuous pieces)
* `Sigma_closed_near_int` (`Step4Combine.lean`) — `distInt(Σ_closed(b₀,v,dStar)) ≤ NB + E1`, built
  from `Upsilon_near_int` / `Upsilon_expand` / `upsilon_err_le` at the *integer* witness `dStar`.
* `Sigma_closed_d_smoothing` (`Step4Smooth.lean`) — `|Σ_closed(d̃ₐ) − Σ_closed(dStar)| ≤ δ'·|d̃ₐ−dStar|`
  (the MVT `d`-smoothing bridge, `b₀,v` fixed), giving `distInt(Σ_closed(b₀,v,d̃ₐ)) ≤ NB+E1+δ`.
* `sigma_v2_lower` / `sigma_v2_upper` (`Step4Enum.lean`) — the `s`-free two-sided magnitude bounds
  `c·Lv²/(Δ²Ω²) ≤ |Σ_closed| ≤ C·Lv²/(Δ²Ω²)` at the smooth point, which force `|Σ_closed| > 1/2`
  (so `s := round ≠ 0`, writeup 1025–1033 floor) and cap `|s|`.

This is the witness-`b₀` form consumed by the downstream sound pieces (`sigma_s_confine`,
`sigma_s_magnitude_extract`); the `b₀→b̃ₐ` slope-smoothing of writeup 1044 is a separate identity
tracked elsewhere.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000

/-- Combined Taylor window with the defect term `|v|`: `4(a + W·|b₀| + |v|) ≤ dd`, mirror of
`Step4SWitness.window_with_v` (re-stated here to avoid touching that vacuous file). -/
private theorem fiber_window_with_v {Wc b₀ v dd : ℝ}
    (hWc : Wc ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hdD : S.D ≤ dd) (hRUW : P.U * P.Wval ≤ S.R)
    (hΩU : S.Ω ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U) :
    ∀ a : ℝ, a ≤ 11 * S.A → 0 ≤ a → 4 * (a + Wc * |b₀| + |v|) ≤ dd := by
  intro a ha_hi' ha_nn
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hUpos := P.U_pos
  refine le_trans ?_ hdD
  have hcore : P.U ^ 6 * S.Δ ≤ P.H * S.Ω ^ 3 := by
    have hRUW' : P.U * (P.G * P.U ^ 5) ≤ P.H * P.G * S.Ω ^ 3 / S.Δ := by
      simpa [Globals.Wval, Scale.R] using hRUW
    rw [le_div_iff₀ hΔ] at hRUW'
    have hcancel : P.G * (P.U ^ 6 * S.Δ) ≤ P.G * (P.H * S.Ω ^ 3) := by nlinarith [hRUW']
    exact le_of_mul_le_mul_left hcancel hG
  have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ (le_of_lt hΩ) hΩU 4
  have hΩ3pos : (0:ℝ) < S.Ω ^ 3 := by positivity
  have hWcW : Wc ≤ 130 * (P.G * P.U ^ 5) := by simpa [Globals.Wval] using hWc
  have hslope : Wc * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * S.B) := by
    apply mul_le_mul hWcW hb0 (abs_nonneg _); positivity
  have hslope2 : Wc * |b₀| ≤ 390000000000000 * P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 := by
    refine le_trans hslope ?_
    rw [Scale.B, le_div_iff₀ hΩ3pos]; field_simp; nlinarith [hΩ3pos, hG]
  have hvΩ : |v| * S.Ω ^ 3 ≤ 10 ^ 20 * (S.Δ * P.U ^ 5) := by
    have h := mul_le_mul_of_nonneg_right hv (le_of_lt hΩ3pos)
    rw [show (10:ℝ) ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) * S.Ω ^ 3
        = 10 ^ 20 * (S.Δ * P.U ^ 5) by field_simp] at h
    exact h
  have hslope3 : Wc * |b₀| * S.Ω ^ 3 ≤ 390000000000000 * P.U ^ 5 * S.Δ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hslope2 (le_of_lt hΩ3pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hΩ3pos)] at this
  have ha_hi'' : a ≤ 11 * (S.Δ * S.Ω) := by simpa [Scale.A] using ha_hi'
  have ha3 : a * S.Ω ^ 3 ≤ 11 * (S.Δ * S.Ω) * S.Ω ^ 3 :=
    mul_le_mul_of_nonneg_right ha_hi'' (le_of_lt hΩ3pos)
  have hKEY : 44 * S.Ω ^ 4 + 1560000000000000 * P.U ^ 5 * S.Δ
        + 400000000000000000000 * (S.Δ * P.U ^ 5) ≤ P.H * S.Ω ^ 3 := by
    have hU8 : (800000000000000000000:ℝ) ≤ P.U := by nlinarith [hUbig]
    have hUΔ : (0:ℝ) < P.U ^ 5 * S.Δ := by positivity
    have hb : 800000000000000000000 * P.U ^ 5 * S.Δ ≤ P.U ^ 6 * S.Δ := by
      have : 800000000000000000000 * P.U ^ 5 ≤ P.U * P.U ^ 5 :=
        mul_le_mul_of_nonneg_right hU8 (by positivity)
      nlinarith [this, hΔ]
    have hc : 88 * S.Ω ^ 4 ≤ P.U ^ 6 * S.Δ := by
      have hU2Δ : (88:ℝ) ≤ P.U ^ 2 * S.Δ := by nlinarith [hUbig, hΔ1]
      have h1 : 88 * P.U ^ 4 ≤ P.U ^ 6 * S.Δ := by
        nlinarith [hU2Δ, pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 4]
      nlinarith [hΩ4, h1, pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 4]
    nlinarith [hb, hc, hcore, hUΔ]
  rw [Scale.D, ← mul_le_mul_iff_of_pos_right hΩ3pos]
  have hKEYΔ : (44 * S.Ω ^ 4 + 1560000000000000 * P.U ^ 5 * S.Δ
        + 400000000000000000000 * (S.Δ * P.U ^ 5)) * S.Δ ≤ P.H * S.Ω ^ 3 * S.Δ :=
    mul_le_mul_of_nonneg_right hKEY (le_of_lt hΔ)
  have hsum : 4 * (a + Wc * |b₀| + |v|) * S.Ω ^ 3
      ≤ 4 * (11 * (S.Δ * S.Ω) * S.Ω ^ 3) + 4 * (390000000000000 * P.U ^ 5 * S.Δ ^ 2)
          + 4 * (10 ^ 20 * (S.Δ * P.U ^ 5)) := by nlinarith [ha3, hslope3, hvΩ, hΩ3pos]
  refine le_trans hsum ?_
  have hΔU : 400000000000000000000 * (S.Δ * P.U ^ 5)
      ≤ 400000000000000000000 * (S.Δ * P.U ^ 5) * S.Δ := by
    nlinarith [hΔ1, mul_pos hΔ (pow_pos hUpos 5)]
  nlinarith [hKEYΔ, hΔU]

/-- **Sound witness → `distInt(Σ_closed(b₀,v,dStar))` bound** via `Sigma_closed_near_int_neg`
(the `bᵢ ≤ 0` keystone).  This is the witness→`inD` recognition block of
`sigma_s_extract_from_witness` *without* the vacuous `Upsilon_s_extract_of_witness` step. -/
theorem fiber_near_int_at_witness {a : ℤ} {ℓ₁ ℓ₂ r : ℕ} {dStar : ℕ → ℤ}
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
    (hRd1 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))| ≤ 14 * P.H / S.D)
    (hRd2 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))| ≤ 14 * P.H / S.D)
    (hd1ned : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ))
    (hd2ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
    (hd21ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar (r + ℓ₁) : ℝ))
    (hb1sgn : dStar (r + ℓ₁) - dStar r ≤ (0:ℤ))
    (hb2sgn : dStar (r + ℓ₂) - dStar r ≤ (0:ℤ))
    (hb3sgn : dStar (r + ℓ₂) - dStar (r + ℓ₁) ≤ (0:ℤ))
    (hplace1 : a + (dStar r - dStar (r + ℓ₁)) ≤ dStar (r + ℓ₁))
    (hplace2 : a + (dStar r - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    (hplace3 : a + (dStar (r + ℓ₁) - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    distInt (Sigma_closed P.X (a : ℝ)
        (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
        (vval P a dStar ℓ₁ ℓ₂ r) (dStar r : ℝ) ℓ₁ ℓ₂)
      ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D + 10 ^ 111 * UpsT P S := by
  set d : ℤ := dStar r with hd_def
  set d₁ : ℤ := dStar (r + ℓ₁) with hd1_def
  set d₂ : ℤ := dStar (r + ℓ₂) with hd2_def
  have hHpos : 0 < P.H := P.H_pos
  have hXpos : 0 < P.X := P.X_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ1Z : (0 : ℤ) < (ℓ₁ : ℤ) := by exact_mod_cast hℓ1
  have hℓ12Z : (ℓ₁ : ℤ) < (ℓ₂ : ℤ) := by exact_mod_cast hℓ12
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12Z
  have hℓ1_loR : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ1nn : (0 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := le_of_lt hℓ1R
  have hℓ2nn : (0 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_of_lt (lt_trans hℓ1R hℓ12R)
  have ha_nn : (0:ℝ) ≤ (a:ℝ) := le_of_lt ha0R
  have h11Ann : (0:ℝ) ≤ 11 * S.A := by have := S.Δ_pos; have := S.Ω_pos; rw [Scale.A]; positivity
  have hr_hi16 : (r : ℝ) ≤ 16 * S.R := le_trans (by linarith [hℓ1R]) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by linarith [hℓ1R]
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by linarith [hℓ1R, hℓ12R]
  have hd_close : |(d : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hDS_pos : 0 < S.D := by rw [Scale.D]; have := P.H_pos; have := S.Δ_pos; positivity
  have hd_pos : 0 < (d : ℝ) := lt_of_lt_of_le hDS_pos hdwin.1
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / ((ℓ₁ : ℤ) : ℝ) with hb₀_def
  set v : ℝ := vval P a dStar ℓ₁ ℓ₂ r with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₁ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
  have hRUW : P.U * P.Wval ≤ S.R := U_mul_W_le_R (S := S) h1 hband hΩU hΔ1 hU1
  have hb0def : ((ℓ₁ : ℤ) : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ) := by rw [hb₀_def]; field_simp
  have hvdef : ((ℓ₂ : ℤ) : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ) := by
    rw [hv_def, vval, hb₀_def, hd_def, hd1_def, hd2_def]; field_simp; ring
  have hb3def : (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v = (d₂ : ℝ) - (d₁ : ℝ) := by
    rw [hv_def, vval, hb₀_def, hd_def, hd1_def, hd2_def]; field_simp; ring
  have hd'def : (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ = (d₁ : ℝ) := by rw [hb0def]; ring
  have hvd := v_defect_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) (d := d) (d₁ := d₁) (d₂ := d₂)
    hAD ha0 ha_lo ha_hi hℓ1Z hℓ1Z hℓ12Z hℓ2W hr_lo hr2_hi
    hd_close hd1_close (dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2)
    h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hv_sharp : |v| ≤ 390000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    have hv_shape : v = ((d₂ : ℝ) - (d : ℝ))
        - (((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ)) * ((d₁ : ℝ) - (d : ℝ)) := by
      rw [hv_def, vval, hd_def, hd1_def, hd2_def]
    rw [hv_shape]; exact hvd
  have hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    refine le_trans hv_sharp ?_
    have hnn : (0 : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by positivity
    gcongr; norm_num
  have hwinv := fiber_window_with_v (S := S) (Wc := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v)
    (dd := (d : ℝ)) hℓ2W hb0 hv hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin : 4 * ((a : ℝ) + ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v|) ≤ (d : ℝ) := hwinv (a:ℝ) ha_hi ha_nn
  have hwin3v := fiber_window_with_v (S := S) (Wc := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v)
    (dd := (d₁ : ℝ)) hℓ2W hb0 hv hd1win.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin3 : 4 * ((a : ℝ) + |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v|)
      ≤ (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ := by
    rw [hd'def]
    have hb3le : |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v| ≤ ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v| := by
      calc |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v|
          ≤ |(((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀| + |v| := abs_add_le _ _
        _ = |((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)| * |b₀| + |v| := by rw [abs_mul]
        _ ≤ ((ℓ₂ : ℤ) : ℝ) * |b₀| + |v| := by
            have : |((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)| ≤ ((ℓ₂ : ℤ) : ℝ) := by
              rw [abs_of_nonneg (by linarith [hℓ12R] : (0:ℝ) ≤ ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))]
              linarith [hℓ1R]
            nlinarith [this, abs_nonneg b₀]
    have := hwin3v (a:ℝ) ha_hi ha_nn
    nlinarith [hb3le, this]
  have hshiftpos : 0 < (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ := by
    rw [hd'def]; exact lt_of_lt_of_le hDS_pos hd1win.1
  have hshift2 : (d : ℝ) / 2 ≤ (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ := by
    rw [hd'def]; nlinarith [hdwin.2, hd1win.1, hDS_pos]
  have hb1ne : ((ℓ₁ : ℤ) : ℝ) * b₀ ≠ 0 := by
    rw [hb0def]; intro h; exact hd1ned (by linarith [sub_eq_zero.mp h])
  have hb2ne : ((ℓ₂ : ℤ) : ℝ) * b₀ + v ≠ 0 := by
    rw [hvdef]; intro h; exact hd2ned (by linarith [sub_eq_zero.mp h])
  have hb3ne : (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v ≠ 0 := by
    rw [hb3def]; intro h; exact hd21ned (by linarith [sub_eq_zero.mp h])
  -- coherence
  have hacoh : (a : ℝ) = ((a : ℤ) : ℝ) := rfl
  have hdcoh : (d : ℝ) = ((d : ℤ) : ℝ) := by norm_cast
  have hd'coh : (d : ℝ) + ((ℓ₁ : ℤ) : ℝ) * b₀ = ((d₁ : ℤ) : ℝ) := hd'def
  have hb1coh : ((ℓ₁ : ℤ) : ℝ) * b₀ = (((d₁ - d : ℤ)) : ℝ) := by rw [hb0def]; push_cast; ring
  have hb2coh : ((ℓ₂ : ℤ) : ℝ) * b₀ + v = (((d₂ - d : ℤ)) : ℝ) := by rw [hvdef]; push_cast; ring
  have hb3coh : (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ + v = (((d₂ - d₁ : ℤ)) : ℝ) := by
    rw [hb3def]; push_cast; ring
  have hDd1 : S.D ≤ ((d + (d₁ - d) : ℤ) : ℝ) := by
    rw [show d + (d₁ - d) = d₁ by ring]; exact_mod_cast hd1win.1
  have hDd2 : S.D ≤ ((d + (d₂ - d) : ℤ) : ℝ) := by
    rw [show d + (d₂ - d) = d₂ by ring]; exact_mod_cast hd2win.1
  have hDd3 : S.D ≤ ((d₁ + (d₂ - d₁) : ℤ) : ℝ) := by
    rw [show d₁ + (d₂ - d₁) = d₂ by ring]; exact_mod_cast hd2win.1
  have hab1 : ((a : ℤ) : ℝ) + ((-(d₁ - d) : ℤ) : ℝ) ≤ ((d + (d₁ - d) : ℤ) : ℝ) := by
    have h : (a : ℝ) + ((d : ℝ) - (d₁ : ℝ)) ≤ (d₁ : ℝ) := by exact_mod_cast hplace1
    rw [show d + (d₁ - d) = d₁ by ring]; push_cast; linarith
  have hab2 : ((a : ℤ) : ℝ) + ((-(d₂ - d) : ℤ) : ℝ) ≤ ((d + (d₂ - d) : ℤ) : ℝ) := by
    have h : (a : ℝ) + ((d : ℝ) - (d₂ : ℝ)) ≤ (d₂ : ℝ) := by exact_mod_cast hplace2
    rw [show d + (d₂ - d) = d₂ by ring]; push_cast; linarith
  have hab3 : ((a : ℤ) : ℝ) + ((-(d₂ - d₁) : ℤ) : ℝ) ≤ ((d₁ + (d₂ - d₁) : ℤ) : ℝ) := by
    have h : (a : ℝ) + ((d₁ : ℝ) - (d₂ : ℝ)) ≤ (d₂ : ℝ) := by exact_mod_cast hplace3
    rw [show d₁ + (d₂ - d₁) = d₂ by ring]; push_cast; linarith
  obtain ⟨_, hinD_d, hinD_da, _⟩ := hinDa
  obtain ⟨_, hinD_d1, hinD_d1a, _⟩ := hinDa1
  obtain ⟨_, hinD_d2, hinD_d2a, _⟩ := hinDa2
  have hS1_2 : inD P.X P.H (d + (d₁ - d)) := by rw [show d + (d₁ - d) = d₁ by ring]; exact hinD_d1
  have hS1_3 : inD P.X P.H (d + a + (d₁ - d)) := by
    rw [show d + a + (d₁ - d) = d₁ + a by ring]; exact hinD_d1a
  have hS2_2 : inD P.X P.H (d + (d₂ - d)) := by rw [show d + (d₂ - d) = d₂ by ring]; exact hinD_d2
  have hS2_3 : inD P.X P.H (d + a + (d₂ - d)) := by
    rw [show d + a + (d₂ - d) = d₂ + a by ring]; exact hinD_d2a
  have hS3_2 : inD P.X P.H (d₁ + (d₂ - d₁)) := by
    rw [show d₁ + (d₂ - d₁) = d₂ by ring]; exact hinD_d2
  have hS3_3 : inD P.X P.H (d₁ + a + (d₂ - d₁)) := by
    rw [show d₁ + a + (d₂ - d₁) = d₂ + a by ring]; exact hinD_d2a
  have hmain := Sigma_closed_near_int_neg (P := P) (S := S) (a := (a : ℝ)) (b₀ := b₀) (v := v)
    (d := (d : ℝ)) (ℓ₁ := ((ℓ₁ : ℤ) : ℝ)) (ℓ₂ := ((ℓ₂ : ℤ) : ℝ))
    (aℤ := (a : ℤ)) (dℤ := d) (d'ℤ := d₁) (b₁ℤ := d₁ - d) (b₂ℤ := d₂ - d) (b₃ℤ := d₂ - d₁)
    (ℓ₁ℤ := (ℓ₁ : ℤ)) (ℓ₂ℤ := (ℓ₂ : ℤ))
    hXpos ha0R ha_hi hd_pos hℓ1_loR hℓ12R hℓ2W hb1ne hb2ne hb3ne hwin hwin3 hshiftpos
    hdwin hb0 hv_sharp hshift2 h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
    hacoh hdcoh hd'coh rfl rfl hb1coh hb2coh hb3coh
    (by exact_mod_cast le_of_lt ha0) hb1sgn hb2sgn hb3sgn
    (by exact_mod_cast le_of_lt hℓ1Z) (le_of_lt hℓ12Z) (by exact_mod_cast hℓ2W)
    hDd1 hDd2 hDd3 hab1 hab2 hab3
    hinD_d hinD_da hS1_2 hS1_3 hS2_2 hS2_3 hinD_d1 hinD_d1a hS3_2 hS3_3
  -- transport: the goal's `Σ_closed` arguments coincide with `(b₀, v, d)`.
  have hgoal_eq : Sigma_closed P.X (a : ℝ)
      (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
      (vval P a dStar ℓ₁ ℓ₂ r) (dStar r : ℝ) ℓ₁ ℓ₂
      = Sigma_closed P.X (a : ℝ) b₀ v (d : ℝ) ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) := by
    rw [hb₀_def, hv_def, hd_def, hd1_def]; norm_num
  rw [hgoal_eq]; exact hmain

set_option maxHeartbeats 25600000 in
/-- **§5 Step-4 large-defect per-`r` smooth-point `s`-extraction** (writeup 1025–1052).

The per-`r` `dStar`-witness bundle mirrors `phiv_distInt_from_witness`/`sigma_s_extract_from_witness`
(closeness, windows, `[D,2D]`), augmented with the smooth-point side data the sound magnitude /
smoothing pieces require: `d̃ₐ(r) ∈ [D,2D]` (`hdtwin`), the smooth-point cancellation-avoidance floor
`hvlo` (writeup 1025–1031, at `d̃ₐ`), the two-sided slope window `hb0lo`, and the regime constants
`hReg`/`hΩH`/`hDeW`/`hv2`.  Conclusion: there is a nonzero `s` with `1 ≤ |s| ≤ 10¹¹¹·G⁵U³⁵/Ω⁸` and
`round (Σ_closed b₀ (vval r) (d̃ₐ r)) = s`. -/
theorem step4_fiber_extract {a : ℤ} {ℓ₁ ℓ₂ r : ℕ} {dStar : ℕ → ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
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
    -- integer-witness sign / placement (decreasing-`d̃ₐ`, `bᵢ ≤ 0`), as in `sigma_s_extract_from_witness`
    (hb1sgn : dStar (r + ℓ₁) - dStar r ≤ (0:ℤ))
    (hb2sgn : dStar (r + ℓ₂) - dStar r ≤ (0:ℤ))
    (hb3sgn : dStar (r + ℓ₂) - dStar (r + ℓ₁) ≤ (0:ℤ))
    (hplace1 : a + (dStar r - dStar (r + ℓ₁)) ≤ dStar (r + ℓ₁))
    (hplace2 : a + (dStar r - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    (hplace3 : a + (dStar (r + ℓ₁) - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    -- smooth-point side data
    (hdtwin : S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X (r : ℝ) (a : ℝ)
      ∧ dtilde P.X (r : ℝ) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hb0lo : S.B / 2000000
        ≤ |((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)|)
    (hvlo : 10 * (((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))
          * (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)) ^ 2
          / dtilde P.X (r : ℝ) (a : ℝ))
        ≤ |vval P a dStar ℓ₁ ℓ₂ r|)
    (hVbig : 10 ^ 60 * V₂ P S ≤ |vval P a dStar ℓ₁ ℓ₂ r|)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 60 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14) :
    ∃ s : ℤ, s ≠ 0
      ∧ (1 : ℝ) ≤ |(s : ℝ)|
      ∧ |(s : ℝ)| ≤ 10 ^ 56 * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
          * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))) * P.U ^ 10 / S.Ω ^ 8
      ∧ round (Sigma_closed P.X (a : ℝ)
          (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
          (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂) = s := by
  -- ===== positivity / casts =====
  set d : ℤ := dStar r with hd_def
  set d₁ : ℤ := dStar (r + ℓ₁) with hd1_def
  set d₂ : ℤ := dStar (r + ℓ₂) with hd2_def
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hV2nn : 0 ≤ V₂ P S := by rw [V₂]; positivity
  have hVcut : V₂ P S ≤ |vval P a dStar ℓ₁ ℓ₂ r| := by nlinarith [hVbig, hV2nn]
  have hℓ1Z : (0 : ℤ) < (ℓ₁ : ℤ) := by exact_mod_cast hℓ1
  have hℓ12Z : (ℓ₁ : ℤ) < (ℓ₂ : ℤ) := by exact_mod_cast hℓ12
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12Z
  have hℓ1_loR : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ12'R : ((ℓ₁ : ℤ) : ℝ) + 1 ≤ ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12'
  have hr_hi16 : (r : ℝ) ≤ 16 * S.R := le_trans (by linarith [hℓ1R]) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by linarith [hℓ1R]
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by linarith [hℓ1R, hℓ12R]
  -- ===== closeness ×2 for b₀ / v shapes =====
  have hd_close : |(d : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hd2_close : |(d₂ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2
  -- ===== b₀, v =====
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / ((ℓ₁ : ℤ) : ℝ) with hb₀_def
  set v : ℝ := vval P a dStar ℓ₁ ℓ₂ r with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₁ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
  -- the v-bound `|v| ≤ 10²⁰·ΔU⁵/Ω³`
  have hvd := v_defect_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) (d := d) (d₁ := d₁) (d₂ := d₂)
    hAD ha0 ha_lo ha_hi hℓ1Z hℓ1Z hℓ12Z hℓ2W hr_lo hr2_hi
    hd_close hd1_close hd2_close h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hv_shape : v = ((d₂ : ℝ) - (d : ℝ))
      - (((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ)) * ((d₁ : ℝ) - (d : ℝ)) := by
    rw [hv_def, vval, hd_def, hd1_def, hd2_def]
  have hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    rw [hv_shape]
    refine le_trans hvd ?_
    have hnn : (0 : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by positivity
    gcongr; norm_num
  -- the smooth-point `hvlo` in `b₀` form
  have hvlo' : 10 * (((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * b₀ ^ 2
        / dtilde P.X (r : ℝ) (a : ℝ)) ≤ |v| := by
    rw [hb₀_def, hv_def]; exact hvlo
  -- ===== STEP 1 : near-integer at the integer witness, then smoothing to `dtilde` =====
  -- The integer-witness near-integer bound at `dStar` (via `Sigma_closed_near_int_neg`).
  have hnearStar := fiber_near_int_at_witness
    (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r) (dStar := dStar)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hr_lo hr1_hi hr2_hi
    hinDa hinDa1 hinDa2 hdwin hd1win hd2win hRd hRd1 hRd2
    hd1ned hd2ned hd21ned hb1sgn hb2sgn hb3sgn hplace1 hplace2 hplace3
    h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
  rw [← hb₀_def, ← hd_def, ← hv_def] at hnearStar
  have hNBeq : 10 ^ 11 * P.Wval ^ 4 * P.H / S.D = 10 ^ 11 * P.Wval ^ 4 / S.Δ := by
    rw [Scale.D]; field_simp
  rw [hNBeq] at hnearStar
  -- smoothing: `|Σ_closed(dtilde) − Σ_closed(dStar)| ≤ δ·|dtilde − dStar|`
  have hsmooth := Sigma_closed_d_smoothing (P := P) (S := S) (a := (a : ℝ))
    (ℓ₁ := ((ℓ₁ : ℤ) : ℝ)) (ℓ₂ := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v)
    (d₁ := (d : ℝ)) (d₂ := dtilde P.X (r : ℝ) (a : ℝ))
    ha0R ha_lo ha_hi hℓ1_loR hℓ12R hℓ12'R hℓ2W
    ⟨S.D_eps_lo hdwin.1, S.D_eps_hi hdwin.2⟩ hdtwin hAD hb0
    (by rw [hb₀_def]; exact hb0lo) hv h1 hband
    hG1 hU1 hΔ1 hH1 hΩU hUbig hΩH hDeW
    (by rw [hv_def] at hVcut ⊢; exact hVcut)
  -- the smoothing's `|d̃ₐ − dStar|`-factor: bound by `3·D` (both in `[D,2D]`).
  set δsm : ℝ := 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
      * |dtilde P.X (r : ℝ) (a : ℝ) - (d : ℝ)| with hδsm_def
  -- assemble: `distInt(Σ_closed(dtilde)) ≤ NB + E1 + δsm`
  set SgS : ℝ := Sigma_closed P.X (a : ℝ) b₀ v (d : ℝ) ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) with hSgS_def
  set SgT : ℝ := Sigma_closed P.X (a : ℝ) b₀ v (dtilde P.X (r : ℝ) (a : ℝ))
      ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) with hSgT_def
  have hSgclose : |SgT - SgS| ≤ δsm := by rw [hSgT_def, hSgS_def, hδsm_def]; exact hsmooth
  have hnearTilde : distInt SgT ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 111 * UpsT P S) + δsm := by
    have hsub : distInt SgT ≤ distInt SgS + distInt (SgT - SgS) := by
      have hSigeq : SgT = SgS - (SgS - SgT) := by ring
      have hswap : distInt (SgS - SgT) = distInt (SgT - SgS) := by
        rw [show SgS - SgT = -(SgT - SgS) by ring, distInt_neg]
      calc distInt SgT = distInt (SgS - (SgS - SgT)) := by rw [← hSigeq]
        _ ≤ distInt SgS + distInt (SgS - SgT) := distInt_sub_le _ _
        _ = distInt SgS + distInt (SgT - SgS) := by rw [hswap]
    have hSU : distInt (SgT - SgS) ≤ |SgT - SgS| := by
      refine le_trans (distInt_le_intDist _ 0) ?_
      rw [Int.cast_zero, sub_zero]
    calc distInt SgT ≤ distInt SgS + distInt (SgT - SgS) := hsub
      _ ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 111 * UpsT P S) + |SgT - SgS| := by
          have : distInt SgS ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 111 * UpsT P S := hnearStar
          linarith [hSU]
      _ ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 111 * UpsT P S) + δsm := by linarith [hSgclose]
  -- ===== STEP 2 : magnitude floor / cap at the smooth point =====
  set dt : ℝ := dtilde P.X (r : ℝ) (a : ℝ) with hdt_def
  have hlow := sigma_v2_lower (P := P) (S := S) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := dt)
    ha0R ha_lo ha_hi hℓ1_loR hℓ12R hℓ12'R hℓ2W hb0 hb0lo hv hvlo'
    hdtwin.1 hdtwin.2 hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
  have hupp := sigma_v2_upper (P := P) (S := S) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := dt)
    ha0R ha_lo ha_hi hℓ1_loR hℓ12R hℓ12'R hℓ2W hb0 hb0lo hv hvlo'
    hdtwin.1 hdtwin.2 hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
  rw [← hSgT_def] at hlow hupp
  -- abbreviate `A := (ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v²)/(Δ²Ω²) ≥ 0`, so `hlow : (1/(2·10⁸))·A ≤ |SgT|`,
  -- `hupp : |SgT| ≤ 10¹⁵·A`.
  have hΔΩ2pos : (0:ℝ) < S.Δ ^ 2 * S.Ω ^ 2 := by positivity
  have hΩ8pos : (0:ℝ) < S.Ω ^ 8 := by positivity
  set A : ℝ := ((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * v ^ 2
      / (S.Δ ^ 2 * S.Ω ^ 2) with hA_def
  have hℓ21nn : (0:ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ) := by linarith [hℓ12R]
  have hAnn : 0 ≤ A := by
    rw [hA_def]; apply div_nonneg _ hΔΩ2pos.le; positivity
  have hlow' : (1 / (2 * 10 ^ 8 : ℝ)) * A ≤ |SgT| := by
    rw [hA_def]
    rw [show (1 / (2 * 10 ^ 8 : ℝ)) * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
          * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * v ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2))
        = (1 / (2 * 10 ^ 8 : ℝ)) * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
          * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) by ring]
    exact hlow
  have hupp' : |SgT| ≤ (10 ^ 15 : ℝ) * A := by
    rw [hA_def]
    rw [show (10 ^ 15 : ℝ) * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
          * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * v ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2))
        = (10 ^ 15 : ℝ) * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
          * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) by ring]
    exact hupp
  -- ===== STEP 2a : err-domination (writeup 1033) ⟹ `round SgT ≠ 0` =====
  have hLge : (2 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ)) := by
    have hL13 : (1:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) ^ 3 := one_le_pow₀ hℓ1_loR
    have h21 : (1:ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ) := by linarith [hℓ12'R]
    have h2 : (2:ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := by linarith [hℓ12'R, hℓ1_loR]
    have hp1 : (2:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ) := by nlinarith [hL13, h2]
    nlinarith [hp1, h21, mul_nonneg (by positivity : (0:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) ^ 3) (le_of_lt (lt_trans hℓ1R hℓ12R))]
  -- the V₂ split and the squared floor
  set T1 : ℝ := (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U)) / S.Ω ^ 6
    with hT1_def
  set T2 : ℝ := Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω) with hT2_def
  have hT1nn : 0 ≤ T1 := by rw [hT1_def]; positivity
  have hT2nn : 0 ≤ T2 := by rw [hT2_def]; positivity
  have hVbig' : 10 ^ 60 * (T1 + T2) ≤ |v| := by
    have hVeq : V₂ P S = T1 + T2 := by rw [V₂, hT1_def, hT2_def]
    rw [← hVeq, hv_def]; exact hVbig
  have hvsqfloor : 10 ^ 120 * (T1 ^ 2 + T2 ^ 2) ≤ v ^ 2 := by
    have hm := mul_le_mul hVbig' hVbig' (by positivity) (abs_nonneg v)
    nlinarith [hm, sq_abs v, mul_nonneg hT1nn hT2nn]
  have hT2sq : T2 ^ 2 = S.Δ * (P.G ^ 4 * P.U ^ 20 * S.Ω ^ 2) := by
    rw [hT2_def, mul_pow, Real.sq_sqrt hΔpos.le]; ring
  have hT1sq : T1 ^ 2 = S.Δ ^ 6 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 12) := by
    have hgg : Real.sqrt P.G * Real.sqrt P.G = P.G := Real.mul_self_sqrt hGpos.le
    have huu : Real.sqrt P.U * Real.sqrt P.U = P.U := Real.mul_self_sqrt hUpos.le
    rw [hT1_def,
      show ((S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U)) / S.Ω ^ 6) ^ 2
        = (S.Δ ^ 3 / P.H) ^ 2 * ((P.G ^ 2) ^ 2 * (Real.sqrt P.G * Real.sqrt P.G)
            * ((P.U ^ 22) ^ 2 * (Real.sqrt P.U * Real.sqrt P.U))) / (S.Ω ^ 6) ^ 2 from by ring,
      hgg, huu]
    field_simp
  -- the leading floor `10¹¹²·(T1²+T2²)/(Δ²Ω²) ≤ |SgT|`
  have hAfloor2 : 2 * 10 ^ 120 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) ≤ A := by
    rw [hA_def]
    apply div_le_div_of_nonneg_right ?_ (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2)
    nlinarith [hLge, hvsqfloor, sq_nonneg v]
  have hSgT_floor : 10 ^ 112 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) ≤ |SgT| := by
    refine le_trans ?_ hlow'
    have h2A : 2 * 10 ^ 120 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) ≤ A := hAfloor2
    have hsplit : (1 / (2 * 10 ^ 8 : ℝ)) * A
        ≥ (1 / (2 * 10 ^ 8 : ℝ)) * (2 * 10 ^ 120 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)) :=
      mul_le_mul_of_nonneg_left h2A (by norm_num)
    have heq : (1 / (2 * 10 ^ 8 : ℝ)) * (2 * 10 ^ 120 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2))
        = 10 ^ 112 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by
      field_simp
    linarith [hsplit, heq.le, heq.ge]
  -- the floor in split form
  have hX1eq : T1 ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2)
      = S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14) := by
    rw [hT1sq]; field_simp
  have hX2eq : T2 ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2) = P.G ^ 4 * P.U ^ 20 / S.Δ := by
    rw [hT2sq]; field_simp
  -- the t3-core regime collapse : `21·10⁹⁷·U¹⁵Δ ≤ HΩ¹¹`
  have hΔU : 10 ^ 15 * P.U ^ 20 ≤ S.Δ := by
    have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
    nlinarith [hDeW, pow_pos hUpos 20]
  have hU10' : (10:ℝ) ^ 330 ≤ P.U ^ 10 := by
    calc (10:ℝ) ^ 330 = ((10:ℝ) ^ 33) ^ 10 := by rw [← pow_mul]
      _ ≤ P.U ^ 10 := pow_le_pow_left₀ (by norm_num) hUbig 10
  have hpay8 := band_pay8 (P := P) (S := S) hband
  have hΔ16 : 21 * 10 ^ 106 * (P.G ^ 2 * P.U ^ 16) ≤ S.Δ := by
    have hU4 : (21:ℝ) * 10 ^ 91 ≤ P.U ^ 4 := by
      calc (21:ℝ) * 10 ^ 91 ≤ (10:ℝ) ^ 93 := by norm_num
        _ ≤ (10:ℝ) ^ 132 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 4 := by rw [← pow_mul]
        _ ≤ P.U ^ 4 := pow_le_pow_left₀ (by norm_num) hUbig 4
    have hG24 : P.G ^ 2 ≤ P.G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
    calc 21 * 10 ^ 106 * (P.G ^ 2 * P.U ^ 16)
        = 10 ^ 15 * (21 * 10 ^ 91) * (P.G ^ 2 * P.U ^ 16) := by ring
      _ ≤ 10 ^ 15 * P.U ^ 4 * (P.G ^ 2 * P.U ^ 16) := by
          gcongr 10 ^ 15 * ?_ * (P.G ^ 2 * P.U ^ 16)
      _ = 10 ^ 15 * (P.G ^ 2 * P.U ^ 20) := by ring
      _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
          have h1' : P.G ^ 2 * P.U ^ 20 ≤ P.G ^ 4 * P.U ^ 20 :=
            mul_le_mul_of_nonneg_right hG24 (by positivity)
          have h2' : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 20 := by positivity
          linarith
      _ ≤ S.Δ := hDeW
  have ht3core : 21 * 10 ^ 106 * (P.U ^ 15 * S.Δ) ≤ P.H * S.Ω ^ 11 := by
    calc 21 * 10 ^ 106 * (P.U ^ 15 * S.Δ)
        = (21 * 10 ^ 106 * (P.U ^ 15 * S.Δ)) * 1 := (mul_one _).symm
      _ ≤ (21 * 10 ^ 106 * (P.U ^ 15 * S.Δ)) * (P.G ^ 2 * P.U ^ 6 * S.Ω ^ 8) :=
          mul_le_mul_of_nonneg_left hpay8 (by positivity)
      _ = (21 * 10 ^ 106 * (P.G ^ 2 * P.U ^ 16)) * (P.U ^ 5 * S.Δ) * S.Ω ^ 8 := by ring
      _ ≤ S.Δ * (P.U ^ 5 * S.Δ) * S.Ω ^ 8 := by
          gcongr ?_ * (P.U ^ 5 * S.Δ) * S.Ω ^ 8
      _ = S.Δ ^ 2 * P.U ^ 5 * S.Ω ^ 8 := by ring
      _ ≤ (P.H * S.Ω ^ 3) * S.Ω ^ 8 := mul_le_mul_of_nonneg_right hReg (by positivity)
      _ = P.H * S.Ω ^ 11 := by ring
  -- `δsm` is dominated by the capped third summand, itself `≤ (1/3)·G⁴U²⁰/Δ`
  have hδsm_le : δsm ≤ 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
      * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
    rw [hδsm_def]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_sub_comm]
    exact hd_close
  have ht3dom : 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
      * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) ≤ (1/3) * (P.G ^ 4 * P.U ^ 20 / S.Δ) := by
    rw [show S.D = P.H * S.Δ from rfl]
    have hLHSeq : 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / (P.H * S.Δ)
          * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        = 7 * 10 ^ 106 * (P.G ^ 4 * P.U ^ 35) / (P.H * S.Ω ^ 11) := by
      field_simp
      ring
    have hRHSeq : (1 / 3 : ℝ) * (P.G ^ 4 * P.U ^ 20 / S.Δ)
        = P.G ^ 4 * P.U ^ 20 / (3 * S.Δ) := by
      rw [div_mul_div_comm, one_mul]
    rw [hLHSeq, hRHSeq, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 7 * 10 ^ 106 * (P.G ^ 4 * P.U ^ 35) * (3 * S.Δ)
        = (P.G ^ 4 * P.U ^ 20) * (21 * 10 ^ 106 * (P.U ^ 15 * S.Δ)) := by ring
      _ ≤ (P.G ^ 4 * P.U ^ 20) * (P.H * S.Ω ^ 11) :=
          mul_le_mul_of_nonneg_left ht3core (by positivity)
      _ = P.G ^ 4 * P.U ^ 20 * (P.H * S.Ω ^ 11) := by ring
  have hW4 : P.Wval ^ 4 = P.G ^ 4 * P.U ^ 20 := by unfold Globals.Wval; ring
  -- err-domination : if `round SgT = 0` then `|SgT| ≤ errB ≤ ½·floor ≤ ½·|SgT|`, absurd
  have hround_ne : round SgT ≠ 0 := by
    intro h0
    have hSgT_small : |SgT| ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 111 * UpsT P S) + δsm := by
      have hdEq : distInt SgT = |SgT| := by
        show |SgT - ((round SgT : ℤ) : ℝ)| = |SgT|
        rw [h0]; norm_num
      linarith [hnearTilde, hdEq.ge, hdEq.le]
    have hXp1 : (0:ℝ) ≤ S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14) := by positivity
    have hXp2 : (0:ℝ) < P.G ^ 4 * P.U ^ 20 / S.Δ := by positivity
    have hUeqT : UpsT P S = S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14) := rfl
    have hfloor' : 10 ^ 112 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14)
          + P.G ^ 4 * P.U ^ 20 / S.Δ) ≤ |SgT| := by
      refine le_trans (le_of_eq ?_) hSgT_floor
      rw [show 10 ^ 112 * (T1 ^ 2 + T2 ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
          = 10 ^ 112 * (T1 ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2) + T2 ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2)) by ring,
        hX1eq, hX2eq]
    rw [hUeqT] at hSgT_small
    have h45eq : 10 ^ 11 * P.Wval ^ 4 / S.Δ = 10 ^ 11 * (P.G ^ 4 * P.U ^ 20 / S.Δ) := by
      rw [hW4]; ring
    rw [h45eq] at hSgT_small
    -- err-domination at the `10⁶⁰·V₂` cut: the SHARP v-window `|v| ≤ 3.9·10¹⁴·ΔU⁵/Ω³`
    -- (`v_defect_le`), threaded through `upsilon_err_le_sharp`, puts the post-sweep
    -- Υ-expansion tolerance at `10¹¹¹·UpsT`, strictly below the `10¹¹²·UpsT` magnitude
    -- floor of `hfloor'` (from `hVbig`, `sigma_v2_lower`) — contradiction.
    linarith [hSgT_small, hfloor', hδsm_le.trans ht3dom, hXp1, hXp2]
  -- ===== STEP 2b : the ℓ-scaled cap =====
  set Lc : ℝ := ((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))
    with hLc_set
  have hΩ6ne : (S.Ω ^ 6 : ℝ) ≠ 0 := by positivity
  have hvsq' : v ^ 2 ≤ (10 ^ 40 : ℝ) * (S.Δ ^ 2 * P.U ^ 10 / S.Ω ^ 6) := by
    have hm := mul_le_mul hv hv (abs_nonneg _) (by positivity)
    have hform : (10 ^ 20 : ℝ) * (S.Δ * P.U ^ 5 / S.Ω ^ 3) * ((10 ^ 20 : ℝ) * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
        = (10 ^ 40 : ℝ) * (S.Δ ^ 2 * P.U ^ 10 / S.Ω ^ 6) := by
      field_simp
    calc v ^ 2 = |v| * |v| := by rw [← sq_abs v]; ring
      _ ≤ (10 ^ 20 : ℝ) * (S.Δ * P.U ^ 5 / S.Ω ^ 3) * ((10 ^ 20 : ℝ) * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) := hm
      _ = (10 ^ 40 : ℝ) * (S.Δ ^ 2 * P.U ^ 10 / S.Ω ^ 6) := hform
  have hUΩ8 : S.Ω ^ 8 ≤ P.U ^ 10 := by
    have h8 : S.Ω ^ 8 ≤ P.U ^ 8 := pow_le_pow_left₀ hΩpos.le hΩU 8
    have h10 : P.U ^ 8 ≤ P.U ^ 10 := pow_le_pow_right₀ hU1 (by norm_num)
    linarith
  have hLcnn : (0:ℝ) ≤ Lc := le_trans (by norm_num) hLge
  have hSgT_cap : |SgT| ≤ (10 ^ 55 : ℝ) * Lc * P.U ^ 10 / S.Ω ^ 8 := by
    refine le_trans hupp' ?_
    rw [hA_def]
    have h1c : Lc * v ^ 2 ≤ Lc * ((10 ^ 40 : ℝ) * (S.Δ ^ 2 * P.U ^ 10 / S.Ω ^ 6)) :=
      mul_le_mul_of_nonneg_left hvsq' hLcnn
    have hmid : (10 ^ 15 : ℝ) * (Lc * v ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2))
        ≤ (10 ^ 15 : ℝ)
            * (Lc * ((10 ^ 40 : ℝ) * (S.Δ ^ 2 * P.U ^ 10 / S.Ω ^ 6)) / (S.Δ ^ 2 * S.Ω ^ 2)) := by
      have hd := div_le_div_of_nonneg_right h1c
        (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2)
      nlinarith [hd]
    calc (10 ^ 15 : ℝ) * (Lc * v ^ 2 / (S.Δ ^ 2 * S.Ω ^ 2))
        ≤ (10 ^ 15 : ℝ)
            * (Lc * ((10 ^ 40 : ℝ) * (S.Δ ^ 2 * P.U ^ 10 / S.Ω ^ 6)) / (S.Δ ^ 2 * S.Ω ^ 2)) := hmid
      _ = (10 ^ 55 : ℝ) * Lc * P.U ^ 10 / S.Ω ^ 8 := by
          field_simp
  -- ===== STEP 3 : extract `s := round SgT` and assemble =====
  refine ⟨round SgT, hround_ne, ?_, ?_, rfl⟩
  · -- `1 ≤ |round SgT|`
    have hscast : (1 : ℤ) ≤ |round SgT| := Int.one_le_abs hround_ne
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|round SgT| : ℤ) : ℝ) := by exact_mod_cast hscast
      _ = |(round SgT : ℝ)| := by rw [Int.cast_abs]
  · -- `|round SgT| ≤ ℓ-scaled cap`
    have hround_near : |(round SgT : ℝ) - SgT| ≤ 1 / 2 := by
      have := abs_sub_round SgT; rwa [abs_sub_comm] at this
    have hsle : |(round SgT : ℝ)| ≤ |SgT| + 1 / 2 := by
      have h := abs_sub_abs_le_abs_sub (round SgT : ℝ) SgT
      linarith [h, hround_near]
    have hbase2 : (2:ℝ) ≤ Lc * P.U ^ 10 / S.Ω ^ 8 := by
      rw [le_div_iff₀ hΩ8pos]
      exact mul_le_mul hLge hUΩ8 (pow_nonneg hΩpos.le 8) (le_trans (by norm_num) hLge)
    have hcap10 : (10 ^ 55 : ℝ) * Lc * P.U ^ 10 / S.Ω ^ 8 + 1 / 2
        ≤ 10 ^ 56 * Lc * P.U ^ 10 / S.Ω ^ 8 := by
      have he1 : (10 ^ 55 : ℝ) * Lc * P.U ^ 10 / S.Ω ^ 8
          = (10 ^ 55 : ℝ) * (Lc * P.U ^ 10 / S.Ω ^ 8) := by ring
      have he2 : (10 ^ 56 : ℝ) * Lc * P.U ^ 10 / S.Ω ^ 8
          = (10 ^ 56 : ℝ) * (Lc * P.U ^ 10 / S.Ω ^ 8) := by ring
      rw [he1, he2]
      nlinarith [hbase2]
    linarith [hsle, hSgT_cap, hcap10]

end Squarefree
