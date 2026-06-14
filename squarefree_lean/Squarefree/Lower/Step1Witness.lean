import Squarefree.Lower.Step1Discharge
import Squarefree.Lower.DefectClose
import Squarefree.Lower.DefectScales

/-!
# §5 Step-1 v=0, per-`r` bound from `RaWitness` data (writeup 820–840)

`phi_distInt_from_witness` is the modeling interface: given the three `D`-scale
witnesses `d, d₁, d₂` of a `v=0` triple (in `RaWitness` shape: `inDa`, `[D,2D]`,
`|R_a(·)−·| ≤ 14H/D`), it produces `distInt(φ(r)) ≤ δ_unif`. It discharges the
hypotheses of `phi_distInt_le_unif` (closeness via `dtilde_close`, the Taylor
window via `step1_window_bound`) internally, so the prop_5_1 assembly only has to
supply witnesses and the regime.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- The Taylor-expansion window `4(a + ℓ₂|b₀|) ≤ d`. In the §5 regime the slope
`|b₀| ≤ 3·10¹²·B` and `ℓ₂ ≤ W`, while `R ≥ U·W` with `U ≥ 10³³`, so the perturbation
`a + ℓ₂|b₀| ≪ D ≤ d`. -/
theorem step1_window_bound {a ℓ₂ : ℤ} {b₀ dd : ℝ}
    (ha_hi : (a:ℝ) ≤ 11 * S.A) (hℓ2W : (ℓ₂:ℝ) ≤ 130 * P.Wval) (hℓ2nn : 0 ≤ (ℓ₂:ℝ))
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hdD : S.D ≤ dd)
    (hRUW : P.U * P.Wval ≤ S.R)
    (hΩU : S.Ω ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U) :
    4 * ((a:ℝ) + (ℓ₂:ℝ) * |b₀|) ≤ dd := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  refine le_trans ?_ hdD
  -- Reduce to `4 * (a + ℓ₂|b₀|) ≤ S.D`.
  -- Step (i): cleared core inequality `U^6 * Δ ≤ H * Ω^3`.
  have hcore : P.U ^ 6 * S.Δ ≤ P.H * S.Ω ^ 3 := by
    have hRUW' : P.U * (P.G * P.U ^ 5) ≤ P.H * P.G * S.Ω ^ 3 / S.Δ := by
      simpa [Globals.Wval, Scale.R] using hRUW
    rw [le_div_iff₀ hΔ] at hRUW'
    -- hRUW' : U * (G * U^5) * Δ ≤ H * G * Ω^3
    have hcancel : P.G * (P.U ^ 6 * S.Δ) ≤ P.G * (P.H * S.Ω ^ 3) := by nlinarith [hRUW']
    exact le_of_mul_le_mul_left hcancel hG
  -- Step (ii)-(iv): bound the slope term.
  -- ℓ₂ * |b₀| ≤ W * (3e12 * B) and W = G U^5, B = Δ²/(G Ω³).
  have hℓ2W' : (ℓ₂:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hslope : (ℓ₂:ℝ) * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * S.B) := by
    apply mul_le_mul hℓ2W' hb0 (abs_nonneg _)
    positivity
  -- The KEY scale inequality.
  have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ (le_of_lt hΩ) hΩU 4
  have hU33 : (10:ℝ) ^ 33 ≤ P.U := hUbig
  have hKEY : 44 * S.Ω ^ 4 + 1560000000000000 * P.U ^ 5 * S.Δ ≤ P.H * S.Ω ^ 3 := by
    -- 12e12 * U^5 * Δ ≤ U^6 * Δ / 2  (since 24e12 ≤ U)
    have hb : 3120000000000000 * P.U ^ 5 * S.Δ ≤ P.U ^ 6 * S.Δ := by
      have hU24 : (3120000000000000:ℝ) ≤ P.U := by nlinarith [hU33]
      have : 3120000000000000 * P.U ^ 5 ≤ P.U * P.U ^ 5 := by
        nlinarith [pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 5]
      nlinarith [this, hΔ]
    -- 88 * Ω^4 ≤ U^6 * Δ
    have hc : 88 * S.Ω ^ 4 ≤ P.U ^ 6 * S.Δ := by
      have hU2Δ : (88:ℝ) ≤ P.U ^ 2 * S.Δ := by nlinarith [hU33, hΔ1]
      have h1 : 88 * P.U ^ 4 ≤ P.U ^ 6 * S.Δ := by nlinarith [hU2Δ, pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 4]
      nlinarith [hΩ4, h1, pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hU1) 4]
    -- combine: 44 Ω^4 + 12e12 U^5 Δ ≤ U^6 Δ ≤ H Ω^3
    nlinarith [hb, hc, hcore]
  -- Now clear denominators. S.D = H*Δ, S.B = Δ²/(G Ω³).
  rw [Scale.D]
  -- target: 4 * (a + ℓ₂|b₀|) ≤ H * Δ
  have hΩ3pos : (0:ℝ) < S.Ω ^ 3 := by positivity
  have ha_hi' : (a:ℝ) ≤ 11 * (S.Δ * S.Ω) := by simpa [Scale.A] using ha_hi
  -- slope: ℓ₂|b₀| ≤ (G U^5) * (3e12 * (Δ²/(G Ω³))) = 3e12 * U^5 * Δ²/Ω³
  have hslope2 : (ℓ₂:ℝ) * |b₀| ≤ 390000000000000 * P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 := by
    refine le_trans hslope ?_
    rw [Scale.B, le_div_iff₀ hΩ3pos]
    field_simp
    nlinarith [hΩ3pos, hG]
  -- Combine into polynomial form by multiplying target by Ω^3 > 0.
  rw [← mul_le_mul_iff_of_pos_right hΩ3pos]
  -- target: 4 * (a + ℓ₂|b₀|) * Ω³ ≤ H * Δ * Ω³
  have hslope3 : (ℓ₂:ℝ) * |b₀| * S.Ω ^ 3 ≤ 390000000000000 * P.U ^ 5 * S.Δ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hslope2 (le_of_lt hΩ3pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hΩ3pos)] at this
  have ha3 : (a:ℝ) * S.Ω ^ 3 ≤ 11 * (S.Δ * S.Ω) * S.Ω ^ 3 :=
    mul_le_mul_of_nonneg_right ha_hi' (le_of_lt hΩ3pos)
  have hKEYΔ : (44 * S.Ω ^ 4 + 1560000000000000 * P.U ^ 5 * S.Δ) * S.Δ ≤ P.H * S.Ω ^ 3 * S.Δ :=
    mul_le_mul_of_nonneg_right hKEY (le_of_lt hΔ)
  nlinarith [hslope3, ha3, hKEYΔ, hΩ3pos, hΔ]

/-- **Step-1 v=0 per-`r` bound (from `RaWitness` data).** -/
theorem phi_distInt_from_witness {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (hr1_hi : r + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hin : inDa P.X P.H a d) (hin1 : inDa P.X P.H a d₁) (hin2 : inDa P.X P.H a d₂)
    (hdwin : S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2*S.D) (hd1win : S.D ≤ (d₁:ℝ) ∧ (d₁:ℝ) ≤ 2*S.D)
    (hd2win : S.D ≤ (d₂:ℝ) ∧ (d₂:ℝ) ≤ 2*S.D)
    (hRd  : |Rfun P.X (a:ℝ) (d:ℝ)  - r|            ≤ 14 * P.H / S.D)
    (hRd1 : |Rfun P.X (a:ℝ) (d₁:ℝ) - (r + (ℓ₁:ℝ))| ≤ 14 * P.H / S.D)
    (hv0 : (ℓ₁:ℝ) * ((d₂:ℝ) - (d:ℝ)) = (ℓ₂:ℝ) * ((d₁:ℝ) - (d:ℝ)))
    (hb0ne : (d₁:ℝ) ≠ (d:ℝ))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U) :
    Counting.distInt (phi P.X (a:ℝ) ℓ₁ ℓ₂ r)
      ≤ (10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  -- Cast facts.
  have hℓ1R : (0:ℝ) < (ℓ₁:ℝ) := by exact_mod_cast hℓ1
  have hℓ1ne : (ℓ₁:ℝ) ≠ 0 := ne_of_gt hℓ1R
  have hℓ1_loR : (1:ℝ) ≤ (ℓ₁:ℝ) := by exact_mod_cast hℓ1_lo
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha0
  have hℓ2W' : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ2nn : (0:ℝ) ≤ (ℓ₂:ℝ) := by
    have : (1:ℤ) ≤ ℓ₂ := le_of_lt (lt_of_le_of_lt hℓ1_lo hℓ12)
    exact_mod_cast (le_trans (by norm_num) this)
  have hGΩ : 0 < P.G * S.Ω ^ 3 := by positivity
  have hBpos : 0 < S.B := by rw [Scale.B]; positivity
  -- r-window pieces.
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1R]
  have hr1_lo : (1/72) * S.R ≤ r + (ℓ₁:ℝ) := by linarith [hℓ1R]
  -- Positivity of d, d₁, d₂.
  have hDpos : 0 < S.D := by rw [Scale.D]; positivity
  have hdpos : 0 < (d:ℝ) := lt_of_lt_of_le hDpos hdwin.1
  have hd1pos : 0 < (d₁:ℝ) := lt_of_lt_of_le hDpos hd1win.1
  have hd2pos : 0 < (d₂:ℝ) := lt_of_lt_of_le hDpos hd2win.1
  -- Closeness bounds via dtilde_close.
  have hd_close := dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi hdwin.1 hdwin.2 hRd
  have hd1_close := dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  -- ===== PART A:  |b₀| ≤ 3·10¹²·B  where b₀ = (d₁−d)/ℓ₁ =====
  obtain ⟨_, _, hbt_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := (a:ℝ)) (ℓ := (ℓ₁:ℝ)) (r := r)
      hAD haR hℓ1R ha_lo ha_hi hr_lo hr1_hi
  rw [bt] at hbt_hi
  set b₀ : ℝ := ((d₁:ℝ) - (d:ℝ)) / (ℓ₁:ℝ) with hb₀_def
  set bt₀ : ℝ := (dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ) - dtilde P.X r (a:ℝ)) / (ℓ₁:ℝ) with hbt_def
  have hΔB : S.Δ / (P.G * S.Ω ^ 3) ≤ S.B := by
    rw [Scale.B, div_le_div_iff₀ hGΩ hGΩ]
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith [hΔ, hΔ1]
    exact mul_le_mul_of_nonneg_right hΔsq hGΩ.le
  have hdiff : |b₀ - bt₀| ≤ 2000000000000 * S.B := by
    have heq : b₀ - bt₀
        = (((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
            - ((d:ℝ) - dtilde P.X r (a:ℝ))) / (ℓ₁:ℝ) := by
      rw [hb₀_def, hbt_def]; field_simp; ring
    rw [heq, abs_div, abs_of_pos hℓ1R]
    have hnum : |((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
            - ((d:ℝ) - dtilde P.X r (a:ℝ))|
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
      calc |((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
              - ((d:ℝ) - dtilde P.X r (a:ℝ))|
          ≤ |(d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ)|
              + |(d:ℝ) - dtilde P.X r (a:ℝ)| := abs_sub _ _
        _ ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
              + 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := add_le_add hd1_close hd_close
        _ = 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by ring
    have hstep : |((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
            - ((d:ℝ) - dtilde P.X r (a:ℝ))| / (ℓ₁:ℝ)
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
      rw [div_le_iff₀ hℓ1R]
      have hnn : (0:ℝ) ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by positivity
      have hle : 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
          ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) * (ℓ₁:ℝ) := by
        have := mul_le_mul_of_nonneg_left hℓ1_loR hnn
        simpa using this
      exact le_trans hnum hle
    calc |((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
            - ((d:ℝ) - dtilde P.X r (a:ℝ))| / (ℓ₁:ℝ)
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := hstep
      _ ≤ 2000000000000 * S.B := mul_le_mul_of_nonneg_left hΔB (by norm_num)
  have hb0 : |b₀| ≤ 3000000000000 * S.B := by
    have htri : |b₀| ≤ |bt₀| + |b₀ - bt₀| := by
      have h := abs_add_le bt₀ (b₀ - bt₀)
      have he : bt₀ + (b₀ - bt₀) = b₀ := by ring
      rwa [he] at h
    have hsum : |b₀| ≤ 1000000 * S.B + 2000000000000 * S.B :=
      le_trans htri (add_le_add hbt_hi hdiff)
    have hfact : (1000000 : ℝ) * S.B + 2000000000000 * S.B = 2000001000000 * S.B := by ring
    have hmono : (2000001000000 : ℝ) * S.B ≤ 3000000000000 * S.B :=
      mul_le_mul_of_nonneg_right (by norm_num) hBpos.le
    rw [hfact] at hsum
    exact le_trans hsum hmono
  -- ===== The Taylor window via step1_window_bound =====
  have hRUW := U_mul_W_le_R (P := P) (S := S) h1 hband hΩU hΔ1 hU1
  have hwin : 4 * ((a:ℝ) + (ℓ₂:ℝ) * |b₀|) ≤ (d:ℝ) :=
    step1_window_bound ha_hi hℓ2W hℓ2nn hb0 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  -- ===== Discharge phi_distInt_le_unif =====
  exact phi_distInt_le_unif hAD ha0 ha_lo ha_hi hℓ1 hℓ1_lo hℓ12 hℓ2W' hr_lo hr1_hi
    hin hin1 hin2 hdpos hd1pos hd2pos hdwin hd1win hd2win hv0 hb0ne hwin
    hd_close hd1_close h1 hband hG1 hU1 hΔ1 hUH hΩU

end Squarefree
