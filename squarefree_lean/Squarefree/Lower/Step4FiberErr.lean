import Squarefree.Lower.Step4Fiber
import Squarefree.Lower.DefectClose
import Squarefree.Lower.DefectBt
import Squarefree.Lower.Step3VBound

/-!
# §5 Step-4 per-`r` `s`-extraction with the SMALL near-integer budget (writeup 1025–1052)

`step4_fiber_extract` (`Step4Fiber.lean`) produces the nonzero integer `s` with
`round (Σ_closed b₀ (vval r) (d̃ₐ r)) = s`, from which one only reads the crude near-integer
budget `|Σ_closed − s| ≤ 1/2`.  Its proof, however, internally establishes the *sharp* budget

  `distInt(Σ_closed(d̃ₐ)) ≤ 45·Wval⁴/Δ + 10¹¹⁰·UpsT + δ_sm`,

`UpsT = Δ⁴G⁵U⁴⁵/(H²Ω¹⁴)`, `45·Wval⁴/Δ ≍ G⁴U²⁰/Δ`, and `δ_sm` the `d→d̃ₐ` smoothing slack.  This
file re-exposes that small bound as a sixth conclusion of the extraction, which the §5 Step-4
confinement double-sum (`sigma_s_confine`) needs for the sharp band diameter.

`step4_fiber_extract_err` re-runs the `hnearTilde` chain (`fiber_near_int_at_witness` at the
integer witness `dStar`, then `Sigma_closed_d_smoothing` to `d̃ₐ`) and combines it with the
`round(Σ) = s` fact via `distInt(Σ) = |Σ − round(Σ)| = |Σ − s|`.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 6400000 in
/-- **§5 Step-4 large-defect per-`r` `s`-extraction with the SMALL near-integer budget.**
Identical hypotheses and first four conclusions to `step4_fiber_extract`, but augmented with the
sharp near-integer bound `|Σ_closed(d̃ₐ) − s| ≤ 45·Wval⁴/Δ + 10¹¹⁰·UpsT + δ_sm` (rather than the
crude `1/2` obtainable from `round = s` alone). -/
theorem step4_fiber_extract_err {a : ℤ} {ℓ₁ ℓ₂ r : ℕ} {dStar : ℕ → ℤ}
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
    (hb1sgn : dStar (r + ℓ₁) - dStar r ≤ (0:ℤ))
    (hb2sgn : dStar (r + ℓ₂) - dStar r ≤ (0:ℤ))
    (hb3sgn : dStar (r + ℓ₂) - dStar (r + ℓ₁) ≤ (0:ℤ))
    (hplace1 : a + (dStar r - dStar (r + ℓ₁)) ≤ dStar (r + ℓ₁))
    (hplace2 : a + (dStar r - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
    (hplace3 : a + (dStar (r + ℓ₁) - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
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
          (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂) = s
      ∧ |Sigma_closed P.X (a : ℝ)
          (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
          (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂ - (s : ℝ)|
        ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S
          + 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
            * |dtilde P.X (r : ℝ) (a : ℝ) - (dStar r : ℝ)| := by
  -- the four-conclusion extraction (nonzero `s`, magnitude bounds, `round Σ = s`)
  obtain ⟨s, hs0, hs1, hscap, hround⟩ := step4_fiber_extract
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W hr_lo hr1_hi hr2_hi
    hinDa hinDa1 hinDa2 hdwin hd1win hd2win hRd hRd1 hRd2
    hd1ned hd2ned hd21ned hb1sgn hb2sgn hb3sgn hplace1 hplace2 hplace3
    hdtwin hb0lo hvlo hVbig hReg h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΩH hDeW hHbig
  -- ===== re-derive the SMALL near-integer budget `hnearTilde` (Step4Fiber internal chain) =====
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
  have hr_hi16 : (r : ℝ) ≤ 16 * S.R := le_trans (by linarith [hℓ1R]) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by linarith [hℓ1R]
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by linarith [hℓ1R, hℓ12R]
  have hd_close : |(d : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hd2_close : |(d₂ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / ((ℓ₁ : ℤ) : ℝ) with hb₀_def
  set v : ℝ := vval P a dStar ℓ₁ ℓ₂ r with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₁ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
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
  -- integer-witness near-integer bound at `dStar`, then smoothing to `d̃ₐ`
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
  -- relax the sharpened `10¹¹¹·UpsT` tolerance back to this file's stated `10¹¹⁹` budget
  have hwk119 : (10:ℝ) ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 111 * UpsT P S
      ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S := by
    have hUpsTnn : (0:ℝ) ≤ UpsT P S := by unfold UpsT; positivity
    nlinarith [hUpsTnn]
  replace hnearStar := hnearStar.trans hwk119
  have hℓ12'R : ((ℓ₁ : ℤ) : ℝ) + 1 ≤ ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12'
  have hsmooth := Sigma_closed_d_smoothing (P := P) (S := S) (a := (a : ℝ))
    (ℓ₁ := ((ℓ₁ : ℤ) : ℝ)) (ℓ₂ := ((ℓ₂ : ℤ) : ℝ)) (b₀ := b₀) (v := v)
    (d₁ := (d : ℝ)) (d₂ := dtilde P.X (r : ℝ) (a : ℝ))
    ha0R ha_lo ha_hi hℓ1_loR hℓ12R hℓ12'R hℓ2W
    ⟨S.D_eps_lo hdwin.1, S.D_eps_hi hdwin.2⟩ hdtwin hAD hb0
    (by rw [hb₀_def]; exact hb0lo) hv h1 hband
    hG1 hU1 hΔ1 hH1 hΩU hUbig hΩH hDeW
    (by rw [hv_def] at hVcut ⊢; exact hVcut)
  set δsm : ℝ := 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
      * |dtilde P.X (r : ℝ) (a : ℝ) - (d : ℝ)| with hδsm_def
  set SgS : ℝ := Sigma_closed P.X (a : ℝ) b₀ v (d : ℝ) ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) with hSgS_def
  set SgT : ℝ := Sigma_closed P.X (a : ℝ) b₀ v (dtilde P.X (r : ℝ) (a : ℝ))
      ((ℓ₁ : ℤ) : ℝ) ((ℓ₂ : ℤ) : ℝ) with hSgT_def
  have hSgclose : |SgT - SgS| ≤ δsm := by rw [hSgT_def, hSgS_def, hδsm_def]; exact hsmooth
  have hnearTilde : distInt SgT ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S) + δsm := by
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
      _ ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S) + |SgT - SgS| := by
          have : distInt SgS ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S := hnearStar
          linarith [hSU]
      _ ≤ (10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S) + δsm := by linarith [hSgclose]
  -- ===== combine: `|Σ − s| = distInt Σ ≤ err` via `round Σ = s` =====
  refine ⟨s, hs0, hs1, hscap, hround, ?_⟩
  have hround_SgT : round SgT = s := hround
  have hdiEq : distInt SgT = |SgT - (s : ℝ)| := by
    show |SgT - ((round SgT : ℤ) : ℝ)| = |SgT - (s : ℝ)|
    rw [hround_SgT]
  rw [hdiEq] at hnearTilde
  exact hnearTilde

end Squarefree
