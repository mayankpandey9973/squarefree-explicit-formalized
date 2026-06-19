import Squarefree.Lower.Step1Reduce
import Squarefree.Lower.Step1Delta
import Squarefree.Lower.DefectBt

/-!
# §5 Step-1 v=0 discharge (writeup 826–840)

Combines the two green per-`r` pieces into the uniform bound:

* `phi_norm_le_v0` (Step1Reduce) :  `distInt(φ(r)) ≤ near-int + 𝒬-E-bound + 10⁴⁰δ`
* `delta_eff_le`   (Step1Delta)  :  that RHS `≤ δ_unif := 10⁶⁰·(1/Δ)G³U¹⁵/Ω⁵`,
  given `|b₀| ≤ 3·10¹²·B`.

The only new content here is the discrete-slope bound `|b₀| ≤ 3·10¹²·B`
(`b₀ = (d₁−d)/ℓ₁`), obtained from the two closeness bounds
`|d−d̃(r)|, |d₁−d̃(r+ℓ₁)| ≤ 10¹²·Δ/(GΩ³)` and `bt_abs_bounds` (`|b̃| ≤ 10⁶·B`):
`b₀ = b̃ + ((d₁−d̃(r+ℓ₁)) − (d−d̃(r)))/ℓ₁`, so `|b₀ − b̃| ≤ 2·10¹²·Δ/(GΩ³) ≤ 2·10¹²·B`
(using `Δ≥1`, `ℓ₁≥1`, `B = Δ²/(GΩ³)`).
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **Step-1 v=0 discharge.** For a `v=0` witness triple `d,d₁,d₂ ∈ 𝒟_a` at the
`D`-scale (each close to the smooth defect `d̃`), the phase is uniformly near-integer:
`distInt(φ(r)) ≤ δ_unif := 10⁶⁰·(1/Δ)·G³·U¹⁵/Ω⁵`. -/
theorem phi_distInt_le_unif {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hr_lo : (1/72) * S.R ≤ r) (hr1_hi : r + (ℓ₁ : ℝ) ≤ 16 * S.R)
    (hin : inDa P.X P.H a d) (hin1 : inDa P.X P.H a d₁) (hin2 : inDa P.X P.H a d₂)
    (hdpos : 0 < (d:ℝ)) (hd1pos : 0 < (d₁:ℝ)) (hd2pos : 0 < (d₂:ℝ))
    (hdwin : S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2*S.D) (hd1win : S.D ≤ (d₁:ℝ) ∧ (d₁:ℝ) ≤ 2*S.D)
    (hd2win : S.D ≤ (d₂:ℝ) ∧ (d₂:ℝ) ≤ 2*S.D)
    (hv0 : (ℓ₁:ℝ) * ((d₂:ℝ) - (d:ℝ)) = (ℓ₂:ℝ) * ((d₁:ℝ) - (d:ℝ)))
    (hb0ne : (d₁:ℝ) ≠ (d:ℝ))
    (hwin : 4 * ((a:ℝ) + (ℓ₂:ℝ) * |((d₁:ℝ) - (d:ℝ))/(ℓ₁:ℝ)|) ≤ (d:ℝ))
    (hd_close  : |(d:ℝ)  - dtilde P.X r (a:ℝ)|             ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hd1_close : |(d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hΩU : S.Ω ≤ P.U) :
    Counting.distInt (phi P.X (a:ℝ) ℓ₁ ℓ₂ r)
      ≤ (10:ℝ)^60 * ((1/S.Δ) * P.G^3 * P.U^15 / S.Ω^5) := by
  -- Cast / positivity facts.
  have hℓ1R : (0:ℝ) < (ℓ₁:ℝ) := by exact_mod_cast hℓ1
  have hℓ1ne : (ℓ₁:ℝ) ≠ 0 := ne_of_gt hℓ1R
  have hℓ1_loR : (1:ℝ) ≤ (ℓ₁:ℝ) := by exact_mod_cast hℓ1_lo
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha0
  have hGΩ : 0 < P.G * S.Ω ^ 3 := by
    have := P.G_pos; have := S.Ω_pos; positivity
  have hBpos : 0 < S.B := by
    rw [Scale.B]; have := S.Δ_pos; positivity
  -- ===== PART A:  |b₀| ≤ 3·10¹²·B  where b₀ = (d₁−d)/ℓ₁ =====
  -- The smooth slope `bt` and its bounds.
  obtain ⟨_, _, hbt_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := (a:ℝ)) (ℓ := (ℓ₁:ℝ)) (r := r)
      hAD haR hℓ1R ha_lo ha_hi hr_lo hr1_hi
  -- Unfold `bt` so it is the explicit difference quotient.
  rw [bt] at hbt_hi
  set b₀ : ℝ := ((d₁:ℝ) - (d:ℝ)) / (ℓ₁:ℝ) with hb₀_def
  set bt₀ : ℝ := (dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ) - dtilde P.X r (a:ℝ)) / (ℓ₁:ℝ) with hbt_def
  -- `Δ/(GΩ³) ≤ B` since `B = Δ²/(GΩ³)` and `Δ ≥ 1`.
  have hΔB : S.Δ / (P.G * S.Ω ^ 3) ≤ S.B := by
    rw [Scale.B]
    rw [div_le_div_iff₀ hGΩ hGΩ]
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith [S.Δ_pos, hΔ1]
    exact mul_le_mul_of_nonneg_right hΔsq hGΩ.le
  -- `|b₀ − bt₀| ≤ 2·10¹²·B`.
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
              + 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
              exact add_le_add hd1_close hd_close
        _ = 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by ring
    -- divide by ℓ₁ ≥ 1, then use Δ/(GΩ³) ≤ B
    have hstep : |((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
            - ((d:ℝ) - dtilde P.X r (a:ℝ))| / (ℓ₁:ℝ)
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
      rw [div_le_iff₀ hℓ1R]
      have hnn : (0:ℝ) ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
        have := S.Δ_pos; positivity
      have hle : 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
          ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) * (ℓ₁:ℝ) := by
        have := mul_le_mul_of_nonneg_left hℓ1_loR hnn
        simpa using this
      exact le_trans hnum hle
    calc |((d₁:ℝ) - dtilde P.X (r + (ℓ₁:ℝ)) (a:ℝ))
            - ((d:ℝ) - dtilde P.X r (a:ℝ))| / (ℓ₁:ℝ)
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := hstep
      _ ≤ 2000000000000 * S.B :=
            mul_le_mul_of_nonneg_left hΔB (by norm_num)
  -- Combine with `|bt₀| ≤ 10⁶·B`.
  have hb0 : |b₀| ≤ 3000000000000 * S.B := by
    have htri : |b₀| ≤ |bt₀| + |b₀ - bt₀| := by
      have h := abs_add_le bt₀ (b₀ - bt₀)
      have he : bt₀ + (b₀ - bt₀) = b₀ := by ring
      rwa [he] at h
    have hsum : |b₀| ≤ 1000000 * S.B + 2000000000000 * S.B :=
      le_trans htri (add_le_add hbt_hi hdiff)
    have hfact : (1000000 : ℝ) * S.B + 2000000000000 * S.B
        = 2000001000000 * S.B := by ring
    have hmono : (2000001000000 : ℝ) * S.B ≤ 3000000000000 * S.B :=
      mul_le_mul_of_nonneg_right (by norm_num) hBpos.le
    rw [hfact] at hsum
    exact le_trans hsum hmono
  -- ===== PART B:  chain the two lemmas =====
  exact le_trans
    (phi_norm_le_v0 hAD ha0 ha_lo ha_hi hℓ1 hℓ1_lo hℓ12 hℓ2W hr_lo hr1_hi
      hin hin1 hin2 hdpos hd1pos hd2pos hdwin hd1win hv0 hb0ne hwin
      hd_close hd1_close h1 hband hG1 hU1 hΔ1 hUH)
    (delta_eff_le (b₀ := b₀) ha_hi haR hℓ1R
      (by exact_mod_cast hℓ12) hℓ2W hdwin hd1win.1 hd2win.1 hb0
      h1 hband hG1 hU1 hΔ1 hΩU)

end Squarefree
