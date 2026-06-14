import Squarefree.Lower.Prop51Witness
import Squarefree.Lower.Step4WindowFacts
import Squarefree.Lower.Step4Hb0gap
import Squarefree.Lower.Step3VBound
import Squarefree.Lower.Step4PhivWitness
import Squarefree.Lower.DefectBt

/-!
# §5 Step-4 pack: per-point hypothesis facts
The pointwise pack facts (`b0box`, `vmax`, `hb0gap`, `hmem`) feeding
`step4_pack_bundle`, each discharged from the witness/window layer.
-/

open Classical Finset Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- Closeness of the witness defect to the smooth profile, at a fiber point, with the
shifted-cast form `dtilde (r + (ℓ:ℤ:ℝ))`. -/
private theorem pack_close {a : ℤ} {Ra : Finset ℕ} {r ℓ : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hRa : ∀ r' ∈ Ra, RaWitness P S a r') (hmem : r + ℓ ∈ Ra) :
    |(dStarOf P S a (r + ℓ) : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
  obtain ⟨_, hlo, hhi, hRd, hr_lo, hr_hi⟩ := dStarOf_spec (hRa (r + ℓ) hmem)
  have hc : ((r + ℓ : ℕ) : ℝ) = (r : ℝ) + ((ℓ : ℤ) : ℝ) := by push_cast; ring
  rw [hc] at hRd hr_lo hr_hi
  exact dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi hlo hhi hRd

/-- `hb0box`: the discrete slope box `|b₀| ≤ 3·10¹²·B` on the pair fiber. -/
theorem step4_pack_b0box {a : ℤ} {Ra : Finset ℕ} {ℓ₁ ℓ₂ : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hG1 : 1 ≤ P.G) (hΔ1 : 1 ≤ S.Δ)
    (hRa : ∀ r' ∈ Ra, RaWitness P S a r')
    {r : ℕ} (hr : r ∈ Ra) (hr1 : r + ℓ₁ ∈ Ra) :
    |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / (ℓ₁ : ℝ)|
      ≤ 3000000000000 * S.B := by
  obtain ⟨_, hlo, hhi, hRd, hr_lo, hr_hi⟩ := dStarOf_spec (hRa r hr)
  have hd_close : |(dStarOf P S a r : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi hlo hhi hRd
  have hd1_close := pack_close (ℓ := ℓ₁) hAD ha0 ha_lo ha_hi hRa hr1
  have hcℓ : ((ℓ₁ : ℤ) : ℝ) = ((ℓ₁ : ℕ) : ℝ) := by push_cast; ring
  rw [hcℓ] at hd1_close
  obtain ⟨_, _, _, _, _, hr_hi'⟩ := dStarOf_spec (hRa (r + ℓ₁) hr1)
  have hrl_hi : (r : ℝ) + (ℓ₁ : ℝ) ≤ 16 * S.R := by
    have : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + (ℓ₁ : ℝ) := by push_cast; ring
    rw [this] at hr_hi'
    exact hr_hi'
  exact bzero_le (P := P) (S := S) hAD (by exact_mod_cast ha0) ha_lo ha_hi
    (by exact_mod_cast hℓ1) (by exact_mod_cast hℓ1) hr_lo hrl_hi hd_close hd1_close hG1 hΔ1

/-- `hvmax`: the global defect cap `|v(r)| ≤ Vmax` on the pair fiber. -/
theorem step4_pack_vmax {a : ℤ} {Ra : Finset ℕ} {ℓ₁ ℓ₂ : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hRa : ∀ r' ∈ Ra, RaWitness P S a r')
    {r : ℕ} (hr : r ∈ Ra) (hr1 : r + ℓ₁ ∈ Ra) (hr2 : r + ℓ₂ ∈ Ra) :
    |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r| ≤ Vmax P S := by
  obtain ⟨_, hlo, hhi, hRd, hr_lo, hr_hi⟩ := dStarOf_spec (hRa r hr)
  have hd_close : |(dStarOf P S a r : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi hlo hhi hRd
  have hd1_close := pack_close (ℓ := ℓ₁) hAD ha0 ha_lo ha_hi hRa hr1
  have hd2_close := pack_close (ℓ := ℓ₂) hAD ha0 ha_lo ha_hi hRa hr2
  obtain ⟨_, _, _, _, _, hr2_hi'⟩ := dStarOf_spec (hRa (r + ℓ₂) hr2)
  have hr2_hi : (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R := by
    have : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
    rw [this] at hr2_hi'
    exact hr2_hi'
  have hkey := v_defect_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ))
    (d := dStarOf P S a r) (d₁ := dStarOf P S a (r + ℓ₁)) (d₂ := dStarOf P S a (r + ℓ₂))
    hAD ha0 ha_lo ha_hi (by exact_mod_cast hℓ1) (by exact_mod_cast hℓ1)
    (by exact_mod_cast hℓ12) hℓ2W hr_lo hr2_hi
    hd_close hd1_close hd2_close h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hvshape : vval P a (dStarOf P S a) ℓ₁ ℓ₂ r
      = ((dStarOf P S a (r + ℓ₂) : ℝ) - (dStarOf P S a r : ℝ))
        - (((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ))
            * ((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) := by
    unfold vval; ring
  rw [hvshape]
  refine le_trans hkey ?_
  unfold Vmax
  have hpos : (0:ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by
    have := S.Δ_pos; have := P.U_pos; have := S.Ω_pos; positivity
  nlinarith [hpos]

/-- `hb0gap`: the discrete-vs-smooth slope gap on the pair fiber, at the capstone's
two-term literal budget (the `step4_hb0gap` bound with `B/R = Δ³/(HG²Ω⁶)` unfolded). -/
theorem step4_pack_hb0gap {a : ℤ} {Ra : Finset ℕ} {ℓ₁ : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁)
    (hRa : ∀ r' ∈ Ra, RaWitness P S a r')
    {r : ℕ} (hr : r ∈ Ra) (hr1 : r + ℓ₁ ∈ Ra) :
    |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / (ℓ₁ : ℝ)
        - b1Model P.X (a : ℝ) (dtilde P.X (r : ℝ) (a : ℝ))|
      ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * (ℓ₁ : ℝ))
        + 10 ^ 13 * (ℓ₁ : ℝ) * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6) := by
  have ha0R : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓpos : (0:ℝ) < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  obtain ⟨_, hlo, hhi, hRd, hr_lo, hr_hi⟩ := dStarOf_spec (hRa r hr)
  have hd_close : |(dStarOf P S a r : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi hlo hhi hRd
  have hd1_close := pack_close (ℓ := ℓ₁) hAD ha0 ha_lo ha_hi hRa hr1
  push_cast at hd1_close
  obtain ⟨_, _, _, _, _, hr_hi'⟩ := dStarOf_spec (hRa (r + ℓ₁) hr1)
  have hrl_hi : (r : ℝ) + (ℓ₁ : ℝ) ≤ 16 * S.R := by push_cast at hr_hi'; linarith
  have hkey := step4_hb0gap (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℝ)) (d := (dStarOf P S a r : ℝ)) (dℓ := (dStarOf P S a (r + ℓ₁) : ℝ))
    hAD ha0R ha_lo ha_hi hℓpos hr_lo hrl_hi hd_close hd1_close
  refine hkey.trans (le_of_eq ?_)
  have hHpos := P.H_pos; have hGpos := P.G_pos; have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  rw [Scale.B, Scale.R]
  field_simp
  ring

/-- `hmem` payload: the `φ_v` near-integer bound on the pair fiber, in the capstone's
ℕ-cast `phiv` shape. -/
theorem step4_pack_hmem {a : ℤ} {Ra : Finset ℕ} {ℓ₁ ℓ₂ : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hRa : ∀ r' ∈ Ra, RaWitness P S a r')
    {r : ℕ} (hr : r ∈ Ra) (hr1 : r + ℓ₁ ∈ Ra) (hr2 : r + ℓ₂ ∈ Ra) :
    distInt (phiv P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ)
        (vval P a (dStarOf P S a) ℓ₁ ℓ₂ r) (r : ℝ))
      ≤ 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) := by
  obtain ⟨hinDa, hlo, hhi, hRd, hr_lo, _⟩ := dStarOf_spec (hRa r hr)
  obtain ⟨hinDa1, _, _, _, _, _⟩ := dStarOf_spec (hRa (r + ℓ₁) hr1)
  obtain ⟨hinDa2, _, _, _, _, _⟩ := dStarOf_spec (hRa (r + ℓ₂) hr2)
  obtain ⟨hd1win, hd2win, hRd1, hRd2, hr1_hi, hr2_hi, hd1ned, hd2ned⟩ :=
    witness_hwin hℓ1 hℓ12 hG1 hU1 hDeW hRa r hr hr1 hr2
  have hℓ1ne : ((ℓ₁ : ℤ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
    exact this.ne'
  have hℓ2bv_ne : (((ℓ₂ : ℤ) : ℝ))
        * (((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
      + vval P a (dStarOf P S a) ℓ₁ ℓ₂ r ≠ 0 := by
    have hid : (((ℓ₂ : ℤ) : ℝ))
          * (((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
        + vval P a (dStarOf P S a) ℓ₁ ℓ₂ r
        = (dStarOf P S a (r + ℓ₂) : ℝ) - (dStarOf P S a r : ℝ) := by
      unfold vval; field_simp; ring
    rw [hid]
    exact sub_ne_zero.mpr hd2ned
  have hkey := phiv_distInt_from_witness (P := P) (S := S) (a := a)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r) (dStar := dStarOf P S a)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ1 hℓ12 (by push_cast; exact hℓ2W)
    hr_lo hr1_hi hr2_hi hinDa hinDa1 hinDa2 ⟨hlo, hhi⟩ hd1win hd2win
    hRd hRd1 hRd2 hd1ned hℓ2bv_ne
    h1 hΔreg hband hG1 hU1 hΔ1 hH1 hΩU hUbig hUH
  push_cast at hkey
  exact hkey

end Squarefree
