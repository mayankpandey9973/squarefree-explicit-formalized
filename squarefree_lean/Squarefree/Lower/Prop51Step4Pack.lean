import Squarefree.Lower.Prop51Step4PackFacts

/-!
# §5 assembly — the Step-4 capstone per-`r` obligations

Producers for `ra_step4_range_complete`'s caller obligations, all derived from the
`RaWitness` choice `dStarOf` (`Prop51Witness.lean`): the slope box `hb0box` (via
`bzero_le`), the global defect cap `hvmax` (via `v_defect_le`), the slope-model gap
`hb0gap` (via `step4_hb0gap`), the `φ_v` near-integer membership `hmem` (via
`phiv_distInt_from_witness`), and the 24-fact window bundle `hfibre`
(`step4_pack_bundle`).  Everything is stated per-`r` on the pair fiber
(`r, r+ℓ₁, r+ℓ₂ ∈ Ra`), with the `V₂var`-cutoff conjunct threaded only where needed
(fact 24).
-/

open Classical Finset Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- Fact 24 (curvature-domination at the cutoff): `10·ℓ₂(ℓ₂−ℓ₁)b₀²/d̃ ≤ 10⁶⁰·V₂`. -/
private theorem pack_fact24_core {L1 L2 b₀ dt : ℝ}
    (hL1 : 1 ≤ L1) (hL12 : L1 ≤ L2) (hL2 : L2 ≤ 130 * (P.G * P.U ^ 5))
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hdt : S.D / 2 ≤ dt)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) :
    10 * (L2 * (L2 - L1) * b₀ ^ 2 / dt) ≤ 10 ^ 60 * V₂ P S := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hDpos : (0:ℝ) < S.D := by rw [Scale.D]; positivity
  have hdtpos : (0:ℝ) < dt := lt_of_lt_of_le (by linarith) hdt
  have hBpos : (0:ℝ) < S.B := by rw [Scale.B]; positivity
  -- numerator bound
  have hL2nn : (0:ℝ) ≤ L2 := by linarith
  have hd0 : (0:ℝ) ≤ L2 - L1 := by linarith
  have hWnn : (0:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by positivity
  have hprod : L2 * (L2 - L1) ≤ 16900 * (P.G * P.U ^ 5) ^ 2 := by
    have h1' : L2 - L1 ≤ 130 * (P.G * P.U ^ 5) := by linarith
    calc L2 * (L2 - L1) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
          mul_le_mul hL2 h1' hd0 hWnn
      _ = 16900 * (P.G * P.U ^ 5) ^ 2 := by ring
  have hb0sq : b₀ ^ 2 ≤ (3000000000000 * S.B) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb0 2
  have hnum : L2 * (L2 - L1) * b₀ ^ 2
      ≤ 16900 * (P.G * P.U ^ 5) ^ 2 * ((3000000000000 * S.B) ^ 2) :=
    mul_le_mul hprod hb0sq (sq_nonneg _) (by positivity)
  -- `LHS ≤ num·(2/D)`
  have hinv : 1 / dt ≤ 2 / S.D := by
    rw [div_le_div_iff₀ hdtpos hDpos]
    linarith
  have hLHS : 10 * (L2 * (L2 - L1) * b₀ ^ 2 / dt)
      ≤ 10 * (16900 * (P.G * P.U ^ 5) ^ 2 * ((3000000000000 * S.B) ^ 2)) * (2 / S.D) := by
    have hnn : (0:ℝ) ≤ L2 * (L2 - L1) * b₀ ^ 2 :=
      mul_nonneg (mul_nonneg hL2nn hd0) (sq_nonneg _)
    have e1 : L2 * (L2 - L1) * b₀ ^ 2 / dt = (L2 * (L2 - L1) * b₀ ^ 2) * (1 / dt) := by ring
    rw [e1]
    have step1 : (L2 * (L2 - L1) * b₀ ^ 2) * (1 / dt)
        ≤ (L2 * (L2 - L1) * b₀ ^ 2) * (2 / S.D) :=
      mul_le_mul_of_nonneg_left hinv hnn
    have step2 : (L2 * (L2 - L1) * b₀ ^ 2) * (2 / S.D)
        ≤ (16900 * (P.G * P.U ^ 5) ^ 2 * ((3000000000000 * S.B) ^ 2)) * (2 / S.D) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    nlinarith [step1, step2]
  refine hLHS.trans ?_
  -- the explicit middle scale `T0 = 10⁶⁰·(Δ³/H)·U¹⁰/Ω⁶`
  have hmid : 10 * (16900 * (P.G * P.U ^ 5) ^ 2 * ((3000000000000 * S.B) ^ 2)) * (2 / S.D)
      = 3042000000000000000000000000000 * (S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6 := by
    rw [Scale.B, Scale.D]
    field_simp
    ring
  rw [hmid]
  -- `V₂ ≥ (Δ³/H)·U¹⁰/Ω⁶`
  have hsG : (1:ℝ) ≤ Real.sqrt P.G := Real.one_le_sqrt.mpr hG1
  have hsU : (1:ℝ) ≤ Real.sqrt P.U := Real.one_le_sqrt.mpr hU1
  have hG2 : (1:ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
  have hU12 : P.U ^ 10 ≤ P.U ^ 22 := pow_le_pow_right₀ hU1 (by norm_num)
  have hcore : (S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6 ≤ V₂ P S := by
    unfold V₂
    have hb : (0:ℝ) ≤ Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω) := by positivity
    have hmono : P.U ^ 10 ≤ P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U) := by
      have h22 : P.U ^ 22 ≤ P.U ^ 22 * Real.sqrt P.U := by
        nlinarith [pow_pos hUpos 22]
      have hpre : (1:ℝ) ≤ P.G ^ 2 * Real.sqrt P.G := by nlinarith
      nlinarith [hU12, h22, pow_pos hUpos 10, pow_pos hUpos 22]
    have hfac : (0:ℝ) ≤ (S.Δ ^ 3 / P.H) / S.Ω ^ 6 := by positivity
    have := mul_le_mul_of_nonneg_left hmono hfac
    calc (S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6
        = ((S.Δ ^ 3 / P.H) / S.Ω ^ 6) * P.U ^ 10 := by ring
      _ ≤ ((S.Δ ^ 3 / P.H) / S.Ω ^ 6)
            * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U)) := this
      _ = (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
            / S.Ω ^ 6 := by ring
      _ ≤ (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
            / S.Ω ^ 6 + Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω) := by linarith
  have hcnn : (0:ℝ) ≤ (S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6 := by positivity
  calc 3042000000000000000000000000000 * (S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6
      = 3042000000000000000000000000000 * ((S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6) := by ring
    _ ≤ 10 ^ 60 * ((S.Δ ^ 3 / P.H) * P.U ^ 10 / S.Ω ^ 6) := by nlinarith [hcnn]
    _ ≤ 10 ^ 60 * V₂ P S := by nlinarith [hcore]

set_option maxHeartbeats 3200000 in
/-- **The capstone 24-fact per-`r` window bundle `hfibre`**, from the `RaWitness` choice:
facts 1–12 from `dStarOf_spec`, 13–15 from `dstar_ne_of_gap`, 16–18 `dstar_decreasing`,
19–21 `dstar_placement`, 22 `dtilde_eps_window`, 23 `dstar_slope_lo`, 24 the
curvature-domination at the `10⁶⁰·V₂` cutoff (`pack_fact24_core`). -/
theorem step4_pack_bundle {a : ℤ} {Ra : Finset ℕ} {ℓ₁ ℓ₂ : ℕ} {V₂var : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hV2ge : 10 ^ 60 * V₂ P S ≤ V₂var)
    (hRa : ∀ r' ∈ Ra, RaWitness P S a r') :
    ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ V₂var < |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r|),
      ((1/72) * S.R ≤ (r : ℝ)) ∧ ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
      ∧ ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
      ∧ inDa P.X P.H a (dStarOf P S a r) ∧ inDa P.X P.H a (dStarOf P S a (r + ℓ₁))
      ∧ inDa P.X P.H a (dStarOf P S a (r + ℓ₂))
      ∧ (S.D ≤ (dStarOf P S a r : ℝ) ∧ (dStarOf P S a r : ℝ) ≤ 2 * S.D)
      ∧ (S.D ≤ (dStarOf P S a (r + ℓ₁) : ℝ) ∧ (dStarOf P S a (r + ℓ₁) : ℝ) ≤ 2 * S.D)
      ∧ (S.D ≤ (dStarOf P S a (r + ℓ₂) : ℝ) ∧ (dStarOf P S a (r + ℓ₂) : ℝ) ≤ 2 * S.D)
      ∧ (|Rfun P.X (a : ℝ) (dStarOf P S a r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
      ∧ (|Rfun P.X (a : ℝ) (dStarOf P S a (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))|
          ≤ 14 * P.H / S.D)
      ∧ (|Rfun P.X (a : ℝ) (dStarOf P S a (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))|
          ≤ 14 * P.H / S.D)
      ∧ ((dStarOf P S a (r + ℓ₁) : ℝ) ≠ (dStarOf P S a r : ℝ))
      ∧ ((dStarOf P S a (r + ℓ₂) : ℝ) ≠ (dStarOf P S a r : ℝ))
      ∧ ((dStarOf P S a (r + ℓ₂) : ℝ) ≠ (dStarOf P S a (r + ℓ₁) : ℝ))
      ∧ (dStarOf P S a (r + ℓ₁) - dStarOf P S a r ≤ (0:ℤ))
      ∧ (dStarOf P S a (r + ℓ₂) - dStarOf P S a r ≤ (0:ℤ))
      ∧ (dStarOf P S a (r + ℓ₂) - dStarOf P S a (r + ℓ₁) ≤ (0:ℤ))
      ∧ (a + (dStarOf P S a r - dStarOf P S a (r + ℓ₁)) ≤ dStarOf P S a (r + ℓ₁))
      ∧ (a + (dStarOf P S a r - dStarOf P S a (r + ℓ₂)) ≤ dStarOf P S a (r + ℓ₂))
      ∧ (a + (dStarOf P S a (r + ℓ₁) - dStarOf P S a (r + ℓ₂)) ≤ dStarOf P S a (r + ℓ₂))
      ∧ (S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X (r : ℝ) (a : ℝ)
          ∧ dtilde P.X (r : ℝ) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9))
      ∧ (S.B / 2000000 ≤ |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ))
            / ((ℓ₁ : ℤ) : ℝ)|)
      ∧ (10 * (((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))
            * (((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)) ^ 2
            / dtilde P.X (r : ℝ) (a : ℝ))
          ≤ |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r|) := by
  intro r hrf
  rw [Finset.mem_filter] at hrf
  obtain ⟨hr, hr1, hr2, hvcut⟩ := hrf
  -- raw witness bundles at the three points
  obtain ⟨hin0, hd0lo, hd0hi, hRd0, hr_lo, hr_hi⟩ := dStarOf_spec (hRa r hr)
  obtain ⟨hin1, hd1lo, hd1hi, hRd1raw, hr1_loraw, hr1_hiraw⟩ := dStarOf_spec (hRa (r + ℓ₁) hr1)
  obtain ⟨hin2, hd2lo, hd2hi, hRd2raw, hr2_loraw, hr2_hiraw⟩ := dStarOf_spec (hRa (r + ℓ₂) hr2)
  -- cast bridges
  have hc1Z : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
  have hc2Z : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
  have hc1N : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + (ℓ₁ : ℝ) := by push_cast; ring
  have hc2N : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + (ℓ₂ : ℝ) := by push_cast; ring
  have hcastm : ((r + ℓ₁ : ℕ) : ℝ) + ((ℓ₂ - ℓ₁ : ℕ) : ℝ) = ((r + ℓ₂ : ℕ) : ℝ) := by
    rw [← Nat.cast_add]; congr 1; omega
  -- ℤ-cast forms for the bundle conjuncts
  have hRd1Z := hRd1raw; rw [hc1Z] at hRd1Z
  have hRd2Z := hRd2raw; rw [hc2Z] at hRd2Z
  have hr1hiZ := hr1_hiraw; rw [hc1Z] at hr1hiZ
  have hr2hiZ := hr2_hiraw; rw [hc2Z] at hr2hiZ
  -- ℕ-cast forms for the windows lemmas
  have hRd1N := hRd1raw; rw [hc1N] at hRd1N
  have hRd2N := hRd2raw; rw [hc2N] at hRd2N
  have hr1hiN := hr1_hiraw; rw [hc1N] at hr1hiN
  have hr2hiN := hr2_hiraw; rw [hc2N] at hr2hiN
  -- distinctness (13–15)
  have hΔ28 := prop51_Δ28 (P := P) (S := S) hG1 hU1 hDeW
  have hgap1 : (1 : ℝ) ≤ |((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) - (r : ℝ)| := by
    rw [show ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) - (r : ℝ) = ((ℓ₁ : ℤ) : ℝ) from by ring,
      abs_of_nonneg (by positivity)]
    exact_mod_cast hℓ1
  have hgap2 : (1 : ℝ) ≤ |((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) - (r : ℝ)| := by
    rw [show ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) - (r : ℝ) = ((ℓ₂ : ℤ) : ℝ) from by ring,
      abs_of_nonneg (by positivity)]
    exact_mod_cast lt_trans hℓ1 hℓ12
  have hgap3 : (1 : ℝ) ≤ |((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))| := by
    rw [show ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))
        = ((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ) from by ring]
    have hz : ((ℓ₁ : ℤ) : ℝ) + 1 ≤ ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
    rw [abs_of_nonneg (by linarith)]; linarith
  have hne1 := dstar_ne_of_gap (S := S) hΔ28 hgap1 hRd0 hRd1Z
  have hne2 := dstar_ne_of_gap (S := S) hΔ28 hgap2 hRd0 hRd2Z
  have hne3 := dstar_ne_of_gap (S := S) hΔ28 hgap3 hRd1Z hRd2Z
  -- ℓ-window facts in `G·U⁵` form
  have hℓ2GU : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ1GU : (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hmGU : ((ℓ₂ - ℓ₁ : ℕ) : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    have hle : ((ℓ₂ - ℓ₁ : ℕ) : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast Nat.sub_le ℓ₂ ℓ₁
    linarith
  have hm1 : 0 < ℓ₂ - ℓ₁ := by omega
  -- decrease (16–18)
  have hdec1 := dstar_decreasing (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1
    hr_lo hr1hiN hd0lo hd0hi hd1lo hd1hi hRd0 hRd1N hG1 hU1 hUbig hDeW
  have hdec2 := dstar_decreasing (P := P) (S := S) hAD ha0 ha_lo ha_hi (lt_trans hℓ1 hℓ12)
    hr_lo hr2hiN hd0lo hd0hi hd2lo hd2hi hRd0 hRd2N hG1 hU1 hUbig hDeW
  have hrlm_hi : ((r + ℓ₁ : ℕ) : ℝ) + ((ℓ₂ - ℓ₁ : ℕ) : ℝ) ≤ 16 * S.R := by
    rw [hcastm]; exact hr2_hiraw
  have hRd2m : |Rfun P.X (a : ℝ) (dStarOf P S a (r + ℓ₂) : ℝ)
      - (((r + ℓ₁ : ℕ) : ℝ) + ((ℓ₂ - ℓ₁ : ℕ) : ℝ))| ≤ 14 * P.H / S.D := by
    rw [hcastm]; exact hRd2raw
  have hdec3 := dstar_decreasing (P := P) (S := S) (r := r + ℓ₁) (ℓ₁ := ℓ₂ - ℓ₁)
    (d₁ := dStarOf P S a (r + ℓ₁)) (d₂ := dStarOf P S a (r + ℓ₂))
    hAD ha0 ha_lo ha_hi hm1 hr1_loraw hrlm_hi hd1lo hd1hi hd2lo hd2hi
    hRd1raw hRd2m hG1 hU1 hUbig hDeW
  -- placement (19–21)
  have hpl1 := dstar_placement (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1 hℓ1GU
    hr_lo hr1hiN hd0lo hd0hi hd1lo hd1hi hRd0 hRd1N h1 hΩU hband hG1 hU1 hΔ1 hUbig
  have hpl2 := dstar_placement (P := P) (S := S) hAD ha0 ha_lo ha_hi (lt_trans hℓ1 hℓ12)
    hℓ2GU hr_lo hr2hiN hd0lo hd0hi hd2lo hd2hi hRd0 hRd2N h1 hΩU hband hG1 hU1 hΔ1 hUbig
  have hpl3 := dstar_placement (P := P) (S := S) (r := r + ℓ₁) (ℓ₁ := ℓ₂ - ℓ₁)
    (d₁ := dStarOf P S a (r + ℓ₁)) (d₂ := dStarOf P S a (r + ℓ₂))
    hAD ha0 ha_lo ha_hi hm1 hmGU hr1_loraw hrlm_hi hd1lo hd1hi hd2lo hd2hi
    hRd1raw hRd2m h1 hΩU hband hG1 hU1 hΔ1 hUbig
  -- fact 22
  have hwin22 := dtilde_eps_window (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
    hd0lo hd0hi hRd0 hG1 hΔ1 hUbig hReg
  -- fact 23 (ℕ-cast then bridge)
  have hslopeN := dstar_slope_lo (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1
    hr_lo hr1hiN hd0lo hd0hi hd1lo hd1hi hRd0 hRd1N hG1 hU1 hUbig hDeW
  have hcℓZ : ((ℓ₁ : ℤ) : ℝ) = ((ℓ₁ : ℕ) : ℝ) := by push_cast; ring
  have hslope23 : S.B / 2000000
      ≤ |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)| := by
    rw [hcℓZ]; exact hslopeN
  -- fact 24
  have hb0N := step4_pack_b0box (ℓ₂ := ℓ₂) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hG1 hΔ1 hRa hr hr1
  have hb0Z : |((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)|
      ≤ 3000000000000 * S.B := by rw [hcℓZ]; exact hb0N
  have hDpos : (0:ℝ) < S.D := by
    rw [Scale.D]; have := P.H_pos; have := S.Δ_pos; positivity
  have hdt2 : S.D / 2 ≤ dtilde P.X (r : ℝ) (a : ℝ) := by nlinarith [hwin22.1, hDpos]
  have hL1Z : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hL12Z : ((ℓ₁ : ℤ) : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12.le
  have hL2Z : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by push_cast; exact hℓ2GU
  have hfact24core := pack_fact24_core (P := P) (S := S)
    (L1 := ((ℓ₁ : ℤ) : ℝ)) (L2 := ((ℓ₂ : ℤ) : ℝ))
    (b₀ := ((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
    (dt := dtilde P.X (r : ℝ) (a : ℝ))
    hL1Z hL12Z hL2Z hb0Z hdt2 hG1 hU1
  have hfact24 : 10 * (((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))
        * (((dStarOf P S a (r + ℓ₁) : ℝ) - (dStarOf P S a r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)) ^ 2
        / dtilde P.X (r : ℝ) (a : ℝ))
      ≤ |vval P a (dStarOf P S a) ℓ₁ ℓ₂ r| :=
    le_trans hfact24core (le_trans hV2ge hvcut.le)
  exact ⟨hr_lo, hr1hiZ, hr2hiZ, hin0, hin1, hin2, ⟨hd0lo, hd0hi⟩, ⟨hd1lo, hd1hi⟩,
    ⟨hd2lo, hd2hi⟩, hRd0, hRd1Z, hRd2Z,
    by exact_mod_cast hne1.symm, by exact_mod_cast hne2.symm, by exact_mod_cast hne3.symm,
    hdec1, hdec2, hdec3,
    by exact_mod_cast hpl1, by exact_mod_cast hpl2, by exact_mod_cast hpl3,
    hwin22, hslope23, hfact24⟩

end Squarefree
