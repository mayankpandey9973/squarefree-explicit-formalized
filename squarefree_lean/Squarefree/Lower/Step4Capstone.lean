import Squarefree.Lower.Step4CapstoneAux

/-!
# §5 Step-4 capstone: the large-defect range count (writeup 1025–1124)

`ra_step4_range_complete` assembles the green pieces: the per-fibre window bundle
(`step4_fibre_window_data`) supplies the signed `s`-extraction; `step4_pack_sign` pins the
sign so each `s`-fibre carries the uniform near-integer budget; `step4_fibre_count_le` counts
each fibre by `2·10²⁰⁰·weight5`; the ev-bridge (`8a·err ≤ 10¹¹²·ev_frozen·ΔΩ`-scale) freezes
the band slot; and `ra_step4_range_add5` collapses the s-sum into the faithful
`80·K·C·(H/Δ)·(t6'+t7')` bound with `K = 2·10³¹²`.
-/

open Finset Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 capstone (writeup 1025–1124): the large-defect range count.**

The range filter `Rng = {r ∈ Ra : r+ℓ₁, r+ℓ₂ ∈ Ra, V₂var < |v(r)|}` is counted by the
faithful collapse bound `80·(2·10³²²)·C·(H/Δ)·(G¹⁵U⁷⁵/(ΔΩ¹³) + Δ²G¹⁵U⁹⁰/(HΩ²⁷))`.

ADDED HYPOTHESES (flagged): `hbud : step4ErrU P S ≤ 1/4`,
`hδbud : 10⁷⁰·(1/Δ)G⁴U¹⁵/Ω⁵ ≤ 1/2` (the witness-defect half-width; at the band lower edge
`Ω⁴ ≍ 1/(GU³)` it is NOT implied by `hDeW` — a regime-largeness input like `hbud`), and
`hHbig : 10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴` — the X-power-small smallness of the near-integer budget
(its `10¹¹⁰·UpsT` term needs the global `H ≫ Δ²·(GU-powers)` calibration, not derivable from
the ambient regime facts listed here; `errB_quarter` discharges `hbud` from `hHbig`).

FILTER CUTOFF: the intended instantiation of the range-filter threshold is
`V₂var := 10⁶⁰ · V₂ P S` (the per-`r` err-domination in `step4_fiber_extract` consumes the
`10⁶⁰`-strengthened floor through `hV2ge`). -/
theorem ra_step4_range_complete
    (a : ℤ) (dStar : ℕ → ℤ) {ℓ₁ ℓ₂ : ℕ} {gap V₂var r₀ r₁ δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval) (hℓ2GU : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hgap0 : 0 ≤ gap)
    (hgapW : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * (ℓ₁ : ℝ))
        + 10 ^ 13 * (ℓ₁ : ℝ) * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + (ℓ₁:ℝ) ≤ 16 * S.R)
    (hδ : δ = 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5))
    -- the filter cutoff: the intended instantiation is `V₂var := 10 ^ 60 * V₂ P S`
    (hV2ge : 10 ^ 60 * V₂ P S ≤ V₂var)
    (hbud : step4ErrU P S ≤ 1 / 4)
    (hδbud : 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) ≤ 1 / 2)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14)
    (Ra : Finset ℕ) (N : ℕ) (C : ℝ) (hC : (10:ℝ) ^ 57 ≤ C) (hCcap : C ≤ (10:ℝ) ^ 120)
    (hNlo : 10 ^ 56 * ((ℓ₁:ℝ) ^ 3 * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) * P.U ^ 10 / S.Ω ^ 8
        ≤ (N : ℝ))
    (hNcap0 : (N : ℝ) ≤ 10 ^ 57 * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
        * P.U ^ 10 / S.Ω ^ 8)
    (hfibre : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|),
        ((1/72) * S.R ≤ (r : ℝ)) ∧ ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
        ∧ ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
        ∧ inDa P.X P.H a (dStar r) ∧ inDa P.X P.H a (dStar (r + ℓ₁))
        ∧ inDa P.X P.H a (dStar (r + ℓ₂))
        ∧ (S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D)
        ∧ (S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D)
        ∧ (S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D)
        ∧ (|Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
        ∧ (|Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))|
            ≤ 14 * P.H / S.D)
        ∧ (|Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))|
            ≤ 14 * P.H / S.D)
        ∧ ((dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ)) ∧ ((dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
        ∧ ((dStar (r + ℓ₂) : ℝ) ≠ (dStar (r + ℓ₁) : ℝ))
        ∧ (dStar (r + ℓ₁) - dStar r ≤ (0:ℤ)) ∧ (dStar (r + ℓ₂) - dStar r ≤ (0:ℤ))
        ∧ (dStar (r + ℓ₂) - dStar (r + ℓ₁) ≤ (0:ℤ))
        ∧ (a + (dStar r - dStar (r + ℓ₁)) ≤ dStar (r + ℓ₁))
        ∧ (a + (dStar r - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
        ∧ (a + (dStar (r + ℓ₁) - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
        ∧ (S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X (r : ℝ) (a : ℝ)
            ∧ dtilde P.X (r : ℝ) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9))
        ∧ (S.B / 2000000 ≤ |((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)|)
        ∧ (10 * (((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))
              * (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)) ^ 2
              / dtilde P.X (r : ℝ) (a : ℝ))
            ≤ |vval P a dStar ℓ₁ ℓ₂ r|))
    (hb0box : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|),
        |((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / (ℓ₁ : ℝ)| ≤ 3000000000000 * S.B)
    (hvmax : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|),
        |vval P a dStar ℓ₁ ℓ₂ r| ≤ Vmax P S)
    (hb0gap : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|),
        |((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / (ℓ₁ : ℝ)
          - b1Model P.X (a : ℝ) (dtilde P.X (r : ℝ) (a : ℝ))| ≤ gap)
    (hmem : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|),
        r₀ ≤ (r : ℝ) ∧ (r : ℝ) ≤ r₁ ∧
        distInt (phiv P.X (a : ℝ) (ℓ₁ : ℝ) (ℓ₂ : ℝ) (vval P a dStar ℓ₁ ℓ₂ r) (r : ℝ)) ≤ δ) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|)).card : ℝ)
      ≤ 80 * (2 * 10 ^ 322) * C * (P.H / S.Δ) *
          (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
           + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
  classical
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have ha0R : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha0
  have hℓ1R : (1:ℝ) ≤ (ℓ₁:ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁:ℝ) + 1 ≤ (ℓ₂:ℝ) := by exact_mod_cast hℓ12
  have hℓ1ltR : (ℓ₁:ℝ) < (ℓ₂:ℝ) := by linarith
  have hℓ1n : 0 < ℓ₁ := hℓ1
  have hℓ12n : ℓ₁ < ℓ₂ := by omega
  have hℓ2WZ : ((ℓ₂:ℤ):ℝ) ≤ 130 * P.Wval := by push_cast; exact hℓ2W
  have hHcap : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := (le_div_iff₀ (by positivity)).mp h1
  have hU10H : P.U ^ 10 ≤ P.H := by
    have hGΔ2 : (1:ℝ) ≤ P.G * S.Δ ^ 2 := by
      nlinarith only [one_le_pow₀ hΔ1 (n := 2), hG1]
    nlinarith only [hHcap, pow_pos hUpos 10, hGΔ2]
  have hΩH : 60 * S.Ω ≤ P.H := by
    have hU9 : (10:ℝ) ^ 297 ≤ P.U ^ 9 := by
      calc (10:ℝ) ^ 297 = ((10:ℝ) ^ 33) ^ 9 := by rw [← pow_mul]
        _ ≤ P.U ^ 9 := pow_le_pow_left₀ (by norm_num) hUbig 9
    have h55U : 60 * P.U ≤ P.U ^ 10 := by
      have h55 : (60:ℝ) ≤ 10 ^ 297 := by
        calc (60:ℝ) ≤ 10 ^ 2 := by norm_num
          _ ≤ 10 ^ 297 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      calc 60 * P.U ≤ 10 ^ 297 * P.U := mul_le_mul_of_nonneg_right h55 hUpos.le
        _ ≤ P.U ^ 9 * P.U := mul_le_mul_of_nonneg_right hU9 hUpos.le
        _ = P.U ^ 10 := by ring
    linarith [mul_le_mul_of_nonneg_left hΩU (by norm_num : (0:ℝ) ≤ 60)]
  have hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ := by
    have hGU : (1:ℝ) ≤ P.G ^ 2 * P.U ^ 15 := by
      nlinarith only [one_le_pow₀ hG1 (n := 2), one_le_pow₀ hU1 (n := 15)]
    nlinarith only [hDeW, mul_le_mul_of_nonneg_left hGU
      (by positivity : (0:ℝ) ≤ P.G ^ 2 * P.U ^ 5),
      (by positivity : (0:ℝ) ≤ P.G ^ 2 * P.U ^ 5)]
  have hA1 : (1:ℝ) ≤ (ℓ₁:ℝ) * (ℓ₂:ℝ) := by
    nlinarith only [mul_nonneg (by linarith : (0:ℝ) ≤ (ℓ₁:ℝ) - 1)
      (by linarith : (0:ℝ) ≤ (ℓ₂:ℝ) - 1), hℓ1R, hℓ1ltR]
  have hL1 : (1:ℝ) ≤ (ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) := by
    nlinarith only [mul_nonneg (by linarith : (0:ℝ) ≤ (ℓ₁:ℝ) * (ℓ₂:ℝ) - 1)
      (by linarith : (0:ℝ) ≤ (ℓ₂:ℝ) - (ℓ₁:ℝ) - 1), hA1, hℓ12R]
  have hLnn : (0:ℝ) ≤ (ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) := le_trans zero_le_one hL1
  have hℓ1GU : (ℓ₁:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by linarith
  have hLW3 : (ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)) ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3 := by
    have hd : (ℓ₂:ℝ) - (ℓ₁:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by linarith
    have hℓ2pos : (0:ℝ) < (ℓ₂:ℝ) := by linarith
    calc (ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))
        ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) := by
          have h12 : (ℓ₁:ℝ) * (ℓ₂:ℝ) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
            mul_le_mul hℓ1GU hℓ2GU hℓ2pos.le (by positivity)
          exact mul_le_mul h12 hd (by linarith) (by positivity)
      _ = 130 ^ 3 * (P.G * P.U ^ 5) ^ 3 := by ring
  have hC1 : (1:ℝ) ≤ C := le_trans (by norm_num) hC
  have hNcapC : (N:ℝ) ≤ C * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
      * P.U ^ 10 / S.Ω ^ 8 := by
    have hx : (0:ℝ) ≤ (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
        * P.U ^ 10 / S.Ω ^ 8 :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hLnn) (by positivity))
        (by positivity)
    calc (N:ℝ) ≤ 10 ^ 57 * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
          * P.U ^ 10 / S.Ω ^ 8 := hNcap0
      _ = 10 ^ 57 * ((ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
          * P.U ^ 10 / S.Ω ^ 8) := by ring
      _ ≤ C * ((ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
          * P.U ^ 10 / S.Ω ^ 8) := mul_le_mul_of_nonneg_right hC hx
      _ = C * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
          * P.U ^ 10 / S.Ω ^ 8 := by ring
  -- the signed window extraction
  have hNloZ : 10 ^ 56 * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
      * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))) * P.U ^ 10 / S.Ω ^ 8 ≤ (N : ℝ) := by
    push_cast
    exact hNlo
  obtain ⟨sgn, hsgn⟩ := step4_fibre_window_data (P := P) (S := S) (V₂ := V₂var)
    hAD ha0 ha_lo ha_hi hℓ1n hℓ12n hℓ12 hℓ2WZ hReg h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
    hΩH hDeW hHbig Ra N hNloZ hV2ge hfibre
  set Rng : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|) with hRngDef
  -- positivity of the extracted integers over the range filter
  have hsgnpos : ∀ r ∈ Rng, 0 < sgn r := by
    intro r hr
    obtain ⟨hIcc, hround, _⟩ := hsgn r hr
    obtain ⟨h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ := hfibre r hr
    push_cast at hround h23 h24
    have hV2nn0 : 0 ≤ V₂ P S := by rw [V₂]; positivity
    have hVcut' : V₂ P S ≤ |vval P a dStar ℓ₁ ℓ₂ r| := by
      have hmem' : r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|) := by rwa [hRngDef] at hr
      have h60 := le_trans hV2ge (Finset.mem_filter.mp hmem').2.2.2.le
      linarith only [h60, hV2nn0]
    have hℓ1Rpos : (0:ℝ) < (ℓ₁:ℝ) := by linarith
    have hb0neg : ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / (ℓ₁ : ℝ) < 0 := by
      apply div_neg_of_neg_of_pos ?_ hℓ1Rpos
      have hle : ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) ≤ 0 := by exact_mod_cast h16
      exact lt_of_le_of_ne hle (sub_ne_zero.mpr h13)
    have hs1 : (1:ℝ) ≤ |((sgn r):ℝ)| := by
      have h1n : 1 ≤ (sgn r).natAbs := (Finset.mem_Icc.mp hIcc).1
      have habs : |((sgn r):ℝ)| = (((sgn r).natAbs : ℤ) : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
      rw [habs]
      exact_mod_cast h1n
    have hroundR : ((sgn r):ℝ) = (round (Sigma_closed P.X (a:ℝ)
        (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / (ℓ₁ : ℝ))
        (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r:ℝ) (a:ℝ)) (ℓ₁:ℝ) (ℓ₂:ℝ)) : ℝ) := by
      exact_mod_cast congrArg (fun z => ((z:ℤ):ℝ)) hround.symm
    exact step4_pack_sign (P := P) (S := S) ha0R ha_lo ha_hi hℓ1R hℓ1ltR hℓ12R hℓ2W
      (hb0box r hr) h23 hb0neg (hvmax r hr) h24 hVcut' h22.1 h22.2
      hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hs1 hroundR
  -- per-fibre five-slot count, with the band slot frozen via the ev-bridge
  have hfiber : ∀ n ∈ Finset.Icc 1 N,
      ((Rng.filter (fun r => (sgn r).natAbs = n)).card : ℝ)
        ≤ 2 * 10 ^ 322 * weight5 (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
            ((P.G ^ 4 * P.U ^ 20 / S.Δ
                + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
              * (S.Δ * S.Ω) / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
            (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
              * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
            (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
            (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n:ℝ) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hsub : Rng.filter (fun r => (sgn r).natAbs = n) ⊆ Rng := Finset.filter_subset _ _
    have herr_small : step4ErrU P S ≤ (1/4) * (n:ℝ) := by
      have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith only [hbud, hn1R]
    have hnNcap : (n:ℝ) ≤ 10 ^ 57 * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
        * P.U ^ 10 / S.Ω ^ 8 := by
      have hcast : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
      linarith [hNcap0]
    have hsgn_eq : ∀ r ∈ Rng.filter (fun r => (sgn r).natAbs = n), sgn r = (n:ℤ) := by
      intro r hr
      have hp := hsgnpos r (hsub hr)
      have he : (sgn r).natAbs = n := (Finset.mem_filter.mp hr).2
      omega
    have hcnt := step4_fibre_count_le (P := P) (S := S) a dStar
      (fun r => ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / (ℓ₁ : ℝ))
      (fun r => dtilde P.X (r:ℝ) (a:ℝ))
      ha0R ha_lo ha_hi hℓ1 hℓ12 hℓ2W hℓ2GU hG1 hU1 hUbig hΔ1 hH1 hΩU hband
      (by rw [hδ]; exact hδbud) h1 hReg hDeW hAD
      hgap0 hgapW step4ErrU_nonneg herr_small hr0_lo hr01 hr1_hi hδ hn1 hnNcap
      (Rng.filter (fun r => (sgn r).natAbs = n))
      (fun r hr => hb0box r (hsub hr))
      (fun r hr => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          h23, _⟩ := hfibre r (hsub hr)
        push_cast at h23
        exact h23)
      (fun r hr => hvmax r (hsub hr))
      (fun r hr => by
        have hr' : r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ V₂var < |vval P a dStar ℓ₁ ℓ₂ r|) := by
          have hx := hsub hr; rwa [hRngDef] at hx
        have hV2nn0 : 0 ≤ V₂ P S := by rw [V₂]; positivity
        have h60 := le_trans hV2ge (Finset.mem_filter.mp hr').2.2.2.le
        linarith only [h60, hV2nn0])
      (fun r hr => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h22,
          _, _⟩ := hfibre r (hsub hr)
        exact h22.1)
      (fun r hr => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h22,
          _, _⟩ := hfibre r (hsub hr)
        exact h22.2)
      (fun r hr => hb0gap r (hsub hr))
      (fun r hr => by
        have hrR := hsub hr
        obtain ⟨hIcc, hround, hbudget⟩ := hsgn r hrR
        obtain ⟨h01, h02, _, _, _, _, h07, _, _, h10, _⟩ := hfibre r hrR
        have hr16 : (r:ℝ) ≤ 16 * S.R := by
          have hcast : (1:ℝ) ≤ ((ℓ₁:ℤ):ℝ) := by exact_mod_cast hℓ1
          linarith [h02]
        have hclose : |dtilde P.X (r:ℝ) (a:ℝ) - (dStar r : ℝ)|
            ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
          rw [abs_sub_comm]
          exact dtilde_close hAD ha0 ha_lo ha_hi h01 hr16 h07.1 h07.2 h10
        have hEq : ((n:ℤ):ℝ) = ((sgn r):ℝ) := by
          exact_mod_cast (hsgn_eq r hr).symm
        push_cast at hbudget
        have hD : (0:ℝ) < S.D := by unfold Scale.D; positivity
        have hcoeff : (0:ℝ) ≤ 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D := by
          positivity
        have hrest : 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S
            + 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
              * |dtilde P.X (r:ℝ) (a:ℝ) - (dStar r : ℝ)| ≤ step4ErrU P S := by
          unfold step4ErrU
          have hm := mul_le_mul_of_nonneg_left hclose hcoeff
          linarith
        rw [hEq]
        exact hbudget.trans hrest)
      (fun r hr => hmem r (hsub hr))
    -- freeze the band slot: ev' = 8a·errU/√L ≤ 10¹¹²·evF, then scale out the 10¹¹²
    have hbev := step4_ev_bridge (P := P) (S := S) ha_hi hG1 hU1 hΩU hband hUbig hReg
      hDeW hL1
    have hb0' : (0:ℝ) ≤ P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2) := by positivity
    have hdc0 : (0:ℝ) ≤ P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
        * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) := by positivity
    have hcE0 := cEhyb_nonneg' (P := P) (S := S) ha0R hℓ1R hℓ12R hgap0
    have hcE20 := cE2hyb_nonneg' (P := P) (S := S) ha0R hℓ1R hℓ12R
    have hcC0 := cChyb_nonneg' (P := P) (S := S) ha0R hℓ1R hℓ12R
    have hn0R : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hw1 := weight5_mono_ev (b := P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
      (dc := P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
        * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
      (cE := cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE₂ := cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
      (cC := cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n := (n:ℝ)) hb0' hdc0 hbev
    have hw2 := weight5_ev_scale (k := (10:ℝ) ^ 122)
      (b := P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
      (ev := (P.G ^ 4 * P.U ^ 20 / S.Δ
          + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
        * (S.Δ * S.Ω) / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
      (dc := P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
        * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
      (cE := cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE₂ := cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
      (cC := cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n := (n:ℝ))
      (by norm_num) hb0' hdc0 hcE0 hcE20 hcC0 hn0R
    refine hcnt.trans ?_
    have hchain := hw1.trans hw2
    calc 2 * 10 ^ 200 * weight5 (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          (8 * (a:ℝ) * step4ErrU P S / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
          (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
            * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
          (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
          (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n:ℝ)
        ≤ 2 * 10 ^ 200 * (10 ^ 122
            * weight5 (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
              ((P.G ^ 4 * P.U ^ 20 / S.Δ
                  + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
                * (S.Δ * S.Ω) / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
              (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
                * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
              (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
              (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n:ℝ)) :=
          mul_le_mul_of_nonneg_left hchain (by norm_num)
      _ = 2 * 10 ^ 322
            * weight5 (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
              ((P.G ^ 4 * P.U ^ 20 / S.Δ
                  + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
                * (S.Δ * S.Ω) / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
              (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4
                * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
              (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
              (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n:ℝ) := by
          rw [show ((10:ℝ) ^ 322 : ℝ) = 10 ^ 200 * 10 ^ 122 from by rw [← pow_add]]
          ring
  -- the six absorb fits
  have hcE0 := cEhyb_nonneg' (P := P) (S := S) ha0R hℓ1R hℓ12R hgap0
  have hcE20 := cE2hyb_nonneg' (P := P) (S := S) ha0R hℓ1R hℓ12R
  have hcC0 := cChyb_nonneg' (P := P) (S := S) ha0R hℓ1R hℓ12R
  have hcE2maj := cE2hyb_le_majorant (P := P) (S := S) ha_hi hℓ1R hℓ12R
  have hEA := step4_fit_cE_A (P := P) (S := S) h1 hDeW hG1 hU1 hΔ1 hH1 hΩU hband hUbig N
    (ℓ₁:ℝ) (ℓ₂:ℝ) hℓ1R hℓ12R hℓ1GU hℓ2GU C hC1 hCcap hNcapC (a:ℝ) gap ha0R ha_hi hgap0
    hgapW _ rfl
  have hEB := step4_fit_cE_B (P := P) (S := S) h1 hG1 hU1 hΔ1 hΩU hUbig N
    (ℓ₁:ℝ) (ℓ₂:ℝ) hℓ1R hℓ12R hℓ1GU hℓ2GU C hC1 hNcapC (a:ℝ) gap ha0R ha_hi hgap0
    hgapW _ rfl
  have hEC := step4_fit_cubic_A (P := P) (S := S) hG1 hU1 hΔ1 hH1 hUbig N
    (ℓ₁:ℝ) ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) hℓ1R hL1 hℓ1GU hLW3 C hC1 hCcap hNcapC
    _ (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) rfl hcE2maj
  have hED := step4_fit_cubic_B (P := P) (S := S) hG1 hU1 hΔ1 hΩU hUbig N
    (ℓ₁:ℝ) ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) hℓ1R hL1 hℓ1GU hLW3 C hC1 hCcap hNcapC
    _ (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) rfl hcE2maj
  have hEE := step4_fit_cC_E (P := P) (S := S) hG1 hU1 hΔ1 hH1 hΩU hUbig hDeW N
    (ℓ₁:ℝ) (ℓ₂:ℝ) hℓ1R hℓ12R hℓ1GU hℓ2GU C hC1 hNcapC (a:ℝ) ha0R ha_hi _ rfl
  have hEF := step4_fit_cC_F (P := P) (S := S) h1 hG1 hU1 hΔ1 hH1 hΩU hUbig N
    (ℓ₁:ℝ) (ℓ₂:ℝ) hℓ1R hℓ12R hℓ1GU hℓ2GU C hC1 hCcap hNcapC (a:ℝ) ha0R ha_hi _ rfl
  -- the five-slot collapse
  exact ra_step4_range_add5 (P := P) (S := S) h1 hΔreg hG1 hU1 hΔ1 hH1 hΩU hUbig N
    (ℓ₁:ℝ) ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))) hℓ1R hL1 hℓ1GU hLW3 C hC1 hNcapC
    (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
    ((P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
      * (S.Δ * S.Ω) / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
    (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
    (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
    (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) rfl rfl rfl hcE0 hcE20 hcC0
    hEA hEB hEC hED hEE hEF (2 * 10 ^ 322) (by norm_num) Rng
    (fun r => (sgn r).natAbs) (fun r hr => (hsgn r hr).1) hfiber

end Squarefree
