import Squarefree.Lower.DefectRegime
import Squarefree.Lower.DefectScales

/-!
# §5 Step-4 delta — the pref-free `v`-replacement piece (writeup 1067, 1071)

`vterm_le` bounds the pref-free Step-4 `v`-replacement term
`6ℓ₁Xa|v|·|1/d̃⁴ − 1/d⁴| = (6Xa/d̃⁴)·ℓ₁|v||(d̃/d)⁴−1|` against `δ = (1/Δ)G⁴U¹⁵/Ω⁵`.
With `6Xa/d̃⁴ ≤ 6.6·10⁵·HGΩ/Δ³` (from `d̃ ≥ D/10`, `a ≤ 11A`, `XA/D⁴ = HGΩ/Δ³`) and the TIGHT
`ℓ₁|v||(d̃/d)⁴−1| ≤ 4·18³·10³²·ΔU¹⁰/(HΩ⁶)` (from `|(d̃/d)⁴−1| ≤ 4·18³|d̃−d|/D ≤ 4·18³·10¹²/(GHΩ³)`
and `ℓ₁|v| ≤ 10²⁰GΔU¹⁰/Ω³`), the product is `≤ δ`.  The tighter `ΔU¹⁰` numerator (vs the
Steps 2/3 `v_replace_le`'s `Δ²GU²⁰`) is what makes the pref-free Step-4 budget close.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **§5 Step-4 delta: the pref-free `v`-replacement piece** (piece 3). -/
theorem vterm_le {a : ℤ} {r : ℝ} {ℓ₁ v : ℝ} {d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hℓ1pos : 0 < ℓ₁) (hℓ1W : ℓ₁ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hd_close : |d - dtilde P.X r (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hH1 : 1 ≤ P.H) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    6 * ℓ₁ * P.X * (a : ℝ) * |v| * |1 / (dtilde P.X r (a : ℝ)) ^ 4 - 1 / d ^ 4|
      ≤ (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5 := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haR : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  obtain ⟨hdt_lo, hdt_hi⟩ :=
    dtilde_asymp_D (P := P) (S := S) hAD haR hr0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  set dr : ℝ := d with hdr_def
  have hdt_pos : 0 < dt := lt_of_lt_of_le (by positivity) hdt_lo
  have hdt_nonneg : 0 ≤ dt := hdt_pos.le
  obtain ⟨hdr_lo, hdr_hi⟩ := hdwin
  have hdr_pos : 0 < dr := lt_of_lt_of_le hDpos hdr_lo
  have hdr_nonneg : 0 ≤ dr := hdr_pos.le
  have hdr_ne : dr ≠ 0 := ne_of_gt hdr_pos
  have hdt_ne : dt ≠ 0 := ne_of_gt hdt_pos
  have hdr_hi' : dr ≤ 18 * S.D := le_trans hdr_hi (by nlinarith [hDpos])
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ1W; exact hℓ1W
  have hvabs_nonneg : 0 ≤ |v| := abs_nonneg v
  -- ===== factor 1: 6Xa/dt⁴ ≤ 660000·HGΩ/Δ³ =====
  have hpref : 6 * P.X * (a : ℝ) / dt ^ 4 ≤ 660000 * (P.H * P.G * S.Ω / S.Δ ^ 3) := by
    have hnum : 6 * P.X * (a : ℝ) ≤ 66 * (P.X * S.A) := by nlinarith [ha_hi, hXpos.le]
    have hden_lo : (S.D / 10) ^ 4 ≤ dt ^ 4 := pow_le_pow_left₀ (by positivity) hdt_lo 4
    have hden_pos : (0:ℝ) < (S.D / 10) ^ 4 := by positivity
    have hstep : 6 * P.X * (a : ℝ) / dt ^ 4 ≤ 66 * (P.X * S.A) / (S.D / 10) ^ 4 :=
      div_le_div₀ (by positivity) hnum hden_pos hden_lo
    refine le_trans hstep (le_of_eq ?_)
    have hXAD : P.X * S.A / S.D ^ 4 = P.H * P.G * S.Ω / S.Δ ^ 3 := by
      have := defect_D4_div_XA (P := P) (S := S)
      rw [div_eq_div_iff (by positivity) (by positivity)] at this ⊢
      nlinarith [this, hΔpos, hHpos, hGpos, hΩpos, hXpos, hApos, hDpos]
    rw [show (66:ℝ) * (P.X * S.A) / (S.D / 10) ^ 4 = 660000 * (P.X * S.A / S.D ^ 4) by
      field_simp; ring, hXAD]
  have hpref_nn : 0 ≤ 6 * P.X * (a : ℝ) / dt ^ 4 := by positivity
  -- ===== factor 2: ℓ₁|v|·|(dt/dr)⁴−1| ≤ 4·18³·10³²·ΔU¹⁰/(HΩ⁶) =====
  have hD4_pos : 0 < S.D ^ 4 := by positivity
  have habs : |(dt / dr) ^ 4 - 1| ≤ 4 * 18 ^ 3 * |dr - dt| / S.D := by
    have hrw2 : (dt / dr) ^ 4 - 1 = (dt ^ 4 - dr ^ 4) / dr ^ 4 := by field_simp
    rw [hrw2, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ dr ^ 4)]
    have hfac : dt ^ 4 - dr ^ 4
        = (dt - dr) * (dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3) := by ring
    rw [hfac, abs_mul]
    have hsum_nonneg : 0 ≤ dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3 := by positivity
    have hsum_le : dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3 ≤ 4 * (18 * S.D) ^ 3 := by
      have hM : (0:ℝ) ≤ 18 * S.D := by positivity
      have h1 : dt ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hdt_nonneg hdt_hi 3
      have h4 : dr ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hdr_nonneg hdr_hi' 3
      have h2 : dt ^ 2 * dr ≤ (18 * S.D) ^ 3 := by
        have hdt2 : dt ^ 2 ≤ (18 * S.D) ^ 2 := pow_le_pow_left₀ hdt_nonneg hdt_hi 2
        calc dt ^ 2 * dr ≤ (18 * S.D) ^ 2 * (18 * S.D) :=
              mul_le_mul hdt2 hdr_hi' hdr_nonneg (by positivity)
          _ = (18 * S.D) ^ 3 := by ring
      have h3 : dt * dr ^ 2 ≤ (18 * S.D) ^ 3 := by
        have hdr2 : dr ^ 2 ≤ (18 * S.D) ^ 2 := pow_le_pow_left₀ hdr_nonneg hdr_hi' 2
        calc dt * dr ^ 2 ≤ (18 * S.D) * (18 * S.D) ^ 2 :=
              mul_le_mul hdt_hi hdr2 (by positivity) hM
          _ = (18 * S.D) ^ 3 := by ring
      linarith [h1, h2, h3, h4]
    rw [abs_of_nonneg hsum_nonneg, abs_sub_comm dt dr]
    have hdr4_lo : S.D ^ 4 ≤ dr ^ 4 := pow_le_pow_left₀ hDpos.le hdr_lo 4
    have habs_nonneg : 0 ≤ |dr - dt| := abs_nonneg _
    calc |dr - dt| * (dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3) / dr ^ 4
        ≤ |dr - dt| * (4 * (18 * S.D) ^ 3) / S.D ^ 4 := by
          apply div_le_div₀ (by positivity) _ hD4_pos hdr4_lo
          exact mul_le_mul_of_nonneg_left hsum_le habs_nonneg
      _ = 4 * 18 ^ 3 * |dr - dt| / S.D := by
          rw [show S.D ^ 4 = S.D * S.D ^ 3 by ring, mul_pow]; field_simp
  have hd_close' : |dr - dt| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := hd_close
  have hfac2 : ℓ₁ * |v| * |(dt / dr) ^ 4 - 1|
      ≤ (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) * (S.Δ * P.U ^ 10) / (P.H * S.Ω ^ 6) := by
    have habs2 : |(dt / dr) ^ 4 - 1|
        ≤ 4 * 18 ^ 3 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) / S.D := by
      refine le_trans habs ?_
      apply div_le_div_of_nonneg_right _ hDpos.le
      exact mul_le_mul_of_nonneg_left hd_close' (by positivity)
    have hstep1 : ℓ₁ * |v| ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) :=
      mul_le_mul hℓ1W' hv hvabs_nonneg (by positivity)
    have hkey : ℓ₁ * |v| * |(dt / dr) ^ 4 - 1|
        ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
            * (4 * 18 ^ 3 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) / S.D) :=
      mul_le_mul hstep1 habs2 (abs_nonneg _) (by positivity)
    refine le_trans hkey (le_of_eq ?_)
    rw [show S.D = P.H * S.Δ from rfl]; field_simp
  -- ===== combine the two factors =====
  have habs_rw : |1 / dt ^ 4 - 1 / dr ^ 4| = (1 / dt ^ 4) * |(dt / dr) ^ 4 - 1| := by
    rw [show (1 / dt ^ 4 - 1 / dr ^ 4) = (1 / dt ^ 4) * (1 - (dt / dr) ^ 4) by
      field_simp]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / dt ^ 4), abs_sub_comm]
  have hregroup : 6 * ℓ₁ * P.X * (a : ℝ) * |v| * |1 / dt ^ 4 - 1 / dr ^ 4|
        = (6 * P.X * (a : ℝ) / dt ^ 4) * (ℓ₁ * |v| * |(dt / dr) ^ 4 - 1|) := by
    rw [habs_rw]; field_simp
  rw [hregroup]
  have hcomb : (6 * P.X * (a : ℝ) / dt ^ 4) * (ℓ₁ * |v| * |(dt / dr) ^ 4 - 1|)
      ≤ (660000 * (P.H * P.G * S.Ω / S.Δ ^ 3))
          * ((130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) * (S.Δ * P.U ^ 10) / (P.H * S.Ω ^ 6)) :=
    mul_le_mul hpref hfac2 (by positivity) (by positivity)
  refine le_trans hcomb ?_
  have hT : (660000 * (P.H * P.G * S.Ω / S.Δ ^ 3))
        * ((130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) * (S.Δ * P.U ^ 10) / (P.H * S.Ω ^ 6))
      = (660000 * (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20)) * P.G * P.U ^ 10 / (S.Δ ^ 2 * S.Ω ^ 5) := by
    field_simp
  rw [hT]
  rw [show (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5
        = P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 5) by field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hUconst : (660000 * (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) : ℝ) ≤ P.U ^ 5 := by
    have : ((10:ℝ) ^ 33) ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ (by norm_num) hUbig 5
    calc (660000 * (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) : ℝ) ≤ ((10:ℝ) ^ 33) ^ 5 := by norm_num
      _ ≤ P.U ^ 5 := this
  have hconst : (660000 * (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) : ℝ) ≤ S.Δ * P.G ^ 3 * P.U ^ 5 := by
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    calc (660000 * (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) : ℝ) ≤ P.U ^ 5 := hUconst
      _ = 1 * 1 * P.U ^ 5 := by ring
      _ ≤ S.Δ * P.G ^ 3 * P.U ^ 5 := by gcongr
  nlinarith [mul_le_mul_of_nonneg_right hconst
      (by positivity : (0:ℝ) ≤ P.G * P.U ^ 10 * (S.Δ * S.Ω ^ 5)),
    hΔpos, hGpos, hUpos, hΩpos]

end Squarefree
