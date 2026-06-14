import Squarefree.Lower.DefectRegime
import Squarefree.Lower.DefectScales

/-!
# §5 Steps 2/3 delta bound — the `d→d̃` v-replacement piece (writeup 884–903)

`v_replace_le` bounds the genuinely new piece of the Steps 2/3 reduction:
`ℓ₁|v|·|(d̃/d)⁴−1| ≤ δ₂₃ := Δ²GU²⁰/(HΩ⁶)`.

Mechanism: `|(d̃/d)⁴−1| = |d̃⁴−d⁴|/d⁴ ≤ 4·18³·|d̃−d|/D` (since `d̃,d ≤ 18D`, `d ≥ D`),
`|d̃−d| ≤ 10¹²Δ/(GΩ³)`, `ℓ₁ ≤ GU⁵`, `|v| ≤ ΔU⁵/Ω³`, so the product is
`≤ 4·18³·10¹²·ΔU¹⁰/(HΩ⁶) ≤ Δ²GU²⁰/(HΩ⁶)` (the constant `4·18³·10¹² ≤ ΔGU¹⁰` by the regime
`Δ ≥ G²U⁵` and `U ≥ 10³³`).
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **Steps 2/3 delta: the v-replacement piece.** -/
theorem v_replace_le {a : ℤ} {r : ℝ} {ℓ₁ v : ℝ} {d : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hℓ1pos : 0 < ℓ₁) (hℓ1W : ℓ₁ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * S.D)
    (hd_close : |(d : ℝ) - dtilde P.X r (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    ℓ₁ * |v| * |(dtilde P.X r (a : ℝ) / (d : ℝ)) ^ 4 - 1|
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
  -- positivity of scale quantities
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  -- r > 0 from the lower window bound
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  -- d̃ ≍ D
  obtain ⟨hdt_lo, hdt_hi⟩ :=
    dtilde_asymp_D hAD (by exact_mod_cast ha0) hr0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  set dr : ℝ := (d : ℝ) with hdr_def
  -- d̃ > 0
  have hdt_pos : 0 < dt := lt_of_lt_of_le (by positivity) hdt_lo
  have hdt_nonneg : 0 ≤ dt := hdt_pos.le
  obtain ⟨hdr_lo, hdr_hi⟩ := hdwin
  have hdr_pos : 0 < dr := lt_of_lt_of_le hDpos hdr_lo
  have hdr_nonneg : 0 ≤ dr := hdr_pos.le
  have hdr_ne : dr ≠ 0 := ne_of_gt hdr_pos
  have hD4_pos : 0 < S.D ^ 4 := by positivity
  -- both ≤ 18 D
  have hdr_hi' : dr ≤ 18 * S.D := le_trans hdr_hi (by nlinarith [hDpos])
  -- KEY abs bound : |(dt/dr)^4 - 1| ≤ 4 * 18^3 * |dr - dt| / S.D
  have habs : |(dt / dr) ^ 4 - 1| ≤ 4 * 18 ^ 3 * |dr - dt| / S.D := by
    -- rewrite (dt/dr)^4 - 1 = (dt^4 - dr^4)/dr^4
    have hrw : (dt / dr) ^ 4 - 1 = (dt ^ 4 - dr ^ 4) / dr ^ 4 := by
      field_simp
    rw [hrw, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ dr ^ 4)]
    -- factor dt^4 - dr^4
    have hfac : dt ^ 4 - dr ^ 4
        = (dt - dr) * (dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3) := by ring
    rw [hfac, abs_mul]
    -- abs of the cubic sum bounded by 4*(18*S.D)^3
    have hsum_nonneg : 0 ≤ dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3 := by positivity
    have hsum_le : dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3 ≤ 4 * (18 * S.D) ^ 3 := by
      have hM : (0:ℝ) ≤ 18 * S.D := by positivity
      have h1 : dt ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hdt_nonneg hdt_hi 3
      have h4 : dr ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hdr_nonneg hdr_hi' 3
      -- dt^2*dr ≤ (18 D)^2 * (18 D) = (18 D)^3
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
    rw [abs_of_nonneg hsum_nonneg]
    -- |dt - dr| = |dr - dt|
    rw [abs_sub_comm dt dr]
    -- dr^4 ≥ S.D^4
    have hdr4_lo : S.D ^ 4 ≤ dr ^ 4 := pow_le_pow_left₀ hDpos.le hdr_lo 4
    have hdr4_pos : 0 < dr ^ 4 := by positivity
    -- combine: numerator up, denominator down
    have habs_nonneg : 0 ≤ |dr - dt| := abs_nonneg _
    calc |dr - dt| * (dt ^ 3 + dt ^ 2 * dr + dt * dr ^ 2 + dr ^ 3) / dr ^ 4
        ≤ |dr - dt| * (4 * (18 * S.D) ^ 3) / S.D ^ 4 := by
          apply div_le_div₀ (by positivity) _ hD4_pos hdr4_lo
          exact mul_le_mul_of_nonneg_left hsum_le habs_nonneg
      _ = 4 * 18 ^ 3 * |dr - dt| / S.D := by
          rw [show S.D ^ 4 = S.D * S.D ^ 3 by ring]
          rw [mul_pow]
          field_simp
  -- now bound ℓ₁*|v|*|(dt/dr)^4-1|
  have hℓ1pos' := hℓ1pos
  have hvabs_nonneg : 0 ≤ |v| := abs_nonneg v
  -- |dr - dt| ≤ 10^12 * Δ/(G Ω^3)
  have hd_close' : |dr - dt| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := hd_close
  -- ℓ₁ ≤ G U^5
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ1W; linarith [hℓ1W]
  -- Step: chain the bounds.
  -- First the product of the three nonneg factors.
  have key : ℓ₁ * |v| * |(dt / dr) ^ 4 - 1|
      ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
          * (4 * 18 ^ 3 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) / S.D) := by
    -- nonnegativity of all RHS-relevant factors
    have hb1 : 0 ≤ 4 * 18 ^ 3 * |dr - dt| / S.D := by positivity
    have hb1' : 4 * 18 ^ 3 * |dr - dt| / S.D
        ≤ 4 * 18 ^ 3 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) / S.D := by
      apply div_le_div_of_nonneg_right _ hDpos.le
      exact mul_le_mul_of_nonneg_left hd_close' (by positivity)
    have habs2 : |(dt / dr) ^ 4 - 1|
        ≤ 4 * 18 ^ 3 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) / S.D :=
      le_trans habs hb1'
    have hgu_pos : 0 ≤ 130 * (P.G * P.U ^ 5) := by positivity
    -- combine three monotone steps
    have hstep1 : ℓ₁ * |v| ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) := by
      apply mul_le_mul hℓ1W' hv hvabs_nonneg hgu_pos
    have hprod_nonneg : 0 ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) := by positivity
    have habs_nonneg2 : 0 ≤ |(dt / dr) ^ 4 - 1| := abs_nonneg _
    exact mul_le_mul hstep1 habs2 habs_nonneg2 hprod_nonneg
  refine le_trans key ?_
  -- Simplify T := the product into a single fraction with denominator P.H * S.Ω^6.
  have hSDeq : S.D = P.H * S.Δ := rfl
  have hTeq : (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
        * (4 * 18 ^ 3 * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) / S.D)
      = (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) * (S.Δ * P.U ^ 10) / (P.H * S.Ω ^ 6) := by
    rw [hSDeq]
    field_simp
  rw [hTeq]
  -- Now compare two fractions with the same positive denominator P.H * S.Ω^6.
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- Goal: (4*18^3*10^12) * (S.Δ * P.U^10) * (P.H * S.Ω^6)
  --        ≤ (S.Δ^2 * P.G * P.U^20) * (P.H * S.Ω^6).
  -- It suffices to show the constant bound: 4*18^3*10^12 ≤ S.Δ * P.G * P.U^10.
  have hG2 : (1:ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
  -- P.U^5 ≤ S.Δ  (from S.Δ ≥ G²U⁵ ≥ U⁵).
  have hΔ_lo : P.U ^ 5 ≤ S.Δ := by
    have hU5pos : (0:ℝ) ≤ P.U ^ 5 := by positivity
    calc P.U ^ 5 = 1 * P.U ^ 5 := (one_mul _).symm
      _ ≤ P.G ^ 2 * P.U ^ 5 := by
          apply mul_le_mul_of_nonneg_right hG2 hU5pos
      _ ≤ S.Δ := hΔreg
  -- U^15 ≥ the numeric constant (since U ≥ 10^33 ≥ 1).
  have hU15 : (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20 : ℝ) ≤ P.U ^ 15 := by
    have h2 : P.U ^ 2 ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
    have hU2 : (10:ℝ) ^ 66 ≤ P.U ^ 2 := by
      have : ((10:ℝ) ^ 33) ^ 2 ≤ P.U ^ 2 := pow_le_pow_left₀ (by norm_num) hUbig 2
      calc (10:ℝ) ^ 66 = ((10:ℝ) ^ 33) ^ 2 := by norm_num
        _ ≤ P.U ^ 2 := this
    have : (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20 : ℝ) ≤ (10:ℝ) ^ 66 := by norm_num
    linarith
  -- Constant bound: 4*18^3*10^12 ≤ S.Δ * P.G * P.U^10.
  have hconst : (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20 : ℝ) ≤ S.Δ * P.G * P.U ^ 10 := by
    have hpu10 : (0:ℝ) ≤ P.U ^ 10 := by positivity
    have hΔG : P.U ^ 5 ≤ S.Δ * P.G := by
      calc P.U ^ 5 = P.U ^ 5 * 1 := (mul_one _).symm
        _ ≤ S.Δ * P.G := by apply mul_le_mul hΔ_lo hG1 (by norm_num) hΔpos.le
    have hstep : P.U ^ 15 ≤ S.Δ * P.G * P.U ^ 10 := by
      calc P.U ^ 15 = P.U ^ 5 * P.U ^ 10 := by ring
        _ ≤ (S.Δ * P.G) * P.U ^ 10 := mul_le_mul_of_nonneg_right hΔG hpu10
    linarith [hU15, hstep]
  -- Finish: multiply the constant bound by the common positive factor (S.Δ * P.U^10 * P.H * S.Ω^6).
  have hcommon : (0:ℝ) ≤ S.Δ * P.U ^ 10 * (P.H * S.Ω ^ 6) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hconst hcommon
  -- hmul : (const) * (S.Δ*U^10*(H*Ω^6)) ≤ (S.Δ*G*U^10) * (S.Δ*U^10*(H*Ω^6))
  calc (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) * (S.Δ * P.U ^ 10) * (P.H * S.Ω ^ 6)
      = (130 * 4 * 18 ^ 3 * 1000000000000 * 10 ^ 20) * (S.Δ * P.U ^ 10 * (P.H * S.Ω ^ 6)) := by ring
    _ ≤ (S.Δ * P.G * P.U ^ 10) * (S.Δ * P.U ^ 10 * (P.H * S.Ω ^ 6)) := hmul
    _ = S.Δ ^ 2 * P.G * P.U ^ 20 * (P.H * S.Ω ^ 6) := by ring

/-- **The Steps 2/3 prefactor bound** `d̃⁴/(6Xa) ≤ 10⁶·Δ³/(HGΩ)`. From `d̃ ≤ 18D`
(`dtilde_asymp_D`), `a ≥ A/5`, and the scale identity `D⁴/(XA) = Δ³/(HGΩ)`
(`defect_D4_div_XA`); `18⁴·5/6 ≤ 10⁶`. -/
theorem prefactor_le {a : ℤ} {r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    (dtilde P.X r (a : ℝ)) ^ 4 / (6 * P.X * (a : ℝ))
      ≤ 10 ^ 6 * (S.Δ ^ 3 / (P.H * P.G * S.Ω)) := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  obtain ⟨hdt_lo, hdt_hi⟩ :=
    dtilde_asymp_D hAD (by exact_mod_cast ha0) hr0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  have hdt_nonneg : 0 ≤ dt := le_trans (by positivity) hdt_lo
  -- numerator: dt^4 ≤ 18^4 * S.D^4
  have hnum : dt ^ 4 ≤ 18 ^ 4 * S.D ^ 4 := by
    have := pow_le_pow_left₀ hdt_nonneg hdt_hi 4
    calc dt ^ 4 ≤ (18 * S.D) ^ 4 := this
      _ = 18 ^ 4 * S.D ^ 4 := by rw [mul_pow]
  -- denominator: 6 * P.X * a ≥ 6 * P.X * (S.A / 5) > 0
  have hden_lo : 6 * P.X * (S.A / 5) ≤ 6 * P.X * (a : ℝ) :=
    mul_le_mul_of_nonneg_left ha_lo (by positivity)
  have hden_pos : 0 < 6 * P.X * (S.A / 5) := by positivity
  -- bound the quotient: numerator up, denominator down
  have hstep : dt ^ 4 / (6 * P.X * (a : ℝ))
      ≤ (18 ^ 4 * S.D ^ 4) / (6 * P.X * (S.A / 5)) := by
    apply div_le_div₀ (by positivity) hnum hden_pos hden_lo
  -- (18^4 * S.D^4)/(6*X*(A/5)) = 87480 * (S.D^4/(X*A))
  have heq : (18 ^ 4 * S.D ^ 4) / (6 * P.X * (S.A / 5))
      = 87480 * (S.D ^ 4 / (P.X * S.A)) := by
    field_simp
    ring
  rw [heq, defect_D4_div_XA S] at hstep
  -- now: dt^4/(6Xa) ≤ 87480 * (Δ³/(HGΩ)) ≤ 10^6 * (Δ³/(HGΩ))
  refine le_trans hstep ?_
  apply mul_le_mul_of_nonneg_right (by norm_num : (87480:ℝ) ≤ 10 ^ 6)
  positivity

/-- **Steps 2/3 delta: the near-integer piece** `(d̃⁴/6Xa)·[ℓ₁(2H/d²+2H/d₂²)+ℓ₂(2H/d²+2H/d₁²)] ≤ δ₂₃`. -/
theorem near_int_piece_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hℓ1pos : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdD : S.D ≤ d) (hd1D : S.D ≤ d₁) (hd2D : S.D ≤ d₂)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    (dtilde P.X r (a : ℝ)) ^ 4 / (6 * P.X * (a : ℝ))
        * (ℓ₁ * (2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2)
           + ℓ₂ * (2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2))
      ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hd1_pos : 0 < d₁ := lt_of_lt_of_le hDpos hd1D
  have hd2_pos : 0 < d₂ := lt_of_lt_of_le hDpos hd2D
  -- prefactor bound
  have hpref := prefactor_le (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hpref_nn : 0 ≤ dt ^ 4 / (6 * P.X * (a : ℝ)) := by positivity
  -- inner: 2H/d² ≤ 2H/S.D² etc.
  have hHd2 : 2 * P.H / d ^ 2 ≤ 2 * P.H / S.D ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hDpos.le hdD 2
  have hHd1 : 2 * P.H / d₁ ^ 2 ≤ 2 * P.H / S.D ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hDpos.le hd1D 2
  have hHd2' : 2 * P.H / d₂ ^ 2 ≤ 2 * P.H / S.D ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hDpos.le hd2D 2
  -- each (2H/d²+2H/dᵢ²) ≤ 4H/S.D²
  have hpair2 : 2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2 ≤ 4 * P.H / S.D ^ 2 := by
    have : 2 * P.H / S.D ^ 2 + 2 * P.H / S.D ^ 2 = 4 * P.H / S.D ^ 2 := by ring
    linarith [hHd2, hHd2']
  have hpair1 : 2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2 ≤ 4 * P.H / S.D ^ 2 := by
    have : 2 * P.H / S.D ^ 2 + 2 * P.H / S.D ^ 2 = 4 * P.H / S.D ^ 2 := by ring
    linarith [hHd2, hHd1]
  -- ℓ₁, ℓ₂ ≤ P.G * P.U^5
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans (le_of_lt hℓ12) hℓ2W'
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := le_trans hℓ1nn hℓ12.le
  -- 4H/S.D² ≥ 0
  have h4Hnn : 0 ≤ 4 * P.H / S.D ^ 2 := by positivity
  -- inner bound: X₁ ≤ (ℓ₁+ℓ₂)*(4H/S.D²) ≤ 2*(G U^5)*(4H/S.D²) = 8 H G U^5 / S.D²
  have hinner : ℓ₁ * (2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2)
        + ℓ₂ * (2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2)
      ≤ 1040 * P.H * (P.G * P.U ^ 5) / S.D ^ 2 := by
    have t1 : ℓ₁ * (2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2) ≤ ℓ₁ * (4 * P.H / S.D ^ 2) :=
      mul_le_mul_of_nonneg_left hpair2 hℓ1nn
    have t2 : ℓ₂ * (2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2) ≤ ℓ₂ * (4 * P.H / S.D ^ 2) :=
      mul_le_mul_of_nonneg_left hpair1 hℓ2nn
    have t3 : ℓ₁ * (4 * P.H / S.D ^ 2) + ℓ₂ * (4 * P.H / S.D ^ 2)
        ≤ (130 * (P.G * P.U ^ 5)) * (4 * P.H / S.D ^ 2) + (130 * (P.G * P.U ^ 5)) * (4 * P.H / S.D ^ 2) := by
      have := mul_le_mul_of_nonneg_right hℓ1W' h4Hnn
      have := mul_le_mul_of_nonneg_right hℓ2W' h4Hnn
      linarith
    have t4 : (130 * (P.G * P.U ^ 5)) * (4 * P.H / S.D ^ 2) + (130 * (P.G * P.U ^ 5)) * (4 * P.H / S.D ^ 2)
        = 1040 * P.H * (P.G * P.U ^ 5) / S.D ^ 2 := by ring
    linarith
  have hinner_nn : 0 ≤ ℓ₁ * (2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2)
        + ℓ₂ * (2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2) := by positivity
  -- product bound
  have hprod : dt ^ 4 / (6 * P.X * (a : ℝ))
        * (ℓ₁ * (2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2)
           + ℓ₂ * (2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2))
      ≤ (10 ^ 6 * (S.Δ ^ 3 / (P.H * P.G * S.Ω))) * (1040 * P.H * (P.G * P.U ^ 5) / S.D ^ 2) := by
    apply mul_le_mul hpref hinner hinner_nn
    positivity
  refine le_trans hprod ?_
  -- simplify RHS using S.D = P.H * S.Δ
  have hSDeq : S.D = P.H * S.Δ := rfl
  have hT1 : (10 ^ 6 * (S.Δ ^ 3 / (P.H * P.G * S.Ω))) * (1040 * P.H * (P.G * P.U ^ 5) / S.D ^ 2)
      = (1040 * 10 ^ 6) * S.Δ * P.U ^ 5 / (P.H ^ 2 * S.Ω) := by
    rw [hSDeq]; field_simp
  rw [hT1]
  -- final: 8*10^6 * Δ * U^5/(H²Ω) ≤ Δ²GU²⁰/(HΩ⁶)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- (8*10^6 * Δ * U^5) * (H * Ω^6) ≤ (Δ²GU²⁰)*(H²Ω)
  -- suffices: 8*10^6 * Ω^5 ≤ Δ * G * U^15 * H
  have hΩ5 : S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩpos.le hΩU 5
  have hU15 : P.U ^ 15 = P.U ^ 5 * P.U ^ 10 := by ring
  have hUbig5 : (1040 * 10 ^ 6 : ℝ) ≤ P.U ^ 10 := by
    have h1 : (10:ℝ) ^ 10 ≤ P.U ^ 10 := pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) hUbig) 10
    have : (1040 * 10 ^ 6 : ℝ) ≤ (10:ℝ) ^ 10 := by norm_num
    linarith
  -- core: 8*10^6 * Ω^5 ≤ Δ*G*U^15*H
  have hcore : (1040 * 10 ^ 6 : ℝ) * S.Ω ^ 5 ≤ S.Δ * P.G * P.U ^ 15 * P.H := by
    calc (1040 * 10 ^ 6 : ℝ) * S.Ω ^ 5
        ≤ (1040 * 10 ^ 6 : ℝ) * P.U ^ 5 :=
          mul_le_mul_of_nonneg_left hΩ5 (by norm_num)
      _ ≤ (P.U ^ 10) * P.U ^ 5 := mul_le_mul_of_nonneg_right hUbig5 (by positivity)
      _ = P.U ^ 15 := by ring
      _ = 1 * 1 * P.U ^ 15 * 1 := by ring
      _ ≤ S.Δ * P.G * P.U ^ 15 * P.H := by
          gcongr
  -- goal: (8*10^6 * Δ * U^5) * (H * Ω^6) ≤ (Δ²GU²⁰)*(H²Ω)
  nlinarith [mul_le_mul_of_nonneg_right hcore
      (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 5 * P.H * S.Ω),
    hΩpos, hΔpos, hGpos, hHpos, hUpos]

/-- **Steps 2/3 delta: the smooth-phase replacement piece** `(d̃⁴/6Xa)·10⁴⁰δ₁ ≤ δ₂₃`,
`δ₁ = (1/Δ)G³U¹⁰/Ω⁵`. -/
theorem replace_piece_le {a : ℤ} {r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    (dtilde P.X r (a : ℝ)) ^ 4 / (6 * P.X * (a : ℝ))
        * ((10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5))
      ≤ S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha0
  -- prefactor bound
  have hpref := prefactor_le (P := P) (S := S) hAD ha0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  have hpref_nn : 0 ≤ dt ^ 4 / (6 * P.X * (a : ℝ)) := by positivity
  -- inner factor is nonneg
  have hinner_nn : 0 ≤ (10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5) := by
    positivity
  -- product bound
  have hprod : dt ^ 4 / (6 * P.X * (a : ℝ))
        * ((10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5))
      ≤ (10 ^ 6 * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))
          * ((10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5)) :=
    mul_le_mul_of_nonneg_right hpref hinner_nn
  refine le_trans hprod ?_
  -- simplify the RHS product to T₃ = 10^46 * Δ² * G² * U^10 / (H * Ω^6)
  have hT3 : (10 ^ 6 * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))
        * ((10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5))
      = (10:ℝ) ^ 51 * S.Δ ^ 2 * P.G ^ 2 * P.U ^ 10 / (P.H * S.Ω ^ 6) := by
    field_simp
  rw [hT3]
  -- final: 10^46 Δ² G² U^10/(HΩ⁶) ≤ Δ²G²U²⁰/(HΩ⁶)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- reduces to: 10^46 ≤ U^10
  have hU10 : (10:ℝ) ^ 51 ≤ P.U ^ 10 := by
    have : ((10:ℝ) ^ 33) ^ 10 ≤ P.U ^ 10 := pow_le_pow_left₀ (by norm_num) hUbig 10
    calc (10:ℝ) ^ 51 ≤ ((10:ℝ) ^ 33) ^ 10 := by norm_num
      _ ≤ P.U ^ 10 := this
  -- multiply by common positive factor (Δ²*G²*U^10*H*Ω^6)
  nlinarith [mul_le_mul_of_nonneg_right hU10
      (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * P.G ^ 2 * P.U ^ 10 * (P.H * S.Ω ^ 6)),
    hΔpos, hGpos, hHpos, hUpos, hΩpos]

end Squarefree
