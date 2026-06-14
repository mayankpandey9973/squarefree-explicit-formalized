import Squarefree.Lower.Step4Compose
import Squarefree.Lower.Step4VsBand
import Squarefree.Lower.Step4Emax
import Squarefree.Lower.Step4SigmaSign
import Squarefree.Lower.Prop51Partition

/-!
# §5 Step-4 per-point packers (writeup 1052–1064, 1108–1124)

Per-point suppliers marshalled into the exact hypothesis shapes of `step4_fibre_branch_le`:
`step4_pack_sqlo` (the `hsq_lo` pin + v-box), `step4_pack_sign` (sign of the extracted
integer, plus the ℤ-collation fact), `step4_pack_lat` (the `ℓ₁⁻¹ℤ` lattice witness).
-/

open Real

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 lattice packer.**  The `hlat` shape of `step4_fibre_branch_le` for
`vOf := vval P a dStar ℓ₁ ℓ₂`: every per-`r` defect lies on the `ℓ₁⁻¹ℤ` lattice. -/
theorem step4_pack_lat (a : ℤ) (dStar : ℕ → ℤ) {ℓ₁ : ℕ} (ℓ₂ : ℕ) (hℓ1 : 0 < ℓ₁) (r : ℕ) :
    ∃ k : ℤ, vval P a dStar ℓ₁ ℓ₂ r = (k : ℝ) / (ℓ₁ : ℝ) := by
  refine ⟨(ℓ₁ : ℤ) * (dStar (r + ℓ₂) - dStar r) - (ℓ₂ : ℤ) * (dStar (r + ℓ₁) - dStar r), ?_⟩
  have hℓ1R : ((ℓ₁ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ1.ne'
  rw [vval]
  push_cast
  field_simp

/-- ℤ-collation: two positive integers with the same `natAbs` are equal (so two fibre points
whose extracted integers are positive with `natAbs = n` share the SAME integer `s = n`). -/
theorem step4_pack_sign_eq {z z' : ℤ} (hz : 0 < z) (hz' : 0 < z')
    (h : z.natAbs = z'.natAbs) : z = z' := by omega

/-- **§5 Step-4 sign packer.**  Thin re-export of `round_Sigma_closed_pos`: in the `b₀ < 0`
regime the extracted integer `s = round(Σ_closed)` is positive.  Together with
`step4_pack_sign_eq` this lets the composer identify the integers of any two fibre points in
the same `natAbs`-class. -/
theorem step4_pack_sign
    {a b₀ v d ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hb0neg : b₀ < 0)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) :
    0 < s :=
  round_Sigma_closed_pos (P := P) (S := S) ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W
    hb0 hb0lo hb0neg hv hvlo hVcut hdD hd2D hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hs1 hround

/-- Nonnegativity of the model parabola value `Ĉ·v² = (Cref·(A/a)²·ℓ₁²)·v²`. -/
private theorem Cv2_nonneg {a v ℓ₁ ℓ₂ : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    0 ≤ (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2 := by
  have hC := Cref_pos (P := P) (S := S) (lt_of_lt_of_le one_pos hℓ1) hℓ12
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg v)

/-- `ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v² ≤ (121/3)·Δ²Ω²·(Ĉ·v²)` — the `a²`-window conversion (sharp `a ≤ 11A`),
via the exact identity `Ĉ·a² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)`. -/
private theorem L3v2_le_Cv2 {a v ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2
      ≤ (121 / 3) * (S.Δ ^ 2 * S.Ω ^ 2)
          * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hane : a ≠ 0 := ha0.ne'
  have hCa2 : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * a ^ 2
      = 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) := by
    rw [show S.A = S.Δ * S.Ω from rfl,
      show Cref P S ℓ₁ ℓ₂ = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (S.Δ ^ 2 * S.Ω ^ 2) from rfl]
    field_simp
  have hkey : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2 * a ^ 2
      = 3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) := by
    linear_combination v ^ 2 * hCa2
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  have ha2 : a ^ 2 ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haA)
      (by positivity : (0:ℝ) ≤ 11 * (S.Δ * S.Ω) + a)]
  have hCnn := Cv2_nonneg (P := P) (S := S) (a := a) (v := v) hℓ1 hℓ12
  nlinarith [mul_le_mul_of_nonneg_left ha2 hCnn, hkey]

/-- `|pref| = (Xa/d⁵)·|−4+10a/d| ≤ 77·GΩ/Δ⁴` — the closed-form prefactor size. -/
private theorem pref_abs_le {a d : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    (P.X * a / d ^ 5) * |(-4 + 10 * a / d)| ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by
  have hGpos := P.G_pos; have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hXpos := P.X_pos
  have hDpos : 0 < S.D := by unfold Scale.D; exact mul_pos P.H_pos hΔpos
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  obtain ⟨_, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hQle : P.X * a / d ^ 5 ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
    have hD5 : S.D ^ 5 = P.X * S.Δ ^ 5 / P.G := by
      unfold Scale.D; rw [P.X_eq_G_mul_H_pow_five]; field_simp
    have hd5ge : S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5 ≤ d ^ 5 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hdD 5
    calc P.X * a / d ^ 5 ≤ P.X * a / (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by gcongr
      _ = a * P.G / (S.Δ ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by rw [hD5]; field_simp
      _ ≤ 12 * P.G * S.Ω / S.Δ ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right haA
            (by positivity : (0:ℝ) ≤ P.G * S.Δ ^ 4), hΔpos, hΩpos, hGpos,
            mul_pos (mul_pos hGpos (pow_pos hΔpos 5)) hΩpos]
  calc (P.X * a / d ^ 5) * |(-4 + 10 * a / d)|
      ≤ (12 * P.G * S.Ω / S.Δ ^ 4) * 4 :=
        mul_le_mul hQle hbr (abs_nonneg _) (by positivity)
    _ = 48 * (P.G * S.Ω / S.Δ ^ 4) := by ring
    _ ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by
        have : (0:ℝ) ≤ P.G * S.Ω / S.Δ ^ 4 := by positivity
        linarith

/-- The sharp `p₂/cubic`-residual piece: `|pref|·(10⁻⁵⁰·L₃|b₀|v²) ≤ (1/48)·Ĉv²`
(`b₀`-window `|b₀| ≤ 3·10¹²·B`, `B = Δ²/(GΩ³)`, then `a ≤ 11A`; net `9317·10⁻³⁸ ≤ 1/48`). -/
private theorem resid_piece_le {a b₀ v ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) :
    77 * (P.G * S.Ω / S.Δ ^ 4)
        * ((1 / 10 ^ 50) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2))
      ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
  have hGpos := P.G_pos; have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hℓ1R : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : (0:ℝ) < ℓ₂ := lt_trans hℓ1R hℓ12
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hL3nn : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hℓ1R.le 3) hℓ2R.le) h21nn) (sq_nonneg v)
  have hCnn := Cv2_nonneg (P := P) (S := S) (a := a) (v := v) hℓ1 hℓ12
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
    rw [show S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) from rfl] at hb0; exact hb0
  have hL3 := L3v2_le_Cv2 (P := P) (S := S) (v := v) ha0 ha_hi hℓ1 hℓ12
  have hmul : |b₀| * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)
      ≤ (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
          * ((121 / 3) * (S.Δ ^ 2 * S.Ω ^ 2)
              * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2)) :=
    mul_le_mul hb0' hL3 hL3nn (by positivity)
  calc 77 * (P.G * S.Ω / S.Δ ^ 4)
        * ((1 / 10 ^ 50) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2))
      = (77 / 10 ^ 50) * (P.G * S.Ω / S.Δ ^ 4)
          * (|b₀| * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)) := by ring
    _ ≤ (77 / 10 ^ 50) * (P.G * S.Ω / S.Δ ^ 4)
          * ((3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
              * ((121 / 3) * (S.Δ ^ 2 * S.Ω ^ 2)
                  * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2))) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = (9317 / 10 ^ 38) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
        field_simp
        ring
    _ ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hCnn

/-- The slope-reconstruction piece: `(Xa/d⁵)·3ℓ₁ℓ₂(ℓ₂−ℓ₁)·|−4+10a/d|·gap·(ℓ₁v)² ≤ (1/48)·Ĉv²`
under the RELAXED two-term gap budget (from `step4_hb0gap`): the budget collapses to
`gap ≤ 1.2·10¹³·Δ/(GΩ³)` via `ℓ₁ ≥ 1` (first term) and `ℓ₁ ≤ GU⁵` + `Δ²U⁵ ≤ HΩ³`
(second term); net `111804·10¹²/Δ ≤ 1/48` from `Δ ≥ 10¹⁵G⁴U²⁰ ≥ 10⁴⁸`. -/
private theorem recon_piece_le {a d v gap ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
        + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)) :
    (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)| * gap * (ℓ₁ * v) ^ 2
      ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
  have hGpos := P.G_pos; have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hHpos := P.H_pos
  have hℓ1R : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : (0:ℝ) < ℓ₂ := lt_trans hℓ1R hℓ12
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hL3nn : (0:ℝ) ≤ 3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) := by positivity
  have hCnn := Cv2_nonneg (P := P) (S := S) (a := a) (v := v) hℓ1 hℓ12
  have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
  have hUU : (10:ℝ) ^ 33 ≤ P.U ^ 20 := hUbig.trans (le_self_pow₀ hU1 (by norm_num))
  have hGU33 : (10:ℝ) ^ 33 ≤ P.G ^ 4 * P.U ^ 20 := by
    have := mul_le_mul hG4 hUU (by norm_num) (le_trans zero_le_one hG4)
    linarith
  have hΔbig : (10:ℝ) ^ 48 ≤ S.Δ := by nlinarith [hDeW, hGU33]
  -- collapse the relaxed two-term budget:  gap ≤ 1.2·10¹³·Δ/(GΩ³)
  have hℓ1GU : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by
    have hW : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
    linarith
  have hT1 : 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
      ≤ 2 * 10 ^ 12 * (S.Δ / (P.G * S.Ω ^ 3)) := by
    rw [div_le_iff₀ (by positivity)]
    have he : 2 * 10 ^ 12 * (S.Δ / (P.G * S.Ω ^ 3)) * (P.G * S.Ω ^ 3 * ℓ₁)
        = 2 * 10 ^ 12 * S.Δ * ℓ₁ := by field_simp
    rw [he]
    nlinarith [hΔpos, hℓ1]
  have hT2 : 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6)
      ≤ 130 * 10 ^ 13 * (S.Δ / (P.G * S.Ω ^ 3)) := by
    rw [div_le_iff₀ (by positivity)]
    have he : 130 * 10 ^ 13 * (S.Δ / (P.G * S.Ω ^ 3)) * (P.H * P.G ^ 2 * S.Ω ^ 6)
        = 130 * (10 ^ 13 * S.Δ * (P.H * P.G * S.Ω ^ 3)) := by field_simp
    rw [he]
    have hkey : ℓ₁ * S.Δ ^ 2 ≤ 130 * (P.G * (P.H * S.Ω ^ 3)) := by
      calc ℓ₁ * S.Δ ^ 2 ≤ (130 * (P.G * P.U ^ 5)) * S.Δ ^ 2 :=
            mul_le_mul_of_nonneg_right hℓ1GU (sq_nonneg _)
        _ = 130 * (P.G * (S.Δ ^ 2 * P.U ^ 5)) := by ring
        _ ≤ 130 * (P.G * (P.H * S.Ω ^ 3)) := by
            have := mul_le_mul_of_nonneg_left hReg hGpos.le
            linarith
    nlinarith [mul_le_mul_of_nonneg_left hkey hΔpos.le]
  have hgap' : gap ≤ 1302 * 10 ^ 12 * (S.Δ / (P.G * S.Ω ^ 3)) := by
    have hsum := add_le_add hT1 hT2
    linarith [hgap.trans hsum]
  have hpref := pref_abs_le (P := P) (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hcoeff : (P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap
      ≤ 100254 * 10 ^ 12 / (S.Δ ^ 3 * S.Ω ^ 2) := by
    have hstep : (P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap
        ≤ (77 * (P.G * S.Ω / S.Δ ^ 4)) * (1302 * 10 ^ 12 * (S.Δ / (P.G * S.Ω ^ 3))) :=
      mul_le_mul hpref hgap' hgap0 (by positivity)
    refine hstep.trans (le_of_eq ?_)
    field_simp
    ring
  have hL3 := L3v2_le_Cv2 (P := P) (S := S) (v := v) ha0 ha_hi hℓ1 hℓ12
  calc (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * |(-4 + 10 * a / d)| * gap * (ℓ₁ * v) ^ 2
      = ((P.X * a / d ^ 5) * |(-4 + 10 * a / d)| * gap)
          * (3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)) := by ring
    _ ≤ (100254 * 10 ^ 12 / (S.Δ ^ 3 * S.Ω ^ 2))
          * (3 * ((121 / 3) * (S.Δ ^ 2 * S.Ω ^ 2)
              * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2))) :=
        mul_le_mul hcoeff (mul_le_mul_of_nonneg_left hL3 (by norm_num)) hL3nn (by positivity)
    _ = (12130734 * 10 ^ 12 / S.Δ) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
        field_simp; ring
    _ ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hCnn
        rw [div_le_div_iff₀ hΔpos (by norm_num)]; nlinarith [hΔbig]

/-- The flat-coefficient drift piece: `20(a/d)²·(Cref·(A/a)²)·(ℓ₁v)² ≤ (1/48)·Ĉv²`
(`20(a/d)² ≤ 2420Ω²/H² ≤ 1/48` from `a ≤ 11A`, `d ≥ D = HΔ`, `H ≥ Δ²U²`, `U ≥ 10³³ ≥ Ω`). -/
private theorem drift_piece_le {a d v ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
      ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
  have hHpos := P.H_pos; have hUpos := P.U_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; exact mul_pos hHpos hΔpos
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hCnn := Cv2_nonneg (P := P) (S := S) (a := a) (v := v) hℓ1 hℓ12
  -- H ≥ Δ²U²  (hReg + Ω ≤ U)
  have hΩ3U3 : S.Ω ^ 3 ≤ P.U ^ 3 := pow_le_pow_left₀ hΩpos.le hΩU 3
  have hHU2 : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * P.U ^ 3 :=
    hReg.trans (mul_le_mul_of_nonneg_left hΩ3U3 hHpos.le)
  have hH : S.Δ ^ 2 * P.U ^ 2 ≤ P.H := by nlinarith [hHU2, pow_pos hUpos 3]
  -- a² ≤ 121·Δ²Ω²,  d² ≥ H²Δ²
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  have ha2 : a ^ 2 ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haA)
      (by positivity : (0:ℝ) ≤ 11 * (S.Δ * S.Ω) + a)]
  have hd2 : P.H ^ 2 * S.Δ ^ 2 / 4 ≤ d ^ 2 := by
    have hdh : S.D / 2 ≤ d := S.D_half_of_eps hdD
    have hD2 : (S.D / 2) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hdh 2
    have : S.D ^ 2 = P.H ^ 2 * S.Δ ^ 2 := by unfold Scale.D; ring
    nlinarith [hD2, this.le, this.ge]
  -- H² ≥ Δ⁴U⁴ ≥ 10⁶⁶·Δ²Ω²  ⟹  20(a/d)² ≤ 1/48
  have hHsq : S.Δ ^ 4 * P.U ^ 4 ≤ P.H ^ 2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * P.U ^ 2) hH]
  have hU2big : (10:ℝ) ^ 66 ≤ P.U ^ 2 := by
    calc (10:ℝ) ^ 66 = ((10:ℝ) ^ 33) ^ 2 := by norm_num
      _ ≤ P.U ^ 2 := pow_le_pow_left₀ (by norm_num) hUbig 2
  have hΩ2 : S.Ω ^ 2 ≤ P.U ^ 2 := pow_le_pow_left₀ hΩpos.le hΩU 2
  have hU4O : (10:ℝ) ^ 66 * S.Ω ^ 2 ≤ P.U ^ 4 := by
    have h := mul_le_mul hU2big hΩ2 (sq_nonneg S.Ω) (by positivity : (0:ℝ) ≤ P.U ^ 2)
    nlinarith [h]
  have hΔ6 : S.Δ ^ 2 ≤ S.Δ ^ 6 := pow_le_pow_right₀ hΔ1 (by norm_num)
  have hd6 : S.Δ ^ 6 * P.U ^ 4 / 4 ≤ d ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hHsq (sq_nonneg S.Δ), hd2]
  have hd2big : (10:ℝ) ^ 65 * (S.Δ ^ 2 * S.Ω ^ 2) ≤ d ^ 2 := by
    have s1 : S.Δ ^ 2 * ((10:ℝ) ^ 66 * S.Ω ^ 2) ≤ S.Δ ^ 2 * P.U ^ 4 :=
      mul_le_mul_of_nonneg_left hU4O (sq_nonneg S.Δ)
    have s2 : S.Δ ^ 2 * P.U ^ 4 ≤ S.Δ ^ 6 * P.U ^ 4 :=
      mul_le_mul_of_nonneg_right hΔ6 (by positivity)
    have key : (10:ℝ) ^ 66 * (S.Δ ^ 2 * S.Ω ^ 2) ≤ S.Δ ^ 6 * P.U ^ 4 := by
      calc (10:ℝ) ^ 66 * (S.Δ ^ 2 * S.Ω ^ 2) = S.Δ ^ 2 * (10 ^ 66 * S.Ω ^ 2) := by ring
        _ ≤ S.Δ ^ 2 * P.U ^ 4 := s1
        _ ≤ S.Δ ^ 6 * P.U ^ 4 := s2
    linarith [key, hd6, (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2)]
  have hado : 20 * (a / d) ^ 2 ≤ 1 / 48 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [ha2, hd2big]
  calc 20 * (a / d) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2) * (ℓ₁ * v) ^ 2
      = (20 * (a / d) ^ 2) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by ring
    _ ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) :=
        mul_le_mul_of_nonneg_right hado hCnn

/-- **§5 Step-4 sharp perturbation budget**: under the large-defect cutoff `hVcut : V₂ ≤ |v|`
(killing the `p₂/d`-linear monomial via `psum_resid_le_sharp`), the deviation of `Σ_closed`
from the model parabola `Ĉ·v²` is at most `(1/16)·Ĉ·v²` — a self-contained `∝v²` bound,
with NO `|s|`-pin input (non-circular replacement of the `Step4_E_le_rho_s` route). -/
private theorem pert_le_sixteenth {a b₀ v d gap ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
        + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (hb0gap : |b₀ - b1Model P.X a d| ≤ gap) :
    |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2|
      ≤ (1 / 16) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
  have hXpos := P.X_pos; have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hUpos := P.U_pos; have hHpos := P.H_pos
  have hDpos : 0 < S.D := by unfold Scale.D; exact mul_pos hHpos hΔpos
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hℓ1R : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : (0:ℝ) < ℓ₂ := lt_trans hℓ1R hℓ12
  have h21 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  -- a ≤ d  (for `Cref_drift_le`): a ≤ 11ΔΩ ≤ Δ·H = D ≤ d  via  H ≥ Δ²U² ≥ U² ≥ 10³³Ω
  have hΩ3U3 : S.Ω ^ 3 ≤ P.U ^ 3 := pow_le_pow_left₀ hΩpos.le hΩU 3
  have hHU2 : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * P.U ^ 3 :=
    hReg.trans (mul_le_mul_of_nonneg_left hΩ3U3 hHpos.le)
  have hH : S.Δ ^ 2 * P.U ^ 2 ≤ P.H := by nlinarith [hHU2, pow_pos hUpos 3]
  have h22 : 22 * S.Ω ≤ P.H := by
    nlinarith [hH, mul_le_mul_of_nonneg_right (one_le_pow₀ hΔ1 : (1:ℝ) ≤ S.Δ ^ 2)
      (sq_nonneg P.U), mul_le_mul_of_nonneg_right hUbig hUpos.le, hΩU, hΩpos]
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  have hDd : P.H * S.Δ * (1 - 1/10 ^ 9) ≤ d := hdD
  have had : a ≤ d := by
    nlinarith [haA, hDd, mul_le_mul_of_nonneg_left h22 hΔpos.le,
      mul_pos hΩpos hΔpos]
  -- the exact three-piece decomposition
  have hid : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
      = (P.X * a / d ^ 5) * (-4 + 10 * a / d)
          * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d
              - 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2)
        + (Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂) * (ℓ₁ * v) ^ 2
        + (Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
            * (ℓ₁ * v) ^ 2 := by
    unfold Sigma_closed Cprime; ring
  -- piece 1: the sharp residual (cubic + p₂ tails), killed by `hVcut`
  have hpref := pref_abs_le (P := P) (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hresid := psum_resid_le_sharp (P := P) (S := S) (a := a)
    hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hVcut (S.D_half_of_eps hdD) hd_pos hReg hG1 hU1 hUbig hDeW
  have hA1 : |(P.X * a / d ^ 5) * (-4 + 10 * a / d)
        * (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d
            - 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2)|
      ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
    refine le_trans ?_ (resid_piece_le (P := P) (S := S) ha0 ha_hi hℓ1 hℓ12 hb0)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ P.X * a / d ^ 5)]
    exact mul_le_mul hpref hresid (abs_nonneg _) (by positivity)
  -- piece 2: slope-reconstruction drift (linearity of `Cprime` in `b₀` + the gap)
  have hKnn : (0:ℝ) ≤ (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by positivity
  have hA2 : |(Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂)
        * (ℓ₁ * v) ^ 2|
      ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
    refine le_trans ?_ (recon_piece_le (P := P) (S := S) (v := v)
      ha0 ha_hi hℓ1 hℓ12 hℓ2W hdD hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hgap0 hgap)
    have hRCeq : Cprime P.X a b₀ d ℓ₁ ℓ₂ - Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂
        = (P.X * a / d ^ 5) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (-4 + 10 * a / d)
            * (b₀ - b1Model P.X a d) := by
      unfold Cprime; ring
    rw [hRCeq, abs_mul, abs_mul, abs_mul, abs_of_nonneg hKnn,
      abs_of_nonneg (sq_nonneg (ℓ₁ * v))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb0gap (mul_nonneg hKnn (abs_nonneg _)))
      (sq_nonneg (ℓ₁ * v))
  -- piece 3: flat-coefficient drift at the smooth model
  have hA3 : |(Cprime P.X a (b1Model P.X a d) d ℓ₁ ℓ₂ - Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
        * (ℓ₁ * v) ^ 2|
      ≤ (1 / 48) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
    refine le_trans ?_ (drift_piece_le (P := P) (S := S) (v := v)
      ha0 ha_hi hℓ1 hℓ12 hdD hReg hU1 hΔ1 hΩU hUbig)
    rw [abs_mul, abs_of_nonneg (sq_nonneg (ℓ₁ * v))]
    exact mul_le_mul_of_nonneg_right
      (Cref_drift_le (P := P) (S := S) ha0 hd_pos had hℓ1R hℓ12) (sq_nonneg (ℓ₁ * v))
  -- triangle across the three pieces:  3·(1/48) = 1/16
  rw [hid]
  refine le_trans ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) ?_
  linarith [hA1, hA2, hA3]

/-- **§5 Step-4 single-point packer.**  From the near-integer pin `|Σ_closed − s| ≤ err`
(`err ≤ ¼|s|`) and the sharp non-circular budget `|Σ_closed − Ĉv²| ≤ (1/16)·Ĉv²`
(`pert_le_sixteenth`, powered by the large-defect cutoff `hVcut : V₂ ≤ |v|` instead of the
old `hρ4`/`hvpin_hi` inputs), the absorption `Ĉv² ≤ (4/3)|s|` makes `E + err ≤ ½|s|`, so the
`Vs_pin` lower pin gives the `hsq_lo` shape of `step4_fibre_branch_le` (with `n := |s|`) AND
the fibre-local v-box `|v| ≤ Vbox` (`vbox_of_pin`). -/
theorem step4_pack_sqlo
    {a b₀ v d gap err ℓ₁ ℓ₂ : ℝ} {s : ℤ} {Sc : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (_hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * ℓ₁)
        + 10 ^ 13 * ℓ₁ * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (hb0gap : |b₀ - b1Model P.X a d| ≤ gap)
    (hSc : Sc = Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
    (herr : |Sc - (s : ℝ)| ≤ err)
    (herr_small : err ≤ (1 / 4) * |(s : ℝ)|) :
    (|s| : ℝ) / 2 ≤ (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
      ∧ |v| ≤ Vbox S ℓ₁ ℓ₂ |(s : ℝ)| := by
  have hpert : |Sc - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2|
      ≤ (1 / 16) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) := by
    rw [hSc]
    exact pert_le_sixteenth (P := P) (S := S) ha0 ha_hi hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo
      hv hVcut hdD hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hgap0 hgap hb0gap
  -- absorption: Ĉv² ≤ (4/3)|s|, hence E + err ≤ (1/12 + 1/4)|s| = (1/3)|s| ≤ ½|s|
  have hsnn : (0:ℝ) ≤ |(s : ℝ)| := abs_nonneg _
  have hsabs : (s : ℝ) ≤ |(s : ℝ)| := le_abs_self _
  have hp := abs_le.mp hpert
  have he := abs_le.mp herr
  have hC2hi : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
      ≤ (4 / 3) * |(s : ℝ)| := by linarith [hp.1, he.2]
  have hreg : (1 / 16) * ((Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) + err
      ≤ (1 / 2 : ℝ) * |(s : ℝ)| := by linarith
  obtain ⟨hlo, -, -, -⟩ :=
    Vs_pin (S := S) ha0 ha_lo ha_hi hℓ1 hℓ12 hpert herr hreg
  refine ⟨?_, vbox_of_pin (S := S) ha0 ha_lo ha_hi hℓ1 hℓ12 hpert herr hreg⟩
  linarith

end Squarefree
