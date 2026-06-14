import Squarefree.Lower.UpsilonErr

/-!
# §5 Step-4 `Υ`-expansion error collapse, SHARP `v`-window form (writeup 1009, 1013)

`upsilon_err_le_sharp` is `upsilon_err_le` with the defect window sharpened from the loose
`|v| ≤ 10²⁰·ΔU⁵/Ω³` to the `v_defect_le` value `|v| ≤ 3.9·10¹⁴·ΔU⁵/Ω³`; the tolerance drops
from `10¹¹⁹·T` to `10¹¹¹·T` (`T = Δ⁴G⁵U⁴⁵/(H²Ω¹⁴)`), which is what the `step4_fiber_extract`
err-domination step (writeup 1033, the `10¹¹²·T` magnitude floor at the `10⁶⁰·V₂` cut) needs.
Constant audit (sympy): pieces 1–4 with the combined window `7.8·10¹⁴·M` and piece 5 reusing
the baked `rres_le` budget sum to `≈ 4.2·10⁹³ ≤ 10¹¹¹`.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000

theorem upsilon_err_le_sharp {a : ℝ} {b₀ v d ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 390000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hshift : d / 2 ≤ d + ℓ₁ * b₀)
    -- regime
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4
            + a ^ 3 * |ℓ₁ * b₀| ^ 3) / d ^ 7)
      + ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4
            + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3) / d ^ 7)
      + ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (10 ^ 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
            + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) / (d + ℓ₁ * b₀) ^ 7)
      + ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (|P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (120 * (ℓ₁ * b₀) ^ 2 / d ^ 7)
          + |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
      + |Rres P.X a b₀ v d ℓ₁ ℓ₂|
      ≤ 10 ^ 111 * UpsT P S := by
  -- ===== positivity =====
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  obtain ⟨hdD, hd2D⟩ := hdwin
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- master scale `M = U⁵Δ²/Ω³`
  set M : ℝ := P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 with hM_def
  have hM_nn : 0 ≤ M := by rw [hM_def]; positivity
  -- ℓ bounds
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have hℓ21W' : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ2W', hℓ1R]
  have hW_nn : 0 ≤ 130 * (P.G * P.U ^ 5) := by positivity
  -- `a ≤ 11ΔΩ ≤ M`
  have ha11 : a ≤ 11 * (S.Δ * S.Ω) := by
    have : (11 : ℝ) * S.A = 11 * (S.Δ * S.Ω) := by unfold Scale.A; ring
    linarith [ha_hi, this]
  have h11ΔΩM : 11 * (S.Δ * S.Ω) ≤ M := by
    rw [hM_def, le_div_iff₀ (by positivity)]
    have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ hΩpos.le hΩU 4
    have hUΔ : (11 : ℝ) ≤ P.U * S.Δ := by
      have : (11 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
      nlinarith [hΔ1, this, hUpos]
    have c1 : a * S.Ω ^ 3 ≤ 11 * S.Δ * S.Ω ^ 4 := by nlinarith [ha11, pow_nonneg hΩpos.le 3]
    have c2 : (11 : ℝ) * S.Δ * S.Ω ^ 4 ≤ 11 * S.Δ * P.U ^ 4 :=
      mul_le_mul_of_nonneg_left hΩ4 (by positivity)
    have c3 : (11 : ℝ) * S.Δ * P.U ^ 4 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hUΔ (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 4),
        hΔpos, hUpos]
    nlinarith [c2, c3, mul_le_mul_of_nonneg_right hΩ4 (by positivity : (0:ℝ) ≤ S.Δ)]
  have hΔΩM : S.Δ * S.Ω ≤ M := by nlinarith [h11ΔΩM, hM_nn]
  have haM : a ≤ M := by nlinarith [ha11, h11ΔΩM]
  -- the three β-magnitudes against `M`
  have hb0M : ℓ₂ * |b₀| ≤ 390000000000000 * M := by
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      have : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
      rw [this] at hb0; exact hb0
    calc ℓ₂ * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
          mul_le_mul hℓ2W' hb0' hb0nn hW_nn
      _ = 390000000000000 * M := by rw [hM_def]; field_simp; ring
  have hℓ1b0M : ℓ₁ * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right hℓ12.le hb0nn) hb0M
  have hℓ21b0M : (ℓ₂ - ℓ₁) * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith : ℓ₂ - ℓ₁ ≤ ℓ₂) hb0nn) hb0M
  have hvM : |v| ≤ 390000000000000 * M := by
    rw [hM_def]
    refine le_trans hv ?_
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith [hΔ1, hΔpos]
    have hnum : S.Δ * P.U ^ 5 ≤ P.U ^ 5 * S.Δ ^ 2 := by nlinarith [hΔsq, pow_nonneg hUpos.le 5]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity))
      (by norm_num)
  -- |ℓ₁b₀| ≤ 3e12 M
  have habs_ℓ1 : |ℓ₁ * b₀| ≤ 390000000000000 * M := by
    rw [abs_mul, abs_of_pos hℓ1R]; exact hℓ1b0M
  -- |ℓ₂b₀+v| ≤ 2e20 M
  have habs_ℓ2v : |ℓ₂ * b₀ + v| ≤ 780000000000000 * M := by
    calc |ℓ₂ * b₀ + v| ≤ |ℓ₂ * b₀| + |v| := abs_add_le _ _
      _ = ℓ₂ * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ2R]
      _ ≤ 390000000000000 * M + 390000000000000 * M := by linarith [hb0M, hvM]
      _ ≤ 780000000000000 * M := by linarith [hM_nn]
  -- |(ℓ₂-ℓ₁)b₀+v| ≤ 2e20 M
  have habs_ℓ21v : |(ℓ₂ - ℓ₁) * b₀ + v| ≤ 780000000000000 * M := by
    calc |(ℓ₂ - ℓ₁) * b₀ + v| ≤ |(ℓ₂ - ℓ₁) * b₀| + |v| := abs_add_le _ _
      _ = (ℓ₂ - ℓ₁) * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ21]
      _ ≤ 390000000000000 * M + 390000000000000 * M := by linarith [hℓ21b0M, hvM]
      _ ≤ 780000000000000 * M := by linarith [hM_nn]
  -- `a ≤ 11ΔΩ` as nonneg, and `11ΔΩ ≤ 2e20 M` (so it can be the `Amag` with `hAb`)
  have ha0' : 0 ≤ a := ha0.le
  have hAmag_le_b : 11 * (S.Δ * S.Ω) ≤ 780000000000000 * M := by nlinarith [h11ΔΩM, hM_nn]
  have hAmag_le_b' : 11 * (S.Δ * S.Ω) ≤ 390000000000000 * M := by nlinarith [h11ΔΩM, hM_nn]
  -- prefactor bounds (each ≤ W⁴)
  have hpre1 : ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ 285610000 * (P.G * P.U ^ 5) ^ 4 := by
    calc ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 2 := by
          gcongr
      _ = 285610000 * (P.G * P.U ^ 5) ^ 4 := by ring
  have hpre1nn : 0 ≤ ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hpre2 : ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ 285610000 * (P.G * P.U ^ 5) ^ 4 := by
    calc ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 2 := by
          gcongr
      _ = 285610000 * (P.G * P.U ^ 5) ^ 4 := by ring
  have hpre2nn : 0 ≤ ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hpre3 : ℓ₁ ^ 2 * ℓ₂ ^ 2 ≤ 285610000 * (P.G * P.U ^ 5) ^ 4 := by
    calc ℓ₁ ^ 2 * ℓ₂ ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 2 := by
          gcongr
      _ = 285610000 * (P.G * P.U ^ 5) ^ 4 := by ring
  have hpre3nn : 0 ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 := by positivity
  -- denominator facts
  have hHΔ7 : 0 < (P.H * S.Δ) ^ 7 := by positivity
  have hd7HΔ : (P.H * S.Δ) ^ 7 ≤ d ^ 7 := by
    have : P.H * S.Δ ≤ d := by have : S.D = P.H * S.Δ := rfl; rw [← this]; exact hdD
    exact pow_le_pow_left₀ (by positivity) this 7
  -- shift denominator: (d+ℓ₁b₀)⁷ ≥ (d/2)⁷ ≥ (HΔ/2)⁷ = (HΔ)⁷/128
  have hshift7 : (P.H * S.Δ) ^ 7 / 128 ≤ (d + ℓ₁ * b₀) ^ 7 := by
    have hdh : 0 < d / 2 := by linarith
    have h1 : (d / 2) ^ 7 ≤ (d + ℓ₁ * b₀) ^ 7 := pow_le_pow_left₀ hdh.le hshift 7
    have h2 : (P.H * S.Δ / 2) ^ 7 ≤ (d / 2) ^ 7 := by
      apply pow_le_pow_left₀ (by positivity)
      have : S.D = P.H * S.Δ := rfl; rw [← this]; linarith [hdD]
    have h3 : (P.H * S.Δ / 2) ^ 7 = (P.H * S.Δ) ^ 7 / 128 := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hshift7pos : 0 < (P.H * S.Δ) ^ 7 / 128 := by positivity
  -- the master collapse `W⁴·X·(ΔΩ)·M⁵/(HΔ)⁷ = UpsT` (in unfolded form, as `piece_le` produces)
  have hTval : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
        * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / (P.H * S.Δ) ^ 7 = UpsT P S :=
    upsilon_scale_id P S
  have hUpsT_nn : 0 ≤ UpsT P S := by unfold UpsT; positivity
  -- abbreviation for the `M`-unfolded scale block that `piece_le` produces
  have hMpow_eq : (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 = M ^ 5 := by rw [hM_def]
  -- ===========================================================
  -- PIECE 1 : term over `ℓ₁b₀`
  -- ===========================================================
  have hin1 : a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4 + a ^ 3 * |ℓ₁ * b₀| ^ 3
      ≤ (3 * 11 * 390000000000000 ^ 5) * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have := inner_le (a := a) (β := ℓ₁ * b₀) (Amag := 11 * (S.Δ * S.Ω))
      (bm := 390000000000000 * M) ha0' ha11 (abs_nonneg _) habs_ℓ1 hAmag_le_b'
    calc a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4 + a ^ 3 * |ℓ₁ * b₀| ^ 3
        ≤ 3 * (11 * (S.Δ * S.Ω)) * (390000000000000 * M) ^ 5 := this
      _ = (3 * 11 * 390000000000000 ^ 5) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  have hP1 : ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4
            + a ^ 3 * |ℓ₁ * b₀| ^ 3) / d ^ 7)
      ≤ (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)) * UpsT P S := by
    have hpc := piece_le (P := P) (S := S) (pref := ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
      (inner := a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4 + a ^ 3 * |ℓ₁ * b₀| ^ 3)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 10 ^ 4)
      (Cin := 3 * 11 * 390000000000000 ^ 5) hpre1nn hpre1
      (by positivity) hin1 hHΔ7 hd7HΔ (by norm_num) (by positivity)
    rw [hTval] at hpc
    calc ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
          * (10 ^ 4 * P.X * (a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4
              + a ^ 3 * |ℓ₁ * b₀| ^ 3) / d ^ 7)
        ≤ 285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5) * UpsT P S := hpc
      _ = (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 2 : term over `ℓ₂b₀+v`
  -- ===========================================================
  have hin2 : a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4 + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3
      ≤ (3 * 11 * (780000000000000) ^ 5) * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have := inner_le (a := a) (β := ℓ₂ * b₀ + v) (Amag := 11 * (S.Δ * S.Ω))
      (bm := 780000000000000 * M) ha0' ha11 (abs_nonneg _) habs_ℓ2v hAmag_le_b
    calc a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4 + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3
        ≤ 3 * (11 * (S.Δ * S.Ω)) * (780000000000000 * M) ^ 5 := this
      _ = (3 * 11 * (780000000000000) ^ 5) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  have hP2 : ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4
            + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3) / d ^ 7)
      ≤ (285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5)) * UpsT P S := by
    have hpc := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
      (inner := a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4 + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 10 ^ 4)
      (Cin := 3 * 11 * (780000000000000) ^ 5) hpre2nn hpre2
      (by positivity) hin2 hHΔ7 hd7HΔ (by norm_num) (by positivity)
    rw [hTval] at hpc
    calc ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
          * (10 ^ 4 * P.X * (a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4
              + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3) / d ^ 7)
        ≤ 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * UpsT P S := hpc
      _ = (285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5)) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 3 : term over `(ℓ₂-ℓ₁)b₀+v`, denominator `(d+ℓ₁b₀)⁷ ≥ (HΔ)⁷/128`
  -- ===========================================================
  have hTval128 : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
        * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / ((P.H * S.Δ) ^ 7 / 128) = 128 * UpsT P S := by
    have heq : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / ((P.H * S.Δ) ^ 7 / 128)
        = 128 * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
            * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / (P.H * S.Δ) ^ 7) := by
      rw [div_div_eq_mul_div]; ring
    rw [heq, hTval]
  have hin3 : a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
        + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3
      ≤ (3 * 11 * (780000000000000) ^ 5) * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have := inner_le (a := a) (β := (ℓ₂ - ℓ₁) * b₀ + v) (Amag := 11 * (S.Δ * S.Ω))
      (bm := 780000000000000 * M) ha0' ha11 (abs_nonneg _) habs_ℓ21v hAmag_le_b
    calc a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
          + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3
        ≤ 3 * (11 * (S.Δ * S.Ω)) * (780000000000000 * M) ^ 5 := this
      _ = (3 * 11 * (780000000000000) ^ 5) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  have hP3 : ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (10 ^ 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
            + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) / (d + ℓ₁ * b₀) ^ 7)
      ≤ (285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * 128) * UpsT P S := by
    have hpc := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * ℓ₂ ^ 2)
      (inner := a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
        + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
      (den := (d + ℓ₁ * b₀) ^ 7) (denlo := (P.H * S.Δ) ^ 7 / 128) (c := 10 ^ 4)
      (Cin := 3 * 11 * (780000000000000) ^ 5) hpre3nn hpre3
      (by positivity) hin3 hshift7pos hshift7 (by norm_num) (by positivity)
    rw [hTval128] at hpc
    calc ℓ₁ ^ 2 * ℓ₂ ^ 2
          * (10 ^ 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
              + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) / (d + ℓ₁ * b₀) ^ 7)
        ≤ 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * (128 * UpsT P S) := hpc
      _ = (285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * 128) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 4 : base-point shift correction (two sub-terms)
  -- ===========================================================
  -- rewrite the two abs values into explicit nonnegative products
  have habs4a : |P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)|
      = 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) := by
    rw [abs_mul, abs_of_pos hXpos]
    rw [show -4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3
          = (-(4 * a)) * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3 by ring, abs_mul, abs_neg,
        abs_of_pos (by positivity : (0:ℝ) < 4 * a), abs_pow]
    ring
  have habs4b : |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
        + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)|
      ≤ P.X * (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) := by
    rw [abs_mul, abs_of_pos hXpos]
    refine mul_le_mul_of_nonneg_left ?_ hXpos.le
    calc |10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4 + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3|
        ≤ |10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4| + |10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3| :=
          abs_add_le _ _
      _ = 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 := by
          have e1 : |10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4|
              = 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 := by
            rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 10 * a)]
          have e2 : |10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3|
              = 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 := by
            rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 10 * a ^ 2)]
          rw [e1, e2]
  -- sub-4a inner bound
  have hin4a : a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2
      ≤ (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2) * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have hsq : (ℓ₁ * b₀) ^ 2 = |ℓ₁ * b₀| ^ 2 := (sq_abs _).symm
    rw [hsq]
    have hM3 : |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 ≤ (780000000000000 * M) ^ 3 := by gcongr
    have hM2 : |ℓ₁ * b₀| ^ 2 ≤ (390000000000000 * M) ^ 2 := by gcongr
    calc a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀| ^ 2
        ≤ 11 * (S.Δ * S.Ω) * (780000000000000 * M) ^ 3 * (390000000000000 * M) ^ 2 := by
          apply mul_le_mul (mul_le_mul ha11 hM3 (by positivity) (by positivity)) hM2
            (by positivity) (by positivity)
      _ = (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  -- sub-4b inner bound
  have hin4b : (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
        * |ℓ₁ * b₀|
      ≤ (10 * 11 * (780000000000000) ^ 4 * 390000000000000
          + 10 * 121 * (780000000000000) ^ 3 * 390000000000000) * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have hM4 : |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 ≤ (780000000000000 * M) ^ 4 := by gcongr
    have hM3 : |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 ≤ (780000000000000 * M) ^ 3 := by gcongr
    have ha2 : a ^ 2 ≤ (11 * (S.Δ * S.Ω)) ^ 2 := by
      have := pow_le_pow_left₀ ha0' ha11 2; exact this
    -- term A: 10a|β|⁴|ℓ₁b₀|
    have hA : 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 * |ℓ₁ * b₀|
        ≤ (10 * 11 * (780000000000000) ^ 4 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by
      calc 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 * |ℓ₁ * b₀|
          ≤ 10 * (11 * (S.Δ * S.Ω)) * (780000000000000 * M) ^ 4 * (390000000000000 * M) := by
            gcongr
        _ = (10 * 11 * (780000000000000) ^ 4 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by ring
    -- term B: 10a²|β|³|ℓ₁b₀| ≤ … using (ΔΩ)² ≤ (ΔΩ)·M
    have hB : 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀|
        ≤ (10 * 121 * (780000000000000) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by
      have hΔΩsq : (S.Δ * S.Ω) ^ 2 ≤ (S.Δ * S.Ω) * M :=
        by nlinarith [hΔΩM, mul_pos hΔpos hΩpos]
      calc 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀|
          ≤ 10 * (11 * (S.Δ * S.Ω)) ^ 2 * (780000000000000 * M) ^ 3 * (390000000000000 * M) := by
            gcongr
        _ = (10 * 121 * (780000000000000) ^ 3 * 390000000000000) * ((S.Δ * S.Ω) ^ 2) * M ^ 4 := by ring
        _ ≤ (10 * 121 * (780000000000000) ^ 3 * 390000000000000) * ((S.Δ * S.Ω) * M) * M ^ 4 := by
            gcongr
        _ = (10 * 121 * (780000000000000) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by ring
    calc (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) * |ℓ₁ * b₀|
        = 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 * |ℓ₁ * b₀|
          + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀| := by ring
      _ ≤ (10 * 11 * (780000000000000) ^ 4 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5
          + (10 * 121 * (780000000000000) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by
            linarith [hA, hB]
      _ = (10 * 11 * (780000000000000) ^ 4 * 390000000000000
            + 10 * 121 * (780000000000000) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  -- assemble piece 4
  have hP4 : ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (|P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (120 * (ℓ₁ * b₀) ^ 2 / d ^ 7)
          + |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
      ≤ (285610000 * 480 * (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2)
          + 285610000 * 64 * (10 * 11 * (780000000000000) ^ 4 * 390000000000000
              + 10 * 121 * (780000000000000) ^ 3 * 390000000000000)) * UpsT P S := by
    -- sub-4a as a `piece_le`
    have hpc4a := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * ℓ₂ ^ 2)
      (inner := a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 480)
      (Cin := 11 * (780000000000000) ^ 3 * 390000000000000 ^ 2) hpre3nn hpre3
      (by positivity) hin4a hHΔ7 hd7HΔ (by norm_num) (by positivity)
    have hpc4b := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * ℓ₂ ^ 2)
      (inner := (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
        * |ℓ₁ * b₀|)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 64)
      (Cin := 10 * 11 * (780000000000000) ^ 4 * 390000000000000
          + 10 * 121 * (780000000000000) ^ 3 * 390000000000000) hpre3nn hpre3
      (by positivity) hin4b hHΔ7 hd7HΔ (by norm_num) (by positivity)
    rw [hTval] at hpc4a hpc4b
    -- rewrite the two abs sub-terms of the goal
    have hd7pos : (0:ℝ) < d ^ 7 := by positivity
    -- sub-4a literal = pref * (480 X inner4a / d⁷)
    have hsub4a : ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)|
          * (120 * (ℓ₁ * b₀) ^ 2 / d ^ 7))
        = ℓ₁ ^ 2 * ℓ₂ ^ 2 * (480 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2) / d ^ 7) := by
      rw [habs4a]; ring
    -- sub-4b literal ≤ pref * (64 X inner4b / d⁷)
    have hsub4b : ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
            + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
        ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 * (64 * P.X
            * ((10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
                * |ℓ₁ * b₀|) / d ^ 7) := by
      have hfac : |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
            + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7)
          ≤ (P.X * (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3))
            * (64 * |ℓ₁ * b₀| / d ^ 7) := by
        gcongr
      calc ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
          ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 * ((P.X * (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
              + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)) * (64 * |ℓ₁ * b₀| / d ^ 7)) := by
            exact mul_le_mul_of_nonneg_left hfac hpre3nn
        _ = ℓ₁ ^ 2 * ℓ₂ ^ 2 * (64 * P.X
              * ((10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
                  * |ℓ₁ * b₀|) / d ^ 7) := by ring
    rw [mul_add, hsub4a]
    calc ℓ₁ ^ 2 * ℓ₂ ^ 2 * (480 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2) / d ^ 7)
          + ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
        ≤ 285610000 * 480 * (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2) * UpsT P S
          + 285610000 * 64 * (10 * 11 * (780000000000000) ^ 4 * 390000000000000
              + 10 * 121 * (780000000000000) ^ 3 * 390000000000000) * UpsT P S := by
          exact add_le_add hpc4a (le_trans hsub4b hpc4b)
      _ = (285610000 * 480 * (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2)
            + 285610000 * 64 * (10 * 11 * (780000000000000) ^ 4 * 390000000000000
                + 10 * 121 * (780000000000000) ^ 3 * 390000000000000)) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 5 : the genuine residual `|Rres|`  (factored into `rres_le`)
  -- ===========================================================
  set Csum : ℝ := 8 * (390000000000000 ^ 3 * (2 * 10 ^ 20))
      + 12 * (390000000000000 ^ 2 * (2 * 10 ^ 20) ^ 2)
      + 10 * (390000000000000 * (2 * 10 ^ 20) ^ 3)
      + 3 * ((2 * 10 ^ 20) ^ 4) with hCsumdef
  have hvM2 : |v| ≤ 2 * 10 ^ 20 * M := by nlinarith [hvM, hM_nn]
  have hP5 : |Rres P.X a b₀ v d ℓ₁ ℓ₂| ≤ 25 * 121 * 285610000 * Csum * UpsT P S :=
    rres_le ha0 ha11 hℓ1R hℓ12 hℓ2W' hd_pos hb0M hvM2 hΔΩM hd7HΔ hM_def
  -- ===========================================================
  -- FINAL ASSEMBLY : sum the five piece bounds
  -- ===========================================================
  have hconst : (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)
      + 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5)
      + 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * 128
      + (285610000 * 480 * (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2)
          + 285610000 * 64 * (10 * 11 * (780000000000000) ^ 4 * 390000000000000
              + 10 * 121 * (780000000000000) ^ 3 * 390000000000000))
      + 25 * 121 * 285610000 * Csum : ℝ) ≤ 10 ^ 111 := by
    rw [hCsumdef]; norm_num
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hP1 hP2) hP3) hP4) hP5
  refine le_trans hsum ?_
  rw [show (10:ℝ) ^ 111 * UpsT P S = 10 ^ 111 * UpsT P S by ring]
  calc 285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5) * UpsT P S
        + 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * UpsT P S
        + 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * 128 * UpsT P S
        + (285610000 * 480 * (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2)
            + 285610000 * 64 * (10 * 11 * (780000000000000) ^ 4 * 390000000000000
                + 10 * 121 * (780000000000000) ^ 3 * 390000000000000)) * UpsT P S
        + 25 * 121 * 285610000 * Csum * UpsT P S
      = (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)
          + 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5)
          + 285610000 * 10 ^ 4 * (3 * 11 * (780000000000000) ^ 5) * 128
          + (285610000 * 480 * (11 * (780000000000000) ^ 3 * 390000000000000 ^ 2)
              + 285610000 * 64 * (10 * 11 * (780000000000000) ^ 4 * 390000000000000
                  + 10 * 121 * (780000000000000) ^ 3 * 390000000000000))
          + 25 * 121 * 285610000 * Csum) * UpsT P S := by ring
    _ ≤ 10 ^ 111 * UpsT P S := by
        exact mul_le_mul_of_nonneg_right hconst hUpsT_nn

end Squarefree
