import Squarefree.Bracket.Sec7FInverse

/-!
# §7 dBreve scale bounds

Upstream grade 3/4 inverse-derivative scale bounds for the §7 residual layer.
-/

namespace Squarefree

set_option maxHeartbeats 800000

private theorem sec7_phase_inv3_scale_base {P : Globals} (S : Scale P) :
    S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) = S.D := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.F Scale.D Scale.A
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_phase_inv4_scale_base {P : Globals} (S : Scale P) :
    S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) = S.D := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.F Scale.D Scale.A
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem dBreve_deriv3_abs_base_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d) (hd_hi : d ≤ 30 * S.D) :
    (1 / 10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) ≤
        |dBreve''' P.X a (Ffun P.X a d)| ∧
      |dBreve''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) := by
  have hXpos : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hd_lo
  have hAleD : S.A ≤ S.D / 10 := by linarith
  have hAle_d : S.A ≤ 2 * d := by linarith
  have ha_le_18d : a ≤ 18 * d := by linarith
  have ha_le_2D : a ≤ 2 * S.D := by linarith
  have hda_lo : d ≤ d + a := by linarith
  have hda_hi : d + a ≤ 32 * S.D := by linarith
  set Q : ℝ := a ^ 2 + 3 * a * d + 3 * d ^ 2 with hQ
  set Poly : ℝ := 5 * a ^ 6 + 40 * a ^ 5 * d + 140 * a ^ 4 * d ^ 2
      + 284 * a ^ 3 * d ^ 3 + 352 * a ^ 2 * d ^ 4
      + 252 * a * d ^ 5 + 84 * d ^ 6 with hPoly
  have hQ_le : Q ≤ 381 * d ^ 2 := by
    rw [hQ]
    nlinarith only [ha_le_18d, ha0.le, hd0.le, sq_nonneg (a - 18 * d)]
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ]
    positivity
  have hQ_ge : 3 * d ^ 2 ≤ Q := by
    rw [hQ]
    nlinarith only [sq_nonneg a, mul_nonneg ha0.le hd0.le]
  have hpoly_lo : 84 * d ^ 6 ≤ Poly := by
    rw [hPoly]
    have h1 : 0 ≤ 5 * a ^ 6 := by positivity
    have h2 : 0 ≤ 40 * a ^ 5 * d := by positivity
    have h3 : 0 ≤ 140 * a ^ 4 * d ^ 2 := by positivity
    have h4 : 0 ≤ 284 * a ^ 3 * d ^ 3 := by positivity
    have h5 : 0 ≤ 352 * a ^ 2 * d ^ 4 := by positivity
    have h6 : 0 ≤ 252 * a * d ^ 5 := by positivity
    nlinarith only [h1, h2, h3, h4, h5, h6]
  have hterm1 : 5 * a ^ 6 ≤ 5 * (2 * S.D) ^ 6 := by gcongr
  have hterm2 : 40 * a ^ 5 * d ≤ 40 * (2 * S.D) ^ 5 * (30 * S.D) := by gcongr
  have hterm3 : 140 * a ^ 4 * d ^ 2 ≤ 140 * (2 * S.D) ^ 4 * (30 * S.D) ^ 2 := by gcongr
  have hterm4 : 284 * a ^ 3 * d ^ 3 ≤ 284 * (2 * S.D) ^ 3 * (30 * S.D) ^ 3 := by gcongr
  have hterm5 : 352 * a ^ 2 * d ^ 4 ≤ 352 * (2 * S.D) ^ 2 * (30 * S.D) ^ 4 := by gcongr
  have hterm6 : 252 * a * d ^ 5 ≤ 252 * (2 * S.D) * (30 * S.D) ^ 5 := by gcongr
  have hterm7 : 84 * d ^ 6 ≤ 84 * (30 * S.D) ^ 6 := by gcongr
  have hpoly_hi : Poly ≤ 74687078720 * S.D ^ 6 := by
    rw [hPoly]
    nlinarith only [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7]
  have hda7 : d ^ 7 ≤ (d + a) ^ 7 := pow_le_pow_left₀ hd0.le hda_lo 7
  have hnum_lo : 3 * 84 * d ^ 20 ≤ 3 * d ^ 7 * (d + a) ^ 7 * Poly := by
    have hprod : d ^ 7 * d ^ 7 * (84 * d ^ 6) ≤ d ^ 7 * (d + a) ^ 7 * Poly := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hda7 (by positivity)) hpoly_lo
        (by positivity) (by positivity)
    nlinarith only [hprod, hd0]
  have hQ5_hi : Q ^ 5 ≤ (381 * d ^ 2) ^ 5 := pow_le_pow_left₀ hQ_nonneg hQ_le 5
  have hden_hi : 8 * P.X ^ 3 * a ^ 3 * Q ^ 5 ≤
      8 * P.X ^ 3 * (11 * S.A) ^ 3 * (381 * d ^ 2) ^ 5 := by
    gcongr
  have hden_pos : 0 < 8 * P.X ^ 3 * a ^ 3 * Q ^ 5 := by
    rw [hQ]
    positivity
  have hden_hi_pos : 0 < 8 * P.X ^ 3 * (11 * S.A) ^ 3 * (381 * d ^ 2) ^ 5 := by
    positivity
  have hloc_lo :
      3 * 84 * d ^ 20 / (8 * P.X ^ 3 * (11 * S.A) ^ 3 * (381 * d ^ 2) ^ 5) ≤
        3 * d ^ 7 * (d + a) ^ 7 * Poly / (8 * P.X ^ 3 * a ^ 3 * Q ^ 5) := by
    rw [div_le_div_iff₀ hden_hi_pos hden_pos]
    have hmul := mul_le_mul hnum_lo hden_hi
      (by positivity : 0 ≤ 8 * P.X ^ 3 * a ^ 3 * Q ^ 5)
      (by positivity : 0 ≤ 3 * d ^ 7 * (d + a) ^ 7 * Poly)
    nlinarith only [hmul]
  have hD10 : S.D ^ 10 ≤ 16 ^ 10 * d ^ 10 := by
    have hpow : (S.D / 16) ^ 10 ≤ d ^ 10 :=
      pow_le_pow_left₀ (by positivity) hd_lo 10
    nlinarith only [hpow, hDpos]
  have hbase_d_lo :
      (3 * 84 : ℝ) / (8 * 11 ^ 3 * 381 ^ 5 * 16 ^ 10) *
          (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) ≤
        (3 * 84 : ℝ) / (8 * 11 ^ 3 * 381 ^ 5) *
          (d ^ 10 / (P.X ^ 3 * S.A ^ 3)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos]
    nlinarith only [hD10,
      mul_le_mul_of_nonneg_left hD10 (show (0:ℝ) ≤ P.X ^ 3 * S.A ^ 3 by positivity)]
  have hbase_eq_lo :
      (3 * 84 : ℝ) / (8 * 11 ^ 3 * 381 ^ 5) *
          (d ^ 10 / (P.X ^ 3 * S.A ^ 3)) =
        3 * 84 * d ^ 20 / (8 * P.X ^ 3 * (11 * S.A) ^ 3 * (381 * d ^ 2) ^ 5) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
  have hbase_lo :
      (1 / 10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) ≤
        3 * d ^ 7 * (d + a) ^ 7 * Poly / (8 * P.X ^ 3 * a ^ 3 * Q ^ 5) := by
    refine le_trans ?_ hloc_lo
    refine le_trans ?_ (by simpa [hbase_eq_lo] using hbase_d_lo)
    have hc : (1 / 10 ^ 80 : ℝ) ≤
        (3 * 84) / (8 * 11 ^ 3 * 381 ^ 5 * 16 ^ 10) := by
      norm_num
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hd7_hi : d ^ 7 ≤ (30 * S.D) ^ 7 := pow_le_pow_left₀ hd0.le hd_hi 7
  have hda7_hi : (d + a) ^ 7 ≤ (32 * S.D) ^ 7 :=
    pow_le_pow_left₀ (by positivity) hda_hi 7
  have hnum_hi : 3 * d ^ 7 * (d + a) ^ 7 * Poly ≤
      3 * (30 * S.D) ^ 7 * (32 * S.D) ^ 7 * (74687078720 * S.D ^ 6) := by
    have hprod1 : d ^ 7 * (d + a) ^ 7 ≤ (30 * S.D) ^ 7 * (32 * S.D) ^ 7 :=
      mul_le_mul hd7_hi hda7_hi (by positivity) (by positivity)
    have hprod2 := mul_le_mul hprod1 hpoly_hi (by positivity)
      (by positivity : 0 ≤ (30 * S.D) ^ 7 * (32 * S.D) ^ 7)
    nlinarith only [hprod2]
  have hQ5_lo : (3 * d ^ 2) ^ 5 ≤ Q ^ 5 := pow_le_pow_left₀ (by positivity) hQ_ge 5
  have hden_lo : 8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5 ≤
      8 * P.X ^ 3 * a ^ 3 * Q ^ 5 := by
    gcongr
  have hden_lo_pos : 0 < 8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5 := by
    positivity
  have hloc_hi :
      3 * d ^ 7 * (d + a) ^ 7 * Poly / (8 * P.X ^ 3 * a ^ 3 * Q ^ 5) ≤
        3 * (30 * S.D) ^ 7 * (32 * S.D) ^ 7 * (74687078720 * S.D ^ 6) /
          (8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5) := by
    rw [div_le_div_iff₀ hden_pos hden_lo_pos]
    have hmul := mul_le_mul hnum_hi hden_lo
      (by positivity : 0 ≤ 8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5)
      (by positivity : 0 ≤ 3 * (30 * S.D) ^ 7 * (32 * S.D) ^ 7 *
        (74687078720 * S.D ^ 6))
    nlinarith only [hmul]
  have hbase_hi :
      3 * (30 * S.D) ^ 7 * (32 * S.D) ^ 7 * (74687078720 * S.D ^ 6) /
          (8 * P.X ^ 3 * (S.A / 5) ^ 3 * (3 * d ^ 2) ^ 5) ≤
        (10 ^ 80 : ℝ) * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
    have hconst : (30 : ℝ) ^ 7 * 32 ^ 7 * 74687078720 * 5 ^ 3 * 16 ^ 10 ≤
        3 ^ 4 * 8 * 10 ^ 80 := by
      norm_num
    have hright : (30 : ℝ) ^ 7 * S.D ^ 10 * 32 ^ 7 * 74687078720 * 5 ^ 3 ≤
        3 ^ 4 * 8 * d ^ 10 * 10 ^ 80 := by
      calc (30 : ℝ) ^ 7 * S.D ^ 10 * 32 ^ 7 * 74687078720 * 5 ^ 3
          ≤ (30 : ℝ) ^ 7 * (16 ^ 10 * d ^ 10) * 32 ^ 7 * 74687078720 * 5 ^ 3 := by
            gcongr
        _ = ((30 : ℝ) ^ 7 * 32 ^ 7 * 74687078720 * 5 ^ 3 * 16 ^ 10) *
              d ^ 10 := by ring
        _ ≤ (3 ^ 4 * 8 * 10 ^ 80) * d ^ 10 := by
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 3 ^ 4 * 8 * d ^ 10 * 10 ^ 80 := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hright
  rw [dBreve_deriv3_abs_factor_image P.X_pos ha0 hd0]
  rw [hQ, hPoly] at hbase_lo hloc_hi
  exact ⟨hbase_lo, le_trans hloc_hi hbase_hi⟩

/-- Grade-3 inverse scale packaging: `F³ |dBreve'''| ≍ HΔ` on the wide image window. -/
theorem dBreve_deriv3_scale_wide_image_construct {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 80 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 80 : ℝ) * (P.H * S.Δ) := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  obtain ⟨hlo, hhi⟩ :=
    dBreve_deriv3_abs_base_wide (P := P) (S := S) (a := a) (d := d)
      hAD ha_lo ha_hi (by linarith) (by linarith)
  constructor
  · calc (1 / 10 ^ 80 : ℝ) * (P.H * S.Δ)
        = (1 / 10 ^ 80 : ℝ) * S.D := rfl
      _ = S.F ^ 3 * ((1 / 10 ^ 80 : ℝ) *
            (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) := by
            rw [show S.F ^ 3 * ((1 / 10 ^ 80 : ℝ) *
                  (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) =
                (1 / 10 ^ 80 : ℝ) *
                  (S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) by ring,
              sec7_phase_inv3_scale_base S]
      _ ≤ S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)|
        ≤ S.F ^ 3 * ((10 ^ 80 : ℝ) *
            (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = (10 ^ 80 : ℝ) * (P.H * S.Δ) := by
            rw [show S.F ^ 3 * ((10 ^ 80 : ℝ) *
                  (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) =
                (10 ^ 80 : ℝ) *
                  (S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) by ring,
              sec7_phase_inv3_scale_base S]
            rfl

/-- Grade-3 inverse scale packaging on the §7 image window. -/
theorem dBreve_deriv3_scale_sec7_image {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d) (hd_hi : d ≤ 30 * S.D) :
    (1 / 10 ^ 80 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 80 : ℝ) * (P.H * S.Δ) := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  obtain ⟨hlo, hhi⟩ :=
    dBreve_deriv3_abs_base_wide (P := P) (S := S) (a := a) (d := d)
      hAD ha_lo ha_hi hd_lo hd_hi
  constructor
  · calc (1 / 10 ^ 80 : ℝ) * (P.H * S.Δ)
        = (1 / 10 ^ 80 : ℝ) * S.D := rfl
      _ = S.F ^ 3 * ((1 / 10 ^ 80 : ℝ) *
            (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) := by
            rw [show S.F ^ 3 * ((1 / 10 ^ 80 : ℝ) *
                  (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) =
                (1 / 10 ^ 80 : ℝ) *
                  (S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) by ring,
              sec7_phase_inv3_scale_base S]
      _ ≤ S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)| :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d)|
        ≤ S.F ^ 3 * ((10 ^ 80 : ℝ) *
            (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = (10 ^ 80 : ℝ) * (P.H * S.Δ) := by
            rw [show S.F ^ 3 * ((10 ^ 80 : ℝ) *
                  (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) =
                (10 ^ 80 : ℝ) *
                  (S.F ^ 3 * (S.D ^ 10 / (P.X ^ 3 * S.A ^ 3))) by ring,
              sec7_phase_inv3_scale_base S]
            rfl

private theorem dBreve_deriv4_abs_base_wide {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d) (hd_hi : d ≤ 30 * S.D) :
    (1 / 10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) ≤
        |dBreve'''' P.X a (Ffun P.X a d)| ∧
      |dBreve'''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) := by
  have hXpos : 0 < P.X := P.X_pos
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hd_lo
  have hAleD : S.A ≤ S.D / 10 := by linarith
  have hAle_d : S.A ≤ 2 * d := by linarith
  have ha_le_18d : a ≤ 18 * d := by linarith
  have ha_le_2D : a ≤ 2 * S.D := by linarith
  have hda_lo : d ≤ d + a := by linarith
  have hda_hi : d + a ≤ 32 * S.D := by linarith
  have had2_lo : 2 * d ≤ a + 2 * d := by linarith
  have had2_hi : a + 2 * d ≤ 62 * S.D := by linarith
  set Q : ℝ := a ^ 2 + 3 * a * d + 3 * d ^ 2 with hQ
  set Poly : ℝ := 7 * a ^ 8 + 70 * a ^ 7 * d + 322 * a ^ 6 * d ^ 2
      + 912 * a ^ 5 * d ^ 3 + 1728 * a ^ 4 * d ^ 4
      + 2232 * a ^ 3 * d ^ 5 + 1920 * a ^ 2 * d ^ 6
      + 1008 * a * d ^ 7 + 252 * d ^ 8 with hPoly
  have hQ_le : Q ≤ 381 * d ^ 2 := by
    rw [hQ]
    nlinarith only [ha_le_18d, ha0.le, hd0.le, sq_nonneg (a - 18 * d)]
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ]
    positivity
  have hQ_ge : 3 * d ^ 2 ≤ Q := by
    rw [hQ]
    nlinarith only [sq_nonneg a, mul_nonneg ha0.le hd0.le]
  have hpoly_lo : 252 * d ^ 8 ≤ Poly := by
    rw [hPoly]
    have h1 : 0 ≤ 7 * a ^ 8 := by positivity
    have h2 : 0 ≤ 70 * a ^ 7 * d := by positivity
    have h3 : 0 ≤ 322 * a ^ 6 * d ^ 2 := by positivity
    have h4 : 0 ≤ 912 * a ^ 5 * d ^ 3 := by positivity
    have h5 : 0 ≤ 1728 * a ^ 4 * d ^ 4 := by positivity
    have h6 : 0 ≤ 2232 * a ^ 3 * d ^ 5 := by positivity
    have h7 : 0 ≤ 1920 * a ^ 2 * d ^ 6 := by positivity
    have h8 : 0 ≤ 1008 * a * d ^ 7 := by positivity
    nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8]
  have hterm1 : 7 * a ^ 8 ≤ 7 * (2 * S.D) ^ 8 := by gcongr
  have hterm2 : 70 * a ^ 7 * d ≤ 70 * (2 * S.D) ^ 7 * (30 * S.D) := by gcongr
  have hterm3 : 322 * a ^ 6 * d ^ 2 ≤ 322 * (2 * S.D) ^ 6 * (30 * S.D) ^ 2 := by gcongr
  have hterm4 : 912 * a ^ 5 * d ^ 3 ≤ 912 * (2 * S.D) ^ 5 * (30 * S.D) ^ 3 := by gcongr
  have hterm5 : 1728 * a ^ 4 * d ^ 4 ≤ 1728 * (2 * S.D) ^ 4 * (30 * S.D) ^ 4 := by gcongr
  have hterm6 : 2232 * a ^ 3 * d ^ 5 ≤ 2232 * (2 * S.D) ^ 3 * (30 * S.D) ^ 5 := by gcongr
  have hterm7 : 1920 * a ^ 2 * d ^ 6 ≤ 1920 * (2 * S.D) ^ 2 * (30 * S.D) ^ 6 := by gcongr
  have hterm8 : 1008 * a * d ^ 7 ≤ 1008 * (2 * S.D) * (30 * S.D) ^ 7 := by gcongr
  have hterm9 : 252 * d ^ 8 ≤ 252 * (30 * S.D) ^ 8 := by gcongr
  have hpoly_hi : Poly ≤ 215482942465792 * S.D ^ 8 := by
    rw [hPoly]
    nlinarith only [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8, hterm9]
  have hda9 : d ^ 9 ≤ (d + a) ^ 9 := pow_le_pow_left₀ hd0.le hda_lo 9
  have hnum_lo : 15 * 2 * 252 * d ^ 27 ≤
      15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly := by
    have hprod1 : d ^ 9 * d ^ 9 ≤ d ^ 9 * (d + a) ^ 9 :=
      mul_le_mul_of_nonneg_left hda9 (by positivity)
    have hprod2 : d ^ 9 * d ^ 9 * (2 * d) ≤
        d ^ 9 * (d + a) ^ 9 * (a + 2 * d) :=
      mul_le_mul hprod1 had2_lo (by positivity) (by positivity)
    have hprod3 : d ^ 9 * d ^ 9 * (2 * d) * (252 * d ^ 8) ≤
        d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly :=
      mul_le_mul hprod2 hpoly_lo (by positivity) (by positivity)
    nlinarith only [hprod3, hd0]
  have hQ7_hi : Q ^ 7 ≤ (381 * d ^ 2) ^ 7 := pow_le_pow_left₀ hQ_nonneg hQ_le 7
  have hden_hi : 16 * P.X ^ 4 * a ^ 4 * Q ^ 7 ≤
      16 * P.X ^ 4 * (11 * S.A) ^ 4 * (381 * d ^ 2) ^ 7 := by
    gcongr
  have hden_pos : 0 < 16 * P.X ^ 4 * a ^ 4 * Q ^ 7 := by
    rw [hQ]
    positivity
  have hden_hi_pos : 0 < 16 * P.X ^ 4 * (11 * S.A) ^ 4 * (381 * d ^ 2) ^ 7 := by
    positivity
  have hloc_lo :
      15 * 2 * 252 * d ^ 27 /
          (16 * P.X ^ 4 * (11 * S.A) ^ 4 * (381 * d ^ 2) ^ 7) ≤
        15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly /
          (16 * P.X ^ 4 * a ^ 4 * Q ^ 7) := by
    rw [div_le_div_iff₀ hden_hi_pos hden_pos]
    have hmul := mul_le_mul hnum_lo hden_hi
      (by positivity : 0 ≤ 16 * P.X ^ 4 * a ^ 4 * Q ^ 7)
      (by positivity : 0 ≤ 15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly)
    nlinarith only [hmul]
  have hD13 : S.D ^ 13 ≤ 16 ^ 13 * d ^ 13 := by
    have hpow : (S.D / 16) ^ 13 ≤ d ^ 13 :=
      pow_le_pow_left₀ (by positivity) hd_lo 13
    nlinarith only [hpow, hDpos]
  have hbase_d_lo :
      (15 * 2 * 252 : ℝ) / (16 * 11 ^ 4 * 381 ^ 7 * 16 ^ 13) *
          (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) ≤
        (15 * 2 * 252 : ℝ) / (16 * 11 ^ 4 * 381 ^ 7) *
          (d ^ 13 / (P.X ^ 4 * S.A ^ 4)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos]
    nlinarith only [hD13,
      mul_le_mul_of_nonneg_left hD13 (show (0:ℝ) ≤ P.X ^ 4 * S.A ^ 4 by positivity)]
  have hbase_eq_lo :
      (15 * 2 * 252 : ℝ) / (16 * 11 ^ 4 * 381 ^ 7) *
          (d ^ 13 / (P.X ^ 4 * S.A ^ 4)) =
        15 * 2 * 252 * d ^ 27 /
          (16 * P.X ^ 4 * (11 * S.A) ^ 4 * (381 * d ^ 2) ^ 7) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
  have hbase_lo :
      (1 / 10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) ≤
        15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly /
          (16 * P.X ^ 4 * a ^ 4 * Q ^ 7) := by
    refine le_trans ?_ hloc_lo
    refine le_trans ?_ (by simpa [hbase_eq_lo] using hbase_d_lo)
    have hc : (1 / 10 ^ 100 : ℝ) ≤
        (15 * 2 * 252) / (16 * 11 ^ 4 * 381 ^ 7 * 16 ^ 13) := by
      norm_num
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hd9_hi : d ^ 9 ≤ (30 * S.D) ^ 9 := pow_le_pow_left₀ hd0.le hd_hi 9
  have hda9_hi : (d + a) ^ 9 ≤ (32 * S.D) ^ 9 :=
    pow_le_pow_left₀ (by positivity) hda_hi 9
  have hnum_hi : 15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly ≤
      15 * (30 * S.D) ^ 9 * (32 * S.D) ^ 9 * (62 * S.D) *
        (215482942465792 * S.D ^ 8) := by
    have hprod1 : d ^ 9 * (d + a) ^ 9 ≤ (30 * S.D) ^ 9 * (32 * S.D) ^ 9 :=
      mul_le_mul hd9_hi hda9_hi (by positivity) (by positivity)
    have hprod2 : d ^ 9 * (d + a) ^ 9 * (a + 2 * d) ≤
        (30 * S.D) ^ 9 * (32 * S.D) ^ 9 * (62 * S.D) :=
      mul_le_mul hprod1 had2_hi (by positivity) (by positivity)
    have hprod3 := mul_le_mul hprod2 hpoly_hi (by positivity)
      (by positivity : 0 ≤ (30 * S.D) ^ 9 * (32 * S.D) ^ 9 * (62 * S.D))
    nlinarith only [hprod3]
  have hQ7_lo : (3 * d ^ 2) ^ 7 ≤ Q ^ 7 := pow_le_pow_left₀ (by positivity) hQ_ge 7
  have hden_lo : 16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7 ≤
      16 * P.X ^ 4 * a ^ 4 * Q ^ 7 := by
    gcongr
  have hden_lo_pos : 0 < 16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7 := by
    positivity
  have hloc_hi :
      15 * d ^ 9 * (d + a) ^ 9 * (a + 2 * d) * Poly /
          (16 * P.X ^ 4 * a ^ 4 * Q ^ 7) ≤
        15 * (30 * S.D) ^ 9 * (32 * S.D) ^ 9 * (62 * S.D) *
          (215482942465792 * S.D ^ 8) /
          (16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7) := by
    rw [div_le_div_iff₀ hden_pos hden_lo_pos]
    have hmul := mul_le_mul hnum_hi hden_lo
      (by positivity : 0 ≤ 16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7)
      (by positivity : 0 ≤ 15 * (30 * S.D) ^ 9 * (32 * S.D) ^ 9 * (62 * S.D) *
        (215482942465792 * S.D ^ 8))
    nlinarith only [hmul]
  have hD14 : S.D ^ 14 ≤ 16 ^ 14 * d ^ 14 := by
    have hpow : (S.D / 16) ^ 14 ≤ d ^ 14 :=
      pow_le_pow_left₀ (by positivity) hd_lo 14
    nlinarith only [hpow, hDpos]
  have hbase_hi :
      15 * (30 * S.D) ^ 9 * (32 * S.D) ^ 9 * (62 * S.D) *
          (215482942465792 * S.D ^ 8) /
          (16 * P.X ^ 4 * (S.A / 5) ^ 4 * (3 * d ^ 2) ^ 7) ≤
        (10 ^ 100 : ℝ) * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hApos, ne_of_gt hd0]
    have hconst : (15 : ℝ) * 30 ^ 9 * 32 ^ 9 * 62 * 215482942465792 *
        5 ^ 4 * 16 ^ 14 ≤ 16 * 3 ^ 7 * 10 ^ 100 := by
      norm_num
    have hright : (15 : ℝ) * 30 ^ 9 * S.D ^ 14 * 32 ^ 9 * 62 *
        215482942465792 * 5 ^ 4 ≤ 16 * 3 ^ 7 * d ^ 14 * 10 ^ 100 := by
      calc (15 : ℝ) * 30 ^ 9 * S.D ^ 14 * 32 ^ 9 * 62 * 215482942465792 * 5 ^ 4
          ≤ (15 : ℝ) * 30 ^ 9 * (16 ^ 14 * d ^ 14) * 32 ^ 9 * 62 *
              215482942465792 * 5 ^ 4 := by
            gcongr
        _ = ((15 : ℝ) * 30 ^ 9 * 32 ^ 9 * 62 * 215482942465792 * 5 ^ 4 *
              16 ^ 14) * d ^ 14 := by ring
        _ ≤ (16 * 3 ^ 7 * 10 ^ 100) * d ^ 14 := by
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 16 * 3 ^ 7 * d ^ 14 * 10 ^ 100 := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hright
  rw [dBreve_deriv4_abs_factor_image P.X_pos ha0 hd0]
  rw [hQ, hPoly] at hbase_lo hloc_hi
  exact ⟨hbase_lo, le_trans hloc_hi hbase_hi⟩

/-- Grade-4 inverse scale packaging: `F⁴ |dBreve''''| ≍ HΔ` on the wide image window. -/
theorem dBreve_deriv4_scale_wide_image_construct {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 10 ≤ d) (hd_hi : d ≤ 18 * S.D) :
    (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  obtain ⟨hlo, hhi⟩ :=
    dBreve_deriv4_abs_base_wide (P := P) (S := S) (a := a) (d := d)
      hAD ha_lo ha_hi (by linarith) (by linarith)
  constructor
  · calc (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ)
        = (1 / 10 ^ 100 : ℝ) * S.D := rfl
      _ = S.F ^ 4 * ((1 / 10 ^ 100 : ℝ) *
            (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) := by
            rw [show S.F ^ 4 * ((1 / 10 ^ 100 : ℝ) *
                  (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) =
                (1 / 10 ^ 100 : ℝ) *
                  (S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) by ring,
              sec7_phase_inv4_scale_base S]
      _ ≤ S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)|
        ≤ S.F ^ 4 * ((10 ^ 100 : ℝ) *
            (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
            rw [show S.F ^ 4 * ((10 ^ 100 : ℝ) *
                  (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) =
                (10 ^ 100 : ℝ) *
                  (S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) by ring,
              sec7_phase_inv4_scale_base S]
            rfl

/-- Grade-4 inverse scale packaging on the §7 image window. -/
theorem dBreve_deriv4_scale_sec7_image {P : Globals} {S : Scale P} {a d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d) (hd_hi : d ≤ 30 * S.D) :
    (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ) ≤
        S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| ∧
      S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| ≤
        (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  obtain ⟨hlo, hhi⟩ :=
    dBreve_deriv4_abs_base_wide (P := P) (S := S) (a := a) (d := d)
      hAD ha_lo ha_hi hd_lo hd_hi
  constructor
  · calc (1 / 10 ^ 100 : ℝ) * (P.H * S.Δ)
        = (1 / 10 ^ 100 : ℝ) * S.D := rfl
      _ = S.F ^ 4 * ((1 / 10 ^ 100 : ℝ) *
            (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) := by
            rw [show S.F ^ 4 * ((1 / 10 ^ 100 : ℝ) *
                  (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) =
                (1 / 10 ^ 100 : ℝ) *
                  (S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) by ring,
              sec7_phase_inv4_scale_base S]
      _ ≤ S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)| :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d)|
        ≤ S.F ^ 4 * ((10 ^ 100 : ℝ) *
            (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = (10 ^ 100 : ℝ) * (P.H * S.Δ) := by
            rw [show S.F ^ 4 * ((10 ^ 100 : ℝ) *
                  (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) =
                (10 ^ 100 : ℝ) *
                  (S.F ^ 4 * (S.D ^ 13 / (P.X ^ 4 * S.A ^ 4))) by ring,
              sec7_phase_inv4_scale_base S]
            rfl

end Squarefree
