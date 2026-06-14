import Squarefree.Structure.PhaseDeriv
import Squarefree.Structure.DaSpacing

/-!
# §5 defect regime, foundational scale bound: `a ≍ A`

From a `RaWitness P S a r` (a popular `d` at the `D`-scale with `r ≈ R_a(d)`, `r ≍ R`), the
gap index `a` is forced to be `≍ A = ΔΩ`.  Concretely (writeup lines 676–690) we prove

  `S.A / 5 ≤ (a : ℝ) ≤ 11 * S.A`,

using the closed form `R_a(d) = X a³/(d²(d+a)²)` (`Rfun_factor'`) together with the scale
identity `R · D⁴ / X = A³`.  This is the entry point for §5's scale-window argument.
-/

namespace Squarefree

set_option maxHeartbeats 1600000

/-- **`a ≍ A`.**  From a `RaWitness` at the `D`-scale, with the mild floors `10·A ≤ D`
(equivalently `10·Ω ≤ H`) and `16777216 ≤ G·H·Ω³`, the gap index `a` satisfies
`A/5 ≤ a ≤ 11·A`. -/
theorem a_asymp_A {P : Globals} {S : Scale P} {a : ℤ} {r : ℕ}
    (hAD : 10 * S.A ≤ S.D) (hfloor : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3)
    (hwit : RaWitness P S a r) :
    S.A / 5 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 11 * S.A := by
  obtain ⟨d, hinDa, hd1, hd2, hrf, hr1, hr2⟩ := hwit
  -- abbreviations
  set X := P.X with hXdef
  set D := S.D with hDdef
  set R := S.R with hRdef
  set A := S.A with hAdef
  -- positivity of globals / scales
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < X := P.X_pos
  have hDeq : D = P.H * S.Δ := rfl
  have hAeq : A = S.Δ * S.Ω := rfl
  have hReq : R = P.H * P.G * S.Ω ^ 3 / S.Δ := rfl
  have hDpos : 0 < D := by rw [hDeq]; positivity
  have hApos : 0 < A := by rw [hAeq]; positivity
  have hRpos : 0 < R := by rw [hReq]; positivity
  -- the real points
  set a0 : ℝ := (a : ℝ) with ha0def
  set d0 : ℝ := (d : ℝ) with hd0def
  have ha0pos : 0 < a0 := by rw [ha0def]; exact_mod_cast hinDa.1
  have hd0pos : 0 < d0 := lt_of_lt_of_le hDpos hd1
  have hsum_pos : 0 < d0 + a0 := by linarith
  have hd0ne : d0 ≠ 0 := ne_of_gt hd0pos
  have hsum_ne : d0 + a0 ≠ 0 := ne_of_gt hsum_pos
  -- the scale identity `R · D⁴ / X = A³`
  have hRDX : R * D ^ 4 / X = A ^ 3 := by
    rw [hReq, hDeq, hAeq, hXdef, P.X_eq_G_mul_H_pow_five]
    field_simp
  -- closed form of Rfun
  have hRfun : Rfun X a0 d0 = X * a0 ^ 3 / (d0 ^ 2 * (d0 + a0) ^ 2) :=
    Rfun_factor' X a0 d0 hd0ne hsum_ne
  -- FLOOR step: `14·H/D ≤ R/1000000`
  have hfloorstep : 14 * P.H / D ≤ R / 1000000 := by
    -- `14 H/(H Δ) = 14/Δ ≤ (H G Ω³/Δ)/1e6` ⟺ `14·1e6 ≤ H G Ω³`, from hfloor.
    have hlhs : 14 * P.H / D = 14 / S.Δ := by
      rw [hDeq]; field_simp
    have hrhs : R / 1000000 = (P.H * P.G * S.Ω ^ 3) / (S.Δ * 1000000) := by
      rw [hReq]; field_simp
    rw [hlhs, hrhs, div_le_div_iff₀ hΔpos (by positivity)]
    -- `14 · (Δ · 1e6) ≤ (H G Ω³) · Δ`
    have hkey : (14000000 : ℝ) ≤ P.H * P.G * S.Ω ^ 3 := by
      have : P.G * P.H * S.Ω ^ 3 = P.H * P.G * S.Ω ^ 3 := by ring
      linarith [hfloor, this]
    nlinarith [hkey, hΔpos]
  -- bounds on Rfun from the witness
  have habs := abs_le.mp hrf
  -- `Rfun ≥ R/73`
  have hRfunlo : R / 73 ≤ X * a0 ^ 3 / (d0 ^ 2 * (d0 + a0) ^ 2) := by
    rw [← hRfun]
    have h1 : (r : ℝ) - 14 * P.H / D ≤ Rfun X a0 d0 := by linarith [habs.1]
    have h2 : R / 73 ≤ (r : ℝ) - 14 * P.H / D := by
      have : R / 72 - R / 1000000 ≤ (r : ℝ) - 14 * P.H / D := by
        linarith [hr1, hfloorstep]
      have hgap : R / 73 ≤ R / 72 - R / 1000000 := by
        rw [div_sub_div _ _ (by norm_num : (72:ℝ) ≠ 0) (by norm_num : (1000000:ℝ) ≠ 0),
          div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hRpos]
      linarith
    linarith
  -- `Rfun ≤ 17 R`
  have hRfunhi : X * a0 ^ 3 / (d0 ^ 2 * (d0 + a0) ^ 2) ≤ 17 * R := by
    rw [← hRfun]
    have h1 : Rfun X a0 d0 ≤ (r : ℝ) + 14 * P.H / D := by linarith [habs.2]
    have h2 : (r : ℝ) + 14 * P.H / D ≤ 17 * R := by
      have : (r : ℝ) + 14 * P.H / D ≤ 16 * R + R / 1000000 := by
        linarith [hr2, hfloorstep]
      nlinarith [hRpos, this]
    linarith
  -- denominators positive
  have hden_pos : 0 < d0 ^ 2 * (d0 + a0) ^ 2 := by positivity
  -- STEP: `a0 ≤ d0`
  have ha_le_d : a0 ≤ d0 := by
    by_contra hcon
    rw [not_le] at hcon  -- d0 < a0
    -- a0 > D since d0 ≥ D
    have ha0gtD : D < a0 := lt_of_le_of_lt hd1 hcon
    -- d0 < a0 ⟹ d0 + a0 < 2 a0; d0 ≤ 2D
    have hsum_lt : d0 + a0 < 2 * a0 := by linarith
    -- denominator bound: d0²(d0+a0)² < (2D)²(2a0)² = 16 D² a0²
    have hden_lt : d0 ^ 2 * (d0 + a0) ^ 2 < 16 * D ^ 2 * a0 ^ 2 := by
      have hd0sq : d0 ^ 2 ≤ (2 * D) ^ 2 := by nlinarith [hd2, hDpos, hd0pos]
      have hsumsq : (d0 + a0) ^ 2 < (2 * a0) ^ 2 := by nlinarith [hsum_lt, hsum_pos, ha0pos]
      have step1 : d0 ^ 2 * (d0 + a0) ^ 2 ≤ (2 * D) ^ 2 * (d0 + a0) ^ 2 :=
        mul_le_mul_of_nonneg_right hd0sq (by positivity)
      have step2 : (2 * D) ^ 2 * (d0 + a0) ^ 2 < (2 * D) ^ 2 * (2 * a0) ^ 2 :=
        mul_lt_mul_of_pos_left hsumsq (by positivity)
      have heq2 : (2 * D) ^ 2 * (2 * a0) ^ 2 = 16 * D ^ 2 * a0 ^ 2 := by ring
      linarith [step1, step2, heq2.le, heq2.ge]
    -- so Rfun > X a0³/(16 D² a0²) = X a0/(16 D²) ≥ X D/(16 D²) = X/(16D)
    have hRfun_gt : X / (16 * D) < X * a0 ^ 3 / (d0 ^ 2 * (d0 + a0) ^ 2) := by
      have hlt1 : X * a0 ^ 3 / (16 * D ^ 2 * a0 ^ 2) < X * a0 ^ 3 / (d0 ^ 2 * (d0 + a0) ^ 2) :=
        div_lt_div_of_pos_left (by positivity) hden_pos hden_lt
      have heq : X * a0 ^ 3 / (16 * D ^ 2 * a0 ^ 2) = X * a0 / (16 * D ^ 2) := by
        field_simp
      have hge2 : X / (16 * D) ≤ X * a0 / (16 * D ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos (mul_pos hXpos hDpos) (by linarith : (0:ℝ) < a0 - D), hXpos, hDpos]
      rw [heq] at hlt1
      linarith
    -- Show X/(16D) > 17 R, contradicting hRfunhi
    have hXD_gt : 17 * R < X / (16 * D) := by
      -- X/(16D) = G H⁴ / (16 Δ); 17 R = 17 H G Ω³/Δ; reduces to H³ > 272 Ω³, from H ≥ 10 Ω
      have hHge : 10 * S.Ω ≤ P.H := by
        -- from 10 A ≤ D i.e. 10 Δ Ω ≤ H Δ
        have : 10 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by rw [← hAeq, ← hDeq]; exact hAD
        nlinarith [hΔpos, this]
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 16 * D)]
      -- `17 R · (16 D) < X`, i.e. `272 R D < X`.  Substitute R = HGΩ³/Δ, D = HΔ, X = G H⁵.
      rw [hReq, hDeq, hXdef, P.X_eq_G_mul_H_pow_five]
      -- goal: `17 * (H G Ω³/Δ) * (16 * (H Δ)) < G H⁵`
      have hsimp : 17 * (P.H * P.G * S.Ω ^ 3 / S.Δ) * (16 * (P.H * S.Δ))
          = 272 * (P.G * P.H ^ 2 * S.Ω ^ 3) := by field_simp; ring
      rw [hsimp]
      -- `272 (G H² Ω³) < G H⁵` ⟺ `272 Ω³ < H³`, times `G H² > 0`.
      have hH3 : (272 : ℝ) * S.Ω ^ 3 < P.H ^ 3 := by
        nlinarith [hHge, hΩpos, hHpos, mul_pos hΩpos hΩpos, sq_nonneg (P.H - 10 * S.Ω),
          mul_pos (mul_pos hΩpos hΩpos) hΩpos,
          mul_nonneg (mul_nonneg hHpos.le hHpos.le) (by linarith : (0:ℝ) ≤ P.H - 10 * S.Ω)]
      have hfac : 0 < P.G * P.H ^ 2 := by positivity
      nlinarith [mul_lt_mul_of_pos_left hH3 hfac, hfac]
    linarith [hRfunhi, hRfun_gt, hXD_gt]
  -- Now `D ≤ d0 ≤ 2D` and `D ≤ d0 + a0 ≤ 4D`
  have hsum_lo : D ≤ d0 + a0 := by linarith
  have hsum_hi : d0 + a0 ≤ 4 * D := by linarith
  -- `D⁴ ≤ d0²(d0+a0)² ≤ 64 D⁴`
  have hden_lo : D ^ 4 ≤ d0 ^ 2 * (d0 + a0) ^ 2 := by
    have h1 : D ^ 2 ≤ d0 ^ 2 := by nlinarith [hd1, hDpos, hd0pos]
    have h2 : D ^ 2 ≤ (d0 + a0) ^ 2 := by nlinarith [hsum_lo, hDpos, hsum_pos]
    nlinarith [h1, h2, pow_pos hDpos 2]
  have hden_hi : d0 ^ 2 * (d0 + a0) ^ 2 ≤ 64 * D ^ 4 := by
    have h1 : d0 ^ 2 ≤ (2 * D) ^ 2 := by nlinarith [hd2, hDpos, hd0pos]
    have h2 : (d0 + a0) ^ 2 ≤ (4 * D) ^ 2 := by nlinarith [hsum_hi, hDpos, hsum_pos]
    nlinarith [h1, h2, pow_pos hDpos 2, sq_nonneg d0, sq_nonneg (d0 + a0)]
  -- LOWER `a`: `X a0³ = Rfun · den ≥ (R/73) D⁴`, so `a0³ ≥ A³/73`
  have hXa3_lo : (R / 73) * D ^ 4 ≤ X * a0 ^ 3 := by
    have hcross : (R / 73) * (d0 ^ 2 * (d0 + a0) ^ 2) ≤ X * a0 ^ 3 := by
      have := (le_div_iff₀ hden_pos).mp hRfunlo
      linarith [this]
    have hmono : (R / 73) * D ^ 4 ≤ (R / 73) * (d0 ^ 2 * (d0 + a0) ^ 2) :=
      mul_le_mul_of_nonneg_left hden_lo (by positivity)
    linarith
  have ha0cube_lo : A ^ 3 / 73 ≤ a0 ^ 3 := by
    -- a0³ = (X a0³)/X ≥ (R D⁴/73)/X = (R D⁴/X)/73 = A³/73
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 73)] at *
    have hXa3 : (R / 73) * D ^ 4 * 73 ≤ X * a0 ^ 3 * 73 := by linarith [hXa3_lo]
    -- divide by X
    have hkey : A ^ 3 ≤ a0 ^ 3 * 73 := by
      have heq : R * D ^ 4 = A ^ 3 * X := by
        have := hRDX
        field_simp at this ⊢
        linarith [this]
      nlinarith [hXa3, hXpos, heq]
    linarith [hkey]
  -- cube-monotone: a0³ ≥ A³/73 ≥ (A/5)³ ⟹ a0 ≥ A/5
  have hlower : A / 5 ≤ a0 := by
    nlinarith [ha0cube_lo, hApos, ha0pos, sq_nonneg (a0 - A / 5), sq_nonneg (a0 + A / 5),
      mul_pos ha0pos ha0pos, mul_pos hApos hApos]
  -- UPPER `a`: `X a0³ = Rfun · den ≤ 17 R · 64 D⁴ = 1088 R D⁴`, so `a0³ ≤ 1088 A³`
  have hXa3_hi : X * a0 ^ 3 ≤ 1088 * R * D ^ 4 := by
    have hcross : X * a0 ^ 3 ≤ 17 * R * (d0 ^ 2 * (d0 + a0) ^ 2) := by
      have := (div_le_iff₀ hden_pos).mp hRfunhi
      linarith [this]
    have hmono : 17 * R * (d0 ^ 2 * (d0 + a0) ^ 2) ≤ 17 * R * (64 * D ^ 4) :=
      mul_le_mul_of_nonneg_left hden_hi (by positivity)
    linarith
  have ha0cube_hi : a0 ^ 3 ≤ 1088 * A ^ 3 := by
    have heq : R * D ^ 4 = A ^ 3 * X := by
      have := hRDX
      field_simp at this ⊢
      linarith [this]
    nlinarith [hXa3_hi, hXpos, heq]
  have hupper : a0 ≤ 11 * A := by
    nlinarith [ha0cube_hi, hApos, ha0pos, sq_nonneg (a0 - 11 * A), sq_nonneg (11 * A - a0),
      mul_pos ha0pos ha0pos, mul_pos hApos hApos]
  exact ⟨hlower, hupper⟩

/-- **`d̃ₐ(r) ≍ D`** (writeup line 343).  Given `a ≍ A` (window `[A/5, 11A]`) and `r ≍ R`
(window `[R/72, 16R]`), the inverse `d̃ₐ(r)` satisfies `D/10 ≤ d̃ₐ(r) ≤ 18·D`.  The mild
floor `10·A ≤ D` (equivalently `10·Ω ≤ H`) is what forces `d̃ ≥ a`. -/
theorem dtilde_asymp_D {P : Globals} {S : Scale P} {a r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hr0 : 0 < r)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R) :
    S.D / 10 ≤ dtilde P.X r a ∧ dtilde P.X r a ≤ 18 * S.D := by
  -- abbreviations
  set X := P.X with hXdef
  set D := S.D with hDdef
  set R := S.R with hRdef
  set A := S.A with hAdef
  -- positivity
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hXpos : 0 < X := P.X_pos
  have hDeq : D = P.H * S.Δ := rfl
  have hAeq : A = S.Δ * S.Ω := rfl
  have hReq : R = P.H * P.G * S.Ω ^ 3 / S.Δ := rfl
  have hDpos : 0 < D := by rw [hDeq]; positivity
  have hApos : 0 < A := by rw [hAeq]; positivity
  have hRpos : 0 < R := by rw [hReq]; positivity
  -- the scale identity `X · A³ / R = D⁴`
  have hXAR : X * A ^ 3 / R = D ^ 4 := by
    rw [hReq, hDeq, hAeq, hXdef, P.X_eq_G_mul_H_pow_five]
    field_simp
  -- `d̃` and the quadratic identity
  set d := dtilde X r a with hddef
  have hdpos : 0 < d := dtilde_pos hXpos ha0 hr0
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hprod : d * (d + a) = w := dtilde_prod hXpos ha0 hr0
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  -- two-sided bound on `X a³/r`, hence on `w²`
  -- upper: `a ≤ 11A`, `r ≥ R/72` ⟹ `X a³/r ≤ X (11A)³ / (R/72) = 95832 D⁴`
  have ha3_hi : a ^ 3 ≤ (11 * A) ^ 3 := pow_le_pow_left₀ ha0.le ha_hi 3
  have ha3_lo : (A / 5) ^ 3 ≤ a ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ A / 5) ha_lo 3
  -- helper: `D⁴ = X A³ / R`, so `X A³ = D⁴ R`
  have hXA3 : X * A ^ 3 = D ^ 4 * R := by
    rw [← hXAR]; field_simp
  have hw2_hi : w ^ 2 ≤ 95832 * D ^ 4 := by
    rw [hwsq]
    -- `X a³/r ≤ X (11A)³ / (R/72) = 95832 (X A³)/R = 95832 D⁴`
    have hnum : X * a ^ 3 ≤ X * (11 * A) ^ 3 :=
      mul_le_mul_of_nonneg_left ha3_hi hXpos.le
    have hstep : X * a ^ 3 / r ≤ X * (11 * A) ^ 3 / (R / 72) := by
      apply div_le_div₀ (by positivity) hnum (by positivity) (by linarith [hr_lo])
    refine hstep.trans ?_
    rw [div_le_iff₀ (by positivity : (0:ℝ) < R / 72)]
    -- `X (11A)³ ≤ 95832 D⁴ · (R/72)`; note `X (11A)³ = 1331 (X A³) = 1331 D⁴ R`
    nlinarith [hXA3, hRpos, pow_pos hDpos 4]
  have hw2_lo : D ^ 4 / 2000 ≤ w ^ 2 := by
    rw [hwsq]
    -- `X a³/r ≥ X (A/5)³ / (16 R) = (X A³)/(2000 R) = D⁴/2000`
    have hnum : X * (A / 5) ^ 3 ≤ X * a ^ 3 :=
      mul_le_mul_of_nonneg_left ha3_lo hXpos.le
    have hstep : X * (A / 5) ^ 3 / (16 * R) ≤ X * a ^ 3 / r := by
      apply div_le_div₀ (by positivity) hnum hr0 (by linarith [hr_hi])
    refine le_trans ?_ hstep
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * R)]
    -- `D⁴/2000 · (16 R) ≤ X (A/5)³`; `X(A/5)³ = (X A³)/125 = D⁴ R/125`
    nlinarith [hXA3, hRpos, pow_pos hDpos 4]
  -- ===== UPPER: `d ≤ 18 D` =====
  -- `d² < d(d+a) = w` (since `a>0`); `w² ≤ 95832 D⁴` ⟹ `w ≤ 310 D²` ⟹ `d² < 310 D²` ⟹ `d < 18 D`
  have hd2_lt_w : d ^ 2 < w := by
    have : d ^ 2 < d * (d + a) := by nlinarith [hdpos, ha0]
    linarith [hprod, this]
  have hw_le : w ≤ 310 * D ^ 2 := by
    nlinarith [hw2_hi, sq_nonneg (w - 310 * D ^ 2), hwpos, hDpos, pow_pos hDpos 2,
      mul_pos hwpos hwpos]
  have hupper : d ≤ 18 * D := by
    nlinarith [hd2_lt_w, hw_le, sq_nonneg (d - 18 * D), hdpos, hDpos, pow_pos hDpos 2,
      mul_pos hdpos hdpos]
  -- ===== `d ≥ a` (the floor-forced inequality) =====
  have hd_ge_a : a ≤ d := by
    by_contra hcon
    rw [not_le] at hcon  -- d < a
    -- `d(d+a) < a·(2a) = 2a²` ⟹ `w < 2a²` ⟹ `w² < 4a⁴` ⟹ `X a³/r < 4 a⁴`
    have hw_lt : w < 2 * a ^ 2 := by
      have : d * (d + a) < a * (2 * a) := by nlinarith [hdpos, ha0, hcon]
      nlinarith [hprod, this]
    have hw2_lt : w ^ 2 < 4 * a ^ 4 := by
      nlinarith [hw_lt, hwpos, ha0, sq_nonneg a, mul_pos ha0 ha0]
    rw [hwsq] at hw2_lt  -- X a³/r < 4 a⁴
    -- ⟹ `X a³ < 4 a⁴ r`, i.e. `X < 4 a r` (divide by `a³>0`)
    have hXar : X < 4 * a * r := by
      have hcross : X * a ^ 3 < 4 * a ^ 4 * r := by
        have := (div_lt_iff₀ hr0).mp hw2_lt; linarith [this]
      have ha3pos : 0 < a ^ 3 := by positivity
      nlinarith [hcross, ha3pos, ha0]
    -- `4 a r ≤ 4·(11A)·(16R) = 704 A R`
    have hbound : 4 * a * r ≤ 704 * (A * R) := by
      nlinarith [ha_hi, hr_hi, ha0, hr0, hApos, hRpos,
        mul_le_mul ha_hi hr_hi hr0.le (by positivity : (0:ℝ) ≤ 11 * A)]
    -- `704 A R < X`: `A·R = H G Ω⁴`, `X = G H⁵`, so ⟺ `704 Ω⁴ < H⁴`, from `H ≥ 10 Ω`
    have hHge : 10 * S.Ω ≤ P.H := by
      have : 10 * (S.Δ * S.Ω) ≤ P.H * S.Δ := by rw [← hAeq, ← hDeq]; exact hAD
      nlinarith [hΔpos, this]
    have hAR : A * R = P.H * P.G * S.Ω ^ 4 := by
      rw [hAeq, hReq]; field_simp
    have h704 : 704 * (A * R) < X := by
      rw [hAR, hXdef, P.X_eq_G_mul_H_pow_five]
      -- `704 (H G Ω⁴) < G H⁵` ⟺ `704 Ω⁴ < H⁴`, times `G H > 0`
      have hH4 : (704 : ℝ) * S.Ω ^ 4 < P.H ^ 4 := by
        have hmono : (10 * S.Ω) ^ 4 ≤ P.H ^ 4 :=
          pow_le_pow_left₀ (by positivity) hHge 4
        nlinarith [hmono, pow_pos hΩpos 4]
      have hfac : 0 < P.G * P.H := by positivity
      nlinarith [mul_lt_mul_of_pos_left hH4 hfac, hfac]
    linarith [hXar, hbound, h704]
  -- ===== LOWER: `d ≥ D/10` =====
  -- `d ≥ a` ⟹ `d+a ≤ 2d` ⟹ `w = d(d+a) ≤ 2 d²`; `w² ≥ D⁴/2000` ⟹ `w ≥ D²/45` ⟹ `d² ≥ D²/90` ⟹ `d ≥ D/10`
  have hw_le_2d2 : w ≤ 2 * d ^ 2 := by
    have : d * (d + a) ≤ 2 * d ^ 2 := by nlinarith [hdpos, hd_ge_a]
    linarith [hprod, this]
  have hw_ge : D ^ 2 / 45 ≤ w := by
    nlinarith [hw2_lo, sq_nonneg (w - D ^ 2 / 45), hwpos, hDpos, pow_pos hDpos 2,
      mul_pos hwpos hwpos]
  have hlower : D / 10 ≤ d := by
    nlinarith [hw_le_2d2, hw_ge, sq_nonneg (d - D / 10), hdpos, hDpos, pow_pos hDpos 2,
      mul_pos hdpos hdpos]
  exact ⟨hlower, hupper⟩

end Squarefree
