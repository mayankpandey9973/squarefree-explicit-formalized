import Squarefree.Lower.Step3Qbound

/-!
# §5 Step-3 per-`r` lower bound on `|𝒬|` in the monotone range (writeup 952–966)

`Qval_abs_ge`: the companion of `Qval_abs_le`.  In the monotone subrange the defect `v` is
large, `V₁ < |v|` with

```
V₁ := 10⁶⁵·(Δ³·U¹⁰)/(H·Ω⁶),
```

so the leading `v`-term `6ℓ₁Xav/d⁴` of `Q_gen_expand` dominates the `b₀²`-term and the
remainder `ERR`.  The mechanism mirrors `Qval_abs_le` but keeps the *lower* bound: every
non-`v` piece of `𝒬` is bounded by `(1/4)·|VTERM|` relative to the `v`-term (cancelling one
factor of `|v|` and using `|v| > V₁`), giving

```
|𝒬| ≥ (1/2)·|VTERM| ≥ (1/2)·(6/80)·ℓ₁·(H·G·Ω/Δ³)·V₁ ≥ 10⁵⁵·L + 1/2,
```

where `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(G·Ω⁵)`.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- Regime scale fact `U⁵·Δ ≤ H·Ω³`, from `h1 : G·U¹⁰ ≤ H/Δ²` and the band. -/
private theorem reg_U5Δ_le (S : Scale P)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U) :
    P.U ^ 5 * S.Δ ≤ P.H * S.Ω ^ 3 := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
    (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
  have hUΔ1 : (1:ℝ) ≤ P.U * S.Δ := by nlinarith [hU1, hΔ1, hUpos, hΔpos]
  have hband' : (1:ℝ) ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := by
    have h4 : P.U ^ 3 * S.Ω ^ 4 ≤ P.U ^ 4 * S.Ω ^ 3 := by
      have e : P.U ^ 4 * S.Ω ^ 3 - P.U ^ 3 * S.Ω ^ 4 = P.U ^ 3 * S.Ω ^ 3 * (P.U - S.Ω) := by ring
      nlinarith [e, mul_nonneg (mul_nonneg (pow_nonneg hUpos.le 3) (pow_nonneg hΩpos.le 3))
        (sub_nonneg.mpr hΩU)]
    nlinarith [hband, mul_le_mul_of_nonneg_left h4 hGpos.le]
  have hGU5 : (1:ℝ) ≤ P.G * P.U ^ 5 * S.Δ * S.Ω ^ 3 := by
    have := mul_le_mul hband' hUΔ1 (by norm_num) (by positivity)
    rw [one_mul] at this
    calc (1:ℝ) ≤ (P.G * P.U ^ 4 * S.Ω ^ 3) * (P.U * S.Δ) := this
      _ = P.G * P.U ^ 5 * S.Δ * S.Ω ^ 3 := by ring
  have h1' : P.U ^ 5 * S.Δ ≤ P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := by
    have := mul_le_mul_of_nonneg_left hGU5 (by positivity : (0:ℝ) ≤ P.U ^ 5 * S.Δ)
    rw [mul_one] at this
    calc P.U ^ 5 * S.Δ ≤ (P.U ^ 5 * S.Δ) * (P.G * P.U ^ 5 * S.Δ * S.Ω ^ 3) := this
      _ = P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := by ring
  calc P.U ^ 5 * S.Δ ≤ P.G * P.U ^ 10 * S.Δ ^ 2 * S.Ω ^ 3 := h1'
    _ ≤ P.H * S.Ω ^ 3 := by nlinarith [hHbig, pow_nonneg hΩpos.le 3]

/-- The numeric core of the v-term lower bound: with `L₀ := ℓ₁·G·U¹⁰/Ω⁵ ≥ 1` and
`ℓ₂(ℓ₂−ℓ₁) ≤ (G·U⁵)²`, the target `10⁵⁵·L + 1/2` is below `(3/80·10⁶⁵)·L₀`. -/
private theorem vterm_numeric (S : Scale P) {l1 l2 : ℝ}
    (hℓ1R : (1:ℝ) ≤ l1) (hℓ12R : l1 < l2) (hℓ2W' : l2 ≤ 130 * (P.G * P.U ^ 5))
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U) :
    10 ^ 55 * (l1 * l2 * (l2 - l1) / (P.G * S.Ω ^ 5)) + 1 / 2
      ≤ (3 / 80 * 10 ^ 65) * (l1 * (P.G * P.U ^ 10 / S.Ω ^ 5)) := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hΩpos := S.Ω_pos
  have hℓ1pos : (0:ℝ) < l1 := lt_of_lt_of_le one_pos hℓ1R
  have hℓ2R : (0:ℝ) < l2 := lt_trans hℓ1pos hℓ12R
  have hℓfac : l2 * (l2 - l1) ≤ 16900 * (P.G * P.U ^ 5) ^ 2 := by
    have e1 : l2 - l1 ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ2W', hℓ1pos]
    have p2 : (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
        = 16900 * (P.G * P.U ^ 5) ^ 2 := by ring
    rw [← p2]; exact mul_le_mul hℓ2W' e1 (by linarith [hℓ12R]) (by positivity)
  have hLle : l1 * l2 * (l2 - l1) / (P.G * S.Ω ^ 5)
      ≤ 16900 * (l1 * (P.G * P.U ^ 10 / S.Ω ^ 5)) := by
    rw [div_le_iff₀ (by positivity)]
    have hstep : l1 * (l2 * (l2 - l1)) ≤ l1 * (16900 * (P.G * P.U ^ 5) ^ 2) :=
      mul_le_mul_of_nonneg_left hℓfac hℓ1pos.le
    calc l1 * l2 * (l2 - l1) = l1 * (l2 * (l2 - l1)) := by ring
      _ ≤ l1 * (16900 * (P.G * P.U ^ 5) ^ 2) := hstep
      _ = 16900 * (l1 * (P.G * P.U ^ 10 / S.Ω ^ 5)) * (P.G * S.Ω ^ 5) := by field_simp; try ring
  have hbase_big : (1:ℝ) ≤ l1 * (P.G * P.U ^ 10 / S.Ω ^ 5) := by
    have hΩ10 : S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩpos.le hΩU 5
    have hUU : (1:ℝ) ≤ P.U ^ 10 / S.Ω ^ 5 := by
      rw [le_div_iff₀ (by positivity)]
      have hUUU : P.U ^ 5 ≤ P.U ^ 10 := by nlinarith [one_le_pow₀ hU1 (n := 5), pow_pos hUpos 5]
      linarith [hΩ10, hUUU]
    have hG : (1:ℝ) ≤ P.G * (P.U ^ 10 / S.Ω ^ 5) := by nlinarith [hG1, hUU, hGpos]
    calc (1:ℝ) ≤ P.G * (P.U ^ 10 / S.Ω ^ 5) := hG
      _ = 1 * (P.G * P.U ^ 10 / S.Ω ^ 5) := by rw [one_mul]; field_simp
      _ ≤ l1 * (P.G * P.U ^ 10 / S.Ω ^ 5) :=
          mul_le_mul_of_nonneg_right hℓ1R (by positivity)
  nlinarith [hLle, hbase_big, mul_le_mul_of_nonneg_left hLle (by norm_num : (0:ℝ) ≤ (10:ℝ) ^ 55)]

set_option maxHeartbeats 800000 in
/-- **§5 Step-3 per-`r` lower bound on `|𝒬|`** in the monotone range `V₁ < |v|`. -/
theorem Qval_abs_ge {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ} {b₀ v : ℝ}
    (_hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (_hr_hi : r ≤ 16 * S.R)
    (hdwin : S.D ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * S.D)
    (hb0def : (ℓ₁ : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ))
    (hvdef : (ℓ₂ : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ))
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hv1 : 10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) < |v|)
    (hd1ned : (d₁ : ℝ) ≠ (d : ℝ)) (hd2ned : (d₂ : ℝ) ≠ (d : ℝ))
    (hwin2 : 4 * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ≤ (d : ℝ))
    (hwin1 : 4 * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ≤ (d : ℝ))
    {𝒬 : ℝ}
    (h𝒬 : 𝒬 = (ℓ₁ : ℝ) * Fab P.X (a : ℝ) ((ℓ₂ : ℝ) * b₀ + v) (d : ℝ)
              - (ℓ₂ : ℝ) * Fab P.X (a : ℝ) ((ℓ₁ : ℝ) * b₀) (d : ℝ))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (_hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) :
    10 ^ 55 * ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) / (P.G * S.Ω ^ 5)) + 1 / 2 ≤ |𝒬| := by
  -- ===== positivity =====
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : 0 < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : 0 < (ℓ₂ : ℝ) := lt_trans hℓ1R hℓ12R
  have hℓ2W' : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hℓ1W' : (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12R.le hℓ2W'
  have hAposS : 0 < S.A := by unfold Scale.A; positivity
  have hdD : S.D ≤ (d : ℝ) := hdwin.1
  have hdRpos : 0 < (d : ℝ) := lt_of_lt_of_le hDpos hdD
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  -- the master scale M = U⁵Δ²/Ω³ and V₁
  set M : ℝ := P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; positivity
  set V₁ : ℝ := 10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) with hV1_def
  have hV1_pos : 0 < V₁ := by rw [hV1_def]; positivity
  have hvpos : 0 < |v| := lt_trans hV1_pos hv1
  -- ===== Q_gen_expand =====
  have hℓ2bv : (ℓ₂ : ℝ) * b₀ + v ≠ 0 := by rw [hvdef]; exact sub_ne_zero.mpr hd2ned
  have hℓ1b₀ : (ℓ₁ : ℝ) * b₀ ≠ 0 := by rw [hb0def]; exact sub_ne_zero.mpr hd1ned
  have hQ := Q_gen_expand (X := P.X) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
    (ℓ₁ := (ℓ₁ : ℝ)) (ℓ₂ := (ℓ₂ : ℝ)) hXpos haR hdRpos hℓ1R hℓ12R hℓ2bv hℓ1b₀ hwin2 hwin1
  rw [← h𝒬] at hQ
  set VTERM : ℝ := 6 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * v / (d : ℝ) ^ 4 with hVTERM_def
  set BTERM : ℝ := 12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)
      * b₀ ^ 2 / (d : ℝ) ^ 5 with hBTERM_def
  set ERR : ℝ := 12 * P.X * (a : ℝ) * (ℓ₁ : ℝ) * |v| * ((a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v|) / (d : ℝ) ^ 5
      + 400 * P.X * (a : ℝ) * (ℓ₁ : ℝ) * |(ℓ₂ : ℝ) * b₀ + v| * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ^ 2 / (d : ℝ) ^ 6
      + 400 * P.X * (a : ℝ) * (ℓ₂ : ℝ) * (ℓ₁ : ℝ) * |b₀| * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ^ 2 / (d : ℝ) ^ 6
      with hERR_def
  have hQ' : |𝒬 - (VTERM - BTERM)| ≤ ERR := hQ
  -- ===== |VTERM| in closed form =====
  have hVabs : |VTERM| = 6 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * |v| / (d : ℝ) ^ 4 := by
    rw [hVTERM_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < (d:ℝ) ^ 4)]
    rw [show (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * v) = (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ)) * v by ring,
      abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 * (ℓ₁ : ℝ) * P.X * (a : ℝ))]
  have hVTERM_pos : 0 < |VTERM| := by rw [hVabs]; positivity
  -- ===== reverse triangle: |𝒬| ≥ |VTERM| − |BTERM| − ERR =====
  have hrev : |VTERM| - (|BTERM| + ERR) ≤ |𝒬| := by
    have h1' : |VTERM - BTERM| - |𝒬 - (VTERM - BTERM)| ≤ |𝒬| := by
      have := abs_sub_abs_le_abs_sub (VTERM - BTERM) 𝒬
      have heq : (VTERM - BTERM) - 𝒬 = -(𝒬 - (VTERM - BTERM)) := by ring
      rw [heq, abs_neg] at this
      linarith [this]
    have h2' : |VTERM| - |BTERM| ≤ |VTERM - BTERM| := by
      have := abs_sub_abs_le_abs_sub VTERM BTERM
      linarith [abs_sub VTERM BTERM, this]
    linarith [h1', h2', hQ']
  -- ===== the scale facts on the auxiliary quantities =====
  have ha_M : (a : ℝ) ≤ M := by
    have ha11 : (a : ℝ) ≤ 11 * (S.Δ * S.Ω) := by
      have : (11 : ℝ) * S.A = 11 * (S.Δ * S.Ω) := by unfold Scale.A; ring
      linarith [ha_hi, this]
    rw [hM_def, le_div_iff₀ (by positivity)]
    have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ hΩpos.le hΩU 4
    have hUΔ : (11 : ℝ) ≤ P.U * S.Δ := by
      have : (11 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
      nlinarith only [hΔ1, this, hUpos]
    have c1 : (a : ℝ) * S.Ω ^ 3 ≤ 11 * S.Δ * S.Ω ^ 4 := by
      have := mul_le_mul_of_nonneg_right ha11 (pow_nonneg hΩpos.le 3); nlinarith only [this]
    have c2 : (11 : ℝ) * S.Δ * S.Ω ^ 4 ≤ 11 * S.Δ * P.U ^ 4 :=
      mul_le_mul_of_nonneg_left hΩ4 (by positivity)
    have c3 : (11 : ℝ) * S.Δ * P.U ^ 4 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hUΔ (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 4),
        hΔpos, hUpos]
    linarith [c1, c2, c3]
  have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
    have : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
    rw [this] at hb0; exact hb0
  have hℓ2b0_M : (ℓ₂ : ℝ) * |b₀| ≤ 390000000000000 * M := by
    calc (ℓ₂ : ℝ) * |b₀|
          ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
          mul_le_mul hℓ2W' hb0' (abs_nonneg _) (by positivity)
      _ = 390000000000000 * M := by rw [hM_def]; field_simp; ring
  have hℓ1b0_M : (ℓ₁ : ℝ) * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right hℓ12R.le (abs_nonneg _)) hℓ2b0_M
  have hv_M : |v| ≤ 10 ^ 20 * M := by
    rw [hM_def]
    refine le_trans hv ?_
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith only [hΔ1, hΔpos]
    have hnum : S.Δ * P.U ^ 5 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith only [hΔsq, pow_nonneg hUpos.le 5]
    have hbase : S.Δ * P.U ^ 5 / S.Ω ^ 3 ≤ P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    exact mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hℓ2b0v_M : |(ℓ₂ : ℝ) * b₀ + v| ≤ 2 * 10 ^ 20 * M := by
    calc |(ℓ₂ : ℝ) * b₀ + v| ≤ |(ℓ₂ : ℝ) * b₀| + |v| := abs_add_le _ _
      _ = (ℓ₂ : ℝ) * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ2R]
      _ ≤ 390000000000000 * M + 10 ^ 20 * M := by linarith [hℓ2b0_M, hv_M]
      _ ≤ 2 * 10 ^ 20 * M := by linarith [hM_pos.le]
  have hfac1 : (a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v| ≤ 2 * 10 ^ 20 * M := by
    have h2 : 2 * (ℓ₂ : ℝ) * |b₀| ≤ 2 * (390000000000000 * M) := by
      have : 2 * (ℓ₂ : ℝ) * |b₀| = 2 * ((ℓ₂ : ℝ) * |b₀|) := by ring
      rw [this]; linarith [hℓ2b0_M]
    linarith [ha_M, h2, hv_M, hM_pos.le]
  have hfac2 : (a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v| ≤ 3 * 10 ^ 20 * M := by
    linarith [ha_M, hℓ2b0v_M, hM_pos.le]
  have hfac3 : (a : ℝ) + (ℓ₁ : ℝ) * |b₀| ≤ 400000000000000 * M := by
    linarith [ha_M, hℓ1b0_M, hM_pos.le]
  -- ===== KEY reduction: BTERM + ERR ≤ (1/2)·|VTERM| =====
  -- The common positive factor K = ℓ₁·X·a/d⁴, so |VTERM| = K·(6|v|).
  set K : ℝ := (ℓ₁ : ℝ) * P.X * (a : ℝ) / (d : ℝ) ^ 4 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  have hVTERM_K : |VTERM| = K * (6 * |v|) := by
    rw [hVabs, hK_def]; field_simp
  -- `d ≥ D > 0` facts for denominators
  have hdD' : (d : ℝ) ≥ S.D := hdD
  have hd_pos : (0:ℝ) < (d : ℝ) := hdRpos
  -- ===== regime fact: U⁵·Δ ≤ H·Ω³   (from h1: H ≥ G·U¹⁰·Δ²) =====
  have hreg : P.U ^ 5 * S.Δ ≤ P.H * S.Ω ^ 3 := reg_U5Δ_le S h1 hband hG1 hU1 hΔ1 hΩU
  -- ===== Piece bounds: each ≤ (1/8)|VTERM| =====
  -- The four brackets (= piece / K).
  set bB : ℝ := 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * b₀ ^ 2 / (d : ℝ) with hbB_def
  set bE1 : ℝ := 12 * |v| * ((a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v|) / (d : ℝ) with hbE1_def
  set bE2 : ℝ := 400 * |(ℓ₂ : ℝ) * b₀ + v| * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ^ 2 / (d : ℝ) ^ 2
    with hbE2_def
  set bE3 : ℝ := 400 * (ℓ₂ : ℝ) * |b₀| * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ^ 2 / (d : ℝ) ^ 2
    with hbE3_def
  -- piece = K · bracket
  have hℓ21pos : (0:ℝ) < (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by linarith [hℓ12R]
  have hBTERM_K : |BTERM| = K * bB := by
    rw [hBTERM_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < (d:ℝ) ^ 5), hK_def, hbB_def]
    rw [show (12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ) * b₀ ^ 2)
        = (12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))) * ((ℓ₁ : ℝ) * P.X * (a : ℝ)) * b₀ ^ 2 by ring,
      abs_mul, abs_mul,
      abs_of_pos (show (0:ℝ) < 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) by
        have : (0:ℝ) < 12 * (ℓ₂ : ℝ) := by positivity
        exact mul_pos this hℓ21pos),
      abs_of_pos (by positivity : (0:ℝ) < (ℓ₁ : ℝ) * P.X * (a : ℝ)), abs_of_nonneg (sq_nonneg b₀)]
    field_simp
  have hERR_K : ERR = K * (bE1 + bE2 + bE3) := by
    rw [hERR_def, hK_def, hbE1_def, hbE2_def, hbE3_def]; field_simp
  have hVTERM_K' : |VTERM| = K * (6 * |v|) := hVTERM_K
  -- ===== bracket bounds: each ≤ (3/4)·V₁ =====
  have hd1 : (0:ℝ) < (d : ℝ) := hd_pos
  have hdD2 : S.D ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ hDpos.le hdD 2
  have hMsq_nn : (0:ℝ) ≤ M := hM_pos.le
  -- common: D = HΔ
  have hSDeq : S.D = P.H * S.Δ := rfl
  -- bB ≤ (3/4)V₁
  -- master equality: V₁/10⁶⁵ = Δ³U¹⁰/(HΩ⁶)
  have hV1_65 : V₁ / 10 ^ 65 = S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6) := by
    rw [hV1_def]; field_simp
  have hV165_nn : (0:ℝ) ≤ V₁ / 10 ^ 65 := by rw [hV1_65]; positivity
  -- helper: const·(V₁/10⁶⁵) ≤ (3/4)·V₁ whenever const ≤ 3/4·10⁶⁵
  have hconst_le : ∀ c : ℝ, c ≤ 3 / 4 * 10 ^ 65 → c * (V₁ / 10 ^ 65) ≤ 3 / 4 * V₁ := by
    intro c hc
    calc c * (V₁ / 10 ^ 65) ≤ (3 / 4 * 10 ^ 65) * (V₁ / 10 ^ 65) :=
          mul_le_mul_of_nonneg_right hc hV165_nn
      _ = 3 / 4 * V₁ := by field_simp
  -- master equality: M²/D = V₁/10⁶⁵
  have hM2D : M ^ 2 / S.D = V₁ / 10 ^ 65 := by
    rw [hV1_65, hM_def, hSDeq]; field_simp
  -- bB ≤ (3/4)V₁  via  bB ≤ 1.08e26·(M²/D) = 1.08e26·(V₁/10⁶⁵)
  have hbB_le : bB ≤ 3 / 4 * V₁ := by
    rw [hbB_def]
    -- 12·ℓ₂(ℓ₂−ℓ₁)·b₀² ≤ 12·(GU⁵)²·(3e12·B)²  and  (GU⁵)²·B² = G²U¹⁰·B² ≤ 1.08e26·M²·(1/9e24)…
    -- cleaner: bound numerator ≤ 1.08e26·M², so bB ≤ 1.08e26·M²/D.
    have hnum : 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * b₀ ^ 2
        ≤ 1825200000000000000000000000000 * M ^ 2 := by
      have hℓfac : (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) ≤ 16900 * (P.G * P.U ^ 5) ^ 2 := by
        have e1 : (ℓ₂ : ℝ) - (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ2W', hℓ1R]
        have p2 : (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))
            = 16900 * (P.G * P.U ^ 5) ^ 2 := by ring
        rw [← p2]; exact mul_le_mul hℓ2W' e1 (by linarith [hℓ12R]) (by positivity)
      have hb0sq : b₀ ^ 2 ≤ (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg b₀) hb0' 2; rwa [sq_abs] at this
      have c1 : 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) ≤ 12 * (16900 * (P.G * P.U ^ 5) ^ 2) := by
        have heq : 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) = 12 * ((ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))) := by ring
        rw [heq]; linarith [mul_le_mul_of_nonneg_left hℓfac (by norm_num : (0:ℝ) ≤ 12)]
      have hstep : 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * b₀ ^ 2
          ≤ 12 * (16900 * (P.G * P.U ^ 5) ^ 2)
              * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) ^ 2 :=
        mul_le_mul c1 hb0sq (sq_nonneg b₀) (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      rw [hM_def]; field_simp; ring
    have hfr : 12 * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * b₀ ^ 2 / (d : ℝ)
        ≤ 1825200000000000000000000000000 * M ^ 2 / S.D :=
      div_le_div₀ (by positivity) hnum hDpos hdD
    refine le_trans hfr ?_
    rw [show 1825200000000000000000000000000 * M ^ 2 / S.D
        = 1825200000000000000000000000000 * (M ^ 2 / S.D) by ring, hM2D]
    exact hconst_le _ (by norm_num)
  -- bE1 ≤ (3/4)V₁  via bracket ≤ 24·10⁴⁰·M²  ⟹ ≤ 24e40·(M²/D) = 24e40·(V₁/10⁶⁵)
  have hbE1_le : bE1 ≤ 3 / 4 * V₁ := by
    rw [hbE1_def]
    have hnum : 12 * |v| * ((a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v|)
        ≤ 240000000000000000000000000000000000000000 * M ^ 2 := by
      have hstep : 12 * |v| * ((a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v|)
          ≤ 12 * (10 ^ 20 * M) * (2 * 10 ^ 20 * M) := by
        have s1 : 12 * |v| ≤ 12 * (10 ^ 20 * M) := by linarith [hv_M]
        exact mul_le_mul s1 hfac1 (by positivity) (by positivity)
      refine le_trans hstep (le_of_eq ?_); ring
    have hfr : 12 * |v| * ((a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v|) / (d : ℝ)
        ≤ 240000000000000000000000000000000000000000 * M ^ 2 / S.D :=
      div_le_div₀ (by positivity) hnum hDpos hdD
    refine le_trans hfr ?_
    rw [show (240000000000000000000000000000000000000000 : ℝ) * M ^ 2 / S.D
        = 240000000000000000000000000000000000000000 * (M ^ 2 / S.D) by ring, hM2D]
    exact hconst_le _ (by norm_num)
  -- master fact: M³/D² ≤ V₁/10⁶⁵   (using U⁵Δ ≤ HΩ³)
  have hM3D2 : M ^ 3 / S.D ^ 2 ≤ V₁ / 10 ^ 65 := by
    have heq : M ^ 3 / S.D ^ 2 = (P.U ^ 5 * S.Δ / (P.H * S.Ω ^ 3))
        * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) := by
      rw [hM_def, hSDeq]; field_simp
    have hV1eq : V₁ / 10 ^ 65 = S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6) := by
      rw [hV1_def]; field_simp
    rw [heq, hV1eq]
    have hrat : P.U ^ 5 * S.Δ / (P.H * S.Ω ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hreg
    have hbase_nn : (0:ℝ) ≤ S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6) := by positivity
    calc (P.U ^ 5 * S.Δ / (P.H * S.Ω ^ 3)) * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6))
        ≤ 1 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) :=
          mul_le_mul_of_nonneg_right hrat hbase_nn
      _ = S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6) := one_mul _
  have hV1_nn : (0:ℝ) ≤ V₁ := hV1_pos.le
  -- bE2 ≤ (3/4)V₁
  have hbE2_le : bE2 ≤ 3 / 4 * V₁ := by
    rw [hbE2_def]
    have hnum : 400 * |(ℓ₂ : ℝ) * b₀ + v| * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ^ 2
        ≤ 400 * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2 := by
      have s1 : 400 * |(ℓ₂ : ℝ) * b₀ + v| ≤ 400 * (2 * 10 ^ 20 * M) := by linarith [hℓ2b0v_M]
      have s2 : ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ^ 2 ≤ (3 * 10 ^ 20 * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfac2 2
      exact mul_le_mul s1 s2 (by positivity) (by positivity)
    have hfr : 400 * |(ℓ₂ : ℝ) * b₀ + v| * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ^ 2 / (d : ℝ) ^ 2
        ≤ 400 * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2 / S.D ^ 2 :=
      div_le_div₀ (by positivity) hnum (by positivity) hdD2
    refine le_trans hfr ?_
    have hcl : 400 * (2 * 10 ^ 20 * M) * (3 * 10 ^ 20 * M) ^ 2 / S.D ^ 2
        = 7200000000000000000000000000000000000000000000000000000000000000 * (M ^ 3 / S.D ^ 2) := by
      ring
    rw [hcl]
    exact le_trans (mul_le_mul_of_nonneg_left hM3D2 (by norm_num)) (hconst_le _ (by norm_num))
  -- bE3 ≤ (3/4)V₁
  have hbE3_le : bE3 ≤ 3 / 4 * V₁ := by
    rw [hbE3_def]
    have hnum : 400 * (ℓ₂ : ℝ) * |b₀| * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ^ 2
        ≤ 400 * (390000000000000 * M) * (400000000000000 * M) ^ 2 := by
      have s1 : 400 * (ℓ₂ : ℝ) * |b₀| ≤ 400 * (390000000000000 * M) := by
        have : 400 * (ℓ₂ : ℝ) * |b₀| = 400 * ((ℓ₂ : ℝ) * |b₀|) := by ring
        rw [this]; linarith [hℓ2b0_M]
      have s2 : ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ^ 2 ≤ (400000000000000 * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfac3 2
      exact mul_le_mul s1 s2 (by positivity) (by positivity)
    have hfr : 400 * (ℓ₂ : ℝ) * |b₀| * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ^ 2 / (d : ℝ) ^ 2
        ≤ 400 * (390000000000000 * M) * (400000000000000 * M) ^ 2 / S.D ^ 2 :=
      div_le_div₀ (by positivity) hnum (by positivity) hdD2
    refine le_trans hfr ?_
    have hcl : 400 * (390000000000000 * M) * (400000000000000 * M) ^ 2 / S.D ^ 2
        = 24960000000000000000000000000000000000000000000 * (M ^ 3 / S.D ^ 2) := by ring
    rw [hcl]
    exact le_trans (mul_le_mul_of_nonneg_left hM3D2 (by norm_num)) (hconst_le _ (by norm_num))
  -- ===== assemble: |BTERM| + ERR = K·(bB+bE1+bE2+bE3) ≤ K·3V₁ ≤ K·3|v| = (1/2)|VTERM| =====
  have hbrk : bB + (bE1 + bE2 + bE3) ≤ 3 * |v| := by
    have hsum : bB + (bE1 + bE2 + bE3) ≤ 3 * V₁ := by
      linarith [hbB_le, hbE1_le, hbE2_le, hbE3_le]
    linarith [hsum, hv1]
  have hBE_K : |BTERM| + ERR = K * (bB + (bE1 + bE2 + bE3)) := by
    rw [hBTERM_K, hERR_K]; ring
  have hBE_half : |BTERM| + ERR ≤ 1 / 2 * |VTERM| := by
    rw [hBE_K, hVTERM_K']
    have : K * (bB + (bE1 + bE2 + bE3)) ≤ K * (3 * |v|) :=
      mul_le_mul_of_nonneg_left hbrk hK_pos.le
    rw [show (1:ℝ)/2 * (K * (6 * |v|)) = K * (3 * |v|) by ring]
    exact this
  -- |𝒬| ≥ (1/2)|VTERM|
  have hQge : 1 / 2 * |VTERM| ≤ |𝒬| := by linarith [hrev, hBE_half]
  -- ===== lower bound on (1/2)|VTERM| =====
  -- (1/2)|VTERM| = 3ℓ₁Xa|v|/d⁴ ≥ 3ℓ₁X(A/5)V₁/(2D)⁴
  have hVlb : 10 ^ 55 * ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) / (P.G * S.Ω ^ 5)) + 1 / 2
      ≤ 1 / 2 * |VTERM| := by
    rw [hVTERM_K', hK_def]
    -- 1/2 * (ℓ₁Xa/d⁴ * 6|v|) = 3ℓ₁Xa|v|/d⁴
    have hVval : 1 / 2 * ((ℓ₁ : ℝ) * P.X * (a : ℝ) / (d : ℝ) ^ 4 * (6 * |v|))
        = 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * |v| / (d : ℝ) ^ 4 := by field_simp; ring
    rw [hVval]
    -- lower bound the v-term: a ≥ A/5, |v| > V₁, d ≤ 2D
    have ha_lo5 : S.A / 5 ≤ (a : ℝ) := ha_lo
    have hd2D : (d : ℝ) ≤ 2 * S.D := hdwin.2
    have hd4 : (d : ℝ) ^ 4 ≤ (2 * S.D) ^ 4 := pow_le_pow_left₀ hd_pos.le hd2D 4
    -- numerator ≥ 3ℓ₁X(A/5)V₁, denom ≤ (2D)⁴
    have hnum_lo : 3 * (ℓ₁ : ℝ) * P.X * (S.A / 5) * V₁
        ≤ 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * |v| := by
      have h1' : 3 * (ℓ₁ : ℝ) * P.X * (S.A / 5) ≤ 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) :=
        mul_le_mul_of_nonneg_left ha_lo5 (by positivity)
      have h2' : 3 * (ℓ₁ : ℝ) * P.X * (S.A / 5) * V₁ ≤ 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * V₁ :=
        mul_le_mul_of_nonneg_right h1' hV1_nn
      have h3' : 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * V₁ ≤ 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * |v| :=
        mul_le_mul_of_nonneg_left hv1.le (by positivity)
      linarith [h2', h3']
    have hfrac_lo : 3 * (ℓ₁ : ℝ) * P.X * (S.A / 5) * V₁ / (2 * S.D) ^ 4
        ≤ 3 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * |v| / (d : ℝ) ^ 4 := by
      apply div_le_div₀ (by positivity) hnum_lo (by positivity) hd4
    refine le_trans ?_ hfrac_lo
    -- evaluate 3ℓ₁X(A/5)V₁/(2D)⁴  =  3/(5·16)·ℓ₁·(XA/D⁴)·V₁
    -- XA/D⁴ = HGΩ/Δ³, V₁ = 10⁶⁵Δ³U¹⁰/(HΩ⁶) ⟹ = (3/80)·10⁶⁵·ℓ₁·GU¹⁰/Ω⁵
    have hXAD4 : P.X * S.A / S.D ^ 4 = P.H * P.G * S.Ω / S.Δ ^ 3 := by
      unfold Scale.A Scale.D; rw [P.X_eq_G_mul_H_pow_five]; field_simp
    have hval : 3 * (ℓ₁ : ℝ) * P.X * (S.A / 5) * V₁ / (2 * S.D) ^ 4
        = (3 / (5 * 16)) * (ℓ₁ : ℝ) * (P.X * S.A / S.D ^ 4) * V₁ := by
      rw [hV1_def, hSDeq]; field_simp; ring
    rw [hval, hXAD4, hV1_def]
    -- (3/80)·ℓ₁·(HGΩ/Δ³)·10⁶⁵·Δ³U¹⁰/(HΩ⁶) = (3/80·10⁶⁵)·ℓ₁·GU¹⁰/Ω⁵
    have hcollapse : (3 / (5 * 16)) * (ℓ₁ : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3)
          * (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)))
        = (3 / 80 * 10 ^ 65) * ((ℓ₁ : ℝ) * (P.G * P.U ^ 10 / S.Ω ^ 5)) := by
      field_simp; ring
    rw [hcollapse]
    have hℓ1geR : (1:ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
    exact vterm_numeric S hℓ1geR hℓ12R hℓ2W' hG1 hU1 hΩU
  linarith [hQge, hVlb]

end Squarefree
