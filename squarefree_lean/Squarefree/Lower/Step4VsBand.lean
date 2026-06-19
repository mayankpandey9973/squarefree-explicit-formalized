import Squarefree.Lower.Step4SsumAdd
import Squarefree.Lower.Step4Cref

/-!
# §5 Step-4 V_s band bridge + per-fibre additive count (writeup 1058–1124)

This file supplies the last analytic input for the Step-4 capstone: the three scale-algebra /
factorization steps that turn the green two-point square-difference data into the per-`s`-fibre
additive count `(Rng.filter (sOf = n)).card ≤ K · weight4add b ev dc cE n` consumed by
`ra_step4_range_add` (`Step4RangeAdd.lean`).

## The three steps

* **`Vs_pin`** — the `V_s` two-sided pin.  From the single-point perturbation bound
  `|Σ_closed − Ĉ·v²| ≤ E` (`Sigma_closed_diff_Cref_le`, with `Ĉ = Cref·(A/a)²·ℓ₁²`) and the
  near-integer budget `|Σ_closed − s| ≤ err` (`step4_fiber_extract_err`), in the regime
  `E + err ≤ ½|s|`, the reverse triangle inequality pins `Ĉ·v² ≍ |s|`:

    `½|s| ≤ Ĉ·v² ≤ (3/2)|s|`.

  Since `Ĉ·a² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)` (because `Cref·A² = 3ℓ₁ℓ₂(ℓ₂−ℓ₁)`, `A² = Δ²Ω²`) and
  `a ∈ [A/5, 11A]`, this is the squared two-sided pin

    `(1/150)·Δ²Ω²|s| ≤ ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v² ≤ 10⁶·Δ²Ω²|s|`

  — exactly the `hvpin_hi` hypothesis (`≤ 10⁶·Δ²Ω²|s|`) that `Step4_E_le_rho_s` /
  `Sigma_closed_diff_Cref_le` consume, discharged here (the sharp constant is `121/2 ≤ 10⁶`).

* **`band_collapse`** — the band shape.  With `Vlo` the pin (`c₀·n ≤ Ĉ·Vlo²`), the kernel v-count
  variable part `2ℓ₁·diam2/Vlo` (`diam2 = (4·err + 2·E0)/Ĉ`, from `step4_sqdiff_diam2_hyb`) collapses to

    `2ℓ₁·diam2/Vlo ≤ ev/√n + cE·√n`,
    `ev = 8ℓ₁·err/(√c₀·√Ĉ)`,   `cE = 4ℓ₁·E0/(√c₀·√Ĉ)`,

  the err-part landing the sharp `1/√n` band and the (n-independent) `E0`-part routed through the
  crude `1/√n ≤ √n` (the additive `√n` room).

* **`vsum_le_weight4add`** — the fibrewise factorization (additive analogue of `vsum_le_weight4'`):
  v-count `vc ≤ 2 + ev/√n + cE√n` times per-`(s,v)` count `Cv ≤ K_C·(b + dc/√n)` gives
  `vc·Cv ≤ K_C·weight4add b ev dc cE n`.
-/

open Real

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 `V_s` two-sided pin (writeup 1108–1124).**  From the single-point perturbation
bound `|Σ_closed − Ĉ·v²| ≤ E` and the near-integer budget `|Σ_closed − s| ≤ err`, in the regime
`E + err ≤ ½|s|`, the closed-form leading term `Ĉ·v²` (`Ĉ = Cref·(A/a)²·ℓ₁²`) is pinned two-sidedly
to `|s|`, equivalently (via `Ĉ·a² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)` and `a ∈ [A/5,11A]`) the squared pins
`hvpin_lo`/`hvpin_hi`.  The `hvpin_hi` constant `10⁶` (sharp `121/2`) is exactly the form
`Step4_E_le_rho_s` consumes. -/
theorem Vs_pin {a v E err : ℝ} {ℓ₁ ℓ₂ : ℝ} {s : ℤ} {Sc : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hpert : |Sc - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2| ≤ E)
    (herr : |Sc - (s : ℝ)| ≤ err)
    (hreg : E + err ≤ (1 / 2 : ℝ) * |(s : ℝ)|) :
    (1 / 2 : ℝ) * |(s : ℝ)| ≤ (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2
    ∧ (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2 ≤ (3 / 2 : ℝ) * |(s : ℝ)|
    ∧ (1 / 150 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2
    ∧ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|) := by
  have hΔpos := S.Δ_pos
  have hΩpos := S.Ω_pos
  have hApos : 0 < S.A := by rw [show S.A = S.Δ * S.Ω from rfl]; positivity
  have hΔne : S.Δ ≠ 0 := hΔpos.ne'
  have hΩne : S.Ω ≠ 0 := hΩpos.ne'
  have hane : a ≠ 0 := ha0.ne'
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hCrefpos := Cref_pos (P := P) (S := S) hℓ1R hℓ12
  have hsnn : (0 : ℝ) ≤ |(s : ℝ)| := abs_nonneg _
  set Ĉ : ℝ := Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2 with hĈdef
  have hĈnn0 : 0 ≤ Ĉ := by
    rw [hĈdef]; exact mul_nonneg (mul_nonneg hCrefpos.le (sq_nonneg _)) (sq_nonneg _)
  have hĈnn : 0 ≤ Ĉ * v ^ 2 := mul_nonneg hĈnn0 (sq_nonneg v)
  -- |Ĉv² − s| ≤ E + err
  have hpert' : |Ĉ * v ^ 2 - Sc| ≤ E := by rw [abs_sub_comm]; exact hpert
  have key : |Ĉ * v ^ 2 - (s : ℝ)| ≤ E + err := by
    have h := abs_add_le (Ĉ * v ^ 2 - Sc) (Sc - (s : ℝ))
    rw [show Ĉ * v ^ 2 - (s : ℝ) = (Ĉ * v ^ 2 - Sc) + (Sc - (s : ℝ)) by ring]
    exact le_trans h (add_le_add hpert' herr)
  -- reverse triangle: |Ĉv² − |s|| ≤ |Ĉv² − s| ≤ E + err ≤ ½|s|
  have hrev : abs (Ĉ * v ^ 2 - |(s : ℝ)|) ≤ E + err := by
    have hstep : abs (Ĉ * v ^ 2 - |(s : ℝ)|) = abs (|Ĉ * v ^ 2| - |(s : ℝ)|) := by
      rw [abs_of_nonneg hĈnn]
    rw [hstep]
    exact le_trans (abs_abs_sub_abs_le_abs_sub _ _) key
  have hbnd := abs_le.mp hrev
  have hCv2_lo : (1 / 2 : ℝ) * |(s : ℝ)| ≤ Ĉ * v ^ 2 := by linarith [hbnd.1, hreg]
  have hCv2_hi : Ĉ * v ^ 2 ≤ (3 / 2 : ℝ) * |(s : ℝ)| := by linarith [hbnd.2, hreg]
  -- Ĉ·a² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)
  have hCa2 : Ĉ * a ^ 2 = 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) := by
    rw [hĈdef, show S.A = S.Δ * S.Ω from rfl,
      show Cref P S ℓ₁ ℓ₂ = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (S.Δ ^ 2 * S.Ω ^ 2) from rfl]
    field_simp
  have hkeyeq : Ĉ * v ^ 2 * a ^ 2 = 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 := by
    linear_combination v ^ 2 * hCa2
  -- a² window: Δ²Ω²/25 ≤ a² ≤ 121Δ²Ω²
  have hAsq : S.A ^ 2 = S.Δ ^ 2 * S.Ω ^ 2 := by rw [show S.A = S.Δ * S.Ω from rfl]; ring
  have ha2lo : S.Δ ^ 2 * S.Ω ^ 2 / 25 ≤ a ^ 2 := by
    nlinarith [pow_le_pow_left₀ (div_nonneg hApos.le (by norm_num : (0:ℝ) ≤ 5)) ha_lo 2, hAsq]
  have ha2hi : a ^ 2 ≤ 121 * (S.Δ ^ 2 * S.Ω ^ 2) := by
    nlinarith [pow_le_pow_left₀ ha0.le ha_hi 2, hAsq]
  -- squared pins
  have hlo : (1 / 150 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 := by
    have h1 : (1 / 2 : ℝ) * |(s : ℝ)| * a ^ 2 ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hCv2_lo (sq_nonneg a)
      rwa [hkeyeq] at hm
    nlinarith [h1, mul_le_mul_of_nonneg_left ha2lo hsnn]
  have hhi : ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)|) := by
    have h2 : 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 ≤ (3 / 2 : ℝ) * |(s : ℝ)| * a ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hCv2_hi (sq_nonneg a)
      rwa [hkeyeq] at hm
    nlinarith [h2, mul_le_mul_of_nonneg_left ha2hi hsnn]
  exact ⟨hCv2_lo, hCv2_hi, hlo, hhi⟩

/-- **§5 Step-4 band collapse (writeup 1108–1124).**  With the pin `c₀·n ≤ Ĉ·Vlo²` (so
`Vlo ≥ √(c₀n/Ĉ) ≍ V_s`), the kernel v-count variable part `2ℓ₁·diam2/Vlo`
(`diam2 = (4·err + 2·E0)/Ĉ`, `step4_sqdiff_diam2_hyb`) is bounded by the additive band shape
`ev/√n + cE·√n` with `ev = 8ℓ₁·err/(√c₀·√Ĉ)` (the sharp `1/√n` band) and
`cE = 4ℓ₁·E0/(√c₀·√Ĉ)` (the `E0`-room, via `1/√n ≤ √n`). -/
theorem band_collapse {ℓ₁ Ĉ Vlo err E0 c₀ n : ℝ}
    (hℓ1 : 0 < ℓ₁) (hĈ : 0 < Ĉ) (hVlo : 0 < Vlo) (hc0 : 0 < c₀)
    (hn1 : 1 ≤ n) (herr0 : 0 ≤ err) (hE00 : 0 ≤ E0)
    (hpin : c₀ * n ≤ Ĉ * Vlo ^ 2) :
    2 * ℓ₁ * ((4 * err + 2 * E0) / Ĉ) / Vlo
      ≤ (8 * ℓ₁ * err / (Real.sqrt c₀ * Real.sqrt Ĉ)) / Real.sqrt n
        + (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) * Real.sqrt n := by
  have hnpos : 0 < n := lt_of_lt_of_le one_pos hn1
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsc_pos : 0 < Real.sqrt c₀ := Real.sqrt_pos.mpr hc0
  have hsĈ_pos : 0 < Real.sqrt Ĉ := Real.sqrt_pos.mpr hĈ
  have hĈVlo_pos : 0 < Ĉ * Vlo := mul_pos hĈ hVlo
  have hDpos : 0 < Real.sqrt Ĉ * Real.sqrt c₀ * Real.sqrt n := by positivity
  have hnum_nn : 0 ≤ 2 * ℓ₁ * (4 * err + 2 * E0) := by positivity
  -- lower bound on the denominator: √Ĉ·√c₀·√n ≤ Ĉ·Vlo
  have hsq : Ĉ * c₀ * n ≤ (Ĉ * Vlo) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hpin hĈ.le]
  have hDle : Real.sqrt Ĉ * Real.sqrt c₀ * Real.sqrt n ≤ Ĉ * Vlo := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hĈVlo_pos.le] at h
    rwa [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Ĉ * c₀) n, Real.sqrt_mul hĈ.le c₀] at h
  -- 1/√n ≤ √n  (since n ≥ 1)
  have hsn_ge1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hn1
  have hinv : 1 / Real.sqrt n ≤ Real.sqrt n := by
    rw [div_le_iff₀ hsn_pos]; nlinarith [hsn_ge1]
  -- the E0-room: cE/√n ≤ cE·√n
  have hcEnn : 0 ≤ 4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ) := by positivity
  have hstep4 : (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) / Real.sqrt n
      ≤ (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) * Real.sqrt n := by
    have heq : (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) / Real.sqrt n
        = (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) * (1 / Real.sqrt n) := by ring
    rw [heq]; exact mul_le_mul_of_nonneg_left hinv hcEnn
  calc 2 * ℓ₁ * ((4 * err + 2 * E0) / Ĉ) / Vlo
      = (2 * ℓ₁ * (4 * err + 2 * E0)) / (Ĉ * Vlo) := by rw [mul_div_assoc', div_div]
    _ ≤ (2 * ℓ₁ * (4 * err + 2 * E0)) / (Real.sqrt Ĉ * Real.sqrt c₀ * Real.sqrt n) :=
        div_le_div_of_nonneg_left hnum_nn hDpos hDle
    _ = (8 * ℓ₁ * err / (Real.sqrt c₀ * Real.sqrt Ĉ)) / Real.sqrt n
          + (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) / Real.sqrt n := by
        field_simp; ring
    _ ≤ (8 * ℓ₁ * err / (Real.sqrt c₀ * Real.sqrt Ĉ)) / Real.sqrt n
          + (4 * ℓ₁ * E0 / (Real.sqrt c₀ * Real.sqrt Ĉ)) * Real.sqrt n := by
        linarith [hstep4]

/-- **§5 Step-4 per-fibre additive factorization (additive analogue of `vsum_le_weight4'`).**  The
v-count `vc ≤ 2 + ev/√n + cE·√n` (band-widened, from `sqdiff_band_card_le` + `band_collapse`) times
the per-`(s,v)` count `Cv ≤ K_C·(b + dc/√n)` (`step4_hperv`) gives the per-`s`-fibre additive count
`vc·Cv ≤ K_C·weight4add b ev dc cE n`. -/
theorem vsum_le_weight4add {K_C vc Cv b ev dc cE n : ℝ}
    (hKC : 0 ≤ K_C) (hb : 0 ≤ b) (hdc : 0 ≤ dc)
    (hvc_nn : 0 ≤ vc)
    (hvc : vc ≤ 2 + ev / Real.sqrt n + cE * Real.sqrt n)
    (hCcol : Cv ≤ K_C * (b + dc / Real.sqrt n)) :
    vc * Cv ≤ K_C * weight4add b ev dc cE n := by
  rw [weight4add]
  have hsqrt_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hbase_nn : 0 ≤ b + dc / Real.sqrt n := by positivity
  have hRHS_nn : 0 ≤ K_C * (b + dc / Real.sqrt n) := mul_nonneg hKC hbase_nn
  calc vc * Cv
      ≤ vc * (K_C * (b + dc / Real.sqrt n)) := mul_le_mul_of_nonneg_left hCcol hvc_nn
    _ ≤ (2 + ev / Real.sqrt n + cE * Real.sqrt n) * (K_C * (b + dc / Real.sqrt n)) :=
        mul_le_mul_of_nonneg_right hvc hRHS_nn
    _ = K_C * ((2 + ev / Real.sqrt n + cE * Real.sqrt n) * (b + dc / Real.sqrt n)) := by ring

/-! ## Fibre-local v-box

The pin `Vs_pin` confines `v` to the box `|v| ≤ Vbox S ℓ₁ ℓ₂ |s|` with
`Vbox = 1000·Δ·Ω·√(n/L₃)`, `L₃ = ℓ₁³ℓ₂(ℓ₂−ℓ₁)` — the square root of the `hvpin_hi` conjunct.
Downstream consumes `Vbox²` (exact) and the cube split `Vbox³ = (10⁹Δ³Ω³/L₃)·√(n/L₃)·n`. -/

/-- The fibre-local v-box radius extracted from the `Vs_pin` upper conjunct:
`Vbox = 1000·Δ·Ω·√(n / (ℓ₁³ℓ₂(ℓ₂−ℓ₁)))`. -/
noncomputable def Vbox (S : Scale P) (ℓ₁ ℓ₂ : ℝ) (n : ℝ) : ℝ :=
  1000 * S.Δ * S.Ω * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))

theorem Vbox_nonneg {ℓ₁ ℓ₂ n : ℝ} : 0 ≤ Vbox S ℓ₁ ℓ₂ n := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Vbox
  positivity

private theorem L3_pos {ℓ₁ ℓ₂ : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    (0 : ℝ) < ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) := by
  have hℓ1R : (0 : ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  exact mul_pos (mul_pos (pow_pos hℓ1R 3) (hℓ1R.trans hℓ12)) (sub_pos.mpr hℓ12)

/-- Exact square of the v-box: `Vbox² = 10⁶·Δ²Ω²·n / (ℓ₁³ℓ₂(ℓ₂−ℓ₁))`. -/
theorem Vbox_sq {ℓ₁ ℓ₂ n : ℝ} (hn : 0 ≤ n) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    (Vbox S ℓ₁ ℓ₂ n) ^ 2 = 10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2 * n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) := by
  have hL3 := L3_pos hℓ1 hℓ12
  have hx : 0 ≤ n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) := div_nonneg hn hL3.le
  unfold Vbox
  rw [show (1000 * S.Δ * S.Ω * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))) ^ 2
      = 1000 ^ 2 * S.Δ ^ 2 * S.Ω ^ 2 * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁))) ^ 2 by ring,
    Real.sq_sqrt hx, show ((10 : ℝ)) ^ 6 = 1000 ^ 2 by norm_num]
  ring

/-- **Fibre-local v-box from the pin (writeup 1108–1124).**  Under the `Vs_pin` hypotheses, the
fourth conjunct `ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v² ≤ 10⁶·Δ²Ω²|s|` is exactly `v² ≤ Vbox²`, so `|v| ≤ Vbox S ℓ₁ ℓ₂ |s|`. -/
theorem vbox_of_pin {a v E err : ℝ} {ℓ₁ ℓ₂ : ℝ} {s : ℤ} {Sc : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hpert : |Sc - (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2| ≤ E)
    (herr : |Sc - (s : ℝ)| ≤ err)
    (hreg : E + err ≤ (1 / 2 : ℝ) * |(s : ℝ)|) :
    |v| ≤ Vbox S ℓ₁ ℓ₂ |(s : ℝ)| := by
  obtain ⟨-, -, -, h4⟩ := Vs_pin (S := S) ha0 ha_lo ha_hi hℓ1 hℓ12 hpert herr hreg
  have hL3 := L3_pos hℓ1 hℓ12
  have hsq : v ^ 2 ≤ Vbox S ℓ₁ ℓ₂ |(s : ℝ)| ^ 2 := by
    rw [Vbox_sq (abs_nonneg _) hℓ1 hℓ12, le_div_iff₀ hL3]
    nlinarith [h4]
  calc |v| = Real.sqrt (v ^ 2) := (Real.sqrt_sq_eq_abs v).symm
    _ ≤ Real.sqrt (Vbox S ℓ₁ ℓ₂ |(s : ℝ)| ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Vbox S ℓ₁ ℓ₂ |(s : ℝ)| := Real.sqrt_sq Vbox_nonneg

/-- Cube split of the v-box (in the quotient-friendly shape):
`Vbox³ ≤ (10⁹·Δ³Ω³ / L₃) · √(n/L₃) · n` with `L₃ = ℓ₁³ℓ₂(ℓ₂−ℓ₁)` (an equality, proved as `≤`). -/
theorem Vbox_cube_div_sqrt_le {ℓ₁ ℓ₂ n : ℝ} (hn : 0 ≤ n) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    (Vbox S ℓ₁ ℓ₂ n) ^ 3
      ≤ (10 ^ 9 * S.Δ ^ 3 * S.Ω ^ 3 / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))
          * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁))) * n := by
  have hL3 := L3_pos hℓ1 hℓ12
  have hx : 0 ≤ n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) := div_nonneg hn hL3.le
  have hcube : Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁))) ^ 3
      = n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁))) := by
    linear_combination Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁))) * Real.sq_sqrt hx
  unfold Vbox
  refine le_of_eq ?_
  rw [show (1000 * S.Δ * S.Ω * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))) ^ 3
      = 1000 ^ 3 * S.Δ ^ 3 * S.Ω ^ 3 * Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁))) ^ 3 by ring,
    hcube, show ((10 : ℝ)) ^ 9 = 1000 ^ 3 by norm_num]
  ring

/-- Monotonicity of the v-box in the fibre variable `n`. -/
theorem Vbox_mono {ℓ₁ ℓ₂ n m : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hnm : n ≤ m) :
    Vbox S ℓ₁ ℓ₂ n ≤ Vbox S ℓ₁ ℓ₂ m := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hL3 := L3_pos hℓ1 hℓ12
  unfold Vbox
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnm (inv_nonneg.mpr hL3.le)

end Squarefree
