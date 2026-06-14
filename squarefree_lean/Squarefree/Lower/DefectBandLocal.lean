import Squarefree.Lower.DefectDeriv
import Squarefree.Lower.DefectRegime

/-!
# §5 band-local (fixed-`a`) scale bounds for `d̃ₐ(r)` and `d̃ₐ'(r)`

The §5 bounds in `DefectBounds` (`dtilde_d1_bounds`, `dtilde_asymp_D`) are deliberately loose:
they cover the FULL parameter range (`a ∈ [A/5, 11A]`, `r ∈ [R/72, 16R]`), which contributes a
huge `a^{3/2}` / `r^{±}` swing.  In the Step-2 bands count, however, **`a` is FIXED** and `r`
ranges over a single band `[r₀, r₁] ⊆ [S.R, 3 S.R]`.  Over such a band the defect inverse and
its derivative vary only by an **absolute** `O(1)` factor.

This file proves, for fixed `a` in the §5 window and `r, r' ∈ [r₀, r₁]` with `S.R ≤ r₀` and
`r₁ ≤ 3 S.R`:

* `dtilde_ratio_band`   : `(1/4) ≤ d̃ₐ(r) / d̃ₐ(r') ≤ 4`   (true factor `≤ 2`).
* `dtilde_d1_ratio_band`: `(1/64) ≤ |d̃ₐ'(r)| / |d̃ₐ'(r')| ≤ 64`.

The constants are ABSOLUTE — no `10⁶`-style blow-up.  The mechanism is the product identity
`d̃(d̃+a) = √(X a³/r)` (`dtilde_prod`), whose right side varies only by `√(r'/r) ∈ [1/√3, √3]`
over the band; this controls the root `d̃`, and then the closed-form derivative
`|d̃'| = d̃(d̃+a)/(2 r (a + 2 d̃))` is controlled factor-by-factor.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **Band-local root comparison.**  If `d, d' > 0`, `a > 0` solve `d(d+a) = w`,
`d'(d'+a) = w'` and `w ≤ 2 w'`, then `d ≤ 2 d'`.  (No use of the absolute scales.) -/
private theorem root_le_of_prod_le {a d d' w w' : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hd' : 0 < d')
    (hprod : d * (d + a) = w) (hprod' : d' * (d' + a) = w')
    (hww : w ≤ 2 * w') : d ≤ 2 * d' := by
  -- Two cases on the ordering of `d, d'`.
  rcases le_or_gt d d' with h | h
  · linarith
  · -- `d > d'`, so `d' + a ≤ d + a`; hence `d(d+a) = w ≤ 2 w' = 2 d'(d'+a) ≤ 2 d'(d+a)`,
    -- giving `d ≤ 2 d'` after dividing by `d + a > 0`.
    have hda : 0 < d + a := by linarith
    have hkey : d * (d + a) ≤ 2 * d' * (d + a) := by
      rw [hprod]
      calc w ≤ 2 * w' := hww
        _ = 2 * (d' * (d' + a)) := by rw [hprod']
        _ ≤ 2 * (d' * (d + a)) := by nlinarith [hd'.le]
        _ = 2 * d' * (d + a) := by ring
    have := le_of_mul_le_mul_right hkey hda
    linarith

/-- **Band-local ratio bound for `d̃ₐ(r)`** (`d̃` varies by ≤ `4×` — true factor ≤ 2).

For fixed `a` in the §5 window and `r, r' ∈ [r₀, r₁]` with `S.R ≤ r₀` and `r₁ ≤ 3 S.R`,

  `(1/4) ≤ d̃ₐ(r) / d̃ₐ(r') ≤ 4`. -/
theorem dtilde_ratio_band {P : Globals} {S : Scale P} {a r r' r₀ r₁ : ℝ}
    (ha0 : 0 < a)
    (hR_lo : S.R ≤ r₀) (hr1_hi : r₁ ≤ 3 * S.R)
    (hr_mem : r ∈ Set.Icc r₀ r₁) (hr'_mem : r' ∈ Set.Icc r₀ r₁) :
    (1 / 4 : ℝ) ≤ dtilde P.X r a / dtilde P.X r' a
      ∧ dtilde P.X r a / dtilde P.X r' a ≤ 4 := by
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  obtain ⟨hr_lo, hr_hi⟩ := hr_mem
  obtain ⟨hr'_lo, hr'_hi⟩ := hr'_mem
  -- band positivity and the `r/r' ≤ 3`, `r'/r ≤ 3` structure
  have hr0pos : 0 < r₀ := lt_of_lt_of_le hRpos hR_lo
  have hrpos : 0 < r := lt_of_lt_of_le hr0pos hr_lo
  have hr'pos : 0 < r' := lt_of_lt_of_le hr0pos hr'_lo
  have hr1pos : 0 < r₁ := lt_of_lt_of_le hrpos hr_hi
  -- `r ≤ 3 r'` and `r' ≤ 3 r`  (both via `r, r' ∈ [r₀, r₁] ⊆ [r₀, 3 r₀]`, `r₀ ≥ S.R`)
  have hr_le_3r' : r ≤ 3 * r' := by
    have : r₁ ≤ 3 * r₀ := by linarith
    linarith
  have hr'_le_3r : r' ≤ 3 * r := by
    have : r₁ ≤ 3 * r₀ := by linarith
    linarith
  -- closed-form roots and the product identity
  set d := dtilde P.X r a with hd_def
  set d' := dtilde P.X r' a with hd'_def
  have hdpos : 0 < d := dtilde_pos P.X_pos ha0 hrpos
  have hd'pos : 0 < d' := dtilde_pos P.X_pos ha0 hr'pos
  set w := Real.sqrt (P.X * a ^ 3 / r) with hw_def
  set w' := Real.sqrt (P.X * a ^ 3 / r') with hw'_def
  have hprod : d * (d + a) = w := dtilde_prod P.X_pos ha0 hrpos
  have hprod' : d' * (d' + a) = w' := dtilde_prod P.X_pos ha0 hr'pos
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw'pos : 0 < w' := Real.sqrt_pos.mpr (by positivity)
  have hwsq : w ^ 2 = P.X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  have hw'sq : w' ^ 2 = P.X * a ^ 3 / r' := Real.sq_sqrt (by positivity)
  -- `w² ≤ 3 w'²`  (since `Xa³/r ≤ 3 · Xa³/r'` ⟺ `r' ≤ 3 r`)
  have hXa3 : 0 < P.X * a ^ 3 := by have := P.X_pos; positivity
  have hw2_le : w ^ 2 ≤ 3 * w' ^ 2 := by
    rw [hwsq, hw'sq]
    rw [div_le_iff₀ hrpos, mul_comm (3 : ℝ), mul_assoc, div_mul_eq_mul_div,
      le_div_iff₀ hr'pos]
    nlinarith [hXa3, hr'_le_3r]
  have hw'2_le : w' ^ 2 ≤ 3 * w ^ 2 := by
    rw [hwsq, hw'sq]
    rw [div_le_iff₀ hr'pos, mul_comm (3 : ℝ), mul_assoc, div_mul_eq_mul_div,
      le_div_iff₀ hrpos]
    nlinarith [hXa3, hr_le_3r']
  -- hence `w ≤ 2 w'` and `w' ≤ 2 w`  (from `w² ≤ 3 w'² ≤ 4 w'²`, both nonneg)
  have hww : w ≤ 2 * w' := by nlinarith [hw2_le, hwpos, hw'pos]
  have hw'w : w' ≤ 2 * w := by nlinarith [hw'2_le, hwpos, hw'pos]
  -- root comparison both ways
  have hd_le : d ≤ 2 * d' := root_le_of_prod_le ha0 hdpos hd'pos hprod hprod' hww
  have hd'_le : d' ≤ 2 * d := root_le_of_prod_le ha0 hd'pos hdpos hprod' hprod hw'w
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hd'pos]; linarith
  · rw [div_le_iff₀ hd'pos]; linarith

/-- **Band-local ratio bound for `|d̃ₐ'(r)|`** (the key Step-2 estimate).

For fixed `a` in the §5 window and `r, r' ∈ [r₀, r₁]` with `S.R ≤ r₀` and `r₁ ≤ 3 S.R`,

  `(1/64) ≤ |d̃ₐ'(r)| / |d̃ₐ'(r')| ≤ 64`.

Over the band `|d̃ₐ'|` varies by an ABSOLUTE `O(1)` factor (≤ 64), NOT `10⁶`.  Uses the closed
form `|d̃'(r)| = d̃(d̃+a)/(2 r (a + 2 d̃))` and the band ratio of `d̃` from `dtilde_ratio_band`. -/
theorem dtilde_d1_ratio_band {P : Globals} {S : Scale P} {a r r' r₀ r₁ : ℝ}
    (ha0 : 0 < a)
    (hR_lo : S.R ≤ r₀) (hr1_hi : r₁ ≤ 3 * S.R)
    (hr_mem : r ∈ Set.Icc r₀ r₁) (hr'_mem : r' ∈ Set.Icc r₀ r₁) :
    (1 / 64 : ℝ) ≤ |deriv (fun s => dtilde P.X s a) r| / |deriv (fun s => dtilde P.X s a) r'|
      ∧ |deriv (fun s => dtilde P.X s a) r| / |deriv (fun s => dtilde P.X s a) r'| ≤ 64 := by
  have hXpos : 0 < P.X := P.X_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  obtain ⟨hr_lo, hr_hi⟩ := hr_mem
  obtain ⟨hr'_lo, hr'_hi⟩ := hr'_mem
  have hr0pos : 0 < r₀ := lt_of_lt_of_le hRpos hR_lo
  have hrpos : 0 < r := lt_of_lt_of_le hr0pos hr_lo
  have hr'pos : 0 < r' := lt_of_lt_of_le hr0pos hr'_lo
  -- `r ≤ 3 r'` and `r' ≤ 3 r`
  have hr_le_3r' : r ≤ 3 * r' := by
    have : r₁ ≤ 3 * r₀ := by linarith
    linarith
  have hr'_le_3r : r' ≤ 3 * r := by
    have : r₁ ≤ 3 * r₀ := by linarith
    linarith
  -- defect roots, positive
  set d := dtilde P.X r a with hd_def
  set d' := dtilde P.X r' a with hd'_def
  have hdpos : 0 < d := dtilde_pos P.X_pos ha0 hrpos
  have hd'pos : 0 < d' := dtilde_pos P.X_pos ha0 hr'pos
  -- the band ratio of the defect itself.  Reprove `d ≤ 2 d'`, `d' ≤ 2 d` from the same
  -- root-comparison core (avoids unfolding the division-ratio statement).
  have hww_setup : ∀ s s' : ℝ, 0 < s → 0 < s' → s' ≤ 3 * s →
      dtilde P.X s a * (dtilde P.X s a + a) ≤ 2 * (dtilde P.X s' a * (dtilde P.X s' a + a)) := by
    intro s s' hs hs' hss'
    rw [dtilde_prod P.X_pos ha0 hs, dtilde_prod P.X_pos ha0 hs']
    have hws : Real.sqrt (P.X * a ^ 3 / s) ^ 2 = P.X * a ^ 3 / s := Real.sq_sqrt (by positivity)
    have hws' : Real.sqrt (P.X * a ^ 3 / s') ^ 2 = P.X * a ^ 3 / s' := Real.sq_sqrt (by positivity)
    have hwspos : 0 < Real.sqrt (P.X * a ^ 3 / s) := Real.sqrt_pos.mpr (by have := P.X_pos; positivity)
    have hws'pos : 0 < Real.sqrt (P.X * a ^ 3 / s') := Real.sqrt_pos.mpr (by have := P.X_pos; positivity)
    have hXa3 : 0 < P.X * a ^ 3 := by have := P.X_pos; positivity
    -- `w² = Xa³/s ≤ 3 · Xa³/s' = 3 w'²` ⟹ `w ≤ 2 w'`
    have hsq_le : Real.sqrt (P.X * a ^ 3 / s) ^ 2 ≤ 3 * Real.sqrt (P.X * a ^ 3 / s') ^ 2 := by
      rw [hws, hws', div_le_iff₀ hs, mul_comm (3 : ℝ), mul_assoc, div_mul_eq_mul_div,
        le_div_iff₀ hs']
      -- goal: `Xa³ · s' ≤ Xa³ · (3 s)`, from `s' ≤ 3 s`
      nlinarith [hXa3, hss']
    nlinarith [hsq_le, hwspos, hws'pos]
  have hd_le : d ≤ 2 * d' :=
    root_le_of_prod_le ha0 hdpos hd'pos rfl rfl (hww_setup r r' hrpos hr'pos hr'_le_3r)
  have hd'_le : d' ≤ 2 * d :=
    root_le_of_prod_le ha0 hd'pos hdpos rfl rfl (hww_setup r' r hr'pos hrpos hr_le_3r')
  -- closed form of the derivatives (negative) and their absolute values as `Num/Den`
  have hderiv : deriv (fun s => dtilde P.X s a) r = - d * (d + a) / (2 * r * (a + 2 * d)) :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hrpos).deriv
  have hderiv' : deriv (fun s => dtilde P.X s a) r' = - d' * (d' + a) / (2 * r' * (a + 2 * d')) :=
    (dtilde_r_hasDerivAt P.X_pos ha0 hr'pos).deriv
  set N := d * (d + a) with hN_def
  set N' := d' * (d' + a) with hN'_def
  set Den := 2 * r * (a + 2 * d) with hDen_def
  set Den' := 2 * r' * (a + 2 * d') with hDen'_def
  have hNpos : 0 < N := by rw [hN_def]; positivity
  have hN'pos : 0 < N' := by rw [hN'_def]; positivity
  have hDenpos : 0 < Den := by rw [hDen_def]; positivity
  have hDen'pos : 0 < Den' := by rw [hDen'_def]; positivity
  have habs : |deriv (fun s => dtilde P.X s a) r| = N / Den := by
    rw [hderiv]
    have : - d * (d + a) / (2 * r * (a + 2 * d)) = - (N / Den) := by
      rw [hN_def, hDen_def]; ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
  have habs' : |deriv (fun s => dtilde P.X s a) r'| = N' / Den' := by
    rw [hderiv']
    have : - d' * (d' + a) / (2 * r' * (a + 2 * d')) = - (N' / Den') := by
      rw [hN'_def, hDen'_def]; ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
  rw [habs, habs']
  -- The full ratio is `(N/Den) / (N'/Den') = (N · Den') / (Den · N')`.
  rw [div_div_div_eq]
  -- Now bound `(N / N')` and `(Den' / Den)` separately by absolute `O(1)` factors.
  -- ratio `N/N' = d(d+a)/(d'(d'+a)) ∈ [1/4, 4]`  (each of `d/d'`, `(d+a)/(d'+a)` ∈ [1/2, 2])
  have hN_le : N ≤ 4 * N' := by
    rw [hN_def, hN'_def]; nlinarith [hd_le, hd'_le, hdpos, hd'pos, ha0]
  have hN'_le : N' ≤ 4 * N := by
    rw [hN_def, hN'_def]; nlinarith [hd_le, hd'_le, hdpos, hd'pos, ha0]
  -- ratio `Den/Den' = r(a+2d)/(r'(a+2d')) : r/r' ∈ [1/3,3], (a+2d)/(a+2d') ∈ [1/2,2]`,
  -- so `Den/Den' ∈ [1/6, 6]` — we use the coarse `[1/16, 16]` to keep nlinarith light.
  have hDen_le : Den ≤ 16 * Den' := by
    rw [hDen_def, hDen'_def]; nlinarith [hr_le_3r', hd_le, hd'_le, hrpos, hr'pos, hdpos, hd'pos, ha0]
  have hDen'_le : Den' ≤ 16 * Den := by
    rw [hDen_def, hDen'_def]; nlinarith [hr'_le_3r, hd_le, hd'_le, hrpos, hr'pos, hdpos, hd'pos, ha0]
  -- combine `(N · Den') / (Den · N')`
  have hprodpos : 0 < Den * N' := by positivity
  constructor
  · rw [le_div_iff₀ hprodpos]
    -- `1/64 · (Den · N') ≤ N · Den'`
    -- from `N' ≤ 4 N` and `Den ≤ 16 Den'`: `Den·N' ≤ 16 Den' · 4 N = 64 N Den'`
    nlinarith [mul_le_mul hDen_le hN'_le (le_of_lt hN'pos) (by positivity : (0:ℝ) ≤ 16 * Den'),
      hNpos, hN'pos, hDenpos, hDen'pos]
  · rw [div_le_iff₀ hprodpos]
    -- `N · Den' ≤ 64 · (Den · N')` from `N ≤ 4 N'`, `Den' ≤ 16 Den`
    nlinarith [mul_le_mul hN_le hDen'_le (le_of_lt hDen'pos) (by positivity : (0:ℝ) ≤ 4 * N'),
      hNpos, hN'pos, hDenpos, hDen'pos]

end Squarefree
