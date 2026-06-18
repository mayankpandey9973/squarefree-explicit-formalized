import Squarefree.Lower.DefectClose
import Squarefree.Lower.Step1Phase

/-!
# §5 `φ_d → φ` replacement (writeup 824–832)

The discrete phase `φ_d = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)·X·a·b₀²/d⁵` (built from witness denominators
`d, d₁` and `b₀ = (d₁−d)/ℓ₁`) is within `O(δ)` of the smooth phase
`φ = phi P.X a ℓ₁ ℓ₂ r`, with `δ = (1/Δ)·G³U¹⁰/Ω⁵`.

This is the discrete↔smooth interface: we replace `d, b₀` by `d̃ₐ(r), b̃ₐ(r)` and absorb the
two perturbation terms (in `b²` and in `1/d⁵`) into the budget `δ`.
-/

namespace Squarefree

open Real

/-- Arithmetic core of the δ-comparison: `G²U¹⁰·(11/(GΩ⁵Δ)) ≤ 11·δ` where `δ = G³U¹⁰/(ΔΩ⁵)`.
Pulled out to keep the heavy main proof's `nlinarith` out of the giant context. -/
private theorem delta_compare_aux {G U Ω Δ δ : ℝ}
    (hG : 0 < G) (hU : 0 < U) (hΩ : 0 < Ω) (hΔ : 0 < Δ)
    (hδeq : δ = G ^ 3 * U ^ 10 / (Δ * Ω ^ 5)) (hG1 : 1 ≤ G) :
    (G ^ 2 * U ^ 10) * (11 / (G * Ω ^ 5 * Δ)) ≤ 11 * δ := by
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have heq : (G ^ 2 * U ^ 10) * (11 / (G * Ω ^ 5 * Δ)) = 11 * δ / G ^ 2 := by
    have hL : (G ^ 2 * U ^ 10) * (11 / (G * Ω ^ 5 * Δ))
        = 11 * (G ^ 2 * U ^ 10) / (G * Ω ^ 5 * Δ) := by ring
    have hΩne : Ω ≠ 0 := ne_of_gt hΩ
    have hΔne : Δ ≠ 0 := ne_of_gt hΔ
    have hGne : G ≠ 0 := ne_of_gt hG
    have hR : 11 * δ / G ^ 2 = 11 * (G ^ 3 * U ^ 10) / (Δ * Ω ^ 5 * G ^ 2) := by
      rw [hδeq]; field_simp
    rw [hL, hR, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [heq, div_le_iff₀ (by positivity)]
  nlinarith [hδpos, hG1, mul_nonneg hδpos.le (sub_nonneg.mpr (by nlinarith [hG1] : (1:ℝ) ≤ G ^ 2))]

/-- Tiny scalar closing inequality `96·10²⁴·(11·δ) ≤ (10⁴⁰/2)·δ` for `δ ≥ 0`. -/
private theorem scalar_close_aux {δ : ℝ} (hδ : 0 ≤ δ) :
    (96000000000000000000000000 : ℝ) * (11 * δ) ≤ (10:ℝ) ^ 45 / 2 * δ := by
  have h10 : (10:ℝ) ^ 45 / 2 = 500000000000000000000000000000000000000000000 := by norm_num
  rw [h10]
  nlinarith [hδ]

/-- **Key §5 absorption** `U⁵·Δ ≤ G²·Ω³·H` (writeup 824–832 budget closure).  Proved by
raising to the 4th power so the band/`h1` integer-power bounds apply.
- `h1 : G·U¹⁰ ≤ H/Δ²`  ⟹  `Δ² ≤ H/(G·U¹⁰)`,
- `hband : 1 ≤ G·U³·Ω⁴`  ⟹  `Ω⁴ ≥ 1/(G·U³)`,
- `hUH : U⁹ ≤ G⁷·H²`,  `H ≥ 1`, `G ≥ 1`, `U ≥ 1`. -/
private theorem absorb_UH_aux {G U Ω Δ H : ℝ}
    (hG : 0 < G) (hU : 0 < U) (hΩ : 0 < Ω) (hΔ : 0 < Δ) (hH : 0 < H)
    (h1 : G * U ^ 10 ≤ H / Δ ^ 2) (hband : 1 ≤ G * U ^ 3 * Ω ^ 4)
    (_hG1 : 1 ≤ G) (_hU1 : 1 ≤ U) (_hH1 : 1 ≤ H) (hUH : U ^ 9 ≤ G ^ 7 * H ^ 2) :
    U ^ 5 * Δ ≤ G ^ 2 * Ω ^ 3 * H := by
  -- It suffices to compare 4th powers (both sides nonneg).
  have hLnn : 0 ≤ U ^ 5 * Δ := by positivity
  have hRnn : 0 ≤ G ^ 2 * Ω ^ 3 * H := by positivity
  -- (U⁵Δ)⁴ = U²⁰Δ⁴ ≤ U²⁰·(H/(G U¹⁰))² = H²/G²
  have hΔ2 : Δ ^ 2 ≤ H / (G * U ^ 10) := by
    rw [le_div_iff₀ (by positivity)]
    have hmul : G * U ^ 10 * Δ ^ 2 ≤ H := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt (pow_pos hΔ 2))
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith [hmul]
  have hΔ4 : Δ ^ 4 ≤ H ^ 2 / (G ^ 2 * U ^ 20) := by
    have hpow : Δ ^ 4 = (Δ ^ 2) ^ 2 := by ring
    have hrhs : (H / (G * U ^ 10)) ^ 2 = H ^ 2 / (G ^ 2 * U ^ 20) := by
      rw [div_pow]; congr 1; ring
    rw [hpow, ← hrhs]
    apply pow_le_pow_left₀ (by positivity) hΔ2
  have hL4 : (U ^ 5 * Δ) ^ 4 ≤ H ^ 2 / G ^ 2 := by
    have hexp : (U ^ 5 * Δ) ^ 4 = U ^ 20 * Δ ^ 4 := by ring
    rw [hexp]
    calc U ^ 20 * Δ ^ 4 ≤ U ^ 20 * (H ^ 2 / (G ^ 2 * U ^ 20)) :=
          mul_le_mul_of_nonneg_left hΔ4 (by positivity)
      _ = H ^ 2 / G ^ 2 := by
          field_simp
  -- Ω⁴ ≥ 1/(G U³), so Ω¹² ≥ 1/(G³U⁹)
  have hΩ4 : 1 / (G * U ^ 3) ≤ Ω ^ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hband]
  have hΩ12 : 1 / (G ^ 3 * U ^ 9) ≤ Ω ^ 12 := by
    have hcube : (1 / (G * U ^ 3)) ^ 3 = 1 / (G ^ 3 * U ^ 9) := by
      rw [div_pow]; congr 1 <;> ring
    have hΩcube : (Ω ^ 4) ^ 3 = Ω ^ 12 := by ring
    rw [← hcube, ← hΩcube]
    apply pow_le_pow_left₀ (by positivity) hΩ4
  -- (G²Ω³H)⁴ = G⁸Ω¹²H⁴ ≥ G⁸·(1/(G³U⁹))·H⁴ = G⁵H⁴/U⁹
  have hR4 : G ^ 5 * H ^ 4 / U ^ 9 ≤ (G ^ 2 * Ω ^ 3 * H) ^ 4 := by
    have hexp : (G ^ 2 * Ω ^ 3 * H) ^ 4 = G ^ 8 * Ω ^ 12 * H ^ 4 := by ring
    rw [hexp]
    calc G ^ 5 * H ^ 4 / U ^ 9 = G ^ 8 * (1 / (G ^ 3 * U ^ 9)) * H ^ 4 := by
          field_simp
      _ ≤ G ^ 8 * Ω ^ 12 * H ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hΩ12 (by positivity)
  -- H²/G² ≤ G⁵H⁴/U⁹  ⟺  U⁹ ≤ G⁷H²
  have hmid : H ^ 2 / G ^ 2 ≤ G ^ 5 * H ^ 4 / U ^ 9 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hUH, sq_nonneg H, _hH1, pow_pos hH 2, pow_pos hG 5, mul_pos (pow_pos hG 5) (pow_pos hH 2)]
  -- chain the 4th-power comparison and take 4th roots
  have h4 : (U ^ 5 * Δ) ^ 4 ≤ (G ^ 2 * Ω ^ 3 * H) ^ 4 :=
    le_trans hL4 (le_trans hmid hR4)
  exact le_of_pow_le_pow_left₀ (by norm_num) hRnn h4

/-- `|y⁵ − x⁵| ≤ 5·M⁴·|x − y|` for `0 ≤ x,y ≤ M`.  (Factor `y⁵−x⁵ = (y−x)·Σ`, bound `|Σ| ≤ 5M⁴`.) -/
private theorem pow5_diff_aux {x y M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    |y ^ 5 - x ^ 5| ≤ 5 * M ^ 4 * |x - y| := by
  have hMnn : 0 ≤ M := le_trans hx hxM
  have hfac : y ^ 5 - x ^ 5
      = (y - x) * (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4) := by ring
  rw [hfac, abs_mul]
  have hsum_nn : 0 ≤ y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4 := by positivity
  have hsum_le : y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4 ≤ 5 * M ^ 4 := by
    have h1 : y ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hy hyM 4
    have h2 : y ^ 3 * x ≤ M ^ 4 := by
      have : y ^ 3 * x ≤ M ^ 3 * M := by
        apply mul_le_mul (pow_le_pow_left₀ hy hyM 3) hxM hx (by positivity)
      nlinarith [this]
    have h3 : y ^ 2 * x ^ 2 ≤ M ^ 4 := by
      have : y ^ 2 * x ^ 2 ≤ M ^ 2 * M ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hy hyM 2) (pow_le_pow_left₀ hx hxM 2) (by positivity) (by positivity)
      nlinarith [this]
    have h4 : y * x ^ 3 ≤ M ^ 4 := by
      have : y * x ^ 3 ≤ M * M ^ 3 :=
        mul_le_mul hyM (pow_le_pow_left₀ hx hxM 3) (by positivity) hMnn
      nlinarith [this]
    have h5 : x ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hx hxM 4
    linarith [h1, h2, h3, h4, h5]
  rw [abs_of_nonneg hsum_nn, abs_sub_comm x y]
  calc |y - x| * (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4)
      ≤ |y - x| * (5 * M ^ 4) := mul_le_mul_of_nonneg_left hsum_le (abs_nonneg _)
    _ = 5 * M ^ 4 * |y - x| := by ring

/-- Term2 δ-comparison core: `G³U¹⁵·(11/(G²Ω⁸H)) ≤ 11·δ`, using `U⁵Δ ≤ G²Ω³H`. -/
private theorem delta_compare2_aux {G U Ω Δ H δ : ℝ}
    (hG : 0 < G) (_hU : 0 < U) (hΩ : 0 < Ω) (hΔ : 0 < Δ) (_hH : 0 < H)
    (hδeq : δ = G ^ 3 * U ^ 10 / (Δ * Ω ^ 5))
    (habsorb : U ^ 5 * Δ ≤ G ^ 2 * Ω ^ 3 * H) :
    (G ^ 3 * U ^ 15) * (11 / (G ^ 2 * Ω ^ 8 * H)) ≤ 11 * δ := by
  rw [hδeq]
  have hL : (G ^ 3 * U ^ 15) * (11 / (G ^ 2 * Ω ^ 8 * H))
      = (11 * (G ^ 3 * U ^ 15)) / (G ^ 2 * Ω ^ 8 * H) := by ring
  have hR : 11 * (G ^ 3 * U ^ 10 / (Δ * Ω ^ 5))
      = (11 * (G ^ 3 * U ^ 10)) / (Δ * Ω ^ 5) := by ring
  rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
  -- (11·G³U¹⁵)·(ΔΩ⁵) ≤ (11·G³U¹⁰)·(G²Ω⁸H)   ⟺   U⁵Δ ≤ G²Ω³H  (factor 11G³U¹⁰Ω⁵)
  have hfac : 11 * (G ^ 3 * U ^ 15) * (Δ * Ω ^ 5)
      = (11 * G ^ 3 * U ^ 10 * Ω ^ 5) * (U ^ 5 * Δ) := by ring
  have hfac2 : 11 * (G ^ 3 * U ^ 10) * (G ^ 2 * Ω ^ 8 * H)
      = (11 * G ^ 3 * U ^ 10 * Ω ^ 5) * (G ^ 2 * Ω ^ 3 * H) := by ring
  rw [hfac, hfac2]
  exact mul_le_mul_of_nonneg_left habsorb (by positivity)

/-- Term2 scalar closing: `C·(11·δ) ≤ (10⁴⁰/2)·δ` for `δ ≥ 0`, `C = 12·5·18⁴·10⁵·10¹²·10¹²`. -/
private theorem term2_scalar_close_aux {δ : ℝ} (hδ : 0 ≤ δ) :
    (12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000) * (11 * δ)
      ≤ (10:ℝ) ^ 45 / 2 * δ := by
  have h10 : (10:ℝ) ^ 45 / 2 = 500000000000000000000000000000000000000000000 := by norm_num
  rw [h10]
  nlinarith [hδ]

/-- `1 ≤ H` from `1 ≤ G·U¹⁰ ≤ H/Δ²` and `1 ≤ Δ`. -/
private theorem one_le_H_aux {G U Δ H : ℝ} (hG : 0 < G) (_hU : 0 < U) (hΔ : 0 < Δ) (_hH : 0 < H)
    (h1 : G * U ^ 10 ≤ H / Δ ^ 2) (hG1 : 1 ≤ G) (hU1 : 1 ≤ U) (hΔ1 : 1 ≤ Δ) : 1 ≤ H := by
  have hb : (1:ℝ) ≤ G * U ^ 10 := by
    have hUp : (1:ℝ) ≤ U ^ 10 := one_le_pow₀ hU1
    nlinarith [hG1, hUp]
  have hΔ2le : Δ ^ 2 ≤ H := by
    have hchain : (1:ℝ) ≤ H / Δ ^ 2 := le_trans hb h1
    rw [le_div_iff₀ (by positivity)] at hchain
    nlinarith [hchain]
  nlinarith [hΔ2le, hΔ1]

/-- Inverse 5th-power difference bound:  `|1/d⁵ − 1/dt⁵| ≤ C·δ'/D⁶` with `C = 5·18⁴·10¹⁷`,
given the windows `D ≤ d ≤ 18D`, `D/10 ≤ dt ≤ 18D`, and `|d − dt| ≤ 10¹²·δ'`.  Pulled out so the
heavy `field_simp` runs in a tiny context. -/
private theorem inv_pow5_close_aux {d dt D δ' : ℝ} (hD : 0 < D) (hδ' : 0 ≤ δ')
    (hd_lo : D ≤ d) (hd_hi : d ≤ 18 * D) (hdt_lo : D / 10 ≤ dt) (hdt_hi : dt ≤ 18 * D)
    (hclose : |d - dt| ≤ 1000000000000 * δ') :
    |1 / d ^ 5 - 1 / dt ^ 5| ≤ (5 * 18 ^ 4 * 100000 * 1000000000000 / D ^ 6) * δ' := by
  have hdpos : 0 < d := lt_of_lt_of_le hD hd_lo
  have hdtpos : 0 < dt := lt_of_lt_of_le (by positivity) hdt_lo
  have hinv_eq : 1 / d ^ 5 - 1 / dt ^ 5 = (dt ^ 5 - d ^ 5) / (d ^ 5 * dt ^ 5) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), one_mul, mul_one]
  have hnum : |dt ^ 5 - d ^ 5| ≤ 5 * (18 * D) ^ 4 * |d - dt| :=
    pow5_diff_aux hdpos.le hdtpos.le hd_hi hdt_hi
  have hden_lo : D ^ 10 / 100000 ≤ d ^ 5 * dt ^ 5 := by
    have h1 : D ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ hD.le hd_lo 5
    have h2 : (D / 10) ^ 5 ≤ dt ^ 5 := pow_le_pow_left₀ (by positivity) hdt_lo 5
    have heq : D ^ 10 / 100000 = D ^ 5 * (D / 10) ^ 5 := by ring
    rw [heq]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hdenpos : 0 < d ^ 5 * dt ^ 5 := by positivity
  have hnum2 : |dt ^ 5 - d ^ 5| ≤ 5 * (18 * D) ^ 4 * (1000000000000 * δ') := by
    refine le_trans hnum ?_
    exact mul_le_mul_of_nonneg_left hclose (by positivity)
  rw [hinv_eq, abs_div, abs_of_pos hdenpos]
  have hnumnn : 0 ≤ 5 * (18 * D) ^ 4 * (1000000000000 * δ') := by positivity
  have hstep : |dt ^ 5 - d ^ 5| / (d ^ 5 * dt ^ 5)
      ≤ (5 * (18 * D) ^ 4 * (1000000000000 * δ')) / (D ^ 10 / 100000) := by
    rw [div_le_div_iff₀ hdenpos (by positivity)]
    have hbound : |dt ^ 5 - d ^ 5| * (D ^ 10 / 100000)
        ≤ (5 * (18 * D) ^ 4 * (1000000000000 * δ')) * (d ^ 5 * dt ^ 5) := by
      apply mul_le_mul hnum2 hden_lo (by positivity) hnumnn
    exact hbound
  refine le_trans hstep (le_of_eq ?_)
  rw [show (18 * D) ^ 4 = 18 ^ 4 * D ^ 4 by ring]
  field_simp

/-- **§5 `φ_d → φ` replacement** (writeup 824–832): the discrete phase is within `10⁴⁰·δ` of
the smooth phase `φ`, where `δ = (1/Δ)·G³U¹⁰/Ω⁵`.  We split the difference
`b₀²/d⁵ − b̃²/d̃⁵` into a `b²`-part and a `1/d⁵`-part and absorb each into the budget. -/
theorem phi_d_replace {P : Globals} {S : Scale P} {a : ℤ} {r ℓ₁ ℓ₂ d d₁ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (hr_lo : (1/72) * S.R ≤ r) (hr1_hi : r + ℓ₁ ≤ 16 * S.R)
    (hd_win : S.D ≤ d ∧ d ≤ 2 * S.D) (hd1_win : S.D ≤ d₁ ∧ d₁ ≤ 2 * S.D)
    (hd_close : |d - dtilde P.X r (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hd1_close : |d₁ - dtilde P.X (r + ℓ₁) (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) :
    |12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * ((d₁ - d) / ℓ₁) ^ 2 / d ^ 5
        - phi P.X (a : ℝ) ℓ₁ ℓ₂ r|
      ≤ (10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5) := by
  -- ===== positivity =====
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha0
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  -- ===== abbreviations =====
  set dt := dtilde P.X r (a:ℝ) with hdt
  set dt1 := dtilde P.X (r + ℓ₁) (a:ℝ) with hdt1
  set bb := bt P.X (a:ℝ) ℓ₁ r with hbb
  set b0 := (d₁ - d) / ℓ₁ with hb0
  -- δ' = Δ/(G·Ω³) = B/Δ
  set δ' := S.Δ / (P.G * S.Ω ^ 3) with hδ'
  have hδ'pos : 0 < δ' := by rw [hδ']; positivity
  -- δ
  set δ := (1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  -- b̃ = (dt1 − dt)/ℓ₁
  have hbb_eq : bb = (dt1 - dt) / ℓ₁ := by rw [hbb, bt, hdt1, hdt]
  -- δ' = B/Δ
  have hδ'B : δ' = S.B / S.Δ := by
    rw [hδ', Scale.B]; field_simp
  -- phi as K·b̃²/d̃⁵
  have hphi : phi P.X (a:ℝ) ℓ₁ ℓ₂ r
      = 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a:ℝ) * bb ^ 2 / dt ^ 5 := by
    rw [phi, hbb, hdt]
  -- ===== windows for d̃, d̃₁ =====
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  have hr1pos : 0 < r + ℓ₁ := by linarith
  have hr_hi : r ≤ 16 * S.R := by linarith
  have hrl_lo : (1/72) * S.R ≤ r + ℓ₁ := by linarith
  obtain ⟨hdt_lo, hdt_hi⟩ :=
    dtilde_asymp_D (P := P) (S := S) hAD haR hr0 ha_lo ha_hi hr_lo hr_hi
  obtain ⟨hdt1_lo, hdt1_hi⟩ :=
    dtilde_asymp_D (P := P) (S := S) hAD haR hr1pos ha_lo ha_hi hrl_lo hr1_hi
  rw [← hdt] at hdt_lo hdt_hi
  rw [← hdt1] at hdt1_lo hdt1_hi
  have hdtpos : 0 < dt := by linarith [hdt_lo, (by positivity : (0:ℝ) < S.D / 10)]
  have hdt1pos : 0 < dt1 := by linarith [hdt1_lo, (by positivity : (0:ℝ) < S.D / 10)]
  -- windows for d, d₁ from hyps
  obtain ⟨hd_lo, hd_hi⟩ := hd_win
  obtain ⟨hd1_lo, hd1_hi⟩ := hd1_win
  -- ===== |b̃| ≤ 10⁶·B =====
  obtain ⟨_, _, hbb_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := (a:ℝ)) (ℓ := ℓ₁) (r := r)
      hAD haR hℓ1 ha_lo ha_hi hr_lo hr1_hi
  rw [← hbb] at hbb_hi
  -- ===== close bounds in terms of δ' =====
  have hd_close' : |d - dt| ≤ 1000000000000 * δ' := by rw [hdt] at hd_close ⊢; rw [hδ']; exact hd_close
  have hd1_close' : |d₁ - dt1| ≤ 1000000000000 * δ' := by
    rw [hdt1] at hd1_close ⊢; rw [hδ']; exact hd1_close
  -- ===== |b₀ − b̃| ≤ 2·10¹²·δ'/ℓ₁ =====
  have hb0_sub : b0 - bb = ((d₁ - dt1) - (d - dt)) / ℓ₁ := by
    rw [hb0, hbb_eq]; field_simp; ring
  have hb0_sub_abs : |b0 - bb| ≤ 2000000000000 * δ' / ℓ₁ := by
    rw [hb0_sub, abs_div, abs_of_pos hℓ1]
    have hnum : |(d₁ - dt1) - (d - dt)| ≤ 2000000000000 * δ' := by
      calc |(d₁ - dt1) - (d - dt)| ≤ |d₁ - dt1| + |d - dt| := abs_sub _ _
        _ ≤ 1000000000000 * δ' + 1000000000000 * δ' := by linarith [hd_close', hd1_close']
        _ = 2000000000000 * δ' := by ring
    gcongr
  -- ===== K and the split =====
  have hℓdiff : 0 < ℓ₂ - ℓ₁ := by linarith
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a:ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  rw [hphi]
  rw [show (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a:ℝ) * ((d₁ - d) / ℓ₁) ^ 2 / d ^ 5)
        = K * b0 ^ 2 / d ^ 5 by rw [hK, hb0],
     show (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a:ℝ) * bb ^ 2 / dt ^ 5)
        = K * bb ^ 2 / dt ^ 5 by rw [hK]]
  -- the algebraic split: K·b0²/d⁵ − K·b̃²/d̃⁵ = K·(b0²−b̃²)/d⁵ + K·b̃²·(1/d⁵ − 1/d̃⁵)
  have hdpos : 0 < d := lt_of_lt_of_le hDpos hd_lo
  have hdpow : (0:ℝ) < d ^ 5 := by positivity
  have hdtpow : (0:ℝ) < dt ^ 5 := by positivity
  have hsplit : K * b0 ^ 2 / d ^ 5 - K * bb ^ 2 / dt ^ 5
      = K * (b0 ^ 2 - bb ^ 2) / d ^ 5 + K * bb ^ 2 * (1 / d ^ 5 - 1 / dt ^ 5) := by
    field_simp
    ring
  rw [hsplit]
  -- triangle inequality
  refine le_trans (abs_add_le _ _) ?_
  -- Term1 := |K·(b0²−b̃²)/d⁵|,  Term2 := |K·b̃²·(1/d⁵−1/d̃⁵)|
  have hHalf : (10:ℝ) ^ 45 * δ = (10:ℝ) ^ 45 / 2 * δ + (10:ℝ) ^ 45 / 2 * δ := by ring
  rw [hHalf]
  -- ===== scale facts =====
  -- X·a·B²/D⁵ ≤ 11/(G·Ω⁵)
  have hXAB2 : P.X * S.A * S.B ^ 2 / S.D ^ 5 = 1 / (P.G * S.Ω ^ 5) := defect_XAB2_div_D5 S
  have hXaB2 : P.X * (a:ℝ) * S.B ^ 2 / S.D ^ 5 ≤ 11 / (P.G * S.Ω ^ 5) := by
    have hstep : P.X * (a:ℝ) * S.B ^ 2 / S.D ^ 5
        ≤ 11 * (P.X * S.A * S.B ^ 2 / S.D ^ 5) := by
      rw [show 11 * (P.X * S.A * S.B ^ 2 / S.D ^ 5)
            = P.X * (11 * S.A) * S.B ^ 2 / S.D ^ 5 by ring]
      gcongr
    rw [hXAB2, mul_one_div] at hstep; exact hstep
  -- X·a·B³/D⁶ ≤ 11/(G·Ω⁵·R)
  have hXAB3 : P.X * S.A * S.B ^ 3 / S.D ^ 6 = 1 / (P.G * S.Ω ^ 5 * S.R) := defect_XAB3_div_D6' S
  have hXaB3 : P.X * (a:ℝ) * S.B ^ 3 / S.D ^ 6 ≤ 11 / (P.G * S.Ω ^ 5 * S.R) := by
    have hstep : P.X * (a:ℝ) * S.B ^ 3 / S.D ^ 6
        ≤ 11 * (P.X * S.A * S.B ^ 3 / S.D ^ 6) := by
      rw [show 11 * (P.X * S.A * S.B ^ 3 / S.D ^ 6)
            = P.X * (11 * S.A) * S.B ^ 3 / S.D ^ 6 by ring]
      gcongr
    rw [hXAB3, mul_one_div] at hstep; exact hstep
  -- 1/(G·Ω⁵·R·Δ) = 1/(G²·Ω⁸·... )?  use R = H·G·Ω³/Δ ⟹ R·Δ = H·G·Ω³
  have hRΔ : S.R * S.Δ = P.H * P.G * S.Ω ^ 3 := by rw [Scale.R]; field_simp
  -- ℓ-budgets
  have hℓ2sq : ℓ₂ * (ℓ₂ - ℓ₁) ≤ 16900 * (P.G ^ 2 * P.U ^ 10) := by
    have h1' : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
    have hGU : (0:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by positivity
    calc ℓ₂ * (ℓ₂ - ℓ₁) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) := by
          apply mul_le_mul hℓ2W h1' (le_of_lt hℓdiff) hGU
      _ = 16900 * (P.G ^ 2 * P.U ^ 10) := by ring
  have hℓ123 : ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) ≤ 2197000 * (P.G ^ 3 * P.U ^ 15) := by
    have hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith
    calc ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) = ℓ₁ * (ℓ₂ * (ℓ₂ - ℓ₁)) := by ring
      _ ≤ (130 * (P.G * P.U ^ 5)) * (16900 * (P.G ^ 2 * P.U ^ 10)) := by
          apply mul_le_mul hℓ1W hℓ2sq (by positivity) (by positivity)
      _ = 2197000 * (P.G ^ 3 * P.U ^ 15) := by ring
  -- ===== Term1 bound =====
  -- |b0 − bb| ≤ 2·10¹²·δ'  (using ℓ₁ ≥ 1)
  have hM1 : |b0 - bb| ≤ 2000000000000 * δ' := by
    calc |b0 - bb| ≤ 2000000000000 * δ' / ℓ₁ := hb0_sub_abs
      _ ≤ 2000000000000 * δ' / 1 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hℓ1_lo
      _ = 2000000000000 * δ' := by ring
  -- |b0 + bb| ≤ 2·10⁶·B + 2·10¹²·δ'
  have hM2 : |b0 + bb| ≤ 2000000 * S.B + 2000000000000 * δ' := by
    have hb0abs : |b0| ≤ 1000000 * S.B + 2000000000000 * δ' := by
      calc |b0| = |bb + (b0 - bb)| := by ring_nf
        _ ≤ |bb| + |b0 - bb| := abs_add_le _ _
        _ ≤ 1000000 * S.B + 2000000000000 * δ' := by linarith [hbb_hi, hM1]
    calc |b0 + bb| ≤ |b0| + |bb| := abs_add_le _ _
      _ ≤ (1000000 * S.B + 2000000000000 * δ') + 1000000 * S.B := by linarith [hb0abs, hbb_hi]
      _ = 2000000 * S.B + 2000000000000 * δ' := by ring
  -- |b0²−b̃²| ≤ |b0−b̃|·|b0+b̃|
  have hb2diff : |b0 ^ 2 - bb ^ 2| ≤ (2000000000000 * δ' / ℓ₁) * (2000000 * S.B + 2000000000000 * δ') := by
    rw [show b0 ^ 2 - bb ^ 2 = (b0 - bb) * (b0 + bb) by ring, abs_mul]
    apply mul_le_mul hb0_sub_abs hM2 (abs_nonneg _) (by positivity)
  -- scale: Xa·δ'·B/D⁵ ≤ 11/(G·Ω⁵·Δ)  and  Xa·δ'²/D⁵ ≤ 11/(G·Ω⁵·Δ)
  have hXaδ'B : P.X * (a:ℝ) * δ' * S.B / S.D ^ 5 ≤ 11 / (P.G * S.Ω ^ 5 * S.Δ) := by
    have heq : P.X * (a:ℝ) * δ' * S.B / S.D ^ 5
        = (P.X * (a:ℝ) * S.B ^ 2 / S.D ^ 5) / S.Δ := by
      rw [hδ'B]; field_simp
    rw [heq, show 11 / (P.G * S.Ω ^ 5 * S.Δ) = (11 / (P.G * S.Ω ^ 5)) / S.Δ by
        rw [div_div]]
    gcongr
  -- Xa·δ'²/D⁵ ≤ 11/(G·Ω⁵·Δ)  (using Δ ≥ 1 to drop one 1/Δ)
  have hXaδ'2 : P.X * (a:ℝ) * δ' ^ 2 / S.D ^ 5 ≤ 11 / (P.G * S.Ω ^ 5 * S.Δ) := by
    have heq : P.X * (a:ℝ) * δ' ^ 2 / S.D ^ 5
        = (P.X * (a:ℝ) * S.B ^ 2 / S.D ^ 5) / S.Δ ^ 2 := by
      rw [hδ'B]; field_simp
    have hstep : (P.X * (a:ℝ) * S.B ^ 2 / S.D ^ 5) / S.Δ ^ 2
        ≤ (11 / (P.G * S.Ω ^ 5)) / S.Δ ^ 2 := by gcongr
    have hΔ2 : (11 / (P.G * S.Ω ^ 5)) / S.Δ ^ 2 ≤ (11 / (P.G * S.Ω ^ 5)) / S.Δ := by
      apply div_le_div_of_nonneg_left (by positivity) hΔpos
      nlinarith only [hΔ1, hΔpos]
    rw [heq, show 11 / (P.G * S.Ω ^ 5 * S.Δ) = (11 / (P.G * S.Ω ^ 5)) / S.Δ by rw [div_div]]
    exact le_trans hstep hΔ2
  -- key δ-comparison:  ℓ₂(ℓ₂−ℓ₁)·11/(G·Ω⁵·Δ) ≤ 11·δ
  have hδeq : δ = P.G ^ 3 * P.U ^ 10 / (S.Δ * S.Ω ^ 5) := by rw [hδ]; field_simp
  have hkey : ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G * S.Ω ^ 5 * S.Δ)) ≤ 16900 * (11 * δ) := by
    have hstep1 : ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G * S.Ω ^ 5 * S.Δ))
        ≤ (16900 * (P.G ^ 2 * P.U ^ 10)) * (11 / (P.G * S.Ω ^ 5 * S.Δ)) :=
      mul_le_mul_of_nonneg_right hℓ2sq (by positivity)
    have hstep2 : (P.G ^ 2 * P.U ^ 10) * (11 / (P.G * S.Ω ^ 5 * S.Δ)) ≤ 11 * δ :=
      delta_compare_aux hGpos hUpos hΩpos hΔpos hδeq hG1
    have hstep2' : (16900 * (P.G ^ 2 * P.U ^ 10)) * (11 / (P.G * S.Ω ^ 5 * S.Δ))
        ≤ 16900 * (11 * δ) := by
      have := mul_le_mul_of_nonneg_left hstep2 (by norm_num : (0:ℝ) ≤ 16900)
      calc (16900 * (P.G ^ 2 * P.U ^ 10)) * (11 / (P.G * S.Ω ^ 5 * S.Δ))
          = 16900 * ((P.G ^ 2 * P.U ^ 10) * (11 / (P.G * S.Ω ^ 5 * S.Δ))) := by ring
        _ ≤ 16900 * (11 * δ) := this
    exact le_trans hstep1 hstep2'
  have hTerm1 : |K * (b0 ^ 2 - bb ^ 2) / d ^ 5| ≤ (10:ℝ) ^ 45 / 2 * δ := by
    -- |K·x/d⁵| = (K/d⁵)·|x|
    have hKd : (0:ℝ) < K / d ^ 5 := by positivity
    have habs : |K * (b0 ^ 2 - bb ^ 2) / d ^ 5| = (K / d ^ 5) * |b0 ^ 2 - bb ^ 2| := by
      rw [show K * (b0 ^ 2 - bb ^ 2) / d ^ 5 = (K / d ^ 5) * (b0 ^ 2 - bb ^ 2) by ring,
        abs_mul, abs_of_pos hKd]
    rw [habs]
    -- bound the difference product and divide by D⁵ ≤ d⁵
    set P1 := (2000000000000 * δ' / ℓ₁) * (2000000 * S.B + 2000000000000 * δ') with hP1
    have hP1nn : 0 ≤ P1 := by rw [hP1]; positivity
    have hstep1 : (K / d ^ 5) * |b0 ^ 2 - bb ^ 2| ≤ (K / S.D ^ 5) * P1 := by
      apply mul_le_mul _ hb2diff (abs_nonneg _) (by positivity)
      apply div_le_div_of_nonneg_left (le_of_lt hKpos) (by positivity)
      exact pow_le_pow_left₀ hDpos.le hd_lo 5
    refine le_trans hstep1 ?_
    -- now the pure-scale bound:  (K/D⁵)·P1 ≤ (10⁴⁰/2)·δ
    -- expand:  (K/D⁵)·P1 = 12ℓ₂(ℓ₂−ℓ₁)·[4·10¹⁸·(Xa·δ'·B/D⁵) + 4·10²⁴·(Xa·δ'²/D⁵)]
    have hexpand : (K / S.D ^ 5) * P1
        = 12 * (ℓ₂ * (ℓ₂ - ℓ₁)) *
            (4000000000000000000 * (P.X * (a:ℝ) * δ' * S.B / S.D ^ 5)
              + 4000000000000000000000000 * (P.X * (a:ℝ) * δ' ^ 2 / S.D ^ 5)) := by
      rw [hK, hP1]; field_simp; ring
    rw [hexpand]
    -- bound each scale piece by 11/(G·Ω⁵·Δ)
    have hbound : 4000000000000000000 * (P.X * (a:ℝ) * δ' * S.B / S.D ^ 5)
          + 4000000000000000000000000 * (P.X * (a:ℝ) * δ' ^ 2 / S.D ^ 5)
        ≤ 8000000000000000000000000 * (11 / (P.G * S.Ω ^ 5 * S.Δ)) := by
      have e1 : 4000000000000000000 * (P.X * (a:ℝ) * δ' * S.B / S.D ^ 5)
          ≤ 4000000000000000000 * (11 / (P.G * S.Ω ^ 5 * S.Δ)) :=
        mul_le_mul_of_nonneg_left hXaδ'B (by norm_num)
      have e2 : 4000000000000000000000000 * (P.X * (a:ℝ) * δ' ^ 2 / S.D ^ 5)
          ≤ 4000000000000000000000000 * (11 / (P.G * S.Ω ^ 5 * S.Δ)) :=
        mul_le_mul_of_nonneg_left hXaδ'2 (by norm_num)
      have hpos : 0 ≤ 11 / (P.G * S.Ω ^ 5 * S.Δ) := by positivity
      linarith [e1, e2, hpos]
    -- combine with the ℓ-budget hkey and 1/G²≤1
    have hfin : 12 * (ℓ₂ * (ℓ₂ - ℓ₁)) * (8000000000000000000000000 * (11 / (P.G * S.Ω ^ 5 * S.Δ)))
        ≤ (10:ℝ) ^ 45 / 2 * δ := by
      have hrw : 12 * (ℓ₂ * (ℓ₂ - ℓ₁)) * (8000000000000000000000000 * (11 / (P.G * S.Ω ^ 5 * S.Δ)))
          = 96000000000000000000000000 * (ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G * S.Ω ^ 5 * S.Δ))) := by
        ring
      rw [hrw]
      have hc1 : 96000000000000000000000000 * (ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G * S.Ω ^ 5 * S.Δ)))
          ≤ 96000000000000000000000000 * (16900 * (11 * δ)) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
      have hc2 : (96000000000000000000000000 : ℝ) * (16900 * (11 * δ))
          ≤ (10:ℝ) ^ 45 / 2 * δ := by
        have h10 : (10:ℝ) ^ 45 / 2 = 500000000000000000000000000000000000000000000 := by
          norm_num
        rw [h10]; nlinarith only [hδpos.le]
      exact le_trans hc1 hc2
    calc 12 * (ℓ₂ * (ℓ₂ - ℓ₁)) *
            (4000000000000000000 * (P.X * (a:ℝ) * δ' * S.B / S.D ^ 5)
              + 4000000000000000000000000 * (P.X * (a:ℝ) * δ' ^ 2 / S.D ^ 5))
        ≤ 12 * (ℓ₂ * (ℓ₂ - ℓ₁)) * (8000000000000000000000000 * (11 / (P.G * S.Ω ^ 5 * S.Δ))) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ (10:ℝ) ^ 45 / 2 * δ := hfin
  -- ===== Term2 bound =====
  -- 1 ≤ H  (from h1, G,U,Δ ≥ 1)
  have hH1 : 1 ≤ P.H := one_le_H_aux hGpos hUpos hΔpos hHpos h1 hG1 hU1 hΔ1
  have hTerm2 : |K * bb ^ 2 * (1 / d ^ 5 - 1 / dt ^ 5)| ≤ (10:ℝ) ^ 45 / 2 * δ := by
    have hd18 : d ≤ 18 * S.D := by linarith
    -- |1/d⁵ − 1/dt⁵| ≤ (5·18⁴·10¹⁷)·δ'/D⁶
    have hinv_bound : |1 / d ^ 5 - 1 / dt ^ 5|
        ≤ (5 * 18 ^ 4 * 100000 * 1000000000000 / S.D ^ 6) * δ' :=
      inv_pow5_close_aux hDpos hδ'pos.le hd_lo hd18 hdt_lo hdt_hi hd_close'
    -- bb² ≤ 10¹²·B²
    have hbb2 : bb ^ 2 ≤ 1000000000000 * S.B ^ 2 := by
      have hh : |bb| ^ 2 ≤ (1000000 * S.B) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hbb_hi 2
      rw [sq_abs, show (1000000 * S.B) ^ 2 = 1000000000000 * S.B ^ 2 by ring] at hh
      exact hh
    -- scale:  Xa·B²·δ'/D⁶ ≤ 11/(G²·Ω⁸·H)
    have hXaB2δ' : P.X * (a:ℝ) * S.B ^ 2 * δ' / S.D ^ 6 ≤ 11 / (P.G ^ 2 * S.Ω ^ 8 * P.H) := by
      have heq : P.X * (a:ℝ) * S.B ^ 2 * δ' / S.D ^ 6
          = (P.X * (a:ℝ) * S.B ^ 3 / S.D ^ 6) / S.Δ := by
        rw [hδ'B]; field_simp
      have hstep : (P.X * (a:ℝ) * S.B ^ 3 / S.D ^ 6) / S.Δ
          ≤ (11 / (P.G * S.Ω ^ 5 * S.R)) / S.Δ :=
        (div_le_div_iff_of_pos_right hΔpos).mpr hXaB3
      have hRΔ' : 11 / (P.G * S.Ω ^ 5 * S.R) / S.Δ = 11 / (P.G ^ 2 * S.Ω ^ 8 * P.H) := by
        rw [div_div]
        congr 1
        rw [show P.G * S.Ω ^ 5 * S.R * S.Δ = P.G * S.Ω ^ 5 * (S.R * S.Δ) by ring, hRΔ]
        ring
      rw [heq]; rw [hRΔ'] at hstep; exact hstep
    -- δ-comparison:  ℓ₁ℓ₂(ℓ₂−ℓ₁)·11/(G²Ω⁸H) ≤ 11·δ
    have hkey2 : ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H))
        ≤ 2197000 * (11 * δ) := by
      have hs1 : ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H))
          ≤ (2197000 * (P.G ^ 3 * P.U ^ 15)) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H)) :=
        mul_le_mul_of_nonneg_right hℓ123 (by positivity)
      have hs2 : (P.G ^ 3 * P.U ^ 15) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H)) ≤ 11 * δ :=
        delta_compare2_aux hGpos hUpos hΩpos hΔpos hHpos hδeq
          (absorb_UH_aux hGpos hUpos hΩpos hΔpos hHpos h1 hband hG1 hU1 hH1 hUH)
      have hs2' : (2197000 * (P.G ^ 3 * P.U ^ 15)) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H))
          ≤ 2197000 * (11 * δ) := by
        have := mul_le_mul_of_nonneg_left hs2 (by norm_num : (0:ℝ) ≤ 2197000)
        calc (2197000 * (P.G ^ 3 * P.U ^ 15)) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H))
            = 2197000 * ((P.G ^ 3 * P.U ^ 15) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H))) := by ring
          _ ≤ 2197000 * (11 * δ) := this
      exact le_trans hs1 hs2'
    -- assemble Term2
    have habs2 : |K * bb ^ 2 * (1 / d ^ 5 - 1 / dt ^ 5)|
        = K * bb ^ 2 * |1 / d ^ 5 - 1 / dt ^ 5| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ K * bb ^ 2)]
    rw [habs2]
    -- K·bb²·|·| ≤ K·(10¹²B²)·(5·18⁴·10²²·δ'/D⁶)
    have hbig : K * bb ^ 2 * |1 / d ^ 5 - 1 / dt ^ 5|
        ≤ K * (1000000000000 * S.B ^ 2)
            * ((5 * 18 ^ 4 * 100000 * 1000000000000 / S.D ^ 6) * δ') := by
      apply mul_le_mul _ hinv_bound (abs_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_left hbb2 hKpos.le
    refine le_trans hbig ?_
    -- rewrite the bound as  12·ℓ₁ℓ₂(ℓ₂−ℓ₁)·C·(Xa·B²·δ'/D⁶)  with C = 10¹²·5·18⁴·10¹⁷
    have hrw : K * (1000000000000 * S.B ^ 2)
            * ((5 * 18 ^ 4 * 100000 * 1000000000000 / S.D ^ 6) * δ')
        = (12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000)
            * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (P.X * (a:ℝ) * S.B ^ 2 * δ' / S.D ^ 6) := by
      rw [hK, mul_div_assoc, mul_div_assoc]
      field_simp
    rw [hrw]
    -- bound the scale factor, then ℓ-budget
    have hc : (0:ℝ) ≤ 12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000 := by norm_num
    have hℓnn : 0 ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
    calc (12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000)
            * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (P.X * (a:ℝ) * S.B ^ 2 * δ' / S.D ^ 6)
        ≤ (12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000)
            * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H)) := by
          apply mul_le_mul_of_nonneg_left hXaB2δ' (by positivity)
      _ = (12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000)
            * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * (11 / (P.G ^ 2 * S.Ω ^ 8 * P.H))) := by ring
      _ ≤ (12 * (5 * 18 ^ 4 * 100000 * 1000000000000) * 1000000000000)
            * (2197000 * (11 * δ)) :=
          mul_le_mul_of_nonneg_left hkey2 hc
      _ ≤ (10:ℝ) ^ 45 / 2 * δ := by
          have h10 : (10:ℝ) ^ 45 / 2 = 500000000000000000000000000000000000000000000 := by
            norm_num
          rw [h10]; nlinarith only [hδpos.le]
  exact add_le_add hTerm1 hTerm2

end Squarefree
