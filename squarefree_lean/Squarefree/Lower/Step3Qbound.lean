import Squarefree.Lower.Step3Model
import Squarefree.Lower.Step23Combine

/-!
# §5 Step-3 per-`r` two-term bound on `|𝒬|` (writeup 808–816, 870–878)

`Qval_abs_le`: for a triple `(d, d₁, d₂)` of `D`-scale witnesses with the discrete slope
`b₀` and defect `v` pinned by `ℓ₁b₀ = d₁−d`, `ℓ₂b₀+v = d₂−d`, the defect `𝒬 = Qval`
satisfies the writeup's two-term envelope
```
|𝒬| ≤ 10³⁰·ℓ₁·(G·H·Ω/Δ³)·V₊  +  10³⁰·(G²·U¹⁵/Ω⁵),
```
where `|v| ≤ V₊`. Mechanism: from `Q_gen_expand`,
`𝒬 = 6ℓ₁Xav/d⁴ − 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xab₀²/d⁵ + O(ERR)`. The triangle inequality splits
`|𝒬|` into

* the leading `v`-term `|6ℓ₁Xav/d⁴| ≤ 66·ℓ₁(GHΩ/Δ³)V₊` (via `defect_D4_div_XA`, `|v| ≤ V₊`,
  `a ≤ 11A`, `d ≥ D`);
* the `b₀²`-term `|12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xab₀²/d⁵| ≤ const·G²U¹⁵/Ω⁵` (via `defect_XAB2_div_D5`,
  `|b₀| ≤ 3·10¹²B`, `ℓ₁ℓ₂(ℓ₂−ℓ₁) ≤ W³ = G³U¹⁵`);
* the remainder `ERR` from `Q_gen_expand`, bounded by dividing `qgen_piece_le`'s
  `PREF·ERR ≤ δ₂₃` by the lower bound `PREF ≥ D⁴/(660000·X·A)` (`d̃ ≥ D/10`, `a ≤ 11A`):
  `ERR ≤ 660000·G²U²⁰/(Δ·Ω⁵) ≤ const·G²U¹⁵/Ω⁵` (using `Δ ≥ U⁵`).

Both `b₀²`-term and `ERR` land in the single `10³⁰·G²U¹⁵/Ω⁵` envelope.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- Scale identity: `X·11·A/D⁴ = 11·(H·G·Ω/Δ³)`. -/
private theorem qb_XA_div_D4 (S : Scale P) :
    (11 : ℝ) * (P.X * S.A) / S.D ^ 4 = 11 * (P.H * P.G * S.Ω / S.Δ ^ 3) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.A Scale.D
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

set_option maxHeartbeats 6400000 in
/-- **§5 Step-3 per-`r` two-term `|𝒬|` bound.** Faithful to writeup line 874. -/
theorem Qval_abs_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ} {b₀ v Vplus : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hdwin : S.D ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * S.D)
    -- discrete slope / defect pinned to the witnesses
    (hb0def : (ℓ₁ : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ))
    (hvdef : (ℓ₂ : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ))
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hVplus : |v| ≤ Vplus) (hVplus_nn : 0 ≤ Vplus)
    (hd1ned : (d₁ : ℝ) ≠ (d : ℝ)) (hd2ned : (d₂ : ℝ) ≠ (d : ℝ))
    -- Taylor windows for `Q_gen_expand`
    (hwin2 : 4 * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ≤ (d : ℝ))
    (hwin1 : 4 * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ≤ (d : ℝ))
    -- `𝒬` in the `Fab` form (matches `Qval`'s `Ffun`-difference form)
    {𝒬 : ℝ}
    (h𝒬 : 𝒬 = (ℓ₁ : ℝ) * Fab P.X (a : ℝ) ((ℓ₂ : ℝ) * b₀ + v) (d : ℝ)
              - (ℓ₂ : ℝ) * Fab P.X (a : ℝ) ((ℓ₁ : ℝ) * b₀) (d : ℝ))
    -- regime
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) :
    |𝒬| ≤ 10 ^ 34 * (ℓ₁ : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus
          + 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
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
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  have hAposS : 0 < S.A := by unfold Scale.A; positivity
  have hdD : S.D ≤ (d : ℝ) := hdwin.1
  have hdRpos : 0 < (d : ℝ) := lt_of_lt_of_le hDpos hdD
  -- ===== d̃ ≍ D =====
  obtain ⟨hdt_lo, hdt_hi⟩ :=
    dtilde_asymp_D hAD haR hr0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdt_def
  have hdt_pos : 0 < dt := lt_of_lt_of_le (by positivity) hdt_lo
  -- ===== Q_gen_expand =====
  have hℓ2bv : (ℓ₂ : ℝ) * b₀ + v ≠ 0 := by rw [hvdef]; exact sub_ne_zero.mpr hd2ned
  have hℓ1b₀ : (ℓ₁ : ℝ) * b₀ ≠ 0 := by rw [hb0def]; exact sub_ne_zero.mpr hd1ned
  have hQ := Q_gen_expand (X := P.X) (a := (a : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
    (ℓ₁ := (ℓ₁ : ℝ)) (ℓ₂ := (ℓ₂ : ℝ)) hXpos haR hdRpos hℓ1R hℓ12R hℓ2bv hℓ1b₀ hwin2 hwin1
  rw [← h𝒬] at hQ
  -- the leading parts
  set VTERM : ℝ := 6 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * v / (d : ℝ) ^ 4 with hVTERM_def
  set BTERM : ℝ := 12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)
      * b₀ ^ 2 / (d : ℝ) ^ 5 with hBTERM_def
  set ERR : ℝ := 12 * P.X * (a : ℝ) * (ℓ₁ : ℝ) * |v| * ((a : ℝ) + 2 * (ℓ₂ : ℝ) * |b₀| + |v|) / (d : ℝ) ^ 5
      + 400 * P.X * (a : ℝ) * (ℓ₁ : ℝ) * |(ℓ₂ : ℝ) * b₀ + v| * ((a : ℝ) + |(ℓ₂ : ℝ) * b₀ + v|) ^ 2 / (d : ℝ) ^ 6
      + 400 * P.X * (a : ℝ) * (ℓ₂ : ℝ) * (ℓ₁ : ℝ) * |b₀| * ((a : ℝ) + (ℓ₁ : ℝ) * |b₀|) ^ 2 / (d : ℝ) ^ 6
      with hERR_def
  -- triangle: |𝒬| ≤ |VTERM| + |BTERM| + ERR
  have hQ' : |𝒬 - (VTERM - BTERM)| ≤ ERR := hQ
  have htri : |𝒬| ≤ |VTERM| + |BTERM| + ERR := by
    have h1' : |𝒬| ≤ |VTERM - BTERM| + |𝒬 - (VTERM - BTERM)| := by
      have h2' := abs_add_le (VTERM - BTERM) (𝒬 - (VTERM - BTERM))
      have heq : (VTERM - BTERM) + (𝒬 - (VTERM - BTERM)) = 𝒬 := by ring
      rw [heq] at h2'; linarith [h2']
    have h3' : |VTERM - BTERM| ≤ |VTERM| + |BTERM| := abs_sub VTERM BTERM
    linarith [h1', h3', hQ']
  refine le_trans htri ?_
  -- ===========================================================
  -- BOUND 1 : |VTERM| ≤ 10³⁰·ℓ₁·(HGΩ/Δ³)·Vplus
  -- ===========================================================
  have hVbound : |VTERM| ≤ 10 ^ 34 * (ℓ₁ : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus := by
    rw [hVTERM_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < (d:ℝ) ^ 4)]
    rw [show (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ) * v) = (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ)) * v by ring]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 * (ℓ₁ : ℝ) * P.X * (a : ℝ))]
    -- numerator ≤ 6ℓ₁X·(11A)·Vplus, denom ≥ D⁴
    have hnum : (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ)) * |v|
        ≤ (6 * (ℓ₁ : ℝ) * P.X * (11 * S.A)) * Vplus := by
      apply mul_le_mul _ hVplus (abs_nonneg _) (by positivity)
      have hrw : (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ)) = (6 * (ℓ₁ : ℝ) * P.X) * (a : ℝ) := by ring
      have hrw' : (6 * (ℓ₁ : ℝ) * P.X * (11 * S.A)) = (6 * (ℓ₁ : ℝ) * P.X) * (11 * S.A) := by ring
      rw [hrw, hrw']
      exact mul_le_mul_of_nonneg_left ha_hi (by positivity)
    have hden : S.D ^ 4 ≤ (d : ℝ) ^ 4 := pow_le_pow_left₀ hDpos.le hdD 4
    have hfrac : (6 * (ℓ₁ : ℝ) * P.X * (a : ℝ)) * |v| / (d : ℝ) ^ 4
        ≤ (6 * (ℓ₁ : ℝ) * P.X * (11 * S.A)) * Vplus / S.D ^ 4 := by
      apply div_le_div₀ (by positivity) hnum (by positivity) hden
    refine le_trans hfrac ?_
    -- (6ℓ₁X·11A·Vplus)/D⁴ = 6·ℓ₁·Vplus·(11·XA/D⁴) = 66·ℓ₁·Vplus·(HGΩ/Δ³)
    have heq : (6 * (ℓ₁ : ℝ) * P.X * (11 * S.A)) * Vplus / S.D ^ 4
        = 6 * (ℓ₁ : ℝ) * Vplus * ((11 : ℝ) * (P.X * S.A) / S.D ^ 4) := by
      rw [mul_div_assoc, mul_div_assoc]
      ring
    rw [heq, qb_XA_div_D4]
    -- 6·ℓ₁·Vplus·11·(HGΩ/Δ³) ≤ 10³⁰·ℓ₁·(HGΩ/Δ³)·Vplus
    have hscale_nn : 0 ≤ P.H * P.G * S.Ω / S.Δ ^ 3 := by positivity
    have hkey : 6 * (ℓ₁ : ℝ) * Vplus * (11 * (P.H * P.G * S.Ω / S.Δ ^ 3))
        = 66 * ((ℓ₁ : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus) := by ring
    rw [hkey]
    have hcoef : (66 : ℝ) ≤ 10 ^ 34 := by norm_num
    have hpos : 0 ≤ (ℓ₁ : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcoef hpos]
  -- ===========================================================
  -- BOUND 2 : |BTERM| ≤ const·G²U¹⁵/Ω⁵
  -- ===========================================================
  have hBbound : |BTERM| ≤ 3 * 10 ^ 33 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    rw [hBTERM_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < (d:ℝ) ^ 5)]
    rw [show (12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ) * b₀ ^ 2)
          = (12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)) * b₀ ^ 2 by ring]
    have hposnum : (0:ℝ) < 12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ) := by
      have hℓ21 : (0:ℝ) < (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by linarith [hℓ12R]
      positivity
    rw [abs_mul, abs_of_nonneg (sq_nonneg b₀), abs_of_pos hposnum]
    -- bound ℓ₁ℓ₂(ℓ₂−ℓ₁) ≤ (GU⁵)³, a ≤ 11A, |b₀|² ≤ (3e12 B)², d⁵ ≥ D⁵
    have hℓfac : (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))
        ≤ 2197000 * (P.G * P.U ^ 5) ^ 3 := by
      have e1 : (ℓ₂ : ℝ) - (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ2W', hℓ1R]
      have hGU5nn : (0:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by positivity
      have s1 : (ℓ₁ : ℝ) * (ℓ₂ : ℝ) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul hℓ1W' hℓ2W' hℓ2R.le hGU5nn
      have s2 : (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))
          ≤ ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))) * (130 * (P.G * P.U ^ 5)) :=
        mul_le_mul s1 e1 (by linarith [hℓ12R]) (by positivity)
      have e3 : ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))) * (130 * (P.G * P.U ^ 5))
          = 2197000 * (P.G * P.U ^ 5) ^ 3 := by ring
      linarith [s2, e3.le, e3.ge]
    have hb0sq : b₀ ^ 2 ≤ (3000000000000 * S.B) ^ 2 := by
      have : |b₀| ^ 2 ≤ (3000000000000 * S.B) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb0 2
      rwa [sq_abs] at this
    have hd5 : S.D ^ 5 ≤ (d : ℝ) ^ 5 := pow_le_pow_left₀ hDpos.le hdD 5
    -- collapse numerator factor: 12·ℓfac·X·(11A) ≤ 12·(GU⁵)³·X·11A
    have hnum : (12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)) * b₀ ^ 2
        ≤ (12 * (2197000 * (P.G * P.U ^ 5) ^ 3) * P.X * (11 * S.A)) * (3000000000000 * S.B) ^ 2 := by
      have c1 : 12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)
          ≤ 12 * (2197000 * (P.G * P.U ^ 5) ^ 3) * P.X * (11 * S.A) := by
        have hstep1 : 12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)
            = (12 * P.X) * ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))) * (a : ℝ) := by ring
        have hstep2 : 12 * (2197000 * (P.G * P.U ^ 5) ^ 3) * P.X * (11 * S.A)
            = (12 * P.X) * (2197000 * (P.G * P.U ^ 5) ^ 3) * (11 * S.A) := by ring
        rw [hstep1, hstep2]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hℓfac (by positivity)) ha_hi
          haR.le (by positivity)
      have c1nn : 0 ≤ 12 * (2197000 * (P.G * P.U ^ 5) ^ 3) * P.X * (11 * S.A) := by positivity
      exact mul_le_mul c1 hb0sq (by positivity) c1nn
    have hfrac : (12 * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * P.X * (a : ℝ)) * b₀ ^ 2 / (d : ℝ) ^ 5
        ≤ (12 * (2197000 * (P.G * P.U ^ 5) ^ 3) * P.X * (11 * S.A)) * (3000000000000 * S.B) ^ 2 / S.D ^ 5 := by
      apply div_le_div₀ (by positivity) hnum (by positivity) hd5
    refine le_trans hfrac ?_
    -- collapse: const·(GU⁵)³·X·A·B²/D⁵ = const·G³U¹⁵·(XAB²/D⁵) = const·G³U¹⁵/(GΩ⁵)
    have hXAB2 : P.X * S.A * S.B ^ 2 / S.D ^ 5 = 1 / (P.G * S.Ω ^ 5) := defect_XAB2_div_D5 S
    have heq : (12 * (2197000 * (P.G * P.U ^ 5) ^ 3) * P.X * (11 * S.A)) * (3000000000000 * S.B) ^ 2 / S.D ^ 5
        = (12 * 2197000 * 11 * 3000000000000 ^ 2) * (P.G ^ 3 * P.U ^ 15) * (P.X * S.A * S.B ^ 2 / S.D ^ 5) := by
      rw [mul_div_assoc]
      ring
    rw [heq, hXAB2]
    -- const·G³U¹⁵·(1/(GΩ⁵)) = const·G²U¹⁵/Ω⁵
    have heq2 : (12 * 2197000 * 11 * 3000000000000 ^ 2 : ℝ) * (P.G ^ 3 * P.U ^ 15) * (1 / (P.G * S.Ω ^ 5))
        = (12 * 2197000 * 11 * 3000000000000 ^ 2) * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
      field_simp <;> ring
    rw [heq2]
    have hcoef : (12 * 2197000 * 11 * 3000000000000 ^ 2 : ℝ) ≤ 3 * 10 ^ 33 := by norm_num
    have hpos : 0 ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcoef hpos]
  -- ===========================================================
  -- BOUND 3 : ERR ≤ const·G²U¹⁵/Ω⁵   (divide qgen_piece_le by PREF ≥ D⁴/(660000 XA))
  -- ===========================================================
  have hERRbound : ERR ≤ 660000 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    set PREF : ℝ := dt ^ 4 / (6 * P.X * (a : ℝ)) with hPREF_def
    have hPREF_pos : 0 < PREF := by rw [hPREF_def]; positivity
    -- qgen_piece_le: PREF · ERR ≤ δ₂₃
    have hqp := qgen_piece_le (P := P) (S := S) (a := a) (r := r) (ℓ₁ := (ℓ₁ : ℝ))
      (ℓ₂ := (ℓ₂ : ℝ)) (b₀ := b₀) (v := v) (d := (d : ℝ))
      hAD ha0 ha_lo ha_hi hr_lo hr_hi hℓ1R hℓ12R hℓ2W hdwin hb0 hv h1 hband
      hG1 hU1 hΔ1 hH1 hΩU hUbig
    rw [← hdt_def, ← hPREF_def, ← hERR_def] at hqp
    -- PREF lower bound: PREF ≥ D⁴/(660000·X·A)
    have hdt4 : S.D ^ 4 / 10 ^ 4 ≤ dt ^ 4 := by
      have h1' : (S.D / 10) ^ 4 ≤ dt ^ 4 := pow_le_pow_left₀ (by positivity) hdt_lo 4
      have : (S.D / 10) ^ 4 = S.D ^ 4 / 10 ^ 4 := by ring
      linarith [h1', this.ge, this.le]
    have hPREF_lo : S.D ^ 4 / (660000 * (P.X * S.A)) ≤ PREF := by
      rw [hPREF_def]
      -- 6·X·a ≤ 6·X·11A = 66·X·A;  dt⁴ ≥ D⁴/10⁴ ⟹ PREF ≥ (D⁴/10⁴)/(66XA) = D⁴/(660000 XA)
      have hden : 6 * P.X * (a : ℝ) ≤ 66 * (P.X * S.A) := by nlinarith [ha_hi, hXpos.le]
      have hden_pos : 0 < 6 * P.X * (a : ℝ) := by positivity
      calc S.D ^ 4 / (660000 * (P.X * S.A))
          = (S.D ^ 4 / 10 ^ 4) / (66 * (P.X * S.A)) := by
            rw [div_div]; congr 1; ring
        _ ≤ dt ^ 4 / (66 * (P.X * S.A)) :=
            div_le_div_of_nonneg_right hdt4 (by positivity)
        _ ≤ dt ^ 4 / (6 * P.X * (a : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hden
    -- ERR ≥ 0
    have hERR_nn : 0 ≤ ERR := by
      rw [hERR_def]; positivity
    -- δ₂₃ ≥ PREF · ERR ≥ (D⁴/(660000 XA)) · ERR  ⟹  ERR ≤ δ₂₃·660000·XA/D⁴
    have hstep : S.D ^ 4 / (660000 * (P.X * S.A)) * ERR
        ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := by
      calc S.D ^ 4 / (660000 * (P.X * S.A)) * ERR
          ≤ PREF * ERR := mul_le_mul_of_nonneg_right hPREF_lo hERR_nn
        _ ≤ S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6) := hqp
    -- multiply both sides by 660000·XA/D⁴ to isolate ERR
    have hmul_pos : 0 < 660000 * (P.X * S.A) / S.D ^ 4 := by positivity
    have hERR_le : ERR
        ≤ (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6)) * (660000 * (P.X * S.A) / S.D ^ 4) := by
      have hh := mul_le_mul_of_nonneg_right hstep hmul_pos.le
      -- LHS simplifies to ERR
      have hsimp : S.D ^ 4 / (660000 * (P.X * S.A)) * ERR * (660000 * (P.X * S.A) / S.D ^ 4) = ERR := by
        field_simp
      rwa [hsimp] at hh
    refine le_trans hERR_le ?_
    -- δ₂₃·660000·XA/D⁴ = 660000·(XA/D⁴)·Δ²GU²⁰/(HΩ⁶) = 660000·(HGΩ/Δ³)·Δ²GU²⁰/(HΩ⁶)
    --                  = 660000·G²U²⁰/(Δ·Ω⁵)
    have hXAD4 : P.X * S.A / S.D ^ 4 = P.H * P.G * S.Ω / S.Δ ^ 3 := by
      have hHpos' := P.H_pos; have hGpos' := P.G_pos
      have hΔpos' := S.Δ_pos; have hΩpos' := S.Ω_pos
      unfold Scale.A Scale.D
      rw [P.X_eq_G_mul_H_pow_five]
      field_simp
    have heqf : (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6)) * (660000 * (P.X * S.A) / S.D ^ 4)
        = 660000 * (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6)) * (P.X * S.A / S.D ^ 4) := by ring
    rw [heqf, hXAD4]
    -- = 660000 · Δ²GU²⁰/(HΩ⁶) · HGΩ/Δ³ = 660000 · G²U²⁰/(Δ·Ω⁵)
    have hcollapse : (660000 : ℝ) * (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6))
          * (P.H * P.G * S.Ω / S.Δ ^ 3)
        = 660000 * (P.G ^ 2 * P.U ^ 20 / (S.Δ * S.Ω ^ 5)) := by
      field_simp <;> ring
    rw [hcollapse]
    -- 660000·G²U²⁰/(Δ·Ω⁵) ≤ 660000·G²U¹⁵/Ω⁵  via Δ ≥ U⁵
    have hΔU5 : P.U ^ 5 ≤ S.Δ := by
      have hG2 : (1:ℝ) ≤ P.G ^ 2 := by nlinarith [hG1]
      have : P.U ^ 5 ≤ P.G ^ 2 * P.U ^ 5 := by nlinarith [hG2, pow_pos hUpos 5]
      linarith [hΔreg, this]
    have hkey : P.U ^ 20 / S.Δ ≤ P.U ^ 15 := by
      rw [div_le_iff₀ hΔpos]
      have := mul_le_mul_of_nonneg_left hΔU5 (pow_nonneg hUpos.le 15)
      calc P.U ^ 20 = P.U ^ 15 * P.U ^ 5 := by ring
        _ ≤ P.U ^ 15 * S.Δ := this
    have hrw1 : (P.G ^ 2 * P.U ^ 20 / (S.Δ * S.Ω ^ 5))
        = (P.G ^ 2 / S.Ω ^ 5) * (P.U ^ 20 / S.Δ) := by
      field_simp <;> ring
    have hrw2 : (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) = (P.G ^ 2 / S.Ω ^ 5) * P.U ^ 15 := by
      rw [div_mul_eq_mul_div]
    rw [hrw1, hrw2]
    have hbase_nn : 0 ≤ (660000 : ℝ) * (P.G ^ 2 / S.Ω ^ 5) := by positivity
    calc (660000 : ℝ) * ((P.G ^ 2 / S.Ω ^ 5) * (P.U ^ 20 / S.Δ))
        = (660000 * (P.G ^ 2 / S.Ω ^ 5)) * (P.U ^ 20 / S.Δ) := by ring
      _ ≤ (660000 * (P.G ^ 2 / S.Ω ^ 5)) * P.U ^ 15 :=
          mul_le_mul_of_nonneg_left hkey hbase_nn
      _ = 660000 * ((P.G ^ 2 / S.Ω ^ 5) * P.U ^ 15) := by ring
  -- ===========================================================
  -- ASSEMBLE : |VTERM| + |BTERM| + ERR ≤ V-envelope + (const+660000)·G²U¹⁵/Ω⁵
  -- ===========================================================
  have henv_nn : 0 ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 := by positivity
  have hsum : (3 * 10 ^ 33 : ℝ) + 660000 ≤ 10 ^ 34 := by norm_num
  have hBE : |BTERM| + ERR ≤ 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    have := mul_le_mul_of_nonneg_right hsum henv_nn
    nlinarith [hBbound, hERRbound, this]
  linarith [hVbound, hBE]

end Squarefree
