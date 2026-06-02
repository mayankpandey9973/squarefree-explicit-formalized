import Squarefree.Params
import Squarefree.Asymp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §3 structural layer: spacing in `𝒟_a` (layer L?)

Faithful `sorry`-stubbed statements of Lemma 3.1 and Prop 3.2 from `../explicit_writeup.md`
(lines 270–322 and 346–393). These elaborate but are not yet proved; each `sorry` is tagged
`STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree

/-- `d ∈ 𝒟` at window `[X, X+H]`. Matches the predicate inside `dCard`. -/
def inD (X H : ℝ) (d : ℤ) : Prop :=
  ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H

/-- `d ∈ 𝒟_a`: `d, d+a` consecutive 𝒟-elements at gap `a` (`a>0`). -/
def inDa (X H : ℝ) (a d : ℤ) : Prop :=
  0 < a ∧ inD X H d ∧ inD X H (d + a) ∧ ∀ d' : ℤ, d < d' → d' < d + a → ¬ inD X H d'

/-- Roth's quantity `R_a(d) = -(2d-a)X/d² + (2d+3a)X/(d+a)²` (over ℝ). -/
noncomputable def Rfun (X : ℝ) (a d : ℝ) : ℝ :=
  -(2 * d - a) * X / d ^ 2 + (2 * d + 3 * a) * X / (d + a) ^ 2

/-- `#𝒟_a[D,2D]`. -/
noncomputable def DaCard (X H : ℝ) (a : ℤ) (D : ℝ) : ℕ :=
  ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter (fun d => inDa X H a d)).card

/-- The closed-form value `S_{a,b}(d)` of the divided combination, over `ℝ`. -/
private noncomputable def Sab (X a b d : ℝ) : ℝ :=
  -(b - a) * X / d ^ 2 + (b + a) * X / (d + a) ^ 2
    - (b + a) * X / (d + b) ^ 2 + (b - a) * X / (d + a + b) ^ 2

/-- Exact factorization of `S_{a,b}(d)` (sympy-verified; writeup line 299). -/
private theorem Sab_factor (X a b d : ℝ)
    (hd : d ≠ 0) (hda : d + a ≠ 0) (hdb : d + b ≠ 0) (hdab : d + a + b ≠ 0) :
    Sab X a b d =
      X * a * b * (a - b) * (a + b) * (a + b + 2 * d)
        * (a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2)
        / (d ^ 2 * (d + a) ^ 2 * (d + b) ^ 2 * (d + a + b) ^ 2) := by
  unfold Sab
  field_simp
  ring

/-- Cube of the threshold expression collapses the `rpow`s. -/
private theorem thresh_cube (c av Δ H X : ℝ) (hav : 0 < av) (hΔ : 0 < Δ)
    (hHX : 0 ≤ H ^ 5 / X) :
    (c * av ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ)) ^ 3
      = c ^ 3 * Δ ^ (5 : ℕ) * (H ^ 5 / X) / av := by
  have e1 : (av ^ (-1/3 : ℝ)) ^ (3:ℕ) = av⁻¹ := by
    rw [← Real.rpow_natCast (av ^ (-1/3 : ℝ)) 3, ← Real.rpow_mul hav.le]
    rw [show (-1/3 : ℝ) * (3:ℕ) = (-1 : ℝ) by push_cast; ring, Real.rpow_neg_one]
  have e2 : (Δ ^ (5/3 : ℝ)) ^ (3:ℕ) = Δ ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast (Δ ^ (5/3 : ℝ)) 3, ← Real.rpow_mul hΔ.le]
    rw [show (5/3 : ℝ) * (3:ℕ) = (5 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have e3 : ((H ^ 5 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) = H ^ 5 / X := by
    rw [← Real.rpow_natCast ((H ^ 5 / X) ^ (1/3 : ℝ)) 3, ← Real.rpow_mul hHX]
    norm_num
  have hpow : (c * av ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ)) ^ 3
      = c ^ 3 * (av ^ (-1/3 : ℝ)) ^ (3:ℕ) * (Δ ^ (5/3 : ℝ)) ^ (3:ℕ)
        * ((H ^ 5 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) := by ring
  rw [hpow, e1, e2, e3]
  field_simp

set_option maxHeartbeats 1600000 in
/-- Analytic core of Lemma 3.1, over `ℝ`: with `Dv = H·Δ`, the closed form `Sab X a b d`
satisfies `|Sab| < 1/2`, `8 b H/Dv² ≤ |Sab|/2`, and `Sab ≠ 0`, in the writeup's regime.
Factored out to keep the elaboration context of `lemma_3_1` small. -/
private theorem lemma_3_1_core (X H Δ a b d : ℝ)
    (hX : 0 < X) (hH : 0 < H) (hΔ : 1 ≤ Δ)
    (ha : 0 < a) (hb : 0 < b) (hb2a : 2 * a ≤ b)
    (hd_lo : H * Δ ≤ d) (hd_hi : d ≤ 2 * (H * Δ))
    (hab_small : a + b ≤ H * Δ) (hbD : b ≤ H * Δ / 2)
    (ha_lo : (64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ) ≤ a)
    (b_bound : b < (1 / 10 : ℝ) * a ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ)) :
    |Sab X a b d| < 1 / 2 ∧
      8 * b * H / (H * Δ) ^ 2 ≤ (1 / 2) * |Sab X a b d| ∧ 0 < |Sab X a b d| := by
  set Dv : ℝ := H * Δ with hDvdef
  have hΔpos : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have hDpos : 0 < Dv := by rw [hDvdef]; positivity
  clear_value Dv
  have hdR : (0:ℝ) < d := lt_of_lt_of_le hDpos hd_lo
  have hapos : (0:ℝ) ≤ a := ha.le
  have hbpos : (0:ℝ) ≤ b := hb.le
  have hahalf : a ≤ b / 2 := by linarith
  -- the four points and their range
  have hp2_lo : Dv ≤ d + a := by linarith
  have hp3_lo : Dv ≤ d + b := by linarith
  have hp4_lo : Dv ≤ d + a + b := by linarith
  have hp1ne : d ≠ 0 := ne_of_gt hdR
  have hp2ne : d + a ≠ 0 := by positivity
  have hp3ne : d + b ≠ 0 := by positivity
  have hp4ne : d + a + b ≠ 0 := by positivity
  have hp1_hi : d ≤ 3 * Dv := by linarith
  have hp2_hi : d + a ≤ 3 * Dv := by linarith
  have hp3_hi : d + b ≤ 3 * Dv := by linarith
  have hp4_hi : d + a + b ≤ 3 * Dv := by linarith
  -- denominator
  set Den : ℝ := d ^ 2 * (d + a) ^ 2 * (d + b) ^ 2 * (d + a + b) ^ 2 with hDendef
  have hDenpos : 0 < Den := by rw [hDendef]; positivity
  -- positive numerator
  set Num : ℝ := X * a * b * (b - a) * (a + b) * (a + b + 2 * d)
      * (a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2) with hNumdef
  have hbma : (0:ℝ) < b - a := by linarith
  have hNumpos : 0 < Num := by rw [hNumdef]; have h2 : (0:ℝ) < a + b + 2 * d := by linarith
                               positivity
  have hSvalfac : Sab X a b d = -Num / Den := by
    rw [Sab_factor X a b d hp1ne hp2ne hp3ne hp4ne, hNumdef, hDendef]; ring
  have hSabs : |Sab X a b d| = Num / Den := by
    rw [hSvalfac, abs_div, abs_neg, abs_of_pos hNumpos, abs_of_pos hDenpos]
  -- factor bounds
  -- bounds: a, b ≤ Dv and d ≤ 2 Dv
  have haDv : a ≤ Dv := by linarith
  have hbDv : b ≤ Dv := by linarith
  have hsq : Dv * Dv = Dv ^ 2 := by ring
  have hF4_ub : a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2 ≤ 17 * Dv ^ 2 := by
    have q1 : a * b ≤ Dv ^ 2 := by
      have h := mul_le_mul haDv hbDv hbpos hDpos.le; rw [hsq] at h; exact h
    have q2 : a * d ≤ 2 * Dv ^ 2 := by
      have h := mul_le_mul haDv hd_hi hdR.le hDpos.le
      calc a * d ≤ Dv * (2 * Dv) := h
        _ = 2 * Dv ^ 2 := by ring
    have q3 : b * d ≤ 2 * Dv ^ 2 := by
      have h := mul_le_mul hbDv hd_hi hdR.le hDpos.le
      calc b * d ≤ Dv * (2 * Dv) := h
        _ = 2 * Dv ^ 2 := by ring
    have q4 : d ^ 2 ≤ 4 * Dv ^ 2 := by
      have h := mul_le_mul hd_hi hd_hi hdR.le (by linarith : (0:ℝ) ≤ 2 * Dv)
      calc d ^ 2 = d * d := by ring
        _ ≤ (2 * Dv) * (2 * Dv) := h
        _ = 4 * Dv ^ 2 := by ring
    linarith
  have hF4_lb : 2 * Dv ^ 2 ≤ a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2 := by
    have hdd : Dv ^ 2 ≤ d ^ 2 := by
      have h := mul_le_mul hd_lo hd_lo hDpos.le hdR.le
      calc Dv ^ 2 = Dv * Dv := by ring
        _ ≤ d * d := h
        _ = d ^ 2 := by ring
    have hterms : (0:ℝ) ≤ a * b + 2 * a * d + 2 * b * d := by positivity
    linarith
  -- Num bounds
  have hNum_ub : Num ≤ 170 * X * a * b ^ 3 * Dv ^ 3 := by
    rw [hNumdef]
    have hpre : (0:ℝ) ≤ X * a * b := by positivity
    calc X * a * b * (b - a) * (a + b) * (a + b + 2 * d)
            * (a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2)
        ≤ X * a * b * b * (2 * b) * (5 * Dv) * (17 * Dv ^ 2) := by
          gcongr <;> first | linarith | exact hF4_ub | positivity
      _ = 170 * X * a * b ^ 3 * Dv ^ 3 := by ring
  have hNum_lb : 2 * X * a * b ^ 3 * Dv ^ 3 ≤ Num := by
    rw [hNumdef]
    calc 2 * X * a * b ^ 3 * Dv ^ 3
        = X * a * b * (b / 2) * b * (2 * Dv) * (2 * Dv ^ 2) := by ring
      _ ≤ X * a * b * (b - a) * (a + b) * (a + b + 2 * d)
            * (a * b + 2 * a * d + 2 * b * d + 2 * d ^ 2) := by
          gcongr <;> first | linarith | exact hF4_lb | positivity
  -- Den bounds
  have hDen_lb : Dv ^ 8 ≤ Den := by
    rw [hDendef]
    calc Dv ^ 8 = Dv ^ 2 * Dv ^ 2 * Dv ^ 2 * Dv ^ 2 := by ring
      _ ≤ d ^ 2 * (d + a) ^ 2 * (d + b) ^ 2 * (d + a + b) ^ 2 := by
          gcongr <;> first | exact hDpos.le | exact hd_lo | exact hp2_lo | exact hp3_lo | exact hp4_lo
  have hDen_ub : Den ≤ 6561 * Dv ^ 8 := by
    rw [hDendef]
    calc d ^ 2 * (d + a) ^ 2 * (d + b) ^ 2 * (d + a + b) ^ 2
        ≤ (3 * Dv) ^ 2 * ((3 * Dv)) ^ 2 * ((3 * Dv)) ^ 2 * ((3 * Dv)) ^ 2 := by
          gcongr <;> first | exact hp1_hi | exact hp2_hi | exact hp3_hi | exact hp4_hi | positivity
      _ = 6561 * Dv ^ 8 := by ring
  -- |Sab| upper and lower in terms of X a b³ / Dv⁵
  have hDv5 : (0:ℝ) < Dv ^ 5 := by positivity
  have hSub : |Sab X a b d| ≤ 170 * X * a * b ^ 3 / Dv ^ 5 := by
    rw [hSabs, div_le_div_iff₀ hDenpos hDv5]
    calc Num * Dv ^ 5 ≤ (170 * X * a * b ^ 3 * Dv ^ 3) * Dv ^ 5 := by
          apply mul_le_mul_of_nonneg_right hNum_ub hDv5.le
      _ = 170 * X * a * b ^ 3 * (Dv ^ 8) := by ring
      _ ≤ 170 * X * a * b ^ 3 * Den := by
          apply mul_le_mul_of_nonneg_left hDen_lb (by positivity)
  have hSlb : (2 / 6561 : ℝ) * X * a * b ^ 3 / Dv ^ 5 ≤ |Sab X a b d| := by
    rw [hSabs, div_le_div_iff₀ hDv5 hDenpos]
    calc (2 / 6561 : ℝ) * X * a * b ^ 3 * Den
        ≤ (2 / 6561 : ℝ) * X * a * b ^ 3 * (6561 * Dv ^ 8) := by
          apply mul_le_mul_of_nonneg_left hDen_ub (by positivity)
      _ = (2 * X * a * b ^ 3 * Dv ^ 3) * Dv ^ 5 := by ring
      _ ≤ Num * Dv ^ 5 := by apply mul_le_mul_of_nonneg_right hNum_lb hDv5.le
  refine ⟨?_, ?_, ?_⟩
  · -- |Sab| < 1/2 from b_bound (cubed)
    have hb3 : b ^ 3 < (1 / 1000 : ℝ) * Δ ^ (5 : ℕ) * (H ^ 5 / X) / a := by
      have hpos : (0:ℝ) < (1 / 10 : ℝ) * a ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ) := by
        have : (0:ℝ) ≤ H ^ 5 / X := by positivity
        have h1 : (0:ℝ) < a ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos ha _
        have h2 : (0:ℝ) < Δ ^ (5/3 : ℝ) := Real.rpow_pos_of_pos hΔpos _
        have h3 : (0:ℝ) < (H ^ 5 / X) ^ (1/3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
        positivity
      calc b ^ 3 < ((1 / 10 : ℝ) * a ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ)) ^ 3 := by
            gcongr ?_ ^ 3 <;> first | exact hbpos | exact b_bound
        _ = (1 / 10 : ℝ) ^ 3 * Δ ^ (5 : ℕ) * (H ^ 5 / X) / a :=
            thresh_cube (1/10) a Δ H X ha hΔpos (by positivity)
        _ = (1 / 1000 : ℝ) * Δ ^ (5 : ℕ) * (H ^ 5 / X) / a := by norm_num
    -- so 170 X a b³/Dv⁵ < 1/2
    have hkey : 170 * X * a * b ^ 3 / Dv ^ 5 < 1 / 2 := by
      have hXab : (0:ℝ) < 170 * X * a := by positivity
      have step : 170 * X * a * b ^ 3 < 170 * X * a * ((1 / 1000 : ℝ) * Δ ^ (5 : ℕ) * (H ^ 5 / X) / a) := by
        apply mul_lt_mul_of_pos_left hb3 hXab
      have hsimp : 170 * X * a * ((1 / 1000 : ℝ) * Δ ^ (5 : ℕ) * (H ^ 5 / X) / a)
          = (170 / 1000 : ℝ) * Δ ^ (5 : ℕ) * H ^ 5 := by
        field_simp
      rw [hsimp] at step
      rw [div_lt_iff₀ hDv5]
      have hDv5eq : Dv ^ 5 = H ^ 5 * Δ ^ (5 : ℕ) := by rw [hDvdef]; push_cast; ring
      rw [hDv5eq]
      have hΔ5pos : (0:ℝ) ≤ Δ ^ (5 : ℕ) := by positivity
      have hH5pos : (0:ℝ) ≤ H ^ 5 := by positivity
      have hgap : (170 / 1000 : ℝ) * Δ ^ (5 : ℕ) * H ^ 5 ≤ (1 / 2) * (H ^ 5 * Δ ^ (5 : ℕ)) := by
        nlinarith [mul_nonneg hΔ5pos hH5pos]
      linarith [step, hgap]
    exact lt_of_le_of_lt hSub hkey
  · -- error ≤ (1/2)|Sab|, via |Sab| ≥ (2/6561) X a b³/Dv⁵ and ha_lo
    have ha3 : (64 : ℝ) ^ 3 * Δ ^ (4 : ℕ) * (H ^ 4 / X) ≤ a ^ 3 := by
      have hcube : ((64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)) ^ 3
          = (64 : ℝ) ^ 3 * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by
        have e2 : (Δ ^ (4/3 : ℝ)) ^ (3:ℕ) = Δ ^ (4 : ℕ) := by
          rw [← Real.rpow_natCast (Δ ^ (4/3 : ℝ)) 3, ← Real.rpow_mul hΔpos.le]
          rw [show (4/3 : ℝ) * (3:ℕ) = (4 : ℕ) by push_cast; ring, Real.rpow_natCast]
        have e3 : ((H ^ 4 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) = H ^ 4 / X := by
          rw [← Real.rpow_natCast ((H ^ 4 / X) ^ (1/3 : ℝ)) 3,
            ← Real.rpow_mul (by positivity)]; norm_num
        calc ((64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)) ^ 3
            = (64:ℝ) ^ 3 * (Δ ^ (4/3 : ℝ)) ^ (3:ℕ) * ((H ^ 4 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) := by ring
          _ = (64 : ℝ) ^ 3 * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by rw [e2, e3]
      rw [← hcube]
      gcongr <;> first | positivity | exact ha_lo
    -- key cross-multiplied inequality: 8 b H Dv³ ≤ (1/6561) X a b³
    have hcross : 8 * b * H * Dv ^ 3 ≤ (1 / 6561 : ℝ) * X * a * b ^ 3 := by
      -- reduce to 8 H Dv³ ≤ (1/6561) X a b²
      have hba2 : a ^ 2 ≤ b ^ 2 := by nlinarith [hb2a, hapos, hbpos]
      have hXa3 : (262144 : ℝ) * Δ ^ (4 : ℕ) * H ^ 4 ≤ X * a ^ 3 := by
        have hXpos := hX
        have : (64 : ℝ) ^ 3 * Δ ^ (4 : ℕ) * (H ^ 4 / X) * X ≤ a ^ 3 * X :=
          mul_le_mul_of_nonneg_right ha3 hX.le
        have hdiv : (64 : ℝ) ^ 3 * Δ ^ (4 : ℕ) * (H ^ 4 / X) * X = (64:ℝ)^3 * Δ ^ (4:ℕ) * H ^ 4 := by
          field_simp
        rw [hdiv] at this
        norm_num at this ⊢
        linarith [this]
      -- 8 H Dv³ ≤ (1/6561) X a³  (uses Δ ≥ 1, Dv = HΔ)
      have hDv3 : Dv ^ 3 = H ^ 3 * Δ ^ 3 := by rw [hDvdef]; ring
      have hstep : 8 * H * Dv ^ 3 ≤ (1 / 6561 : ℝ) * X * a ^ 3 := by
        rw [hDv3]
        have hΔ4 : Δ ^ (4:ℕ) = Δ ^ 3 * Δ := by ring
        have hub2 : (1 / 6561 : ℝ) * X * a ^ 3 ≥ (1 / 6561 : ℝ) * (262144 * Δ ^ (4:ℕ) * H ^ 4) := by
          have : (1 / 6561 : ℝ) * (262144 * Δ ^ (4:ℕ) * H ^ 4) ≤ (1 / 6561 : ℝ) * (X * a ^ 3) := by
            apply mul_le_mul_of_nonneg_left hXa3 (by norm_num)
          linarith [this]
        have hΔ3pos : (0:ℝ) < Δ ^ 3 := by positivity
        have hH4pos : (0:ℝ) < H ^ 4 := by positivity
        have : (1 / 6561 : ℝ) * (262144 * Δ ^ (4:ℕ) * H ^ 4) - 8 * H * (H ^ 3 * Δ ^ 3)
            = (Δ ^ 3 * H ^ 4) * ((262144 / 6561 : ℝ) * Δ - 8) := by rw [hΔ4]; ring
        nlinarith [hub2, mul_nonneg hΔ3pos.le hH4pos.le, hΔ]
      -- now multiply by b > 0 and use a²·(ab) ≤ b²·(ab)
      have hlast : (1 / 6561 : ℝ) * X * a ^ 3 * b ≤ (1 / 6561 : ℝ) * X * a * b ^ 3 := by
        have hcoef : (0:ℝ) ≤ (1 / 6561 : ℝ) * X * a * b := by positivity
        nlinarith [hba2, hcoef, mul_nonneg hapos hbpos]
      have heqb : 8 * b * H * Dv ^ 3 = b * (8 * H * Dv ^ 3) := by ring
      rw [heqb]
      calc b * (8 * H * Dv ^ 3) ≤ b * ((1 / 6561 : ℝ) * X * a ^ 3) :=
            mul_le_mul_of_nonneg_left hstep hbpos
        _ = (1 / 6561 : ℝ) * X * a ^ 3 * b := by ring
        _ ≤ (1 / 6561 : ℝ) * X * a * b ^ 3 := hlast
    -- convert hcross to the divided form, chain through hSlb
    have hmid : 8 * b * H / Dv ^ 2 ≤ (1 / 2) * ((2 / 6561 : ℝ) * X * a * b ^ 3 / Dv ^ 5) := by
      have hDv2 : (0:ℝ) < Dv ^ 2 := by positivity
      have hDv3pos : (0:ℝ) < Dv ^ 3 := by positivity
      rw [div_le_iff₀ hDv2]
      have hrhs : (1 / 2) * ((2 / 6561 : ℝ) * X * a * b ^ 3 / Dv ^ 5) * Dv ^ 2
          = (1 / 6561 : ℝ) * X * a * b ^ 3 / Dv ^ 3 := by
        field_simp
      rw [hrhs, le_div_iff₀ hDv3pos]
      linarith [hcross]
    calc 8 * b * H / Dv ^ 2
        ≤ (1 / 2) * ((2 / 6561 : ℝ) * X * a * b ^ 3 / Dv ^ 5) := hmid
      _ ≤ (1 / 2) * |Sab X a b d| := by
          apply mul_le_mul_of_nonneg_left hSlb (by norm_num)
  · rw [hSabs]; positivity

/-- **Lemma 3.1**: spacing lower bound in `𝒟_a` (writeup 270–322).

The faithful range hypotheses the writeup proof uses (auditor-flagged) are threaded
explicitly: `d ≍ D` (`S.D ≤ d ≤ 2 S.D`), the regime bound `b ≤ D/2` (the writeup's `b ≪ D`),
the lower bound `a ≫ Δ^{4/3}(H⁴/X)^{1/3}`, and `Δ ≥ 1` (a dyadic scale). -/
theorem lemma_3_1 : ∃ c : ℝ, 0 < c ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a →
      ∀ d b : ℤ, 0 < b → inDa P.X P.H a d → inDa P.X P.H a (d + b) →
        (∃ d' : ℤ, d < d' ∧ d' < d + b ∧ inDa P.X P.H a d') →
        (S.D ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * S.D) →
        (b : ℝ) ≤ S.D / 2 →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ (a : ℝ) →
        1 ≤ S.Δ →
        c * (a : ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ) ≤ (b : ℝ) := by
  refine ⟨(1 : ℝ) / 10, by norm_num, ?_⟩
  intro P S a ha d b hb hDa_d hDa_db ⟨d', hdd', hd'db, hDa_d'⟩ hd hbD ha_lo hΔ
  -- abbreviations
  set X := P.X with hXdef
  set H := P.H with hHdef
  set Δ := S.Δ with hΔdef
  set Dv := S.D with hDvdef
  have hXpos : 0 < X := P.X_pos
  have hHpos : 0 < H := P.H_pos
  have hΔpos : 0 < Δ := S.Δ_pos
  have hDeq : Dv = H * Δ := rfl
  have hDpos : 0 < Dv := by rw [hDeq]; positivity
  obtain ⟨hd_lo, hd_hi⟩ := hd
  -- positivity of the integer quantities, as reals
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  -- extract the four `inD` memberships
  obtain ⟨-, hD1, hD2, hgap_d⟩ := hDa_d         -- d ∈ 𝒟, d+a ∈ 𝒟, (d,d+a)∩𝒟 = ∅
  obtain ⟨-, hD3, hD4, -⟩ := hDa_db             -- d+b ∈ 𝒟, (d+b)+a ∈ 𝒟
  obtain ⟨-, hDd', -, hgap_d'⟩ := hDa_d'        -- d' ∈ 𝒟, (d',d'+a)∩𝒟 = ∅
  -- `b ≥ 2a` (writeup line 283)
  have hb2a : 2 * a ≤ b := by
    have hd'ge : d + a ≤ d' := by
      by_contra h; push_neg at h; exact hgap_d d' hdd' h hDd'
    have hdbge : d' + a ≤ d + b := by
      by_contra h; push_neg at h; exact hgap_d' (d + b) (by omega) h hD3
    omega
  have hb2aR : 2 * (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2a
  have habR : (a : ℝ) ≤ (b : ℝ) := by linarith
  -- the four points, as reals
  set p1 : ℝ := (d : ℝ) with hp1
  set p2 : ℝ := (d : ℝ) + (a : ℝ) with hp2
  set p3 : ℝ := (d : ℝ) + (b : ℝ) with hp3
  set p4 : ℝ := (d : ℝ) + (a : ℝ) + (b : ℝ) with hp4
  -- each point lies in [Dv, 3 Dv]
  have hab_small : (a : ℝ) + (b : ℝ) ≤ Dv := by linarith [hbD]
  have hp1_lo : Dv ≤ p1 := hd_lo
  have hp1_hi : p1 ≤ 3 * Dv := by rw [hp1]; linarith
  have hp2_lo : Dv ≤ p2 := by rw [hp2]; linarith
  have hp2_hi : p2 ≤ 3 * Dv := by rw [hp2]; linarith
  have hp3_lo : Dv ≤ p3 := by rw [hp3]; linarith
  have hp3_hi : p3 ≤ 3 * Dv := by rw [hp3]; linarith
  have hp4_lo : Dv ≤ p4 := by rw [hp4]; linarith
  have hp4_hi : p4 ≤ 3 * Dv := by rw [hp4]; linarith
  have hp1_pos : 0 < p1 := lt_of_lt_of_le hDpos hp1_lo
  have hp2_pos : 0 < p2 := lt_of_lt_of_le hDpos hp2_lo
  have hp3_pos : 0 < p3 := lt_of_lt_of_le hDpos hp3_lo
  have hp4_pos : 0 < p4 := lt_of_lt_of_le hDpos hp4_lo
  have hp1sq : (0:ℝ) < p1 ^ 2 := by positivity
  have hp2sq : (0:ℝ) < p2 ^ 2 := by positivity
  have hp3sq : (0:ℝ) < p3 ^ 2 := by positivity
  have hp4sq : (0:ℝ) < p4 ^ 2 := by positivity
  -- extract integers; rewrite each membership in terms of the points pᵢ²
  obtain ⟨m1, hm1lo, hm1hi⟩ := hD1
  obtain ⟨m2, hm2lo, hm2hi⟩ := hD2
  obtain ⟨m3, hm3lo, hm3hi⟩ := hD3
  obtain ⟨m4, hm4lo, hm4hi⟩ := hD4
  push_cast at hm2lo hm2hi hm3lo hm3hi hm4lo hm4hi
  -- canonicalize the square of the fourth point, `(↑d+↑b+↑a)² = p4²`
  have hp4sqeq : ((d : ℝ) + (b : ℝ) + (a : ℝ)) ^ 2 = p4 ^ 2 := by rw [hp4]; ring
  rw [hp4sqeq] at hm4lo hm4hi
  -- collect, in pᵢ² form: `X ≤ mᵢ pᵢ² ≤ X + H`
  have h1 : X ≤ (m1 : ℝ) * p1 ^ 2 ∧ (m1 : ℝ) * p1 ^ 2 ≤ X + H := ⟨hm1lo, hm1hi⟩
  have h2 : X ≤ (m2 : ℝ) * p2 ^ 2 ∧ (m2 : ℝ) * p2 ^ 2 ≤ X + H := ⟨hm2lo, hm2hi⟩
  have h3 : X ≤ (m3 : ℝ) * p3 ^ 2 ∧ (m3 : ℝ) * p3 ^ 2 ≤ X + H := ⟨hm3lo, hm3hi⟩
  have h4 : X ≤ (m4 : ℝ) * p4 ^ 2 ∧ (m4 : ℝ) * p4 ^ 2 ≤ X + H := ⟨hm4lo, hm4hi⟩
  -- error terms eᵢ = mᵢ - X/pᵢ², with 0 ≤ eᵢ ≤ H/pᵢ²
  set e1 : ℝ := (m1 : ℝ) - X / p1 ^ 2 with he1def
  set e2 : ℝ := (m2 : ℝ) - X / p2 ^ 2 with he2def
  set e3 : ℝ := (m3 : ℝ) - X / p3 ^ 2 with he3def
  set e4 : ℝ := (m4 : ℝ) - X / p4 ^ 2 with he4def
  have ebound : ∀ (m : ℤ) (p : ℝ), 0 < p ^ 2 → X ≤ (m : ℝ) * p ^ 2 →
      (m : ℝ) * p ^ 2 ≤ X + H → 0 ≤ (m : ℝ) - X / p ^ 2 ∧ (m : ℝ) - X / p ^ 2 ≤ H / p ^ 2 := by
    intro m p hp hlo hhi
    have hpne : p ^ 2 ≠ 0 := ne_of_gt hp
    have key : ((m : ℝ) - X / p ^ 2) * p ^ 2 = (m : ℝ) * p ^ 2 - X := by
      rw [sub_mul, div_mul_cancel₀ X hpne]
    constructor
    · have h0 : 0 ≤ ((m : ℝ) - X / p ^ 2) * p ^ 2 := by rw [key]; linarith
      exact (mul_nonneg_iff_of_pos_right hp).mp h0
    · rw [le_div_iff₀ hp, key]; linarith
  obtain ⟨he1lo, he1hi⟩ := ebound m1 p1 hp1sq h1.1 h1.2
  obtain ⟨he2lo, he2hi⟩ := ebound m2 p2 hp2sq h2.1 h2.2
  obtain ⟨he3lo, he3hi⟩ := ebound m3 p3 hp3sq h3.1 h3.2
  obtain ⟨he4lo, he4hi⟩ := ebound m4 p4 hp4sq h4.1 h4.2
  -- The integer `J` (writeup line 287) and its real value.
  set J : ℤ := -(b - a) * m1 + (b + a) * m2 - (b + a) * m3 + (b - a) * m4 with hJdef
  set Sval : ℝ := Sab X (a : ℝ) (b : ℝ) (d : ℝ) with hSdef
  set errsum : ℝ := -((b : ℝ) - a) * e1 + ((b : ℝ) + a) * e2
      - ((b : ℝ) + a) * e3 + ((b : ℝ) - a) * e4 with herrdef
  -- `J = Sval + errsum`  (writeup line 291)
  have hp1ne : p1 ≠ 0 := ne_of_gt hp1_pos
  have hp2ne : p2 ≠ 0 := ne_of_gt hp2_pos
  have hp3ne : p3 ≠ 0 := ne_of_gt hp3_pos
  have hp4ne : p4 ≠ 0 := ne_of_gt hp4_pos
  -- `Sval` in explicit pᵢ-form (definitional, since d+a = p2 etc.)
  have hSexpl : Sval = -((b : ℝ) - a) * X / p1 ^ 2 + ((b : ℝ) + a) * X / p2 ^ 2
      - ((b : ℝ) + a) * X / p3 ^ 2 + ((b : ℝ) - a) * X / p4 ^ 2 := by
    rw [hSdef]; unfold Sab; rfl
  -- `mᵢ = X/pᵢ² + eᵢ`
  have hm1eq : (m1 : ℝ) = X / p1 ^ 2 + e1 := by rw [he1def]; ring
  have hm2eq : (m2 : ℝ) = X / p2 ^ 2 + e2 := by rw [he2def]; ring
  have hm3eq : (m3 : ℝ) = X / p3 ^ 2 + e3 := by rw [he3def]; ring
  have hm4eq : (m4 : ℝ) = X / p4 ^ 2 + e4 := by rw [he4def]; ring
  have hJval : (J : ℝ) = Sval + errsum := by
    rw [hJdef]; push_cast
    rw [hSexpl, herrdef, hm1eq, hm2eq, hm3eq, hm4eq]
    ring
  have hDv2pos : (0:ℝ) < Dv ^ 2 := by positivity
  -- error bound `|errsum| ≤ 8 b H / Dv²`  (writeup: O((a+b) H/D²))
  have hHpe : ∀ p : ℝ, Dv ≤ p → H / p ^ 2 ≤ H / Dv ^ 2 := by
    intro p hp
    have hpsq : Dv ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hDpos.le hp 2
    exact div_le_div_of_nonneg_left hHpos.le hDv2pos hpsq
  have he1' : e1 ≤ H / Dv ^ 2 := le_trans he1hi (hHpe p1 hp1_lo)
  have he2' : e2 ≤ H / Dv ^ 2 := le_trans he2hi (hHpe p2 hp2_lo)
  have he3' : e3 ≤ H / Dv ^ 2 := le_trans he3hi (hHpe p3 hp3_lo)
  have he4' : e4 ≤ H / Dv ^ 2 := le_trans he4hi (hHpe p4 hp4_lo)
  have hHDpos : (0:ℝ) ≤ H / Dv ^ 2 := by positivity
  have hcoef2 : (b : ℝ) + a ≤ 2 * b := by linarith
  -- each `|coef · eᵢ| ≤ 2 b (H/Dv²)`
  have hMnn : (0:ℝ) ≤ 2 * (b:ℝ) * (H / Dv ^ 2) := by positivity
  have tabs1 : |(-((b : ℝ) - a)) * e1| ≤ 2 * b * (H / Dv ^ 2) := by
    rw [abs_mul, abs_of_nonpos (by linarith : (-((b:ℝ)-a)) ≤ 0), abs_of_nonneg he1lo]
    have : (b:ℝ) - a ≤ 2 * b := by linarith
    calc -(-((b:ℝ)-a)) * e1 = ((b:ℝ)-a) * e1 := by ring
      _ ≤ 2 * b * (H / Dv ^ 2) := mul_le_mul this he1' he1lo (by linarith)
  have tabs2 : |((b : ℝ) + a) * e2| ≤ 2 * b * (H / Dv ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (b:ℝ)+a), abs_of_nonneg he2lo]
    exact mul_le_mul hcoef2 he2' he2lo (by linarith)
  have tabs3 : |((b : ℝ) + a) * e3| ≤ 2 * b * (H / Dv ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (b:ℝ)+a), abs_of_nonneg he3lo]
    exact mul_le_mul hcoef2 he3' he3lo (by linarith)
  have tabs4 : |((b : ℝ) - a) * e4| ≤ 2 * b * (H / Dv ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (b:ℝ)-a), abs_of_nonneg he4lo]
    exact mul_le_mul (by linarith) he4' he4lo (by linarith)
  have herr_bound : |errsum| ≤ 8 * (b : ℝ) * H / Dv ^ 2 := by
    have heq : errsum = (-((b : ℝ) - a)) * e1 + (((b : ℝ) + a) * e2
        + ((-(((b : ℝ) + a) * e3)) + ((b : ℝ) - a) * e4)) := by rw [herrdef]; ring
    have htri : |errsum| ≤ |(-((b : ℝ) - a)) * e1| + (|((b : ℝ) + a) * e2|
        + (|((b : ℝ) + a) * e3| + |((b : ℝ) - a) * e4|)) := by
      rw [heq]
      have b3 : |(-(((b : ℝ) + a) * e3)) + ((b : ℝ) - a) * e4|
          ≤ |((b : ℝ) + a) * e3| + |((b : ℝ) - a) * e4| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
      have b2 : |((b : ℝ) + a) * e2 + ((-(((b : ℝ) + a) * e3)) + ((b : ℝ) - a) * e4)|
          ≤ |((b : ℝ) + a) * e2| + (|((b : ℝ) + a) * e3| + |((b : ℝ) - a) * e4|) := by
        refine le_trans (abs_add_le _ _) ?_; gcongr
      refine le_trans (abs_add_le _ _) ?_; gcongr
    have hsum : 8 * (b : ℝ) * H / Dv ^ 2 = 2 * b * (H / Dv ^ 2) + (2 * b * (H / Dv ^ 2)
        + (2 * b * (H / Dv ^ 2) + 2 * b * (H / Dv ^ 2))) := by ring
    rw [hsum]
    linarith [htri, tabs1, tabs2, tabs3, tabs4]
  -- Suppose the bound fails; derive the contrapositive hypothesis `b < threshold`.
  by_contra hcon
  push_neg at hcon
  -- range hypotheses in the `H*Δ` form the core expects
  have hd_lo' : H * Δ ≤ (d : ℝ) := by rw [← hDeq]; exact hd_lo
  have hd_hi' : (d : ℝ) ≤ 2 * (H * Δ) := by rw [← hDeq]; exact hd_hi
  have hab_small' : (a : ℝ) + b ≤ H * Δ := by rw [← hDeq]; exact hab_small
  have hbD' : (b : ℝ) ≤ H * Δ / 2 := by rw [← hDeq]; exact hbD
  obtain ⟨hSlt, herr_dom, hSpos⟩ :=
    lemma_3_1_core X H Δ (a : ℝ) (b : ℝ) (d : ℝ) hXpos hHpos hΔ haR hbR hb2aR
      hd_lo' hd_hi' hab_small' hbD' ha_lo hcon
  -- `Sval = Sab X a b d`, `|errsum| ≤ 8 b H/(HΔ)²`
  have herr_dom' : |errsum| ≤ (1 / 2) * |Sval| := by
    have : (8 * (b : ℝ) * H / Dv ^ 2) = 8 * (b : ℝ) * H / (H * Δ) ^ 2 := by rw [hDeq]
    calc |errsum| ≤ 8 * (b : ℝ) * H / Dv ^ 2 := herr_bound
      _ = 8 * (b : ℝ) * H / (H * Δ) ^ 2 := this
      _ ≤ (1 / 2) * |Sab X (a : ℝ) (b : ℝ) (d : ℝ)| := herr_dom
      _ = (1 / 2) * |Sval| := by rw [hSdef]
  -- |Jreal| < 1 and 0 < |Jreal|, contradicting integrality
  have hJabs_lt : |(J : ℝ)| < 1 := by
    rw [hJval]
    calc |Sval + errsum| ≤ |Sval| + |errsum| := abs_add_le _ _
      _ ≤ |Sval| + (1 / 2) * |Sval| := by linarith [herr_dom']
      _ = (3 / 2) * |Sval| := by ring
      _ < (3 / 2) * (1 / 2) := by apply mul_lt_mul_of_pos_left hSlt (by norm_num)
      _ < 1 := by norm_num
  have hJabs_pos : 0 < |(J : ℝ)| := by
    rw [hJval]
    have h1 : |Sval| - |errsum| ≤ |Sval + errsum| := by
      have hbd := abs_sub_abs_le_abs_sub Sval (-errsum)
      simp only [abs_neg, sub_neg_eq_add] at hbd
      linarith [hbd]
    have hge : (1 / 2) * |Sval| ≤ |Sval + errsum| := by linarith [herr_dom', h1]
    have hSvalpos : 0 < |Sval| := by rw [hSdef]; exact hSpos
    linarith [hge, hSvalpos]
  -- integrality contradiction
  have hJzero : J = 0 := by
    by_contra hJne
    have : (1 : ℤ) ≤ |J| := Int.one_le_abs hJne
    have : (1 : ℝ) ≤ |(J : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast this
    linarith [hJabs_lt]
  rw [hJzero] at hJabs_pos
  simp at hJabs_pos

/-- **Prop 3.2** (writeup 346–393). Fiber bound is the STATED WEAK (non-sharp) form. -/
theorem prop_3_2 : ∃ (c₁ C₁ C₂ C₃ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a → ∀ (D : ℝ), 0 < D → ∀ (dtil : ℝ → ℝ),
      ∃ (Ra : Finset ℕ) (dStar : ℕ → ℤ),
        (∀ r ∈ Ra, inDa P.X P.H a (dStar r)) ∧
        (∀ r ∈ Ra, c₁ * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ C₁ * S.R) ∧
        (∀ r ∈ Ra, Rfun P.X (a : ℝ) (dtil (r : ℝ)) = (r : ℝ)) ∧
        ((DaCard P.X P.H a D : ℝ) ≤ C₂ * (Ra.card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ))) ∧
        (∀ r ∈ Ra, |(dStar r : ℝ) - dtil (r : ℝ)| ≤ C₃ * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3)) := by
  sorry -- STUB: prop_3_2

/-- `𝐃(Ω) := ∑_{a∼A} #𝒟_a` (writeup line 2008), the dyadic `A`-block sum of `DaCard`. -/
noncomputable def DBlock (P : Globals) (S : Scale P) (D : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (DaCard P.X P.H a D : ℝ)

end Squarefree
