import Squarefree.Lower.UpsilonNearInt

/-!
# §5 Step-4 `Υ` near-integer, the `b ≤ 0` (reflected) form (writeup 996–998)

The `b ≥ 0` keystone `inD_distInt_Shat` / `Upsilon_near_int` (`UpsilonNearInt.lean`) assumes the
mixed-second-difference shift is nonnegative.  But the actual §5 §3 data has all shifts
`bᵢ < 0`: the `d*`-spacings come from a **decreasing** `d̃ₐ` (cf. `bt_abs_bounds`).  This file
clones the two keystone lemmas for `b ≤ 0` via the sympy-verified reflection identity

  `Ŝ_{a,b}(d) = − Ŝ_{a,−b}(d+b)`   (`Shat_reflect`, `DefectShat.lean`),

whose four spacing points `{(d+b), (d+b)+a, d, d+a}` are exactly the same set
`{d, d+a, d+b, d+a+b}` as `Ŝ_{a,b}(d)`, just re-ordered.  Combined with `distInt_neg`, the
`b ≤ 0` per-`Ŝ` bound is `distInt(Ŝ_{a,b}(d)) ≤ 15·H/(d+b)`, and the assembled
`distInt(Υ) ≤ 45·Wval⁴·H/D = 45·Wval⁴/Δ` is preserved.
-/

namespace Squarefree

open Squarefree.Counting

/-- **Per-`Ŝ` near-integer brick for `b ≤ 0`** (the reflected form of `inD_distInt_Shat`).
For decreasing-`d̃ₐ` spacings all shifts `bᵢ < 0`, so the `b ≥ 0` brick does not apply directly.
Using `Shat_reflect` (`Ŝ_{a,b}(d) = −Ŝ_{a,−b}(d+b)`) and `distInt_neg`, we reduce to the
`b ≥ 0` brick at `(a, −b, d+b)`; the four spacing points `{d+b, (d+b)+a, d, d+a}` are the same
set `{d, d+a, d+b, d+a+b}`.  The conclusion bound becomes `15·H/(d+b)` (the new base point). -/
theorem inD_distInt_Shat_neg {X H : ℝ} {a b d : ℤ}
    (hX : 0 < X) (hd : 0 < ((d + b : ℤ) : ℝ)) (ha : 0 ≤ a) (_hb : b ≤ 0)
    (hab : (a : ℝ) + ((-b : ℤ) : ℝ) ≤ ((d + b : ℤ) : ℝ))
    (hin0 : inD X H d) (hin1 : inD X H (d + a))
    (hin2 : inD X H (d + b)) (hin3 : inD X H (d + a + b)) :
    distInt (Shat X (a : ℝ) (b : ℝ) (d : ℝ)) ≤ 15 * H / ((d + b : ℤ) : ℝ) := by
  -- reflect: `Shat X a b d = - Shat X a (-b) (d+b)`
  rw [show (Shat X (a : ℝ) (b : ℝ) (d : ℝ))
        = - Shat X (a : ℝ) ((-b : ℤ) : ℝ) (((d + b : ℤ)) : ℝ) by
      rw [Shat_reflect X (a : ℝ) (b : ℝ) (d : ℝ)]; push_cast; ring_nf]
  rw [distInt_neg]
  -- the `(d+b)+(-b) = d` and `(d+b)+a+(-b) = d+a` integer normalizations
  have hin0' : inD X H ((d + b) + (-b)) := by rw [show (d + b) + (-b) = d by ring]; exact hin0
  have hin1' : inD X H ((d + b) + a + (-b)) := by
    rw [show (d + b) + a + (-b) = d + a by ring]; exact hin1
  have hin2' : inD X H ((d + b) + a) := by
    rw [show (d + b) + a = d + a + b by ring]; exact hin3
  exact inD_distInt_Shat (a := a) (b := -b) (d := d + b) hX hd ha
    (by linarith : (0:ℤ) ≤ -b) hab hin2 hin2' hin0' hin1'

/-- **§5 Step-4 near-integer of `Υ`, `b ≤ 0` form** (writeup 996–998).  Mirror of
`Upsilon_near_int` for the decreasing-`d̃ₐ` triples, where all three shifts `bᵢ ≤ 0`.  Each
per-`Ŝ` bound uses `inD_distInt_Shat_neg`, giving `distInt(Ŝᵢ) ≤ 15·H/(dᵢ+bᵢ)`; the window
hypotheses `S.D ≤ dᵢ+bᵢ` (each shifted point `dᵢ+bᵢ` is itself a `d*`-witness in `[D,2D]`)
turn this into `≤ 15·H/D`, so the assembled bound `distInt(Υ) ≤ 45·Wval⁴·H/D = 45·Wval⁴/Δ` is
preserved. -/
theorem Upsilon_near_int_neg {P : Globals} (S : Scale P)
    {a d d' b₁ b₂ b₃ ℓ₁ ℓ₂ : ℤ}
    (ha : 0 ≤ a) (hb1 : b₁ ≤ 0) (hb2 : b₂ ≤ 0) (hb3 : b₃ ≤ 0)
    (hℓ1 : 0 ≤ ℓ₁) (hℓ12 : ℓ₁ ≤ ℓ₂)
    (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    -- the shifted base points `d+bᵢ`, `d'+b₃` are `d*`-witnesses in `[D, 2D]`
    (hDd1 : S.D ≤ ((d + b₁ : ℤ) : ℝ)) (hDd2 : S.D ≤ ((d + b₂ : ℤ) : ℝ))
    (hDd3 : S.D ≤ ((d' + b₃ : ℤ) : ℝ))
    (hab1 : (a : ℝ) + ((-b₁ : ℤ) : ℝ) ≤ ((d + b₁ : ℤ) : ℝ))
    (hab2 : (a : ℝ) + ((-b₂ : ℤ) : ℝ) ≤ ((d + b₂ : ℤ) : ℝ))
    (hab3 : (a : ℝ) + ((-b₃ : ℤ) : ℝ) ≤ ((d' + b₃ : ℤ) : ℝ))
    -- `Ŝ₁ = Shat a b₁ d`: four points `d, d+a, d+b₁, d+a+b₁ ∈ 𝒟`
    (hS1_0 : inD P.X P.H d) (hS1_1 : inD P.X P.H (d + a))
    (hS1_2 : inD P.X P.H (d + b₁)) (hS1_3 : inD P.X P.H (d + a + b₁))
    -- `Ŝ₂ = Shat a b₂ d`
    (hS2_2 : inD P.X P.H (d + b₂)) (hS2_3 : inD P.X P.H (d + a + b₂))
    -- `Ŝ₃ = Shat a b₃ d'`: four points `d', d'+a, d'+b₃, d'+a+b₃ ∈ 𝒟`
    (hS3_0 : inD P.X P.H d') (hS3_1 : inD P.X P.H (d' + a))
    (hS3_2 : inD P.X P.H (d' + b₃)) (hS3_3 : inD P.X P.H (d' + a + b₃)) :
    distInt
      ((((ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ)) : ℝ) * Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ)
        - (((ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ)) : ℝ) * Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ)
        + (((ℓ₁ ^ 2 * ℓ₂ ^ 2 : ℤ)) : ℝ) * Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ))
      ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D := by
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd1pos : 0 < ((d + b₁ : ℤ) : ℝ) := lt_of_lt_of_le hDpos hDd1
  have hd2pos : 0 < ((d + b₂ : ℤ) : ℝ) := lt_of_lt_of_le hDpos hDd2
  have hd3pos : 0 < ((d' + b₃ : ℤ) : ℝ) := lt_of_lt_of_le hDpos hDd3
  -- ℓ-bounds as reals
  have hℓ1R : (0 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : (0 : ℝ) ≤ (ℓ₂ : ℝ) := le_trans hℓ1R hℓ12R
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hWnn : (0 : ℝ) ≤ 130 * P.Wval := by rw [Globals.Wval]; positivity
  have hℓ1W : (ℓ₁ : ℝ) ≤ 130 * P.Wval := le_trans hℓ12R hℓ2W
  -- the three per-Ŝ near-integer bounds (reflected brick)
  have hB1 : distInt (Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ)) ≤ 15 * P.H / ((d + b₁ : ℤ) : ℝ) :=
    inD_distInt_Shat_neg hXpos hd1pos ha hb1 hab1 hS1_0 hS1_1 hS1_2 hS1_3
  have hB2 : distInt (Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ)) ≤ 15 * P.H / ((d + b₂ : ℤ) : ℝ) :=
    inD_distInt_Shat_neg hXpos hd2pos ha hb2 hab2 hS1_0 hS1_1 hS2_2 hS2_3
  have hB3 : distInt (Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ)) ≤ 15 * P.H / ((d' + b₃ : ℤ) : ℝ) :=
    inD_distInt_Shat_neg hXpos hd3pos ha hb3 hab3 hS3_0 hS3_1 hS3_2 hS3_3
  -- each `15 H/(dᵢ+bᵢ) ≤ 15 H/D`
  have hHdD : ∀ {dd : ℝ}, S.D ≤ dd → 0 < dd →
      (15 : ℝ) * P.H / dd ≤ 15 * P.H / S.D := by
    intro dd hdd hddpos
    apply div_le_div_of_nonneg_left (by positivity) hDpos hdd
  have hB1' : distInt (Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ)) ≤ 15 * P.H / S.D :=
    le_trans hB1 (hHdD hDd1 hd1pos)
  have hB2' : distInt (Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ)) ≤ 15 * P.H / S.D :=
    le_trans hB2 (hHdD hDd2 hd2pos)
  have hB3' : distInt (Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ)) ≤ 15 * P.H / S.D :=
    le_trans hB3 (hHdD hDd3 hd3pos)
  -- the integer coefficients are nonneg and ≤ Wval⁴
  have hK1nn : (0 : ℤ) ≤ ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hK2nn : (0 : ℤ) ≤ ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hK3nn : (0 : ℤ) ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 := by positivity
  have hℓ21W : (ℓ₂ : ℝ) - (ℓ₁ : ℝ) ≤ 130 * P.Wval := by linarith [hℓ2W, hℓ1R]
  have hℓ21nn : (0 : ℝ) ≤ (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by linarith [hℓ12R]
  -- Wval⁴ bound for each K (each is a product of four ℓ-factors ≤ Wval)
  have hKW : ∀ {x y z w : ℝ}, 0 ≤ x → x ≤ 130 * P.Wval → 0 ≤ y → y ≤ 130 * P.Wval →
      0 ≤ z → z ≤ 130 * P.Wval → 0 ≤ w → w ≤ 130 * P.Wval →
      x * y * z * w ≤ (130 * P.Wval) ^ 4 := by
    intro x y z w hx0 hxW hy0 hyW hz0 hzW hw0 hwW
    have h1 : x * y ≤ (130 * P.Wval) * (130 * P.Wval) := mul_le_mul hxW hyW hy0 hWnn
    have h2 : x * y * z ≤ ((130 * P.Wval) * (130 * P.Wval)) * (130 * P.Wval) :=
      mul_le_mul h1 hzW hz0 (by positivity)
    have h3 : x * y * z * w
        ≤ (((130 * P.Wval) * (130 * P.Wval)) * (130 * P.Wval)) * (130 * P.Wval) :=
      mul_le_mul h2 hwW hw0 (by positivity)
    nlinarith [h3]
  have hK1W : ((ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ) ≤ (130 * P.Wval) ^ 4 := by
    have : ((ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ)
        = (ℓ₂ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) := by
      push_cast; ring
    rw [this]
    exact hKW hℓ2R hℓ2W hℓ2R hℓ2W hℓ21nn hℓ21W hℓ21nn hℓ21W
  have hK2W : ((ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ) ≤ (130 * P.Wval) ^ 4 := by
    have : ((ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ)
        = (ℓ₁ : ℝ) * (ℓ₁ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) := by
      push_cast; ring
    rw [this]
    exact hKW hℓ1R hℓ1W hℓ1R hℓ1W hℓ21nn hℓ21W hℓ21nn hℓ21W
  have hK3W : ((ℓ₁ ^ 2 * ℓ₂ ^ 2 : ℤ) : ℝ) ≤ (130 * P.Wval) ^ 4 := by
    have : ((ℓ₁ ^ 2 * ℓ₂ ^ 2 : ℤ) : ℝ)
        = (ℓ₁ : ℝ) * (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * (ℓ₂ : ℝ) := by push_cast; ring
    rw [this]
    exact hKW hℓ1R hℓ1W hℓ1R hℓ1W hℓ2R hℓ2W hℓ2R hℓ2W
  -- per-term: distInt(Kᵢ·Ŝᵢ) ≤ Kᵢ·(15 H/D) ≤ Wval⁴·(15 H/D)
  have hHDnn : (0 : ℝ) ≤ 15 * P.H / S.D := by positivity
  have hT1 : distInt (((ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ) * Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ))
      ≤ (130 * P.Wval) ^ 4 * (15 * P.H / S.D) := by
    refine le_trans (distInt_intMul_bound hK1nn hB1') ?_
    exact mul_le_mul_of_nonneg_right hK1W hHDnn
  have hT2 : distInt (((ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ) * Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ))
      ≤ (130 * P.Wval) ^ 4 * (15 * P.H / S.D) := by
    refine le_trans (distInt_intMul_bound hK2nn hB2') ?_
    exact mul_le_mul_of_nonneg_right hK2W hHDnn
  have hT3 : distInt (((ℓ₁ ^ 2 * ℓ₂ ^ 2 : ℤ) : ℝ) * Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ))
      ≤ (130 * P.Wval) ^ 4 * (15 * P.H / S.D) := by
    refine le_trans (distInt_intMul_bound hK3nn hB3') ?_
    exact mul_le_mul_of_nonneg_right hK3W hHDnn
  -- triangle: distInt(A - B + C) ≤ distInt A + distInt B + distInt C
  set A : ℝ := ((ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ) * Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ) with hA
  set B : ℝ := ((ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 : ℤ) : ℝ) * Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ) with hB
  set C : ℝ := ((ℓ₁ ^ 2 * ℓ₂ ^ 2 : ℤ) : ℝ) * Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ) with hC
  have htri : distInt (A - B + C) ≤ distInt A + distInt B + distInt C := by
    have h1 : distInt (A - B) ≤ distInt A + distInt B := distInt_sub_le A B
    have h2 : distInt ((A - B) + C) ≤ distInt (A - B) + distInt C := by
      have := distInt_sub_le (A - B) (-C)
      rwa [sub_neg_eq_add, distInt_neg] at this
    linarith [h1, h2]
  refine le_trans htri ?_
  -- 3·15·130⁴ = 1.285245·10¹⁰ ≤ 10¹¹
  have hWHD : (0 : ℝ) ≤ P.Wval ^ 4 * P.H / S.D := by
    rw [Globals.Wval]; positivity
  have hsum : (130 * P.Wval) ^ 4 * (15 * P.H / S.D) + (130 * P.Wval) ^ 4 * (15 * P.H / S.D)
      + (130 * P.Wval) ^ 4 * (15 * P.H / S.D) ≤ 10 ^ 11 * P.Wval ^ 4 * P.H / S.D := by
    have he : (130 * P.Wval) ^ 4 * (15 * P.H / S.D) + (130 * P.Wval) ^ 4 * (15 * P.H / S.D)
        + (130 * P.Wval) ^ 4 * (15 * P.H / S.D)
        = 12852450000 * (P.Wval ^ 4 * P.H / S.D) := by ring
    rw [he]
    calc (12852450000 : ℝ) * (P.Wval ^ 4 * P.H / S.D)
        ≤ 10 ^ 11 * (P.Wval ^ 4 * P.H / S.D) :=
          mul_le_mul_of_nonneg_right (by norm_num) hWHD
      _ = 10 ^ 11 * P.Wval ^ 4 * P.H / S.D := by ring
  linarith [hT1, hT2, hT3, hsum]

end Squarefree
