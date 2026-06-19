import Squarefree.Lower.DefectShat
import Squarefree.Lower.QNearInt

/-!
# §5 Step-4 `Υ` near-integer (writeup 996–998)

The §5 large-defect range is controlled by the near-integer property of the corrected
mixed second difference `Ŝ_{a,b}` (`Shat`, `DefectShat.lean`).  On `𝒟_a` one has
`Ŝ_{a,b}(d) ∈ ℤ + O(H/d)` (writeup 999, `R_a(d) ∈ ℤ + O(1/Δ)`), because `Ŝ_{a,b}(d)`
is an **integer**-coefficient combination of the four atoms `X/r²` at
`r ∈ {d, d+a, d+b, d+a+b}` — each within `O(H/r²)` of an integer on `𝒟` — and the
coefficients (`2d−b`, `−2a+b−2d`, `−3b−2d`, `2a+3b+2d`) are integers because `a,b,d ∈ ℤ`.

This file proves:

* `inD_distInt_Shat` — the per-`Ŝ` brick: `distInt (Ŝ_{a,b}(d)) ≤ 15·H/d` from `inD` at the
  four spacing points (the analogue of `inDa_distInt_Ffun`).
* `Upsilon_near_int` — the assembly: `Υ = ℓ₂²(ℓ₂−ℓ₁)²·Ŝ₁ − ℓ₁²(ℓ₂−ℓ₁)²·Ŝ₂ + ℓ₁²ℓ₂²·Ŝ₃`
  is within `45·Wval⁴·H/D` of an integer (writeup 998: `Υ ∈ ℤ + O(W⁴/Δ)`; with `D = HΔ`,
  `H/D = 1/Δ`).
-/

namespace Squarefree

open Squarefree.Counting

set_option maxHeartbeats 1600000

/-- **Per-`Ŝ` near-integer brick** (writeup 999, analogue of `inDa_distInt_Ffun`).
`Ŝ_{a,b}(d) = Σ cᵢ·X/rᵢ²` over `r ∈ {d, d+a, d+b, d+a+b}` with **integer** coefficients
`c = (2d−b, −2a+b−2d, −3b−2d, 2a+3b+2d)`.  On `𝒟` each `X/rᵢ² = mᵢ − eᵢ` with
`0 ≤ eᵢ ≤ H/rᵢ²`, so `Ŝ = (integer) − Σcᵢeᵢ` is within `(Σ|cᵢ|)·H/d² ≤ 15·H/d` of an
integer (using `rᵢ ≥ d` and `4a+7b+8d ≤ 15d` from `a+b ≤ d`). -/
theorem inD_distInt_Shat {X H : ℝ} {a b d : ℤ}
    (hd : 0 < (d : ℝ)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : (a : ℝ) + (b : ℝ) ≤ (d : ℝ))
    (hin0 : inD X H d) (hin1 : inD X H (d + a))
    (hin2 : inD X H (d + b)) (hin3 : inD X H (d + a + b)) :
    distInt (Shat X (a : ℝ) (b : ℝ) (d : ℝ)) ≤ 15 * H / (d : ℝ) := by
  -- the four points and their squares
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set p0 : ℝ := (d : ℝ) with hp0
  set p1 : ℝ := (d : ℝ) + (a : ℝ) with hp1
  set p2 : ℝ := (d : ℝ) + (b : ℝ) with hp2
  set p3 : ℝ := (d : ℝ) + (a : ℝ) + (b : ℝ) with hp3
  have hp0pos : 0 < p0 := hd
  have hp1pos : 0 < p1 := by rw [hp1]; positivity
  have hp2pos : 0 < p2 := by rw [hp2]; positivity
  have hp3pos : 0 < p3 := by rw [hp3]; positivity
  have hp0sq : (0:ℝ) < p0 ^ 2 := by positivity
  have hp1sq : (0:ℝ) < p1 ^ 2 := by positivity
  have hp2sq : (0:ℝ) < p2 ^ 2 := by positivity
  have hp3sq : (0:ℝ) < p3 ^ 2 := by positivity
  -- casts of the integer points
  have hp1cast : ((d + a : ℤ) : ℝ) = p1 := by rw [hp1]; push_cast; ring
  have hp2cast : ((d + b : ℤ) : ℝ) = p2 := by rw [hp2]; push_cast; ring
  have hp3cast : ((d + a + b : ℤ) : ℝ) = p3 := by rw [hp3]; push_cast; ring
  -- multipliers
  obtain ⟨m0, hm0lo, hm0hi⟩ := hin0
  obtain ⟨m1, hm1lo, hm1hi⟩ := hin1
  obtain ⟨m2, hm2lo, hm2hi⟩ := hin2
  obtain ⟨m3, hm3lo, hm3hi⟩ := hin3
  rw [hp1cast] at hm1lo hm1hi
  rw [hp2cast] at hm2lo hm2hi
  rw [hp3cast] at hm3lo hm3hi
  -- error terms eᵢ = mᵢ - X/pᵢ², with 0 ≤ eᵢ ≤ H/pᵢ²
  set e0 : ℝ := (m0 : ℝ) - X / p0 ^ 2 with he0
  set e1 : ℝ := (m1 : ℝ) - X / p1 ^ 2 with he1
  set e2 : ℝ := (m2 : ℝ) - X / p2 ^ 2 with he2
  set e3 : ℝ := (m3 : ℝ) - X / p3 ^ 2 with he3
  have ebound : ∀ (m : ℤ) (p : ℝ), 0 < p ^ 2 → X ≤ (m : ℝ) * p ^ 2 →
      (m : ℝ) * p ^ 2 ≤ X + H → 0 ≤ (m : ℝ) - X / p ^ 2 ∧ (m : ℝ) - X / p ^ 2 ≤ H / p ^ 2 := by
    intro m p hp hlo hhi
    have hpne : p ^ 2 ≠ 0 := ne_of_gt hp
    have key : ((m : ℝ) - X / p ^ 2) * p ^ 2 = (m : ℝ) * p ^ 2 - X := by
      rw [sub_mul, div_mul_cancel₀ X hpne]
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ ((m : ℝ) - X / p ^ 2) * p ^ 2 := by rw [key]; linarith
      exact (mul_nonneg_iff_of_pos_right hp).mp h0
    · rw [le_div_iff₀ hp, key]; linarith
  obtain ⟨he0lo, he0hi⟩ := ebound m0 p0 hp0sq hm0lo hm0hi
  obtain ⟨he1lo, he1hi⟩ := ebound m1 p1 hp1sq hm1lo hm1hi
  obtain ⟨he2lo, he2hi⟩ := ebound m2 p2 hp2sq hm2lo hm2hi
  obtain ⟨he3lo, he3hi⟩ := ebound m3 p3 hp3sq hm3lo hm3hi
  -- `H ≥ 0`
  have hH0 : (0 : ℝ) ≤ H := by linarith [hm0lo, hm0hi]
  -- the integer combination n = c_d m0 + c_da m1 + c_db m2 + c_dab m3
  set n : ℤ := (2 * d - b) * m0 + (-2 * a + b - 2 * d) * m1
      + (-3 * b - 2 * d) * m2 + (2 * a + 3 * b + 2 * d) * m3 with hn
  -- `mᵢ = X/pᵢ² + eᵢ`
  have hm0eq : (m0 : ℝ) = X / p0 ^ 2 + e0 := by rw [he0]; ring
  have hm1eq : (m1 : ℝ) = X / p1 ^ 2 + e1 := by rw [he1]; ring
  have hm2eq : (m2 : ℝ) = X / p2 ^ 2 + e2 := by rw [he2]; ring
  have hm3eq : (m3 : ℝ) = X / p3 ^ 2 + e3 := by rw [he3]; ring
  -- errsum := Σ cᵢ eᵢ
  set errsum : ℝ := (2 * (d:ℝ) - b) * e0 + (-2 * (a:ℝ) + b - 2 * d) * e1
      + (-3 * (b:ℝ) - 2 * d) * e2 + (2 * (a:ℝ) + 3 * b + 2 * d) * e3 with herr
  -- Key identity: Shat = n - errsum
  have hShat_val : Shat X (a : ℝ) (b : ℝ) (d : ℝ) = (n : ℝ) - errsum := by
    rw [Shat_unfold, hn]; push_cast
    rw [show ((d:ℝ) + (a:ℝ)) = p1 from hp1.symm,
        show ((d:ℝ) + (b:ℝ)) = p2 from hp2.symm,
        show (((d:ℝ) + (b:ℝ)) + (a:ℝ)) = p3 by rw [hp3]; ring,
        show ((d:ℝ) + (a:ℝ) + (b:ℝ)) = p3 from hp3.symm]
    rw [herr, hm0eq, hm1eq, hm2eq, hm3eq]
    ring
  -- error bound: |errsum| ≤ 15 H / d
  -- each |cᵢ| ≤ |coef|, eᵢ ∈ [0, H/pᵢ²] ⊆ [0, H/d²]
  have hp0le : (d : ℝ) ≤ p0 := le_of_eq hp0.symm
  have hp1le : (d : ℝ) ≤ p1 := by rw [hp1]; linarith
  have hp2le : (d : ℝ) ≤ p2 := by rw [hp2]; linarith
  have hp3le : (d : ℝ) ≤ p3 := by rw [hp3]; linarith
  have hHpe : ∀ p : ℝ, (d:ℝ) ≤ p → H / p ^ 2 ≤ H / (d:ℝ) ^ 2 := by
    intro p hp
    have hpsq : (d:ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hd.le hp 2
    exact div_le_div_of_nonneg_left hH0 (by positivity) hpsq
  have he0' : e0 ≤ H / (d:ℝ) ^ 2 := le_trans he0hi (hHpe p0 hp0le)
  have he1' : e1 ≤ H / (d:ℝ) ^ 2 := le_trans he1hi (hHpe p1 hp1le)
  have he2' : e2 ≤ H / (d:ℝ) ^ 2 := le_trans he2hi (hHpe p2 hp2le)
  have he3' : e3 ≤ H / (d:ℝ) ^ 2 := le_trans he3hi (hHpe p3 hp3le)
  have hHDnn : (0:ℝ) ≤ H / (d:ℝ) ^ 2 := by positivity
  -- |coefᵢ| bounds: each ≤ (4a+7b+8d) is too crude per term; bound per term and sum
  -- |2d−b| ≤ 2d ; |−2a+b−2d| ≤ 2a+b+2d ; |−3b−2d| = 3b+2d ; |2a+3b+2d| = 2a+3b+2d
  have habs0 : |2 * (d:ℝ) - b| ≤ 2 * (d:ℝ) := by
    rw [abs_le]; constructor <;> linarith [hbR, hab]
  have habs1 : |(-2 * (a:ℝ) + b - 2 * d)| ≤ 2 * (a:ℝ) + b + 2 * d := by
    rw [abs_le]; constructor <;> linarith [haR, hbR]
  have habs2 : |(-3 * (b:ℝ) - 2 * d)| = 3 * (b:ℝ) + 2 * d := by
    rw [show (-3 * (b:ℝ) - 2 * d) = -(3 * b + 2 * d) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
  have habs3 : |(2 * (a:ℝ) + 3 * b + 2 * d)| = 2 * (a:ℝ) + 3 * b + 2 * d := by
    rw [abs_of_nonneg (by positivity)]
  -- bound |errsum| via triangle inequality on the four products
  have hbd : |errsum| ≤ (2 * (d:ℝ) + (2 * (a:ℝ) + b + 2 * d) + (3 * (b:ℝ) + 2 * d)
      + (2 * (a:ℝ) + 3 * b + 2 * d)) * (H / (d:ℝ) ^ 2) := by
    have t0 : |(2 * (d:ℝ) - b) * e0| ≤ (2 * (d:ℝ)) * (H / (d:ℝ) ^ 2) := by
      rw [abs_mul, abs_of_nonneg he0lo]
      exact mul_le_mul habs0 he0' he0lo (by positivity)
    have t1 : |(-2 * (a:ℝ) + b - 2 * d) * e1| ≤ (2 * (a:ℝ) + b + 2 * d) * (H / (d:ℝ) ^ 2) := by
      rw [abs_mul, abs_of_nonneg he1lo]
      exact mul_le_mul habs1 he1' he1lo (by positivity)
    have t2 : |(-3 * (b:ℝ) - 2 * d) * e2| ≤ (3 * (b:ℝ) + 2 * d) * (H / (d:ℝ) ^ 2) := by
      rw [abs_mul, abs_of_nonneg he2lo, habs2]
      exact mul_le_mul_of_nonneg_left he2' (by positivity)
    have t3 : |(2 * (a:ℝ) + 3 * b + 2 * d) * e3| ≤ (2 * (a:ℝ) + 3 * b + 2 * d) * (H / (d:ℝ) ^ 2) := by
      rw [abs_mul, abs_of_nonneg he3lo, habs3]
      exact mul_le_mul_of_nonneg_left he3' (by positivity)
    have htri : |errsum| ≤ |(2 * (d:ℝ) - b) * e0| + |(-2 * (a:ℝ) + b - 2 * d) * e1|
        + |(-3 * (b:ℝ) - 2 * d) * e2| + |(2 * (a:ℝ) + 3 * b + 2 * d) * e3| := by
      rw [herr]
      refine le_trans (abs_add_le _ _) ?_
      gcongr
      refine le_trans (abs_add_le _ _) ?_
      gcongr
      exact abs_add_le _ _
    have hsum : (2 * (d:ℝ) + (2 * (a:ℝ) + b + 2 * d) + (3 * (b:ℝ) + 2 * d)
        + (2 * (a:ℝ) + 3 * b + 2 * d)) * (H / (d:ℝ) ^ 2)
        = (2 * (d:ℝ)) * (H / (d:ℝ) ^ 2) + (2 * (a:ℝ) + b + 2 * d) * (H / (d:ℝ) ^ 2)
          + (3 * (b:ℝ) + 2 * d) * (H / (d:ℝ) ^ 2)
          + (2 * (a:ℝ) + 3 * b + 2 * d) * (H / (d:ℝ) ^ 2) := by ring
    rw [hsum]
    linarith [htri, t0, t1, t2, t3]
  -- the coefficient sum ≤ 15 d (using 4a + 7b ≤ 7(a+b) ≤ 7d)
  have hcoefsum : 2 * (d:ℝ) + (2 * (a:ℝ) + b + 2 * d) + (3 * (b:ℝ) + 2 * d)
      + (2 * (a:ℝ) + 3 * b + 2 * d) ≤ 15 * (d:ℝ) := by linarith [hab, haR, hbR]
  have herr_final : |errsum| ≤ 15 * H / (d:ℝ) := by
    refine le_trans hbd ?_
    have hstep : (2 * (d:ℝ) + (2 * (a:ℝ) + b + 2 * d) + (3 * (b:ℝ) + 2 * d)
        + (2 * (a:ℝ) + 3 * b + 2 * d)) * (H / (d:ℝ) ^ 2)
        ≤ (15 * (d:ℝ)) * (H / (d:ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcoefsum hHDnn
    refine le_trans hstep ?_
    rw [show (15 * (d:ℝ)) * (H / (d:ℝ) ^ 2) = 15 * H * ((d:ℝ) / (d:ℝ) ^ 2) by ring]
    rw [show (d:ℝ) / (d:ℝ) ^ 2 = 1 / (d:ℝ) by rw [pow_two]; field_simp]
    rw [show 15 * H * (1 / (d:ℝ)) = 15 * H / (d:ℝ) by ring]
  -- conclude: distInt Shat ≤ |Shat - n| = |errsum| ≤ 15 H / d
  have hbound : |Shat X (a : ℝ) (b : ℝ) (d : ℝ) - (n : ℝ)| ≤ 15 * H / (d:ℝ) := by
    rw [hShat_val, show ((n:ℝ) - errsum) - (n:ℝ) = -errsum by ring, abs_neg]
    exact herr_final
  exact le_trans (distInt_le_intDist _ n) hbound

/-- `distInt (-x) = distInt x`. -/
theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  refine le_antisymm ?_ ?_
  · refine le_trans (distInt_le_intDist (-x) (-round x)) ?_
    have e : (-x) - ((-round x : ℤ) : ℝ) = -(x - round x) := by push_cast; ring
    rw [e, abs_neg]; simp only [distInt, le_refl]
  · refine le_trans (distInt_le_intDist x (-round (-x))) ?_
    have e : x - ((-round (-x) : ℤ) : ℝ) = -((-x) - round (-x)) := by push_cast; ring
    rw [e, abs_neg]; simp only [distInt, le_refl]

/-- `distInt (K·t) ≤ |K|·distInt t ≤ K·B` for integer `K ≥ 0` and `distInt t ≤ B`. -/
theorem distInt_intMul_bound {K : ℤ} {t B : ℝ} (hK : 0 ≤ K) (hB : distInt t ≤ B) :
    distInt ((K : ℝ) * t) ≤ (K : ℝ) * B := by
  refine le_trans (distInt_intMul_le K t) ?_
  rw [abs_of_nonneg (by exact_mod_cast hK)]
  exact mul_le_mul_of_nonneg_left hB (by exact_mod_cast hK)

/-- **§5 Step-4 near-integer of `Υ`** (writeup 996–998).

`Υ = ℓ₂²(ℓ₂−ℓ₁)²·Ŝ_{a,b₁}(d) − ℓ₁²(ℓ₂−ℓ₁)²·Ŝ_{a,b₂}(d) + ℓ₁²ℓ₂²·Ŝ_{a,b₃}(d')`
is an **integer**-coefficient combination of three corrected mixed second differences, each
within `15·H/dᵢ` of an integer on `𝒟` (`inD_distInt_Shat`).  Here `b₁ = ℓ₁b₀`,
`b₂ = ℓ₂b₀+v`, `b₃ = (ℓ₂−ℓ₁)b₀+v`, `d' = d+ℓ₁b₀`; each is an **integer** spacing value (a
difference of integer `𝒟`-witnesses), so the brick applies.  The three coefficients
`K₁ = ℓ₂²(ℓ₂−ℓ₁)²`, `K₂ = ℓ₁²(ℓ₂−ℓ₁)²`, `K₃ = ℓ₁²ℓ₂²` are each `≤ Wval⁴` (since `ℓᵢ ≤ Wval`),
giving `distInt(Υ) ≤ 45·Wval⁴·H/D = 45·Wval⁴/Δ` (writeup 998: `Υ ∈ ℤ + O(W⁴/Δ)`, using
`D = HΔ`).

The `Ŝ`-spacing-point `inD` data and the `D ≤ dᵢ` window bounds are taken as hypotheses,
exactly as `Q_distInt_le` takes the `inDa` witnesses; the `dᵢ = HΔ` relation enters through
`S.D = HΔ` and `S.D ≤ dᵢ`. -/
theorem Upsilon_near_int {P : Globals} (S : Scale P)
    {a d d' b₁ b₂ b₃ ℓ₁ ℓ₂ : ℤ}
    (ha : 0 ≤ a) (hb1 : 0 ≤ b₁) (hb2 : 0 ≤ b₂) (hb3 : 0 ≤ b₃)
    (hℓ1 : 0 ≤ ℓ₁) (hℓ12 : ℓ₁ ≤ ℓ₂)
    (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (hDd : S.D ≤ (d : ℝ)) (hDd' : S.D ≤ (d' : ℝ))
    (hab1 : (a : ℝ) + (b₁ : ℝ) ≤ (d : ℝ)) (hab2 : (a : ℝ) + (b₂ : ℝ) ≤ (d : ℝ))
    (hab3 : (a : ℝ) + (b₃ : ℝ) ≤ (d' : ℝ))
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
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le hDpos hDd
  have hd'pos : 0 < (d' : ℝ) := lt_of_lt_of_le hDpos hDd'
  -- ℓ-bounds as reals
  have hℓ1R : (0 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ2R : (0 : ℝ) ≤ (ℓ₂ : ℝ) := le_trans hℓ1R hℓ12R
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hWnn : (0 : ℝ) ≤ 130 * P.Wval := by rw [Globals.Wval]; positivity
  have hℓ1W : (ℓ₁ : ℝ) ≤ 130 * P.Wval := le_trans hℓ12R hℓ2W
  -- the three per-Ŝ near-integer bounds
  have hB1 : distInt (Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ)) ≤ 15 * P.H / (d : ℝ) :=
    inD_distInt_Shat hdpos ha hb1 hab1 hS1_0 hS1_1 hS1_2 hS1_3
  have hB2 : distInt (Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ)) ≤ 15 * P.H / (d : ℝ) :=
    inD_distInt_Shat hdpos ha hb2 hab2 hS1_0 hS1_1 hS2_2 hS2_3
  have hB3 : distInt (Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ)) ≤ 15 * P.H / (d' : ℝ) :=
    inD_distInt_Shat hd'pos ha hb3 hab3 hS3_0 hS3_1 hS3_2 hS3_3
  -- each `15 H/dᵢ ≤ 15 H/D`
  have hHdD : ∀ {dd : ℤ}, S.D ≤ (dd : ℝ) → 0 < (dd : ℝ) →
      (15 : ℝ) * P.H / (dd : ℝ) ≤ 15 * P.H / S.D := by
    intro dd hdd hddpos
    apply div_le_div_of_nonneg_left (by positivity) hDpos hdd
  have hB1' : distInt (Shat P.X (a : ℝ) (b₁ : ℝ) (d : ℝ)) ≤ 15 * P.H / S.D :=
    le_trans hB1 (hHdD hDd hdpos)
  have hB2' : distInt (Shat P.X (a : ℝ) (b₂ : ℝ) (d : ℝ)) ≤ 15 * P.H / S.D :=
    le_trans hB2 (hHdD hDd hdpos)
  have hB3' : distInt (Shat P.X (a : ℝ) (b₃ : ℝ) (d' : ℝ)) ≤ 15 * P.H / S.D :=
    le_trans hB3 (hHdD hDd' hd'pos)
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
