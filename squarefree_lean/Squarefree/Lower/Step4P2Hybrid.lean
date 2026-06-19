import Squarefree.Lower.Step4P2Capped

/-!
# §5 Step-4 large-defect `p₂/d̃` HYBRID (fibre-local v-box) additive budget

The capped budget `E0_p2` (`Step4P2Capped.lean`) evaluates the polynomial majorant
`P2AbsMaj` at the **global** `v`-cap `Vmax = 10²⁰·(Δ·U⁵/Ω³)` in *all four* `v`-monomials.
The audit shows this overshoots on the low `v`-degrees: the `v`-degree-1 and `v`-degree-2
monomials must be evaluated at the **fibre-local** box `V ≤ Vmax` (so the downstream `n`-power
comes out right), while the degree-3 and degree-4 monomials must STAY capped at `Vmax`.

This file splits `P2AbsMaj` by `v`-degree and proves the hybrid pointwise/additive bounds.

## Closed forms (consumed by the numerics layer)

`P2AbsMaj ℓ₁ ℓ₂ B V` has no `v`-degree-0 part; its split is:

* `P2HybCoeff1 ℓ₁ ℓ₂ B = 5 · ℓ₁³ · ℓ₂² · (ℓ₂ − ℓ₁)² · B³`
  (total coefficient of `V¹` in `P2AbsMaj ℓ₁ ℓ₂ B V`);
* `P2HybCoeff2 ℓ₁ ℓ₂ B = 15 · ℓ₁³ · ℓ₂² · (ℓ₂ − ℓ₁) · B²`
  (total coefficient of `V²` in `P2AbsMaj ℓ₁ ℓ₂ B V`);
* `P2CapRest ℓ₁ ℓ₂ B Vc = 5 · ℓ₁³ · ℓ₂ · (3ℓ₂ − 2ℓ₁) · B · Vc³ + (5/2) · ℓ₁³ · (2ℓ₂ − ℓ₁) · Vc⁴`
  (the degree-3 and degree-4 monomials, evaluated at the cap `Vc`).

So `P2AbsMaj ℓ₁ ℓ₂ B V = P2HybCoeff1 ℓ₁ ℓ₂ B · V + P2HybCoeff2 ℓ₁ ℓ₂ B · V²
+ (degree-3,4 monomials at V)`, and for `0 ≤ V ≤ Vc` the hybrid majorant
`P2HybCoeff1·V + P2HybCoeff2·V² + P2CapRest(Vc)` dominates `P2AbsMaj ℓ₁ ℓ₂ B V`.

The additive budget `E0_p2_hyb P S ℓ₁ ℓ₂ V` is the hybrid majorant at the §5 box corner
`B = 3·10¹²·S.B` and cap `Vc = Vmax P S`, scaled by `77·(GΩ/Δ⁴)/D` exactly as `E0_p2`.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

/-- Total coefficient of `V¹` in `P2AbsMaj ℓ₁ ℓ₂ B V`: `5·ℓ₁³·ℓ₂²·(ℓ₂−ℓ₁)²·B³`. -/
noncomputable def P2HybCoeff1 (ℓ₁ ℓ₂ B : ℝ) : ℝ :=
  5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * B ^ 3

/-- Total coefficient of `V²` in `P2AbsMaj ℓ₁ ℓ₂ B V`: `15·ℓ₁³·ℓ₂²·(ℓ₂−ℓ₁)·B²`. -/
noncomputable def P2HybCoeff2 (ℓ₁ ℓ₂ B : ℝ) : ℝ :=
  15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * B ^ 2

/-- The `v`-degree-3 and degree-4 monomials of `P2AbsMaj`, evaluated at the cap `Vc`:
`5·ℓ₁³·ℓ₂·(3ℓ₂−2ℓ₁)·B·Vc³ + (5/2)·ℓ₁³·(2ℓ₂−ℓ₁)·Vc⁴`.  (`P2AbsMaj` has no degree-0 part.) -/
noncomputable def P2CapRest (ℓ₁ ℓ₂ B Vc : ℝ) : ℝ :=
  5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * B * Vc ^ 3
    + (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * Vc ^ 4

private theorem coeff1_nonneg {ℓ₁ ℓ₂ B : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hB0 : 0 ≤ B) : 0 ≤ P2HybCoeff1 ℓ₁ ℓ₂ B := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  unfold P2HybCoeff1; positivity

private theorem coeff2_nonneg {ℓ₁ ℓ₂ B : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (_hB0 : 0 ≤ B) : 0 ≤ P2HybCoeff2 ℓ₁ ℓ₂ B := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  unfold P2HybCoeff2
  exact mul_nonneg (mul_nonneg (by positivity) h21) (by positivity)

private theorem caprest_nonneg {ℓ₁ ℓ₂ B Vc : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hB0 : 0 ≤ B) (hVc0 : 0 ≤ Vc) : 0 ≤ P2CapRest ℓ₁ ℓ₂ B Vc := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  unfold P2CapRest
  have t3 : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * B * Vc ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) h32) hB0) (by positivity)
  have t4 : (0:ℝ) ≤ (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * Vc ^ 4 :=
    mul_nonneg (mul_nonneg (by positivity) h2ℓ) (by positivity)
  linarith

/-- **The full majorant at the local box `V` is dominated by the hybrid majorant**:
degrees 1,2 stay at `V`; degrees 3,4 step up `V ≤ Vc` (monotone, nonneg coefficients). -/
private theorem maj_le_hybrid {ℓ₁ ℓ₂ Bx V Vc : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hBx0 : 0 ≤ Bx) (hV0 : 0 ≤ V) (hVVc : V ≤ Vc) :
    P2AbsMaj ℓ₁ ℓ₂ Bx V
      ≤ P2HybCoeff1 ℓ₁ ℓ₂ Bx * V + P2HybCoeff2 ℓ₁ ℓ₂ Bx * V ^ 2
        + P2CapRest ℓ₁ ℓ₂ Bx Vc := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hc3 : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * Bx :=
    mul_nonneg (mul_nonneg (by positivity) h32) hBx0
  have hc4 : (0:ℝ) ≤ (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) :=
    mul_nonneg (by positivity) h2ℓ
  have hm3 : V ^ 3 ≤ Vc ^ 3 := pow_le_pow_left₀ hV0 hVVc 3
  have hm4 : V ^ 4 ≤ Vc ^ 4 := pow_le_pow_left₀ hV0 hVVc 4
  have h3 := mul_le_mul_of_nonneg_left hm3 hc3
  have h4 := mul_le_mul_of_nonneg_left hm4 hc4
  unfold P2AbsMaj P2HybCoeff1 P2HybCoeff2 P2CapRest
  nlinarith [h3, h4]

private theorem asub' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le x (-y)).trans (le_of_eq (by rw [abs_neg]))

/-- `|P₂| ≤ P2AbsMaj ℓ₁ ℓ₂ Bx V` at the local box (`Step4P2Size.lean`'s private
`abs_Ptwo_le_maj`, reproved here since it is not exported). -/
private theorem abs_Ptwo_le_maj_local {b₀ v ℓ₁ ℓ₂ Bx V : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb : |b₀| ≤ Bx) (hBx0 : 0 ≤ Bx)
    (hv : |v| ≤ V) :
    |Ptwo b₀ v ℓ₁ ℓ₂| ≤ P2AbsMaj ℓ₁ ℓ₂ Bx V := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hc1 : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hc2 : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h21
  have hc3 : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) := mul_nonneg (by positivity) h32
  have hc4 : (0:ℝ) ≤ (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h2ℓ
  have hA : |(-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v)|
      = 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * |b₀| ^ 3 * |v| := by
    rw [show -5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v
          = -(5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * (b₀ ^ 3 * v)) by ring,
      abs_neg, abs_mul, abs_of_nonneg hc1, abs_mul, abs_pow]
    ring
  have hB : |(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2)|
      = 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * |b₀| ^ 2 * |v| ^ 2 := by
    rw [show 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2
          = (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) * (b₀ ^ 2 * v ^ 2) by ring,
      abs_mul, abs_of_nonneg hc2, abs_mul, abs_pow, abs_pow]
    ring
  have hC : |(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3)|
      = 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * |b₀| * |v| ^ 3 := by
    rw [show 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3
          = (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) * (b₀ * v ^ 3) by ring,
      abs_mul, abs_of_nonneg hc3, abs_mul, abs_pow]
    ring
  have hD : |((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4)|
      = (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * |v| ^ 4 := by
    rw [show (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4
          = ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 4 by ring,
      abs_mul, abs_of_nonneg hc4, abs_pow]
  have htri : |Ptwo b₀ v ℓ₁ ℓ₂|
      ≤ |(-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v)|
        + |(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2)|
        + |(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3)|
        + |((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4)| := by
    rw [Ptwo]
    exact (asub' _ _).trans (add_le_add ((asub' _ _).trans
      (add_le_add (asub' _ _) (le_refl _))) (le_refl _))
  rw [hA, hB, hC, hD] at htri
  have step1 : |Ptwo b₀ v ℓ₁ ℓ₂| ≤ P2AbsMaj ℓ₁ ℓ₂ |b₀| |v| :=
    htri.trans (le_of_eq (by unfold P2AbsMaj; ring))
  refine step1.trans ?_
  have hVnn : 0 ≤ V := le_trans hvnn hv
  have mono : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c →
      c * |b₀| ^ i * |v| ^ j ≤ c * Bx ^ i * V ^ j := fun c i j hc =>
    mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0nn hb i) hc)
      (pow_le_pow_left₀ hvnn hv j) (pow_nonneg hvnn j) (mul_nonneg hc (pow_nonneg hBx0 i))
  have m1 := mono (5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) 3 1 hc1
  have m2 := mono (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) 2 2 hc2
  have m3 := mono (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) 1 3 hc3
  have m4 := mono ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) 0 4 hc4
  simp only [pow_one, pow_zero, mul_one] at m1 m2 m3 m4
  unfold P2AbsMaj
  linarith [m1, m2, m3, m4]

/-- **Hybrid pointwise majorant for `P₂`**: the `v`-degree-1,2 monomials are bounded at the
fibre-local box `V`, the degree-3,4 monomials at the cap `Vc ≥ V`. -/
theorem p2_hybrid_pointwise {b₀ v ℓ₁ ℓ₂ Bx V Vc : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb : |b₀| ≤ Bx) (hBx0 : 0 ≤ Bx)
    (hv : |v| ≤ V) (hV0 : 0 ≤ V) (hVVc : V ≤ Vc) :
    |Ptwo b₀ v ℓ₁ ℓ₂|
      ≤ P2HybCoeff1 ℓ₁ ℓ₂ Bx * V + P2HybCoeff2 ℓ₁ ℓ₂ Bx * V ^ 2
        + P2CapRest ℓ₁ ℓ₂ Bx Vc :=
  (abs_Ptwo_le_maj_local hℓ1 hℓ12 hb hBx0 hv).trans
    (maj_le_hybrid hℓ1 hℓ12 hBx0 hV0 hVVc)

/-- **The HYBRID `p₂` additive budget** `E0_p2_hyb`.  The hybrid majorant (degrees 1,2 at the
fibre-local box `V`; degrees 3,4 at the global cap `Vmax`) at the §5 box corner
`b₀ = 3·10¹²·B`, scaled by the `pref`-bound `77·(GΩ/Δ⁴)` and the defect floor `1/D`. -/
noncomputable def E0_p2_hyb (P : Globals) (S : Scale P) (ℓ₁ ℓ₂ V : ℝ) : ℝ :=
  77 * (P.G * S.Ω / S.Δ ^ 4) *
    ((P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * V
      + P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * V ^ 2
      + P2CapRest ℓ₁ ℓ₂ (3000000000000 * S.B) (Vmax P S)) / S.D)

private theorem Bcorner_nonneg : (0:ℝ) ≤ 3000000000000 * S.B := by
  have := S.Δ_pos; have := P.G_pos; have := S.Ω_pos
  unfold Scale.B; positivity

theorem E0_p2_hyb_nonneg {ℓ₁ ℓ₂ V : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hV0 : 0 ≤ V) :
    0 ≤ E0_p2_hyb P S ℓ₁ ℓ₂ V := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hB0 : (0:ℝ) ≤ 3000000000000 * S.B := Bcorner_nonneg
  have h1 : 0 ≤ P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * V :=
    mul_nonneg (coeff1_nonneg hℓ1 hℓ12 hB0) hV0
  have h2 : 0 ≤ P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * V ^ 2 :=
    mul_nonneg (coeff2_nonneg hℓ1 hℓ12 hB0) (by positivity)
  have h3 : 0 ≤ P2CapRest ℓ₁ ℓ₂ (3000000000000 * S.B) (Vmax P S) :=
    caprest_nonneg hℓ1 hℓ12 hB0 Vmax_nonneg
  unfold E0_p2_hyb
  have hnum : 0 ≤ P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * V
      + P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * V ^ 2
      + P2CapRest ℓ₁ ℓ₂ (3000000000000 * S.B) (Vmax P S) := by linarith
  positivity

/-- `E0_p2_hyb` is monotone in the fibre-local box `V` (on `0 ≤ V`). -/
theorem E0_p2_hyb_mono {ℓ₁ ℓ₂ V V' : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hV0 : 0 ≤ V) (hVV' : V ≤ V') :
    E0_p2_hyb P S ℓ₁ ℓ₂ V ≤ E0_p2_hyb P S ℓ₁ ℓ₂ V' := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hB0 : (0:ℝ) ≤ 3000000000000 * S.B := Bcorner_nonneg
  have hsc : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hVV' (coeff1_nonneg (B := 3000000000000 * S.B) hℓ1 hℓ12 hB0)
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV0 hVV' 2)
    (coeff2_nonneg (B := 3000000000000 * S.B) hℓ1 hℓ12 hB0)
  have hnum : P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * V
      + P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * V ^ 2
      + P2CapRest ℓ₁ ℓ₂ (3000000000000 * S.B) (Vmax P S)
      ≤ P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * V'
        + P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * V' ^ 2
        + P2CapRest ℓ₁ ℓ₂ (3000000000000 * S.B) (Vmax P S) := by linarith
  unfold E0_p2_hyb
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hDpos.le) hsc

/-- **§5 Step-4 large-defect `p₂/d̃` HYBRID additive bound** (audit-corrected v-split).

Same hypothesis list as `p2_capped_additive_le`, except the `v`-box is the fibre-local
`|v| ≤ V` with `V ≤ Vmax`: the magnitude of `pref·(P₂/d̃)` is dominated by `E0_p2_hyb`,
whose `v`-degree-1,2 monomials sit at `V` and whose degree-3,4 monomials stay at `Vmax`. -/
theorem p2_hybrid_additive_le
    {a b₀ v d ℓ₁ ℓ₂ V : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hv : |v| ≤ V) (hVcap : V ≤ Vmax P S) (hV0 : 0 ≤ V)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    |(P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))|
      ≤ E0_p2_hyb P S ℓ₁ ℓ₂ V := by
  have hB0 : (0:ℝ) ≤ 3000000000000 * S.B := Bcorner_nonneg
  have hbudget := abs_pref_mul_Ptwo_div_le_p2PointBudget
    (S := S) ha0 ha_hi hℓ1 hℓ12 hb0 hB0 hv hV0 hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  refine hbudget.trans ?_
  have hmaj := maj_le_hybrid (Bx := 3000000000000 * S.B) (Vc := Vmax P S)
    hℓ1 hℓ12 hB0 hV0 hVcap
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hsc : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) := by positivity
  unfold E0_p2_hyb
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmaj hDpos.le) hsc

end Squarefree
