import Squarefree.Lower.Step4Magnitude

/-!
# §5 Step-4 large-defect `p₂/d̃` SIZE bound (writeup 1024; attempt-1 `SquareDiff.lean:1957–2137`)

The **additive** (point-budget) majorant for the quartic `P₂`-contribution to the closed
cubic/quartic form `Σ_closed = pref·(P₁ + P₂/d)`, where `pref = (Xa/d⁵)·(−4+10a/d)`.

This is the faithful *polynomial majorant* of the `p₂` term — the SIZE (magnitude) of
`pref·P₂/d̃`, **not** a difference and **not** collapsed to `O(|s|)`.  Each of the four
`v`-monomials of `P₂` (coefficients `−5ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²b̃³`, `−15ℓ₁³ℓ₂²(ℓ₂−ℓ₁)b̃²`,
`−5ℓ₁³ℓ₂(3ℓ₂−2ℓ₁)b̃`, `−(5/2)ℓ₁³(2ℓ₂−ℓ₁)`) is bounded by its absolute majorant
`P2AbsMaj ℓ₁ ℓ₂ Bx Vx` at `|b₀| ≤ Bx`, `|v| ≤ Vx`, `d̃ ≥ D`, giving the point budget

  `|pref·P₂/d̃| ≤ 77·(GΩ/Δ⁴)·P2AbsMaj(ℓ₁,ℓ₂,Bx,Vx)/D`.

This is the attempt-2 port of `largeDefectReplacementP2PointBudgetMd` /
`abs_largeDefectSigmaPrefReal_actual_mul_p2_div_le_replacementP2PointBudget`, with the
`pref`-scale collapsed to the clean negative `X`-power `GΩ/Δ⁴ = X·A/D⁵` (since `X = G·H⁵`,
`A = ΔΩ`, `D = HΔ`).

## Conventions (the D-agent must match these)
* `pref := (X·a/d⁵)·(−4 + 10·a/d)`  — the closed-form leading bracket.
* `Bx`  — any upper box for `|b₀|`; the §5 window gives `Bx = 3·10¹²·B` (`hb0`).
* `Vx`  — any upper box for `|v|`; the band box `≍V_s` gives `Vx = 10²⁰·(Δ·U⁵/Ω³)` (`hv`),
          but the lemma is stated for an arbitrary box so the caller may instead substitute
          the per-`s` pin `Vx ≍ V_s` (`v² ≍ Δ²Ω²|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁))`).
* `D ≤ d̃`  — the dyadic lower bound on the defect denominator.

The negative `X`-power `ρ_p2 := |pref·P₂/d̃| / |s|` is then obtained downstream by
substituting `Vx ≍ V_s` and using the regime `Δ²U⁵ ≤ HΩ³` (`hReg`) to collapse the `Δ²/H`
factor; see the §5 summation layer (writeup `Λ_p2(s)` row).
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The absolute polynomial majorant of the quartic `P₂(b₀,v,ℓ₁,ℓ₂)` (`DefectUpsilon.lean:33`):
each monomial with its sign collapsed and `b₀ → B`, `v → V`.  All four coefficients are
nonnegative for `1 ≤ ℓ₁ < ℓ₂`. -/
noncomputable def P2AbsMaj (ℓ₁ ℓ₂ B V : ℝ) : ℝ :=
  5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * B ^ 3 * V
    + 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * B ^ 2 * V ^ 2
    + 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * B * V ^ 3
    + (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * V ^ 4

private theorem asub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le x (-y)).trans (le_of_eq (by rw [abs_neg]))

/-- **`|P₂| ≤ P2AbsMaj`** at any box `|b₀| ≤ Bx`, `|v| ≤ Vx`.  The polynomial majorant of the
quartic `P₂`: triangle inequality across the four monomials, then monotonicity in `(B,V)`. -/
private theorem abs_Ptwo_le_maj {b₀ v ℓ₁ ℓ₂ Bx Vx : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb : |b₀| ≤ Bx) (hBx0 : 0 ≤ Bx)
    (hvx : |v| ≤ Vx) :
    |Ptwo b₀ v ℓ₁ ℓ₂| ≤ P2AbsMaj ℓ₁ ℓ₂ Bx Vx := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- nonnegative coefficients
  have hc1 : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hc2 : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h21
  have hc3 : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) := mul_nonneg (by positivity) h32
  have hc4 : (0:ℝ) ≤ (5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) := mul_nonneg (by positivity) h2ℓ
  -- abs of each monomial (signs collapsed)
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
  -- triangle inequality across the four monomials of P₂
  have htri : |Ptwo b₀ v ℓ₁ ℓ₂|
      ≤ |(-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v)|
        + |(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2)|
        + |(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3)|
        + |((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4)| := by
    rw [Ptwo]
    exact (asub _ _).trans (add_le_add ((asub _ _).trans
      (add_le_add (asub _ _) (le_refl _))) (le_refl _))
  rw [hA, hB, hC, hD] at htri
  -- step to majorant at (|b₀|,|v|), then monotone up to (Bx,Vx)
  have step1 : |Ptwo b₀ v ℓ₁ ℓ₂| ≤ P2AbsMaj ℓ₁ ℓ₂ |b₀| |v| :=
    htri.trans (le_of_eq (by unfold P2AbsMaj; ring))
  refine step1.trans ?_
  have mono : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c →
      c * |b₀| ^ i * |v| ^ j ≤ c * Bx ^ i * Vx ^ j := fun c i j hc =>
    mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0nn hb i) hc)
      (pow_le_pow_left₀ hvnn hvx j) (pow_nonneg hvnn j) (mul_nonneg hc (pow_nonneg hBx0 i))
  have m1 := mono (5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2) 3 1 hc1
  have m2 := mono (15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)) 2 2 hc2
  have m3 := mono (5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)) 1 3 hc3
  have m4 := mono ((5 / 2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) 0 4 hc4
  simp only [pow_one, pow_zero, mul_one] at m1 m2 m3 m4
  unfold P2AbsMaj
  linarith [m1, m2, m3, m4]

/-- **§5 Step-4 large-defect `p₂/d̃` SIZE (point) bound** (writeup 1024; attempt-1
`abs_largeDefectSigmaPrefReal_actual_mul_p2_div_le_replacementP2PointBudget`).

The magnitude of the quartic `P₂`-contribution `pref·P₂/d̃` to the closed form `Σ_closed`,
where `pref = (X·a/d⁵)·(−4+10·a/d)`, is dominated by the *polynomial majorant* point budget

  `77·(GΩ/Δ⁴)·P2AbsMaj(ℓ₁,ℓ₂,Bx,Vx)/D`,

with `Bx`/`Vx` arbitrary boxes for `|b₀|`/`|v|`.  The `pref`-scale collapses to the negative
`X`-power `GΩ/Δ⁴ = X·A/D⁵` (since `X = G·H⁵`, `A = ΔΩ`, `D = HΔ`).  The leading bracket
`|−4+10a/d| ≤ 7` uses the §5 regime via `bracket_ad_small`. -/
theorem abs_pref_mul_Ptwo_div_le_p2PointBudget
    {a b₀ v d ℓ₁ ℓ₂ Bx Vx : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb : |b₀| ≤ Bx) (hBx0 : 0 ≤ Bx)
    (hvx : |v| ≤ Vx) (_hVx0 : 0 ≤ Vx)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    |(P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))|
      ≤ 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D) := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  -- bracket bound  |−4 + 10a/d| ≤ 4
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  -- |Ptwo| ≤ P2AbsMaj
  have hP2 : |Ptwo b₀ v ℓ₁ ℓ₂| ≤ P2AbsMaj ℓ₁ ℓ₂ Bx Vx :=
    abs_Ptwo_le_maj hℓ1 hℓ12 hb hBx0 hvx
  have hMnn : 0 ≤ P2AbsMaj ℓ₁ ℓ₂ Bx Vx := le_trans (abs_nonneg _) hP2
  -- scale collapse  X·A/D⁵ = GΩ/Δ⁴
  have hXAD : P.X * S.A / S.D ^ 5 = P.G * S.Ω / S.Δ ^ 4 := by
    unfold Scale.A Scale.D
    rw [P.X_eq_G_mul_H_pow_five]; field_simp
  -- |pref| ≤ 45·GΩ/Δ⁴  (ε-window: 11/(1−ε)⁵ ≤ 45/4, bracket ≤ 4)
  have hd5ge : S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5 ≤ d ^ 5 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hdD 5
  have hQle : P.X * a / d ^ 5 ≤ 45 / 4 * (P.X * S.A / S.D ^ 5) := by
    rw [show 45 / 4 * (P.X * S.A / S.D ^ 5) = 45 / 4 * (P.X * S.A) / S.D ^ 5 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : P.X * a * S.D ^ 5 ≤ P.X * (11 * S.A) * S.D ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha_hi hXpos.le) (pow_pos hDpos 5).le]
    have e2 : P.X * (11 * S.A) * S.D ^ 5
        ≤ 45 / 4 * (P.X * S.A) * (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by
      nlinarith [mul_pos (mul_pos hXpos hApos) (pow_pos hDpos 5)]
    have e3 : 45 / 4 * (P.X * S.A) * (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5)
        ≤ 45 / 4 * (P.X * S.A) * d ^ 5 :=
      mul_le_mul_of_nonneg_left hd5ge (by positivity)
    linarith [e1, e2, e3]
  have hpref : |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| ≤ 45 * (P.G * S.Ω / S.Δ ^ 4) := by
    rw [abs_mul, abs_of_pos (show (0:ℝ) < P.X * a / d ^ 5 by positivity)]
    calc (P.X * a / d ^ 5) * |(-4 + 10 * a / d)|
        ≤ (45 / 4 * (P.X * S.A / S.D ^ 5)) * 4 :=
          mul_le_mul hQle hbr (abs_nonneg _) (by positivity)
      _ = 45 * (P.X * S.A / S.D ^ 5) := by ring
      _ = 45 * (P.G * S.Ω / S.Δ ^ 4) := by rw [hXAD]
  -- |Ptwo/d̃| ≤ (77/45)·P2AbsMaj/D  (the window slack sits in 77/45 ≥ 1/(1−ε))
  have hP2div : |Ptwo b₀ v ℓ₁ ℓ₂ / d| ≤ 77 / 45 * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D) := by
    rw [abs_div, abs_of_pos hd_pos,
      show 77 / 45 * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D)
        = 77 / 45 * P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D by ring,
      div_le_div_iff₀ hd_pos hDpos]
    nlinarith [mul_le_mul_of_nonneg_left hdD hMnn,
      mul_le_mul_of_nonneg_right hP2 hDpos.le]
  -- assemble
  rw [show (P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))
        = ((P.X * a / d ^ 5) * (-4 + 10 * a / d)) * (Ptwo b₀ v ℓ₁ ℓ₂ / d) by ring,
    abs_mul]
  calc |(P.X * a / d ^ 5) * (-4 + 10 * a / d)| * |Ptwo b₀ v ℓ₁ ℓ₂ / d|
      ≤ (45 * (P.G * S.Ω / S.Δ ^ 4)) * (77 / 45 * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D)) :=
        mul_le_mul hpref hP2div (abs_nonneg _) (by positivity)
    _ = 77 * (P.G * S.Ω / S.Δ ^ 4) * (P2AbsMaj ℓ₁ ℓ₂ Bx Vx / S.D) := by ring

end Squarefree
