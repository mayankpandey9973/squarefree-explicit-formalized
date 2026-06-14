import Squarefree.Lower.DefectExpand

/-!
# §5 general (v ≠ 0) `𝒬` expansion (writeup 783–792)

`Q_gen_expand` is the keystone for Steps 2/3/4: the combination
`𝒬 = ℓ₁·F_{a,ℓ₂b₀+v}(d) − ℓ₂·F_{a,ℓ₁b₀}(d)` expands as
`6ℓ₁Xav/d⁴ − 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xab₀²/d⁵ + O(...)`. The leading `6ab₀X/d⁴` terms cancel; the
`d⁴` survivor is the pure `v`-term `6ℓ₁Xav`, the `d⁵` survivor at `v=0` is `−φ_d`, and the
remainder collects the v-dependent `d⁵` term `−12Xaℓ₁v(a+2ℓ₂b₀+v)/d⁵` (writeup error) plus
the two `Fab_expand` `d⁶` remainders. At `v=0` this reduces to `Q_v0_expand`.
-/

namespace Squarefree

/-- **§5 general `𝒬` expansion.** -/
theorem Q_gen_expand {X a b₀ v d ℓ₁ ℓ₂ : ℝ} (hX : 0 < X) (ha : 0 < a)
    (hd : 0 < d) (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hℓ2bv : ℓ₂ * b₀ + v ≠ 0) (hℓ1b₀ : ℓ₁ * b₀ ≠ 0)
    (hwin2 : 4 * (a + |ℓ₂ * b₀ + v|) ≤ d) (hwin1 : 4 * (a + ℓ₁ * |b₀|) ≤ d) :
    |(ℓ₁ * Fab X a (ℓ₂ * b₀ + v) d - ℓ₂ * Fab X a (ℓ₁ * b₀) d)
       - (6 * ℓ₁ * X * a * v / d ^ 4
          - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * b₀ ^ 2 / d ^ 5)|
      ≤ 12 * X * a * ℓ₁ * |v| * (a + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
        + 400 * X * a * ℓ₁ * |ℓ₂ * b₀ + v| * (a + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
        + 400 * X * a * ℓ₂ * ℓ₁ * |b₀| * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := by
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hd5 : (0:ℝ) < d ^ 5 := by positivity
  -- the two `Fab_expand` estimates
  have hE2 := Fab_expand hX ha hℓ2bv hd hwin2
  -- rewrite `|ℓ₁ * b₀| = ℓ₁ * |b₀|` to match the given window hypothesis
  have habs1 : |ℓ₁ * b₀| = ℓ₁ * |b₀| := by rw [abs_mul, abs_of_pos hℓ1]
  have hwin1' : 4 * (a + |ℓ₁ * b₀|) ≤ d := by rw [habs1]; exact hwin1
  have hE1 := Fab_expand hX ha hℓ1b₀ hd hwin1'
  rw [habs1] at hE1
  -- abbreviations for the two leading parts
  set L₂ : ℝ := 6 * a * (ℓ₂ * b₀ + v) * X / d ^ 4
      - 12 * a * (ℓ₂ * b₀ + v) * (a + (ℓ₂ * b₀ + v)) * X / d ^ 5 with hL₂
  set L₁ : ℝ := 6 * a * (ℓ₁ * b₀) * X / d ^ 4
      - 12 * a * (ℓ₁ * b₀) * (a + ℓ₁ * b₀) * X / d ^ 5 with hL₁
  set F₂ : ℝ := Fab X a (ℓ₂ * b₀ + v) d with hF₂
  set F₁ : ℝ := Fab X a (ℓ₁ * b₀) d with hF₁
  -- THE ALGEBRAIC IDENTITY (verified by sympy): the residual v-term
  have hLid : ℓ₁ * L₂ - ℓ₂ * L₁
        - (6 * ℓ₁ * X * a * v / d ^ 4 - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * b₀ ^ 2 / d ^ 5)
      = -12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v) / d ^ 5 := by
    rw [hL₂, hL₁]; field_simp; ring
  -- rewrite the goal LHS as `ℓ₁·(F₂ − L₂) − ℓ₂·(F₁ − L₁) + residual`
  have heq : (ℓ₁ * F₂ - ℓ₂ * F₁)
        - (6 * ℓ₁ * X * a * v / d ^ 4 - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * b₀ ^ 2 / d ^ 5)
      = (ℓ₁ * (F₂ - L₂) - ℓ₂ * (F₁ - L₁))
        + (-12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v) / d ^ 5) := by
    rw [← hLid]; ring
  rw [heq]
  -- triangle inequality on the three pieces
  have htri : |(ℓ₁ * (F₂ - L₂) - ℓ₂ * (F₁ - L₁))
        + (-12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v) / d ^ 5)|
      ≤ (ℓ₁ * |F₂ - L₂| + ℓ₂ * |F₁ - L₁|)
        + |(-12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v) / d ^ 5)| := by
    refine le_trans (abs_add_le _ _) ?_
    gcongr
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos hℓ1, abs_of_pos hℓ2]
  refine le_trans htri ?_
  -- bound the residual term: 12·X·a·ℓ₁·|v|·(a+2ℓ₂|b₀|+|v|)/d⁵
  have hres : |(-12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v) / d ^ 5)|
      ≤ 12 * X * a * ℓ₁ * |v| * (a + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5 := by
    rw [abs_div, abs_of_pos hd5]
    rw [show (-12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v))
          = -((12 * X * a * ℓ₁) * (v * (a + 2 * ℓ₂ * b₀ + v))) by ring]
    rw [abs_neg, abs_mul (12 * X * a * ℓ₁), abs_mul v,
      abs_of_pos (by positivity : (0:ℝ) < 12 * X * a * ℓ₁)]
    rw [div_le_div_iff_of_pos_right hd5]
    have htriabs : |a + 2 * ℓ₂ * b₀ + v| ≤ a + 2 * ℓ₂ * |b₀| + |v| := by
      have h1 : |a + 2 * ℓ₂ * b₀ + v| ≤ |a + 2 * ℓ₂ * b₀| + |v| := abs_add_le _ _
      have h2 : |a + 2 * ℓ₂ * b₀| ≤ a + 2 * ℓ₂ * |b₀| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_of_pos ha, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * ℓ₂)]
      linarith
    calc (12 * X * a * ℓ₁) * (|v| * |a + 2 * ℓ₂ * b₀ + v|)
        ≤ (12 * X * a * ℓ₁) * (|v| * (a + 2 * ℓ₂ * |b₀| + |v|)) := by
          gcongr
      _ = 12 * X * a * ℓ₁ * |v| * (a + 2 * ℓ₂ * |b₀| + |v|) := by ring
  -- bound the two `Fab` pieces by their `Fab_expand` estimates
  have hb2 : ℓ₁ * |F₂ - L₂|
      ≤ 400 * X * a * ℓ₁ * |ℓ₂ * b₀ + v| * (a + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6 := by
    calc ℓ₁ * |F₂ - L₂|
        ≤ ℓ₁ * (400 * X * (a * |ℓ₂ * b₀ + v| * (a + |ℓ₂ * b₀ + v|) ^ 2) / d ^ 6) :=
          mul_le_mul_of_nonneg_left hE2 hℓ1.le
      _ = 400 * X * a * ℓ₁ * |ℓ₂ * b₀ + v| * (a + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6 := by ring
  have hb1 : ℓ₂ * |F₁ - L₁|
      ≤ 400 * X * a * ℓ₂ * ℓ₁ * |b₀| * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := by
    calc ℓ₂ * |F₁ - L₁|
        ≤ ℓ₂ * (400 * X * (a * (ℓ₁ * |b₀|) * (a + ℓ₁ * |b₀|) ^ 2) / d ^ 6) :=
          mul_le_mul_of_nonneg_left hE1 hℓ2.le
      _ = 400 * X * a * ℓ₂ * ℓ₁ * |b₀| * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := by ring
  -- assemble: the three RHS terms
  calc (ℓ₁ * |F₂ - L₂| + ℓ₂ * |F₁ - L₁|)
        + |(-12 * X * a * ℓ₁ * v * (a + 2 * ℓ₂ * b₀ + v) / d ^ 5)|
      ≤ (400 * X * a * ℓ₁ * |ℓ₂ * b₀ + v| * (a + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
          + 400 * X * a * ℓ₂ * ℓ₁ * |b₀| * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6)
        + 12 * X * a * ℓ₁ * |v| * (a + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5 :=
        add_le_add (add_le_add hb2 hb1) hres
    _ = 12 * X * a * ℓ₁ * |v| * (a + 2 * ℓ₂ * |b₀| + |v|) / d ^ 5
        + 400 * X * a * ℓ₁ * |ℓ₂ * b₀ + v| * (a + |ℓ₂ * b₀ + v|) ^ 2 / d ^ 6
        + 400 * X * a * ℓ₂ * ℓ₁ * |b₀| * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := by ring

end Squarefree
