import Squarefree.Lower.Step2CurvCurv

/-!
# §5 Step-2 curvature lower bound (`f`-free Wronskian branch) — algebraic + MVT helpers

Supporting lemmas for `phif_curvature_lower_curv` (`Step2CurvCurv3`):

* `welim_poly` — the **f-elimination Wronskian identity**.  Writing `ψ = d̃⁴/(6Xa)`,
  `ψ' = 4d̃³d̃'/(6Xa)`, `ψ'' = (12d̃²d̃'²+4d̃³d̃'')/(6Xa)` and `φ_f = ψ·(f+φ)`, the combination
  `𝒲 = ψ''·φ_f' − ψ'·φ_f''` is `f`-free and equals `(4K/(6Xa)²)·Ñ_act` with `Ñ_act` the explicit
  polynomial in the actual finite-difference atoms (`b=b̃, bp=b̃', bd=b̃''`).  (sympy-verified.)
* `Ncorr_alg` — the **finite-difference correction expansion**: `Ñ_act − Ñ_s` (smooth `b̃→d̃'` etc.)
  expands into 7 monomials, each carrying at least one of `ε₁=b̃−d̃', ε₂=b̃'−d̃'', ε₃=b̃''−d̃'''`.
* `fd_error_bound` — the **double mean-value bound** `|(f(r+ℓ)−f(r))/ℓ − g r| ≤ ℓ·M` whenever
  `f' = g`, `g' = h`, `|h| ≤ M` on `[r,r+ℓ]`.  Used to bound each `εᵢ` by `ℓ₁·sup|d̃⁽ⁱ⁺¹⁾|`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **f-elimination Wronskian identity** (sympy-verified).  With `ψ'' = (12d²d1²+4d³d2)/(6Xa)`,
`ψ' = 4d³d1/(6Xa)`, the actual derivatives `D1 = ψ'(f+φ)+ψ·φ1`,
`D2 = ψ''(f+φ)+2ψ'·φ1+ψ·φ2` (with `φ1,φ2` the **closed forms** `K·b·br/d⁶`, `K·G/d⁶`),
the Wronskian `ψ''·D1 − ψ'·D2` is `f`-free and equals `(4K/(6Xa)²)·Ñ_act`. -/
lemma welim_poly (X a d d1 d2 b bp bd φ φ1 φ2 f K : ℝ)
    (hg : (6 : ℝ) * X * a ≠ 0) (hd6 : d ^ 6 ≠ 0) (hd : d ≠ 0)
    (hφ1 : φ1 = K * b * (2 * bp * d - 5 * b * d1) / d ^ 6)
    (hφ2 : φ2 = K * (bp * (2 * bp * d - 5 * b * d1)
        + b * (2 * bd * d - 3 * bp * d1 - 5 * b * d2)
        - 6 * b * (2 * bp * d - 5 * b * d1) * d1 / d) / d ^ 6) :
    (12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a)
        * ((4 * d ^ 3 * d1 / (6 * X * a)) * (f + φ) + (d ^ 4 / (6 * X * a)) * φ1)
      - (4 * d ^ 3 * d1 / (6 * X * a))
        * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a) * (f + φ)
            + (8 * d ^ 3 * d1 / (6 * X * a)) * φ1 + (d ^ 4 / (6 * X * a)) * φ2)
      = (4 * K / (6 * X * a) ^ 2)
        * ((d * d2 - 5 * d1 ^ 2) * b * (2 * bp * d - 5 * b * d1)
            - d * d1 * (bp * (2 * bp * d - 5 * b * d1)
                + b * (2 * bd * d - 3 * bp * d1 - 5 * b * d2))
            + 6 * d1 ^ 2 * b * (2 * bp * d - 5 * b * d1)) := by
  subst hφ1 hφ2
  field_simp
  ring

/-- **Finite-difference correction expansion** (sympy-verified).  Substituting `b = d1+ε₁`,
`bp = d2+ε₂`, `bd = s4+ε₃` into `Ñ_act` and subtracting the smooth `Ñ_s = −d1(5d1⁴−10d1²d2 d
+2d1 s4 d²)` gives a 7-monomial polynomial, each monomial carrying an `ε`. -/
lemma Ncorr_alg (d d1 d2 s4 e1 e2 e3 : ℝ) :
    ((d * d2 - 5 * d1 ^ 2) * (d1 + e1) * (2 * (d2 + e2) * d - 5 * (d1 + e1) * d1)
        - d * d1 * ((d2 + e2) * (2 * (d2 + e2) * d - 5 * (d1 + e1) * d1)
            + (d1 + e1) * (2 * (s4 + e3) * d - 3 * (d2 + e2) * d1 - 5 * (d1 + e1) * d2))
        + 6 * d1 ^ 2 * (d1 + e1) * (2 * (d2 + e2) * d - 5 * (d1 + e1) * d1))
      - (-(d1 * (5 * d1 ^ 4 - 10 * d1 ^ 2 * d2 * d + 2 * d1 * s4 * d ^ 2)))
      = -5 * d1 ^ 3 * e1 ^ 2 + 2 * d * (d * d2 + 5 * d1 ^ 2) * e1 * e2 - 2 * d ^ 2 * d1 * e1 * e3
        - 2 * (d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4) * e1
        - 2 * d ^ 2 * d1 * e2 ^ 2 + 2 * d * d1 * (5 * d1 ^ 2 - d * d2) * e2
        - 2 * d ^ 2 * d1 ^ 2 * e3 := by
  ring

/-- **Double mean-value bound.**  If `f' = g` and `g' = h` on `[r,r+ℓ]` (in the `HasDerivAt`
sense) and `|h| ≤ M` there, then the first finite difference of `f` differs from `g r` by at most
`ℓ·M`.  (Slope `= g ξ` by MVT, then `g ξ − g r = (ξ−r)·h η` by a second MVT.) -/
lemma fd_error_bound {f g h : ℝ → ℝ} {r ℓ M : ℝ} (hℓ : 0 < ℓ)
    (hfg : ∀ x ∈ Set.Icc r (r + ℓ), HasDerivAt f (g x) x)
    (hgh : ∀ x ∈ Set.Icc r (r + ℓ), HasDerivAt g (h x) x)
    (hMb : ∀ x ∈ Set.Icc r (r + ℓ), |h x| ≤ M) :
    |(f (r + ℓ) - f r) / ℓ - g r| ≤ ℓ * M := by
  have hrr : r < r + ℓ := by linarith
  have hcf : ContinuousOn f (Set.Icc r (r + ℓ)) :=
    fun x hx => (hfg x hx).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f g hrr hcf
    (fun x hx => hfg x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hsub : r + ℓ - r = ℓ := by ring
  rw [hsub] at hξeq
  -- second MVT on `g` over `[r, ξ]`
  have hrξ : r < ξ := hξ.1
  have hξle : ξ ≤ r + ℓ := le_of_lt hξ.2
  have hcg : ContinuousOn g (Set.Icc r ξ) :=
    fun x hx => (hgh x ⟨hx.1, le_trans hx.2 hξle⟩).continuousAt.continuousWithinAt
  obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope g h hrξ hcg
    (fun x hx => hgh x ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hξle⟩)
  have hξrne : ξ - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hrξ)
  have hgdiff : g ξ - g r = (ξ - r) * h η := by
    rw [hηeq]; field_simp
  have hval : (f (r + ℓ) - f r) / ℓ - g r = (ξ - r) * h η := by
    rw [← hξeq]; exact hgdiff
  rw [hval, abs_mul]
  have hξr : |ξ - r| ≤ ℓ := by
    rw [abs_of_pos (by linarith)]; linarith [hξ.2]
  have hηmem : η ∈ Set.Icc r (r + ℓ) := ⟨le_of_lt hη.1, le_trans (le_of_lt hη.2) hξle⟩
  exact mul_le_mul hξr (hMb η hηmem) (abs_nonneg _) hℓ.le


/-- **The 7-term finite-difference correction bound** (abstract).  Given scale bounds on the
atoms `d, d1, d2, s4` and on the finite-difference errors `e1, e2, e3` (each `≤ ℓ₁·sup`), the
`Ñ_act − Ñ_s` correction polynomial is `≤ B⁵/(2·10²⁹)`.  Each of the 7 monomials carries a factor
`ℓ₁/R`, and `hsmall : 10⁷⁸·ℓ₁ ≤ R` makes the total negligible against the smooth scale `B⁵/10²⁹`. -/
lemma correction_abstract {d d1 d2 s4 e1 e2 e3 B R l1 : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hl1 : 0 < l1)
    (hd_hi : |d| ≤ 18 * (B * R))
    (hd1 : |d1| ≤ 10 ^ 6 * B)
    (hd2 : |d2| ≤ 10 ^ 13 * (B / R))
    (hs4 : |s4| ≤ 10 ^ 19 * (B / R ^ 2))
    (he1 : |e1| ≤ l1 * (10 ^ 13 * (B / R)))
    (he2 : |e2| ≤ l1 * (10 ^ 19 * (B / R ^ 2)))
    (he3 : |e3| ≤ l1 * (2 * 10 ^ 25 * (B / R ^ 3)))
    (hsmall : 10 ^ 78 * l1 ≤ R) :
    |(-5 * d1 ^ 3 * e1 ^ 2 + 2 * d * (d * d2 + 5 * d1 ^ 2) * e1 * e2 - 2 * d ^ 2 * d1 * e1 * e3
        - 2 * (d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4) * e1
        - 2 * d ^ 2 * d1 * e2 ^ 2 + 2 * d * d1 * (5 * d1 ^ 2 - d * d2) * e2
        - 2 * d ^ 2 * d1 ^ 2 * e3)|
      ≤ B ^ 5 / (2 * 10 ^ 29) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hl1R : l1 ≤ R := by nlinarith [hsmall, hl1]
  -- folding fact `ℓ₁²B⁵/R² ≤ ℓ₁B⁵/R`
  have hsq : l1 ^ 2 * B ^ 5 / R ^ 2 ≤ l1 * B ^ 5 / R := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hl1.le (pow_nonneg hB.le 5)) hR.le)
      (sub_nonneg.mpr hl1R)]
  -- inner sum bounds
  have hc2 : |d * d2 + 5 * d1 ^ 2| ≤ 2 * 10 ^ 14 * B ^ 2 := by
    have h1 : |d * d2| ≤ 18 * (B * R) * (10 ^ 13 * (B / R)) := by
      rw [abs_mul]; exact mul_le_mul hd_hi hd2 (abs_nonneg _) (by positivity)
    have h2 : |5 * d1 ^ 2| ≤ 5 * (10 ^ 6 * B) ^ 2 := by
      rw [abs_mul, abs_pow, show |(5:ℝ)| = 5 from by norm_num]; gcongr
    have h1' : 18 * (B * R) * (10 ^ 13 * (B / R)) = 18 * 10 ^ 13 * B ^ 2 := by field_simp <;> ring
    have h2' : 5 * (10 ^ 6 * B) ^ 2 = 5 * 10 ^ 12 * B ^ 2 := by ring
    calc |d * d2 + 5 * d1 ^ 2| ≤ |d * d2| + |5 * d1 ^ 2| := abs_add_le _ _
      _ ≤ 18 * 10 ^ 13 * B ^ 2 + 5 * 10 ^ 12 * B ^ 2 := by rw [← h1', ← h2']; linarith
      _ ≤ 2 * 10 ^ 14 * B ^ 2 := by nlinarith [sq_nonneg B, hB]
  have hc6 : |5 * d1 ^ 2 - d * d2| ≤ 2 * 10 ^ 14 * B ^ 2 := by
    have h1 : |d * d2| ≤ 18 * (B * R) * (10 ^ 13 * (B / R)) := by
      rw [abs_mul]; exact mul_le_mul hd_hi hd2 (abs_nonneg _) (by positivity)
    have h2 : |5 * d1 ^ 2| ≤ 5 * (10 ^ 6 * B) ^ 2 := by
      rw [abs_mul, abs_pow, show |(5:ℝ)| = 5 from by norm_num]; gcongr
    have h1' : 18 * (B * R) * (10 ^ 13 * (B / R)) = 18 * 10 ^ 13 * B ^ 2 := by field_simp <;> ring
    have h2' : 5 * (10 ^ 6 * B) ^ 2 = 5 * 10 ^ 12 * B ^ 2 := by ring
    calc |5 * d1 ^ 2 - d * d2| ≤ |5 * d1 ^ 2| + |d * d2| := abs_sub _ _
      _ ≤ 5 * 10 ^ 12 * B ^ 2 + 18 * 10 ^ 13 * B ^ 2 := by rw [← h1', ← h2']; linarith
      _ ≤ 2 * 10 ^ 14 * B ^ 2 := by nlinarith [sq_nonneg B, hB]
  have hc4 : |d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4|
      ≤ 4 * 10 ^ 28 * B ^ 4 := by
    have hA : |d ^ 2 * d1 * s4| ≤ (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2)) := by
      rw [abs_mul, abs_mul, abs_pow]
      exact mul_le_mul (mul_le_mul (by gcongr) hd1 (abs_nonneg _) (by positivity)) hs4
        (abs_nonneg _) (by positivity)
    have hBb : |d ^ 2 * d2 ^ 2| ≤ (18 * (B * R)) ^ 2 * (10 ^ 13 * (B / R)) ^ 2 := by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (by gcongr) (by gcongr) (by positivity) (by positivity)
    have hCc : |5 * d * d1 ^ 2 * d2|
        ≤ 5 * (18 * (B * R)) * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, show |(5:ℝ)| = 5 from by norm_num]; gcongr
    have hDd : |5 * d1 ^ 4| ≤ 5 * (10 ^ 6 * B) ^ 4 := by
      rw [abs_mul, abs_pow, show |(5:ℝ)| = 5 from by norm_num]; gcongr
    have eA : (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (10 ^ 19 * (B / R ^ 2))
        = 324 * 10 ^ 25 * B ^ 4 := by field_simp <;> ring
    have eB : (18 * (B * R)) ^ 2 * (10 ^ 13 * (B / R)) ^ 2 = 324 * 10 ^ 26 * B ^ 4 := by
      field_simp <;> ring
    have eC : 5 * (18 * (B * R)) * (10 ^ 6 * B) ^ 2 * (10 ^ 13 * (B / R)) = 90 * 10 ^ 25 * B ^ 4 := by
      field_simp <;> ring
    have eD : 5 * (10 ^ 6 * B) ^ 4 = 5 * 10 ^ 24 * B ^ 4 := by ring
    rw [eA] at hA; rw [eB] at hBb; rw [eC] at hCc; rw [eD] at hDd
    have hsplit : |d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4|
        ≤ |d ^ 2 * d1 * s4| + |d ^ 2 * d2 ^ 2| + |5 * d * d1 ^ 2 * d2| + |5 * d1 ^ 4| := by
      have e0 : d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4
          = d ^ 2 * d1 * s4 + (-(d ^ 2 * d2 ^ 2)) + (-(5 * d * d1 ^ 2 * d2)) + 5 * d1 ^ 4 := by ring
      rw [e0]
      calc |d ^ 2 * d1 * s4 + -(d ^ 2 * d2 ^ 2) + -(5 * d * d1 ^ 2 * d2) + 5 * d1 ^ 4|
          ≤ |d ^ 2 * d1 * s4 + -(d ^ 2 * d2 ^ 2) + -(5 * d * d1 ^ 2 * d2)| + |5 * d1 ^ 4| :=
            abs_add_le _ _
        _ ≤ |d ^ 2 * d1 * s4 + -(d ^ 2 * d2 ^ 2)| + |-(5 * d * d1 ^ 2 * d2)| + |5 * d1 ^ 4| := by
            gcongr; exact abs_add_le _ _
        _ ≤ (|d ^ 2 * d1 * s4| + |-(d ^ 2 * d2 ^ 2)|) + |-(5 * d * d1 ^ 2 * d2)| + |5 * d1 ^ 4| := by
            gcongr; exact abs_add_le _ _
        _ = |d ^ 2 * d1 * s4| + |d ^ 2 * d2 ^ 2| + |5 * d * d1 ^ 2 * d2| + |5 * d1 ^ 4| := by
            rw [abs_neg, abs_neg]
    calc _ ≤ _ := hsplit
      _ ≤ 324 * 10 ^ 25 * B ^ 4 + 324 * 10 ^ 26 * B ^ 4 + 90 * 10 ^ 25 * B ^ 4 + 5 * 10 ^ 24 * B ^ 4 := by
            linarith [hA, hBb, hCc, hDd]
      _ ≤ 4 * 10 ^ 28 * B ^ 4 := by nlinarith [pow_nonneg hB.le 4]
  -- name the 7 signed terms
  set T1 := -5 * d1 ^ 3 * e1 ^ 2 with hT1
  set T2 := 2 * d * (d * d2 + 5 * d1 ^ 2) * e1 * e2 with hT2
  set T3 := 2 * d ^ 2 * d1 * e1 * e3 with hT3
  set T4 := 2 * (d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4) * e1 with hT4
  set T5 := 2 * d ^ 2 * d1 * e2 ^ 2 with hT5
  set T6 := 2 * d * d1 * (5 * d1 ^ 2 - d * d2) * e2 with hT6
  set T7 := 2 * d ^ 2 * d1 ^ 2 * e3 with hT7
  -- per-term magnitude bounds (each `≤ Kᵢ·ℓ₁B⁵/R`)
  have hT1bd : |T1| ≤ (5 * 10 ^ 44) * (l1 * B ^ 5 / R) := by
    rw [hT1]
    calc |(-5 * d1 ^ 3 * e1 ^ 2 : ℝ)|
        ≤ 5 * (10 ^ 6 * B) ^ 3 * (l1 * (10 ^ 13 * (B / R))) ^ 2 := by
          rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(-5 : ℝ)| = 5 from by norm_num]; gcongr
      _ = (5 * 10 ^ 44) * (l1 ^ 2 * B ^ 5 / R ^ 2) := by field_simp <;> ring
      _ ≤ (5 * 10 ^ 44) * (l1 * B ^ 5 / R) := by exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hT2bd : |T2| ≤ (72 * 10 ^ 46) * (l1 * B ^ 5 / R) := by
    rw [hT2]
    calc |2 * d * (d * d2 + 5 * d1 ^ 2) * e1 * e2|
        ≤ 2 * (18 * (B * R)) * (2 * 10 ^ 14 * B ^ 2) * (l1 * (10 ^ 13 * (B / R)))
            * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]; gcongr
      _ = (72 * 10 ^ 46) * (l1 ^ 2 * B ^ 5 / R ^ 2) := by field_simp <;> ring
      _ ≤ (72 * 10 ^ 46) * (l1 * B ^ 5 / R) := by exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hT3bd : |T3| ≤ (1296 * 10 ^ 44) * (l1 * B ^ 5 / R) := by
    rw [hT3]
    calc |2 * d ^ 2 * d1 * e1 * e3|
        ≤ 2 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (l1 * (10 ^ 13 * (B / R)))
            * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, show |(2 : ℝ)| = 2 from by norm_num]
          gcongr
      _ = (1296 * 10 ^ 44) * (l1 ^ 2 * B ^ 5 / R ^ 2) := by field_simp <;> ring
      _ ≤ (1296 * 10 ^ 44) * (l1 * B ^ 5 / R) := by
            exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hT4bd : |T4| ≤ (8 * 10 ^ 41) * (l1 * B ^ 5 / R) := by
    rw [hT4]
    calc |2 * (d ^ 2 * d1 * s4 - d ^ 2 * d2 ^ 2 - 5 * d * d1 ^ 2 * d2 + 5 * d1 ^ 4) * e1|
        ≤ 2 * (4 * 10 ^ 28 * B ^ 4) * (l1 * (10 ^ 13 * (B / R))) := by
          rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]; gcongr
      _ = (8 * 10 ^ 41) * (l1 * B ^ 5 / R) := by field_simp <;> ring
  have hT5bd : |T5| ≤ (648 * 10 ^ 44) * (l1 * B ^ 5 / R) := by
    rw [hT5]
    calc |2 * d ^ 2 * d1 * e2 ^ 2|
        ≤ 2 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) * (l1 * (10 ^ 19 * (B / R ^ 2))) ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, show |(2 : ℝ)| = 2 from by norm_num]
          gcongr
      _ = (648 * 10 ^ 44) * (l1 ^ 2 * B ^ 5 / R ^ 2) := by field_simp <;> ring
      _ ≤ (648 * 10 ^ 44) * (l1 * B ^ 5 / R) := by
            exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hT6bd : |T6| ≤ (72 * 10 ^ 39) * (l1 * B ^ 5 / R) := by
    rw [hT6]
    calc |2 * d * d1 * (5 * d1 ^ 2 - d * d2) * e2|
        ≤ 2 * (18 * (B * R)) * (10 ^ 6 * B) * (2 * 10 ^ 14 * B ^ 2)
            * (l1 * (10 ^ 19 * (B / R ^ 2))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]; gcongr
      _ = (72 * 10 ^ 39) * (l1 * B ^ 5 / R) := by field_simp <;> ring
  have hT7bd : |T7| ≤ (1296 * 10 ^ 37) * (l1 * B ^ 5 / R) := by
    rw [hT7]
    calc |2 * d ^ 2 * d1 ^ 2 * e3|
        ≤ 2 * (18 * (B * R)) ^ 2 * (10 ^ 6 * B) ^ 2 * (l1 * (2 * 10 ^ 25 * (B / R ^ 3))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, show |(2 : ℝ)| = 2 from by norm_num]
          gcongr
      _ = (1296 * 10 ^ 37) * (l1 * B ^ 5 / R) := by field_simp <;> ring
  -- triangle inequality on the 7 signed terms
  have htri : |T1 + T2 - T3 - T4 - T5 + T6 - T7|
      ≤ |T1| + |T2| + |T3| + |T4| + |T5| + |T6| + |T7| := by
    have s1 := abs_sub (T1 + T2 - T3 - T4 - T5 + T6) T7
    have s2 := abs_add_le (T1 + T2 - T3 - T4 - T5) T6
    have s3 := abs_sub (T1 + T2 - T3 - T4) T5
    have s4' := abs_sub (T1 + T2 - T3) T4
    have s5 := abs_sub (T1 + T2) T3
    have s6 := abs_add_le T1 T2
    linarith [s1, s2, s3, s4', s5, s6]
  -- final numeric combine
  have hXnn : (0:ℝ) ≤ l1 * B ^ 5 / R := by positivity
  have h2l1 : 2 * 10 ^ 77 * l1 ≤ R := by nlinarith [hsmall, hl1]
  have hfin : (10 : ℝ) ^ 48 * (l1 * B ^ 5 / R) ≤ B ^ 5 / (2 * 10 ^ 29) := by
    rw [show (10 : ℝ) ^ 48 * (l1 * B ^ 5 / R) = (10 ^ 48 * (l1 * B ^ 5)) / R from by ring,
        div_le_div_iff₀ hR (by positivity)]
    nlinarith [mul_nonneg (pow_pos hB 5).le (sub_nonneg.mpr h2l1), pow_pos hB 5]
  calc |T1 + T2 - T3 - T4 - T5 + T6 - T7|
      ≤ |T1| + |T2| + |T3| + |T4| + |T5| + |T6| + |T7| := htri
    _ ≤ ((5 * 10 ^ 44) + (72 * 10 ^ 46) + (1296 * 10 ^ 44) + (8 * 10 ^ 41) + (648 * 10 ^ 44)
          + (72 * 10 ^ 39) + (1296 * 10 ^ 37)) * (l1 * B ^ 5 / R) := by
        have := hT1bd; have := hT2bd; have := hT3bd; have := hT4bd
        have := hT5bd; have := hT6bd; have := hT7bd
        nlinarith [hT1bd, hT2bd, hT3bd, hT4bd, hT5bd, hT6bd, hT7bd, hXnn]
    _ ≤ (10 : ℝ) ^ 48 * (l1 * B ^ 5 / R) := by
        apply mul_le_mul_of_nonneg_right _ hXnn; norm_num
    _ ≤ B ^ 5 / (2 * 10 ^ 29) := hfin

end Squarefree
