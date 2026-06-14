import Squarefree.Bracket.Sec7MonExpFam1
import Squarefree.Bracket.Sec7MonExpFam2
import Squarefree.Bracket.Sec7MonExpFam3

/-!
# §7 N9′ — the `Sec7MonExp` constructor at the §3 site (A3 gate ruling)

A3 GATE RULING (formalization_plan.md): the N9 bundle `Sec7MonExp` is BUILT at the §3 site
— the abstract `Sec7Phase` admits no monomial expansion.  The §3 inputs are the value-level
monomial expansions of `f₁, f₂, f₃` (md 1589–1605), which follow from the `R_a`/`F_a`
expansions `R_a(d) = Xa³/d⁴·(1 − 2a/d + O((a/d)²))` (md 326–344) and the `C⁵` control
`d̃_a^{(j)}(ρ) ≍ HΔ/Rʲ` (md 341–344; in-tree `dtilde_d1_bounds` … `dtilde_d5_upper`).
They are packaged as `Sec7RaExpData`: graded error families `e_iD` (derivative chains to
order 5 = m + 3 with m ≤ 2, exactly the md-343 orders) with bounds
`|e_iD m| ≤ cExpIn·(T_i/Rᵐ)·(Ω/H)` on the wide window, plus the leading coefficients
`c₁, c₂` (md 1602: `c_d, c₁, c₂, c₃ ≠ 0`; exact §3 values `c₁ = (a/A)²/6 ∈ [1/6, 2/3]`,
`c₂ = 2(a/A)^{-5/4} ∈ [2^{-1/4}, 2]`, windows `[1/16, 4]` with slack; sympy-banked).
`c₃ = 3c₁c₂` is DEFINITIONAL here (A3: chain rule `f₃' = −f₁f₂'` on leading monomials),
so the input `f₃`-expansion is stated against `3c₁c₂` directly.

The constructor `sec7_monExp_build` derives the nine differenced N9 fields (md 1606–33)
by differencing the leading monomials: MVT/Taylor on the explicit `sec7_powMonD` families
plus the graded error chains.  Constant ledger (sympy-banked, 2026-06-12): worst field
`d3f3_exp` at `m = 2` costs `|c₃|·|aprod(−1/4,6)|·(2·cWin)^{25/4} ≈ 1.05·10²⁴ ≤ sec7_cExp
= 10²⁵` (9.5× margin); `sec7_cExpIn = 10²` covers all error-part terms.

Hypothesis discharge at the §7 call site: `1 ≤ hᵢ` and `|ξᵢ| ≤ h_Σ` from the shift box /
N6 realignment (md 1528–29); the additive window hypotheses keep all displaced points
inside the wide `r`-window.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

/-- **N9′ — the `Sec7MonExp` constructor at the §3 site** (A3 gate ruling; md 1589–1633
from md 326–344).  From the §3 expansion data `Sec7RaExpData`, the shift-box positivity
`1 ≤ hᵢ`, the realignment-shift bounds `|ξᵢ| ≤ h_Σ` (md 1528–29), and the smallness
`24·h_Σ·cWin ≤ R` (from `h_Σ ≤ 3W⁴` and the N18 side condition `R ≥ W⁸`), build the N9
bundle: `c₃ := 3c₁c₂` definitionally (md 1662–63), the coefficient windows from the §3
windows `[1/16, 4]`, and the nine differenced expansions by MVT/Taylor differencing of
the leading monomials. -/
noncomputable def sec7_monExp_build {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (RE : Sec7RaExpData P S W a Ph j)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ where
  c₁ := RE.c₁
  c₂ := RE.c₂
  c₃ := 3 * RE.c₁ * RE.c₂
  c₁_window := ⟨RE.c₁_lo, RE.c₁_hi⟩
  c₂_window := ⟨RE.c₂_lo, RE.c₂_hi⟩
  c₃_window := by
    have habs : |3 * RE.c₁ * RE.c₂| = 3 * |RE.c₁| * |RE.c₂| := by
      rw [abs_mul, abs_mul]; norm_num
    constructor
    · rw [habs]
      have h1 := RE.c₁_lo; have h2 := RE.c₂_lo
      have h0 : (0:ℝ) ≤ |RE.c₁| := abs_nonneg _
      nlinarith
    · rw [habs]
      have h1 := RE.c₁_hi; have h2 := RE.c₂_hi
      have h1n : (0:ℝ) ≤ |RE.c₁| := abs_nonneg _
      have h2n : (0:ℝ) ≤ |RE.c₂| := abs_nonneg _
      nlinarith
  c₃_eq := by ring
  f1C := fun k t => RE.e₁D k t + sec7_powMonD S.R (RE.c₁ * S.T₁) (-1) k t
  f2C := fun k t => RE.e₂D k t + sec7_powMonD S.R (RE.c₂ * S.T₂) ((3:ℝ)/4) k t
  f3C := fun k t => RE.e₃D k t + sec7_powMonD S.R (3 * RE.c₁ * RE.c₂ * S.T₃) (-(1:ℝ)/4) k t
  f1C_zero := by
    intro t
    rw [RE.e₁D_zero t, sec7_powMonD_zero]
    unfold sec7_powMon
    ring
  f2C_zero := by
    intro t
    rw [RE.e₂D_zero t, sec7_powMonD_zero]
    unfold sec7_powMon
    ring
  f3C_zero := by
    intro t
    rw [RE.e₃D_zero t, sec7_powMonD_zero]
    unfold sec7_powMon
    ring_nf
  f1C_deriv := fun m hm r hr =>
    (RE.e₁D_deriv m (by omega) r hr).add
      (sec7_powMonD_hasDerivAt (sec7_R_pos S) _ _ m (sec7_rWinWide_pos hpad hr))
  f2C_deriv := fun m hm r hr =>
    (RE.e₂D_deriv m (by omega) r hr).add
      (sec7_powMonD_hasDerivAt (sec7_R_pos S) _ _ m (sec7_rWinWide_pos hpad hr))
  f3C_deriv := fun m hm r hr =>
    (RE.e₃D_deriv m (by omega) r hr).add
      (sec7_powMonD_hasDerivAt (sec7_R_pos S) _ _ m (sec7_rWinWide_pos hpad hr))
  f1_exp := RE.build_f1_exp hh₁ hh₂ hh₃ hW hpad hshift
  d1f1_exp₁ := RE.build_d1f1_exp hh₁ hh₂ hh₃ hh₁
    (by have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
        have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
        show (h₁:ℝ) ≤ (h₁:ℝ) + h₂ + h₃; linarith) hW hpad hshift
  d1f1_exp₂ := RE.build_d1f1_exp hh₁ hh₂ hh₃ hh₂
    (by have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
        have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
        show (h₂:ℝ) ≤ (h₁:ℝ) + h₂ + h₃; linarith) hW hpad hshift
  d1f1_exp₃ := RE.build_d1f1_exp hh₁ hh₂ hh₃ hh₃
    (by have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
        have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
        show (h₃:ℝ) ≤ (h₁:ℝ) + h₂ + h₃; linarith) hW hpad hshift
  B_exp₁ := RE.build_B_exp hh₁ hh₂ hh₃ hh₂ hh₃
    (by have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
        show (h₂:ℝ) + h₃ ≤ (h₁:ℝ) + h₂ + h₃; linarith) hξ₁ hW hpad hshift
  B_exp₂ := RE.build_B_exp hh₁ hh₂ hh₃ hh₁ hh₃
    (by have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
        show (h₁:ℝ) + h₃ ≤ (h₁:ℝ) + h₂ + h₃; linarith) hξ₂ hW hpad hshift
  B_exp₃ := RE.build_B_exp hh₁ hh₂ hh₃ hh₁ hh₂
    (by have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
        show (h₁:ℝ) + h₂ ≤ (h₁:ℝ) + h₂ + h₃; linarith) hξ₃ hW hpad hshift
  B03_exp := RE.build_B03_exp hh₁ hh₂ hh₃ hW hpad hshift
  d3f3_exp := RE.build_d3f3_exp hh₁ hh₂ hh₃ hW hpad hshift

end Squarefree
