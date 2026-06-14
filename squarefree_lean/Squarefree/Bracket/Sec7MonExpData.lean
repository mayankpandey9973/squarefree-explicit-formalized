import Squarefree.Bracket.Sec7PhaseExp
import Squarefree.Bracket.Sec7MonExpAux

/-!
# §7 N9′ data layer — windows, helpers, and the §3 input pack `Sec7RaExpData`

Support layer for the N9′ constructor (`Sec7MonExpBuild.lean`; A3 gate ruling: the
`Sec7MonExp` bundle is BUILT at the §3 site, md 326–344 / 1589–1633).  Contents: the
input constant `sec7_cExpIn`, the wide/mid `r`-windows with their membership lemmas,
scale-positivity and monomial sup-bound helpers shared by the N9′ family lemmas
(`Sec7MonExpFam*.lean`), and the §3 input pack `Sec7RaExpData` (md 1589–1605: leading
coefficients `c₁, c₂` with exact §3 windows `c₁ = (a/A)²/6 ∈ [1/6, 2/3]`,
`c₂ = 2(a/A)^{-5/4} ∈ [2^{-1/4}, 2]` inside `[1/16, 4]`, plus the graded expansion-error
families `e_iD` to order 5 = m + 3, the md-343 `C⁵` control `d̃_a^{(j)} ≍ HΔ/Rʲ`).
`c₃ = 3c₁c₂` is definitional at the constructor (md 1662–63 chain rule on leading
monomials), so the `f₃`-expansion is stated against `3c₁c₂` directly.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

set_option maxHeartbeats 1600000

/-! ### Shared private helpers for the family lemmas
(The wide/mid window layer `sec7_rWinWide`/`sec7_rWinMid` and its membership lemmas
moved to `Sec7Defs.lean` so the `Sec7MonExp` chain fields can state against them.) -/

theorem sec7_T₁_pos {P : Globals} (S : Scale P) : 0 < S.T₁ := by
  have := P.H_pos; have := P.G_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold Scale.T₁ Scale.F; positivity

theorem sec7_T₂_pos {P : Globals} (S : Scale P) : 0 < S.T₂ := by
  have := P.H_pos; have := P.G_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold Scale.T₂ Scale.F; positivity

theorem sec7_T₃_pos {P : Globals} (S : Scale P) : 0 < S.T₃ := by
  have := P.H_pos; have := S.Δ_pos; unfold Scale.T₃; positivity

theorem sec7_relErr_pos (P : Globals) (S : Scale P) : 0 < sec7_relErr P S := by
  have := P.H_pos; have := S.Ω_pos; have := P.U_pos; unfold sec7_relErr; positivity

theorem sec7_hSum_ge3 {h₁ h₂ h₃ : ℤ} (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃) :
    (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
  have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
  have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
  have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
  unfold sec7_hSum; linarith

/-- Points within the additive shift pad of the mid window are in the wide window. -/
theorem sec7_mem_wide_of_near {P : Globals} {S : Scale P} {W r d : ℝ}
    (hr : r ∈ sec7_rWinMid S W) (hd : |d| ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    r + d ∈ sec7_rWinWide S W :=
  sec7_mid_add_mem_wide hr hd

/-- Sup-bound for the graded monomials on the wide window (nonpositive exponent). -/
theorem sec7_powMonD_wide_bound {P : Globals} {S : Scale P} {W c α : ℝ} {k : ℕ}
    (hαk : α - (k:ℝ) ≤ 0)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    {x : ℝ} (hx : x ∈ sec7_rWinWide S W) :
    |sec7_powMonD S.R c α k x| ≤
      |c| * |sec7_aprod α k| / S.R ^ k * (2 * sec7_cWin) ^ ((k:ℝ) - α) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hK : (1:ℝ) ≤ 2 * sec7_cWin := by norm_num [sec7_cWin]
  have hx0 : 0 < x / S.R := div_pos (sec7_rWinWide_pos hpad hx) hR
  have hlo : 1 / (2 * sec7_cWin) ≤ x / S.R := sec7_rWinWide_div_lo hpad hx
  have h := sec7_powMon_abs_le (R := S.R) (c := c * sec7_aprod α k / S.R ^ k)
    (α := α - k) (K := 2 * sec7_cWin) (t := x) hK hαk hx0 hlo
  have habs : |c * sec7_aprod α k / S.R ^ k| = |c| * |sec7_aprod α k| / S.R ^ k := by
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hR k)]
  have hexp : -(α - (k:ℝ)) = (k:ℝ) - α := by ring
  rw [habs, hexp] at h
  exact h

/-- Quarter-integer numeric bound: `(2cWin)^{q/4} ≤ b` from `(2cWin)^q ≤ b⁴`. -/
theorem sec7_rpow_quarter_le {q : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : (2 * sec7_cWin) ^ q ≤ b ^ 4) :
    (2 * sec7_cWin) ^ ((q:ℝ) / 4) ≤ b := by
  have hK : (0:ℝ) < 2 * sec7_cWin := by norm_num [sec7_cWin]
  have h1 : (2 * sec7_cWin) ^ ((q:ℝ) / 4) = ((2 * sec7_cWin) ^ q) ^ ((1:ℝ)/4) := by
    rw [← Real.rpow_natCast (2 * sec7_cWin) q, ← Real.rpow_mul hK.le]
    ring_nf
  have h2 : ((2 * sec7_cWin) ^ q) ^ ((1:ℝ)/4) ≤ (b ^ 4) ^ ((1:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h3 : (b ^ 4) ^ ((1:ℝ)/4) = b := by
    rw [← Real.rpow_natCast b 4, ← Real.rpow_mul hb]
    norm_num
  rw [h1]; rw [h3] at h2; exact h2

/- §3 input pack for N9′ (md 1589–1605 value-level expansions; md 341–44 `C⁵` control).
   The graded families `e_iD` are the §3 expansion errors and their first five derivatives;
   `e_iD_zero` ties grade 0 to the concrete phase pieces of `Sec7Phase` (md 1505–07), and
   the chains live on the OPEN wide window so that plain `iteratedDeriv` is honest. -/
/-- **§3 expansion data** for the fiber `a` and §7 shift `j` (md 1589–1605): leading
coefficients `c₁, c₂` with their windows, and the graded expansion-error families of
`f₁ − c₁T₁y⁻¹`, `f₂ − c₂T₂y^{3/4}`, `f₃ − 3c₁c₂T₃y^{-1/4}` to order 5, with bounds
`cExpIn·(T_i/Rᵐ)·(Ω/H)` on the wide window.  Produced by the §3 layer (`Rfun`/`Ffun`/
`dtilde`, md 326–344); consumed by `sec7_monExp_build`. -/
structure Sec7RaExpData (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) (Ph : Sec7Phase P S W a)
    (j : ℤ) where
  c₁ : ℝ
  c₂ : ℝ
  c₁_lo : 1 / 16 ≤ |c₁|
  c₁_hi : |c₁| ≤ 4
  c₂_lo : 1 / 16 ≤ |c₂|
  c₂_hi : |c₂| ≤ 4
  e₁D : ℕ → ℝ → ℝ
  e₂D : ℕ → ℝ → ℝ
  e₃D : ℕ → ℝ → ℝ
  e₁D_zero : ∀ t, e₁D 0 t = Ph.f1D j 0 t - c₁ * S.T₁ * (t / S.R) ^ (-(1:ℝ))
  e₂D_zero : ∀ t, e₂D 0 t = Ph.f2D 0 t - c₂ * S.T₂ * (t / S.R) ^ ((3:ℝ)/4)
  e₃D_zero : ∀ t, e₃D 0 t = Ph.f3D j 0 t - 3 * c₁ * c₂ * S.T₃ * (t / S.R) ^ (-(1:ℝ)/4)
  e₁D_deriv : ∀ m < 5, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (e₁D m) (e₁D (m + 1) r) r
  e₂D_deriv : ∀ m < 5, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (e₂D m) (e₂D (m + 1) r) r
  e₃D_deriv : ∀ m < 5, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (e₃D m) (e₃D (m + 1) r) r
  e₁D_bound : ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
    |e₁D m r| ≤ sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErr P S
  e₂D_bound : ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
    |e₂D m r| ≤ sec7_cExpIn * (S.T₂ / S.R ^ m) * sec7_relErr P S
  e₃D_bound : ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
    |e₃D m r| ≤ sec7_cExpIn * (S.T₃ / S.R ^ m) * sec7_relErr P S
end Squarefree
