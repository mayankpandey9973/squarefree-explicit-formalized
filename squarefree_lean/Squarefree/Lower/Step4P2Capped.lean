import Squarefree.Lower.Step4P2Size

/-!
# §5 Step-4 large-defect `p₂/d̃` CAPPED (s-independent) additive budget

This is the **auditor-corrected** form of the `p₂`-contribution point budget.  The naive
route substitutes the per-`s` pin `Vx ≍ V_s` (`v² ≍ Δ²Ω²|s|/L`) into the polynomial majorant
`P2AbsMaj`, producing a budget `∝ |s|²` whose summation over `|s| ≤ S` lands at the *wrong*
power `S^{3/2}` (the "X-finding" failure).

The fix is to evaluate the majorant at the **global `v`-cap**
`Vmax := 10²⁰·(Δ·U⁵/Ω³)` (the `V₂ ≤ Vmax` band cutoff `monotoneV2Upper`), giving an
**s-INDEPENDENT** additive term `E0_p2`.  Because the actual `|v|` for the fibre is `≤ Vmax`
regardless of `s` (that is the content of the cap), the same point bound holds with `Vmax`
in place of `V_s`.  The `s`-dependence then re-enters only downstream through the per-`s`
fibre weight `1/(Ĉ·V_s)`, so

  `Σ_{|s|≤S} E0_p2/(Ĉ·V_s) ≍ E0_p2·Σ_{|s|≤S} |s|^{-1/2} ≍ E0_p2·S^{1/2}`,

the **faithful** `S^{1/2}` power.

`E0_p2` reuses the majorant `P2AbsMaj` and the parametrized point budget
`abs_pref_mul_Ptwo_div_le_p2PointBudget` from `Step4P2Size.lean` verbatim; only the
`v`-argument is the fixed scale `Vmax` (NOT `V_s s`).  The `b₀`-box is the §5 window corner
`3·10¹²·B = 3·10¹²·Δ²/(GΩ³)` already threaded as `hb0` through `Step4Combine`.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

/-- The global `v`-cap `Vmax = 10²⁰·(Δ·U⁵/Ω³)` (the `V₂ ≤ Vmax` band cutoff).  This is a
**fixed scale**, manifestly independent of the band index `s`. -/
noncomputable def Vmax (P : Globals) (S : Scale P) : ℝ :=
  10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)

theorem Vmax_nonneg : 0 ≤ Vmax P S := by
  have := S.Δ_pos; have := P.U_pos; have := S.Ω_pos
  unfold Vmax; positivity

/-- **The s-INDEPENDENT capped `p₂` additive budget** `E0_p2`.  The polynomial majorant
`P2AbsMaj` evaluated at the §5 box corner `b₀ = 3·10¹²·B` and the `v`-cap `v = Vmax`, scaled
by the `pref`-bound `77·(GΩ/Δ⁴)` and the defect floor `1/D`.  No `s` occurs: the cap is what
makes this additive term constant across the band, hence the downstream `S^{1/2}` power. -/
noncomputable def E0_p2 (P : Globals) (S : Scale P) (ℓ₁ ℓ₂ : ℝ) : ℝ :=
  77 * (P.G * S.Ω / S.Δ ^ 4) *
    (P2AbsMaj ℓ₁ ℓ₂ (3000000000000 * S.B) (Vmax P S) / S.D)

theorem E0_p2_nonneg {ℓ₁ ℓ₂ : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    0 ≤ E0_p2 P S ℓ₁ ℓ₂ := by
  have hGpos := P.G_pos; have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hBx0 : (0:ℝ) ≤ 3000000000000 * S.B := by
    unfold Scale.B; positivity
  have hVx0 : (0:ℝ) ≤ Vmax P S := Vmax_nonneg
  unfold E0_p2 P2AbsMaj
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have h2ℓ : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  positivity

/-- **§5 Step-4 large-defect `p₂/d̃` CAPPED additive bound** (auditor-corrected).

The magnitude of the quartic `P₂`-contribution `pref·(P₂/d̃)` to `Σ_closed`
(`pref = (Xa/d⁵)(−4+10a/d)`) is dominated by the **s-INDEPENDENT** budget `E0_p2`, obtained by
evaluating the polynomial majorant at the global `v`-cap `Vmax = 10²⁰ΔU⁵/Ω³` rather than the
per-`s` pin `V_s`.  This is the instantiation `Vx := Vmax`, `Bx := 3·10¹²·B` of the
parametrized point budget `abs_pref_mul_Ptwo_div_le_p2PointBudget`; the cap `hv : |v| ≤ Vmax`
is exactly the §5 band cutoff threaded through `Step4Combine`. -/
theorem p2_capped_additive_le
    {a b₀ v d ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hv : |v| ≤ Vmax P S)
    (hdD : S.D ≤ d)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    |(P.X * a / d ^ 5) * ((-4 + 10 * a / d) * (Ptwo b₀ v ℓ₁ ℓ₂ / d))|
      ≤ E0_p2 P S ℓ₁ ℓ₂ := by
  have hBx0 : (0:ℝ) ≤ 3000000000000 * S.B := by
    have := S.Δ_pos; have := P.G_pos; have := S.Ω_pos
    unfold Scale.B; positivity
  have hbudget := abs_pref_mul_Ptwo_div_le_p2PointBudget
    (S := S) ha0 ha_hi hℓ1 hℓ12 hb0 hBx0 hv (S.D_eps_lo hdD) h1 hG1 hU1 hΔ1 hΩU hUbig
  simpa only [E0_p2] using hbudget

end Squarefree
