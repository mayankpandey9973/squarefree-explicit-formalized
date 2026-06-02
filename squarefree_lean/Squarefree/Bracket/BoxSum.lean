import Squarefree.Params
import Squarefree.Bracket.Admissible
import Squarefree.Counting.Preimage
import Squarefree.Structure.DaSpacing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

/-!
# §7 box-sum bracket counts (Prop 7.1, Prop 7.3)

Faithful `sorry`-stubbed statements of Prop 7.1 and Prop 7.3 from `../explicit_writeup.md`
(lines 1404–1435 and 1993–2000). These elaborate but are not yet proved; each `sorry` is
tagged `STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset Squarefree.Counting

namespace Squarefree

/-- **Prop 7.1** (writeup 1404–1435). Fixed `j` in band `|j| ≪ 1+H/A²`:
`#{r≍R : ‖g_j(r)‖ ≤ δ₀} ≪ R/W` under the admissibility envelope. `g_j`, `f̃ₐ`, `d̆ₐ`, `δ₀`
supplied with defining hypotheses (δ₀ bounded by the corrected `Δ⁵/(H³G²Ω²)+Δ²/(H²GA)`). -/
theorem prop_7_1 (P : Globals) (S : Scale P) (W : ℝ) (hW : AdmissibleW P S W)
    (ftil dBreve dBreve' : ℝ → ℝ) (gfun : ℤ → ℝ → ℝ)
    (hg : ∀ (j : ℤ) (r : ℝ),
        gfun j r = dBreve (ftil r + j) - dBreve' (ftil r + j) * Int.fract (ftil r))
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀)
    (hδ₀ : δ₀ ≤ S.Δ ^ 5 / (P.H ^ 3 * P.G ^ 2 * S.Ω ^ 2) + S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A))
    (j : ℤ) (cj : ℝ) (hcj : 0 < cj) (hj : (|j| : ℝ) ≤ cj * (1 + P.H / S.A ^ 2)) :
    ∃ C : ℝ, 0 < C ∧
      (((Finset.Icc ⌈S.R⌉ ⌊2 * S.R⌋).filter (fun r => distInt (gfun j (r : ℝ)) ≤ δ₀)).card : ℝ)
        ≤ C * (S.R / W) := by
  sorry -- STUB: prop_7_1

/-- **Prop 7.3** (writeup 1993–2000): `#ℛ_a ≪ (1+H/A²)·R/W`. `Ra` is the §3 set (mapped into 𝒟_a). -/
theorem prop_7_3 (P : Globals) (S : Scale P) (a : ℤ) (ha : 0 < a) (W : ℝ)
    (hW : AdmissibleW P S W)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ) (hRa : ∀ r ∈ Ra, inDa P.X P.H a (dStar r)) :
    ∃ C : ℝ, 0 < C ∧ (Ra.card : ℝ) ≤ C * ((1 + P.H / S.A ^ 2) * (S.R / W)) := by
  sorry -- STUB: prop_7_3

end Squarefree
