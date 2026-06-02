import Squarefree.Params
import Squarefree.Asymp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §3 structural layer: spacing in `𝒟_a` (layer L?)

Faithful `sorry`-stubbed statements of Lemma 3.1 and Prop 3.2 from `../explicit_writeup.md`
(lines 270–322 and 346–393). These elaborate but are not yet proved; each `sorry` is tagged
`STUB: <name>`. See `CLAUDE.md` §3/§4.
-/

open Classical Finset

namespace Squarefree

/-- `d ∈ 𝒟` at window `[X, X+H]`. Matches the predicate inside `dCard`. -/
def inD (X H : ℝ) (d : ℤ) : Prop :=
  ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H

/-- `d ∈ 𝒟_a`: `d, d+a` consecutive 𝒟-elements at gap `a` (`a>0`). -/
def inDa (X H : ℝ) (a d : ℤ) : Prop :=
  0 < a ∧ inD X H d ∧ inD X H (d + a) ∧ ∀ d' : ℤ, d < d' → d' < d + a → ¬ inD X H d'

/-- Roth's quantity `R_a(d) = -(2d-a)X/d² + (2d+3a)X/(d+a)²` (over ℝ). -/
noncomputable def Rfun (X : ℝ) (a d : ℝ) : ℝ :=
  -(2 * d - a) * X / d ^ 2 + (2 * d + 3 * a) * X / (d + a) ^ 2

/-- `#𝒟_a[D,2D]`. -/
noncomputable def DaCard (X H : ℝ) (a : ℤ) (D : ℝ) : ℕ :=
  ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter (fun d => inDa X H a d)).card

/-- **Lemma 3.1**: spacing lower bound in `𝒟_a` (writeup 270–322). -/
theorem lemma_3_1 : ∃ c : ℝ, 0 < c ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a →
      ∀ d b : ℤ, 0 < b → inDa P.X P.H a d → inDa P.X P.H a (d + b) →
        (∃ d' : ℤ, d < d' ∧ d' < d + b ∧ inDa P.X P.H a d') →
        c * (a : ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ) ≤ (b : ℝ) := by
  sorry -- STUB: lemma_3_1

/-- **Prop 3.2** (writeup 346–393). Fiber bound is the STATED WEAK (non-sharp) form. -/
theorem prop_3_2 : ∃ (c₁ C₁ C₂ C₃ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a → ∀ (D : ℝ), 0 < D → ∀ (dtil : ℝ → ℝ),
      ∃ (Ra : Finset ℕ) (dStar : ℕ → ℤ),
        (∀ r ∈ Ra, inDa P.X P.H a (dStar r)) ∧
        (∀ r ∈ Ra, c₁ * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ C₁ * S.R) ∧
        (∀ r ∈ Ra, Rfun P.X (a : ℝ) (dtil (r : ℝ)) = (r : ℝ)) ∧
        ((DaCard P.X P.H a D : ℝ) ≤ C₂ * (Ra.card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ))) ∧
        (∀ r ∈ Ra, |(dStar r : ℝ) - dtil (r : ℝ)| ≤ C₃ * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3)) := by
  sorry -- STUB: prop_3_2

/-- `𝐃(Ω) := ∑_{a∼A} #𝒟_a` (writeup line 2008), the dyadic `A`-block sum of `DaCard`. -/
noncomputable def DBlock (P : Globals) (S : Scale P) (D : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (DaCard P.X P.H a D : ℝ)

end Squarefree
