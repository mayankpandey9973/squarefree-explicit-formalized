import Squarefree.Params
import Squarefree.Structure.DaSpacing
import Squarefree.Lower.Prop51Assembly
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §5 lower-bound input: Prop 5.1 (layer L?)

Faithful statement of Prop 5.1 from `../explicit_writeup.md` (lines 731–741), PROVED via
the §5 assembly: `prop51_perpair` (per-pair fiber count ≤ `Bcombine`) feeds
`Ra_card_le_popular` (Markov/popularity pair-sum) and `prop51_combine` (W²-fold to the
3-term RHS), with the window `Wnat := ⌈128·Wval⌉₊` (so `128W ≤ Wnat ≤ 130W`).
-/

open Classical Finset

namespace Squarefree

set_option exponentiation.threshold 500 in
/-- **Prop 5.1** (writeup 731–741). `Ra` is the §3 set `ℛ_a` (cardinality `#ℛ_a`):
the structural hypothesis `∀ r ∈ Ra, RaWitness P S a r` records that each `r ∈ Ra` is
witnessed by a popular `d` at the `D`-scale with `r ≈ R_a(d)` (writeup §3 / `DaSpacing`).

The two regime hypotheses `GU^{10} ≤ H/Δ²` and `G²U^5 ≤ Δ` and the popularity hypothesis
`R/W ≤ #ℛ_a` are the writeup's `≫`/`≥` constraints with the absolute constants normalised to
`1` (per `CLAUDE.md` §7): they are genuine bare inequalities, not the logically-vacuous
`∃ c>0, c·(…) ≤ (…)` forms (any tiny `c` would satisfy those), so the regime/popularity
constraints are actually imposed.

The AUDITED-FAITHFUL regime pack (regime ruling 2026-06-10) records the ambient `X`-largeness /
band / window facts the §5 step lemmas consume (all discharged by the large-`x` branch of
`dblock_off_strip`): scale floors `1 ≤ G, U, Δ, H`, the band facts `Ω ≤ U` and
`1 ≤ G·U³·Ω⁴`, the `X`-largeness `10³³ ≤ U`, the regime calibrations `U⁹ ≤ G⁷H²`,
`10¹⁵·G⁴U²⁰ ≤ Δ`, `10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴`, the Step-4 witness-defect half-width budget
`10⁷⁰·(1/Δ)G⁴U¹⁵/Ω⁵ ≤ 1/2` (exact `Step4Capstone` form), the `a`-window `A/5 ≤ a ≤ 11A`,
`60Ω ≤ H`, and the `N`-free log cap: the Step-3 `hlogcap` evaluated at the `hNenv` max cap
`10⁹⁰(Na+Nb+Nc)` (it implies `log N + 1 ≤ G³U¹⁵√Δ·Ω` for every `N` below the cap by log
monotonicity).  NOT included (ruled UNFAITHFUL): `1 ≤ Ω` and `G ≤ U`. -/
theorem prop_5_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a → 10 * S.A ≤ S.D →
      (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 → ∀ (Ra : Finset ℕ),
      (∀ r ∈ Ra, RaWitness P S a r) →
      (P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) →
      (P.G ^ 2 * P.U ^ 5 ≤ S.Δ) →
      (S.R / P.Wval ≤ (Ra.card : ℝ)) →
      -- AUDITED-FAITHFUL regime pack (regime ruling 2026-06-10)
      (1 ≤ P.G) → (1 ≤ P.U) → (1 ≤ S.Δ) → (1 ≤ P.H) →
      (S.Ω ≤ P.U) → (1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) → ((10:ℝ) ^ 33 ≤ P.U) →
      (P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) →
      (10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) →
      (10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14) →
      (10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) ≤ 1 / 2) →
      (S.A / 5 ≤ (a : ℝ)) → ((a : ℝ) ≤ 11 * S.A) →
      (60 * S.Ω ≤ P.H) →
      (Real.log (10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
          + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
          + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) + 1
        ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω) →
      (Ra.card : ℝ) ≤ C * (P.H / S.Δ) *
        ( P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω)
        + P.G ^ 16 * P.U ^ 85 / (S.Δ * S.Ω ^ 13)
        + (S.Δ ^ 2 / P.H) * (P.G ^ 16 * P.U ^ 100) / S.Ω ^ 27 ) := by
  refine ⟨10 ^ 415, by positivity, ?_⟩
  intro P S a ha hAD hGHΩ Ra hwit hreg1 hreg2 hpop hG1 hU1 hΔ1 hH1 hΩU hband hX
    hUcal hDeW hHbig hδbud haA1 haA2 hΩH hlogcap
  classical
  have hGpos := P.G_pos; have hUpos := P.U_pos
  -- ===== the Wnat window: `Wnat := ⌈128·Wval⌉₊`, so `128W ≤ Wnat ≤ 130W` =====
  have hWpos : 0 < P.Wval := by rw [Globals.Wval]; positivity
  have hW1 : (1 : ℝ) ≤ P.Wval := by
    have hU5 : (1 : ℝ) ≤ P.U ^ 5 := one_le_pow₀ hU1
    rw [Globals.Wval]; nlinarith
  set Wnat : ℕ := ⌈128 * P.Wval⌉₊ with hWnatdef
  have hWlo : 128 * P.Wval ≤ (Wnat : ℝ) := Nat.le_ceil _
  have hWnatpos : 0 < Wnat := by
    rw [hWnatdef]; exact Nat.ceil_pos.mpr (by linarith)
  have hWhi : (Wnat : ℝ) ≤ 130 * P.Wval := by
    have hc : (Wnat : ℝ) < 128 * P.Wval + 1 := by
      rw [hWnatdef]; exact Nat.ceil_lt_add_one (by linarith)
    linarith
  -- ===== the per-pair budget `B` (off-window truncated fiber count) =====
  set B : ℕ → ℕ → ℝ := fun ℓ₁ ℓ₂ =>
    if 0 < ℓ₁ ∧ ℓ₁ < ℓ₂ ∧ ℓ₂ ≤ Wnat
    then ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ) else 0 with hBdef
  have hBnn : ∀ ℓ₁ ℓ₂, 0 ≤ B ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂; simp only [hBdef]; split <;> positivity
  have hB0 : ∀ ℓ₁ ℓ₂, ¬(0 < ℓ₁ ∧ ℓ₁ < ℓ₂ ∧ ℓ₂ ≤ Wnat) → B ℓ₁ ℓ₂ = 0 := by
    intro ℓ₁ ℓ₂ h; simp only [hBdef]; rw [if_neg h]
  have hpair : ∀ ℓ₁ ℓ₂ : ℕ, 0 < ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ Wnat →
      ((Ra.filter (fun r => r + ℓ₁ ∈ Ra ∧ r + ℓ₂ ∈ Ra)).card : ℝ) ≤ B ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂ h1 h12 h2W
    simp only [hBdef]; rw [if_pos ⟨h1, h12, h2W⟩]
  have hBle : ∀ ℓ₁ ℓ₂, 0 < ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ Wnat → B ℓ₁ ℓ₂ ≤ Bcombine P S ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂ h1 h12 h2W
    have hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval := by
      have hc : (ℓ₂ : ℝ) ≤ (Wnat : ℝ) := by exact_mod_cast h2W
      linarith
    have hcount := prop51_perpair P S a ha hAD hGHΩ Ra hwit hreg1 hreg2 hpop hG1 hU1 hΔ1
      hH1 hΩU hband hX hUcal hDeW hHbig hδbud haA1 haA2 hΩH hlogcap ℓ₁ ℓ₂ ⟨h1, h12, hℓ2W⟩
    simp only [hBdef]; rw [if_pos ⟨h1, h12, h2W⟩]; exact hcount
  -- ===== the Markov window and popularity discharge =====
  have hRfloor := prop51_R_floor (P := P) (S := S) hreg1 hband hΩU hG1 hU1 hX hDeW
  have hRW8 : 8 * P.Wval ≤ S.R := by
    have h8 : 8 * P.Wval ≤ 10 ^ 113 * P.Wval := by nlinarith
    rw [Globals.Wval] at h8; rw [Globals.Wval]
    calc 8 * (P.G * P.U ^ 5) ≤ 10 ^ 113 * (P.G * P.U ^ 5) := h8
      _ ≤ S.R := hRfloor
  have hRpos : (0 : ℝ) < S.R :=
    lt_of_lt_of_le (by positivity) hRfloor
  have hm : ∀ r ∈ Ra, (1/72) * S.R ≤ (r : ℝ) :=
    fun r hr => (dStarOf_spec (hwit r hr)).2.2.2.2.1
  have hM : ∀ r ∈ Ra, (r : ℝ) ≤ 16 * S.R :=
    fun r hr => (dStarOf_spec (hwit r hr)).2.2.2.2.2
  have hpopM := markov_discharge (P := P) (S := S) (Ra := Ra) (Wnat := Wnat)
    hRW8 hWlo hWpos hpop
  have hcard := Ra_card_le_popular (Ra := Ra) (Wnat := Wnat)
    (m := (1/72) * S.R) (M := 16 * S.R) (B := B)
    hWnatpos hBnn (by linarith) hm hM hpair hpopM
  -- ===== combine: `2·Σ B ≤ 10⁴¹⁵·(H/Δ)·(3 terms)` =====
  have hcombine := prop51_combine (P := P) (S := S) hG1 hU1 hΩU hband hreg2
    Wnat ⟨by linarith, hWhi⟩ B hBle hB0
  linarith

end Squarefree
