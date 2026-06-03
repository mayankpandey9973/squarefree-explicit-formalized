import Squarefree.Opt.StripAux
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §8/§9 per-Ω-scale block bound `𝐃(Ω) ≪ H/U`

The core §5–§9 per-scale result, at the `DBlock` (= `𝐃(Ω) = Σ_{a∼A} #𝒟_a`) level.

The dichotomy is split by `Ω` against `c₀·G^{-1/4}U^{-3/4}` for a fixed absolute `c₀` chosen by
`dblock_bound` (the writeup's `Ω ≫ G^{-1/4}U^{-3/4}` threshold, line 406):
* `dblock_bound`     — `Ω ≥ c₀·G^{-1/4}U^{-3/4}` (the band): the lower edge makes Prop 3.2's
  fiber factor `1+Ω^{-8/3}G^{-2/3} ≤ X^{O(u)}`. Strip dichotomy internal (off-strip Props 5.1/6.1;
  on-strip Prop 7.3 + `18977g+15315u<2`).
* `dblock_small_omega` — `Ω ≤ c₀·G^{-1/4}U^{-3/4}` (below the band): the trivial Prop 3.2 bound
  (writeup lines 400–406), no §5/§6/§7. Works for any `c₀`, with `C` depending on `c₀`.

Both carry the Nair–Roth regime hypotheses that `a_decomposition`'s sum range supplies:
`64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A` (every gap in the block is super-threshold) and `2A ≤ D`.
These are exactly `prop_3_2_fiber`'s per-`a` hypotheses lifted to the block scale `A`.

`c₀` is in the existential prefix (chosen by the lemma), NOT a per-application `∃` — the latter
would make the band hypothesis vacuous. Replaces the old `prop_8_1` (`dCard` granularity, no band).
-/

open Classical Finset

namespace Squarefree

/-- **§8/§9 per-Ω block bound.** For `Ω` in the band `[c₀·G^{-1/4}U^{-3/4}, U]` (with `c₀` chosen
here), `𝐃(Ω) ≪ H/U`. Strip dichotomy internal (off-strip: Props 5.1/6.1; on-strip: Prop 7.3 +
`18977g+15315u<2`). The regime hypotheses `64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A`, `2A ≤ D` are supplied by
`a_decomposition`'s sum range. -/
theorem dblock_bound (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ 18977 * g + 15315 * u < 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  sorry -- STUB: dblock_bound

set_option maxHeartbeats 1000000 in
/-- Small-Ω block bound (below the band): the trivial Prop 3.2 bound (writeup 400–406), no §5/§6/§7.
Uniform (absolute) `C`, valid for any band constant `c₀` (with `C` depending on `c₀`). The regime
hypotheses match `dblock_bound`'s, so the two compose over `a_decomposition`'s sum.

The hypothesis `X^{1/100} ≤ Δ` (the long range, supplied by `key_dyadic`) is ESSENTIAL: with only
`1 ≤ Δ` the statement is false — at `Δ=1`, band-edge `Ω`, the `+1`-induced bare `R = HGΩ³/Δ` term
leaves a `+g/4` surplus over `H/U`. The `1/100` margin dominates `g/4 < 1/37954`, so absolute `C`
holds (no `X^{O(u)}`). Term-by-term: the two `A·R` terms are killed by the band edge; `A`, `Δ·…`
by the Nair–Roth Δ-ceiling `Δ ≤ Ω³X/(64³H⁴)`; the two `/Δ` terms by `Δ ≥ X^{1/100}`; the rest by
`H/U → ∞`. (Needs `g < 2/18977`, `u ≤ 1/100`.) -/
theorem dblock_small_omega (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), 1 ≤ P.X → 0 < P.g → P.g < 2 / 18977 → 0 < P.u → P.u ≤ 1 / 100 →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  obtain ⟨c₁, C₁, C₂, hc₁, hC₁, hC₂, hfiber⟩ := prop_3_2_fiber
  -- the absolute constant: sum of the eight monomial constants, times C₂
  refine ⟨C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
      + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1 + (64:ℝ) ^ (-8/3:ℝ)),
    by positivity, ?_⟩
  intro P hX hg0 hg hu0 hu' S hΔlong hNR hAD hband D hDpos hDeq
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hH := P.H_pos
  have hU := P.U_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hG := P.G_pos
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  have hRpos : (0:ℝ) < S.R := by unfold Scale.R; positivity
  -- Δ ≥ 1 from X^{1/100} ≤ Δ and X ≥ 1
  have hΔ1 : (1:ℝ) ≤ S.Δ := le_trans (Real.one_le_rpow hX (by norm_num)) hΔlong
  -- fiber factor abbreviation
  set φ : ℝ := StripAux.fiberφ P S with hφdef
  have hφnn : 0 ≤ φ := by
    rw [hφdef, StripAux.fiberφ_def]; positivity
  -- uniform per-a upper bound M := C₂·(C₁R+1)·(1+φ)
  set M : ℝ := C₂ * (C₁ * S.R + 1) * (1 + φ) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; have : (0:ℝ) ≤ C₁ * S.R + 1 := by positivity
    positivity
  -- DaCard ≤ M for each a in the block
  have hper : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (DaCard P.X P.H a D : ℝ) ≤ M := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨haL, haR⟩ := ha
    -- A ≤ a, a ≤ 2A, 0 < a
    have hAa : S.A ≤ (a:ℝ) := le_trans (Int.le_ceil S.A) (by exact_mod_cast haL)
    have ha2A : (a:ℝ) ≤ 2 * S.A := le_trans (by exact_mod_cast haR) (Int.floor_le (2 * S.A))
    have ha0 : 0 < a := by
      have : (0:ℤ) < ⌈S.A⌉ := Int.ceil_pos.mpr hApos
      omega
    have h2AD : 2 * S.A ≤ S.D := hAD
    obtain ⟨Ra, hRaBand, hRaCard⟩ :=
      hfiber P S a ha0 hΔ1 (le_trans hNR hAa) hAa ha2A h2AD D hDpos hDeq
    -- #Ra ≤ C₁·R + 1
    have hRaSub : Ra ⊆ Finset.range (⌊C₁ * S.R⌋₊ + 1) := by
      intro r hr
      rw [Finset.mem_range]
      have := (hRaBand r hr).2
      have hfloor : r ≤ ⌊C₁ * S.R⌋₊ := Nat.le_floor (by exact_mod_cast this)
      omega
    have hRacard : (Ra.card : ℝ) ≤ C₁ * S.R + 1 := by
      have h1 : Ra.card ≤ ⌊C₁ * S.R⌋₊ + 1 := by
        have := Finset.card_le_card hRaSub
        rwa [Finset.card_range] at this
      have h2 : (⌊C₁ * S.R⌋₊ : ℝ) ≤ C₁ * S.R := Nat.floor_le (by positivity)
      calc (Ra.card : ℝ) ≤ ((⌊C₁ * S.R⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (⌊C₁ * S.R⌋₊ : ℝ) + 1 := by push_cast; ring
        _ ≤ C₁ * S.R + 1 := by linarith [h2]
    -- combine: DaCard ≤ C₂·#Ra·(1+φ) ≤ C₂·(C₁R+1)·(1+φ) = M
    rw [hMdef]
    have h1φ : (0:ℝ) ≤ 1 + φ := by linarith [hφnn]
    calc (DaCard P.X P.H a D : ℝ)
        ≤ C₂ * (Ra.card : ℝ) * (1 + φ) := by
          rw [hφdef, StripAux.fiberφ_def]; exact hRaCard
      _ ≤ C₂ * (C₁ * S.R + 1) * (1 + φ) := by
          apply mul_le_mul_of_nonneg_right _ h1φ
          exact mul_le_mul_of_nonneg_left hRacard hC₂.le
  -- DBlock ≤ #Icc · M
  have hsum : DBlock P S D ≤ (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card • M := by
    unfold DBlock
    exact Finset.sum_le_card_nsmul _ _ _ hper
  -- #Icc ≤ A + 1
  have hcardR : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) ≤ S.A + 1 := by
    have h1 : (⌊2 * S.A⌋ : ℝ) ≤ 2 * S.A := Int.floor_le _
    have h2 : S.A ≤ (⌈S.A⌉ : ℝ) := Int.le_ceil _
    by_cases hle : ⌈S.A⌉ ≤ ⌊2 * S.A⌋ + 1
    · have hz := Int.card_Icc_of_le ⌈S.A⌉ ⌊2 * S.A⌋ hle
      have hcr : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) = (⌊2 * S.A⌋ : ℝ) + 1 - (⌈S.A⌉ : ℝ) := by
        have : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) = ((⌊2 * S.A⌋ + 1 - ⌈S.A⌉ : ℤ) : ℝ) := by
          exact_mod_cast hz
        rw [this]; push_cast; ring
      rw [hcr]; linarith [h1, h2]
    · have hempty : Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋ = ∅ := by
        rw [Finset.Icc_eq_empty]; omega
      rw [hempty]; simp; linarith [hApos]
  have hDle : DBlock P S D ≤ (S.A + 1) * M := by
    have hnsmul : (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card • M
        = ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) * M := by
      rw [nsmul_eq_mul]
    rw [hnsmul] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_right hcardR hMnn)
  -- expand (A+1)·M = C₂·[8 monomials], bound each
  have hbody : (S.A + 1) * M
      ≤ C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
        + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
        + (64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by
    -- the eight per-term bounds (φ = StripAux.fiberφ P S)
    have hφeq : φ = StripAux.fiberφ P S := hφdef
    have t1 := StripAux.term1_le P S c₀ C₁ hC₁ hc₀ hX hu0 hband
    have t2 := StripAux.term2_le P S c₀ C₁ hC₁ hc₀ hX hband
    have t3 := StripAux.term3_le P S c₀ hc₀ hX hu0 hΔ1 hNR hband
    have t4 := StripAux.term4_le P S c₀ hc₀ hX hΔ1 hNR hband
    have t5 := StripAux.term5_le P S c₀ C₁ hC₁ hc₀ hX hg hu0 hΔlong hband
    have t6 := StripAux.term6_le P S c₀ C₁ hC₁ hc₀ hX hg hu0 hu' hΔlong hband
    have t7 := StripAux.term7_le P hX hg hu'
    have t8 := StripAux.term8_le P S hX hg hu' hΔ1 hNR
    rw [← hφeq] at t2 t4 t6 t8
    -- (A+1)·M = C₂·(t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8)
    have hexpand : (S.A + 1) * M
        = C₂ * (S.A * (C₁ * S.R) + S.A * (C₁ * S.R) * φ + S.A + S.A * φ
          + C₁ * S.R + C₁ * S.R * φ + 1 + φ) := by
      rw [hMdef]; ring
    rw [hexpand, show C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
        + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
        + (64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U)
        = C₂ * ((C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
          + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
          + (64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U)) by ring]
    apply mul_le_mul_of_nonneg_left _ hC₂.le
    -- sum the eight bounds (all RHS share factor (H/U)); collect
    have hsum8 : S.A * (C₁ * S.R) + S.A * (C₁ * S.R) * φ + S.A + S.A * φ
          + C₁ * S.R + C₁ * S.R * φ + 1 + φ
        ≤ (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
          + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
          + (64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by
      have hrhs : (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
          + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
          + (64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U)
          = (C₁ * c₀ ^ (4:ℝ)) * (P.H / P.U) + (C₁ * c₀ ^ (4/3:ℝ)) * (P.H / P.U)
            + (c₀ ^ (4:ℝ) / 64 ^ 3) * (P.H / P.U) + (c₀ ^ (4/3:ℝ) / 64 ^ 3) * (P.H / P.U)
            + (C₁ * c₀ ^ (3:ℝ)) * (P.H / P.U) + (C₁ * c₀ ^ (1/3:ℝ)) * (P.H / P.U)
            + (1:ℝ) * (P.H / P.U) + ((64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by ring
      rw [hrhs]
      linarith [t1, t2, t3, t4, t5, t6, t7, t8]
    exact hsum8
  -- chain and rewrite C * H / U = C * (H/U)
  have hfin : DBlock P S D
      ≤ C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / 64 ^ 3
        + c₀ ^ (4/3:ℝ) / 64 ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
        + (64:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := hDle.trans hbody
  -- C * P.H / P.U = C * (P.H / P.U)
  rw [mul_div_assoc]
  exact hfin

end Squarefree
