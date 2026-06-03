import Squarefree.Opt.Strip
import Squarefree.Opt.OnStripAux

/-!
# §9 on-strip case + the merged per-Ω block bound

`dblock_on_strip` is the §9 core (writeup 2083–2221): on the unresolved strip,
`𝐃(Ω) ≪ H/U` via Prop 7.3 with `W = W_{≠0}` (the largest admissible envelope, = the `e14`
monomial `H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}`) and the optimization `18977g+15315u<2` (the `e14`
constraint is the unique binding one: `840·(9.3) = 18977g+15315u−2`). It needs the full
`prop_3_2` (carrying `dStar`/`inDa`, gated by a `dtil = R_a⁻¹` right-inverse on the band).

`dblock_bound` is the merger: it picks shared `u, C, c₀, Cu`, splits on `S.x` against the strip
edges, and dispatches to `dblock_off_strip` (`Opt/Strip.lean`) / `dblock_on_strip`.
-/

open Classical Finset

namespace Squarefree

set_option maxHeartbeats 1600000 in
/-- **On-strip case** of `dblock_bound` (§9 core, writeup 2083–2221). Shared params `u, c₀, Cu`.
On the strip `G^{-2}Ω^{-11/2}X^{-Cu·u} ≤ x ≤ G^{17}Ω^{-26}X^{Cu·u}`, `𝐃(Ω) ≪ H/U` via Prop 7.3 with
`W = W_{≠0}` and `18977g+15315u<2`. Added hypothesis `hubudget : 18977g+(16995+790·Cu)u ≤ 2`
(the writeup's "shrink `u`"): the **sharp** `g`-coefficient `18977` keeps the full range
`g < 2/18977`, while all `X^{O(u)}` bookkeeping (`2u` fiber, Prop 7.3's `X^{O(u)}`, strip-edge
`X^{±Cu·u}`) sits in the `u`-coefficient `16995+790·Cu`.  Implies `hopt` and the on-strip
envelope/closing budgets; for any `g < 2/18977`, `u := (2 − 18977g)/(2(16995+790·Cu)) > 0`
satisfies it (the budget value is then `(2 + 18977g)/2 < 2`). -/
theorem dblock_on_strip (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18977)
    (u : ℝ) (hu0 : 0 < u) (hopt : 18977 * g + 15315 * u < 2) (hu2 : u ≤ 1 / 100)
    (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (Cu : ℝ) (hCu : 1 ≤ Cu)
    (hubudget : 18977 * g + (16995 + 790 * Cu) * u ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (64 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)) ≤ S.x →
        S.x ≤ P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) →
        ∀ D : ℝ, 0 < D → D = S.D → DBlock P S D ≤ C * P.H / P.U := by
  obtain ⟨c₁', C₁', C₂', hc₁', hC₁', hC₂', hfiber'⟩ := prop_3_2_fiber_dStar
  obtain ⟨C₇, hC₇, hp73⟩ := prop_7_3
  -- output constant
  refine ⟨C₂' * (C₇ * (4 * (1 + c₀ ^ (-8/3 : ℝ)))), ?_, ?_⟩
  · have := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-8/3 : ℝ)
    positivity
  intro P hg hu hX S hΔlong hNR hAD hbandlo hΩU hxlo hxhi D hDpos hDeq
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hH := P.H_pos; have hU := P.U_pos
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hc₀0 : 0 < c₀ := lt_of_lt_of_le one_pos hc₀
  have hg0' : 0 ≤ P.g := by rw [hg]; exact hg0.le
  have hPu : 0 < P.u := by rw [hu]; exact hu0
  have hΔ1 : (1:ℝ) ≤ S.Δ := le_trans (Real.one_le_rpow hX (by norm_num)) hΔlong
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  -- derive 1 < P.X from the regime  (128³·Δ·H ≤ X)
  have hXgt : 1 < P.X := by
    -- 128 Δ^{4/3}(H⁴/X)^{1/3} ≤ 2A ≤ D = HΔ  ⟹ cube ⟹ 128³ Δ H ≤ X
    have hH1 : (1:ℝ) ≤ P.H := by
      rw [Globals.H]; exact Real.one_le_rpow hX (by rw [hg]; linarith [hg1])
    have hcube := StripAux.delta_ceiling P S hΔ1 hNR  -- Δ ≤ Ω³X/(64³H⁴)
    -- alternatively use threshold + 2A ≤ D
    have h128 : (128:ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.D := by
      have : (128:ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)
          = 2 * ((64:ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) := by ring
      rw [this]; linarith [hNR, hAD]
    have hDval : S.D = P.H * S.Δ := rfl
    -- cube both sides:  128³ Δ⁴ H⁴/X ≤ H³Δ³
    have hLcube : ((128:ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ 3
        = (128:ℝ) ^ 3 * S.Δ ^ 4 * (P.H ^ 4 / P.X) := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (S.Δ ^ (4/3:ℝ)) 3, ← Real.rpow_mul hΔ.le,
          ← Real.rpow_natCast ((P.H ^ 4 / P.X) ^ (1/3:ℝ)) 3, ← Real.rpow_mul (by positivity)]
      rw [show (4:ℝ)/3 * (3:ℕ) = (4:ℕ) by push_cast; ring, Real.rpow_natCast,
          show (1:ℝ)/3 * (3:ℕ) = (1:ℕ) by push_cast; ring, Real.rpow_natCast]; ring
    have hmono : ((128:ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ)) ^ 3 ≤ S.D ^ 3 :=
      pow_le_pow_left₀ (by positivity) h128 3
    rw [hLcube, hDval] at hmono
    -- 128³ Δ⁴ H⁴/X ≤ H³Δ³  ⟹  X ≥ 128³ Δ H ≥ 128³
    have hX' : (128:ℝ) ^ 3 * S.Δ ^ 4 * P.H ^ 4 ≤ (P.H * S.Δ) ^ 3 * P.X := by
      have e : (128:ℝ) ^ 3 * S.Δ ^ 4 * (P.H ^ 4 / P.X) * P.X = 128 ^ 3 * S.Δ ^ 4 * P.H ^ 4 := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hmono hX0.le, e]
    have hge : (128:ℝ) ^ 3 ≤ P.X := by
      have hΔ3H3 : (0:ℝ) < S.Δ ^ 3 * P.H ^ 3 := by positivity
      -- hX' : 128³ Δ⁴ H⁴ ≤ (H Δ)³ X = (Δ³H³)·X ;  LHS = (Δ³H³)·(128³ Δ H)
      have hfac : (128:ℝ) ^ 3 * S.Δ ^ 4 * P.H ^ 4 = (S.Δ ^ 3 * P.H ^ 3) * (128 ^ 3 * S.Δ * P.H) := by
        ring
      have hrhs : (P.H * S.Δ) ^ 3 * P.X = (S.Δ ^ 3 * P.H ^ 3) * P.X := by ring
      rw [hfac, hrhs] at hX'
      have hmul : (128:ℝ) ^ 3 * S.Δ * P.H ≤ P.X := le_of_mul_le_mul_left hX' hΔ3H3
      nlinarith [hmul, hΔ1, hH1]
    nlinarith [hge]
  -- StripData
  have SD : OnStripAux.StripData P S c₀ Cu :=
    { hX := hX, hc₀ := hc₀, hCu := hCu, hxlo := hxlo, hxhi := hxhi, hΩlo := hbandlo, hΩhi := hΩU }
  -- admissibility envelope at Wnz
  have hgP : P.g = g := hg
  have hbudP : OnStripAux.Budget P.g P.u Cu := by
    show 18977 * P.g + (16995 + 790 * Cu) * P.u ≤ 2
    rw [hg, hu]; exact hubudget
  have hAdm : AdmissibleW P S (OnStripAux.Wnz P S) :=
    OnStripAux.admissibleW_Wnz P S c₀ Cu SD hXgt hg0' hPu.le hbudP
  -- per-a bound:  DaCard ≤ C₂'·C₇·(1+φ)·(1+H/A²)·(R/Wnz)
  set M : ℝ := C₂' * (C₇ * ((1 + StripAux.fiberφ P S)
      * ((1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S)))) with hMdef
  have hWnzpos := OnStripAux.Wnz_pos P S
  have hRpos : (0:ℝ) < S.R := by unfold Scale.R; positivity
  have hφnn : (0:ℝ) ≤ StripAux.fiberφ P S := by
    rw [StripAux.fiberφ_def]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hG.le _)
  have hper : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (DaCard P.X P.H a D : ℝ) ≤ M := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨haL, haR⟩ := ha
    have hAa : S.A ≤ (a:ℝ) := le_trans (Int.le_ceil S.A) (by exact_mod_cast haL)
    have ha2A : (a:ℝ) ≤ 2 * S.A := le_trans (by exact_mod_cast haR) (Int.floor_le (2 * S.A))
    have ha0 : 0 < a := by
      have : (0:ℤ) < ⌈S.A⌉ := Int.ceil_pos.mpr hApos; omega
    obtain ⟨Ra, dStar, hinDa, _hband, hDaC⟩ :=
      hfiber' P S a ha0 hΔ1 (le_trans hNR hAa) hAa ha2A hAD D hDpos hDeq
    have h73 := hp73 P S a ha0 (OnStripAux.Wnz P S) hAdm Ra dStar hinDa
    -- DaCard ≤ C₂'·#Ra·(1+φ) ≤ C₂'·[C₇·(1+H/A²)·(R/Wnz)]·(1+φ)
    have hφeq : (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)) = 1 + StripAux.fiberφ P S := by
      rw [StripAux.fiberφ_def]
    rw [hMdef]
    calc (DaCard P.X P.H a D : ℝ)
        ≤ C₂' * (Ra.card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)) := hDaC
      _ = C₂' * ((1 + StripAux.fiberφ P S) * (Ra.card : ℝ)) := by rw [hφeq]; ring
      _ ≤ C₂' * ((1 + StripAux.fiberφ P S) * (C₇ * ((1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S)))) := by
          apply mul_le_mul_of_nonneg_left _ hC₂'.le
          exact mul_le_mul_of_nonneg_left h73 (by linarith [hφnn])
      _ = C₂' * (C₇ * ((1 + StripAux.fiberφ P S)
            * ((1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S)))) := by ring
  -- sum: DBlock ≤ #Icc · M ≤ (A+1)·M
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    have : 0 ≤ (1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S) := by positivity
    have : 0 ≤ (1 + StripAux.fiberφ P S) * ((1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S)) := by
      apply mul_nonneg (by linarith [hφnn]) this
    positivity
  have hSM : DBlock P S D ≤ (S.A + 1) * M := by
    have hsum : DBlock P S D ≤ (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card • M := by
      rw [DBlock]; exact Finset.sum_le_card_nsmul _ _ _ hper
    have hcardR : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) ≤ S.A + 1 := by
      by_cases hle : ⌈S.A⌉ ≤ ⌊2 * S.A⌋ + 1
      · have hz := Int.card_Icc_of_le ⌈S.A⌉ ⌊2 * S.A⌋ hle
        have hcr : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ)
            = (⌊2 * S.A⌋ : ℝ) + 1 - (⌈S.A⌉ : ℝ) := by
          have : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) = ((⌊2 * S.A⌋ + 1 - ⌈S.A⌉ : ℤ) : ℝ) := by
            exact_mod_cast hz
          rw [this]; push_cast; ring
        rw [hcr]; linarith [Int.floor_le (2 * S.A), Int.le_ceil S.A]
      · have hempty : Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋ = ∅ := by rw [Finset.Icc_eq_empty]; omega
        rw [hempty]; simp; linarith [hApos]
    calc DBlock P S D ≤ (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card • M := hsum
      _ = ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) * M := by rw [nsmul_eq_mul]
      _ ≤ (S.A + 1) * M := mul_le_mul_of_nonneg_right hcardR hMnn
  -- closing LP
  have hclose := OnStripAux.closing_bound P S c₀ Cu SD hg0' hPu (by rw [hg, hu]; exact hubudget)
  -- assemble
  rw [mul_div_assoc]
  calc DBlock P S D ≤ (S.A + 1) * M := hSM
    _ = C₂' * (C₇ * ((S.A + 1) * (1 + StripAux.fiberφ P S)
          * ((1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S)))) := by rw [hMdef]; ring
    _ ≤ C₂' * (C₇ * ((4 * (1 + c₀ ^ (-8/3 : ℝ))) * (P.H / P.U))) := by
        apply mul_le_mul_of_nonneg_left _ hC₂'.le
        exact mul_le_mul_of_nonneg_left hclose hC₇.le
    _ = C₂' * (C₇ * (4 * (1 + c₀ ^ (-8/3 : ℝ)))) * (P.H / P.U) := by ring

/-- **§8/§9 per-Ω block bound** (merger). For `Ω` in the band `[c₀·G^{-1/4}U^{-3/4}, U]`,
`𝐃(Ω) ≪ H/U`. Picks shared `u, C, c₀, Cu`, splits `S.x` against the strip edges, and dispatches to
`dblock_off_strip` / `dblock_on_strip`. The regime hypotheses `64·Δ^{4/3}(H⁴/X)^{1/3} ≤ A`, `2A ≤ D`
are supplied by `a_decomposition`'s sum range. -/
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

end Squarefree
