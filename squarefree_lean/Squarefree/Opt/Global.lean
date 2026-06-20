import Squarefree.Opt.Strip
import Squarefree.Opt.OnStripAux
import Squarefree.Opt.OnStripEnvelope
import Squarefree.Bracket.BoxSum

/-!
# §9 on-strip case + the merged per-Ω block bound

`dblock_on_strip` is the §9 core (writeup 2083–2221): on the unresolved strip,
`𝐃(Ω) ≪ H/U` via Prop 7.3 with `W = W_{≠0}` (the largest admissible envelope, = the `e14`
monomial `H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}`) and the optimization `18187g+15315u<2` (the `e14`
constraint is the unique binding one: `840·(9.3) = 18187g+15315u−2`). It needs the full
`prop_3_2` (carrying `dStar`/`inDa`, gated by a `dtil = R_a⁻¹` right-inverse on the band).

`dblock_bound` is the merger: it picks shared `u, C, c₀, Cu`, splits on `S.x` against the strip
edges, and dispatches to `dblock_off_strip` (`Opt/Strip.lean`) / `dblock_on_strip`.
-/

open Classical Finset

namespace Squarefree

/-- Explicit on-strip block constant: `prop32fiberD_C2 · (C_prop73 · 10²⁵ · 4·(1+c₀^{-8/3}))`,
where `prop32fiberD_C2` is the Prop 3.2 fiber constant and `C_prop73` the Prop 7.3 constant. -/
noncomputable def dblockOnStrip_C (c₀ : ℝ) : ℝ :=
  prop32fiberD_C2 * (C_prop73 * 10 ^ 25 * (4 * (1 + c₀ ^ (-8/3 : ℝ))))

/-- Explicit-constant form of `dblock_on_strip` (§9 core, writeup 2083–2221): the on-strip block
constant is `dblockOnStrip_C c₀`. Math is the original `dblock_on_strip` body; only the witnessed
constant is surfaced. -/
theorem dblock_on_strip_explicit (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18187)
    (u : ℝ) (hu0 : 0 < u) (hopt : 18187 * g + 15315 * u < 2) (hu2 : u ≤ 1 / 100)
    (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (Cu : ℝ) (hCu : 1 ≤ Cu)
    (hubudget : 18187 * g + (18675 + 790 * Cu) * u ≤ 2) :
    0 < dblockOnStrip_C c₀ ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
        Real.log P.X ≤ P.X ^ P.u →
        (10:ℝ) ^ 33 ≤ P.U →
        (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)) ≤ S.x →
        S.x ≤ P.G ^ 16 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) →
        ∀ D : ℝ, 0 < D → D = S.D → DBlock P S D ≤ dblockOnStrip_C c₀ * P.H / P.U := by
  obtain ⟨hc₁', hC₁', hC₂', hfiber'⟩ := prop_3_2_fiber_dStar_explicit
  set C₂' := prop32fiberD_C2 with hC2'def
  clear_value C₂'
  have hp73 := prop_7_3_explicit
  set C₇ : ℝ := C_prop73 with hC₇def
  have hC₇ : 0 < C₇ := by
    rw [hC₇def]; unfold C_prop73
    have h1 := sec7_cJ_pos
    have h2 : (0 : ℝ) < C_prop71 := by unfold C_prop71; exact sec7_cCubeIn_pos
    positivity
  clear_value C₇
  -- output constant (the 10²⁵ absorbs `W = 10⁻²⁵·Wnz` in Prop 7.3's `R/W` denominator)
  have hCeq : dblockOnStrip_C c₀ = C₂' * (C₇ * 10 ^ 25 * (4 * (1 + c₀ ^ (-8/3 : ℝ)))) := by
    unfold dblockOnStrip_C; rw [hC2'def, hC₇def]
  rw [hCeq]
  refine ⟨?_, ?_⟩
  · have := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-8/3 : ℝ)
    positivity
  intro P hg hu hX S hΔlong hX0big hlog hUbig hNR hAD hbandlo hΩU hxlo hxhi D hDpos hDeq
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hH := P.H_pos; have hU := P.U_pos
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hc₀0 : 0 < c₀ := lt_of_lt_of_le one_pos hc₀
  have hg0' : 0 ≤ P.g := by rw [hg]; exact hg0.le
  have hPu : 0 < P.u := by rw [hu]; exact hu0
  have hG1 : 1 ≤ P.G := Real.one_le_rpow hX hg0'
  have hΔ1 : (1:ℝ) ≤ S.Δ := le_trans (Real.one_le_rpow hX (by norm_num)) hΔlong
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  -- derive 1 < P.X from the `X^{1/100} ≥ 16777216` floor
  have hXgt : 1 < P.X := by
    -- X^{1/100} ≥ 16777216 > 1 = 1^{1/100}, and t ↦ t^{1/100} is monotone, so X > 1
    by_contra hle
    push Not at hle  -- hle : P.X ≤ 1
    have hX1 : P.X = 1 := le_antisymm hle hX
    have : P.X ^ (1/100 : ℝ) = 1 := by rw [hX1, Real.one_rpow]
    rw [this] at hX0big
    linarith [hX0big]
  -- StripData
  have SD : OnStripAux.StripData P S c₀ Cu :=
    { hX := hX, hc₀ := hc₀, hCu := hCu, hxlo := hxlo, hxhi := hxhi, hΩlo := hbandlo, hΩhi := hΩU }
  -- admissibility envelope at Wnz
  have hgP : P.g = g := hg
  have hbudP : OnStripAux.Budget P.g P.u Cu := by
    show 18187 * P.g + (18675 + 790 * Cu) * P.u ≤ 2
    rw [hg, hu]; exact hubudget
  have hEnv : Sec7Envelope P S
      ((10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * OnStripAux.Wnz P S) :=
    OnStripAux.sec7Envelope_Wnz P S c₀ Cu SD hXgt hg0' hPu.le hbudP hX0big hlog
  have hX2upos : (0:ℝ) < P.X ^ (2 * P.u) := Real.rpow_pos_of_pos hX0 _
  have hAD10 : 10 * S.A ≤ S.D := by
    have hexp : (1/100 : ℝ) ≤ (1 - P.g) / 5 - P.u := by
      rw [hg, hu]
      linarith only [hg1, hu2]
    have hXpow10 : (10 : ℝ) ≤ P.X ^ (1/100 : ℝ) := by
      linarith [hX0big]
    have hXpow_le : P.X ^ (1/100 : ℝ) ≤ P.X ^ ((1 - P.g) / 5 - P.u) :=
      Real.rpow_le_rpow_of_exponent_le hX hexp
    have hratio : P.H / P.U = P.X ^ ((1 - P.g) / 5 - P.u) := by
      rw [Globals.H, Globals.U, Real.rpow_sub P.X_pos]
    have hHU : 10 * P.U ≤ P.H := by
      have h10 : (10 : ℝ) ≤ P.H / P.U := by
        rw [hratio]
        exact le_trans hXpow10 hXpow_le
      exact (le_div_iff₀ P.U_pos).mp h10
    have hΩH : 10 * S.Ω ≤ P.H := by
      exact le_trans (mul_le_mul_of_nonneg_left hΩU (by norm_num : (0:ℝ) ≤ 10)) hHU
    rw [show S.A = S.Δ * S.Ω from rfl, show S.D = P.H * S.Δ from rfl]
    nlinarith only [S.Δ_pos, hΩH]
  -- per-a bound:  DaCard ≤ C₂'·(C₇·10²⁵)·(1+φ)·(1+H/A²)·(X^{2u}·R/Wnz)
  set M : ℝ := C₂' * (C₇ * 10 ^ 25 * ((1 + StripAux.fiberφ P S)
      * ((1 + P.H / S.A ^ 2)
        * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S))))) with hMdef
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
    have hloq : (1/4:ℝ) * S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) ≤ (a:ℝ) := by
      refine le_trans ?_ (le_trans hNR hAa)
      have hthr : (0:ℝ) ≤ S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) :=
        mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (by positivity) _)
      nlinarith only [hthr]
    obtain ⟨Ra, _dStar, _hinDa, _hband, _hnear, hwit, hDaC⟩ :=
      hfiber' P S a ha0 hΔlong hX0big hloq hAa ha2A hAD D hDpos hDeq
    have h73raw := hp73 P S a ha0 hAD10 hG1 hAa ha2A
      ((10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * OnStripAux.Wnz P S) hEnv
      c₀ Cu SD hbudP hg0' hPu hX0big hUbig hlog Ra hwit
    have h73 : (Ra.card : ℝ)
        ≤ C₇ * 10 ^ 25 * ((1 + P.H / S.A ^ 2)
            * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S))) := by
      refine le_trans h73raw (le_of_eq ?_)
      rw [show S.R / ((10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * OnStripAux.Wnz P S)
            = 10 ^ 25 * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S)) by
          rw [show ((10:ℝ) ^ (-25 : ℤ)) = ((10:ℝ) ^ 25)⁻¹ by norm_num,
              show P.X ^ (-(2:ℝ) * P.u) = (P.X ^ (2 * P.u))⁻¹ by
                rw [← Real.rpow_neg hX0.le]; congr 1; ring]
          field_simp [hWnzpos.ne', hX2upos.ne']]
      ring
    -- DaCard ≤ C₂'·#Ra·(1+φ) ≤ C₂'·[C₇·(1+H/A²)·(R/Wnz)]·(1+φ)
    have hφeq : (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)) = 1 + StripAux.fiberφ P S := by
      rw [StripAux.fiberφ_def]
    rw [hMdef]
    calc (DaCard P.X P.H a D : ℝ)
        ≤ C₂' * (Ra.card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ)) := hDaC
      _ = C₂' * ((1 + StripAux.fiberφ P S) * (Ra.card : ℝ)) := by rw [hφeq]; ring
      _ ≤ C₂' * ((1 + StripAux.fiberφ P S) * (C₇ * 10 ^ 25
            * ((1 + P.H / S.A ^ 2)
              * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S))))) := by
          apply mul_le_mul_of_nonneg_left _ hC₂'.le
          exact mul_le_mul_of_nonneg_left h73 (by linarith [hφnn])
      _ = C₂' * (C₇ * 10 ^ 25 * ((1 + StripAux.fiberφ P S)
            * ((1 + P.H / S.A ^ 2)
              * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S))))) := by ring
  -- sum: DBlock ≤ #Icc · M ≤ (A+1)·M
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ (1 + P.H / S.A ^ 2)
        * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S)) := by positivity
    have h2 : 0 ≤ (1 + StripAux.fiberφ P S) * ((1 + P.H / S.A ^ 2)
        * (P.X ^ (2 * P.u) * (S.R / OnStripAux.Wnz P S))) :=
      mul_nonneg (by linarith [hφnn]) h1
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
    _ = C₂' * (C₇ * 10 ^ 25 * (P.X ^ (2 * P.u) * ((S.A + 1) * (1 + StripAux.fiberφ P S)
          * ((1 + P.H / S.A ^ 2) * (S.R / OnStripAux.Wnz P S))))) := by rw [hMdef]; ring
    _ ≤ C₂' * (C₇ * 10 ^ 25 * ((4 * (1 + c₀ ^ (-8/3 : ℝ))) * (P.H / P.U))) := by
        apply mul_le_mul_of_nonneg_left _ hC₂'.le
        exact mul_le_mul_of_nonneg_left hclose (by positivity)
    _ = C₂' * (C₇ * 10 ^ 25 * (4 * (1 + c₀ ^ (-8/3 : ℝ)))) * (P.H / P.U) := by ring

/-- **On-strip case** of `dblock_bound` (§9 core, writeup 2083–2221). Shared params `u, c₀, Cu`.
On the strip `G^{-2}Ω^{-11/2}X^{-Cu·u} ≤ x ≤ G^{17}Ω^{-26}X^{Cu·u}`, `𝐃(Ω) ≪ H/U` via Prop 7.3 with
`W = W_{≠0}` and `18187g+15315u<2`. Added hypothesis `hubudget : 18187g+(18675+790·Cu)u ≤ 2`
(the writeup's "shrink `u`"): the **sharp** `g`-coefficient `18187` keeps the full range
`g < 2/18187`, while all `X^{O(u)}` bookkeeping (`2u` fiber, the AM-7 `X^{-2u}` envelope
deflation, Prop 7.3's `X^{O(u)}`, strip-edge `X^{±Cu·u}`) sits in the `u`-coefficient
`18675+790·Cu`.  Implies `hopt` and the on-strip envelope/closing budgets; for any
`g < 2/18187`, `u := (2 − 18187g)/(2(18675+790·Cu)) > 0` satisfies it (the budget value is
then `(2 + 18187g)/2 < 2`).  AM-8: threads `hlog : log X ≤ X^u` to Prop 7.3's pack. -/
theorem dblock_on_strip (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18187)
    (u : ℝ) (hu0 : 0 < u) (hopt : 18187 * g + 15315 * u < 2) (hu2 : u ≤ 1 / 100)
    (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (Cu : ℝ) (hCu : 1 ≤ Cu)
    (hubudget : 18187 * g + (18675 + 790 * Cu) * u ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
        Real.log P.X ≤ P.X ^ P.u →
        (10:ℝ) ^ 33 ≤ P.U →
        (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)) ≤ S.x →
        S.x ≤ P.G ^ 16 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) →
        ∀ D : ℝ, 0 < D → D = S.D → DBlock P S D ≤ C * P.H / P.U :=
  ⟨dblockOnStrip_C c₀,
    (dblock_on_strip_explicit g hg0 hg1 u hu0 hopt hu2 c₀ hc₀ Cu hCu hubudget).1,
    (dblock_on_strip_explicit g hg0 hg1 u hu0 hopt hu2 c₀ hc₀ Cu hCu hubudget).2⟩

/-- Explicit `u` witness for `dblock_bound`: half of the min of the three `u`-constraint
thresholds (off-strip budget, on-strip budget, `u ≤ 1/100`), with `Cu = (3/2)·C6 + 232`. -/
noncomputable def dblockBound_u (g : ℝ) : ℝ :=
  min ((1/200 - 20 * g) / (StripAux.C6 + 100))
      (min ((2 - 18187 * g) / (18675 + 790 * ((3/2) * StripAux.C6 + 232))) (1/100)) / 2

/-- Explicit `C` witness for `dblock_bound`: `max` of the off/on-strip block constants at `c₀ = 1`. -/
noncomputable def dblockBound_C (_g : ℝ) : ℝ :=
  max (dblockOffStrip_C 1) (dblockOnStrip_C 1)

/-- Explicit `c₀` witness for `dblock_bound`. -/
noncomputable def dblockBound_c0 : ℝ := 1

/-- Explicit-constant form of `dblock_bound`: surfaces the witnesses `dblockBound_u`,
`dblockBound_C`, `dblockBound_c0`.  Math is the original `dblock_bound` body. -/
theorem dblock_bound_explicit (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18187) :
    0 < dblockBound_u g ∧ 18187 * g + 15315 * (dblockBound_u g) < 2 ∧
      0 < dblockBound_C g ∧ 0 < dblockBound_c0 ∧
      ∀ (P : Globals), P.g = g → P.u = dblockBound_u g → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
        Real.log P.X ≤ P.X ^ P.u →
        (10:ℝ) ^ 33 ≤ P.U →
        (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        dblockBound_c0 * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ dblockBound_C g * P.H / P.U := by
  -- shared constants
  have hC6 := StripAux.C6_pos
  set C6 : ℝ := StripAux.C6 with hC6def
  set Cu : ℝ := (3/2) * C6 + 232 with hCudef
  have hCu_off : (3/2) * StripAux.C6 + 232 ≤ Cu := by rw [hCudef, hC6def]
  have hCu_on : (1:ℝ) ≤ Cu := by rw [hCudef]; linarith only [hC6]
  -- positivity of the denominators / numerators in the witness
  have hden1 : (0:ℝ) < C6 + 100 := by linarith
  have hden2 : (0:ℝ) < 18675 + 790 * Cu := by linarith only [hCu_on]
  have hg1' : g < 1 / 4000 := by linarith [hg1]
  have hnum1 : (0:ℝ) < 1/200 - 20 * g := by linarith [hg1']
  have hnum2 : (0:ℝ) < 2 - 18187 * g := by linarith only [hg1]
  -- u witness: half of the min of the three constraints' thresholds
  set u : ℝ := min ((1/200 - 20 * g) / (C6 + 100))
      (min ((2 - 18187 * g) / (18675 + 790 * Cu)) (1/100)) / 2 with hudef
  have hm1 : (0:ℝ) < (1/200 - 20 * g) / (C6 + 100) := div_pos hnum1 hden1
  have hm2 : (0:ℝ) < (2 - 18187 * g) / (18675 + 790 * Cu) := div_pos hnum2 hden2
  have hm3 : (0:ℝ) < (1:ℝ)/100 := by norm_num
  have hminpos : (0:ℝ) < min ((1/200 - 20 * g) / (C6 + 100))
      (min ((2 - 18187 * g) / (18675 + 790 * Cu)) (1/100)) := lt_min hm1 (lt_min hm2 hm3)
  have hu0 : 0 < u := by rw [hudef]; linarith [hminpos]
  -- u ≤ each threshold (half of min ≤ min ≤ each arg)
  have hule_min : u ≤ min ((1/200 - 20 * g) / (C6 + 100))
      (min ((2 - 18187 * g) / (18675 + 790 * Cu)) (1/100)) := by
    rw [hudef]; linarith [hminpos]
  have hu_off : u ≤ (1/200 - 20 * g) / (C6 + 100) :=
    le_trans hule_min (min_le_left _ _)
  have hu_on : u ≤ (2 - 18187 * g) / (18675 + 790 * Cu) :=
    le_trans hule_min (le_trans (min_le_right _ _) (min_le_left _ _))
  have hu2 : u ≤ 1 / 100 :=
    le_trans hule_min (le_trans (min_le_right _ _) (min_le_right _ _))
  -- off budget: (C6+100)·u ≤ 1/200 - 20g
  have hubud_off : (StripAux.C6 + 100) * u ≤ 1/200 - 20 * g := by
    rw [← hC6def]
    have := (le_div_iff₀ hden1).mp hu_off
    linarith [this]
  -- on budget: 18187g + (18675+790Cu)·u ≤ 2
  have hubud_on : 18187 * g + (18675 + 790 * Cu) * u ≤ 2 := by
    have := (le_div_iff₀ hden2).mp hu_on
    linarith only [this]
  -- goal opt: 18187g + 15315u < 2  (strict, via 15315 < 18675+790Cu and u>0)
  have hopt : 18187 * g + 15315 * u < 2 := by
    have hcoef : 15315 * u < (18675 + 790 * Cu) * u := by
      apply mul_lt_mul_of_pos_right _ hu0
      linarith only [hCu_on]
    linarith [hubud_on, hcoef]
  -- bridge the witness defs to the local `u` / `max` value
  have hbridge_u : dblockBound_u g = u := by
    unfold dblockBound_u; rw [hudef, hCudef, hC6def]
  -- instantiate the two halves (explicit constants)
  have hoffpair := dblock_off_strip_explicit g hg0 hg1 u hu0 hopt hu2 1 le_rfl Cu hCu_off hubud_off
  have honpair := dblock_on_strip_explicit g hg0 hg1 u hu0 hopt hu2 1 le_rfl Cu hCu_on hubud_on
  set Coff := dblockOffStrip_C 1 with hCoffdef
  set Con := dblockOnStrip_C 1 with hCondef
  obtain ⟨hCoff, hoff⟩ := hoffpair
  obtain ⟨hCon, hon⟩ := honpair
  have hCbridge : dblockBound_C g = max Coff Con := by
    unfold dblockBound_C; rw [← hCoffdef, ← hCondef]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hbridge_u]; exact hu0
  · rw [hbridge_u]; exact hopt
  · rw [hCbridge]; exact lt_max_of_lt_left hCoff
  · unfold dblockBound_c0; exact one_pos
  · rw [hbridge_u, hCbridge]
    intro P hPg hPu hX S hΔ hX0big hlog hUbig hNR hAD hband hΩU D hDpos hDeq
    simp only [dblockBound_c0] at hband
    have hH := P.H_pos; have hU := P.U_pos
    have hHU : (0:ℝ) ≤ P.H / P.U := by positivity
    -- trichotomy on S.x
    by_cases h1 : S.x ≤ P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))
    · have := hoff P hPg hPu hX S hΔ hX0big hlog hUbig hNR hAD hband hΩU (Or.inl h1) D hDpos hDeq
      calc DBlock P S D ≤ Coff * P.H / P.U := this
        _ ≤ max Coff Con * P.H / P.U := by
            rw [mul_div_assoc, mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) hHU
    · by_cases h2 : P.G ^ 16 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) ≤ S.x
      · have := hoff P hPg hPu hX S hΔ hX0big hlog hUbig hNR hAD hband hΩU (Or.inr h2) D hDpos hDeq
        calc DBlock P S D ≤ Coff * P.H / P.U := this
          _ ≤ max Coff Con * P.H / P.U := by
              rw [mul_div_assoc, mul_div_assoc]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) hHU
      · push Not at h1 h2
        have := hon P hPg hPu hX S hΔ hX0big hlog hUbig hNR hAD hband hΩU h1.le h2.le D hDpos hDeq
        calc DBlock P S D ≤ Con * P.H / P.U := this
          _ ≤ max Coff Con * P.H / P.U := by
              rw [mul_div_assoc, mul_div_assoc]
              exact mul_le_mul_of_nonneg_right (le_max_right _ _) hHU

/-- **§8/§9 per-Ω block bound** (merger). For `Ω` in the band `[c₀·G^{-1/4}U^{-3/4}, U]`,
`𝐃(Ω) ≪ H/U`. Picks shared `u, C, c₀, Cu`, splits `S.x` against the strip edges, and dispatches to
`dblock_off_strip` / `dblock_on_strip`. The regime hypotheses `(1/4)·Δ^{4/3}(H⁴/X)^{1/3} ≤ A`,
`2A ≤ D` are supplied by `a_decomposition`'s sum range. -/
theorem dblock_bound (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18187) :
    ∃ u : ℝ, 0 < u ∧ 18187 * g + 15315 * u < 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
        Real.log P.X ≤ P.X ^ P.u →
        (10:ℝ) ^ 33 ≤ P.U →
        (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω →
        S.Ω ≤ P.U →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dblock_bound_explicit g hg0 hg1
  exact ⟨dblockBound_u g, h1, h2, dblockBound_C g, h3, dblockBound_c0, h4, h5⟩

end Squarefree
