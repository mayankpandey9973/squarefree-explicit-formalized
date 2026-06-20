import Squarefree.Opt.StripAux
import Squarefree.Opt.StripRegimePack
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §8/§9 per-Ω-scale block bound `𝐃(Ω) ≪ H/U`

The core §5–§9 per-scale result, at the `DBlock` (= `𝐃(Ω) = Σ_{a∼A} #𝒟_a`) level.

The dichotomy is split by `Ω` against `c₀·G^{-1/4}U^{-3/4}` for a fixed absolute `c₀` chosen by
`dblock_bound` (the writeup's `Ω ≫ G^{-1/4}U^{-3/4}` threshold, line 406):
* `dblock_bound`     — `Ω ≥ c₀·G^{-1/4}U^{-3/4}` (the band): the lower edge makes Prop 3.2's
  fiber factor `1+Ω^{-8/3}G^{-2/3} ≤ X^{O(u)}`. Strip dichotomy internal (off-strip Props 5.1/6.1;
  on-strip Prop 7.3 + `18187g+15315u<2`).
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

/-- In the §6 range, `10U ≤ H`: with `H = X^{(1-g)/5}`, `U = X^u`, the exponent gap
`(1-g)/5 - u ≥ 1/100` and `X^{1/100} ≥ 16777216 ≥ 10`. -/
private theorem five_U_le_H (P : Globals) (hX : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ))
    (hg : P.g < 2 / 18187) (hu : P.u ≤ 1 / 100) : 10 * P.U ≤ P.H := by
  have hX0 : 0 < P.X := P.X_pos
  -- X > 1 (else X^{1/100} ≤ 1 < 16777216)
  have hX1 : (1:ℝ) ≤ P.X := by
    by_contra h
    push Not at h
    have hle1 : P.X ^ (1/100 : ℝ) ≤ 1 :=
      Real.rpow_le_one hX0.le h.le (by norm_num : (0:ℝ) ≤ 1/100)
    linarith
  -- exponent gap ≥ 1/100
  have hexp : (1/100 : ℝ) ≤ (1 - P.g) / 5 - P.u := by linarith [hg, hu]
  -- X^{(1-g)/5 - u} ≥ X^{1/100} ≥ 16777216 ≥ 5
  have hmono : P.X ^ (1/100 : ℝ) ≤ P.X ^ ((1 - P.g) / 5 - P.u) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hge5 : (10:ℝ) ≤ P.X ^ ((1 - P.g) / 5 - P.u) := by linarith
  -- H = U · X^{(1-g)/5 - u}
  have hHU : P.H = P.U * P.X ^ ((1 - P.g) / 5 - P.u) := by
    rw [Globals.H, Globals.U, ← Real.rpow_add hX0]
    congr 1; ring
  have hUpos : 0 < P.U := P.U_pos
  calc 10 * P.U = P.U * 10 := by ring
    _ ≤ P.U * P.X ^ ((1 - P.g) / 5 - P.u) := by
        exact mul_le_mul_of_nonneg_left hge5 hUpos.le
    _ = P.H := hHU.symm

/-- The §6 Ω-floor: in the band `Ω ≥ c₀·G^{-1/4}U^{-3/4}` (with `c₀ ≥ 1`), the curvature scale
`G·H·Ω³ ≥ 500`.  `G·H·Ω³ ≥ G·H·e₀³` where `e₀ = c₀·G^{-1/4}U^{-3/4}`, and
`G·H·e₀³ = c₀³·X^{1/5+g/20-9u/4} ≥ X^{71/400} ≥ X^{1/100} ≥ 16777216 ≥ 500`. -/
private theorem ghΩ3_ge_500 (P : Globals) (S : Scale P) (c₀ : ℝ) (hc₀ : 1 ≤ c₀)
    (hX : 1 ≤ P.X) (hg0 : 0 ≤ P.g) (hu2 : P.u ≤ 1/100)
    (hband : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω)
    (hX0big : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) :
    (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 := by
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hH := P.H_pos; have hU := P.U_pos; have hΩ := S.Ω_pos
  have hc₀0 : 0 < c₀ := lt_of_lt_of_le one_pos hc₀
  set e0 : ℝ := c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) with he0def
  have he0pos : 0 < e0 := by
    rw [he0def]
    have := Real.rpow_pos_of_pos hG (-1/4 : ℝ)
    have := Real.rpow_pos_of_pos hU (-3/4 : ℝ); positivity
  -- Ω³ ≥ e0³
  have hΩ3 : e0 ^ 3 ≤ S.Ω ^ 3 := pow_le_pow_left₀ he0pos.le hband 3
  -- e0³ in X-power form
  have he03 : e0 ^ 3 = c₀ ^ 3 * P.X ^ (-3*P.g/4 - 9*P.u/4) := by
    rw [he0def, mul_pow, mul_pow,
        ← Real.rpow_natCast (P.G ^ (-1/4 : ℝ)) 3, ← Real.rpow_natCast (P.U ^ (-3/4 : ℝ)) 3,
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hU.le, Globals.G, Globals.U,
        ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    push_cast
    rw [show P.g * (-1/4 * 3) + P.u * (-3/4 * 3) = -3*P.g/4 - 9*P.u/4 by ring]
  -- G·H in X-power form
  have hGH : P.G * P.H = P.X ^ (P.g + (1 - P.g)/5) := by
    rw [Globals.G, Globals.H, ← Real.rpow_add hX0]
  -- G·H·e0³ = c₀³·X^{1/5+g/20-9u/4}
  have hghe : P.G * P.H * e0 ^ 3 = c₀ ^ 3 * P.X ^ (1/5 + P.g/20 - 9*P.u/4) := by
    rw [hGH, he03,
        show P.X ^ (P.g + (1 - P.g)/5) * (c₀ ^ 3 * P.X ^ (-3*P.g/4 - 9*P.u/4))
            = c₀ ^ 3 * (P.X ^ (P.g + (1 - P.g)/5) * P.X ^ (-3*P.g/4 - 9*P.u/4)) by ring,
        ← Real.rpow_add hX0,
        show P.g + (1 - P.g)/5 + (-3*P.g/4 - 9*P.u/4) = 1/5 + P.g/20 - 9*P.u/4 by ring]
  -- lower bound the X-power: exponent ≥ 1/100
  have hexp : (1/100 : ℝ) ≤ 1/5 + P.g/20 - 9*P.u/4 := by
    have : 9*P.u/4 ≤ 9/400 := by linarith [hu2]
    linarith [hg0]
  have hmono : P.X ^ (1/100 : ℝ) ≤ P.X ^ (1/5 + P.g/20 - 9*P.u/4) :=
    Real.rpow_le_rpow_of_exponent_le hX hexp
  calc (16777216:ℝ) ≤ P.X ^ (1/100 : ℝ) := hX0big
    _ ≤ P.X ^ (1/5 + P.g/20 - 9*P.u/4) := hmono
    _ ≤ c₀ ^ 3 * P.X ^ (1/5 + P.g/20 - 9*P.u/4) := by
        have hxp : (0:ℝ) < P.X ^ (1/5 + P.g/20 - 9*P.u/4) := Real.rpow_pos_of_pos hX0 _
        have hc3 : (1:ℝ) ≤ c₀ ^ 3 := one_le_pow₀ hc₀
        linarith [mul_le_mul_of_nonneg_right hc3 hxp.le]
    _ = P.G * P.H * e0 ^ 3 := hghe.symm
    _ ≤ P.G * P.H * S.Ω ^ 3 := by
        apply mul_le_mul_of_nonneg_left hΩ3
        positivity

set_option maxHeartbeats 600000 in
/-- **Off-strip case** of `dblock_bound` (Prop 8.1, writeup 2020–2079). `u, c₀, Cu` are shared
parameters (the merger `dblock_bound` picks them). Small-x edge `x ≤ G^{-2}Ω^{-11/2}X^{-Cu·u}` via
`prop_6_1` (binding term `x^{2/3}G^{4/3}Ω^{11/3}`); large-x edge `x ≥ G^{17}Ω^{-26}X^{Cu·u}` via
`prop_5_1` (binding term `x^{-1}G^{17}Ω^{-26}`). No `dStar` bridge needed.

**Added hypotheses** (relative to the original stub; the merger discharges them after obtaining
the opaque Prop 6.1 budget constant `StripAux.C6`):
* `hCu : (3/2)·C6 + 232 ≤ Cu` (was `1 ≤ Cu`) — the edge cutoff must dominate the Prop 6.1
  budget (small-x term 2) and the Prop 5.1 `U^{100}` budget (large-x terms 3, +1·3).
* `hubudget : (C6 + 100)·u ≤ 1/200 - 20·g` — the "shrink `u`" of the writeup (line 2079);
  RHS `> 0` since `g < 2/18187`. -/
theorem dblock_off_strip (g : ℝ) (hg0 : 0 < g) (hg1 : g < 2 / 18187)
    (u : ℝ) (hu0 : 0 < u) (hopt : 18187 * g + 15315 * u < 2) (hu2 : u ≤ 1 / 100)
    (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (Cu : ℝ) (hCu : (3/2) * StripAux.C6 + 232 ≤ Cu)
    (hubudget : (StripAux.C6 + 100) * u ≤ 1/200 - 20 * g) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), P.g = g → P.u = u → 1 ≤ P.X →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
        Real.log P.X ≤ P.X ^ P.u →
        (10:ℝ) ^ 33 ≤ P.U →
        (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω → S.Ω ≤ P.U →
        ( S.x ≤ P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))
          ∨ P.G ^ 16 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) ≤ S.x ) →
        ∀ D : ℝ, 0 < D → D = S.D → DBlock P S D ≤ C * P.H / P.U := by
  have hC6 := StripAux.C6_pos
  have hC5 := StripAux.C5_pos
  set C6 : ℝ := StripAux.C6 with hC6def
  set C5 : ℝ := StripAux.C5 with hC5def
  obtain ⟨c₁', C₁', C₂', hc₁', hC₁', hC₂', hfiber'⟩ := prop_3_2_fiber_dStar
  set Bf : ℝ := 1 + c₀ ^ (-8/3 : ℝ) with hBfdef
  have hBf1 : (1:ℝ) ≤ Bf := by
    rw [hBfdef]; have := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-8/3 : ℝ); linarith
  -- the output absolute constant (dominates both disjunction branches)
  refine ⟨C₂' * (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
      + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
        + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
      + 2 + 2), ?_, ?_⟩
  · have hBfpos : (0:ℝ) < Bf := by linarith
    have := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-7/2 : ℝ)
    have h12 := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-12 : ℝ)
    have h1 := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-1 : ℝ)
    have h13 := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-13 : ℝ)
    have h14 := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc₀) (-14 : ℝ)
    positivity
  intro P hg hu hX S hΔlong hX0big hlog hUbig hNR hAD hbandlo hΩU hdisj D hDpos hDeq
  have hX0 : (0:ℝ) < P.X := lt_of_lt_of_le one_pos hX
  have hG := P.G_pos; have hH := P.H_pos; have hU := P.U_pos
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hc₀0 : 0 < c₀ := lt_of_lt_of_le one_pos hc₀
  have hg0' : 0 ≤ P.g := by rw [hg]; exact hg0.le
  have hPu : 0 < P.u := by rw [hu]; exact hu0
  have hΔ1 : (1:ℝ) ≤ S.Δ := le_trans (Real.one_le_rpow hX (by norm_num)) hΔlong
  -- key: DBlock ≤ C₂'·(1+φ)·∑#RaOf
  obtain ⟨RaOf, hapos, hwit, hDsum⟩ :=
    StripAux.dblock_le_sum_Ra P S C₂' D
      (fun a ha0 _ hlo hAa ha2A h2AD Dd hDdpos hDdeq => by
        have hloq : (1/4:ℝ) * S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) ≤ (a:ℝ) := by
          refine le_trans ?_ hlo
          have hthr : (0:ℝ) ≤ S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) :=
            mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (by positivity) _)
          linarith [hthr]
        obtain ⟨Ra, _dStar, _hinDa, _hband, _hnear, hRaWit, hcard⟩ :=
          hfiber' P S a ha0 hΔlong hX0big hloq hAa ha2A h2AD Dd hDdpos hDdeq
        exact ⟨Ra, hRaWit, hcard⟩)
      hΔ1 hNR hAD hDpos hDeq
  -- φ factor + budget abbreviations
  have hφnn : (0:ℝ) ≤ StripAux.fiberφ P S := by
    rw [StripAux.fiberφ_def]
    have hDA : (0:ℝ) ≤ S.Δ / S.A := by
      have : (0:ℝ) < S.A := by unfold Scale.A; positivity
      positivity
    exact mul_nonneg (Real.rpow_nonneg hDA _) (Real.rpow_nonneg hG.le _)
  have h1φnn : (0:ℝ) ≤ 1 + StripAux.fiberφ P S := by linarith
  -- specialise hubudget / hCu to P (P.u = u, P.g = g)
  have hbu : (C6 + 100) * P.u ≤ 1/200 - 20 * P.g := by rw [hu, hg]; exact hubudget
  have hCuP : (3/2) * C6 + 232 ≤ Cu := hCu
  -- C6, C5 are the prop budget constants
  have hwit' : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (0 < a) ∧ ∀ r ∈ RaOf a, RaWitness P S a r :=
    fun a ha => ⟨hapos a ha, hwit a ha⟩
  -- regime hyp for Prop 6.1: 10A ≤ D, i.e. 10·(ΔΩ) ≤ H·Δ, from 10Ω ≤ 10U ≤ H
  have hAD5 : 10 * S.A ≤ S.D := by
    have h5UH : 10 * P.U ≤ P.H :=
      five_U_le_H P hX0big (by rw [hg]; exact hg1) (by rw [hu]; exact hu2)
    have h5ΩH : 10 * S.Ω ≤ P.H := le_trans (by linarith [hΩU]) h5UH
    unfold Scale.A Scale.D
    linarith [mul_le_mul_of_nonneg_left h5ΩH hΔ.le]
  have hΩfloor : (16777216 : ℝ) ≤ P.G * P.H * S.Ω ^ 3 :=
    ghΩ3_ge_500 P S c₀ hc₀ hX hg0' (by rw [hu]; exact hu2) hbandlo hX0big
  have hg1' : P.g ≤ 1 := by rw [hg]; linarith [hg1]
  have hband6 : P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) ≤ S.Ω := by
    refine le_trans ?_ hbandlo
    have hbpos : (0:ℝ) < P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ) := by
      have := Real.rpow_pos_of_pos hG (-1/4 : ℝ)
      have := Real.rpow_pos_of_pos hU (-3/4 : ℝ); positivity
    linarith [mul_le_mul_of_nonneg_right hc₀ hbpos.le]
  have hprop6 := StripAux.prop_6_1_spec P S hX hPu hg1' hAD5 hband6 hΩfloor hlog RaOf hwit'
  rw [← hC6def] at hprop6
  -- rewrite the target  C * P.H / P.U = C * (P.H / P.U)
  rw [mul_div_assoc]
  -- abbreviate the sum
  set Sr : ℝ := ∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ) with hSdef
  have hSnn : 0 ≤ Sr := Finset.sum_nonneg (fun a _ => by positivity)
  rcases hdisj with hsmall | hlarge
  · -- ========== SMALL-x case (Prop 6.1) ==========
    -- ∑#RaOf ≤ C6·H·X^{C6u}·(T1+T2+T3)
    set T1 : ℝ := S.x * P.G * S.Ω ^ 2 with hT1def
    set T2 : ℝ := S.x ^ (2/3 : ℝ) * P.G ^ (4/3 : ℝ) * S.Ω ^ (11/3 : ℝ) with hT2def
    set T3 : ℝ := P.H ^ (-1/2 : ℝ) * P.G ^ (1/2 : ℝ) * S.Ω ^ (5/2 : ℝ) with hT3def
    -- per-term q_i := C6·H·X^{C6u}·T_i, each ≤ c_i·H·X^{e_i}, e_i ≤ -3u
    have hxbud : (0:ℝ) ≤ P.X ^ (C6 * P.u) := (Real.rpow_pos_of_pos hX0 _).le
    have hxnn : (0:ℝ) ≤ S.x := by unfold Scale.x; positivity
    have hT1nn : (0:ℝ) ≤ T1 := by rw [hT1def]; positivity
    have hT2nn : (0:ℝ) ≤ T2 := by rw [hT2def]; positivity
    have hT3nn : (0:ℝ) ≤ T3 := by rw [hT3def]; positivity
    have hqnn_base : (0:ℝ) ≤ C6 * (P.H * P.X ^ (C6 * P.u)) :=
      mul_nonneg hC6.le (mul_nonneg hH.le hxbud)
    -- T2 bound
    have hT2 := StripAux.smallx_edge_T2 P S Cu (by rw [← hT2def] at *; exact hsmall)
    -- T1 bound
    have hT1 := StripAux.smallx_edge_T1 P S c₀ Cu hc₀0 hsmall hbandlo
    -- T3 bound
    have hT3 := StripAux.smallx_edge_T3 P S hΩU
    -- now bound q2 = C6·H·X^{C6u}·T2 ≤ C6·H·X^{C6u - (2/3)Cu·u}
    have hq2 : C6 * (P.H * P.X ^ (C6 * P.u)) * T2
        ≤ C6 * P.H * P.X ^ (C6 * P.u + -(2/3) * (Cu * P.u)) := by
      rw [show C6 * P.H * P.X ^ (C6 * P.u + -(2/3) * (Cu * P.u))
            = C6 * P.H * (P.X ^ (C6 * P.u) * P.X ^ (-(2/3) * (Cu * P.u))) by
            rw [← Real.rpow_add hX0]]
      rw [show C6 * (P.H * P.X ^ (C6 * P.u)) * T2
            = C6 * P.H * (P.X ^ (C6 * P.u) * T2) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hT2 hxbud
    have he2 : C6 * P.u + -(2/3) * (Cu * P.u) ≤ -3 * P.u := by
      have hp : ((3/2) * C6 + 232) * P.u ≤ Cu * P.u :=
        mul_le_mul_of_nonneg_right hCuP hPu.le
      linarith [hp, hPu]
    have hq1 : C6 * (P.H * P.X ^ (C6 * P.u)) * T1
        ≤ C6 * c₀ ^ (-7/2 : ℝ) * P.H * P.X ^ (C6 * P.u + (-P.g/8 + 21*P.u/8 - Cu * P.u)) := by
      rw [show C6 * c₀ ^ (-7/2 : ℝ) * P.H * P.X ^ (C6 * P.u + (-P.g/8 + 21*P.u/8 - Cu * P.u))
            = C6 * P.H * (P.X ^ (C6 * P.u) * (c₀ ^ (-7/2 : ℝ)
              * P.X ^ (-P.g/8 + 21*P.u/8 - Cu * P.u))) by
            rw [show C6 * P.u + (-P.g/8 + 21*P.u/8 - Cu * P.u)
                  = C6 * P.u + (-P.g/8 + 21*P.u/8 - Cu * P.u) from rfl,
                Real.rpow_add hX0]; ring]
      rw [show C6 * (P.H * P.X ^ (C6 * P.u)) * T1 = C6 * P.H * (P.X ^ (C6 * P.u) * T1) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hT1 hxbud
    have he1 : C6 * P.u + (-P.g/8 + 21*P.u/8 - Cu * P.u) ≤ -3 * P.u := by
      have hp : ((3/2) * C6 + 232) * P.u ≤ Cu * P.u :=
        mul_le_mul_of_nonneg_right hCuP hPu.le
      linarith [hp, hPu, hg0', mul_nonneg hC6.le hPu.le]
    have hq3 : C6 * (P.H * P.X ^ (C6 * P.u)) * T3
        ≤ C6 * P.H * P.X ^ (C6 * P.u + (-(1 - P.g)/10 + P.g/2 + 5*P.u/2)) := by
      rw [show C6 * P.H * P.X ^ (C6 * P.u + (-(1 - P.g)/10 + P.g/2 + 5*P.u/2))
            = C6 * P.H * (P.X ^ (C6 * P.u) * P.X ^ (-(1 - P.g)/10 + P.g/2 + 5*P.u/2)) by
            rw [← Real.rpow_add hX0]]
      rw [show C6 * (P.H * P.X ^ (C6 * P.u)) * T3 = C6 * P.H * (P.X ^ (C6 * P.u) * T3) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hT3 hxbud
    have he3 : C6 * P.u + (-(1 - P.g)/10 + P.g/2 + 5*P.u/2) ≤ -3 * P.u := by
      linarith [hbu, hPu, hg0']
    -- apply fiber_prop_term to each
    have hF2 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo
      (c := C6) (e := C6 * P.u + -(2/3) * (Cu * P.u)) hC6.le (mul_nonneg hqnn_base hT2nn) hq2 he2
    have hF1 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo
      (c := C6 * c₀ ^ (-7/2 : ℝ)) (e := C6 * P.u + (-P.g/8 + 21*P.u/8 - Cu * P.u))
      (by positivity) (mul_nonneg hqnn_base hT1nn) hq1 he1
    have hF3 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo
      (c := C6) (e := C6 * P.u + (-(1 - P.g)/10 + P.g/2 + 5*P.u/2))
      hC6.le (mul_nonneg hqnn_base hT3nn) hq3 he3
    -- DBlock ≤ C₂'·(1+φ)·Sr ≤ C₂'·[(1+φ)q1+(1+φ)q2+(1+φ)q3]
    have hSle : Sr ≤ C6 * (P.H * P.X ^ (C6 * P.u)) * T1
        + C6 * (P.H * P.X ^ (C6 * P.u)) * T2 + C6 * (P.H * P.X ^ (C6 * P.u)) * T3 := by
      have : C6 * P.H * P.X ^ (C6 * P.u) * (T1 + T2 + T3)
          = C6 * (P.H * P.X ^ (C6 * P.u)) * T1
            + C6 * (P.H * P.X ^ (C6 * P.u)) * T2 + C6 * (P.H * P.X ^ (C6 * P.u)) * T3 := by ring
      rw [← this]; exact hprop6
    have hkey : DBlock P S D ≤ C₂' * ((1 + StripAux.fiberφ P S)
        * (C6 * (P.H * P.X ^ (C6 * P.u)) * T1)
        + (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T2)
        + (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T3)) := by
      refine hDsum.trans ?_
      rw [show C₂' * (1 + StripAux.fiberφ P S) * Sr
            = C₂' * ((1 + StripAux.fiberφ P S) * Sr) by ring]
      apply mul_le_mul_of_nonneg_left _ hC₂'.le
      calc (1 + StripAux.fiberφ P S) * Sr
          ≤ (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T1
              + C6 * (P.H * P.X ^ (C6 * P.u)) * T2 + C6 * (P.H * P.X ^ (C6 * P.u)) * T3) :=
            mul_le_mul_of_nonneg_left hSle h1φnn
        _ = (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T1)
            + (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T2)
            + (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T3) := by ring
    refine hkey.trans ?_
    rw [show (C₂' * (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
            + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
            + 2 + 2)) * (P.H / P.U)
          = C₂' * ((Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
            + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
            + 2 + 2) * (P.H / P.U)) by ring]
    -- each (1+φ)·qᵢ ≤ Bf·cᵢ·(H/U); collect into the witness
    apply mul_le_mul_of_nonneg_left _ hC₂'.le
    have hHUpos : (0:ℝ) ≤ P.H / P.U := by positivity
    have hslack : (0:ℝ) ≤ C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
          + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ))) * (P.H / P.U)
        + 2 * (P.H / P.U) + 2 * (P.H / P.U) := by
      have hBfpos : (0:ℝ) < Bf := by linarith
      have h12 := Real.rpow_pos_of_pos hc₀0 (-12 : ℝ)
      have h1 := Real.rpow_pos_of_pos hc₀0 (-1 : ℝ)
      have h13 := Real.rpow_pos_of_pos hc₀0 (-13 : ℝ)
      have h14 := Real.rpow_pos_of_pos hc₀0 (-14 : ℝ)
      have := hC5; positivity
    calc (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T1)
        + (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T2)
        + (1 + StripAux.fiberφ P S) * (C6 * (P.H * P.X ^ (C6 * P.u)) * T3)
        ≤ Bf * (C6 * c₀ ^ (-7/2 : ℝ)) * (P.H / P.U)
          + Bf * C6 * (P.H / P.U) + Bf * C6 * (P.H / P.U) :=
          add_le_add (add_le_add hF1 hF2) hF3
      _ ≤ (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
            + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
            + 2 + 2) * (P.H / P.U) := by
            rw [show (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
                  + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
                    + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
                  + 2 + 2) * (P.H / P.U)
                = (Bf * (C6 * c₀ ^ (-7/2 : ℝ)) * (P.H / P.U)
                    + Bf * C6 * (P.H / P.U) + Bf * C6 * (P.H / P.U))
                  + (C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
                    + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ))) * (P.H / P.U)
                    + 2 * (P.H / P.U) + 2 * (P.H / P.U)) by ring]
            exact le_add_of_nonneg_right hslack
  · -- ========== LARGE-x case (Prop 5.1) ==========
    -- prop_5_1 hyp (i): ∃c>0, c·GU^10 ≤ H/Δ² = x.  Use c = 1 via the edge + Ω ≤ U + Cu ≥ 36.
    have hWpos : (0:ℝ) < P.Wval := by rw [StripAux.Wval_eq]; positivity
    have hUpow10 : P.U ^ 10 = P.X ^ (P.u * 10) := by
      rw [Globals.U, ← Real.rpow_natCast (P.X ^ P.u) 10, ← Real.rpow_mul hX0.le]; push_cast; ring
    have hGUe : P.G * P.U ^ 10 = P.X ^ (P.g + P.u * 10) := by
      rw [Globals.G, hUpow10, ← Real.rpow_add hX0]
    have hxval : S.x = P.H / S.Δ ^ 2 := rfl
    have hG10 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2 := by
      rw [← hxval]
      refine le_trans ?_ hlarge
      -- GU^10 ≤ G^17 Ω^{-26} X^{Cu u}  ⟸  X^{g+10u} ≤ X^{17g + 26u + Cu u}  (Ω ≤ U, exp≥0)
      have hΩ26 : S.Ω ^ (-26 : ℝ) ≥ P.U ^ (-26 : ℝ) := by
        rw [ge_iff_le, show P.U ^ (-26 : ℝ) = (P.U ^ (26:ℝ))⁻¹ by rw [← Real.rpow_neg hU.le],
            show S.Ω ^ (-26 : ℝ) = (S.Ω ^ (26:ℝ))⁻¹ by rw [← Real.rpow_neg hΩ.le]]
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow hΩ.le hΩU (by norm_num)
      have hUm26 : P.U ^ (-26 : ℝ) = P.X ^ (P.u * (-26)) := by
        rw [Globals.U, ← Real.rpow_mul hX0.le]
      have hG17e : (P.G : ℝ) ^ 16 = P.X ^ (P.g * 16) := by
        rw [Globals.G, ← Real.rpow_natCast (P.X ^ P.g) 16, ← Real.rpow_mul hX0.le]; norm_num
      have h36 : 36 * P.u ≤ Cu * P.u :=
        mul_le_mul_of_nonneg_right (by linarith [hCuP, hC6]) hPu.le
      calc P.G * P.U ^ 10 = P.X ^ (P.g + P.u * 10) := hGUe
        _ ≤ P.X ^ (16 * P.g + P.u * (-26) + Cu * P.u) := by
            apply Real.rpow_le_rpow_of_exponent_le hX
            linarith [h36, hg0']
        _ = (P.G ^ 16) * (P.U ^ (-26 : ℝ)) * P.X ^ (Cu * P.u) := by
            rw [hG17e, hUm26, ← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; ring
        _ ≤ P.G ^ 16 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left hΩ26 (by positivity)
    -- prop_5_1 hyp (ii): G²U^5 ≤ Δ via Δ ≥ X^{1/100} ≥ G²U^5.
    have hG25 : P.G ^ 2 * P.U ^ 5 ≤ S.Δ := by
      refine le_trans ?_ hΔlong
      have hG2e : (P.G : ℝ) ^ 2 = P.X ^ (P.g * 2) := by
        rw [Globals.G, ← Real.rpow_natCast (P.X ^ P.g) 2, ← Real.rpow_mul hX0.le]; norm_num
      have hU5e : (P.U : ℝ) ^ 5 = P.X ^ (P.u * 5) := by
        rw [Globals.U, ← Real.rpow_natCast (P.X ^ P.u) 5, ← Real.rpow_mul hX0.le]; norm_num
      rw [hG2e, hU5e, ← Real.rpow_add hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX
      have hbu' : C6 * P.u + 100 * P.u ≤ 1/200 - 20 * P.g := by
        have : (C6 + 100) * P.u = C6 * P.u + 100 * P.u := by ring
        linarith [hbu, this]
      have hC6u : 0 ≤ C6 * P.u := mul_nonneg hC6.le hPu.le
      linarith [hbu', hC6u, hg0']
    -- ===== AUDITED-FAITHFUL regime pack for prop_5_1 (regime ruling 2026-06-10) =====
    have hG1 : 1 ≤ P.G := Real.one_le_rpow hX hg0'
    have hU1 : 1 ≤ P.U := Real.one_le_rpow hX hPu.le
    have hH1 : 1 ≤ P.H := Real.one_le_rpow hX (by rw [hg]; linarith [hg1])
    have hu2P : P.u ≤ 1/100 := by rw [hu]; exact hu2
    have hbu100 : 100 * P.u + 20 * P.g ≤ 1/200 := by linarith [hbu, mul_pos hC6 hPu]
    have hgq : P.g ≤ 1/4000 := by linarith [hbu100, hPu.le]
    have hCu232 : (232:ℝ) ≤ Cu := by linarith [hCuP, hC6.le]
    have hband1 : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := StripAux.regime_band_one P S hband6
    have hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2 := StripAux.regime_UH P hX hg0' hu2P
    have hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ :=
      StripAux.regime_DeW P S hX hg0' hPu hbu100 hUbig hΔlong
    have hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14 :=
      StripAux.regime_Hbig P S Cu hCu232 hX hPu hG1 hΩU hUbig hlarge
    have hδbud : 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5) ≤ 1 / 2 :=
      StripAux.regime_delta_bud P S hX hg0' hPu hbu100 hband6 hUbig hΔlong
    have hΩH60 : 60 * S.Ω ≤ P.H := StripAux.regime_omega_H P S hX hgq hu2P hΩU hUbig
    have hlogcap := StripAux.regime_logcap P S hX hg0' hgq hPu hu2P hG1 hU1
      hband6 hΩU hΔ1 hUbig hlog
    -- abbreviations for the three prop-5.1 terms
    set P1 : ℝ := P.G ^ 9 * P.U ^ 51 / (S.Δ ^ (1/2 : ℝ) * S.Ω) with hP1def
    set P2 : ℝ := P.G ^ 16 * P.U ^ 85 / (S.Δ * S.Ω ^ 13) with hP2def
    set P3 : ℝ := (S.Δ ^ 2 / P.H) * (P.G ^ 16 * P.U ^ 100) / S.Ω ^ 27 with hP3def
    set RW : ℝ := S.R / P.Wval with hRWdef
    have hRpos : (0:ℝ) < S.R := by unfold Scale.R; positivity
    have hWpos2 : (0:ℝ) < P.Wval := by rw [StripAux.Wval_eq]; positivity
    have hRWnn : 0 ≤ RW := by rw [hRWdef]; exact div_nonneg hRpos.le hWpos2.le
    have hΔ12 : (0:ℝ) < S.Δ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hΔ _
    have hP1nn : 0 ≤ P1 := by rw [hP1def]; exact div_nonneg (by positivity) (by positivity)
    have hP2nn : 0 ≤ P2 := by rw [hP2def]; exact div_nonneg (by positivity) (by positivity)
    have hP3nn : 0 ≤ P3 := by rw [hP3def]; exact div_nonneg (by positivity) (by positivity)
    have hPnn : 0 ≤ P.H / S.Δ * (P1 + P2 + P3) :=
      mul_nonneg (by positivity) (by linarith [hP1nn, hP2nn, hP3nn])
    set M : ℝ := RW + C5 * (P.H / S.Δ * (P1 + P2 + P3)) with hMdef
    have hMnn : 0 ≤ M := by rw [hMdef]; have := hC5; positivity
    -- per-a: #RaOf a ≤ M
    have hper : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ) ≤ M := by
      intro a ha
      have ha0 := hapos a ha
      rw [hMdef]
      by_cases hcase : ((RaOf a).card : ℝ) ≤ RW
      · linarith [hcase, mul_nonneg hC5.le hPnn]
      · push Not at hcase
        have hpop : S.R / P.Wval ≤ ((RaOf a).card : ℝ) := by
          rw [← hRWdef]; exact hcase.le
        -- the a-window `A/5 ≤ a ≤ 11A` from `a ∈ Icc ⌈A⌉ ⌊2A⌋`
        have hamem := Finset.mem_Icc.mp ha
        have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
        have haA : S.A ≤ (a:ℝ) := le_trans (Int.le_ceil S.A) (by exact_mod_cast hamem.1)
        have ha2A : (a:ℝ) ≤ 2 * S.A :=
          le_trans (by exact_mod_cast hamem.2) (Int.floor_le (2 * S.A))
        have ha_lo : S.A / 5 ≤ (a:ℝ) := le_trans (by linarith) haA
        have ha_hi : (a:ℝ) ≤ 11 * S.A := le_trans ha2A (by linarith)
        have hp5 := StripAux.prop_5_1_spec P S a ha0 hAD5 hΩfloor (RaOf a) (hwit a ha) hG10 hG25 hpop
          hG1 hU1 hΔ1 hH1 hΩU hband1 hUbig hUH hDeW hHbig hδbud ha_lo ha_hi hΩH60 hlogcap
        rw [← hC5def, ← hP1def, ← hP2def, ← hP3def] at hp5
        calc ((RaOf a).card : ℝ)
            ≤ C5 * (P.H / S.Δ) * (P1 + P2 + P3) := hp5
          _ = C5 * (P.H / S.Δ * (P1 + P2 + P3)) := by ring
          _ ≤ RW + C5 * (P.H / S.Δ * (P1 + P2 + P3)) := by linarith [hRWnn]
    -- drop the (literal-heavy) regime-pack facts: only `hper` consumes them
    clear hlogcap hΩH60 hδbud hHbig hDeW hUH hband1 hCu232 hgq hbu100 hu2P hH1 hU1 hG1
    -- Sr ≤ #Icc • M ≤ (A+1)·M
    have hSM : Sr ≤ (S.A + 1) * M := by
      have hsum : Sr ≤ (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card • M := by
        rw [hSdef]; exact Finset.sum_le_card_nsmul _ _ _ hper
      have hcardR : ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) ≤ S.A + 1 := by
        have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
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
      calc Sr ≤ (Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card • M := hsum
        _ = ((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).card : ℝ) * M := by rw [nsmul_eq_mul]
        _ ≤ (S.A + 1) * M := mul_le_mul_of_nonneg_right hcardR hMnn
    -- the six prop-5.1 base bounds (q ≤ c·H·X^e) and their fiber multipliers
    have hΔlong' := hΔlong
    -- main terms
    have hM1 := StripAux.largex_main_P1 P S hX hΔlong
    have hM2 := StripAux.largex_main_P2 P S c₀ hc₀0 hX hΔlong hbandlo
    have hM3 := StripAux.largex_main_P3 P S Cu hX hlarge
    have hL1 := StripAux.largex_plus_P1 P S c₀ hc₀0 hX hΔlong hbandlo
    have hL2 := StripAux.largex_plus_P2 P S c₀ hc₀0 hX hΔlong hbandlo
    have hL3 := StripAux.largex_plus_P3 P S c₀ Cu hc₀0 hX hlarge hbandlo
    rw [← hP1def] at hM1 hL1
    rw [← hP2def] at hM2 hL2
    rw [← hP3def] at hM3 hL3
    -- exponent budgets ≤ -3u (all linear; the U-budget hubudget + Cu bound)
    have hbu' : C6 * P.u + 100 * P.u ≤ 1/200 - 20 * P.g := by
      have h : (C6 + 100) * P.u = C6 * P.u + 100 * P.u := by ring
      linarith [hbu, h]
    have hC6u : 0 ≤ C6 * P.u := mul_nonneg hC6.le hPu.le
    have h100 : 103 * P.u ≤ Cu * P.u :=
      mul_le_mul_of_nonneg_right (by linarith [hCuP, hC6]) hPu.le
    have heM1 : 9 * P.g + 51 * P.u + (1/100 : ℝ) * (-1/2) ≤ -3 * P.u := by
      linarith [hbu', hC6u, hg0', hPu]
    have heM2 : 16 * P.g + 85 * P.u + (1/100 : ℝ) * (-1) + (-P.g/4 - 3*P.u/4) * (-12) ≤ -3 * P.u := by
      rw [show (-P.g/4 - 3*P.u/4) * (-12) = 3*P.g + 9*P.u by ring]
      linarith [hbu', hC6u, hg0', hPu]
    have heM3 : 100 * P.u - Cu * P.u ≤ -3 * P.u := by linarith [h100]
    have heL1 : 9 * P.g + 51 * P.u + (1/100 : ℝ) * (-3/2) + (-P.g/4 - 3*P.u/4) * (-1) ≤ -3 * P.u := by
      rw [show (-P.g/4 - 3*P.u/4) * (-1) = P.g/4 + 3*P.u/4 by ring]
      linarith [hbu', hC6u, hg0', hPu]
    have heL2 : 16 * P.g + 85 * P.u + (1/100 : ℝ) * (-2) + (-P.g/4 - 3*P.u/4) * (-13) ≤ -3 * P.u := by
      rw [show (-P.g/4 - 3*P.u/4) * (-13) = 13*P.g/4 + 39*P.u/4 by ring]
      linarith [hbu', hC6u, hg0', hPu]
    have heL3 : (-(1 - P.g))/10 + 16 * P.g / 2 + 100 * P.u
        + (-P.g/4 - 3*P.u/4) * (-14) - Cu * P.u / 2 ≤ -3 * P.u := by
      rw [show (-P.g/4 - 3*P.u/4) * (-14) = 14*P.g/4 + 42*P.u/4 by ring]
      have h113 : 113 * P.u ≤ Cu * P.u / 2 := by
        have h226 : 226 * P.u ≤ Cu * P.u := mul_le_mul_of_nonneg_right (by linarith [hCuP, hC6]) hPu.le
        linarith [h226]
      linarith [h113, hg0', hPu]
    -- nonneg of the q's
    have hAHd_nn : 0 ≤ S.A * (P.H / S.Δ) := by
      have : (0:ℝ) < S.A := by unfold Scale.A; positivity
      positivity
    have hHd_nn : (0:ℝ) ≤ P.H / S.Δ := by positivity
    -- fiber multipliers:  (1+φ)·q ≤ Bf·c·(H/U)
    have hFM1 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo (c := 1)
      zero_le_one (mul_nonneg hAHd_nn hP1nn) hM1 heM1
    have hFM2 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo (c := c₀ ^ (-12 : ℝ))
      (by positivity) (mul_nonneg hAHd_nn hP2nn) hM2 heM2
    have hFM3 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo (c := 1)
      zero_le_one (mul_nonneg hAHd_nn hP3nn) hM3 heM3
    have hFL1 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo (c := c₀ ^ (-1 : ℝ))
      (by positivity) (mul_nonneg hHd_nn hP1nn) hL1 heL1
    have hFL2 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo (c := c₀ ^ (-13 : ℝ))
      (by positivity) (mul_nonneg hHd_nn hP2nn) hL2 heL2
    have hFL3 := StripAux.fiber_prop_term P S c₀ hc₀0 hX hPu hbandlo (c := c₀ ^ (-14 : ℝ))
      (by positivity) (mul_nonneg hHd_nn hP3nn) hL3 heL3
    -- trivial RW terms
    have hTR1 := StripAux.largex_triv_AR P S hg0' hX hPu hΩU
    have hTR2 := StripAux.largex_triv_R P S hg0' hX hPu hΔlong hΩU
    rw [← hRWdef] at hTR1 hTR2
    -- assemble: DBlock ≤ C₂'·(1+φ)·Sr ≤ C₂'·(1+φ)·(A+1)·M ≤ C₂'·(witness inner)·(H/U)
    have hkeyL : DBlock P S D ≤ C₂' * ((1 + StripAux.fiberφ P S) * ((S.A + 1) * M)) := by
      refine hDsum.trans ?_
      rw [show C₂' * (1 + StripAux.fiberφ P S) * Sr
            = C₂' * ((1 + StripAux.fiberφ P S) * Sr) by ring]
      apply mul_le_mul_of_nonneg_left _ hC₂'.le
      exact mul_le_mul_of_nonneg_left hSM h1φnn
    refine hkeyL.trans ?_
    rw [show C₂' * (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
            + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
            + 2 + 2) * (P.H / P.U)
          = C₂' * ((Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
            + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
            + 2 + 2) * (P.H / P.U)) by ring]
    apply mul_le_mul_of_nonneg_left _ hC₂'.le
    -- expand (1+φ)·(A+1)·M into the 8 fiber terms
    have hexpand : (1 + StripAux.fiberφ P S) * ((S.A + 1) * M)
        = (1 + StripAux.fiberφ P S) * (S.A * RW)
          + (1 + StripAux.fiberφ P S) * RW
          + C5 * ((1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P1)
            + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P2)
            + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P3)
            + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P1)
            + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P2)
            + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P3)) := by
      simp only [hMdef]; ring
    rw [hexpand]
    have hHUpos : (0:ℝ) ≤ P.H / P.U := by positivity
    -- C5-block: sum of the six fiber bounds, scaled by C5 ≥ 0
    have hsum6 : (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P1)
          + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P2)
          + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P3)
          + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P1)
          + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P2)
          + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P3)
        ≤ Bf * 1 * (P.H / P.U) + Bf * c₀ ^ (-12 : ℝ) * (P.H / P.U) + Bf * 1 * (P.H / P.U)
          + Bf * c₀ ^ (-1 : ℝ) * (P.H / P.U) + Bf * c₀ ^ (-13 : ℝ) * (P.H / P.U)
          + Bf * c₀ ^ (-14 : ℝ) * (P.H / P.U) :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hFM1 hFM2) hFM3) hFL1) hFL2) hFL3
    have hC5block : C5 * ((1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P1)
          + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P2)
          + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P3)
          + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P1)
          + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P2)
          + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P3))
        ≤ C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
            + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ))) * (P.H / P.U) := by
      have := mul_le_mul_of_nonneg_left hsum6 hC5.le
      refine this.trans (le_of_eq ?_); ring
    -- slack: the small-x-only Bf·(C6...) block is nonneg
    have hslackL : (0:ℝ) ≤ Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6) * (P.H / P.U) := by
      have hBfpos : (0:ℝ) < Bf := by linarith
      have := Real.rpow_pos_of_pos hc₀0 (-7/2 : ℝ); positivity
    -- final collection
    calc (1 + StripAux.fiberφ P S) * (S.A * RW)
          + (1 + StripAux.fiberφ P S) * RW
          + C5 * ((1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P1)
            + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P2)
            + (1 + StripAux.fiberφ P S) * (S.A * (P.H / S.Δ) * P3)
            + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P1)
            + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P2)
            + (1 + StripAux.fiberφ P S) * (P.H / S.Δ * P3))
        ≤ 2 * (P.H / P.U) + 2 * (P.H / P.U)
          + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ))) * (P.H / P.U) := by
          linarith [hTR1, hTR2, hC5block]
      _ ≤ (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
            + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
              + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
            + 2 + 2) * (P.H / P.U) := by
          rw [show (Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6)
                + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
                  + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ)))
                + 2 + 2) * (P.H / P.U)
              = Bf * (C6 * c₀ ^ (-7/2 : ℝ) + C6 + C6) * (P.H / P.U)
                + (2 * (P.H / P.U) + 2 * (P.H / P.U)
                  + C5 * (Bf * (1 + c₀ ^ (-12 : ℝ) + 1)
                    + Bf * (c₀ ^ (-1 : ℝ) + c₀ ^ (-13 : ℝ) + c₀ ^ (-14 : ℝ))) * (P.H / P.U)) by ring]
          linarith [hslackL]

/-- Small-Ω block bound (below the band): the trivial Prop 3.2 bound (writeup 400–406), no §5/§6/§7.
Uniform (absolute) `C`, valid for any band constant `c₀` (with `C` depending on `c₀`). The regime
hypotheses match `dblock_bound`'s, so the two compose over `a_decomposition`'s sum.

The hypothesis `X^{1/100} ≤ Δ` (the long range, supplied by `key_dyadic`) is ESSENTIAL: with only
`1 ≤ Δ` the statement is false — at `Δ=1`, band-edge `Ω`, the `+1`-induced bare `R = HGΩ³/Δ` term
leaves a `+g/4` surplus over `H/U`. The `1/100` margin dominates `g/4 < 1/36374`, so absolute `C`
holds (no `X^{O(u)}`). Term-by-term: the two `A·R` terms are killed by the band edge; `A`, `Δ·…`
by the Nair–Roth Δ-ceiling `Δ ≤ Ω³X/(64³H⁴)`; the two `/Δ` terms by `Δ ≥ X^{1/100}`; the rest by
`H/U → ∞`. (Needs `g < 2/18187`, `u ≤ 1/100`.) -/
theorem dblock_small_omega (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Globals), 1 ≤ P.X → 0 < P.g → P.g < 2 / 18187 → 0 < P.u → P.u ≤ 1 / 100 →
      ∀ (S : Scale P), P.X ^ (1/100 : ℝ) ≤ S.Δ →
        (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
        (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ S.A →
        2 * S.A ≤ S.D →
        S.Ω ≤ c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) →
        ∀ D : ℝ, 0 < D → D = S.D →
          DBlock P S D ≤ C * P.H / P.U := by
  obtain ⟨c₁, C₁, C₂, hc₁, hC₁, hC₂, hfiber⟩ := prop_3_2_fiber
  -- the absolute constant: sum of the eight monomial constants, times C₂
  refine ⟨C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
      + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1 + (1/4:ℝ) ^ (-8/3:ℝ)),
    by positivity, ?_⟩
  intro P hX hg0 hg hu0 hu' S hΔlong hX0big hNR hAD hband D hDpos hDeq
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
    have hloq : (1/4:ℝ) * S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) ≤ (a:ℝ) := by
      refine le_trans ?_ (le_trans hNR hAa)
      have hthr : (0:ℝ) ≤ S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) :=
        mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (by positivity) _)
      linarith [hthr]
    obtain ⟨Ra, hRaBand, hRaCard⟩ :=
      hfiber P S a ha0 hΔlong hX0big hloq hAa ha2A h2AD D hDpos hDeq
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
      ≤ C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
        + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
        + (1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by
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
    rw [hexpand, show C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
        + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
        + (1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U)
        = C₂ * ((C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
          + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
          + (1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U)) by ring]
    apply mul_le_mul_of_nonneg_left _ hC₂.le
    -- sum the eight bounds (all RHS share factor (H/U)); collect
    have hsum8 : S.A * (C₁ * S.R) + S.A * (C₁ * S.R) * φ + S.A + S.A * φ
          + C₁ * S.R + C₁ * S.R * φ + 1 + φ
        ≤ (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
          + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
          + (1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by
      have hrhs : (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
          + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
          + (1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U)
          = (C₁ * c₀ ^ (4:ℝ)) * (P.H / P.U) + (C₁ * c₀ ^ (4/3:ℝ)) * (P.H / P.U)
            + (c₀ ^ (4:ℝ) / (1/4) ^ 3) * (P.H / P.U) + (c₀ ^ (4/3:ℝ) / (1/4) ^ 3) * (P.H / P.U)
            + (C₁ * c₀ ^ (3:ℝ)) * (P.H / P.U) + (C₁ * c₀ ^ (1/3:ℝ)) * (P.H / P.U)
            + (1:ℝ) * (P.H / P.U) + ((1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := by ring
      rw [hrhs]
      linarith [t1, t2, t3, t4, t5, t6, t7, t8]
    exact hsum8
  -- chain and rewrite C * H / U = C * (H/U)
  have hfin : DBlock P S D
      ≤ C₂ * (C₁ * c₀ ^ (4:ℝ) + C₁ * c₀ ^ (4/3:ℝ) + c₀ ^ (4:ℝ) / (1/4) ^ 3
        + c₀ ^ (4/3:ℝ) / (1/4) ^ 3 + C₁ * c₀ ^ (3:ℝ) + C₁ * c₀ ^ (1/3:ℝ) + 1
        + (1/4:ℝ) ^ (-8/3:ℝ)) * (P.H / P.U) := hDle.trans hbody
  -- C * P.H / P.U = C * (P.H / P.U)
  rw [mul_div_assoc]
  exact hfin

end Squarefree
