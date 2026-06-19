import Squarefree.Lower.Step3FsumTightMon

/-!
# §5 Step-3 scale-domination to the CORRECTED monomials `t4', t5'` (writeup 975–984)

`step3_fsum_le_t4t5` is the §5 Step-3 scale-domination lemma targeting the **correct** two
Step-3 `Bcombine` monomials (the 4th and 5th of `Bcombine`, the V₂-range / collapsed-`ℓ₁`
monomials):

* `t4' = (H/Δ)·(Δ²/H)·G^{15/2}·U^{95/2}/Ω⁸`  (the `Δ²/H` term);
* `t5' = (H/Δ)·G⁷·U³⁵/(Δ^{1/2}·Ω)`           (the `1/√Δ` term).

It bounds the per-pair Step-3 `f`-sum `2·10⁵⁸·(κ·N² + ρ·N + (ρ/κ)·(log N + 1))` produced by
`Ra_step3_fsum` by a constant multiple of `t4' + t5'`.

**Payless κ·Na-leg (hHbig-route).** The κN²-leg comparison `κ·Na ≤ ρ` reduces (in
√-variables) to `Δ²·√G·U^{15/2} ≤ H·Ω³`, which follows SQUARED from the regime calibration
`hHbig : 10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴` (in `prop_5_1`'s pack) together with `Ω ≤ U` and
`G,U ≥ 1` — `H²Ω⁶·U⁸ ≥ H²Ω¹⁴ ≥ 10¹¹²·Δ⁴G⁵U⁴⁵ ≥ Δ⁴GU¹⁵·U⁸`, cancel `U⁸`.  No band-edge
`G·U⁴` pay is needed, so the conclusion monomials are the UNbumped `t4', t5'` above.  The
`κ·Nc ≤ ρ` comparison still uses the faithful band-edge primitive `hband : 1 ≤ G·U³·Ω⁴`
(via the pay fact `1 ≤ G·U⁴·Ω³`, absorbed into its own `g²v²` slack for free).

The cap on `N` here is the **V₂** envelope (the genuine Step-3 `f`-cap with `ℓ₁ ≤ W = G·U⁵`
collapsed), `N ≤ 10⁹⁰·(Na + Nb + Nc)` with

* `Na = G^{9/2}·U^{55/2}/Ω⁵`,
* `Nb = H·G⁴·Ω²·U¹⁵/Δ^{5/2}`,
* `Nc = G²·U¹⁵/Ω⁵`.

Decomposition (all `sympy`-verified):
* `ρ·N → t4'+t5'`: `ρ·Na = (H/Δ)t4'` exact, `ρ·Nb = (H/Δ)t5'` exact, `ρ·Nc ≤ (H/Δ)t4'`.
* `κ·N² ≤ ρ·N`: each `κ·Nx ≤ ρ` (`κNa/ρ = Δ²G^{1/2}U^{15/2}/(HΩ³) ≤ 1` via `hHbig`,
  `κNb/ρ = Ω⁴/(√Δ U⁵) ≤ 1`, `κNc/ρ = Δ²/(G²HΩ³U⁵) ≤ 1`).
* `(ρ/κ)·(log N + 1) → t5'`: by the largeness hypothesis `log N + 1 ≤ G³U¹⁵√Δ·Ω` the harmonic
  term is `≤ (ρ/κ)·G³U¹⁵√Δ·Ω = (H/Δ)t5'` exactly (the writeup's omitted log is `X^{o(1)}`,
  absorbed into this faithful `X`-large condition).

Scale identities: `κ = Δ³/(H·G·Ω)`, `ρ = G²·Δ·U²⁰/Ω³`, `ρ/κ = G³·H·U²⁰/(Δ²·Ω²)`.

The conclusion constant is `10²⁴⁴` (head-room for the ×130² envelope traffic; the worst leg
is `≈ 1.2·10²³⁹`).
-/

namespace Squarefree

open Finset

variable {P : Globals} {S : Scale P}
set_option maxHeartbeats 3200000 in
/-- **Step-3 scale-domination to the corrected monomials (writeup 975–984).** The per-pair
Step-3 `f`-sum bound from `Ra_step3_fsum` — `2·10⁵⁸·(κ·N² + ρ·N + (ρ/κ)·(log N + 1))` with
`κ = D⁴/(X·A)`, `ρ = R·(Δ²·G·U²⁰/(H·Ω⁶))` and `N` the admissible-`f` cap at the **V₂**
envelope — lands under a constant multiple of the two Step-3 `Bcombine` V₂-range monomials

* `t4' = (H/Δ)·(Δ²/H)·G^{15/2}·U^{95/2}/Ω⁸`  (the `Δ²/H` term);
* `t5' = (H/Δ)·G⁷·U³⁵/(Δ^{1/2}·Ω)`           (the `1/√Δ` term).

The V₂ envelope `N ≤ 10⁹⁰·(Na + Nb + Nc)` gives `ρN ≤ const·(t4'+t5')` via the exact
identities `ρNa = (H/Δ)t4'`, `ρNb = (H/Δ)t5'`, `ρNc ≤ (H/Δ)t4'`.  The κN²-leg is PAYLESS:
`κ·Na ≤ ρ` follows from the regime calibration `hHbig : 10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴` (squared
comparison, no `G·U⁴` band-edge pay; the band-edge primitive `hband : 1 ≤ G·U³·Ω⁴` is still
used on the `κ·Nc` leg).  The largeness hypothesis `hlogcap : log N + 1 ≤ G³U¹⁵√Δ·Ω` gives
`(ρ/κ)·(log N + 1) ≤ (ρ/κ)·G³U¹⁵√Δ·Ω = (H/Δ)t5'`.  Comparisons use the working regime
(`Δ²·G·U¹⁰ ≤ H`, `Ω ≤ U`, `G,U,Δ,H ≥ 1`, band edge `1 ≤ G·U³·Ω⁴`, `hHbig`). -/
theorem step3_fsum_le_t4t5
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hΩU : S.Ω ≤ P.U)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14)
    (N : ℝ) (hN1 : 1 ≤ N)
    (hNbd : N ≤ 10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
        + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
        + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5))
    (hlogcap : Real.log N + 1 ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω) :
    2 * 10 ^ 58 * ((S.D ^ 4 / (P.X * S.A)) * N ^ 2
        + (S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))) * N
        + (S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))) / (S.D ^ 4 / (P.X * S.A))
            * (Real.log N + 1))
      ≤ 10 ^ 244 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2)
              / S.Ω ^ 8)
          + (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35
              / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω))) := by
  -- positivity
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos; have hXpos := P.X_pos
  have hGnn := hGpos.le; have hUnn := hUpos.le; have hHnn := hHpos.le
  have hΩnn := hΩpos.le; have hΔnn := hΔpos.le
  -- square-root building blocks: sG = √G, sU = √U, sD = √Δ
  set sG : ℝ := P.G ^ ((1 : ℝ) / 2) with hsGdef
  set sU : ℝ := P.U ^ ((1 : ℝ) / 2) with hsUdef
  set sD : ℝ := S.Δ ^ ((1 : ℝ) / 2) with hsDdef
  have hsG0 : 0 < sG := Real.rpow_pos_of_pos hGpos _
  have hsU0 : 0 < sU := Real.rpow_pos_of_pos hUpos _
  have hsD0 : 0 < sD := Real.rpow_pos_of_pos hΔpos _
  have hsG1 : 1 ≤ sG := Real.one_le_rpow hG1 (by norm_num)
  have hsU1 : 1 ≤ sU := Real.one_le_rpow hU1 (by norm_num)
  have hsD1 : 1 ≤ sD := Real.one_le_rpow hΔ1 (by norm_num)
  -- second-power collapses sG² = G etc.
  have hsG2 : sG ^ 2 = P.G := by
    rw [hsGdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hGnn]; norm_num
  have hsU2 : sU ^ 2 = P.U := by
    rw [hsUdef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hUnn]; norm_num
  have hsD2 : sD ^ 2 = S.Δ := by
    rw [hsDdef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hΔnn]; norm_num
  -- half-power facts for the targets
  have hG152 : P.G ^ ((15 : ℝ) / 2) = sG ^ 15 := by
    rw [hsGdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/2)) 15, ← Real.rpow_mul hGnn]; norm_num
  have hU952 : P.U ^ ((95 : ℝ) / 2) = sU ^ 95 := by
    rw [hsUdef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/2)) 95, ← Real.rpow_mul hUnn]; norm_num
  have hΔ12 : S.Δ ^ ((1 : ℝ) / 2) = sD := hsDdef.symm
  -- envelope half-powers
  have hG92 : P.G ^ ((9 : ℝ) / 2) = sG ^ 9 := by
    rw [hsGdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/2)) 9, ← Real.rpow_mul hGnn]; norm_num
  have hU552 : P.U ^ ((55 : ℝ) / 2) = sU ^ 55 := by
    rw [hsUdef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/2)) 55, ← Real.rpow_mul hUnn]; norm_num
  have hΔ52 : S.Δ ^ ((5 : ℝ) / 2) = sD ^ 5 := by
    rw [hsDdef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 5, ← Real.rpow_mul hΔnn]; norm_num
  -- √Δ as the rpow-1/2 building block
  have hsqrtΔ : Real.sqrt S.Δ = sD := by
    rw [hsDdef, Real.sqrt_eq_rpow]
  -- κ, ρ in plain monomials
  have hκval : S.D ^ 4 / (P.X * S.A) = S.Δ ^ 3 / (P.H * P.G * S.Ω) :=
    defect_D4_div_XA S
  have hHne := ne_of_gt hHpos; have hΔne := ne_of_gt hΔpos
  have hΩne := ne_of_gt hΩpos; have hGne := ne_of_gt hGpos
  have hρval : S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
      = P.G ^ 3 * S.Δ * P.U ^ 20 / S.Ω ^ 3 := by
    unfold Scale.R; field_simp
  have hρκval : (S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))) / (S.D ^ 4 / (P.X * S.A))
      = P.G ^ 4 * P.H * P.U ^ 20 / (S.Δ ^ 2 * S.Ω ^ 2) := by
    rw [hρval, hκval]; field_simp
  -- rewrite the three LHS coefficients (ρ/κ first to keep ρ-pattern intact)
  rw [hρκval, hρval, hκval]
  -- ===== Express targets, envelope pieces, and coefficients in √-variables =====
  have hU35 : P.U ^ 35 = sU ^ 70 := by rw [← hsU2]; ring
  have hG2 : P.G ^ 2 = sG ^ 4 := by rw [← hsG2]; ring
  have hG7 : P.G ^ 7 = sG ^ 14 := by rw [← hsG2]; ring
  have hU15 : P.U ^ 15 = sU ^ 30 := by rw [← hsU2]; ring
  have hU20 : P.U ^ 20 = sU ^ 40 := by rw [← hsU2]; ring
  have hG3 : P.G ^ 3 = sG ^ 6 := by rw [← hsG2]; ring
  have hG4 : P.G ^ 4 = sG ^ 8 := by rw [← hsG2]; ring
  have hΔ1' : S.Δ = sD ^ 2 := hsD2.symm
  have hΔ3 : S.Δ ^ 3 = sD ^ 6 := by rw [hΔ1']; ring
  have hΔ2' : S.Δ ^ 2 = sD ^ 4 := by rw [hΔ1']; ring
  -- t4' = sD²·sG¹⁵·sU⁹⁵/Ω⁸ (the payless target)
  have ht4eq : (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2)
        / S.Ω ^ 8) = sD ^ 2 * sG ^ 15 * sU ^ 95 / S.Ω ^ 8 := by
    rw [hG152, hU952, hΔ2', hΔ1']
    field_simp
  -- t5' = H·sG¹⁴·sU⁷⁰/(sD³·Ω) (the payless target)
  have ht5eq : (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω))
        = P.H * sG ^ 14 * sU ^ 70 / (sD ^ 3 * S.Ω) := by
    rw [hG7, hU35, hΔ12, hΔ1']
    field_simp
  -- ρ-coeff = sD²·sG⁶·sU⁴⁰/Ω³
  have hρeq : P.G ^ 3 * S.Δ * P.U ^ 20 / S.Ω ^ 3 = sD ^ 2 * sG ^ 6 * sU ^ 40 / S.Ω ^ 3 := by
    rw [hG3, hΔ1', hU20]; ring
  -- κ-coeff = sD⁶/(H·sG²·Ω)
  have hκeq : S.Δ ^ 3 / (P.H * P.G * S.Ω) = sD ^ 6 / (P.H * sG ^ 2 * S.Ω) := by
    rw [hΔ3, hsG2]
  -- ρ/κ-coeff = H·sG⁸·sU⁴⁰/(sD⁴·Ω²)
  have hρκeq : P.G ^ 4 * P.H * P.U ^ 20 / (S.Δ ^ 2 * S.Ω ^ 2)
      = P.H * sG ^ 8 * sU ^ 40 / (sD ^ 4 * S.Ω ^ 2) := by
    rw [hG4, hU20, hΔ2']; ring
  -- envelope pieces in √-variables: Na = sG⁹sU⁵⁵/Ω⁵, Nb = H sG⁸ Ω² sU³⁰/sD⁵, Nc = sG⁴sU³⁰/Ω⁵
  have hNaeq : P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5
      = sG ^ 9 * sU ^ 55 / S.Ω ^ 5 := by rw [hG92, hU552]
  have hNbeq : P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2)
      = P.H * sG ^ 8 * S.Ω ^ 2 * sU ^ 30 / sD ^ 5 := by rw [hG4, hU15, hΔ52]
  have hNceq : P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 = sG ^ 4 * sU ^ 30 / S.Ω ^ 5 := by rw [hG2, hU15]
  -- regime fact in √-variables: sD⁴·sG²·sU²⁰ ≤ H  (from h1)
  have hH_big : S.Δ ^ 2 * P.G * P.U ^ 10 ≤ P.H := by
    have hΔ2 : (0:ℝ) < S.Δ ^ 2 := by positivity
    have hkey := (le_div_iff₀ hΔ2).mp h1
    have heq : S.Δ ^ 2 * P.G * P.U ^ 10 = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
    rw [heq]; exact hkey
  have hH_big' : sD ^ 4 * sG ^ 2 * sU ^ 20 ≤ P.H := by
    have hU10 : P.U ^ 10 = sU ^ 20 := by rw [← hsU2]; ring
    calc sD ^ 4 * sG ^ 2 * sU ^ 20 = S.Δ ^ 2 * P.G * P.U ^ 10 := by
            rw [hΔ2', hsG2, hU10]
      _ ≤ P.H := hH_big
  -- √-variable regime fact: Ω ≤ sU² (from Ω ≤ U)
  have hΩsU2 : S.Ω ≤ sU ^ 2 := by rw [hsU2]; exact hΩU
  -- band-edge pay fact: 1 ≤ sG²·sU⁸·Ω³ (from `hband : 1 ≤ G·U³·Ω⁴` and Ω ≤ sU²);
  -- consumed only by the `κ·Nc` leg.
  have hband' : (1:ℝ) ≤ sG ^ 2 * sU ^ 6 * S.Ω ^ 4 := by
    have heq : P.G * P.U ^ 3 * S.Ω ^ 4 = sG ^ 2 * sU ^ 6 * S.Ω ^ 4 := by
      rw [← hsG2, ← hsU2]; ring
    rw [← heq]; exact hband
  have hpay : (1:ℝ) ≤ sG ^ 2 * sU ^ 8 * S.Ω ^ 3 := by
    calc (1:ℝ) ≤ sG ^ 2 * sU ^ 6 * S.Ω ^ 4 := hband'
      _ = (sG ^ 2 * sU ^ 6 * S.Ω ^ 3) * S.Ω := by ring
      _ ≤ (sG ^ 2 * sU ^ 6 * S.Ω ^ 3) * sU ^ 2 :=
          mul_le_mul_of_nonneg_left hΩsU2 (by positivity)
      _ = sG ^ 2 * sU ^ 8 * S.Ω ^ 3 := by ring
  -- ===== the hHbig-route key fact: Δ⁴·G·U¹⁵ ≤ H²·Ω⁶ (square of the κNa-leg comparison) =====
  have hΔ4GU15 : S.Δ ^ 4 * P.G * P.U ^ 15 ≤ P.H ^ 2 * S.Ω ^ 6 := by
    -- H²Ω⁶·U⁸ ≥ H²Ω¹⁴ ≥ 10¹¹²·Δ⁴G⁵U⁴⁵ ≥ Δ⁴GU¹⁵·U⁸; cancel U⁸ > 0.
    have hΩ8 : S.Ω ^ 8 ≤ P.U ^ 8 := pow_le_pow_left₀ hΩnn hΩU 8
    have hup : P.H ^ 2 * S.Ω ^ 14 ≤ P.H ^ 2 * S.Ω ^ 6 * P.U ^ 8 := by
      calc P.H ^ 2 * S.Ω ^ 14 = P.H ^ 2 * S.Ω ^ 6 * S.Ω ^ 8 := by ring
        _ ≤ P.H ^ 2 * S.Ω ^ 6 * P.U ^ 8 :=
            mul_le_mul_of_nonneg_left hΩ8 (by positivity)
    have hGU : P.G * P.U ^ 23 ≤ P.G ^ 5 * P.U ^ 45 := by
      have hg' : P.G ^ 1 ≤ P.G ^ 5 := pow_le_pow_right₀ hG1 (by norm_num)
      have hu' : P.U ^ 23 ≤ P.U ^ 45 := pow_le_pow_right₀ hU1 (by norm_num)
      calc P.G * P.U ^ 23 = P.G ^ 1 * P.U ^ 23 := by ring
        _ ≤ P.G ^ 5 * P.U ^ 23 := mul_le_mul_of_nonneg_right hg' (by positivity)
        _ ≤ P.G ^ 5 * P.U ^ 45 := mul_le_mul_of_nonneg_left hu' (by positivity)
    have hlow : S.Δ ^ 4 * P.G * P.U ^ 15 * P.U ^ 8
        ≤ 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) := by
      have e : S.Δ ^ 4 * P.G * P.U ^ 15 * P.U ^ 8 = S.Δ ^ 4 * (P.G * P.U ^ 23) := by ring
      rw [e]
      calc S.Δ ^ 4 * (P.G * P.U ^ 23) ≤ S.Δ ^ 4 * (P.G ^ 5 * P.U ^ 45) :=
            mul_le_mul_of_nonneg_left hGU (by positivity)
        _ = 1 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) := by ring
        _ ≤ 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hchain : S.Δ ^ 4 * P.G * P.U ^ 15 * P.U ^ 8 ≤ (P.H ^ 2 * S.Ω ^ 6) * P.U ^ 8 :=
      le_trans hlow (le_trans hHbig hup)
    exact le_of_mul_le_mul_right hchain (by positivity)
  have hkey2' : sD ^ 8 * sG ^ 2 * sU ^ 30 ≤ P.H ^ 2 * S.Ω ^ 6 := by
    calc sD ^ 8 * sG ^ 2 * sU ^ 30 = S.Δ ^ 4 * P.G * P.U ^ 15 := by
          rw [← hsD2, ← hsG2, ← hsU2]; ring
      _ ≤ P.H ^ 2 * S.Ω ^ 6 := hΔ4GU15
  -- ===== rewrite the LHS coefficients & the envelope bound to √-variables =====
  rw [hκeq, hρeq, hρκeq, ht4eq, ht5eq]
  rw [hNaeq, hNbeq, hNceq] at hNbd
  -- the rewritten log-cap RHS: G³U¹⁵√Δ·Ω = sG⁶·sU³⁰·sD·Ω
  have hcapeq : P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω = sG ^ 6 * sU ^ 30 * sD * S.Ω := by
    rw [hG3, hU15, hsqrtΔ]
  rw [hcapeq] at hlogcap
  -- abbreviate the rewritten coefficients & targets
  set κc : ℝ := sD ^ 6 / (P.H * sG ^ 2 * S.Ω) with hκcdef
  set ρc : ℝ := sD ^ 2 * sG ^ 6 * sU ^ 40 / S.Ω ^ 3 with hρcdef
  set rkc : ℝ := P.H * sG ^ 8 * sU ^ 40 / (sD ^ 4 * S.Ω ^ 2) with hrkcdef
  set T5 : ℝ := P.H * sG ^ 14 * sU ^ 70 / (sD ^ 3 * S.Ω) with hT5def
  set T4 : ℝ := sD ^ 2 * sG ^ 15 * sU ^ 95 / S.Ω ^ 8 with hT4def
  set Na : ℝ := sG ^ 9 * sU ^ 55 / S.Ω ^ 5 with hNadef
  set Nb : ℝ := P.H * sG ^ 8 * S.Ω ^ 2 * sU ^ 30 / sD ^ 5 with hNbdef
  set Nc : ℝ := sG ^ 4 * sU ^ 30 / S.Ω ^ 5 with hNcdef
  have hκcnn : 0 ≤ κc := by rw [hκcdef]; positivity
  have hρcnn : 0 ≤ ρc := by rw [hρcdef]; positivity
  have hrkcnn : 0 ≤ rkc := by rw [hrkcdef]; positivity
  have hT5nn : 0 ≤ T5 := by rw [hT5def]; positivity
  have hT4nn : 0 ≤ T4 := by rw [hT4def]; positivity
  have hNann : 0 ≤ Na := by rw [hNadef]; positivity
  have hNbnn : 0 ≤ Nb := by rw [hNbdef]; positivity
  have hNcnn : 0 ≤ Nc := by rw [hNcdef]; positivity
  have hNnn : (0:ℝ) ≤ N := by linarith
  -- envelope: N ≤ 10⁹⁰·(Na + Nb + Nc)
  have hCn : N ≤ 10 ^ 90 * Na + 10 ^ 90 * Nb + 10 ^ 90 * Nc := hNbd
  -- ===== core √-variable monomial bounds via helpers =====
  -- ρ-side: ρc·Na = T4, ρc·Nb = T5, ρc·Nc ≤ T4
  have hρNa : ρc * Na = T4 := by
    rw [hρcdef, hNadef, hT4def]; exact monρ_Na hΩpos
  have hρNb : ρc * Nb = T5 := by
    rw [hρcdef, hNbdef, hT5def]; exact monρ_Nb hsD0 hΩpos
  have hρNc : ρc * Nc ≤ T4 := by
    rw [hρcdef, hNcdef, hT4def]; exact monρ_Nc hsG0 hsU0 hsD0 hΩpos hsG1 hsU1
  -- κ-side (all payless): κc·Na ≤ ρc (hHbig-route), κc·Nb ≤ ρc, κc·Nc ≤ ρc
  have hκNa : κc * Na ≤ ρc := by
    rw [hκcdef, hNadef, hρcdef]
    exact monκ_Na hsG0 hsU0 hsD0 hΩpos hHpos hkey2'
  have hκNb : κc * Nb ≤ ρc := by
    rw [hκcdef, hNbdef, hρcdef]
    exact monκ_Nb hsG0 hsU0 hsD0 hΩpos hHpos hsU1 hsD1 hΩsU2
  have hκNc : κc * Nc ≤ ρc := by
    rw [hκcdef, hNcdef, hρcdef]
    exact monκ_Nc hsG0 hsU0 hsD0 hΩpos hHpos hsG1 hsU1 hpay hH_big'
  -- log-cap: rkc·(log N + 1) ≤ rkc·(sG⁶sU³⁰ sD Ω) = T5
  have hrkcap : rkc * (sG ^ 6 * sU ^ 30 * sD * S.Ω) = T5 := by
    rw [hrkcdef, hT5def]
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- ===== assemble the three LHS terms =====
  -- term ρ: ρc·N ≤ 10⁹⁰·(2·T4 + T5)
  have htermρ : ρc * N ≤ 10 ^ 90 * (2 * T4 + T5) := by
    have hstep : ρc * N ≤ ρc * (10 ^ 90 * Na + 10 ^ 90 * Nb + 10 ^ 90 * Nc) :=
      mul_le_mul_of_nonneg_left hCn hρcnn
    have hexp : ρc * (10 ^ 90 * Na + 10 ^ 90 * Nb + 10 ^ 90 * Nc)
        = 10 ^ 90 * (ρc * Na) + 10 ^ 90 * (ρc * Nb) + 10 ^ 90 * (ρc * Nc) := by ring
    rw [hexp, hρNa, hρNb] at hstep
    have hNcbd : (10:ℝ) ^ 90 * (ρc * Nc) ≤ 10 ^ 90 * T4 :=
      mul_le_mul_of_nonneg_left hρNc (by norm_num)
    nlinarith [hstep, hNcbd]
  -- κN ≤ 3·10⁹⁰·ρc (payless)
  have hκN : κc * N ≤ 3 * 10 ^ 90 * ρc := by
    have hstep : κc * N ≤ κc * (10 ^ 90 * Na + 10 ^ 90 * Nb + 10 ^ 90 * Nc) :=
      mul_le_mul_of_nonneg_left hCn hκcnn
    have hexp : κc * (10 ^ 90 * Na + 10 ^ 90 * Nb + 10 ^ 90 * Nc)
        = 10 ^ 90 * (κc * Na) + 10 ^ 90 * (κc * Nb) + 10 ^ 90 * (κc * Nc) := by ring
    rw [hexp] at hstep
    have hb1 : (10:ℝ) ^ 90 * (κc * Na) ≤ 10 ^ 90 * ρc :=
      mul_le_mul_of_nonneg_left hκNa (by norm_num)
    have hb2 : (10:ℝ) ^ 90 * (κc * Nb) ≤ 10 ^ 90 * ρc :=
      mul_le_mul_of_nonneg_left hκNb (by norm_num)
    have hb3 : (10:ℝ) ^ 90 * (κc * Nc) ≤ 10 ^ 90 * ρc :=
      mul_le_mul_of_nonneg_left hκNc (by norm_num)
    linarith [hstep, hb1, hb2, hb3]
  -- term κ: κc·N² ≤ 3·10⁹⁰·ρc·N ≤ 3·10⁹⁰·10⁹⁰·(2T4+T5)
  have htermκ : κc * N ^ 2 ≤ 3 * 10 ^ 90 * (10 ^ 90 * (2 * T4 + T5)) := by
    calc κc * N ^ 2 = (κc * N) * N := by ring
      _ ≤ (3 * 10 ^ 90 * ρc) * N := mul_le_mul_of_nonneg_right hκN hNnn
      _ = 3 * 10 ^ 90 * (ρc * N) := by ring
      _ ≤ 3 * 10 ^ 90 * (10 ^ 90 * (2 * T4 + T5)) :=
          mul_le_mul_of_nonneg_left htermρ (by norm_num)
  -- term ρ/κ: rkc·(log N + 1) ≤ rkc·(cap) = T5
  have htermlog : rkc * (Real.log N + 1) ≤ T5 := by
    have hstep : rkc * (Real.log N + 1) ≤ rkc * (sG ^ 6 * sU ^ 30 * sD * S.Ω) :=
      mul_le_mul_of_nonneg_left hlogcap hrkcnn
    rw [hrkcap] at hstep; exact hstep
  -- ===== combine =====
  have hcombine : κc * N ^ 2 + ρc * N + rkc * (Real.log N + 1)
      ≤ 3 * 10 ^ 90 * (10 ^ 90 * (2 * T4 + T5)) + 10 ^ 90 * (2 * T4 + T5) + T5 := by
    linarith [htermκ, htermρ, htermlog]
  -- the intermediate bound equals (cT4·T4 + cT5·T5) with both coeffs ≤ 10²⁴⁴
  have hexpand : 2 * 10 ^ 58 * (3 * 10 ^ 90 * (10 ^ 90 * (2 * T4 + T5))
        + 10 ^ 90 * (2 * T4 + T5) + T5)
      = (2 * 10 ^ 58 * (6 * 10 ^ 180 + 2 * 10 ^ 90)) * T4
        + (2 * 10 ^ 58 * (3 * 10 ^ 180 + 10 ^ 90 + 1)) * T5 := by ring
  have hcT4 : (2 * 10 ^ 58 * (6 * 10 ^ 180 + 2 * 10 ^ 90)) * T4 ≤ 10 ^ 244 * T4 :=
    mul_le_mul_of_nonneg_right (by norm_num) hT4nn
  have hcT5 : (2 * 10 ^ 58 * (3 * 10 ^ 180 + 10 ^ 90 + 1)) * T5 ≤ 10 ^ 244 * T5 :=
    mul_le_mul_of_nonneg_right (by norm_num) hT5nn
  calc 2 * 10 ^ 58 * (κc * N ^ 2 + ρc * N + rkc * (Real.log N + 1))
      ≤ 2 * 10 ^ 58 * (3 * 10 ^ 90 * (10 ^ 90 * (2 * T4 + T5))
          + 10 ^ 90 * (2 * T4 + T5) + T5) := by
        apply mul_le_mul_of_nonneg_left hcombine (by norm_num)
    _ = (2 * 10 ^ 58 * (6 * 10 ^ 180 + 2 * 10 ^ 90)) * T4
        + (2 * 10 ^ 58 * (3 * 10 ^ 180 + 10 ^ 90 + 1)) * T5 := hexpand
    _ ≤ 10 ^ 244 * T4 + 10 ^ 244 * T5 := by linarith [hcT4, hcT5]
    _ = 10 ^ 244 * (T4 + T5) := by ring

end Squarefree
