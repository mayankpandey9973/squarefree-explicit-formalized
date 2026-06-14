import Squarefree.Lower.Prop51Step4Prime

/-!
# §5 Step-4 per-pair s-sum collapse — ADDITIVE form (sharp `1/√n` band + additive `√n` room)

The faithful Step-4 v-count produced by the **additive** square-difference route
(`Step4SqDiff.lean`: `#F ≤ 2 + 2·ℓ₁·diam/Vlo`, `diam = (4·err + 4·E)/Ĉ`, with the perturbation
`E ≤ ρ·|s|` of `Step4_E_le_rho_s`) has, as a function of `n = |s|` with `Vlo ≍ V_s(n)`, the shape

  `#F ≤ 2 + c_err/√n + c_E·√n`,

where the `c_err/√n` band is the SHARP near-integer band (`c_err = err·ΔΩ/√L`, `L = ℓ₁ℓ₂(ℓ₂−ℓ₁)`)
and the **additive** `c_E·√n` term (`c_E = (8/3)·ρ·ΔΩ/√L`) is the geometric room opened by the
perturbation `E`.  Paired with `Cv ≤ K_C·(b + dc/√n)` (`b = Rδ = H·G⁵U¹⁵/(Δ²Ω²)`,
`dc = (G⁴U¹⁵/Ω⁴)·√L`, `step4_hperv`), the per-`s` count `#F·Cv` summed over `1 ≤ n ≤ N` lands the
faithful `t6' + t7'` monomials.

## Structure of the collapse (`ra_step4_ssum_collapse_add`)

Pointwise (for `n ≥ 1`)
  `(2 + c_err/√n + c_E√n)(b + dc/√n)
      = weight4' b c_err dc n  +  (b + dc/√n)  +  (c_E·b·√n + c_E·dc)`,
so the s-sum splits into:

* the **SHARP** part `∑ weight4' + ∑ (b + dc/√n)` — both `≤ ∑ weight4'`-bound; REUSED verbatim from
  the green `ra_step4_ssum_collapse'` (`Prop51Step4Prime`), landing `16·C·(H/Δ)·(t6' + t7')`;
* the **E-part** `∑ (c_E·b·√n + c_E·dc) = c_E·b·∑√n + c_E·dc·N ≤ c_E·b·(N·√N) + c_E·dc·N`, summed by
  the green `sum_sqrt_le` (`Σ√n ≤ N√N`) and `Σ1 = N`.  Its domination by the faithful RHS is the
  caller obligation `hEA`, `hEB` (the two E-part products are each `≤` a `t6'`/`t7'` block).

The E-part **does** fit for the `E_recon` (`231·10⁶/Δ`) and `E_drift` (`6·10⁷·Ω²/H²`) summands of
`ρ` with room to spare; the `E_cubic` (`1/U¹⁴`) and `E_p2` summands must be routed through the
`|v| ≤ C·V_s` confinement (not band-widening) before this lemma applies — see the note in
`ra_step4_ssum_collapse_add`'s docstring.
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The TRUE-ℓ Step-4 s-sum integrand, **ADDITIVE form**: the SHARP near-integer band v-count
`(1 + c_err/√n)` widened by the additive perturbation room `c_E·√n` (so the constant `1` becomes
`2` and the `√n` term is appended), paired with the bare smooth count factor `(b + dc/√n)`:

  `weight4add b c_err dc c_E n = (2 + c_err/√n + c_E·√n)·(b + dc/√n)`. -/
noncomputable def weight4add (b ev dc cE : ℝ) (n : ℝ) : ℝ :=
  (2 + ev / Real.sqrt n + cE * Real.sqrt n) * (b + dc / Real.sqrt n)

/-- **§5 Step-4 per-pair s-sum collapse (ADDITIVE, sharp `1/√n` band + additive `√n` room).**

For the additive v-count weight `(2 + c_err/√n + c_E√n)(b + dc/√n)`, summed over `1 ≤ n ≤ N`, with
the SHARP-band coefficients of `ra_step4_ssum_collapse'` (`b = Rδ`, `ev = c_err = err·ΔΩ/√L`,
`dc = (G⁴U¹⁵/Ω⁴)√L`) and the additive E-coefficient `cE ≥ 0`, the s-sum is

  `≤ 48·C·(H/Δ)·(G¹⁵U⁷⁵/(ΔΩ¹³) + Δ²G¹⁵U⁹⁵/(HΩ²⁷))`   (the faithful `t6' + t7'`),

provided the two E-part products are each dominated by a `t6'`/`t7'` block (`hEA`, `hEB`).  The
SHARP part is the green `ra_step4_ssum_collapse'`; the E-part `c_E·b·∑√n + c_E·dc·N` is summed by
`sum_sqrt_le` / `Σ1 = N`.

`hEA`/`hEB` hold for the `E_recon`/`E_drift` summands of `ρ` (`c_E ≍ ρ·ΔΩ/√L`) with room to spare;
the `E_cubic`/`E_p2` summands of `ρ` overshoot here and must enter via the `|v| ≤ C·V_s`
confinement instead. -/
theorem ra_step4_ssum_collapse_add
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ)
    (ℓ₁ L : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hLlo : 1 ≤ L)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hLW3 : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3)
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
    (b ev dc cE : ℝ)
    (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
    (hev : ev = (P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
                  * (S.Δ * S.Ω) / Real.sqrt L)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt L)
    (hcEnn : 0 ≤ cE)
    (hEA : cE * b * ((N : ℝ) * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
    (hEB : cE * dc * (N : ℝ)
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 95 / (P.H * S.Ω ^ 27))) :
    (∑ n ∈ Finset.Icc 1 N, weight4add b ev dc cE (n : ℝ))
      ≤ 48 * C * (P.H / S.Δ) *
          ( P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 95 / (P.H * S.Ω ^ 27) ) := by
  -- positivity scaffolding
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hCnn : 0 ≤ C := le_trans zero_le_one hC
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hevnn : 0 ≤ ev := by rw [hev]; positivity
  have hdcnn : 0 ≤ dc := by rw [hdc]; positivity
  -- abbreviations for the two faithful monomials and the half-RHS base
  set g75 : ℝ := P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13) with hg75
  set g90 : ℝ := S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) with hg90
  set g95 : ℝ := S.Δ ^ 2 * P.G ^ 15 * P.U ^ 95 / (P.H * S.Ω ^ 27) with hg95
  have hg75nn : 0 ≤ g75 := by rw [hg75]; positivity
  have hg95nn : 0 ≤ g95 := by rw [hg95]; positivity
  have hHΔnn : 0 ≤ P.H / S.Δ := by positivity
  have hg90le95 : g90 ≤ g95 := by
    rw [hg90, hg95, div_le_div_iff₀ (by positivity) (by positivity)]
    have hU : P.U ^ 90 ≤ P.U ^ 95 := pow_le_pow_right₀ hU1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hU
      (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * P.G ^ 15 * (P.H * S.Ω ^ 27))]
  -- ============ SHARP part: reuse `ra_step4_ssum_collapse'` ============
  have hsharp := ra_step4_ssum_collapse' (P := P) (S := S) h1 hΔreg hG1 hU1 hΔ1 hH1 hΩU hUbig
    N ℓ₁ L hℓ1lo hLlo hℓ1W hLW3 C hC hNcap b ev dc hb hev hdc
  -- `hsharp : ∑ weight4' ≤ 16·C·(H/Δ)·(g75 + g90)`, fold to base `(g75 + g95)`
  have hRle : (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ))
      ≤ 16 * C * (P.H / S.Δ) * (g75 + g95) := by
    refine le_trans hsharp ?_
    rw [← hg75, ← hg90]
    have : 16 * C * (P.H / S.Δ) * (g75 + g90) ≤ 16 * C * (P.H / S.Δ) * (g75 + g95) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hg90le95]
    exact this
  set base : ℝ := P.H / S.Δ * (g75 + g95) with hbase
  have hbasenn : 0 ≤ base := by rw [hbase]; positivity
  have hRle' : (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ)) ≤ 16 * C * base := by
    rw [hbase]; refine le_trans hRle (le_of_eq ?_); ring
  -- ============ pointwise split of the additive weight ============
  have hpt : ∀ n ∈ Finset.Icc 1 N, weight4add b ev dc cE (n : ℝ)
      = weight4' b ev dc (n : ℝ) + (b + dc / Real.sqrt (n : ℝ))
        + (cE * b * Real.sqrt (n : ℝ) + cE * dc) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hsqne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqpos
    rw [weight4add, weight4']
    field_simp
    ring
  -- ∑ (b + dc/√n) ≤ ∑ weight4'
  have hbdc_le : (∑ n ∈ Finset.Icc 1 N, (b + dc / Real.sqrt (n : ℝ)))
      ≤ ∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hbdcnn : 0 ≤ b + dc / Real.sqrt (n : ℝ) := by positivity
    have hfac : 0 ≤ ev / Real.sqrt (n : ℝ) := by positivity
    rw [weight4']
    nlinarith [mul_nonneg hfac hbdcnn]
  -- E-part: c_E·b·∑√n + c_E·dc·N
  have hEsqrt : (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ))
      ≤ cE * b * ((N : ℝ) * Real.sqrt (N : ℝ)) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ))
        = cE * b * ∑ n ∈ Finset.Icc 1 N, Real.sqrt (n : ℝ) := by
      rw [Finset.mul_sum]
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (sum_sqrt_le N) (mul_nonneg hcEnn hbnn)
  have hEconst : (∑ _n ∈ Finset.Icc 1 N, cE * dc) = cE * dc * (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  -- controlled split of the additive sum into the three sub-sums
  have e1 : (∑ n ∈ Finset.Icc 1 N, weight4add b ev dc cE (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, (weight4' b ev dc (n : ℝ) + (b + dc / Real.sqrt (n : ℝ))))
        + (∑ n ∈ Finset.Icc 1 N, (cE * b * Real.sqrt (n : ℝ) + cE * dc)) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  have e2 : (∑ n ∈ Finset.Icc 1 N, (weight4' b ev dc (n : ℝ) + (b + dc / Real.sqrt (n : ℝ))))
      = (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ))
        + (∑ n ∈ Finset.Icc 1 N, (b + dc / Real.sqrt (n : ℝ))) := Finset.sum_add_distrib
  have e3 : (∑ n ∈ Finset.Icc 1 N, (cE * b * Real.sqrt (n : ℝ) + cE * dc))
      = (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ)) + cE * dc * (N : ℝ) := by
    rw [Finset.sum_add_distrib, hEconst]
  rw [e1, e2, e3]
  -- assemble
  have hsharp_total : (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ))
      + (∑ n ∈ Finset.Icc 1 N, (b + dc / Real.sqrt (n : ℝ)))
      ≤ 32 * C * base := by
    have := add_le_add hRle' (le_trans hbdc_le hRle')
    linarith [this]
  have hEA' : (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ))
      ≤ 8 * C * (P.H / S.Δ) * g75 := le_trans hEsqrt (by rw [hg75]; exact hEA)
  have hEB' : cE * dc * (N : ℝ) ≤ 8 * C * (P.H / S.Δ) * g95 := by rw [hg95]; exact hEB
  -- 8·C·(H/Δ)·g75 + 8·C·(H/Δ)·g95 = 8·C·base
  have hEsum : 8 * C * (P.H / S.Δ) * g75 + 8 * C * (P.H / S.Δ) * g95 = 8 * C * base := by
    rw [hbase]; ring
  have hfinal : 48 * C * (P.H / S.Δ) * (g75 + g95) = 48 * C * base := by rw [hbase]; ring
  rw [hfinal]
  -- (∑w4' + ∑bdc) + (∑cEb√n + cEdc·N) ≤ 32·C·base + 8·C·base = 40·C·base ≤ 48·C·base
  have hCbase : 0 ≤ C * base := mul_nonneg hCnn hbasenn
  linarith [hsharp_total, hEA', hEB', hEsum, hCbase]

end Squarefree
