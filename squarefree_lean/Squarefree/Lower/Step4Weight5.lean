import Squarefree.Lower.Step4SsumAdd

/-!
# §5 Step-4 five-slot additive collapse (`weight5`)

Extension of the additive Step-4 collapse (`Step4SsumAdd` / `Step4RangeAdd`) by two further
v-count slots: a linear-in-`n` slot `cE₂·n` and a constant slot `cC`, giving the five-slot weight

  `weight5 b ev dc cE cE₂ cC n = (2 + ev/√n + cE·√n + cE₂·n + cC)·(b + dc/√n)`.

The s-sum splits pointwise as `weight5 = weight4add + (cE₂·n + cC)·(b + dc/√n)`:

* the four-slot part is the green `ra_step4_ssum_collapse_add`
  (`≤ 48·C·(H/Δ)·(t6' + t7')`);
* the new part expands (via `n/√n = √n`) to the four products
  `cE₂·b·n + cE₂·dc·√n + cC·b + cC·dc/√n`, summed by `step4_ssum`
  (`Σn ≤ N²`, `Σ√n ≤ N√N`, `Σ1 = N`, `Σ1/√n ≤ 2√N`) and absorbed by the four caller
  obligations `hEC`–`hEF` into the faithful `t6'`/`t7'` blocks.

Total: `≤ 80·C·(H/Δ)·( G¹⁵U⁷⁵/(ΔΩ¹³) + Δ²G¹⁵U⁹⁰/(HΩ²⁷) )`.  `ra_step4_range_add5` is the
fibrewise-card wiring (clone of `ra_step4_range_add`) with conclusion constant `80·K·C·(H/Δ)`.
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- The TRUE-ℓ Step-4 s-sum integrand, **five-slot ADDITIVE form**: the SHARP near-integer band
v-count `(1 + ev/√n)` widened by the additive perturbation room `cE·√n`, the linear room `cE₂·n`
and the constant room `cC`, paired with the bare smooth count factor `(b + dc/√n)`:

  `weight5 b ev dc cE cE₂ cC n = (2 + ev/√n + cE·√n + cE₂·n + cC)·(b + dc/√n)`. -/
noncomputable def weight5 (b ev dc cE cE₂ cC : ℝ) (n : ℝ) : ℝ :=
  (2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC) * (b + dc / Real.sqrt n)

/-- g90 variant of `ra_step4_ssum_collapse_add` (Step4SsumAdd): identical statement except the
second monomial block is the faithful `Δ²G¹⁵U⁹⁰/(HΩ²⁷)` — the sharp `ra_step4_ssum_collapse'`
natively outputs `g75 + g90`, so no fold up to `U⁹⁵` is needed. -/
private theorem ra_step4_ssum_collapse_add90
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
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27))) :
    (∑ n ∈ Finset.Icc 1 N, weight4add b ev dc cE (n : ℝ))
      ≤ 48 * C * (P.H / S.Δ) *
          ( P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) ) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hCnn : 0 ≤ C := le_trans zero_le_one hC
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hevnn : 0 ≤ ev := by rw [hev]; positivity
  have hdcnn : 0 ≤ dc := by rw [hdc]; positivity
  set g75 : ℝ := P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13) with hg75
  set g90 : ℝ := S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) with hg90
  have hg75nn : 0 ≤ g75 := by rw [hg75]; positivity
  have hg90nn : 0 ≤ g90 := by rw [hg90]; positivity
  have hsharp := ra_step4_ssum_collapse' (P := P) (S := S) h1 hΔreg hG1 hU1 hΔ1 hH1 hΩU hUbig
    N ℓ₁ L hℓ1lo hLlo hℓ1W hLW3 C hC hNcap b ev dc hb hev hdc
  set base : ℝ := P.H / S.Δ * (g75 + g90) with hbase
  have hbasenn : 0 ≤ base := by rw [hbase]; positivity
  have hRle' : (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ)) ≤ 16 * C * base := by
    rw [hbase, hg75, hg90]
    refine le_trans hsharp (le_of_eq ?_); ring
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
  have hEsqrt : (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ))
      ≤ cE * b * ((N : ℝ) * Real.sqrt (N : ℝ)) := by
    have hrw : (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ))
        = cE * b * ∑ n ∈ Finset.Icc 1 N, Real.sqrt (n : ℝ) := by
      rw [Finset.mul_sum]
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (sum_sqrt_le N) (mul_nonneg hcEnn hbnn)
  have hEconst : (∑ _n ∈ Finset.Icc 1 N, cE * dc) = cE * dc * (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
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
  have hsharp_total : (∑ n ∈ Finset.Icc 1 N, weight4' b ev dc (n : ℝ))
      + (∑ n ∈ Finset.Icc 1 N, (b + dc / Real.sqrt (n : ℝ)))
      ≤ 32 * C * base := by
    have := add_le_add hRle' (le_trans hbdc_le hRle')
    linarith [this]
  have hEA' : (∑ n ∈ Finset.Icc 1 N, cE * b * Real.sqrt (n : ℝ))
      ≤ 8 * C * (P.H / S.Δ) * g75 := le_trans hEsqrt (by rw [hg75]; exact hEA)
  have hEB' : cE * dc * (N : ℝ) ≤ 8 * C * (P.H / S.Δ) * g90 := by rw [hg90]; exact hEB
  have hEsum : 8 * C * (P.H / S.Δ) * g75 + 8 * C * (P.H / S.Δ) * g90 = 8 * C * base := by
    rw [hbase]; ring
  have hfinal : 48 * C * (P.H / S.Δ) * (g75 + g90) = 48 * C * base := by rw [hbase]; ring
  rw [hfinal]
  have hCbase : 0 ≤ C * base := mul_nonneg hCnn hbasenn
  linarith [hsharp_total, hEA', hEB', hEsum, hCbase]

/-- **§5 Step-4 per-pair s-sum collapse (five-slot ADDITIVE form).**

For the five-slot weight `(2 + ev/√n + cE√n + cE₂n + cC)(b + dc/√n)` summed over `1 ≤ n ≤ N`,
with the SHARP-band coefficients of `ra_step4_ssum_collapse_add` and the additional slot
coefficients `cE₂, cC ≥ 0`, the s-sum is

  `≤ 80·C·(H/Δ)·( G¹⁵U⁷⁵/(ΔΩ¹³) + Δ²G¹⁵U⁹⁰/(HΩ²⁷) )`,

provided the six absorb products `hEA`–`hEF` are each dominated by a `t6'`/`t7'` block.  The
four-slot part is `ra_step4_ssum_collapse_add`; the new part `cE₂·b·Σn + cE₂·dc·Σ√n + cC·b·Σ1
+ cC·dc·Σ1/√n` is summed by `step4_ssum`. -/
theorem ra_step4_ssum_collapse5
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ)
    (ℓ₁ L : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hLlo : 1 ≤ L)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hLW3 : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3)
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
    (b ev dc cE cE₂ cC : ℝ)
    (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
    (hev : ev = (P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
                  * (S.Δ * S.Ω) / Real.sqrt L)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt L)
    (hcEnn : 0 ≤ cE) (hcE₂nn : 0 ≤ cE₂) (hcCnn : 0 ≤ cC)
    (hEA : cE * b * ((N : ℝ) * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
    (hEB : cE * dc * (N : ℝ)
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (hEC : cE₂ * b * (N : ℝ) ^ 2
        ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
    (hED : cE₂ * dc * ((N : ℝ) * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (hEE : cC * b * (N : ℝ)
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (hEF : cC * dc * (2 * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27))) :
    (∑ n ∈ Finset.Icc 1 N, weight5 b ev dc cE cE₂ cC (n : ℝ))
      ≤ 80 * C * (P.H / S.Δ) *
          ( P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) ) := by
  -- positivity scaffolding
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hCnn : 0 ≤ C := le_trans zero_le_one hC
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hdcnn : 0 ≤ dc := by rw [hdc]; positivity
  -- pointwise split of the five-slot weight (uses `n/√n = √n`)
  have hpt : ∀ n ∈ Finset.Icc 1 N, weight5 b ev dc cE cE₂ cC (n : ℝ)
      = weight4add b ev dc cE (n : ℝ)
        + (cE₂ * b * (n : ℝ) + cE₂ * dc * Real.sqrt (n : ℝ) + cC * b
            + cC * dc / Real.sqrt (n : ℝ)) := by
    intro n _hn
    have hds : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := Real.div_sqrt
    rw [weight5, weight4add]
    calc (2 + ev / Real.sqrt (n : ℝ) + cE * Real.sqrt (n : ℝ) + cE₂ * (n : ℝ) + cC)
          * (b + dc / Real.sqrt (n : ℝ))
        = (2 + ev / Real.sqrt (n : ℝ) + cE * Real.sqrt (n : ℝ)) * (b + dc / Real.sqrt (n : ℝ))
          + (cE₂ * b * (n : ℝ) + cE₂ * dc * ((n : ℝ) / Real.sqrt (n : ℝ)) + cC * b
              + cC * dc / Real.sqrt (n : ℝ)) := by ring
      _ = _ := by rw [hds]
  have e1 : (∑ n ∈ Finset.Icc 1 N, weight5 b ev dc cE cE₂ cC (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, weight4add b ev dc cE (n : ℝ))
        + (∑ n ∈ Finset.Icc 1 N, (cE₂ * b * (n : ℝ) + cE₂ * dc * Real.sqrt (n : ℝ) + cC * b
            + cC * dc / Real.sqrt (n : ℝ))) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  -- four-slot part: the green additive collapse
  have hmain := ra_step4_ssum_collapse_add90 (P := P) (S := S) h1 hΔreg hG1 hU1 hΔ1 hH1 hΩU
    hUbig N ℓ₁ L hℓ1lo hLlo hℓ1W hLW3 C hC hNcap b ev dc cE hb hev hdc hcEnn hEA hEB
  -- new part: the elementary four-sum bound
  have hextra : (∑ n ∈ Finset.Icc 1 N, (cE₂ * b * (n : ℝ) + cE₂ * dc * Real.sqrt (n : ℝ)
            + cC * b + cC * dc / Real.sqrt (n : ℝ)))
      ≤ cE₂ * b * (N : ℝ) ^ 2 + cE₂ * dc * ((N : ℝ) * Real.sqrt (N : ℝ)) + cC * b * (N : ℝ)
        + cC * dc * (2 * Real.sqrt (N : ℝ)) :=
    step4_ssum (cE₂ * b) (cE₂ * dc) (cC * b) (cC * dc)
      (mul_nonneg hcE₂nn hbnn) (mul_nonneg hcE₂nn hdcnn)
      (mul_nonneg hcCnn hdcnn) N
  -- nonnegativity of the two faithful monomial blocks
  have hm75 : 0 ≤ C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by positivity
  have hm95 : 0 ≤ C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
    positivity
  -- assemble: 48 + (8 + 8 + 8 + 8) = 80 with room (56·g75 + 72·g95 ≤ 80·(g75 + g95))
  rw [e1]
  linarith [hmain, hextra, hEC, hED, hEE, hEF, hm75, hm95]

/-- **§5 Step-4 per-pair RANGE bound — five-slot ADDITIVE assembly.**

A finite range set `Rng` of admissible large-defect `r`-values, each carrying an extracted index
`sOf r` with `1 ≤ sOf r ≤ N`, with each `s`-fibre of size `≤ K · weight5 b ev dc cE cE₂ cC n`
(the five-slot per-`(s,v)` count) and the six absorb products `hEA`–`hEF` dominated by the
faithful `t6'`/`t7'` blocks, has total cardinality

  `≤ 80·K·C·(H/Δ)·( G¹⁵U⁷⁵/(ΔΩ¹³) + Δ²G¹⁵U⁹⁰/(HΩ²⁷) )`.

The s-sum is discharged by the five-slot collapse `ra_step4_ssum_collapse5`. -/
theorem ra_step4_range_add5
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (N : ℕ)
    (ℓ₁ L : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hLlo : 1 ≤ L)
    (hℓ1W : ℓ₁ ≤ 130 * (P.G * P.U ^ 5)) (hLW3 : L ≤ 130 ^ 3 * (P.G * P.U ^ 5) ^ 3)
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N : ℝ) ≤ C * ℓ₁ ^ 2 * L * P.U ^ 10 / S.Ω ^ 8)
    (b ev dc cE cE₂ cC : ℝ)
    (hb : b = P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
    (hev : ev = (P.G ^ 4 * P.U ^ 20 / S.Δ + S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14))
                  * (S.Δ * S.Ω) / Real.sqrt L)
    (hdc : dc = P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt L)
    (hcEnn : 0 ≤ cE) (hcE₂nn : 0 ≤ cE₂) (hcCnn : 0 ≤ cC)
    (hEA : cE * b * ((N : ℝ) * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
    (hEB : cE * dc * (N : ℝ)
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (hEC : cE₂ * b * (N : ℝ) ^ 2
        ≤ 8 * C * (P.H / S.Δ) * (P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
    (hED : cE₂ * dc * ((N : ℝ) * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (hEE : cC * b * (N : ℝ)
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (hEF : cC * dc * (2 * Real.sqrt (N : ℝ))
        ≤ 8 * C * (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    (K : ℝ) (hK : 0 ≤ K)
    (Rng : Finset ℕ) (sOf : ℕ → ℕ)
    (hsmaps : ∀ r ∈ Rng, sOf r ∈ Finset.Icc 1 N)
    (hfiber : ∀ n ∈ Finset.Icc 1 N,
        ((Rng.filter (fun r => sOf r = n)).card : ℝ)
          ≤ K * weight5 b ev dc cE cE₂ cC (n : ℝ)) :
    (Rng.card : ℝ)
      ≤ 80 * K * C * (P.H / S.Δ) *
          ( P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) ) := by
  classical
  have hmaps : (Rng : Set ℕ).MapsTo sOf (Finset.Icc 1 N) := fun r hr => hsmaps r hr
  have hcard : Rng.card = ∑ n ∈ Finset.Icc 1 N, (Rng.filter (fun r => sOf r = n)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hcardR : (Rng.card : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ((Rng.filter (fun r => sOf r = n)).card : ℝ) := by
    rw [hcard]; push_cast; rfl
  have hsum_le : (∑ n ∈ Finset.Icc 1 N, ((Rng.filter (fun r => sOf r = n)).card : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 N, K * weight5 b ev dc cE cE₂ cC (n : ℝ) :=
    Finset.sum_le_sum hfiber
  rw [hcardR]
  refine le_trans hsum_le ?_
  rw [← Finset.mul_sum]
  have hcollapse := ra_step4_ssum_collapse5 (P := P) (S := S) h1 hΔreg hG1 hU1 hΔ1 hH1 hΩU
    hUbig N ℓ₁ L hℓ1lo hLlo hℓ1W hLW3 C hC hNcap b ev dc cE cE₂ cC hb hev hdc hcEnn hcE₂nn
    hcCnn hEA hEB hEC hED hEE hEF
  calc K * (∑ n ∈ Finset.Icc 1 N, weight5 b ev dc cE cE₂ cC (n : ℝ))
      ≤ K * (80 * C * (P.H / S.Δ) *
          ( P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) )) :=
        mul_le_mul_of_nonneg_left hcollapse hK
    _ = 80 * K * C * (P.H / S.Δ) *
          ( P.G ^ 15 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 15 * P.U ^ 90 / (P.H * S.Ω ^ 27) ) := by ring

end Squarefree
