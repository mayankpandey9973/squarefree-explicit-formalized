import Squarefree.Bracket.Sec7ErrBound
import Squarefree.Bracket.Sec7PhiDeriv
import Squarefree.Bracket.Sec7PhiSmooth
import Squarefree.Counting.Bands

/-!
# §7 zero-carry scale and per-triple count (plan nodes N12–N13) — Phase-1c SIGNATURES ONLY

md 1686–1781, the branch `ρ₀ = 0`: the actual scale `T_{ρ,u} = |B_{ρ,u}| + |C*P·T₃/R³|`
(md 1697–1700), the Wronskian calibration `|Φ'| ≪ T_{ρ,u}/R`, `|Φ'| + R|Φ''| ≍ T_{ρ,u}/R`
with `O(1)` zeros of `Φ', Φ''` (md 1730–38) under the subordination of the eq-(7.5)
remainder (md 1701–29), and the per-triple Lemma-4.2 application with its five
evaluations and (7.6) (md 1740–81; sympy-banked, tools/sec7_ledger.py).

TRAP-3 (plan): md 1717's ambient `x ≫ GU¹⁰` is NOT available on the strip.  All
subordination inputs are stated as `X^{-c}`-smallness hypotheses in monomial form
(`sec7_cSub·(W⁴Ω²) ≤ √(Hx)`, `sec7_cSub·(GΩ⁶U³) ≤ H`, …), never the literal.

## Constant ledger additions (absolute constants; tools/sec7_ledger.py)
* `sec7_cCal = 10⁹` (ARB-1: role NARROWED) — the N8-conclusion / N13 `hδ`-threshold
  constant only; `≥ max(8·sec7_cTay, sec7_cN6) = 10⁸`.
* ARB-1 (A4) N12 split — the calibration constants are now per-statement:
  `sec7_cDer = 10⁹` (N12a upper, content `2.6·10⁸`), `sec7_cLow = 10⁷` (N12b Wronskian
  lower), `sec7_cTup = 10¹⁷` (N12d upper, content `3.0·10¹⁶`), `sec7_cTlo = 10¹²`
  (N12d lower, content `7.6·10¹¹`).
* `sec7_KZero = 100` — the `O(1)` bound on the zeros of `Φ'_{ρ,u}` and `Φ''_{ρ,u}`;
  N12c is now the `Sec7ZeroHyp.few_critical` FIELD (ARB-1, A4: produced at the concrete
  call site, not provable from the abstract bundle).
* `sec7_cN13 = 10⁴³` (ARB-1) — the N13 conclusion constant; content
  `112·(cu/cl)·(K+1)·cTup ≈ 9.4·10⁴¹` (engine `112`, slack-calibration ratio, piece
  count, and the N12d-upper `cTup`); the in-tree engine is log-free.
* AM-2 (G1/U4): N12/N13 are PARAMETERIZED by a dyadic sub-window `(p q : ℕ)` with
  `[p,q] ⊆ [⌈R/72⌉,⌊16R⌋]` and `q ≤ 2p`; the 11-window dyadic sum over `[R/72,16R]`
  happens in the triple split (BoxSum).
* `sec7_cSub = 2·10⁵⁷` (Φ″ re-pin 2026-06-17, was 10⁵⁵; `≥ 2.6·cErr`) — the
  subordination-hypothesis constant of `hsub1/hsub2/hrel`; capped by `sec7_cSub_le_X_2_25`
  at `2¹⁹² = X^{2/25} ≈ 6.3·10⁵⁷` (3.14× margin), well within corner capacity `10^{64.3}`.
  cSub is what keeps `cErr` OUT of `cDer`/`cTup`.
-/

open Classical Finset Squarefree.FiniteDiff

namespace Squarefree

/-- N8-conclusion / N13 `hδ`-threshold constant (ledger; ARB-1 role narrowed:
`≥ max(8·sec7_cTay, sec7_cN6) = 10⁸`). -/
def sec7_cCal : ℝ := 10 ^ 15

/-- N12a derivative-upper calibration constant (ARB-1 split; content `2.6·10⁸`). -/
def sec7_cDer : ℝ := 10 ^ 9

/-- N12b Wronskian-lower calibration constant (ARB-1 split). -/
def sec7_cLow : ℝ := 10 ^ 7

/-- N12d `T_{ρ,u}`-upper evaluation constant (ARB-1 split; content `3.0·10¹⁶`). -/
def sec7_cTup : ℝ := 10 ^ 17

/-- N12d `T_{ρ,u}`-lower evaluation constant (ARB-1 split; content `7.6·10¹¹`). -/
def sec7_cTlo : ℝ := 10 ^ 12

/-- `O(1)` bound for the zero counts of `Φ'_{ρ,u}`, `Φ''_{ρ,u}` (md 1737–38; ledger). -/
def sec7_KZero : ℕ := 100

/-- N13 conclusion constant (ledger; ARB-1: content `112·(cu/cl)·(K+1)·cTup ≈ 9.4·10⁴¹`). -/
def sec7_cN13 : ℝ := 10 ^ 43

/-- Subordination-hypothesis constant of `Sec7ZeroHyp.hsub1/hsub2/hrel` (ARB-1:
`≥ 2.6·cErr`; N11 re-pin 2026-06-12: `cErr = 10⁴²` forces `cSub ≥ 2.6·10⁴²`).
**Φ″ re-pin 2026-06-17: `10⁵⁵ → 2·10⁵⁷`** — the m=3 (Φ″) domination ceiling is `2.2·10⁻¹⁰·cSub`,
and the honest e₃ order-6 residual const (`3.9·10³⁰`, vs the stale `8e7`-based `10²⁹`) forces
`cErr3 ≥ 9.6·10⁴⁶`, needing `cSub ≥ 4.4·10⁵⁶`.  `2·10⁵⁷ ≤ 2¹⁹² = X^{2/25}` (the `sec7_cSub_le_X_2_25`
cap, 3.14× margin under `hX24`) and well within the binding-corner capacity `10^{64.3}`. -/
def sec7_cSub : ℝ := 2 * 10 ^ 57

theorem sec7_cCal_pos : (0:ℝ) < sec7_cCal := by norm_num [sec7_cCal]
theorem sec7_cDer_pos : (0:ℝ) < sec7_cDer := by norm_num [sec7_cDer]
theorem sec7_cLow_pos : (0:ℝ) < sec7_cLow := by norm_num [sec7_cLow]
theorem sec7_cTup_pos : (0:ℝ) < sec7_cTup := by norm_num [sec7_cTup]
theorem sec7_cTlo_pos : (0:ℝ) < sec7_cTlo := by norm_num [sec7_cTlo]
theorem sec7_cN13_pos : (0:ℝ) < sec7_cN13 := by norm_num [sec7_cN13]
theorem sec7_cSub_pos : (0:ℝ) < sec7_cSub := by norm_num [sec7_cSub]

private theorem Sec7MonExp.Cstar_lower_tight {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) :
    (21 / 4096 : ℝ) ≤ |ME.Cstar| := by
  rw [ME.Cstar_eq]
  have h1 := ME.c₁_window.1
  have h2 := ME.c₂_window.1
  have habs : |-(21 / 16) * ME.c₁ * ME.c₂| = (21 / 16 : ℝ) * |ME.c₁| * |ME.c₂| := by
    rw [abs_mul, abs_mul]
    norm_num
  rw [habs]
  nlinarith [abs_nonneg ME.c₁, abs_nonneg ME.c₂]

private theorem Sec7MonExp.Cstar_upper_tight {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) :
    |ME.Cstar| ≤ (21 : ℝ) := by
  rw [ME.Cstar_eq]
  have h1 := ME.c₁_window.2
  have h2 := ME.c₂_window.2
  have habs : |-(21 / 16) * ME.c₁ * ME.c₂| = (21 / 16 : ℝ) * |ME.c₁| * |ME.c₂| := by
    rw [abs_mul, abs_mul]
    norm_num
  rw [habs]
  nlinarith [abs_nonneg ME.c₁, abs_nonneg ME.c₂]

private theorem sec7_Pprod_ge_one_of_box {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    (1 : ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
  have a1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hbox.1.1
  have a2 : (1 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hbox.2.1.1
  have a3 : (1 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hbox.2.2.1
  unfold sec7_Pprod
  have h12 : (1 : ℝ) ≤ (h₁ : ℝ) * h₂ := by nlinarith
  nlinarith

private theorem sec7_Bcoef_zero_upper {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃) (hρ₀ : ρ₀ = 0)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) :
    |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃| ≤
      4 * sec7_cFib * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
        3 * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT2 : 0 < S.T₂ := sec7_T₂_pos S
  have hTR : 0 < S.T₁ / S.R := div_pos hT1 hR
  have hT2R : 0 < S.T₂ / S.R ^ 2 := by positivity
  have hh₁ : 1 ≤ h₁ := hbox.1.1
  have hh₂ : 1 ≤ h₂ := hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := hbox.2.2.1
  have a1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hh₁
  have a2 : (1 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hh₂
  have a3 : (1 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hh₃
  have hSv0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
    unfold sec7_hSum
    linarith
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_Pprod_ge_one_of_box (W := W) hbox
    linarith
  have hA0 : 0 ≤ sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) := by positivity
  have hB0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by
    have hT3 : 0 < S.T₃ := sec7_T₃_pos S
    positivity
  have hfib1_nonneg : 0 ≤ 1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) := by positivity
  have hfib2_nonneg : 0 ≤ 1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) := by positivity
  have hfib3_nonneg : 0 ≤ 1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) := by positivity
  have hc1 : |ME.c₁| ≤ 4 := ME.c₁_window.2
  have hsum_abs :
      |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| ≤
        sec7_cFib * (sec7_hSum h₁ h₂ h₃ +
          3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2)) := by
    have htri :
        |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| ≤
        (h₁ : ℝ) * |(u₁ : ℝ) - ρ₁| + (h₂ : ℝ) * |(u₂ : ℝ) - ρ₂| +
          (h₃ : ℝ) * |(u₃ : ℝ) - ρ₃| := by
      calc
        |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
            (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)|
            ≤ |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁)| +
                |(h₂ : ℝ) * ((u₂ : ℝ) - ρ₂)| +
                |(h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| := by
              have h := abs_add_le ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) +
                (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂)) ((h₃ : ℝ) * ((u₃ : ℝ) - ρ₃))
              have h' := abs_add_le ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁))
                ((h₂ : ℝ) * ((u₂ : ℝ) - ρ₂))
              linarith
          _ = (h₁ : ℝ) * |(u₁ : ℝ) - ρ₁| + (h₂ : ℝ) * |(u₂ : ℝ) - ρ₂| +
                (h₃ : ℝ) * |(u₃ : ℝ) - ρ₃| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ (h₁ : ℝ)),
                abs_of_nonneg (by linarith : 0 ≤ (h₂ : ℝ)),
                abs_of_nonneg (by linarith : 0 ≤ (h₃ : ℝ))]
    calc
      |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
          (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)|
          ≤ (h₁ : ℝ) * |(u₁ : ℝ) - ρ₁| + (h₂ : ℝ) * |(u₂ : ℝ) - ρ₂| +
              (h₃ : ℝ) * |(u₃ : ℝ) - ρ₃| := htri
      _ ≤ (h₁ : ℝ) * (sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))) +
            (h₂ : ℝ) * (sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))) +
            (h₃ : ℝ) * (sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) := by
          gcongr
      _ = sec7_cFib * (sec7_hSum h₁ h₂ h₃ +
          3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2)) := by
          unfold sec7_hSum sec7_Pprod
          ring
  calc
    |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃|
        ≤ 4 * (S.T₁ / S.R) *
            (sec7_cFib * (sec7_hSum h₁ h₂ h₃ +
              3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 2))) := by
        unfold Sec7MonExp.Bcoef
        subst ρ₀
        rw [Int.cast_zero]
        have hmul :
            |ME.c₁ * (S.T₁ / S.R) *
              (((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
                (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (0 : ℝ) * sec7_hSum h₁ h₂ h₃)| =
              |ME.c₁| * (S.T₁ / S.R) *
                |(h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
                  (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)| := by
          have hzero :
              (((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
                (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) - (0 : ℝ) * sec7_hSum h₁ h₂ h₃) =
                (h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) +
                  (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃) := by ring
          rw [hzero, abs_mul, abs_mul, abs_of_pos hTR]
        rw [hmul]
        nlinarith [mul_le_mul_of_nonneg_right hsum_abs hTR.le,
          mul_le_mul_of_nonneg_right hc1
            (mul_nonneg hTR.le (abs_nonneg ((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) +
              (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) + (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃))))]
    _ = 4 * sec7_cFib * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          3 * sec7_Pprod h₁ h₂ h₃ * (S.T₁ * S.T₂ / S.R ^ 3)) := by ring
    _ = 4 * sec7_cFib * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          3 * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
        rw [sec7_T₁_mul_T₂ S]

private theorem sec7_dyadic_window_bounds {P : Globals} {S : Scale P} {p q : ℕ} {r : ℝ}
    (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hr : r ∈ Set.Icc (p : ℝ) (q : ℝ)) :
    S.R / 72 ≤ r ∧ r ≤ 16 * S.R := by
  have hpqR : (p : ℝ) ≤ (q : ℝ) := le_trans hr.1 hr.2
  have hpq : p ≤ q := by exact_mod_cast hpqR
  have hpmem : (p : ℤ) ∈ Finset.Icc (p : ℤ) (q : ℤ) := by
    rw [Finset.mem_Icc]
    constructor
    · rfl
    · exact_mod_cast hpq
  have hqmem : (q : ℤ) ∈ Finset.Icc (p : ℤ) (q : ℤ) := by
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast hpq
    · rfl
  have hpwide := Finset.mem_Icc.mp (hwin hpmem)
  have hqwide := Finset.mem_Icc.mp (hwin hqmem)
  have hpR : S.R / 72 ≤ (p : ℝ) :=
    le_trans (Int.le_ceil (S.R / 72)) (by exact_mod_cast hpwide.1)
  have hqR : (q : ℝ) ≤ 16 * S.R :=
    le_trans (by exact_mod_cast hqwide.2) (Int.floor_le (16 * S.R))
  exact ⟨le_trans hpR hr.1, le_trans hr.2 hqR⟩

private theorem sec7_dyadic_window_mem_rWin {P : Globals} {S : Scale P} {W : ℝ} {p q : ℕ} {r : ℝ}
    (hW : 0 < W)
    (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hr : r ∈ Set.Icc (p : ℝ) (q : ℝ)) :
    r ∈ sec7_rWin S W := by
  have hb := sec7_dyadic_window_bounds (S := S) hwin hr
  have hpad0 : 0 ≤ W + W ^ 2 + W ^ 4 := by positivity
  simp only [sec7_rWin, Set.mem_Icc]
  constructor <;> linarith

private theorem sec7_hSum_le_three_Pprod_of_box {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_hSum h₁ h₂ h₃ ≤ 3 * sec7_Pprod h₁ h₂ h₃ := by
  have a1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hbox.1.1
  have a2 : (1 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hbox.2.1.1
  have a3 : (1 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hbox.2.2.1
  have h10 : (0 : ℝ) ≤ (h₁ : ℝ) := by linarith
  have h20 : (0 : ℝ) ≤ (h₂ : ℝ) := by linarith
  have h30 : (0 : ℝ) ≤ (h₃ : ℝ) := by linarith
  have h23 : (1 : ℝ) ≤ (h₂ : ℝ) * h₃ := by nlinarith
  have h13 : (1 : ℝ) ≤ (h₁ : ℝ) * h₃ := by nlinarith
  have h12 : (1 : ℝ) ≤ (h₁ : ℝ) * h₂ := by nlinarith
  have h1le : (h₁ : ℝ) ≤ (h₁ : ℝ) * h₂ * h₃ := by
    calc
      (h₁ : ℝ) ≤ (h₁ : ℝ) * ((h₂ : ℝ) * h₃) :=
        le_mul_of_one_le_right h10 h23
      _ = (h₁ : ℝ) * h₂ * h₃ := by ring
  have h2le : (h₂ : ℝ) ≤ (h₁ : ℝ) * h₂ * h₃ := by
    calc
      (h₂ : ℝ) ≤ (h₂ : ℝ) * ((h₁ : ℝ) * h₃) :=
        le_mul_of_one_le_right h20 h13
      _ = (h₁ : ℝ) * h₂ * h₃ := by ring
  have h3le : (h₃ : ℝ) ≤ (h₁ : ℝ) * h₂ * h₃ := by
    calc
      (h₃ : ℝ) ≤ (h₃ : ℝ) * ((h₁ : ℝ) * h₂) :=
        le_mul_of_one_le_right h30 h12
      _ = (h₁ : ℝ) * h₂ * h₃ := by ring
  unfold sec7_hSum sec7_Pprod
  linarith

private theorem sec7_hSum_sq_le_nine_W4_Pprod {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    (sec7_hSum h₁ h₂ h₃) ^ 2 ≤ 9 * W ^ 4 * sec7_Pprod h₁ h₂ h₃ := by
  have hW : (0 : ℝ) ≤ W := le_trans zero_le_one (sec7_W_ge_one hbox)
  have hS0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
    have hS3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
      sec7_hSum_ge3 hbox.1.1 hbox.2.1.1 hbox.2.2.1
    linarith
  have hSpp := sec7_hSum_le_three_Pprod_of_box hbox
  have hSw := sec7_hSum_le_3W4 hbox
  have hPP0 : 0 ≤ 3 * sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_Pprod_ge_one_of_box hbox
    positivity
  calc
    (sec7_hSum h₁ h₂ h₃) ^ 2
        = sec7_hSum h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ := by ring
    _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (3 * W ^ 4) :=
        mul_le_mul hSpp hSw hS0 hPP0
    _ = 9 * W ^ 4 * sec7_Pprod h₁ h₂ h₃ := by ring

private theorem sec7_T₁_div_R_eq_GΩ5_T₃ {P : Globals} (S : Scale P) :
    S.T₁ / S.R = (P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.T₁ Scale.T₃ Scale.F Scale.R
  field_simp

private theorem sec7_sqrt_Hx_mul_GΩ3_eq_R {P : Globals} (S : Scale P) :
    Real.sqrt (P.H * S.x) * P.G * S.Ω ^ 3 = S.R := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hHx : P.H * S.x = (P.H / S.Δ) ^ 2 := by
    unfold Scale.x
    field_simp
  rw [hHx, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ P.H / S.Δ)]
  unfold Scale.R
  field_simp

private theorem sec7_GΩ5_relErr_le_inv_cSub {P : Globals} {S : Scale P}
    (hsub2 : sec7_cSub * (P.G * S.Ω ^ 6 * P.U ^ 3) ≤ P.H) :
    P.G * S.Ω ^ 5 * sec7_relErr P S ≤ 1 / sec7_cSub := by
  have hH := P.H_pos
  have hc : 0 < sec7_cSub := sec7_cSub_pos
  have hmain : sec7_cSub * (P.G * S.Ω ^ 5 * sec7_relErr P S) ≤ 1 := by
    have hdiv := div_le_div_of_nonneg_right hsub2 hH.le
    calc
      sec7_cSub * (P.G * S.Ω ^ 5 * sec7_relErr P S)
          = sec7_cSub * (P.G * S.Ω ^ 6 * P.U ^ 3) / P.H := by
            unfold sec7_relErr
            field_simp
      _ ≤ P.H / P.H := hdiv
      _ = 1 := by field_simp
  rw [le_div_iff₀ hc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

private theorem sec7_W4_GΩ5_div_R_le_inv_cSub {P : Globals} {S : Scale P} {W : ℝ}
    (hsub1 : sec7_cSub * (W ^ 4 * S.Ω ^ 2) ≤ Real.sqrt (P.H * S.x)) :
    W ^ 4 * (P.G * S.Ω ^ 5) / S.R ≤ 1 / sec7_cSub := by
  have hR : 0 < S.R := sec7_R_pos S
  have hc : 0 < sec7_cSub := sec7_cSub_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hGΩ3 : 0 ≤ P.G * S.Ω ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hsub1 hGΩ3
  have hmain : sec7_cSub * (W ^ 4 * (P.G * S.Ω ^ 5)) ≤ S.R := by
    calc
      sec7_cSub * (W ^ 4 * (P.G * S.Ω ^ 5))
          = (sec7_cSub * (W ^ 4 * S.Ω ^ 2)) * (P.G * S.Ω ^ 3) := by ring
      _ ≤ Real.sqrt (P.H * S.x) * (P.G * S.Ω ^ 3) := hmul
      _ = S.R := by simpa [mul_assoc] using sec7_sqrt_Hx_mul_GΩ3_eq_R S
  have hdiv : sec7_cSub * (W ^ 4 * (P.G * S.Ω ^ 5) / S.R) ≤ 1 := by
    calc
      sec7_cSub * (W ^ 4 * (P.G * S.Ω ^ 5) / S.R)
          = sec7_cSub * (W ^ 4 * (P.G * S.Ω ^ 5)) / S.R := by ring
      _ ≤ S.R / S.R := div_le_div_of_nonneg_right hmain hR.le
      _ = 1 := by field_simp
  rw [le_div_iff₀ hc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv

private theorem sec7_relErr_le_inv_10_143 {P : Globals} {S : Scale P}
    (hrel : sec7_relErr P S * 10 ^ 143 ≤ 1) :
    sec7_relErr P S ≤ 1 / (10 : ℝ) ^ 143 := by
  have hpow : 0 < (10 : ℝ) ^ 143 := by positivity
  rw [le_div_iff₀ hpow]
  simpa [mul_comm] using hrel

private theorem sec7_relErrF_le_inv_10_143 {P : Globals} {S : Scale P}
    (hrel : sec7_relErrF P S * 10 ^ 143 ≤ 1) :
    sec7_relErrF P S ≤ 1 / (10 : ℝ) ^ 143 := by
  have hpow : 0 < (10 : ℝ) ^ 143 := by positivity
  rw [le_div_iff₀ hpow]
  simpa [mul_comm] using hrel


/- md 1572–76 (eq 7.3): "δ₁(h) := δ₀ + ST₁/R² = δ₀ + S/(Rx²G²Ω⁴)"
   (the two forms agree exactly: T₁/R = 1/(x²G²Ω⁴), ledger). -/
/-- **`δ₁(h)`** (md 1574): the per-triple proximity threshold `δ₀ + S·T₁/R²`. -/
noncomputable def sec7_delta1 (P : Globals) (S : Scale P) (h₁ h₂ h₃ : ℤ) : ℝ :=
  sec7_delta0 P S + sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2

/- md 1697–1700: "We use the actual scale  T_{ρ,u} := |B_{ρ,u}| + |C*P(T₃/R³)|". -/
/-- **The zero-branch scale `T_{ρ,u}`** (md 1697–1700). -/
noncomputable def Sec7MonExp.Tscale {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℝ :=
  |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃| +
    |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)|

/- Hypothesis bundle for the branch `ρ₀ = 0` (md 1686–1729): the envelope, the band/box/shift
   data of N9, the carry/fiber sizes (md 1556, 1560–70), global `C²`-smoothness of `Φ_{ρ,u}`
   (consumed by the bands engine; discharged at the concrete §3 call site), and the TRAP-3
   subordination smallness facts:
   md 1705–17: "h_Σ²T₁/R² ≪ PT₃/R³ because (h_Σ²T₁/R²)/(PT₃/R³) ≪ W⁴Ω²(Hx)^{-1/2} ≪ X^{-c}"
     — transcribed as `sec7_cSub·(W⁴Ω²) ≤ √(Hx)` (ratio identity sympy-banked);
   md 1718–29: "(h_ΣT₁R⁻¹)/(PT₃R⁻³) ≤ (h_Σ/P)GΩ⁵ ≪ GΩ⁵ and hence
     h_Σ(T₁/R)X^{-(1-g)/5+O(u)} ≪ PT₃/R³" — needs `GΩ⁵·relErr` small, transcribed as
     `sec7_cSub·(GΩ⁶U³) ≤ H` in the current TRAP-3 field, plus the strip-dispatched
     `relErr·10¹⁴³ ≤ 1` for absolute relErr terms. -/
/-- **Zero-branch hypothesis bundle** (md 1686–1729; TRAP-3 smallness forms). -/
structure Sec7ZeroHyp (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) (Ph : Sec7Phase P S W a)
    (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ) (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : Prop where
  env : Sec7Envelope P S W
  hj : sec7_jBand P S j
  hbox : sec7_shiftBox W h₁ h₂ h₃
  hW : 0 < W
  hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288
  hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)
  hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃
  hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃
  hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃
  /-- md 1686: "First suppose ρ₀ = 0." -/
  hρ₀ : ρ₀ = 0
  hρ₁ : |(ρ₁ : ℝ)| ≤ sec7_cCarry
  hρ₂ : |(ρ₂ : ℝ)| ≤ sec7_cCarry
  hρ₃ : |(ρ₃ : ℝ)| ≤ sec7_cCarry
  hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))
  hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))
  hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))
  hcd : ContDiffOn ℝ 2 (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    (Set.Ioo (S.R / 144 - 1) (40 * S.R + 1))
  /-- md 1705–17 in TRAP-3 form: `W⁴Ω²(Hx)^{-1/2} ≪ X^{-c}`. -/
  hsub1 : sec7_cSub * (W ^ 4 * S.Ω ^ 2) ≤ Real.sqrt (P.H * S.x)
  /-- md 1718–29 in TRAP-3 form for `relErr = (Ω/H)·U³`: `GΩ⁵·relErr ≪ X^{-c}`. -/
  hsub2 : sec7_cSub * (P.G * S.Ω ^ 6 * P.U ^ 3) ≤ P.H
  /-- The loosened f₁/f₃ residual scale is power-saving below the subordination floor:
  `G·Ω⁵·relErrF ≤ 1/cSub` (relErrF = X^{-19/100}, band+admissibility; discharged at the
  construction site by `sec7_zero_hGΩ5F`). Replaces the old `relErr·G·U²` subordination form. -/
  hGΩ5F : P.G * S.Ω ^ 5 * sec7_relErrF P S ≤ 1 / sec7_cSub
  /-- Strip smallness for the faithful `relErr = (Ω/H)·U³` scale. -/
  hrel : sec7_relErr P S * 10 ^ 143 ≤ 1
  /-- Strip smallness for the loosened f₁/f₃ residual scale. -/
  hrelF : sec7_relErrF P S * 10 ^ 143 ≤ 1

private theorem sec7_Cbase_le_Tscale_tight {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) ≤
      200 * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hPP1 : (1 : ℝ) ≤ sec7_Pprod h₁ h₂ h₃ :=
    sec7_Pprod_ge_one_of_box hbox
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by linarith
  have hCterm_eq :
      |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)| =
        |ME.Cstar| * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hPP0, abs_of_pos (div_pos hT3 (pow_pos hR 3))]
    ring
  have hTge :
      (21 / 4096 : ℝ) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) ≤
        ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
    calc
      (21 / 4096 : ℝ) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))
          ≤ |ME.Cstar| * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
            gcongr
            exact ME.Cstar_lower_tight
      _ = |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)| := hCterm_eq.symm
      _ ≤ ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
            unfold Sec7MonExp.Tscale
            linarith [abs_nonneg (ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)]
  have hTnn : 0 ≤ ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
    unfold Sec7MonExp.Tscale
    positivity
  calc
    sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)
        = (4096 / 21 : ℝ) *
            ((21 / 4096 : ℝ) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by ring
    _ ≤ (4096 / 21 : ℝ) * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
          exact mul_le_mul_of_nonneg_left hTge (by norm_num)
    _ ≤ 200 * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
          nlinarith

private theorem sec7_zero_errScale_subordinate {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) :
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ ≤
      1000 * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_Pprod_ge_one_of_box Hyp.hbox
    linarith
  have hC0nn : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
  have hC0T := sec7_Cbase_le_Tscale_tight (ME := ME) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) Hyp.hbox
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hrelF0 : 0 ≤ sec7_relErrF P S := (sec7_relErrF_pos P S).le
  have hT1id := sec7_T₁_div_R_eq_GΩ5_T₃ S
  have hSlePP := sec7_hSum_le_three_Pprod_of_box Hyp.hbox
  have hGrel := sec7_GΩ5_relErr_le_inv_cSub (P := P) (S := S) Hyp.hsub2
  have hGrelF := Hyp.hGΩ5F
  have hGrel0 : 0 ≤ P.G * S.Ω ^ 5 * sec7_relErr P S :=
    mul_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hrel0
  have hGrelF0 : 0 ≤ P.G * S.Ω ^ 5 * sec7_relErrF P S :=
    mul_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hrelF0
  have hArel :
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErr P S ≤
        (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErr P S
          = sec7_hSum h₁ h₂ h₃ *
              ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) * sec7_relErr P S := by rw [hT1id]
      _ = sec7_hSum h₁ h₂ h₃ * (P.G * S.Ω ^ 5 * sec7_relErr P S) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (1 / sec7_cSub) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hArelF :
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S ≤
        (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S
          = sec7_hSum h₁ h₂ h₃ *
              ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) * sec7_relErrF P S := by rw [hT1id]
      _ = sec7_hSum h₁ h₂ h₃ * (P.G * S.Ω ^ 5 * sec7_relErrF P S) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (1 / sec7_cSub) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hrel := sec7_relErr_le_inv_10_143 Hyp.hrel
  have hrelF := sec7_relErrF_le_inv_10_143 Hyp.hrelF
  have hCrel :
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S ≤
        (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S
          ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (1 / (10 : ℝ) ^ 143) := by
            gcongr
      _ = (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hCrelF :
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S ≤
        (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S
          ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (1 / (10 : ℝ) ^ 143) := by
            gcongr
      _ = (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hSsq := sec7_hSum_sq_le_nine_W4_Pprod Hyp.hbox
  have hWsub := sec7_W4_GΩ5_div_R_le_inv_cSub (P := P) (S := S) Hyp.hsub1
  have hGΩR0 : 0 ≤ (P.G * S.Ω ^ 5) / S.R :=
    div_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hR.le
  have hE2 :
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 ≤
        (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2
          = (sec7_hSum h₁ h₂ h₃) ^ 2 * (S.T₁ / S.R) / S.R := by ring
      _ = (sec7_hSum h₁ h₂ h₃) ^ 2 *
            ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) / S.R := by rw [hT1id]
      _ = (sec7_hSum h₁ h₂ h₃) ^ 2 * ((P.G * S.Ω ^ 5) / S.R) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (9 * W ^ 4 * sec7_Pprod h₁ h₂ h₃) * ((P.G * S.Ω ^ 5) / S.R) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = 9 * sec7_Pprod h₁ h₂ h₃ *
            (W ^ 4 * (P.G * S.Ω ^ 5) / S.R) * (S.T₃ / S.R ^ 3) := by ring
      _ ≤ 9 * sec7_Pprod h₁ h₂ h₃ * (1 / sec7_cSub) * (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hSR := sec7_hSum_R_small Hyp.env Hyp.hbox
  have hSRdiv : sec7_hSum h₁ h₂ h₃ / S.R ≤ 1 / (10 : ℝ) ^ 149 := by
    have hpow : 0 < (10 : ℝ) ^ 149 := by positivity
    rw [le_div_iff₀ hpow]
    have hdiv := div_le_div_of_nonneg_right hSR hR.le
    calc
      sec7_hSum h₁ h₂ h₃ / S.R * (10 : ℝ) ^ 149
          = (sec7_hSum h₁ h₂ h₃ * (10 : ℝ) ^ 149) / S.R := by ring
      _ ≤ S.R / S.R := hdiv
      _ = 1 := by field_simp
  have hE4 :
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4) ≤
        (1 / (10 : ℝ) ^ 149) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)
          = (sec7_hSum h₁ h₂ h₃ / S.R) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 149) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
            gcongr
  calc
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀
        = sec7_cErr *
            (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S +
              (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
              sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)) := by
          unfold sec7_errScale
          rw [Hyp.hρ₀]
          simp only [if_true, zero_mul, zero_add]
    _ ≤ sec7_cErr *
          ((3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 149) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
          apply mul_le_mul_of_nonneg_left
          · gcongr
          · exact sec7_cErr_pos.le
    _ ≤ 1000 * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
          norm_num [sec7_cErr, sec7_cSub] at hC0T ⊢
          nlinarith

private theorem sec7_powMonD_dyadic_bound {R c α K t : ℝ} {k : ℕ}
    (hR : 0 < R) (hK : 1 ≤ K) (hαk : α - (k : ℝ) ≤ 0)
    (ht0 : 0 < t / R) (ht : 1 / K ≤ t / R) :
    |sec7_powMonD R c α k t| ≤
      |c| * |sec7_aprod α k| / R ^ k * K ^ ((k : ℝ) - α) := by
  have h := sec7_powMon_abs_le (R := R) (c := c * sec7_aprod α k / R ^ k)
    (α := α - k) (K := K) (t := t) hK hαk ht0 ht
  have habs : |c * sec7_aprod α k / R ^ k| = |c| * |sec7_aprod α k| / R ^ k := by
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hR k)]
  have hexp : -(α - (k : ℝ)) = (k : ℝ) - α := by ring
  rwa [habs, hexp] at h

private theorem sec7_pow72_17_four_le :
    (72 : ℝ) ^ ((17 : ℝ) / 4) ≤ 3 * (72 : ℝ) ^ 4 := by
  have h72 : (0 : ℝ) ≤ 72 := by norm_num
  have h72pos : (0 : ℝ) < 72 := by norm_num
  have hq0 : (0 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
  have hqraw : (72 : ℝ) ^ ((1 : ℝ) / 4) ≤ ((3 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow h72 (by norm_num : (72 : ℝ) ≤ 3 ^ 4) hq0
  have h3 : ((3 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = 3 := by
    rw [← Real.rpow_natCast (3 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hq : (72 : ℝ) ^ ((1 : ℝ) / 4) ≤ 3 := by
    rw [h3] at hqraw
    exact hqraw
  calc
    (72 : ℝ) ^ ((17 : ℝ) / 4)
        = (72 : ℝ) ^ (4 : ℕ) * (72 : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [show (17 : ℝ) / 4 = (4 : ℝ) + (1 : ℝ) / 4 by norm_num,
            Real.rpow_add h72pos]
          norm_num
    _ ≤ (72 : ℝ) ^ (4 : ℕ) * 3 := by
          gcongr
    _ = 3 * (72 : ℝ) ^ 4 := by ring

private theorem sec7_principal_hasDerivAt_zero {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (hρ₀ : ρ₀ = 0)
    {r : ℝ} (hrpos : 0 < r) :
    HasDerivAt (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
      (sec7_powMonD S.R (ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) 1 r +
        sec7_powMonD S.R
          (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) 1 r) r := by
  subst ρ₀
  have hR : 0 < S.R := sec7_R_pos S
  set B : ℝ := ME.Bcoef 0 ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ with hB
  set C : ℝ := ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) with hC
  have hBder :
      HasDerivAt (sec7_powMon S.R B (-(2 : ℝ))) (sec7_powMonD S.R B (-(2 : ℝ)) 1 r) r := by
    simpa [sec7_powMonD_zero] using
      (sec7_powMonD_hasDerivAt hR B (-(2 : ℝ)) 0 hrpos)
  have hCder :
      HasDerivAt (sec7_powMon S.R C (-(13 : ℝ) / 4))
        (sec7_powMonD S.R C (-(13 : ℝ) / 4) 1 r) r := by
    simpa [sec7_powMonD_zero] using
      (sec7_powMonD_hasDerivAt hR C (-(13 : ℝ) / 4) 0 hrpos)
  have hsum := hBder.add hCder
  have hsum0 :
      HasDerivAt
        (sec7_powMon S.R (ME.Bcoef 0 ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) +
          sec7_powMon S.R
            (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4))
        (sec7_powMonD S.R (ME.Bcoef 0 ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) 1 r +
          sec7_powMonD S.R
            (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) 1 r) r := by
    simpa [hB, hC, mul_assoc] using hsum
  have hprincipal :
      ME.principal 0 ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ =
        sec7_powMon S.R (ME.Bcoef 0 ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) +
          sec7_powMon S.R
            (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) := by
    funext t
    simp [Sec7MonExp.principal, sec7_powMon, mul_assoc]
  simpa [hprincipal] using hsum0

private theorem sec7_zero_principal_deriv_upper {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (hρ₀ : ρ₀ = 0)
    {r : ℝ} (hrb : S.R / 72 ≤ r ∧ r ≤ 16 * S.R) :
    |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
      (300000000 : ℝ) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hrpos : 0 < r := by nlinarith
  have hyrpos : 0 < r / S.R := div_pos hrpos hR
  have hylo : (1 / 72 : ℝ) ≤ r / S.R := by
    rw [le_div_iff₀ hR]
    linarith
  set B : ℝ := ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ with hB
  set C : ℝ := ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) with hC
  have hder := sec7_principal_hasDerivAt_zero (ME := ME) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
    (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) hρ₀ hrpos
  have hderiv :
      deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        sec7_powMonD S.R B (-(2 : ℝ)) 1 r +
          sec7_powMonD S.R C (-(13 : ℝ) / 4) 1 r := by
    simpa [hB, hC] using hder.deriv
  have hBbd := sec7_powMonD_dyadic_bound (R := S.R) (c := B) (α := (-(2 : ℝ)))
    (K := (72 : ℝ)) (k := 1) hR (by norm_num) (by norm_num) hyrpos hylo
  have hBbd' :
      |sec7_powMonD S.R B (-(2 : ℝ)) 1 r| ≤ 746496 * |B| / S.R := by
    calc
      |sec7_powMonD S.R B (-(2 : ℝ)) 1 r|
          ≤ |B| * 2 / S.R * (72 : ℝ) ^ (((1 : ℕ) : ℝ) - (-(2 : ℝ))) := by
            simpa [sec7_aprod] using hBbd
      _ = |B| * 2 / S.R * 373248 := by norm_num
      _ = 746496 * |B| / S.R := by ring
  have hCbd := sec7_powMonD_dyadic_bound (R := S.R) (c := C) (α := (-(13 : ℝ) / 4))
    (K := (72 : ℝ)) (k := 1) hR (by norm_num) (by norm_num) hyrpos hylo
  have hCbd' :
      |sec7_powMonD S.R C (-(13 : ℝ) / 4) 1 r| ≤ 262020096 * |C| / S.R := by
    have hpow := sec7_pow72_17_four_le
    calc
      |sec7_powMonD S.R C (-(13 : ℝ) / 4) 1 r|
          ≤ |C| * |sec7_aprod (-(13 : ℝ) / 4) 1| / S.R ^ 1 *
              (72 : ℝ) ^ (((1 : ℕ) : ℝ) - (-(13 : ℝ) / 4)) := hCbd
      _ = |C| * ((13 : ℝ) / 4) / S.R * (72 : ℝ) ^ ((17 : ℝ) / 4) := by
            norm_num [sec7_aprod]
      _ ≤ |C| * ((13 : ℝ) / 4) / S.R * (3 * (72 : ℝ) ^ 4) := by
            gcongr
      _ = 262020096 * |C| / S.R := by
            norm_num
            ring
  have htri :
      |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        746496 * |B| / S.R + 262020096 * |C| / S.R := by
    rw [hderiv]
    exact le_trans (abs_add_le _ _) (add_le_add hBbd' hCbd')
  have hcoef :
      746496 * |B| + 262020096 * |C| ≤
        300000000 * (|B| + |C|) := by
    nlinarith [abs_nonneg B, abs_nonneg C]
  calc
    |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
        ≤ 746496 * |B| / S.R + 262020096 * |C| / S.R := htri
    _ = (746496 * |B| + 262020096 * |C|) / S.R := by ring
    _ ≤ (300000000 * (|B| + |C|)) / S.R :=
          div_le_div_of_nonneg_right hcoef hR.le
    _ = (300000000 : ℝ) * ((|B| + |C|) / S.R) := by ring
    _ = (300000000 : ℝ) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
          unfold Sec7MonExp.Tscale
          rw [← hB, ← hC]

private theorem sec7_pow16_17_four :
    (16 : ℝ) ^ ((17 : ℝ) / 4) = 131072 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem sec7_pow16_21_four :
    (16 : ℝ) ^ ((21 : ℝ) / 4) = 2097152 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem sec7_wronskian_two_monomials_lower {B C y : ℝ}
    (hy : 0 < y) (hy16 : y ≤ 16) :
    |B| + |C| ≤ (700000 : ℝ) *
      (|(-2 : ℝ) * B * y ^ (-(3 : ℝ)) - (13 / 4 : ℝ) * C * y ^ (-(17 : ℝ) / 4)| +
        |(6 : ℝ) * B * y ^ (-(4 : ℝ)) +
          (221 / 16 : ℝ) * C * y ^ (-(21 : ℝ) / 4)|) := by
  set U : ℝ :=
    (-2 : ℝ) * B * y ^ (-(3 : ℝ)) - (13 / 4 : ℝ) * C * y ^ (-(17 : ℝ) / 4) with hU
  set V : ℝ :=
    (6 : ℝ) * B * y ^ (-(4 : ℝ)) + (221 / 16 : ℝ) * C * y ^ (-(21 : ℝ) / 4) with hV
  have hBsol :
      B = -(8 / 65 : ℝ) * ((221 / 16 : ℝ) * y ^ 3 * U + (13 / 4 : ℝ) * y ^ 4 * V) := by
    subst U
    subst V
    have h1 : y ^ (3 : ℕ) * y ^ (-(3 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast y 3, ← Real.rpow_add hy]
      norm_num
    have h2 : y ^ (3 : ℕ) * y ^ (-(17 : ℝ) / 4) = y ^ (-(5 : ℝ) / 4) := by
      rw [← Real.rpow_natCast y 3, ← Real.rpow_add hy]
      norm_num
    have h3 : y ^ (4 : ℕ) * y ^ (-(4 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast y 4, ← Real.rpow_add hy]
      norm_num
    have h4 : y ^ (4 : ℕ) * y ^ (-(21 : ℝ) / 4) = y ^ (-(5 : ℝ) / 4) := by
      rw [← Real.rpow_natCast y 4, ← Real.rpow_add hy]
      norm_num
    ring_nf
    rw [show y ^ 3 * B * y ^ (-(3 : ℝ)) =
        B * (y ^ (3 : ℕ) * y ^ (-(3 : ℝ))) by ring, h1]
    rw [show y ^ 3 * C * y ^ (-(17 : ℝ) / 4) =
        C * (y ^ (3 : ℕ) * y ^ (-(17 : ℝ) / 4)) by ring, h2]
    rw [show y ^ 4 * B * y ^ (-(4 : ℝ)) =
        B * (y ^ (4 : ℕ) * y ^ (-(4 : ℝ))) by ring, h3]
    rw [show y ^ 4 * C * y ^ (-(21 : ℝ) / 4) =
        C * (y ^ (4 : ℕ) * y ^ (-(21 : ℝ) / 4)) by ring, h4]
    ring
  have hCsol :
      C = (8 / 65 : ℝ) * (6 * y ^ ((17 : ℝ) / 4) * U +
        2 * y ^ ((21 : ℝ) / 4) * V) := by
    subst U
    subst V
    have h1 : y ^ ((17 : ℝ) / 4) * y ^ (-(3 : ℝ)) = y ^ ((5 : ℝ) / 4) := by
      rw [← Real.rpow_add hy]
      norm_num
    have h2 : y ^ ((17 : ℝ) / 4) * y ^ (-(17 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hy]
      norm_num
    have h3 : y ^ ((21 : ℝ) / 4) * y ^ (-(4 : ℝ)) = y ^ ((5 : ℝ) / 4) := by
      rw [← Real.rpow_add hy]
      norm_num
    have h4 : y ^ ((21 : ℝ) / 4) * y ^ (-(21 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hy]
      norm_num
    ring_nf
    rw [show y ^ (17 / 4 : ℝ) * B * y ^ (-(3 : ℝ)) =
        B * (y ^ ((17 : ℝ) / 4) * y ^ (-(3 : ℝ))) by ring, h1]
    rw [show y ^ (17 / 4 : ℝ) * C * y ^ (-(17 : ℝ) / 4) =
        C * (y ^ ((17 : ℝ) / 4) * y ^ (-(17 : ℝ) / 4)) by ring, h2]
    rw [show B * y ^ (21 / 4 : ℝ) * y ^ (-(4 : ℝ)) =
        B * (y ^ ((21 : ℝ) / 4) * y ^ (-(4 : ℝ))) by ring, h3]
    rw [show C * y ^ (21 / 4 : ℝ) * y ^ (-(21 : ℝ) / 4) =
        C * (y ^ ((21 : ℝ) / 4) * y ^ (-(21 : ℝ) / 4)) by ring, h4]
    ring
  have hy3 : y ^ 3 ≤ (4096 : ℝ) := by
    have h := pow_le_pow_left₀ hy.le hy16 3
    norm_num at h
    exact h
  have hy4 : y ^ 4 ≤ (65536 : ℝ) := by
    have h := pow_le_pow_left₀ hy.le hy16 4
    norm_num at h
    exact h
  have hy17 : y ^ ((17 : ℝ) / 4) ≤ (131072 : ℝ) := by
    have h := Real.rpow_le_rpow hy.le hy16 (by norm_num : (0 : ℝ) ≤ (17 : ℝ) / 4)
    rwa [sec7_pow16_17_four] at h
  have hy21 : y ^ ((21 : ℝ) / 4) ≤ (2097152 : ℝ) := by
    have h := Real.rpow_le_rpow hy.le hy16 (by norm_num : (0 : ℝ) ≤ (21 : ℝ) / 4)
    rwa [sec7_pow16_21_four] at h
  have hBbd : |B| ≤ (7000 : ℝ) * |U| + (27000 : ℝ) * |V| := by
    rw [hBsol, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < (8 / 65 : ℝ))]
    have htri := abs_add_le ((221 / 16 : ℝ) * y ^ 3 * U) ((13 / 4 : ℝ) * y ^ 4 * V)
    have hUbd := mul_le_mul_of_nonneg_right hy3 (abs_nonneg U)
    have hUbd' := mul_le_mul_of_nonneg_left hUbd (by norm_num : (0 : ℝ) ≤ (221 / 16 : ℝ))
    have hVbd := mul_le_mul_of_nonneg_right hy4 (abs_nonneg V)
    have hVbd' := mul_le_mul_of_nonneg_left hVbd (by norm_num : (0 : ℝ) ≤ (13 / 4 : ℝ))
    calc
      (8 / 65) * |(221 / 16) * y ^ 3 * U + (13 / 4) * y ^ 4 * V|
          ≤ (8 / 65) * (|(221 / 16) * y ^ 3 * U| + |(13 / 4) * y ^ 4 * V|) := by
            exact mul_le_mul_of_nonneg_left htri (by norm_num)
      _ = (8 / 65) * ((221 / 16) * y ^ 3 * |U| + (13 / 4) * y ^ 4 * |V|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul,
              abs_of_pos (by norm_num : (0 : ℝ) < (221 / 16 : ℝ)),
              abs_of_nonneg (pow_nonneg hy.le 3),
              abs_of_pos (by norm_num : (0 : ℝ) < (13 / 4 : ℝ)),
              abs_of_nonneg (pow_nonneg hy.le 4)]
            try ring
      _ ≤ (8 / 65) * ((221 / 16) * 4096 * |U| + (13 / 4) * 65536 * |V|) := by
            nlinarith
      _ ≤ 7000 * |U| + 27000 * |V| := by
            nlinarith [abs_nonneg U, abs_nonneg V]
  have hCbd : |C| ≤ (97000 : ℝ) * |U| + (517000 : ℝ) * |V| := by
    rw [hCsol, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (8 / 65 : ℝ))]
    have htri := abs_add_le (6 * y ^ ((17 : ℝ) / 4) * U) (2 * y ^ ((21 : ℝ) / 4) * V)
    have hy17pos : 0 < y ^ ((17 : ℝ) / 4) := Real.rpow_pos_of_pos hy _
    have hy21pos : 0 < y ^ ((21 : ℝ) / 4) := Real.rpow_pos_of_pos hy _
    have hUbd := mul_le_mul_of_nonneg_right hy17 (abs_nonneg U)
    have hUbd' := mul_le_mul_of_nonneg_left hUbd (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    have hVbd := mul_le_mul_of_nonneg_right hy21 (abs_nonneg V)
    have hVbd' := mul_le_mul_of_nonneg_left hVbd (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    calc
      (8 / 65) * |6 * y ^ ((17 : ℝ) / 4) * U + 2 * y ^ ((21 : ℝ) / 4) * V|
          ≤ (8 / 65) * (|6 * y ^ ((17 : ℝ) / 4) * U| +
            |2 * y ^ ((21 : ℝ) / 4) * V|) := by
            exact mul_le_mul_of_nonneg_left htri (by norm_num)
      _ = (8 / 65) * (6 * y ^ ((17 : ℝ) / 4) * |U| +
            2 * y ^ ((21 : ℝ) / 4) * |V|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            rw [abs_of_pos (by norm_num : (0 : ℝ) < (6 : ℝ)), abs_of_pos hy17pos,
              abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)), abs_of_pos hy21pos]
            try ring
      _ ≤ (8 / 65) * (6 * 131072 * |U| + 2 * 2097152 * |V|) := by
            nlinarith
      _ ≤ 97000 * |U| + 517000 * |V| := by
            nlinarith [abs_nonneg U, abs_nonneg V]
  calc
    |B| + |C|
        ≤ (7000 * |U| + 27000 * |V|) + (97000 * |U| + 517000 * |V|) :=
          add_le_add hBbd hCbd
    _ ≤ 700000 * (|U| + |V|) := by
          nlinarith [abs_nonneg U, abs_nonneg V]
    _ = 700000 *
        (|(-2 : ℝ) * B * y ^ (-(3 : ℝ)) - (13 / 4 : ℝ) * C * y ^ (-(17 : ℝ) / 4)| +
          |(6 : ℝ) * B * y ^ (-(4 : ℝ)) +
            (221 / 16 : ℝ) * C * y ^ (-(21 : ℝ) / 4)|) := by
          rw [hU, hV]

private theorem sec7_zero_principal_deriv_formula {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (hρ₀ : ρ₀ = 0)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    {r : ℝ} (hrWin : r ∈ sec7_rWin S W) :
    S.R * deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
      (-2 : ℝ) * ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ * (r / S.R) ^ (-(3 : ℝ)) -
        (13 / 4 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) *
          (r / S.R) ^ (-(17 : ℝ) / 4) := by
  have hR : 0 < S.R := sec7_R_pos S
  set B : ℝ := ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ with hB
  set C : ℝ := ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) with hC
  have hjet := sec7_principal_iteratedDeriv_eq (ME := ME)
    hW hpad
    (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂)
    (u₃ := u₃) 1 (by norm_num) r hrWin
  have hderiv :
      deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r := by
    simpa [iteratedDeriv_one] using hjet
  rw [hderiv, hB, hC]
  subst ρ₀
  unfold sec7_principalJet sec7_powMonD sec7_powMon
  norm_num [sec7_aprod]
  field_simp [hR.ne']
  try ring

private theorem sec7_zero_principal_second_formula {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (hρ₀ : ρ₀ = 0)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    {r : ℝ} (hrWin : r ∈ sec7_rWin S W) :
    S.R ^ 2 * iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
      (6 : ℝ) * ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ * (r / S.R) ^ (-(4 : ℝ)) +
        (221 / 16 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) *
          (r / S.R) ^ (-(21 : ℝ) / 4) := by
  have hR : 0 < S.R := sec7_R_pos S
  set B : ℝ := ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ with hB
  set C : ℝ := ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) with hC
  have hjet := sec7_principal_iteratedDeriv_eq (ME := ME)
    hW hpad
    (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂)
    (u₃ := u₃) 2 (by norm_num) r hrWin
  rw [hjet, hB, hC]
  subst ρ₀
  unfold sec7_principalJet sec7_powMonD sec7_powMon
  norm_num [sec7_aprod]
  field_simp [hR.ne']
  try ring

private theorem sec7_zero_principal_scale_lower {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (hρ₀ : ρ₀ = 0)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    {r : ℝ} (hrWin : r ∈ sec7_rWin S W) (hrb : S.R / 72 ≤ r ∧ r ≤ 16 * S.R) :
    ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R ≤
      (700000 : ℝ) *
        (|deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hrpos : 0 < r := by nlinarith
  set B : ℝ := ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ with hB
  set C : ℝ := ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) with hC
  set y : ℝ := r / S.R with hydef
  have hy : 0 < y := by
    rw [hydef]
    exact div_pos hrpos hR
  have hy16 : y ≤ 16 := by
    rw [hydef, div_le_iff₀ hR]
    exact hrb.2
  set U : ℝ := (-2 : ℝ) * B * y ^ (-(3 : ℝ)) -
    (13 / 4 : ℝ) * C * y ^ (-(17 : ℝ) / 4) with hU
  set V : ℝ := (6 : ℝ) * B * y ^ (-(4 : ℝ)) +
    (221 / 16 : ℝ) * C * y ^ (-(21 : ℝ) / 4) with hV
  have hwr := sec7_wronskian_two_monomials_lower (B := B) (C := C) hy hy16
  have hD1 :
      S.R * deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = U := by
    rw [hU, hB, hC, hydef]
    exact sec7_zero_principal_deriv_formula (ME := ME) hρ₀ hW hpad hrWin
  have hD2 :
      S.R ^ 2 * iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = V := by
    rw [hV, hB, hC, hydef]
    exact sec7_zero_principal_second_formula (ME := ME) hρ₀ hW hpad hrWin
  have hD1abs :
      |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| = |U| / S.R := by
    have h := congrArg abs hD1
    rw [abs_mul, abs_of_pos hR] at h
    rw [← h]
    field_simp [hR.ne']
  have hD2abs :
      S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| = |V| / S.R := by
    have h := congrArg abs hD2
    rw [abs_mul, abs_of_pos (pow_pos hR 2)] at h
    rw [← h]
    field_simp [hR.ne']
    try ring
  have hT :
      ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ = |B| + |C| := by
    unfold Sec7MonExp.Tscale
    rw [← hB, ← hC]
  calc
    ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R
        = (|B| + |C|) / S.R := by rw [hT]
    _ ≤ (700000 * (|U| + |V|)) / S.R :=
          div_le_div_of_nonneg_right hwr hR.le
    _ = 700000 * (|U| / S.R + |V| / S.R) := by ring
    _ = 700000 *
          (|deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) := by
          rw [hD1abs, hD2abs]

private theorem sec7_zero_errScale_subordinate_tiny {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) :
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ ≤
      (1 / (10 : ℝ) ^ 8) * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_Pprod_ge_one_of_box Hyp.hbox
    linarith
  have hC0nn : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
  have hC0T := sec7_Cbase_le_Tscale_tight (ME := ME) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) Hyp.hbox
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hrelF0 : 0 ≤ sec7_relErrF P S := (sec7_relErrF_pos P S).le
  have hT1id := sec7_T₁_div_R_eq_GΩ5_T₃ S
  have hSlePP := sec7_hSum_le_three_Pprod_of_box Hyp.hbox
  have hGrel := sec7_GΩ5_relErr_le_inv_cSub (P := P) (S := S) Hyp.hsub2
  have hGrelF := Hyp.hGΩ5F
  have hGrel0 : 0 ≤ P.G * S.Ω ^ 5 * sec7_relErr P S :=
    mul_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hrel0
  have hGrelF0 : 0 ≤ P.G * S.Ω ^ 5 * sec7_relErrF P S :=
    mul_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hrelF0
  have hArel :
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErr P S ≤
        (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErr P S
          = sec7_hSum h₁ h₂ h₃ *
              ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) * sec7_relErr P S := by rw [hT1id]
      _ = sec7_hSum h₁ h₂ h₃ * (P.G * S.Ω ^ 5 * sec7_relErr P S) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (1 / sec7_cSub) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hArelF :
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S ≤
        (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S
          = sec7_hSum h₁ h₂ h₃ *
              ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) * sec7_relErrF P S := by rw [hT1id]
      _ = sec7_hSum h₁ h₂ h₃ * (P.G * S.Ω ^ 5 * sec7_relErrF P S) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (1 / sec7_cSub) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hrel := sec7_relErr_le_inv_10_143 Hyp.hrel
  have hrelF := sec7_relErrF_le_inv_10_143 Hyp.hrelF
  have hCrel :
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S ≤
        (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S
          ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (1 / (10 : ℝ) ^ 143) := by
            gcongr
      _ = (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hCrelF :
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S ≤
        (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S
          ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (1 / (10 : ℝ) ^ 143) := by
            gcongr
      _ = (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hSsq := sec7_hSum_sq_le_nine_W4_Pprod Hyp.hbox
  have hWsub := sec7_W4_GΩ5_div_R_le_inv_cSub (P := P) (S := S) Hyp.hsub1
  have hGΩR0 : 0 ≤ (P.G * S.Ω ^ 5) / S.R :=
    div_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hR.le
  have hE2 :
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 ≤
        (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2
          = (sec7_hSum h₁ h₂ h₃) ^ 2 * (S.T₁ / S.R) / S.R := by ring
      _ = (sec7_hSum h₁ h₂ h₃) ^ 2 *
            ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) / S.R := by rw [hT1id]
      _ = (sec7_hSum h₁ h₂ h₃) ^ 2 * ((P.G * S.Ω ^ 5) / S.R) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (9 * W ^ 4 * sec7_Pprod h₁ h₂ h₃) * ((P.G * S.Ω ^ 5) / S.R) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = 9 * sec7_Pprod h₁ h₂ h₃ *
            (W ^ 4 * (P.G * S.Ω ^ 5) / S.R) * (S.T₃ / S.R ^ 3) := by ring
      _ ≤ 9 * sec7_Pprod h₁ h₂ h₃ * (1 / sec7_cSub) * (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hSR := sec7_hSum_R_small Hyp.env Hyp.hbox
  have hSRdiv : sec7_hSum h₁ h₂ h₃ / S.R ≤ 1 / (10 : ℝ) ^ 149 := by
    have hpow : 0 < (10 : ℝ) ^ 149 := by positivity
    rw [le_div_iff₀ hpow]
    have hdiv := div_le_div_of_nonneg_right hSR hR.le
    calc
      sec7_hSum h₁ h₂ h₃ / S.R * (10 : ℝ) ^ 149
          = (sec7_hSum h₁ h₂ h₃ * (10 : ℝ) ^ 149) / S.R := by ring
      _ ≤ S.R / S.R := hdiv
      _ = 1 := by field_simp
  have hE4 :
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4) ≤
        (1 / (10 : ℝ) ^ 149) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)
          = (sec7_hSum h₁ h₂ h₃ / S.R) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 149) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
            gcongr
  calc
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀
        = sec7_cErr *
            (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S +
              (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
              sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)) := by
          unfold sec7_errScale
          rw [Hyp.hρ₀]
          simp only [if_true, zero_mul, zero_add]
    _ ≤ sec7_cErr *
          ((3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 149) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
          apply mul_le_mul_of_nonneg_left
          · gcongr
          · exact sec7_cErr_pos.le
    _ ≤ (1 / (10 : ℝ) ^ 8) * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
          norm_num [sec7_cErr, sec7_cSub] at hC0T ⊢
          nlinarith

private theorem sec7_zero_err_combo_subordinate {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    {r : ℝ} (hrWin : r ∈ sec7_rWin S W) :
    |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
        S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
      (1 / (10 : ℝ) ^ 7) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hρ0abs : |(ρ₀ : ℝ)| ≤ sec7_cCarry := by
    rw [Hyp.hρ₀]
    norm_num [sec7_cCarry]
  have hErr1raw := sec7_err_deriv_bound (ME := ME) Hyp.env Hyp.hj Hyp.hbox
    Hyp.hW Hyp.hpad Hyp.hshift Hyp.hrel Hyp.hrelF
    Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ0abs Hyp.hρ₁ Hyp.hρ₂ Hyp.hρ₃
    Hyp.hu₁ Hyp.hu₂ Hyp.hu₃ 1 (by norm_num) r hrWin
  have hErr1 :
      |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R := by
    simpa [iteratedDeriv_one] using hErr1raw
  have hErr2 := sec7_err_deriv_bound (ME := ME) Hyp.env Hyp.hj Hyp.hbox
    Hyp.hW Hyp.hpad Hyp.hshift Hyp.hrel Hyp.hrelF
    Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ0abs Hyp.hρ₁ Hyp.hρ₂ Hyp.hρ₃
    Hyp.hu₁ Hyp.hu₂ Hyp.hu₃ 2 (by norm_num) r hrWin
  have hTiny := sec7_zero_errScale_subordinate_tiny (ME := ME) Hyp
  have hE1 :
      |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        (1 / (10 : ℝ) ^ 8) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
    calc
      |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          ≤ sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R := hErr1
      _ ≤ ((1 / (10 : ℝ) ^ 8) * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) / S.R :=
            div_le_div_of_nonneg_right hTiny hR.le
      _ = (1 / (10 : ℝ) ^ 8) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by ring
  have hE2 :
      S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        (1 / (10 : ℝ) ^ 8) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
    calc
      S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          ≤ S.R * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ 2) :=
            mul_le_mul_of_nonneg_left hErr2 hR.le
      _ = sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R := by
            field_simp [hR.ne']
            try ring
      _ ≤ ((1 / (10 : ℝ) ^ 8) * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) / S.R :=
            div_le_div_of_nonneg_right hTiny hR.le
      _ = (1 / (10 : ℝ) ^ 8) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by ring
  have hTnonneg : 0 ≤ ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R := by
    unfold Sec7MonExp.Tscale
    positivity
  calc
    |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
        S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
        ≤ (1 / (10 : ℝ) ^ 8) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) +
          (1 / (10 : ℝ) ^ 8) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) :=
          add_le_add hE1 hE2
    _ ≤ (1 / (10 : ℝ) ^ 7) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
          norm_num
          nlinarith

section N12

variable {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} {Ph : Sec7Phase P S W a}
  {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ} {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}

/- N12 (md 1697–1704, 1730–34): "We use the actual scale T_{ρ,u} := |B_{ρ,u}| + |C*P(T₃/R³)|.
   The Taylor remainder in (7.5) is subordinate to this scale. … It follows that, on each
   interval in the carry/fiber cover,  |Φ'_{ρ,u}(r)| ≪ T_{ρ,u}/R". -/
/-- **N12a** (md 1730–32; AM-2 dyadic sub-window; ARB-1: constant `sec7_cDer`): the
derivative upper calibration `|Φ'| ≤ cDer·T_{ρ,u}/R` on a dyadic sub-window. -/
theorem sec7_zero_deriv_upper (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    (p q : ℕ) (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hdyad : q ≤ 2 * p) :
    ∀ r ∈ Set.Icc (p : ℝ) (q : ℝ),
      |deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cDer * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
  intro r hr
  have _ : q ≤ 2 * p := hdyad
  have hR : 0 < S.R := sec7_R_pos S
  have hrb := sec7_dyadic_window_bounds (S := S) hwin hr
  have hrWin := sec7_dyadic_window_mem_rWin (S := S) Hyp.hW hwin hr
  have hrpos : 0 < r := by nlinarith
  have hpr :
      |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        (300000000 : ℝ) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) :=
    sec7_zero_principal_deriv_upper (ME := ME) Hyp.hρ₀ hrb
  have hρ0abs : |(ρ₀ : ℝ)| ≤ sec7_cCarry := by
    rw [Hyp.hρ₀]
    norm_num [sec7_cCarry]
  have hErrBound := sec7_err_deriv_bound (ME := ME) Hyp.env Hyp.hj Hyp.hbox
    Hyp.hW Hyp.hpad Hyp.hshift Hyp.hrel Hyp.hrelF
    Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ0abs Hyp.hρ₁ Hyp.hρ₂ Hyp.hρ₃
    Hyp.hu₁ Hyp.hu₂ Hyp.hu₃ 1 (by norm_num) r hrWin
  have hErrBound' :
      |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R := by
    simpa [iteratedDeriv_one] using hErrBound
  have hErrSub := sec7_zero_errScale_subordinate (ME := ME) Hyp
  have hErr :
      |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        1000 * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
    calc
      |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          ≤ sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R := hErrBound'
      _ ≤ (1000 * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) / S.R :=
            div_le_div_of_nonneg_right hErrSub hR.le
      _ = 1000 * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by ring
  have hprHas := sec7_principal_hasDerivAt_zero (ME := ME) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
    (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) Hyp.hρ₀ hrpos
  have hprDiff : DifferentiableAt ℝ (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r :=
    hprHas.differentiableAt
  have hrwin : r ∈ Set.Ioo (S.R / 144 - 1) (40 * S.R + 1) := by
    rw [Set.mem_Ioo]
    exact ⟨by nlinarith [hrb.1, hR], by nlinarith [hrb.2, hR]⟩
  have hPhiDiff :
      DifferentiableAt ℝ
        (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r :=
    (Hyp.hcd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hrwin)
  have hErrDiff : DifferentiableAt ℝ (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r := by
    unfold Sec7MonExp.Err
    exact hPhiDiff.sub hprDiff
  have hPhiEq :
      (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) =
        fun x => ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x +
          ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x := by
    funext x
    exact sec7_eq75 ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x
  have hderivPhi :
      deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r +
          deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r := by
    rw [hPhiEq]
    exact deriv_fun_add hprDiff hErrDiff
  have hTnonneg : 0 ≤ ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R := by
    unfold Sec7MonExp.Tscale
    positivity
  calc
    |deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
        = |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r +
            deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by rw [hderivPhi]
    _ ≤ |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| :=
        abs_add_le _ _
    _ ≤ (300000000 : ℝ) * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) +
          1000 * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) :=
        add_le_add hpr hErr
    _ ≤ sec7_cDer * (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R) := by
        norm_num [sec7_cDer]
        nlinarith

/- N12 (md 1694–96, 1730–34): "The two monomials y⁻² and y^{-13/4} have nonzero Wronskian,
   so the principal parts of Φ'_{ρ,u} and RΦ''_{ρ,u} cannot vanish simultaneously. …
   |Φ'_{ρ,u}(r)| + R|Φ''_{ρ,u}(r)| ≍ T_{ρ,u}/R". -/
/-- **N12b** (md 1732–34; AM-2 dyadic sub-window; ARB-1: constant `sec7_cLow`): the
Wronskian lower calibration `T_{ρ,u}/R ≤ cLow·(|Φ'| + R|Φ''|)` on a dyadic sub-window. -/
theorem sec7_zero_scale_lower (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    (p q : ℕ) (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hdyad : q ≤ 2 * p) :
    ∀ r ∈ Set.Icc (p : ℝ) (q : ℝ),
      ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R ≤
        sec7_cLow *
          (|deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            S.R * |iteratedDeriv 2 (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) := by
  intro r hr
  have _ : q ≤ 2 * p := hdyad
  have hR : 0 < S.R := sec7_R_pos S
  have hrb := sec7_dyadic_window_bounds (S := S) hwin hr
  have hrWin := sec7_dyadic_window_mem_rWin (S := S) Hyp.hW hwin hr
  have hPrincipal := sec7_zero_principal_scale_lower (ME := ME) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃)
    Hyp.hρ₀ Hyp.hW Hyp.hpad hrWin hrb
  have hErr := sec7_zero_err_combo_subordinate (ME := ME) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) Hyp hrWin
  have hh₁ : 1 ≤ h₁ := Hyp.hbox.1.1
  have hh₂ : 1 ≤ h₂ := Hyp.hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := Hyp.hbox.2.2.1
  have hSR := sec7_hSum_R_small Hyp.env Hyp.hbox
  have hSv3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
    sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hsh : 24 * sec7_hSum h₁ h₂ h₃ * sec7_cWin ≤ S.R := by
    calc
      24 * sec7_hSum h₁ h₂ h₃ * sec7_cWin
          = sec7_hSum h₁ h₂ h₃ * 24000 := by
            rw [show sec7_cWin = 1000 from by norm_num [sec7_cWin]]
            ring
      _ ≤ sec7_hSum h₁ h₂ h₃ * 10 ^ 149 := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            norm_num
      _ ≤ S.R := hSR
  have hsplit1raw := sec7_Phi_iteratedDeriv_eq_principal_add_Err ME hh₁ hh₂ hh₃
    Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hW Hyp.hpad Hyp.hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃
    1 (by norm_num) r hrWin
  have hsplit1 :
      deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r +
          deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r := by
    simpa [iteratedDeriv_one] using hsplit1raw
  have hsplit2 := sec7_Phi_iteratedDeriv_two_eq_principal_add_Err ME hh₁ hh₂ hh₃
    Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hW Hyp.hpad Hyp.hshift
    ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r := r) hrWin
  have hpr1le :
      |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        |deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by
    have hpr_eq :
        deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
          deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r -
            deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r := by
      rw [hsplit1]
      ring
    calc
      |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          = |deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r -
              deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by rw [hpr_eq]
      _ ≤ |deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            |deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| :=
          abs_sub _ _
  have hpr2abs :
      |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by
    have hpr2_eq :
        iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
          iteratedDeriv 2
            (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r -
            iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r := by
      rw [hsplit2]
      ring
    calc
      |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          = |iteratedDeriv 2
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r -
              iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by rw [hpr2_eq]
      _ ≤ |iteratedDeriv 2
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| :=
          abs_sub _ _
  have hpr2le :
      S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        S.R * |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by
    calc
      S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|
          ≤ S.R *
              (|iteratedDeriv 2
                (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
                |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) :=
            mul_le_mul_of_nonneg_left hpr2abs hR.le
      _ = S.R * |iteratedDeriv 2
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by ring
  have hprincipalCombo :
      |deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        (|deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          S.R * |iteratedDeriv 2
            (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) +
        (|deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
          S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) := by
    nlinarith [hpr1le, hpr2le]
  have hmain :
      ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R ≤
        (700000 : ℝ) *
          ((|deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            S.R * |iteratedDeriv 2
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) +
            (1 / (10 : ℝ) ^ 7) *
              (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R)) := by
    calc
      ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R
          ≤ (700000 : ℝ) *
              (|deriv (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
                S.R * |iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) :=
            hPrincipal
      _ ≤ (700000 : ℝ) *
            ((|deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
              S.R * |iteratedDeriv 2
                (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) +
              (|deriv (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
                S.R * |iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|)) := by
            exact mul_le_mul_of_nonneg_left hprincipalCombo (by norm_num)
      _ ≤ (700000 : ℝ) *
          ((|deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
            S.R * |iteratedDeriv 2
              (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r|) +
            (1 / (10 : ℝ) ^ 7) *
              (ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R)) := by
            apply mul_le_mul_of_nonneg_left
            · nlinarith [hErr]
            · norm_num
  have hTnonneg : 0 ≤ ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ / S.R := by
    unfold Sec7MonExp.Tscale
    positivity
  have hPhiNonneg :
      0 ≤ |deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| +
        S.R * |iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| := by
    positivity
  norm_num [sec7_cLow] at hmain ⊢
  nlinarith

/-- **Generic Rolle/subsingleton.**  If `F` is continuous on `[p,q]` and its derivative
never vanishes on `(p,q)`, then `F` has at most one zero on `[p,q]`. -/
private theorem sec7_zeros_subsingleton_of_deriv_ne {F : ℝ → ℝ} {p q : ℝ}
    (hcont : ContinuousOn F (Set.Icc p q))
    (hne : ∀ x ∈ Set.Ioo p q, deriv F x ≠ 0) :
    (Set.Icc p q ∩ {x | F x = 0}).Subsingleton := by
  intro x hx y hy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt
      (hcont.mono (Set.Icc_subset_Icc hx.1.1 hy.1.2)) (by rw [hx.2, hy.2])
    exact absurd hc0 (hne c ⟨lt_of_le_of_lt hx.1.1 hc.1, lt_of_lt_of_le hc.2 hy.1.2⟩)
  · exact heq
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hgt
      (hcont.mono (Set.Icc_subset_Icc hy.1.1 hx.1.2)) (by rw [hy.2, hx.2])
    exact absurd hc0 (hne c ⟨lt_of_le_of_lt hy.1.1 hc.1, lt_of_lt_of_le hc.2 hx.1.2⟩)

/-- A subsingleton set is finite with `ncard ≤ sec7_KZero`. -/
private theorem sec7_finite_ncard_KZero_of_subsingleton {s : Set ℝ} (hs : s.Subsingleton) :
    s.Finite ∧ s.ncard ≤ sec7_KZero := by
  refine ⟨hs.finite, ?_⟩
  have h1 : s.ncard ≤ 1 := (Set.ncard_le_one hs.finite).mpr (fun a ha b hb => hs ha hb)
  exact le_trans h1 (by norm_num [sec7_KZero])

/-- **Weighted-derivative collapse of one power monomial.**
`3x²·D¹(c·yᵅ) + x³·D²(c·yᵅ) = R·c·α·(α+2)·yᵅ⁺¹`, `y = x/R`. -/
private theorem sec7_powMonD_weighted_collapse {R : ℝ} (hR : 0 < R) (c α : ℝ) {x : ℝ}
    (hx : 0 < x) :
    3 * x ^ 2 * sec7_powMonD R c α 1 x + x ^ 3 * sec7_powMonD R c α 2 x
      = R * c * α * (α + 2) * (x / R) ^ (α + 1) := by
  have hxR0 : (0 : ℝ) < x / R := div_pos hx hR
  have hRne : R ≠ 0 := ne_of_gt hR
  have hx2 : x ^ 2 * (x / R) ^ (α - 1) = R ^ 2 * (x / R) ^ (α + 1) := by
    have hxx : x ^ 2 = R ^ 2 * (x / R) ^ (2 : ℕ) := by field_simp
    rw [hxx, mul_assoc, ← Real.rpow_natCast (x / R) 2, ← Real.rpow_add hxR0]
    congr 2
    push_cast; ring
  have hx3 : x ^ 3 * (x / R) ^ (α - 2) = R ^ 3 * (x / R) ^ (α + 1) := by
    have hxx : x ^ 3 = R ^ 3 * (x / R) ^ (3 : ℕ) := by field_simp
    rw [hxx, mul_assoc, ← Real.rpow_natCast (x / R) 3, ← Real.rpow_add hxR0]
    congr 2
    push_cast; ring
  unfold sec7_powMonD sec7_powMon
  have ha1 : sec7_aprod α 1 = α := by simp [sec7_aprod]
  have ha2 : sec7_aprod α 2 = α * (α - 1) := by simp [sec7_aprod]
  rw [ha1, ha2]
  push_cast
  rw [show (3 : ℝ) * x ^ 2 * (c * α / R ^ 1 * (x / R) ^ (α - 1))
        = (3 * c * α / R ^ 1) * (x ^ 2 * (x / R) ^ (α - 1)) by ring,
      show x ^ 3 * (c * (α * (α - 1)) / R ^ 2 * (x / R) ^ (α - 2))
        = (c * (α * (α - 1)) / R ^ 2) * (x ^ 3 * (x / R) ^ (α - 2)) by ring,
      hx2, hx3]
  field_simp
  ring

/-- **Principal weighted collapse, `ρ₀ = 0`.**  Both the `T₁`- and `B`-monomials annihilate
under the `(r³·Φ')'` weight (the `B`-monomial because its `α+2 = 0`), leaving a single
`C·R·y⁻⁹ᐟ⁴` monomial with coefficient `65/16`. -/
private theorem sec7_principal_weighted_collapse {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (hρ₀ : ρ₀ = 0)
    (hR : 0 < S.R) {x : ℝ} (hx : 0 < x) :
    3 * x ^ 2 * sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x
        + x ^ 3 * sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x
      = (65 / 16) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
          (x / S.R) ^ (-(9 : ℝ) / 4) := by
  subst hρ₀
  simp only [sec7_principalJet]
  have e1 := sec7_powMonD_weighted_collapse (R := S.R) hR (ME.c₁ * (0 : ℝ) * S.T₁) (-(1 : ℝ)) hx
  have e2 := sec7_powMonD_weighted_collapse (R := S.R) hR
    (ME.Bcoef 0 ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) hx
  have e3 := sec7_powMonD_weighted_collapse (R := S.R) hR
    (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) hx
  rw [show (-(13 : ℝ) / 4 + 1) = -(9 : ℝ) / 4 by norm_num] at e3
  push_cast at e1 e2 e3 ⊢
  linear_combination e1 + e2 + e3


/-- **Subordination to the `C`-base scale** (md 1701–29, TRAP-3 form): the eq-(7.5)
remainder scale is `≪ P·T₃/R³`, the surviving `C`-monomial base.  Same chain as
`sec7_zero_errScale_subordinate_tiny`, but kept against `P·T₃/R³` (not collapsed to
`T_{ρ,u}`), so it controls the lone surviving monomial of the weighted `Φ'`-collapse. -/
private theorem sec7_zero_errScale_le_Cbase {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) :
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ ≤
      (1 / (10 : ℝ) ^ 10) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by
    have hPP1 := sec7_Pprod_ge_one_of_box Hyp.hbox
    linarith
  have hC0nn : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
  have hC0T := sec7_Cbase_le_Tscale_tight (ME := ME) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (ρ₂ := ρ₂) (ρ₃ := ρ₃) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) Hyp.hbox
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hrelF0 : 0 ≤ sec7_relErrF P S := (sec7_relErrF_pos P S).le
  have hT1id := sec7_T₁_div_R_eq_GΩ5_T₃ S
  have hSlePP := sec7_hSum_le_three_Pprod_of_box Hyp.hbox
  have hGrel := sec7_GΩ5_relErr_le_inv_cSub (P := P) (S := S) Hyp.hsub2
  have hGrelF := Hyp.hGΩ5F
  have hGrel0 : 0 ≤ P.G * S.Ω ^ 5 * sec7_relErr P S :=
    mul_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hrel0
  have hGrelF0 : 0 ≤ P.G * S.Ω ^ 5 * sec7_relErrF P S :=
    mul_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hrelF0
  have hArel :
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErr P S ≤
        (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErr P S
          = sec7_hSum h₁ h₂ h₃ *
              ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) * sec7_relErr P S := by rw [hT1id]
      _ = sec7_hSum h₁ h₂ h₃ * (P.G * S.Ω ^ 5 * sec7_relErr P S) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (1 / sec7_cSub) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hArelF :
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S ≤
        (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S
          = sec7_hSum h₁ h₂ h₃ *
              ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) * sec7_relErrF P S := by rw [hT1id]
      _ = sec7_hSum h₁ h₂ h₃ * (P.G * S.Ω ^ 5 * sec7_relErrF P S) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (3 * sec7_Pprod h₁ h₂ h₃) * (1 / sec7_cSub) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hrel := sec7_relErr_le_inv_10_143 Hyp.hrel
  have hrelF := sec7_relErrF_le_inv_10_143 Hyp.hrelF
  have hCrel :
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S ≤
        (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S
          ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (1 / (10 : ℝ) ^ 143) := by
            gcongr
      _ = (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hCrelF :
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S ≤
        (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S
          ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (1 / (10 : ℝ) ^ 143) := by
            gcongr
      _ = (1 / (10 : ℝ) ^ 143) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hSsq := sec7_hSum_sq_le_nine_W4_Pprod Hyp.hbox
  have hWsub := sec7_W4_GΩ5_div_R_le_inv_cSub (P := P) (S := S) Hyp.hsub1
  have hGΩR0 : 0 ≤ (P.G * S.Ω ^ 5) / S.R :=
    div_nonneg (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5)) hR.le
  have hE2 :
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 ≤
        (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2
          = (sec7_hSum h₁ h₂ h₃) ^ 2 * (S.T₁ / S.R) / S.R := by ring
      _ = (sec7_hSum h₁ h₂ h₃) ^ 2 *
            ((P.G * S.Ω ^ 5) * (S.T₃ / S.R ^ 3)) / S.R := by rw [hT1id]
      _ = (sec7_hSum h₁ h₂ h₃) ^ 2 * ((P.G * S.Ω ^ 5) / S.R) *
            (S.T₃ / S.R ^ 3) := by ring
      _ ≤ (9 * W ^ 4 * sec7_Pprod h₁ h₂ h₃) * ((P.G * S.Ω ^ 5) / S.R) *
            (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = 9 * sec7_Pprod h₁ h₂ h₃ *
            (W ^ 4 * (P.G * S.Ω ^ 5) / S.R) * (S.T₃ / S.R ^ 3) := by ring
      _ ≤ 9 * sec7_Pprod h₁ h₂ h₃ * (1 / sec7_cSub) * (S.T₃ / S.R ^ 3) := by
            gcongr
      _ = (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
  have hSR := sec7_hSum_R_small Hyp.env Hyp.hbox
  have hSRdiv : sec7_hSum h₁ h₂ h₃ / S.R ≤ 1 / (10 : ℝ) ^ 149 := by
    have hpow : 0 < (10 : ℝ) ^ 149 := by positivity
    rw [le_div_iff₀ hpow]
    have hdiv := div_le_div_of_nonneg_right hSR hR.le
    calc
      sec7_hSum h₁ h₂ h₃ / S.R * (10 : ℝ) ^ 149
          = (sec7_hSum h₁ h₂ h₃ * (10 : ℝ) ^ 149) / S.R := by ring
      _ ≤ S.R / S.R := hdiv
      _ = 1 := by field_simp
  have hE4 :
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4) ≤
        (1 / (10 : ℝ) ^ 149) *
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    calc
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)
          = (sec7_hSum h₁ h₂ h₃ / S.R) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 149) *
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
            gcongr
  calc
    sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀
        = sec7_cErr *
            (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
              sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S +
              (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
              sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)) := by
          unfold sec7_errScale
          rw [Hyp.hρ₀]
          simp only [if_true, zero_mul, zero_add]
    _ ≤ sec7_cErr *
          ((3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
            (1 / (10 : ℝ) ^ 149) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
          apply mul_le_mul_of_nonneg_left
          · gcongr
          · exact sec7_cErr_pos.le
    _ ≤ (1 / (10 : ℝ) ^ 10) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
          have hc :
              sec7_cErr * (3 / sec7_cSub + 1 / (10 : ℝ) ^ 143 + 1 / (10 : ℝ) ^ 143 +
                9 / sec7_cSub + 1 / (10 : ℝ) ^ 149) ≤ 1 / (10 : ℝ) ^ 10 := by
            norm_num [sec7_cErr, sec7_cSub]
          rw [show sec7_cErr *
                ((3 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
                  (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
                  (1 / (10 : ℝ) ^ 143) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
                  (9 / sec7_cSub) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) +
                  (1 / (10 : ℝ) ^ 149) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
              = (sec7_cErr * (3 / sec7_cSub + 1 / (10 : ℝ) ^ 143 + 1 / (10 : ℝ) ^ 143 +
                  9 / sec7_cSub + 1 / (10 : ℝ) ^ 149)) *
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) by ring]
          exact mul_le_mul_of_nonneg_right hc hC0nn

/-- **N12c, `Φ'` (deriv) branch.**  On a dyadic count sub-window `[p,q]`, the weighted jet
`r ↦ r³·Φ'_{ρ,u}(r)` has a non-vanishing derivative (the `ρ₀=0` principal collapses to a single
`C·R·r⁻⁹ᐟ⁴` monomial, dominating the subordinate remainder), hence — by Rolle — at most one zero;
so `Φ'_{ρ,u}` has `≤ 1 ≤ sec7_KZero` zeros on `[p,q]`. -/
private theorem sec7_zero_deriv_few {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ} {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    (p q : ℕ) (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hdyad : q ≤ 2 * p) :
    (Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).Finite ∧
      (Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).ncard ≤
        sec7_KZero := by
  have hR : 0 < S.R := sec7_R_pos S
  have hh₁ : 1 ≤ h₁ := Hyp.hbox.1.1
  have hh₂ : 1 ≤ h₂ := Hyp.hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := Hyp.hbox.2.2.1
  have hPPpos : 0 < sec7_Pprod h₁ h₂ h₃ :=
    lt_of_lt_of_le one_pos (sec7_Pprod_ge_one_of_box Hyp.hbox)
  have hCbasepos : 0 < sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) :=
    mul_pos hPPpos (div_pos (sec7_T₃_pos S) (pow_pos hR 3))
  have hC0nn : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := hCbasepos.le
  have hρ0abs : |(ρ₀ : ℝ)| ≤ sec7_cCarry := by rw [Hyp.hρ₀]; norm_num [sec7_cCarry]
  have hE0nn : 0 ≤ sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ := by
    have hre := (sec7_relErr_pos P S).le
    have hreF := (sec7_relErrF_pos P S).le
    have hT1 := (sec7_T₁_pos S).le
    have hT3 := (sec7_T₃_pos S).le
    have h3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
    have : 0 ≤ sec7_errScale P S h₁ h₂ h₃ ρ₀ := by
      unfold sec7_errScale; positivity
    exact mul_nonneg sec7_cErr_pos.le this
  have hsubC := sec7_zero_errScale_le_Cbase ME Hyp
  have hne : ∀ x ∈ Set.Ioo (p : ℝ) (q : ℝ),
      deriv (fun r => r ^ 3 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r) x ≠ 0 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (p : ℝ) (q : ℝ) := Set.Ioo_subset_Icc_self hx
    have hrb := sec7_dyadic_window_bounds (S := S) hwin hxIcc
    have hxpos : 0 < x := by nlinarith [hrb.1, hR]
    have hrWin := sec7_dyadic_window_mem_rWin (S := S) Hyp.hW hwin hxIcc
    have hmid := (sec7_rWin_subset_mid S Hyp.hW) hrWin
    have hjet1 : HasDerivAt (sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1)
        (sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x) x := by
      have := sec7_PhiJet_chain ME hh₁ hh₂ hh₃ Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hshift
        ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 (by norm_num) x hmid
      simpa using this
    have hp : HasDerivAt (fun r : ℝ => r ^ 3) (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    have hFderiv : HasDerivAt (fun r => r ^ 3 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r)
        (3 * x ^ 2 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          x ^ 3 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x) x := hp.mul hjet1
    have hsplit1 : sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x =
        sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x := by
      simp only [sec7_ErrJet]; ring
    have hsplit2 : sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x =
        sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x +
          sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x := by
      simp only [sec7_ErrJet]; ring
    have hcollapse := sec7_principal_weighted_collapse (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃)
      (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) ME Hyp.hρ₀ hR hxpos
    have hErrJet1eq : sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x =
        iteratedDeriv 1 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) x :=
      (sec7_Err_iteratedDeriv_eq ME hh₁ hh₂ hh₃ Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hW Hyp.hpad
        Hyp.hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 (by norm_num) x hrWin).symm
    have hErrJet2eq : sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x =
        iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) x :=
      (sec7_Err_iteratedDeriv_eq ME hh₁ hh₂ hh₃ Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hW Hyp.hpad
        Hyp.hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 (by norm_num) x hrWin).symm
    have hb1 : |sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R := by
      rw [hErrJet1eq]
      have := sec7_err_deriv_bound (ME := ME) Hyp.env Hyp.hj Hyp.hbox Hyp.hW Hyp.hpad
        Hyp.hshift Hyp.hrel Hyp.hrelF Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ0abs
        Hyp.hρ₁ Hyp.hρ₂ Hyp.hρ₃ Hyp.hu₁ Hyp.hu₂ Hyp.hu₃ 1 (by norm_num) x hrWin
      simpa using this
    have hb2 : |sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ 2 := by
      rw [hErrJet2eq]
      exact sec7_err_deriv_bound (ME := ME) Hyp.env Hyp.hj Hyp.hbox Hyp.hW Hyp.hpad
        Hyp.hshift Hyp.hrel Hyp.hrelF Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ hρ0abs
        Hyp.hρ₁ Hyp.hρ₂ Hyp.hρ₃ Hyp.hu₁ Hyp.hu₂ Hyp.hu₃ 2 (by norm_num) x hrWin
    have hx16 : x ≤ 16 * S.R := hrb.2
    have hxsq : x ^ 2 ≤ 256 * S.R ^ 2 := by
      nlinarith [mul_nonneg (by linarith [hx16] : (0:ℝ) ≤ 16 * S.R - x)
        (by linarith [hxpos, hR] : (0:ℝ) ≤ 16 * S.R + x)]
    have hxcube : x ^ 3 ≤ 4096 * S.R ^ 3 := by
      nlinarith [mul_le_mul hx16 hxsq (sq_nonneg x) (by linarith [hR] : (0:ℝ) ≤ 16 * S.R),
        hR.le]
    have hyge : (1 / 512 : ℝ) ≤ (x / S.R) ^ (-(9 : ℝ) / 4) := by
      have hxR0 : (0 : ℝ) < x / S.R := div_pos hxpos hR
      have hxR16 : x / S.R ≤ 16 := by rw [div_le_iff₀ hR]; linarith [hx16]
      have hmono : (16 : ℝ) ^ (-(9 : ℝ) / 4) ≤ (x / S.R) ^ (-(9 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_nonpos hxR0 hxR16 (by norm_num)
      have h512 : (16 : ℝ) ^ (-(9 : ℝ) / 4) = 1 / 512 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast 2 4,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        rw [show ((4 : ℕ) : ℝ) * (-(9 : ℝ) / 4) = -((9:ℕ):ℝ) by norm_num,
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast 2 9]
        norm_num
      rw [h512] at hmono; exact hmono
    have hypos : 0 < (x / S.R) ^ (-(9 : ℝ) / 4) := Real.rpow_pos_of_pos (div_pos hxpos hR) _
    have hDlb : (1365 / 33554432 : ℝ) * (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) ≤
        |(65 / 16 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
          (x / S.R) ^ (-(9 : ℝ) / 4)| := by
      have hpos : (0:ℝ) < 65 / 16 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
          (x / S.R) ^ (-(9 : ℝ) / 4) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hCbasepos) hR) hypos
      rw [show (65 / 16 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
            (x / S.R) ^ (-(9 : ℝ) / 4)
          = ME.Cstar * (65 / 16 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
              (x / S.R) ^ (-(9 : ℝ) / 4)) by ring, abs_mul, abs_of_pos hpos]
      have hCstar : (21 / 4096 : ℝ) ≤ |ME.Cstar| := ME.Cstar_lower_tight
      have hprod : (21 / 4096 : ℝ) * (1 / 512) ≤ |ME.Cstar| * (x / S.R) ^ (-(9 : ℝ) / 4) :=
        mul_le_mul hCstar hyge (by norm_num) (abs_nonneg _)
      calc (1365 / 33554432 : ℝ) * (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
          = 65 / 16 * ((21 / 4096) * (1 / 512)) *
              (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by ring
        _ ≤ 65 / 16 * (|ME.Cstar| * (x / S.R) ^ (-(9 : ℝ) / 4)) *
              (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num))
              (mul_nonneg hR.le hC0nn)
        _ = |ME.Cstar| * (65 / 16 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
              (x / S.R) ^ (-(9 : ℝ) / 4)) := by ring
    have hEterm_le : |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x| ≤
        3 * x ^ 2 * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R) +
          x ^ 3 * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ 2) := by
      calc |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
              x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x|
          ≤ |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x| +
              |x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x| := abs_add_le _ _
        _ = 3 * x ^ 2 * |sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x| +
              x ^ 3 * |sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x| := by
            rw [abs_mul (3 * x ^ 2) (sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x),
              abs_mul (x ^ 3) (sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * x ^ 2),
              abs_of_nonneg (pow_nonneg hxpos.le 3)]
        _ ≤ 3 * x ^ 2 * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R) +
              x ^ 3 * (sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ 2) :=
            add_le_add (mul_le_mul_of_nonneg_left hb1 (by positivity))
              (mul_le_mul_of_nonneg_left hb2 (pow_nonneg hxpos.le 3))
    have hEub : |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x| ≤
        (4864 / 10 ^ 10 : ℝ) * (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
      set E0 := sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ with hE0def
      have t1 : 3 * x ^ 2 * (E0 / S.R) ≤ 768 * S.R * E0 := by
        rw [show 3 * x ^ 2 * (E0 / S.R) = 3 * x ^ 2 * E0 / S.R by ring, div_le_iff₀ hR]
        nlinarith [mul_nonneg hE0nn (sub_nonneg.2 hxsq), hE0nn]
      have t2 : x ^ 3 * (E0 / S.R ^ 2) ≤ 4096 * S.R * E0 := by
        rw [show x ^ 3 * (E0 / S.R ^ 2) = x ^ 3 * E0 / S.R ^ 2 by ring,
          div_le_iff₀ (pow_pos hR 2)]
        nlinarith [mul_nonneg hE0nn (sub_nonneg.2 hxcube), hE0nn]
      have hstep : 4864 * S.R * E0 ≤
          4864 * S.R * ((1 / 10 ^ 10) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) :=
        mul_le_mul_of_nonneg_left hsubC (mul_nonneg (by norm_num) hR.le)
      calc |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
              x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x|
          ≤ 3 * x ^ 2 * (E0 / S.R) + x ^ 3 * (E0 / S.R ^ 2) := hEterm_le
        _ ≤ 768 * S.R * E0 + 4096 * S.R * E0 := add_le_add t1 t2
        _ ≤ (4864 / 10 ^ 10 : ℝ) * (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
            rw [show 768 * S.R * E0 + 4096 * S.R * E0 = 4864 * S.R * E0 by ring]
            calc 4864 * S.R * E0
                ≤ 4864 * S.R * ((1 / 10 ^ 10) *
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := hstep
              _ = (4864 / 10 ^ 10 : ℝ) *
                    (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by ring
    have hRC0 : (0:ℝ) < S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := mul_pos hR hCbasepos
    have hlt : |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x| <
        |(65 / 16 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
          (x / S.R) ^ (-(9 : ℝ) / 4)| := by
      calc |3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
              x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x|
          ≤ (4864 / 10 ^ 10 : ℝ) * (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := hEub
        _ < (1365 / 33554432 : ℝ) * (S.R * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) :=
            mul_lt_mul_of_pos_right (by norm_num) hRC0
        _ ≤ _ := hDlb
    have heq : deriv (fun r => r ^ 3 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r) x =
        (65 / 16 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
          (x / S.R) ^ (-(9 : ℝ) / 4) +
        (3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x) := by
      rw [hFderiv.deriv, hsplit1, hsplit2]
      linear_combination hcollapse
    rw [heq]
    intro hz
    have hDeq : (65 / 16 : ℝ) * (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) * S.R *
        (x / S.R) ^ (-(9 : ℝ) / 4) =
        -(3 * x ^ 2 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 x +
          x ^ 3 * sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 x) := by linarith [hz]
    rw [hDeq, abs_neg] at hlt
    exact lt_irrefl _ hlt
  have hcont : ContinuousOn (fun r => r ^ 3 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r)
      (Set.Icc (p : ℝ) (q : ℝ)) := by
    have hg : ContinuousOn (sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1)
        (Set.Icc (p : ℝ) (q : ℝ)) := by
      intro r hr
      have hrWin := sec7_dyadic_window_mem_rWin (S := S) Hyp.hW hwin hr
      have hmid := (sec7_rWin_subset_mid S Hyp.hW) hrWin
      exact ((sec7_PhiJet_chain ME hh₁ hh₂ hh₃ Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hshift
        ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 (by norm_num) r hmid).continuousAt).continuousWithinAt
    exact (continuous_pow 3).continuousOn.mul hg
  have hss := sec7_zeros_subsingleton_of_deriv_ne hcont hne
  have hsetEq : Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0} =
      Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | r ^ 3 * sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r = 0} := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    refine and_congr_right (fun hr => ?_)
    have hrb := sec7_dyadic_window_bounds (S := S) hwin hr
    have hrpos : 0 < r := by nlinarith [hrb.1, hR]
    have hrWin := sec7_dyadic_window_mem_rWin (S := S) Hyp.hW hwin hr
    have hderiv : deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 r := by
      rw [← iteratedDeriv_one]
      exact sec7_Phi_iteratedDeriv_eq ME hh₁ hh₂ hh₃ Hyp.hξ₁ Hyp.hξ₂ Hyp.hξ₃ Hyp.hW Hyp.hshift
        ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 1 (by norm_num) r hrWin
    rw [hderiv]
    have hr3 : (r : ℝ) ^ 3 ≠ 0 := by positivity
    constructor
    · intro h; rw [h]; ring
    · intro h; rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr3
      · exact h'
  rw [hsetEq]
  exact sec7_finite_ncard_KZero_of_subsingleton hss

/-- **N12c** (md 1735–81): `Φ'_{ρ,u}` and `Φ''_{ρ,u}` have at most `sec7_KZero` zeros on each
dyadic sub-window `[p,q]` of the wide count range — the attempt-1 "WALL".  DERIVED over the full
`Sec7ZeroHyp` pack (not a structure field): the proof needs the §3 `ra_e` expansion (via `ME`/`Ph`),
`Hyp.hρ₀ : ρ₀ = 0`, and strip-smallness (`Hyp.hrel/hrelF/hsub*`), none reachable by a `Sec7Phase`
field.  With `ρ₀ = 0` the principal part is `B·y⁻² + C*·P·(T₃/R³)·y⁻¹³ᐟ⁴`; the weighted derivatives
`(r³Φ')'`, `(r⁴Φ'')'` collapse to a single non-vanishing `y⁻⁹ᐟ⁴` monomial ⟹ each zero-set is a
subsingleton (`≤ 1 ≪ sec7_KZero`). -/
theorem sec7_zero_few_critical {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ} {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) :
    ∀ p q : ℕ,
    Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋ → q ≤ 2 * p →
    ((Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).Finite ∧
      (Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | deriv (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).ncard ≤
        sec7_KZero) ∧
    ((Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).Finite ∧
      (Set.Icc (p : ℝ) (q : ℝ) ∩
        {r | iteratedDeriv 2
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r = 0}).ncard ≤
        sec7_KZero) := by
  intro p q hwin hdyad
  refine ⟨sec7_zero_deriv_few ME Hyp p q hwin hdyad, ?_⟩
  sorry -- STUB: N12c Phi'' branch needs iteratedDeriv 3 (sec7_leib_deriv is m<2; cross-file)

/- N12 (md 1739–52): "Since C* ≠ 0,  T_{ρ,u} ≫ P(T₃/R³) ≍ P/(x²G³Ω⁹),  while
   T_{ρ,u} ≪ h_Σ/(x²G²Ω⁴) + P/(x²G³Ω⁹)"  (monomial identities `T₁/R = 1/(x²G²Ω⁴)`,
   `T₃/R³ = 1/(x²G³Ω⁹)` sympy-banked). -/
/-- **N12d** (md 1739–52; ARB-1 split constants `sec7_cTlo`/`sec7_cTup`): the two-sided
evaluation of the scale `T_{ρ,u}`. -/
theorem sec7_zero_Tscale_bounds (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) :
    sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) ≤
        sec7_cTlo * ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ ∧
      ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ ≤
        sec7_cTup * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
          sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT3 : 0 < S.T₃ := sec7_T₃_pos S
  have hPP1 : (1 : ℝ) ≤ sec7_Pprod h₁ h₂ h₃ :=
    sec7_Pprod_ge_one_of_box Hyp.hbox
  have hPP0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ := by linarith
  have hPscale0 : 0 ≤ sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
  have hA0 : 0 ≤ sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) := by
    have hSv3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
      sec7_hSum_ge3 Hyp.hbox.1.1 Hyp.hbox.2.1.1 Hyp.hbox.2.2.1
    positivity
  have hCterm_eq :
      |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)| =
        |ME.Cstar| * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hPP0, abs_of_pos (div_pos hT3 (pow_pos hR 3))]
    ring
  constructor
  · have hTge :
        (21 / 4096 : ℝ) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) ≤
          ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
      calc
        (21 / 4096 : ℝ) * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))
            ≤ |ME.Cstar| * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
              gcongr
              exact ME.Cstar_lower_tight
        _ = |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)| := hCterm_eq.symm
        _ ≤ ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ := by
              unfold Sec7MonExp.Tscale
              have hnn :
                  0 ≤ |ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃| :=
                abs_nonneg _
              linarith
    rw [sec7_cTlo]
    nlinarith
  · have hB := sec7_Bcoef_zero_upper (ME := ME) (W := W) Hyp.hbox Hyp.hρ₀
      Hyp.hu₁ Hyp.hu₂ Hyp.hu₃
    have hCupper :
        |ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)| ≤
          21 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
      rw [hCterm_eq]
      gcongr
      exact ME.Cstar_upper_tight
    have hCupper' :
        |ME.Cstar| * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) ≤
          21 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
      simpa [hCterm_eq] using hCupper
    unfold Sec7MonExp.Tscale
    rw [hCterm_eq]
    norm_num [sec7_cFib, sec7_cTup] at hB ⊢
    nlinarith

end N12

private theorem sec7_count_split (p q s δ : ℝ) (φ : ℝ → ℝ) :
    (((Finset.Icc ⌈p⌉ ⌊q⌋).filter
      (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (((Finset.Icc ⌈p⌉ ⌊s⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        + (((Finset.Icc ⌈s⌉ ⌊q⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) := by
  classical
  have hsub : (Finset.Icc ⌈p⌉ ⌊q⌋).filter
      (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)
      ⊆ ((Finset.Icc ⌈p⌉ ⌊s⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ))
        ∪ ((Finset.Icc ⌈s⌉ ⌊q⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hpn, hnq⟩, hδn⟩ := hn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    rcases le_or_gt n ⌊s⌋ with hle | hgt
    · exact Or.inl ⟨⟨hpn, hle⟩, hδn⟩
    · refine Or.inr ⟨⟨?_, hnq⟩, hδn⟩
      have : ⌈s⌉ ≤ ⌊s⌋ + 1 := Int.ceil_le_floor_add_one s
      omega
  calc
    (((Finset.Icc ⌈p⌉ ⌊q⌋).filter
        (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ ((((Finset.Icc ⌈p⌉ ⌊s⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ))
          ∪ ((Finset.Icc ⌈s⌉ ⌊q⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((Finset.Icc ⌈p⌉ ⌊s⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        + (((Finset.Icc ⌈s⌉ ⌊q⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _

private theorem sec7_count_le_of_chain (δ B : ℝ) (φ : ℝ → ℝ) :
    ∀ (L : List ℝ) (a b : ℝ),
      List.IsChain (fun p q =>
        (((Finset.Icc ⌈p⌉ ⌊q⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) ≤ B)
        (a :: (L ++ [b])) →
      (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
        (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ ((L.length : ℝ) + 1) * B := by
  intro L
  induction L with
  | nil =>
    intro a b hch
    simp only [List.nil_append] at hch
    rw [List.isChain_cons_cons] at hch
    simpa using hch.1
  | cons s L' ih =>
    intro a b hch
    simp only [List.cons_append] at hch
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hab, hrest⟩ := hch
    have hsplit := sec7_count_split a b s δ φ
    have hIH := ih s b hrest
    have hstep :
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B + ((L'.length : ℝ) + 1) * B := by
      calc
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ (((Finset.Icc ⌈a⌉ ⌊s⌋).filter
                (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
              + (((Finset.Icc ⌈s⌉ ⌊b⌋).filter
                (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) :=
              hsplit
        _ ≤ B + ((L'.length : ℝ) + 1) * B := by linarith
    calc
      (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
        (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B + ((L'.length : ℝ) + 1) * B := hstep
      _ = (((s :: L').length : ℝ) + 1) * B := by
          push_cast [List.length_cons]
          ring

private theorem sec7_iteratedDeriv_two_eq (φ : ℝ → ℝ) (z : ℝ) :
    iteratedDeriv 2 φ z = deriv (deriv φ) z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem sec7_const_sign_of_no_zero {g : ℝ → ℝ} {p q : ℝ}
    (hcont : ContinuousOn g (Set.Icc p q))
    (hno : ∀ z ∈ Set.Ioo p q, g z ≠ 0) :
    (∀ z ∈ Set.Ioo p q, 0 ≤ g z) ∨ (∀ z ∈ Set.Ioo p q, g z ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₁, hx₁mem, hx₁neg⟩, ⟨x₀, hx₀mem, hx₀pos⟩⟩ := hcon
  have hsubIoo : Set.uIcc x₀ x₁ ⊆ Set.Ioo p q :=
    Set.ordConnected_Ioo.uIcc_subset hx₀mem hx₁mem
  have hsub : Set.uIcc x₀ x₁ ⊆ Set.Icc p q := hsubIoo.trans Set.Ioo_subset_Icc_self
  have hcontU : ContinuousOn g (Set.uIcc x₀ x₁) := hcont.mono hsub
  have hmem0 : (0 : ℝ) ∈ Set.uIcc (g x₀) (g x₁) := by
    rw [Set.mem_uIcc]
    exact Or.inr ⟨le_of_lt hx₁neg, le_of_lt hx₀pos⟩
  obtain ⟨c, hcmem, hcval⟩ := intermediate_value_uIcc hcontU hmem0
  exact hno c (hsubIoo hcmem) hcval

private theorem sec7_mono_or_anti_of_no_zero {φ : ℝ → ℝ} {p q : ℝ}
    (hcd : ContDiff ℝ 2 φ)
    (hno : ∀ z ∈ Set.Ioo p q, iteratedDeriv 2 φ z ≠ 0) :
    MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q) := by
  have hcd1 : ContDiff ℝ 1 (deriv φ) := by
    have h2 : ContDiff ℝ (1 + 1) φ := by
      norm_num
      exact hcd
    exact h2.deriv'
  have hcont1 : ContinuousOn (deriv φ) (Set.Icc p q) :=
    (hcd1.continuous).continuousOn
  have hdiff1 : DifferentiableOn ℝ (deriv φ) (interior (Set.Icc p q)) :=
    (hcd1.differentiable (by norm_num)).differentiableOn
  have hcont2 : ContinuousOn (iteratedDeriv 2 φ) (Set.Icc p q) := by
    have : Continuous (deriv (deriv φ)) := hcd1.continuous_deriv (by norm_num)
    refine ContinuousOn.congr (this.continuousOn) ?_
    intro z _
    exact sec7_iteratedDeriv_two_eq φ z
  rcases sec7_const_sign_of_no_zero hcont2 hno with hpos | hneg
  · left
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q) hcont1 hdiff1 ?_
    intro z hz
    rw [interior_Icc] at hz
    rw [← sec7_iteratedDeriv_two_eq φ z]
    exact hpos z hz
  · right
    refine antitoneOn_of_deriv_nonpos (convex_Icc p q) hcont1 hdiff1 ?_
    intro z hz
    rw [interior_Icc] at hz
    rw [← sec7_iteratedDeriv_two_eq φ z]
    exact hneg z hz

private theorem sec7_geo_chain_of_sorted (Z : Set ℝ) (a b : ℝ) :
    ∀ (L : List ℝ) (c : ℝ), a ≤ c → c ≤ b →
      L.Pairwise (· ≤ ·) → (∀ x ∈ L, c ≤ x ∧ x ≤ b) →
      (∀ z ∈ Z, c < z → z < b → z ∈ L) →
      List.IsChain
        (fun p q => a ≤ p ∧ q ≤ b ∧ (Set.Ioo p q ∩ Z = ∅))
        (c :: (L ++ [b])) := by
  intro L
  induction L with
  | nil =>
    intro c hac hcb _ _ hcover
    simp only [List.nil_append]
    rw [List.isChain_cons_cons]
    refine ⟨⟨hac, le_refl b, ?_⟩, List.isChain_singleton b⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzIoo, hzZ⟩
    exact absurd (hcover z hzZ hzIoo.1 hzIoo.2) (by simp)
  | cons x L' ih =>
    intro c hac hcb hsorted hbounds hcover
    simp only [List.cons_append]
    rw [List.isChain_cons_cons]
    have hxmem : x ∈ x :: L' := List.mem_cons_self
    have hxb : x ≤ b := (hbounds x hxmem).2
    have hcx : c ≤ x := (hbounds x hxmem).1
    have hsorted' : L'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsorted).2
    have hxle : ∀ y ∈ L', x ≤ y := (List.pairwise_cons.mp hsorted).1
    refine ⟨⟨hac, hxb, ?_⟩, ?_⟩
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzIoo, hzZ⟩
      have hzL : z ∈ x :: L' := hcover z hzZ hzIoo.1 (lt_of_lt_of_le hzIoo.2 hxb)
      rcases List.mem_cons.mp hzL with hzx | hzL'
      · exact absurd hzx (ne_of_lt hzIoo.2)
      · exact absurd (hxle z hzL') (not_le_of_gt hzIoo.2)
    · apply ih x (le_trans hac hcx) hxb hsorted'
      · intro y hy
        exact ⟨hxle y hy, (hbounds y (List.mem_cons_of_mem x hy)).2⟩
      · intro z hzZ hxz hzb
        have hzL : z ∈ x :: L' := hcover z hzZ (lt_of_le_of_lt hcx hxz) hzb
        rcases List.mem_cons.mp hzL with hzx | hzL'
        · exact absurd hzx.symm (ne_of_lt hxz)
        · exact hzL'

private theorem sec7_exists_mono_piece_breakpoints (a b : ℝ) (K : ℕ) (φ : ℝ → ℝ)
    (hab : a ≤ b) (hcd : ContDiff ℝ 2 φ)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K) :
    ∃ L : List ℝ, L.length ≤ K ∧
      List.IsChain (fun p q => a ≤ p ∧ q ≤ b ∧
        (MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q)))
        (a :: (L ++ [b])) := by
  classical
  set Z : Set ℝ := Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0} with hZdef
  set L : List ℝ := hz2fin.toFinset.sort (· ≤ ·) with hLdef
  refine ⟨L, ?_, ?_⟩
  · rw [hLdef, Finset.length_sort]
    have hcardZ : hz2fin.toFinset.card = Z.ncard :=
      (Set.ncard_eq_toFinset_card Z hz2fin).symm
    rw [hcardZ]
    exact hz2
  · have hsortedL : L.Pairwise (· ≤ ·) := by
      rw [hLdef]
      exact Finset.pairwise_sort _ _
    have hbounds : ∀ x ∈ L, a ≤ x ∧ x ≤ b := by
      intro x hx
      rw [hLdef, Finset.mem_sort, Set.Finite.mem_toFinset, hZdef] at hx
      exact hx.1
    have hcover : ∀ z ∈ Z, a < z → z < b → z ∈ L := by
      intro z hzZ _ _
      rw [hLdef, Finset.mem_sort, Set.Finite.mem_toFinset]
      exact hzZ
    have hgeo := sec7_geo_chain_of_sorted Z a b L a (le_refl a) hab hsortedL hbounds hcover
    refine hgeo.imp ?_
    rintro p q ⟨hap, hqb, hgap⟩
    refine ⟨hap, hqb, ?_⟩
    apply sec7_mono_or_anti_of_no_zero hcd
    intro z hzIoo hzero
    have hzab : z ∈ Set.Icc a b :=
      ⟨le_of_lt (lt_of_le_of_lt hap hzIoo.1), le_of_lt (lt_of_lt_of_le hzIoo.2 hqb)⟩
    have hzZ : z ∈ Z := by
      rw [hZdef]
      exact ⟨hzab, hzero⟩
    have : z ∈ Set.Ioo p q ∩ Z := ⟨hzIoo, hzZ⟩
    rw [hgap] at this
    exact this

private theorem sec7_bands_count_active_split_slack (N T δ a b cu cl : ℝ) (K : ℕ)
    (φ : ℝ → ℝ) (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hcu : 1 ≤ cu) (hcl : 0 < cl) (hcl1 : cl ≤ 1)
    (hactive : 4 * δ < cl ^ 2 * T)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N)) (hcd : ContDiff ℝ 2 φ)
    (hd1 : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ cu * (T / N))
    (hlower : ∀ x ∈ Set.Icc a b,
      cl * (T / N) ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
      (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
        (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  classical
  set B : ℝ := 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) with hBdef
  have hBnn : 0 ≤ B := by
    have hs : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
    have hcu_pos : 0 < cu := lt_of_lt_of_le zero_lt_one hcu
    rw [hBdef]
    positivity
  rcases le_or_gt a b with hab | hba
  swap
  · have hltceil : ⌊b⌋ < ⌈a⌉ := by
      have h1 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
      have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
      exact_mod_cast (by linarith : (⌊b⌋ : ℝ) < (⌈a⌉ : ℝ))
    have hempty : (Finset.Icc ⌈a⌉ ⌊b⌋) = ∅ := Finset.Icc_eq_empty (by omega)
    have hzero : ((Finset.Icc ⌈a⌉ ⌊b⌋).filter
        (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card = 0 := by
      rw [hempty]
      simp
    rw [hzero, Nat.cast_zero]
    have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
    nlinarith [mul_nonneg hK1 hBnn]
  obtain ⟨L, hLlen, hLchain⟩ :=
    sec7_exists_mono_piece_breakpoints a b K φ hab hcd hz2fin hz2
  have hcountchain :
      List.IsChain (fun p q =>
        (((Finset.Icc ⌈p⌉ ⌊q⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) ≤ B)
        (a :: (L ++ [b])) := by
    refine hLchain.imp ?_
    rintro p q ⟨hap, hqb, hmono⟩
    have hpq_sub : Set.Icc p q ⊆ Set.Icc a b := Set.Icc_subset_Icc hap hqb
    have hd1' : ∀ x ∈ Set.Icc p q, |deriv φ x| ≤ cu * (T / N) :=
      fun x hx => hd1 x (hpq_sub hx)
    have hlower' : ∀ x ∈ Set.Icc p q,
        cl * (T / N) ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x| :=
      fun x hx => hlower x (hpq_sub hx)
    have hpiece := Counting.bands_count_mono_slack N T δ a b p q cu cl φ hN hT hδ
      hcu hcl hcl1 hactive hcd hsub hpq_sub hd1' hlower' hmono
    rw [hBdef]
    exact hpiece
  have hchain := sec7_count_le_of_chain δ B φ L a b hcountchain
  have hlen_le : ((L.length : ℝ) + 1) ≤ ((K : ℝ) + 1) := by
    have : (L.length : ℝ) ≤ (K : ℝ) := by exact_mod_cast hLlen
    linarith
  calc
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
      (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ ((L.length : ℝ) + 1) * B := hchain
    _ ≤ ((K : ℝ) + 1) * B := by
        exact mul_le_mul_of_nonneg_right hlen_le hBnn
    _ = 112 * (cu / cl) * ((K : ℝ) + 1) *
        (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
        rw [hBdef]
        ring

private theorem sec7_bands_count_slack_split (N T δ a b cu cl : ℝ) (K : ℕ)
    (φ : ℝ → ℝ) (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hcu : 1 ≤ cu) (hcl : 0 < cl) (hcl1 : cl ≤ 1)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N)) (hcd : ContDiff ℝ 2 φ)
    (hd1 : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ cu * (T / N))
    (hlower : ∀ x ∈ Set.Icc a b,
      cl * (T / N) ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
      (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
        (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  by_cases hactive : 4 * δ < cl ^ 2 * T
  · exact sec7_bands_count_active_split_slack N T δ a b cu cl K φ hN hT hδ
      hcu hcl hcl1 hactive hsub hcd hd1 hlower hz2fin hz2
  · have hnot : cl ^ 2 * T ≤ 4 * δ := le_of_not_gt hactive
    have hratio : (cl / 2) ^ 2 ≤ δ / T := by
      rw [le_div_iff₀ hT]
      nlinarith [hnot, hcl.le]
    have hsqrt : cl / 2 ≤ Real.sqrt (δ / T) := by
      have h := Real.sqrt_le_sqrt hratio
      rwa [Real.sqrt_sq (by positivity)] at h
    have hlen := Counting.card_filter_le_length a b δ φ
    have hRHSnn : 0 ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
      have hs : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
      nlinarith [hN.le, hT.le, hδ.le]
    rcases le_or_gt a b with hab | hba
    · have haIcc : a ∈ Set.Icc N (3 * N) := hsub ⟨le_refl a, hab⟩
      have hbIcc : b ∈ Set.Icc N (3 * N) := hsub ⟨hab, le_refl b⟩
      have hcount :
          (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ (4 / cl) * N * Real.sqrt (δ / T) + 1 := by
        calc
          (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
              ≤ (b - a) + 1 := hlen hab
          _ ≤ 2 * N + 1 := by linarith [haIcc.1, hbIcc.2]
          _ ≤ (4 / cl) * N * Real.sqrt (δ / T) + 1 := by
              have hstep : 2 * N ≤ (4 / cl) * N * Real.sqrt (δ / T) := by
                have hcoef : (2 : ℝ) ≤ (4 / cl) * Real.sqrt (δ / T) := by
                  rw [show (4 / cl) * Real.sqrt (δ / T) =
                      (4 * Real.sqrt (δ / T)) / cl by ring]
                  rw [le_div_iff₀ hcl]
                  nlinarith [hsqrt]
                have hmul := mul_le_mul_of_nonneg_right hcoef hN.le
                nlinarith [hmul]
              linarith
      have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
      have hcucl : 1 ≤ cu / cl := by
        rw [le_div_iff₀ hcl]
        nlinarith [hcu, hcl1]
      calc
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ (4 / cl) * N * Real.sqrt (δ / T) + 1 := hcount
        _ ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
            (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
            have hs : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
            have hcoeff : 4 / cl ≤ 112 * (cu / cl) * ((K : ℝ) + 1) := by
              rw [div_le_iff₀ hcl]
              rw [show 112 * (cu / cl) * ((K : ℝ) + 1) * cl =
                  112 * cu * ((K : ℝ) + 1) by
                    field_simp [hcl.ne']
                    ]
              nlinarith [hcu, hK1]
            have hleft₁ : (4 / cl) * N * Real.sqrt (δ / T)
                ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
                    (N * Real.sqrt (δ / T)) := by
              have hNs : 0 ≤ N * Real.sqrt (δ / T) := mul_nonneg hN.le hs
              have hmul := mul_le_mul_of_nonneg_right hcoeff hNs
              nlinarith [hmul]
            have hleft₂ : (1 : ℝ)
                ≤ 112 * (cu / cl) * ((K : ℝ) + 1) * 1 := by
              nlinarith [hK1, hcucl]
            have hC0 : 0 ≤ 112 * (cu / cl) * ((K : ℝ) + 1) := by
              have : 0 ≤ cu / cl := div_nonneg (le_trans zero_le_one hcu) hcl.le
              positivity
            have hmonoR :
                112 * (cu / cl) * ((K : ℝ) + 1) *
                    (N * Real.sqrt (δ / T) + 1)
                  ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
                    (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
              apply mul_le_mul_of_nonneg_left _ hC0
              nlinarith [hN.le, hT.le, hδ.le, hs]
            nlinarith [hleft₁, hleft₂, hmonoR]
    · have hltceil : ⌊b⌋ < ⌈a⌉ := by
        have h1 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
        have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
        exact_mod_cast (by linarith : (⌊b⌋ : ℝ) < (⌈a⌉ : ℝ))
      have hempty : (Finset.Icc ⌈a⌉ ⌊b⌋) = ∅ := Finset.Icc_eq_empty (by omega)
      have hzero : ((Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card = 0 := by
        rw [hempty]
        simp
      rw [hzero, Nat.cast_zero]
      have hK0 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
      have hcucl0 : 0 ≤ cu / cl := div_nonneg (le_trans zero_le_one hcu) hcl.le
      positivity

/-- `ContDiffOn` variant of `sec7_bands_count_slack_split`: the §7 branch phase is only
`ContDiffOn` an open window (it is `Function.invFun`-built), so we bump-extend it to a global
`C²` function `ψ`, transfer the derivative/curvature/zero-set data to `ψ` on `[a,b]`, count `ψ`
(it agrees with `φ` on every integer of `[⌈a⌉, ⌊b⌋] ⊆ [a,b]`), and read the bound back on `φ`. -/
private theorem sec7_bands_count_slack_split_contDiffOn (N T δ a b cu cl : ℝ) (K : ℕ)
    (φ : ℝ → ℝ) (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hcu : 1 ≤ cu) (hcl : 0 < cl) (hcl1 : cl ≤ 1)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N))
    (hcdO : ContDiffOn ℝ 2 φ (Set.Ioo (a - 1) (b + 1)))
    (hd1 : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ cu * (T / N))
    (hlower : ∀ x ∈ Set.Icc a b,
      cl * (T / N) ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
      (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
        (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  classical
  rcases lt_or_ge a b with hab | hba
  · -- MAIN case: bump-extend `φ` to a global `C²` `ψ`, transfer data, count `ψ`.
    obtain ⟨ψ, hψcd, hψeq⟩ := sec7_exists_global_extension hab hcdO
    have hderiv : ∀ x ∈ Set.Icc a b, deriv ψ x = deriv φ x :=
      fun x hx => (hψeq x hx).deriv_eq
    have hiter : ∀ x ∈ Set.Icc a b, iteratedDeriv 2 ψ x = iteratedDeriv 2 φ x :=
      fun x hx => Filter.EventuallyEq.iteratedDeriv_eq 2 (hψeq x hx)
    have hd1' : ∀ x ∈ Set.Icc a b, |deriv ψ x| ≤ cu * (T / N) := by
      intro x hx; rw [hderiv x hx]; exact hd1 x hx
    have hlower' : ∀ x ∈ Set.Icc a b,
        cl * (T / N) ≤ |deriv ψ x| + N * |iteratedDeriv 2 ψ x| := by
      intro x hx; rw [hderiv x hx, hiter x hx]; exact hlower x hx
    have hzset : (Set.Icc a b ∩ {x | iteratedDeriv 2 ψ x = 0})
        = (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hxab, hx0⟩; exact ⟨hxab, by rw [← hiter x hxab]; exact hx0⟩
      · rintro ⟨hxab, hx0⟩; exact ⟨hxab, by rw [hiter x hxab]; exact hx0⟩
    have hz2fin' : (Set.Icc a b ∩ {x | iteratedDeriv 2 ψ x = 0}).Finite := by
      rw [hzset]; exact hz2fin
    have hz2' : (Set.Icc a b ∩ {x | iteratedDeriv 2 ψ x = 0}).ncard ≤ K := by
      rw [hzset]; exact hz2
    have hψn : ∀ n : ℤ, ⌈a⌉ ≤ n → n ≤ ⌊b⌋ → ψ (n : ℝ) = φ (n : ℝ) := by
      intro n hlo hhi
      have hnmem : (n : ℝ) ∈ Set.Icc a b := by
        refine ⟨?_, ?_⟩
        · exact le_trans (Int.le_ceil a) (by exact_mod_cast hlo)
        · exact le_trans (by exact_mod_cast hhi) (Int.floor_le b)
      exact (hψeq (n : ℝ) hnmem).eq_of_nhds
    have hfilt : (Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)
        = (Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (ψ (n : ℝ)) ≤ δ) := by
      apply Finset.filter_congr
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [hψn n hn.1 hn.2]
    rw [hfilt]
    exact sec7_bands_count_slack_split N T δ a b cu cl K ψ hN hT hδ
      hcu hcl hcl1 hsub hψcd hd1' hlower' hz2fin' hz2'
  · -- DEGENERATE case `b ≤ a`: the index window has card ≤ 1, while RHS ≥ 1.
    have hfloorceil : ⌊b⌋ ≤ ⌈a⌉ := by
      have h1 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
      have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
      exact_mod_cast (by linarith : (⌊b⌋ : ℝ) ≤ (⌈a⌉ : ℝ))
    have hcardle : (Finset.Icc ⌈a⌉ ⌊b⌋).card ≤ 1 := by
      rw [Int.card_Icc]; omega
    have hfle : ((Finset.Icc ⌈a⌉ ⌊b⌋).filter
        (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card ≤ 1 :=
      le_trans (Finset.card_filter_le _ _) hcardle
    have hcucl : (1 : ℝ) ≤ cu / cl := by
      rw [le_div_iff₀ hcl]; nlinarith [hcu, hcl1]
    have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      linarith
    have hbig : (1 : ℝ) ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
      have hs : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
      nlinarith [hN.le, hδ.le, hT.le, hs]
    have hp1 : (1 : ℝ) ≤ 112 * (cu / cl) := by nlinarith [hcucl]
    have hp2 : (1 : ℝ) ≤ 112 * (cu / cl) * ((K : ℝ) + 1) := by
      have := mul_le_mul hp1 hK1 (by norm_num) (le_trans zero_le_one hp1)
      simpa using this
    have hp3 : (1 : ℝ) ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
        (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
      have := mul_le_mul hp2 hbig (by norm_num) (le_trans zero_le_one hp2)
      simpa using this
    calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 1 := by exact_mod_cast hfle
      _ ≤ 112 * (cu / cl) * ((K : ℝ) + 1) *
          (N * (δ + Real.sqrt (δ / T)) + T + 1) := hp3

private theorem sec7_R_delta0_eq (P : Globals) (S : Scale P) :
    S.R * sec7_delta0 P S = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold sec7_delta0 Scale.R Scale.x Scale.A
  field_simp

private theorem sec7_T₁_div_R_eval {P : Globals} (S : Scale P) :
    S.T₁ / S.R = 1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.T₁ Scale.R Scale.F Scale.x
  field_simp

private theorem sec7_T₃_div_R_cubed_eval {P : Globals} (S : Scale P) :
    S.T₃ / S.R ^ 3 = 1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  unfold Scale.T₃ Scale.R Scale.x
  field_simp

private theorem sec7_Tscale_upper_eval {P : Globals} (S : Scale P) (h₁ h₂ h₃ : ℤ) :
    sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
        sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) =
      sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
        sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) := by
  rw [sec7_T₁_div_R_eval, sec7_T₃_div_R_cubed_eval]
  ring

private theorem sec7_R_delta1_eq (P : Globals) (S : Scale P) (h₁ h₂ h₃ : ℤ) :
    S.R * sec7_delta1 P S h₁ h₂ h₃ =
      P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
        sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
  have hR := sec7_R_pos S
  calc
    S.R * sec7_delta1 P S h₁ h₂ h₃
        = S.R * sec7_delta0 P S +
            S.R * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) := by
          rw [sec7_delta1]
          ring
    _ = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            S.R * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) := by
          rw [sec7_R_delta0_eq]
    _ = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ * (S.T₁ / S.R) := by
          congr 1
          field_simp [hR.ne']
    _ = P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
          rw [sec7_T₁_div_R_eval]
          ring

private theorem sec7_Hx_half_eval (P : Globals) (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) = P.H / S.Δ := by
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  have hx : 0 < S.x := by
    unfold Scale.x
    positivity
  rw [← Real.mul_rpow hH.le hx.le]
  have hHx : P.H * S.x = (P.H / S.Δ) ^ (2:ℕ) := by
    unfold Scale.x
    field_simp
  rw [hHx, ← Real.rpow_natCast (P.H / S.Δ) 2, ← Real.rpow_mul (by positivity)]
  norm_num

private theorem sec7_R_mono_eval (P : Globals) (S : Scale P) :
    S.R = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
  rw [sec7_Hx_half_eval]
  unfold Scale.R
  field_simp

private theorem sec7_sqrt_le_of_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  have h := sq_le_sq.mp hxy
  rwa [abs_of_nonneg hx, abs_of_nonneg hy] at h

private theorem sec7_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply sec7_sqrt_le_of_sq
  · positivity
  · positivity
  · rw [Real.sq_sqrt (add_nonneg hx hy)]
    rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

private theorem sec7_sqrt_two_mul_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
  apply sec7_sqrt_le_of_sq
  · positivity
  · positivity
  · rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx)]
    rw [mul_pow, Real.sq_sqrt hx]
    nlinarith [hx]

private theorem sec7_pair_sqrt_constant_le (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (10 : ℝ) ^ 6 * (2 * A + B) ≤ (10 : ℝ) ^ 7 * (A + B) := by
  norm_num
  nlinarith [hA, hB]

private theorem sec7_four_sqrt_constant_le (X B : ℝ) (hX : 0 ≤ X) (hXB : X ≤ B) :
    4 * ((10 : ℝ) ^ 8 * ((10 : ℝ) ^ 7 * X)) ≤ (10 : ℝ) ^ 19 * B := by
  norm_num
  nlinarith [hX, hXB]

private theorem sec7_Tup_constant_le (X B : ℝ) (hX : 0 ≤ X) (hXB : X ≤ B) :
    (16 * sec7_cTup) * X ≤ (10 : ℝ) ^ 19 * B := by
  rw [sec7_cTup]
  norm_num
  nlinarith [hX, hXB]

private theorem sec7_sqrt_window_scale_le {p R T0 δ T : ℝ}
    (hp : 0 < p) (hR : 0 < R) (hT0 : 0 < T0) (hδ : 0 < δ)
    (hTdef : T = p * (T0 / R)) (hp_le : p ≤ 16 * R) :
    p * Real.sqrt (δ / T) ≤ 4 * R * Real.sqrt (δ / T0) := by
  have hTpos : 0 < T := by
    rw [hTdef]
    positivity
  apply sec7_sqrt_le_of_sq
  · positivity
  · positivity
  · rw [mul_pow, Real.sq_sqrt (div_nonneg hδ.le hTpos.le)]
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hδ.le hT0.le)]
    rw [hTdef]
    field_simp [hp.ne', hR.ne', hT0.ne']
    nlinarith [hp_le, hR.le, hδ.le]

private theorem sec7_four_terms_to_1e20 (X Y Z B : ℝ)
    (hX : X ≤ (10 : ℝ) ^ 19 * B) (hY : Y ≤ (10 : ℝ) ^ 19 * B)
    (hZ : Z ≤ (10 : ℝ) ^ 19 * B) (hOne : 1 ≤ (10 : ℝ) ^ 19 * B) :
    X + Y + Z + 1 ≤ (10 : ℝ) ^ 20 * B := by
  norm_num
  nlinarith [hX, hY, hZ, hOne]

private theorem sec7_engine_prefactor_absorb (C I B : ℝ)
    (hC : C ≤ (10 : ℝ) ^ 23) (hI : I ≤ (10 : ℝ) ^ 20 * B)
    (hI0 : 0 ≤ I) :
    C * I ≤ sec7_cN13 * B := by
  calc
    C * I ≤ (10 : ℝ) ^ 23 * I := mul_le_mul_of_nonneg_right hC hI0
    _ ≤ (10 : ℝ) ^ 23 * ((10 : ℝ) ^ 20 * B) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ sec7_cN13 * B := by
      rw [sec7_cN13]
      ring_nf
      exact le_rfl

private theorem sec7_R_sqrt_delta_main_eval {P : Globals} {S : Scale P} {h₁ h₂ h₃ : ℤ}
    (hPP : 0 < sec7_Pprod h₁ h₂ h₃) :
    S.R * Real.sqrt (((P.G * S.Ω / S.x ^ 2) / S.R) /
        (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
      ≤
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
          S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hx : 0 < S.x := by
    have hΔ := S.Δ_pos
    unfold Scale.x
    positivity
  have hΩ := S.Ω_pos
  have hR := sec7_R_pos S
  have hT3 := sec7_T₃_pos S
  apply sec7_sqrt_le_of_sq
  · positivity
  · positivity
  · have hden : 0 < sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ((P.G * S.Ω / S.x ^ 2) / S.R) /
        (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))]
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hPP.le]
    rw [show (P.H ^ ((1:ℝ)/4)) ^ 2 = P.H ^ ((1:ℝ)/2) by
      rw [← Real.rpow_natCast (P.H ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hH.le]
      norm_num]
    rw [show (S.x ^ ((1:ℝ)/4)) ^ 2 = S.x ^ ((1:ℝ)/2) by
      rw [← Real.rpow_natCast (S.x ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hx.le]
      norm_num]
    rw [show (P.G ^ ((5:ℝ)/2)) ^ 2 = P.G ^ (5:ℝ) by
      rw [← Real.rpow_natCast (P.G ^ ((5:ℝ)/2)) 2, ← Real.rpow_mul hG.le]
      norm_num]
    rw [show (S.Ω ^ ((13:ℝ)/2)) ^ 2 = S.Ω ^ (13:ℝ) by
      rw [← Real.rpow_natCast (S.Ω ^ ((13:ℝ)/2)) 2, ← Real.rpow_mul hΩ.le]
      norm_num]
    rw [show P.G ^ (5:ℝ) = P.G ^ 5 by
      rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
    rw [show S.Ω ^ (13:ℝ) = S.Ω ^ 13 by
      rw [show (13:ℝ) = ((13:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
    rw [sec7_T₃_div_R_cubed_eval, sec7_R_mono_eval]
    field_simp [hH.ne', hG.ne', hx.ne', hΩ.ne', hPP.ne']
    ring_nf
    norm_num

private theorem sec7_R_sqrt_Ssym_eval {P : Globals} {S : Scale P} {h₁ h₂ h₃ : ℤ}
    (hSsym : 0 ≤ sec7_Ssym h₁ h₂ h₃) (hPP : 0 < sec7_Pprod h₁ h₂ h₃) :
    S.R * Real.sqrt (((sec7_Ssym h₁ h₂ h₃ /
        (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.R) /
        (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
      ≤
        P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
          Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hx : 0 < S.x := by
    have hΔ := S.Δ_pos
    unfold Scale.x
    positivity
  have hΩ := S.Ω_pos
  have hR := sec7_R_pos S
  have hT3 := sec7_T₃_pos S
  apply sec7_sqrt_le_of_sq
  · positivity
  · positivity
  · have hden : 0 < sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by positivity
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤
        ((sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / S.R) /
          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))]
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hSsym hPP.le)]
    rw [mul_pow, mul_pow]
    rw [show (P.H ^ ((1:ℝ)/4)) ^ 2 = P.H ^ ((1:ℝ)/2) by
      rw [← Real.rpow_natCast (P.H ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hH.le]
      norm_num]
    rw [show (S.x ^ ((1:ℝ)/4)) ^ 2 = S.x ^ ((1:ℝ)/2) by
      rw [← Real.rpow_natCast (S.x ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hx.le]
      norm_num]
    rw [sec7_T₃_div_R_cubed_eval, sec7_R_mono_eval]
    field_simp [hH.ne', hG.ne', hx.ne', hΩ.ne', hPP.ne']
    nlinarith [hSsym]

/- N13 (md 1740–81): "For this fixed triple, using the lower bound for T_{ρ,u} in the
   square-root terms and the upper bound for the +T_{ρ,u}-term, Lemma 4.2 gives
     R√(δ₀/T_{ρ,u}) ≪ H^{1/4}x^{1/4}G^{5/2}Ω^{13/2}P^{-1/2},
     R√((S/(Rx²G²Ω⁴))/T_{ρ,u}) ≪ H^{1/4}x^{1/4}GΩ⁴(S/P)^{1/2},
   and  T_{ρ,u} ≪ h_Σ/(x²G²Ω⁴) + P/(x²G³Ω⁹).   Together with
     Rδ₁(h) ≪ GΩ/x² + Ω²/H + S/(x²G²Ω⁴)   (7.6) …"
   All five evaluations sympy-banked (tools/sec7_ledger.py): Rδ₀ = GΩ/x² + Ω²/H and
   R·(ST₁/R²) = S/(x²G²Ω⁴) are EXACT; both square-root evaluations are exact on the
   `GΩ/x²`-part of δ₀, and the `Ω²/H`-part is dominated via the strip fact `x²Ω ≤ HG`
   (hypothesis `hxsmall`; ratio identity (Ω²/H)/(GΩ/x²) = x²Ω/(HG), banked).
   AM-2: the count is over a dyadic sub-window `[p,q] ⊆ [⌈R/72⌉,⌊16R⌋]`, `q ≤ 2p` (the
   carry/fiber cover piece, md 1567–70, enters via `piece ∩ window ≤ window`); the threshold
   `δ ≤ cCal·δ₁(h)` is the eq-(7.3) proximity (md 1572–76).  In-tree Lemma 4.2 =
   `bands_count_mono_slack`/`bands_count` (`Counting/Bands.lean`, log-free: the writeup's
   dyadic-band log is already absorbed there); `sec7_cN13` absorbs its constant `112`,
   the `(KZero+1)` piece count, and the evaluation constants. -/
set_option maxHeartbeats 4000000

/-- **N13** (md 1740–81): the per-triple, per-branch, per-fiber near-integer count in its
explicit (7.6)-form — the shape N15 harvests.  Conclusion terms, in order: the three
(7.6)-terms `GΩ/x² + Ω²/H + S/(x²G²Ω⁴)` (= `Rδ₁` exactly); the two square-root
evaluations `H^{1/4}x^{1/4}G^{5/2}Ω^{13/2}/√P` and `H^{1/4}x^{1/4}GΩ⁴√(S/P)`; the
`T_{ρ,u}`-term `h_Σ/(x²G²Ω⁴) + P/(x²G³Ω⁹)`; and the engine `+1`. -/
theorem sec7_zero_triple_count {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} {Ph : Sec7Phase P S W a}
    {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ} {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Hyp : Sec7ZeroHyp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    (hxsmall : S.x ^ 2 * S.Ω ≤ P.H * P.G)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ sec7_cCal * sec7_delta1 P S h₁ h₂ h₃)
    -- AM-2: dyadic sub-window of the wide count range (engine: `Icc ⊆ [N,3N]`)
    (p q : ℕ) (hwin : Finset.Icc (p : ℤ) (q : ℤ) ⊆ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hdyad : q ≤ 2 * p) :
    (((Finset.Icc (p : ℤ) (q : ℤ)).filter (fun n : ℤ =>
        Counting.distInt
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ sec7_cN13 *
        (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
          sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) /
            Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
          P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
            Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
          sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
          sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) +
          1) := by
  classical
  set φ : ℝ → ℝ :=
    sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃
    with hφdef
  set T0 : ℝ := ME.Tscale ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ with hT0def
  set T : ℝ := (p : ℝ) * (T0 / S.R) with hTdef
  set cl : ℝ := 1 / (72 * sec7_cLow) with hcldef
  set A1 : ℝ := P.G * S.Ω / S.x ^ 2 with hA1def
  set A2 : ℝ := S.Ω ^ 2 / P.H with hA2def
  set A3 : ℝ := sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) with hA3def
  set A4 : ℝ :=
    P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
      S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃)
    with hA4def
  set A5 : ℝ :=
    P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
      Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃)
    with hA5def
  set A6 : ℝ := sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) with hA6def
  set A7 : ℝ := sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) with hA7def
  set Bfin : ℝ := A1 + A2 + A3 + A4 + A5 + A6 + A7 + 1 with hBfindef
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hR := sec7_R_pos S
  have hT3 := sec7_T₃_pos S
  have hx : 0 < S.x := by
    have hΔ := S.Δ_pos
    unfold Scale.x
    positivity
  have hPP1 : (1 : ℝ) ≤ sec7_Pprod h₁ h₂ h₃ :=
    sec7_Pprod_ge_one_of_box Hyp.hbox
  have hPPpos : 0 < sec7_Pprod h₁ h₂ h₃ := lt_of_lt_of_le zero_lt_one hPP1
  have hSsym0 : 0 ≤ sec7_Ssym h₁ h₂ h₃ := by
    have h1 : (0 : ℝ) ≤ (h₁ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) Hyp.hbox.1.1)
    have h2 : (0 : ℝ) ≤ (h₂ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) Hyp.hbox.2.1.1)
    have h3 : (0 : ℝ) ≤ (h₃ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) Hyp.hbox.2.2.1)
    unfold sec7_Ssym
    nlinarith [mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h2 h3]
  have hHsum0 : 0 ≤ sec7_hSum h₁ h₂ h₃ := by
    have hS3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ :=
      sec7_hSum_ge3 Hyp.hbox.1.1 Hyp.hbox.2.1.1 Hyp.hbox.2.2.1
    linarith
  have hA1 : 0 ≤ A1 := by rw [hA1def]; positivity
  have hA2 : 0 ≤ A2 := by rw [hA2def]; positivity
  have hA3 : 0 ≤ A3 := by rw [hA3def]; positivity
  have hA4 : 0 ≤ A4 := by rw [hA4def]; positivity
  have hA5 : 0 ≤ A5 := by rw [hA5def]; positivity
  have hA6 : 0 ≤ A6 := by rw [hA6def]; positivity
  have hA7 : 0 ≤ A7 := by rw [hA7def]; positivity
  have hBfin_ge1 : (1 : ℝ) ≤ Bfin := by
    rw [hBfindef]
    nlinarith [hA1, hA2, hA3, hA4, hA5, hA6, hA7]
  have hBfin0 : 0 ≤ Bfin := le_trans (by norm_num) hBfin_ge1
  rcases le_or_gt p q with hpq | hpq
  · have hp_mem : (p : ℝ) ∈ Set.Icc (p : ℝ) (q : ℝ) :=
      ⟨le_rfl, by exact_mod_cast hpq⟩
    have hpwide := sec7_dyadic_window_bounds (S := S) hwin hp_mem
    have hp_pos : 0 < (p : ℝ) := by nlinarith [hR]
    have hp_le_16R : (p : ℝ) ≤ 16 * S.R := hpwide.2
    have hR_le_72p : S.R ≤ 72 * (p : ℝ) := by
      calc
        S.R = 72 * (S.R / 72) := by ring
        _ ≤ 72 * (p : ℝ) := mul_le_mul_of_nonneg_left hpwide.1 (by norm_num)
    have hsub : Set.Icc (p : ℝ) (q : ℝ) ⊆ Set.Icc (p : ℝ) (3 * (p : ℝ)) := by
      intro r hr
      constructor
      · exact hr.1
      · have hq2p : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hdyad
        calc
          r ≤ (q : ℝ) := hr.2
          _ ≤ 2 * (p : ℝ) := hq2p
          _ ≤ 3 * (p : ℝ) := by linarith [hp_pos.le]
    have hTb :
        sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) ≤ sec7_cTlo * T0 ∧
          T0 ≤ sec7_cTup * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
            sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
      simpa [hT0def] using sec7_zero_Tscale_bounds (ME := ME) Hyp
    have hPscale_pos : 0 < sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) := by
      exact mul_pos hPPpos (div_pos hT3 (pow_pos hR 3))
    have hT0pos : 0 < T0 := by
      have hlow : sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) ≤ sec7_cTlo * T0 := by
        simpa [hT0def] using hTb.1
      have : 0 < sec7_cTlo * T0 := lt_of_lt_of_le hPscale_pos hlow
      rw [mul_comm] at this
      exact pos_of_mul_pos_left this sec7_cTlo_pos.le
    have hTpos : 0 < T := by
      rw [hTdef]
      exact mul_pos hp_pos (div_pos hT0pos hR)
    have hTN : T / (p : ℝ) = T0 / S.R := by
      rw [hTdef]
      field_simp [hp_pos.ne']
    have hcu : (1 : ℝ) ≤ sec7_cDer := by norm_num [sec7_cDer]
    have hclpos : 0 < cl := by rw [hcldef]; norm_num [sec7_cLow]
    have hcl1 : cl ≤ 1 := by rw [hcldef]; norm_num [sec7_cLow]
    have hd1 : ∀ r ∈ Set.Icc (p : ℝ) (q : ℝ), |deriv φ r| ≤ sec7_cDer * (T / (p : ℝ)) := by
      intro r hr
      have h := sec7_zero_deriv_upper (ME := ME) Hyp p q hwin hdyad r hr
      simpa [hφdef, hT0def, hTN] using h
    have hlower : ∀ r ∈ Set.Icc (p : ℝ) (q : ℝ),
        cl * (T / (p : ℝ)) ≤ |deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r| := by
      intro r hr
      have hlow := sec7_zero_scale_lower (ME := ME) Hyp p q hwin hdyad r hr
      have haux :
          |deriv φ r| + S.R * |iteratedDeriv 2 φ r| ≤
            72 * (|deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r|) := by
        have h1nn : 0 ≤ |deriv φ r| := abs_nonneg _
        have h2nn : 0 ≤ |iteratedDeriv 2 φ r| := abs_nonneg _
        have hleft : |deriv φ r| ≤ 72 * |deriv φ r| := by nlinarith [h1nn]
        have hright : S.R * |iteratedDeriv 2 φ r| ≤
            (72 * (p : ℝ)) * |iteratedDeriv 2 φ r| :=
          mul_le_mul_of_nonneg_right hR_le_72p h2nn
        nlinarith [hleft, hright]
      have htmp :
          T0 / S.R ≤ sec7_cLow *
            (72 * (|deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r|)) := by
        calc
          T0 / S.R ≤ sec7_cLow *
              (|deriv φ r| + S.R * |iteratedDeriv 2 φ r|) := by
                simpa [hφdef, hT0def] using hlow
          _ ≤ sec7_cLow *
              (72 * (|deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r|)) := by
                exact mul_le_mul_of_nonneg_left haux sec7_cLow_pos.le
      have hcancel :
          cl * (T0 / S.R) ≤ |deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r| := by
        rw [hcldef]
        calc
          (1 / (72 * sec7_cLow)) * (T0 / S.R)
              ≤ (1 / (72 * sec7_cLow)) *
                  (sec7_cLow *
                    (72 * (|deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r|))) := by
                apply mul_le_mul_of_nonneg_left htmp
                positivity
          _ = |deriv φ r| + (p : ℝ) * |iteratedDeriv 2 φ r| := by
                field_simp [sec7_cLow_pos.ne']
      simpa [hTN] using hcancel
    obtain ⟨_, hz2pack⟩ := sec7_zero_few_critical ME Hyp p q hwin hdyad
    -- restrict the window `ContDiffOn` to `[p-1, q+1]` (count window `[p,q] ⊆ [p,3p]`).
    have hq2p : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hdyad
    have hcdO : ContDiffOn ℝ 2 φ (Set.Ioo ((p : ℝ) - 1) ((q : ℝ) + 1)) := by
      rw [hφdef]
      refine Hyp.hcd.mono (Set.Ioo_subset_Ioo ?_ ?_)
      · linarith [hpwide.1, hR.le]
      · linarith [hpwide.2, hq2p, hR.le]
    have hengine :=
      sec7_bands_count_slack_split_contDiffOn (p : ℝ) T δ (p : ℝ) (q : ℝ)
        sec7_cDer cl sec7_KZero φ hp_pos hTpos hδ0 hcu hclpos hcl1
        hsub hcdO hd1 hlower hz2pack.1 hz2pack.2
    have hRdelta1 :
        S.R * sec7_delta1 P S h₁ h₂ h₃ = A1 + A2 + A3 := by
      rw [hA1def, hA2def, hA3def]
      exact sec7_R_delta1_eq P S h₁ h₂ h₃
    have hδ1pos : 0 < sec7_delta1 P S h₁ h₂ h₃ := by
      nlinarith [hδ0, hδ, sec7_cCal_pos]
    have hA2_le_A1 : A2 ≤ A1 := by
      rw [hA1def, hA2def]
      rw [div_le_div_iff₀ (by positivity : 0 < P.H) (by positivity : 0 < S.x ^ 2)]
      calc
        S.Ω ^ 2 * S.x ^ 2 = (S.x ^ 2 * S.Ω) * S.Ω := by ring
        _ ≤ (P.H * P.G) * S.Ω := mul_le_mul_of_nonneg_right hxsmall hΩ.le
        _ = P.G * S.Ω * P.H := by ring
    have hδlinear : (p : ℝ) * δ ≤ (10 : ℝ) ^ 19 * Bfin := by
      have hpδ : (p : ℝ) * δ ≤ 16 * sec7_cCal * (S.R * sec7_delta1 P S h₁ h₂ h₃) := by
        nlinarith [hp_le_16R, hδ, hR.le, hδ0.le, sec7_cCal_pos.le]
      rw [hRdelta1] at hpδ
      have hsum_le : A1 + A2 + A3 ≤ Bfin := by
        rw [hBfindef]
        nlinarith [hA4, hA5, hA6, hA7]
      calc
        (p : ℝ) * δ ≤ 16 * sec7_cCal * (A1 + A2 + A3) := hpδ
        _ ≤ (10 : ℝ) ^ 19 * Bfin := by
            norm_num [sec7_cCal]
            nlinarith [hsum_le, hBfin0]
    have hPscale_le : sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) ≤ sec7_cTlo * T0 := by
      simpa [hT0def] using hTb.1
    have hδ1_le :
        sec7_delta1 P S h₁ h₂ h₃ ≤ (2 * A1 + A3) / S.R := by
      rw [le_div_iff₀ hR]
      calc
        sec7_delta1 P S h₁ h₂ h₃ * S.R
            = S.R * sec7_delta1 P S h₁ h₂ h₃ := by ring
        _ = A1 + A2 + A3 := hRdelta1
        _ ≤ 2 * A1 + A3 := by nlinarith [hA2_le_A1]
    have hsqrt_delta1_T0 :
        S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0) ≤
          (10 : ℝ) ^ 7 * (A4 + A5) := by
      have hinside :
          sec7_delta1 P S h₁ h₂ h₃ / T0 ≤
            sec7_cTlo * ((2 * A1 + A3) / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
        have hBnonneg : 0 ≤ (2 * A1 + A3) / S.R := by positivity
        calc
          sec7_delta1 P S h₁ h₂ h₃ / T0
              ≤ ((2 * A1 + A3) / S.R) / T0 :=
                div_le_div_of_nonneg_right hδ1_le hT0pos.le
          _ ≤ sec7_cTlo * ((2 * A1 + A3) / S.R) /
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
              rw [div_le_div_iff₀ hT0pos hPscale_pos]
              calc
                ((2 * A1 + A3) / S.R) *
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))
                    ≤ ((2 * A1 + A3) / S.R) * (sec7_cTlo * T0) :=
                      mul_le_mul_of_nonneg_left hPscale_le hBnonneg
                _ = sec7_cTlo * ((2 * A1 + A3) / S.R) * T0 := by ring
      have hsq_le := Real.sqrt_le_sqrt hinside
      have hsclo : Real.sqrt sec7_cTlo ≤ (10 : ℝ) ^ 6 := by
        rw [sec7_cTlo]
        calc Real.sqrt ((10 : ℝ) ^ 12)
            = Real.sqrt (((10 : ℝ) ^ 6) ^ 2) := by rw [← pow_mul]
          _ = (10 : ℝ) ^ 6 := Real.sqrt_sq (by positivity)
          _ ≤ (10 : ℝ) ^ 6 := le_rfl
      have harg_nonneg : 0 ≤ ((2 * A1 + A3) / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
        positivity
      have hsplit :
          Real.sqrt (((2 * A1 + A3) / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
            ≤ 2 * Real.sqrt ((A1 / S.R) /
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) +
              Real.sqrt ((A3 / S.R) /
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
        have hx1 : 0 ≤ (2 * ((A1 / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) := by positivity
        have hx2 : 0 ≤ (A3 / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by positivity
        calc
          Real.sqrt (((2 * A1 + A3) / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
              = Real.sqrt (2 * ((A1 / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) +
                (A3 / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
                congr 1
                field_simp [hR.ne', hPscale_pos.ne']
          _ ≤ Real.sqrt (2 * ((A1 / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) +
                Real.sqrt ((A3 / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) :=
                sec7_sqrt_add_le _ _ hx1 hx2
          _ ≤ 2 * Real.sqrt ((A1 / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) +
                Real.sqrt ((A3 / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
                have hbase : 0 ≤ (A1 / S.R) /
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
                  positivity
                have h2 :
                    Real.sqrt (2 * ((A1 / S.R) /
                      (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))))
                    ≤ 2 * Real.sqrt ((A1 / S.R) /
                      (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) :=
                  sec7_sqrt_two_mul_le_two_sqrt _ hbase
                nlinarith
      have heval1 :
          S.R * Real.sqrt ((A1 / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) ≤ A4 := by
        rw [hA1def, hA4def]
        exact sec7_R_sqrt_delta_main_eval (S := S) (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hPPpos
      have heval2 :
          S.R * Real.sqrt ((A3 / S.R) /
              (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) ≤ A5 := by
        rw [hA3def, hA5def]
        exact sec7_R_sqrt_Ssym_eval (S := S) (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hSsym0 hPPpos
      calc
        S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0)
            ≤ S.R * Real.sqrt (sec7_cTlo * ((2 * A1 + A3) / S.R) /
                  (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by
              exact mul_le_mul_of_nonneg_left hsq_le hR.le
        _ = S.R * (Real.sqrt sec7_cTlo *
              Real.sqrt (((2 * A1 + A3) / S.R) /
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) := by
              rw [show sec7_cTlo * ((2 * A1 + A3) / S.R) /
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) =
                  sec7_cTlo * (((2 * A1 + A3) / S.R) /
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) by ring]
              rw [Real.sqrt_mul sec7_cTlo_pos.le]
        _ ≤ S.R * ((10 : ℝ) ^ 6 *
              Real.sqrt (((2 * A1 + A3) / S.R) /
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hsclo (Real.sqrt_nonneg _)) hR.le
        _ = (10 : ℝ) ^ 6 * (S.R *
              Real.sqrt (((2 * A1 + A3) / S.R) /
                (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) := by ring
        _ ≤ (10 : ℝ) ^ 6 * (2 * A4 + A5) := by
              have hsplitR :
                  S.R * Real.sqrt (((2 * A1 + A3) / S.R) /
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) ≤
                    2 * A4 + A5 := by
                calc
                  S.R * Real.sqrt (((2 * A1 + A3) / S.R) /
                    (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))
                      ≤ S.R * (2 * Real.sqrt ((A1 / S.R) /
                          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) +
                        Real.sqrt ((A3 / S.R) /
                          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) :=
                        mul_le_mul_of_nonneg_left hsplit hR.le
                  _ = 2 * (S.R * Real.sqrt ((A1 / S.R) /
                          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)))) +
                        S.R * Real.sqrt ((A3 / S.R) /
                          (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3))) := by ring
                  _ ≤ 2 * A4 + A5 := by
                        exact add_le_add (mul_le_mul_of_nonneg_left heval1 (by norm_num)) heval2
              exact mul_le_mul_of_nonneg_left hsplitR (by positivity)
        _ ≤ (10 : ℝ) ^ 7 * (A4 + A5) := by
              exact sec7_pair_sqrt_constant_le A4 A5 hA4 hA5
    have hpsqrt : (p : ℝ) * Real.sqrt (δ / T) ≤ (10 : ℝ) ^ 19 * Bfin := by
      have hp_sqrt_base :
          (p : ℝ) * Real.sqrt (δ / T) ≤ 4 * S.R * Real.sqrt (δ / T0) := by
        exact sec7_sqrt_window_scale_le hp_pos hR hT0pos hδ0 hTdef hp_le_16R
      have hs_cal :
          S.R * Real.sqrt (δ / T0) ≤ (10 : ℝ) ^ 8 *
            (S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0)) := by
        have hinside : δ / T0 ≤ sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ / T0 := by
          exact div_le_div_of_nonneg_right hδ hT0pos.le
        have hs := Real.sqrt_le_sqrt hinside
        have hcal : Real.sqrt sec7_cCal ≤ (10 : ℝ) ^ 8 := by
          rw [sec7_cCal]
          apply sec7_sqrt_le_of_sq
          · positivity
          · positivity
          · rw [Real.sq_sqrt (by positivity : 0 ≤ (10 : ℝ) ^ 15)]
            norm_num
        calc
          S.R * Real.sqrt (δ / T0)
              ≤ S.R * Real.sqrt (sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ / T0) :=
                mul_le_mul_of_nonneg_left hs hR.le
          _ = S.R * (Real.sqrt sec7_cCal *
                Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0)) := by
                rw [show sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ / T0 =
                    sec7_cCal * (sec7_delta1 P S h₁ h₂ h₃ / T0) by ring]
                rw [Real.sqrt_mul sec7_cCal_pos.le]
          _ ≤ (10 : ℝ) ^ 8 *
                (S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0)) := by
                calc
                  S.R * (Real.sqrt sec7_cCal *
                      Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0))
                      ≤ S.R * ((10 : ℝ) ^ 8 *
                        Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0)) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right hcal (Real.sqrt_nonneg _)) hR.le
                  _ = (10 : ℝ) ^ 8 *
                        (S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0)) := by ring
      have hA45_le_B : A4 + A5 ≤ Bfin := by
        have hprefix : 0 ≤ A1 + A2 + A3 + A6 + A7 + 1 := by positivity
        calc
          A4 + A5 ≤ (A1 + A2 + A3 + A6 + A7 + 1) + (A4 + A5) :=
            le_add_of_nonneg_left hprefix
          _ = A1 + A2 + A3 + A4 + A5 + A6 + A7 + 1 := by ring
          _ = Bfin := by rw [hBfindef]
      calc
        (p : ℝ) * Real.sqrt (δ / T)
            ≤ 4 * S.R * Real.sqrt (δ / T0) := hp_sqrt_base
        _ = 4 * (S.R * Real.sqrt (δ / T0)) := by ring
        _ ≤ 4 * ((10 : ℝ) ^ 8 *
              (S.R * Real.sqrt (sec7_delta1 P S h₁ h₂ h₃ / T0))) := by
              exact mul_le_mul_of_nonneg_left hs_cal (by norm_num)
        _ ≤ 4 * ((10 : ℝ) ^ 8 * ((10 : ℝ) ^ 7 * (A4 + A5))) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_left hsqrt_delta1_T0 (by positivity)
              · norm_num
        _ ≤ (10 : ℝ) ^ 19 * Bfin := by
              exact sec7_four_sqrt_constant_le (A4 + A5) Bfin
                (add_nonneg hA4 hA5) hA45_le_B
    have hTlinear : T ≤ (10 : ℝ) ^ 19 * Bfin := by
      have hT_le : T ≤ 16 * T0 := by
        calc
          T = (p : ℝ) * (T0 / S.R) := hTdef
          _ ≤ (16 * S.R) * (T0 / S.R) :=
              mul_le_mul_of_nonneg_right hp_le_16R (by positivity)
          _ = 16 * T0 := by
              field_simp [hR.ne']
      have hT0_eval : T0 ≤ sec7_cTup * (A6 + A7) := by
        calc
          T0 ≤ sec7_cTup * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) +
                sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) := by
              simpa [hT0def] using hTb.2
          _ = sec7_cTup * (A6 + A7) := by
              rw [hA6def, hA7def, sec7_Tscale_upper_eval]
      have hA67_le_B : A6 + A7 ≤ Bfin := by
        have hprefix : 0 ≤ A1 + A2 + A3 + A4 + A5 + 1 := by positivity
        calc
          A6 + A7 ≤ (A1 + A2 + A3 + A4 + A5 + 1) + (A6 + A7) :=
            le_add_of_nonneg_left hprefix
          _ = A1 + A2 + A3 + A4 + A5 + A6 + A7 + 1 := by ring
          _ = Bfin := by rw [hBfindef]
      calc
        T ≤ 16 * T0 := hT_le
        _ ≤ 16 * (sec7_cTup * (A6 + A7)) :=
            mul_le_mul_of_nonneg_left hT0_eval (by norm_num)
        _ = (16 * sec7_cTup) * (A6 + A7) := by ring
        _ ≤ (10 : ℝ) ^ 19 * Bfin :=
            sec7_Tup_constant_le (A6 + A7) Bfin (add_nonneg hA6 hA7) hA67_le_B
    have hinside :
        (p : ℝ) * (δ + Real.sqrt (δ / T)) + T + 1 ≤ (10 : ℝ) ^ 20 * Bfin := by
      have hone : (1 : ℝ) ≤ (10 : ℝ) ^ 19 * Bfin := by
        calc
          (1 : ℝ) ≤ Bfin := hBfin_ge1
          _ = 1 * Bfin := by ring
          _ ≤ (10 : ℝ) ^ 19 * Bfin :=
            mul_le_mul_of_nonneg_right (by norm_num) hBfin0
      have hpd_split :
          (p : ℝ) * (δ + Real.sqrt (δ / T)) =
            (p : ℝ) * δ + (p : ℝ) * Real.sqrt (δ / T) := by ring
      rw [hpd_split]
      exact sec7_four_terms_to_1e20 ((p : ℝ) * δ)
        ((p : ℝ) * Real.sqrt (δ / T)) T Bfin hδlinear hpsqrt hTlinear hone
    have hpref :
        112 * (sec7_cDer / cl) * ((sec7_KZero : ℝ) + 1) ≤ (10 : ℝ) ^ 23 := by
      rw [hcldef]
      norm_num [sec7_cDer, sec7_cLow, sec7_KZero]
    have htarget :
        (((Finset.Icc ⌈(p : ℝ)⌉ ⌊(q : ℝ)⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ sec7_cN13 * Bfin := by
      calc
        (((Finset.Icc ⌈(p : ℝ)⌉ ⌊(q : ℝ)⌋).filter
          (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ 112 * (sec7_cDer / cl) * ((sec7_KZero : ℝ) + 1) *
                ((p : ℝ) * (δ + Real.sqrt (δ / T)) + T + 1) := by
              simpa [hcldef] using hengine
        _ ≤ sec7_cN13 * Bfin := by
              have hinside0 :
                  0 ≤ (p : ℝ) * (δ + Real.sqrt (δ / T)) + T + 1 := by
                have hs : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
                have hpd0 :
                    0 ≤ (p : ℝ) * (δ + Real.sqrt (δ / T)) :=
                  mul_nonneg hp_pos.le (add_nonneg hδ0.le hs)
                exact add_nonneg (add_nonneg hpd0 hTpos.le) zero_le_one
              exact sec7_engine_prefactor_absorb
                (112 * (sec7_cDer / cl) * ((sec7_KZero : ℝ) + 1))
                ((p : ℝ) * (δ + Real.sqrt (δ / T)) + T + 1)
                Bfin hpref hinside hinside0
    have hcount_eq :
        ((((Finset.Icc (p : ℤ) (q : ℤ)).filter (fun n : ℤ =>
          Counting.distInt
            (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)) =
          (((Finset.Icc ⌈(p : ℝ)⌉ ⌊(q : ℝ)⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) := by
      simp [hφdef]
    have hBfin_expand :
        Bfin =
          P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
              S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
              Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
            sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) + 1 := by
      rw [hBfindef, hA1def, hA2def, hA3def, hA4def, hA5def, hA6def, hA7def]
    calc
      (((Finset.Icc (p : ℤ) (q : ℤ)).filter (fun n : ℤ =>
        Counting.distInt
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (n : ℝ)) ≤ δ)).card : ℝ)
          = (((Finset.Icc ⌈(p : ℝ)⌉ ⌊(q : ℝ)⌋).filter
            (fun (n : ℤ) => Counting.distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) := hcount_eq
      _ ≤ sec7_cN13 * Bfin := htarget
      _ = sec7_cN13 *
          (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
              S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
              Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
            sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) + 1) := by
            rw [hBfin_expand]
  · have hlt : (q : ℤ) < (p : ℤ) := by exact_mod_cast hpq
    have hempty : Finset.Icc (p : ℤ) (q : ℤ) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    have hBfin_expand :
        Bfin =
          P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
              S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
              Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
            sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) + 1 := by
      rw [hBfindef, hA1def, hA2def, hA3def, hA4def, hA5def, hA6def, hA7def]
    have hnonneg : 0 ≤ sec7_cN13 * Bfin :=
      mul_nonneg (by norm_num [sec7_cN13]) hBfin0
    calc
      (0 : ℝ) ≤ sec7_cN13 * Bfin := hnonneg
      _ = sec7_cN13 *
          (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H +
            sec7_Ssym h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
              S.Ω ^ ((13:ℝ)/2) / Real.sqrt (sec7_Pprod h₁ h₂ h₃) +
            P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
              Real.sqrt (sec7_Ssym h₁ h₂ h₃ / sec7_Pprod h₁ h₂ h₃) +
            sec7_hSum h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) +
            sec7_Pprod h₁ h₂ h₃ / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) + 1) := by
            rw [hBfin_expand]

end Squarefree
