import Squarefree.Opt.OnStripAux
import Squarefree.Bracket.Sec7Defs

/-!
# §9 on-strip discharge of the §7 full envelope (`Sec7Envelope`) at `W = 10⁻²⁵·X^{-2u}·Wnz`

`sec7Envelope_Wnz`: on the unresolved strip, the bundled §7 full admissibility envelope
(md 1421–1451, `Bracket/Sec7Defs.lean`) holds at `W = 10⁻²⁵·X^{-2u}·Wnz`, where
`Wnz = H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}` is the §9 bottleneck (`Opt/OnStripAux.lean`).
All 25 `≪`-entries are the k-th powers of the root-form entries `Wnz ≤ m_k` (each via
`Wnz_le_mono`); the four no-absorption residual entries (AM-4: now `sec7_envC`-form) have root
tuples `(3/16,1/16,1/8,1/8)`, `(3/28,1/28,1/7,3/7)`, `(1/6,−1/6,−2/9,−8/9)`,
`(1/14,−1/14,0,2/21)` (sympy-verified corner slacks `≥ 0.0115`).  The hypothesis-side constant
`sec7_envC = 10²⁰⁰` is absorbed by `ε = 10⁻²⁵` since every entry power is `k ≥ 8`:
`10²⁰⁰·(10⁻²⁵)^k ≤ 1`; the ARB-2 entries `n4–n7` carry `sec7_envC2 = 10³⁰⁰`, absorbed at
`k ≥ 12` (`env_master2`; their powers are 18/42/30/54).  The AM-7 logs `(1+log X)` on the
top-carry entries are killed by the `X^{-2u}` deflation (`log_absorb`:
`1+log X ≤ 1+X^u ≤ X^{2u} ≤ X^{2uk}`, from `hlog : log X ≤ X^u` and `X^{1/100} ≥ 2²⁴` ⟹
`X^u ≥ log X ≥ 200`); the ARB-1 squared logs on `n1/n2/tc9/tc10` by `log_absorb_sq`.
-/

open Classical Finset

namespace Squarefree.OnStripAux

open Squarefree

set_option maxHeartbeats 1600000

/-- Master entry discharger: `sec7_envC·(10⁻²⁵·Wnz)^k ≤ H^A x^B G^C Ω^D` whenever
`(A,B,C,D) = k·(a,b,c,d)` and the root comparison `Wnz ≤ H^a x^b G^c Ω^d` holds on the strip
(via `Wnz_le_mono`).  Needs `k ≥ 8` so that `sec7_envC·(10⁻²⁵)^k ≤ 1`. -/
private theorem env_master (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (k : ℕ) (hk : 8 ≤ k) (a b c d A B C' D' : ℝ)
    (hA : a * k = A) (hB : b * k = B) (hC : c * k = C') (hD : d * k = D')
    (hE : 0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21)) :
    sec7_envC * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k
      ≤ P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
  have hroot := Wnz_le_mono P S c₀ Cu D a b c d hE
  have hWnz := (Wnz_pos P S).le
  have hpow : Wnz P S ^ k ≤ (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ^ k :=
    pow_le_pow_left₀ hWnz hroot k
  have heps : sec7_envC * ((10:ℝ) ^ (-25 : ℤ)) ^ k ≤ 1 := by
    have h1 : ((10:ℝ) ^ (-25 : ℤ)) ^ k = (10:ℝ) ^ ((-25 : ℤ) * k) := by
      rw [← zpow_natCast ((10:ℝ) ^ (-25 : ℤ)) k, ← zpow_mul]
    have h2 : sec7_envC = (10:ℝ) ^ (200 : ℤ) := by norm_num [sec7_envC]
    rw [h1, h2, ← zpow_add₀ (by norm_num : (10:ℝ) ≠ 0)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  have hexpand : (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ^ k
      = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
    rw [mul_pow, mul_pow, mul_pow,
        ← Real.rpow_natCast (P.H ^ a) k, ← Real.rpow_natCast (S.x ^ b) k,
        ← Real.rpow_natCast (P.G ^ c) k, ← Real.rpow_natCast (S.Ω ^ d) k,
        ← Real.rpow_mul hH.le, ← Real.rpow_mul hx.le, ← Real.rpow_mul hG.le,
        ← Real.rpow_mul hΩ.le, hA, hB, hC, hD]
  calc sec7_envC * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k
      = sec7_envC * ((10:ℝ) ^ (-25 : ℤ)) ^ k * Wnz P S ^ k := by rw [mul_pow]; ring
    _ ≤ 1 * (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ^ k :=
        mul_le_mul heps hpow (pow_nonneg hWnz k) zero_le_one
    _ = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by rw [one_mul, hexpand]

/-- ARB-2 master entry discharger for the four `sec7_envC2`-entries `n4–n7`: as
`env_master`, but with `sec7_envC2 = 10³⁰⁰`, needing `k ≥ 12` so that
`sec7_envC2·(10⁻²⁵)^k ≤ 1` (the four entries have `k = 18, 42, 30, 54`). -/
private theorem env_master2 (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (k : ℕ) (hk : 12 ≤ k) (a b c d A B C' D' : ℝ)
    (hA : a * k = A) (hB : b * k = B) (hC : c * k = C') (hD : d * k = D')
    (hE : 0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21)) :
    sec7_envC2 * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k
      ≤ P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
  have hroot := Wnz_le_mono P S c₀ Cu D a b c d hE
  have hWnz := (Wnz_pos P S).le
  have hpow : Wnz P S ^ k ≤ (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ^ k :=
    pow_le_pow_left₀ hWnz hroot k
  have heps : sec7_envC2 * ((10:ℝ) ^ (-25 : ℤ)) ^ k ≤ 1 := by
    have h1 : ((10:ℝ) ^ (-25 : ℤ)) ^ k = (10:ℝ) ^ ((-25 : ℤ) * k) := by
      rw [← zpow_natCast ((10:ℝ) ^ (-25 : ℤ)) k, ← zpow_mul]
    have h2 : sec7_envC2 = (10:ℝ) ^ (300 : ℤ) := by
      rw [sec7_envC2, show (300:ℤ) = ((300:ℕ):ℤ) by norm_num, zpow_natCast]
    rw [h1, h2, ← zpow_add₀ (by norm_num : (10:ℝ) ≠ 0)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  have hexpand : (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ^ k
      = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
    rw [mul_pow, mul_pow, mul_pow,
        ← Real.rpow_natCast (P.H ^ a) k, ← Real.rpow_natCast (S.x ^ b) k,
        ← Real.rpow_natCast (P.G ^ c) k, ← Real.rpow_natCast (S.Ω ^ d) k,
        ← Real.rpow_mul hH.le, ← Real.rpow_mul hx.le, ← Real.rpow_mul hG.le,
        ← Real.rpow_mul hΩ.le, hA, hB, hC, hD]
  calc sec7_envC2 * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k
      = sec7_envC2 * ((10:ℝ) ^ (-25 : ℤ)) ^ k * Wnz P S ^ k := by rw [mul_pow]; ring
    _ ≤ 1 * (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d) ^ k :=
        mul_le_mul heps hpow (pow_nonneg hWnz k) zero_le_one
    _ = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by rw [one_mul, hexpand]

/-- AM-7 log absorption (master per-`k` lemma): `(1+log X)·(X^{-2u})^k ≤ 1` for `k ≥ 1`.
From `hlog : log X ≤ X^u` and `X^{1/100} ≥ 2²⁴` one gets `X^u ≥ log X ≥ 200`, whence
`1 + log X ≤ 1 + X^u ≤ X^u·X^u = X^{2u} ≤ X^{2uk}`. -/
private theorem log_absorb (P : Globals) (hu : 0 ≤ P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) (hlog : Real.log P.X ≤ P.X ^ P.u)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + Real.log P.X) * (P.X ^ (-(2:ℝ) * P.u)) ^ k ≤ 1 := by
  have hX0 : (0:ℝ) < P.X := P.X_pos
  have hX1 : (1:ℝ) ≤ P.X := by
    by_contra h
    push_neg at h
    have : P.X ^ (1/100 : ℝ) ≤ 1 :=
      Real.rpow_le_one hX0.le h.le (by norm_num)
    linarith
  -- `log X ≥ 200` from `X^{1/100} ≥ 2²⁴ > e²`
  have he2 : Real.exp 2 ≤ 16777216 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hl24 : (2:ℝ) ≤ Real.log 16777216 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr he2
  have hlX : (200:ℝ) ≤ Real.log P.X := by
    have hm : Real.log 16777216 ≤ Real.log (P.X ^ (1/100 : ℝ)) :=
      Real.log_le_log (by norm_num) hX24
    rw [Real.log_rpow hX0] at hm
    linarith
  have ht2 : (2:ℝ) ≤ P.X ^ P.u := le_trans (by linarith) hlog
  -- `1 + log X ≤ X^{2uk}`
  have key : 1 + Real.log P.X ≤ P.X ^ ((2:ℝ) * P.u * k) := by
    have h1 : 1 + Real.log P.X ≤ P.X ^ P.u * P.X ^ P.u := by nlinarith
    have h2 : P.X ^ P.u * P.X ^ P.u = P.X ^ ((2:ℝ) * P.u) := by
      rw [← Real.rpow_add hX0]; congr 1; ring
    have h3 : P.X ^ ((2:ℝ) * P.u) ≤ P.X ^ ((2:ℝ) * P.u * k) := by
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      nlinarith
    rw [h2] at h1
    linarith
  have hpow : (P.X ^ (-(2:ℝ) * P.u)) ^ k = (P.X ^ ((2:ℝ) * P.u * k))⁻¹ := by
    rw [← Real.rpow_natCast (P.X ^ (-(2:ℝ) * P.u)) k, ← Real.rpow_mul hX0.le,
        show -(2:ℝ) * P.u * (k:ℝ) = -((2:ℝ) * P.u * k) by ring, Real.rpow_neg hX0.le]
  have hp : (0:ℝ) < P.X ^ ((2:ℝ) * P.u * k) := Real.rpow_pos_of_pos hX0 _
  rw [hpow]
  calc (1 + Real.log P.X) * (P.X ^ ((2:ℝ) * P.u * k))⁻¹
      ≤ P.X ^ ((2:ℝ) * P.u * k) * (P.X ^ ((2:ℝ) * P.u * k))⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hp.le)
    _ = 1 := mul_inv_cancel₀ hp.ne'

/-- ARB-1 squared-log absorption: `(1+log X)²·(X^{-2u})^k ≤ 1` for `k ≥ 2` (square the
`k = 1` instance of `log_absorb` and dominate the leftover `(X^{-2u})^{k-2}` by `1`). -/
private theorem log_absorb_sq (P : Globals) (hu : 0 ≤ P.u)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) (hlog : Real.log P.X ≤ P.X ^ P.u)
    (k : ℕ) (hk : 2 ≤ k) :
    (1 + Real.log P.X) ^ 2 * (P.X ^ (-(2:ℝ) * P.u)) ^ k ≤ 1 := by
  have hX0 : (0:ℝ) < P.X := P.X_pos
  have hX1 : (1:ℝ) ≤ P.X := by
    by_contra h
    push_neg at h
    have : P.X ^ (1/100 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le h.le (by norm_num)
    linarith
  set L : ℝ := 1 + Real.log P.X with hLdef
  set b : ℝ := P.X ^ (-(2:ℝ) * P.u) with hbdef
  have hb0 : (0:ℝ) ≤ b := (Real.rpow_pos_of_pos hX0 _).le
  have hL0 : (0:ℝ) ≤ L := by
    have := Real.log_nonneg hX1; rw [hLdef]; linarith
  have h1 : L * b ≤ 1 := by
    have h := log_absorb P hu hX24 hlog 1 le_rfl
    rwa [pow_one] at h
  have hb1 : b ^ (k - 2) ≤ 1 := by
    refine pow_le_one₀ hb0 ?_
    exact Real.rpow_le_one_of_one_le_of_nonpos hX1 (by nlinarith)
  have hbk : b ^ k = b * b * b ^ (k - 2) := by
    rw [show b * b = b ^ 2 from (sq b).symm, ← pow_add]
    congr 1
    omega
  calc L ^ 2 * b ^ k = (L * b) * (L * b) * b ^ (k - 2) := by rw [hbk]; ring
    _ ≤ 1 * 1 * 1 := by
        refine mul_le_mul (mul_le_mul h1 h1 (mul_nonneg hL0 hb0) zero_le_one) hb1
          (pow_nonneg hb0 _) (by norm_num)
    _ = 1 := by norm_num

/-- **The §7 full envelope at `W = 10⁻²⁵·X^{-2u}·Wnz`** (Sec7Envelope discharge on the strip).
All 25 power-form entries close from the single uniform budget `Budget g u Cu`
(`18977g + (18675+790·Cu)u ≤ 2`), exactly as `admissibleW_Wnz`; the `ε = 10⁻²⁵` prefactor
absorbs `sec7_envC = 10²⁰⁰` since every entry power is `k ≥ 8`, and the `X^{-2u}` deflation
kills the AM-7 logs on the ten top-carry entries (`log_absorb`). -/
theorem sec7Envelope_Wnz (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (hXgt : 1 < P.X) (hg : 0 ≤ P.g) (hu : 0 ≤ P.u) (hbud : Budget P.g P.u Cu)
    (hX24 : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ)) (hlog : Real.log P.X ≤ P.X ^ P.u) :
    Sec7Envelope P S ((10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * Wnz P S) := by
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (16995 + 790 * Cu) * P.u ≤ 2 := by
    have h := hbud
    unfold Budget at h
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1680) hu]
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu (by linarith)
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  have hG0 : P.G ≠ 0 := hG.ne'
  have hΩ0 : S.Ω ≠ 0 := hΩ.ne'
  have hx0 : S.x ≠ 0 := hx.ne'
  have hWpos : (0:ℝ) < (10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * Wnz P S := by
    have h1 := Wnz_pos P S
    have h2 : (0:ℝ) < P.X ^ (-(2:ℝ) * P.u) := Real.rpow_pos_of_pos P.X_pos _
    positivity
  set Wf : ℝ := (10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * Wnz P S with hWfdef
  -- split `Wf^k` into the deflation power times the old `(10⁻²⁵·Wnz)^k`
  have hWsplit : ∀ k : ℕ, Wf ^ k
      = (P.X ^ (-(2:ℝ) * P.u)) ^ k * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k := by
    intro k
    rw [hWfdef, show (10:ℝ) ^ (-25 : ℤ) * P.X ^ (-(2:ℝ) * P.u) * Wnz P S
        = P.X ^ (-(2:ℝ) * P.u) * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) by ring, mul_pow]
  have hbase_nn : ∀ k : ℕ, (0:ℝ) ≤ sec7_envC * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k := by
    intro k
    have h1 : (0:ℝ) ≤ (10:ℝ) ^ (-25 : ℤ) * Wnz P S :=
      mul_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 10) _) (Wnz_pos P S).le
    exact mul_nonneg sec7_envC_pos.le (pow_nonneg h1 k)
  have hxk : ∀ k : ℕ, (P.X ^ (-(2:ℝ) * P.u)) ^ k ≤ 1 := by
    intro k
    refine pow_le_one₀ (Real.rpow_nonneg (by linarith [D.hX]) _) ?_
    exact Real.rpow_le_one_of_one_le_of_nonpos D.hX (by linarith)
  -- master entry dischargers at `Wf` (without / with the AM-7 log)
  have hEM : ∀ (k : ℕ), 8 ≤ k → ∀ a b c d A B C' D' : ℝ,
      a * k = A → b * k = B → c * k = C' → d * k = D' →
      0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21) →
      sec7_envC * Wf ^ k ≤ P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
    intro k hk a b c d A B C' D' hA hB hC hD hE
    have hold := env_master P S c₀ Cu D k hk a b c d A B C' D' hA hB hC hD hE
    calc sec7_envC * Wf ^ k
        = (P.X ^ (-(2:ℝ) * P.u)) ^ k
            * (sec7_envC * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k) := by rw [hWsplit k]; ring
      _ ≤ 1 * (P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D') :=
          mul_le_mul (hxk k) hold (hbase_nn k) zero_le_one
      _ = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := one_mul _
  have hEML : ∀ (k : ℕ), 8 ≤ k → ∀ a b c d A B C' D' : ℝ,
      a * k = A → b * k = B → c * k = C' → d * k = D' →
      0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21) →
      sec7_envC * Wf ^ k * (1 + Real.log P.X)
        ≤ P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
    intro k hk a b c d A B C' D' hA hB hC hD hE
    have hold := env_master P S c₀ Cu D k hk a b c d A B C' D' hA hB hC hD hE
    have hL := log_absorb P hu hX24 hlog k (by omega)
    calc sec7_envC * Wf ^ k * (1 + Real.log P.X)
        = ((1 + Real.log P.X) * (P.X ^ (-(2:ℝ) * P.u)) ^ k)
            * (sec7_envC * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k) := by rw [hWsplit k]; ring
      _ ≤ 1 * (P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D') :=
          mul_le_mul hL hold (hbase_nn k) zero_le_one
      _ = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := one_mul _
  -- ARB-2 discharger for the `sec7_envC2`-entries `n4–n7` (`k ≥ 12`)
  have hEM2 : ∀ (k : ℕ), 12 ≤ k → ∀ a b c d A B C' D' : ℝ,
      a * k = A → b * k = B → c * k = C' → d * k = D' →
      0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21) →
      sec7_envC2 * Wf ^ k ≤ P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
    intro k hk a b c d A B C' D' hA hB hC hD hE
    have hold := env_master2 P S c₀ Cu D k hk a b c d A B C' D' hA hB hC hD hE
    have hb2 : (0:ℝ) ≤ sec7_envC2 * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k :=
      mul_nonneg sec7_envC2_pos.le (pow_nonneg
        (mul_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 10) _) (Wnz_pos P S).le) k)
    calc sec7_envC2 * Wf ^ k
        = (P.X ^ (-(2:ℝ) * P.u)) ^ k
            * (sec7_envC2 * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k) := by rw [hWsplit k]; ring
      _ ≤ 1 * (P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D') :=
          mul_le_mul (hxk k) hold hb2 zero_le_one
      _ = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := one_mul _
  -- ARB-1/ARB-2 squared-log discharger for `n1/n2/n3/res1/res2/tc9/tc10` (`k ≥ 8 ≥ 2`)
  have hEMLsq : ∀ (k : ℕ), 8 ≤ k → ∀ a b c d A B C' D' : ℝ,
      a * k = A → b * k = B → c * k = C' → d * k = D' →
      0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21) →
      sec7_envC * Wf ^ k * (1 + Real.log P.X) ^ 2
        ≤ P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := by
    intro k hk a b c d A B C' D' hA hB hC hD hE
    have hold := env_master P S c₀ Cu D k hk a b c d A B C' D' hA hB hC hD hE
    have hL := log_absorb_sq P hu hX24 hlog k (by omega)
    calc sec7_envC * Wf ^ k * (1 + Real.log P.X) ^ 2
        = ((1 + Real.log P.X) ^ 2 * (P.X ^ (-(2:ℝ) * P.u)) ^ k)
            * (sec7_envC * ((10:ℝ) ^ (-25 : ℤ) * Wnz P S) ^ k) := by rw [hWsplit k]; ring
      _ ≤ 1 * (P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D') :=
          mul_le_mul hL hold (hbase_nn k) zero_le_one
      _ = P.H ^ A * S.x ^ B * P.G ^ C' * S.Ω ^ D' := one_mul _
  refine
    { W_pos := hWpos
      n1 := ?_, n2 := ?_, n3 := ?_, n4 := ?_, n5 := ?_, n6 := ?_, n7 := ?_, n8 := ?_, n9 := ?_
      res1 := ?_, res2 := ?_, res3 := ?_, res4 := ?_
      off1 := ?_, off2 := ?_
      tc1 := ?_, tc2 := ?_, tc3 := ?_, tc4 := ?_, tc5 := ?_
      tc6 := ?_, tc7 := ?_, tc8 := ?_, tc9 := ?_, tc10 := ?_
      R_gt_one := ?_, T1_gt_one := ?_ }
  -- n1 = e01^16 (ARB-1: squared log)
  · refine le_trans (hEMLsq 16 (by norm_num) (1/16) (5/16) 0 (1/4)
      1 5 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- n2 = e02^28 (ARB-1: squared log)
  · refine le_trans (hEMLsq 28 (by norm_num) (1/28) (5/28) (1/14) (1/2)
      1 5 2 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- n3 = e03^40 (ARB-2/A6: squared log)
  · refine le_trans (hEMLsq 40 (by norm_num) (1/40) (1/8) (1/5) (3/5)
      1 5 8 24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- n4 = e04^18 (factors G⁶Ω¹⁴ moved left; ARB-2: `sec7_envC2`, k = 18 ≥ 12)
  · have h := hEM2 18 (by norm_num) (1/18) (1/18) (-1/3) (-7/9)
      1 1 (-6) (-14) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC2 * (Wf ^ 18 * P.G ^ 6 * S.Ω ^ 14)
        = sec7_envC2 * Wf ^ 18 * (P.G ^ 6 * S.Ω ^ 14) := by ring
      _ ≤ P.H ^ (1:ℝ) * S.x ^ (1:ℝ) * P.G ^ ((-6):ℝ) * S.Ω ^ ((-14):ℝ)
            * (P.G ^ 6 * S.Ω ^ 14) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = P.H * S.x := by
          rw [Real.rpow_one, Real.rpow_one, Real.rpow_neg hG.le, Real.rpow_neg hΩ.le,
              Real.rpow_ofNat, Real.rpow_ofNat]
          field_simp
  -- n5 = e05^42 (factor G² moved left; ARB-2: `sec7_envC2`, k = 42 ≥ 12)
  · have h := hEM2 42 (by norm_num) (1/42) (1/42) (-1/21) (1/7)
      1 1 (-2) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC2 * (Wf ^ 42 * P.G ^ 2)
        = sec7_envC2 * Wf ^ 42 * P.G ^ 2 := by ring
      _ ≤ P.H ^ (1:ℝ) * S.x ^ (1:ℝ) * P.G ^ ((-2):ℝ) * S.Ω ^ (6:ℝ) * P.G ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = P.H * S.x * S.Ω ^ 6 := by
          rw [Real.rpow_one, Real.rpow_one, Real.rpow_neg hG.le,
              Real.rpow_ofNat, Real.rpow_ofNat]
          field_simp
  -- n6 = e06^30 (factor Ω⁴ moved left; ARB-2: `sec7_envC2`, k = 30 ≥ 12)
  · have h := hEM2 30 (by norm_num) (1/30) (1/30) 0 (-2/15)
      1 1 0 (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC2 * (Wf ^ 30 * S.Ω ^ 4)
        = sec7_envC2 * Wf ^ 30 * S.Ω ^ 4 := by ring
      _ ≤ P.H ^ (1:ℝ) * S.x ^ (1:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ ((-4):ℝ) * S.Ω ^ 4 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = P.H * S.x := by
          rw [Real.rpow_one, Real.rpow_one, Real.rpow_zero, mul_one,
              Real.rpow_neg hΩ.le, Real.rpow_ofNat]
          field_simp
  -- n7 = e07^54 (ARB-2: `sec7_envC2`, k = 54 ≥ 12)
  · refine le_trans (hEM2 54 (by norm_num) (1/54) (1/54) (2/27) (8/27)
      1 1 4 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- n8 = e08^30
  · refine le_trans (hEM 30 (by norm_num) (1/30) (1/6) (4/15) (4/5)
      1 5 8 24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- n9 = e09^42
  · refine le_trans (hEM 42 (by norm_num) (1/42) (5/42) (5/21) (17/21)
      1 5 10 34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- res1: root (3/16,1/16,1/8,1/8), k=16 (ARB-2/A6: squared log)
  · refine le_trans (hEMLsq 16 (by norm_num) (3/16) (1/16) (1/8) (1/8)
      3 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- res2: root (3/28,1/28,1/7,3/7), k=28 (ARB-2/A6: squared log)
  · refine le_trans (hEMLsq 28 (by norm_num) (3/28) (1/28) (1/7) (3/7)
      3 1 4 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- res3: root (1/6,−1/6,−2/9,−8/9), k=18, constant-free (x³G⁴Ω¹⁶ moved left)
  · have h := hEM 18 (by norm_num) (1/6) (-1/6) (-2/9) (-8/9)
      3 (-3) (-4) (-16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC * (Wf ^ 18 * S.x ^ 3 * P.G ^ 4 * S.Ω ^ 16)
        = sec7_envC * Wf ^ 18 * (S.x ^ 3 * P.G ^ 4 * S.Ω ^ 16) := by ring
      _ ≤ P.H ^ (3:ℝ) * S.x ^ ((-3):ℝ) * P.G ^ ((-4):ℝ) * S.Ω ^ ((-16):ℝ)
            * (S.x ^ 3 * P.G ^ 4 * S.Ω ^ 16) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = P.H ^ 3 := by
          rw [Real.rpow_neg hx.le, Real.rpow_neg hG.le, Real.rpow_neg hΩ.le,
              Real.rpow_ofNat, Real.rpow_ofNat, Real.rpow_ofNat, Real.rpow_ofNat]
          field_simp
  -- res4: root (1/14,−1/14,0,2/21), k=42, constant-free (x³ moved left)
  · have h := hEM 42 (by norm_num) (1/14) (-1/14) 0 (2/21)
      3 (-3) 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC * (Wf ^ 42 * S.x ^ 3)
        = sec7_envC * Wf ^ 42 * S.x ^ 3 := by ring
      _ ≤ P.H ^ (3:ℝ) * S.x ^ ((-3):ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (4:ℝ) * S.x ^ 3 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = P.H ^ 3 * S.Ω ^ 4 := by
          rw [Real.rpow_zero, mul_one, Real.rpow_neg hx.le,
              Real.rpow_ofNat, Real.rpow_ofNat, Real.rpow_ofNat]
          field_simp
  -- off1 = e20^12
  · refine le_trans (hEM 12 (by norm_num) (1/24) (5/24) (1/4) (7/12)
      ((1:ℝ)/2) ((5:ℝ)/2) 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- off2 = e21^18
  · refine le_trans (hEM 18 (by norm_num) (1/36) (5/36) (2/9) (2/3)
      ((1:ℝ)/2) ((5:ℝ)/2) 4 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- tc1 = e10^8
  · refine le_trans (hEML 8 (by norm_num) (1/48) (5/48) (1/8) (7/24)
      ((1:ℝ)/6) ((5:ℝ)/6) 1 ((7:ℝ)/3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- tc2 = e11^8 (pure rpow target)
  · exact hEML 8 (by norm_num) (1/16) (1/16) (-1/16) (1/16)
      ((1:ℝ)/2) ((1:ℝ)/2) (-(1:ℝ)/2) ((1:ℝ)/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
  -- tc3 = e12^11
  · refine le_trans (hEML 11 (by norm_num) (1/22) (1/22) (1/11) (3/11)
      ((1:ℝ)/2) ((1:ℝ)/2) 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- tc4 = e13^8
  · refine le_trans (hEML 8 (by norm_num) (1/16) (1/16) (1/8) (3/8)
      ((1:ℝ)/2) ((1:ℝ)/2) 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- tc5 = e14^14 (the Wnz root itself)
  · refine le_trans (hEML 14 (by norm_num) (1/84) (5/84) (1/7) (11/21)
      ((1:ℝ)/6) ((5:ℝ)/6) 2 ((22:ℝ)/3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by unfold ratioExp; norm_num)) (le_of_eq ?_)
    simp
  -- tc6 = e15^14 (pure rpow target)
  · exact hEML 14 (by norm_num) (1/28) (1/28) (1/28) (11/28)
      ((1:ℝ)/2) ((1:ℝ)/2) ((1:ℝ)/2) ((11:ℝ)/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
  -- tc7 = e16^17
  · refine le_trans (hEML 17 (by norm_num) (1/34) (1/34) (2/17) (8/17)
      ((1:ℝ)/2) ((1:ℝ)/2) 2 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- tc8 = e17^14
  · refine le_trans (hEML 14 (by norm_num) (1/28) (1/28) (1/7) (4/7)
      ((1:ℝ)/2) ((1:ℝ)/2) 2 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])) (le_of_eq ?_)
    simp
  -- tc9 = e18^16 (factor x moved left; ARB-1: squared log)
  · have h := hEMLsq 16 (by norm_num) (1/16) (-1/16) 0 0
      1 (-1) 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC * (Wf ^ 16 * S.x) * (1 + Real.log P.X) ^ 2
        = sec7_envC * Wf ^ 16 * (1 + Real.log P.X) ^ 2 * S.x := by ring
      _ ≤ P.H ^ (1:ℝ) * S.x ^ ((-1):ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (0:ℝ) * S.x :=
          mul_le_mul_of_nonneg_right h hx.le
      _ = P.H := by
          rw [Real.rpow_one, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one,
              Real.rpow_neg hx.le, Real.rpow_one]
          field_simp
  -- tc10 = e19^28 (factor x moved left; ARB-1: squared log)
  · have h := hEMLsq 28 (by norm_num) (1/28) (-1/28) (1/14) (5/14)
      1 (-1) 2 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
    calc sec7_envC * (Wf ^ 28 * S.x) * (1 + Real.log P.X) ^ 2
        = sec7_envC * Wf ^ 28 * (1 + Real.log P.X) ^ 2 * S.x := by ring
      _ ≤ P.H ^ (1:ℝ) * S.x ^ ((-1):ℝ) * P.G ^ (2:ℝ) * S.Ω ^ (10:ℝ) * S.x :=
          mul_le_mul_of_nonneg_right h hx.le
      _ = P.H * P.G ^ 2 * S.Ω ^ 10 := by
          rw [Real.rpow_one, Real.rpow_neg hx.le, Real.rpow_one,
              Real.rpow_ofNat, Real.rpow_ofNat]
          field_simp
  -- R > 1
  · rw [R_mono]
    exact one_lt_mono P S c₀ Cu D hXgt (1/2) (1/2) 1 3
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])
  -- T₁ > 1
  · rw [T1_mono]
    exact one_lt_mono P S c₀ Cu D hXgt (1/2) (-3/2) (-1) (-1)
      (by unfold ratioExp; norm_num; nlinarith [hbud', hg, hu, huCu, huCu1])

end Squarefree.OnStripAux
