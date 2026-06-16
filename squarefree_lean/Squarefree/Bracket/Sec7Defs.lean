import Squarefree.Params
import Squarefree.FiniteDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

/-!
# §7 definitional layer (plan nodes N1–N2)

Definitions and hypothesis bundles for §7 of `../explicit_writeup.md` (md 1299–1386):
the threshold `δ₀` (md 1360, AS DISPLAYED — TRAP-1), the phase-data bundle `Sec7Phase`
(md 1327–31 inverse-function scales + md 1509–14 derivative windows), the bundled full
admissibility envelope `Sec7Envelope` (md 1421–1451), and the scale identities
`T₁·T₂ = T₃`, `T₂/R² = 1/(GΩ⁵)`, `R·T₁ = A²` (md 1382–86; sympy-banked).

## Constant ledger (absolute constants; see tools/sec7_ledger.py)
* `sec7_cPh = 10¹²` — the two-sided `≍` comparability constant in all `Sec7Phase` scale
  facts (the md uses bare `≍`; CLAUDE.md §7 → named generous absolute constant).
* `sec7_cWin = 10³` — window aperture for the `t ≍ F` window `[F/10³, 10³F]`.
* `sec7_cExpIn = 10¹⁶` — input-side residual-expansion constant for the concrete §3
  residuals, bounded by the output expansion budget `sec7_cExp = 10²⁵`.
* `sec7_cJ = 10²⁰` — the `j`-band constant in `|j| ≪ 1 + H/A²` (md 1307–09).  G1+U3 bump:
  N3's `hprox` is discharged by `ftil_prox` (Sec7Prox.lean) at `10¹⁸·(H/A²)`, so the band
  needs `≥ 2·10¹⁸` (sympy-banked, tools/sec7_ledger.py U4).
* `sec7_cTay = 10¹²` — N4's conclusion-threshold constant (AM-1; A1-gate bump): the branch
  reduction filters at `sec7_cTay·δ₀`, absorbing the G≥1 Taylor budget `cPh·(HΔ/F²) ≤
  cPh·(Δ⁵/(H³Ω²))` (chain `HΔ/F² = (Δ⁵/(H³Ω²))·G⁻²`, sympy-banked) and the `hd` piece:
  `cTay = max(cPh, cdMar)`.
* `sec7_cdMar = 10⁷` — the md-1325 `d`-proximity constant of N4's `hd` (A1 gate: the only
  producer route — mean value through `d̆'` × the Prop-3.2 near-integrality — has floor
  `2·cPh = 2·10⁶` on the scale `Δ²/(H²GA)`; the old `1/2` was undischargeable).
* `sec7_cN6 = 10¹⁴` — N6's eq-(7.1) error constant (A1 gate: ≥4 Leibniz `|T|≥2` terms plus
  ~3 realignment second-differences total ≲ 40·cPh; `10²·cPh` gives slack).  Riders:
  N8's `hprod` carries it, and `sec7_cCal` is kept in `Sec7ZeroScale.lean`.
* `sec7_envC = 10²⁰⁰` — the "sufficiently small absolute constant" of the envelope's
  `≪`-entries (md 1419), transcribed hypothesis-side as `sec7_envC · Wᵏ ≤ (monomial)`.
  Call sites discharge it from the strip's `X^{O(u)}` slack.
* `sec7_envC2 = 10³⁰⁰` — ARB-2 per-entry split: the four entries `n4–n7` are the exact
  ¹⁄₄-power fits of the harvest's z4/z4f/z5/z5f terms (binding chain
  `18·cTriple·harvM·cBox = 1.8·10⁶⁴` at `cTriple = 10⁵⁶`, content `10²⁵⁸ ≤ 10³⁰⁰`);
  they carry the larger constant, absorbed on-strip at `ε = 10⁻²⁵` since their powers
  are `k ≥ 18 ≥ 12`.
* ARB-1/ARB-2 (AM-7 sharpened, A6): the seven envelope entries
  `n1, n2, n3, res1, res2, tc9, tc10` carry the SQUARED log `(1 + log X)²`
  (Prop-4.3 engine log × harvest log), killed on-strip by `log_absorb_sq`
  (`Opt/OnStripEnvelope.lean`); zero-branch consumption is unchanged since
  `(1 + log X)² ≥ 1`.
-/

open Classical Finset

namespace Squarefree

open Squarefree.FiniteDiff

/-- `≍`-comparability constant for the §7 phase scale facts (ledger). -/
def sec7_cPh : ℝ := 10 ^ 10

/-- Window aperture for the §7 `t ≍ F` range (ledger). -/
def sec7_cWin : ℝ := 10 ^ 3

/-- Input-side residual-expansion constant for the §3→§7 monomial package. -/
def sec7_cExpIn : ℝ := 10 ^ 25

/-- `j`-band constant: the §7 shifts satisfy `|j| ≤ sec7_cJ·(1 + H/A²)` (md 1307–09).
G1+U3: `10²⁰ ≥ 2·10¹⁸`, the `ftil_prox` discharge level (ledger U4). -/
def sec7_cJ : ℝ := 10 ^ 20

/-- N4 conclusion-threshold constant (AM-1, A1-gate bump; ledger U4): the branch
reduction's filter runs at `sec7_cTay · sec7_delta0`; `cTay = max(cPh, cdMar)`. -/
def sec7_cTay : ℝ := 10 ^ 10

/-- The md-1325 `d`-proximity constant of N4's `hd` (AM-1, A1-gate bump; ledger U4:
producer floor `2·cPh`, 5× slack). -/
def sec7_cdMar : ℝ := 10 ^ 7

/-- N6 eq-(7.1) error constant (A1 gate; ledger U4): `10²·cPh` covers the Leibniz
`|T|≥2` terms and the realignment second-differences. -/
def sec7_cN6 : ℝ := 10 ^ 12

/-- The "sufficiently small absolute constant" of the envelope `≪`-entries (md 1419),
kept hypothesis-side as `sec7_envC · Wᵏ ≤ …` (ledger). -/
def sec7_envC : ℝ := 10 ^ 200

/-- ARB-2 envelope constant for the four binding entries `n4–n7` (the exact ¹⁄₄-power
fits of the harvest chain `18·cTriple·harvM·cBox`; ledger). -/
def sec7_envC2 : ℝ := 10 ^ 300

theorem sec7_cPh_pos : (0:ℝ) < sec7_cPh := by norm_num [sec7_cPh]
theorem sec7_cWin_pos : (0:ℝ) < sec7_cWin := by norm_num [sec7_cWin]
theorem sec7_cExpIn_pos : (0:ℝ) < sec7_cExpIn := by norm_num [sec7_cExpIn]
theorem sec7_cJ_pos : (0:ℝ) < sec7_cJ := by norm_num [sec7_cJ]
theorem sec7_cTay_pos : (0:ℝ) < sec7_cTay := by norm_num [sec7_cTay]
theorem sec7_cdMar_pos : (0:ℝ) < sec7_cdMar := by norm_num [sec7_cdMar]
theorem sec7_cN6_pos : (0:ℝ) < sec7_cN6 := by norm_num [sec7_cN6]
theorem sec7_envC_pos : (0:ℝ) < sec7_envC := by norm_num [sec7_envC]
theorem sec7_envC2_pos : (0:ℝ) < sec7_envC2 := by norm_num [sec7_envC2]

/- md 1604–06: "a/d̃_a(r) ≪ A/D = Ω/H = X^{-(1-g)/5+O(u)} = o(1)".
   The §7 `+j` shift audit adds the uniform `U^3` budget over the band. -/
/-- The §7 faithful relative-error scale `(Ω/H)·U^3`. -/
noncomputable def sec7_relErr (P : Globals) (S : Scale P) : ℝ := (S.Ω / P.H) * P.U ^ 3

/-- Extra loose polynomial budget for the f₁/f₃ residual route (since `∂_j f₃ = −f₁` makes
those residuals `T₁`-scale, off the tight budget by `≍ G·U^{1/2}`; f₂ stays tight).
⚠ DO NOT BUMP: `G·U^2` sits at the `hrel143` boundary — the Err discharge needs
`sec7_relErrF·10^143 ≤ 1`, and `relErr·G·U^2 ≍ X^{-1/5}` has only ~1.5 orders of slack there.
A larger power (or `>~32×` constant) breaks `sec7_relErrF_le`. Results-invariant as-is:
`prop_7_1`/`prop_7_3` and `δ=2/94885` are residual-magnitude-independent. -/
noncomputable def sec7_cGU (P : Globals) (_S : Scale P) : ℝ := P.G * P.U ^ 2

/-- Loosened f₁/f₃ relative-error scale.  After the `hG10x`-deletion re-pin this is the
power-saving budget `X^{-19/100}` directly (the old `relErr·G·U^2` product was regime-false
on-strip via the `x = H/Δ² = O(1)` factor; `sec7_ra_jF_powersaving` supplies `|j|/F ≤ X^{-19/100}`
from the strip lower bound instead).  `sec7_cGU`/`sec7_relErr` are kept as defs (still used by
f₂'s tight route and possibly other call sites). -/
noncomputable def sec7_relErrF (P : Globals) (_S : Scale P) : ℝ :=
  P.X ^ (-(19 : ℝ) / 100)

/- md 1358–1361 (display, TRAP-1: use AS DISPLAYED, the larger `Δ⁵/(H³Ω²)` form, NOT the
   md-1352 `G²`-identity):
   "δ₀ := (Δ⁵/H³)(Δ/A)² + Δ²/(H²GA)". -/
/-- §7 threshold `δ₀` (md 1360, verbatim display). Since `A = ΔΩ` this equals
`Δ⁵/(H³Ω²) + Δ²/(H²GA)` (`sec7_delta0_eq`). -/
noncomputable def sec7_delta0 (P : Globals) (S : Scale P) : ℝ :=
  S.Δ ^ 5 / P.H ^ 3 * (S.Δ / S.A) ^ 2 + S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A)

/-- `δ₀ = Δ⁵/(H³Ω²) + Δ²/(H²GA)` (md 1360 with `A = ΔΩ`). -/
theorem sec7_delta0_eq (P : Globals) (S : Scale P) :
    sec7_delta0 P S =
      S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) + S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A) := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hH := P.H_pos
  unfold sec7_delta0 Scale.A
  field_simp

/- md 1371–1380: scales (already defs in `Params.lean`): `T₁ := HΔ/F`, `T₂ := F`, `T₃ := HΔ`.
   md 1382–86: "T₁/R = x⁻²G⁻²Ω⁻⁴, T₂/R² = G⁻¹Ω⁻⁵, T₃/R³ = G⁻³Ω⁻⁹x⁻²."
   Identity ledger (sympy: tools/sec7_ledger.py): T₁·T₂ = T₃, T₂/R² = 1/(GΩ⁵), R·T₁ = A². -/

/-- `T₁·T₂ = T₃` (md 1373–79; ledger alias of `Scale.T₁_mul_T₂_eq_T₃`). -/
theorem sec7_T₁_mul_T₂ {P : Globals} (S : Scale P) : S.T₁ * S.T₂ = S.T₃ :=
  S.T₁_mul_T₂_eq_T₃

/-- `T₂/R² = 1/(GΩ⁵)` (md 1384; sympy-banked). -/
theorem sec7_T₂_div_R_sq {P : Globals} (S : Scale P) :
    S.T₂ / S.R ^ 2 = 1 / (P.G * S.Ω ^ 5) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.T₂ Scale.F Scale.R
  field_simp

/-- `R·T₁ = A²` (md 1373/1383 with `A = ΔΩ`; the N17 pivot `T_{ρ,q} ≍ T₁`; sympy-banked). -/
theorem sec7_R_mul_T₁ {P : Globals} (S : Scale P) : S.R * S.T₁ = S.A ^ 2 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.R Scale.T₁ Scale.F Scale.A
  field_simp

/- md 1330: the inverse-function scales hold "(t ≍ F)"; md 1509–14 hold on the
   widened nonzero-engine window `R/144 ≤ r ≤ 40R` (and its `h`-shifted points). -/
/-- The §7 `t ≍ F` window `[F/cWin, cWin·F]` (md 1330). -/
noncomputable def sec7_tWin {P : Globals} (S : Scale P) : Set ℝ :=
  Set.Icc (S.F / sec7_cWin) (sec7_cWin * S.F)

/-- The §7 `r` window `[R/144, 40R]` with two additive shift pads. -/
noncomputable def sec7_rWin {P : Globals} (S : Scale P) (W : ℝ) : Set ℝ :=
  Set.Icc (S.R / 144 - 2 * (W + W ^ 2 + W ^ 4))
    (40 * S.R + 2 * (W + W ^ 2 + W ^ 4))

/-- The wide §7 `r` window where the §3 expansion data live. -/
noncomputable def sec7_rWinWide {P : Globals} (S : Scale P) (W : ℝ) : Set ℝ :=
  Set.Ioo (S.R / 144 - 6 * (W + W ^ 2 + W ^ 4))
    (40 * S.R + 6 * (W + W ^ 2 + W ^ 4))

/-- The mid §7 `r` window, sandwiched `rWin ⊆ mid`, `mid + shifts ⊆ wide`. -/
noncomputable def sec7_rWinMid {P : Globals} (S : Scale P) (W : ℝ) : Set ℝ :=
  Set.Ioo (S.R / 144 - 3 * (W + W ^ 2 + W ^ 4))
    (40 * S.R + 3 * (W + W ^ 2 + W ^ 4))

theorem sec7_rWinMid_isOpen {P : Globals} (S : Scale P) (W : ℝ) :
    IsOpen (sec7_rWinMid S W) :=
  isOpen_Ioo

/-- `R > 0` (scale positivity; local helper). -/
theorem sec7_R_pos {P : Globals} (S : Scale P) : 0 < S.R := by
  have := P.H_pos; have := P.G_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold Scale.R; positivity

/-- `sec7_rWin ⊆ sec7_rWinMid` for positive shift scale. -/
theorem sec7_rWin_subset_mid {P : Globals} (S : Scale P) {W : ℝ} (hW : 0 < W) :
    sec7_rWin S W ⊆ sec7_rWinMid S W := by
  intro r hr
  have hpad : 0 < W + W ^ 2 + W ^ 4 := by positivity
  simp only [sec7_rWin, Set.mem_Icc] at hr
  simp only [sec7_rWinMid, Set.mem_Ioo]
  constructor <;> linarith

/-- Displaced points from the mid window stay in the wide window:
`r ∈ mid`, `|s| ≤ 3(W + W² + W⁴)` ⟹ `r + s ∈ wide`. -/
theorem sec7_mid_add_mem_wide {P : Globals} {S : Scale P} {W r s : ℝ}
    (hr : r ∈ sec7_rWinMid S W) (hs : |s| ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    r + s ∈ sec7_rWinWide S W := by
  simp only [sec7_rWinMid, Set.mem_Ioo] at hr
  simp only [sec7_rWinWide, Set.mem_Ioo]
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  constructor <;> linarith

/-- Wide-window points are positive (so the power monomials are smooth there). -/
theorem sec7_rWinWide_pos {P : Globals} {S : Scale P} {W r : ℝ}
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hr : r ∈ sec7_rWinWide S W) : 0 < r := by
  have hR : 0 < S.R := sec7_R_pos S
  simp only [sec7_rWinWide, Set.mem_Ioo] at hr
  linarith

/-- Wide-window points have `1/(2cWin) ≤ r/R` (the sup-bound aperture). -/
theorem sec7_rWinWide_div_lo {P : Globals} {S : Scale P} {W r : ℝ}
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hr : r ∈ sec7_rWinWide S W) : 1 / (2 * sec7_cWin) ≤ r / S.R := by
  have hR : 0 < S.R := sec7_R_pos S
  simp only [sec7_rWinWide, Set.mem_Ioo] at hr
  rw [le_div_iff₀ hR]
  norm_num [sec7_cWin]
  linarith

/- md 1307–09: "For each integer j with |j| ≪ 1 + H/A²". -/
/-- The §7 `j`-band: `|j| ≤ sec7_cJ·(1 + H/A²)` (md 1307–09). -/
def sec7_jBand (P : Globals) (S : Scale P) (j : ℤ) : Prop :=
  (|j| : ℝ) ≤ sec7_cJ * (1 + P.H / S.A ^ 2)

/- md 1327–31: "the inverse-function scale  F·d̆ₐ'(t) ≍ HΔ,  F²·d̆ₐ''(t) ≍ HΔ  (t ≍ F)".
   md 1505–07: "f₃(r) := d̆ₐ(f̃ₐ(r)+j),  f₁(r) := −d̆ₐ'(f̃ₐ(r)+j),  f₂(r) := f̃ₐ(r)".
   md 1509–14: "f₁^{(m)}(r) ≍ T₁/Rᵐ,  f₂^{(m)}(r) ≍ T₂/Rᵐ,  f₃^{(m)}(r) ≍ T₃/Rᵐ". -/
/-- Shift bounds under which the §7 branch phase is `C²` on the count window: the box bounds
`1 ≤ h₁ ≤ W`, `1 ≤ h₂ ≤ W²`, `1 ≤ h₃ ≤ W⁴` (md 1463–66, = `sec7_shiftBox` unfolded) and
`|ξᵢ| ≤ h₁+h₂+h₃` (= `sec7_hSum`).  These keep every `f`-piece argument inside `sec7_rWin`
(the `f₁,f₃` pieces shift up by at most `h_Σ`; the globally-smooth `f₂ = f̃` absorbs the `ξ`).
Stated here (upstream of `sec7_shiftBox`) by inlining the conjuncts. -/
def sec7_phiBound (W : ℝ) (h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ) : Prop :=
  ((1 ≤ h₁ ∧ (h₁ : ℝ) ≤ W) ∧ (1 ≤ h₂ ∧ (h₂ : ℝ) ≤ W ^ 2) ∧ (1 ≤ h₃ ∧ (h₃ : ℝ) ≤ W ^ 4)) ∧
    |ξ₁| ≤ (h₁ : ℝ) + h₂ + h₃ ∧ |ξ₂| ≤ (h₁ : ℝ) + h₂ + h₃ ∧ |ξ₃| ≤ (h₁ : ℝ) + h₂ + h₃

/-- §7 phase data for the fiber `a ∼ A` (md 1299–1331, 1505–14): the functions
`f̃ₐ, d̆ₐ, d̆ₐ', d̆ₐ''` with the inverse-function scales `F·d̆' ≍ HΔ`, `F²·d̆'' ≍ HΔ` on
`t ≍ F`, and the `m`-th derivative families (`m ≤ 3`) of `f₁ = −d̆'(f̃+j)`, `f₂ = f̃`,
`f₃ = d̆(f̃+j)` with the windows `f_i^{(m)} ≍ T_i/Rᵐ` on `r ≍ R` (`j` in the §7 band).
All `≍` carry the absolute constant `sec7_cPh`; `shift_mem` records that the §7 Taylor
points `f̃(r)+j−θ`, `θ ∈ [0,1]` (md 1332–43), stay in the `t`-window. -/
structure Sec7Phase (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) where
  ftil : ℝ → ℝ
  dBreve : ℝ → ℝ
  dBreve' : ℝ → ℝ
  dBreve'' : ℝ → ℝ
  dBreve_hasDeriv : ∀ t ∈ sec7_tWin S, HasDerivAt dBreve (dBreve' t) t
  dBreve'_hasDeriv : ∀ t ∈ sec7_tWin S, HasDerivAt dBreve' (dBreve'' t) t
  Fd'_lo : ∀ t ∈ sec7_tWin S, P.H * S.Δ ≤ sec7_cPh * (S.F * |dBreve' t|)
  Fd'_hi : ∀ t ∈ sec7_tWin S, S.F * |dBreve' t| ≤ sec7_cPh * (P.H * S.Δ)
  F2d''_lo : ∀ t ∈ sec7_tWin S, P.H * S.Δ ≤ sec7_cPh * (S.F ^ 2 * |dBreve'' t|)
  F2d''_hi : ∀ t ∈ sec7_tWin S, S.F ^ 2 * |dBreve'' t| ≤ sec7_cPh * (P.H * S.Δ)
  f1D : ℤ → ℕ → ℝ → ℝ
  f2D : ℕ → ℝ → ℝ
  f3D : ℤ → ℕ → ℝ → ℝ
  f1D_zero : ∀ j r, f1D j 0 r = -dBreve' (ftil r + j)
  f2D_zero : f2D 0 = ftil
  f3D_zero : ∀ j r, f3D j 0 r = dBreve (ftil r + j)
  f1D_hasDeriv : ∀ j, sec7_jBand P S j → ∀ m < 4, ∀ r ∈ sec7_rWin S W,
    HasDerivAt (f1D j m) (f1D j (m + 1) r) r
  f2D_hasDeriv : ∀ m < 4, ∀ r ∈ sec7_rWin S W,
    HasDerivAt (f2D m) (f2D (m + 1) r) r
  f3D_hasDeriv : ∀ j, sec7_jBand P S j → ∀ m < 4, ∀ r ∈ sec7_rWin S W,
    HasDerivAt (f3D j m) (f3D j (m + 1) r) r
  f1D_lo : ∀ j, sec7_jBand P S j → ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
    S.T₁ / S.R ^ m ≤ sec7_cPh * |f1D j m r|
  f1D_hi : ∀ j, sec7_jBand P S j → ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
    |f1D j m r| ≤ sec7_cPh * (S.T₁ / S.R ^ m)
  f2D_lo : ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W, S.T₂ / S.R ^ m ≤ sec7_cPh * |f2D m r|
  f2D_hi : ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W, |f2D m r| ≤ sec7_cPh * (S.T₂ / S.R ^ m)
  f3D_lo : ∀ j, sec7_jBand P S j → ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
    S.T₃ / S.R ^ m ≤ sec7_cPh * |f3D j m r|
  f3D_hi : ∀ j, sec7_jBand P S j → ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
    |f3D j m r| ≤ sec7_cPh * (S.T₃ / S.R ^ m)
  shift_mem : ∀ r ∈ sec7_rWin S W, ∀ j, sec7_jBand P S j →
    ∀ θ ∈ Set.Icc (0:ℝ) 1, ftil r + j - θ ∈ sec7_tWin S
  /-- §3 leading coefficient for the `f₁` expansion, by `j`-branch. -/
  ra_c₁ : ℤ → ℝ
  /-- §3 leading coefficient for the `f₂` expansion, by `j`-branch. -/
  ra_c₂ : ℤ → ℝ
  ra_c₁_lo : ∀ j, sec7_jBand P S j → 1 / 16 ≤ |ra_c₁ j|
  ra_c₁_hi : ∀ j, sec7_jBand P S j → |ra_c₁ j| ≤ 4
  ra_c₂_lo : ∀ j, sec7_jBand P S j → 1 / 16 ≤ |ra_c₂ j|
  ra_c₂_hi : ∀ j, sec7_jBand P S j → |ra_c₂ j| ≤ 4
  /-- Graded §3 expansion error for `f₁`, indexed by branch and derivative grade. -/
  ra_e₁D : ℤ → ℕ → ℝ → ℝ
  /-- Graded §3 expansion error for `f₂`, indexed by branch and derivative grade. -/
  ra_e₂D : ℤ → ℕ → ℝ → ℝ
  /-- Graded §3 expansion error for `f₃`, indexed by branch and derivative grade. -/
  ra_e₃D : ℤ → ℕ → ℝ → ℝ
  ra_e₁D_zero : ∀ j, sec7_jBand P S j → ∀ t,
    ra_e₁D j 0 t =
      f1D j 0 t - ra_c₁ j * S.T₁ * (t / S.R) ^ (-(1:ℝ))
  ra_e₂D_zero : ∀ j, sec7_jBand P S j → ∀ t,
    ra_e₂D j 0 t = f2D 0 t - ra_c₂ j * S.T₂ * (t / S.R) ^ ((3:ℝ)/4)
  ra_e₃D_zero : ∀ j, sec7_jBand P S j → ∀ t,
    ra_e₃D j 0 t =
      f3D j 0 t - 3 * ra_c₁ j * ra_c₂ j * S.T₃ * (t / S.R) ^ (-(1:ℝ)/4)
  ra_e₁D_deriv : ∀ j, sec7_jBand P S j → ∀ m < 5, ∀ r ∈ sec7_rWinWide S W,
    HasDerivAt (ra_e₁D j m) (ra_e₁D j (m + 1) r) r
  ra_e₂D_deriv : ∀ j, sec7_jBand P S j → ∀ m < 5, ∀ r ∈ sec7_rWinWide S W,
    HasDerivAt (ra_e₂D j m) (ra_e₂D j (m + 1) r) r
  ra_e₃D_deriv : ∀ j, sec7_jBand P S j → ∀ m < 5, ∀ r ∈ sec7_rWinWide S W,
    HasDerivAt (ra_e₃D j m) (ra_e₃D j (m + 1) r) r
  ra_e₁D_bound : ∀ j, sec7_jBand P S j → ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
    |ra_e₁D j m r| ≤ sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S
  ra_e₂D_bound : ∀ j, sec7_jBand P S j → ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
    |ra_e₂D j m r| ≤ sec7_cExpIn * (S.T₂ / S.R ^ m) * sec7_relErr P S
  ra_e₃D_bound : ∀ j, sec7_jBand P S j → ∀ m ≤ 5, ∀ r ∈ sec7_rWinWide S W,
    |ra_e₃D j m r| ≤ sec7_cExpIn * (S.T₃ / S.R ^ m) * sec7_relErrF P S
  /-- Global `C²` regularity of the branch phase used by the counting engines. -/
  phiContDiff : ∀ (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ)
      (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ),
    sec7_jBand P S j → sec7_phiBound W h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ →
    ContDiffOn ℝ 2 (fun r =>
      diff3 (h₁ : ℝ) h₂ h₃ (f3D j 0) r
        + f1D j 0 (r + ((h₁ : ℝ) + h₂ + h₃)) *
            (diff3 (h₁ : ℝ) h₂ h₃ (f2D 0) r + ρ₀)
        + diff1 (h₁ : ℝ) (f1D j 0) (r + ((h₁ : ℝ) + h₂ + h₃) - h₁) *
            (diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (f2D 0)) (r + ξ₁) - u₁ + ρ₁)
        + diff1 (h₂ : ℝ) (f1D j 0) (r + ((h₁ : ℝ) + h₂ + h₃) - h₂) *
            (diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (f2D 0)) (r + ξ₂) - u₂ + ρ₂)
        + diff1 (h₃ : ℝ) (f1D j 0) (r + ((h₁ : ℝ) + h₂ + h₃) - h₃) *
            (diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (f2D 0)) (r + ξ₃) - u₃ + ρ₃))
      (Set.Ioo (S.R / 144 - 1) (40 * S.R + 1))

/- N2 (md 1327–31): "F·d̆ₐ'(t) ≍ HΔ, F²·d̆ₐ''(t) ≍ HΔ (t ≍ F)" — accessor (carried fields,
   no stub). -/
/-- **N2a** (md 1327–31): the inverse-function scales, two-sided with constant `sec7_cPh`. -/
theorem Sec7Phase.inverse_scale {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    (Ph : Sec7Phase P S W a) :
    ∀ t ∈ sec7_tWin S,
      (P.H * S.Δ ≤ sec7_cPh * (S.F * |Ph.dBreve' t|) ∧
        S.F * |Ph.dBreve' t| ≤ sec7_cPh * (P.H * S.Δ)) ∧
      (P.H * S.Δ ≤ sec7_cPh * (S.F ^ 2 * |Ph.dBreve'' t|) ∧
        S.F ^ 2 * |Ph.dBreve'' t| ≤ sec7_cPh * (P.H * S.Δ)) :=
  fun t ht => ⟨⟨Ph.Fd'_lo t ht, Ph.Fd'_hi t ht⟩, ⟨Ph.F2d''_lo t ht, Ph.F2d''_hi t ht⟩⟩

/- N2 (md 1509–14): "f₁^{(m)} ≍ T₁/Rᵐ, f₂^{(m)} ≍ T₂/Rᵐ, f₃^{(m)} ≍ T₃/Rᵐ" — accessor. -/
/-- **N2b** (md 1509–14): the `f_i^{(m)} ≍ T_i/Rᵐ` derivative windows (`m ≤ 3`,
`r ≍ R`, `j` in the §7 band), two-sided with constant `sec7_cPh`. -/
theorem Sec7Phase.fi_window {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    (Ph : Sec7Phase P S W a) {j : ℤ} (hj : sec7_jBand P S j) {m : ℕ}
    (hm : m ≤ 3) :
    ∀ r ∈ sec7_rWin S W,
      (S.T₁ / S.R ^ m ≤ sec7_cPh * |Ph.f1D j m r| ∧
        |Ph.f1D j m r| ≤ sec7_cPh * (S.T₁ / S.R ^ m)) ∧
      (S.T₂ / S.R ^ m ≤ sec7_cPh * |Ph.f2D m r| ∧
        |Ph.f2D m r| ≤ sec7_cPh * (S.T₂ / S.R ^ m)) ∧
      (S.T₃ / S.R ^ m ≤ sec7_cPh * |Ph.f3D j m r| ∧
        |Ph.f3D j m r| ≤ sec7_cPh * (S.T₃ / S.R ^ m)) :=
  fun r hr =>
    ⟨⟨Ph.f1D_lo j hj m hm r hr, Ph.f1D_hi j hj m hm r hr⟩,
      ⟨Ph.f2D_lo m hm r hr, Ph.f2D_hi m hm r hr⟩,
      ⟨Ph.f3D_lo j hj m hm r hr, Ph.f3D_hi j hj m hm r hr⟩⟩

/- md 1421–1451, the bundled full envelope: "the original nine integer-power constraints
   [= e01–e09 of the md 1394–1417 min display, raised to their integer powers], the four
   no-absorption residual constraints  W¹⁶ ≤ H³xG²Ω², W²⁸ ≤ H³xG⁴Ω¹², W¹⁸x³G⁴Ω¹⁶ ≤ H³,
   W⁴²x³ ≤ H³Ω⁴  [md 1426–31, verbatim, constant-free], the two offset constraints
   W¹² ≪ H^{1/2}x^{5/2}G³Ω⁷, W¹⁸ ≪ H^{1/2}x^{5/2}G⁴Ω¹²  [md 1435–37], the ten
   nonzero-top-carry constraints displayed above [= e10–e19 raised; the last two equal the
   md-1443 residual square-root forms  W¹⁶x ≪ H, W²⁸x ≪ HG²Ω¹⁰], and the §4.3 side
   conditions R > 1, T₁ > 1 [scale-level; 0 < δ₁(h) < 1, |F''| ≍ 1 are per-h, in-proof].
   All transcriptions sympy-checked per-entry (tmp ledger → tools/sec7_ledger.py).
   LEDGER NOTE: md 1953 displays the 4th top-carry as W⁸ ≪ H^{1/2}x^{1/2}G²Ω³; the min
   display e13 = H^{1/16}x^{1/16}G^{1/8}Ω^{3/8} gives the stronger G¹-form, which we take
   (it is what "displayed above" bundles, and implies md 1953 for G ≥ 1). -/
/-- **§7 bundled full admissibility envelope** (md 1421–1451): 25 inequalities
(nine integer-power + four no-absorption + two offsets + ten nonzero-top-carry) plus the
scale-level side conditions. `≪`-entries carry the hypothesis-side absolute constant
`sec7_envC` (md 1419 "sufficiently small `c`"); the four no-absorption entries are
constant-free, verbatim md 1426–31. -/
structure Sec7Envelope (P : Globals) (S : Scale P) (W : ℝ) : Prop where
  W_pos : 0 < W
  -- nine integer-power constraints (e01–e09 raised; sympy-banked).  ARB-1/ARB-2 (A6):
  -- n1/n2/n3 carry the squared log; n4–n7 are the binding ¹⁄₄-power fits, on `sec7_envC2`.
  n1 : sec7_envC * W ^ 16 * (1 + Real.log P.X) ^ 2 ≤ P.H * S.x ^ 5 * S.Ω ^ 4
  n2 : sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14
  n3 : sec7_envC * W ^ 40 * (1 + Real.log P.X) ^ 2 ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24
  n4 : sec7_envC2 * (W ^ 18 * P.G ^ 6 * S.Ω ^ 14) ≤ P.H * S.x
  n5 : sec7_envC2 * (W ^ 42 * P.G ^ 2) ≤ P.H * S.x * S.Ω ^ 6
  n6 : sec7_envC2 * (W ^ 30 * S.Ω ^ 4) ≤ P.H * S.x
  n7 : sec7_envC2 * W ^ 54 ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16
  n8 : sec7_envC * W ^ 30 ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24
  n9 : sec7_envC * W ^ 42 ≤ P.H * S.x ^ 5 * P.G ^ 10 * S.Ω ^ 34
  -- four no-absorption residual constraints (md 1426–31; G1 ruling AM-4: `sec7_envC`-form,
  -- matching the other `≪`-entries; ARB-2 (A6): res1/res2 carry the squared log)
  res1 : sec7_envC * W ^ 16 * (1 + Real.log P.X) ^ 2 ≤ P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2
  res2 : sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 ≤ P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12
  res3 : sec7_envC * (W ^ 18 * S.x ^ 3 * P.G ^ 4 * S.Ω ^ 16) ≤ P.H ^ 3
  res4 : sec7_envC * (W ^ 42 * S.x ^ 3) ≤ P.H ^ 3 * S.Ω ^ 4
  -- two offset constraints (md 1435–37)
  off1 : sec7_envC * W ^ 12 ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7
  off2 : sec7_envC * W ^ 18 ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 4 * S.Ω ^ 12
  -- ten nonzero-top-carry constraints (e10–e19 raised; md 1944–66, 1443).  G1 ruling AM-7:
  -- each carries the unabsorbable Prop-4.3 log `(1 + log X)` on the W-side (binding at tc5,
  -- the `Wnz` monomial itself, which has zero `X`-slack); callers kill it with their `ε`.
  tc1 : sec7_envC * W ^ 8 * (1 + Real.log P.X)
    ≤ P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G * S.Ω ^ ((7:ℝ)/3)
  tc2 : sec7_envC * W ^ 8 * (1 + Real.log P.X) ≤
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (-(1:ℝ)/2) * S.Ω ^ ((1:ℝ)/2)
  tc3 : sec7_envC * W ^ 11 * (1 + Real.log P.X)
    ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3
  tc4 : sec7_envC * W ^ 8 * (1 + Real.log P.X)
    ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3
  tc5 : sec7_envC * W ^ 14 * (1 + Real.log P.X)
    ≤ P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G ^ 2 * S.Ω ^ ((22:ℝ)/3)
  tc6 : sec7_envC * W ^ 14 * (1 + Real.log P.X) ≤
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ ((1:ℝ)/2) * S.Ω ^ ((11:ℝ)/2)
  tc7 : sec7_envC * W ^ 17 * (1 + Real.log P.X)
    ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8
  tc8 : sec7_envC * W ^ 14 * (1 + Real.log P.X)
    ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8
  -- ARB-1: tc9/tc10 carry the SQUARED log (engine log × harvest log).
  tc9 : sec7_envC * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2 ≤ P.H
  tc10 : sec7_envC * (W ^ 28 * S.x) * (1 + Real.log P.X) ^ 2 ≤ P.H * P.G ^ 2 * S.Ω ^ 10
  -- §4.3 side conditions (md 1445–48, scale-level)
  R_gt_one : 1 < S.R
  T1_gt_one : 1 < S.T₁

end Squarefree
