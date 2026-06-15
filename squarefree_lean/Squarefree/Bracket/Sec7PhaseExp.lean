import Squarefree.Bracket.Sec7Defs
import Squarefree.FiniteDiff

/-!
# §7 phase expansion (plan nodes N9–N11) — Phase-1c SIGNATURES ONLY

md 1589–1682: the monomial expansions of `f₁, f₂, f₃, B_i, B_{03}, Δ_{h₁,h₂,h₃}f₃` with
relative error `≪ A/D = Ω/H` (N9, md 1589–1633), plus the faithful `U^3` budget for the
`+j` shift, the eq-(7.5) principal-part decomposition
with `C* = −(21/16)c₁c₂ ≠ 0` (N10, md 1634–65; sympy-banked, tools/sec7_ledger.py), and the
`Err^{(m)}` bound (N11, md 1666–82).

## Constant ledger additions (absolute constants; tools/sec7_ledger.py)
* `sec7_cMon = 10⁶` — legacy window constant (kept: `Cstar_lower` states against it);
  the `Sec7MonExp` window FIELDS are the §3-tight `[1/16, 4]` (interface ruling
  2026-06-12), with `c₃ = 3c₁c₂ ∈ [3/256, 48]`.
* `sec7_cExp = 10²⁵` (ARB-1, A3) — the `O(·)` constant of the five N9 difference
  expansions; content `cWin^{29/4} ≈ 5.6·10²¹`.
* `sec7_cErr = 10⁴²` (N11 re-pin 2026-06-12, ledger-coupled with `sec7_cSub = 10⁴⁴`) —
  the N11 `Err^{(m)}` constant; floor `≈ 9·10⁴⁰` at the tight windows.
* `sec7_cCarry = 10⁶`, `sec7_cFib = 10¹⁰` — carry size `ρᵢ = O(1)` (md 1556) and fiber size
  `|uᵢ − ρᵢ| ≪ 1 + h_jh_k·T₂/R²` (md 1560–70).  ARB-1 re-audit: cFib count/size content
  `2·(3/16)·72^{5/4}·cMon ≈ 7.9·10⁷` (shave to 10⁸ REFUTED, 127× kept).
* `sec7_cMult = 10⁴` (ARB-1, A6) — carry-tuple multiplicity of the N7 cover:
  `ρ₀ ∈ (−4,4)` (≤9 values), `ρᵢ ∈ (−3,2)` (≤7 each); content `9·7³ = 3087`.
  It multiplies the N7 cover COUNT (`Sec7Branch.sec7_carry_fiber_cover`); for the
  per-triple chain vs `sec7_cTriple = 10⁵⁶` see `Bracket/Sec7Harvest.lean` and
  tools/sec7_ledger.py (ARB-2 block).
* All errors are stated with the faithful relative-error scale `sec7_relErr = (Ω/H)·U^3`,
  reflecting md 1604–06 together with the uniform `+j`-shift distortion over the band.
-/

open Classical Finset Squarefree.FiniteDiff

namespace Squarefree

/-- Window constant for the N9 leading coefficients: `1/cMon ≤ |cᵢ| ≤ cMon` (ledger). -/
def sec7_cMon : ℝ := 10 ^ 6

/-- `O(·)` constant of the five N9 difference expansions (ledger; ARB-1: `cWin^{29/4}`-class). -/
def sec7_cExp : ℝ := 10 ^ 25

/-- `O(·)` constant of the N11 `Err^{(m)}` bound (ledger; N11 re-pin 2026-06-12: floor
`≈ 9·10⁴⁰` — binding terms `Nᵢ·eKᵢ` (`4·4·6·(2cWin)⁴·cExp ≈ 4.8·10⁴⁰`) and `eA·M0`
(`4·cExp·c_M0 ≈ 4·10⁴⁰`) — at the tight `[1/16,4]` coefficient windows; ≥10× margin). -/
def sec7_cErr : ℝ := 10 ^ 42

/-- Carry-tuple multiplicity constant of the N7 cover (ARB-1, A6; ledger: `9·7³ = 3087`). -/
def sec7_cMult : ℝ := 10 ^ 4

/-- Carry-size constant: `|ρᵢ| ≤ sec7_cCarry` (md 1556: carries are `O(1)`; ledger). -/
def sec7_cCarry : ℝ := 10 ^ 6

/-- Fiber-size constant: `|uᵢ − ρᵢ| ≤ sec7_cFib·(1 + h_jh_k·T₂/R²)` (md 1560–70; ledger;
AM-5 bump for the AM-2 wide-window cover). -/
def sec7_cFib : ℝ := 10 ^ 10

theorem sec7_cMon_pos : (0:ℝ) < sec7_cMon := by norm_num [sec7_cMon]
theorem sec7_cExp_pos : (0:ℝ) < sec7_cExp := by norm_num [sec7_cExp]
theorem sec7_cErr_pos : (0:ℝ) < sec7_cErr := by norm_num [sec7_cErr]
theorem sec7_cMult_pos : (0:ℝ) < sec7_cMult := by norm_num [sec7_cMult]

/- md 1463–66 (Lemma 7.2): "integer shifts 1 ≤ h₁ ≤ ⌊W⌋, 1 ≤ h₂ ≤ ⌊W²⌋, 1 ≤ h₃ ≤ ⌊W⁴⌋". -/
/-- The §7 rectangular shift box (md 1463–66). -/
def sec7_shiftBox (W : ℝ) (h₁ h₂ h₃ : ℤ) : Prop :=
  (1 ≤ h₁ ∧ (h₁ : ℝ) ≤ W) ∧ (1 ≤ h₂ ∧ (h₂ : ℝ) ≤ W ^ 2) ∧ (1 ≤ h₃ ∧ (h₃ : ℝ) ≤ W ^ 4)

/- md 1488–93: "P := h₁h₂h₃, S := h₁h₂ + h₁h₃ + h₂h₃"; md 1545: "h_Σ = h₁+h₂+h₃". -/
/-- `h_Σ = h₁ + h₂ + h₃` (md 1545). -/
def sec7_hSum (h₁ h₂ h₃ : ℤ) : ℝ := (h₁ : ℝ) + h₂ + h₃

/-- `P = h₁h₂h₃` (md 1490). -/
def sec7_Pprod (h₁ h₂ h₃ : ℤ) : ℝ := (h₁ : ℝ) * h₂ * h₃

/-- `S = h₁h₂ + h₁h₃ + h₂h₃` (md 1491). -/
def sec7_Ssym (h₁ h₂ h₃ : ℤ) : ℝ := (h₁ : ℝ) * h₂ + (h₁ : ℝ) * h₃ + (h₂ : ℝ) * h₃

/- N9 (md 1589–1633): "The asymptotic expansions of R_a(d) and F_a(d) imply
     f₂(r) = c₂T₂(r/R)^{3/4}(1+O(a/d̃_a(r))),  f₁(r) = c₁T₁(r/R)^{-1}(1+O(·)),
     f₃(r) = c₃T₃(r/R)^{-1/4}(1+O(·)),  with c_d,c₁,c₂,c₃ ≠ 0  and
     a/d̃_a(r) ≪ A/D = Ω/H.   Differencing the leading monomials gives, with y = r/R,
     f₁(r+h_Σ) = c₁T₁y⁻¹ − c₁h_Σ(T₁/R)y⁻² + O(h_Σ²T₁/R² + T₁X^{-(1-g)/5+O(u)}),
     Δ_{h_i}f₁(r+h_Σ−h_i) = −c₁h_i(T₁/R)y⁻² + O(h_ih_ΣT₁/R² + h_i(T₁/R)X^{-(1-g)/5+O(u)}),
     B_i(r) = β_ih_jh_k(T₂/R²)y^{-5/4} + O(h_jh_k(T₂/R²)X^{-(1-g)/5+O(u)} + h_jh_kh_Σ(T₂/R³)),
     B_{03}(r) = β₀P(T₂/R³)y^{-9/4} + O(P(T₂/R³)X^{-(1-g)/5+O(u)} + Ph_Σ(T₂/R⁴)),
     Δ_{h₁,h₂,h₃}f₃(r) = γ₀P(T₃/R³)y^{-13/4} + O(P(T₃/R³)X^{-(1-g)/5+O(u)} + Ph_Σ(T₃/R⁴))."
   The leading coefficients are baked in explicitly per md 1648–61
   ("B₀₃ = (15/64)c₂P(T₂/R³)y^{-9/4}+⋯", second/third differences of c₂T₂y^{3/4}: β = −(3/16)c₂,
   β₀ = (15/64)c₂; third difference of c₃T₃y^{-1/4}: "Δf₃ = −(45/64)c₃P(T₃/R³)y^{-13/4}+⋯"),
   and the inverse-function relation md 1662–63 "implies c₃ = 3c₁c₂" is carried as the exact
   field `c₃_eq` (it is exact for the leading asymptotic constants of §3). `X^{-(1-g)/5+O(u)}`
   is transcribed as the faithful scale `sec7_relErr = (Ω/H)·U^3` after the shift audit.
   GRADED FORM (Phase-1f): md 1666–76 bounds "Err^{(m)}(r) ≪ (1/Rᵐ)(…)" for the derivative
   orders m ≤ 2, which N11 cannot extract from value-level (m = 0) expansions alone; per
   md 1509–14 (`f_i^{(m)} ≍ T_i/Rᵐ`) each expansion differentiates with its error divided by
   `Rᵐ`, so every field is stated for `m ≤ 2` as `|iteratedDeriv m (piece − monomial)| ≤
   (m = 0 bound)/Rᵐ`; `m = 0` (`iteratedDeriv_zero`) is the md display verbatim. -/
/-- **N9 data bundle** (md 1589–1633 + leading coefficients md 1648–63): the §7 monomial
expansions of the differenced phase pieces, with faithful relative-error scale `(Ω/H)·U^3`.
`B_i` is the
double difference of `f₂` at the `ξ_i`-shifted point (md 1547–53), `B_{03}` the triple
difference. -/
structure Sec7MonExp (P : Globals) (S : Scale P) (W : ℝ) (a : ℤ) (Ph : Sec7Phase P S W a)
    (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ) where
  c₁ : ℝ
  c₂ : ℝ
  c₃ : ℝ
  /-- §3 truth (Sec7MonExp-interface ruling 2026-06-12): `c₁ = (a/A)²/6 ∈ [1/6, 2/3]`,
  window `[1/16, 4]` with slack. -/
  c₁_window : 1 / 16 ≤ |c₁| ∧ |c₁| ≤ 4
  /-- §3 truth: `c₂ = 2(a/A)^{-5/4} ∈ [2^{-1/4}, 2]`, window `[1/16, 4]` with slack. -/
  c₂_window : 1 / 16 ≤ |c₂| ∧ |c₂| ≤ 4
  /-- Derived window of `c₃ = 3c₁c₂` from the `[1/16, 4]` windows. -/
  c₃_window : 3 / 256 ≤ |c₃| ∧ |c₃| ≤ 48
  /-- md 1662–63: the inverse-function relation `f₃' = −f₁f₂' + O(·)` "implies c₃ = 3c₁c₂". -/
  c₃_eq : c₃ = 3 * c₁ * c₂
  /-- Graded witness chain of `f₁` (Sec7MonExp-interface ruling: the §3 derivative chains
  exposed as fields; grade 0 is the phase piece itself, transitions on the open wide
  window — what N11's Leibniz/chain identifications need). -/
  f1C : ℕ → ℝ → ℝ
  f2C : ℕ → ℝ → ℝ
  f3C : ℕ → ℝ → ℝ
  f1C_zero : ∀ t, f1C 0 t = Ph.f1D j 0 t
  f2C_zero : ∀ t, f2C 0 t = Ph.f2D 0 t
  f3C_zero : ∀ t, f3C 0 t = Ph.f3D j 0 t
  f1C_deriv : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (f1C m) (f1C (m + 1) r) r
  f2C_deriv : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (f2C m) (f2C (m + 1) r) r
  f3C_deriv : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (f3C m) (f3C (m + 1) r) r
  /-- md 1607–12: `f₁(r+h_Σ) = c₁T₁y⁻¹ − c₁h_Σ(T₁/R)y⁻² + O(h_Σ²T₁/R² + T₁·(Ω/H))`,
  graded `m ≤ 2` (md 1666–76). -/
  f1_exp : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        Ph.f1D j 0 (t + sec7_hSum h₁ h₂ h₃) -
          (c₁ * S.T₁ * (t / S.R) ^ (-(1:ℝ)) -
            c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
      sec7_cExp * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 + S.T₁ * sec7_relErrF P S) /
        S.R ^ m
  /-- md 1613–17: `Δ_{h₁}f₁(r+h_Σ−h₁) = −c₁h₁(T₁/R)y⁻² + O(h₁h_ΣT₁/R² + h₁(T₁/R)(Ω/H))`,
  graded `m ≤ 2`. -/
  d1f1_exp₁ : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff1 (h₁ : ℝ) (Ph.f1D j 0) (t + sec7_hSum h₁ h₂ h₃ - h₁) -
          (-(c₁ * h₁ * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
      sec7_cExp * ((h₁ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
        (h₁ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m
  /-- md 1613–17, `i = 2`, graded `m ≤ 2`. -/
  d1f1_exp₂ : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff1 (h₂ : ℝ) (Ph.f1D j 0) (t + sec7_hSum h₁ h₂ h₃ - h₂) -
          (-(c₁ * h₂ * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
      sec7_cExp * ((h₂ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
        (h₂ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m
  /-- md 1613–17, `i = 3`, graded `m ≤ 2`. -/
  d1f1_exp₃ : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff1 (h₃ : ℝ) (Ph.f1D j 0) (t + sec7_hSum h₁ h₂ h₃ - h₃) -
          (-(c₁ * h₃ * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
      sec7_cExp * ((h₃ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
        (h₃ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m
  /-- md 1618–22 (`i = 1`, `{j,k} = {2,3}`; β = −(3/16)c₂ per md 1648–53):
  `B₁(r) = −(3/16)c₂h₂h₃(T₂/R²)y^{-5/4} + O(h₂h₃(T₂/R²)(Ω/H) + h₂h₃h_Σ(T₂/R³))`,
  graded `m ≤ 2`. -/
  B_exp₁ : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (t + ξ₁) -
          (-(3/16) * c₂ * h₂ * h₃ * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) r| ≤
      sec7_cExp * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
        (h₂ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ m
  /-- md 1618–22, `i = 2`, `{j,k} = {1,3}`, graded `m ≤ 2`. -/
  B_exp₂ : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (t + ξ₂) -
          (-(3/16) * c₂ * h₁ * h₃ * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) r| ≤
      sec7_cExp * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
        (h₁ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ m
  /-- md 1618–22, `i = 3`, `{j,k} = {1,2}`, graded `m ≤ 2`. -/
  B_exp₃ : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) (t + ξ₃) -
          (-(3/16) * c₂ * h₁ * h₂ * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) r| ≤
      sec7_cExp * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
        (h₁ : ℝ) * h₂ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ m
  /-- md 1623–27 (β₀ = (15/64)c₂ per md 1648–50):
  `B₀₃(r) = (15/64)c₂P(T₂/R³)y^{-9/4} + O(P(T₂/R³)(Ω/H) + Ph_Σ(T₂/R⁴))`, graded `m ≤ 2`. -/
  B03_exp : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) t -
          (15/64) * c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * (t / S.R) ^ (-(9:ℝ)/4)) r| ≤
      sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
        sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) / S.R ^ m
  /-- md 1628–33 (γ₀ = −(45/64)c₃ per md 1658–61):
  `Δ_{h₁,h₂,h₃}f₃(r) = −(45/64)c₃P(T₃/R³)y^{-13/4} + O(P(T₃/R³)(Ω/H) + Ph_Σ(T₃/R⁴))`,
  graded `m ≤ 2`. -/
  d3f3_exp : ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
    |iteratedDeriv m (fun t =>
        diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) t -
          (-(45/64) * c₃ * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) *
            (t / S.R) ^ (-(13:ℝ)/4))) r| ≤
      sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
        sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₃ / S.R ^ 4) / S.R ^ m

/- N9 (md 1589–1633): the expansions hold for every fiber `a ∼ A`, every `j` in the §7 band,
   every triple in the shift box, and the `ξ_i`-shifted points with `|ξ_i| ≤ h_Σ` (md 1547–53).
   ARB-1 (zero consumers confirmed): the bare existence theorem `sec7_monExp_exists` was
   DELETED; the `Sec7MonExp` data is produced at the concrete §3 call site (through the
   asymptotic expansions of `R_a(d)`, `F_a(d)`, md 334, 1589–90), never abstractly. -/

/- md 1580–87 (eq 7.4): "Φ_{ρ,u}(r) := Δ_{h₁,h₂,h₃}f₃(r) + f₁(r+h_Σ)(B₀₃(r)+ρ₀)
     + Σ_{i=1}³ Δ_{h_i}f₁(r+h_Σ−h_i)(B_i(r)−u_i+ρ_i)",
   with B₀₃ = Δ_{h₁,h₂,h₃}f₂, B₁ = Δ_{h₂,h₃}f₂(·+ξ₁), B₂ = Δ_{h₁,h₃}f₂(·+ξ₂),
   B₃ = Δ_{h₁,h₂}f₂(·+ξ₃) (md 1547–53).  Defined here (its home node N8 is in the
   not-yet-created Sec7Branch; Sec7Branch will import this). -/
/-- **Eq (7.4)** (md 1580–87): the per-branch, per-fiber phase `Φ_{ρ,u}`. -/
noncomputable def sec7_Phi {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    (Ph : Sec7Phase P S W a)
    (j h₁ h₂ h₃ : ℤ) (ξ₁ ξ₂ ξ₃ : ℝ) (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℝ → ℝ := fun r =>
  diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) r
    + Ph.f1D j 0 (r + sec7_hSum h₁ h₂ h₃) * (diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) r + ρ₀)
    + diff1 (h₁ : ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₁) *
        (diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (r + ξ₁) - u₁ + ρ₁)
    + diff1 (h₂ : ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₂) *
        (diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (r + ξ₂) - u₂ + ρ₂)
    + diff1 (h₃ : ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₃) *
        (diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) (r + ξ₃) - u₃ + ρ₃)

/- md 1636–43 (eq 7.5): the `y⁻²`-coefficient "c₁(T₁/R)(Σ_{i=1}³ h_i(u_i−ρ_i) − ρ₀h_Σ)". -/
/-- The eq-(7.5) `y⁻²`-coefficient `B` (md 1638–41); in the branch `ρ₀ = 0` this is the
`B_{ρ,u}` of md 1691–95. -/
noncomputable def Sec7MonExp.Bcoef {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℝ :=
  ME.c₁ * (S.T₁ / S.R) *
    (((h₁ : ℝ) * ((u₁ : ℝ) - ρ₁) + (h₂ : ℝ) * ((u₂ : ℝ) - ρ₂) + (h₃ : ℝ) * ((u₃ : ℝ) - ρ₃)) -
      (ρ₀ : ℝ) * sec7_hSum h₁ h₂ h₃)

/- md 1663–65: "C* = −(45/64)c₃ + (51/64)c₁c₂"; (51/64 = 15/64 + 9/16, md 1648–58;
   sympy-banked, tools/sec7_ledger.py). -/
/-- The eq-(7.5) cubic-term coefficient `C*` (md 1648–65). -/
noncomputable def Sec7MonExp.Cstar {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) : ℝ :=
  -(45/64) * ME.c₃ + (51/64) * ME.c₁ * ME.c₂

/- md 1636–43 (eq 7.5): "Φ_{ρ,u}(r) = c₁ρ₀T₁y⁻¹ + c₁(T₁/R)(Σh_i(u_i−ρ_i) − ρ₀h_Σ)y⁻²
     + C*P(T₃/R³)y^{-13/4} + Err(r)". -/
/-- The eq-(7.5) principal part (md 1636–43). -/
noncomputable def Sec7MonExp.principal {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℝ → ℝ :=
  fun r =>
    ME.c₁ * ρ₀ * S.T₁ * (r / S.R) ^ (-(1:ℝ))
      + ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ * (r / S.R) ^ (-(2:ℝ))
      + ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * (r / S.R) ^ (-(13:ℝ)/4)

/-- The eq-(7.5) remainder `Err := Φ_{ρ,u} − principal` (md 1636–43, named difference). -/
noncomputable def Sec7MonExp.Err {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a} {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℝ → ℝ :=
  fun r =>
    sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r
      - ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r

section N10

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a}
  {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}

/- N10 (md 1636–43, eq 7.5): "Since T₁T₂/R³ = T₃/R³, the leading part of Φ_{ρ,u} is
     Φ_{ρ,u}(r) = c₁ρ₀T₁y⁻¹ + c₁(T₁/R)(Σh_i(u_i−ρ_i) − ρ₀h_Σ)y⁻² + C*P(T₃/R³)y^{-13/4}
                  + Err(r)". -/
/-- **N10a, eq (7.5)** (md 1636–43): the principal-part decomposition of `Φ_{ρ,u}`. -/
theorem sec7_eq75 (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ r, sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r =
      ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r + ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r := by
  intro r
  simp only [Sec7MonExp.Err]
  ring

/- N10 (md 1662–65): "The inverse-function relation … implies c₃ = 3c₁c₂.  Therefore
     C* = −(45/64)c₃ + (51/64)c₁c₂ = −(21/16)c₁c₂ ≠ 0"  (sympy-banked, ledger). -/
/-- **N10b** (md 1663–65): `C* = −(21/16)c₁c₂`. -/
theorem Sec7MonExp.Cstar_eq (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) :
    ME.Cstar = -(21/16) * ME.c₁ * ME.c₂ := by
  rw [Sec7MonExp.Cstar, ME.c₃_eq]; ring

/-- **N10c** (md 1665): `C* ≠ 0`; quantitatively `|C*| ≥ (21/16)/cMon²` (coefficient
windows), the form the N12 scale comparability consumes. -/
theorem Sec7MonExp.Cstar_lower (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) :
    (21/16) / sec7_cMon ^ 2 ≤ |ME.Cstar| := by
  rw [ME.Cstar_eq]
  have h1 := ME.c₁_window.1
  have h2 := ME.c₂_window.1
  have habs : |(-(21/16) * ME.c₁ * ME.c₂)| = (21/16) * |ME.c₁| * |ME.c₂| := by
    rw [abs_mul, abs_mul]; norm_num
  rw [habs]
  -- tight windows (interface ruling): `|cᵢ| ≥ 1/16`, far above the stated `1/cMon` floor
  calc (21/16) / sec7_cMon ^ 2 ≤ (21/16) * (1 / 16) * (1 / 16) := by
        rw [sec7_cMon]; norm_num
    _ ≤ (21/16) * |ME.c₁| * |ME.c₂| := by nlinarith [abs_nonneg ME.c₁, abs_nonneg ME.c₂]

end N10

/- N11 (md 1666–82): "Err^{(m)}(r) ≪ (1/Rᵐ)(1_{ρ₀≠0}T₁X^{-(1-g)/5+O(u)}
     + (h_ΣT₁/R + PT₃/R³)X^{-(1-g)/5+O(u)} + h_Σ²T₁/R²).
   Here the terms of size Ph_ΣT₃/R⁴ from the Taylor remainders have been absorbed into
   P(T₃/R³)X^{-(1-g)/5+O(u)}, since h_Σ/R ≤ W⁴/R ≪ X^{-c} in the displayed W-range.
   Thus in the branch ρ₀ = 0 there is no stand-alone T₁X^{-(1-g)/5+O(u)} error term."
   `X^{-(1-g)/5+O(u)}` is transcribed as the faithful `sec7_relErr = (Ω/H)·U^3`; the absorption
   needs `h_Σ/R ≤ (Ω/H)`-smallness, carried hypothesis-side below (TRAP-3 form). -/
/-- **N11 error scale** (md 1666–74): the `m = 0` size of `Err`.  ARB-1 (A2): the Taylor
remainder `P·h_Σ·T₃/R⁴` is KEPT as an explicit term (the md-1675–80 absorption into
`P(T₃/R³)·(Ω/H)` needed the undischargeable `habs : h_Σ/R ≤ Ω/H`, now dropped). -/
noncomputable def sec7_errScale (P : Globals) (S : Scale P) (h₁ h₂ h₃ ρ₀ : ℤ) : ℝ :=
  (if ρ₀ = 0 then 0 else 1) * S.T₁ * sec7_relErrF P S
    + sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * sec7_relErrF P S
    + sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S
    + sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S
    + (sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2
    + sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * (S.T₃ / S.R ^ 4)

/- **N11** (`sec7_err_deriv_bound`, md 1666–82) lives in `Bracket/Sec7ErrBound.lean`:
its proof needs the wide-window chain machinery of `Sec7MonExpAux`/`Sec7MonExpData`
(which import this file), so the theorem sits one layer downstream. -/

end Squarefree
