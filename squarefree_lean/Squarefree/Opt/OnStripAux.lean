import Squarefree.Opt.StripAux
import Squarefree.Bracket.Admissible
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §9 on-strip helper lemmas for `dblock_on_strip` (`Opt/Global.lean`)

The §9 core needs, on the unresolved strip
`G^{-2}Ω^{-11/2}X^{-Cu·u} ≤ x ≤ G^{17}Ω^{-26}X^{Cu·u}`, `c₀G^{-1/4}U^{-3/4} ≤ Ω ≤ U`:

* the 21 admissibility entries `Wnz ≤ m_k` for the §7 envelope `AdmissibleW P S Wnz` with `c = 1`,
  where `Wnz = H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}` is the `e14` monomial (the strip minimum), plus
  `R > 1`, `T₁ > 1`;
* the closing LP arithmetic reducing `(A+1)(1+φ)(1+H/A²)(R/Wnz) ≤ C·H/U` to `18977g+15315u<2`.

These keep `Opt/Global.lean`'s elaboration small.  See `explicit_writeup.md` §9 (2083–2221) and
`math_audit.md` §9.  Every exponent here is reproduced in the route audit.
-/

open Classical Finset

namespace Squarefree.OnStripAux

open Squarefree

/-- The §9 bottleneck envelope `Wnz := H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}` (the `e14` monomial). -/
noncomputable def Wnz (P : Globals) (S : Scale P) : ℝ :=
  P.H ^ (1/84 : ℝ) * S.x ^ (5/84 : ℝ) * P.G ^ (1/7 : ℝ) * S.Ω ^ (11/21 : ℝ)

theorem Wnz_pos (P : Globals) (S : Scale P) : 0 < Wnz P S := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx : 0 < S.x := by unfold Scale.x; have := S.Δ_pos; positivity
  unfold Wnz
  have := Real.rpow_pos_of_pos hH (1/84 : ℝ)
  have := Real.rpow_pos_of_pos hx (5/84 : ℝ)
  have := Real.rpow_pos_of_pos hG (1/7 : ℝ)
  have := Real.rpow_pos_of_pos hΩ (11/21 : ℝ)
  positivity

theorem x_pos (P : Globals) (S : Scale P) : 0 < S.x := by
  unfold Scale.x; have := S.Δ_pos; have := P.H_pos; positivity

/-- Lower bound a power `v^δ` of a positive `v` by its worst edge (`v ≥ vlo` for `δ ≥ 0`,
`v ≤ vhi` for `δ ≤ 0`); the result is a power of `X` once the edge is an `X`-power. -/
private theorem rpow_ge_edge_pos {v vlo : ℝ} (hvlo : 0 < vlo) {δ : ℝ}
    (hδ : 0 ≤ δ) (hedge : vlo ≤ v) : vlo ^ δ ≤ v ^ δ :=
  Real.rpow_le_rpow hvlo.le hedge hδ

private theorem rpow_ge_edge_neg {v vhi : ℝ} (hv : 0 < v) {δ : ℝ}
    (hδ : δ ≤ 0) (hedge : v ≤ vhi) : vhi ^ δ ≤ v ^ δ :=
  Real.rpow_le_rpow_of_nonpos hv hedge hδ

/-- `G^c = X^{g·c}`. -/
private theorem G_xpow (P : Globals) (c : ℝ) : P.G ^ c = P.X ^ (P.g * c) := by
  rw [Globals.G, ← Real.rpow_mul P.X_pos.le]
/-- `H^a = X^{((1-g)/5)·a}`. -/
private theorem H_xpow (P : Globals) (a : ℝ) : P.H ^ a = P.X ^ ((1 - P.g)/5 * a) := by
  rw [Globals.H, ← Real.rpow_mul P.X_pos.le]
/-- `U^a = X^{u·a}`. -/
private theorem U_xpow (P : Globals) (a : ℝ) : P.U ^ a = P.X ^ (P.u * a) := by
  rw [Globals.U, ← Real.rpow_mul P.X_pos.le]

/-- The strip data, packaged. `c₀ ≥ 1`, `Cu ≥ 1`, the two `x`-edges and two `Ω`-edges, and
`X ≥ 1`. -/
structure StripData (P : Globals) (S : Scale P) (c₀ Cu : ℝ) : Prop where
  hX : 1 ≤ P.X
  hc₀ : 1 ≤ c₀
  hCu : 1 ≤ Cu
  hxlo : P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u)) ≤ S.x
  hxhi : S.x ≤ P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u)
  hΩlo : c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) ≤ S.Ω
  hΩhi : S.Ω ≤ P.U

/-- Lower bound on `S.x^b` as an `X`-power times a `G,Ω`-monomial, choosing the worst `x`-edge by
the sign of `b`.  Returns `(P.G^(gx) * S.Ω^(ox)) * P.X^(ux) ≤ S.x^b` with explicit exponents. -/
private theorem x_pow_lb (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (b : ℝ) :
    (if 0 ≤ b then
      P.G ^ (-2*b) * S.Ω ^ (-11/2*b) * P.X ^ (-(Cu*P.u)*b)
     else
      P.G ^ (17*b) * S.Ω ^ (-26*b) * P.X ^ ((Cu*P.u)*b)) ≤ S.x ^ b := by
  have hx := x_pos P S
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hX := P.X_pos
  by_cases hb : 0 ≤ b
  · rw [if_pos hb]
    have h1 : (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ b ≤ S.x ^ b :=
      Real.rpow_le_rpow (by positivity) D.hxlo hb
    refine le_trans (le_of_eq ?_) h1
    have e : (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ b
        = P.G ^ ((-2:ℝ)*b) * S.Ω ^ ((-11/2:ℝ)*b) * P.X ^ ((-(Cu*P.u))*b) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hX.le _),
          Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hΩ.le _),
          ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le, ← Real.rpow_mul hX.le]
    exact e.symm
  · rw [if_neg hb]
    have hble : b ≤ 0 := not_le.mp hb |>.le
    have h1 : S.x ^ b ≥ (P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u)) ^ b :=
      Real.rpow_le_rpow_of_nonpos (by positivity) D.hxhi hble
    refine le_trans (le_of_eq ?_) h1
    have e : (P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u)) ^ b
        = P.G ^ ((17:ℝ)*b) * S.Ω ^ ((-26:ℝ)*b) * P.X ^ ((Cu*P.u)*b) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hX.le _),
          Real.mul_rpow (by positivity) (Real.rpow_nonneg hΩ.le _),
          ← Real.rpow_natCast P.G 17, ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le,
          ← Real.rpow_mul hX.le]
      norm_num
    exact e.symm

/-- Lower bound on `S.Ω^d` choosing the worst `Ω`-edge by the sign of `d`. For `d ≥ 0` uses the
lower edge `c₀G^{-1/4}U^{-3/4}` and `c₀ ≥ 1` to drop `c₀`; for `d ≤ 0` uses `Ω ≤ U`. -/
private theorem om_pow_lb (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (d : ℝ) :
    (if 0 ≤ d then P.G ^ (-1/4*d) * P.U ^ (-3/4*d) else P.U ^ d) ≤ S.Ω ^ d := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hU := P.U_pos
  by_cases hd : 0 ≤ d
  · rw [if_pos hd]
    have hlb_pos : 0 < c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) := by
      have := Real.rpow_pos_of_pos hG (-1/4 : ℝ); have := Real.rpow_pos_of_pos hU (-3/4 : ℝ)
      have : 0 < c₀ := lt_of_lt_of_le one_pos D.hc₀; positivity
    have h1 : (c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) ^ d ≤ S.Ω ^ d :=
      Real.rpow_le_rpow hlb_pos.le D.hΩlo hd
    refine le_trans ?_ h1
    rw [Real.mul_rpow (lt_of_lt_of_le one_pos D.hc₀).le (by positivity),
        Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hU.le _),
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hU.le]
    have hc₀d : (1:ℝ) ≤ c₀ ^ d := Real.one_le_rpow D.hc₀ hd
    have hpos : 0 ≤ P.G ^ (-1/4*d) * P.U ^ (-3/4*d) := by positivity
    calc P.G ^ (-1/4*d) * P.U ^ (-3/4*d)
        = 1 * (P.G ^ (-1/4*d) * P.U ^ (-3/4*d)) := by ring
      _ ≤ c₀ ^ d * (P.G ^ (-1/4*d) * P.U ^ (-3/4*d)) :=
          mul_le_mul_of_nonneg_right hc₀d hpos
      _ = c₀ ^ d * (P.G ^ ((-1)/4 * d) * P.U ^ ((-3)/4 * d)) := by norm_num
  · rw [if_neg hd]
    have hdle : d ≤ 0 := not_le.mp hd |>.le
    exact Real.rpow_le_rpow_of_nonpos hΩ D.hΩhi hdle

/-- Factor a monomial as `Wnz` times the ratio monomial (the exponent differences). -/
private theorem mono_eq_Wnz_mul (P : Globals) (S : Scale P) (a b c d : ℝ) :
    P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d
      = Wnz P S * (P.H ^ (a - 1/84) * S.x ^ (b - 5/84) * P.G ^ (c - 1/7)
          * S.Ω ^ (d - 11/21)) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  unfold Wnz
  rw [show a = 1/84 + (a - 1/84) by ring, show b = 5/84 + (b - 5/84) by ring,
      show c = 1/7 + (c - 1/7) by ring, show d = 11/21 + (d - 11/21) by ring,
      Real.rpow_add hH, Real.rpow_add hx, Real.rpow_add hG, Real.rpow_add hΩ]
  ring

/-- The worst-case `X`-exponent of the ratio monomial `H^A x^B G^C Ω^D` after substituting the
worst `x`-edge (per sign of `B`) and then the worst `Ω`-edge (per sign of the resulting
`Ω`-exponent).  A pure function of `g, u, Cu, A, B, C, cD`. -/
noncomputable def ratioExp (g u Cu A B C cD : ℝ) : ℝ :=
  (1 - g)/5 * A + g * C
  + (if 0 ≤ B then g * (-2*B) else g * (17*B))
  + (if 0 ≤ B then (-(Cu*u))*B else (Cu*u)*B)
  + (let Op := (if 0 ≤ B then (-11/2*B) else (-26*B)) + cD;
     if 0 ≤ Op then g * (-1/4*Op) + u * (-3/4*Op) else u * Op)

/-- One-`X`-power lower bound on the ratio monomial. -/
private theorem ratio_lb (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (A B C cD : ℝ) :
    P.X ^ (ratioExp P.g P.u Cu A B C cD)
      ≤ P.H ^ A * S.x ^ B * P.G ^ C * S.Ω ^ cD := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  have hX := P.X_pos
  set xG : ℝ := if 0 ≤ B then -2*B else 17*B with hxG
  set xX : ℝ := if 0 ≤ B then (-(Cu*P.u))*B else (Cu*P.u)*B with hxX
  set xOm : ℝ := if 0 ≤ B then -11/2*B else -26*B with hxOm
  set Op : ℝ := xOm + cD with hOp
  set Oedge : ℝ := if 0 ≤ Op then P.g * (-1/4*Op) + P.u * (-3/4*Op) else P.u * Op with hOe
  -- x-edge lower bound (split G/Ω/X parts)
  have hxb' : P.G ^ xG * S.Ω ^ xOm * P.X ^ xX ≤ S.x ^ B := by
    have hxb := x_pow_lb P S c₀ Cu D B
    by_cases hB : 0 ≤ B
    · rw [if_pos hB] at hxb; rw [hxG, hxX, hxOm, if_pos hB, if_pos hB, if_pos hB]; exact hxb
    · rw [if_neg hB] at hxb; rw [hxG, hxX, hxOm, if_neg hB, if_neg hB, if_neg hB]; exact hxb
  -- merged Ω lower bound (X-power form)
  have hΩX : P.X ^ Oedge ≤ S.Ω ^ Op := by
    have hΩcomb := om_pow_lb P S c₀ Cu D Op
    by_cases hOpge : 0 ≤ Op
    · rw [if_pos hOpge] at hΩcomb
      rw [hOe, if_pos hOpge, Real.rpow_add hX, ← G_xpow, ← U_xpow]; exact hΩcomb
    · rw [if_neg hOpge] at hΩcomb
      rw [hOe, if_neg hOpge, ← U_xpow]; exact hΩcomb
  -- the X-exponent equals ratioExp
  have hEval : ratioExp P.g P.u Cu A B C cD
      = (1 - P.g)/5 * A + P.g * C + P.g * xG + xX + Oedge := by
    rw [ratioExp, hxG, hxX, hOe, hOp, hxOm]
    simp only []
    split_ifs <;> ring
  -- assemble
  rw [hEval]
  have hΩsplit : S.Ω ^ xOm * S.Ω ^ cD = S.Ω ^ Op := by rw [← Real.rpow_add hΩ, hOp]
  calc P.X ^ ((1 - P.g)/5 * A + P.g * C + P.g * xG + xX + Oedge)
      = P.X ^ ((1 - P.g)/5 * A) * (P.G ^ xG * P.X ^ xX) * P.G ^ C * P.X ^ Oedge := by
        rw [G_xpow, G_xpow, ← Real.rpow_add hX, ← Real.rpow_add hX, ← Real.rpow_add hX,
            ← Real.rpow_add hX]; ring_nf
    _ ≤ P.X ^ ((1 - P.g)/5 * A) * (P.G ^ xG * P.X ^ xX) * P.G ^ C * S.Ω ^ Op :=
        mul_le_mul_of_nonneg_left hΩX (by positivity)
    _ = P.H ^ A * (P.G ^ xG * S.Ω ^ xOm * P.X ^ xX) * P.G ^ C * S.Ω ^ cD := by
        rw [H_xpow, ← hΩsplit]; ring
    _ ≤ P.H ^ A * S.x ^ B * P.G ^ C * S.Ω ^ cD := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hΩ.le cD)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hG.le C)
        exact mul_le_mul_of_nonneg_left hxb' (Real.rpow_nonneg hH.le _)

/-- **Master monomial comparison.** On the strip, `Wnz ≤ P.H^a·S.x^b·P.G^c·S.Ω^d` whenever the
worst-case ratio `X`-exponent `ratioExp g u Cu (a-1/84) (b-5/84) (c-1/7) (d-11/21)` is `≥ 0`. -/
theorem Wnz_le_mono (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (a b c d : ℝ)
    (hE : 0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21)) :
    Wnz P S ≤ P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d := by
  have hWpos := Wnz_pos P S
  rw [mono_eq_Wnz_mul]
  have hrl := ratio_lb P S c₀ Cu D (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21)
  have h1le : (1:ℝ) ≤ P.X ^ (ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21)) :=
    Real.one_le_rpow D.hX hE
  calc Wnz P S = Wnz P S * 1 := by ring
    _ ≤ Wnz P S * (P.H ^ (a - 1/84) * S.x ^ (b - 5/84) * P.G ^ (c - 1/7) * S.Ω ^ (d - 11/21)) :=
        mul_le_mul_of_nonneg_left (le_trans h1le hrl) hWpos.le

/-- A monomial `> 1` on the strip whenever its `X`-exponent is `> 0` (and `X > 1`).
Used for `R > 1`, `T₁ > 1`. -/
theorem one_lt_mono (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (hXgt : 1 < P.X) (a b c d : ℝ)
    (hE : 0 < ratioExp P.g P.u Cu a b c d) :
    (1:ℝ) < P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d :=
  lt_of_lt_of_le (Real.one_lt_rpow hXgt hE) (ratio_lb P S c₀ Cu D a b c d)

/-- `S.x^(1/2) = H^(1/2)/Δ`. -/
private theorem x_half (P : Globals) (S : Scale P) : S.x ^ (1/2:ℝ) = P.H ^ (1/2:ℝ) / S.Δ := by
  have hH := P.H_pos; have hΔ := S.Δ_pos
  unfold Scale.x
  rw [Real.div_rpow hH.le (by positivity)]
  congr 1
  rw [show (S.Δ^2 : ℝ) = S.Δ^(2:ℕ) from by norm_num, ← Real.rpow_natCast S.Δ 2,
      ← Real.rpow_mul hΔ.le, show ((2:ℕ):ℝ) * (1/2:ℝ) = 1 by norm_num, Real.rpow_one]

/-- `R = H^{1/2}·x^{1/2}·G^1·Ω^3` (rpow monomial form). -/
theorem R_mono (P : Globals) (S : Scale P) :
    S.R = P.H ^ (1/2:ℝ) * S.x ^ (1/2:ℝ) * P.G ^ (1:ℝ) * S.Ω ^ (3:ℝ) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos
  have hHval : P.H ^ (1/2:ℝ) * P.H ^ (1/2:ℝ) = P.H := by rw [← Real.rpow_add hH]; norm_num
  have hΩ3 : S.Ω ^ (3:ℝ) = S.Ω ^ 3 := by rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [x_half, Real.rpow_one, hΩ3]
  unfold Scale.R
  rw [show P.H ^ (1/2:ℝ) * (P.H ^ (1/2:ℝ) / S.Δ) * P.G * S.Ω ^ 3
        = (P.H ^ (1/2:ℝ) * P.H ^ (1/2:ℝ)) * P.G * S.Ω ^ 3 / S.Δ by ring, hHval]

/-- `S.x^(-3/2) = H^(-3/2)·Δ³`, with `H^(-3/2)·H^(1/2) = H⁻¹`. -/
private theorem x_n32 (P : Globals) (S : Scale P) :
    S.x ^ (-3/2:ℝ) = P.H ^ (-3/2:ℝ) * S.Δ ^ (3:ℝ) := by
  have hH := P.H_pos; have hΔ := S.Δ_pos
  unfold Scale.x
  rw [Real.div_rpow hH.le (by positivity)]
  rw [show (S.Δ^2 : ℝ) = S.Δ^(2:ℕ) from by norm_num, ← Real.rpow_natCast S.Δ 2,
      ← Real.rpow_mul hΔ.le, show ((2:ℕ):ℝ) * (-3/2:ℝ) = -(3:ℝ) by norm_num,
      Real.rpow_neg hΔ.le, div_inv_eq_mul]

/-- `T₁ = H^{1/2}·x^{-3/2}·G^{-1}·Ω^{-1}` (rpow monomial form). -/
theorem T1_mono (P : Globals) (S : Scale P) :
    S.T₁ = P.H ^ (1/2:ℝ) * S.x ^ (-3/2:ℝ) * P.G ^ (-1:ℝ) * S.Ω ^ (-1:ℝ) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos
  have hΔ3 : S.Δ ^ (3:ℝ) = S.Δ ^ 3 := by rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hHinv : P.H ^ (1/2:ℝ) * P.H ^ (-3/2:ℝ) = P.H⁻¹ := by
    rw [← Real.rpow_add hH, show (1/2:ℝ) + (-3/2:ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [x_n32, Real.rpow_neg_one, Real.rpow_neg_one, hΔ3]
  unfold Scale.T₁ Scale.F
  rw [show P.H ^ (1/2:ℝ) * (P.H ^ (-3/2:ℝ) * S.Δ ^ 3) * P.G⁻¹ * S.Ω⁻¹
        = (P.H ^ (1/2:ℝ) * P.H ^ (-3/2:ℝ)) * S.Δ ^ 3 * P.G⁻¹ * S.Ω⁻¹ by ring, hHinv]
  field_simp

/-- The uniform on-strip `(g,u,Cu)`-budget that discharges every monomial comparison, the
`R>1`/`T₁>1` exponents, and the closing LP.  The `g`-coefficient is the sharp `18977` (so the
range is the full `g < 2/18977`); all `X^{O(u)}` bookkeeping (the `2u` fiber factor, Prop 7.3's
`X^{O(u)}`, and the strip-edge `X^{±Cu·u}`) lives purely in the `u`-coefficient `18675 + 790·Cu`
(G1 ruling AM-7: the envelope's `(1+log X)` is killed by an extra `X^{-2u}` in the caller's `W`,
whose `X^{+2u}` re-enters the closing LP — `+1680` on the `u`-coefficient, sympy-verified).
The RHS is the sharp `2` (the binding `H·A` closing term needs exactly `≤ 2`), so the budget
admits every `g < 2/18977` via a small `u > 0`. -/
def Budget (g u Cu : ℝ) : Prop := 18977 * g + (18675 + 790 * Cu) * u ≤ 2

/-- **The §7 admissibility envelope at the §9 bottleneck `Wnz`** (with constant `c = 1`).
Every entry `e0k` is `Wnz ≤ m_k` (the strip minimum), via `Wnz_le_mono`; `R>1`, `T₁>1` via
`one_le_mono`.  All 22 facts close from the single uniform budget
`18977g + (16995 + 790·Cu)u ≤ 199/100`.  For the 20 non-binding comparisons this is far stronger
than needed: each has an affine exponent `α_k − β_k·g − (γ_k + δ_k·Cu)·u ≥ 0` with `β_k ≥ 0` and
corner slack `α_k − β_k·(2/18977) ≥ 0.00122 > 0`, so `g ≤ 2/18977` (implied, since the `u`-term is
`≥ 0`) plus the resulting pure-`u` bound suffices. -/
noncomputable def admissibleW_Wnz (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (hXgt : 1 < P.X) (hg : 0 ≤ P.g) (hu : 0 ≤ P.u) (hbud : Budget P.g P.u Cu) :
    AdmissibleW P S (Wnz P S) := by
  have hCu := D.hCu
  have hbud' : 18977 * P.g + (16995 + 790 * Cu) * P.u ≤ 2 := by
    have h := hbud
    unfold Budget at h
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1680) hu]
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu (by linarith)
  -- master discharger for one comparison `Wnz ≤ H^a x^b G^c Ω^d`
  have wle : ∀ a b c d : ℝ,
      0 ≤ ratioExp P.g P.u Cu (a - 1/84) (b - 5/84) (c - 1/7) (d - 11/21) →
      Wnz P S ≤ P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d :=
    fun a b c d hE => Wnz_le_mono P S c₀ Cu D a b c d hE
  -- master discharger for `1 < H^a x^b G^c Ω^d`
  have ole : ∀ a b c d : ℝ, 0 < ratioExp P.g P.u Cu a b c d →
      (1:ℝ) < P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d :=
    fun a b c d hE => one_lt_mono P S c₀ Cu D hXgt a b c d hE
  refine
    { W_pos := Wnz_pos P S
      c := 1
      c_pos := one_pos
      e01 := ?_, e02 := ?_, e03 := ?_, e04 := ?_, e05 := ?_, e06 := ?_, e07 := ?_
      e08 := ?_, e09 := ?_, e10 := ?_, e11 := ?_, e12 := ?_, e13 := ?_, e14 := ?_
      e15 := ?_, e16 := ?_, e17 := ?_, e18 := ?_, e19 := ?_, e20 := ?_, e21 := ?_
      R_gt_one := ?_, T1_gt_one := ?_ }
  -- e01: no G factor
  · rw [one_mul, show P.H ^ (1/16:ℝ) * S.x ^ (5/16:ℝ) * S.Ω ^ (1/4:ℝ)
          = P.H ^ (1/16:ℝ) * S.x ^ (5/16:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (1/4:ℝ) by
        rw [Real.rpow_zero]; ring]
    exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  -- e06: no G factor
  · rw [one_mul, show P.H ^ (1/30:ℝ) * S.x ^ (1/30:ℝ) * S.Ω ^ (-2/15:ℝ)
          = P.H ^ (1/30:ℝ) * S.x ^ (1/30:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (-2/15:ℝ) by
        rw [Real.rpow_zero]; ring]
    exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  -- e14: Wnz itself
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num)
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  -- e18: no G, no Ω factor
  · rw [one_mul, show P.H ^ (1/16:ℝ) * S.x ^ (-1/16:ℝ)
          = P.H ^ (1/16:ℝ) * S.x ^ (-1/16:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (0:ℝ) by
        rw [Real.rpow_zero, Real.rpow_zero]; ring]
    exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  · rw [one_mul]; exact wle _ _ _ _ (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  -- R > 1
  · rw [R_mono]
    exact ole (1/2) (1/2) 1 3 (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])
  -- T₁ > 1
  · rw [T1_mono]
    exact ole (1/2) (-3/2) (-1) (-1) (by unfold ratioExp; norm_num; linarith [hbud', hg, hu, huCu, huCu1])

/-! ### Closing-LP upper bounds (Step D) -/

/-- Upper bound a power `v^δ` of a positive `v` by its worst (largest) edge:
`v ≤ vhi` for `δ ≥ 0`, `v ≥ vlo` for `δ ≤ 0`. -/
private theorem x_pow_ub (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (b : ℝ) :
    S.x ^ b ≤ (if 0 ≤ b then P.G ^ (17*b) * S.Ω ^ (-26*b) * P.X ^ ((Cu*P.u)*b)
              else P.G ^ (-2*b) * S.Ω ^ (-11/2*b) * P.X ^ (-(Cu*P.u)*b)) := by
  have hx := x_pos P S; have hG := P.G_pos; have hΩ := S.Ω_pos; have hX := P.X_pos
  by_cases hb : 0 ≤ b
  · rw [if_pos hb]
    have h1 : S.x ^ b ≤ (P.G ^ 17 * S.Ω ^ (-26 : ℝ) * P.X ^ (Cu * P.u)) ^ b :=
      Real.rpow_le_rpow hx.le D.hxhi hb
    refine le_trans h1 (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hX.le _),
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hΩ.le _),
        ← Real.rpow_natCast P.G 17, ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le,
        ← Real.rpow_mul hX.le]
    norm_num
  · rw [if_neg hb]
    have hble : b ≤ 0 := not_le.mp hb |>.le
    have h1 : S.x ^ b ≤ (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ b :=
      Real.rpow_le_rpow_of_nonpos (by positivity) D.hxlo hble
    refine le_trans h1 (le_of_eq ?_)
    have e : (P.G ^ (-2 : ℝ) * S.Ω ^ (-11/2 : ℝ) * P.X ^ (-(Cu * P.u))) ^ b
        = P.G ^ ((-2:ℝ)*b) * S.Ω ^ ((-11/2:ℝ)*b) * P.X ^ ((-(Cu*P.u))*b) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hX.le _),
          Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hΩ.le _),
          ← Real.rpow_mul hG.le, ← Real.rpow_mul hΩ.le, ← Real.rpow_mul hX.le]
    exact e

/-- Upper bound `S.Ω^d ≤ (worst edge)`: `d ≥ 0` ⇒ `Ω ≤ U`; `d ≤ 0` ⇒ `Ω ≥ c₀G^{-1/4}U^{-3/4}`
(and `c₀ ≥ 1`, `d ≤ 0` ⇒ `c₀^d ≤ 1`, dropped). -/
private theorem om_pow_ub (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (d : ℝ) :
    S.Ω ^ d ≤ (if 0 ≤ d then P.U ^ d else P.G ^ (-1/4*d) * P.U ^ (-3/4*d)) := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hU := P.U_pos
  by_cases hd : 0 ≤ d
  · rw [if_pos hd]; exact Real.rpow_le_rpow hΩ.le D.hΩhi hd
  · rw [if_neg hd]
    have hdle : d ≤ 0 := not_le.mp hd |>.le
    have hlb_pos : 0 < c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ)) := by
      have := Real.rpow_pos_of_pos hG (-1/4 : ℝ); have := Real.rpow_pos_of_pos hU (-3/4 : ℝ)
      have : 0 < c₀ := lt_of_lt_of_le one_pos D.hc₀; positivity
    have h1 : S.Ω ^ d ≤ (c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) ^ d :=
      Real.rpow_le_rpow_of_nonpos hlb_pos D.hΩlo hdle
    refine le_trans h1 ?_
    rw [Real.mul_rpow (lt_of_lt_of_le one_pos D.hc₀).le (by positivity),
        Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hU.le _),
        ← Real.rpow_mul hG.le, ← Real.rpow_mul hU.le]
    have hc₀d : c₀ ^ d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos D.hc₀ hdle
    have hpos : 0 ≤ P.G ^ (-1/4*d) * P.U ^ (-3/4*d) := by positivity
    calc c₀ ^ d * (P.G ^ (-1/4 * d) * P.U ^ (-3/4 * d))
        ≤ 1 * (P.G ^ (-1/4*d) * P.U ^ (-3/4*d)) :=
          mul_le_mul hc₀d (le_refl _) hpos (by norm_num)
      _ = P.G ^ (-1/4*d) * P.U ^ (-3/4*d) := by ring

/-- Worst-case (largest) `X`-exponent of `H^A x^B G^C Ω^D` on the strip. -/
noncomputable def ratioExpU (g u Cu A B C cD : ℝ) : ℝ :=
  (1 - g)/5 * A + g * C
  + (if 0 ≤ B then g * (17*B) else g * (-2*B))
  + (if 0 ≤ B then (Cu*u)*B else (-(Cu*u))*B)
  + (let Op := (if 0 ≤ B then (-26*B) else (-11/2*B)) + cD;
     if 0 ≤ Op then u * Op else g * (-1/4*Op) + u * (-3/4*Op))

/-- `H^A x^B G^C Ω^cD ≤ X^{ratioExpU …}`. -/
private theorem mono_ub (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (A B C cD : ℝ) :
    P.H ^ A * S.x ^ B * P.G ^ C * S.Ω ^ cD ≤ P.X ^ (ratioExpU P.g P.u Cu A B C cD) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  have hX := P.X_pos
  set xG : ℝ := if 0 ≤ B then 17*B else -2*B with hxG
  set xX : ℝ := if 0 ≤ B then (Cu*P.u)*B else -(Cu*P.u)*B with hxX
  set xOm : ℝ := if 0 ≤ B then -26*B else -11/2*B with hxOm
  set Op : ℝ := xOm + cD with hOp
  set Oedge : ℝ := if 0 ≤ Op then P.u * Op else P.g * (-1/4*Op) + P.u * (-3/4*Op) with hOe
  have hxb' : S.x ^ B ≤ P.G ^ xG * S.Ω ^ xOm * P.X ^ xX := by
    have hxb := x_pow_ub P S c₀ Cu D B
    by_cases hB : 0 ≤ B
    · rw [if_pos hB] at hxb; rw [hxG, hxX, hxOm, if_pos hB, if_pos hB, if_pos hB]; exact hxb
    · rw [if_neg hB] at hxb; rw [hxG, hxX, hxOm, if_neg hB, if_neg hB, if_neg hB]; exact hxb
  have hΩX : S.Ω ^ Op ≤ P.X ^ Oedge := by
    have hΩcomb := om_pow_ub P S c₀ Cu D Op
    by_cases hOpge : 0 ≤ Op
    · rw [if_pos hOpge] at hΩcomb
      rw [hOe, if_pos hOpge, ← U_xpow]; exact hΩcomb
    · rw [if_neg hOpge] at hΩcomb
      rw [hOe, if_neg hOpge, Real.rpow_add hX, ← G_xpow, ← U_xpow]; exact hΩcomb
  have hEval : ratioExpU P.g P.u Cu A B C cD
      = (1 - P.g)/5 * A + P.g * C + P.g * xG + xX + Oedge := by
    rw [ratioExpU, hxG, hxX, hOe, hOp, hxOm]
    simp only []
    split_ifs <;> ring
  rw [hEval]
  have hΩsplit : S.Ω ^ xOm * S.Ω ^ cD = S.Ω ^ Op := by rw [← Real.rpow_add hΩ, hOp]
  calc P.H ^ A * S.x ^ B * P.G ^ C * S.Ω ^ cD
      ≤ P.H ^ A * (P.G ^ xG * S.Ω ^ xOm * P.X ^ xX) * P.G ^ C * S.Ω ^ cD := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hΩ.le cD)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hG.le C)
        exact mul_le_mul_of_nonneg_left hxb' (Real.rpow_nonneg hH.le _)
    _ = P.H ^ A * (P.G ^ xG * P.X ^ xX) * P.G ^ C * S.Ω ^ Op := by
        rw [← hΩsplit]; ring
    _ ≤ P.H ^ A * (P.G ^ xG * P.X ^ xX) * P.G ^ C * P.X ^ Oedge :=
        mul_le_mul_of_nonneg_left hΩX (by positivity)
    _ = P.X ^ ((1 - P.g)/5 * A + P.g * C + P.g * xG + xX + Oedge) := by
        rw [H_xpow, G_xpow, G_xpow, ← Real.rpow_add hX, ← Real.rpow_add hX, ← Real.rpow_add hX,
            ← Real.rpow_add hX]; ring_nf

/-! ### Monomial identities for the four closing-LP terms -/

/-- `S.R / Wnz = H^{41/84}·x^{37/84}·G^{6/7}·Ω^{52/21}`. -/
private theorem RW_mono (P : Globals) (S : Scale P) :
    S.R / Wnz P S
      = P.H ^ (41/84:ℝ) * S.x ^ (37/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (52/21:ℝ) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  rw [R_mono, Wnz]
  rw [div_eq_iff (by positivity)]
  rw [show P.H ^ (41/84:ℝ) * S.x ^ (37/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (52/21:ℝ)
        * (P.H ^ (1/84:ℝ) * S.x ^ (5/84:ℝ) * P.G ^ (1/7:ℝ) * S.Ω ^ (11/21:ℝ))
      = (P.H ^ (41/84:ℝ) * P.H ^ (1/84:ℝ)) * (S.x ^ (37/84:ℝ) * S.x ^ (5/84:ℝ))
        * (P.G ^ (6/7:ℝ) * P.G ^ (1/7:ℝ)) * (S.Ω ^ (52/21:ℝ) * S.Ω ^ (11/21:ℝ)) by ring]
  rw [← Real.rpow_add hH, ← Real.rpow_add hx, ← Real.rpow_add hG, ← Real.rpow_add hΩ]
  norm_num

/-- `S.A = H^{1/2}·x^{-1/2}·Ω` (since `A = ΔΩ`, `Δ = (H/x)^{1/2}`). -/
private theorem A_mono (P : Globals) (S : Scale P) :
    S.A = P.H ^ (1/2:ℝ) * S.x ^ (-1/2:ℝ) * S.Ω := by
  have hH := P.H_pos; have hΔ := S.Δ_pos; have hx := x_pos P S
  have hxn12 : S.x ^ (-1/2:ℝ) = P.H ^ (-1/2:ℝ) * S.Δ := by
    unfold Scale.x
    rw [Real.div_rpow hH.le (by positivity)]
    rw [show (S.Δ^2 : ℝ) = S.Δ^(2:ℕ) from by norm_num, ← Real.rpow_natCast S.Δ 2,
        ← Real.rpow_mul hΔ.le, show ((2:ℕ):ℝ) * (-1/2:ℝ) = -(1:ℝ) by norm_num,
        Real.rpow_neg hΔ.le, Real.rpow_one, div_inv_eq_mul]
  rw [hxn12]
  unfold Scale.A
  rw [show P.H ^ (1/2:ℝ) * (P.H ^ (-1/2:ℝ) * S.Δ) * S.Ω
        = (P.H ^ (1/2:ℝ) * P.H ^ (-1/2:ℝ)) * S.Δ * S.Ω by ring,
      ← Real.rpow_add hH, show (1/2:ℝ) + (-1/2:ℝ) = 0 by norm_num, Real.rpow_zero, one_mul]

/-- `H/A = H^{1/2}·x^{1/2}·Ω^{-1}`. -/
private theorem HA_mono (P : Globals) (S : Scale P) :
    P.H / S.A = P.H ^ (1/2:ℝ) * S.x ^ (1/2:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (-1:ℝ) := by
  have hH := P.H_pos; have hΩ := S.Ω_pos; have hx := x_pos P S; have hΔ := S.Δ_pos
  rw [Real.rpow_zero, Real.rpow_neg_one, x_half]
  -- RHS = H^{1/2}·(H^{1/2}/Δ)·1·Ω⁻¹ = (H^{1/2}·H^{1/2})/Δ · Ω⁻¹ = H/(ΔΩ)
  have hH12 : P.H ^ (1/2:ℝ) * P.H ^ (1/2:ℝ) = P.H := by rw [← Real.rpow_add hH]; norm_num
  rw [show P.H ^ (1/2:ℝ) * (P.H ^ (1/2:ℝ) / S.Δ) * 1 * S.Ω⁻¹
        = (P.H ^ (1/2:ℝ) * P.H ^ (1/2:ℝ)) / (S.Δ * S.Ω) by field_simp, hH12]
  unfold Scale.A; rfl

/-- `H/A² = x·Ω^{-2}`. -/
private theorem HA2_mono (P : Globals) (S : Scale P) :
    P.H / S.A ^ 2 = P.H ^ (0:ℝ) * S.x ^ (1:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (-2:ℝ) := by
  have hH := P.H_pos; have hΩ := S.Ω_pos; have hΔ := S.Δ_pos
  rw [Real.rpow_zero, Real.rpow_zero, Real.rpow_one,
      show (-2:ℝ) = ((-2:ℤ):ℝ) by norm_num, Real.rpow_intCast]
  unfold Scale.A Scale.x
  field_simp

/-- `H/U = X^{(1-g)/5 - u}`. -/
private theorem HU_xpow (P : Globals) : P.H / P.U = P.X ^ ((1 - P.g)/5 - P.u) := by
  rw [Globals.H, Globals.U, ← Real.rpow_sub P.X_pos]

/-- A single closing-LP monomial term: if `(R/Wnz)·M = H^a x^b G^c Ω^d` and the worst-case
exponent (plus the `2u` fiber factor and the `2u` of the AM-7 envelope `W`-deflation) is
`≤ (1-g)/5 - u`, then `X^{4u}·(R/Wnz)·M ≤ X^{(1-g)/5-u} = H/U`. -/
private theorem closing_term (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (term a b c d : ℝ) (hterm : term = P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d)
    (hExp : ratioExpU P.g P.u Cu a b c d + 4 * P.u ≤ (1 - P.g)/5 - P.u) :
    P.X ^ (4 * P.u) * term ≤ P.H / P.U := by
  have hX := P.X_pos
  rw [HU_xpow, hterm]
  have h1 := mono_ub P S c₀ Cu D a b c d
  calc P.X ^ (4 * P.u) * (P.H ^ a * S.x ^ b * P.G ^ c * S.Ω ^ d)
      ≤ P.X ^ (4 * P.u) * P.X ^ (ratioExpU P.g P.u Cu a b c d) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hX.le _)
    _ = P.X ^ (4 * P.u + ratioExpU P.g P.u Cu a b c d) := by rw [← Real.rpow_add hX]
    _ ≤ P.X ^ ((1 - P.g)/5 - P.u) :=
        Real.rpow_le_rpow_of_exponent_le D.hX (by linarith [hExp])

/-- Combine `R/Wnz` (a monomial) with one of `A, H/A, 1, H/A²` (also a monomial) into a single
`H^a x^b G^c Ω^d`. -/
private theorem RW_mul (P : Globals) (S : Scale P) (a₂ b₂ c₂ d₂ : ℝ) :
    (P.H ^ (41/84:ℝ) * S.x ^ (37/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (52/21:ℝ))
      * (P.H ^ a₂ * S.x ^ b₂ * P.G ^ c₂ * S.Ω ^ d₂)
      = P.H ^ (41/84 + a₂) * S.x ^ (37/84 + b₂) * P.G ^ (6/7 + c₂) * S.Ω ^ (52/21 + d₂) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := x_pos P S
  rw [Real.rpow_add hH, Real.rpow_add hx, Real.rpow_add hG, Real.rpow_add hΩ]; ring

/-- **Closing LP** (Step D): on the strip, with the uniform budget
`18977g + (18675 + 790·Cu)u ≤ 2`, the per-scale envelope
`X^{2u}·(A+1)·(1+φ)·(1+H/A²)·(R/Wnz)` is `≤ 4·(1+c₀^{-8/3})·(H/U)`.  The leading `X^{2u}` is
the AM-7 envelope `W`-deflation re-entering through `R/W`.  The binding `H·A` term has the
sharp `g`-coefficient `18977` (writeup (9.3): `840·(9.3) = 18977g + 15315u − 2`, plus the `+2u`
fiber factor, the `+2u` deflation, and the `±Cu·u` strip edges absorbed into the
`u`-coefficient: `15315 + 1680 + 1680 = 18675`, sympy-verified). -/
theorem closing_bound (P : Globals) (S : Scale P) (c₀ Cu : ℝ) (D : StripData P S c₀ Cu)
    (hg : 0 ≤ P.g) (hu : 0 < P.u)
    (hbud : 18977 * P.g + (18675 + 790 * Cu) * P.u ≤ 2) :
    P.X ^ (2 * P.u)
        * ((S.A + 1) * (1 + StripAux.fiberφ P S) * ((1 + P.H / S.A ^ 2) * (S.R / Wnz P S)))
      ≤ (4 * (1 + c₀ ^ (-8/3 : ℝ))) * (P.H / P.U) := by
  have hX := P.X_pos; have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := x_pos P S; have hΔ := S.Δ_pos
  have hCu := D.hCu
  have huCu : (0:ℝ) ≤ P.u * Cu := mul_nonneg hu.le (by linarith)
  have huCu1 : (0:ℝ) ≤ P.u * (Cu - 1) := mul_nonneg hu.le (by linarith)
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  have hRWpos : 0 < S.R / Wnz P S := by
    have : 0 < S.R := by unfold Scale.R; positivity
    exact div_pos this (Wnz_pos P S)
  have hc₀ : 0 < c₀ := lt_of_lt_of_le one_pos D.hc₀
  -- fiber factor budget
  have hφ := StripAux.fiber_factor_budget P S c₀ hc₀ D.hX hu D.hΩlo
  rw [← StripAux.fiberφ_def] at hφ
  set Bφ : ℝ := 1 + c₀ ^ (-8/3:ℝ) with hBφ
  have hBφpos : 0 < Bφ := by
    rw [hBφ]; have := Real.rpow_pos_of_pos hc₀ (-8/3:ℝ); linarith
  -- expand (A+1)(1+H/A²)(R/Wnz) = (R/Wnz)·(A + H/A + 1 + H/A²)
  have hHAident : S.A * (P.H / S.A ^ 2) = P.H / S.A := by field_simp
  have hexp : (S.A + 1) * ((1 + P.H / S.A ^ 2) * (S.R / Wnz P S))
      = (S.R / Wnz P S) * S.A + (S.R / Wnz P S) * (P.H / S.A)
        + (S.R / Wnz P S) * 1 + (S.R / Wnz P S) * (P.H / S.A ^ 2) := by
    rw [show (S.A + 1) * ((1 + P.H / S.A ^ 2) * (S.R / Wnz P S))
          = (S.R / Wnz P S) * (S.A + (S.A * (P.H / S.A ^ 2)) + 1 + (P.H / S.A ^ 2)) by ring,
        hHAident]; ring
  -- the four monomial terms as `term`s
  have hRWm := RW_mono P S
  -- term_A = (R/Wnz)·A
  have hAm : S.A = P.H ^ (1/2:ℝ) * S.x ^ (-1/2:ℝ) * P.G ^ (0:ℝ) * S.Ω ^ (1:ℝ) := by
    rw [A_mono, Real.rpow_zero, Real.rpow_one]; ring
  have htA : (S.R / Wnz P S) * S.A
      = P.H ^ (83/84:ℝ) * S.x ^ (-5/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (73/21:ℝ) := by
    rw [hRWm, hAm, RW_mul]; norm_num
  have htHA : (S.R / Wnz P S) * (P.H / S.A)
      = P.H ^ (83/84:ℝ) * S.x ^ (79/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (31/21:ℝ) := by
    rw [hRWm, HA_mono, RW_mul]; norm_num
  have ht1 : (S.R / Wnz P S) * 1
      = P.H ^ (41/84:ℝ) * S.x ^ (37/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (52/21:ℝ) := by
    rw [mul_one, hRWm]
  have htHA2 : (S.R / Wnz P S) * (P.H / S.A ^ 2)
      = P.H ^ (41/84:ℝ) * S.x ^ (121/84:ℝ) * P.G ^ (6/7:ℝ) * S.Ω ^ (10/21:ℝ) := by
    rw [hRWm, HA2_mono, RW_mul]; norm_num
  -- bound each X^{2u}·term ≤ H/U
  have bA := closing_term P S c₀ Cu D _ _ _ _ _ htA
    (by unfold ratioExpU; norm_num; linarith [hbud, hg, hu, hCu, huCu, huCu1])
  have bHA := closing_term P S c₀ Cu D _ _ _ _ _ htHA
    (by unfold ratioExpU; norm_num; linarith [hbud, hg, hu, hCu, huCu, huCu1])
  have b1 := closing_term P S c₀ Cu D _ _ _ _ _ ht1
    (by unfold ratioExpU; norm_num; linarith [hbud, hg, hu, hCu, huCu, huCu1])
  have bHA2 := closing_term P S c₀ Cu D _ _ _ _ _ htHA2
    (by unfold ratioExpU; norm_num; linarith [hbud, hg, hu, hCu, huCu, huCu1])
  -- assemble
  have hsum_nn : 0 ≤ (S.R / Wnz P S) * S.A + (S.R / Wnz P S) * (P.H / S.A)
      + (S.R / Wnz P S) * 1 + (S.R / Wnz P S) * (P.H / S.A ^ 2) := by
    have h1 : 0 ≤ (S.R / Wnz P S) * S.A := by positivity
    have h2 : 0 ≤ (S.R / Wnz P S) * (P.H / S.A) := by positivity
    have h3 : 0 ≤ (S.R / Wnz P S) * (1:ℝ) := by positivity
    have h4 : 0 ≤ (S.R / Wnz P S) * (P.H / S.A ^ 2) := by positivity
    linarith
  have hX2upos : (0:ℝ) < P.X ^ (2 * P.u) := Real.rpow_pos_of_pos hX _
  have hX44 : P.X ^ (2 * P.u) * P.X ^ (2 * P.u) = P.X ^ (4 * P.u) := by
    rw [← Real.rpow_add hX]; congr 1; ring
  calc P.X ^ (2 * P.u)
          * ((S.A + 1) * (1 + StripAux.fiberφ P S) * ((1 + P.H / S.A ^ 2) * (S.R / Wnz P S)))
      = (1 + StripAux.fiberφ P S)
          * (P.X ^ (2 * P.u) * ((S.A + 1) * ((1 + P.H / S.A ^ 2) * (S.R / Wnz P S)))) := by ring
    _ ≤ (Bφ * P.X ^ (2 * P.u))
          * (P.X ^ (2 * P.u) * ((S.A + 1) * ((1 + P.H / S.A ^ 2) * (S.R / Wnz P S)))) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg hX2upos.le (by rw [hexp]; exact hsum_nn))
        rw [show (1 + c₀^(-8/3:ℝ)) * P.X ^ (2*P.u) = Bφ * P.X ^ (2 * P.u) from by rw [hBφ]] at hφ
        exact hφ
    _ = Bφ * ((P.X ^ (2*P.u) * P.X ^ (2*P.u)) * ((S.R / Wnz P S) * S.A)
          + (P.X ^ (2*P.u) * P.X ^ (2*P.u)) * ((S.R / Wnz P S) * (P.H / S.A))
          + (P.X ^ (2*P.u) * P.X ^ (2*P.u)) * ((S.R / Wnz P S) * 1)
          + (P.X ^ (2*P.u) * P.X ^ (2*P.u)) * ((S.R / Wnz P S) * (P.H / S.A ^ 2))) := by
        rw [hexp]; ring
    _ = Bφ * (P.X ^ (4*P.u) * ((S.R / Wnz P S) * S.A)
          + P.X ^ (4*P.u) * ((S.R / Wnz P S) * (P.H / S.A))
          + P.X ^ (4*P.u) * ((S.R / Wnz P S) * 1)
          + P.X ^ (4*P.u) * ((S.R / Wnz P S) * (P.H / S.A ^ 2))) := by rw [hX44]
    _ ≤ Bφ * (P.H / P.U + P.H / P.U + P.H / P.U + P.H / P.U) :=
        mul_le_mul_of_nonneg_left (by linarith [bA, bHA, b1, bHA2]) hBφpos.le
    _ = (4 * (1 + c₀ ^ (-8/3 : ℝ))) * (P.H / P.U) := by rw [hBφ]; ring

end Squarefree.OnStripAux
