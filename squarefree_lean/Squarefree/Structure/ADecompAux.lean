import Squarefree.Structure.DaSpacing
import Squarefree.Counting.Preimage

/-!
# §3 A-decomposition — analytic helpers (self-contained, no §4)

Algebraic/analytic core lemmas for `a_decomposition` (`Squarefree.Structure.ADecomp`).
Two pieces, both at the level of the `inD` membership predicate:

* `tiny_gap_impossible` — first-difference (Nair–Roth) bound: two `𝒟`-elements `d, d+a`
  in `[D,2D]` are spaced `a ≥ D³/(6X)` (writeup 256–267, step (2) of the roadmap).
* `det_isolation_core` — the determinant lower bound: among three consecutive `𝒟`-elements
  `d, d+a, d+a+b` the integer `Δ = b·m₀ − (a+b)·m₁ + a·m₂` satisfies `0 < |Δ| < 1` if both
  gaps `a,b` are below the threshold `(D⁴/(8X))^{1/3}/2`, which is impossible — so no two
  consecutive gaps are both sub-threshold (writeup 260–267, step (3)).

Both are kept `private` to this and the `ADecomp` module.
-/

open Classical Finset Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 400000

/-- `F_a(d) = X/d² − X/(d+a)²`, the first difference of `X/d²`. -/
noncomputable def Ffun (X a d : ℝ) : ℝ := X / d ^ 2 - X / (d + a) ^ 2

/-- Exact factorization of `F_a(d)` (sympy-verified). -/
private theorem Ffun_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    Ffun X a d = X * a * (a + 2 * d) / (d ^ 2 * (d + a) ^ 2) := by
  unfold Ffun; field_simp; ring

/-- Shared bound: if `X ≤ m·r² ≤ X+H` and `r²>0` then `0 ≤ m − X/r² ≤ H/r²`. -/
private theorem err_bound (X H : ℝ) (m : ℤ) (r : ℝ) (hr : 0 < r ^ 2)
    (hlo : X ≤ (m : ℝ) * r ^ 2) (hhi : (m : ℝ) * r ^ 2 ≤ X + H) :
    0 ≤ (m : ℝ) - X / r ^ 2 ∧ (m : ℝ) - X / r ^ 2 ≤ H / r ^ 2 := by
  have hrne : r ^ 2 ≠ 0 := ne_of_gt hr
  have key : ((m : ℝ) - X / r ^ 2) * r ^ 2 = (m : ℝ) * r ^ 2 - X := by
    rw [sub_mul, div_mul_cancel₀ X hrne]
  refine ⟨?_, ?_⟩
  · have h0 : 0 ≤ ((m : ℝ) - X / r ^ 2) * r ^ 2 := by rw [key]; linarith
    exact (mul_nonneg_iff_of_pos_right hr).mp h0
  · rw [le_div_iff₀ hr, key]; linarith

/-- **B1 step** of the §3→§6 near-curve bridge: a popular `d` (one belonging to a `𝒟_a`-gap,
so both `d` and `d+a` lie in `𝒟`) makes `F_a(d) = X/d² − X/(d+a)²` lie within `2H/d²` of an
integer.  The witnessing integer is `m − m'`, where `m·d²` and `m'·(d+a)²` lie in `[X,X+H]`. -/
theorem inDa_distInt_Ffun {X H : ℝ} {a d : ℤ} (_hX : 0 < X) (hd : 0 < (d : ℝ)) (ha : 0 < a)
    (hin : inDa X H a d) :
    distInt (Ffun X (a : ℝ) (d : ℝ)) ≤ 2 * H / (d : ℝ) ^ 2 := by
  obtain ⟨-, hD, hDa, -⟩ := hin
  -- the two points and their squares
  set p : ℝ := (d : ℝ) with hp
  set q : ℝ := (d : ℝ) + (a : ℝ) with hq
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hppos : 0 < p := hd
  have hqpos : 0 < q := by rw [hq]; positivity
  have hpsq : (0 : ℝ) < p ^ 2 := by positivity
  have hqsq : (0 : ℝ) < q ^ 2 := by positivity
  have hqcast : ((d + a : ℤ) : ℝ) = q := by rw [hq]; push_cast; ring
  -- extract the multipliers
  obtain ⟨m, hmlo, hmhi⟩ := hD
  obtain ⟨m', hm'lo, hm'hi⟩ := hDa
  rw [hqcast] at hm'lo hm'hi
  obtain ⟨hmlo', hmhi'⟩ := err_bound X H m p hpsq hmlo hmhi
  obtain ⟨hm'lo', hm'hi'⟩ := err_bound X H m' q hqsq hm'lo hm'hi
  -- `H ≥ 0` from `X ≤ m·p² ≤ X+H`
  have hH0 : (0 : ℝ) ≤ H := by linarith [hmlo, hmhi]
  -- `H/q² ≤ H/p²` since `p² ≤ q²`
  have hpq2 : p ^ 2 ≤ q ^ 2 := by
    apply pow_le_pow_left₀ hppos.le; rw [hp, hq]; linarith
  have hHpq : H / q ^ 2 ≤ H / p ^ 2 := by
    apply div_le_div_of_nonneg_left hH0 hpsq hpq2
  -- `Ffun = (m - m') - ((m - X/p²) - (m' - X/q²))`
  set n : ℤ := m - m' with hn
  have hFval : Ffun X (a : ℝ) p = (n : ℝ)
      - (((m : ℝ) - X / p ^ 2) - ((m' : ℝ) - X / q ^ 2)) := by
    rw [hn]; push_cast
    rw [show Ffun X (a : ℝ) p = X / p ^ 2 - X / q ^ 2 by unfold Ffun; rw [hq]]
    ring
  -- distance to the integer `n`
  have hbound : |Ffun X (a : ℝ) p - (n : ℝ)| ≤ 2 * H / p ^ 2 := by
    rw [hFval, show ((n : ℝ) - (((m : ℝ) - X / p ^ 2) - ((m' : ℝ) - X / q ^ 2))) - (n : ℝ)
        = -(((m : ℝ) - X / p ^ 2) - ((m' : ℝ) - X / q ^ 2)) by ring, abs_neg, abs_le]
    constructor
    · have : (0 : ℝ) ≤ ((m' : ℝ) - X / q ^ 2) := hm'lo'
      have hub : ((m' : ℝ) - X / q ^ 2) ≤ H / p ^ 2 := le_trans hm'hi' hHpq
      rw [show -(2 * H / p ^ 2) = -(H / p ^ 2) - (H / p ^ 2) by ring]
      linarith [hmlo', hmhi']
    · rw [show 2 * H / p ^ 2 = H / p ^ 2 + H / p ^ 2 by ring]
      have hub' : ((m' : ℝ) - X / q ^ 2) ≤ H / p ^ 2 := le_trans hm'hi' hHpq
      linarith [hmhi', hm'lo']
  calc distInt (Ffun X (a : ℝ) (d : ℝ))
      = distInt (Ffun X (a : ℝ) p) := by rw [hp]
    _ ≤ |Ffun X (a : ℝ) p - (n : ℝ)| := round_le _ n
    _ ≤ 2 * H / p ^ 2 := hbound
    _ = 2 * H / (d : ℝ) ^ 2 := by rw [hp]

/-- **Tiny gaps impossible.** If `d, d+a ∈ 𝒟` (window `[X, X+H]`), `0 < a`, `D ≤ d ≤ 2D`, and the
`X`-large regime `8 H D ≤ X`, `D² ≤ X`, `1 ≤ H`, `2 ≤ D` holds, then the gap is `≥ D³/(6X)`.

(Roadmap step 2: if `a < d³/(6X)` then `F_a(d) < 1/2`, so its nearest integer is `0`, forcing
`F_a(d) ≤ H/d²`, whence `a ≤ 2Hd/X ≤ 4HD/X < 1`, contradicting `a ≥ 1`.) -/
theorem tiny_gap_impossible (X H D : ℝ) (a d : ℤ)
    (hX : 0 < X) (hH : 1 ≤ H) (hD : 2 ≤ D) (hDX : D ^ 2 ≤ X) (hHD2 : 4 * H ≤ D ^ 2)
    (hDd : D ≤ (d : ℝ)) (hd2D : (d : ℝ) ≤ 2 * D)
    (hHD : 8 * H * D ≤ X) (ha : 0 < a)
    (hd : inD X H d) (hda : inD X H (d + a)) :
    D ^ 3 / (6 * X) ≤ (a : ℝ) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hDpos : (0 : ℝ) < D := by linarith
  have hdR : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le hDpos hDd
  by_contra hcon
  push Not at hcon
  -- `a < d³/(6X)` and `a ≤ d`
  have hd3 : D ^ 3 ≤ (d : ℝ) ^ 3 := by gcongr
  have haltd3 : (a : ℝ) < (d : ℝ) ^ 3 / (6 * X) := by
    refine lt_of_lt_of_le hcon ?_
    apply div_le_div_of_nonneg_right hd3 (by positivity)
  have hd2X : (d : ℝ) ^ 2 ≤ 6 * X := by
    linarith [mul_le_mul hd2D hd2D hdR.le (by linarith : (0:ℝ) ≤ 2 * D), hDX, sq_nonneg D]
  have hale : (a : ℝ) ≤ (d : ℝ) := by
    have : (d : ℝ) ^ 3 / (6 * X) ≤ (d : ℝ) := by
      rw [div_le_iff₀ (by positivity)]; linarith [mul_le_mul_of_nonneg_left hd2X hdR.le]
    linarith [haltd3, this]
  -- points and squares
  set p : ℝ := (d : ℝ) with hp
  set q : ℝ := (d : ℝ) + (a : ℝ) with hq
  have hqcast : ((d + a : ℤ) : ℝ) = q := by rw [hq]; push_cast; ring
  have hppos : 0 < p := hdR
  have hqpos : 0 < q := by rw [hq]; positivity
  have hpsq : (0:ℝ) < p ^ 2 := by positivity
  have hqsq : (0:ℝ) < q ^ 2 := by positivity
  have hpne : p ≠ 0 := ne_of_gt hppos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  -- multipliers and error terms
  obtain ⟨m0, hm0lo, hm0hi⟩ := hd
  obtain ⟨m1, hm1lo, hm1hi⟩ := hda
  rw [hqcast] at hm1lo hm1hi
  set e0 : ℝ := (m0 : ℝ) - X / p ^ 2 with he0
  set e1 : ℝ := (m1 : ℝ) - X / q ^ 2 with he1
  obtain ⟨he0lo, he0hi⟩ := err_bound X H m0 p hpsq hm0lo hm0hi
  obtain ⟨he1lo, he1hi⟩ := err_bound X H m1 q hqsq hm1lo hm1hi
  -- F = (m0 - m1) - (e0 - e1)
  set k : ℤ := m0 - m1 with hk
  have hFval : Ffun X (a:ℝ) p = (k : ℝ) - (e0 - e1) := by
    rw [hk]; push_cast
    rw [show Ffun X (a:ℝ) p = X / p ^ 2 - X / q ^ 2 by unfold Ffun; rw [hq]]
    rw [he0, he1]; ring
  -- F factorization & two-sided bounds
  have hFfac : Ffun X (a:ℝ) p = X * (a:ℝ) * ((a:ℝ) + 2 * p) / (p ^ 2 * q ^ 2) := by
    rw [show q = p + (a:ℝ) by rw [hp, hq]]
    exact Ffun_factor X (a:ℝ) p hpne (by rw [← hq]; exact hqne)
  have haRpos : (0:ℝ) < (a:ℝ) := by linarith
  have hFnn : 0 ≤ Ffun X (a:ℝ) p := by rw [hFfac]; positivity
  have hcoef : (0:ℝ) ≤ X * (a:ℝ) := by positivity
  have hFub : Ffun X (a:ℝ) p ≤ 3 * X * (a:ℝ) / p ^ 3 := by
    rw [hFfac, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq2 : p ^ 2 ≤ q ^ 2 := by apply pow_le_pow_left₀ hppos.le; rw [hp, hq]; linarith
    -- goal: X·a·(a+2p)·p³ ≤ 3·X·a·(p²·q²)
    have e1 : X * (a:ℝ) * ((a:ℝ) + 2 * p) * p ^ 3 ≤ X * (a:ℝ) * (3 * p) * p ^ 3 := by
      have : X * (a:ℝ) * ((a:ℝ) + 2 * p) ≤ X * (a:ℝ) * (3 * p) := by
        apply mul_le_mul_of_nonneg_left _ hcoef; linarith [hale]
      linarith [mul_le_mul_of_nonneg_right this (pow_pos hppos 3).le]
    have e2 : X * (a:ℝ) * (3 * p) * p ^ 3 ≤ 3 * X * (a:ℝ) * (p ^ 2 * q ^ 2) := by
      have : X * (a:ℝ) * (p ^ 2 * p ^ 2) ≤ X * (a:ℝ) * (p ^ 2 * q ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hcoef; exact mul_le_mul_of_nonneg_left hq2 hpsq.le
      linarith [this]
    linarith [e1, e2]
  have hFlb : X * (a:ℝ) / (2 * p ^ 3) ≤ Ffun X (a:ℝ) p := by
    rw [hFfac, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq2 : q ^ 2 ≤ 4 * p ^ 2 := by
      have : q ≤ 2 * p := by rw [hq]; linarith
      linarith [mul_le_mul this this hqpos.le (by linarith : (0:ℝ) ≤ 2 * p)]
    -- goal: X·a·(p²·q²) ≤ X·a·(a+2p)·(2·p³)
    have e1 : X * (a:ℝ) * (p ^ 2 * q ^ 2) ≤ X * (a:ℝ) * (p ^ 2 * (4 * p ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hcoef; exact mul_le_mul_of_nonneg_left hq2 hpsq.le
    have e2 : X * (a:ℝ) * (p ^ 2 * (4 * p ^ 2)) ≤ X * (a:ℝ) * ((a:ℝ) + 2 * p) * (2 * p ^ 3) := by
      have hb : X * (a:ℝ) * (2 * p) * (2 * p ^ 3) ≤ X * (a:ℝ) * ((a:ℝ) + 2 * p) * (2 * p ^ 3) := by
        have : X * (a:ℝ) * (2 * p) ≤ X * (a:ℝ) * ((a:ℝ) + 2 * p) := by
          apply mul_le_mul_of_nonneg_left _ hcoef; linarith [haRpos]
        linarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 2 * p ^ 3)]
      linarith [hb]
    linarith [e1, e2]
  -- F < 1/2
  have hFhalf : Ffun X (a:ℝ) p < 1 / 2 := by
    have hstep : 3 * X * (a:ℝ) / p ^ 3 < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have hh : (a:ℝ) < p ^ 3 / (6 * X) := by rw [hp]; exact haltd3
      rw [lt_div_iff₀ (by positivity)] at hh
      linarith [hh]
    linarith [hFub]
  -- δ = H/p²;  e0 - e1 ∈ [-δ, δ];  δ < 1/2
  have hδlt : H / p ^ 2 < 1 / 2 := by
    rw [div_lt_iff₀ hpsq]
    have hpD : D ^ 2 ≤ p ^ 2 := by apply pow_le_pow_left₀ hDpos.le hDd
    linarith [hH, hHD2, hpD]
  have he1' : e1 ≤ H / p ^ 2 := by
    refine le_trans he1hi ?_
    apply div_le_div_of_nonneg_left (by linarith) hpsq
    apply pow_le_pow_left₀ hppos.le; rw [hq]; linarith
  have hediff_lo : -(H / p ^ 2) ≤ e0 - e1 := by linarith [he0lo, he1']
  have hediff_hi : e0 - e1 ≤ H / p ^ 2 := by linarith [he0hi, he1lo]
  -- nearest integer to F is 0
  have hk0 : k = 0 := by
    have hFk : |Ffun X (a:ℝ) p - (k:ℝ)| ≤ H / p ^ 2 := by
      rw [hFval, show (k:ℝ) - (e0 - e1) - (k:ℝ) = -(e0 - e1) by ring, abs_neg, abs_le]
      exact ⟨by linarith [hediff_hi], by linarith [hediff_lo]⟩
    by_contra hkne
    rw [abs_le] at hFk
    rcases lt_or_gt_of_ne hkne with hneg | hpos
    · have : (k:ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith [hFnn, hδlt, this, hFk.1]
    · have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      linarith [hFhalf, hδlt, this, hFk.2]
  -- F = -(e0 - e1) ≤ δ, hence Xa/(2p³) ≤ H/p², so X·a ≤ 2Hp ≤ 4HD ≤ X/2, a < 1
  have hFle : Ffun X (a:ℝ) p ≤ H / p ^ 2 := by
    rw [hFval, hk0]; push_cast; simp only [zero_sub, neg_sub]; linarith [hediff_lo]
  have hchain : X * (a:ℝ) / (2 * p ^ 3) ≤ H / p ^ 2 := le_trans hFlb hFle
  have haub : X * (a:ℝ) ≤ 2 * H * p := by
    rw [div_le_div_iff₀ (by positivity) hpsq] at hchain
    exact le_of_mul_le_mul_right
      (by linarith [hchain] : X * (a:ℝ) * p ^ 2 ≤ 2 * H * p * p ^ 2) hpsq
  -- contradiction: X·a ≤ 2Hp = 2Hd ≤ 4HD ≤ X/2 < X ≤ X·a
  have : X * (a:ℝ) ≤ X / 2 := by
    have h2Hp : 2 * H * p ≤ 4 * H * D := by
      rw [hp]; linarith [mul_le_mul_of_nonneg_left hd2D (by linarith : (0:ℝ) ≤ 2 * H)]
    linarith [haub, h2Hp, hHD]
  linarith [this, mul_le_mul_of_nonneg_left haR hX.le]

/-! ## Determinant isolation -/

/-- `Δ₀(a,b,d) = b·X/d² − (a+b)·X/(d+a)² + a·X/(d+a+b)²`, second-divided-difference combination. -/
private noncomputable def Dfun (X a b d : ℝ) : ℝ :=
  b * X / d ^ 2 - (a + b) * X / (d + a) ^ 2 + a * X / (d + a + b) ^ 2

/-- Exact factorization of `Δ₀` (sympy-verified). -/
private theorem Dfun_factor (X a b d : ℝ)
    (hd : d ≠ 0) (hda : d + a ≠ 0) (hdab : d + a + b ≠ 0) :
    Dfun X a b d =
      X * a * b * (a + b) * (a ^ 2 + a * b + 4 * a * d + 2 * b * d + 3 * d ^ 2)
        / (d ^ 2 * (d + a) ^ 2 * (d + a + b) ^ 2) := by
  unfold Dfun; field_simp; ring

/-- Two-sided bound on `Δ₀` for `D ≤ d ≤ 2D`, `a+b ≤ d`, `a,b>0`. -/
private theorem Dfun_bounds (X _H D a b d : ℝ)
    (hX : 0 < X) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b)
    (hDd : D ≤ d) (hd2D : d ≤ 2 * D) (hab : a + b ≤ d) :
    (3 / 256 : ℝ) * X * (a * b * (a + b)) / D ^ 4 ≤ Dfun X a b d ∧
      Dfun X a b d ≤ 11 * X * (a * b * (a + b)) / D ^ 4 := by
  have hdpos : 0 < d := lt_of_lt_of_le hD hDd
  have hda : (0:ℝ) < d + a := by linarith
  have hdab : (0:ℝ) < d + a + b := by linarith
  have hane : d ≠ 0 := ne_of_gt hdpos
  have hbne : d + a ≠ 0 := ne_of_gt hda
  have hcne : d + a + b ≠ 0 := ne_of_gt hdab
  -- a ≤ d, b ≤ d
  have hale : a ≤ d := by linarith
  have hble : b ≤ d := by linarith
  set Num : ℝ := X * a * b * (a + b) * (a ^ 2 + a * b + 4 * a * d + 2 * b * d + 3 * d ^ 2) with hN
  set Den : ℝ := d ^ 2 * (d + a) ^ 2 * (d + a + b) ^ 2 with hDen
  have hNpos : 0 < Num := by rw [hN]; positivity
  have hDenpos : 0 < Den := by rw [hDen]; positivity
  have hval : Dfun X a b d = Num / Den := by rw [Dfun_factor X a b d hane hbne hcne, hN, hDen]
  -- polynomial G bounds:  3d² ≤ G ≤ 11d²
  have hG_lb : 3 * d ^ 2 ≤ a ^ 2 + a * b + 4 * a * d + 2 * b * d + 3 * d ^ 2 := by
    linarith [sq_nonneg a, mul_pos ha hb, mul_pos ha hdpos, mul_pos hb hdpos]
  have hG_ub : a ^ 2 + a * b + 4 * a * d + 2 * b * d + 3 * d ^ 2 ≤ 11 * d ^ 2 := by
    linarith [mul_le_mul hale hale ha.le hdpos.le, mul_le_mul hale hble hb.le hdpos.le,
      mul_le_mul_of_nonneg_right hale hdpos.le, mul_le_mul_of_nonneg_right hble hdpos.le]
  -- Den bounds:  d⁶ ≤ Den ≤ 16 d⁶ ;  and d⁶ ≥ D⁶, d⁶ ≤ 16 D⁶
  have hDen_lb : d ^ 6 ≤ Den := by
    rw [hDen]
    have h1 : d ^ 2 ≤ (d + a) ^ 2 := by linarith [mul_pos ha hdpos, sq_nonneg a]
    have h2 : d ^ 2 ≤ (d + a + b) ^ 2 := by
      linarith [sq_nonneg a, sq_nonneg b, mul_pos ha hb, mul_pos ha hdpos, mul_pos hb hdpos]
    calc d ^ 6 = d ^ 2 * d ^ 2 * d ^ 2 := by ring
      _ ≤ d ^ 2 * (d + a) ^ 2 * (d + a + b) ^ 2 := by gcongr
  have hDen_ub : Den ≤ 16 * d ^ 6 := by
    rw [hDen]
    have h1 : (d + a) ^ 2 ≤ 4 * d ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hale hdpos.le, mul_le_mul hale hale ha.le hdpos.le]
    have h2 : (d + a + b) ^ 2 ≤ 4 * d ^ 2 := by
      linarith [mul_le_mul hab hab (by linarith : (0:ℝ) ≤ a + b) hdpos.le,
        mul_le_mul_of_nonneg_left hab hdpos.le]
    calc d ^ 2 * (d + a) ^ 2 * (d + a + b) ^ 2 ≤ d ^ 2 * (4 * d ^ 2) * (4 * d ^ 2) := by
          gcongr
      _ = 16 * d ^ 6 := by ring
  refine ⟨?_, ?_⟩
  · -- lower:  (3/256) X ab(a+b)/D⁴ ≤ Num/Den
    rw [hval, le_div_iff₀ hDenpos]
    -- Num ≥ X ab(a+b)·3d², Den ≤ 16 d⁶ ≤ 16·(2D)⁴·d²... use Den ≤ 16 d⁶ and d ≤ 2D
    have hd6 : d ^ 6 ≤ 16 * D ^ 4 * d ^ 2 := by
      have h4 : d ^ 4 ≤ (2 * D) ^ 4 := pow_le_pow_left₀ hdpos.le hd2D 4
      calc d ^ 6 = d ^ 4 * d ^ 2 := by ring
        _ ≤ (2 * D) ^ 4 * d ^ 2 := by gcongr
        _ = 16 * D ^ 4 * d ^ 2 := by ring
    have hNum_lb : X * (a * b * (a + b)) * (3 * d ^ 2) ≤ Num := by
      rw [hN]
      have hC : (0:ℝ) ≤ X * (a * b * (a + b)) := by positivity
      linarith [mul_le_mul_of_nonneg_left hG_lb hC]
    have hkey : (3 / 256 : ℝ) * X * (a * b * (a + b)) / D ^ 4 * Den
        ≤ (3 / 256 : ℝ) * X * (a * b * (a + b)) / D ^ 4 * (16 * d ^ 6) := by
      apply mul_le_mul_of_nonneg_left hDen_ub
      apply div_nonneg (by positivity) (by positivity)
    refine le_trans hkey ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hC : (0:ℝ) ≤ X * (a * b * (a + b)) := by positivity
    have HA : X * (a * b * (a + b)) * (3 * d ^ 2) * D ^ 4 ≤ Num * D ^ 4 :=
      mul_le_mul_of_nonneg_right hNum_lb (by positivity)
    have HB : X * (a * b * (a + b)) * d ^ 6 ≤ X * (a * b * (a + b)) * (16 * D ^ 4 * d ^ 2) :=
      mul_le_mul_of_nonneg_left hd6 hC
    linarith [HA, HB]
  · -- upper:  Num/Den ≤ 11 X ab(a+b)/D⁴
    rw [hval, div_le_iff₀ hDenpos]
    have hNum_ub : Num ≤ X * (a * b * (a + b)) * (11 * d ^ 2) := by
      rw [hN]
      have hC : (0:ℝ) ≤ X * (a * b * (a + b)) := by positivity
      linarith [mul_le_mul_of_nonneg_left hG_ub hC]
    have hD4d6 : D ^ 4 * d ^ 2 ≤ d ^ 6 := by
      linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD.le hDd 4)
        (by positivity : (0:ℝ) ≤ d ^ 2)]
    -- 11 X ab(a+b)/D⁴ · Den ≥ 11 X ab(a+b)/D⁴ · d⁶ ≥ 11 X ab(a+b)·d²  ≥ Num
    have hk1 : 11 * X * (a * b * (a + b)) / D ^ 4 * d ^ 6
        ≤ 11 * X * (a * b * (a + b)) / D ^ 4 * Den := by
      apply mul_le_mul_of_nonneg_left hDen_lb
      apply div_nonneg (by positivity) (by positivity)
    refine le_trans ?_ hk1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hC : (0:ℝ) ≤ X * (a * b * (a + b)) := by positivity
    have HA : Num * D ^ 4 ≤ X * (a * b * (a + b)) * (11 * d ^ 2) * D ^ 4 :=
      mul_le_mul_of_nonneg_right hNum_ub (by positivity)
    have HB : 11 * (X * (a * b * (a + b))) * (D ^ 4 * d ^ 2)
        ≤ 11 * (X * (a * b * (a + b))) * d ^ 6 :=
      mul_le_mul_of_nonneg_left hD4d6 (by positivity)
    linarith [HA, HB]

/-- **No two consecutive sub-threshold gaps.** For three consecutive `𝒟`-elements
`d, d+a, d+a+b` (window `[X,X+H]`, `0<a`, `0<b`) in `[D,2D]` with `a+b ≤ d`, the algebraic
threshold conditions below (both gaps `≤ T₀ = thr/2`, the determinant `Δ₀` dominating its
error, and `H,D,X > 0`) are contradictory. So among three consecutive `𝒟`-elements the two
gaps cannot both be `≤ T₀`. -/
theorem no_two_small_gaps (X H D : ℝ) (a b d : ℤ) (T0 : ℝ)
    (hX : 0 < X) (hH : 0 < H) (hD : 0 < D)
    (ha : 0 < a) (hb : 0 < b)
    (hDd : D ≤ (d : ℝ)) (hd2D : (d : ℝ) ≤ 2 * D) (hab_d : (a : ℝ) + (b : ℝ) ≤ (d : ℝ))
    (haT : (a : ℝ) ≤ T0) (hbT : (b : ℝ) ≤ T0) (hT0 : 0 < T0)
    (hcube : 8 * X * (2 * T0) ^ 3 ≤ D ^ 4) (heps : 8 * H * (2 * T0) ≤ D ^ 2)
    (hab_big : 2 * H / D ^ 2 < (3 / 256 : ℝ) * X * ((a : ℝ) * (b : ℝ)) / D ^ 4)
    (hd0 : inD X H d) (hda : inD X H (d + a)) (hdab : inD X H (d + a + b)) :
    False := by
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hD hDd
  -- points and squares
  set p0 : ℝ := (d : ℝ) with hp0
  set p1 : ℝ := (d : ℝ) + (a : ℝ) with hp1
  set p2 : ℝ := (d : ℝ) + (a : ℝ) + (b : ℝ) with hp2
  have hp1cast : ((d + a : ℤ) : ℝ) = p1 := by rw [hp1]; push_cast; ring
  have hp2cast : ((d + a + b : ℤ) : ℝ) = p2 := by rw [hp2]; push_cast; ring
  have hp0pos : 0 < p0 := hdpos
  have hp1pos : 0 < p1 := by rw [hp1]; positivity
  have hp2pos : 0 < p2 := by rw [hp2]; positivity
  have hp0sq : (0:ℝ) < p0 ^ 2 := by positivity
  have hp1sq : (0:ℝ) < p1 ^ 2 := by positivity
  have hp2sq : (0:ℝ) < p2 ^ 2 := by positivity
  -- multipliers and errors
  obtain ⟨m0, hm0lo, hm0hi⟩ := hd0
  obtain ⟨m1, hm1lo, hm1hi⟩ := hda
  obtain ⟨m2, hm2lo, hm2hi⟩ := hdab
  rw [hp1cast] at hm1lo hm1hi
  rw [hp2cast] at hm2lo hm2hi
  set e0 : ℝ := (m0 : ℝ) - X / p0 ^ 2 with he0
  set e1 : ℝ := (m1 : ℝ) - X / p1 ^ 2 with he1
  set e2 : ℝ := (m2 : ℝ) - X / p2 ^ 2 with he2
  obtain ⟨he0lo, he0hi⟩ := err_bound X H m0 p0 hp0sq hm0lo hm0hi
  obtain ⟨he1lo, he1hi⟩ := err_bound X H m1 p1 hp1sq hm1lo hm1hi
  obtain ⟨he2lo, he2hi⟩ := err_bound X H m2 p2 hp2sq hm2lo hm2hi
  -- the integer J = b m0 - (a+b) m1 + a m2
  set J : ℤ := b * m0 - (a + b) * m1 + a * m2 with hJ
  set errsum : ℝ := (b:ℝ) * e0 - ((a:ℝ) + b) * e1 + (a:ℝ) * e2 with herr
  have hJval : (J : ℝ) = Dfun X (a:ℝ) (b:ℝ) (d:ℝ) + errsum := by
    rw [hJ]; push_cast
    have hm0e : (m0:ℝ) = X / p0 ^ 2 + e0 := by rw [he0]; ring
    have hm1e : (m1:ℝ) = X / p1 ^ 2 + e1 := by rw [he1]; ring
    have hm2e : (m2:ℝ) = X / p2 ^ 2 + e2 := by rw [he2]; ring
    rw [show Dfun X (a:ℝ) (b:ℝ) (d:ℝ)
          = (b:ℝ) * X / p0 ^ 2 - ((a:ℝ) + b) * X / p1 ^ 2 + (a:ℝ) * X / p2 ^ 2 by
        unfold Dfun; rw [hp0, hp1, hp2]]
    rw [herr, hm0e, hm1e, hm2e]; ring
  -- determinant bounds
  obtain ⟨hD0_lb, hD0_ub⟩ := Dfun_bounds X H D (a:ℝ) (b:ℝ) (d:ℝ) hX hD haR hbR hDd hd2D hab_d
  -- |errsum| ≤ 2(a+b) H / D²
  have hHD2 : ∀ p : ℝ, D ≤ p → H / p ^ 2 ≤ H / D ^ 2 := by
    intro p hp
    have hpsq : D ^ 2 ≤ p ^ 2 := by apply pow_le_pow_left₀ hD.le hp
    exact div_le_div_of_nonneg_left hH.le (by positivity) hpsq
  have he0' : e0 ≤ H / D ^ 2 := le_trans he0hi (hHD2 p0 (by rw [hp0]; exact hDd))
  have he1' : e1 ≤ H / D ^ 2 := le_trans he1hi (hHD2 p1 (by rw [hp1]; linarith))
  have he2' : e2 ≤ H / D ^ 2 := le_trans he2hi (hHD2 p2 (by rw [hp2]; linarith))
  have hHDnn : (0:ℝ) ≤ H / D ^ 2 := by positivity
  have hab2T : (a:ℝ) + b ≤ 2 * T0 := by linarith [haT, hbT]
  have herr_bd : |errsum| ≤ 2 * ((a:ℝ) + b) * (H / D ^ 2) := by
    have t0 : |(b:ℝ) * e0| ≤ (b:ℝ) * (H / D ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left he0' hbR.le
    have t1 : |((a:ℝ) + b) * e1| ≤ ((a:ℝ) + b) * (H / D ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left he1' (by linarith)
    have t2 : |(a:ℝ) * e2| ≤ (a:ℝ) * (H / D ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left he2' haR.le
    have htri : |errsum| ≤ |(b:ℝ) * e0| + |((a:ℝ) + b) * e1| + |(a:ℝ) * e2| := by
      have heq : errsum = (b:ℝ) * e0 + (-(((a:ℝ) + b) * e1) + (a:ℝ) * e2) := by rw [herr]; ring
      rw [heq]
      refine le_trans (abs_add_le _ _) ?_
      have hinner : |(-(((a:ℝ) + b) * e1) + (a:ℝ) * e2)| ≤ |((a:ℝ) + b) * e1| + |(a:ℝ) * e2| := by
        refine le_trans (abs_add_le _ _) ?_; rw [abs_neg]
      linarith [hinner]
    calc |errsum| ≤ |(b:ℝ) * e0| + |((a:ℝ) + b) * e1| + |(a:ℝ) * e2| := htri
      _ ≤ 2 * ((a:ℝ) + b) * (H / D ^ 2) := by linarith [t0, t1, t2, haR, hbR]
  -- Δ₀ ≤ 11/32
  have hD0small : Dfun X (a:ℝ) (b:ℝ) (d:ℝ) ≤ 11 / 32 := by
    refine le_trans hD0_ub ?_
    -- 11 X ab(a+b)/D⁴ ≤ 11 X (2T0³)... ≤ 11/32, using ab(a+b) ≤ 2T0³ and 64 X T0³ ≤ D⁴
    have habp : (a:ℝ) * (b:ℝ) * ((a:ℝ) + b) ≤ 2 * T0 ^ 3 := by
      have h1 : (a:ℝ) * (b:ℝ) ≤ T0 ^ 2 := by linarith [mul_le_mul haT hbT hbR.le hT0.le]
      have h2 : (a:ℝ) + b ≤ 2 * T0 := hab2T
      linarith [mul_le_mul h1 h2 (by linarith : (0:ℝ) ≤ (a:ℝ) + b)
        (by positivity : (0:ℝ) ≤ T0 ^ 2)]
    have hXT : 64 * X * T0 ^ 3 ≤ D ^ 4 := by linarith [hcube]
    rw [div_le_iff₀ (by positivity)]
    have hstep : 11 * X * ((a:ℝ) * (b:ℝ) * ((a:ℝ) + b)) ≤ 11 * X * (2 * T0 ^ 3) := by
      apply mul_le_mul_of_nonneg_left habp (by positivity)
    linarith [hstep, hXT]
  -- |errsum| ≤ 1/4
  have herr_quarter : |errsum| ≤ 1 / 4 := by
    refine le_trans herr_bd ?_
    -- 2(a+b) H/D² ≤ 4 T0 H/D² ≤ 1/4, using a+b ≤ 2T0 and 16 H T0 ≤ D²
    have h16 : 16 * H * T0 ≤ D ^ 2 := by linarith [heps]
    have hle : 2 * ((a:ℝ) + b) * (H / D ^ 2) ≤ 4 * T0 * (H / D ^ 2) := by
      have : 2 * ((a:ℝ) + b) ≤ 4 * T0 := by linarith [hab2T]
      apply mul_le_mul_of_nonneg_right this hHDnn
    refine le_trans hle ?_
    rw [show (4:ℝ) * T0 * (H / D ^ 2) = 4 * T0 * H / D ^ 2 by ring, div_le_iff₀ (by positivity)]
    linarith [h16]
  -- |J| < 1
  have hJabs_lt : |(J:ℝ)| < 1 := by
    rw [hJval]
    have : 0 ≤ Dfun X (a:ℝ) (b:ℝ) (d:ℝ) := by
      refine le_trans ?_ hD0_lb; positivity
    calc |Dfun X (a:ℝ) (b:ℝ) (d:ℝ) + errsum|
        ≤ |Dfun X (a:ℝ) (b:ℝ) (d:ℝ)| + |errsum| := abs_add_le _ _
      _ = Dfun X (a:ℝ) (b:ℝ) (d:ℝ) + |errsum| := by rw [abs_of_nonneg this]
      _ ≤ 11 / 32 + 1 / 4 := by linarith [hD0small, herr_quarter]
      _ < 1 := by norm_num
  -- J ≠ 0:  Δ₀ > |errsum|
  have hD0_dom : |errsum| < Dfun X (a:ℝ) (b:ℝ) (d:ℝ) := by
    refine lt_of_le_of_lt herr_bd ?_
    -- 2(a+b) H/D² < (3/256) X ab(a+b)/D⁴ ≤ Δ₀
    have hfac : 2 * ((a:ℝ) + b) * (H / D ^ 2) < (3 / 256 : ℝ) * X * ((a:ℝ) * (b:ℝ)) / D ^ 4 * ((a:ℝ) + b) := by
      have hpos : (0:ℝ) < (a:ℝ) + b := by linarith
      have := mul_lt_mul_of_pos_right hab_big hpos
      calc 2 * ((a:ℝ) + b) * (H / D ^ 2) = 2 * H / D ^ 2 * ((a:ℝ) + b) := by ring
        _ < (3 / 256 : ℝ) * X * ((a:ℝ) * (b:ℝ)) / D ^ 4 * ((a:ℝ) + b) := this
    refine lt_of_lt_of_le hfac ?_
    -- (3/256) X ab/D⁴ ·(a+b) = (3/256) X ab(a+b)/D⁴ ≤ Δ₀
    rw [show (3 / 256 : ℝ) * X * ((a:ℝ) * (b:ℝ)) / D ^ 4 * ((a:ℝ) + b)
          = (3 / 256 : ℝ) * X * ((a:ℝ) * (b:ℝ) * ((a:ℝ) + b)) / D ^ 4 by ring]
    exact hD0_lb
  have hJabs_pos : 0 < |(J:ℝ)| := by
    rw [hJval]
    have hD0nn : 0 ≤ Dfun X (a:ℝ) (b:ℝ) (d:ℝ) := by refine le_trans ?_ hD0_lb; positivity
    have hb' : Dfun X (a:ℝ) (b:ℝ) (d:ℝ) - |errsum| ≤ |Dfun X (a:ℝ) (b:ℝ) (d:ℝ) + errsum| := by
      have h := abs_sub_abs_le_abs_sub (Dfun X (a:ℝ) (b:ℝ) (d:ℝ)) (-errsum)
      simp only [abs_neg, sub_neg_eq_add] at h
      rw [abs_of_nonneg hD0nn] at h; exact h
    linarith [hb', hD0_dom]
  -- integrality contradiction
  have hJzero : J = 0 := by
    by_contra hne
    have h1 : (1:ℤ) ≤ |J| := Int.one_le_abs hne
    have : (1:ℝ) ≤ |(J:ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h1
    linarith [hJabs_lt]
  rw [hJzero] at hJabs_pos; simp at hJabs_pos

end Squarefree
