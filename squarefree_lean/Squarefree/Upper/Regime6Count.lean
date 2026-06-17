import Squarefree.Upper.Regime6
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# §6 regime assembly (part 2): global `C²` extension and per-`r` count

The B1/B2 layer feeding `prop_6_1` (`Upper/Regime.lean`): the global `C²` extension `ftil_ext`
of the §6 phase, the curvature `F`-scale `A²·lam ≍ F`, and the per-`r` integer-count bound from
Prop 4.3 (`nearCurve_count`).  See `../explicit_writeup.md` lines 1255–1268 and `math_audit.md` §6.
-/

open Classical Finset
open Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 1000000

/-! ## Stage B1: global `C²` extension of `ftil` via a bump cutoff -/

/-- `ContDiffAt` for the literal `ftil X r ·` at a positive point. -/
private theorem ftil_contDiffAt' {X r a : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    ContDiffAt ℝ 2 (fun a => ftil X r a) a := by
  show ContDiffAt ℝ 2 (fun a : ℝ => r * Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) / a ^ 2) a
  have hinner : ContDiffAt ℝ 2 (fun a : ℝ => Real.sqrt (X * a ^ 3 / r)) a := by
    refine ContDiffAt.sqrt ?_ (by positivity)
    fun_prop (disch := assumption)
  have hrad : ContDiffAt ℝ 2 (fun a : ℝ => a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r)) a := by
    fun_prop (disch := assumption)
  have houter : ContDiffAt ℝ 2
      (fun a : ℝ => Real.sqrt (a ^ 2 + 4 * Real.sqrt (X * a ^ 3 / r))) a := by
    refine ContDiffAt.sqrt hrad ?_
    have : 0 < Real.sqrt (X * a ^ 3 / r) := Real.sqrt_pos.mpr (by positivity)
    positivity
  exact (contDiffAt_const.mul houter).div (contDiffAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt ha))

/-- The `C²` bump cutoff for the §6 window: `1` on `[A/4,3A]`, supported in `(A/8,4A) ⊂ (0,∞)`.
Center `13A/8`, `rIn = 11A/8`, `rOut = 12A/8 = 3A/2`. -/
private noncomputable def ftilBump (A : ℝ) (hA : 0 < A) : ContDiffBump (13 * A / 8 : ℝ) where
  rIn := 11 * A / 8
  rOut := 12 * A / 8
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The globally `C²` extension of `ftil X r ·`: bump cutoff times `ftil`. -/
private noncomputable def ftil_ext (X r A : ℝ) (hA : 0 < A) : ℝ → ℝ :=
  fun a => (ftilBump A hA) a * ftil X r a

/-- The bump is `1` on `[A/4, 3A]`. -/
private theorem ftilBump_eq_one {A : ℝ} (hA : 0 < A) {a : ℝ}
    (h1 : A / 4 ≤ a) (h2 : a ≤ 3 * A) : (ftilBump A hA) a = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> · show _ ; simp only [ftilBump]; linarith

/-- The bump vanishes off `(A/8, 25A/8)` — in particular it is `0` for `a ≤ A/8`. -/
private theorem ftilBump_eventuallyEq_zero {A : ℝ} (hA : 0 < A) {a : ℝ}
    (ha : a < A / 8) : (ftilBump A hA) =ᶠ[nhds a] 0 := by
  have hopen : IsOpen {x : ℝ | x < A / 8} := isOpen_lt continuous_id continuous_const
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ha) ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  show (ftilBump A hA) x = (0 : ℝ → ℝ) x
  rw [Pi.zero_apply]
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  simp only [ftilBump]
  -- need 12A/8 ≤ |x - 13A/8|, i.e. x - 13A/8 ≤ -12A/8
  rw [le_abs]; right; linarith

/-- `ftil_ext` is globally `C²`. -/
private theorem ftil_ext_contDiff {X r A : ℝ} (hX : 0 < X) (hr : 0 < r) (hA : 0 < A) :
    ContDiff ℝ 2 (ftil_ext X r A hA) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  by_cases hpos : A / 16 < a
  · -- in the region where ftil is smooth (a > A/16 > 0)
    have ha0 : 0 < a := by linarith
    have hbump : ContDiffAt ℝ 2 (fun y => (ftilBump A hA) y) a :=
      ContDiffBump.contDiffAt _
    have hftil : ContDiffAt ℝ 2 (fun y => ftil X r y) a := ftil_contDiffAt' hX ha0 hr
    exact hbump.mul hftil
  · -- a ≤ A/16 < A/8: bump is eventually 0, so ftil_ext is eventually 0
    push Not at hpos
    have ha8 : a < A / 8 := by linarith
    have hz : ftil_ext X r A hA =ᶠ[nhds a] 0 := by
      have := ftilBump_eventuallyEq_zero hA ha8
      filter_upwards [this] with x hx
      show (ftilBump A hA) x * ftil X r x = (0 : ℝ → ℝ) x
      rw [Pi.zero_apply] at hx ⊢
      rw [hx, zero_mul]
    exact ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℝ))) hz

/-- `ftil_ext` agrees with `ftil` on `[A/4, 3A]`. -/
private theorem ftil_ext_eq {X r A : ℝ} (hA : 0 < A) {a : ℝ}
    (h1 : A / 4 ≤ a) (h2 : a ≤ 3 * A) : ftil_ext X r A hA a = ftil X r a := by
  unfold ftil_ext
  rw [ftilBump_eq_one hA h1 h2, one_mul]

/-- Second derivatives of `ftil_ext` and `ftil` agree on `[A/2, 5A/2]` (the bump ≡ 1 on a
neighborhood `(A/4, 3A)`). -/
private theorem ftil_ext_deriv2_eq {X r A : ℝ} (hA : 0 < A) {a : ℝ}
    (h1 : A / 2 ≤ a) (h2 : a ≤ 5 * A / 2) :
    iteratedDeriv 2 (ftil_ext X r A hA) a = iteratedDeriv 2 (fun t => ftil X r t) a := by
  have heq : ftil_ext X r A hA =ᶠ[nhds a] (fun t => ftil X r t) := by
    have hopen : IsOpen (Set.Ioo (A / 4) (3 * A)) := isOpen_Ioo
    have hmem : a ∈ Set.Ioo (A / 4) (3 * A) := by
      constructor <;> · show _ ; linarith
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
    intro x hx
    exact ftil_ext_eq hA (le_of_lt hx.1) (le_of_lt hx.2)
  exact Filter.EventuallyEq.iteratedDeriv_eq 2 heq

/-! ## Stage B2 scale: the curvature scale `A²·lam ≍ F` -/

/-- Two-sided bound on `(f̃''(a))²` in terms of `r²·w/a⁸` (`w = √(Xa³/r)`), under the regime
`16a² ≤ 4√(Xa³/r)`.  Rational constants `81/5 ≤ (f̃''(a))²·a⁸/(r²w) ≤ 313/8`. -/
private theorem ftil_dd_sq_bounds {X r a : ℝ} (hX : 0 < X) (hr : 0 < r) (ha : 0 < a)
    (hreg : 16 * a ^ 2 ≤ 4 * Real.sqrt (X * a ^ 3 / r)) :
    (81 / 5 : ℝ) * (r ^ 2 * Real.sqrt (X * a ^ 3 / r) / a ^ 8)
        ≤ (iteratedDeriv 2 (fun t => ftil X r t) a) ^ 2
      ∧ (iteratedDeriv 2 (fun t => ftil X r t) a) ^ 2
        ≤ (313 / 8 : ℝ) * (r ^ 2 * Real.sqrt (X * a ^ 3 / r) / a ^ 8) := by
  set w := Real.sqrt (X * a ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w ^ 2 = X * a ^ 3 / r := Real.sq_sqrt (by positivity)
  -- regime: 4a² ≤ w
  have hreg' : 4 * a ^ 2 ≤ w := by linarith [hreg]
  have ha2w : a ^ 2 ≤ w / 4 := by linarith [hreg']
  -- D² = a²+4w, D³ via 6th power
  set D := Real.sqrt (a ^ 2 + 4 * w) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = a ^ 2 + 4 * w := Real.sq_sqrt (by positivity)
  -- the exact value
  have hval : iteratedDeriv 2 (fun t => ftil X r t) a
      = r * (4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2) / (2 * a ^ 4 * D ^ 3) := by
    rw [ftil_iteratedDeriv2 hX hr ha]
  rw [hval]
  set N := 4 * a ^ 4 + 39 * a ^ 2 * w + 90 * w ^ 2 with hNdef
  have hNpos : 0 < N := by rw [hNdef]; positivity
  -- N bounds: 90w² ≤ N ≤ 100w²
  have hNlo : 90 * w ^ 2 ≤ N := by rw [hNdef]; nlinarith [sq_nonneg a, hwpos.le, ha]
  have hNhi : N ≤ 100 * w ^ 2 := by
    rw [hNdef]
    nlinarith [ha2w, hwpos, sq_nonneg a, mul_pos (mul_pos ha ha) hwpos,
      mul_le_mul_of_nonneg_right ha2w hwpos.le]
  -- D⁶ = (a²+4w)³ ; 64w³ ≤ D⁶ ≤ 125w³
  have hD6 : D ^ 6 = (a ^ 2 + 4 * w) ^ 3 := by
    rw [show D ^ 6 = (D ^ 2) ^ 3 by ring, hD2]
  have hD6lo : (64 : ℝ) * w ^ 3 ≤ D ^ 6 := by
    rw [hD6]; nlinarith [hwpos, sq_nonneg a, mul_pos (mul_pos hwpos hwpos) hwpos]
  have hD6hi : D ^ 6 ≤ (125 : ℝ) * w ^ 3 := by
    rw [hD6]; nlinarith [ha2w, hwpos, sq_nonneg a, mul_pos (mul_pos hwpos hwpos) hwpos,
      mul_pos hwpos hwpos]
  -- compute (f̃'')² = r²N²/(4a⁸D⁶)
  have hsq : (r * N / (2 * a ^ 4 * D ^ 3)) ^ 2 = r ^ 2 * N ^ 2 / (4 * a ^ 8 * D ^ 6) := by
    rw [div_pow]; congr 1
    · ring
    · ring
  rw [hsq]
  have ha8 : 0 < a ^ 8 := by positivity
  have hD6pos : 0 < D ^ 6 := by positivity
  have h4a8D6 : 0 < 4 * a ^ 8 * D ^ 6 := by positivity
  constructor
  · -- lower: 81/5 · r²w/a⁸ ≤ r²N²/(4a⁸D⁶)
    rw [le_div_iff₀ h4a8D6]
    -- 81/5·r²w/a⁸·(4a⁸D⁶) = (324/5)·r²w·D⁶ ≤ ... need r²N² ≥ that
    have hN2lo : (90 * w ^ 2) ^ 2 ≤ N ^ 2 := by nlinarith [hNlo, hNpos, hwpos]
    have key : (81 / 5 : ℝ) * (r ^ 2 * w / a ^ 8) * (4 * a ^ 8 * D ^ 6)
        ≤ r ^ 2 * N ^ 2 := by
      have e1 : (81 / 5 : ℝ) * (r ^ 2 * w / a ^ 8) * (4 * a ^ 8 * D ^ 6)
          = (324 / 5 : ℝ) * r ^ 2 * w * D ^ 6 := by field_simp; ring
      rw [e1]
      have hD6le : (324 / 5 : ℝ) * r ^ 2 * w * D ^ 6
          ≤ (324 / 5 : ℝ) * r ^ 2 * w * (125 * w ^ 3) :=
        mul_le_mul_of_nonneg_left hD6hi (by positivity)
      calc (324 / 5 : ℝ) * r ^ 2 * w * D ^ 6
          ≤ (324 / 5 : ℝ) * r ^ 2 * w * (125 * w ^ 3) := hD6le
        _ = r ^ 2 * (8100 * w ^ 4) := by ring
        _ = r ^ 2 * (90 * w ^ 2) ^ 2 := by ring
        _ ≤ r ^ 2 * N ^ 2 := mul_le_mul_of_nonneg_left hN2lo (by positivity)
    linarith [key]
  · -- upper: r²N²/(4a⁸D⁶) ≤ 313/8 · r²w/a⁸
    rw [div_le_iff₀ h4a8D6]
    have hN2hi : N ^ 2 ≤ (100 * w ^ 2) ^ 2 := by nlinarith [hNhi, hNpos, hwpos]
    have key : r ^ 2 * N ^ 2
        ≤ (313 / 8 : ℝ) * (r ^ 2 * w / a ^ 8) * (4 * a ^ 8 * D ^ 6) := by
      have e1 : (313 / 8 : ℝ) * (r ^ 2 * w / a ^ 8) * (4 * a ^ 8 * D ^ 6)
          = (313 / 2 : ℝ) * r ^ 2 * w * D ^ 6 := by field_simp; ring
      rw [e1]
      have hD6ge : (313 / 2 : ℝ) * r ^ 2 * w * (64 * w ^ 3)
          ≤ (313 / 2 : ℝ) * r ^ 2 * w * D ^ 6 :=
        mul_le_mul_of_nonneg_left hD6lo (by positivity)
      calc r ^ 2 * N ^ 2
          ≤ r ^ 2 * (100 * w ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hN2hi (by positivity)
        _ = r ^ 2 * (10000 * w ^ 4) := by ring
        _ ≤ (313 / 2 : ℝ) * r ^ 2 * w * (64 * w ^ 3) := by nlinarith [hwpos, sq_nonneg r, mul_pos hwpos hwpos]
        _ ≤ (313 / 2 : ℝ) * r ^ 2 * w * D ^ 6 := hD6ge
    linarith [key]

/-- Explicit lower curvature-scale constant `cl = ((81/5)²/(256⁴·72³))^{1/4}`. -/
noncomputable def prop6ScaleLo : ℝ := ((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) ^ (1/4 : ℝ)

/-- Explicit upper curvature-scale constant `cu = ((313/8)²·16³)^{1/4}`. -/
noncomputable def prop6ScaleHi : ℝ := ((313/8 : ℝ) ^ 2 * 16 ^ 3) ^ (1/4 : ℝ)

theorem prop6ScaleLo_pos : 0 < prop6ScaleLo := by unfold prop6ScaleLo; positivity
theorem prop6ScaleHi_pos : 0 < prop6ScaleHi := by unfold prop6ScaleHi; positivity

/-- The polynomial 4th-power identity `R³·X/A⁵ = F⁴` (writeup line 1258 scale). -/
private theorem R3X_div_A5_eq_F4 {P : Globals} (S : Scale P) :
    S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hH := P.H_pos; have hG := P.G_pos
  rw [Scale.R, Scale.A, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

/-- **Curvature `F`-scale** (writeup line 1258): for `r ∈ [R/72, 16R]`, the curvature `lam`
(from `ftil_curv_bound`) satisfies `A²·lam ≍ F`, with absolute constants.  Proved via the
4th-power identity `R³X/A⁵ = F⁴`. -/
private theorem ftil_curv_F_scale {P : Globals} {S : Scale P} {r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hrlo : (1/72) * S.R ≤ r) (hrhi : r ≤ 16 * S.R) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ a ∈ Set.Icc (S.A / 2) (5 * S.A / 2),
        lam ≤ iteratedDeriv 2 (fun t => ftil P.X r t) a ∧
        iteratedDeriv 2 (fun t => ftil P.X r t) a ≤ 256 * lam) ∧
        prop6ScaleLo * S.F ≤ S.A ^ 2 * lam ∧ S.A ^ 2 * lam ≤ prop6ScaleHi * S.F := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hFpos : 0 < S.F := by unfold Scale.F; positivity
  have hRpos : 0 < S.R := by rw [Scale.R]; positivity
  -- curvature regime + ftil_curv_bound
  have hreg := prop6_curv_regime hAD hr0 hrhi
  obtain ⟨lam, hlampos, hlamspec⟩ := ftil_curv_bound hX hr0 hApos hreg
  refine ⟨lam, hlampos, hlamspec, ?_⟩
  -- the per-a square bound at a = A
  have hAmem : S.A ∈ Set.Icc (S.A / 2) (5 * S.A / 2) := by
    constructor <;> · show _ ; linarith
  obtain ⟨hl1, hl2⟩ := hlamspec S.A hAmem
  obtain ⟨hsq_lo, hsq_hi⟩ := ftil_dd_sq_bounds hX hr0 hApos (hreg S.A hAmem)
  set f2 := iteratedDeriv 2 (fun t => ftil P.X r t) S.A with hf2def
  have hf2pos : 0 < f2 := lt_of_lt_of_le hlampos hl1
  -- w(A): w² = X A³/r ; let q := r²·w/A⁸ ≥ 0
  set w := Real.sqrt (P.X * S.A ^ 3 / r) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w ^ 2 = P.X * S.A ^ 3 / r := Real.sq_sqrt (by positivity)
  set q := r ^ 2 * w / S.A ^ 8 with hqdef
  have hqpos : 0 < q := by rw [hqdef]; positivity
  -- the key 4th-power normalization: A⁸·q² = r³·X/A⁵
  have hAq2 : S.A ^ 8 * q ^ 2 = r ^ 3 * P.X / S.A ^ 5 := by
    rw [hqdef]
    have : (r ^ 2 * w / S.A ^ 8) ^ 2 = r ^ 4 * w ^ 2 / S.A ^ 16 := by
      rw [div_pow]; congr 1 <;> ring
    rw [show S.A ^ 8 * (r ^ 2 * w / S.A ^ 8) ^ 2 = S.A ^ 8 * (r ^ 4 * w ^ 2 / S.A ^ 16) by rw [this]]
    rw [hw2]
    field_simp
  have hF4 : S.R ^ 3 * P.X / S.A ^ 5 = S.F ^ 4 := R3X_div_A5_eq_F4 S
  -- r³X/A⁵ two-sided in R³X/A⁵ = F⁴
  have hr3lo : ((1/72 : ℝ)) ^ 3 * S.F ^ 4 ≤ r ^ 3 * P.X / S.A ^ 5 := by
    have hpow : ((1/72 : ℝ) * S.R) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by positivity) hrlo 3
    rw [← hF4, show ((1/72 : ℝ)) ^ 3 * (S.R ^ 3 * P.X / S.A ^ 5)
          = ((1/72 : ℝ) * S.R) ^ 3 * P.X / S.A ^ 5 by ring]
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hX.le) (by positivity)
  have hr3hi : r ^ 3 * P.X / S.A ^ 5 ≤ (16 : ℝ) ^ 3 * S.F ^ 4 := by
    have hpow : r ^ 3 ≤ (16 * S.R) ^ 3 := pow_le_pow_left₀ hr0.le hrhi 3
    rw [← hF4, show (16 : ℝ) ^ 3 * (S.R ^ 3 * P.X / S.A ^ 5)
          = (16 * S.R) ^ 3 * P.X / S.A ^ 5 by ring]
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hX.le) (by positivity)
  -- 4th-power bounds on (A²·lam)
  -- upper: (A²lam)⁴ ≤ Ku·F⁴ with Ku = (313/8)²·16³
  have hUp4 : (S.A ^ 2 * lam) ^ 4 ≤ ((313/8 : ℝ) ^ 2 * 16 ^ 3) * S.F ^ 4 := by
    have hlam4 : lam ^ 4 ≤ f2 ^ 4 := pow_le_pow_left₀ hlampos.le hl1 4
    have hf24 : f2 ^ 4 ≤ (313/8 : ℝ) ^ 2 * q ^ 2 := by
      have : f2 ^ 4 = (f2 ^ 2) ^ 2 := by ring
      rw [this]
      calc (f2 ^ 2) ^ 2 ≤ ((313/8 : ℝ) * q) ^ 2 :=
            pow_le_pow_left₀ (sq_nonneg f2) (by rw [hqdef] at hsq_hi ⊢; exact hsq_hi) 2
        _ = (313/8 : ℝ) ^ 2 * q ^ 2 := by ring
    calc (S.A ^ 2 * lam) ^ 4 = S.A ^ 8 * lam ^ 4 := by ring
      _ ≤ S.A ^ 8 * f2 ^ 4 := mul_le_mul_of_nonneg_left hlam4 (by positivity)
      _ ≤ S.A ^ 8 * ((313/8 : ℝ) ^ 2 * q ^ 2) := mul_le_mul_of_nonneg_left hf24 (by positivity)
      _ = (313/8 : ℝ) ^ 2 * (S.A ^ 8 * q ^ 2) := by ring
      _ = (313/8 : ℝ) ^ 2 * (r ^ 3 * P.X / S.A ^ 5) := by rw [hAq2]
      _ ≤ (313/8 : ℝ) ^ 2 * ((16 : ℝ) ^ 3 * S.F ^ 4) :=
          mul_le_mul_of_nonneg_left hr3hi (by positivity)
      _ = ((313/8 : ℝ) ^ 2 * 16 ^ 3) * S.F ^ 4 := by ring
  -- lower: Kl·F⁴ ≤ (A²lam)⁴ with Kl = (81/5)²/(256⁴·72³)
  have hLo4 : ((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) * S.F ^ 4 ≤ (S.A ^ 2 * lam) ^ 4 := by
    have hlamge : f2 / 256 ≤ lam := by linarith [hl2]
    have hlam4 : (f2 / 256) ^ 4 ≤ lam ^ 4 :=
      pow_le_pow_left₀ (by positivity) hlamge 4
    have hf24 : (81/5 : ℝ) ^ 2 * q ^ 2 ≤ f2 ^ 4 := by
      have : f2 ^ 4 = (f2 ^ 2) ^ 2 := by ring
      rw [this]
      calc (81/5 : ℝ) ^ 2 * q ^ 2 = ((81/5 : ℝ) * q) ^ 2 := by ring
        _ ≤ (f2 ^ 2) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by rw [hqdef] at hsq_lo ⊢; exact hsq_lo) 2
    calc ((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) * S.F ^ 4
        = (1 / 256 ^ 4) * ((81/5 : ℝ) ^ 2 * ((1/72 : ℝ) ^ 3 * S.F ^ 4)) := by ring
      _ ≤ (1 / 256 ^ 4) * ((81/5 : ℝ) ^ 2 * (r ^ 3 * P.X / S.A ^ 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr3lo (by positivity)) (by positivity)
      _ = (1 / 256 ^ 4) * ((81/5 : ℝ) ^ 2 * (S.A ^ 8 * q ^ 2)) := by rw [hAq2]
      _ = (1 / 256 ^ 4) * (S.A ^ 8 * ((81/5 : ℝ) ^ 2 * q ^ 2)) := by ring
      _ ≤ (1 / 256 ^ 4) * (S.A ^ 8 * f2 ^ 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf24 (by positivity)) (by positivity)
      _ = S.A ^ 8 * (f2 / 256) ^ 4 := by ring
      _ ≤ S.A ^ 8 * lam ^ 4 := mul_le_mul_of_nonneg_left hlam4 (by positivity)
      _ = (S.A ^ 2 * lam) ^ 4 := by ring
  -- extract 4th roots
  refine ⟨?_, ?_⟩
  · -- cl·F ≤ A²lam :  (cl·F)⁴ = Kl·F⁴ ≤ (A²lam)⁴
    rw [prop6ScaleLo]
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
    have hc4 : (((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) ^ (1/4 : ℝ)) ^ 4
        = (81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3) := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]
      norm_num
    calc (((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) ^ (1/4 : ℝ) * S.F) ^ 4
        = (((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) ^ (1/4 : ℝ)) ^ 4 * S.F ^ 4 := by ring
      _ = ((81/5 : ℝ) ^ 2 / (256 ^ 4 * 72 ^ 3)) * S.F ^ 4 := by rw [hc4]
      _ ≤ (S.A ^ 2 * lam) ^ 4 := hLo4
  · -- A²lam ≤ cu·F :  (A²lam)⁴ ≤ Ku·F⁴ = (cu·F)⁴
    rw [prop6ScaleHi]
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
    have hc4 : (((313/8 : ℝ) ^ 2 * 16 ^ 3) ^ (1/4 : ℝ)) ^ 4 = (313/8 : ℝ) ^ 2 * 16 ^ 3 := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]
      norm_num
    calc (S.A ^ 2 * lam) ^ 4
        ≤ ((313/8 : ℝ) ^ 2 * 16 ^ 3) * S.F ^ 4 := hUp4
      _ = (((313/8 : ℝ) ^ 2 * 16 ^ 3) ^ (1/4 : ℝ)) ^ 4 * S.F ^ 4 := by rw [hc4]
      _ = (((313/8 : ℝ) ^ 2 * 16 ^ 3) ^ (1/4 : ℝ) * S.F) ^ 4 := by ring

/-! ## Stage B2: per-`r` count over `a ∼ A` -/

/-- The uniform per-`r` count constant: `max (nearCurve_count constant) 2`, an absolute
constant independent of `r`, so it can be pulled out of the sum over `r`. -/
noncomputable def prop6CountConst : ℝ := max (Squarefree.Geometry.nearCurve_count.choose) 2

theorem prop6CountConst_pos : 0 < prop6CountConst :=
  lt_of_lt_of_le Squarefree.Geometry.nearCurve_count.choose_spec.1 (le_max_left _ _)

/-- **Per-`r` count** (writeup line 1265).  For `r ∈ [R/72, 16R]`, the number of `a ∈ (⌊A⌋, ⌊2A⌋]`
with `distInt(f̃ₐ(r)) ≤ δ` is bounded by Prop 4.3 applied to the global `C²` extension
`ftil_ext`, with `N = A`, `T = A²·lam ≍ F`.  The constant is the absolute `prop6CountConst`
(uniform in `r`); returns the scale data `T ≍ F`. -/
theorem prop6_count_per_r {P : Globals} {S : Scale P} {r : ℝ} {δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (hr0 : 0 < r) (hrlo : (1/72) * S.R ≤ r) (hrhi : r ≤ 16 * S.R)
    (hA1 : 1 < S.A) (hδ0 : 0 < δ) (hone : 1 < prop6ScaleLo * S.F) :
    ∃ T : ℝ, 1 < T ∧
      prop6ScaleLo * S.F ≤ T ∧ T ≤ prop6ScaleHi * S.F ∧
      ((((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ)).filter
          (fun n => distInt (ftil P.X r n) ≤ δ)).card : ℝ)
        ≤ prop6CountConst * ((S.A * T) ^ (1/3 : ℝ) + S.A * δ
               + S.A * Real.sqrt (δ / T) * Real.log (2 + S.A * Real.sqrt (δ / T)) + 1) := by
  classical
  have hX := P.X_pos
  have hApos : 0 < S.A := lt_trans one_pos hA1
  have hAne : S.A ≠ 0 := hApos.ne'
  obtain ⟨lam, hlampos, hlamspec, hclF, hcuF⟩ :=
    ftil_curv_F_scale hAD hr0 hrlo hrhi
  set T := S.A ^ 2 * lam with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hT1 : 1 < T := lt_of_lt_of_le hone hclF
  -- the normalized curve Fnorm s = ftil_ext(A·s)/T
  set F0 := ftil_ext P.X r S.A hApos with hF0def
  have hF0cd : ContDiff ℝ 2 F0 := ftil_ext_contDiff hX hr0 hApos
  set Fnorm : ℝ → ℝ := fun s => F0 (S.A * s) / T with hFnormdef
  -- ContDiff of Fnorm
  have hFcomp : ContDiff ℝ 2 (fun s : ℝ => F0 (S.A * s)) := by
    have : ContDiff ℝ 2 (fun s : ℝ => F0 (S.A * s)) :=
      hF0cd.comp (by fun_prop)
    exact this
  have hFnormcd : ContDiff ℝ 2 Fnorm := by
    have : ContDiff ℝ 2 (fun s => (fun s => F0 (S.A * s)) s / T) :=
      hFcomp.div_const T
    exact this
  -- iteratedDeriv 2 Fnorm s = A²/T · iteratedDeriv 2 F0 (A·s)
  have hFnorm2 : ∀ s : ℝ, iteratedDeriv 2 Fnorm s
      = (S.A ^ 2 / T) * iteratedDeriv 2 F0 (S.A * s) := by
    intro s
    have hd1 : iteratedDeriv 2 Fnorm s = iteratedDeriv 2 (fun s => F0 (S.A * s)) s / T := by
      rw [hFnormdef]; exact iteratedDeriv_div_const _ T
    rw [hd1, iteratedDeriv_comp_const_mul hF0cd S.A]
    ring
  -- value identity: T·Fnorm(n/A) = F0(n)
  have hval : ∀ n : ℝ, T * Fnorm (n / S.A) = F0 n := by
    intro n
    rw [hFnormdef]
    simp only
    rw [mul_div_cancel₀ n hAne, mul_div_cancel₀ (F0 n) hTpos.ne']
  -- the curvature normalization: for s ∈ [1/2,5/2], Fnorm''(s) ∈ [1,256]
  have hFn_lo : ∀ s ∈ Set.Icc (1/2 : ℝ) (5/2), 1 ≤ |iteratedDeriv 2 Fnorm s| := by
    intro s hs
    obtain ⟨hsl, hsr⟩ := hs
    have hAs1 : S.A / 2 ≤ S.A * s := by nlinarith [hApos, hsl]
    have hAs2 : S.A * s ≤ 5 * S.A / 2 := by nlinarith [hApos, hsr]
    have hext := ftil_ext_deriv2_eq (X := P.X) (r := r) hApos hAs1 hAs2
    have hspec := (hlamspec (S.A * s) ⟨hAs1, hAs2⟩).1
    rw [hFnorm2, hF0def, hext]
    rw [abs_of_pos (by
      have : 0 < iteratedDeriv 2 (fun t => ftil P.X r t) (S.A * s) :=
        lt_of_lt_of_le hlampos hspec
      positivity)]
    rw [hTdef]
    rw [show S.A ^ 2 / (S.A ^ 2 * lam) = 1 / lam by field_simp]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlampos, one_mul]
    exact hspec
  have hFn_hi : ∀ s ∈ Set.Icc (1/2 : ℝ) (5/2), |iteratedDeriv 2 Fnorm s| ≤ 256 := by
    intro s hs
    obtain ⟨hsl, hsr⟩ := hs
    have hAs1 : S.A / 2 ≤ S.A * s := by nlinarith [hApos, hsl]
    have hAs2 : S.A * s ≤ 5 * S.A / 2 := by nlinarith [hApos, hsr]
    have hext := ftil_ext_deriv2_eq (X := P.X) (r := r) hApos hAs1 hAs2
    have hspec := (hlamspec (S.A * s) ⟨hAs1, hAs2⟩).2
    have hspeclo := (hlamspec (S.A * s) ⟨hAs1, hAs2⟩).1
    rw [hFnorm2, hF0def, hext]
    rw [abs_of_pos (by
      have : 0 < iteratedDeriv 2 (fun t => ftil P.X r t) (S.A * s) :=
        lt_of_lt_of_le hlampos hspeclo
      positivity)]
    rw [hTdef]
    rw [show S.A ^ 2 / (S.A ^ 2 * lam) = 1 / lam by field_simp]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hlampos]
    linarith [hspec]
  -- apply nearCurve_count; the constant is the uniform `prop6CountConst = max C₀ 2`.
  set C₀ : ℝ := Squarefree.Geometry.nearCurve_count.choose with hC₀def
  have hcount := Squarefree.Geometry.nearCurve_count.choose_spec.2
  rw [← hC₀def] at hcount
  set C : ℝ := prop6CountConst with hCdef
  have hC : 0 < C := prop6CountConst_pos
  have hcle : C₀ ≤ C := by rw [hCdef, prop6CountConst, ← hC₀def]; exact le_max_left _ _
  have hc2 : (2:ℝ) ≤ C := by rw [hCdef, prop6CountConst]; exact le_max_right _ _
  -- the RHS sum (without `C`) is nonnegative
  have hδle : (0:ℝ) ≤ δ := hδ0.le
  have hsumnn : (0:ℝ) ≤ (S.A * T) ^ (1/3 : ℝ) + S.A * δ
      + S.A * Real.sqrt (δ / T) * Real.log (2 + S.A * Real.sqrt (δ / T)) + 1 := by
    have h1 : (0:ℝ) ≤ (S.A * T) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h2 : (0:ℝ) ≤ S.A * δ := by positivity
    have h3 : (0:ℝ) ≤ S.A * Real.sqrt (δ / T)
        * Real.log (2 + S.A * Real.sqrt (δ / T)) := by
      have hsqrt : (0:ℝ) ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
      have hlog : (0:ℝ) ≤ Real.log (2 + S.A * Real.sqrt (δ / T)) := by
        apply Real.log_nonneg
        have : (0:ℝ) ≤ S.A * Real.sqrt (δ / T) := by positivity
        linarith
      positivity
    linarith
  refine ⟨T, hT1, hclF, hcuF, ?_⟩
  by_cases hδ1 : δ < 1
  · -- δ < 1: the original Prop 4.3 route.
    have hkey := hcount S.A T δ Fnorm hA1 hT1 hδ0 hδ1 hFnormcd hFn_lo hFn_hi
    -- normalize the `do`-block in `hkey` to `.image Int.cast`
    simp only [bind_pure_comp, Finset.fmap_def] at hkey
    -- the two filter predicates agree on the image of `Ioc ⌊A⌋ ⌊2A⌋`
    have hfilter_eq :
        ((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ)).filter
            (fun n => distInt (ftil P.X r n) ≤ δ)
          = ((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ)).filter
              (fun n => distInt (T * Fnorm (n / S.A)) ≤ δ) := by
      apply Finset.filter_congr
      intro x hx
      obtain ⟨n, hnmem, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hnl, hnr⟩ := Finset.mem_Ioc.mp hnmem
      -- n ∈ [A/4, 3A]:  n > ⌊A⌋ ⟹ n ≥ A ;  n ≤ ⌊2A⌋ ≤ 2A
      have hnlo : S.A / 4 ≤ (n : ℝ) := by
        have h1 : S.A < (⌊S.A⌋ : ℝ) + 1 := Int.lt_floor_add_one S.A
        have h2 : (⌊S.A⌋ : ℝ) + 1 ≤ (n : ℝ) := by
          have : ⌊S.A⌋ + 1 ≤ n := hnl
          exact_mod_cast this
        linarith [hApos]
      have hnhi : (n : ℝ) ≤ 3 * S.A := by
        have h1 : (⌊2 * S.A⌋ : ℝ) ≤ 2 * S.A := Int.floor_le (2 * S.A)
        have h2 : (n : ℝ) ≤ (⌊2 * S.A⌋ : ℝ) := by exact_mod_cast hnr
        linarith [hApos]
      have heqval : T * Fnorm ((n : ℝ) / S.A) = ftil P.X r (n : ℝ) := by
        rw [hval (n : ℝ)]
        show F0 (n : ℝ) = ftil P.X r (n : ℝ)
        rw [hF0def]
        exact ftil_ext_eq (X := P.X) (r := r) hApos hnlo hnhi
      rw [heqval]
    rw [hfilter_eq]
    refine le_trans hkey (mul_le_mul_of_nonneg_right hcle hsumnn)
  · -- δ ≥ 1: every n has distInt(ftil) ≤ 1/2 < 1 ≤ δ, so the filter is the full image.
    push Not at hδ1
    -- the filter equals the whole image
    have hfull :
        ((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ)).filter
            (fun n => distInt (ftil P.X r n) ≤ δ)
          = (Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ) := by
      apply Finset.filter_true_of_mem
      intro x _
      calc distInt (ftil P.X r x) ≤ 1/2 := by
            unfold distInt; exact abs_sub_round _
        _ ≤ δ := by linarith [hδ1]
    rw [hfull]
    -- card of image ≤ card of Ioc = ⌊2A⌋ - ⌊A⌋ ≤ 2A + 1, and bound by 2·(A·δ)
    have hcard_img : (((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).image (Int.cast : ℤ → ℝ)).card : ℝ)
        ≤ ((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    refine le_trans hcard_img ?_
    -- card (Ioc ⌊A⌋ ⌊2A⌋) = (⌊2A⌋ - ⌊A⌋).toNat ≤ 2A - A + 1 = A + 1
    have hcardIoc : ((Finset.Ioc ⌊S.A⌋ ⌊2 * S.A⌋).card : ℝ) ≤ S.A + 1 := by
      rw [Int.card_Ioc]
      -- (⌊2A⌋ - ⌊A⌋).toNat ≤ ⌊2A⌋ - ⌊A⌋  (as reals, when nonneg) ≤ 2A - (A-1) = A+1
      have hub : ((⌊2 * S.A⌋ - ⌊S.A⌋).toNat : ℝ) ≤ S.A + 1 := by
        rcases le_or_gt (⌊2 * S.A⌋ - ⌊S.A⌋) 0 with hle | hlt
        · have : ((⌊2 * S.A⌋ - ⌊S.A⌋).toNat : ℝ) = 0 := by
            rw [Int.toNat_of_nonpos hle]; simp
          rw [this]; linarith [hApos]
        · have hcastZ : (((⌊2 * S.A⌋ - ⌊S.A⌋).toNat : ℤ) : ℝ) = (⌊2 * S.A⌋ : ℝ) - (⌊S.A⌋ : ℝ) := by
            rw [Int.toNat_of_nonneg hlt.le]; push_cast; ring
          have hcast : ((⌊2 * S.A⌋ - ⌊S.A⌋).toNat : ℝ) = (⌊2 * S.A⌋ : ℝ) - (⌊S.A⌋ : ℝ) := by
            rw [← hcastZ]; push_cast; ring
          rw [hcast]
          have h2A : (⌊2 * S.A⌋ : ℝ) ≤ 2 * S.A := Int.floor_le _
          have hA : S.A - 1 < (⌊S.A⌋ : ℝ) := by
            have := Int.sub_one_lt_floor S.A; linarith
          linarith
      exact hub
    refine le_trans hcardIoc ?_
    -- A + 1 ≤ 2·A·δ ≤ C·(... + A·δ + ...)  using 1 < A, 1 ≤ δ
    have hAδ : S.A + 1 ≤ 2 * (S.A * δ) := by
      have h1 : S.A * 1 ≤ S.A * δ := mul_le_mul_of_nonneg_left hδ1 hApos.le
      nlinarith [hApos, hA1, hδ1, h1]
    refine le_trans hAδ ?_
    -- 2·(A·δ) ≤ C·(sum) since C ≥ 2 and the sum ≥ A·δ + (nonneg)
    have hCge2 : (2:ℝ) ≤ C := hc2
    have hothernn : (0:ℝ) ≤ (S.A * T) ^ (1/3 : ℝ)
        + S.A * Real.sqrt (δ / T) * Real.log (2 + S.A * Real.sqrt (δ / T)) + 1 := by
      have h1 : (0:ℝ) ≤ (S.A * T) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
      have h3 : (0:ℝ) ≤ S.A * Real.sqrt (δ / T)
          * Real.log (2 + S.A * Real.sqrt (δ / T)) := by
        have hsqrt : (0:ℝ) ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
        have hlog : (0:ℝ) ≤ Real.log (2 + S.A * Real.sqrt (δ / T)) := by
          apply Real.log_nonneg
          have : (0:ℝ) ≤ S.A * Real.sqrt (δ / T) := by positivity
          linarith
        positivity
      linarith
    have hAδnn : (0:ℝ) ≤ S.A * δ := by positivity
    nlinarith [hCge2, hAδnn, hothernn, mul_le_mul_of_nonneg_right hCge2 hAδnn]


end Squarefree
