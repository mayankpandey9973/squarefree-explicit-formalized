import Squarefree.Structure.ADecompAux
import Mathlib

/-!
# §5 sharp Taylor expansion of the mixed second difference `F_{a,b}`

`Fab X a b d := Ffun X a d - Ffun X a (d+b)`, where `Ffun X a d = X/d² − X/(d+a)²`.
Unfolding, `Fab X a b d = X·(1/d² − 1/(d+a)² − 1/(d+b)² + 1/(d+a+b)²)`, a mixed second
difference.  We prove its sharp 4-term Taylor expansion (writeup 769):

`|Fab X a b d − (6abX/d⁴ − 12ab(a+b)X/d⁵)| ≤ 400·X·a·b·(a+b)²/d⁶`.

The proof: the per-point order-4 Taylor remainder `rem x` of `1/(d+x)²` satisfies an exact
algebraic identity reducing `Fab − leading` to `X·(rem(a+b) − rem a − rem b)`, and a double
mean-value argument bounds the mixed difference by `a·b·|rem₂ ζ|` for some `ζ ∈ (0,a+b)`,
with `|rem₂ ζ| ≤ 400(a+b)²/d⁶`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- `F_{a,b}(d) = F_a(d) − F_a(d+b)`, the mixed second difference of `X/d²`. -/
noncomputable def Fab (X a b d : ℝ) : ℝ := Ffun X a d - Ffun X a (d + b)

section Expand

variable {d x : ℝ}

/-- Order-4 Taylor remainder of `1/(d+x)²` at the base point `d`. -/
private noncomputable def rem (d x : ℝ) : ℝ :=
  1 / (d + x) ^ 2 - (1 / d ^ 2 - 2 * x / d ^ 3 + 3 * x ^ 2 / d ^ 4 - 4 * x ^ 3 / d ^ 5)

/-- First derivative of `rem d ·`. -/
private noncomputable def rem1 (d x : ℝ) : ℝ :=
  -2 / (d + x) ^ 3 + 2 / d ^ 3 - 6 * x / d ^ 4 + 12 * x ^ 2 / d ^ 5

/-- Second derivative of `rem d ·`. -/
private noncomputable def rem2 (d x : ℝ) : ℝ :=
  6 / (d + x) ^ 4 - 6 / d ^ 4 + 24 * x / d ^ 5

/-- `rem` vanishes at `x = 0`. -/
private theorem rem_zero : rem d 0 = 0 := by
  simp only [rem, add_zero]
  ring

/-- `HasDerivAt (rem d ·) (rem1 d x) x` whenever `d ≠ 0` and `d + x ≠ 0`. -/
private theorem rem_hasDerivAt (hd : d ≠ 0) (hdx : d + x ≠ 0) :
    HasDerivAt (fun y => rem d y) (rem1 d x) x := by
  have hbase : HasDerivAt (fun y => (d + y)) 1 x := by
    simpa using (hasDerivAt_id x).const_add d
  have hsq : HasDerivAt (fun y => (d + y) ^ 2) (2 * (d + x) ^ 1 * 1) x :=
    hbase.pow 2
  have hsqne : (d + x) ^ 2 ≠ 0 := pow_ne_zero 2 hdx
  have hinv : HasDerivAt (fun y => 1 / (d + y) ^ 2)
      (-(2 * (d + x) ^ 1 * 1) / ((d + x) ^ 2) ^ 2) x := by
    simpa [one_div] using hsq.inv hsqne
  -- the polynomial part
  have hx2 : HasDerivAt (fun y => y ^ 2) (2 * x ^ 1 * 1) x := (hasDerivAt_id x).pow 2
  have hx3 : HasDerivAt (fun y => y ^ 3) (3 * x ^ 2 * 1) x := (hasDerivAt_id x).pow 3
  have hpoly : HasDerivAt
      (fun y => 1 / d ^ 2 - 2 * y / d ^ 3 + 3 * y ^ 2 / d ^ 4 - 4 * y ^ 3 / d ^ 5)
      (-2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5) x := by
    have t1 : HasDerivAt (fun y => 2 * y / d ^ 3) (2 / d ^ 3) x := by
      have := ((hasDerivAt_id x).const_mul (2 : ℝ)).div_const (d ^ 3)
      simpa using this
    have t2 : HasDerivAt (fun y => 3 * y ^ 2 / d ^ 4) (6 * x / d ^ 4) x := by
      have := (hx2.const_mul (3 : ℝ)).div_const (d ^ 4)
      have h2 : (3 : ℝ) * (2 * x ^ 1 * 1) / d ^ 4 = 6 * x / d ^ 4 := by ring
      rw [h2] at this; exact this
    have t3 : HasDerivAt (fun y => 4 * y ^ 3 / d ^ 5) (12 * x ^ 2 / d ^ 5) x := by
      have := (hx3.const_mul (4 : ℝ)).div_const (d ^ 5)
      have h3 : (4 : ℝ) * (3 * x ^ 2 * 1) / d ^ 5 = 12 * x ^ 2 / d ^ 5 := by ring
      rw [h3] at this; exact this
    have hc : HasDerivAt (fun _ : ℝ => 1 / d ^ 2) 0 x := hasDerivAt_const x _
    have hraw := ((hc.sub t1).add t2).sub t3
    have hde : (0 : ℝ) - 2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5
        = -2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5 := by ring
    rw [hde] at hraw
    exact hraw
  have hraw := hinv.sub hpoly
  have hde : -(2 * (d + x) ^ 1 * 1) / ((d + x) ^ 2) ^ 2 -
        (-2 / d ^ 3 + 6 * x / d ^ 4 - 12 * x ^ 2 / d ^ 5) = rem1 d x := by
    simp only [rem1]
    field_simp
    ring
  rw [hde] at hraw
  exact hraw

/-- `HasDerivAt (rem1 d ·) (rem2 d x) x` whenever `d ≠ 0` and `d + x ≠ 0`. -/
private theorem rem1_hasDerivAt (hd : d ≠ 0) (hdx : d + x ≠ 0) :
    HasDerivAt (fun y => rem1 d y) (rem2 d x) x := by
  have hbase : HasDerivAt (fun y => (d + y)) 1 x := by
    simpa using (hasDerivAt_id x).const_add d
  have hcube : HasDerivAt (fun y => (d + y) ^ 3) (3 * (d + x) ^ 2 * 1) x :=
    hbase.pow 3
  have hcubene : (d + x) ^ 3 ≠ 0 := pow_ne_zero 3 hdx
  have h1 : HasDerivAt (fun y => 1 / (d + y) ^ 3)
      (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2) x := by
    simpa [one_div] using hcube.inv hcubene
  have hinv : HasDerivAt (fun y => -2 / (d + y) ^ 3)
      (-2 * (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2)) x := by
    have hraw := h1.const_mul (-2 : ℝ)
    have hfe : (fun y => -2 * (1 / (d + y) ^ 3)) = (fun y => -2 / (d + y) ^ 3) := by
      ext y; rw [mul_one_div]
    rw [hfe] at hraw
    exact hraw
  have hx2 : HasDerivAt (fun y => y ^ 2) (2 * x ^ 1 * 1) x := (hasDerivAt_id x).pow 2
  have hpoly : HasDerivAt
      (fun y => 2 / d ^ 3 - 6 * y / d ^ 4 + 12 * y ^ 2 / d ^ 5)
      (-6 / d ^ 4 + 24 * x / d ^ 5) x := by
    have t1 : HasDerivAt (fun y => 6 * y / d ^ 4) (6 / d ^ 4) x := by
      have := ((hasDerivAt_id x).const_mul (6 : ℝ)).div_const (d ^ 4)
      simpa using this
    have t2 : HasDerivAt (fun y => 12 * y ^ 2 / d ^ 5) (24 * x / d ^ 5) x := by
      have := (hx2.const_mul (12 : ℝ)).div_const (d ^ 5)
      have h2 : (12 : ℝ) * (2 * x ^ 1 * 1) / d ^ 5 = 24 * x / d ^ 5 := by ring
      rw [h2] at this; exact this
    have hc : HasDerivAt (fun _ : ℝ => 2 / d ^ 3) 0 x := hasDerivAt_const x _
    have hraw := (hc.sub t1).add t2
    have hde : (0 : ℝ) - 6 / d ^ 4 + 24 * x / d ^ 5 = -6 / d ^ 4 + 24 * x / d ^ 5 := by ring
    rw [hde] at hraw
    exact hraw
  have hcombined : HasDerivAt
      (fun y => -2 / (d + y) ^ 3 + (2 / d ^ 3 - 6 * y / d ^ 4 + 12 * y ^ 2 / d ^ 5))
      (-2 * (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2) +
        (-6 / d ^ 4 + 24 * x / d ^ 5)) x := hinv.add hpoly
  have hfun_eq : (fun y => -2 / (d + y) ^ 3 + (2 / d ^ 3 - 6 * y / d ^ 4 + 12 * y ^ 2 / d ^ 5))
      = (fun y => rem1 d y) := by
    ext y; simp only [rem1]; ring
  have hderiv_eq : -2 * (-(3 * (d + x) ^ 2 * 1) / ((d + x) ^ 3) ^ 2) +
        (-6 / d ^ 4 + 24 * x / d ^ 5) = rem2 d x := by
    simp only [rem2]
    field_simp
    ring
  rw [hfun_eq, hderiv_eq] at hcombined
  exact hcombined

end Expand

/-- Two-sided bound on the second-derivative remainder `rem2`, valid for any `ζ` with
`4·|ζ| ≤ d` (so `d + ζ > 0`).  This is the sign-symmetric extension used when `b < 0`. -/
private theorem rem2_abs_bound {d ζ : ℝ} (hd : 0 < d) (hζd : 4 * |ζ| ≤ d) :
    |rem2 d ζ| ≤ 400 * ζ ^ 2 / d ^ 6 := by
  -- unfold `4*|ζ| ≤ d` into the two one-sided bounds
  have hpair := abs_le.mp (by linarith [hζd] : |ζ| ≤ d / 4)
  have hζhi : ζ ≤ d / 4 := hpair.2
  have hζlo : -(d / 4) ≤ ζ := hpair.1
  have hdz : 0 < d + ζ := by linarith
  have hdz6 : (0:ℝ) < d ^ 6 := by positivity
  have hdzpow : (0:ℝ) < (d + ζ) ^ 4 := by positivity
  have hcd : (0:ℝ) < d ^ 6 * (d + ζ) ^ 4 := by positivity
  have hrw : rem2 d ζ
      = (6 * d ^ 6 - 6 * d ^ 2 * (d + ζ) ^ 4 + 24 * ζ * d * (d + ζ) ^ 4)
        / (d ^ 6 * (d + ζ) ^ 4) := by
    simp only [rem2]
    field_simp
  have hbnd : 400 * ζ ^ 2 / d ^ 6
      = (400 * ζ ^ 2 * (d + ζ) ^ 4) / (d ^ 6 * (d + ζ) ^ 4) := by
    rw [eq_div_iff (ne_of_gt hcd)]
    field_simp
  -- two key facts: ζ ≥ -d/4 gives d³ζ ≥ -d⁴/4 and dζ³ ≥ -d⁴/64
  have hd3 : 0 ≤ d ^ 3 := by positivity
  have hd4 : 0 ≤ d ^ 4 := by positivity
  -- d³·ζ ≥ -(d/4)·d³  (multiply ζ ≥ -d/4 by d³ ≥ 0)
  have hcube : -(d ^ 4 / 4) ≤ d ^ 3 * ζ := by nlinarith [hζlo, hd3]
  -- ζ³ ≥ -(d/4)³ since cube is monotone and ζ ≥ -d/4
  have hquad : (0:ℝ) ≤ ζ ^ 2 - ζ * (d / 4) + (d / 4) ^ 2 := by
    nlinarith [sq_nonneg (ζ - d / 8), sq_nonneg d]
  have hz3 : -(d ^ 3 / 64) ≤ ζ ^ 3 := by
    nlinarith [mul_nonneg (by linarith [hζlo] : (0:ℝ) ≤ ζ + d / 4) hquad]
  -- so d·ζ³ ≥ -d⁴/64
  have hdz3 : -(d ^ 4 / 64) ≤ d * ζ ^ 3 := by nlinarith [hz3, hd]
  -- the degree-4 factors g (after pulling out ζ²) are nonneg
  have hgP : (0:ℝ) ≤ 460 * d ^ 4 + 1720 * d ^ 3 * ζ + 2490 * d ^ 2 * ζ ^ 2
      + 1624 * d * ζ ^ 3 + 400 * ζ ^ 4 := by
    nlinarith [hcube, hdz3, sq_nonneg (d * ζ), sq_nonneg (ζ ^ 2), hd4,
      mul_nonneg (sq_nonneg d) (sq_nonneg ζ)]
  have hgM : (0:ℝ) ≤ 340 * d ^ 4 + 1480 * d ^ 3 * ζ + 2310 * d ^ 2 * ζ ^ 2
      + 1576 * d * ζ ^ 3 + 400 * ζ ^ 4 := by
    nlinarith [hcube, hdz3, sq_nonneg (d * ζ), sq_nonneg (ζ ^ 2), hd4,
      mul_nonneg (sq_nonneg d) (sq_nonneg ζ)]
  rw [hrw, hbnd, abs_div, abs_of_pos hcd, div_le_div_iff_of_pos_right hcd, abs_le]
  -- after clearing denominators, N+B = ζ²·gP and B−N = ζ²·gM, both nonneg
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (sq_nonneg ζ) hgP]
  · nlinarith [mul_nonneg (sq_nonneg ζ) hgM]

/-- **§5 sharp expansion of `F_{a,b}`** (writeup 769). The mixed second difference
`Fab X a b d` agrees with its 4-term Taylor leading part up to `O(X·a|b|(a+|b|)²/d⁶)`,
valid for `b ≠ 0` of either sign. -/
theorem Fab_expand {X a b d : ℝ} (hX : 0 < X) (ha : 0 < a) (hb : b ≠ 0) (hd : 0 < d)
    (hab : 4 * (a + |b|) ≤ d) :
    |Fab X a b d - (6 * a * b * X / d ^ 4 - 12 * a * b * (a + b) * X / d ^ 5)|
      ≤ 400 * X * (a * |b| * (a + |b|) ^ 2) / d ^ 6 := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hbd0 : 4 * |b| ≤ d := by linarith [ha.le]
  have hb_ge : -(d / 4) ≤ b := by
    have := (abs_le.mp (by linarith [abs_nonneg b] : |b| ≤ d / 4)).1; linarith
  have hda : d + a ≠ 0 := by positivity
  have hdb : d + b ≠ 0 := ne_of_gt (by linarith [hb_ge])
  have hdab : d + a + b ≠ 0 := ne_of_gt (by linarith [hb_ge, ha])
  -- ALGEBRAIC IDENTITY: Fab − leading = X·(rem(a+b) − rem a − rem b)
  have hid : Fab X a b d - (6 * a * b * X / d ^ 4 - 12 * a * b * (a + b) * X / d ^ 5)
      = X * (rem d (a + b) - rem d a - rem d b) := by
    simp only [Fab, Ffun, rem]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hX]
  -- the window bound |b| ≤ d/4, as a usable inequality and its two one-sided forms
  have hbd : 4 * |b| ≤ d := by linarith [ha.le]
  have hbpair := abs_le.mp (by linarith [hbd] : |b| ≤ d / 4)
  have hb_hi : b ≤ d / 4 := hbpair.2
  have hb_lo : -(d / 4) ≤ b := hbpair.1
  -- a generic point `s` in `[0,a]` (and `s+b`) keeps `d + ·` away from 0
  have hpt_pos : ∀ s : ℝ, 0 ≤ s → s ≤ a → 0 < d + s := by
    intro s hs0 hsa; nlinarith [hbpos, hbd]
  have hsb_pos : ∀ s : ℝ, 0 ≤ s → s ≤ a → 0 < d + (s + b) := by
    intro s hs0 hsa; nlinarith [hb_lo, ha.le]
  -- DOUBLE MVT: bound |rem(a+b) − rem a − rem b| ≤ a·|b|·400(a+|b|)²/d⁶
  -- φ s := rem(s+b) − rem s.  rem(a+b)−rem a−rem b = φ a − φ 0.
  set φ : ℝ → ℝ := fun s => rem d (s + b) - rem d s with hφ
  set φ' : ℝ → ℝ := fun s => rem1 d (s + b) - rem1 d s with hφ'
  have hφ_hasDeriv : ∀ s, 0 ≤ s → s ≤ a → HasDerivAt φ (φ' s) s := by
    intro s hs0 hsa
    have hsb : d + (s + b) ≠ 0 := ne_of_gt (hsb_pos s hs0 hsa)
    have hsne : d + s ≠ 0 := ne_of_gt (hpt_pos s hs0 hsa)
    have h1 : HasDerivAt (fun t => rem d (t + b)) (rem1 d (s + b)) s := by
      have hshift : HasDerivAt (fun t => t + b) 1 s := (hasDerivAt_id s).add_const b
      have := (rem_hasDerivAt hd0 hsb).comp s hshift
      simpa using this
    have h2 : HasDerivAt (fun t => rem d t) (rem1 d s) s := rem_hasDerivAt hd0 hsne
    exact h1.sub h2
  -- MVT for φ on [0, a]
  have hφc : ContinuousOn φ (Set.Icc 0 a) := by
    intro x hx
    exact (hφ_hasDeriv x hx.1 hx.2).continuousAt.continuousWithinAt
  have hφd : ∀ x ∈ Set.Ioo (0:ℝ) a, HasDerivAt φ (φ' x) x := by
    intro x hx; exact hφ_hasDeriv x (le_of_lt hx.1) (le_of_lt hx.2)
  obtain ⟨η, hη_mem, hη_eq⟩ := exists_hasDerivAt_eq_slope φ φ' ha hφc hφd
  have hη_pos : 0 < η := hη_mem.1
  have hη_lt : η < a := hη_mem.2
  -- slope = (φ a − φ 0)/a, and φ a − φ 0 = rem(a+b)−rem a−rem b
  have hφ0 : φ 0 = rem d b - rem d 0 := by simp [hφ]
  have hφa : φ a = rem d (a + b) - rem d a := by simp [hφ]
  have hdiff_eq : rem d (a + b) - rem d a - rem d b = φ a - φ 0 := by
    rw [hφ0, hφa, rem_zero]; ring
  have hslopeφ : (φ a - φ 0) / (a - 0) = φ' η := hη_eq.symm
  have hφ'η : φ' η = rem1 d (η + b) - rem1 d η := rfl
  have hstep1 : φ a - φ 0 = a * (rem1 d (η + b) - rem1 d η) := by
    have : (φ a - φ 0) / a = rem1 d (η + b) - rem1 d η := by
      rw [← hφ'η, ← hslopeφ]; ring_nf
    field_simp at this ⊢
    linarith [this]
  -- the endpoints `η` and `η+b` lie in `[-|b|, a]`, so `d + ·` stays positive there
  have hη_pt_pos : 0 < d + η := hpt_pos η hη_pos.le hη_lt.le
  have hηb_pt_pos : 0 < d + (η + b) := hsb_pos η hη_pos.le hη_lt.le
  -- inner MVT for rem1 between `η` and `η+b` (orientation depends on sign of `b`):
  -- ∃ ζ between them with rem1(η+b) − rem1 η = b · rem2 ζ and |ζ| ≤ a + |b|.
  set ψ : ℝ → ℝ := fun s => rem1 d s with hψ
  have hstep2 : ∃ ζ : ℝ, |ζ| ≤ a + |b| ∧ rem1 d (η + b) - rem1 d η = b * rem2 d ζ := by
    rcases lt_trichotomy b 0 with hbneg | hbz | hbpos'
    · -- b < 0: interval [η+b, η]
      have hlt : η + b < η := by linarith
      -- on [η+b, η] all points x satisfy d + x > 0 and continuity/derivative
      have hψc : ContinuousOn ψ (Set.Icc (η + b) η) := by
        intro x hx
        have hxpos : 0 < d + x := by
          have hx1 : η + b ≤ x := hx.1
          have hx2 : x ≤ η := hx.2
          nlinarith [hηb_pt_pos, hη_pt_pos]
        exact (rem1_hasDerivAt hd0 (ne_of_gt hxpos)).continuousAt.continuousWithinAt
      have hψd : ∀ x ∈ Set.Ioo (η + b) η, HasDerivAt ψ (rem2 d x) x := by
        intro x hx
        have hxpos : 0 < d + x := by
          have hx1 : η + b < x := hx.1
          have hx2 : x < η := hx.2
          nlinarith [hηb_pt_pos, hη_pt_pos]
        exact rem1_hasDerivAt hd0 (ne_of_gt hxpos)
      obtain ⟨ζ, hζ_mem, hζ_eq⟩ :=
        exists_hasDerivAt_eq_slope ψ (fun s => rem2 d s) hlt hψc hψd
      have hζ_lo : η + b < ζ := hζ_mem.1
      have hζ_hi : ζ < η := hζ_mem.2
      have hζ_ub : |ζ| ≤ a + |b| := by
        rw [abs_le]; rw [abs_of_neg hbneg] at *
        constructor <;> nlinarith [hη_pos, hη_lt]
      refine ⟨ζ, hζ_ub, ?_⟩
      have hslopeψ : (ψ η - ψ (η + b)) / (η - (η + b)) = rem2 d ζ := hζ_eq.symm
      have hψeval : ψ η - ψ (η + b) = rem1 d η - rem1 d (η + b) := rfl
      have hden : η - (η + b) = -b := by ring
      rw [hden, hψeval] at hslopeψ
      have hbne0 : (-b) ≠ 0 := by linarith
      field_simp at hslopeψ ⊢
      linarith [hslopeψ]
    · exact absurd hbz hb
    · -- b > 0: interval [η, η+b]
      have hlt : η < η + b := by linarith
      have hψc : ContinuousOn ψ (Set.Icc η (η + b)) := by
        intro x hx
        have hxpos : 0 < d + x := by
          have hx1 : η ≤ x := hx.1
          have hx2 : x ≤ η + b := hx.2
          nlinarith [hηb_pt_pos, hη_pt_pos]
        exact (rem1_hasDerivAt hd0 (ne_of_gt hxpos)).continuousAt.continuousWithinAt
      have hψd : ∀ x ∈ Set.Ioo η (η + b), HasDerivAt ψ (rem2 d x) x := by
        intro x hx
        have hxpos : 0 < d + x := by
          have hx1 : η < x := hx.1
          have hx2 : x < η + b := hx.2
          nlinarith [hηb_pt_pos, hη_pt_pos]
        exact rem1_hasDerivAt hd0 (ne_of_gt hxpos)
      obtain ⟨ζ, hζ_mem, hζ_eq⟩ :=
        exists_hasDerivAt_eq_slope ψ (fun s => rem2 d s) hlt hψc hψd
      have hζ_lo : η < ζ := hζ_mem.1
      have hζ_hi : ζ < η + b := hζ_mem.2
      have hζ_ub : |ζ| ≤ a + |b| := by
        rw [abs_le]; rw [abs_of_pos hbpos'] at *
        constructor <;> nlinarith [hη_pos, hη_lt]
      refine ⟨ζ, hζ_ub, ?_⟩
      have hslopeψ : (ψ (η + b) - ψ η) / ((η + b) - η) = rem2 d ζ := hζ_eq.symm
      have hψeval : ψ (η + b) - ψ η = rem1 d (η + b) - rem1 d η := rfl
      have hden : (η + b) - η = b := by ring
      rw [hden, hψeval] at hslopeψ
      field_simp at hslopeψ ⊢
      linarith [hslopeψ]
  obtain ⟨ζ, hζ_ub, hstep2⟩ := hstep2
  have hfinal : rem d (a + b) - rem d a - rem d b = a * b * rem2 d ζ := by
    rw [hdiff_eq, hstep1, hstep2]; ring
  rw [hfinal]
  -- BOUND |rem2 ζ| ≤ 400 (a+|b|)² / d⁶  via the two-sided rem2 bound
  have hζd : 4 * |ζ| ≤ d := by
    have : a + |b| ≤ d / 4 := by linarith [hab]
    linarith [hζ_ub, abs_nonneg b, ha.le]
  have hrem2_bound : |rem2 d ζ| ≤ 400 * ζ ^ 2 / d ^ 6 := rem2_abs_bound hd hζd
  have hζab2 : ζ ^ 2 ≤ (a + |b|) ^ 2 := by
    have h1 : |ζ| ≤ a + |b| := hζ_ub
    have h2 : (0:ℝ) ≤ a + |b| := by positivity
    calc ζ ^ 2 = |ζ| ^ 2 := (sq_abs ζ).symm
      _ ≤ (a + |b|) ^ 2 := by gcongr
  have hrem2_bound2 : |rem2 d ζ| ≤ 400 * (a + |b|) ^ 2 / d ^ 6 := by
    refine le_trans hrem2_bound ?_
    have hd6 : (0:ℝ) < d ^ 6 := by positivity
    gcongr
  -- final: |a·b·rem2 ζ| = a·|b|·|rem2 ζ| ≤ a·|b|·400(a+|b|)²/d⁶
  rw [abs_mul, abs_mul, abs_of_pos ha]
  have hfinbound : a * |b| * |rem2 d ζ| ≤ 400 * (a * |b| * (a + |b|) ^ 2) / d ^ 6 := by
    have hab_nonneg : 0 ≤ a * |b| := by positivity
    calc a * |b| * |rem2 d ζ|
        ≤ a * |b| * (400 * (a + |b|) ^ 2 / d ^ 6) :=
          mul_le_mul_of_nonneg_left hrem2_bound2 hab_nonneg
      _ = 400 * (a * |b| * (a + |b|) ^ 2) / d ^ 6 := by ring
  calc X * (a * |b| * |rem2 d ζ|)
      ≤ X * (400 * (a * |b| * (a + |b|) ^ 2) / d ^ 6) :=
        mul_le_mul_of_nonneg_left hfinbound hX.le
    _ = 400 * X * (a * |b| * (a + |b|) ^ 2) / d ^ 6 := by ring

/-- **§5 `𝒬` expansion at `v = 0`** (writeup 819–822). The combination
`ℓ₁·F_{a,ℓ₂b₀}(d) − ℓ₂·F_{a,ℓ₁b₀}(d)` has its leading `6ab₀X/d⁴` terms cancel; the surviving
`d⁵` term equals `−φ_d = −12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xab₀²/d⁵`, up to the combined remainder. -/
theorem Q_v0_expand {X a b₀ d ℓ₁ ℓ₂ : ℝ} (hX : 0 < X) (ha : 0 < a) (hb₀ : b₀ ≠ 0)
    (hd : 0 < d) (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hwin : 4 * (a + ℓ₂ * |b₀|) ≤ d) :
    |(ℓ₁ * Fab X a (ℓ₂ * b₀) d - ℓ₂ * Fab X a (ℓ₁ * b₀) d)
       - (-12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * b₀ ^ 2 / d ^ 5)|
      ≤ 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * ((a + ℓ₂ * |b₀|) ^ 2 + (a + ℓ₁ * |b₀|) ^ 2) / d ^ 6 := by
  have hℓ2 : 0 < ℓ₂ := lt_trans hℓ1 hℓ12
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hb₀pos : 0 < |b₀| := abs_pos.mpr hb₀
  have hℓ1b₀ : ℓ₁ * b₀ ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hℓ1) hb₀
  have hℓ2b₀ : ℓ₂ * b₀ ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hℓ2) hb₀
  -- |ℓ·b₀| = ℓ·|b₀| for the positive scalars ℓ₁, ℓ₂
  have habs2 : |ℓ₂ * b₀| = ℓ₂ * |b₀| := by rw [abs_mul, abs_of_pos hℓ2]
  have habs1 : |ℓ₁ * b₀| = ℓ₁ * |b₀| := by rw [abs_mul, abs_of_pos hℓ1]
  -- window for the `ℓ₂` term: `4*(a + |ℓ₂ b₀|) = 4*(a + ℓ₂|b₀|) ≤ d` is `hwin`
  have hwin2 : 4 * (a + |ℓ₂ * b₀|) ≤ d := by rw [habs2]; exact hwin
  -- window for the `ℓ₁` term follows from `ℓ₁|b₀| ≤ ℓ₂|b₀|`
  have hwin1 : 4 * (a + |ℓ₁ * b₀|) ≤ d := by
    rw [habs1]
    have hle : ℓ₁ * |b₀| ≤ ℓ₂ * |b₀| := by nlinarith [hℓ12, hb₀pos]
    nlinarith [hwin, hle]
  -- the two `Fab_expand` estimates
  have hE2 := Fab_expand hX ha hℓ2b₀ hd hwin2
  have hE1 := Fab_expand hX ha hℓ1b₀ hd hwin1
  rw [habs2] at hE2
  rw [habs1] at hE1
  -- abbreviations for the two leading parts
  set L₂ : ℝ := 6 * a * (ℓ₂ * b₀) * X / d ^ 4 - 12 * a * (ℓ₂ * b₀) * (a + ℓ₂ * b₀) * X / d ^ 5
    with hL₂
  set L₁ : ℝ := 6 * a * (ℓ₁ * b₀) * X / d ^ 4 - 12 * a * (ℓ₁ * b₀) * (a + ℓ₁ * b₀) * X / d ^ 5
    with hL₁
  set F₂ : ℝ := Fab X a (ℓ₂ * b₀) d with hF₂
  set F₁ : ℝ := Fab X a (ℓ₁ * b₀) d with hF₁
  -- rewrite the goal LHS as `ℓ₁·(F₂ − L₂) − ℓ₂·(F₁ − L₁)`
  have heq : (ℓ₁ * F₂ - ℓ₂ * F₁) - (-12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * b₀ ^ 2 / d ^ 5)
      = ℓ₁ * (F₂ - L₂) - ℓ₂ * (F₁ - L₁) := by
    rw [hL₂, hL₁]; field_simp; ring
  rw [heq]
  -- triangle inequality
  have htri : |ℓ₁ * (F₂ - L₂) - ℓ₂ * (F₁ - L₁)|
      ≤ ℓ₁ * |F₂ - L₂| + ℓ₂ * |F₁ - L₁| := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos hℓ1, abs_of_pos hℓ2]
  refine le_trans htri ?_
  -- bound each piece by its `Fab_expand` estimate (now with |ℓ·b₀| = ℓ·|b₀|)
  have hb2 : ℓ₁ * |F₂ - L₂|
      ≤ 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * (a + ℓ₂ * |b₀|) ^ 2 / d ^ 6 := by
    calc ℓ₁ * |F₂ - L₂|
        ≤ ℓ₁ * (400 * X * (a * (ℓ₂ * |b₀|) * (a + ℓ₂ * |b₀|) ^ 2) / d ^ 6) :=
          mul_le_mul_of_nonneg_left hE2 hℓ1.le
      _ = 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * (a + ℓ₂ * |b₀|) ^ 2 / d ^ 6 := by ring
  have hb1 : ℓ₂ * |F₁ - L₁|
      ≤ 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := by
    calc ℓ₂ * |F₁ - L₁|
        ≤ ℓ₂ * (400 * X * (a * (ℓ₁ * |b₀|) * (a + ℓ₁ * |b₀|) ^ 2) / d ^ 6) :=
          mul_le_mul_of_nonneg_left hE1 hℓ2.le
      _ = 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := by ring
  calc ℓ₁ * |F₂ - L₂| + ℓ₂ * |F₁ - L₁|
      ≤ 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * (a + ℓ₂ * |b₀|) ^ 2 / d ^ 6
        + 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * (a + ℓ₁ * |b₀|) ^ 2 / d ^ 6 := add_le_add hb2 hb1
    _ = 400 * X * a * |b₀| * ℓ₁ * ℓ₂ * ((a + ℓ₂ * |b₀|) ^ 2 + (a + ℓ₁ * |b₀|) ^ 2) / d ^ 6 := by
        ring
