import Squarefree.Geometry.NearCurveProof
import Squarefree.Geometry.NearCurveSpacing
import Squarefree.Geometry.NearCurveTypeI
import Squarefree.Geometry.NearCurveTypeIClass
import Squarefree.Geometry.NearCurvePacking
import Squarefree.Geometry.NearCurveGreedy
import Squarefree.Geometry.NearCurveStrip
import Squarefree.Geometry.NearCurveTypeII
import Mathlib

/-!
# §4.3 residual span bound, Type I/II stubs, and `prop43_local`

The residual count of `../explicit_writeup.md` (lines 568–578) and the assembly of
the λ-normalized Prop 4.3 core `prop43_local` (line 482) from the concrete
partitions `#nearSet = #residual + #major`, `#major = #typeI + #typeII`.

The two genuine analytic estimates (Type I total ≪ Nδ+1, writeup 605; Type II
total ≪ Nδ + √(δ/λ)·log + 1, writeup 665) remain as CONCRETE named stubs.
The rational-line reconstruction `collinear_five_on_majorLine` is now proved.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

/-! ## Residual span bound (writeup 568–578)

The span lower bound `dspan = min((1/(4λ))^{1/3}, 1/(4δ))`.  Any five residual
points span at least this, via the trichotomy: a non-collinear triple gives the
spacing bound `1 ≤ 2λL³ + 2δL`; all-collinear on a large-denominator line are
`q`-separated; all-collinear on a small-denominator line force an `OnMajorArc`
witness, contradicting residual membership. -/

/-- The residual span scale `min((1/(512λ))^{1/3}, 1/(64δ))`.  The cube-root term is
keyed to the curvature-256 spacing `1 ≤ 256λL³ + 2δL` (so `256λ·(1/(512λ)) = 1/2`); the
`δ`-floor matches the (lowered) Type I denominator cutoff `denomCutoff = 1/64`. -/
noncomputable def dspan (lam δ : ℝ) : ℝ := min ((1 / (512 * lam)) ^ (1/3 : ℝ)) (1 / (64 * δ))

theorem dspan_pos {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) : 0 < dspan lam δ := by
  rw [dspan, lt_min_iff]
  refine ⟨Real.rpow_pos_of_pos (by positivity) _, by positivity⟩

/-- **Non-collinear triple span** (writeup 489–514).  For near-set points
`a < b < c` in `[N/2, 5N/2]` with non-collinear lattice points, the span
`(c − a)` is at least `dspan`.  Proof: `noncollinear_span_lower` gives
`1 ≤ 2λ(c−a)³ + 2δ(c−a)`, so at least one of the two terms is `≥ 1/2`. -/
theorem noncollinear_triple_span {f : ℝ → ℝ} {N lam δ : ℝ} {a b c : ℤ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hf : ContDiff ℝ 2 f)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    (hsub : Set.Icc ((a : ℝ)) ((c : ℝ)) ⊆ Set.Icc (N / 2) (5 * N / 2))
    (hab : a < b) (hbc : b < c)
    (hda : |f (a : ℝ) - (latticeY f a : ℝ)| ≤ δ)
    (hdb : |f (b : ℝ) - (latticeY f b : ℝ)| ≤ δ)
    (hdc : |f (c : ℝ) - (latticeY f c : ℝ)| ≤ δ)
    (hncol : collinearDet f a b c ≠ 0) :
    dspan lam δ ≤ (c : ℝ) - (a : ℝ) := by
  -- Apply the proven engine.
  have hfon : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) (c : ℝ)) := hf.contDiffOn
  have hf2 : ∀ x ∈ Set.Icc (a : ℝ) (c : ℝ), |iteratedDeriv 2 f x| ≤ 256 * lam :=
    fun x hx => hupper x (hsub hx)
  -- `collinearDet = ℓ_a(c-b) + ℓ_b(a-c) + ℓ_c(b-a)` is the `hncol` numerator.
  have hncol' : latticeY f a * (c - b) + latticeY f b * (a - c)
      + latticeY f c * (b - a) ≠ 0 := hncol
  have hspan := noncollinear_span_lower (Λ := 256 * lam) (δ := δ)
    hδ.le hab hbc hfon hf2 hda hdb hdc hncol'
  -- `1 ≤ 2λ L³ + 2δ L`, with `L = c - a`.
  set L : ℝ := (c : ℝ) - (a : ℝ) with hLdef
  have hacR : (a : ℝ) < (c : ℝ) := by exact_mod_cast (hab.trans hbc)
  have hLpos : 0 < L := by rw [hLdef]; linarith
  -- so `2λ L³ ≥ 1/2`  or  `2δ L ≥ 1/2`.
  by_contra hcon
  push Not at hcon
  -- `L < dspan`, hence `L < (1/(512λ))^{1/3}` and `L < 1/(64δ)`.
  have h1 : L < (1 / (512 * lam)) ^ (1/3 : ℝ) := lt_of_lt_of_le hcon (min_le_left _ _)
  have h2 : L < 1 / (64 * δ) := lt_of_lt_of_le hcon (min_le_right _ _)
  -- bound each term.
  have ht2 : 2 * δ * L < 1 / 2 := by
    have hstep : δ * L < δ * (1 / (64 * δ)) := mul_lt_mul_of_pos_left h2 hδ
    have hδ4 : δ * (1 / (64 * δ)) = 1 / 64 := by field_simp
    rw [hδ4] at hstep; linarith
  have ht1 : 256 * lam * L ^ 3 < 1 / 2 := by
    -- L < (1/(512λ))^{1/3} ⟹ L³ < 1/(512λ) ⟹ 256λ L³ < 1/2.
    have hbase : (0 : ℝ) < 1 / (512 * lam) := by positivity
    have hpow : ((1 / (512 * lam)) ^ (1/3 : ℝ)) ^ (3 : ℕ) = 1 / (512 * lam) := by
      rw [← Real.rpow_natCast ((1 / (512 * lam)) ^ (1/3 : ℝ)) 3,
        ← Real.rpow_mul hbase.le]
      norm_num
    have hLcube : L ^ 3 < 1 / (512 * lam) := by
      calc L ^ 3 < ((1 / (512 * lam)) ^ (1/3 : ℝ)) ^ 3 := by
            apply pow_lt_pow_left₀ h1 hLpos.le (by norm_num)
        _ = 1 / (512 * lam) := hpow
    have hstep : 256 * lam * L ^ 3 < 256 * lam * (1 / (512 * lam)) :=
      mul_lt_mul_of_pos_left hLcube (by positivity)
    have h4l : 256 * lam * (1 / (512 * lam)) = 1 / 2 := by field_simp; ring
    rw [h4l] at hstep
    exact hstep
  linarith [hspan, ht1, ht2]

/-- **Rational-line reconstruction.**  Five sorted near-set points whose lattice
points are collinear (each `collinearDet f n₀ n₁ nᵢ = 0`) lie on a common rational
`MajorLine D` (`OnLine f D nᵢ` for every `i`).  Construct `D.slope =
(ℓ_{n₁}−ℓ_{n₀})/(n₁−n₀)` reduced (gcd factor `c`); collinearity through the first
two points forces all five onto the cleared-denominator line. -/
theorem collinear_five_on_majorLine {f : ℝ → ℝ} {n₀ n₁ n₂ n₃ n₄ : ℤ}
    (h01 : n₀ < n₁) (h12 : n₁ < n₂) (h23 : n₂ < n₃) (h34 : n₃ < n₄)
    (hc012 : collinearDet f n₀ n₁ n₂ = 0)
    (hc013 : collinearDet f n₀ n₁ n₃ = 0)
    (hc014 : collinearDet f n₀ n₁ n₄ = 0) :
    ∃ D : MajorLine, OnLine f D n₀ ∧ OnLine f D n₁ ∧ OnLine f D n₂
      ∧ OnLine f D n₃ ∧ OnLine f D n₄ := by
  -- Reconstruct the supporting rational line from the first two points.
  set ℓ : ℤ → ℤ := latticeY f with hℓ
  set s : ℚ := Rat.divInt (ℓ n₁ - ℓ n₀) (n₁ - n₀) with hs
  have hd0 : (n₁ - n₀ : ℤ) ≠ 0 := by omega
  -- gcd factor `c`: `ℓ₁-ℓ₀ = c·s.num`, `n₁-n₀ = c·s.den`.
  obtain ⟨c, hcnum, hcden⟩ := Rat.num_den_mk hd0 hs
  have hcne : c ≠ 0 := by
    intro h; apply hd0; rw [hcden, h]; ring
  set D : MajorLine := ⟨s, (s.den : ℤ) * ℓ n₀ - s.num * n₀⟩ with hD
  -- `OnLine` from the cleared slope equation `s.den·(ℓ_n−ℓ₀) = s.num·(n−n₀)`.
  have onLine_of : ∀ n : ℤ,
      (s.den : ℤ) * (ℓ n - ℓ n₀) = s.num * (n - n₀) → OnLine f D n := by
    intro n hn
    show (D.denom) * ℓ n = D.slope.num * n + D.shift
    simp only [hD, MajorLine.denom]
    linarith [hn]
  -- Collinearity `⟹` the cleared equation, by cancelling the gcd factor `c`.
  have clear_of : ∀ n : ℤ,
      (n₁ - n₀) * (ℓ n - ℓ n₀) = (ℓ n₁ - ℓ n₀) * (n - n₀)
      → (s.den : ℤ) * (ℓ n - ℓ n₀) = s.num * (n - n₀) := by
    intro n hcol
    have e1 : c * (s.den : ℤ) = n₁ - n₀ := by rw [hcden]
    have e2 : c * s.num = ℓ n₁ - ℓ n₀ := by rw [hcnum]
    have hmul : c * ((s.den : ℤ) * (ℓ n - ℓ n₀)) = c * (s.num * (n - n₀)) := by
      calc c * ((s.den : ℤ) * (ℓ n - ℓ n₀))
          = (n₁ - n₀) * (ℓ n - ℓ n₀) := by rw [← e1]; ring
        _ = (ℓ n₁ - ℓ n₀) * (n - n₀) := hcol
        _ = c * (s.num * (n - n₀)) := by rw [← e2]; ring
    exact mul_left_cancel₀ hcne hmul
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · exact onLine_of n₀ (by ring)
  · exact onLine_of n₁ (clear_of n₁ (by ring))
  · refine onLine_of n₂ (clear_of n₂ ?_)
    have := hc012; simp only [collinearDet, ← hℓ] at this; linarith [this]
  · refine onLine_of n₃ (clear_of n₃ ?_)
    have := hc013; simp only [collinearDet, ← hℓ] at this; linarith [this]
  · refine onLine_of n₄ (clear_of n₄ ?_)
    have := hc014; simp only [collinearDet, ← hℓ] at this; linarith [this]

/-- **Residual five-span** (writeup 568–576).  Any five distinct residual points
span at least `dspan`.  Trichotomy: a non-collinear triple gives the spacing
bound; all-collinear on a large-denominator line are `q`-separated; all-collinear
on a small-denominator line force an `OnMajorArc` witness, contradiction. -/
theorem residual_five_span {f : ℝ → ℝ} {N lam δ : ℝ}
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ < 1) (hf : ContDiff ℝ 2 f)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    {t : Finset ℤ} (htsub : t ⊆ residualSet f N δ) (htcard : t.card = 5) :
    ∃ x ∈ t, ∃ y ∈ t, dspan lam δ ≤ (y : ℝ) - (x : ℝ) := by
  classical
  obtain ⟨n₀, n₁, n₂, n₃, n₄, hn0t, hn1t, hn2t, hn3t, hn4t, h01, h12, h23, h34⟩ :=
    exists_five_sorted htcard
  -- All five are residual, hence near-set points.
  have hres : ∀ {n}, n ∈ t → n ∈ residualSet f N δ := fun hn => htsub hn
  have hnear : ∀ {n}, n ∈ t → n ∈ nearSet f N δ := fun hn => (mem_residualSet.mp (htsub hn)).1
  -- Refine to `x = n₀`, `y = n₄`: the full span dominates.
  refine ⟨n₀, hn0t, n₄, hn4t, ?_⟩
  -- Domain inclusion: `Icc (n₀:ℝ)(n₄:ℝ) ⊆ Icc (N/2)(5N/2)`.
  have hNpos : (0 : ℝ) < N := by linarith
  have hflo_lo : ∀ {n}, n ∈ nearSet f N δ → N / 2 ≤ (n : ℝ) := by
    intro n hn
    have h1 := (mem_nearSet.mp hn).1.1
    have h2 : (⌊N⌋ : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h3 : N - 1 < (⌊N⌋ : ℝ) := by have := Int.sub_one_lt_floor N; linarith
    linarith
  have hflo_hi : ∀ {n}, n ∈ nearSet f N δ → (n : ℝ) ≤ 5 * N / 2 := by
    intro n hn
    have h1 := (mem_nearSet.mp hn).1.2
    have h2 : (n : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by exact_mod_cast h1
    have h3 : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
    linarith
  have hsub04 : Set.Icc ((n₀ : ℝ)) ((n₄ : ℝ)) ⊆ Set.Icc (N / 2) (5 * N / 2) := by
    intro x hx
    exact ⟨le_trans (hflo_lo (hnear hn0t)) hx.1, le_trans hx.2 (hflo_hi (hnear hn4t))⟩
  -- δ-closeness of all five.
  have hd : ∀ {n}, n ∈ t → |f (n : ℝ) - (latticeY f n : ℝ)| ≤ δ :=
    fun hn => nearSet_dist_le (hnear hn)
  -- TRICHOTOMY.
  by_cases hcol : collinearDet f n₀ n₁ n₂ = 0 ∧ collinearDet f n₀ n₁ n₃ = 0
      ∧ collinearDet f n₀ n₁ n₄ = 0
  · -- All collinear: get a common MajorLine.
    obtain ⟨hc012, hc013, hc014⟩ := hcol
    obtain ⟨D, hD0, hD1, hD2, hD3, hD4⟩ :=
      collinear_five_on_majorLine h01 h12 h23 h34 hc012 hc013 hc014
    -- denominator dichotomy: q > c/δ  or  q ≤ c/δ.
    by_cases hq : (D.denom : ℝ) ≤ denomCutoff / δ
    · -- Small denominator: middle point `n₂` is OnMajorArc, contradicting residual.
      exfalso
      have hn2res : ¬ OnMajorArc f N δ n₂ := (mem_residualSet.mp (hres hn2t)).2
      apply hn2res
      exact ⟨D, n₀, n₄, hnear hn0t, hnear hn4t, hnear hn2t,
        h01.trans (h12), h23.trans h34, hD0, hD2, hD4, hq⟩
    · -- Large denominator: the points are `q`-separated, so span `≥ q ≥ ... ≥ 1/(4δ)`.
      push Not at hq
      -- `D.denom ∣ (n₄ − n₀)` (both on line; needs `gcd(num,den)=1`).
      have hdvd : D.denom ∣ (n₄ - n₀) := by
        have hcop : IsCoprime (D.slope.num) (D.denom) := by
          have := D.slope.reduced
          rw [Int.isCoprime_iff_gcd_eq_one]
          simpa [MajorLine.denom, Int.gcd] using this
        have hd1 := OnLine.sub_dvd hD4 hD0
        exact (IsCoprime.dvd_of_dvd_mul_left hcop.symm hd1)
      have hpos : 0 < n₄ - n₀ := by omega
      have hqle : D.denom ≤ n₄ - n₀ := Int.le_of_dvd hpos hdvd
      have hqleR : (D.denom : ℝ) ≤ (n₄ : ℝ) - (n₀ : ℝ) := by
        have : ((D.denom : ℤ) : ℝ) ≤ ((n₄ - n₀ : ℤ) : ℝ) := by exact_mod_cast hqle
        push_cast at this; linarith
      -- `1/(64δ) < q ≤ n₄ - n₀`, and `dspan ≤ 1/(64δ)`.
      have hcut : denomCutoff / δ = (1 / 64) / δ := by rw [denomCutoff]
      have hsmall : (1 : ℝ) / (64 * δ) ≤ (D.denom : ℝ) := by
        rw [hcut] at hq
        have hdd : (1 / 64 : ℝ) / δ = 1 / (64 * δ) := by rw [div_div]
        rw [hdd] at hq; linarith
      calc dspan lam δ ≤ 1 / (64 * δ) := min_le_right _ _
        _ ≤ (D.denom : ℝ) := hsmall
        _ ≤ (n₄ : ℝ) - (n₀ : ℝ) := hqleR
  · -- Some triple is non-collinear; pick it and apply the span bound.
    push Not at hcol
    have hexists : collinearDet f n₀ n₁ n₂ ≠ 0 ∨ collinearDet f n₀ n₁ n₃ ≠ 0
        ∨ collinearDet f n₀ n₁ n₄ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact absurd hall.2.2 (hcol hall.1 hall.2.1)
    rcases hexists with hne | hne | hne
    · -- non-collinear triple n₀ n₁ n₂, span n₂ - n₀ ≤ n₄ - n₀.
      have := noncollinear_triple_span hlam hδ hf hupper
        (Set.Icc_subset_Icc le_rfl (by exact_mod_cast (h23.trans h34).le) |>.trans hsub04)
        h01 h12 (hd hn0t) (hd hn1t) (hd hn2t) hne
      have hmono : (n₂ : ℝ) - (n₀ : ℝ) ≤ (n₄ : ℝ) - (n₀ : ℝ) := by
        have : (n₂ : ℝ) ≤ (n₄ : ℝ) := by exact_mod_cast (h23.trans h34).le
        linarith
      linarith [this]
    · have := noncollinear_triple_span hlam hδ hf hupper
        (Set.Icc_subset_Icc le_rfl (by exact_mod_cast h34.le) |>.trans hsub04)
        h01 (h12.trans h23) (hd hn0t) (hd hn1t) (hd hn3t) hne
      have hmono : (n₃ : ℝ) - (n₀ : ℝ) ≤ (n₄ : ℝ) - (n₀ : ℝ) := by
        have : (n₃ : ℝ) ≤ (n₄ : ℝ) := by exact_mod_cast h34.le
        linarith
      linarith [this]
    · have := noncollinear_triple_span hlam hδ hf hupper hsub04
        h01 (h12.trans (h23.trans h34)) (hd hn0t) (hd hn1t) (hd hn4t) hne
      linarith [this]

/-- **Residual card bound** (writeup 578): `#residualSet ≤ 512·(N·λ^{1/3} + N·δ + 1)`.
Uses `card_le_of_five_span` with `d = dspan` (every five residual points span
`≥ dspan`), then bounds `1/dspan ≤ (512λ)^{1/3} + 64δ = 8λ^{1/3} + 64δ` and the interval
length by `N+1`.  The cube-root scale `512 = 8³` comes from the curvature-256 spacing;
the `64`-coefficient on `δ` from the lowered `δ`-floor `1/(64δ)`; the public constant
remains `512` (the grown `8λ^{1/3}` term is still absorbed). -/
theorem residual_card_bound {f : ℝ → ℝ} {N lam δ : ℝ}
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ < 1) (hf : ContDiff ℝ 2 f)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    ((residualSet f N δ).card : ℝ) ≤ 512 * (N * lam ^ (1/3 : ℝ) + N * δ + 1) := by
  have hdpos : 0 < dspan lam δ := dspan_pos hlam hδ
  -- membership in `[⌊N⌋, ⌊2N⌋]`.
  have hmem : ∀ n ∈ residualSet f N δ,
      ((⌊N⌋ : ℤ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ ((⌊2 * N⌋ : ℤ) : ℝ) := by
    intro n hn
    have h := (mem_nearSet.mp (mem_residualSet.mp hn).1).1
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hlohi : ((⌊N⌋ : ℤ) : ℝ) ≤ ((⌊2 * N⌋ : ℤ) : ℝ) := by
    have : (⌊N⌋ : ℤ) ≤ ⌊2 * N⌋ := by
      apply Int.floor_le_floor; linarith
    exact_mod_cast this
  -- five-span hypothesis.
  have hspan := card_le_of_five_span (S := residualSet f N δ) hdpos hlohi hmem
    (fun t ht htc => residual_five_span hN2 hlam hδ hδ1 hf hupper ht htc)
  -- bound `(⌊2N⌋ - ⌊N⌋ : ℝ) ≤ N + 1`.
  have hlen : ((⌊2 * N⌋ : ℤ) : ℝ) - ((⌊N⌋ : ℤ) : ℝ) ≤ N + 1 := by
    have ha : ((⌊2 * N⌋ : ℤ) : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
    have hb : N - 1 < ((⌊N⌋ : ℤ) : ℝ) := by have := Int.sub_one_lt_floor N; linarith
    linarith
  -- `1/A = (512λ)^{1/3}` and `1/B = 64δ`.
  have hApos : 0 < (1 / (512 * lam)) ^ (1/3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hBpos : 0 < (1 / (64 * δ)) := by positivity
  have hinvA : 1 / ((1 / (512 * lam)) ^ (1/3 : ℝ)) = (512 * lam) ^ (1/3 : ℝ) := by
    have hcast : (1 / (512 * lam) : ℝ) ^ (1/3 : ℝ) = (512 * lam) ^ (-(1/3) : ℝ) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hcast, Real.rpow_neg (by positivity), one_div, inv_inv]
  have hinvB : 1 / (1 / (64 * δ)) = 64 * δ := by
    rw [one_div_one_div]
  -- bound `1/dspan ≤ (512λ)^{1/3} + 64δ`.
  have hinv : 1 / dspan lam δ ≤ (512 * lam) ^ (1/3 : ℝ) + 64 * δ := by
    rw [dspan]
    rcases min_cases ((1 / (512 * lam)) ^ (1/3 : ℝ)) (1 / (64 * δ)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, hinvA]
      have : 0 ≤ 64 * δ := by positivity
      linarith
    · rw [he, hinvB]
      have : 0 ≤ (512 * lam) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
      linarith
  -- assemble.
  have hlen0 : (0 : ℝ) ≤ ((⌊2 * N⌋ : ℤ) : ℝ) - ((⌊N⌋ : ℤ) : ℝ) := by linarith [hlohi]
  have hdiv_le : (((⌊2 * N⌋ : ℤ) : ℝ) - ((⌊N⌋ : ℤ) : ℝ)) / dspan lam δ
      ≤ (N + 1) * ((512 * lam) ^ (1/3 : ℝ) + 64 * δ) := by
    rw [div_eq_mul_one_div]
    apply mul_le_mul hlen hinv (le_of_lt (by positivity)) (by positivity)
  -- final numeric chase.
  have hNpos : (0 : ℝ) < N := by linarith
  have hl13 : (0 : ℝ) ≤ lam ^ (1/3 : ℝ) := Real.rpow_nonneg hlam.le _
  have h4l13 : (512 * lam) ^ (1/3 : ℝ) = 512 ^ (1/3 : ℝ) * lam ^ (1/3 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hlam.le]
  have h4cube : (512 : ℝ) ^ (1/3 : ℝ) ≤ 8 := by
    rw [show (8 : ℝ) = (512 : ℝ) ^ (1/3 : ℝ) by
      rw [show (512 : ℝ) = 8 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast 8 3,
        ← Real.rpow_mul (by norm_num)]; norm_num]
  calc ((residualSet f N δ).card : ℝ)
      ≤ 4 * ((((⌊2 * N⌋ : ℤ) : ℝ) - ((⌊N⌋ : ℤ) : ℝ)) / dspan lam δ + 1) := hspan
    _ ≤ 4 * ((N + 1) * ((512 * lam) ^ (1/3 : ℝ) + 64 * δ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hdiv_le]
    _ = 4 * ((N + 1) * (512 ^ (1/3:ℝ) * lam ^ (1/3:ℝ) + 64 * δ) + 1) := by rw [h4l13]
    _ ≤ 512 * (N * lam ^ (1/3 : ℝ) + N * δ + 1) := by
        have hN1 : (1 : ℝ) ≤ N := by linarith
        have hLL : (512 : ℝ) ^ (1/3:ℝ) * lam ^ (1/3:ℝ) ≤ 8 * lam ^ (1/3:ℝ) :=
          mul_le_mul_of_nonneg_right h4cube hl13
        have hLN : lam ^ (1/3:ℝ) ≤ N * lam ^ (1/3:ℝ) := by nlinarith [hl13, hN1]
        have hδN : δ ≤ N * δ := by nlinarith [hδ.le, hN1]
        nlinarith [hLL, hLN, hδN, hl13, hδ.le, hNpos.le,
          mul_nonneg hl13 hNpos.le, mul_nonneg hδ.le hNpos.le]

/-! ## Type I / Type II card bounds (writeup 581–666) — concrete stubs

These are the two remaining genuine analytic estimates: the Type I proper-arc
total (`≪ Nδ + 1`, writeup 605) and the Type II proper-arc total
(`≪ Nδ + √(δ/λ)·log(2+√(δ/λ)) + 1`, writeup 665).  Stated concretely on the
`typeISet` / `typeIISet` filters. -/

/-- **Type I total (writeup 581–605), FULLY PROVEN**: `#typeISet ≤ 384·(N·δ + 1)`.

The greedy packing (`typeI_arc_sum`) handles `δ < 1/2` (the writeup's "`c₁` sufficiently
small" regime, where the re-anchored distinct-line gap `repArc g + d(A_g)/48 ≤ repArc g'`
holds).  For `δ ≥ 1/2` the bound is trivial: `typeISet ⊆ nearSet ⊆ Finset.Icc ⌊N⌋ ⌊2N⌋`, so
`#typeISet ≤ N + 2 ≤ 2Nδ + 2 ≤ 384(Nδ+1)`.  The constant `384` carries slack absorbing the
line-indexed proper-arc factor 2 (writeup 532), the factor-2 per-arc count, and the
`/48`-window's doubling of the `/24`-gap constant. -/
theorem typeI_card_bound {f : ℝ → ℝ} {N lam δ : ℝ}
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ < 1) (hf : ContDiff ℝ 2 f)
    (hfloor : 1 ≤ N ^ 2 * lam)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    ((typeISet f N lam δ).card : ℝ) ≤ 384 * (N * δ + 1) := by
  by_cases hδhalf : δ < 1/2
  · exact typeI_arc_sum hN2 hlam hδ hδhalf hf hfloor hlower hupper
  · -- `δ ≥ 1/2`: trivial cardinality bound `#typeISet ≤ N + 2 ≤ 2Nδ + 2 ≤ 384(Nδ+1)`.
    push Not at hδhalf
    have hN0 : (0 : ℝ) ≤ N := by linarith
    -- `typeISet ⊆ nearSet ⊆ Finset.Icc ⌊N⌋ ⌊2N⌋`.
    have hsubN : typeISet f N lam δ ⊆ nearSet f N δ := by
      intro n hn
      have hmaj : n ∈ majorSet f N δ := (mem_typeISet.mp hn).1
      simp only [majorSet, Finset.mem_filter] at hmaj; exact hmaj.1
    have hsub : typeISet f N lam δ ⊆ Finset.Icc ⌊N⌋ ⌊2 * N⌋ :=
      hsubN.trans (Finset.filter_subset _ _)
    have hcardle : (typeISet f N lam δ).card ≤ (Finset.Icc ⌊N⌋ ⌊2 * N⌋).card :=
      Finset.card_le_card hsub
    have hIcccard : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℝ) ≤ N + 2 := by
      have hle : ⌊N⌋ ≤ ⌊2 * N⌋ := by apply Int.floor_le_floor; linarith
      have hcard_eq : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℤ) = ⌊2 * N⌋ + 1 - ⌊N⌋ :=
        Int.card_Icc_of_le _ _ (by omega)
      have hval : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℝ)
          = (⌊2 * N⌋ : ℝ) - (⌊N⌋ : ℝ) + 1 := by
        have : (((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℤ) : ℝ)
            = ((⌊2 * N⌋ + 1 - ⌊N⌋ : ℤ) : ℝ) := by exact_mod_cast hcard_eq
        push_cast at this; linarith
      rw [hval]
      have ha : ((⌊2 * N⌋ : ℤ) : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
      have hb : N - 1 < ((⌊N⌋ : ℤ) : ℝ) := by have := Int.sub_one_lt_floor N; linarith
      linarith
    have hcardleR : ((typeISet f N lam δ).card : ℝ) ≤ N + 2 := by
      calc ((typeISet f N lam δ).card : ℝ)
            ≤ ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℝ) := by exact_mod_cast hcardle
        _ ≤ N + 2 := hIcccard
    -- `N ≤ 2Nδ` (since `δ ≥ 1/2`), so `N + 2 ≤ 2Nδ + 2 ≤ 384(Nδ+1)`.
    nlinarith [hcardleR, hN0, hδhalf, mul_nonneg hN0 hδ.le]

/-- **Prop 4.3, λ-normalized core with the pinned constant** (writeup line 482).  Assembled from the
residual bound and the Type I / Type II card bounds via the concrete partitions
`#nearSet = #residual + #major` and `#major = #typeI + #typeII`.  For small `N`
(`N < 2`) the count is trivially `O(1)`.  This is the explicit constant form of
`prop43_local`, exposing the literal constant used in its proof. -/
theorem prop43_local_explicit :
    ∀ (N lam δ : ℝ) (f : ℝ → ℝ), 0 < N → 0 < lam → 0 < δ → δ < 1 → ContDiff ℝ 2 f →
      1 ≤ N ^ 2 * lam →
      (∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) →
      (∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) →
      (((Finset.Icc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ 109159296 * (N * lam ^ (1/3 : ℝ) + N * δ
               + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1) := by
  intro N lam δ f hN hlam hδ hδ1 hf hfloor hlower hupper
  -- Normalize the `do`-block (`bind`/`pure`) in the goal into `.image Int.cast`.
  simp only [bind_pure_comp, Finset.fmap_def]
  -- The conclusion's `ℝ`-cast image filtered set has the same card as the integer
  -- `nearSet f N δ`, since `Int.cast` is injective.
  have himg : (((Finset.Icc ⌊N⌋ ⌊2 * N⌋).image (Int.cast : ℤ → ℝ)).filter
        (fun (n : ℝ) => distInt (f n) ≤ δ))
      = (nearSet f N δ).image (Int.cast : ℤ → ℝ) := by
    rw [Finset.filter_image, nearSet]
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)]
  by_cases hN2 : 2 ≤ N
  · -- Main regime.
    have hsplit1 := nearSet_card_split f N δ
    have hsplit2 := majorSet_card_split f N lam δ
    have hres := residual_card_bound hN2 hlam hδ hδ1 hf hupper
    have hI := typeI_card_bound hN2 hlam hδ hδ1 hf hfloor hlower hupper
    have hII := typeII_card_bound hN2 hlam hδ hδ1 hf hlower hupper
    -- `#nearSet = #res + #I + #II`.
    have hcard : ((nearSet f N δ).card : ℝ)
        = (residualSet f N δ).card + (typeISet f N lam δ).card
          + (typeIISet f N lam δ).card := by
      have : (nearSet f N δ).card
          = (residualSet f N δ).card + ((typeISet f N lam δ).card
            + (typeIISet f N lam δ).card) := by rw [hsplit1, hsplit2]
      rw [this]; push_cast; ring
    rw [hcard]
    -- combine the three bounds.
    have hsq : 0 ≤ Real.sqrt (δ / lam) := Real.sqrt_nonneg _
    have hlog : 0 ≤ Real.log (2 + Real.sqrt (δ / lam)) := by
      apply Real.log_nonneg; linarith [hsq]
    have hslog : 0 ≤ Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) :=
      mul_nonneg hsq hlog
    have hNl : 0 ≤ N * lam ^ (1/3 : ℝ) := by positivity
    have hNd : 0 ≤ N * δ := by positivity
    nlinarith [hres, hI, hII, hslog, hNl, hNd]
  · -- Small `N` (`N < 2`): `#nearSet ≤ ⌊2N⌋ - ⌊N⌋ + 1`, bounded by a constant.
    push Not at hN2
    have hsub : nearSet f N δ ⊆ Finset.Icc ⌊N⌋ ⌊2 * N⌋ := Finset.filter_subset _ _
    have hcardle : (nearSet f N δ).card ≤ (Finset.Icc ⌊N⌋ ⌊2 * N⌋).card :=
      Finset.card_le_card hsub
    have hIcccard : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℝ) ≤ N + 2 := by
      have hle : ⌊N⌋ ≤ ⌊2 * N⌋ := by apply Int.floor_le_floor; linarith
      have hcard_eq : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℤ) = ⌊2 * N⌋ + 1 - ⌊N⌋ :=
        Int.card_Icc_of_le _ _ (by omega)
      have hval : ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℝ)
          = (⌊2 * N⌋ : ℝ) - (⌊N⌋ : ℝ) + 1 := by
        have : (((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℤ) : ℝ)
            = ((⌊2 * N⌋ + 1 - ⌊N⌋ : ℤ) : ℝ) := by exact_mod_cast hcard_eq
        push_cast at this; linarith
      rw [hval]
      have ha : ((⌊2 * N⌋ : ℤ) : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
      have hb : N - 1 < ((⌊N⌋ : ℤ) : ℝ) := by have := Int.sub_one_lt_floor N; linarith
      linarith
    have hcardleR : ((nearSet f N δ).card : ℝ) ≤ N + 2 := by
      calc ((nearSet f N δ).card : ℝ) ≤ ((Finset.Icc ⌊N⌋ ⌊2 * N⌋).card : ℝ) := by
            exact_mod_cast hcardle
        _ ≤ N + 2 := hIcccard
    have hNl : 0 ≤ N * lam ^ (1/3 : ℝ) := by positivity
    have hNd : 0 ≤ N * δ := by positivity
    have hsq : 0 ≤ Real.sqrt (δ / lam) := Real.sqrt_nonneg _
    have hlog : 0 ≤ Real.log (2 + Real.sqrt (δ / lam)) := by
      apply Real.log_nonneg; linarith [hsq]
    have hslog : 0 ≤ Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) :=
      mul_nonneg hsq hlog
    nlinarith [hcardleR, hNl, hNd, hslog, hN2]

theorem prop43_local : ∃ C : ℝ, 0 < C ∧
    ∀ (N lam δ : ℝ) (f : ℝ → ℝ), 0 < N → 0 < lam → 0 < δ → δ < 1 → ContDiff ℝ 2 f →
      1 ≤ N ^ 2 * lam →
      (∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|) →
      (∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) →
      (((Finset.Icc ⌊N⌋ ⌊2 * N⌋).filter (fun n => distInt (f (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ C * (N * lam ^ (1/3 : ℝ) + N * δ
               + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1) := by
  exact ⟨109159296, by norm_num, prop43_local_explicit⟩

end Squarefree.Geometry
