import Squarefree.Geometry.NearCurveTypeIIBCount
import Squarefree.Geometry.NearCurveTypeIIDoubleSum
import Squarefree.Geometry.NearCurveGreedy
import Squarefree.Geometry.NearCurveStrip
import Squarefree.Geometry.NearCurveConvexArc
import Squarefree.Geometry.NearCurveAux
import Mathlib

/-!
# §4.3 Type II backbone — assembly (writeup 608–665)

The Type II proper-arc count.  A **Type II** point `n ∈ typeIISet` is a major point
whose witness line's proper arc is *long* (`L > δ√(q/λ)`); equivalently it fails the
Type I shortness predicate `OnTypeIArc`.  Being a major point it still has an
`OnMajorArc` witness triple `a < n < b` on a small-denominator line `D`, so its
counting object is the un-windowed proper major arc `properArc' D` and `D.denom = q`.

This module supplies the final assembly that reduces
`typeII_card_bound` (writeup 665):
  `#typeIISet ≤ K·(Nδ + √(δ/λ)·log(2+√(δ/λ)) + 1)`
combining the slope-localization + convexity `b`-count from
`NearCurveTypeIIBCount` (via `typeII_lines_count_per_denom`) and the double-sum
arithmetic from `NearCurveTypeIIDoubleSum` (`typeII_double_sum`).

The reduction mirrors `NearCurveGreedy`'s `lineSet`/biUnion grouping: each Type II
point lies on the carrier of its witness line, and the cover splits into ≤2 strip
components per line, then is grouped by denominator.

Constant: `K = 16384` (the factor 2 from `lineCarrier' ≤ 2·properArc'`, the per-line
ceiling, and the cross-term/harmonic absorption folded into the double sum).
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## §4.3 Type II line count per denominator (the combine) -/

set_option maxHeartbeats 300000 in
/-- **Type II lines per denominator** (writeup 624–650).  For a fixed denominator
`q`, the number of Type II witness lines is `≤ ⌈852800(qNλ+1)⌉₊`.

Assembly: the lines of denom `q` fibre over their *slope*; each slope-fibre has `≤ 1025`
lines (`typeII_b_count_per_slope`, curvature ratio 256), and the slopes are localized to
a window of width `768Nλ + 64√(λ/q)` around `f'(N)` (`typeII_slope_localized` +
`slopeNum_image_card_le`), giving `≤ q(768Nλ + 64√(λ/q)) + 1` slopes.  Combining and
using `√(qλ) ≤ 1 + qNλ` (as `N ≥ 1`) bounds the product by `852800(qNλ+1)`. -/
theorem typeII_lines_count_per_denom (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hδ : 0 < δ) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    (q : ℤ) (hq : 0 < q) :
    ((typeIILines f N lam δ).filter (fun D => D.denom = q)).card
      ≤ ⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set Fq := (typeIILines f N lam δ).filter (fun D => D.denom = q) with hFqdef
  -- The slope window: `[c₀ − R, c₀ + R]`, `c₀ = f'(N)`, `R = 384Nλ + 32√(λ/q)`.
  set c₀ : ℝ := deriv f N with hc₀
  set R : ℝ := 384 * N * lam + 32 * Real.sqrt (lam / (q : ℝ)) with hR
  -- (1) fibre `Fq` over `D ↦ D.slope.num`: `#Fq = Σ_{r ∈ image} #fibre ≤ #image · 1025`.
  have hfib : Fq.card ≤ (Fq.image (fun D => D.slope.num)).card * 1025 := by
    have hcardfw : Fq.card
        = ∑ r ∈ Fq.image (fun D => D.slope.num),
            (Fq.filter (fun D => D.slope.num = r)).card :=
      Finset.card_eq_sum_card_fiberwise (fun D _ => Finset.mem_image_of_mem _ ‹_›)
    rw [hcardfw]
    calc ∑ r ∈ Fq.image (fun D => D.slope.num),
            (Fq.filter (fun D => D.slope.num = r)).card
        ≤ ∑ _r ∈ Fq.image (fun D => D.slope.num), 1025 := by
          apply Finset.sum_le_sum
          intro r hr
          -- each numerator-fibre has `≤ 6` lines: refine to a slope-fibre.
          obtain ⟨D₀, hD₀F, hD₀r⟩ := Finset.mem_image.mp hr
          -- the fibre `{D ∈ Fq : D.slope.num = r}` ⊆ b-count fibre of `D₀`.
          have hsubF : Fq.filter (fun D => D.slope.num = r)
              ⊆ (typeIILines f N lam δ).filter
                  (fun D => D.denom = q ∧ D.slope = D₀.slope) := by
            intro D hD
            rw [Finset.mem_filter] at hD ⊢
            rw [hFqdef, Finset.mem_filter] at hD
            obtain ⟨⟨hDmem, hDden⟩, hDnum⟩ := hD
            refine ⟨hDmem, hDden, ?_⟩
            -- same denom + same num ⟹ same slope (reduced rationals).
            rw [hFqdef, Finset.mem_filter] at hD₀F
            have hD₀den : D₀.denom = q := hD₀F.2
            have hdeneq : D.slope.den = D₀.slope.den := by
              have h1 : (D.denom : ℤ) = q := hDden
              have h2 : (D₀.denom : ℤ) = q := hD₀den
              rw [MajorLine.denom] at h1 h2
              omega
            have hnumeq : D.slope.num = D₀.slope.num := by rw [hDnum, hD₀r]
            exact Rat.ext hnumeq hdeneq
          calc (Fq.filter (fun D => D.slope.num = r)).card
              ≤ ((typeIILines f N lam δ).filter
                  (fun D => D.denom = q ∧ D.slope = D₀.slope)).card :=
                Finset.card_le_card hsubF
            _ ≤ 1025 := typeII_b_count_per_slope hf hlam hδ hN2 hlower q D₀
      _ = (Fq.image (fun D => D.slope.num)).card * 1025 := by
          rw [Finset.sum_const, smul_eq_mul]
  -- (2) `#image ≤ q·(2R) + 1` by the fraction count over the slope window.
  have hslopebd : ∀ D ∈ Fq, c₀ - R ≤ (D.slope : ℝ) ∧ (D.slope : ℝ) ≤ c₀ + R := by
    intro D hD
    rw [hFqdef, Finset.mem_filter] at hD
    obtain ⟨hDmem, hDden⟩ := hD
    have hloc := typeII_slope_localized hf hlam hδ hN2 hlower hupper hDmem
    have hqeq : (D.denom : ℝ) = (q : ℝ) := by exact_mod_cast hDden
    rw [hqeq] at hloc
    rw [abs_le] at hloc
    constructor <;> [linarith [hloc.1]; linarith [hloc.2]]
  have hdenF : ∀ D ∈ Fq, D.denom = q := by
    intro D hD; rw [hFqdef, Finset.mem_filter] at hD; exact hD.2
  have hRnn : (0 : ℝ) ≤ R := by rw [hR]; positivity
  have himg : ((Fq.image (fun D => D.slope.num)).card : ℝ)
      ≤ (q : ℝ) * ((c₀ + R) - (c₀ - R)) + 1 :=
    slopeNum_image_card_le hq (by linarith) Fq hdenF hslopebd
  have himg' : ((Fq.image (fun D => D.slope.num)).card : ℝ)
      ≤ (q : ℝ) * (2 * R) + 1 := by
    convert himg using 2; ring
  -- (3) numeric combine: `#Fq ≤ 1025·(q·2R + 1) ≤ 852800(qNλ+1)`.
  -- `q·2R = 768qNλ + 64√(qλ)`; `√(qλ) ≤ 1 + qNλ`.
  have hsqrt_qlam : Real.sqrt ((q : ℝ) * lam) ≤ 1 + (q : ℝ) * N * lam := by
    -- `√(qλ) ≤ 1 + qλ` (AM-GM type: `√t ≤ 1 + t` for `t ≥ 0`), then `qλ ≤ qNλ`.
    have ht : (0 : ℝ) ≤ (q : ℝ) * lam := by positivity
    have h1 : Real.sqrt ((q : ℝ) * lam) ≤ 1 + (q : ℝ) * lam := by
      nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg ((q : ℝ) * lam),
        sq_nonneg (Real.sqrt ((q : ℝ) * lam) - 1)]
    have h2 : (q : ℝ) * lam ≤ (q : ℝ) * N * lam := by nlinarith [hqR, hlam]
    linarith
  -- `q·√(λ/q) = √(qλ)`: `q·√(λ/q) = √(q²·λ/q) = √(qλ)`.
  have hqsqrt : (q : ℝ) * Real.sqrt (lam / (q : ℝ)) = Real.sqrt ((q : ℝ) * lam) := by
    rw [show (q : ℝ) * lam = (q : ℝ) ^ 2 * (lam / (q : ℝ)) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hqR.le]
  -- `q·2R = 768qNλ + 64·q·√(λ/q) = 768qNλ + 64√(qλ)`.
  have hq2R : (q : ℝ) * (2 * R)
      = 768 * ((q : ℝ) * N * lam) + 64 * Real.sqrt ((q : ℝ) * lam) := by
    rw [hR]
    have hexp : (q : ℝ) * (2 * (384 * N * lam + 32 * Real.sqrt (lam / (q : ℝ))))
        = 768 * ((q : ℝ) * N * lam) + 64 * ((q : ℝ) * Real.sqrt (lam / (q : ℝ))) := by ring
    rw [hexp, hqsqrt]
  -- Final bound: `#Fq ≤ 1025·(768qNλ + 64√(qλ) + 1) ≤ 1025·(768qNλ + 64(1+qNλ) + 1)`.
  -- abstract the sqrt to keep arithmetic light.
  set S : ℝ := Real.sqrt ((q : ℝ) * lam) with hS
  set M : ℝ := (q : ℝ) * N * lam with hM
  have hSbd : S ≤ 1 + M := by rw [hS, hM]; exact hsqrt_qlam
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; positivity
  have hq2R' : (q : ℝ) * (2 * R) = 768 * M + 64 * S := by rw [hq2R]
  -- pure real-arithmetic core (no `Real.sqrt`/`Finset` left to unfold).
  have harith : ∀ C K Sx Mx : ℝ, 0 ≤ Mx → 0 ≤ K → C ≤ K * 1025 →
      K ≤ (768 * Mx + 64 * Sx) + 1 → Sx ≤ 1 + Mx → C ≤ 852800 * (Mx + 1) := by
    intro C K Sx Mx hMx hKx hCK hKb hSb
    nlinarith [hCK, hKb, hSb, hMx, hKx]
  have hkey : (Fq.card : ℝ) ≤ 852800 * (M + 1) := by
    have hfibR : (Fq.card : ℝ)
        ≤ ((Fq.image (fun D => D.slope.num)).card : ℝ) * 1025 := by exact_mod_cast hfib
    have himg'' : ((Fq.image (fun D => D.slope.num)).card : ℝ) ≤ (768 * M + 64 * S) + 1 := by
      rw [← hq2R']; exact himg'
    have hK0 : (0 : ℝ) ≤ ((Fq.image (fun D => D.slope.num)).card : ℝ) := by positivity
    exact harith _ _ S M hM0 hK0 hfibR himg'' hSbd
  -- pass to the ceiling.
  have hceil : (Fq.card : ℝ) ≤ (⌈852800 * (M + 1)⌉₊ : ℝ) :=
    le_trans hkey (Nat.le_ceil _)
  have : (Fq.card : ℝ) ≤ (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ) := by
    rw [hM] at hceil; exact hceil
  exact_mod_cast this

/-! ## The cover — Type II points sit on their witness-line carriers (PROVEN) -/

/-- **Cover.**  Every Type II point lies on the carrier of its witness line, so
`typeIISet ⊆ typeIILines.biUnion lineCarrier'`. -/
private theorem typeIISet_subset_biUnion :
    typeIISet f N lam δ
      ⊆ (typeIILines f N lam δ).biUnion (fun D => lineCarrier' f N δ D) := by
  classical
  intro n hn
  obtain ⟨_, _, haN, hbN, hnN, _, _, _, hon, _, _⟩ := witnessII_spec hn
  rw [Finset.mem_biUnion]
  refine ⟨witnessLineII f N δ n, ?_, ?_⟩
  · exact mem_typeIILines.mpr ⟨n, hn, rfl⟩
  · exact mem_lineCarrier'.mpr ⟨hnN, hon⟩

/-- **`#typeIISet ≤ Σ_{D∈typeIILines} 2·#properArc' D`** (PROVEN, writeup 652).  The
cover into carriers + `card_biUnion_le` + the ≤2-component factor
(`lineCarrier'_card_le_two_properArc'`). -/
theorem typeII_card_le_carrier_sum :
    ((typeIISet f N lam δ).card : ℝ)
      ≤ ∑ D ∈ typeIILines f N lam δ, 2 * ((properArc' f N δ D).card : ℝ) := by
  classical
  have hcover : (typeIISet f N lam δ).card
      ≤ ((typeIILines f N lam δ).biUnion (fun D => lineCarrier' f N δ D)).card :=
    Finset.card_le_card typeIISet_subset_biUnion
  have hbu : ((typeIILines f N lam δ).biUnion (fun D => lineCarrier' f N δ D)).card
      ≤ ∑ D ∈ typeIILines f N lam δ, (lineCarrier' f N δ D).card :=
    Finset.card_biUnion_le
  have hcomp : ∑ D ∈ typeIILines f N lam δ, (lineCarrier' f N δ D).card
      ≤ ∑ D ∈ typeIILines f N lam δ, 2 * (properArc' f N δ D).card :=
    Finset.sum_le_sum (fun D _ => lineCarrier'_card_le_two_properArc')
  have hnat : (typeIISet f N lam δ).card
      ≤ ∑ D ∈ typeIILines f N lam δ, 2 * (properArc' f N δ D).card :=
    le_trans hcover (le_trans hbu hcomp)
  calc ((typeIISet f N lam δ).card : ℝ)
      ≤ ((∑ D ∈ typeIILines f N lam δ, 2 * (properArc' f N δ D).card : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = ∑ D ∈ typeIILines f N lam δ, 2 * ((properArc' f N δ D).card : ℝ) := by
        push_cast; ring

/-! ## STUB 7 — the per-denominator grouping/re-index -/

/-- **STUB.** The remaining grouping/re-index step (writeup 652–656).  Re-indexes the
proven carrier sum `Σ_{D∈typeIILines} 2·#properArc' D` (`typeII_card_le_carrier_sum`)
by denominator `q ∈ [1, ⌊4√(δ/λ)⌋]` (finite by `typeII_denom_le`) and bounds the
inner fiber sum by `(#lines of denom q)·2·max_ν` via `typeII_lines_count_per_denom`
(line count) + `typeII_nu_per_line` (per-line `ν`), giving the per-`(q)` summand.
Deferred. -/
theorem typeII_carrier_sum_le_grouped (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hδ : 0 < δ) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    (∑ D ∈ typeIILines f N lam δ, 2 * ((properArc' f N δ D).card : ℝ))
      ≤ ∑ q ∈ Finset.Icc 1 ⌊4 * Real.sqrt (δ / lam)⌋₊,
          2 * (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ)
            * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1) := by
  classical
  set Qmax := ⌊4 * Real.sqrt (δ / lam)⌋₊ with hQmax
  set key : MajorLine → ℕ := fun D => D.slope.den with hkey
  -- (1) The fiber key maps `typeIILines` into `Icc 1 Qmax`.
  have hmaps : ∀ D ∈ typeIILines f N lam δ, key D ∈ Finset.Icc 1 Qmax := by
    intro D hD
    rw [Finset.mem_Icc]
    simp only [hkey]
    constructor
    · have : 0 < D.slope.den := D.slope.pos
      omega
    · -- `D.slope.den ≤ 4√(δ/λ)` from `typeII_denom_le`, then `≤ Qmax = ⌊·⌋`.
      have hreal : (D.denom : ℝ) ≤ 4 * Real.sqrt (δ / lam) :=
        typeII_denom_le hf hlam hδ hN2 hlower hD
      have hden : ((D.slope.den : ℝ)) ≤ 4 * Real.sqrt (δ / lam) := by
        have : (D.denom : ℝ) = (D.slope.den : ℝ) := by
          simp [MajorLine.denom]
        rwa [this] at hreal
      rw [hQmax]
      exact Nat.le_floor hden
  -- (2) Re-index the carrier sum by the denominator fiber.
  have hfiber := Finset.sum_fiberwise_of_maps_to (g := key) hmaps
    (fun D => 2 * ((properArc' f N δ D).card : ℝ))
  rw [← hfiber]
  -- (3) Bound each fiber sum: per-line `ν ≤ 4√(δ/λ)/q + 1`, then count lines.
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.mem_Icc] at hq
  have hq1 : 1 ≤ q := hq.1
  -- nonneg factor `4√(δ/λ)/q + 1`.
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hfac_nn : (0 : ℝ) ≤ 4 * Real.sqrt (δ / lam) / (q : ℝ) + 1 := by positivity
  -- the fiber is `typeIILines.filter (key = q)`.
  set Fq := (typeIILines f N lam δ).filter (fun D => key D = q) with hFq
  -- inner sum ≤ (#Fq) · 2 · (4√/q + 1)  (each term, with q = D.slope.den).
  have hinner : ∑ D ∈ Fq, 2 * ((properArc' f N δ D).card : ℝ)
      ≤ ∑ D ∈ Fq, 2 * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro D hDF
    rw [hFq, Finset.mem_filter] at hDF
    have hkeyD : key D = q := hDF.2
    have hnu : ((properArc' f N δ D).card : ℝ)
        ≤ 4 * Real.sqrt (δ / lam) / (D.denom : ℝ) + 1 :=
      typeII_nu_per_line hf hlam hδ hN2 hlower D
    have hqeq : (D.denom : ℝ) = (q : ℝ) := by
      rw [MajorLine.denom]; rw [hkey] at hkeyD; exact_mod_cast hkeyD
    rw [hqeq] at hnu
    linarith
  -- evaluate the constant inner sum.
  have hconst : ∑ D ∈ Fq, 2 * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1)
      = (Fq.card : ℝ) * (2 * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- count the lines of denominator `q`.
  have hcount : (Fq.card : ℝ) ≤ (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ) := by
    have hcZ := typeII_lines_count_per_denom hf hlam hδ hN2 hlower hupper (q := (q : ℤ))
      (by exact_mod_cast hq1)
    have hFqeq : Fq = (typeIILines f N lam δ).filter (fun D => D.denom = (q : ℤ)) := by
      rw [hFq]; apply Finset.filter_congr
      intro D _
      rw [hkey, MajorLine.denom]
      constructor
      · intro h; exact_mod_cast h
      · intro h; exact_mod_cast h
    rw [hFqeq]
    have hcastQ : (((q : ℤ) : ℝ)) = (q : ℝ) := by push_cast; ring
    calc (((typeIILines f N lam δ).filter (fun D => D.denom = (q : ℤ))).card : ℝ)
        ≤ ((⌈852800 * (((q : ℤ) : ℝ) * N * lam + 1)⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcZ
      _ = (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ) := by rw [hcastQ]
  -- combine.
  calc ∑ D ∈ Fq, 2 * ((properArc' f N δ D).card : ℝ)
      ≤ (Fq.card : ℝ) * (2 * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1)) := by
        rw [← hconst]; exact hinner
    _ ≤ (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ)
          * (2 * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_right hcount
        positivity
    _ = 2 * (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ)
          * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1) := by ring

/-- **`#typeIISet ≤ per-(q) double sum`** (writeup 652–656): the proven carrier sum
chained through the deferred re-index. -/
theorem typeII_card_le_grouped (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ)
    (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    ((typeIISet f N lam δ).card : ℝ)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊4 * Real.sqrt (δ / lam)⌋₊,
          2 * (⌈852800 * ((q : ℝ) * N * lam + 1)⌉₊ : ℝ)
            * (4 * Real.sqrt (δ / lam) / (q : ℝ) + 1) :=
  typeII_card_le_carrier_sum.trans
    (typeII_carrier_sum_le_grouped hf hlam hδ hN2 hlower hupper)

/-! ## The assembly — Type II card bound -/

/-- **`typeII_card_bound`** (writeup 665).  The Type II proper-arc total:
`#typeIISet ≤ 16384·(Nδ + √(δ/λ)·log(2+√(δ/λ)) + 1)`.

Assembly: `typeII_card_le_grouped` reduces `#typeIISet` to the per-`(q)` double sum,
and `typeII_double_sum` evaluates it to the closed form.  The constant `16384` is the
`typeII_double_sum` constant (the factor `2` and per-line ceiling are already inside
the summand). -/
theorem typeII_card_bound {f : ℝ → ℝ} {N lam δ : ℝ}
    (hN2 : 2 ≤ N) (hlam : 0 < lam) (hδ : 0 < δ) (_hδ1 : δ < 1) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam) :
    ((typeIISet f N lam δ).card : ℝ)
      ≤ 109158400 * (N * δ + Real.sqrt (δ / lam) * Real.log (2 + Real.sqrt (δ / lam)) + 1) :=
  (typeII_card_le_grouped hf hlam hδ hN2 hlower hupper).trans
    (typeII_double_sum N lam δ hlam hδ hN2)

end Squarefree.Geometry
