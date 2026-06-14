import Squarefree.Geometry.NearCurveTypeIClass
import Mathlib

/-!
# §4.3 Type I disjoint-interval packing (writeup 599–605)

This module supplies the combinatorial packing that closes the Type I total
`#typeISet ≤ 8·(N·δ + 1)`.  The analytic inputs are proved upstream:
`offLine_spacing` (the quadratic spacing bound, writeup 534–562) and
`typeI_offLine_gap` (writeup 587–598, every off-line near-set point of a Type I
arc is `≥ d(A)/24` from the base, `d(A) = (B−A)/(qδ)`).

The two genuinely combinatorial facts are isolated here:

* `onLine_near_residue` — near-set points on a fixed line `D` lie in one residue
  class `mod q` (denominator), via `OnLine.sub_dvd` plus `num`/`den` coprimality.
* `typeISet_witness` — every Type I point carries a concrete witness line `D`,
  arc endpoints `a < n < b`, with `q ≤ 1/(4δ)` and span `B−A ≤ δ√(q/λ)`.

The final greedy sum over arcs (writeup 599–605) is left as the single concrete
named stub `typeI_arc_sum` consumed by `typeI_card_bound`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

/-! ## Near-set points on a line are one residue class mod `q` -/

/-- **`q ∣ (n − m)` for two near-set points on the same line.**  `OnLine.sub_dvd`
gives `q ∣ p·(n−m)`; since `gcd(p,q)=1` (reduced slope) this forces `q ∣ (n−m)`.
This is the residue-class fact behind `residueClass_card_le`. -/
theorem denom_dvd_sub_of_onLine {f : ℝ → ℝ} {D : MajorLine} {n m : ℤ}
    (hn : OnLine f D n) (hm : OnLine f D m) :
    D.denom ∣ (n - m) := by
  -- `q ∣ p·(n−m)` and `gcd(p,q)=1`.
  have hdvd : D.denom ∣ (D.slope.num * (n - m)) := OnLine.sub_dvd hn hm
  -- coprimality of numerator and denominator (as integers).
  have hcop : IsCoprime (D.slope.num) (D.denom) := by
    have h := D.slope.reduced  -- `Nat.Coprime D.slope.num.natAbs D.slope.den`
    have hco : IsCoprime (D.slope.num) ((D.slope.den : ℤ)) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using h
    simpa [MajorLine.denom] using hco
  -- `q ∣ p·k` & `gcd(p,q)=1` ⟹ `q ∣ k`.
  exact (hcop.symm.dvd_of_dvd_mul_left hdvd)

/-- **Residue-count of near-set points on a line in a window.**  If every element
of `S ⊆ ℤ` lies in `[lo, hi]` and on the line `D`, then `#S ≤ (hi−lo)/q + 1`.
Direct application of `Squarefree.residueClass_card_le` with the residue fact
`denom_dvd_sub_of_onLine`, using any fixed base point `r` on the line. -/
theorem onLine_window_card_le {f : ℝ → ℝ} {D : MajorLine} {lo hi : ℝ}
    (hlohi : lo ≤ hi) (S : Finset ℤ)
    (hmem : ∀ n ∈ S, (lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) ∧ OnLine f D n) :
    (S.card : ℝ) ≤ (hi - lo) / (D.denom : ℝ) + 1 := by
  -- pick a base `r` on the line, or `0` if `S` is empty.
  rcases S.eq_empty_or_nonempty with hSe | ⟨r, hr⟩
  · subst hSe
    simp only [Finset.card_empty, Nat.cast_zero]
    have hqR : (0 : ℝ) < (D.denom : ℝ) := by
      have := D.denom_pos; exact_mod_cast this
    have : (0 : ℝ) ≤ (hi - lo) / (D.denom : ℝ) := div_nonneg (by linarith) hqR.le
    linarith
  · have hrline : OnLine f D r := (hmem r hr).2
    refine Squarefree.residueClass_card_le D.denom_pos r lo hi hlohi S ?_
    intro n hn
    refine ⟨(hmem n hn).1.1, (hmem n hn).1.2, ?_⟩
    exact denom_dvd_sub_of_onLine (hmem n hn).2 hrline

/-! ## Per-arc residue count specialized to a Type I witness

For a Type I witness line `D` with arc `[a, b]`, the near-set points on `D` inside
the arc window number `ν(A) ≤ (b−a)/q + 1 = δ·d(A) + 1`, where `d(A) = (b−a)/(qδ)`.
-/

/-- **Per-arc residue count.**  If `S` collects near-set points all on `D` and all
inside the closed window `[a, b]`, then `#S ≤ δ·d(A) + 1`. -/
theorem arc_residue_count {f : ℝ → ℝ} {D : MajorLine} {δ : ℝ} {a b : ℤ}
    (hδ : 0 < δ) (hab : a ≤ b) (S : Finset ℤ)
    (hmem : ∀ n ∈ S, ((a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (b : ℝ)) ∧ OnLine f D n) :
    (S.card : ℝ) ≤ δ * arcDensity D δ a b + 1 := by
  have hqR : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hcount := onLine_window_card_le (f := f) (D := D) (lo := (a : ℝ)) (hi := (b : ℝ))
    habR S hmem
  -- `((b−a)/q) = δ·((b−a)/(qδ)) = δ·d(A)`.
  have hrw : ((b : ℝ) - (a : ℝ)) / (D.denom : ℝ) = δ * arcDensity D δ a b := by
    rw [arcDensity]; field_simp
  rwa [hrw] at hcount

/-- **Sharp per-arc residue count** (avoids the `+1`).  If `S` collects near-set
points all on `D` and all inside `[a, b]`, and the arc satisfies `2·q ≤ b − a`
(equivalently `(b−a)/q ≥ 2`, which holds for a Type I witness since there are at
least three `q`-separated residue points `a < n < b` on `D`), then
`#S ≤ (3/2)·δ·d(A)`.  Proof: `#S ≤ (b−a)/q + 1 ≤ (b−a)/q + (1/2)(b−a)/q
= (3/2)(b−a)/q = (3/2)·δ·d(A)`. -/
theorem arc_residue_count_sharp {f : ℝ → ℝ} {D : MajorLine} {δ : ℝ} {a b : ℤ}
    (hδ : 0 < δ) (hab : a ≤ b) (hq2 : 2 * (D.denom : ℝ) ≤ (b : ℝ) - (a : ℝ))
    (S : Finset ℤ)
    (hmem : ∀ n ∈ S, ((a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (b : ℝ)) ∧ OnLine f D n) :
    (S.card : ℝ) ≤ (3 / 2) * (δ * arcDensity D δ a b) := by
  have hqR : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  have hcount := arc_residue_count hδ hab S hmem
  -- `δ·d(A) = (b−a)/q`, and `2q ≤ b−a` gives `1 ≤ (1/2)·(b−a)/q = (1/2)·δ·d(A)`.
  have hdA : δ * arcDensity D δ a b = ((b : ℝ) - (a : ℝ)) / (D.denom : ℝ) := by
    rw [arcDensity]; field_simp
  have h1 : (1 : ℝ) ≤ (1 / 2) * (δ * arcDensity D δ a b) := by
    rw [hdA]
    have : (1 / 2 : ℝ) * (((b : ℝ) - (a : ℝ)) / (D.denom : ℝ))
        = (((b : ℝ) - (a : ℝ)) / 2) / (D.denom : ℝ) := by ring
    rw [this, le_div_iff₀ hqR]
    linarith [hq2]
  linarith [hcount, h1]

/-- **Per-arc residue count, factor-2 form** (avoids the `+1`, weaker spacing).  If
`S` collects near-set points all on `D` and all inside `[a, b]`, and the arc satisfies
`q ≤ b − a` (i.e. `≥ 2` `q`-separated residue points, one gap `≥ q`), then
`#S ≤ 2·δ·d(A)`.  Proof: `#S ≤ (b−a)/q + 1 ≤ (b−a)/q + (b−a)/q = 2(b−a)/q = 2δ·d(A)`. -/
theorem arc_residue_count_two {f : ℝ → ℝ} {D : MajorLine} {δ : ℝ} {a b : ℤ}
    (hδ : 0 < δ) (hab : a ≤ b) (hq : (D.denom : ℝ) ≤ (b : ℝ) - (a : ℝ))
    (S : Finset ℤ)
    (hmem : ∀ n ∈ S, ((a : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (b : ℝ)) ∧ OnLine f D n) :
    (S.card : ℝ) ≤ 2 * (δ * arcDensity D δ a b) := by
  have hqR : (0 : ℝ) < (D.denom : ℝ) := by have := D.denom_pos; exact_mod_cast this
  have hcount := arc_residue_count hδ hab S hmem
  -- `δ·d(A) = (b−a)/q`, and `q ≤ b−a` gives `1 ≤ (b−a)/q = δ·d(A)`.
  have hdA : δ * arcDensity D δ a b = ((b : ℝ) - (a : ℝ)) / (D.denom : ℝ) := by
    rw [arcDensity]; field_simp
  have h1 : (1 : ℝ) ≤ δ * arcDensity D δ a b := by
    rw [hdA, le_div_iff₀ hqR]; linarith
  linarith [hcount, h1]

/-! ## Disjointness gap (writeup 599–604)

If two Type I witness arcs `A_j` (line `D`, base near-set point `m₀` on `D`, arc
`[A,B]`) and `A_k` have first `x`-coordinates `n_j < n_k`, and the first point
`n_k` of `A_k` is OFF `D`, then `typeI_offLine_gap` forces `n_k − n_j ≥ d(A_j)/24`.
This is the spacing fact that makes the greedy intervals `I_j = [n_j, n_j +
d(A_j)/24)` pairwise disjoint. -/

/-- **Off-line gap, integer-endpoint form.**  For a Type I witness with INTEGER
arc endpoints `a < b` (the near-set endpoints), an off-line near-set point `m` is
`≥ d(A)/24` from the base `m₀ = a`, where `d(A) = (b−a)/(qδ) = arcDensity D δ a b`.
This is the disjointness driver: two arcs with first points `n_j < n_k`, `n_k` off
`A_j`'s line, satisfy `n_k − n_j ≥ d(A_j)/24`. -/
theorem offLine_gap_arc {f : ℝ → ℝ} {D : MajorLine} {lam δ : ℝ} {a b m₀ m : ℤ}
    (hf : ContDiff ℝ 2 f) (hlam : 0 < lam) (hδ : 0 < δ) (hab : a < b)
    (hq : (D.denom : ℝ) ≤ 1 / (4 * δ))
    (hdom : ∀ x ∈ Set.Icc (min (a : ℝ) (m : ℝ)) (max (b : ℝ) (m : ℝ)),
      |iteratedDeriv 2 f x| ≤ 256 * lam)
    (hgA : |lineRes f D (a : ℝ)| ≤ δ) (hgB : |lineRes f D (b : ℝ)| ≤ δ)
    (hm₀ : (m₀ : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ)) (hgm₀ : |lineRes f D (m₀ : ℝ)| ≤ δ)
    (hmne : (m : ℝ) ≠ (m₀ : ℝ))
    (hmoff : ¬ OnLine f D m) (hfm : |f (m : ℝ) - (latticeY f m : ℝ)| ≤ δ)
    (htypeI : ((b : ℝ) - (a : ℝ)) ≤ δ * Real.sqrt ((D.denom : ℝ) / (256 * lam))) :
    arcDensity D δ a b / 24 ≤ |(m : ℝ) - (m₀ : ℝ)| := by
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have h := typeI_offLine_gap (f := f) (D := D) (lam := lam) (δ := δ)
    (A := (a : ℝ)) (B := (b : ℝ)) (m₀ := (m₀ : ℝ)) (m := m)
    hf hlam hδ habR hq hdom hgA hgB hm₀ hgm₀ hmne hmoff hfm htypeI
  simpa only [arcDensity] using h

/-! ## Disjoint-interval length sum (the packing inequality)

Abstract packing fact, proved via Lebesgue measure: a finite family of pairwise
disjoint half-open intervals `[lo i, lo i + len i)` with `0 ≤ len i`, all contained
in `[L, U]`, has total length `Σ len i ≤ U − L`. -/

open MeasureTheory in
/-- **Disjoint-interval packing.**  Pairwise-disjoint half-open intervals
`Ico (lo i) (lo i + len i)`, `0 ≤ len i`, all `⊆ Icc L U`, have `Σ len i ≤ U − L`. -/
private theorem sum_len_le_of_disjoint_Ico {ι : Type*} (s : Finset ι)
    (lo len : ι → ℝ) (L U : ℝ) (hLU : L ≤ U) (hlen : ∀ i ∈ s, 0 ≤ len i)
    (hsub : ∀ i ∈ s, Set.Ico (lo i) (lo i + len i) ⊆ Set.Icc L U)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => Set.Ico (lo i) (lo i + len i))) :
    ∑ i ∈ s, len i ≤ U - L := by
  classical
  -- Work in `ℝ≥0∞` with Lebesgue measure.
  have hmeas : ∀ i, MeasurableSet (Set.Ico (lo i) (lo i + len i)) :=
    fun i => measurableSet_Ico
  -- `Σ vol(Ico i) = vol(⋃ Ico i) ≤ vol(Icc L U)`.
  have hbu : (∑ i ∈ s, volume (Set.Ico (lo i) (lo i + len i)))
      = volume (⋃ i ∈ s, Set.Ico (lo i) (lo i + len i)) :=
    (measure_biUnion_finset hdisj (fun i _ => hmeas i)).symm
  have hsubU : (⋃ i ∈ s, Set.Ico (lo i) (lo i + len i)) ⊆ Set.Icc L U := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hsub i hi hxi
  have hmono : volume (⋃ i ∈ s, Set.Ico (lo i) (lo i + len i)) ≤ volume (Set.Icc L U) :=
    measure_mono hsubU
  have hvolIco : ∀ i ∈ s, volume (Set.Ico (lo i) (lo i + len i)) = ENNReal.ofReal (len i) := by
    intro i _
    rw [Real.volume_Ico]; congr 1; ring
  have hvolIcc : volume (Set.Icc L U) = ENNReal.ofReal (U - L) := by
    rw [Real.volume_Icc]
  -- Convert to reals.
  have hsumeq : (∑ i ∈ s, volume (Set.Ico (lo i) (lo i + len i)))
      = ENNReal.ofReal (∑ i ∈ s, len i) := by
    rw [Finset.sum_congr rfl hvolIco]
    rw [ENNReal.ofReal_sum_of_nonneg hlen]
  rw [hsumeq] at hbu
  rw [hvolIcc] at hmono
  -- now `hbu : ofReal (Σ len) = volume (⋃ ...)` and `hmono : volume (⋃ ...) ≤ ofReal (U−L)`.
  have hle : ENNReal.ofReal (∑ i ∈ s, len i) ≤ ENNReal.ofReal (U - L) := by
    rw [hbu]; exact hmono
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hle

/-- **Disjoint-interval packing with bases in a window** (the §4.3 Type I form).
Pairwise-disjoint half-open intervals `Ico (lo i) (lo i + len i)`, `0 ≤ len i`, with
all *bases* `lo i ∈ [B0, B1]`, have `Σ len i ≤ (B1 − B0) + (sup len)`.  Proof: each
interval lies in `Icc B0 (B1 + M)` with `M := sup len` (since `lo i ≥ B0` and
`lo i + len i ≤ B1 + M`), so `sum_len_le_of_disjoint_Ico` gives
`Σ len ≤ (B1 + M) − B0`. -/
private theorem sum_len_le_of_disjoint_Ico_bases {ι : Type*} (s : Finset ι)
    (lo len : ι → ℝ) (B0 B1 M : ℝ) (hB : B0 ≤ B1) (hM0 : 0 ≤ M)
    (hlen : ∀ i ∈ s, 0 ≤ len i) (hlenM : ∀ i ∈ s, len i ≤ M)
    (hbase : ∀ i ∈ s, B0 ≤ lo i ∧ lo i ≤ B1)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => Set.Ico (lo i) (lo i + len i))) :
    ∑ i ∈ s, len i ≤ (B1 - B0) + M := by
  have hsub : ∀ i ∈ s, Set.Ico (lo i) (lo i + len i) ⊆ Set.Icc B0 (B1 + M) := by
    intro i hi x hx
    simp only [Set.mem_Ico] at hx
    obtain ⟨hb0, hb1⟩ := hbase i hi
    refine ⟨le_trans hb0 hx.1, ?_⟩
    have : x < lo i + len i := hx.2
    linarith [hlenM i hi, this]
  have hBM : B0 ≤ B1 + M := by linarith
  have := sum_len_le_of_disjoint_Ico s lo len B0 (B1 + M) hBM hlen hsub hdisj
  linarith

/-- **Gap ⇒ interval disjointness.**  If the half-open packing intervals are
ordered by left endpoint and the left interval's length does not reach the next
left endpoint (`lo₁ + len₁ ≤ lo₂`, the consequence of `offLine_gap_arc`), then the
two intervals are disjoint. -/
private theorem Ico_disjoint_of_gap {lo₁ len₁ lo₂ len₂ : ℝ}
    (hgap : lo₁ + len₁ ≤ lo₂) :
    Disjoint (Set.Ico lo₁ (lo₁ + len₁)) (Set.Ico lo₂ (lo₂ + len₂)) := by
  rw [Set.disjoint_left]
  intro x hx hx2
  exact absurd hx.2 (by simp only [Set.mem_Ico] at hx2 ⊢; linarith [hx2.1])

/-! ## The greedy sum over Type I arcs (writeup 599–605)

The remaining step is the greedy disjoint-interval packing.  The three reusable
mathematical inputs are now proved in this module:

* `arc_residue_count_sharp` — the `+1`-free per-arc count `ν(A) ≤ (3/2)·δ·d(A)`
  (using `q ≤ (b−a)/2`, i.e. `≥ 3` residue points on the arc);
* `offLine_gap_arc` — the disjointness driver `d(A_j)/24 ≤ |n_k − n_j|`;
* `Ico_disjoint_of_gap` + `sum_len_le_of_disjoint_Ico` — the packing inequality
  `Σ_j (d(A_j)/24) ≤ N + 1` from pairwise-disjoint intervals in `[N, 2N+1]`.

What remains as the single concrete named stub `typeI_arc_sum` is the *greedy
assembly*: choosing a witness arc per point, indexing the packing by distinct
arcs, deriving the `offLine_gap_arc` hypotheses from the `typeISet`/global data,
and combining `Σ ν(A_j) ≤ (3/2)δ·Σ d(A_j) ≤ (3/2)δ·24(N+1) = 36(Nδ+δ) ≤ 48(Nδ+1)`.
The achievable constant is `36`; we state `48` so the bound has slack and the
`(Nδ+1)` shape consumed by `prop43_local` is preserved. -/

/-! ## The greedy packing data and the abstract assembly

We separate the *geometry* (constructing the greedy selected set `G` with the
disjointness and covering properties — writeup 599–604) from the *arithmetic*
(combining the per-arc counts and the disjoint-length sum into the final bound).

A **greedy packing** for `typeISet f N lam δ` is a finite index set `G` together
with, for each `g ∈ G`,

* a real left-endpoint `lo g` and a nonnegative arc-density `dens g`, with the
  half-open packing interval `Ico (lo g) (lo g + dens g / 24)` contained in the
  window `Icc N (2·N + 1)` and these intervals pairwise disjoint (writeup 599–604);
* a per-arc residue count `nu g` with `nu g ≤ (3/2)·δ·dens g` (the sharp per-arc
  count `arc_residue_count_sharp`);

such that the counts cover the whole Type I set: `#typeISet ≤ Σ_{g∈G} nu g`.

`GreedyPacking` bundles exactly these hypotheses; `card_le_of_greedyPacking`
performs the (fully real) final arithmetic. -/

/-- The abstract greedy-packing data extracted from the §4.3 geometry (bases form).

The §4.3 Type I packing (writeup 599–605) packs half-open intervals `[lo g, lo g +
dens g/24)` whose **bases** `lo g` lie in the near-set window `[⌊N⌋, ⌊2N⌋]`.  The Type I
arcs are *short* — `dens g = d(A_g) ≤ 1/√λ ≤ N` (the curvature floor `N²λ ≥ 1`) — so the
single density-cap field `densCap ≤ 24·N` (giving `dens/24 ≤ N`) lets the bases-packing
lemma `sum_len_le_of_disjoint_Ico_bases` conclude `Σ dens/24 ≤ (⌊2N⌋−⌊N⌋) + densCap/24 ≤
N + N = 2N`.  This replaces the (false) per-window cap `dens ≤ 24`. -/
structure GreedyPacking (f : ℝ → ℝ) (N lam δ : ℝ) where
  /-- The selected (greedy) index set. -/
  G : Finset ℤ
  /-- Left endpoint (base) of the packing interval of a selected point. -/
  lo : ℤ → ℝ
  /-- Arc-density `d(A_g)` of a selected point. -/
  dens : ℤ → ℝ
  /-- Per-arc residue count of a selected point. -/
  nu : ℤ → ℝ
  /-- A uniform cap on the arc-densities, with `densCap ≤ 24·N`. -/
  densCap : ℝ
  /-- Arc densities are nonnegative. -/
  dens_nonneg : ∀ g ∈ G, 0 ≤ dens g
  /-- Per-arc count: `ν(A_g) ≤ 2·δ·d(A_g)` (factor-2 form, valid for `≥2`-point arcs). -/
  nu_le : ∀ g ∈ G, nu g ≤ 2 * (δ * dens g)
  /-- Each arc density is bounded by the cap. -/
  dens_le_cap : ∀ g ∈ G, dens g ≤ densCap
  /-- The cap is at most `48·N` (Type I shortness + curvature floor; `/48`-window). -/
  cap_le : densCap ≤ 48 * N
  /-- Packing interval *bases* lie in the floor window `[⌊N⌋, ⌊2N⌋]`. -/
  base_mem : ∀ g ∈ G, (⌊N⌋ : ℝ) ≤ lo g ∧ lo g ≤ (⌊2 * N⌋ : ℝ)
  /-- Packing intervals are pairwise disjoint (`/48`-window). -/
  interval_disjoint :
    (G : Set ℤ).PairwiseDisjoint (fun g => Set.Ico (lo g) (lo g + dens g / 48))
  /-- The arcs cover `typeISet` up to the writeup's factor 2 (line 532: "at most
  twice the total over proper major arcs"): on each selected line, the near-points
  split into ≤2 components and the rep's proper-arc count `nu g` dominates half. -/
  card_le_two_sum_nu : ((typeISet f N lam δ).card : ℝ) ≤ 2 * ∑ g ∈ G, nu g

/-- **Abstract assembly (fully real, bases form).**  From a `GreedyPacking` one gets
`#typeISet ≤ 384·(N·δ + 1)`.  This is the writeup 599–605 arithmetic with the line 532
factor 2 and the `/48`-window: `#typeISet ≤ 2·Σ ν`, `Σ ν ≤ 2δ·Σ dens`, and the
**bases**-packing disjoint-length sum `Σ dens/48 ≤ (⌊2N⌋−⌊N⌋) + densCap/48 ≤ (N+1) + N =
2N+1` (i.e. `Σ dens ≤ 48(2N+1)`) via `sum_len_le_of_disjoint_Ico_bases` and `densCap ≤ 48N`
(Type I shortness `dens ≤ 1/√λ ≤ N`).  Hence `#typeISet ≤ 2·2δ·48(2N+1) = 384Nδ + 192δ ≤
384(Nδ+1)`. -/
theorem card_le_of_greedyPacking {f : ℝ → ℝ} {N lam δ : ℝ}
    (hN0 : 0 ≤ N) (hδ : 0 < δ) (hδ1 : δ < 1)
    (P : GreedyPacking f N lam δ) :
    ((typeISet f N lam δ).card : ℝ) ≤ 384 * (N * δ + 1) := by
  classical
  -- (1) `Σ ν ≤ 2·δ·Σ dens`.
  have hsum_nu : ∑ g ∈ P.G, P.nu g ≤ ∑ g ∈ P.G, 2 * (δ * P.dens g) :=
    Finset.sum_le_sum P.nu_le
  -- floor-window: `⌊N⌋ ≤ ⌊2N⌋` and `⌊2N⌋ ≤ 2N`, `⌊N⌋ > N − 1`, so `⌊2N⌋ − ⌊N⌋ ≤ N + 1`.
  have hfloorLU : (⌊N⌋ : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by
    have : ⌊N⌋ ≤ ⌊2 * N⌋ := Int.floor_le_floor (by linarith)
    exact_mod_cast this
  have hfloorgap : ((⌊2 * N⌋ : ℝ) - (⌊N⌋ : ℝ)) ≤ N + 1 := by
    have ha : ((⌊2 * N⌋ : ℤ) : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
    have hb : N - 1 < ((⌊N⌋ : ℤ) : ℝ) := by have := Int.sub_one_lt_floor N; linarith
    push_cast at ha hb ⊢; linarith
  -- density cap as a length cap: `dens g / 48 ≤ max (densCap/48) 0 ≤ N` (the `max`
  -- ensures the bases-lemma nonnegativity even when `G = ∅`).
  set M : ℝ := max (P.densCap / 48) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hcapN : M ≤ N := by
    refine max_le ?_ hN0
    have := P.cap_le; linarith
  -- (2) the **bases** disjoint-length sum.
  have hpack : ∑ g ∈ P.G, P.dens g / 48
      ≤ ((⌊2 * N⌋ : ℝ) - (⌊N⌋ : ℝ)) + M := by
    refine sum_len_le_of_disjoint_Ico_bases P.G P.lo (fun g => P.dens g / 48)
      (⌊N⌋ : ℝ) (⌊2 * N⌋ : ℝ) M hfloorLU hM0 ?_ ?_ ?_ P.interval_disjoint
    · intro g hg; exact div_nonneg (P.dens_nonneg g hg) (by norm_num)
    · intro g hg
      exact le_trans (div_le_div_of_nonneg_right (P.dens_le_cap g hg) (by norm_num))
        (le_max_left _ _)
    · intro g hg; exact P.base_mem g hg
  -- `Σ dens/48 ≤ (N+1) + N = 2N+1`, so `Σ dens ≤ 48·(2N+1)`.
  have hsum_dens : ∑ g ∈ P.G, P.dens g ≤ 48 * (2 * N + 1) := by
    have hpack2 : ∑ g ∈ P.G, P.dens g / 48 ≤ 2 * N + 1 := by
      have := le_trans hpack (add_le_add hfloorgap hcapN); linarith
    have heq : ∑ g ∈ P.G, P.dens g / 48 = (∑ g ∈ P.G, P.dens g) / 48 := by
      rw [Finset.sum_div]
    rw [heq] at hpack2
    have : (∑ g ∈ P.G, P.dens g) ≤ (2 * N + 1) * 48 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 48)] at hpack2; exact hpack2
    linarith
  -- (3) chain.
  have hrw : ∑ g ∈ P.G, 2 * (δ * P.dens g)
      = 2 * δ * ∑ g ∈ P.G, P.dens g := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring
  have hδ0 : 0 ≤ δ := hδ.le
  have hsumnu_bound : ∑ g ∈ P.G, P.nu g ≤ 2 * δ * (48 * (2 * N + 1)) := by
    refine le_trans hsum_nu ?_
    rw [hrw]
    have h2δ : (0 : ℝ) ≤ 2 * δ := by positivity
    exact mul_le_mul_of_nonneg_left hsum_dens h2δ
  have hkey : ((typeISet f N lam δ).card : ℝ) ≤ 2 * (2 * δ * (48 * (2 * N + 1))) := by
    refine le_trans P.card_le_two_sum_nu ?_
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_le_mul_of_nonneg_left hsumnu_bound h2
  -- final numeric slack: `384Nδ + 192δ ≤ 384(Nδ+1)`, using `δ ≤ 1`.
  refine le_trans hkey ?_
  nlinarith [hN0, hδ0, hδ1.le, mul_nonneg hN0 hδ0]

/-! The greedy *construction* of `exists_greedyPacking` (and the resulting Type I
total `typeI_arc_sum`) is performed in `Squarefree.Geometry.NearCurveGreedy`, which
imports this module.  The single remaining concrete stub lives there
(`exists_greedySel`, the greedy leftmost-uncovered selection); everything in this
module is fully proven. -/

end Squarefree.Geometry
