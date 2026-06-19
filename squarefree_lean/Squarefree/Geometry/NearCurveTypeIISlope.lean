import Squarefree.Geometry.NearCurveTypeIIBase
import Squarefree.Geometry.NearCurveStrip
import Squarefree.Geometry.NearCurveAux
import Mathlib

/-!
# §4.3 Type II — slope localization (writeup 626–650)

The MVT slope-localization machinery (`typeII_slope_localized`) and the reduced
fraction count `slopeNum_image_card_le`.  Split out of `NearCurveTypeII`.
-/

open Classical Finset

namespace Squarefree.Geometry

open Squarefree Squarefree.Counting

variable {f : ℝ → ℝ} {N lam δ : ℝ}

/-! ## §4.3 slope-localization machinery -/

/-- Near-set coordinates live in the curvature window `[N/2, 5N/2]`. -/
theorem nearCoord_mem_Icc {p : ℤ} (hN2 : 2 ≤ N) (hp : p ∈ nearSet f N δ) :
    (p : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) := by
  rw [mem_nearSet] at hp
  obtain ⟨⟨hlo, hhi⟩, _⟩ := hp
  have hloR : (⌊N⌋ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo
  have hhiR : (p : ℝ) ≤ (⌊2 * N⌋ : ℝ) := by exact_mod_cast hhi
  have hflo : N - 1 < (⌊N⌋ : ℝ) := by have := Int.sub_one_lt_floor N; linarith
  have hfhi : (⌊2 * N⌋ : ℝ) ≤ 2 * N := Int.floor_le (2 * N)
  exact ⟨by linarith, by linarith⟩

/-- For an `OnLine` near-set point `p`, the line-residual is small: `|g(p)| ≤ δ`. -/
private theorem lineResNear_le {D : MajorLine} {p : ℤ}
    (hp : p ∈ nearSet f N δ) (hon : OnLine f D p) :
    |lineRes f D (p : ℝ)| ≤ δ := by
  rw [lineRes, lineVal_eq_latticeY hon]
  exact nearSet_dist_le hp

/-- `(D.slope : ℝ) = (D.slope.num : ℝ) / (D.denom : ℝ)` (the line's reduced slope). -/
private theorem slope_cast_eq (D : MajorLine) :
    ((D.slope : ℝ)) = (D.slope.num : ℝ) / (D.denom : ℝ) := by
  rw [MajorLine.denom]
  push_cast
  exact_mod_cast Rat.cast_def (K := ℝ) (D.slope)

/-- **Type II long-arc property** (writeup 608–610).  A Type II witness line `D`
has a *long* proper arc: `δ·√(q/λ) < properHi' − properLo'`.  Because `D` carries
the `OnMajorArc` collinear triple `a < n < b` of a point `n ∉ OnTypeIArc`, the arc
cannot be short (else `OnTypeIArc n` would hold via this very `D`). -/
theorem typeII_longArc {D : MajorLine} (hD : D ∈ typeIILines f N lam δ) :
    δ * Real.sqrt ((D.denom : ℝ) / (256 * lam))
      < (properHi' f N δ D : ℝ) - (properLo' f N δ D : ℝ) := by
  obtain ⟨n, hn, hDn⟩ := mem_typeIILines.mp hD
  obtain ⟨a, b, haN, hbN, hnN, han, hnb, hoa, hon, hob, hq⟩ := witnessII_spec hn
  have hnotI : ¬ OnTypeIArc f N lam δ n := (mem_typeIISet.mp hn).2
  by_contra hle
  push Not at hle
  -- `hle : properHi' − properLo' ≤ δ·√(q/λ)` ⟹ `OnTypeIArc n` via this `D`.
  apply hnotI
  refine ⟨witnessLineII f N δ n, a, b, haN, hbN, hnN, han, hnb, hoa, hon, hob, hq, ?_⟩
  rw [hDn]
  exact hle

/-- **Slope localization** (writeup 644–648).  Every Type II witness line `D`,
on the MVT side, has its slope within `2√(λ/q)` of some `f'(ξ)` with `ξ` in the
proper-arc span (so in `[N/2, 5N/2]`); transferring to the reference point `N`
(`|f''| ≤ 2λ`) gives `|D.slope − f'(N)| ≤ 3Nλ + 2√(λ/q)`. -/
theorem typeII_slope_localized (hf : ContDiff ℝ 2 f) (hlam : 0 < lam)
    (hδ : 0 < δ) (hN2 : 2 ≤ N)
    (hlower : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), lam ≤ |iteratedDeriv 2 f x|)
    (hupper : ∀ x ∈ Set.Icc (N / 2) (5 * N / 2), |iteratedDeriv 2 f x| ≤ 256 * lam)
    {D : MajorLine} (hD : D ∈ typeIILines f N lam δ) :
    |(D.slope : ℝ) - deriv f N| ≤ 384 * N * lam + 32 * Real.sqrt (lam / (D.denom : ℝ)) := by
  classical
  have _ := hlower
  have hqZ : 0 < D.denom := D.denom_pos
  have hqR : (0 : ℝ) < (D.denom : ℝ) := by exact_mod_cast hqZ
  -- arc is nonempty (≥2 points).
  have h2 : 2 ≤ (properArc' f N δ D).card := two_le_properArc'II hD
  have hne : (properArc' f N δ D).Nonempty := Finset.card_pos.mp (by omega)
  set lo : ℤ := properLo' f N δ D with hlodef
  set hi : ℤ := properHi' f N δ D with hhidef
  have hlomem := properLo'_mem (D := D) hne
  have hhimem := properHi'_mem (D := D) hne
  rw [← hlodef] at hlomem; rw [← hhidef] at hhimem
  obtain ⟨hloNear, hloOn, _, _⟩ := mem_properArc'_facts hlomem
  obtain ⟨hhiNear, hhiOn, _, _⟩ := mem_properArc'_facts hhimem
  -- the long-arc lower bound and span (tightened split `δ√(q/(256λ))`).
  have hlong : δ * Real.sqrt ((D.denom : ℝ) / (256 * lam)) < (hi : ℝ) - (lo : ℝ) :=
    typeII_longArc hD
  set L : ℝ := (hi : ℝ) - (lo : ℝ) with hLdef
  have hWnn : (0 : ℝ) ≤ δ * Real.sqrt ((D.denom : ℝ) / (256 * lam)) := by positivity
  have hLpos : 0 < L := lt_of_le_of_lt hWnn hlong
  have hlohiR : (lo : ℝ) < (hi : ℝ) := by rw [hLdef] at hLpos; linarith
  -- `|g(lo)|, |g(hi)| ≤ δ`.
  have hglo : |lineRes f D (lo : ℝ)| ≤ δ :=
    lineResNear_le hloNear hloOn
  have hghi : |lineRes f D (hi : ℝ)| ≤ δ :=
    lineResNear_le hhiNear hhiOn
  -- MVT: `∃ ξ ∈ (lo, hi)`, `|f'(ξ) − r/q| ≤ 2δ/L`.
  obtain ⟨ξ, hξ, hξeq⟩ := lineRes_mvt (D := D) hf hlohiR
  have hξIcc : ξ ∈ Set.Icc (lo : ℝ) (hi : ℝ) := ⟨hξ.1.le, hξ.2.le⟩
  have hgξ : |deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ)| ≤ 2 * δ / L := by
    have hval : deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ)
        = (lineRes f D (hi : ℝ) - lineRes f D (lo : ℝ)) / L := by
      rw [hξeq, hLdef]
      rw [mul_comm, mul_div_assoc]
      rw [div_self (by linarith : ((hi : ℝ) - (lo : ℝ)) ≠ 0)]
      rw [mul_one]
    rw [hval, abs_div, abs_of_pos hLpos]
    rw [div_le_div_iff_of_pos_right hLpos]
    calc |lineRes f D (hi : ℝ) - lineRes f D (lo : ℝ)|
        ≤ |lineRes f D (hi : ℝ)| + |lineRes f D (lo : ℝ)| := abs_sub _ _
      _ ≤ δ + δ := by linarith
      _ = 2 * δ := by ring
  -- `2δ/L < 32√(λ/q)` from `L > δ√(q/(256λ))`.
  have hslope_sqrt : 2 * δ / L < 32 * Real.sqrt (lam / (D.denom : ℝ)) := by
    -- `δ√(q/(256λ)) < L`, both positive ⟹ `2δ/L < 2δ/(δ√(q/(256λ))) = 2√(256λ/q) = 32√(λ/q)`.
    have hWpos : 0 < δ * Real.sqrt ((D.denom : ℝ) / (256 * lam)) := by
      have hsq : 0 < Real.sqrt ((D.denom : ℝ) / (256 * lam)) :=
        Real.sqrt_pos.mpr (by positivity)
      positivity
    have hstep : 2 * δ / L < 2 * δ / (δ * Real.sqrt ((D.denom : ℝ) / (256 * lam))) := by
      apply div_lt_div_of_pos_left (by positivity) hWpos hlong
    refine lt_of_lt_of_le hstep (le_of_eq ?_)
    -- `2δ/(δ√(q/(256λ))) = 2/√(q/(256λ)) = 2√(256λ/q) = 32√(λ/q)`.
    have hsqrtne : Real.sqrt ((D.denom : ℝ) / (256 * lam)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    -- `√(q/(256λ))⁻¹ = √(256λ/q) = 16·√(λ/q)`.
    have hinv : (Real.sqrt ((D.denom : ℝ) / (256 * lam)))⁻¹
        = 16 * Real.sqrt (lam / (D.denom : ℝ)) := by
      rw [← Real.sqrt_inv, inv_div]
      rw [show (256 * lam) / (D.denom : ℝ) = 256 * (lam / (D.denom : ℝ)) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 256)]
      rw [show Real.sqrt 256 = 16 by
        rw [show (256:ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [show 2 * δ / (δ * Real.sqrt ((D.denom : ℝ) / (256 * lam)))
        = 2 * (Real.sqrt ((D.denom : ℝ) / (256 * lam)))⁻¹ by
      field_simp]
    rw [hinv]; ring
  -- transfer `f'(ξ) → f'(N)` via the Lipschitz bound: `|f'(ξ)−f'(N)| ≤ 2λ|ξ−N|`.
  -- arc endpoints lie in `[N/2, 5N/2]`, so `ξ ∈ [lo, hi] ⊆ [N/2, 5N/2]`.
  have hloIcc : (lo : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) :=
    nearCoord_mem_Icc hN2 hloNear
  have hhiIcc : (hi : ℝ) ∈ Set.Icc (N / 2) (5 * N / 2) :=
    nearCoord_mem_Icc hN2 hhiNear
  have hξwin : ξ ∈ Set.Icc (N / 2) (5 * N / 2) :=
    ⟨le_trans hloIcc.1 hξIcc.1, le_trans hξIcc.2 hhiIcc.2⟩
  have hNwin : N ∈ Set.Icc (N / 2) (5 * N / 2) := by
    constructor <;> [linarith; linarith]
  have htrans : |deriv f ξ - deriv f N| ≤ 384 * N * lam := by
    have h1 := abs_deriv_sub_le hf hupper hξwin hNwin
    have h2 : |ξ - N| ≤ 3 * N / 2 := by
      rw [abs_le]; constructor <;> [linarith [hξwin.1, hξwin.2]; linarith [hξwin.1, hξwin.2]]
    calc |deriv f ξ - deriv f N| ≤ 256 * lam * |ξ - N| := h1
      _ ≤ 256 * lam * (3 * N / 2) := by apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 384 * N * lam := by ring
  -- combine: `|slope − f'(N)| ≤ |slope − f'(ξ)| + |f'(ξ) − f'(N)|`.
  have hslope_eq : (D.slope : ℝ) = (D.slope.num : ℝ) / (D.denom : ℝ) := slope_cast_eq D
  have hgξ' : |(D.slope : ℝ) - deriv f ξ| ≤ 32 * Real.sqrt (lam / (D.denom : ℝ)) := by
    rw [hslope_eq]
    have : |(D.slope.num : ℝ) / (D.denom : ℝ) - deriv f ξ|
        = |deriv f ξ - (D.slope.num : ℝ) / (D.denom : ℝ)| := abs_sub_comm _ _
    rw [this]
    linarith [hgξ, hslope_sqrt]
  calc |(D.slope : ℝ) - deriv f N|
      ≤ |(D.slope : ℝ) - deriv f ξ| + |deriv f ξ - deriv f N| := by
        have := abs_sub_le (D.slope : ℝ) (deriv f ξ) (deriv f N); linarith
    _ ≤ 32 * Real.sqrt (lam / (D.denom : ℝ)) + 384 * N * lam := by linarith [hgξ', htrans]
    _ = 384 * N * lam + 32 * Real.sqrt (lam / (D.denom : ℝ)) := by ring

/-! ## §4.3 fraction count -/

/-- **Fraction count** (writeup 644–650).  For `0 < q`, the reduced rationals of
denominator `q` whose value lies in `[α, β]` are indexed by their numerators, which
fall in `Icc ⌈qα⌉ ⌊qβ⌋`; hence there are `≤ q(β − α) + 1` of them.  Stated as: the
image of a finset `s` of `MajorLine`s of fixed `denom q` with all slopes in `[α, β]`
under `D ↦ D.slope.num` has cardinality `≤ q(β − α) + 1`. -/
theorem slopeNum_image_card_le {α β : ℝ} {q : ℤ} (hq : 0 < q) (hab : α ≤ β)
    (s : Finset MajorLine)
    (hden : ∀ D ∈ s, D.denom = q)
    (hslope : ∀ D ∈ s, α ≤ (D.slope : ℝ) ∧ (D.slope : ℝ) ≤ β) :
    ((s.image (fun D => D.slope.num)).card : ℝ) ≤ (q : ℝ) * (β - α) + 1 := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- every image numerator lies in `Icc ⌈qα⌉ ⌊qβ⌋`.
  have hsub : s.image (fun D => D.slope.num) ⊆ Finset.Icc ⌈(q : ℝ) * α⌉ ⌊(q : ℝ) * β⌋ := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨D, hD, hrD⟩ := hr
    subst hrD
    have hqd : D.denom = q := hden D hD
    obtain ⟨hαle, hleβ⟩ := hslope D hD
    have hslopeeq : (D.slope : ℝ) = (D.slope.num : ℝ) / (q : ℝ) := by
      rw [slope_cast_eq D, hqd]
    rw [Finset.mem_Icc]
    have hnumeq : (D.slope.num : ℝ) = (q : ℝ) * (D.slope : ℝ) := by
      rw [hslopeeq]; field_simp
    constructor
    · -- `⌈qα⌉ ≤ r`: `qα ≤ q·slope = r`.
      have : (q : ℝ) * α ≤ (D.slope.num : ℝ) := by
        rw [hnumeq]; exact mul_le_mul_of_nonneg_left hαle hqR.le
      exact Int.ceil_le.mpr (by exact_mod_cast this)
    · -- `r ≤ ⌊qβ⌋`: `r = q·slope ≤ qβ`.
      have : (D.slope.num : ℝ) ≤ (q : ℝ) * β := by
        rw [hnumeq]; exact mul_le_mul_of_nonneg_left hleβ hqR.le
      exact Int.le_floor.mpr (by exact_mod_cast this)
  have hcard : (s.image (fun D => D.slope.num)).card
      ≤ (Finset.Icc ⌈(q : ℝ) * α⌉ ⌊(q : ℝ) * β⌋).card := Finset.card_le_card hsub
  have hcardR : ((s.image (fun D => D.slope.num)).card : ℝ)
      ≤ ((Finset.Icc ⌈(q : ℝ) * α⌉ ⌊(q : ℝ) * β⌋).card : ℝ) := by exact_mod_cast hcard
  -- `(⌊qβ⌋ + 1 − ⌈qα⌉).toNat ≤ qβ − qα + 1`.
  have hub : ((⌊(q : ℝ) * β⌋ + 1 - ⌈(q : ℝ) * α⌉).toNat : ℝ) ≤ (q : ℝ) * (β - α) + 1 := by
    have hfl : (⌊(q : ℝ) * β⌋ : ℝ) ≤ (q : ℝ) * β := Int.floor_le _
    have hcl : (q : ℝ) * α ≤ (⌈(q : ℝ) * α⌉ : ℝ) := Int.le_ceil _
    have hqβα : (0 : ℝ) ≤ (q : ℝ) * (β - α) := by apply mul_nonneg hqR.le; linarith
    by_cases hpos : 0 ≤ ⌊(q : ℝ) * β⌋ + 1 - ⌈(q : ℝ) * α⌉
    · have hcast : ((⌊(q : ℝ) * β⌋ + 1 - ⌈(q : ℝ) * α⌉).toNat : ℝ)
          = (⌊(q : ℝ) * β⌋ : ℝ) + 1 - (⌈(q : ℝ) * α⌉ : ℝ) := by
        rw [show ((⌊(q : ℝ) * β⌋ + 1 - ⌈(q : ℝ) * α⌉).toNat : ℝ)
            = (((⌊(q : ℝ) * β⌋ + 1 - ⌈(q : ℝ) * α⌉).toNat : ℤ) : ℝ) by push_cast; ring,
          Int.toNat_of_nonneg hpos]
        push_cast; ring
      rw [hcast]; nlinarith [hfl, hcl]
    · rw [Int.toNat_of_nonpos (by omega)]
      push_cast; linarith
  have hcardeq : (Finset.Icc ⌈(q : ℝ) * α⌉ ⌊(q : ℝ) * β⌋).card
      = (⌊(q : ℝ) * β⌋ + 1 - ⌈(q : ℝ) * α⌉).toNat := by rw [Int.card_Icc]
  rw [hcardeq] at hcardR
  linarith [hcardR, hub]

end Squarefree.Geometry
