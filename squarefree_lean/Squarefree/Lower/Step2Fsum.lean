import Squarefree.Lower.Step2Count
import Squarefree.Lower.PairWeightSum

/-!
# §5 Step-2 `f`-sum assembly (writeup 921–949)

`Ra_step2_fsum` turns the per-`f` BANDS bound `Ra_step2_count` into a per-pair Step-2 count by
partitioning the triple set by the value `f = round(Qval …)` and summing the per-`f` bound across
`f ∈ Icc (-N) N`.  As in Step 3, the fiberwise partition collapses by `±`-symmetry to twice the
half-sum over `1 ≤ n ≤ N`.  The three half-sum pieces

* `∑ 1 ≤ N`, `∑ |f| = ∑ n ≤ N²` (the `T_f = κ|f|` term),
* `∑ 1/√n ≤ 2√N` (the `√(4δ/(κf))` term, via the `√`-telescope)

give the clean 4-term shape

`#F ≤ C₂·(R·δ₂₃·N + 2·R·√(δ₂₃/κ)·√N + κ·N² + N)`,

with `κ = D⁴/(X·A)`, `δ₂₃ = Δ²·G·U²⁰/(H·Ω⁶)` and the absolute constant `C₂ := 10³⁵` absorbing
`186·10³¹`, the BANDS factor `4`, `√4 = 2` and the `±`-symmetry `2`.  The fiber threshold
`10⁹⁰·L ≤ |round(Qval)|` discharges `Ra_step2_count`'s `hflarge` per surviving fiber.
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- Reciprocal-`√` telescope: for `i ≥ 1`, `1/√i ≤ 2(√i − √(i−1))`.  Follows from
`2(√i − √(i−1)) = 2/(√i + √(i−1)) ≥ 2/(2√i) = 1/√i`. -/
private lemma recipsqrt_le_sqrt_telescope (i : ℕ) (hi : 1 ≤ i) :
    (1 : ℝ) / Real.sqrt i ≤ 2 * (Real.sqrt i - Real.sqrt (i - 1)) := by
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hipos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le one_pos hi1
  have hi1nonneg : (0 : ℝ) ≤ (i : ℝ) - 1 := by linarith
  set a := Real.sqrt i with ha
  set b := Real.sqrt ((i : ℝ) - 1) with hb
  have ha2 : a ^ 2 = (i : ℝ) := Real.sq_sqrt (le_of_lt hipos)
  have hb2 : b ^ 2 = (i : ℝ) - 1 := Real.sq_sqrt hi1nonneg
  have hanonneg : 0 ≤ a := Real.sqrt_nonneg _
  have hbnonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hapos : 0 < a := by
    have h2 : (0 : ℝ) < a ^ 2 := by rw [ha2]; exact hipos
    nlinarith [hanonneg]
  -- a² − b² = 1
  have hdiff : a ^ 2 - b ^ 2 = 1 := by rw [ha2, hb2]; ring
  -- b ≤ a
  have hba : b ≤ a := by rw [ha, hb]; exact Real.sqrt_le_sqrt (by linarith)
  have hsum_le : a + b ≤ 2 * a := by linarith
  -- (a−b)(a+b) = 1
  have hab1 : (a - b) * (a + b) = 1 := by nlinarith [hdiff]
  -- 1/(2a) ≤ a − b
  have key : (1 : ℝ) / (2 * a) ≤ a - b := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hab1, hsum_le, hapos, hba]
  -- 1/√i = 1/a = 2·(1/(2a)) ≤ 2(a−b)
  have h2a : (1 : ℝ) / a = 2 * (1 / (2 * a)) := by field_simp
  calc (1 : ℝ) / Real.sqrt i = 1 / a := by rw [ha]
    _ = 2 * (1 / (2 * a)) := h2a
    _ ≤ 2 * (a - b) := by linarith [key]

/-- `√`-harmonic upper bound: `∑_{n=1}^N 1/√n ≤ 2√N`. -/
private lemma sqrt_harmonic_le_two_sqrt (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt n) ≤ 2 * Real.sqrt N := by
  have hreindex :
      (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt n)
        = ∑ i ∈ Finset.range N, (1 : ℝ) / Real.sqrt (i + 1) := by
    rw [← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    push_cast; ring
  rw [hreindex]
  have hterm : ∀ i ∈ Finset.range N,
      (1 : ℝ) / Real.sqrt (i + 1) ≤ 2 * (Real.sqrt (i + 1) - Real.sqrt i) := by
    intro i _
    have h := recipsqrt_le_sqrt_telescope (i + 1) (Nat.le_add_left 1 i)
    have e2 : ((i + 1 : ℕ) : ℝ) - 1 = (i : ℝ) := by push_cast; ring
    have e1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [e2, e1] at h
    exact h
  have hsum_le :
      (∑ i ∈ Finset.range N, (1 : ℝ) / Real.sqrt (i + 1))
        ≤ ∑ i ∈ Finset.range N, 2 * (Real.sqrt (i + 1) - Real.sqrt i) :=
    Finset.sum_le_sum hterm
  refine le_trans hsum_le ?_
  have htel :
      (∑ i ∈ Finset.range N, 2 * (Real.sqrt (i + 1) - Real.sqrt i))
        = 2 * Real.sqrt N := by
    have hcongr :
        (∑ i ∈ Finset.range N, 2 * (Real.sqrt (i + 1) - Real.sqrt i))
          = ∑ i ∈ Finset.range N,
              ((fun n : ℕ => 2 * Real.sqrt n) (i + 1) - (fun n : ℕ => 2 * Real.sqrt n) i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only
      push_cast
      ring
    rw [hcongr, Finset.sum_range_sub (fun n : ℕ => 2 * Real.sqrt n) N]
    simp [Real.sqrt_zero]
  rw [htel]

/-- Gauss-sum bound over `Icc 1 N`: `∑_{n=1}^N n ≤ N²` (in `ℝ`). -/
private lemma step2_gauss_sum_le_sq (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    push_cast
    nlinarith [ih, hk]

/-- **Step-2 half-sum bound (BANDS).**  The per-`f` BANDS weight summed over `1 ≤ n ≤ N`:
`∑ (R·(4δ + √(4δ/(κn))) + κn + 1) ≤ R·4δ·N + 4·R·√(δ/κ)·√N + κ·N² + N`. -/
private lemma step2_fsum_half (κ δ R : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hR : 0 ≤ R) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (R * (4 * δ + Real.sqrt (4 * δ / (κ * (n : ℝ)))) + κ * (n : ℝ) + 1))
      ≤ R * (4 * δ) * (N : ℝ) + 4 * R * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ)
          + κ * (N : ℝ) ^ 2 + (N : ℝ) := by
  -- split the sum into four pieces
  have hsplit : (∑ n ∈ Finset.Icc 1 N,
        (R * (4 * δ + Real.sqrt (4 * δ / (κ * (n : ℝ)))) + κ * (n : ℝ) + 1))
      = (∑ n ∈ Finset.Icc 1 N, R * (4 * δ))
        + (∑ n ∈ Finset.Icc 1 N, R * Real.sqrt (4 * δ / (κ * (n : ℝ))))
        + (∑ n ∈ Finset.Icc 1 N, κ * (n : ℝ))
        + (∑ _n ∈ Finset.Icc 1 N, (1 : ℝ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsplit]
  -- piece 1: ∑ R·4δ = R·4δ·N
  have hp1 : (∑ n ∈ Finset.Icc 1 N, R * (4 * δ)) = R * (4 * δ) * (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  -- piece 3: ∑ κn ≤ κ·N²
  have hp3 : (∑ n ∈ Finset.Icc 1 N, κ * (n : ℝ)) ≤ κ * (N : ℝ) ^ 2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (step2_gauss_sum_le_sq N) hκ.le
  -- piece 4: ∑ 1 = N
  have hp4 : (∑ _n ∈ Finset.Icc 1 N, (1 : ℝ)) = (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  -- piece 2: ∑ R·√(4δ/(κn)) = R·√(4δ/κ)·∑ 1/√n ≤ R·√(4δ/κ)·2√N = 4·R·√(δ/κ)·√N
  have hp2 : (∑ n ∈ Finset.Icc 1 N, R * Real.sqrt (4 * δ / (κ * (n : ℝ))))
      ≤ 4 * R * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ) := by
    -- rewrite each √(4δ/(κn)) = √(4δ/κ)·(1/√n)
    have hrw : (∑ n ∈ Finset.Icc 1 N, R * Real.sqrt (4 * δ / (κ * (n : ℝ))))
        = R * Real.sqrt (4 * δ / κ) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (n : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
      have hfac : (4 * δ / (κ * (n : ℝ))) = (4 * δ / κ) * (1 / (n : ℝ)) := by
        field_simp
      rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_div' 1 (by norm_num),
        Real.sqrt_one]
      ring
    rw [hrw]
    -- √(4δ/κ) = 2·√(δ/κ)
    have hsqrt4 : Real.sqrt (4 * δ / κ) = 2 * Real.sqrt (δ / κ) := by
      rw [show (4 * δ / κ) = 4 * (δ / κ) by ring, Real.sqrt_mul (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt4]
    have hRsq : 0 ≤ R * (2 * Real.sqrt (δ / κ)) := by positivity
    have hharm := sqrt_harmonic_le_two_sqrt N
    calc R * (2 * Real.sqrt (δ / κ)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (n : ℝ)
        ≤ R * (2 * Real.sqrt (δ / κ)) * (2 * Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hharm hRsq
      _ = 4 * R * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ) := by ring
  rw [hp1, hp4]
  linarith [hp2, hp3]

set_option maxHeartbeats 1600000 in
/-- **Step-2 per-pair count via fiberwise partition + `f`-sum.**  The fiber threshold
`10⁹⁰·L ≤ |round(Qval)|` (`L = ℓ₁ℓ₂(ℓ₂−ℓ₁)/(G·Ω⁵)`) discharges `Ra_step2_count`'s `hflarge`,
the `±`-symmetry collapses the `Icc(-N)N` sum to twice the half-sum, and the three half-sums
(`∑1`, `∑n`, `∑1/√n`) give the clean BANDS 4-term shape with absolute constant `C₂ = 10³⁵`. -/
theorem Ra_step2_fsum {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) (N : ℕ) :
    ((Ra.filter (fun r =>
        (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ (10:ℝ)^90 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
            / (P.G * S.Ω ^ 5)) ≤ |((round (Qval P a dStar ℓ₁ ℓ₂ r)):ℝ)|
        ∧ (round (Qval P a dStar ℓ₁ ℓ₂ r)).natAbs ≤ N)).card : ℝ)
      ≤ (10:ℝ)^35 * ( S.R * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) * (N:ℝ)
            + 2 * S.R * Real.sqrt ((S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / (S.D^4/(P.X*S.A)))
                * Real.sqrt (N:ℝ)
            + (S.D^4/(P.X*S.A)) * (N:ℝ)^2
            + (N:ℝ) ) := by
  -- abbreviations
  set κ : ℝ := S.D ^ 4 / (P.X * S.A) with hκdef
  set δ₂₃ : ℝ := S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6) with hδdef
  -- positivity facts
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hXpos := P.X_pos
  have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
  have hApos : (0 : ℝ) < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  have hδpos : 0 < δ₂₃ := by rw [hδdef]; positivity
  -- the threshold constant L
  set L : ℝ := (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
      / (P.G * S.Ω ^ 5)) with hLdef
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  have hLpos : (0 : ℝ) < L := by
    rw [hLdef]
    have hℓ1pos : (0:ℝ) < ((ℓ₁:ℤ):ℝ) := by linarith
    have hℓ2pos : (0:ℝ) < ((ℓ₂:ℤ):ℝ) := by linarith
    have hdiff : (0:ℝ) < ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by linarith
    positivity
  -- abbreviation for the round-value function
  set g : ℕ → ℤ := fun r => round (Qval P a dStar ℓ₁ ℓ₂ r) with hgdef
  -- the per-`f` predicate inside the filter
  set p : ℕ → Prop := fun r =>
      (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ (10:ℝ)^90 * L ≤ |((g r):ℝ)| ∧ (g r).natAbs ≤ N with hpdef
  classical
  -- the full filtered set
  set S2 : Finset ℕ := Ra.filter p with hS2def
  -- per-`f` weight `h₀`
  set h₀ : ℝ → ℝ := fun x =>
      186 * 10 ^ 31 * (S.R * (4 * δ₂₃ + Real.sqrt (4 * δ₂₃ / (x * κ))) + x * κ + 1) with hh0def
  -- ===== Step 1: every r ∈ S2 maps into Icc (-N) N under g =====
  have hmap : ∀ r ∈ S2, g r ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
    intro r hr
    rw [hS2def, Finset.mem_filter] at hr
    have hnatabs : (g r).natAbs ≤ N := hr.2.2.2.2
    rw [Finset.mem_Icc]
    have hle : |g r| ≤ (N:ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hnatabs
    constructor
    · linarith [abs_le.mp hle |>.1]
    · linarith [abs_le.mp hle |>.2]
  -- ===== Step 2: fiberwise card decomposition =====
  have hcard_eq : S2.card
      = ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (S2.filter (fun r => g r = f)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  -- ===== Step 3: per-fiber bound =====
  have hfiber : ∀ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      ((S2.filter (fun r => g r = f)).card : ℝ)
        ≤ (if f = 0 then 0 else h₀ |(f : ℝ)|) := by
    intro f hf
    by_cases hf0 : f = 0
    · -- empty fiber: the threshold conjunct forces |g r| > 0
      simp only [hf0, if_true]
      have hempty : S2.filter (fun r => g r = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro r hr
        rw [hS2def, Finset.mem_filter] at hr
        intro hgr0
        have hthr : (10:ℝ)^90 * L ≤ |((g r):ℝ)| := hr.2.2.2.1
        rw [hgr0] at hthr
        simp only [Int.cast_zero, abs_zero] at hthr
        have : (0:ℝ) < (10:ℝ)^90 * L := by positivity
        linarith
      rw [hempty]
      simp
    · -- nonempty / general fiber: bound by Ra_step2_count f
      simp only [hf0, if_false]
      set Ff : Finset ℕ := S2.filter (fun r => g r = f) with hFfdef
      rcases Finset.eq_empty_or_nonempty Ff with hFe | hFne
      · rw [hFe]
        simp only [Finset.card_empty, Nat.cast_zero]
        have hfRpos : 0 < |(f : ℝ)| := by
          have : (f : ℝ) ≠ 0 := by exact_mod_cast hf0
          positivity
        have : 0 ≤ h₀ |(f : ℝ)| := by
          rw [hh0def]
          have hpos : 0 ≤ S.R * (4 * δ₂₃ + Real.sqrt (4 * δ₂₃ / (|(f:ℝ)| * κ)))
              + |(f:ℝ)| * κ + 1 := by positivity
          positivity
        exact this
      · -- nonempty fiber: derive hflarge for this f, apply Ra_step2_count
        obtain ⟨r₀, hr₀⟩ := hFne
        rw [hFfdef, Finset.mem_filter, hS2def, Finset.mem_filter] at hr₀
        have hgr₀ : g r₀ = f := hr₀.2
        have hthr₀ : (10:ℝ)^90 * L ≤ |((g r₀):ℝ)| := hr₀.1.2.2.2.1
        -- translate to hflarge in f
        have hflarge : (10:ℝ) ^ 90 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ)
            * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) / (P.G * S.Ω ^ 5)) ≤ |(f : ℝ)| := by
          rw [← hLdef]
          rw [hgr₀] at hthr₀
          convert hthr₀ using 2
        -- the BANDS count for this f
        have hcount := Ra_step2_count (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W
          hflarge h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg Ra dStar hdStar
        -- Ff ⊆ the count filter set
        have hsub : Ff ⊆ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ round (Qval P a dStar ℓ₁ ℓ₂ r) = f) := by
          intro r hr
          rw [hFfdef, Finset.mem_filter, hS2def, Finset.mem_filter] at hr
          rw [Finset.mem_filter]
          refine ⟨hr.1.1, hr.1.2.1, hr.1.2.2.1, ?_⟩
          have : g r = f := hr.2
          rw [hgdef] at this; exact this
        have hcardle : (Ff.card : ℝ) ≤
            ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
              ∧ round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        -- chain into count bound; rewrite RHS as h₀ |f|
        rw [hh0def]
        have hfκ : |(f : ℝ)| * S.D ^ 4 / (P.X * S.A) = |(f:ℝ)| * κ := by
          rw [hκdef, mul_div_assoc]
        have hrwcount : 186 * 10 ^ 31 * (S.R * (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
              + Real.sqrt (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
                  / (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A))))
            + (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A)) + 1)
            = 186 * 10 ^ 31 * (S.R * (4 * δ₂₃ + Real.sqrt (4 * δ₂₃ / (|(f:ℝ)| * κ)))
                + |(f:ℝ)| * κ + 1) := by
          rw [hδdef, hfκ]
        rw [hrwcount] at hcount
        linarith [hcardle, hcount]
  -- ===== Step 4: sum the fiber bounds =====
  have hsumle : (S2.card : ℝ)
      ≤ ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (if f = 0 then 0 else h₀ |(f : ℝ)|) := by
    rw [hcard_eq, Nat.cast_sum]
    exact Finset.sum_le_sum hfiber
  -- ===== Step 5: ± symmetry =====
  have hsym : ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (if f = 0 then 0 else h₀ |(f : ℝ)|)
      = 2 * ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ) := by
    set k : ℤ → ℝ := fun f => if f = 0 then 0 else h₀ |(f : ℝ)| with hkdef
    have hkeven : ∀ f : ℤ, k (-f) = k f := by
      intro f
      rw [hkdef]
      by_cases hf0 : f = 0
      · simp [hf0]
      · have hnf0 : -f ≠ 0 := by simpa using hf0
        simp only [hf0, hnf0, if_false]
        congr 1
        push_cast
        rw [abs_neg]
    have hzero : k 0 = 0 := by rw [hkdef]; simp
    have hposeq : ∑ n ∈ Finset.Icc 1 N, k ((n : ℤ)) = ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := hn.1
      rw [hkdef]
      have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp only [hnz, if_false]
      congr 1
      have : (0:ℝ) ≤ ((n:ℤ):ℝ) := by positivity
      rw [abs_of_nonneg this]
      push_cast; ring
    have hnegset : (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f < 0)
        = (Finset.Icc (1:ℤ) (N:ℤ)).map ⟨fun n => -n, fun a b h => by simpa using h⟩ := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨hlo, _⟩, hneg⟩
        exact ⟨-f, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨n, ⟨hn1, hnN⟩, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hposset : (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => 0 < f)
        = Finset.Icc (1:ℤ) (N:ℤ) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hhi⟩, hpos⟩; exact ⟨by omega, hhi⟩
      · rintro ⟨hlo, hhi⟩; exact ⟨⟨by omega, hhi⟩, by omega⟩
    have hIccZN : ∑ f ∈ Finset.Icc (1:ℤ) (N:ℤ), k f = ∑ n ∈ Finset.Icc 1 N, k ((n:ℤ)) := by
      have hImg : Finset.Icc (1:ℤ) (N:ℤ)
          = (Finset.Icc 1 N).image (fun n : ℕ => (n : ℤ)) := by
        ext f
        simp only [Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨hlo, hhi⟩
          refine ⟨f.toNat, ⟨?_, ?_⟩, ?_⟩ <;> omega
        · rintro ⟨n, ⟨hn1, hnN⟩, rfl⟩
          exact ⟨by exact_mod_cast hn1, by exact_mod_cast hnN⟩
      rw [hImg, Finset.sum_image]
      intro x _ y _ h
      simpa using h
    have htri : ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), k f
        = (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f < 0), k f)
        + (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f = 0), k f)
        + (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => 0 < f), k f) := by
      have hsplit1 : ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), k f
          = (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f < 0), k f)
          + (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => ¬ f < 0), k f) :=
        (Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(N:ℤ)) (N:ℤ)) (fun f => f < 0) k).symm
      have hsplit2 : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => ¬ f < 0), k f
          = (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f = 0), k f)
          + (∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => 0 < f), k f) := by
        have h := (Finset.sum_filter_add_sum_filter_not
            ((Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => ¬ f < 0)) (fun f => f = 0) k).symm
        rw [h]
        congr 1
        · apply Finset.sum_congr _ (fun _ _ => rfl)
          ext f; simp only [Finset.mem_filter]; constructor
          · rintro ⟨⟨hmem, _⟩, hf0⟩; exact ⟨hmem, hf0⟩
          · rintro ⟨hmem, hf0⟩; exact ⟨⟨hmem, by omega⟩, hf0⟩
        · apply Finset.sum_congr _ (fun _ _ => rfl)
          ext f; simp only [Finset.mem_filter]; constructor
          · rintro ⟨⟨hmem, hnlt⟩, hne⟩; exact ⟨hmem, by omega⟩
          · rintro ⟨hmem, hpos⟩; exact ⟨⟨hmem, by omega⟩, by omega⟩
      rw [hsplit1, hsplit2, add_assoc]
    have hnegsum : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f < 0), k f
        = ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by
      rw [hnegset, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Function.Embedding.coeFn_mk]
      exact hkeven n
    have hzerosum : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f = 0), k f = 0 := by
      apply Finset.sum_eq_zero
      intro f hf
      rw [Finset.mem_filter] at hf
      rw [hf.2]; exact hzero
    have hpossum : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => 0 < f), k f
        = ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by
      rw [hposset]
    calc ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), k f
        = ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n + 0 + ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by
            rw [htri, hnegsum, hzerosum, hpossum]
      _ = 2 * ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by ring
      _ = 2 * ∑ n ∈ Finset.Icc 1 N, k ((n:ℤ)) := by rw [hIccZN]
      _ = 2 * ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ) := by rw [hposeq]
  rw [hsym] at hsumle
  -- ===== Step 6: apply step2_fsum_half =====
  -- the inner half-sum matches step2_fsum_half's LHS after factoring 186·10³¹
  have hinner : ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ)
      = 186 * 10 ^ 31 * ∑ n ∈ Finset.Icc 1 N,
          (S.R * (4 * δ₂₃ + Real.sqrt (4 * δ₂₃ / (κ * (n:ℝ)))) + κ * (n:ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [hh0def]
    rw [mul_comm (n:ℝ) κ]
  rw [hinner] at hsumle
  have hhalf := step2_fsum_half κ δ₂₃ S.R hκpos hδpos hRpos.le N
  -- chain
  have hfinal : (S2.card : ℝ)
      ≤ 2 * (186 * 10 ^ 31) * ( S.R * (4 * δ₂₃) * (N:ℝ)
          + 4 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
          + κ * (N:ℝ) ^ 2 + (N:ℝ) ) := by
    have hstep : 2 * (186 * 10 ^ 31 * ∑ n ∈ Finset.Icc 1 N,
          (S.R * (4 * δ₂₃ + Real.sqrt (4 * δ₂₃ / (κ * (n:ℝ)))) + κ * (n:ℝ) + 1))
        ≤ 2 * (186 * 10 ^ 31 * ( S.R * (4 * δ₂₃) * (N:ℝ)
            + 4 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
            + κ * (N:ℝ) ^ 2 + (N:ℝ) )) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hhalf (by norm_num)
    have heq : 2 * (186 * 10 ^ 31 * ( S.R * (4 * δ₂₃) * (N:ℝ)
          + 4 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
          + κ * (N:ℝ) ^ 2 + (N:ℝ) ))
        = 2 * (186 * 10 ^ 31) * ( S.R * (4 * δ₂₃) * (N:ℝ)
          + 4 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
          + κ * (N:ℝ) ^ 2 + (N:ℝ) ) := by ring
    rw [heq] at hstep
    linarith [hsumle, hstep]
  -- ===== Step 7: fold constants into 10³⁵ and match the target 4-term shape =====
  -- target RHS uses R·δ₂₃·N and 2·R·√(δ₂₃/κ)·√N; ours uses R·4δ₂₃·N and 4·R·√(δ₂₃/κ)·√N
  have hsqrtnn : 0 ≤ Real.sqrt (δ₂₃ / κ) := Real.sqrt_nonneg _
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hsqrtN : 0 ≤ Real.sqrt (N:ℝ) := Real.sqrt_nonneg _
  have hRHSrw : 2 * (186 * 10 ^ 31) * ( S.R * (4 * δ₂₃) * (N:ℝ)
        + 4 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
        + κ * (N:ℝ) ^ 2 + (N:ℝ) )
      ≤ (10:ℝ)^35 * ( S.R * δ₂₃ * (N:ℝ)
          + 2 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
          + κ * (N:ℝ) ^ 2 + (N:ℝ) ) := by
    -- termwise: every coefficient on the LHS is ≤ 10³⁵, and each term is ≥ 0
    have hRδN : 0 ≤ S.R * δ₂₃ * (N:ℝ) := by positivity
    have hsqterm : 0 ≤ 2 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ) := by positivity
    have hκN2 : 0 ≤ κ * (N:ℝ) ^ 2 := by positivity
    -- LHS = 2·186·10³¹·(4·(R·δ₂₃·N) + 2·(2·R·√(δ₂₃/κ)·√N) + (κN²) + N)
    have hLrw : 2 * (186 * 10 ^ 31) * ( S.R * (4 * δ₂₃) * (N:ℝ)
          + 4 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
          + κ * (N:ℝ) ^ 2 + (N:ℝ) )
        = 2 * (186 * 10 ^ 31) * 4 * (S.R * δ₂₃ * (N:ℝ))
          + 2 * (186 * 10 ^ 31) * 2 * (2 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ))
          + 2 * (186 * 10 ^ 31) * (κ * (N:ℝ) ^ 2)
          + 2 * (186 * 10 ^ 31) * (N:ℝ) := by ring
    have hRrw : (10:ℝ)^35 * ( S.R * δ₂₃ * (N:ℝ)
          + 2 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ)
          + κ * (N:ℝ) ^ 2 + (N:ℝ) )
        = (10:ℝ)^35 * (S.R * δ₂₃ * (N:ℝ))
          + (10:ℝ)^35 * (2 * S.R * Real.sqrt (δ₂₃ / κ) * Real.sqrt (N:ℝ))
          + (10:ℝ)^35 * (κ * (N:ℝ) ^ 2)
          + (10:ℝ)^35 * (N:ℝ) := by ring
    rw [hLrw, hRrw]
    have hc1 : 2 * (186 * 10 ^ 31) * 4 ≤ (10:ℝ)^35 := by norm_num
    have hc2 : 2 * (186 * 10 ^ 31) * 2 ≤ (10:ℝ)^35 := by norm_num
    have hc3 : 2 * (186 * 10 ^ 31 : ℝ) ≤ (10:ℝ)^35 := by norm_num
    have hb1 := mul_le_mul_of_nonneg_right hc1 hRδN
    have hb2 := mul_le_mul_of_nonneg_right hc2 hsqterm
    have hb3 := mul_le_mul_of_nonneg_right hc3 hκN2
    have hb4 := mul_le_mul_of_nonneg_right hc3 hNnn
    linarith [hb1, hb2, hb3, hb4]
  -- conclude: rewrite κ, δ₂₃ back
  have hchain := le_trans hfinal hRHSrw
  rw [hκdef, hδdef] at hchain
  exact hchain

end Squarefree
