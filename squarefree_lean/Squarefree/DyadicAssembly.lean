import Squarefree.Structure.ADecomp
import Squarefree.ShortDelta
import Squarefree.Opt.Global
import Squarefree.Opt.Strip

/-!
# §1 dyadic assembly

Glue lemma: combine the proved pieces — `prop_2_4` (short Δ), `a_decomposition` (Nair–Roth
reduction), `dblock_bound` / `dblock_small_omega` (per-Ω block bounds) — into the §1 key
estimate `#𝒟[D,2D] ≪ H/U` for a single dyadic scale `D` with `H/U ≪ D ≪ X^{1/2}`.

The two genuinely new ingredients here are:
* `dyadic_cover_sum` — a dyadic tiling: the `a`-sum `Σ_{a∈[t, t·2^{K+1}]}` is covered by the
  `K+1` blocks `Σ_{a∈[t·2^k, t·2^{k+1}]}`, because consecutive blocks adjoin (no integer gap);
* `log_le_rpow` — `log X ≤ ε⁻¹ X^ε`, which converts the `O(log X)` number-of-scales factor into a
  tiny `X^{ε}` power, absorbed by shrinking the result exponent below `dblock_bound`'s `u`.
-/

open Classical Finset

namespace Squarefree

namespace DyadicAssembly

/-- Dyadic tiling for a nonnegative integer-indexed function.  If `f ≥ 0`, `t > 0`, then the sum
over `[⌈t⌉, ⌊t·2^{K+1}⌋]` is at most the sum of the `K+1` dyadic blocks `[⌈t·2^k⌉, ⌊t·2^{k+1}⌋]`.
The blocks adjoin with no integer gap because `2·(t·2^k) = t·2^{k+1}` and
`⌈y⌉ ≤ ⌊y⌋ + 1`. -/
private theorem dyadic_cover_sum (f : ℤ → ℝ) (hf : ∀ a, 0 ≤ f a) (t : ℝ) (ht : 0 < t) :
    ∀ K : ℕ,
      ∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋, f a ≤
        ∑ k ∈ Finset.range (K + 1),
          ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a := by
  intro K
  induction K with
  | zero =>
    rw [zero_add, Finset.sum_range_one]
    norm_num
  | succ K ih =>
    -- big interval ⊆ (interval up to 2^{K+1}) ∪ (block K+1)
    have hcover :
        Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1 + 1)⌋ ⊆
          Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋ ∪
            Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋ := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      by_cases hle : a ≤ ⌊t * 2 ^ (K + 1)⌋
      · exact Or.inl ⟨ha.1, hle⟩
      · refine Or.inr ⟨?_, ha.2⟩
        -- ⌈t·2^{K+1}⌉ ≤ ⌊t·2^{K+1}⌋ + 1 ≤ a
        have h1 : ⌈t * 2 ^ (K + 1)⌉ ≤ ⌊t * 2 ^ (K + 1)⌋ + 1 := Int.ceil_le_floor_add_one _
        omega
    calc
      ∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1 + 1)⌋, f a
          ≤ ∑ a ∈ (Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋ ∪
              Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋), f a :=
            Finset.sum_le_sum_of_subset_of_nonneg hcover (fun a _ _ => hf a)
      _ ≤ (∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋, f a) +
            ∑ a ∈ Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋, f a := by
            set s₁ := Finset.Icc ⌈t⌉ ⌊t * 2 ^ (K + 1)⌋ with hs₁
            set s₂ := Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋ with hs₂
            have hui : (∑ x ∈ s₁ ∪ s₂, f x) + ∑ x ∈ s₁ ∩ s₂, f x =
                (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := Finset.sum_union_inter
            have hinter : 0 ≤ ∑ a ∈ (s₁ ∩ s₂), f a :=
              Finset.sum_nonneg (fun a _ => hf a)
            linarith
      _ ≤ (∑ k ∈ Finset.range (K + 1),
              ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a) +
            ∑ a ∈ Finset.Icc ⌈t * 2 ^ (K + 1)⌉ ⌊t * 2 ^ (K + 1 + 1)⌋, f a := by
            gcongr
      _ = ∑ k ∈ Finset.range (K + 1 + 1),
              ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a := by
            rw [Finset.sum_range_succ (fun k =>
              ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a) (K + 1)]

/-- A dyadic covering exponent: for `0 < t ≤ b` there is `n` with `b ≤ t·2^{n+1} ≤ 2b`. -/
private theorem exists_cover_exp (t b : ℝ) (ht : 0 < t) (hb : t ≤ b) :
    ∃ n : ℕ, b ≤ t * 2 ^ (n + 1) ∧ t * 2 ^ (n + 1) ≤ 2 * b ∧ (2 : ℝ) ^ (n + 1) ≤ 2 * b / t := by
  have hbt : (1 : ℝ) ≤ b / t := (one_le_div ht).mpr hb
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hbt (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_, ?_, ?_⟩
  · -- b ≤ t·2^{n+1} from b/t < 2^{n+1}
    rw [← div_le_iff₀' ht]
    exact le_of_lt hn2
  · -- t·2^{n+1} ≤ 2b from 2^n ≤ b/t
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have h2 : (2 : ℝ) ^ n * t ≤ b := by
      rw [← le_div_iff₀ ht]; exact hn1
    rw [hpow]; nlinarith [h2]
  · -- 2^{n+1} ≤ 2b/t
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have h2 : (2 : ℝ) ^ n * t ≤ b := by
      rw [← le_div_iff₀ ht]; exact hn1
    rw [hpow, le_div_iff₀ ht]; nlinarith [h2]

/-- Threshold identity `(1/4)·(D/H)^{4/3}·(H⁴/X)^{1/3} = D^{4/3}/(4·X^{1/3})`. -/
private theorem thr_identity {H X D : ℝ} (hH : 0 < H) (hX : 0 < X) (hD : 0 < D) :
    (1/4 : ℝ) * (D / H) ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)
      = D ^ (4/3 : ℝ) / (4 * X ^ (1/3 : ℝ)) := by
  rw [Real.div_rpow hD.le hH.le, Real.div_rpow (by positivity) hX.le]
  have hH43 : ((H ^ 4 : ℝ)) ^ (1/3 : ℝ) = H ^ (4/3 : ℝ) := by
    rw [← Real.rpow_natCast H 4, ← Real.rpow_mul hH.le]; norm_num
  rw [hH43]
  have hHne : (H : ℝ) ^ (4/3 : ℝ) ≠ 0 := by positivity
  field_simp

/-- `2·bb ≤ X²·t` where `bb = (D/H)·U`, `t = D^{4/3}/(4X^{1/3})`, reduces to `8U ≤ X^{5/3}`. -/
private theorem two_bb_le_sq_t {H X U D : ℝ} (hH : 1 ≤ H) (hX : 0 < X) (hD : 1 ≤ D)
    (hU : 0 < U) (h8 : 8 * U ≤ X ^ (5/3 : ℝ)) :
    2 * ((D / H) * U) ≤ X ^ (2 : ℝ) * (D ^ (4/3 : ℝ) / (4 * X ^ (1/3 : ℝ))) := by
  have hX0 : 0 < X := hX
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD
  have hHpos : 0 < H := lt_of_lt_of_le one_pos hH
  have hD13 : (1:ℝ) ≤ D ^ (1/3 : ℝ) := Real.one_le_rpow hD (by norm_num)
  have hDD43 : D ≤ D ^ (4/3 : ℝ) := by
    have he : D ^ (4/3 : ℝ) = D * D ^ (1/3 : ℝ) := by
      rw [show (4/3 : ℝ) = 1 + 1/3 by norm_num, Real.rpow_add hDpos, Real.rpow_one]
    rw [he]; nlinarith [hDpos, hD13]
  have ht_eq : X ^ (2:ℝ) * (D ^ (4/3 : ℝ) / (4 * X ^ (1/3 : ℝ)))
      = X ^ (5/3 : ℝ) * D ^ (4/3 : ℝ) / 4 := by
    rw [show X ^ (2:ℝ) = X ^ (5/3 : ℝ) * X ^ (1/3 : ℝ) by rw [← Real.rpow_add hX0]; norm_num]
    field_simp
  rw [ht_eq, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
  have hX53pos : (0:ℝ) < X ^ (5/3 : ℝ) := Real.rpow_pos_of_pos hX0 _
  calc 2 * (D / H * U) * 4 = 8 * U * (D / H) := by ring
    _ ≤ 8 * U * D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hHpos]; nlinarith [hDpos, hH]
    _ ≤ X ^ (5/3 : ℝ) * D := mul_le_mul_of_nonneg_right h8 hDpos.le
    _ ≤ X ^ (5/3 : ℝ) * D ^ (4/3 : ℝ) := mul_le_mul_of_nonneg_left hDD43 hX53pos.le

/-- Cover-and-count: if the dyadic blocks of `f` are each `≤ B ≥ 0` and `[⌈t⌉,⌊bb⌋]` is covered by
the first `n+1` blocks, then `∑_{[⌈t⌉,⌊bb⌋]} f ≤ (n+1)·B`. -/
private theorem cover_sum_le (f : ℤ → ℝ) (hf : ∀ a, 0 ≤ f a) (t bb B : ℝ) (ht : 0 < t)
    (n : ℕ) (hcov : bb ≤ t * 2 ^ (n + 1)) (hB : 0 ≤ B)
    (hblock : ∀ k ∈ Finset.range (n + 1),
        ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a ≤ B) :
    ∑ a ∈ Finset.Icc ⌈t⌉ ⌊bb⌋, f a ≤ ((n : ℝ) + 1) * B := by
  have hsub : Finset.Icc ⌈t⌉ ⌊bb⌋ ⊆ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (n + 1)⌋ :=
    Finset.Icc_subset_Icc_right (Int.floor_le_floor hcov)
  calc ∑ a ∈ Finset.Icc ⌈t⌉ ⌊bb⌋, f a
      ≤ ∑ a ∈ Finset.Icc ⌈t⌉ ⌊t * 2 ^ (n + 1)⌋, f a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hf a)
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          ∑ a ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, f a := dyadic_cover_sum f hf t ht n
    _ ≤ ∑ _k ∈ Finset.range (n + 1), B := Finset.sum_le_sum hblock
    _ = ((n : ℝ) + 1) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- `Real.log X ≤ ε⁻¹ · X^ε` for `X ≥ 1` and `ε > 0`.  (From `log_le_sub_one_of_pos` applied to
`X^ε`: `ε·log X = log (X^ε) ≤ X^ε - 1 ≤ X^ε`.) -/
private theorem log_le_rpow {ε : ℝ} (hε : 0 < ε) {X : ℝ} (hX : 1 ≤ X) :
    Real.log X ≤ ε⁻¹ * X ^ ε := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hxe : 0 < X ^ ε := Real.rpow_pos_of_pos hX0 _
  have hlog : Real.log (X ^ ε) ≤ X ^ ε - 1 := Real.log_le_sub_one_of_pos hxe
  rw [Real.log_rpow hX0] at hlog
  have h1 : ε * Real.log X ≤ X ^ ε := by linarith
  rw [← le_div_iff₀' hε] at h1
  rwa [div_eq_inv_mul] at h1

/-- "Large `X` makes a lower power negligible": for `α < β`, once `X ≥ c^{1/(β-α)}` and `X ≥ 1`,
`c · X^α ≤ X^β`. -/
private theorem rpow_dominate {c α β : ℝ} (hc : 0 < c) (hαβ : α < β) {X : ℝ}
    (hX1 : 1 ≤ X) (hXc : c ^ ((β - α)⁻¹) ≤ X) : c * X ^ α ≤ X ^ β := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hd : 0 < β - α := by linarith
  -- c ≤ X^{β-α}
  have hcle : c ≤ X ^ (β - α) := by
    have := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ c ^ ((β - α)⁻¹)) hXc hd.le
    rwa [← Real.rpow_mul hc.le, inv_mul_cancel₀ (ne_of_gt hd),
      Real.rpow_one] at this
  -- multiply by X^α > 0
  have hXα : 0 < X ^ α := Real.rpow_pos_of_pos hX0 _
  calc c * X ^ α ≤ X ^ (β - α) * X ^ α := by nlinarith [hXα]
    _ = X ^ β := by rw [← Real.rpow_add hX0]; ring_nf

end DyadicAssembly

open DyadicAssembly in
set_option maxHeartbeats 1600000 in
theorem key_dyadic_assembly (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℝ, X ^ ((1 - g) / 5) / X ^ u ≤ D → D ≤ X ^ (1/2 : ℝ) →
        (dCard X (X ^ ((1 - g) / 5)) D : ℝ) ≤ C * X ^ ((1 - g) / 5) / X ^ u := by
  classical
  -- the per-block bound and its band constant
  obtain ⟨u_b, hu_b, hopt, C_b, hC_b, c₀, hc₀, hbound⟩ := dblock_bound g hg hg'
  obtain ⟨C_s, hC_s, hsmall⟩ := dblock_small_omega c₀ hc₀
  obtain ⟨u_2, hu_2, C_2, hC_2, X_2, h2⟩ := prop_2_4 g hg hg'
  -- u_b < 1/100 < 1/200 from the optimization budget 18977 g + 15315 u_b < 2
  have hub100 : u_b < 1 / 100 := by nlinarith [hg, hopt]
  have hub200 : u_b < 1 / 200 := by nlinarith [hg, hopt]
  -- result exponent: below both u_b/2 (room for the O(log) shrink) and u_2 (prop_2_4 budget)
  refine ⟨min (u_b / 2) u_2, lt_min (by linarith) hu_2, ?_⟩
  set u : ℝ := min (u_b / 2) u_2 with hudef
  have hu0 : 0 < u := lt_min (by linarith) hu_2
  have hu_half : u ≤ u_b / 2 := min_le_left _ _
  have huu2 : u ≤ u_2 := min_le_right _ _
  have huub : u < u_b := lt_of_le_of_lt hu_half (by linarith)
  have hub_sub : u_b / 2 ≤ u_b - u := by linarith [hu_half]
  -- the assembled constant
  set C_blk : ℝ := max C_b C_s with hCblkdef
  have hCblk_pos : 0 < C_blk := lt_of_lt_of_le hC_b (le_max_left _ _)
  refine ⟨6 * C_blk + 6 + C_2, by positivity, ?_⟩
  -- abbreviation for the H-exponent
  set a : ℝ := (1 - g) / 5 with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hub_a : u_b < a := by rw [hadef]; nlinarith [hg, hub100]
  -- the (absolute) thresholds X must exceed
  set Tlog : ℝ := (8 / (u_b * Real.log 2)) ^ ((u_b / 4)⁻¹) with hTlogdef
  set t8  : ℝ := 8 ^ ((1 - (a + 1/2))⁻¹) with ht8def
  set t1025 : ℝ := 1025 ^ (((1:ℝ)/100)⁻¹) with ht1025def
  set t64 : ℝ := 64 ^ ((1 + 1/50 - a)⁻¹) with ht64def
  set t2  : ℝ := 2 ^ ((a - u_b)⁻¹) with ht2def
  set tbig : ℝ := 16777216 ^ ((1/100 : ℝ)⁻¹) with htbigdef
  set X₀ : ℝ := max X_2 (max tbig (max t8 (max t1025
      (max t64 (max t2 (max Tlog 8)))))) with hX₀def
  refine ⟨X₀, ?_⟩
  intro X hXX₀ D hDlo hDhi
  -- extract each threshold from X₀ ≤ X
  have hXX2 : X_2 ≤ X := le_trans (le_max_left _ _) hXX₀
  have hXtbig : tbig ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXX₀
  have hXt8 : t8 ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hXX₀
  have hXt1025 : t1025 ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hXX₀
  have hXt64 : t64 ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))))) hXX₀
  have hXt2 : t2 ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))) hXX₀
  have hXTlog : Tlog ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))))) hXX₀
  have hX8 : (8 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))))) hXX₀
  -- basic facts about X
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  -- the global parameter pack (with u = u_b)
  set P : Globals := ⟨X, g, u_b, hX0⟩ with hPdef
  have hPH : P.H = X ^ a := by rw [hPdef, Globals.H, hadef]
  have hPG : P.G = X ^ g := by rw [hPdef, Globals.G]
  have hPU : P.U = X ^ u_b := by rw [hPdef, Globals.U]
  have hHpos : 0 < P.H := P.H_pos
  have hH1 : (1 : ℝ) ≤ P.H := by rw [hPH]; exact Real.one_le_rpow hX1 ha0.le
  have hUpos : 0 < P.U := P.U_pos
  -- target rewrite: dCard X (X^a) D = dCard P.X P.H D
  have hgoalcast : (dCard X (X ^ a) D : ℝ) = (dCard P.X P.H D : ℝ) := by rw [hPH, hPdef]
  rw [hgoalcast]
  -- D positivity (from lower bound X^a/X^u ≤ D, RHS positive)
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDlo
  have hDhi' : D ≤ P.X ^ (1/2 : ℝ) := by rw [hPdef]; exact hDhi
  -- the result RHS in P-terms:  C * X^a / X^u = C * P.H / X^u
  have hRHS : (6 * C_blk + 6 + C_2) * X ^ a / X ^ u
      = (6 * C_blk + 6 + C_2) * P.H / X ^ u := by rw [hPH]
  rw [hRHS]
  -- case split on Δ = D/H vs X^{1/100}, i.e. D vs H·X^{1/100}
  rcases le_or_gt D (P.H * P.X ^ (1/100 : ℝ)) with hShort | hLong
  · -- SHORT regime: prop_2_4
    have hShort' : D ≤ X ^ a * X ^ (1 / 100 : ℝ) := by
      rw [← hPH]; simpa [hPdef] using hShort
    have hkey := h2 X hXX2 D hDpos hShort'
    -- dCard X (X^a) D = dCard P.X P.H D
    rw [hgoalcast] at hkey
    -- bound C_2·X^a/X^{u_2} ≤ (6C_blk+6+C_2)·P.H/X^u
    have hXu2pos : (0 : ℝ) < X ^ u_2 := Real.rpow_pos_of_pos hX0 _
    have hXupos : (0 : ℝ) < X ^ u := Real.rpow_pos_of_pos hX0 _
    have hmono : X ^ a / X ^ u_2 ≤ X ^ a / X ^ u := by
      apply div_le_div_of_nonneg_left (by positivity) hXupos
      exact Real.rpow_le_rpow_of_exponent_le hX1 huu2
    calc (dCard P.X P.H D : ℝ) ≤ C_2 * X ^ a / X ^ u_2 := hkey
      _ = C_2 * (X ^ a / X ^ u_2) := by ring
      _ ≤ C_2 * (X ^ a / X ^ u) := by
          apply mul_le_mul_of_nonneg_left hmono hC_2.le
      _ ≤ (6 * C_blk + 6 + C_2) * (X ^ a / X ^ u) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [hCblk_pos]
      _ = (6 * C_blk + 6 + C_2) * P.H / X ^ u := by rw [hPH]; ring
  · -- LONG regime: a_decomposition + dyadic blocks
    have hX13pos : (0 : ℝ) < X ^ (1/3 : ℝ) := Real.rpow_pos_of_pos hX0 _
    have hX12 : D ≤ X ^ (1/2 : ℝ) := by simpa [hPdef] using hDhi'
    -- regime hypotheses for a_decomposition
    have hD1 : P.H * P.X ^ (1/100 : ℝ) ≤ D := hLong.le
    have hHD : 8 * P.H * D ≤ P.X := by
      rw [hPH, hPdef]
      have h1 : 8 * X ^ a * D ≤ 8 * X ^ a * X ^ (1/2 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hX12 (by positivity : (0:ℝ) ≤ 8 * X ^ a)
        linarith [this]
      have h2 : 8 * X ^ a * X ^ (1/2 : ℝ) = 8 * X ^ (a + 1/2) := by
        rw [Real.rpow_add hX0]; ring
      have h3 : 8 * X ^ (a + 1/2) ≤ X ^ (1 : ℝ) :=
        rpow_dominate (by norm_num) (by rw [hadef]; nlinarith [hg]) hX1 hXt8
      rw [Real.rpow_one] at h3
      rw [h2] at h1; linarith
    have hDlarge : 1025 * P.H ≤ D := by
      have h1025 : (1025 : ℝ) * X ^ (0 : ℝ) ≤ X ^ (1/100 : ℝ) :=
        rpow_dominate (by norm_num) (by norm_num) hX1
          (by rw [ht1025def] at hXt1025; rw [show ((1:ℝ)/100 - 0) = (1:ℝ)/100 by ring]; exact hXt1025)
      rw [Real.rpow_zero, mul_one] at h1025
      calc 1025 * P.H = 1025 * X ^ a := by rw [hPH]
        _ ≤ X ^ (1/100 : ℝ) * X ^ a := by nlinarith [Real.rpow_pos_of_pos hX0 a]
        _ = X ^ a * X ^ (1/100 : ℝ) := by ring
        _ = P.H * P.X ^ (1/100 : ℝ) := by rw [hPH, hPdef]
        _ ≤ D := hLong.le
    have hEps : 64 * P.H ^ 3 ≤ P.X * D ^ 2 := by
      -- D ≥ H·X^{1/100} ⟹ D² ≥ H²·X^{1/50}; X·D² ≥ X·H²·X^{1/50} = H²·X^{1+1/50}; 64H ≤ X^{1+1/50}
      have hHX100 : P.H * X ^ (1/100 : ℝ) ≤ D := by simpa [hPdef] using hLong.le
      have hHX100pos : (0:ℝ) < P.H * X ^ (1/100 : ℝ) := by positivity
      have hDsq : (P.H * X ^ (1/100 : ℝ)) ^ 2 ≤ D ^ 2 := by
        apply pow_le_pow_left₀ hHX100pos.le hHX100
      have hsq_eq : (P.H * X ^ (1/100 : ℝ)) ^ 2 = P.H ^ 2 * X ^ (1/50 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (X ^ (1/100:ℝ)) 2, ← Real.rpow_mul hX0.le]
        norm_num
      have h64 : 64 * X ^ a ≤ X ^ (1 + 1/50 : ℝ) :=
        rpow_dominate (by norm_num) (by rw [hadef]; nlinarith [hg]) hX1 hXt64
      have hXsplit : X ^ (1 + 1/50 : ℝ) = X * X ^ (1/50 : ℝ) := by
        rw [show (1 + 1/50 : ℝ) = (1:ℝ) + 1/50 from rfl, Real.rpow_add hX0, Real.rpow_one]
      -- assemble
      have hH2pos : (0:ℝ) < P.H ^ 2 := by positivity
      have hX150pos : (0:ℝ) < X ^ (1/50 : ℝ) := Real.rpow_pos_of_pos hX0 _
      calc 64 * P.H ^ 3 = (64 * P.H) * P.H ^ 2 := by ring
        _ ≤ (X ^ (1 + 1/50 : ℝ)) * P.H ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hH2pos.le
            rw [hPH]; linarith [h64]
        _ = X * (P.H ^ 2 * X ^ (1/50 : ℝ)) := by rw [hXsplit]; ring
        _ ≤ X * D ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hX0.le
            rw [← hsq_eq]; exact hDsq
        _ = P.X * D ^ 2 := by rw [hPdef]
    have hHU : P.U ≤ P.H := by
      rw [hPU, hPH]; exact Real.rpow_le_rpow_of_exponent_le hX1 hub_a.le
    have hdec := a_decomposition P D hX1 hg hg' hu_b hD1 hDhi' hHD hDlarge hEps hHU
    -- abbreviations
    set t : ℝ := D ^ (4 / 3 : ℝ) / (4 * P.X ^ (1 / 3 : ℝ)) with htdef
    set Δ : ℝ := D / P.H with hΔdef
    set bb : ℝ := (D / P.H) * P.U with hbbdef
    have hΔpos : 0 < Δ := by rw [hΔdef]; positivity
    have hD43pos : (0:ℝ) < D ^ (4/3 : ℝ) := Real.rpow_pos_of_pos hDpos _
    have htpos : 0 < t := by rw [htdef, hPdef]; positivity
    have hbbpos : 0 < bb := by rw [hbbdef]; positivity
    -- threshold identity:  (1/4)·Δ^{4/3}·(H^4/X)^{1/3} = t
    have hHX13pos : (0:ℝ) < (P.H ^ 4 / P.X) ^ (1/3 : ℝ) := by
      apply Real.rpow_pos_of_pos; rw [hPdef]; positivity
    have hthr : (1/4 : ℝ) * Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) = t := by
      rw [hΔdef, htdef]; exact thr_identity (H := P.H) (X := P.X) (D := D) hHpos P.X_pos hDpos
    -- DaCard ≥ 0 as a real
    have hDaC_nonneg : ∀ b : ℤ, (0:ℝ) ≤ (DaCard P.X P.H b D : ℝ) := fun b => by positivity
    -- 2·bb ≤ D  (i.e. 2U ≤ H), used for the regime hyp 2A ≤ D
    have h2bb : 2 * bb ≤ D := by
      rw [hbbdef, hPU, hPH]
      have h2 : (2:ℝ) * X ^ u_b ≤ X ^ a :=
        rpow_dominate (by norm_num) hub_a hX1 hXt2
      have hDH : (0:ℝ) < D / X ^ a := by rw [← hPH]; positivity
      rw [show (2:ℝ) * (D / X ^ a * X ^ u_b) = (D / X ^ a) * (2 * X ^ u_b) by ring]
      calc (D / X ^ a) * (2 * X ^ u_b) ≤ (D / X ^ a) * X ^ a := by
              apply mul_le_mul_of_nonneg_left h2 hDH.le
        _ = D := by field_simp
    -- 16777216 ≤ X^{1/100}
    have h16M : (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) := by
      have := rpow_dominate (c := (16777216:ℝ)) (α := 0) (β := 1/100) (by norm_num) (by norm_num)
        hX1 (by rw [htbigdef] at hXtbig; rw [show ((1:ℝ)/100 - 0) = (1:ℝ)/100 by ring]; exact hXtbig)
      rw [Real.rpow_zero, mul_one] at this
      rw [hPdef]; exact this
    -- X^{1/100} ≤ Δ  (from H·X^{1/100} ≤ D)
    have hΔlong : P.X ^ (1/100 : ℝ) ≤ Δ := by
      rw [hΔdef, le_div_iff₀ hHpos, mul_comm]
      simpa [hPdef] using hD1
    -- the scale family S_k : Ω = (t/Δ)·2^k
    have hΩk_pos : ∀ k : ℕ, 0 < (t / Δ) * 2 ^ k := fun k => by positivity
    set Sk : ℕ → Scale P := fun k => ⟨Δ, (t / Δ) * 2 ^ k, hΔpos, hΩk_pos k⟩ with hSkdef
    have hSkA : ∀ k : ℕ, (Sk k).A = t * 2 ^ k := by
      intro k; rw [hSkdef]; show Δ * ((t / Δ) * 2 ^ k) = t * 2 ^ k
      field_simp
    have hSkD : ∀ k : ℕ, (Sk k).D = D := by
      intro k; rw [hSkdef]; show P.H * Δ = D
      rw [hΔdef]; field_simp
    -- DBlock S_k = ∑ over the k-th dyadic block of DaCard
    have hSkBlock : ∀ k : ℕ, DBlock P (Sk k) D =
        ∑ b ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, (DaCard P.X P.H b D : ℝ) := by
      intro k
      rw [DBlock, hSkA k]
      congr 1
      rw [show t * 2 ^ (k + 1) = 2 * (t * 2 ^ k) by ring]
    -- per-block bound: for k with the two regime side-conditions, DBlock ≤ C_blk·H/U
    have hblk : ∀ k : ℕ, 2 * (t * 2 ^ k) ≤ D → (t / Δ) * 2 ^ k ≤ P.U →
        DBlock P (Sk k) D ≤ C_blk * P.H / P.U := by
      intro k h2A hΩU
      have hSkΔ : (Sk k).Δ = Δ := rfl
      have hNR : (1/4 : ℝ) * (Sk k).Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ (Sk k).A := by
        rw [hSkA k, hSkΔ, hthr]
        have h2k : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith [htpos, h2k]
      have hAD : 2 * (Sk k).A ≤ (Sk k).D := by rw [hSkA k, hSkD k]; exact h2A
      have hΩUle : (Sk k).Ω ≤ P.U := by
        show (t / Δ) * 2 ^ k ≤ P.U; exact hΩU
      have hDeq : D = (Sk k).D := (hSkD k).symm
      -- case split on Ω vs the band edge
      rcases le_or_gt (c₀ * (P.G ^ (-1/4 : ℝ) * P.U ^ (-3/4 : ℝ))) (Sk k).Ω with hband | hband
      · -- on/above band edge: dblock_bound
        have := hbound P rfl rfl hX1 (Sk k) hΔlong h16M hNR hAD hband hΩUle D hDpos hDeq
        calc DBlock P (Sk k) D ≤ C_b * P.H / P.U := this
          _ ≤ C_blk * P.H / P.U := by
              gcongr
              exact le_max_left _ _
      · -- below band edge: dblock_small_omega
        have := hsmall P hX1 hg hg' hu_b (le_of_lt hub100) (Sk k) hΔlong h16M hNR hAD
          (le_of_lt hband) D hDpos hDeq
        calc DBlock P (Sk k) D ≤ C_s * P.H / P.U := this
          _ ≤ C_blk * P.H / P.U := by
              gcongr
              exact le_max_right _ _
    -- the sum S (over Icc⌈t⌉⌊bb⌋) — split on whether it is the trivial (empty) range
    set Ssum : ℝ := ∑ b ∈ Finset.Icc ⌈t⌉ ⌊bb⌋, (DaCard P.X P.H b D : ℝ) with hSsumdef
    have hSsum_nonneg : 0 ≤ Ssum := Finset.sum_nonneg (fun b _ => hDaC_nonneg b)
    -- H/U comparison: P.H/P.U ≤ P.H/X^u  (u ≤ u_b)
    have hHU_le : P.H / P.U ≤ P.H / X ^ u := by
      rw [hPU]
      apply div_le_div_of_nonneg_left hHpos.le (Real.rpow_pos_of_pos hX0 _)
      exact Real.rpow_le_rpow_of_exponent_le hX1 (le_of_lt huub)
    have hXupos : (0:ℝ) < X ^ u := Real.rpow_pos_of_pos hX0 _
    -- main bound on Ssum:  Ssum ≤ C_blk · P.H / X^u
    have hSsum_bound : Ssum ≤ C_blk * P.H / X ^ u := by
      rcases le_or_gt t bb with htbb | htbb
      · -- non-trivial range: dyadic cover
        obtain ⟨n, hcov1, hcov2, hcov3⟩ := exists_cover_exp t bb htpos htbb
        -- each block ≤ C_blk·H/U; side conditions for k ≤ n
        have hblk_all : ∀ k ∈ Finset.range (n + 1),
            ∑ b ∈ Finset.Icc ⌈t * 2 ^ k⌉ ⌊t * 2 ^ (k + 1)⌋, (DaCard P.X P.H b D : ℝ)
              ≤ C_blk * P.H / P.U := by
          intro k hk
          rw [Finset.mem_range] at hk
          have h2k_le : (2:ℝ) ^ (k + 1) ≤ 2 ^ (n + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h2k_le' : (2:ℝ) ^ k ≤ 2 ^ n :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          -- 2·(t·2^k) = t·2^{k+1} ≤ t·2^{n+1} ≤ 2bb ≤ D
          have hcond1 : 2 * (t * 2 ^ k) ≤ D := by
            have h1 : t * 2 ^ (k + 1) ≤ t * 2 ^ (n + 1) :=
              mul_le_mul_of_nonneg_left h2k_le htpos.le
            have h2 : 2 * (t * 2 ^ k) = t * 2 ^ (k + 1) := by ring
            linarith [hcov2, h2bb, h1]
          -- (t/Δ)·2^k = t·2^k/Δ ≤ bb/Δ = U
          have hcond2 : (t / Δ) * 2 ^ k ≤ P.U := by
            have hbbΔ : bb / Δ = P.U := by rw [hbbdef, hΔdef]; field_simp
            have hle : t * 2 ^ k ≤ t * 2 ^ n :=
              mul_le_mul_of_nonneg_left h2k_le' htpos.le
            have htk_le_bb : t * 2 ^ k ≤ bb := by
              have hexp : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
              linarith [hcov2, hle, hexp ▸ hcov2]
            calc (t / Δ) * 2 ^ k = (t * 2 ^ k) / Δ := by ring
              _ ≤ bb / Δ := by gcongr
              _ = P.U := hbbΔ
          have hb := hblk k hcond1 hcond2
          rw [hSkBlock k] at hb
          exact hb
        have hStep : Ssum ≤ ((n : ℝ) + 1) * (C_blk * P.H / P.U) := by
          rw [hSsumdef]
          exact cover_sum_le (fun b => (DaCard P.X P.H b D : ℝ)) (fun b => hDaC_nonneg b)
            t bb (C_blk * P.H / P.U) htpos n hcov1 (by positivity) hblk_all
        -- N = n+1 ≤ X^{u_b/2}
        have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        -- 2·bb ≤ X²·t  (i.e. 2bb/t ≤ X²); reduces to 8·U ≤ X^{5/3} (H, D^{1/3} ≥ 1)
        have hD1' : (1:ℝ) ≤ D := by linarith [hDlarge, hH1]
        have h8U : (8:ℝ) * P.U ≤ P.X ^ (5/3 : ℝ) := by
          rw [hPU, hPdef]
          apply rpow_dominate (by norm_num) (by linarith [hub100]) hX1
          refine le_trans ?_ hX8
          calc (8:ℝ) ^ ((5/3 - u_b)⁻¹)
              ≤ 8 ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num)
                  (inv_le_one_of_one_le₀ (by linarith [hub100]))
            _ = 8 := by norm_num
        have h2bb_t : 2 * bb ≤ X ^ (2 : ℝ) * t := by
          rw [hbbdef, htdef, hPdef]
          exact two_bb_le_sq_t (H := P.H) (X := X) (U := P.U) (D := D) hH1 hX0 hD1'
            hUpos (by rw [hPU, hPdef] at h8U; exact h8U)
        have h2bbt : 2 * bb / t ≤ X ^ (2 : ℝ) := by
          rw [div_le_iff₀ htpos]; linarith [h2bb_t]
        have h2N : (2:ℝ) ^ (n + 1) ≤ X ^ (2 : ℝ) := le_trans hcov3 h2bbt
        have hlogN : ((n : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log X := by
          have e1 : Real.log ((2:ℝ) ^ (n + 1)) = ((n:ℝ) + 1) * Real.log 2 := by
            rw [Real.log_pow]; push_cast; ring
          have e2 : Real.log (X ^ (2:ℝ)) = 2 * Real.log X := by rw [Real.log_rpow hX0]
          have hmono := Real.log_le_log (by positivity) h2N
          rw [e1, e2] at hmono; exact hmono
        -- log X ≤ (4/u_b) X^{u_b/4}
        have hlogX : Real.log X ≤ (u_b / 4)⁻¹ * X ^ (u_b / 4) :=
          log_le_rpow (ε := u_b / 4) (by linarith) hX1
        have hX4pos : (0:ℝ) < X ^ (u_b / 4) := Real.rpow_pos_of_pos hX0 _
        -- (2/log2)·logX ≤ (8/(u_b log2))·X^{u_b/4}
        have hmid : (2 / Real.log 2) * Real.log X ≤ (8 / (u_b * Real.log 2)) * X ^ (u_b / 4) := by
          have h2log : (0:ℝ) < 2 / Real.log 2 := by positivity
          calc (2 / Real.log 2) * Real.log X
              ≤ (2 / Real.log 2) * ((u_b / 4)⁻¹ * X ^ (u_b / 4)) := by
                apply mul_le_mul_of_nonneg_left hlogX h2log.le
            _ = (8 / (u_b * Real.log 2)) * X ^ (u_b / 4) := by
                rw [inv_div]; field_simp; ring
        -- (8/(u_b log2))·X^{u_b/4} ≤ X^{u_b/2}
        have hdom : (8 / (u_b * Real.log 2)) * X ^ (u_b / 4) ≤ X ^ (u_b / 2) := by
          have hd := rpow_dominate (c := 8 / (u_b * Real.log 2)) (α := u_b / 4) (β := u_b / 2)
            (by positivity) (by linarith) hX1
            (by rw [hTlogdef] at hXTlog
                rw [show (u_b / 2 - u_b / 4) = u_b / 4 by ring]; exact hXTlog)
          exact hd
        have hNbound : ((n : ℝ) + 1) ≤ X ^ (u_b / 2) := by
          have hNle : ((n:ℝ) + 1) ≤ (2 / Real.log 2) * Real.log X := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hlog2pos]
            linarith [hlogN]
          linarith [hNle, hmid, hdom]
        -- X^{u_b/2}·(H/U) ≤ H/X^u  (since U = X^{u_b}, and X^{u_b/2}/X^{u_b} = X^{-u_b/2} ≤ X^{-u})
        have hXub_half : X ^ (u_b / 2) * (P.H / P.U) ≤ P.H / X ^ u := by
          rw [hPU]
          have hL : X ^ (u_b / 2) * (P.H / X ^ u_b) = P.H * X ^ (u_b / 2 - u_b) := by
            rw [Real.rpow_sub hX0]; field_simp
          have hR : P.H / X ^ u = P.H * X ^ (-u) := by
            rw [Real.rpow_neg hX0.le]; field_simp
          rw [hL, hR]
          apply mul_le_mul_of_nonneg_left _ hHpos.le
          apply Real.rpow_le_rpow_of_exponent_le hX1
          linarith [hu_half]
        -- assemble Ssum bound
        calc Ssum ≤ ((n : ℝ) + 1) * (C_blk * P.H / P.U) := hStep
          _ ≤ X ^ (u_b / 2) * (C_blk * P.H / P.U) := by
              apply mul_le_mul_of_nonneg_right hNbound
              positivity
          _ = C_blk * (X ^ (u_b / 2) * (P.H / P.U)) := by ring
          _ ≤ C_blk * (P.H / X ^ u) := mul_le_mul_of_nonneg_left hXub_half hCblk_pos.le
          _ = C_blk * P.H / X ^ u := by ring
      · -- trivial range: Icc⌈t⌉⌊bb⌋ empty, Ssum = 0
        have hempty : Finset.Icc ⌈t⌉ ⌊bb⌋ = ∅ := by
          rw [Finset.Icc_eq_empty_iff]
          intro hle
          have : ⌈t⌉ ≤ ⌊bb⌋ := hle
          have hb_lt_t : bb < t := htbb
          have h1 : (⌊bb⌋ : ℝ) ≤ bb := Int.floor_le bb
          have h2 : t ≤ (⌈t⌉ : ℝ) := Int.le_ceil t
          have h3 : (⌈t⌉ : ℝ) ≤ (⌊bb⌋ : ℝ) := by exact_mod_cast this
          linarith
        rw [hSsumdef, hempty, Finset.sum_empty]
        positivity
    -- final assembly:  dCard ≤ 6·Ssum + 6·H/U ≤ (6C_blk+6+C_2)·H/X^u
    calc (dCard P.X P.H D : ℝ)
        ≤ 6 * Ssum + 6 * (P.H / P.U) := hdec
      _ ≤ 6 * (C_blk * P.H / X ^ u) + 6 * (P.H / X ^ u) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hSsum_bound (by norm_num)
          · exact mul_le_mul_of_nonneg_left hHU_le (by norm_num)
      _ ≤ (6 * C_blk + 6 + C_2) * P.H / X ^ u := by
          have hPHX : 0 ≤ P.H / X ^ u := by positivity
          have hexp1 : 6 * (C_blk * P.H / X ^ u) + 6 * (P.H / X ^ u)
              = (6 * C_blk + 6) * (P.H / X ^ u) := by ring
          have hexp2 : (6 * C_blk + 6 + C_2) * P.H / X ^ u
              = (6 * C_blk + 6 + C_2) * (P.H / X ^ u) := by ring
          rw [hexp1, hexp2]
          apply mul_le_mul_of_nonneg_right _ hPHX
          linarith [hC_2]

end Squarefree
