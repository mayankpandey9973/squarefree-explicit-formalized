import Squarefree.Lower.Step3Perf
import Squarefree.Lower.PairWeightSum

/-!
# §5 Step-3 `f`-sum assembly (writeup 975–984)

`Ra_step3_fsum` turns the per-`f` bound `Ra_step3_perf` into a per-pair Step-3 count by
partitioning the triple set by the value `f = round(Qval …)` and summing the per-`f` bound
across `f ∈ Icc (-N) N`.  By `±`-symmetry (the per-`f` weight depends only on `|f|`) the sum
collapses to twice the half-sum over `1 ≤ n ≤ N`, which `step3_fsum_half_log` bounds by
`κ N² + ρ N + (ρ/κ)(log N + 1)`.

Here `κ = D⁴/(X·A)` and `ρ = R·Δ²·G·U²⁰/(H·Ω⁶)`; the scale-domination of the `N²`, `N`,
`log N` terms and the derivation `|f| ≤ N` are deferred — `N` is a hypothesis here.
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **Step-3 per-pair count via fiberwise partition + `f`-sum.** -/
theorem Ra_step3_fsum {a : ℤ}
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
        ∧ (10:ℝ)^55 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
            / (P.G * S.Ω ^ 5)) ≤ |((round (Qval P a dStar ℓ₁ ℓ₂ r)):ℝ)|
        ∧ (round (Qval P a dStar ℓ₁ ℓ₂ r)).natAbs ≤ N)).card : ℝ)
      ≤ 2 * (10:ℝ)^58 * ( (S.D^4/(P.X*S.A)) * (N:ℝ)^2
            + (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) * (N:ℝ)
            + (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) / (S.D^4/(P.X*S.A))
                * (Real.log (N:ℝ) + 1) ) := by
  -- abbreviations
  set κ : ℝ := S.D ^ 4 / (P.X * S.A) with hκdef
  set ρ : ℝ := S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) with hρdef
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
  have hρnn : 0 ≤ ρ := by rw [hρdef]; positivity
  -- the threshold constant L (the geometric lower-bound factor)
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
      ∧ (10:ℝ)^55 * L ≤ |((g r):ℝ)| ∧ (g r).natAbs ≤ N with hpdef
  classical
  -- the full filtered set
  set S3 : Finset ℕ := Ra.filter p with hS3def
  -- per-`f` weight `h₀`
  set h₀ : ℝ → ℝ := fun x => (10:ℝ)^58 * (κ * x + ρ + ρ / (κ * x)) with hh0def
  -- ===== Step 1: every r ∈ S3 maps into Icc (-N) N under g =====
  have hmap : ∀ r ∈ S3, g r ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
    intro r hr
    rw [hS3def, Finset.mem_filter] at hr
    have hnatabs : (g r).natAbs ≤ N := hr.2.2.2.2
    rw [Finset.mem_Icc]
    have hle : |g r| ≤ (N:ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hnatabs
    constructor
    · linarith [abs_le.mp hle |>.1]
    · linarith [abs_le.mp hle |>.2]
  -- ===== Step 2: fiberwise card decomposition =====
  have hcard_eq : S3.card
      = ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (S3.filter (fun r => g r = f)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  -- ===== Step 3: per-fiber bound =====
  -- For each f ∈ Icc(-N)N, bound the fiber card by `if f = 0 then 0 else h₀ |f|`.
  have hfiber : ∀ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      ((S3.filter (fun r => g r = f)).card : ℝ)
        ≤ (if f = 0 then 0 else h₀ |(f : ℝ)|) := by
    intro f hf
    by_cases hf0 : f = 0
    · -- empty fiber: the threshold conjunct forces |g r| > 0
      simp only [hf0, if_true]
      have hempty : S3.filter (fun r => g r = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro r hr
        rw [hS3def, Finset.mem_filter] at hr
        intro hgr0
        have hthr : (10:ℝ)^55 * L ≤ |((g r):ℝ)| := hr.2.2.2.1
        rw [hgr0] at hthr
        simp only [Int.cast_zero, abs_zero] at hthr
        have : (0:ℝ) < (10:ℝ)^55 * L := by positivity
        linarith
      rw [hempty]
      simp
    · -- nonempty / general fiber: bound by Ra_step3_perf f
      simp only [hf0, if_false]
      -- the fiber filtered set
      set Ff : Finset ℕ := S3.filter (fun r => g r = f) with hFfdef
      -- card ≤ 0 if empty; otherwise extract hflarge from a member and apply perf
      rcases Finset.eq_empty_or_nonempty Ff with hFe | hFne
      · rw [hFe]
        simp only [Finset.card_empty, Nat.cast_zero]
        -- h₀ |f| ≥ 0
        have hfRpos : 0 < |(f : ℝ)| := by
          have : (f : ℝ) ≠ 0 := by exact_mod_cast hf0
          positivity
        have : 0 ≤ h₀ |(f : ℝ)| := by
          rw [hh0def]
          have : 0 ≤ κ * |(f:ℝ)| + ρ + ρ / (κ * |(f:ℝ)|) := by positivity
          positivity
        exact this
      · -- nonempty fiber: derive hflarge for this f, apply Ra_step3_perf
        obtain ⟨r₀, hr₀⟩ := hFne
        rw [hFfdef, Finset.mem_filter, hS3def, Finset.mem_filter] at hr₀
        -- hr₀ : (r₀ ∈ Ra ∧ p r₀) ∧ g r₀ = f
        have hgr₀ : g r₀ = f := hr₀.2
        have hthr₀ : (10:ℝ)^55 * L ≤ |((g r₀):ℝ)| := hr₀.1.2.2.2.1
        -- translate to hflarge in f
        have hflarge : (10:ℝ) ^ 55 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ)
            * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) / (P.G * S.Ω ^ 5)) ≤ |(f : ℝ)| := by
          rw [← hLdef]
          rw [hgr₀] at hthr₀
          convert hthr₀ using 2
        -- the perf bound for this f
        have hperf := Ra_step3_perf (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W
          hflarge h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg Ra dStar hdStar
        -- Ff ⊆ the perf filter set
        have hsub : Ff ⊆ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ round (Qval P a dStar ℓ₁ ℓ₂ r) = f) := by
          intro r hr
          rw [hFfdef, Finset.mem_filter, hS3def, Finset.mem_filter] at hr
          rw [Finset.mem_filter]
          refine ⟨hr.1.1, hr.1.2.1, hr.1.2.2.1, ?_⟩
          have : g r = f := hr.2
          rw [hgdef] at this; exact this
        have hcardle : (Ff.card : ℝ) ≤
            ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
              ∧ round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        -- chain into perf bound; rewrite RHS as h₀ |f|
        rw [hh0def]
        have hrwperf : (10:ℝ) ^ 58 * ((|(f : ℝ)| * S.D ^ 4 / (P.X * S.A))
            + S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
            + S.R * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
                / (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A)))
            = (10:ℝ)^58 * (κ * |(f:ℝ)| + ρ + ρ / (κ * |(f:ℝ)|)) := by
          rw [hκdef, hρdef]; ring_nf
        rw [hrwperf] at hperf
        linarith [hcardle, hperf]
  -- ===== Step 4: sum the fiber bounds =====
  have hsumle : (S3.card : ℝ)
      ≤ ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (if f = 0 then 0 else h₀ |(f : ℝ)|) := by
    rw [hcard_eq, Nat.cast_sum]
    exact Finset.sum_le_sum hfiber
  -- ===== Step 5: ± symmetry =====
  -- the if-guarded sum equals 2 * ∑_{n∈Icc 1 N} h₀ n
  have hsym : ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (if f = 0 then 0 else h₀ |(f : ℝ)|)
      = 2 * ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ) := by
    -- split off f = 0 (which contributes 0), then split into positive and negative
    -- We use: Icc(-N)N partitions into {f < 0} and {f ≥ 0}; relate each to Icc 1 N.
    -- First, drop the zero term: the if-guarded function maps 0 to 0.
    -- Reindex via the involution f ↦ -f on Icc(-N)N (which fixes 0).
    -- ∑ k(f) = ∑ k(-f) where k f = if f=0 then 0 else h₀ |f|, since |f| = |-f|.
    -- So the sum over negatives equals the sum over positives. Concretely:
    set k : ℤ → ℝ := fun f => if f = 0 then 0 else h₀ |(f : ℝ)| with hkdef
    -- k is even: k (-f) = k f
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
    -- split Icc(-N)N = Icc(-N)(-1) ∪ {0} ∪ Icc 1 N (as sums)
    -- Use Finset.sum over Icc by the map relating to Icc 1 N.
    -- Approach: ∑_{Icc(-N)N} k = ∑_{Icc 1 N} k(-n) + k 0 + ∑_{Icc 1 N} k n
    -- via reindexing negatives n ↦ -n.
    have hzero : k 0 = 0 := by rw [hkdef]; simp
    -- positive part: ∑_{n∈Icc 1 N} k n = ∑_{n∈Icc 1 N} h₀ n
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
    -- Now decompose the integer interval sum.
    -- Icc(-N)N = (Icc 1 N image under neg) ∪ {0} ∪ Icc 1 N
    -- Use the standard: ∑_{Icc(-N)N} = ∑_{Ico(-N)0} + k 0 + ∑_{Ioc 0 N}? Easier:
    -- map the negative half via Finset.sum_map with the embedding n ↦ -n.
    -- Build: the set of negatives = (Finset.Icc 1 N).map (negation embedding).
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
    -- the Icc 1 N (ℤ) sum vs Icc 1 N (ℕ) sum of k
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
    -- decompose the big sum: zero / pos / neg using filter trichotomy
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
    -- evaluate each piece
    -- negative piece:
    have hnegsum : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f < 0), k f
        = ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by
      rw [hnegset, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Function.Embedding.coeFn_mk]
      exact hkeven n
    -- zero piece:
    have hzerosum : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => f = 0), k f = 0 := by
      apply Finset.sum_eq_zero
      intro f hf
      rw [Finset.mem_filter] at hf
      rw [hf.2]; exact hzero
    -- positive piece:
    have hpossum : ∑ f ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun f => 0 < f), k f
        = ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by
      rw [hposset]
    -- assemble
    calc ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), k f
        = ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n + 0 + ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by
            rw [htri, hnegsum, hzerosum, hpossum]
      _ = 2 * ∑ n ∈ Finset.Icc (1:ℤ) (N:ℤ), k n := by ring
      _ = 2 * ∑ n ∈ Finset.Icc 1 N, k ((n:ℤ)) := by rw [hIccZN]
      _ = 2 * ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ) := by rw [hposeq]
  -- ===== Step 6: apply step3_fsum_half_log =====
  rw [hsym] at hsumle
  -- the inner sum matches step3_fsum_half_log's LHS after factoring 10^58
  have hinner : ∑ n ∈ Finset.Icc 1 N, h₀ (n : ℝ)
      = (10:ℝ)^58 * ∑ n ∈ Finset.Icc 1 N, (κ * (n:ℝ) + ρ + ρ / (κ * (n:ℝ))) := by
    rw [Finset.mul_sum]
  rw [hinner] at hsumle
  have hhalf := step3_fsum_half_log κ ρ hκpos hρnn N
  -- chain: S3.card ≤ 2 * 10^58 * (inner sum) ≤ 2 * 10^58 * (κ N² + ρ N + (ρ/κ)(log N + 1))
  have hfinal : (S3.card : ℝ)
      ≤ 2 * (10:ℝ)^58 * (κ * (N:ℝ)^2 + ρ * (N:ℝ) + (ρ / κ) * (Real.log (N:ℝ) + 1)) := by
    have hstep : 2 * ((10:ℝ)^58 * ∑ n ∈ Finset.Icc 1 N, (κ * (n:ℝ) + ρ + ρ / (κ * (n:ℝ))))
        ≤ 2 * ((10:ℝ)^58 * (κ * (N:ℝ)^2 + ρ * (N:ℝ) + (ρ / κ) * (Real.log (N:ℝ) + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hhalf (by positivity)
    have : 2 * ((10:ℝ)^58 * (κ * (N:ℝ)^2 + ρ * (N:ℝ) + (ρ / κ) * (Real.log (N:ℝ) + 1)))
        = 2 * (10:ℝ)^58 * (κ * (N:ℝ)^2 + ρ * (N:ℝ) + (ρ / κ) * (Real.log (N:ℝ) + 1)) := by
      ring
    rw [this] at hstep
    linarith [hsumle, hstep]
  -- conclude: rewrite κ, ρ back
  rw [hκdef, hρdef] at hfinal
  exact hfinal

end Squarefree
