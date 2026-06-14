import Squarefree.Lower.Step2CountBand

/-!
# §5 Step-2 per-`f` count via narrow-band tiling (`Ra_step2_count`)

`Ra_step2_count` is the BANDS analogue of `Ra_step3_count`: for a fixed integer `f`, the set of
triples `r ∈ Ra` (with `r+ℓ₁,r+ℓ₂ ∈ Ra`) whose defect `𝒬(r)` rounds to `f` has card bounded by the
`√(δ/T)` BANDS shape `C·(S.R·(δ₂₃ + √(δ₂₃/T₀)) + T₀ + 1)`, with `T₀ = |f|·S.D⁴/(P.X·S.A)`,
`δ₂₃ = S.Δ²·G·U²⁰/(H·Ω⁶)` and `C` an ABSOLUTE constant.

The window `[(1/72)S.R, 16 S.R]` is tiled by `K_band = 178` narrow bands of ratio
`λ = (51/50)²`; per band `step2_band_count` (`Step2CountBand`) gives `≤ 10³¹·(...)`, summed by the
band-budget induction `step2_count_window`.  `C = (K_band+1)·10³¹ = 179·10³¹`.
-/

open Classical
open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- Split a `[a,b]`-restricted `ℕ`-filter at a real breakpoint `s`: the card is at most the sum of
the `[a,s]`- and `[s,b]`-restricted cards. -/
private theorem filter_band_split (F : Finset ℕ) (pr : ℕ → Prop)
    (a b s : ℝ) :
    ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)).card : ℝ)
      ≤ ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s ∧ pr r)).card : ℝ)
        + ((F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)).card : ℝ) := by
  classical
  have hsub : F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)
      ⊆ (F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s ∧ pr r))
        ∪ (F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrF, ha, hb, hpr⟩ := hr
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt (r:ℝ) s with hle | hgt
    · exact Or.inl ⟨hrF, ha, hle, hpr⟩
    · exact Or.inr ⟨hrF, le_of_lt hgt, hb, hpr⟩
  calc ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)).card : ℝ)
      ≤ (((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s ∧ pr r))
          ∪ (F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by exact_mod_cast Finset.card_union_le _ _

/-- A `[a,b]`-restricted `ℕ`-filter that holds at most one integer (`b ≤ a`) has card `≤ 1`. -/
private theorem filter_band_degen (F : Finset ℕ) (pr : ℕ → Prop)
    (a b : ℝ) (hba : b < a + 1) :
    ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)).card : ℝ) ≤ 1 := by
  classical
  -- all members equal `⌈a⌉` (the unique integer in `[a, a+1)`), so the filter is a subsingleton.
  have hsub : (F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b ∧ pr r)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨_, hax, hxb, _⟩ := hx
    obtain ⟨_, hay, hyb, _⟩ := hy
    -- both `x`, `y` lie in `[a, a+1)`, so `|x - y| < 1`; as naturals, `x = y`.
    have hxylt : (x:ℝ) < (y:ℝ) + 1 := by linarith [lt_of_le_of_lt hxb hba, hay]
    have hyxlt : (y:ℝ) < (x:ℝ) + 1 := by linarith [lt_of_le_of_lt hyb hba, hax]
    have hxy : x < y + 1 := by exact_mod_cast hxylt
    have hyx : y < x + 1 := by exact_mod_cast hyxlt
    omega
  exact_mod_cast hsub

/-- **Band-budget tiling.**  With band ratio `λ = (51/50)²`, if the interval `[a,b]` fits in `k`
narrow bands (`b ≤ λ^k·a`, `(1/72)S.R ≤ a ≤ b ≤ 16S.R − ℓ₁`), then the count of `F`-members in
`[a,b]` (each near a `φ_f`-integer, `distInt ≤ δ`) is `≤ (k+1)·10³¹·q`, with
`q = S.R·(δ+√(δ/T₀)) + T₀ + 1`.  Induction on `k`, peeling the bottom band `[a, min(b,λ²a)]`
(bounded by `step2_band_count`) off `[a,b]` via `filter_band_split`. -/
private theorem step2_count_window {a₀ ℓ₁ ℓ₂ f δ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a₀)
    (ha_lo : S.A / 5 ≤ a₀) (ha_hi : a₀ ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ1_lo : 1 ≤ ℓ₁)
    (hsmall : (10:ℝ) ^ 33 * ℓ₁ ≤ S.R)
    (hδ : 0 < δ)
    (hflarge : (10:ℝ) ^ 90 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (P.G * S.Ω ^ 5)) ≤ |f|)
    (F : Finset ℕ)
    (hFdist : ∀ r ∈ F, Counting.distInt (phif P.X a₀ ℓ₁ ℓ₂ f (r : ℝ)) ≤ δ) :
    ∀ (k : ℕ) (a b : ℝ), (1/72) * S.R ≤ a → a ≤ b → b + ℓ₁ ≤ 16 * S.R →
      b ≤ (51 / 50) ^ (2 * k) * a →
      ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ)
        ≤ ((k : ℝ) + 1) * (10 ^ 31 * (S.R * (δ + Real.sqrt (δ / (|f| * S.D ^ 4 / (P.X * S.A))))
            + (|f| * S.D ^ 4 / (P.X * S.A)) + 1)) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; have := P.H_pos; have := S.Δ_pos; positivity
  have hApos : 0 < S.A := by unfold Scale.A; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hfabs_pos : 0 < |f| := lt_of_lt_of_le (by
    have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
    have hℓ2 : 0 < ℓ₂ := by linarith
    have := P.G_pos; have := S.Ω_pos; positivity) hflarge
  set Cq : ℝ := 10 ^ 31 * (S.R * (δ + Real.sqrt (δ / (|f| * S.D ^ 4 / (P.X * S.A))))
      + (|f| * S.D ^ 4 / (P.X * S.A)) + 1) with hCq_def
  have hsqnn : 0 ≤ Real.sqrt (δ / (|f| * S.D ^ 4 / (P.X * S.A))) := Real.sqrt_nonneg _
  have hT0pos : 0 < |f| * S.D ^ 4 / (P.X * S.A) := by have := P.X_pos; positivity
  have hCq_nn : 0 ≤ Cq := by rw [hCq_def]; nlinarith [hRpos.le, hδ.le, hT0pos.le, hsqnn]
  have hCqge1 : (1:ℝ) ≤ Cq := by rw [hCq_def]; nlinarith [hRpos.le, hδ.le, hT0pos.le, hsqnn]
  intro k
  induction k with
  | zero =>
    intro a b ha hab hbwin hgeo
    -- `λ^0 = 1`, so `b ≤ a`; the band holds at most one integer.
    simp only [Nat.mul_zero, pow_zero, one_mul] at hgeo
    have hdeg : ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ) ≤ 1 := by
      have := filter_band_degen F (fun _ => True) a b (by linarith [hgeo])
      simpa using this
    have hgoal : ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ)
        ≤ (((0:ℕ):ℝ) + 1) * Cq := by
      rw [Nat.cast_zero, zero_add, one_mul]; exact le_trans hdeg hCqge1
    exact hgoal
  | succ k ih =>
    intro a b ha hab hbwin hgeo
    set lam : ℝ := (51 / 50) ^ 2 with hlam_def
    have hlam_pos : 0 < lam := by rw [hlam_def]; positivity
    have hlam_ge1 : (1:ℝ) ≤ lam := by rw [hlam_def]; norm_num
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
    -- bottom band `[a, s]` with `s = min b (λ²·a)`.
    set s : ℝ := min b (lam * a) with hs_def
    have hs_le_b : s ≤ b := min_le_left _ _
    have ha_le_s : a ≤ s := by
      rw [hs_def, le_min_iff]; exact ⟨hab, by nlinarith [hlam_ge1, hapos]⟩
    have hs_narrow : s ≤ lam * a := min_le_right _ _
    have hswin : s + ℓ₁ ≤ 16 * S.R := by linarith [hs_le_b, hbwin]
    -- split the count at `s`
    have hsplit := filter_band_split F (fun _ => True) a b s
    simp only [and_true] at hsplit
    -- BOTTOM band `[a,s]`: bounded by `step2_band_count` (or trivially `≤ 1` if degenerate).
    have hbot : ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s)).card : ℝ) ≤ Cq := by
      rcases eq_or_lt_of_le ha_le_s with hdeg | hlt
      · -- a = s: single point.
        have := filter_band_degen F (fun _ => True) a s (by rw [← hdeg]; linarith)
        simp only [and_true] at this
        calc _ ≤ (1:ℝ) := this
          _ ≤ Cq := hCqge1
      · -- a < s: a genuine band, apply `step2_band_count` with `𝒯` = the band filter.
        rw [hCq_def]
        apply step2_band_count (P := P) (S := S) (a := a₀) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
          (r₀ := a) (r₁ := s) (δ := δ)
          hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ1_lo ha hlt hs_narrow hswin hsmall hδ hflarge _
        intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨hrF, hra, hrs⟩ := hr
        exact ⟨hra, hrs, hFdist r hrF⟩
    -- TOP band `[s,b]`: budget `k`, since `b ≤ λ^(k+1)·a = λ^k·(λ²·a)` and `s ≥` ... need `b ≤ λ^k·s`.
    have htop : ((F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ) ≤ ((k:ℝ) + 1) * Cq := by
      by_cases hbs : b ≤ s
      · -- `[s,b]` empty/degenerate (b ≤ s).
        have := filter_band_degen F (fun _ => True) s b (by linarith [hbs])
        simp only [and_true] at this
        calc _ ≤ (1:ℝ) := this
          _ ≤ ((k:ℝ) + 1) * Cq := by nlinarith [hCqge1, (by positivity : (0:ℝ) ≤ (k:ℝ))]
      · -- `s < b`, so `s = λ²·a` (since `s = min b (λ²a) < b`), and `b ≤ λ^(k+1)a = λ^k·s`.
        push_neg at hbs
        -- `min b (lam*a) < b` ⟹ `lam*a < b` ⟹ `s = lam*a`.
        have hlamab : lam * a ≤ b := by
          have hmlt : min b (lam * a) < b := by rw [← hs_def]; exact hbs
          rcases min_lt_iff.mp hmlt with hbb | hla
          · exact absurd hbb (lt_irrefl b)
          · exact le_of_lt hla
        have hs_eq : s = lam * a := by rw [hs_def, min_eq_right hlamab]
        have hgeo' : b ≤ (51 / 50) ^ (2 * k) * s := by
          rw [hs_eq, hlam_def]
          have hpow : (51 / 50 : ℝ) ^ (2 * (k + 1)) = (51 / 50) ^ (2 * k) * (51 / 50) ^ 2 := by
            rw [← pow_add]; congr 1
          rw [hpow] at hgeo
          calc b ≤ (51 / 50) ^ (2 * k) * (51 / 50) ^ 2 * a := hgeo
            _ = (51 / 50) ^ (2 * k) * ((51 / 50) ^ 2 * a) := by ring
        have hs72 : (1/72) * S.R ≤ s := le_trans ha ha_le_s
        exact ih s b hs72 (le_of_lt hbs) hbwin hgeo'
    calc ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ)
        ≤ ((F.filter (fun (r:ℕ) => a ≤ (r:ℝ) ∧ (r:ℝ) ≤ s)).card : ℝ)
          + ((F.filter (fun (r:ℕ) => s ≤ (r:ℝ) ∧ (r:ℝ) ≤ b)).card : ℝ) := hsplit
      _ ≤ Cq + ((k:ℝ) + 1) * Cq := by linarith [hbot, htop]
      _ = ((((k : ℕ) + 1 : ℕ) : ℝ) + 1) * Cq := by push_cast; ring

/-- **§5 Step-2 per-`f` count (BANDS).**  The BANDS analogue of `Ra_step3_count`: for a fixed
integer `f` (`f`-large at `10⁹⁰`), the set of triples `r ∈ Ra` (with `r+ℓ₁,r+ℓ₂ ∈ Ra`) whose
defect `𝒬(r)` rounds to `f` has card `≤ 186·10³¹·(S.R·(δ + √(δ/T₀)) + T₀ + 1)`, with
`δ = 4·δ₂₃`, `δ₂₃ = S.Δ²·G·U²⁰/(H·Ω⁶)`, `T₀ = |f|·S.D⁴/(P.X·S.A)`.  The window `[(1/72)S.R, 16S.R]`
is tiled by `K_band = 185` narrow bands (ratio `λ = (51/50)²`, `λ^(2·185) ≥ 1152`); the absolute
constant is `C = (185+1)·10³¹ = 186·10³¹`. -/
theorem Ra_step2_count {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    {f : ℤ}
    (hflarge : (10:ℝ) ^ 90 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
        / (P.G * S.Ω ^ 5)) ≤ |(f : ℝ)|)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
        round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ)
      ≤ 186 * 10 ^ 31 * (S.R * (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
            + Real.sqrt (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
                / (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A))))
          + (|(f : ℝ)| * S.D ^ 4 / (P.X * S.A)) + 1) := by
  classical
  have hHpos := P.H_pos
  have hΔpos := S.Δ_pos
  have hUpos := P.U_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  -- abbreviations
  set δ : ℝ := 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) with hδ_def
  have hδpos : 0 < δ := by rw [hδ_def]; have := S.Ω_pos; have := P.G_pos; positivity
  set T₀ : ℝ := |(f : ℝ)| * S.D ^ 4 / (P.X * S.A) with hT0_def
  -- `hsmall : 10³³·ℓ₁ ≤ S.R` (chain through Wval / U·W ≤ R), as in Ra_step3_count.
  have hWpos : (0 : ℝ) < P.Wval := by rw [Globals.Wval]; have := P.G_pos; positivity
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  have hℓ1W : ((ℓ₁ : ℤ) : ℝ) ≤ 130 * P.Wval := by linarith [hℓ2W, hℓ12R]
  have hRUW : 130 * (P.U * P.Wval) ≤ S.R :=
    U_mul_W130_le_R (S := S) h1 hband hΩU hΔ1 hU1 hUbig hG1
  have hsmall : (10:ℝ) ^ 33 * ((ℓ₁ : ℤ) : ℝ) ≤ S.R := by
    have hWnn : (0:ℝ) ≤ 130 * P.Wval := by
      rw [Globals.Wval]; have := P.G_pos; positivity
    calc (10:ℝ) ^ 33 * ((ℓ₁ : ℤ) : ℝ)
        ≤ (10:ℝ) ^ 33 * (130 * P.Wval) := by
          apply mul_le_mul_of_nonneg_left hℓ1W (by positivity)
      _ ≤ P.U * (130 * P.Wval) := mul_le_mul_of_nonneg_right hUbig hWnn
      _ = 130 * (P.U * P.Wval) := by ring
      _ ≤ S.R := hRUW
  -- the §5 window value `a` (real-valued phase center)
  set ar : ℝ := (a : ℝ) with har_def
  have har0 : 0 < ar := by rw [har_def]; exact_mod_cast ha0
  have hℓ1r : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  -- the filter set `F`
  set F : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
      round (Qval P a dStar ℓ₁ ℓ₂ r) = f) with hF_def
  -- every `r ∈ F` has `distInt(φ_f r) ≤ δ`  (via `phif_distInt_from_witness`, as in Ra_step3_count)
  have hFdist : ∀ r ∈ F, Counting.distInt (phif P.X ar ((ℓ₁:ℤ):ℝ) ((ℓ₂:ℤ):ℝ) (f:ℝ) (r : ℝ)) ≤ δ := by
    intro r hr
    rw [hF_def, Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1Ra, hr2Ra, hround⟩ := hr
    obtain ⟨hin0, hlo0, hhi0, hRd0, hwlo0, hwhi0⟩ := hdStar r hrRa
    obtain ⟨hin1, hlo1, hhi1, hRd1, hwlo1, hwhi1⟩ := hdStar (r + ℓ₁) hr1Ra
    obtain ⟨hin2, hlo2, hhi2, hRd2, hwlo2, hwhi2⟩ := hdStar (r + ℓ₂) hr2Ra
    have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
    have hcast2 : ((r + ℓ₂ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast1] at hRd1 hwhi1 hwlo1
    rw [hcast2] at hRd2 hwhi2 hwlo2
    have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
    have hd0pos : (0 : ℝ) < (dStar r : ℝ) := lt_of_lt_of_le hDpos hlo0
    have hd1pos : (0 : ℝ) < (dStar (r + ℓ₁) : ℝ) := lt_of_lt_of_le hDpos hlo1
    have hd2pos : (0 : ℝ) < (dStar (r + ℓ₂) : ℝ) := lt_of_lt_of_le hDpos hlo2
    -- `Δ > 28` for the non-degeneracy.
    have hΔbig : (28 : ℝ) < S.Δ := by
      have hU5 : P.U ≤ P.U ^ 5 := by
        nlinarith [pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ) ≤ (10:ℝ)^33) hUbig)
          (by norm_num : (1:ℕ) ≤ 5), hUpos]
      have hG2 : (1 : ℝ) ≤ P.G ^ 2 := by nlinarith [hG1]
      have : P.U ^ 5 ≤ P.G ^ 2 * P.U ^ 5 := by nlinarith [hG2, pow_pos hUpos 5]
      have h28 : (28 : ℝ) ≤ P.U := by nlinarith [hUbig]
      nlinarith [hΔreg, this, hU5, h28]
    have hd1ned : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ) := by
      intro hcontra
      rw [hcontra] at hRd1
      have htri : ((ℓ₁ : ℤ) : ℝ) ≤ 28 * P.H / S.D := by
        have hk := abs_sub_le ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))
          (Rfun P.X (a : ℝ) (dStar r : ℝ)) (r : ℝ)
        have habs1 : |(r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - Rfun P.X (a : ℝ) (dStar r : ℝ)|
            ≤ 14 * P.H / S.D := by rw [abs_sub_comm]; exact hRd1
        have heq : |(r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - (r : ℝ)| = ((ℓ₁ : ℤ) : ℝ) := by
          rw [show (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) - (r : ℝ) = ((ℓ₁ : ℤ) : ℝ) by ring]
          exact abs_of_nonneg (by linarith [hℓ1R])
        rw [heq] at hk
        calc ((ℓ₁ : ℤ) : ℝ) ≤ 14 * P.H / S.D + 14 * P.H / S.D :=
              le_trans hk (by linarith [hRd0, habs1])
          _ = 28 * P.H / S.D := by ring
      have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
        rw [show S.D = P.H * S.Δ from rfl, mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
      rw [hsimp] at htri
      have hmul : ((ℓ₁ : ℤ) : ℝ) * S.Δ ≤ 28 := by rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
      have hge : S.Δ ≤ ((ℓ₁ : ℤ) : ℝ) * S.Δ := by
        have := mul_le_mul_of_nonneg_right hℓ1R (le_of_lt hΔpos); linarith [this]
      linarith [hmul, hge, hΔbig]
    have hd2ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ) := by
      have hℓ2R : (1 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := by
        have : (1:ℤ) ≤ (ℓ₂:ℤ) := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hℓ1 hℓ12))
        exact_mod_cast this
      intro hcontra
      rw [hcontra] at hRd2
      have htri : ((ℓ₂ : ℤ) : ℝ) ≤ 28 * P.H / S.D := by
        have hk := abs_sub_le ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))
          (Rfun P.X (a : ℝ) (dStar r : ℝ)) (r : ℝ)
        have habs2 : |(r : ℝ) + ((ℓ₂ : ℤ) : ℝ) - Rfun P.X (a : ℝ) (dStar r : ℝ)|
            ≤ 14 * P.H / S.D := by rw [abs_sub_comm]; exact hRd2
        have heq : |(r : ℝ) + ((ℓ₂ : ℤ) : ℝ) - (r : ℝ)| = ((ℓ₂ : ℤ) : ℝ) := by
          rw [show (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) - (r : ℝ) = ((ℓ₂ : ℤ) : ℝ) by ring]
          exact abs_of_nonneg (by linarith [hℓ2R])
        rw [heq] at hk
        calc ((ℓ₂ : ℤ) : ℝ) ≤ 14 * P.H / S.D + 14 * P.H / S.D :=
              le_trans hk (by linarith [hRd0, habs2])
          _ = 28 * P.H / S.D := by ring
      have hsimp : 28 * P.H / S.D = 28 / S.Δ := by
        rw [show S.D = P.H * S.Δ from rfl, mul_comm (28:ℝ) P.H, mul_div_mul_left _ _ (ne_of_gt hHpos)]
      rw [hsimp] at htri
      have hmul : ((ℓ₂ : ℤ) : ℝ) * S.Δ ≤ 28 := by rw [le_div_iff₀ hΔpos] at htri; linarith [htri]
      have hge : S.Δ ≤ ((ℓ₂ : ℤ) : ℝ) * S.Δ := by
        have := mul_le_mul_of_nonneg_right hℓ2R (le_of_lt hΔpos); linarith [this]
      linarith [hmul, hge, hΔbig]
    have h𝒬 : Qval P a dStar ℓ₁ ℓ₂ r
        = ((ℓ₁ : ℤ) : ℝ) * Fab P.X (a : ℝ) ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ)) (dStar r : ℝ)
          - ((ℓ₂ : ℤ) : ℝ) * Fab P.X (a : ℝ)
              ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) (dStar r : ℝ) := by
      simp only [Qval, Fab]
      rw [show (dStar r : ℝ) + ((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ)) = (dStar (r + ℓ₂) : ℝ) by ring,
        show (dStar r : ℝ) + ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) = (dStar (r + ℓ₁) : ℝ) by ring]
      push_cast; ring
    have hf_near : |(f : ℝ) - Qval P a dStar ℓ₁ ℓ₂ r|
        ≤ ((ℓ₁ : ℤ) : ℝ) * (2 * P.H / (dStar r : ℝ) ^ 2 + 2 * P.H / (dStar (r + ℓ₂) : ℝ) ^ 2)
          + ((ℓ₂ : ℤ) : ℝ)
              * (2 * P.H / (dStar r : ℝ) ^ 2 + 2 * P.H / (dStar (r + ℓ₁) : ℝ) ^ 2) := by
      have heqd : |(f : ℝ) - Qval P a dStar ℓ₁ ℓ₂ r|
          = Counting.distInt (Qval P a dStar ℓ₁ ℓ₂ r) := by
        rw [Counting.distInt, abs_sub_comm, hround]
      rw [heqd, show Qval P a dStar ℓ₁ ℓ₂ r
          = ((ℓ₁:ℤ):ℝ) * (Ffun P.X (a:ℝ) (dStar r : ℝ) - Ffun P.X (a:ℝ) (dStar (r+ℓ₂) : ℝ))
            - ((ℓ₂:ℤ):ℝ)
                * (Ffun P.X (a:ℝ) (dStar r : ℝ) - Ffun P.X (a:ℝ) (dStar (r+ℓ₁) : ℝ)) by
        simp only [Qval]; push_cast; ring]
      exact Q_distInt_le (X := P.X) (H := P.H) (a := a)
        (d := dStar r) (d₁ := dStar (r + ℓ₁)) (d₂ := dStar (r + ℓ₂))
        (ℓ₁ := (ℓ₁:ℤ)) (ℓ₂ := (ℓ₂:ℤ))
        P.X_pos ha0 hd0pos hd1pos hd2pos (by exact_mod_cast (Nat.zero_le ℓ₁))
        (by exact_mod_cast (Nat.zero_le ℓ₂)) hin0 hin1 hin2
    have hfinal := phif_distInt_from_witness (P := P) (S := S) (a := a) (r := (r:ℝ))
      (ℓ₁ := (ℓ₁:ℤ)) (ℓ₂ := (ℓ₂:ℤ)) (d := dStar r) (d₁ := dStar (r + ℓ₁)) (d₂ := dStar (r + ℓ₂))
      (𝒬 := Qval P a dStar ℓ₁ ℓ₂ r) (f := f)
      hAD ha0 ha_lo ha_hi (by exact_mod_cast hℓ1) (by exact_mod_cast hℓ1)
      (by exact_mod_cast hℓ12) hℓ2W hwlo0 (by linarith [hwhi1]) (by linarith [hwhi2])
      hin0 hin1 hin2 ⟨hlo0, hhi0⟩ ⟨hlo1, hhi1⟩ ⟨hlo2, hhi2⟩
      hRd0 hRd1 hRd2 hd1ned hd2ned h𝒬 hf_near
      h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg
    rw [hδ_def, har_def]; exact hfinal
  -- apply the tiling at `a = (1/72)S.R`, `b = 16S.R − ℓ₁`, budget `K_band = 185`.
  have hwindow := step2_count_window (P := P) (S := S) (a₀ := ar) (ℓ₁ := ((ℓ₁:ℤ):ℝ))
    (ℓ₂ := ((ℓ₂:ℤ):ℝ)) (f := (f:ℝ)) (δ := δ)
    hAD har0 ha_lo ha_hi hℓ1r hℓ12R hℓ1R hsmall hδpos hflarge F hFdist 185
    ((1/72) * S.R) (16 * S.R - ((ℓ₁:ℤ):ℝ))
  -- discharge the four geometric hypotheses of `step2_count_window`.
  have hℓ1leR : ((ℓ₁:ℤ):ℝ) ≤ S.R := by
    have : ((ℓ₁:ℤ):ℝ) ≤ (10:ℝ)^33 * ((ℓ₁:ℤ):ℝ) := by nlinarith [hℓ1R]
    linarith [hsmall, this]
  have ha_le_b : (1/72) * S.R ≤ 16 * S.R - ((ℓ₁:ℤ):ℝ) := by linarith [hℓ1leR, hRpos]
  have hbwin : (16 * S.R - ((ℓ₁:ℤ):ℝ)) + ((ℓ₁:ℤ):ℝ) ≤ 16 * S.R := by linarith
  have hgeo : 16 * S.R - ((ℓ₁:ℤ):ℝ) ≤ (51 / 50) ^ (2 * 185) * ((1/72) * S.R) := by
    have hpowge : (1152 : ℝ) ≤ (51 / 50) ^ (2 * 185) := by
      -- `1152·50^370 ≤ 51^370` (ℕ), so `1152 ≤ (51/50)^370`.
      have hnat : (1152 : ℕ) * 50 ^ 370 ≤ 51 ^ 370 := by decide
      have hR : (1152 : ℝ) * (50:ℝ) ^ 370 ≤ (51:ℝ) ^ 370 := by exact_mod_cast hnat
      have h50 : (0:ℝ) < (50:ℝ) ^ 370 := by positivity
      have hpoweq : (51 / 50 : ℝ) ^ (2 * 185) = (51:ℝ) ^ 370 / (50:ℝ) ^ 370 := by
        rw [show (2 * 185 : ℕ) = 370 from rfl, div_pow]
      rw [hpoweq, le_div_iff₀ h50]
      exact hR
    have hub : 16 * S.R - ((ℓ₁:ℤ):ℝ) ≤ 1152 * ((1/72) * S.R) := by
      have : (1152 : ℝ) * ((1/72) * S.R) = 16 * S.R := by ring
      rw [this]; linarith [hℓ1r]
    calc 16 * S.R - ((ℓ₁:ℤ):ℝ) ≤ 1152 * ((1/72) * S.R) := hub
      _ ≤ (51 / 50) ^ (2 * 185) * ((1/72) * S.R) :=
            mul_le_mul_of_nonneg_right hpowge (by positivity)
  have hcount := hwindow (le_refl _) ha_le_b hbwin hgeo
  -- the filter `F` equals the `[(1/72)S.R, 16S.R−ℓ₁]`-band filter (every member is in the window).
  have hFsub : F.filter (fun (r:ℕ) => (1/72) * S.R ≤ (r:ℝ) ∧ (r:ℝ) ≤ 16 * S.R - ((ℓ₁:ℤ):ℝ)) = F := by
    apply Finset.filter_true_of_mem
    intro r hr
    rw [hF_def, Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1Ra, _, _⟩ := hr
    obtain ⟨_, _, _, _, hwlo0, _⟩ := hdStar r hrRa
    obtain ⟨_, _, _, _, _, hwhi1⟩ := hdStar (r + ℓ₁) hr1Ra
    have hcast1 : ((r + ℓ₁ : ℕ) : ℝ) = (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast1] at hwhi1
    exact ⟨hwlo0, by linarith [hwhi1]⟩
  -- assemble: rewrite the count target in terms of `δ`, `T₀`, and the band-filter.
  rw [hF_def] at hFsub
  have hKcast : (((185 : ℕ) : ℝ) + 1) = 186 := by norm_num
  calc ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
          round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ)
      = (((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧
          round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).filter
          (fun (r:ℕ) => (1/72) * S.R ≤ (r:ℝ) ∧ (r:ℝ) ≤ 16 * S.R - ((ℓ₁:ℤ):ℝ))).card : ℝ) := by
        rw [hFsub]
    _ ≤ (((185 : ℕ) : ℝ) + 1) * (10 ^ 31 * (S.R * (δ + Real.sqrt (δ / T₀)) + T₀ + 1)) := hcount
    _ = 186 * 10 ^ 31 * (S.R * (δ + Real.sqrt (δ / T₀)) + T₀ + 1) := by rw [hKcast]; ring

end Squarefree
