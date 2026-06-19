import Squarefree.Counting.Preimage
import Mathlib

/-!
# §4 derivative-band counting (Lemma 4.2)

Proof of the derivative-band counting lemma from `../explicit_writeup.md` (lines 426–461).

The writeup uses a `log(T/δ)`-many dyadic band partition, which introduces a stray `log` not
present in the stated bound.  We instead use a **fixed, `O(1)`-many** band partition keyed to the
balance points `√(δT)/N`, `√T/N`, `T/(4N)`, giving the log-free conclusion
`N(δ+√(δ/T)) + T + 1`.  See `CLAUDE.md` §3/§4/§7.

## Structure

* `card_filter_le_length` — trivial cardinality bound (`count ≤ b - a + 1`).
* `bands_count_trivial` — the regime `T ≤ 4δ`, where the trivial bound already suffices.
* `bands_count_active` — the active regime `4δ < T`; the genuine band decomposition lives here
  (currently a tracked concrete stub — see §4).
* `bands_count` — assembles the two regimes into the faithful public statement.
-/

open Classical Finset

namespace Squarefree.Counting

/-- The number of near-integer points in `[a,b]` is at most the number of integers in `[a,b]`,
which as a real is `≤ b - a + 1`.  This is the universal crude bound. -/
theorem card_filter_le_length (a b δ : ℝ) (φ : ℝ → ℝ) (hab : a ≤ b) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (b - a) + 1 := by
  classical
  have hcard_le : ((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card
      ≤ (Finset.Icc ⌈a⌉ ⌊b⌋).card :=
    Finset.card_filter_le (Finset.Icc ⌈a⌉ ⌊b⌋) (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)
  -- `(Finset.Icc ⌈a⌉ ⌊b⌋).card = (⌊b⌋ + 1 - ⌈a⌉).toNat`.
  have hcast : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ (b - a) + 1 := by
    have h1 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
    have h2 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
    have hcardeq : (Finset.Icc ⌈a⌉ ⌊b⌋).card = (⌊b⌋ + 1 - ⌈a⌉).toNat := Int.card_Icc _ _
    rw [hcardeq]
    -- `(m.toNat : ℝ) ≤ (m : ℝ)` always (it's `max m 0 ≥ m`... here `m.toNat ≤ m` as ints fails;
    -- instead bound `m.toNat ≤ |m| ≤ m+` — easiest: `(m.toNat : ℝ) ≤ (m : ℝ) when 0 ≤ m`, else 0).
    have htoNatle : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) ≤ (b - a) + 1 := by
      have h3 : ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) ≤ (b - a) + 1 := by push_cast; linarith
      rcases le_or_gt 0 (⌊b⌋ + 1 - ⌈a⌉) with hnn | hneg
      · have hcast2 : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℤ)) = (⌊b⌋ + 1 - ⌈a⌉ : ℤ) :=
          Int.toNat_of_nonneg hnn
        have : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) = ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
          exact_mod_cast hcast2
        rw [this]; exact h3
      · have hz : (⌊b⌋ + 1 - ⌈a⌉).toNat = 0 := Int.toNat_of_nonpos (le_of_lt hneg)
        rw [hz, Nat.cast_zero]
        linarith [hab]
    exact htoNatle
  calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) := by exact_mod_cast hcard_le
    _ ≤ (b - a) + 1 := hcast

/-- **Trivial regime `T ≤ 4δ`.**  Here `√(δ/T) ≥ 1/2`, so the crude bound `count ≤ b - a + 1 ≤ 2N+1`
is already `≤ 4(N√(δ/T) + 1) ≤ 4 · (RHS)`. -/
theorem bands_count_trivial (N T δ a b : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N)) (htriv : T ≤ 4 * δ) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 4 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  classical
  -- Either `[a,b]` is empty (count is 0) or `a ≤ b` and `[a,b] ⊆ [N,3N]`.
  rcases le_or_gt a b with hab | hba
  · -- `a ≤ b`: use the crude length bound, and `a,b ∈ [N,3N]`.
    have haIcc : a ∈ Set.Icc N (3 * N) := hsub ⟨le_refl a, hab⟩
    have hbIcc : b ∈ Set.Icc N (3 * N) := hsub ⟨hab, le_refl b⟩
    have hb_le : b ≤ 3 * N := hbIcc.2
    have ha_ge : N ≤ a := haIcc.1
    have hlen : (b - a) + 1 ≤ 2 * N + 1 := by linarith
    -- `√(δ/T) ≥ 1/2` since `δ/T ≥ 1/4`.
    have hratio : (1 : ℝ) / 4 ≤ δ / T := by
      rw [le_div_iff₀ hT]; linarith
    have hsqrt_half : (1 : ℝ) / 2 ≤ Real.sqrt (δ / T) := by
      have h := Real.sqrt_le_sqrt hratio
      rwa [show Real.sqrt ((1:ℝ)/4) = 1/2 by
        rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have hcount := card_filter_le_length a b δ φ hab
    have hNsqrt : N ≤ 2 * N * Real.sqrt (δ / T) := by nlinarith [hN.le, hsqrt_half]
    have hRHS_nonneg : 0 ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
      have : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
      nlinarith [hN.le, hδ.le, hT.le]
    calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ (b - a) + 1 := hcount
      _ ≤ 2 * N + 1 := hlen
      _ ≤ 4 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
          have hsq : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
          nlinarith [hNsqrt, hN.le, hδ.le, hT.le]
  · -- `b < a`: the interval `[a,b]` is empty, so `Finset.Icc ⌈a⌉ ⌊b⌋ = ∅`.
    have hltceil : ⌊b⌋ < ⌈a⌉ := by
      have h1 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
      have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
      have : (⌊b⌋ : ℝ) < (⌈a⌉ : ℝ) := by linarith
      exact_mod_cast this
    have hempty : (Finset.Icc ⌈a⌉ ⌊b⌋) = ∅ := Finset.Icc_eq_empty (by omega)
    have hzero : ((Finset.Icc ⌈a⌉ ⌊b⌋).filter
        (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card = 0 := by
      rw [hempty]; simp
    rw [hzero]
    simp only [Nat.cast_zero]
    have : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
    nlinarith [hN.le, hδ.le, hT.le]

/-- **MVT expansion (lower bound).**  If `φ` is differentiable and `|φ'| ≥ F` on all of `[p,q]`,
then `φ` expands distances by `F` on `[p,q]`: `F·|x-y| ≤ |φ x - φ y|`.  (The `preimage_count`
`F`-expansion hypothesis.) -/
theorem mvt_expand_lower (p q F : ℝ) (φ : ℝ → ℝ)
    (hdiff : Differentiable ℝ φ)
    (hlb : ∀ z ∈ Set.Icc p q, F ≤ |deriv φ z|) :
    ∀ x ∈ Set.Icc p q, ∀ y ∈ Set.Icc p q, F * |x - y| ≤ |φ x - φ y| := by
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · -- `x < y`: apply MVT on `[x,y] ⊆ [p,q]`.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope φ hxy
      (hdiff.continuous.continuousOn) (hdiff.differentiableOn)
    have hcIcc : c ∈ Set.Icc p q := by
      refine ⟨?_, ?_⟩
      · exact le_trans hx.1 (le_of_lt hc.1)
      · exact le_trans (le_of_lt hc.2) hy.2
    have hFc : F ≤ |deriv φ c| := hlb c hcIcc
    have hne : y - x ≠ 0 := by linarith
    have : |deriv φ c| = |φ y - φ x| / |y - x| := by
      rw [hslope, abs_div]
    rw [this] at hFc
    rw [le_div_iff₀ (by positivity : (0:ℝ) < |y - x|)] at hFc
    calc F * |x - y| = F * |y - x| := by rw [abs_sub_comm]
      _ ≤ |φ y - φ x| := hFc
      _ = |φ x - φ y| := by rw [abs_sub_comm]
  · subst hxy; simp
  · -- `y < x`: symmetric.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope φ hxy
      (hdiff.continuous.continuousOn) (hdiff.differentiableOn)
    have hcIcc : c ∈ Set.Icc p q := by
      refine ⟨?_, ?_⟩
      · exact le_trans hy.1 (le_of_lt hc.1)
      · exact le_trans (le_of_lt hc.2) hx.2
    have hFc : F ≤ |deriv φ c| := hlb c hcIcc
    have hne : x - y ≠ 0 := by linarith
    have : |deriv φ c| = |φ x - φ y| / |x - y| := by
      rw [hslope, abs_div]
    rw [this] at hFc
    rw [le_div_iff₀ (by positivity : (0:ℝ) < |x - y|)] at hFc
    linarith [hFc]

/-- General MVT distance bound: `|φ x - φ y| ≤ G·|x - y|` when `|φ'| ≤ G` between `x` and `y`. -/
private theorem mvt_dist_le (G : ℝ) (φ : ℝ → ℝ) (hdiff : Differentiable ℝ φ)
    {x y : ℝ} (hub : ∀ z ∈ Set.Icc (min x y) (max x y), |deriv φ z| ≤ G) :
    |φ x - φ y| ≤ G * |x - y| := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope φ hlt
      (hdiff.continuous.continuousOn) (hdiff.differentiableOn)
    have hmin : min x y = x := min_eq_left (le_of_lt hlt)
    have hmax : max x y = y := max_eq_right (le_of_lt hlt)
    have hcIcc : c ∈ Set.Icc (min x y) (max x y) := by
      rw [hmin, hmax]; exact ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hGc : |deriv φ c| ≤ G := hub c hcIcc
    have hne : (0:ℝ) < |y - x| := by rw [abs_pos]; exact fun h => by linarith [sub_eq_zero.mp h]
    have heq2 : |φ y - φ x| = |deriv φ c| * |y - x| := by
      rw [hslope, abs_div, div_mul_cancel₀ _ (ne_of_gt hne)]
    calc |φ x - φ y| = |φ y - φ x| := abs_sub_comm _ _
      _ = |deriv φ c| * |y - x| := heq2
      _ ≤ G * |y - x| := by apply mul_le_mul_of_nonneg_right hGc (abs_nonneg _)
      _ = G * |x - y| := by rw [abs_sub_comm]
  · subst heq; simp
  · obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope φ hgt
      (hdiff.continuous.continuousOn) (hdiff.differentiableOn)
    have hmin : min x y = y := min_eq_right (le_of_lt hgt)
    have hmax : max x y = x := max_eq_left (le_of_lt hgt)
    have hcIcc : c ∈ Set.Icc (min x y) (max x y) := by
      rw [hmin, hmax]; exact ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hGc : |deriv φ c| ≤ G := hub c hcIcc
    have hne : (0:ℝ) < |x - y| := by rw [abs_pos]; exact fun h => by linarith [sub_eq_zero.mp h]
    have heq2 : |φ x - φ y| = |deriv φ c| * |x - y| := by
      rw [hslope, abs_div, div_mul_cancel₀ _ (ne_of_gt hne)]
    calc |φ x - φ y| = |deriv φ c| * |x - y| := heq2
      _ ≤ G * |x - y| := by apply mul_le_mul_of_nonneg_right hGc (abs_nonneg _)

/-- **MVT variation (upper bound).**  If `φ` is differentiable and `|φ'| ≤ G` on all of `[p,q]`,
then `φ` varies by at most `G·(q-p)` on `[p,q]`.  (The `preimage_count` `V`-variation
hypothesis, with `V = G·(q-p)`.) -/
theorem mvt_var_upper (p q G : ℝ) (φ : ℝ → ℝ) (hpq : p ≤ q)
    (hdiff : Differentiable ℝ φ)
    (hub : ∀ z ∈ Set.Icc p q, |deriv φ z| ≤ G) :
    ∀ x ∈ Set.Icc p q, ∀ y ∈ Set.Icc p q, |φ x - φ y| ≤ G * (q - p) := by
  have hG : 0 ≤ G := le_trans (abs_nonneg _) (hub p ⟨le_refl p, hpq⟩)
  intro x hx y hy
  have hsub : Set.Icc (min x y) (max x y) ⊆ Set.Icc p q := by
    apply Set.Icc_subset_Icc
    · exact le_min hx.1 hy.1
    · exact max_le hx.2 hy.2
  have hxy_bound : |φ x - φ y| ≤ G * |x - y| :=
    mvt_dist_le G φ hdiff (fun z hz => hub z (hsub hz))
  calc |φ x - φ y| ≤ G * |x - y| := hxy_bound
    _ ≤ G * (q - p) := by
        apply mul_le_mul_of_nonneg_left _ hG
        rw [abs_le]
        exact ⟨by have := hx.1; have := hy.2; linarith, by have := hx.2; have := hy.1; linarith⟩

/-- **Uniform band bound.**  On a sub-interval `[u,v]` where `F ≤ |φ'| ≤ G` (with `0 < F`),
combine the MVT `F`-expansion and `G`-variation with `preimage_count` to bound the near-integer
count by `(G(v-u) + 2δ + 1)(2δ/F + 1)`.  This is the per-band engine. -/
theorem band_count_uniform (u v F G δ : ℝ) (φ : ℝ → ℝ)
    (hdiff : Differentiable ℝ φ) (huv : u ≤ v) (hF : 0 < F) (hδ : 0 ≤ δ)
    (hlb : ∀ z ∈ Set.Icc u v, F ≤ |deriv φ z|)
    (hub : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ G) :
    (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (G * (v - u) + 2 * δ + 1) * (2 * δ / F + 1) := by
  have hV : 0 ≤ G * (v - u) := by
    have hG : 0 ≤ G := le_trans (abs_nonneg _) (hub u ⟨le_refl u, huv⟩)
    have : 0 ≤ v - u := by linarith
    positivity
  have hexp : ∀ x ∈ Set.Icc u v, ∀ y ∈ Set.Icc u v, F * |x - y| ≤ |φ x - φ y| :=
    mvt_expand_lower u v F φ hdiff hlb
  have hvar : ∀ x ∈ Set.Icc u v, ∀ y ∈ Set.Icc u v, |φ x - φ y| ≤ G * (v - u) :=
    mvt_var_upper u v G φ huv hdiff hub
  exact preimage_count u v (G * (v - u)) F δ φ hF hδ hV hexp hvar

/-- **Curvature fact.**  From the scale lower bound `T/N ≤ |φ'| + N|φ''|` (`hlower`), at any point
where `|φ'(x)| ≤ T/(2N)` we get `|φ''(x)| ≥ T/(2N²)`. -/
theorem curvature_lower (N T : ℝ) (φ : ℝ → ℝ) (hN : 0 < N) {x : ℝ}
    (hlower : T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hsmall : |deriv φ x| ≤ T / (2 * N)) :
    T / (2 * N ^ 2) ≤ |iteratedDeriv 2 φ x| := by
  -- `N|φ''| ≥ T/N - |φ'| ≥ T/N - T/(2N) = T/(2N)`, so `|φ''| ≥ T/(2N²)`.
  have hN2 : (0:ℝ) < N ^ 2 := by positivity
  have h1 : T / N - |deriv φ x| ≤ N * |iteratedDeriv 2 φ x| := by linarith
  have h2 : T / (2 * N) ≤ N * |iteratedDeriv 2 φ x| := by
    have : T / N - T / (2 * N) = T / (2 * N) := by field_simp; ring
    linarith [h1, hsmall]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * N ^ 2)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * N)] at h2
  nlinarith [h2, hN, abs_nonneg (iteratedDeriv 2 φ x)]

/-- **Count splitting at a breakpoint.**  The near-integer count over `[⌈p⌉,⌊q⌋]` splits as the
sum of the counts over `[⌈p⌉,⌊s⌋]` and `[⌈s⌉,⌊q⌋]` for any real breakpoint `s`.  (The integer
intervals cover `[⌈p⌉,⌊q⌋]` since `⌈s⌉ ≤ ⌊s⌋ + 1`.) -/
private theorem count_split (p q s δ : ℝ) (φ : ℝ → ℝ) :
    (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (((Finset.Icc ⌈p⌉ ⌊s⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        + (((Finset.Icc ⌈s⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) := by
  classical
  have hsub : (Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)
      ⊆ ((Finset.Icc ⌈p⌉ ⌊s⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ))
        ∪ ((Finset.Icc ⌈s⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hpn, hnq⟩, hδn⟩ := hn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    rcases le_or_gt n ⌊s⌋ with hle | hgt
    · exact Or.inl ⟨⟨hpn, hle⟩, hδn⟩
    · refine Or.inr ⟨⟨?_, hnq⟩, hδn⟩
      have : ⌈s⌉ ≤ ⌊s⌋ + 1 := Int.ceil_le_floor_add_one s
      omega
  calc (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ ((((Finset.Icc ⌈p⌉ ⌊s⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ))
          ∪ ((Finset.Icc ⌈s⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((Finset.Icc ⌈p⌉ ⌊s⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        + (((Finset.Icc ⌈s⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _

/-- **Low-region length bound.**  On a sub-interval `[s,t]` where the derivative is small
(`|φ'| ≤ F₀`) and the second derivative is large (`|φ''| ≥ T/(2N²)`, from `curvature_lower`),
the monotonicity of `φ'` forces `[s,t]` to be short: its length is at most `4N·F₀·N/T`.
With `F₀ = √(δT)/N` this is `4N√(δ/T)`.

Proof: `φ'` is differentiable with `deriv (deriv φ) = iteratedDeriv 2 φ`, of absolute value
`≥ T/(2N²)` on `[s,t]`.  By the MVT-expansion (`mvt_expand_lower` applied to `deriv φ`),
`(T/(2N²))·(t-s) ≤ |φ'(t) - φ'(s)| ≤ |φ'(t)| + |φ'(s)| ≤ 2F₀`, so `t - s ≤ 4N²F₀/T`. -/
private theorem mono_low_length (N T F₀ s t : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hst : s ≤ t)
    (hcd : ContDiff ℝ 2 φ)
    (hsmall : ∀ z ∈ Set.Icc s t, |deriv φ z| ≤ F₀)
    (hcurv : ∀ z ∈ Set.Icc s t, T / (2 * N ^ 2) ≤ |iteratedDeriv 2 φ z|) :
    t - s ≤ 4 * N ^ 2 * F₀ / T := by
  -- `deriv φ` is differentiable (φ is `C²`), and `deriv (deriv φ) = iteratedDeriv 2 φ`.
  have hdiff1 : Differentiable ℝ (deriv φ) := by
    have h2 : ContDiff ℝ (1 + 1) φ := by norm_num; exact hcd
    have : ContDiff ℝ 1 (deriv φ) := h2.deriv'
    exact this.differentiable (by norm_num)
  have hderiv2 : ∀ z, deriv (deriv φ) z = iteratedDeriv 2 φ z := by
    intro z
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- MVT-expansion for `g := deriv φ` with constant `T/(2N²)`.
  have hcurv' : ∀ z ∈ Set.Icc s t, T / (2 * N ^ 2) ≤ |deriv (deriv φ) z| := by
    intro z hz; rw [hderiv2 z]; exact hcurv z hz
  have hexp := mvt_expand_lower s t (T / (2 * N ^ 2)) (deriv φ) hdiff1 hcurv'
  have hkey : T / (2 * N ^ 2) * |t - s| ≤ |deriv φ t - deriv φ s| :=
    hexp t ⟨hst, le_refl t⟩ s ⟨le_refl s, hst⟩
  have hsmallt : |deriv φ t| ≤ F₀ := hsmall t ⟨hst, le_refl t⟩
  have hsmalls : |deriv φ s| ≤ F₀ := hsmall s ⟨le_refl s, hst⟩
  have hub2 : |deriv φ t - deriv φ s| ≤ 2 * F₀ := by
    calc |deriv φ t - deriv φ s| ≤ |deriv φ t| + |deriv φ s| := abs_sub _ _
      _ ≤ F₀ + F₀ := add_le_add hsmallt hsmalls
      _ = 2 * F₀ := by ring
  have habs : |t - s| = t - s := abs_of_nonneg (by linarith)
  rw [habs] at hkey
  have hchain : T / (2 * N ^ 2) * (t - s) ≤ 2 * F₀ := le_trans hkey hub2
  have hN2 : (0 : ℝ) < 2 * N ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hN2] at hchain
  rw [le_div_iff₀ hT]
  nlinarith [hchain]

/-- **High sub-region count.**  On a sub-interval `[u,v]` where `4δ ≤ |φ'| ≤ T/N`, the fiber bound
`2δ/|φ'| ≤ 1/2` makes `band_count_uniform` give `count ≤ (3/2)·(T/N·(v-u) + 2δ + 1)`.  No blow-up:
the `2δ/F` factor is `≤ 1/2`. -/
private theorem bands_count_mono_high (N T δ u v : ℝ) (φ : ℝ → ℝ)
    (hδ : 0 < δ) (hdiff : Differentiable ℝ φ) (huv : u ≤ v)
    (hlb : ∀ z ∈ Set.Icc u v, 4 * δ ≤ |deriv φ z|)
    (hub : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ T / N) :
    (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (3 / 2) * (T / N * (v - u) + 2 * δ + 1) := by
  have h4δ : (0 : ℝ) < 4 * δ := by linarith
  have hbase := band_count_uniform u v (4 * δ) (T / N) δ φ hdiff huv h4δ hδ.le hlb hub
  -- `2δ/(4δ) + 1 = 3/2`.
  have hfac : 2 * δ / (4 * δ) + 1 = 3 / 2 := by
    field_simp; ring
  rw [hfac] at hbase
  -- `band_count_uniform` gives `≤ (T/N·(v-u) + 2δ + 1)·(3/2)`; commute.
  calc (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (T / N * (v - u) + 2 * δ + 1) * (3 / 2) := hbase
    _ = (3 / 2) * (T / N * (v - u) + 2 * δ + 1) := by ring

/-- **Threshold split for a continuous function.**  If `g` is continuous on `[u,v]`, `g u ≤ c` and
`g v ≥ c`, there is `w ∈ [u,v]` with `g w = c`.  Combined with monotonicity (used at the call site)
this separates the sub-interval into `{g ≤ c}` and `{g ≥ c}` halves.  This is just IVT packaged for
the band split. -/
private theorem exists_crossing (g : ℝ → ℝ) (u v c : ℝ) (huv : u ≤ v)
    (hcont : ContinuousOn g (Set.Icc u v)) (hlo : g u ≤ c) (hhi : c ≤ g v) :
    ∃ w ∈ Set.Icc u v, g w = c := by
  have hmem : c ∈ Set.Icc (g u) (g v) := ⟨hlo, hhi⟩
  obtain ⟨w, hw, hwc⟩ := intermediate_value_Icc huv hcont hmem
  exact ⟨w, hw, hwc⟩

/-- **`|deriv φ|` is continuous on `[u,v]`** for `C²` `φ`. -/
private theorem hcont_abs (φ : ℝ → ℝ) (u v : ℝ) (hcd : ContDiff ℝ 2 φ) :
    ContinuousOn (fun z => |deriv φ z|) (Set.Icc u v) := by
  have hcd1 : ContDiff ℝ 1 (deriv φ) := by
    have h2 : ContDiff ℝ (1 + 1) φ := by norm_num; exact hcd
    exact h2.deriv'
  exact (continuous_abs.comp hcd1.continuous).continuousOn

/-- **`|deriv φ|` is monotone-or-antitone** when `deriv φ` is monotone-or-antitone and of constant
sign.  Four cases: `(≥0, mono) → |·| mono`, `(≥0, anti) → |·| anti`, `(≤0, mono) → |·| anti`,
`(≤0, anti) → |·| mono`.  (`|deriv φ z| = deriv φ z` resp. `= -(deriv φ z)` on the interval.) -/
private theorem abs_deriv_mono_or_anti (φ : ℝ → ℝ) (u v : ℝ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc u v) ∨ AntitoneOn (deriv φ) (Set.Icc u v))
    (hsign : (∀ z ∈ Set.Icc u v, 0 ≤ deriv φ z) ∨ (∀ z ∈ Set.Icc u v, deriv φ z ≤ 0)) :
    MonotoneOn (fun z => |deriv φ z|) (Set.Icc u v)
      ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc u v) := by
  rcases hsign with hpos | hneg
  · have habs : ∀ z ∈ Set.Icc u v, |deriv φ z| = deriv φ z := fun z hz => abs_of_nonneg (hpos z hz)
    rcases hmono with hm | ha
    · exact Or.inl (by
        intro x hx y hy hxy; simp only [habs x hx, habs y hy]; exact hm hx hy hxy)
    · exact Or.inr (by
        intro x hx y hy hxy; simp only [habs x hx, habs y hy]; exact ha hx hy hxy)
  · have habs : ∀ z ∈ Set.Icc u v, |deriv φ z| = -(deriv φ z) :=
      fun z hz => abs_of_nonpos (hneg z hz)
    rcases hmono with hm | ha
    · exact Or.inr (by
        intro x hx y hy hxy; simp only [habs x hx, habs y hy]; exact neg_le_neg (hm hx hy hxy))
    · exact Or.inl (by
        intro x hx y hy hxy; simp only [habs x hx, habs y hy]; exact neg_le_neg (ha hx hy hxy))

/-- **Single-threshold split of a monotone-or-antitone `|φ'|`-interval.**  Given `[u,v]` on which
`|deriv φ|` is monotone-or-antitone and a threshold `t`, there is `w ∈ [u,v]` so that one of the two
sub-intervals `[u,w]`, `[w,v]` is **LOW** (`|φ'| ≤ t`) and the other is **HIGH** (`t ≤ |φ'|`).  The
disjunction records which side is which; in both cases `count[u,v] ≤ count[u,w] + count[w,v]` (via
`count_split`).  This is the engine of the dyadic recursion. -/
private theorem mono_abs_one_split (φ : ℝ → ℝ) (u v t : ℝ) (huv : u ≤ v)
    (hcd : ContDiff ℝ 2 φ)
    (habsmono : MonotoneOn (fun z => |deriv φ z|) (Set.Icc u v)
      ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc u v)) :
    ∃ w, u ≤ w ∧ w ≤ v ∧
      ((∀ z ∈ Set.Icc u w, |deriv φ z| ≤ t) ∨ (∀ z ∈ Set.Icc u w, t ≤ |deriv φ z|)) ∧
      ((∀ z ∈ Set.Icc w v, |deriv φ z| ≤ t) ∨ (∀ z ∈ Set.Icc w v, t ≤ |deriv φ z|)) := by
  rcases habsmono with hinc | hdec
  · -- `|φ'|` increasing: LOW = `[u,w]`, HIGH = `[w,v]`.
    rcases le_or_gt (|deriv φ u|) t with hsmallu | hbigu
    · rcases le_or_gt t (|deriv φ v|) with hbigv | hsmallv
      · obtain ⟨w, hwmem, hwval⟩ := exists_crossing (fun z => |deriv φ z|) u v t huv
          (hcont_abs φ u v hcd) hsmallu hbigv
        refine ⟨w, hwmem.1, hwmem.2, Or.inl ?_, Or.inr ?_⟩
        · intro z hz
          have : |deriv φ z| ≤ |deriv φ w| := hinc ⟨hz.1, le_trans hz.2 hwmem.2⟩ hwmem hz.2
          rw [hwval] at this; exact this
        · intro z hz
          have : |deriv φ w| ≤ |deriv φ z| := hinc hwmem ⟨le_trans hwmem.1 hz.1, hz.2⟩ hz.1
          rw [hwval] at this; exact this
      · -- `|φ'| ≤ t` on all of `[u,v]`: `w = v`, both halves LOW.
        refine ⟨v, huv, le_refl v, Or.inl ?_, Or.inl ?_⟩
        · intro z hz
          have : |deriv φ z| ≤ |deriv φ v| := hinc hz ⟨huv, le_refl v⟩ hz.2
          linarith [hsmallv]
        · intro z hz
          have : z = v := le_antisymm hz.2 hz.1
          subst this; linarith [hsmallv]
    · -- `t ≤ |φ'|` on all: `w = u`, both halves HIGH.
      refine ⟨u, le_refl u, huv, Or.inr ?_, Or.inr ?_⟩
      · intro z hz
        have : z = u := le_antisymm hz.2 hz.1
        subst this; linarith [hbigu]
      · intro z hz
        have : |deriv φ u| ≤ |deriv φ z| := hinc ⟨le_refl u, huv⟩ hz hz.1
        linarith [hbigu]
  · -- `|φ'|` decreasing: HIGH = `[u,w]`, LOW = `[w,v]`.
    rcases le_or_gt (|deriv φ v|) t with hsmallv | hbigv
    · rcases le_or_gt t (|deriv φ u|) with hbigu | hsmallu
      · obtain ⟨w, hwmem, hwval⟩ :
            ∃ w ∈ Set.Icc u v, |deriv φ w| = t := by
          obtain ⟨w, hwmem, hwval⟩ := exists_crossing (fun z => -(|deriv φ z|)) u v (-t) huv
            ((hcont_abs φ u v hcd).neg) (by simpa using hbigu) (by simpa using hsmallv)
          exact ⟨w, hwmem, by simpa using hwval⟩
        refine ⟨w, hwmem.1, hwmem.2, Or.inr ?_, Or.inl ?_⟩
        · intro z hz
          have : |deriv φ w| ≤ |deriv φ z| := hdec ⟨hz.1, le_trans hz.2 hwmem.2⟩ hwmem hz.2
          rw [hwval] at this; exact this
        · intro z hz
          have : |deriv φ z| ≤ |deriv φ w| := hdec hwmem ⟨le_trans hwmem.1 hz.1, hz.2⟩ hz.1
          rw [hwval] at this; exact this
      · -- `|φ'| ≤ t` on all: `w = v`, both halves LOW.
        refine ⟨v, huv, le_refl v, Or.inl ?_, Or.inl ?_⟩
        · intro z hz
          have : |deriv φ z| ≤ |deriv φ u| := hdec ⟨le_refl u, huv⟩ hz hz.1
          linarith [hsmallu]
        · intro z hz
          have : z = v := le_antisymm hz.2 hz.1
          subst this; linarith [hsmallu]
    · -- `t ≤ |φ'|` on all: `w = u`, both halves HIGH.
      have hvu : |deriv φ v| ≤ |deriv φ u| := hdec ⟨le_refl u, huv⟩ ⟨huv, le_refl v⟩ huv
      refine ⟨u, le_refl u, huv, Or.inr ?_, Or.inr ?_⟩
      · intro z hz
        have : z = u := le_antisymm hz.2 hz.1
        subst this; linarith [hbigv, hvu]
      · intro z hz
        have : |deriv φ v| ≤ |deriv φ z| := hdec hz ⟨huv, le_refl v⟩ hz.2
        linarith [hbigv]

/-- **Recursive dyadic band sum.**  On `[u,v]` where `|deriv φ|` is monotone-or-antitone and
`F ≤ |φ'| ≤ 2^J·F` (with `0 < F`), the near-integer count is bounded by the aggregate of `J+1`
dyadic bands `[2^j F, 2^{j+1} F]`:
`count ≤ 4δ(v-u) + 2·(2^J F)(v-u) + 2(2δ+1)(2δ/F) + (J+1)(2δ+1)`.

Proof by induction on `J`, peeling the **bottom** band `[F,2F]` at each step (so the geometric
fiber sum stays keyed to the running bottom and telescopes to `2(2δ+1)(2δ/F)`).  The single peel
uses `mono_abs_one_split` at threshold `2F` and `band_count_uniform` on the bottom band. -/
private theorem bands_dyadic_sum :
    ∀ (J : ℕ) (F δ u v : ℝ) (φ : ℝ → ℝ),
      0 < F → 0 ≤ δ → u ≤ v → ContDiff ℝ 2 φ →
      (MonotoneOn (fun z => |deriv φ z|) (Set.Icc u v)
        ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc u v)) →
      (∀ z ∈ Set.Icc u v, F ≤ |deriv φ z|) →
      (∀ z ∈ Set.Icc u v, |deriv φ z| ≤ 2 ^ J * F) →
      (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ 4 * δ * (v - u) + 2 * (2 ^ J * F) * (v - u)
            + 2 * (2 * δ + 1) * (2 * δ / F) + (J + 1) * (2 * δ + 1) := by
  intro J
  induction J with
  | zero =>
    intro F δ u v φ hF hδ huv hcd _ hlb hub
    -- `2^0 F = F`, so `F ≤ |φ'| ≤ F`. Bound by `band_count_uniform` with `G = 2F`.
    have hdiff : Differentiable ℝ φ := hcd.differentiable (by norm_num)
    have hub2F : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ 2 * F := by
      intro z hz; have := hub z hz; simp only [pow_zero, one_mul] at this; linarith
    have hbase := band_count_uniform u v F (2 * F) δ φ hdiff huv hF hδ hlb hub2F
    -- `(2F(v-u)+2δ+1)(2δ/F+1) = 4δ(v-u) + 2F(v-u) + (2δ+1)(2δ/F) + (2δ+1)`.
    have hexpand : (2 * F * (v - u) + 2 * δ + 1) * (2 * δ / F + 1)
        = 4 * δ * (v - u) + 2 * F * (v - u) + (2 * δ + 1) * (2 * δ / F) + (2 * δ + 1) := by
      field_simp; ring
    rw [hexpand] at hbase
    have hgeo : 0 ≤ (2 * δ + 1) * (2 * δ / F) := by positivity
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add]
    nlinarith [hbase, hgeo]
  | succ J ih =>
    intro F δ u v φ hF hδ huv hcd habsmono hlb hub
    have hdiff : Differentiable ℝ φ := hcd.differentiable (by norm_num)
    have h2F : (0:ℝ) < 2 * F := by linarith
    -- Peel the bottom band at threshold `2F`.
    obtain ⟨w, huw, hwv, hL, hR⟩ := mono_abs_one_split φ u v (2 * F) huv hcd habsmono
    have hsubuw : Set.Icc u w ⊆ Set.Icc u v := Set.Icc_subset_Icc (le_refl u) hwv
    have hsubwv : Set.Icc w v ⊆ Set.Icc u v := Set.Icc_subset_Icc huw (le_refl v)
    -- count splits over `[u,w]`, `[w,v]`.
    have hs := count_split u v w δ φ
    have hgeonn : 0 ≤ (2 * δ + 1) * (2 * δ / F) := by positivity
    have hbandnn : 0 ≤ (2 * δ + 1) := by linarith
    have hpowpos : (0:ℝ) < 2 ^ (J + 1) * F := by positivity
    have h2Fle : 2 * F ≤ 2 ^ (J + 1) * F := by
      have : (2:ℝ) ≤ 2 ^ (J + 1) := by
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (J + 1) := by apply pow_le_pow_right₀ (by norm_num); omega
      nlinarith [hF.le, this]
    -- Per-half **LOW** bound (`|φ'| ≤ 2F` on `[a,b]`), inflated to the `2^{J+1}F` coefficient.
    have lowBound : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc u v →
        (∀ z ∈ Set.Icc a b, |deriv φ z| ≤ 2 * F) →
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 4 * δ * (b - a) + 2 * (2 ^ (J + 1) * F) * (b - a)
              + (2 * δ + 1) * (2 * δ / F) + (2 * δ + 1) := by
      intro a b hab hsubab hubM
      have hlbM : ∀ z ∈ Set.Icc a b, F ≤ |deriv φ z| := fun z hz => hlb z (hsubab hz)
      have hbase := band_count_uniform a b F (2 * F) δ φ hdiff hab hF hδ hlbM hubM
      have hexpand : (2 * F * (b - a) + 2 * δ + 1) * (2 * δ / F + 1)
          = 4 * δ * (b - a) + 2 * F * (b - a) + (2 * δ + 1) * (2 * δ / F) + (2 * δ + 1) := by
        field_simp; ring
      rw [hexpand] at hbase
      have hlen : 0 ≤ b - a := by linarith
      have hcoef : 2 * F * (b - a) ≤ 2 * (2 ^ (J + 1) * F) * (b - a) := by nlinarith [h2Fle, hlen]
      linarith [hbase, hcoef]
    -- Per-half **HIGH** bound (`2F ≤ |φ'|` on `[a,b]`), via the IH at bottom `2F`.
    have highBound : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc u v →
        (MonotoneOn (fun z => |deriv φ z|) (Set.Icc a b)
          ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc a b)) →
        (∀ z ∈ Set.Icc a b, 2 * F ≤ |deriv φ z|) →
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 4 * δ * (b - a) + 2 * (2 ^ (J + 1) * F) * (b - a)
              + (2 * δ + 1) * (2 * δ / F) + (J + 1) * (2 * δ + 1) := by
      intro a b hab hsubab hmonoab hlbH
      have hubH : ∀ z ∈ Set.Icc a b, |deriv φ z| ≤ 2 ^ J * (2 * F) := by
        intro z hz
        have := hub z (hsubab hz)
        have hpow : (2:ℝ) ^ (J + 1) * F = 2 ^ J * (2 * F) := by ring
        rw [hpow] at this; exact this
      have hih := ih (2 * F) δ a b φ h2F hδ hab hcd hmonoab hlbH hubH
      have hpoweq : (2:ℝ) ^ J * (2 * F) = 2 ^ (J + 1) * F := by ring
      rw [hpoweq] at hih
      have hgeohalf : 2 * (2 * δ + 1) * (2 * δ / (2 * F)) = (2 * δ + 1) * (2 * δ / F) := by
        rw [show (2:ℝ) * δ / (2 * F) = (2 * δ) * (2 * F)⁻¹ by rw [div_eq_mul_inv],
          show (2:ℝ) * δ / F = (2 * δ) * F⁻¹ by rw [div_eq_mul_inv], mul_inv]
        ring
      rw [hgeohalf] at hih
      have hcast : ((J : ℝ) + 1) = ((J + 1 : ℕ) : ℝ) := by push_cast; ring
      calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 4 * δ * (b - a) + 2 * (2 ^ (J + 1) * F) * (b - a)
              + (2 * δ + 1) * (2 * δ / F) + ((J : ℝ) + 1) * (2 * δ + 1) := hih
        _ = 4 * δ * (b - a) + 2 * (2 ^ (J + 1) * F) * (b - a)
              + (2 * δ + 1) * (2 * δ / F) + (J + 1) * (2 * δ + 1) := by rw [hcast]
    -- monotonicity of `|φ'|` restricts to each half.
    have hmonouw : MonotoneOn (fun z => |deriv φ z|) (Set.Icc u w)
        ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc u w) :=
      habsmono.imp (fun h => h.mono hsubuw) (fun h => h.mono hsubuw)
    have hmonowv : MonotoneOn (fun z => |deriv φ z|) (Set.Icc w v)
        ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc w v) :=
      habsmono.imp (fun h => h.mono hsubwv) (fun h => h.mono hsubwv)
    have hsuccnat : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
    -- `(J+2)(2δ+1)` is the target band-count: `((J+1)+1)`.
    rw [show ((J + 1 : ℕ) : ℝ) + 1 = (J : ℝ) + 1 + 1 by rw [hsuccnat]]
    -- length sum identity (both `(w-u)+(v-w) = v-u`).
    have hlinL : 4 * δ * (w - u) + 2 * (2 ^ (J + 1) * F) * (w - u)
        + (4 * δ * (v - w) + 2 * (2 ^ (J + 1) * F) * (v - w))
        = 4 * δ * (v - u) + 2 * (2 ^ (J + 1) * F) * (v - u) := by ring
    -- **Guard**: is all of `[u,v]` `≥ 2F`?  If so, recurse directly (no peel, `J+1` bands total).
    by_cases hallHigh : ∀ z ∈ Set.Icc u v, 2 * F ≤ |deriv φ z|
    · -- whole interval HIGH: one direct IH call at bottom `2F`, `J+1` bands.
      have hwhole := highBound u v huv (le_refl _) habsmono hallHigh
      -- target band-count `(J+1+1)(2δ+1)` ≥ `(J+1)(2δ+1)`.
      have hJ1nn : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
      nlinarith [hwhole, hbandnn, hJ1nn]
    · -- not all `≥2F`: witness `z₀` with `|φ'(z₀)| < 2F`, so NOT both halves HIGH.
      push Not at hallHigh
      obtain ⟨z₀, hz₀mem, hz₀lt⟩ := hallHigh
      -- the LOW band-term `(2δ+1)` and HIGH band-term `(J+1)(2δ+1)`: per-half, keeping distinct.
      -- bound for a LOW half (`(2δ+1)` band-term):
      have huwLow : (∀ z ∈ Set.Icc u w, |deriv φ z| ≤ 2 * F) →
          (((Finset.Icc ⌈u⌉ ⌊w⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ 4 * δ * (w - u) + 2 * (2 ^ (J + 1) * F) * (w - u)
                + (2 * δ + 1) * (2 * δ / F) + (2 * δ + 1) :=
        fun h => lowBound u w huw hsubuw h
      have hwvLow : (∀ z ∈ Set.Icc w v, |deriv φ z| ≤ 2 * F) →
          (((Finset.Icc ⌈w⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ 4 * δ * (v - w) + 2 * (2 ^ (J + 1) * F) * (v - w)
                + (2 * δ + 1) * (2 * δ / F) + (2 * δ + 1) :=
        fun h => lowBound w v hwv hsubwv h
      have huwHigh : (∀ z ∈ Set.Icc u w, 2 * F ≤ |deriv φ z|) →
          (((Finset.Icc ⌈u⌉ ⌊w⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ 4 * δ * (w - u) + 2 * (2 ^ (J + 1) * F) * (w - u)
                + (2 * δ + 1) * (2 * δ / F) + (J + 1) * (2 * δ + 1) :=
        fun h => highBound u w huw hsubuw hmonouw h
      have hwvHigh : (∀ z ∈ Set.Icc w v, 2 * F ≤ |deriv φ z|) →
          (((Finset.Icc ⌈w⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            ≤ 4 * δ * (v - w) + 2 * (2 ^ (J + 1) * F) * (v - w)
                + (2 * δ + 1) * (2 * δ / F) + (J + 1) * (2 * δ + 1) :=
        fun h => highBound w v hwv hsubwv hmonowv h
      -- `(2δ+1) ≤ (J+1)(2δ+1)`: inflate the smaller band-term when needed.
      have hbandle : (2 * δ + 1) ≤ ((J : ℝ) + 1) * (2 * δ + 1) := by
        have hJ1 : (1 : ℝ) ≤ (J : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
          linarith
        nlinarith [hJ1, hbandnn]
      have hJ1nn : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
      -- `z₀` lies in one of the halves, ruling out that half being HIGH.
      rcases le_or_gt z₀ w with hz₀w | hz₀w
      · -- `z₀ ∈ [u,w]`: `[u,w]` is NOT HIGH (since `|φ'(z₀)| < 2F`), so by `hL` it is LOW.
        have huwNotHigh : ¬ (∀ z ∈ Set.Icc u w, 2 * F ≤ |deriv φ z|) := by
          intro hcontra; exact absurd (hcontra z₀ ⟨hz₀mem.1, hz₀w⟩) (by linarith [hz₀lt])
        have hLlow : ∀ z ∈ Set.Icc u w, |deriv φ z| ≤ 2 * F := hL.resolve_right huwNotHigh
        have hb1 := huwLow hLlow
        rcases hR with hRlow | hRhigh
        · -- both LOW: band-terms `(2δ+1) + (2δ+1) ≤ (J+2)(2δ+1)`.
          have hb2 := hwvLow hRlow
          nlinarith [hs, hb1, hb2, hlinL, hbandle, hbandnn]
        · -- `[w,v]` HIGH: band-terms `(2δ+1) + (J+1)(2δ+1) = (J+2)(2δ+1)`.
          have hb2 := hwvHigh hRhigh
          nlinarith [hs, hb1, hb2, hlinL]
      · -- `z₀ ∈ [w,v]`: `[w,v]` is NOT HIGH, so by `hR` it is LOW.
        have hwvNotHigh : ¬ (∀ z ∈ Set.Icc w v, 2 * F ≤ |deriv φ z|) := by
          intro hcontra; exact absurd (hcontra z₀ ⟨le_of_lt hz₀w, hz₀mem.2⟩) (by linarith [hz₀lt])
        have hRlow : ∀ z ∈ Set.Icc w v, |deriv φ z| ≤ 2 * F := hR.resolve_right hwvNotHigh
        have hb2 := hwvLow hRlow
        rcases hL with hLlow | hLhigh
        · have hb1 := huwLow hLlow
          nlinarith [hs, hb1, hb2, hlinL, hbandle, hbandnn]
        · have hb1 := huwHigh hLhigh
          nlinarith [hs, hb1, hb2, hlinL]

/-- **MID dyadic-sum core (the genuine crux of Lemma 4.2 — concrete remaining stub).**
On a sub-interval `[u,v]` where `deriv φ` has **constant sign** and is monotone-or-antitone (so
`|deriv φ|` is monotone), with `√(δT)/N ≤ |deriv φ| ≤ 4δ`, the near-integer count is bounded by
`N√(δ/T) + 2Nδ + 1`.

This is the dyadic part: band `|φ'| ∈ [2^j√(δT)/N, 2^{j+1}√(δT)/N)` (`j = 0 … J`,
`J ≈ log₂(4N√(δ/T))`), `band_count_uniform` per band.  Summing — the cross term `Σ 4δ·len_j`,
the variation `Σ G_j len_j`, the geometric fiber sum `≤ C·N√(δ/T)`, and the `(J+1)(2δ+1)`
"+1-per-band" log term `⌈log₂(4N√(δ/T))⌉ ≤ C(N√(δ/T)+1)` absorption.  See `math_audit.md` §4.2.

CONCRETE STUB (`bands_count_mono_mid`): the dyadic-band sum with `log₂(4x) ≤ C(x+1)` absorption. -/
private theorem bands_count_mono_mid (N T δ u v : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ) (hactive : 4 * δ < T) (huv : u ≤ v)
    (hcd : ContDiff ℝ 2 φ)
    (hsub : Set.Icc u v ⊆ Set.Icc N (3 * N))
    (hlb : ∀ z ∈ Set.Icc u v, Real.sqrt (δ * T) / N ≤ |deriv φ z|)
    (hub : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ 4 * δ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc u v) ∨ AntitoneOn (deriv φ) (Set.Icc u v))
    (hsign : (∀ z ∈ Set.Icc u v, 0 ≤ deriv φ z) ∨ (∀ z ∈ Set.Icc u v, deriv φ z ≤ 0)) :
    (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 1 := by
  -- `F₀ := √(δT)/N > 0`; `|deriv φ|` is monotone-or-antitone (constant sign + monotone `φ'`).
  set F₀ : ℝ := Real.sqrt (δ * T) / N with hF₀def
  have hsqrtδT_pos : 0 < Real.sqrt (δ * T) := Real.sqrt_pos.mpr (by positivity)
  have hF₀ : 0 < F₀ := by rw [hF₀def]; positivity
  have habsmono : MonotoneOn (fun z => |deriv φ z|) (Set.Icc u v)
      ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc u v) :=
    abs_deriv_mono_or_anti φ u v hmono hsign
  -- abbreviation `s := N√(δ/T) = 2δ/F₀ / 2` and the basic facts.
  set s : ℝ := N * Real.sqrt (δ / T) with hsdef
  have hsnn : 0 ≤ s := by rw [hsdef]; positivity
  -- `2δ/F₀ = 2N√(δ/T) = 2s`.
  have h2δF : 2 * δ / F₀ = 2 * s := by
    rw [hF₀def, hsdef]
    have hsqrt_eq : Real.sqrt (δ * T) / T = Real.sqrt (δ / T) := by
      rw [Real.sqrt_mul hδ.le, Real.sqrt_div hδ.le]
      have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
      have hsTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
      rw [eq_div_iff (ne_of_gt hsTpos), div_mul_eq_mul_div, mul_assoc, hsT,
        mul_div_assoc, div_self (ne_of_gt hT), mul_one]
    rw [div_div_eq_mul_div, eq_comm, ← hsqrt_eq]
    have hself : Real.sqrt (δ * T) * Real.sqrt (δ * T) = δ * T := Real.mul_self_sqrt (by positivity)
    rw [eq_div_iff (ne_of_gt hsqrtδT_pos)]; field_simp; nlinarith only [hself]
  -- `s ≥ 1/4` (band non-empty: `√(δT)/N ≤ 4δ` at `u`).
  have hband_u : F₀ ≤ 4 * δ := le_trans (hlb u ⟨le_refl u, huv⟩) (hub u ⟨le_refl u, huv⟩)
  have hs_quarter : (1:ℝ)/4 ≤ s := by
    rw [hsdef]
    have h1 : Real.sqrt (δ * T) ≤ 4 * δ * N := by
      have := hband_u; rw [hF₀def, div_le_iff₀ hN] at this; linarith
    have h2 : δ * T ≤ (4 * δ * N)^2 := by
      nlinarith only [Real.sqrt_nonneg (δ*T), h1, Real.sq_sqrt (show (0:ℝ) ≤ δ * T by positivity)]
    have h3 : (1:ℝ)/(16 * N^2) ≤ δ / T := by
      rw [div_le_div_iff₀ (by positivity) hT]; nlinarith only [h2, hδ, hT.le, hN.le]
    have h4 : Real.sqrt ((1:ℝ)/(16*N^2)) ≤ Real.sqrt (δ/T) := Real.sqrt_le_sqrt h3
    have h5 : Real.sqrt ((1:ℝ)/(16*N^2)) = 1/(4*N) := by
      rw [show (1:ℝ)/(16*N^2) = (1/(4*N))^2 by field_simp; ring, Real.sqrt_sq (by positivity)]
    rw [h5] at h4
    nlinarith only [h4, hN.le, show N * (1/(4*N)) = (1:ℝ)/4 by field_simp]
  -- `√(δ/T) < 1/2`, so `s < N/2`.
  have hsqrt_half : Real.sqrt (δ / T) < 1 / 2 := by
    have hlt : δ / T < 1/4 := by rw [div_lt_iff₀ hT]; linarith
    have h := Real.sqrt_lt_sqrt (by positivity) hlt
    rwa [show Real.sqrt ((1:ℝ)/4) = 1/2 by
      rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hsN2 : s < N / 2 := by rw [hsdef]; nlinarith only [hsqrt_half, hN, Real.sqrt_nonneg (δ/T)]
  -- length `v - u ≤ 2N`.
  have hlen2N : v - u ≤ 2 * N := by
    have hu := (hsub ⟨le_refl u, huv⟩).1; have hv := (hsub ⟨huv, le_refl v⟩).2; linarith
  -- **Choose** smallest `J : ℕ` with `4δ ≤ 2^J · F₀`.  Then `2^J F₀ ≤ 8δ` and `J ≤ 4δ/F₀ + 1`.
  -- Package the choice so `J` is opaque (avoids unfolding `Nat.find`).
  obtain ⟨J, hJspec, hJle, hpow8δ⟩ :
      ∃ J : ℕ, 4 * δ ≤ 2 ^ J * F₀ ∧ (J : ℝ) ≤ 4 * δ / F₀ + 1 ∧ 2 ^ J * F₀ ≤ 8 * δ := by
    have hex : ∃ J : ℕ, 4 * δ ≤ 2 ^ J * F₀ := by
      obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (4 * δ / F₀) (by norm_num : (1:ℝ) < 2)
      exact ⟨J, by rw [div_lt_iff₀ hF₀] at hJ; linarith⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
      · rw [hz]; simp only [Nat.cast_zero]; positivity
      · have hmin : ¬ (4 * δ ≤ 2 ^ (Nat.find hex - 1) * F₀) := Nat.find_min hex (by omega)
        push Not at hmin
        have hpowlt : 2 ^ (Nat.find hex - 1) < 4 * δ / F₀ := by
          rw [lt_div_iff₀ hF₀]; linarith [hmin]
        have h1 : ((Nat.find hex - 1 : ℕ) : ℝ) < 2 ^ (Nat.find hex - 1) := by
          exact_mod_cast Nat.lt_two_pow_self
        have h3 : (Nat.find hex : ℝ) = ((Nat.find hex - 1 : ℕ) : ℝ) + 1 := by
          have hJeq : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
          rw [hJeq]; push_cast; ring
        rw [h3]; linarith [lt_trans h1 hpowlt]
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
      · rw [hz]; simp only [pow_zero, one_mul]; linarith [hband_u]
      · have hmin : ¬ (4 * δ ≤ 2 ^ (Nat.find hex - 1) * F₀) := Nat.find_min hex (by omega)
        push Not at hmin
        have hpoweq : (2:ℝ) ^ (Nat.find hex) = 2 * 2 ^ (Nat.find hex - 1) := by
          conv_lhs => rw [show Nat.find hex = (Nat.find hex - 1) + 1 by omega]
          rw [pow_succ]; ring
        rw [hpoweq]; nlinarith only [hmin, hF₀.le]
  -- `4δ/F₀ = 4s` (twice `2δ/F₀ = 2s`); hence `J + 1 ≤ 4s + 2 ≤ 12s`.
  have h4δF_eq : 4 * δ / F₀ = 4 * s := by
    have : 4 * δ / F₀ = 2 * (2 * δ / F₀) := by ring
    rw [this, h2δF]; ring
  have hJ1_12s : (J : ℝ) + 1 ≤ 12 * s := by
    rw [h4δF_eq] at hJle; nlinarith only [hJle, hs_quarter]
  -- Apply the recursive dyadic band sum with `F = F₀`, level `J`.
  have hubJ : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ 2 ^ J * F₀ :=
    fun z hz => le_trans (hub z hz) hJspec
  have hdyadic := bands_dyadic_sum J F₀ δ u v φ hF₀ hδ.le huv hcd habsmono hlb hubJ
  -- count ≤ 4δ(v-u) + 2(2^J F₀)(v-u) + 2(2δ+1)(2δ/F₀) + (J+1)(2δ+1).
  -- Now bound each term; `2δ/F₀ = 2s`, `2^J F₀ ≤ 8δ`, `v-u ≤ 2N`, `s ≤ N/2`, `s ≥ 1/4`.
  rw [h2δF] at hdyadic
  -- `√(δ/T) ≤ 1/2`-flavoured facts: `δ·s ≤ Nδ/2` and `s ≤ N/2`.
  have hδs : δ * s ≤ N * δ / 2 := by nlinarith only [hsN2, hδ.le, hsnn]
  have hsNδ : 0 ≤ N * δ := by positivity
  have hlennn : 0 ≤ v - u := by linarith
  -- length-coefficient bounds.
  have hL1 : 4 * δ * (v - u) ≤ 8 * (N * δ) := by nlinarith only [hlen2N, hδ.le, hlennn]
  have hL2 : 2 * (2 ^ J * F₀) * (v - u) ≤ 32 * (N * δ) := by
    have hge : 2 * (2 ^ J * F₀) * (v - u) ≤ 2 * (8 * δ) * (v - u) := by
      apply mul_le_mul_of_nonneg_right _ hlennn
      nlinarith only [hpow8δ]
    nlinarith only [hge, hlen2N, hδ.le, hlennn]
  -- geometric term: `2(2δ+1)(2s) = 8δs + 4s ≤ 8·(Nδ/2) + 4s = 4Nδ + 4s`.
  have hL3 : 2 * (2 * δ + 1) * (2 * s) ≤ 4 * (N * δ) + 4 * s := by nlinarith only [hδs, hsnn, hδ.le]
  -- band term: `(J+1)(2δ+1) ≤ 12s(2δ+1) = 24δs + 12s ≤ 24·(Nδ/2) + 12s = 12Nδ + 12s`.
  have hL4 : ((J : ℝ) + 1) * (2 * δ + 1) ≤ 12 * (N * δ) + 12 * s := by
    have hb : (0:ℝ) ≤ 2 * δ + 1 := by linarith
    have hstep : ((J : ℝ) + 1) * (2 * δ + 1) ≤ 12 * s * (2 * δ + 1) := by
      apply mul_le_mul_of_nonneg_right hJ1_12s hb
    nlinarith only [hstep, hδs, hsnn, hδ.le]
  -- conclude: total ≤ 56Nδ + 16s ≤ 16s + 56Nδ + 1.  (`16 * N√(δ/T) = 16 s`.)
  have hfinal : (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 16 * s + 56 * (N * δ) := by
    have := hdyadic
    linarith [this, hL1, hL2, hL3, hL4]
  rw [hsdef] at hfinal
  nlinarith only [hfinal, hsnn, hsNδ]

/-- **Monotone threshold split.**  For `g` continuous and monotone on `[p,q]` (`p ≤ q`) and a
threshold pair `-c ≤ c` (`0 ≤ c`), there are `p ≤ c₁ ≤ c₂ ≤ q` with: the middle `[c₁,c₂]` is Low
(`|g| ≤ c`); each end is either a single point (`p = c₁`, resp. `c₂ = q`) or a constant-sign Band
(`c ≤ |g|`, and `g ≤ 0` on the left / `0 ≤ g` on the right).  The crossings come from IVT
(`exists_crossing`); monotonicity gives the one-sided bounds and the ordering `c₁ ≤ c₂`. -/
private theorem mono_threshold_split (g : ℝ → ℝ) (p q c : ℝ) (hpq : p ≤ q) (hc : 0 ≤ c)
    (hcont : ContinuousOn g (Set.Icc p q)) (hmono : MonotoneOn g (Set.Icc p q)) :
    ∃ c₁ c₂, p ≤ c₁ ∧ c₁ ≤ c₂ ∧ c₂ ≤ q ∧
      (c₁ = c₂ ∨ ∀ z ∈ Set.Icc c₁ c₂, |g z| ≤ c) ∧
      (p = c₁ ∨ ((∀ z ∈ Set.Icc p c₁, c ≤ |g z|) ∧ (∀ z ∈ Set.Icc p c₁, g z ≤ 0))) ∧
      (c₂ = q ∨ ((∀ z ∈ Set.Icc c₂ q, c ≤ |g z|) ∧ (∀ z ∈ Set.Icc c₂ q, 0 ≤ g z))) := by
  have hpmem : p ∈ Set.Icc p q := ⟨le_refl p, hpq⟩
  have hqmem : q ∈ Set.Icc p q := ⟨hpq, le_refl q⟩
  -- `c₁ ∈ [p,q]`: on `[p,c₁]` either `p = c₁` or `g ≤ -c`; on `[c₁,q]`, `-c ≤ g`.
  obtain ⟨c₁, hc1mem, hc1lo, hc1ge⟩ :
      ∃ c₁ ∈ Set.Icc p q,
        (p = c₁ ∨ ∀ z ∈ Set.Icc p c₁, g z ≤ -c)
          ∧ (c₁ = q ∨ ∀ z ∈ Set.Icc c₁ q, -c ≤ g z) := by
    rcases le_or_gt (g p) (-c) with hgp | hgp
    · rcases le_or_gt (-c) (g q) with hgq | hgq
      · obtain ⟨w, hwmem, hwval⟩ := exists_crossing g p q (-c) hpq hcont hgp hgq
        refine ⟨w, hwmem, Or.inr ?_, Or.inr ?_⟩
        · intro z hz
          have : g z ≤ g w := hmono ⟨hz.1, le_trans hz.2 hwmem.2⟩ hwmem hz.2
          rw [hwval] at this; exact this
        · intro z hz
          have : g w ≤ g z := hmono hwmem ⟨le_trans hwmem.1 hz.1, hz.2⟩ hz.1
          rw [hwval] at this; exact this
      · -- `g q < -c`: whole interval `≤ -c`; take `c₁ = q`.
        refine ⟨q, hqmem, Or.inr ?_, Or.inl rfl⟩
        intro z hz
        have : g z ≤ g q := hmono ⟨hz.1, le_trans hz.2 (le_refl q)⟩ hqmem hz.2
        linarith [hgq]
    · -- `g p > -c`: take `c₁ = p` (degenerate left), and `-c ≤ g` on `[p,q]`.
      refine ⟨p, hpmem, Or.inl rfl, Or.inr ?_⟩
      intro z hz; exact le_trans (le_of_lt hgp) (hmono hpmem ⟨hz.1, hz.2⟩ hz.1)
  -- `c₂ ∈ [c₁,q]`: on `[c₂,q]` either `c₂ = q` or `c ≤ g`; on `[c₁,c₂]`, `g ≤ c`.
  have hcont1 : ContinuousOn g (Set.Icc c₁ q) :=
    hcont.mono (Set.Icc_subset_Icc hc1mem.1 (le_refl q))
  have hmono1 : MonotoneOn g (Set.Icc c₁ q) :=
    hmono.mono (Set.Icc_subset_Icc hc1mem.1 (le_refl q))
  have hc1q : c₁ ≤ q := hc1mem.2
  obtain ⟨c₂, hc2mem, hc2hi, hc2le⟩ :
      ∃ c₂ ∈ Set.Icc c₁ q,
        (c₂ = q ∨ ∀ z ∈ Set.Icc c₂ q, c ≤ g z)
          ∧ (c₁ = c₂ ∨ ∀ z ∈ Set.Icc c₁ c₂, g z ≤ c) := by
    rcases le_or_gt c (g q) with hgq | hgq
    · rcases le_or_gt (g c₁) c with hgc1 | hgc1
      · obtain ⟨w, hwmem, hwval⟩ := exists_crossing g c₁ q c hc1q hcont1 hgc1 hgq
        refine ⟨w, hwmem, Or.inr ?_, Or.inr ?_⟩
        · intro z hz
          have : g w ≤ g z := hmono1 hwmem ⟨le_trans hwmem.1 hz.1, hz.2⟩ hz.1
          rw [hwval] at this; exact this
        · intro z hz
          have : g z ≤ g w := hmono1 ⟨hz.1, le_trans hz.2 hwmem.2⟩ hwmem hz.2
          rw [hwval] at this; exact this
      · -- `g c₁ > c`: whole `[c₁,q]` has `g ≥ c`; take `c₂ = c₁` (degenerate middle).
        refine ⟨c₁, ⟨le_refl c₁, hc1q⟩, Or.inr ?_, Or.inl rfl⟩
        intro z hz; exact le_trans (le_of_lt hgc1) (hmono1 ⟨le_refl c₁, hc1q⟩ hz hz.1)
    · -- `g q < c`: whole `[c₁,q]` has `g ≤ c`; take `c₂ = q` (degenerate right).
      refine ⟨q, ⟨hc1q, le_refl q⟩, Or.inl rfl, Or.inr ?_⟩
      intro z hz
      have : g z ≤ g q := hmono1 ⟨hz.1, le_trans hz.2 (le_refl q)⟩ ⟨hc1q, le_refl q⟩ hz.2
      linarith [hgq]
  refine ⟨c₁, c₂, hc1mem.1, hc2mem.1, hc2mem.2, ?_, ?_, ?_⟩
  · -- middle Low: `|g| ≤ c` on `[c₁,c₂]` (from `-c ≤ g` and `g ≤ c`), unless degenerate.
    rcases hc2le with hdeg | hle
    · exact Or.inl hdeg
    rcases hc1ge with hc1eqq | hge
    · -- `c₁ = q`, so `[c₁,c₂] ⊆ [q,q]`: degenerate `c₁ = c₂`.
      refine Or.inl (le_antisymm hc2mem.1 ?_)
      rw [hc1eqq]; exact hc2mem.2
    · refine Or.inr ?_
      intro z hz
      have hzq : z ∈ Set.Icc c₁ q := ⟨hz.1, le_trans hz.2 hc2mem.2⟩
      rw [abs_le]; exact ⟨hge z hzq, hle z hz⟩
  · -- left disjunction.
    rcases hc1lo with hpc1 | hband
    · exact Or.inl hpc1
    · refine Or.inr ⟨?_, ?_⟩
      · intro z hz
        have hgz : g z ≤ -c := hband z hz
        rw [abs_of_nonpos (by linarith [hgz, hc])]; linarith [hgz]
      · intro z hz; linarith [hband z hz, hc]
  · -- right disjunction.
    rcases hc2hi with hc2q | hband
    · exact Or.inl hc2q
    · refine Or.inr ⟨?_, ?_⟩
      · intro z hz
        have : c ≤ g z := hband z hz
        rw [abs_of_nonneg (le_trans hc (hband z hz))]; exact hband z hz
      · intro z hz; linarith [hband z hz, hc]

/-- **`|deriv φ|`-threshold split for a monotone-or-antitone `φ'`.**  Applies `mono_threshold_split`
to `deriv φ` (monotone case) or to `-(deriv φ)` (antitone case) and rephrases the result purely in
terms of `|deriv φ|` plus a constant-sign disjunct, ready for `bands_count_mono_low_slack` (middle)
and `bands_count_mono_band_slack` (ends). -/
private theorem mono_abs_threshold_split (φ : ℝ → ℝ) (p q c : ℝ) (hpq : p ≤ q) (hc : 0 ≤ c)
    (hcont : ContinuousOn (deriv φ) (Set.Icc p q))
    (hmono : MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q)) :
    ∃ c₁ c₂, p ≤ c₁ ∧ c₁ ≤ c₂ ∧ c₂ ≤ q ∧
      (c₁ = c₂ ∨ ∀ z ∈ Set.Icc c₁ c₂, |deriv φ z| ≤ c) ∧
      (p = c₁ ∨ ((∀ z ∈ Set.Icc p c₁, c ≤ |deriv φ z|) ∧
        ((∀ z ∈ Set.Icc p c₁, 0 ≤ deriv φ z) ∨ (∀ z ∈ Set.Icc p c₁, deriv φ z ≤ 0)))) ∧
      (c₂ = q ∨ ((∀ z ∈ Set.Icc c₂ q, c ≤ |deriv φ z|) ∧
        ((∀ z ∈ Set.Icc c₂ q, 0 ≤ deriv φ z) ∨ (∀ z ∈ Set.Icc c₂ q, deriv φ z ≤ 0)))) := by
  rcases hmono with hmon | hanti
  · obtain ⟨c₁, c₂, h1, h2, h3, hmid, hL, hR⟩ :=
      mono_threshold_split (deriv φ) p q c hpq hc hcont hmon
    exact ⟨c₁, c₂, h1, h2, h3, hmid,
      hL.imp_right (fun h => ⟨h.1, Or.inr h.2⟩), hR.imp_right (fun h => ⟨h.1, Or.inl h.2⟩)⟩
  · -- antitone: apply to `-(deriv φ)`, monotone.
    have hcont' : ContinuousOn (fun z => -(deriv φ z)) (Set.Icc p q) := hcont.neg
    have hmon' : MonotoneOn (fun z => -(deriv φ z)) (Set.Icc p q) := by
      intro x hx y hy hxy; simp only [neg_le_neg_iff]; exact hanti hx hy hxy
    obtain ⟨c₁, c₂, h1, h2, h3, hmid, hL, hR⟩ :=
      mono_threshold_split (fun z => -(deriv φ z)) p q c hpq hc hcont' hmon'
    refine ⟨c₁, c₂, h1, h2, h3, ?_, ?_, ?_⟩
    · exact hmid.imp_right (fun h z hz => by have := h z hz; rwa [abs_neg] at this)
    · refine hL.imp_right (fun h => ⟨fun z hz => by have := h.1 z hz; rwa [abs_neg] at this, ?_⟩)
      exact Or.inl (fun z hz => by have := h.2 z hz; linarith)
    · refine hR.imp_right (fun h => ⟨fun z hz => by have := h.1 z hz; rwa [abs_neg] at this, ?_⟩)
      exact Or.inr (fun z hz => by have := h.2 z hz; linarith)

/-- **SLACK low sub-region count.**  The Low sub-region count where the curvature lower bound
carries a slack factor `cl ∈ (0,1]`: `hlower` only gives `cl·(T/N) ≤ |φ'| + N|φ''|`.  Tracing the
length bound (`mono_low_length` with curvature `cl·T/(2N²)`, threshold `√(δT)/N` UNCHANGED) the
middle length degrades by exactly `cl⁻¹`, so `count ≤ cl⁻¹·(4N√(δ/T)) + 1`.  The activity
hypothesis must be strengthened to `4δ < cl²·T` (needed for `√(δT) ≤ cl·T/2` in the curvature step,
since the threshold is unmoved). -/
private theorem bands_count_mono_low_slack (N T δ cl u v : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ) (hcl : 0 < cl)
    (hactive : 4 * δ < cl ^ 2 * T) (huv : u ≤ v)
    (hcd : ContDiff ℝ 2 φ)
    (hsmall : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ Real.sqrt (δ * T) / N)
    (hlower : ∀ z ∈ Set.Icc u v, cl * (T / N) ≤ |deriv φ z| + N * |iteratedDeriv 2 φ z|) :
    (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (1 / cl) * (4 * N * Real.sqrt (δ / T)) + 1 := by
  have hclT : 0 < cl * T := by positivity
  -- `√(δT) ≤ cl·T/2` from `4δ < cl²·T`.
  have hsqrtδT_le : Real.sqrt (δ * T) ≤ cl * T / 2 := by
    have hsq : (cl * T / 2) ^ 2 = cl ^ 2 * T ^ 2 / 4 := by ring
    have hδT_le : δ * T ≤ (cl * T / 2) ^ 2 := by rw [hsq]; nlinarith [hT.le, hactive]
    have h2 := Real.sqrt_le_sqrt hδT_le
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hF0_le : Real.sqrt (δ * T) / N ≤ cl * T / (2 * N) := by
    rw [div_le_div_iff₀ hN (by positivity : (0:ℝ) < 2 * N)]
    nlinarith [hsqrtδT_le, hN.le]
  -- curvature `cl·T/(2N²) ≤ |φ''|` on `[u,v]`.
  have hcurv : ∀ z ∈ Set.Icc u v, cl * T / (2 * N ^ 2) ≤ |iteratedDeriv 2 φ z| := by
    intro z hz
    have hlz : cl * T / N ≤ |deriv φ z| + N * |iteratedDeriv 2 φ z| := by
      have := hlower z hz; rwa [mul_div_assoc]
    exact curvature_lower N (cl * T) φ hN hlz (le_trans (hsmall z hz) hF0_le)
  have hlen := mono_low_length N (cl * T) (Real.sqrt (δ * T) / N) u v φ hN hclT huv hcd hsmall hcurv
  have hsqrt_eq : Real.sqrt (δ * T) / T = Real.sqrt (δ / T) := by
    rw [Real.sqrt_mul hδ.le, Real.sqrt_div hδ.le]
    have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
    have hsTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
    rw [eq_div_iff (ne_of_gt hsTpos), div_mul_eq_mul_div, mul_assoc, hsT,
      mul_div_assoc, div_self (ne_of_gt hT), mul_one]
  have hlen' : v - u ≤ (1 / cl) * (4 * N * Real.sqrt (δ / T)) := by
    have hrw : 4 * N ^ 2 * (Real.sqrt (δ * T) / N) / (cl * T)
        = (1 / cl) * (4 * N * (Real.sqrt (δ * T) / T)) := by
      field_simp
    rw [hrw, hsqrt_eq] at hlen
    exact hlen
  have hcount := card_filter_le_length u v δ φ huv
  linarith [hcount, hlen']

/-- **SLACK band sub-region count.**  The Band sub-region count where the upper derivative bound
carries a slack factor `cu ≥ 1`: `|φ'| ≤ cu·T/N`.  The slack enters only the HIGH part (via
`bands_count_mono_high` at scale `cu·T`); the MID part (`bands_count_mono_mid`) and the lower
threshold `√(δT)/N` are UNCHANGED.  Conclusion gains `cu` on the `T`-term:
`count ≤ 16N√(δ/T)+56Nδ+4·cu·T+3`. -/
private theorem bands_count_mono_band_slack (N T δ cu u v : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ) (hcu : 1 ≤ cu) (hactive : 4 * δ < T) (huv : u ≤ v)
    (hcd : ContDiff ℝ 2 φ)
    (hsub : Set.Icc u v ⊆ Set.Icc N (3 * N))
    (hlb : ∀ z ∈ Set.Icc u v, Real.sqrt (δ * T) / N ≤ |deriv φ z|)
    (hub : ∀ z ∈ Set.Icc u v, |deriv φ z| ≤ cu * T / N)
    (hmono : MonotoneOn (deriv φ) (Set.Icc u v) ∨ AntitoneOn (deriv φ) (Set.Icc u v))
    (hsign : (∀ z ∈ Set.Icc u v, 0 ≤ deriv φ z) ∨ (∀ z ∈ Set.Icc u v, deriv φ z ≤ 0)) :
    (((Finset.Icc ⌈u⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 4 * cu * T + 3 := by
  classical
  have hdiff : Differentiable ℝ φ := hcd.differentiable (by norm_num)
  have hcunn : (0:ℝ) ≤ cu := le_trans zero_le_one hcu
  have hcoefnn : (0:ℝ) ≤ cu * T / N := div_nonneg (mul_nonneg hcunn hT.le) hN.le
  have hsqrtnn : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
  have hlen2N : v - u ≤ 2 * N := by
    have hu : u ∈ Set.Icc N (3 * N) := hsub ⟨le_refl u, huv⟩
    have hv : v ∈ Set.Icc N (3 * N) := hsub ⟨huv, le_refl v⟩
    have := hu.1; have := hv.2; linarith
  have habsmono : MonotoneOn (fun z => |deriv φ z|) (Set.Icc u v)
      ∨ AntitoneOn (fun z => |deriv φ z|) (Set.Icc u v) :=
    abs_deriv_mono_or_anti φ u v hmono hsign
  obtain ⟨w, huw, hwv, hsum⟩ :
      ∃ w, u ≤ w ∧ w ≤ v ∧
        (((Finset.Icc ⌈u⌉ ⌊w⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          + (((Finset.Icc ⌈w⌉ ⌊v⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ (16 * N * Real.sqrt (δ / T) + 56 * N * δ + 1)
            + (3 / 2) * (cu * T / N * (v - u) + 2 * δ + 1) := by
    have midOf : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
        (∀ z ∈ Set.Icc a b, |deriv φ z| ≤ 4 * δ) →
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 1 := by
      intro a b hua hab hbv hubM
      have hsubab : Set.Icc a b ⊆ Set.Icc u v := Set.Icc_subset_Icc hua hbv
      have hlbM : ∀ z ∈ Set.Icc a b, Real.sqrt (δ * T) / N ≤ |deriv φ z| :=
        fun z hz => hlb z (hsubab hz)
      have hsignM : (∀ z ∈ Set.Icc a b, 0 ≤ deriv φ z) ∨ (∀ z ∈ Set.Icc a b, deriv φ z ≤ 0) :=
        hsign.imp (fun h z hz => h z (hsubab hz)) (fun h z hz => h z (hsubab hz))
      have hmonoM : MonotoneOn (deriv φ) (Set.Icc a b) ∨ AntitoneOn (deriv φ) (Set.Icc a b) :=
        hmono.imp (fun h => h.mono hsubab) (fun h => h.mono hsubab)
      exact bands_count_mono_mid N T δ a b φ hN hT hδ hactive hab hcd (hsubab.trans hsub)
        hlbM hubM hmonoM hsignM
    have highOf : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
        (∀ z ∈ Set.Icc a b, 4 * δ ≤ |deriv φ z|) →
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ (3 / 2) * (cu * T / N * (v - u) + 2 * δ + 1) := by
      intro a b hua hab hbv hlbH
      have hsubab : Set.Icc a b ⊆ Set.Icc u v := Set.Icc_subset_Icc hua hbv
      have hubH : ∀ z ∈ Set.Icc a b, |deriv φ z| ≤ cu * T / N := fun z hz => hub z (hsubab hz)
      have hbase := bands_count_mono_high N (cu * T) δ a b φ hδ hdiff hab hlbH hubH
      have hmono_len : cu * T / N * (b - a) ≤ cu * T / N * (v - u) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoefnn
      have : (3 / 2) * (cu * T / N * (b - a) + 2 * δ + 1)
          ≤ (3 / 2) * (cu * T / N * (v - u) + 2 * δ + 1) := by nlinarith [hmono_len]
      linarith
    have hMIDpt : ∀ a b : ℝ, a ≤ b → b - a = 0 →
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 1 := by
      intro a b hab hba
      have hc := card_filter_le_length a b δ φ hab
      rw [hba] at hc
      nlinarith [hc, hN.le, hδ.le, hsqrtnn]
    have hHIGHpt : ∀ a b : ℝ, a ≤ b → b - a = 0 →
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ (3 / 2) * (cu * T / N * (v - u) + 2 * δ + 1) := by
      intro a b hab hba
      have hc := card_filter_le_length a b δ φ hab
      rw [hba] at hc
      have hnn : 0 ≤ cu * T / N * (v - u) := mul_nonneg hcoefnn (by linarith)
      nlinarith [hc, hδ.le, hnn]
    rcases habsmono with hmonoinc | hmonodec
    · rcases le_or_gt (|deriv φ u|) (4 * δ) with hsmallu | hbigu
      · rcases le_or_gt (4 * δ) (|deriv φ v|) with hbigv | hsmallv
        · obtain ⟨w, hwmem, hwval⟩ := exists_crossing (fun z => |deriv φ z|) u v (4 * δ) huv
            (by exact (hcont_abs φ u v hcd)) hsmallu hbigv
          refine ⟨w, hwmem.1, hwmem.2, add_le_add ?_ ?_⟩
          · refine midOf u w (le_refl u) hwmem.1 hwmem.2 ?_
            intro z hz
            have : |deriv φ z| ≤ |deriv φ w| :=
              hmonoinc ⟨hz.1, le_trans hz.2 hwmem.2⟩ hwmem hz.2
            rw [hwval] at this; exact this
          · refine highOf w v hwmem.1 hwmem.2 (le_refl v) ?_
            intro z hz
            have : |deriv φ w| ≤ |deriv φ z| :=
              hmonoinc hwmem ⟨le_trans hwmem.1 hz.1, hz.2⟩ hz.1
            rw [hwval] at this; exact this
        · refine ⟨v, huv, le_refl v, add_le_add ?_ (hHIGHpt v v (le_refl v) (by ring))⟩
          refine midOf u v (le_refl u) huv (le_refl v) ?_
          intro z hz
          have : |deriv φ z| ≤ |deriv φ v| := hmonoinc hz ⟨huv, le_refl v⟩ hz.2
          linarith [hsmallv]
      · refine ⟨u, le_refl u, huv, add_le_add (hMIDpt u u (le_refl u) (by ring)) ?_⟩
        refine highOf u v (le_refl u) huv (le_refl v) ?_
        intro z hz
        have : |deriv φ u| ≤ |deriv φ z| := hmonoinc ⟨le_refl u, huv⟩ hz hz.1
        linarith [hbigu]
    · rcases le_or_gt (|deriv φ v|) (4 * δ) with hsmallv | hbigv
      · rcases le_or_gt (4 * δ) (|deriv φ u|) with hbigu | hsmallu
        · obtain ⟨w, hwmem, hwval⟩ :
              ∃ w ∈ Set.Icc u v, |deriv φ w| = 4 * δ := by
            obtain ⟨w, hwmem, hwval⟩ := exists_crossing (fun z => -(|deriv φ z|)) u v (-(4 * δ)) huv
              ((hcont_abs φ u v hcd).neg) (by simpa using hbigu) (by simpa using hsmallv)
            exact ⟨w, hwmem, by simpa using hwval⟩
          refine ⟨w, hwmem.1, hwmem.2, ?_⟩
          rw [add_comm (16 * N * Real.sqrt (δ / T) + 56 * N * δ + 1)]
          refine add_le_add ?_ ?_
          · refine highOf u w (le_refl u) hwmem.1 hwmem.2 ?_
            intro z hz
            have : |deriv φ w| ≤ |deriv φ z| :=
              hmonodec ⟨hz.1, le_trans hz.2 hwmem.2⟩ hwmem hz.2
            rw [hwval] at this; exact this
          · refine midOf w v hwmem.1 hwmem.2 (le_refl v) ?_
            intro z hz
            have : |deriv φ z| ≤ |deriv φ w| :=
              hmonodec hwmem ⟨le_trans hwmem.1 hz.1, hz.2⟩ hz.1
            rw [hwval] at this; exact this
        · refine ⟨v, huv, le_refl v, add_le_add ?_ (hHIGHpt v v (le_refl v) (by ring))⟩
          refine midOf u v (le_refl u) huv (le_refl v) ?_
          intro z hz
          have : |deriv φ z| ≤ |deriv φ u| := hmonodec ⟨le_refl u, huv⟩ hz hz.1
          linarith [hsmallu]
      · refine ⟨u, le_refl u, huv, add_le_add (hMIDpt u u (le_refl u) (by ring)) ?_⟩
        refine highOf u v (le_refl u) huv (le_refl v) ?_
        intro z hz
        have : |deriv φ v| ≤ |deriv φ z| := hmonodec hz ⟨huv, le_refl v⟩ hz.2
        linarith [hbigv]
  have hs := count_split u v w δ φ
  have hTN2N : cu * T / N * (v - u) ≤ 2 * cu * T := by
    have hstep := mul_le_mul_of_nonneg_left hlen2N hcoefnn
    have hNN : cu * T / N * (2 * N) = 2 * cu * T := by field_simp
    rw [hNN] at hstep; exact hstep
  nlinarith only [hs, hsum, hTN2N, hactive, mul_nonneg (sub_nonneg.mpr hcu) hT.le,
    hN.le, hδ.le, hsqrtnn]

/-- **SLACK Low/Band/Band assembly.**  The Low/Band/Band assembly where the two ends carry `cu` on
their `T`-term and the middle carries `cl⁻¹` on its `√(δ/T)`-term.  The aggregate fits under
`112·(cu/cl)·(N(δ+√(δ/T)) + T + 1)`. -/
private theorem bands_count_mono_of_split_slack (N T δ cu cl p q c₁ c₂ : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ) (hcu : 1 ≤ cu) (hcl : 0 < cl) (hcl1 : cl ≤ 1)
    (hsqrtnn : 0 ≤ Real.sqrt (δ / T))
    (hLeft : (((Finset.Icc ⌈p⌉ ⌊c₁⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 4 * cu * T + 3)
    (hMid : (((Finset.Icc ⌈c₁⌉ ⌊c₂⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (1 / cl) * (4 * N * Real.sqrt (δ / T)) + 1)
    (hRight : (((Finset.Icc ⌈c₂⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 4 * cu * T + 3) :
    (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  have hs1 := count_split p q c₁ δ φ
  have hs2 := count_split c₁ q c₂ δ φ
  set r := Real.sqrt (δ / T) with hr
  have hcunn : (0:ℝ) ≤ cu := le_trans zero_le_one hcu
  have hrnn : 0 ≤ r := hsqrtnn
  have hNr : (0:ℝ) ≤ N * r := mul_nonneg hN.le hrnn
  have hNδ : (0:ℝ) ≤ N * δ := mul_nonneg hN.le hδ.le
  have hsplit : (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ (16 * N * r + 56 * N * δ + 4 * cu * T + 3)
        + ((1 / cl) * (4 * N * r) + 1)
        + (16 * N * r + 56 * N * δ + 4 * cu * T + 3) := by
    linarith [hs1, hs2, hLeft, hMid, hRight]
  rw [show (112:ℝ) * (cu / cl) * (N * (δ + r) + T + 1)
        = (112 * cu * (N * (δ + r) + T + 1)) / cl from by ring]
  rw [le_div_iff₀ hcl]
  have hmulcl := mul_le_mul_of_nonneg_right hsplit hcl.le
  have hclear : ((16 * N * r + 56 * N * δ + 4 * cu * T + 3)
        + ((1 / cl) * (4 * N * r) + 1)
        + (16 * N * r + 56 * N * δ + 4 * cu * T + 3)) * cl
      = cl * (32 * N * r + 112 * N * δ + 8 * cu * T + 7) + 4 * N * r := by
    field_simp; ring
  rw [hclear] at hmulcl
  nlinarith only [hmulcl, hcl, hcl1, hcu, hcunn, hNr, hNδ, hT.le,
    mul_nonneg (sub_nonneg.mpr hcu) hNr, mul_nonneg (sub_nonneg.mpr hcl1) hNr,
    mul_nonneg (sub_nonneg.mpr hcu) hNδ, mul_nonneg (sub_nonneg.mpr hcl1) hNδ,
    mul_nonneg hcunn hT.le, mul_nonneg (sub_nonneg.mpr hcl1) (mul_nonneg hcunn hT.le)]

/-- **SLACK derivative-band count (two-sided slack engine).**  Generalizes `bands_count_mono` to
carry an upper slack `cu ≥ 1` (`|φ'| ≤ cu·(T/N)`) and a lower/curvature slack `cl ∈ (0,1]`
(`cl·(T/N) ≤ |φ'| + N|φ''|`).  The slack degrades the count by an explicit factor `g(cu,cl) = cu/cl`
(`= 1` at `cu = cl = 1`): the upper slack `cu` hits only the LEFT/RIGHT bands (their `T`-term), the
lower slack `cl` hits only the MIDDLE (its `√(δ/T)`-term, as `cl⁻¹`); the `δ`-measure term is
undegraded.  The threshold `√(δT)/N` is unchanged, so the activity hypothesis is `4δ < cl²·T`. -/
theorem bands_count_mono_slack (N T δ a b p q cu cl : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hcu : 1 ≤ cu) (hcl : 0 < cl) (hcl1 : cl ≤ 1)
    (hactive : 4 * δ < cl ^ 2 * T)
    (hcd : ContDiff ℝ 2 φ)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N))
    (hpq_sub : Set.Icc p q ⊆ Set.Icc a b)
    (hd1 : ∀ x ∈ Set.Icc p q, |deriv φ x| ≤ cu * (T / N))
    (hlower : ∀ x ∈ Set.Icc p q, cl * (T / N) ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hmono : MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q)) :
    (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  have hsqrtnn : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
  have hcunn : (0:ℝ) ≤ cu := le_trans zero_le_one hcu
  have hcucl_pos : 0 < cu / cl := div_pos (lt_of_lt_of_le one_pos hcu) hcl
  have hcl2 : cl ^ 2 ≤ 1 := by nlinarith [hcl1, hcl.le]
  have hactiveT : 4 * δ < T := by nlinarith [hactive, hcl2, hT.le]
  rcases le_or_gt p q with hpq | hqp
  swap
  · have hltceil : ⌊q⌋ < ⌈p⌉ := by
      have h1 : p ≤ (⌈p⌉ : ℝ) := Int.le_ceil p
      have h2 : (⌊q⌋ : ℝ) ≤ q := Int.floor_le q
      exact_mod_cast (by linarith : (⌊q⌋ : ℝ) < (⌈p⌉ : ℝ))
    have hzero : ((Finset.Icc ⌈p⌉ ⌊q⌋).filter
        (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card = 0 := by
      rw [Finset.Icc_eq_empty (by omega)]; simp
    rw [hzero, Nat.cast_zero]
    have hpos : 0 ≤ 112 * (cu / cl) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
      apply mul_nonneg (mul_nonneg (by norm_num) hcucl_pos.le)
      nlinarith [hN.le, hδ.le, hT.le, hsqrtnn]
    linarith [hpos]
  set c : ℝ := Real.sqrt (δ * T) / N with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  have hcont : ContinuousOn (deriv φ) (Set.Icc p q) := by
    have hcd1 : ContDiff ℝ 1 (deriv φ) := by
      have h2 : ContDiff ℝ (1 + 1) φ := by norm_num; exact hcd
      exact h2.deriv'
    exact hcd1.continuous.continuousOn
  obtain ⟨c₁, c₂, hpc1, hc12, hc2q, hmid, hLeft, hRight⟩ :=
    mono_abs_threshold_split φ p q c hpq hcnn hcont hmono
  have hsubM : Set.Icc c₁ c₂ ⊆ Set.Icc p q := Set.Icc_subset_Icc hpc1 hc2q
  have hsubL : Set.Icc p c₁ ⊆ Set.Icc p q := Set.Icc_subset_Icc (le_refl p) (le_trans hc12 hc2q)
  have hsubR : Set.Icc c₂ q ⊆ Set.Icc p q := Set.Icc_subset_Icc (le_trans hpc1 hc12) (le_refl q)
  have hband_ge1 : (1 : ℝ) ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 4 * cu * T + 3 := by
    nlinarith [hN.le, hδ.le, hT.le, hsqrtnn, mul_nonneg hcunn hT.le]
  have hlow_ge1 : (1 : ℝ) ≤ (1 / cl) * (4 * N * Real.sqrt (δ / T)) + 1 := by
    have h0 : 0 ≤ (1 / cl) * (4 * N * Real.sqrt (δ / T)) :=
      mul_nonneg (div_nonneg zero_le_one hcl.le)
        (mul_nonneg (mul_nonneg (by norm_num) hN.le) hsqrtnn)
    linarith
  have hMidBound :
      (((Finset.Icc ⌈c₁⌉ ⌊c₂⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ (1 / cl) * (4 * N * Real.sqrt (δ / T)) + 1 := by
    rcases hmid with hdeg | hsmall
    · have hc := card_filter_le_length c₁ c₂ δ φ hc12
      have : c₂ - c₁ = 0 := by rw [hdeg]; ring
      rw [this] at hc; linarith [hc, hlow_ge1]
    · have hlowlower : ∀ z ∈ Set.Icc c₁ c₂, cl * (T / N) ≤ |deriv φ z| + N * |iteratedDeriv 2 φ z| :=
        fun z hz => hlower z (hsubM hz)
      exact bands_count_mono_low_slack N T δ cl c₁ c₂ φ hN hT hδ hcl hactive hc12 hcd hsmall
        hlowlower
  have hLeftBound :
      (((Finset.Icc ⌈p⌉ ⌊c₁⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 4 * cu * T + 3 := by
    rcases hLeft with hdeg | ⟨hlb, hsign⟩
    · have hc := card_filter_le_length p c₁ δ φ hpc1
      have : c₁ - p = 0 := by rw [hdeg]; ring
      rw [this] at hc; linarith [hc, hband_ge1]
    · have hub : ∀ z ∈ Set.Icc p c₁, |deriv φ z| ≤ cu * T / N := by
        intro z hz; have := hd1 z (hsubL hz); rwa [mul_div_assoc]
      have hmonoL : MonotoneOn (deriv φ) (Set.Icc p c₁) ∨ AntitoneOn (deriv φ) (Set.Icc p c₁) :=
        hmono.imp (fun h => h.mono hsubL) (fun h => h.mono hsubL)
      exact bands_count_mono_band_slack N T δ cu p c₁ φ hN hT hδ hcu hactiveT hpc1 hcd
        (hsubL.trans (hpq_sub.trans hsub)) hlb hub hmonoL hsign
  have hRightBound :
      (((Finset.Icc ⌈c₂⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ 16 * N * Real.sqrt (δ / T) + 56 * N * δ + 4 * cu * T + 3 := by
    rcases hRight with hdeg | ⟨hlb, hsign⟩
    · have hc := card_filter_le_length c₂ q δ φ hc2q
      have : q - c₂ = 0 := by rw [hdeg]; ring
      rw [this] at hc; linarith [hc, hband_ge1]
    · have hub : ∀ z ∈ Set.Icc c₂ q, |deriv φ z| ≤ cu * T / N := by
        intro z hz; have := hd1 z (hsubR hz); rwa [mul_div_assoc]
      have hmonoR : MonotoneOn (deriv φ) (Set.Icc c₂ q) ∨ AntitoneOn (deriv φ) (Set.Icc c₂ q) :=
        hmono.imp (fun h => h.mono hsubR) (fun h => h.mono hsubR)
      exact bands_count_mono_band_slack N T δ cu c₂ q φ hN hT hδ hcu hactiveT hc2q hcd
        (hsubR.trans (hpq_sub.trans hsub)) hlb hub hmonoR hsign
  exact bands_count_mono_of_split_slack N T δ cu cl p q c₁ c₂ φ hN hT hδ hcu hcl hcl1 hsqrtnn
    hLeftBound hMidBound hRightBound

theorem bands_count_mono (N T δ a b p q : ℝ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ) (hactive : 4 * δ < T)
    (hcd : ContDiff ℝ 2 φ)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N))
    (hpq_sub : Set.Icc p q ⊆ Set.Icc a b)
    (hd1 : ∀ x ∈ Set.Icc p q, |deriv φ x| ≤ T / N)
    (hlower : ∀ x ∈ Set.Icc p q, T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    -- `φ'` is monotone on the piece (constant-sign `φ''`).
    (hmono : MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q)) :
    (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  -- Specialize the two-sided slack engine at `cu = cl = 1` (where `g(1,1) = 1`).
  have h := bands_count_mono_slack N T δ a b p q 1 1 φ hN hT hδ le_rfl one_pos le_rfl
    (by simpa using hactive) hcd hsub hpq_sub
    (fun x hx => by simpa using hd1 x hx)
    (fun x hx => by simpa using hlower x hx) hmono
  have e : (112:ℝ) * (1 / 1) * (N * (δ + Real.sqrt (δ / T)) + T + 1)
      = 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by rw [div_one, mul_one]
  rw [e] at h
  exact h

/-- **Breakpoint chaining (the combinatorial core).**  Given an ordered list of breakpoints
`L = [s₁,…,sₘ]` with the per-consecutive-piece bound `count[sᵢ,sᵢ₊₁] ≤ B` packaged as a chain over
`a :: L ++ [b]`, the total count `count[a,b]` is at most `(m+1)·B`.  Proven by induction on `L`,
peeling the first breakpoint and applying `count_split` at it.  This is the genuine summation of the
`≤ K+1` per-piece bounds; it is fully discharged here (no stub). -/
private theorem count_le_of_chain (δ B : ℝ) (φ : ℝ → ℝ) :
    ∀ (L : List ℝ) (a b : ℝ),
      List.IsChain (fun p q =>
        (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) ≤ B)
        (a :: (L ++ [b])) →
      (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ ((L.length : ℝ) + 1) * B := by
  intro L
  induction L with
  | nil =>
    intro a b hch
    simp only [List.nil_append] at hch
    rw [List.isChain_cons_cons] at hch
    simpa using hch.1
  | cons s L' ih =>
    intro a b hch
    simp only [List.cons_append] at hch
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hab, hrest⟩ := hch
    have hsplit := count_split a b s δ φ
    have hIH := ih s b hrest
    have hstep :
        (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ B + ((L'.length : ℝ) + 1) * B := by
      calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
          ≤ (((Finset.Icc ⌈a⌉ ⌊s⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
            + (((Finset.Icc ⌈s⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) :=
            hsplit
        _ ≤ B + ((L'.length : ℝ) + 1) * B := by linarith
    calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ B + ((L'.length : ℝ) + 1) * B := hstep
      _ = (((s :: L').length : ℝ) + 1) * B := by push_cast [List.length_cons]; ring

/-- **`iteratedDeriv 2 φ` is `deriv (deriv φ)`** (pointwise), for any `φ`. -/
private theorem iteratedDeriv_two_eq (φ : ℝ → ℝ) (z : ℝ) :
    iteratedDeriv 2 φ z = deriv (deriv φ) z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- **Constant sign on the interior from a no-interior-zero gap.**  If `g` is continuous on
`[p,q]` and has no zero in the open interval `(p,q)`, then `g` is either `≥ 0` on all of `(p,q)`
or `≤ 0` on all of `(p,q)`.  (IVT: if `g` took both a positive and a negative value on the
connected `(p,q)` it would vanish somewhere in `(p,q)`.) -/
private theorem const_sign_of_no_zero {g : ℝ → ℝ} {p q : ℝ}
    (hcont : ContinuousOn g (Set.Icc p q))
    (hno : ∀ z ∈ Set.Ioo p q, g z ≠ 0) :
    (∀ z ∈ Set.Ioo p q, 0 ≤ g z) ∨ (∀ z ∈ Set.Ioo p q, g z ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₁, hx₁mem, hx₁neg⟩, ⟨x₀, hx₀mem, hx₀pos⟩⟩ := hcon
  -- `g x₁ < 0` and `0 < g x₀`, both in `Ioo p q`.
  have hsubIoo : Set.uIcc x₀ x₁ ⊆ Set.Ioo p q :=
    Set.ordConnected_Ioo.uIcc_subset hx₀mem hx₁mem
  have hsub : Set.uIcc x₀ x₁ ⊆ Set.Icc p q := hsubIoo.trans Set.Ioo_subset_Icc_self
  have hcontU : ContinuousOn g (Set.uIcc x₀ x₁) := hcont.mono hsub
  have hmem0 : (0 : ℝ) ∈ Set.uIcc (g x₀) (g x₁) := by
    rw [Set.mem_uIcc]; exact Or.inr ⟨le_of_lt hx₁neg, le_of_lt hx₀pos⟩
  obtain ⟨c, hcmem, hcval⟩ := intermediate_value_uIcc hcontU hmem0
  -- `c ∈ uIcc x₀ x₁ ⊆ Ioo p q`, and `g c = 0` — contradiction.
  exact hno c (hsubIoo hcmem) hcval

/-- **No-interior-zero gap ⟹ `deriv φ` monotone or antitone on `[p,q]`.**  If `φ` is `C²` and
`iteratedDeriv 2 φ` (= `(deriv φ)'`) has no zero in the open interval `(p,q)`, then by
`const_sign_of_no_zero` it has constant sign there, so `deriv φ` is `MonotoneOn` (sign `≥ 0`)
or `AntitoneOn` (sign `≤ 0`) on `[p,q]`. -/
private theorem mono_or_anti_of_no_zero {φ : ℝ → ℝ} {p q : ℝ}
    (hcd : ContDiff ℝ 2 φ)
    (hno : ∀ z ∈ Set.Ioo p q, iteratedDeriv 2 φ z ≠ 0) :
    MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q) := by
  -- `deriv φ` is `C¹`, so continuous and differentiable; `(deriv φ)' = iteratedDeriv 2 φ`.
  have hcd1 : ContDiff ℝ 1 (deriv φ) := by
    have h2 : ContDiff ℝ (1 + 1) φ := by norm_num; exact hcd
    exact h2.deriv'
  have hcont1 : ContinuousOn (deriv φ) (Set.Icc p q) :=
    (hcd1.continuous).continuousOn
  have hdiff1 : DifferentiableOn ℝ (deriv φ) (interior (Set.Icc p q)) :=
    (hcd1.differentiable (by norm_num)).differentiableOn
  -- The second derivative as `deriv (deriv φ)`, continuous on `[p,q]`.
  have hcont2 : ContinuousOn (iteratedDeriv 2 φ) (Set.Icc p q) := by
    have : Continuous (deriv (deriv φ)) := hcd1.continuous_deriv (by norm_num)
    refine ContinuousOn.congr (this.continuousOn) ?_
    intro z _; exact iteratedDeriv_two_eq φ z
  -- Constant sign of `iteratedDeriv 2 φ` on `Ioo p q`.
  rcases const_sign_of_no_zero hcont2 hno with hpos | hneg
  · -- `≥ 0` on the interior ⟹ MonotoneOn.
    left
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q) hcont1 hdiff1 ?_
    intro z hz
    rw [interior_Icc] at hz
    rw [← iteratedDeriv_two_eq φ z]
    exact hpos z hz
  · -- `≤ 0` on the interior ⟹ AntitoneOn.
    right
    refine antitoneOn_of_deriv_nonpos (convex_Icc p q) hcont1 hdiff1 ?_
    intro z hz
    rw [interior_Icc] at hz
    rw [← iteratedDeriv_two_eq φ z]
    exact hneg z hz

/-- **Chain over `c :: L ++ [b]` from a sorted, covering breakpoint list.**  The relation `Geo`
carries fixed outer bounds `a, b`: `Geo p q := a ≤ p ∧ q ≤ b ∧ Ioo p q ∩ Z = ∅`.  Given a current
left endpoint `c` with `a ≤ c ≤ b`, a list `L` sorted ascending with all elements in `[c,b]`, and
which covers every `Z`-point strictly inside `(c,b)`, the relation holds along every consecutive
pair of `c :: L ++ [b]`.  Proven by induction on `L`, peeling the first gap `(c, head L)`: a
`Z`-point there would be a covered zero below the minimum of `L`.  Recursion advances `c ↦ head L`
while keeping the outer bounds `a, b` (hence the relation) fixed. -/
private theorem geo_chain_of_sorted (Z : Set ℝ) (a b : ℝ) :
    ∀ (L : List ℝ) (c : ℝ), a ≤ c → c ≤ b →
      L.Pairwise (· ≤ ·) → (∀ x ∈ L, c ≤ x ∧ x ≤ b) →
      (∀ z ∈ Z, c < z → z < b → z ∈ L) →
      List.IsChain
        (fun p q => a ≤ p ∧ q ≤ b ∧ (Set.Ioo p q ∩ Z = ∅))
        (c :: (L ++ [b])) := by
  intro L
  induction L with
  | nil =>
    intro c hac hcb _ _ hcover
    simp only [List.nil_append]
    rw [List.isChain_cons_cons]
    refine ⟨⟨hac, le_refl b, ?_⟩, List.isChain_singleton b⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzIoo, hzZ⟩
    exact absurd (hcover z hzZ hzIoo.1 hzIoo.2) (by simp)
  | cons x L' ih =>
    intro c hac hcb hsorted hbounds hcover
    simp only [List.cons_append]
    rw [List.isChain_cons_cons]
    have hxmem : x ∈ x :: L' := List.mem_cons_self
    have hxb : x ≤ b := (hbounds x hxmem).2
    have hcx : c ≤ x := (hbounds x hxmem).1
    -- head-of-tail facts from sortedness.
    have hsorted' : L'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsorted).2
    have hxle : ∀ y ∈ L', x ≤ y := (List.pairwise_cons.mp hsorted).1
    refine ⟨⟨hac, hxb, ?_⟩, ?_⟩
    · -- gap `(c, x)` contains no `Z`-point.
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzIoo, hzZ⟩
      have hzL : z ∈ x :: L' := hcover z hzZ hzIoo.1 (lt_of_lt_of_le hzIoo.2 hxb)
      rcases List.mem_cons.mp hzL with hzx | hzL'
      · exact absurd hzx (ne_of_lt hzIoo.2)
      · exact absurd (hxle z hzL') (not_le_of_gt hzIoo.2)
    · -- recurse with left endpoint `x` (outer bounds `a,b` unchanged).
      apply ih x (le_trans hac hcx) hxb hsorted'
      · intro y hy; exact ⟨hxle y hy, (hbounds y (List.mem_cons_of_mem x hy)).2⟩
      · intro z hzZ hxz hzb
        have hzL : z ∈ x :: L' := hcover z hzZ (lt_of_le_of_lt hcx hxz) hzb
        rcases List.mem_cons.mp hzL with hzx | hzL'
        · exact absurd hzx.symm (ne_of_lt hxz)
        · exact hzL'

/-- **Existence of the monotone-piece breakpoint list.**  From the finite zero set of
`φ'' = iteratedDeriv 2 φ` in `[a,b]` (size `≤ K`), the interval `[a,b]` decomposes into `≤ K+1`
subintervals on which `φ''` has constant sign, hence on which `φ'` is monotone.  We enumerate the
zero set as a sorted list `L`, take breakpoints `a :: L ++ [b]`, and on each open gap `φ''` is
nonzero, so (being continuous, `ContDiff ℝ 2 φ`) of one sign by IVT, giving `MonotoneOn`/
`AntitoneOn` of `deriv φ`.

The finiteness of the zero set is carried explicitly (`hz2fin`): `ncard ≤ K` alone does not
imply finiteness (an infinite set has `ncard = 0`), and the math intends finitely many zeros. -/
private theorem exists_mono_piece_breakpoints (a b : ℝ) (K : ℕ) (φ : ℝ → ℝ)
    (hab : a ≤ b)
    (hcd : ContDiff ℝ 2 φ)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K) :
    ∃ L : List ℝ, L.length ≤ K ∧
      List.IsChain (fun p q => a ≤ p ∧ q ≤ b ∧
        (MonotoneOn (deriv φ) (Set.Icc p q) ∨ AntitoneOn (deriv φ) (Set.Icc p q)))
        (a :: (L ++ [b])) := by
  classical
  set Z : Set ℝ := Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0} with hZdef
  -- The sorted breakpoint list: zeros of `φ''` in `[a,b]`.
  set L : List ℝ := hz2fin.toFinset.sort (· ≤ ·) with hLdef
  refine ⟨L, ?_, ?_⟩
  · -- `L.length = #Z = ncard Z ≤ K`.
    rw [hLdef, Finset.length_sort]
    have hcardZ : hz2fin.toFinset.card = Z.ncard :=
      (Set.ncard_eq_toFinset_card Z hz2fin).symm
    rw [hcardZ]; exact hz2
  · -- The geometric chain, then upgraded to the monotone/antitone chain.
    have hsortedL : L.Pairwise (· ≤ ·) := by
      rw [hLdef]; exact Finset.pairwise_sort _ _
    have hbounds : ∀ x ∈ L, a ≤ x ∧ x ≤ b := by
      intro x hx
      rw [hLdef, Finset.mem_sort, Set.Finite.mem_toFinset, hZdef] at hx
      exact hx.1
    have hcover : ∀ z ∈ Z, a < z → z < b → z ∈ L := by
      intro z hzZ _ _
      rw [hLdef, Finset.mem_sort, Set.Finite.mem_toFinset]
      exact hzZ
    have hgeo := geo_chain_of_sorted Z a b L a (le_refl a) hab hsortedL hbounds hcover
    refine hgeo.imp ?_
    rintro p q ⟨hap, hqb, hgap⟩
    refine ⟨hap, hqb, ?_⟩
    -- No `Z`-point in `(p,q)` ⟹ no `φ''`-zero in `Ioo p q` (since `Ioo p q ⊆ [a,b]`).
    apply mono_or_anti_of_no_zero hcd
    intro z hzIoo hzero
    have hzab : z ∈ Set.Icc a b :=
      ⟨le_of_lt (lt_of_le_of_lt hap hzIoo.1), le_of_lt (lt_of_lt_of_le hzIoo.2 hqb)⟩
    have hzZ : z ∈ Z := by rw [hZdef]; exact ⟨hzab, hzero⟩
    have : z ∈ Set.Ioo p q ∩ Z := ⟨hzIoo, hzZ⟩
    rw [hgap] at this
    exact this

/-- **Piece-split assembly.**  Split `[a,b]` into the `≤ K+1` maximal subintervals on which `φ''`
has constant sign (there are `≤ (#zeros of φ'') + 1 ≤ K+1` of them), on each of which `φ'` is
monotone.  Each such piece is bounded by `bands_count_mono` (constant `8`).  Summing the `≤ K+1`
per-piece bounds (via `count_le_of_chain`, which chains `count_split`'s sub-additivity at the `≤ K`
interior breakpoints) gives the conclusion with constant `8(K+1) ≤ 64(K+1)`.

The combinatorial summation (`count_le_of_chain`) and the per-piece analytic content
(`bands_count_mono`) are both discharged here; the breakpoint construction is delegated to
`exists_mono_piece_breakpoints`. -/
private theorem bands_count_active_split (N T δ a b : ℝ) (K : ℕ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ) (hactive : 4 * δ < T)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N)) (hcd : ContDiff ℝ 2 φ)
    (hd1 : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ T / N)
    (hlower : ∀ x ∈ Set.Icc a b, T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (_hz1 : (Set.Icc a b ∩ {x | deriv φ x = 0}).ncard ≤ K)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * ((K : ℝ) + 1) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  classical
  set B : ℝ := 112 * (N * (δ + Real.sqrt (δ / T)) + T + 1) with hBdef
  have hBnn : 0 ≤ B := by
    have hsq : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
    rw [hBdef]; nlinarith [hN.le, hδ.le, hT.le]
  -- If `[a,b]` is empty the count is `0 ≤` RHS; otherwise `a ≤ b`.
  rcases le_or_gt a b with hab | hba
  swap
  · have hltceil : ⌊b⌋ < ⌈a⌉ := by
      have h1 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
      have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
      have : (⌊b⌋ : ℝ) < (⌈a⌉ : ℝ) := by linarith
      exact_mod_cast this
    have hempty : (Finset.Icc ⌈a⌉ ⌊b⌋) = ∅ := Finset.Icc_eq_empty (by omega)
    have hzero : ((Finset.Icc ⌈a⌉ ⌊b⌋).filter
        (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card = 0 := by rw [hempty]; simp
    rw [hzero, Nat.cast_zero]
    have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
    have hRHS : 0 ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
      have : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
      nlinarith [hN.le, hδ.le, hT.le]
    nlinarith [mul_nonneg hK1 hRHS]
  -- Get the sorted monotone-piece breakpoints.
  obtain ⟨L, hLlen, hLchain⟩ :=
    exists_mono_piece_breakpoints a b K φ hab hcd hz2fin hz2
  -- Each consecutive piece `[p,q]` is monotone, so `bands_count_mono` gives `count[p,q] ≤ B`.
  have hcountchain :
      List.IsChain (fun p q =>
        (((Finset.Icc ⌈p⌉ ⌊q⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) ≤ B)
        (a :: (L ++ [b])) := by
    refine hLchain.imp ?_
    rintro p q ⟨hap, hqb, hmono⟩
    have hpq_sub : Set.Icc p q ⊆ Set.Icc a b := by
      apply Set.Icc_subset_Icc hap hqb
    have hd1' : ∀ x ∈ Set.Icc p q, |deriv φ x| ≤ T / N := fun x hx => hd1 x (hpq_sub hx)
    have hlower' : ∀ x ∈ Set.Icc p q, T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x| :=
      fun x hx => hlower x (hpq_sub hx)
    have := bands_count_mono N T δ a b p q φ hN hT hδ hactive hcd hsub hpq_sub hd1' hlower' hmono
    rw [hBdef]; exact this
  -- Chain the per-piece bounds: `count[a,b] ≤ (L.length + 1)·B`.
  have hchain := count_le_of_chain δ B φ L a b hcountchain
  -- `(L.length + 1) ≤ (K + 1)`, and `B ≥ 0`.
  have hlen_le : ((L.length : ℝ) + 1) ≤ ((K : ℝ) + 1) := by
    have : (L.length : ℝ) ≤ (K : ℝ) := by exact_mod_cast hLlen
    linarith
  calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ ((L.length : ℝ) + 1) * B := hchain
    _ ≤ ((K : ℝ) + 1) * B := by apply mul_le_mul_of_nonneg_right hlen_le hBnn
    _ = 112 * ((K : ℝ) + 1) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by rw [hBdef]; ring

/-- **Active regime `4δ < T`** of Lemma 4.2.

The per-piece analytic content (level/point decoupling, log-free count) is discharged by the proven
`bands_count_mono` (constant `8`, via `mono_low_length` + `bands_count_mono_high`); the `≤ K+1`
constant-sign-`φ''` piece decomposition and its summation are handled by `bands_count_active_split`.
Constant `8(K+1) ≤ 64(K+1)`. -/
theorem bands_count_active (N T δ a b : ℝ) (K : ℕ) (φ : ℝ → ℝ)
    (hN : 0 < N) (hT : 0 < T) (hδ : 0 < δ)
    (hsub : Set.Icc a b ⊆ Set.Icc N (3 * N)) (hcd : ContDiff ℝ 2 φ)
    (hd1 : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ T / N)
    (hlower : ∀ x ∈ Set.Icc a b, T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|)
    (hz1 : (Set.Icc a b ∩ {x | deriv φ x = 0}).ncard ≤ K)
    (hz2fin : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite)
    (hz2 : (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K)
    (hactive : 4 * δ < T) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      ≤ 112 * ((K : ℝ) + 1) * (N * (δ + Real.sqrt (δ / T)) + T + 1) :=
  bands_count_active_split N T δ a b K φ hN hT hδ hactive hsub hcd hd1 hlower hz1 hz2fin hz2

/-- The near-integer count written with the monadic `Finset ℝ` coercion (as the public statement
elaborates) equals the count written with an honest `Finset ℤ` filter (as `preimage_count` and the
helpers use).  Both range over the same integers; `(↑) : ℤ → ℝ` is injective. -/
private theorem card_do_eq_card_int (a b δ : ℝ) (φ : ℝ → ℝ) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun n => distInt (φ (n : ℝ)) ≤ δ)).card
      = ((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card := by
  have hbind : (do let a ← (Finset.Icc ⌈a⌉ ⌊b⌋); pure (↑a : ℝ))
      = (Finset.Icc ⌈a⌉ ⌊b⌋).image (fun (n : ℤ) => (n : ℝ)) := by
    rw [bind_pure_comp]; rfl
  rw [hbind, Finset.filter_image,
    Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h)]

/-- **Lemma 4.2** (writeup 426–461): derivative-band counting, faithful public statement.

The writeup's `log(T/δ)`-many dyadic bands are replaced by a **fixed `O(1)`-many** band partition
(thresholds `√(δT)/N`, `√T/N`, `T/(4N)`), giving the log-free conclusion.  The `(K+1)` factor comes
from splitting `[a,b]` into `≤ (#zeros of φ'')+1 ≤ K+1` constant-sign-`φ''` intervals (on which
`φ'` is monotone).  The trivial regime `T ≤ 4δ` is handled by the crude length bound
(`bands_count_trivial`); the active regime `4δ < T` is the band decomposition
(`bands_count_active`).  Constant `C = 64`. -/
theorem bands_count : ∃ C : ℝ, 0 < C ∧
    ∀ (N T δ a b : ℝ) (K : ℕ) (φ : ℝ → ℝ),
      0 < N → 0 < T → 0 < δ → Set.Icc a b ⊆ Set.Icc N (3 * N) → ContDiff ℝ 2 φ →
      (∀ x ∈ Set.Icc a b, |deriv φ x| ≤ T / N) →
      (∀ x ∈ Set.Icc a b, T / N ≤ |deriv φ x| + N * |iteratedDeriv 2 φ x|) →
      (Set.Icc a b ∩ {x | deriv φ x = 0}).ncard ≤ K →
      (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).Finite →
      (Set.Icc a b ∩ {x | iteratedDeriv 2 φ x = 0}).ncard ≤ K →
      (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun n => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ C * ((K : ℝ) + 1) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
  refine ⟨112, by norm_num, ?_⟩
  intro N T δ a b K φ hN hT hδ hsub hcd hd1 hlower hz1 hz2fin hz2
  -- Convert the public monadic-coerced count to the honest `Finset ℤ` form.
  rw [show (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun n => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
      = (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ) by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (card_do_eq_card_int a b δ φ)]
  have hRHS_nonneg : 0 ≤ N * (δ + Real.sqrt (δ / T)) + T + 1 := by
    have : 0 ≤ Real.sqrt (δ / T) := Real.sqrt_nonneg _
    nlinarith [hN.le, hδ.le, hT.le]
  have hKpos : (1 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  by_cases htriv : T ≤ 4 * δ
  · -- Trivial regime: `count ≤ 4·RHS ≤ 64(K+1)·RHS`.
    have hbase := bands_count_trivial N T δ a b φ hN hT hδ hsub htriv
    calc (((Finset.Icc ⌈a⌉ ⌊b⌋).filter (fun (n : ℤ) => distInt (φ (n : ℝ)) ≤ δ)).card : ℝ)
        ≤ 4 * (N * (δ + Real.sqrt (δ / T)) + T + 1) := hbase
      _ ≤ 112 * ((K : ℝ) + 1) * (N * (δ + Real.sqrt (δ / T)) + T + 1) := by
          nlinarith [hRHS_nonneg, hKpos]
  · -- Active regime.
    have htriv' : 4 * δ < T := lt_of_not_ge htriv
    exact bands_count_active N T δ a b K φ hN hT hδ hsub hcd hd1 hlower hz1 hz2fin hz2 htriv'

end Squarefree.Counting
