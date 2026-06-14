import Squarefree.FiniteDiff
import Mathlib

/-!
# Finite-difference mean-value bounds (§7 support for node N6)

Generic facts feeding `sec7_third_diff_product_rule` (Bracket/Sec7Branch.lean, md 1516–34):
the exact discrete Leibniz expansion of `Δ_{h₁,h₂,h₃}(u·v)` (whose `|T| ≤ 1` terms are eq
(7.1)'s main terms with `ξᵢ = 0` and whose four `|T| ≥ 2` terms form the error), the
`|Δ_h{f}| ≤ 1` fract bounds, and the MVT bounds `|Δ_{h…}f| ≤ C·∏h` from derivative bounds
on an interval.
-/

namespace Squarefree.FiniteDiff

/-- Exact discrete Leibniz rule for the mixed third difference of a product (md 1516–22):
the first four right-hand terms are the `|T| ≤ 1` main terms of eq (7.1) (at shifts
`ξᵢ = 0`), the last four are the `|T| ≥ 2` error terms. -/
theorem diff3_mul (u v : ℝ → ℝ) (h₁ h₂ h₃ r : ℝ) :
    diff3 h₁ h₂ h₃ (fun t => u t * v t) r =
      u (r + (h₁ + h₂ + h₃)) * diff3 h₁ h₂ h₃ v r
      + diff1 h₁ u (r + h₂ + h₃) * diff1 h₂ (diff1 h₃ v) r
      + diff1 h₂ u (r + h₁ + h₃) * diff1 h₁ (diff1 h₃ v) r
      + diff1 h₃ u (r + h₁ + h₂) * diff1 h₁ (diff1 h₂ v) r
      + diff1 h₁ (diff1 h₂ u) (r + h₃) * diff1 h₃ v r
      + diff1 h₁ (diff1 h₃ u) (r + h₂) * diff1 h₂ v r
      + diff1 h₂ (diff1 h₃ u) (r + h₁) * diff1 h₁ v r
      + diff3 h₁ h₂ h₃ u r * v r := by
  simp only [diff3, diff1]
  ring_nf

/-- `|{y}| ≤ 1`. -/
theorem abs_fract_le (y : ℝ) : |Int.fract y| ≤ 1 := by
  have h1 := Int.fract_nonneg y
  have h2 := Int.fract_lt_one y
  rw [abs_le]; constructor <;> linarith

/-- `|Δ_h {f}| ≤ 1` (both fract values lie in `[0,1)`). -/
theorem abs_diff1_fract_le (h : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    |diff1 h (fun t => Int.fract (f t)) x| ≤ 1 := by
  simp only [diff1]
  have h1 := Int.fract_nonneg (f (x + h))
  have h2 := Int.fract_lt_one (f (x + h))
  have h3 := Int.fract_nonneg (f x)
  have h4 := Int.fract_lt_one (f x)
  rw [abs_le]; constructor <;> linarith

/-- MVT bound for a single forward difference: a derivative bound `|f'| ≤ C` on `[a,b]`
gives `|Δ_h f(x)| ≤ C·h` whenever `x, x+h ∈ [a,b]`, `h ≥ 0`. -/
theorem abs_diff1_le {f f' : ℝ → ℝ} {a b C h x : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hC : ∀ t ∈ Set.Icc a b, |f' t| ≤ C)
    (hh : 0 ≤ h) (hx : x ∈ Set.Icc a b) (hxh : x + h ∈ Set.Icc a b) :
    |diff1 h f x| ≤ C * h := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := C) (s := Set.Icc a b)
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by simpa [Real.norm_eq_abs] using hC t ht)
    (convex_Icc a b) hx hxh
  simp only [diff1]
  calc |f (x + h) - f x| ≤ C * |x + h - x| := by
        simpa [Real.norm_eq_abs] using key
    _ = C * h := by rw [show x + h - x = h by ring, abs_of_nonneg hh]

/-- Derivative of a forward difference (pointwise). -/
theorem hasDerivAt_diff1 {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : HasDerivAt f (f' x) x) (hxh : HasDerivAt f (f' (x + h)) (x + h)) :
    HasDerivAt (diff1 h f) (diff1 h f' x) x := by
  simp only [diff1]
  have h1 : HasDerivAt (fun y => f (y + h)) (f' (x + h)) x := by
    have := hxh.comp x (hasDerivAt_id x |>.add_const h)
    simpa using this
  exact h1.sub hx

/-- MVT bound for a double forward difference: `|f''| ≤ C` on `[a,b]` gives
`|Δ_{h₂}Δ_{h₃} f(x)| ≤ C·h₃·h₂` whenever `x, x+h₂+h₃ ∈ [a,b]`, `h₂, h₃ ≥ 0`. -/
theorem abs_diff2_le {f f' f'' : ℝ → ℝ} {a b C h₂ h₃ x : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hd' : ∀ t ∈ Set.Icc a b, HasDerivAt f' (f'' t) t)
    (hC : ∀ t ∈ Set.Icc a b, |f'' t| ≤ C)
    (h2 : 0 ≤ h₂) (h3 : 0 ≤ h₃)
    (hx : x ∈ Set.Icc a b) (hxh : x + h₂ + h₃ ∈ Set.Icc a b) :
    |diff1 h₂ (diff1 h₃ f) x| ≤ C * h₃ * h₂ := by
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨ha', hb'⟩ := hxh
  have hdg : ∀ t ∈ Set.Icc x (x + h₂), HasDerivAt (diff1 h₃ f) (diff1 h₃ f' t) t := by
    intro t ht
    exact hasDerivAt_diff1
      (hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (hd (t + h₃) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hCg : ∀ t ∈ Set.Icc x (x + h₂), |diff1 h₃ f' t| ≤ C * h₃ := by
    intro t ht
    exact abs_diff1_le hd' hC h3 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact abs_diff1_le hdg hCg h2 (Set.left_mem_Icc.2 (by linarith))
    (Set.right_mem_Icc.2 (by linarith))

/-- MVT bound for the mixed third difference: `|f'''| ≤ C` on `[a,b]` gives
`|Δ_{h₁,h₂,h₃} f(x)| ≤ C·h₃·h₂·h₁` whenever `x, x+h₁+h₂+h₃ ∈ [a,b]`, `hᵢ ≥ 0`. -/
theorem abs_diff3_le {f f' f'' f''' : ℝ → ℝ} {a b C h₁ h₂ h₃ x : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hd' : ∀ t ∈ Set.Icc a b, HasDerivAt f' (f'' t) t)
    (hd'' : ∀ t ∈ Set.Icc a b, HasDerivAt f'' (f''' t) t)
    (hC : ∀ t ∈ Set.Icc a b, |f''' t| ≤ C)
    (h1 : 0 ≤ h₁) (h2 : 0 ≤ h₂) (h3 : 0 ≤ h₃)
    (hx : x ∈ Set.Icc a b) (hxh : x + h₁ + h₂ + h₃ ∈ Set.Icc a b) :
    |diff3 h₁ h₂ h₃ f x| ≤ C * h₃ * h₂ * h₁ := by
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨ha', hb'⟩ := hxh
  have hdg : ∀ t ∈ Set.Icc x (x + h₁),
      HasDerivAt (diff1 h₂ (diff1 h₃ f)) (diff1 h₂ (diff1 h₃ f') t) t := by
    intro t ht
    have inner : ∀ s ∈ Set.Icc x (x + h₁ + h₂),
        HasDerivAt (diff1 h₃ f) (diff1 h₃ f' s) s := by
      intro s hs
      exact hasDerivAt_diff1
        (hd s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        (hd (s + h₃) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    exact hasDerivAt_diff1
      (inner t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (inner (t + h₂) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hCg : ∀ t ∈ Set.Icc x (x + h₁),
      |diff1 h₂ (diff1 h₃ f') t| ≤ C * h₃ * h₂ := by
    intro t ht
    exact abs_diff2_le hd' hd'' hC h2 h3 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact abs_diff1_le hdg hCg h1 (Set.left_mem_Icc.2 (by linarith))
    (Set.right_mem_Icc.2 (by linarith))

/-- Signed MVT: a nonnegative derivative on `[a,b]` gives `Δ_h f(x) ≥ 0` for `h ≥ 0`
(§7 support for node N7: monotonicity of the fiber drivers `B_i`). -/
theorem diff1_nonneg {f f' : ℝ → ℝ} {a b h x : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hC : ∀ t ∈ Set.Icc a b, 0 ≤ f' t)
    (hh : 0 ≤ h) (hx : x ∈ Set.Icc a b) (hxh : x + h ∈ Set.Icc a b) :
    0 ≤ diff1 h f x := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · simp [diff1]
  · have hsub : Set.Icc x (x + h) ⊆ Set.Icc a b := fun t ht =>
      ⟨le_trans hx.1 ht.1, le_trans ht.2 hxh.2⟩
    have hcont : ContinuousOn f (Set.Icc x (x + h)) := fun t ht =>
      ((hd t (hsub ht)).continuousAt).continuousWithinAt
    have hlt : x < x + h := by linarith
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont
      (fun t ht => hd t (hsub (Set.mem_Icc_of_Ioo ht)))
    have h0 : 0 ≤ f' c := hC c (hsub (Set.mem_Icc_of_Ioo hc))
    rw [hslope] at h0
    have hden : (0:ℝ) < x + h - x := by linarith
    have := mul_nonneg h0 hden.le
    rw [div_mul_cancel₀ _ (ne_of_gt hden)] at this
    simpa [diff1] using this

/-- Signed MVT for the double difference: `f'' ≥ 0` on `[a,b]` gives
`Δ_{h₂}Δ_{h₃} f(x) ≥ 0`. -/
theorem diff2_nonneg {f f' f'' : ℝ → ℝ} {a b h₂ h₃ x : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hd' : ∀ t ∈ Set.Icc a b, HasDerivAt f' (f'' t) t)
    (hC : ∀ t ∈ Set.Icc a b, 0 ≤ f'' t)
    (h2 : 0 ≤ h₂) (h3 : 0 ≤ h₃)
    (hx : x ∈ Set.Icc a b) (hxh : x + h₂ + h₃ ∈ Set.Icc a b) :
    0 ≤ diff1 h₂ (diff1 h₃ f) x := by
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨ha', hb'⟩ := hxh
  have hdg : ∀ t ∈ Set.Icc x (x + h₂), HasDerivAt (diff1 h₃ f) (diff1 h₃ f' t) t := by
    intro t ht
    exact hasDerivAt_diff1
      (hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (hd (t + h₃) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hCg : ∀ t ∈ Set.Icc x (x + h₂), 0 ≤ diff1 h₃ f' t := by
    intro t ht
    exact diff1_nonneg hd' hC h3 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact diff1_nonneg hdg hCg h2 (Set.left_mem_Icc.2 (by linarith))
    (Set.right_mem_Icc.2 (by linarith))

/-- First-order Taylor with a second-derivative bound, backward step (§7 node N4, md
1332–43): `|f(c−s) − f(c) + f'(c)·s| ≤ C·s²` when `|f''| ≤ C` on `[a,b] ∋ c−s, c`,
`s ≥ 0`. -/
theorem abs_taylor1_le {f f' f'' : ℝ → ℝ} {a b C s c : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hd' : ∀ t ∈ Set.Icc a b, HasDerivAt f' (f'' t) t)
    (hC : ∀ t ∈ Set.Icc a b, |f'' t| ≤ C)
    (hs : 0 ≤ s) (hcs : c - s ∈ Set.Icc a b) (hc : c ∈ Set.Icc a b) :
    |f (c - s) - f c + f' c * s| ≤ C * s ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC c hc)
  have hsub : Set.Icc (c - s) c ⊆ Set.Icc a b := fun t ht =>
    ⟨le_trans hcs.1 ht.1, le_trans ht.2 hc.2⟩
  -- `g y := f y − f'(c)·y` has `g' t = f' t − f' c` with `|g'| ≤ C·s` on `[c−s, c]`
  have hdg : ∀ t ∈ Set.Icc (c - s) c,
      HasDerivAt (fun y => f y - f' c * y) (f' t - f' c) t := by
    intro t ht
    simpa using (hd t (hsub ht)).sub ((hasDerivAt_id t).const_mul (f' c))
  have hbg : ∀ t ∈ Set.Icc (c - s) c, |f' t - f' c| ≤ C * s := by
    intro t ht
    have hmemc : t + (c - t) ∈ Set.Icc a b := by
      rw [show t + (c - t) = c by ring]; exact hc
    have h1 : |diff1 (c - t) f' t| ≤ C * (c - t) :=
      abs_diff1_le hd' hC (by linarith [ht.2]) (hsub ht) hmemc
    have h2 : |f' c - f' t| ≤ C * (c - t) := by
      simpa [diff1, show t + (c - t) = c by ring] using h1
    rw [abs_sub_comm]
    refine le_trans h2 (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith [ht.1]
  have hmem2 : c - s + s ∈ Set.Icc (c - s) c := by
    rw [show c - s + s = c by ring]
    exact Set.right_mem_Icc.2 (by linarith)
  have key := abs_diff1_le hdg hbg hs (Set.left_mem_Icc.2 (by linarith)) hmem2
  have e : diff1 s (fun y => f y - f' c * y) (c - s) = f c - f (c - s) - f' c * s := by
    simp only [diff1, show c - s + s = c by ring]; ring
  rw [e] at key
  calc |f (c - s) - f c + f' c * s|
      = |f c - f (c - s) - f' c * s| := by
        rw [show f (c - s) - f c + f' c * s = -(f c - f (c - s) - f' c * s) by ring, abs_neg]
    _ ≤ C * s * s := key
    _ = C * s ^ 2 := by ring

/-- A continuous function with no zero on `[a,b]` has constant sign: some `σ ∈ {±1}` with
`0 ≤ σ·f` on `[a,b]` (§7 node N7: constant sign of `f₂'''` on the count window). -/
theorem exists_sign_of_ne_zero {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hne : ∀ t ∈ Set.Icc a b, f t ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ t ∈ Set.Icc a b, 0 ≤ σ * f t := by
  rcases le_or_gt a b with hab | hab
  swap
  · exact ⟨1, Or.inl rfl, fun t ht => absurd (le_trans ht.1 ht.2) (not_le.mpr hab)⟩
  have hIVT : ∀ t ∈ Set.Icc a b, f a < 0 → 0 < f t → False := by
    intro t ht hfa hft
    have hsub : Set.uIcc a t ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le ht.1]
      exact fun y hy => ⟨hy.1, le_trans hy.2 ht.2⟩
    have h0 : (0:ℝ) ∈ Set.uIcc (f a) (f t) := by
      rw [Set.mem_uIcc]; exact Or.inl ⟨hfa.le, hft.le⟩
    obtain ⟨y, hy, hfy⟩ := intermediate_value_uIcc (hcont.mono hsub) h0
    exact hne y (hsub hy) hfy
  have hIVT' : ∀ t ∈ Set.Icc a b, 0 < f a → f t < 0 → False := by
    intro t ht hfa hft
    have hsub : Set.uIcc a t ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le ht.1]
      exact fun y hy => ⟨hy.1, le_trans hy.2 ht.2⟩
    have h0 : (0:ℝ) ∈ Set.uIcc (f a) (f t) := by
      rw [Set.mem_uIcc]; exact Or.inr ⟨hft.le, hfa.le⟩
    obtain ⟨y, hy, hfy⟩ := intermediate_value_uIcc (hcont.mono hsub) h0
    exact hne y (hsub hy) hfy
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.2 hab
  rcases le_or_gt 0 (f a) with hfa | hfa
  · have hfa' : 0 < f a := lt_of_le_of_ne hfa (Ne.symm (hne a hamem))
    refine ⟨1, Or.inl rfl, fun t ht => ?_⟩
    rcases le_or_gt 0 (f t) with hpos | hneg
    · nlinarith
    · exact absurd (hIVT' t ht hfa' hneg) not_false
  · refine ⟨-1, Or.inr rfl, fun t ht => ?_⟩
    rcases le_or_gt (f t) 0 with hneg | hpos
    · nlinarith
    · exact absurd (hIVT t ht hfa hpos) not_false

/-- If `F` is injective on the `φ`-values of `s`, the `φ`-image is no larger than the
`F ∘ φ`-image (§7 node N7: the fiber tuple is counted through a monotone scalar). -/
theorem card_image_factor {γ α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset γ) (φ : γ → α) (F : α → β)
    (hinj : ∀ r ∈ s, ∀ r' ∈ s, F (φ r) = F (φ r') → φ r = φ r') :
    (s.image φ).card ≤ (s.image fun r => F (φ r)).card := by
  refine Finset.card_le_card_of_injOn F ?_ ?_
  · intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv ⊢
    obtain ⟨r, hr, rfl⟩ := hv
    exact ⟨r, hr, rfl⟩
  · intro v hv w hw hFvw
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv hw
    obtain ⟨r, hr, rfl⟩ := hv
    obtain ⟨r', hr', rfl⟩ := hw
    exact hinj r hr r' hr' hFvw

/-- Lattice-path count (§7 node N7, eq 7.2): three `ℤ`-valued functions, each
non-decreasing on `Finset.Icc p q`, take at most `1 + Σᵢ (gᵢ q − gᵢ p)` distinct joint
values. -/
theorem card_image_mono3 {p q : ℤ} (hpq : p ≤ q) (g₁ g₂ g₃ : ℤ → ℤ)
    (h₁ : ∀ r ∈ Finset.Icc p q, ∀ r' ∈ Finset.Icc p q, r ≤ r' → g₁ r ≤ g₁ r')
    (h₂ : ∀ r ∈ Finset.Icc p q, ∀ r' ∈ Finset.Icc p q, r ≤ r' → g₂ r ≤ g₂ r')
    (h₃ : ∀ r ∈ Finset.Icc p q, ∀ r' ∈ Finset.Icc p q, r ≤ r' → g₃ r ≤ g₃ r') :
    (((Finset.Icc p q).image fun r => (g₁ r, g₂ r, g₃ r)).card : ℤ) ≤
      1 + (g₁ q - g₁ p) + (g₂ q - g₂ p) + (g₃ q - g₃ p) := by
  have hpmem : p ∈ Finset.Icc p q := Finset.mem_Icc.mpr ⟨le_refl p, hpq⟩
  have hqmem : q ∈ Finset.Icc p q := Finset.mem_Icc.mpr ⟨hpq, le_refl q⟩
  set F : ℤ × ℤ × ℤ → ℤ := fun v => v.1 - g₁ p + (v.2.1 - g₂ p) + (v.2.2 - g₃ p) with hF
  have hinj : ∀ r ∈ Finset.Icc p q, ∀ r' ∈ Finset.Icc p q,
      F (g₁ r, g₂ r, g₃ r) = F (g₁ r', g₂ r', g₃ r') →
        (g₁ r, g₂ r, g₃ r) = (g₁ r', g₂ r', g₃ r') := by
    intro r hr r' hr' hFe
    simp only [hF] at hFe
    simp only [Prod.mk.injEq]
    rcases le_total r r' with hle | hle
    · have e1 := h₁ r hr r' hr' hle; have e2 := h₂ r hr r' hr' hle
      have e3 := h₃ r hr r' hr' hle
      omega
    · have e1 := h₁ r' hr' r hr hle; have e2 := h₂ r' hr' r hr hle
      have e3 := h₃ r' hr' r hr hle
      omega
  have hle1 := card_image_factor (Finset.Icc p q) (fun r => (g₁ r, g₂ r, g₃ r)) F hinj
  set D : ℤ := g₁ q - g₁ p + (g₂ q - g₂ p) + (g₃ q - g₃ p) with hD
  have hsub : ((Finset.Icc p q).image fun r => F (g₁ r, g₂ r, g₃ r)) ⊆
      Finset.Icc 0 D := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨r, hr, rfl⟩ := hv
    have hrm := Finset.mem_Icc.mp hr
    have l1 := h₁ p hpmem r hr hrm.1; have u1 := h₁ r hr q hqmem hrm.2
    have l2 := h₂ p hpmem r hr hrm.1; have u2 := h₂ r hr q hqmem hrm.2
    have l3 := h₃ p hpmem r hr hrm.1; have u3 := h₃ r hr q hqmem hrm.2
    simp only [hF, hD, Finset.mem_Icc]
    omega
  have hD0 : 0 ≤ D := by
    have l1 := h₁ p hpmem q hqmem hpq; have l2 := h₂ p hpmem q hqmem hpq
    have l3 := h₃ p hpmem q hqmem hpq
    omega
  have h3 : ((Finset.Icc (0:ℤ) D).card : ℤ) = 1 + D := by
    rw [Int.card_Icc, show D + 1 - 0 = 1 + D by ring,
      Int.toNat_of_nonneg (by omega)]
  calc (((Finset.Icc p q).image fun r => (g₁ r, g₂ r, g₃ r)).card : ℤ)
      ≤ (((Finset.Icc p q).image fun r => F (g₁ r, g₂ r, g₃ r)).card : ℤ) := by
        exact_mod_cast hle1
    _ ≤ ((Finset.Icc (0:ℤ) D).card : ℤ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = 1 + D := h3
    _ = 1 + (g₁ q - g₁ p) + (g₂ q - g₂ p) + (g₃ q - g₃ p) := by rw [hD]; ring

end Squarefree.FiniteDiff
