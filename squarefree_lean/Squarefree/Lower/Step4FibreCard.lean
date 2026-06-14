import Squarefree.Lower.Step4SqDiff

/-!
# §5 Step-4 fibre cardinality (writeup 1058)

Pure Finset/ℝ composition layer over the `sqdiff_band_card_le` kernel: the v-count ×
per-v-count fibre bound, the sign split, and the `Vlo` pin one-liner.
-/

open Real Finset

namespace Squarefree

/-- **§5 Step-4 fibre count = v-count × per-v count.**  An index range `Rng` whose defects
`vOf r` are `ℓ₁⁻¹ℤ`-lattice points pinned `Vlo ≤ |vOf r|` with pairwise square-difference
budget `diam`, and with `≤ Cv` indices per defect value, has
`#Rng ≤ (2 + 2·ℓ₁·diam/Vlo)·Cv` (kernel `sqdiff_band_card_le` on the value set). -/
theorem fibre_v_card_le {ℓ₁ Vlo diam Cv : ℝ}
    (hℓ1 : 0 < ℓ₁) (hVlo : 0 < Vlo) (hdiam : 0 ≤ diam) (hCv : 0 ≤ Cv)
    (Rng : Finset ℕ) (vOf : ℕ → ℝ)
    (hlat : ∀ r ∈ Rng, ∃ k : ℤ, vOf r = (k : ℝ) / ℓ₁)
    (hpin : ∀ r ∈ Rng, Vlo ≤ |vOf r|)
    (hpair : ∀ r ∈ Rng, ∀ r' ∈ Rng, |vOf r ^ 2 - vOf r' ^ 2| ≤ diam)
    (hperv : ∀ w : ℝ, ((Rng.filter (fun r => vOf r = w)).card : ℝ) ≤ Cv) :
    (Rng.card : ℝ) ≤ (2 + 2 * ℓ₁ * diam / Vlo) * Cv := by
  classical
  set F : Finset ℝ := Rng.image vOf with hF
  have hFcard : (F.card : ℝ) ≤ 2 + 2 * ℓ₁ * diam / Vlo := by
    apply sqdiff_band_card_le hℓ1 hVlo hdiam F
    · intro v hv
      rw [hF, Finset.mem_image] at hv
      obtain ⟨r, hr, rfl⟩ := hv
      exact hlat r hr
    · intro v hv
      rw [hF, Finset.mem_image] at hv
      obtain ⟨r, hr, rfl⟩ := hv
      exact hpin r hr
    · intro v hv v' hv'
      rw [hF, Finset.mem_image] at hv hv'
      obtain ⟨r, hr, rfl⟩ := hv
      obtain ⟨r', hr', rfl⟩ := hv'
      exact hpair r hr r' hr'
  have hsplit : Rng.card = ∑ w ∈ F, (Rng.filter (fun r => vOf r = w)).card := by
    rw [hF]; exact Finset.card_eq_sum_card_image vOf Rng
  have hsum : (Rng.card : ℝ) = ∑ w ∈ F, ((Rng.filter (fun r => vOf r = w)).card : ℝ) := by
    rw [hsplit]; push_cast; rfl
  rw [hsum]
  calc ∑ w ∈ F, ((Rng.filter (fun r => vOf r = w)).card : ℝ)
      ≤ ∑ _w ∈ F, Cv := Finset.sum_le_sum (fun w _ => hperv w)
    _ = (F.card : ℝ) * Cv := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 + 2 * ℓ₁ * diam / Vlo) * Cv := mul_le_mul_of_nonneg_right hFcard hCv

/-- **Sign decomposition of the fibre.**  `#Rng = #(Rng, vOf ≥ 0) + #(Rng, vOf < 0)`,
cast to `ℝ` — the `b₀<0` sign split feeding each branch into `fibre_v_card_le`. -/
theorem fibre_card_sign_split (Rng : Finset ℕ) (vOf : ℕ → ℝ) :
    (Rng.card : ℝ) = ((Rng.filter (fun r => 0 ≤ vOf r)).card : ℝ)
      + ((Rng.filter (fun r => ¬ 0 ≤ vOf r)).card : ℝ) := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Rng) (fun r => 0 ≤ vOf r)
  exact_mod_cast h.symm

/-- **`band_collapse5` pin one-liner.**  From `n ≤ 2·Ĉ·Vlo²` extract the squared lower
pin `n/(2Ĉ) ≤ Vlo²`. -/
theorem vlo_pin_of_sq {n Ĉ Vlo : ℝ} (hĈ : 0 < Ĉ)
    (h : n ≤ 2 * Ĉ * Vlo ^ 2) : n / (2 * Ĉ) ≤ Vlo ^ 2 := by
  rw [div_le_iff₀ (by positivity)]
  linarith

end Squarefree
