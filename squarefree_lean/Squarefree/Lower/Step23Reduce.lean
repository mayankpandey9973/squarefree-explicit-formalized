import Squarefree.Lower.Step23Phase
import Squarefree.Lower.DefectExpand
import Squarefree.Lower.QNearInt

/-!
# §5 Steps 2/3 shared per-`r` reduction (writeup 877–903)

`phif_dist_le` is the v≠0 analogue of `phi_norm_le_v0`: for the integer `M = ℓ₁v`
(so `ℓ₁v ∈ ℤ`), the smooth phase `φ_f = (dt⁴/6Xa)(f+φ)` is near-integer up to a clean
four-term remainder. The algebraic core is the EXACT identity
`φ_f − M = (dt⁴/6Xa)(f−𝒬) + M((dt/d)⁴−1) + (dt⁴/6Xa)(φ−φ_d) + (dt⁴/6Xa)(𝒬−lead)`
(`𝒬` and `φ_d` cancel — they are add/subtract intermediaries), where
`lead = 6ℓ₁Xav/d⁴ − φ_d`. The four remainder pieces are bounded downstream by, in order,
`Q_distInt_le` (near-int, with `f = round 𝒬`), the `d→dt` `v`-replacement, `phi_d_replace`,
and `Q_gen_expand`.
-/

open Squarefree.Counting

namespace Squarefree

/-- **§5 Steps 2/3 per-`r` reduction (algebraic core).** -/
theorem phif_dist_le {P : Globals} {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ b₀ v 𝒬 f : ℝ} {d : ℝ} {M : ℤ}
    (ha : 0 < (a : ℝ)) (hd : 0 < d) (hℓ1 : 0 < ℓ₁)
    (hM : ℓ₁ * v = (M : ℝ))
    (_h𝒬 : 𝒬 = ℓ₁ * Fab P.X (a : ℝ) (ℓ₂ * b₀ + v) d - ℓ₂ * Fab P.X (a : ℝ) (ℓ₁ * b₀) d) :
    distInt (phif P.X (a : ℝ) ℓ₁ ℓ₂ f r)
      ≤ (dtilde P.X r (a : ℝ)) ^ 4 / (6 * P.X * (a : ℝ))
          * ( |f - 𝒬|
              + |𝒬 - (6 * ℓ₁ * P.X * (a : ℝ) * v / d ^ 4
                      - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * b₀ ^ 2 / d ^ 5)|
              + |phi P.X (a : ℝ) ℓ₁ ℓ₂ r
                  - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * b₀ ^ 2 / d ^ 5| )
        + ℓ₁ * |v| * |(dtilde P.X r (a : ℝ) / d) ^ 4 - 1| := by
  -- ne-zero / positivity facts
  have hX0 : P.X ≠ 0 := ne_of_gt P.X_pos
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hd0 : d ≠ 0 := ne_of_gt hd
  -- abbreviations: make `dt` and `φ` opaque
  set dt := dtilde P.X r (a : ℝ) with hdt_def
  set φ := phi P.X (a : ℝ) ℓ₁ ℓ₂ r with hφ_def
  -- prefactor and the two "lead/φ_d" terms (φ_d is the b₀² term)
  set pref := dt ^ 4 / (6 * P.X * (a : ℝ)) with hpref_def
  set φ_d := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * b₀ ^ 2 / d ^ 5 with hφd_def
  set lead := 6 * ℓ₁ * P.X * (a : ℝ) * v / d ^ 4 - φ_d with hlead_def
  -- `pref ≥ 0`
  have h6Xa : (0:ℝ) < 6 * P.X * (a : ℝ) := by
    have := P.X_pos; positivity
  have hpref_nn : 0 ≤ pref := by
    rw [hpref_def]
    exact div_nonneg (by positivity) h6Xa.le
  -- `(M : ℝ) = ℓ₁ * v`
  have hMv : (M : ℝ) = ℓ₁ * v := hM.symm
  -- ============ Step 2: the EXACT identity ============
  have hident : phif P.X (a : ℝ) ℓ₁ ℓ₂ f r - (M : ℝ)
      = pref * (f - 𝒬) + (M : ℝ) * ((dt / d) ^ 4 - 1)
        + pref * (φ - φ_d) + pref * (𝒬 - lead) := by
    rw [hMv, hlead_def, hφd_def, hpref_def, phif]
    field_simp
    ring
  -- ============ Step 1: distInt ≤ |·| ============
  refine le_trans (distInt_le_intDist (phif P.X (a : ℝ) ℓ₁ ℓ₂ f r) M) ?_
  rw [hident]
  -- ============ Step 3: triangle inequality ============
  -- absolute value of the four-term sum ≤ sum of absolute values
  have htri : |pref * (f - 𝒬) + (M : ℝ) * ((dt / d) ^ 4 - 1)
                + pref * (φ - φ_d) + pref * (𝒬 - lead)|
      ≤ |pref * (f - 𝒬)| + |(M : ℝ) * ((dt / d) ^ 4 - 1)|
        + |pref * (φ - φ_d)| + |pref * (𝒬 - lead)| := by
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    exact abs_add_le _ _
  refine le_trans htri ?_
  -- per-term simplifications
  have e1 : |pref * (f - 𝒬)| = pref * |f - 𝒬| := by
    rw [abs_mul, abs_of_nonneg hpref_nn]
  have e3 : |pref * (φ - φ_d)| = pref * |φ - φ_d| := by
    rw [abs_mul, abs_of_nonneg hpref_nn]
  have e4 : |pref * (𝒬 - lead)| = pref * |𝒬 - lead| := by
    rw [abs_mul, abs_of_nonneg hpref_nn]
  have eM : |(M : ℝ) * ((dt / d) ^ 4 - 1)| = ℓ₁ * |v| * |(dt / d) ^ 4 - 1| := by
    rw [abs_mul, hMv, abs_mul, abs_of_pos hℓ1]
  rw [e1, e3, e4, eM]
  -- reassemble: group the three `pref*|·|` terms, matching goal order
  -- goal RHS inner sum order: |f-𝒬| + |𝒬-lead| + |φ-φ_d|
  rw [hlead_def]
  ring_nf
  rfl

end Squarefree
