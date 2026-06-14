import Squarefree.Lower.Step4SqDiff
import Squarefree.Lower.Step4FiberErr

/-!
# §5 Step-4 fibre window bundle (writeup 1025–1091)

GREEN here:
* `step4_fibre_window_data` — the ~40-hyp window bundle is discharged uniformly over the
  fibre, producing a single signed extraction `sgn : ℕ → ℤ` with `(sgn r).natAbs ∈ Icc 1 N`
  (the `hsmaps`/`sOf` data the fibre-sum route consumes), plus the per-`r` `round = sgn r`
  identity and the SMALL near-integer budget.

(The historical `diam`-budget → fibre-`hconf` recenter seam that used to live here was pruned
with the superseded crude Step-4 route; the live confinement now flows through the
additive/SquareDiff capstone in `Step4Capstone`.)
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **§5 Step-4 fibre window bundle → `sOf`/`hsmaps` (item 1 of the capstone, writeup 1025–1091).**
Given the §5 regime and, per `r` in the large-defect range filter `Rng`, the full Step-4 per-`r`
window/sign/placement bundle (the 25 facts `step4_fiber_extract_err` consumes), this produces a
*single* signed `s`-extraction `sgn : ℕ → ℤ` such that, for every `r ∈ Rng`, the natural-abs index
`(sgn r).natAbs` lands in `Icc 1 N` (the `hsmaps` predicate of the fibre-sum route, with
`sOf r := (sgn r).natAbs`), together with the per-`r` round-identity `round(Σ_closed(d̃ₐ)) = sgn r`,
its magnitude bounds, and the SMALL near-integer budget.

This discharges the ~40-hyp window bundle uniformly over the fibre. -/
theorem step4_fibre_window_data {a : ℤ} {ℓ₁ ℓ₂ : ℕ} {dStar : ℕ → ℤ} {V₂ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 60 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14)
    (Ra : Finset ℕ) (N : ℕ)
    (hNlo : 10 ^ 56 * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
        * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))) * P.U ^ 10 / S.Ω ^ 8 ≤ (N : ℝ))
    (hV2ge : 10 ^ 60 * Squarefree.V₂ P S ≤ V₂)
    (hfibre : ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂ < |vval P a dStar ℓ₁ ℓ₂ r|),
        ((1/72) * S.R ≤ (r : ℝ)) ∧ ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
        ∧ ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
        ∧ inDa P.X P.H a (dStar r) ∧ inDa P.X P.H a (dStar (r + ℓ₁))
        ∧ inDa P.X P.H a (dStar (r + ℓ₂))
        ∧ (S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D)
        ∧ (S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D)
        ∧ (S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D)
        ∧ (|Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
        ∧ (|Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))| ≤ 14 * P.H / S.D)
        ∧ (|Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))| ≤ 14 * P.H / S.D)
        ∧ ((dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ)) ∧ ((dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
        ∧ ((dStar (r + ℓ₂) : ℝ) ≠ (dStar (r + ℓ₁) : ℝ))
        ∧ (dStar (r + ℓ₁) - dStar r ≤ (0:ℤ)) ∧ (dStar (r + ℓ₂) - dStar r ≤ (0:ℤ))
        ∧ (dStar (r + ℓ₂) - dStar (r + ℓ₁) ≤ (0:ℤ))
        ∧ (a + (dStar r - dStar (r + ℓ₁)) ≤ dStar (r + ℓ₁))
        ∧ (a + (dStar r - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
        ∧ (a + (dStar (r + ℓ₁) - dStar (r + ℓ₂)) ≤ dStar (r + ℓ₂))
        ∧ (S.D * (1 - 1/10 ^ 9) ≤ dtilde P.X (r : ℝ) (a : ℝ)
            ∧ dtilde P.X (r : ℝ) (a : ℝ) ≤ 2 * S.D * (1 + 1/10 ^ 9))
        ∧ (S.B / 2000000 ≤ |((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)|)
        ∧ (10 * (((ℓ₂ : ℤ) : ℝ) * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))
              * (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ)) ^ 2
              / dtilde P.X (r : ℝ) (a : ℝ))
            ≤ |vval P a dStar ℓ₁ ℓ₂ r|)) :
    ∃ sgn : ℕ → ℤ, ∀ r ∈ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ V₂ < |vval P a dStar ℓ₁ ℓ₂ r|),
        (sgn r).natAbs ∈ Finset.Icc 1 N
        ∧ round (Sigma_closed P.X (a : ℝ)
              (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
              (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂) = sgn r
        ∧ |Sigma_closed P.X (a : ℝ)
              (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
              (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂ - (sgn r : ℝ)|
            ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S
              + 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
                * |dtilde P.X (r : ℝ) (a : ℝ) - (dStar r : ℝ)| := by
  classical
  set Rng : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ V₂ < |vval P a dStar ℓ₁ ℓ₂ r|) with hRng
  -- the per-`r` existence of the signed extraction (default `1` off the fibre)
  have hex : ∀ r : ℕ, ∃ s : ℤ, r ∈ Rng →
      ((1 : ℝ) ≤ |(s : ℝ)| ∧ s ≠ 0
        ∧ |(s : ℝ)| ≤ 10 ^ 56 * (((ℓ₁ : ℤ) : ℝ) ^ 3 * ((ℓ₂ : ℤ) : ℝ)
            * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))) * P.U ^ 10 / S.Ω ^ 8
        ∧ round (Sigma_closed P.X (a : ℝ)
              (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
              (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂) = s
        ∧ |Sigma_closed P.X (a : ℝ)
              (((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ)) / ((ℓ₁ : ℤ) : ℝ))
              (vval P a dStar ℓ₁ ℓ₂ r) (dtilde P.X (r : ℝ) (a : ℝ)) ℓ₁ ℓ₂ - (s : ℝ)|
            ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ + 10 ^ 119 * UpsT P S
              + 7 * (10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) / S.D
                * |dtilde P.X (r : ℝ) (a : ℝ) - (dStar r : ℝ)|) := by
    intro r
    by_cases hr : r ∈ Rng
    · obtain ⟨hr_lo, hr1_hi, hr2_hi, hinDa, hinDa1, hinDa2, hdwin, hd1win, hd2win,
        hRd, hRd1, hRd2, hd1ned, hd2ned, hd21ned, hb1sgn, hb2sgn, hb3sgn,
        hplace1, hplace2, hplace3, hdtwin, hb0lo, hvlo⟩ := hfibre r hr
      have hVbig : 10 ^ 60 * Squarefree.V₂ P S ≤ |vval P a dStar ℓ₁ ℓ₂ r| := by
        have hmem : V₂ < |vval P a dStar ℓ₁ ℓ₂ r| := by
          rw [hRng] at hr
          exact (Finset.mem_filter.mp hr).2.2.2
        exact le_trans hV2ge hmem.le
      obtain ⟨s, hs0, hs1, hscap, hround, herr⟩ := step4_fiber_extract_err
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W hr_lo hr1_hi hr2_hi
        hinDa hinDa1 hinDa2 hdwin hd1win hd2win hRd hRd1 hRd2
        hd1ned hd2ned hd21ned hb1sgn hb2sgn hb3sgn hplace1 hplace2 hplace3
        hdtwin hb0lo hvlo hVbig hReg h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΩH hDeW hHbig
      exact ⟨s, fun _ => ⟨hs1, hs0, hscap, hround, herr⟩⟩
    · exact ⟨1, fun h => absurd h hr⟩
  choose sgn hsgn using hex
  refine ⟨sgn, ?_⟩
  intro r hr
  obtain ⟨hs1, hs0, hscap, hround, herr⟩ := hsgn r hr
  refine ⟨?_, hround, herr⟩
  rw [Finset.mem_Icc]
  refine ⟨Nat.one_le_iff_ne_zero.mpr (fun h => hs0 (Int.natAbs_eq_zero.mp h)), ?_⟩
  -- `(sgn r).natAbs ≤ N` from `|sgn r| ≤ cap ≤ N`
  have hcastle : ((sgn r).natAbs : ℝ) ≤ (N : ℝ) := by
    have hcast : ((sgn r).natAbs : ℝ) = |(sgn r : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hcast]
    exact le_trans hscap hNlo
  exact_mod_cast hcastle

end Squarefree
