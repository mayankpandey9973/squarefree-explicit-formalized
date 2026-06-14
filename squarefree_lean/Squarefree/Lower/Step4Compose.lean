import Squarefree.Lower.Step4Band5
import Squarefree.Lower.Step4FibreCard

/-!
# §5 Step-4 per-fibre branch composition

`fibre_v_card_le` × `band_collapse5` × `vsum_le_weight5`: the per-fibre, per-sign-branch
five-slot count, with all analytic input as hypotheses.
-/

open Real Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- `cE2hyb ≥ 0` (all factors nonnegative; `2ℓ₂ − ℓ₁ ≥ 0` from `1 ≤ ℓ₁ ≤ ℓ₂ − 1`). -/
private theorem cE2hyb_nonneg' {a ℓ₁ ℓ₂ : ℝ} (ha0 : 0 < a) (hℓ1 : 1 ≤ ℓ₁)
    (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) : 0 ≤ cE2hyb P S a ℓ₁ ℓ₂ := by
  have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have h2l : (0:ℝ) ≤ 2*ℓ₂ - ℓ₁ := by linarith
  unfold cE2hyb
  exact div_nonneg (mul_nonneg (by positivity) h2l)
    (mul_nonneg hΔ.le (sq_nonneg _))

/-- `cChyb ≥ 0` (`B = Δ²/(GΩ³) ≥ 0`, `D = HΔ > 0`). -/
private theorem cChyb_nonneg' {a ℓ₁ ℓ₂ : ℝ} (ha0 : 0 < a) (hℓ1 : 1 ≤ ℓ₁)
    (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) : 0 ≤ cChyb P S a ℓ₁ ℓ₂ := by
  have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hH := P.H_pos
  have hL0 : (0:ℝ) ≤ ℓ₁*ℓ₂*(ℓ₂-ℓ₁) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hB : (0:ℝ) ≤ S.B := by
    rw [show S.B = S.Δ^2/(P.G*S.Ω^3) from rfl]; positivity
  have hD : (0:ℝ) < S.D := by
    rw [show S.D = P.H*S.Δ from rfl]; positivity
  have hE0 : (0:ℝ) ≤ Ecap4p3 P S ℓ₁ ℓ₂ := Ecap4p3_nonneg hℓ1 hℓ12
  unfold cChyb
  have hM0 : (0:ℝ) ≤ 10^44 * a * P.G * S.Ω^2 * (ℓ₁*ℓ₂*(ℓ₂-ℓ₁)) * S.B^3 / (S.Δ^3 * S.D) :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) hL0) (pow_nonneg hB 3))
      (by positivity)
  have hQ0 : (0:ℝ) ≤ 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁)) :=
    div_nonneg (by positivity) (Real.sqrt_nonneg _)
  linarith

/-- Kernel pin: `nr/2 ≤ Ĉ·v²` gives `√(nr/(2Ĉ)) ≤ |v|`. -/
private theorem sqrt_pin {Ĉ nr v : ℝ} (hĈ0 : 0 < Ĉ) (h : nr/2 ≤ Ĉ * v^2) :
    Real.sqrt (nr/(2*Ĉ)) ≤ |v| := by
  have h2 : nr/(2*Ĉ) ≤ v^2 := vlo_pin_of_sq hĈ0 (by linarith)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h2

/-- **§5 Step-4 per-fibre, per-sign-branch count.**  Lattice defects pinned below by the
`n/(2Ĉ)` square bound with pairwise square-diff budget `diam` and per-value count
`K_C·(b + dc/√n)` give the five-slot bound `K_C·weight5`. -/
theorem step4_fibre_branch_le {a ℓ₁ ℓ₂ gap err K_C b dc : ℝ} {n : ℕ}
    (ha0 : 0 < a) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hgap : 0 ≤ gap) (herr : 0 ≤ err) (hn : 1 ≤ n)
    (hKC : 0 ≤ K_C) (hb : 0 ≤ b) (hdc : 0 ≤ dc)
    (Fib : Finset ℕ) (vOf : ℕ → ℝ)
    (hlat : ∀ r ∈ Fib, ∃ k : ℤ, vOf r = (k : ℝ) / ℓ₁)
    (hsq_lo : ∀ r ∈ Fib,
      (n : ℝ) / 2 ≤ (Cref P S ℓ₁ ℓ₂ * (S.A/a)^2 * ℓ₁^2) * (vOf r)^2)
    (hpair : ∀ r ∈ Fib, ∀ r' ∈ Fib,
      |vOf r ^ 2 - vOf r' ^ 2|
        ≤ (4*err + 2*(Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ (n:ℝ))
            + 2*Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ (n:ℝ))))
          / (Cref P S ℓ₁ ℓ₂ * (S.A/a)^2 * ℓ₁^2))
    (hperv : ∀ w : ℝ, ((Fib.filter (fun r => vOf r = w)).card : ℝ)
        ≤ K_C * (b + dc / Real.sqrt (n:ℝ))) :
    (Fib.card : ℝ)
      ≤ K_C * weight5 b (8*a*err / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))) dc
          (cEhyb P S a ℓ₁ ℓ₂ gap) (cE2hyb P S a ℓ₁ ℓ₂) (cChyb P S a ℓ₁ ℓ₂) (n:ℝ) := by
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hlt : ℓ₁ < ℓ₂ := by linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hA0 : (0:ℝ) < S.A := by
    rw [show S.A = S.Δ*S.Ω from rfl]; exact mul_pos S.Δ_pos S.Ω_pos
  set Ĉ := Cref P S ℓ₁ ℓ₂ * (S.A/a)^2 * ℓ₁^2 with hĈdef
  have hĈ0 : 0 < Ĉ := mul_pos (mul_pos (Cref_pos hℓ1p hlt)
    (pow_pos (div_pos hA0 ha0) 2)) (pow_pos hℓ1p 2)
  set Vlo := Real.sqrt ((n:ℝ)/(2*Ĉ)) with hVlodef
  have hVlo0 : 0 < Vlo := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have hVsq : (n:ℝ)/(2*Ĉ) ≤ Vlo^2 := by
    rw [hVlodef]; exact (Real.sq_sqrt (by positivity)).ge
  have hpin : ∀ r ∈ Fib, Vlo ≤ |vOf r| := fun r hr => by
    rw [hVlodef]; exact sqrt_pin hĈ0 (hsq_lo r hr)
  set T := 4*err + 2*(Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ (n:ℝ))
    + 2*Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ (n:ℝ))) with hTdef
  have hT0 : 0 ≤ T := by
    have h1 : 0 ≤ Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ (n:ℝ)) :=
      Step4EcubV_nonneg hℓ1 hlt Vbox_nonneg
    have h2 : 0 ≤ Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ (n:ℝ)) :=
      Step4EremHyb_nonneg hℓ1 hlt hgap Vbox_nonneg
    rw [hTdef]; linarith
  have hCv0 : 0 ≤ K_C * (b + dc / Real.sqrt (n:ℝ)) :=
    mul_nonneg hKC (add_nonneg hb (div_nonneg hdc (Real.sqrt_nonneg _)))
  have h4 := fibre_v_card_le hℓ1p hVlo0 (div_nonneg hT0 hĈ0.le) hCv0 Fib vOf
    hlat hpin hpair hperv
  have h5 := band_collapse5 ha0 hℓ1 hℓ12 hgap herr hn1 hĈdef hVlo0 hVsq
  rw [← hTdef] at h5
  have hq0 : 0 ≤ 2*ℓ₁*(T/Ĉ)/Vlo :=
    div_nonneg (mul_nonneg (by positivity) (div_nonneg hT0 hĈ0.le)) hVlo0.le
  exact h4.trans (vsum_le_weight5 hKC hb hdc (by linarith)
    (cE2hyb_nonneg' ha0 hℓ1 hℓ12) (cChyb_nonneg' ha0 hℓ1 hℓ12) (Nat.cast_nonneg n)
    (by linarith [h5]) (le_refl _))

end Squarefree
