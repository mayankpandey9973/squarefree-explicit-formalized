import Squarefree.Lower.Step4Compose
import Squarefree.Lower.Step4PackPoint
import Squarefree.Lower.Step4PackPair
import Squarefree.Lower.Step4PackPerv
import Squarefree.Lower.Step4FibreCard

/-!
# §5 Step-4 per-fibre count (C2a per sign branch)

Assembles the green packers (`step4_pack_lat`/`step4_pack_sqlo`/`step4_pack_pair`/
`step4_pack_perv`) through `step4_fibre_branch_le` on each sign branch of
`fibre_card_sign_split`, yielding the per-fibre count `2·10²⁰⁰·weight5`.
-/

open Real Finset Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- `a ≤ d` from the `a`-window and `d ≥ D = HΔ` (mirror of the inline step in
`pert_le_sixteenth`). -/
private theorem a_le_d' {a d : ℝ} (ha_hi : a ≤ 11 * S.A)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) : a ≤ d := by
  have hHpos := P.H_pos; have hUpos := P.U_pos
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hΩ3U3 : S.Ω ^ 3 ≤ P.U ^ 3 := pow_le_pow_left₀ hΩpos.le hΩU 3
  have hHU2 : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * P.U ^ 3 :=
    hReg.trans (mul_le_mul_of_nonneg_left hΩ3U3 hHpos.le)
  have hH : S.Δ ^ 2 * P.U ^ 2 ≤ P.H := by nlinarith [hHU2, pow_pos hUpos 3]
  have h22 : 22 * S.Ω ≤ P.H := by
    nlinarith [hH, mul_le_mul_of_nonneg_right (one_le_pow₀ hΔ1 : (1:ℝ) ≤ S.Δ ^ 2)
      (sq_nonneg P.U), mul_le_mul_of_nonneg_right hUbig hUpos.le, hΩU, hΩpos]
  have haA : a ≤ 11 * (S.Δ * S.Ω) := by unfold Scale.A at ha_hi; exact ha_hi
  have hDd : P.H * S.Δ * (1 - 1/10 ^ 9) ≤ d := hdD
  nlinarith [haA, hDd, mul_le_mul_of_nonneg_left h22 hΔpos.le,
    mul_pos hΩpos hΔpos]

/-- Squared pin, lower side: `n/2 ≤ Ĉ·v²` with `Ĉ·a² = 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)` and `a ≥ A/5`
gives `(1/150)·Δ²Ω²·n ≤ ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v²`. -/
private theorem pin_lo_of_sqlo {a v ℓ₁ ℓ₂ nr : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (hnr : 0 ≤ nr)
    (h : nr / 2 ≤ (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2) :
    (1/150 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * nr) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 := by
  have hΔpos := S.Δ_pos; have hΩpos := S.Ω_pos
  have hane : a ≠ 0 := ha0.ne'
  have hCa2 : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * a ^ 2
      = 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) := by
    rw [show Cref P S ℓ₁ ℓ₂ = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (S.Δ ^ 2 * S.Ω ^ 2) from rfl,
      show S.A = S.Δ * S.Ω from rfl]
    field_simp
  have hkey : (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2 * a ^ 2
      = 3 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) := by
    linear_combination v ^ 2 * hCa2
  have ha_lo' : S.Δ * S.Ω / 5 ≤ a := by
    rw [show S.A = S.Δ * S.Ω from rfl] at ha_lo; exact ha_lo
  have ha2 : S.Δ ^ 2 * S.Ω ^ 2 / 25 ≤ a ^ 2 := by
    nlinarith [mul_le_mul ha_lo' ha_lo' (by positivity) ha0.le]
  have hA1 : nr / 2 * a ^ 2
      ≤ (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2 * ℓ₁ ^ 2) * v ^ 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_right h (sq_nonneg a)
  have hA2 : nr / 2 * (S.Δ ^ 2 * S.Ω ^ 2 / 25) ≤ nr / 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_left ha2 (by linarith)
  nlinarith [hA1, hA2, hkey]

/-- Squared pin, upper side: `|v| ≤ Vbox S ℓ₁ ℓ₂ n` squares to
`ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v² ≤ 10⁶·Δ²Ω²·n` (`Vbox_sq`). -/
private theorem pin_hi_of_vbox {v ℓ₁ ℓ₂ nr : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hnr : 0 ≤ nr)
    (h : |v| ≤ Vbox S ℓ₁ ℓ₂ nr) :
    ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2 ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * nr) := by
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hL3 : (0:ℝ) < ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) :=
    mul_pos (mul_pos (pow_pos hℓ1p 3) (hℓ1p.trans hℓ12)) (sub_pos.mpr hℓ12)
  have hvsq : v ^ 2 ≤ (Vbox S ℓ₁ ℓ₂ nr) ^ 2 := by
    rw [← sq_abs v]
    exact pow_le_pow_left₀ (abs_nonneg v) h 2
  rw [Vbox_sq hnr hℓ1 hℓ12, le_div_iff₀ hL3] at hvsq
  nlinarith [hvsq]

/-- **§5 Step-4 per-fibre count (C2a, both sign branches).**  A fibre `Fib` of indices `r`
whose defects `vval P a dStar ℓ₁ ℓ₂ r` carry the §5 window data and a uniform near-integer
pin `|Σ_closed(r) − n| ≤ err` numbers at most `2·10²⁰⁰·weight5(…)·` at band index `n`. -/
theorem step4_fibre_count_le
    (a : ℤ) (dStar : ℕ → ℤ) {ℓ₁ ℓ₂ : ℕ} {gap err r₀ r₁ δ : ℝ} {n : ℕ}
    (b₀Of dOf : ℕ → ℝ)
    (ha0 : 0 < (a:ℝ)) (ha_lo : S.A / 5 ≤ (a:ℝ)) (ha_hi : (a:ℝ) ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hℓ2W : (ℓ₂:ℝ) ≤ 130 * P.Wval) (hℓ2GU : (ℓ₂:ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hδhalf : δ ≤ 1 / 2)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hAD : 10 * S.A ≤ S.D)
    (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2 * 10 ^ 12 * S.Δ / (P.G * S.Ω ^ 3 * (ℓ₁:ℝ))
        + 10 ^ 13 * (ℓ₁:ℝ) * S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6))
    (herr0 : 0 ≤ err) (herr_small : err ≤ (1/4) * (n:ℝ))
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + (ℓ₁:ℝ) ≤ 16 * S.R)
    (hδ : δ = 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5))
    (hn : 1 ≤ n)
    (hnN : (n:ℝ) ≤ 10 ^ 57 * (ℓ₁:ℝ) ^ 2 * ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ)))
        * P.U ^ 10 / S.Ω ^ 8)
    (Fib : Finset ℕ)
    (hb0box : ∀ r ∈ Fib, |b₀Of r| ≤ 3000000000000 * S.B)
    (hb0lo : ∀ r ∈ Fib, S.B / 2000000 ≤ |b₀Of r|)
    (hvmax : ∀ r ∈ Fib, |vval P a dStar ℓ₁ ℓ₂ r| ≤ Vmax P S)
    (hVcut : ∀ r ∈ Fib, V₂ P S ≤ |vval P a dStar ℓ₁ ℓ₂ r|)
    (hdD : ∀ r ∈ Fib, S.D * (1 - 1/10 ^ 9) ≤ dOf r)
    (_hd2D : ∀ r ∈ Fib, dOf r ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hb0gap : ∀ r ∈ Fib, |b₀Of r - b1Model P.X (a:ℝ) (dOf r)| ≤ gap)
    (hni : ∀ r ∈ Fib,
      |Sigma_closed P.X (a:ℝ) (b₀Of r) (vval P a dStar ℓ₁ ℓ₂ r) (dOf r) (ℓ₁:ℝ) (ℓ₂:ℝ)
        - ((n:ℤ):ℝ)| ≤ err)
    (hmem : ∀ r ∈ Fib, r₀ ≤ (r:ℝ) ∧ (r:ℝ) ≤ r₁ ∧
      distInt (phiv P.X (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) (vval P a dStar ℓ₁ ℓ₂ r) (r:ℝ)) ≤ δ) :
    (Fib.card : ℝ)
      ≤ 2 * 10 ^ 200 * weight5 (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          (8 * (a:ℝ) * err / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
          (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
          (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
          (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n:ℝ) := by
  have hℓ1R : (1:ℝ) ≤ (ℓ₁:ℝ) := by exact_mod_cast hℓ1
  have hℓ12R' : (ℓ₁:ℝ) + 1 ≤ (ℓ₂:ℝ) := by exact_mod_cast hℓ12
  have hℓ12R : (ℓ₁:ℝ) < (ℓ₂:ℝ) := by linarith
  have hcast2 : |((n:ℤ):ℝ)| = (n:ℝ) := by
    rw [Int.cast_natCast]; exact abs_of_nonneg (Nat.cast_nonneg n)
  have hsqlo : ∀ r ∈ Fib,
      (n:ℝ) / 2 ≤ (Cref P S (ℓ₁:ℝ) (ℓ₂:ℝ) * (S.A / (a:ℝ)) ^ 2 * (ℓ₁:ℝ) ^ 2)
          * (vval P a dStar ℓ₁ ℓ₂ r) ^ 2
        ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ Vbox S (ℓ₁:ℝ) (ℓ₂:ℝ) (n:ℝ) := by
    intro r hr
    have hvm : |vval P a dStar ℓ₁ ℓ₂ r| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) :=
      hvmax r hr
    have h := step4_pack_sqlo (P := P) (S := S) ha0 ha_lo ha_hi hℓ1R hℓ12R hℓ12R' hℓ2W
      (hb0box r hr) (hb0lo r hr) hvm (hVcut r hr) (hdD r hr)
      hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW hgap0 hgap (hb0gap r hr) rfl (hni r hr)
      (by rw [hcast2]; exact herr_small)
    refine ⟨?_, ?_⟩
    · have h1' := h.1
      rwa [hcast2] at h1'
    · have h2' := h.2
      rwa [hcast2] at h2'
  have hbranch : ∀ B : Finset ℕ, B ⊆ Fib →
      (∀ r ∈ B, ∀ r' ∈ B, 0 ≤ vval P a dStar ℓ₁ ℓ₂ r * vval P a dStar ℓ₁ ℓ₂ r') →
      (B.card : ℝ) ≤ 10 ^ 200 * weight5 (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2))
          (8 * (a:ℝ) * err / Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
          (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt ((ℓ₁:ℝ) * (ℓ₂:ℝ) * ((ℓ₂:ℝ) - (ℓ₁:ℝ))))
          (cEhyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ) gap) (cE2hyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ))
          (cChyb P S (a:ℝ) (ℓ₁:ℝ) (ℓ₂:ℝ)) (n:ℝ) := by
    intro B hBsub hBsign
    have hG0 := P.G_pos; have hU0 := P.U_pos; have hH0 := P.H_pos
    have hΔ0 := S.Δ_pos; have hΩ0 := S.Ω_pos
    refine step4_fibre_branch_le ha0 hℓ1R hℓ12R' hgap0 herr0 hn (by norm_num)
      (by positivity) (by positivity) B (vval P a dStar ℓ₁ ℓ₂)
      (fun r _ => step4_pack_lat a dStar ℓ₂ hℓ1 r)
      (fun r hr => (hsqlo r (hBsub hr)).1)
      (fun r hr r' hr' => step4_pack_pair ha0 ha_hi
        (a_le_d' ha_hi (hdD r (hBsub hr)) hReg hΔ1 hΩU hUbig)
        (a_le_d' ha_hi (hdD r' (hBsub hr')) hReg hΔ1 hΩU hUbig)
        hℓ1R hℓ12R hℓ12R'
        (hsqlo r (hBsub hr)).2 (hsqlo r' (hBsub hr')).2
        (hvmax r (hBsub hr)) (hvmax r' (hBsub hr'))
        (hBsign r hr r' hr')
        (hdD r (hBsub hr)) (hdD r' (hBsub hr'))
        h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
        (hb0gap r (hBsub hr)) (hb0gap r' (hBsub hr')) hgap0
        (hb0box r (hBsub hr)) (hb0box r' (hBsub hr'))
        (hni r (hBsub hr)) (hni r' (hBsub hr')))
      (step4_pack_perv hG1 hU1 hUbig hΔ1 hH1 hΩU hband hδhalf h1 hReg hDeW hAD ha0 ha_lo
        ha_hi
        hℓ1R hℓ12R' hℓ2GU hr0_lo hr01 hr1_hi hδ hn hnN B (vval P a dStar ℓ₁ ℓ₂)
        (fun r hr => hmem r (hBsub hr)) (fun r hr => hVcut r (hBsub hr))
        (fun r hr => pin_lo_of_sqlo ha0 ha_lo (Nat.cast_nonneg n)
          (hsqlo r (hBsub hr)).1)
        (fun r hr => pin_hi_of_vbox hℓ1R hℓ12R (Nat.cast_nonneg n)
          (hsqlo r (hBsub hr)).2))
  rw [fibre_card_sign_split Fib (vval P a dStar ℓ₁ ℓ₂)]
  have hplus := hbranch (Fib.filter (fun r => 0 ≤ vval P a dStar ℓ₁ ℓ₂ r))
    (Finset.filter_subset _ _)
    (fun r hr r' hr' =>
      mul_nonneg (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hr').2)
  have hminus := hbranch (Fib.filter (fun r => ¬ 0 ≤ vval P a dStar ℓ₁ ℓ₂ r))
    (Finset.filter_subset _ _)
    (fun r hr r' hr' => (mul_pos_of_neg_of_neg
      (not_le.mp (Finset.mem_filter.mp hr).2)
      (not_le.mp (Finset.mem_filter.mp hr').2)).le)
  linarith

end Squarefree
