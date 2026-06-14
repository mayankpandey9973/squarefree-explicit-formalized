import Squarefree.Lower.Prop51Bridge
import Squarefree.Lower.Step2FsumCurv
import Squarefree.Lower.Step2FsumCurvTight

/-!
# §5 Step-2 per-pair RANGE bound (writeup 867–950)

`ra_step2_range_le` is the pure-assembly lemma that turns the Step-2 `v`-range `0 < |v(r)| ≤ V₁`
count (the `s₂` term of `fiber_le_sum_ranges`) into the two Step-2 `Bcombine` monomials `t2 + t3`.

Wiring (mirrors `ra_step3_range_le`):
1. **subset.** For `r` in the range `0 < |v(r)| ≤ V₁`, the EASY bridge `qval_round_le` (from
   `|v(r)| ≤ V₁`) gives `(round(Qval r)).natAbs ≤ N` whenever `N ≥ Mbound(ℓ₁,V₁) + 1/2`.  So the
   range filter ⊆ the `Ra_step2_fsum_curv` filter, hence card-`≤`.
2. **fsum.** `Ra_step2_fsum_curv` bounds that card by the curvature `f`-sum shape.
3. **scale.** `step2_fsum_curv_le_t2t3` collapses it to `10⁴⁰⁰·(t2 + t3)`.

The `N`-cap `N ≤ 10⁹⁸·G²U¹⁵/Ω⁵` (consumed by the collapse) is taken as a hypothesis `hNenv`; it is
jointly satisfiable with `Mbound(ℓ₁,V₁)+1/2 ≤ N` once `ℓ₁ ≤ W = G·U⁵` is collapsed (writeup 940).
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **§5 Step-2 per-pair RANGE bound.**  The `v`-range `0 < |v(r)| ≤ V₁` part of the pair fiber is
bounded by the two Step-2 `Bcombine` monomials `t2 + t3`. -/
theorem ra_step2_range_le {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hsmall : (10:ℝ) ^ 110 * ((ℓ₁ : ℤ) : ℝ) ≤ S.R)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R)
    (hwin : ∀ r ∈ Ra, (r + ℓ₁ ∈ Ra) → (r + ℓ₂ ∈ Ra) →
        (S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D) ∧
        (S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D) ∧
        |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))| ≤ 14 * P.H / S.D ∧
        |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))| ≤ 14 * P.H / S.D ∧
        (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R ∧ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R ∧
        (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
    (N : ℕ)
    (hNcap : Mbound P S ℓ₁ (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6))) + 1 / 2 ≤ (N : ℝ))
    (hNenv : (N : ℝ) ≤ 10 ^ 102 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ 0 < |vval P a dStar ℓ₁ ℓ₂ r|
          ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ 10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)))).card : ℝ)
      ≤ 10 ^ 408 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
          + (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))) := by
  classical
  have hHpos := P.H_pos; have hGpos := P.G_pos; have hUpos := P.U_pos
  have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos; have hXpos := P.X_pos
  have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
  have hApos : (0 : ℝ) < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  set V₁ : ℝ := 10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) with hV1_def
  have hV1_nn : 0 ≤ V₁ := by rw [hV1_def]; positivity
  -- ===== Step 1: the range filter ⊆ the `Ra_step2_fsum_curv` filter =====
  set F_range : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ 0 < |vval P a dStar ℓ₁ ℓ₂ r| ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₁) with hFrange
  set F_fsum : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ (round (Qval P a dStar ℓ₁ ℓ₂ r)).natAbs ≤ N) with hFfsum
  have hsub : F_range ⊆ F_fsum := by
    intro r hr
    rw [hFrange, Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1, hr2, _hvlo, hvhi⟩ := hr
    obtain ⟨_hinDa, hdwin1, hdwin2, hRd, hr_lo, _hr_hi⟩ := hdStar r hrRa
    obtain ⟨hd1win, hd2win, hRd1, hRd2, hr1_hi, hr2_hi, hd1ned, hd2ned⟩ := hwin r hrRa hr1 hr2
    rw [hFfsum, Finset.mem_filter]
    refine ⟨hrRa, hr1, hr2, ?_⟩
    exact qval_round_le (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r)
      (dStar := dStar) (V₂ := V₁) (N := N)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hr_lo hr1_hi hr2_hi
      ⟨hdwin1, hdwin2⟩ hd1win hd2win hRd hRd1 hRd2 hd1ned hd2ned hvhi hV1_nn
      h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΔreg hNcap
  have hcard : (F_range.card : ℝ) ≤ (F_fsum.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  -- ===== Step 2: bound `F_fsum.card` by the curvature `f`-sum =====
  have hfsum := Ra_step2_fsum_curv (P := P) (S := S) (a := a)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg hsmall
    Ra dStar hdStar N
  -- ===== Step 3: the collapse hypotheses =====
  -- N ≥ 1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hMnn : 0 ≤ Mbound P S ℓ₁ V₁ := by
      rw [Mbound]
      have hℓnn : (0:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by positivity
      positivity
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp only [Nat.cast_zero] at hNcap; linarith [hMnn, hNcap]
      · exact h
    exact_mod_cast hNpos
  -- `T_curv` bounds:  B²/D ≤ T_curv ≤ (G·U⁵)³·(B²/D)
  set Tc : ℝ := ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D with hTc_def
  have hℓ2R : (1 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_of_lt (lt_of_le_of_lt hℓ1R hℓ12R)
  have hℓprod_lo : (1 : ℝ) ≤ ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) := by
    have hd1 : (1:ℝ) ≤ ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by
      have hz : (ℓ₁:ℤ) < (ℓ₂:ℤ) := by exact_mod_cast hℓ12
      have hz2 : (ℓ₁:ℤ) + 1 ≤ (ℓ₂:ℤ) := by omega
      have hr2 : ((ℓ₁:ℤ):ℝ) + 1 ≤ ((ℓ₂:ℤ):ℝ) := by exact_mod_cast hz2
      linarith
    have hp1 : (1:ℝ) ≤ ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) := by nlinarith [hℓ1R, hℓ2R]
    nlinarith [hp1, hd1]
  have hℓ1W : ((ℓ₁:ℤ):ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    have := le_trans (le_of_lt hℓ12R) hℓ2W; rw [Globals.Wval] at this; exact this
  have hℓ2W' : ((ℓ₂:ℤ):ℝ) ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hℓprod_hi : ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
      ≤ 2197000 * (P.G * P.U ^ 5) ^ 3 := by
    have hdiff : (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ1R, hℓ2W']
    have hWnn : (0:ℝ) ≤ 130 * (P.G * P.U ^ 5) := by positivity
    have h1' : ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) :=
      mul_le_mul hℓ1W hℓ2W' (by positivity) hWnn
    have hdnn : (0:ℝ) ≤ (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) := by linarith [hℓ12R]
    have hprodnn : (0:ℝ) ≤ ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) := by positivity
    calc ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
        ≤ ((130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5))) * (130 * (P.G * P.U ^ 5)) :=
          mul_le_mul h1' hdiff hdnn (by positivity)
      _ = 2197000 * (P.G * P.U ^ 5) ^ 3 := by ring
  have hBDnn : 0 ≤ S.B ^ 2 / S.D := by positivity
  have hTclo : S.B ^ 2 / S.D ≤ Tc := by
    rw [hTc_def]
    rw [show ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D
        = (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))) * (S.B ^ 2 / S.D) by ring]
    calc S.B ^ 2 / S.D = 1 * (S.B ^ 2 / S.D) := by ring
      _ ≤ (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))) * (S.B ^ 2 / S.D) :=
          mul_le_mul_of_nonneg_right hℓprod_lo hBDnn
  have hTchi0 : Tc ≤ 2197000 * ((P.G * P.U ^ 5) ^ 3 * (S.B ^ 2 / S.D)) := by
    rw [hTc_def, show ((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ)) * S.B ^ 2 / S.D
        = (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))) * (S.B ^ 2 / S.D) by ring]
    calc (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))) * (S.B ^ 2 / S.D)
        ≤ (2197000 * (P.G * P.U ^ 5) ^ 3) * (S.B ^ 2 / S.D) :=
          mul_le_mul_of_nonneg_right hℓprod_hi hBDnn
      _ = 2197000 * ((P.G * P.U ^ 5) ^ 3 * (S.B ^ 2 / S.D)) := by ring
  -- weaken to the `10⁷`-slack form consumed by the (Wnat-route-ready) collapse
  have hTchi : Tc ≤ 10 ^ 7 * ((P.G * P.U ^ 5) ^ 3 * (S.B ^ 2 / S.D)) := by
    refine le_trans hTchi0 ?_
    have hnn : (0:ℝ) ≤ (P.G * P.U ^ 5) ^ 3 * (S.B ^ 2 / S.D) := by positivity
    nlinarith [hnn]
  -- ===== chain (scaled collapse at the envelope value `N'`) =====
  set N' : ℝ := 10 ^ 98 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) with hN'def
  have hΩ5GU : S.Ω ^ 5 ≤ P.G ^ 2 * P.U ^ 15 := by
    calc S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩpos.le hΩU 5
      _ ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
      _ ≤ P.G ^ 2 * P.U ^ 15 := by
          nlinarith [one_le_pow₀ (n := 2) hG1, pow_pos hUpos 15]
  have hN'1 : (1 : ℝ) ≤ N' := by
    rw [hN'def]
    have h1d : (1:ℝ) ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 :=
      (one_le_div (by positivity)).mpr hΩ5GU
    nlinarith [h1d]
  have hNle : (N : ℝ) ≤ 10 ^ 4 * N' := by
    rw [hN'def]
    calc (N : ℝ) ≤ 10 ^ 102 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := hNenv
      _ = 10 ^ 4 * (10 ^ 98 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) := by ring
  have hcollapse := step2_fsum_curv_le_t2t3 (P := P) (S := S)
    hG1 hU1 hΔ1 hH1 hΩU h1 N' hN'1 (le_of_eq hN'def) Tc hTclo hTchi
  -- scale the collapse: `E(N) ≤ 10⁸·E(N')`
  have hTc0 : (0:ℝ) ≤ Tc := le_trans (by positivity) hTclo
  have hAnn : (0:ℝ) ≤ S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
      + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc)) + Tc + 1 := by
    have h0 : (0:ℝ) ≤ S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
        + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc)) := by
      apply mul_nonneg (by unfold Scale.R; positivity)
      exact add_nonneg (by positivity) (Real.sqrt_nonneg _)
    linarith
  have hκnn : (0:ℝ) ≤ S.D^4/(P.X*S.A) := by
    unfold Scale.D Scale.A; positivity
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hN'nn : (0:ℝ) ≤ N' := le_trans zero_le_one hN'1
  have h2N : 2*(N:ℝ)+1 ≤ 10^4*(2*N'+1) := by linarith [hNle]
  have hinner : (S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
        + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc)) + Tc + 1)
        + (N:ℝ) * (S.D^4/(P.X*S.A))
      ≤ 10^4 * ((S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
        + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc)) + Tc + 1)
        + N' * (S.D^4/(P.X*S.A))) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNle) hκnn, hAnn,
      mul_nonneg hN'nn hκnn]
  calc (F_range.card : ℝ)
      ≤ (F_fsum.card : ℝ) := hcard
    _ ≤ (2 * (N:ℝ) + 1) * 10 ^ 200 * (S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
            + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc))
          + Tc + 1 + (N:ℝ) * (S.D^4/(P.X*S.A))) := hfsum
    _ ≤ (10^4*(2 * N' + 1)) * 10 ^ 200 * (S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
            + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc))
          + Tc + 1 + (N:ℝ) * (S.D^4/(P.X*S.A))) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2N (by positivity))
        linarith [hAnn, mul_nonneg hNnn hκnn]
    _ ≤ (10^4*(2 * N' + 1)) * 10 ^ 200 * (10^4 * (S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
            + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc))
          + Tc + 1 + N' * (S.D^4/(P.X*S.A)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hinner]
    _ = 10^8 * ((2 * N' + 1) * 10 ^ 200 * (S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
            + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) / Tc))
          + Tc + 1 + N' * (S.D^4/(P.X*S.A)))) := by ring
    _ ≤ 10^8 * (10 ^ 400 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
          + (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8)))) := by
        apply mul_le_mul_of_nonneg_left hcollapse (by positivity)
    _ = 10 ^ 408 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
          + (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))) := by
        rw [← mul_assoc, show ((10:ℝ)^8 * 10^400 : ℝ) = 10^408 by
          rw [← pow_add]]

end Squarefree
