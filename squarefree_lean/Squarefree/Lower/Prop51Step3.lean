import Squarefree.Lower.Prop51Bridge
import Squarefree.Lower.Step3Fsum
import Squarefree.Lower.Step3FsumTight

/-!
# §5 Step-3 per-pair RANGE bound (writeup 952–990, 1167–1177)

`ra_step3_range_le` is the pure-assembly lemma that turns the Step-3 `v`-range
`V₁ < |v(r)| ≤ V₂` count (the `s₃` term of `fiber_le_sum_ranges`) into the two Step-3
`Bcombine` monomials `t4' + t5'` (the `step3_fsum_le_t4t5` RHS).

The wiring is:

1. **subset.** For `r` in the range `V₁ < |v(r)| ≤ V₂` filter, the HARD bridge
   `qval_round_ge` (from `V₁ < |v(r)|`) supplies the `10⁵⁵·L ≤ |round(Qval r)|` conjunct and
   the EASY bridge `qval_round_le` (from `|v(r)| ≤ V₂`) supplies `(round(Qval r)).natAbs ≤ N`.
   So the range filter is a subset of the `Ra_step3_fsum` filter, hence card-`≤`.
2. **fsum.** `Ra_step3_fsum` bounds that card by `2·10⁵⁸·(κN² + ρN + (ρ/κ)(log N + 1))`.
3. **scale.** `step3_fsum_le_t4t5` bounds that by `10²⁴⁴·(t4' + t5')` with the PAYLESS
   monomials `t4' = (H/Δ)(Δ²/H)G^{15/2}U^{95/2}/Ω⁸`, `t5' = (H/Δ)G⁷U³⁵/(√Δ·Ω)` — the κN²-leg
   runs off the regime calibration `hHbig : 10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴` (in `prop_5_1`'s pack); the
   faithful band-edge primitive `hband : 1 ≤ G·U³·Ω⁴` is still used on the `κ·Nc` leg (no
   `1 ≤ Ω` hypothesis anywhere; see `Step3FsumTight.lean`).

The two `N`-constraints — the f-cap LOWER end `Mbound(V₂) + 1/2 ≤ N` (consumed by
`qval_round_le`) and the V₂ scale-domination envelope UPPER end `N ≤ 10⁹⁰·(Na + Nb + Nc)` with
`Na = G^{9/2}U^{55/2}/Ω⁵`, `Nb = H·G⁴·Ω²·U¹⁵/Δ^{5/2}`, `Nc = G²U¹⁵/Ω⁵` (consumed by
`step3_fsum_le_t4t5`) — are now CONSISTENT at the V₂ value (since
`Mbound(ℓ₁,V₂) ≤ 10⁹⁰·(Na+Nb+Nc)` once `ℓ₁ ≤ W = G·U⁵` is collapsed); both are taken as
hypotheses, their joint satisfiability the caller's responsibility (it pins the absolute
`V₂`-constant, writeup 1163–1166).  The benign `X^{o(1)}` log is absorbed by the faithful
`X`-large hypothesis `hlogcap : log N + 1 ≤ G³U¹⁵√Δ·Ω`, threaded through to `prop_5_1`.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **§5 Step-3 per-pair RANGE bound.**  The `v`-range `V₁ < |v(r)| ≤ V₂` part of the pair
fiber is bounded by the two Step-3 `Bcombine` monomials `t4' + t5'`.  Pure assembly of
`qval_round_ge`/`qval_round_le` (subset), `Ra_step3_fsum` (f-sum) and `step3_fsum_le_t4t5`
(scale). -/
theorem ra_step3_range_le {a : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ)
    (hHbig : 10 ^ 121 * (S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45) ≤ P.H ^ 2 * S.Ω ^ 14)
    (_hℓ1W : (ℓ₁ : ℝ) ≤ 130 * P.Wval)
    (Ra : Finset ℕ) (dStar : ℕ → ℤ)
    (hdStar : ∀ r ∈ Ra, inDa P.X P.H a (dStar r) ∧
        S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D ∧
        |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D ∧
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R)
    -- the per-`r` `dStar`-shift / window data the bridge lemmas consume
    (hwin : ∀ r ∈ Ra, (r + ℓ₁ ∈ Ra) → (r + ℓ₂ ∈ Ra) →
        (S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D) ∧
        (S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D) ∧
        |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))| ≤ 14 * P.H / S.D ∧
        |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))| ≤ 14 * P.H / S.D ∧
        (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R ∧ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R ∧
        (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
    (N : ℕ) (V₂ : ℝ) (hV2_nn : 0 ≤ V₂)
    -- the f-cap, LOWER end (consumed by `qval_round_le`)
    (hNcap : Mbound P S ℓ₁ V₂ + 1 / 2 ≤ (N : ℝ))
    -- the V₂ scale-domination envelope, UPPER end (consumed by `step3_fsum_le_t4t5`);
    -- this is `N ≤ 10⁹⁰·(Na + Nb + Nc)` — the genuine V₂ `f`-cap with `ℓ₁ ≤ W` collapsed.
    -- Jointly consistent with `hNcap` since `Mbound(ℓ₁,V₂) ≤ 10⁹⁰·(Na+Nb+Nc)` at the V₂ value.
    (hNenv : (N : ℝ) ≤ 10 ^ 97 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
        + 10 ^ 97 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
        + 10 ^ 97 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5))
    -- the largeness hypothesis absorbing the benign `X^{o(1)}` log: the `N`-free form at the
    -- `10⁹⁰` envelope cap (`prop_5_1` verbatim); the `10⁷` stretch costs a factor `2` via
    -- `log N' ≥ log 10⁷`, absorbed by the scaled collapse below.
    (hlogcap : Real.log (10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
          + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
          + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) + 1
        ≤ P.G ^ 3 * P.U ^ 15 * Real.sqrt S.Δ * S.Ω) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ 10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) < |vval P a dStar ℓ₁ ℓ₂ r|
          ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₂)).card : ℝ)
      ≤ 10 ^ 258 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2)
              / S.Ω ^ 8)
          + (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35
              / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω))) := by
  classical
  -- the abbreviation for the geometric threshold `L`
  set V₁ : ℝ := 10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)) with hV1def
  -- ===== Step 1: the range filter ⊆ the `Ra_step3_fsum` filter =====
  set F_range : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ V₁ < |vval P a dStar ℓ₁ ℓ₂ r| ∧ |vval P a dStar ℓ₁ ℓ₂ r| ≤ V₂) with hFrange
  set F_fsum : Finset ℕ := Ra.filter (fun r =>
      (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ (10:ℝ)^55 * (((ℓ₁:ℤ):ℝ) * ((ℓ₂:ℤ):ℝ) * (((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ))
          / (P.G * S.Ω ^ 5)) ≤ |((round (Qval P a dStar ℓ₁ ℓ₂ r)):ℝ)|
      ∧ (round (Qval P a dStar ℓ₁ ℓ₂ r)).natAbs ≤ N) with hFfsum
  have hsub : F_range ⊆ F_fsum := by
    intro r hr
    rw [hFrange, Finset.mem_filter] at hr
    obtain ⟨hrRa, hr1, hr2, hvlo, hvhi⟩ := hr
    obtain ⟨_hinDa, hdwin1, hdwin2, hRd, hr_lo, hr_hi⟩ := hdStar r hrRa
    obtain ⟨hd1win, hd2win, hRd1, hRd2, hr1_hi, hr2_hi, hd1ned, hd2ned⟩ := hwin r hrRa hr1 hr2
    rw [hFfsum, Finset.mem_filter]
    refine ⟨hrRa, hr1, hr2, ?_, ?_⟩
    · -- the HARD bridge gives the `10⁵⁵L ≤ |round|` conjunct
      have hge := qval_round_ge (P := P) (S := S) (a := a) (dStar := dStar)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hr_lo hr1_hi hr2_hi
        ⟨hdwin1, hdwin2⟩ hd1win hd2win hRd hRd1 hRd2 hd1ned hd2ned hvlo
        h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΔreg
      exact hge
    · -- the EASY bridge gives `natAbs ≤ N`
      have hle := qval_round_le (P := P) (S := S) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (r := r)
        (dStar := dStar) (V₂ := V₂) (N := N)
        hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hr_lo hr1_hi hr2_hi
        ⟨hdwin1, hdwin2⟩ hd1win hd2win hRd hRd1 hRd2 hd1ned hd2ned hvhi hV2_nn
        h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΔreg hNcap
      exact hle
  have hcard : (F_range.card : ℝ) ≤ (F_fsum.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  -- ===== Step 2: bound `F_fsum.card` by the f-sum =====
  have hfsum := Ra_step3_fsum (P := P) (S := S) (a := a)
    hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg
    Ra dStar hdStar N
  -- ===== Step 3: bound the f-sum by `10²⁴⁰·(t3 + t4)` =====
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hMnn : 0 ≤ Mbound P S ℓ₁ V₂ := by
      rw [Mbound]
      have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos
      have := P.U_pos
      have hℓnn : (0:ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by positivity
      positivity
    -- `Mbound + 1/2 ≤ N` and `0 ≤ Mbound` give `1/2 ≤ N`, so the natural `N ≥ 1`.
    have hhalf : (1 : ℝ) / 2 ≤ (N : ℝ) := by linarith [hNcap, hMnn]
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; norm_num at hhalf
      · exact h
    exact_mod_cast hNpos
  -- ===== Step 4: scaled collapse at the `10⁹⁰` envelope value `N'` =====
  set N' : ℝ := 10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
      + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
      + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) with hN'def
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hΩpos := S.Ω_pos
  have hNab0 : (0:ℝ) ≤ 10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
      + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2)) := by
    have := P.H_pos; have := S.Δ_pos; positivity
  have hNc90 : (10:ℝ) ^ 90 ≤ 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    have hΩ5GU : S.Ω ^ 5 ≤ P.G ^ 2 * P.U ^ 15 := by
      calc S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩpos.le hΩU 5
        _ ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
        _ ≤ P.G ^ 2 * P.U ^ 15 := by
            nlinarith [one_le_pow₀ (n := 2) hG1, pow_pos hUpos 15]
    have h1d : (1:ℝ) ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 :=
      (one_le_div (by positivity)).mpr hΩ5GU
    nlinarith [h1d]
  have hN'90 : (10:ℝ) ^ 90 ≤ N' := by rw [hN'def]; linarith [hNab0, hNc90]
  have hN'1 : (1 : ℝ) ≤ N' := le_trans (by norm_num) hN'90
  have hN'pos : (0:ℝ) < N' := lt_of_lt_of_le one_pos hN'1
  have hNle : (N : ℝ) ≤ 10 ^ 7 * N' := by
    rw [hN'def]; calc (N:ℝ) ≤ _ := hNenv
      _ = 10 ^ 7 * (10 ^ 90 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
          + 10 ^ 90 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
          + 10 ^ 90 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) := by ring
  have hscale := step3_fsum_le_t4t5 (P := P) (S := S)
    hG1 hU1 hΔ1 hH1 hband hΩU h1 hHbig N' hN'1 hN'def.le hlogcap
  -- the log stretch: `log N + 1 ≤ 2·(log N' + 1)`
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
  have hlog2 : Real.log (N:ℝ) + 1 ≤ 2 * (Real.log N' + 1) := by
    have hmono : Real.log (N:ℝ) ≤ Real.log (10 ^ 7 * N') := Real.log_le_log hNpos hNle
    have hsplit : Real.log ((10:ℝ) ^ 7 * N') = Real.log ((10:ℝ) ^ 7) + Real.log N' :=
      Real.log_mul (by positivity) hN'pos.ne'
    have h7le : Real.log ((10:ℝ) ^ 7) ≤ Real.log N' :=
      Real.log_le_log (by positivity) (le_trans (by norm_num) hN'90)
    have hN'nn : 0 ≤ Real.log N' := Real.log_nonneg hN'1
    linarith [hmono, hsplit.le, hsplit.ge, h7le, hN'nn]
  -- ===== chain =====
  have hκ0 : (0:ℝ) ≤ S.D^4/(P.X*S.A) := by
    unfold Scale.D Scale.A
    have := P.H_pos; have := S.Δ_pos; have := P.X_pos; have := S.Ω_pos; positivity
  have hρ0 : (0:ℝ) ≤ S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) := by
    unfold Scale.R
    have := P.H_pos; have := S.Δ_pos; have := S.Ω_pos; positivity
  have hρκ0 : (0:ℝ) ≤ (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) / (S.D^4/(P.X*S.A)) :=
    div_nonneg hρ0 hκ0
  have hNsq : (N:ℝ)^2 ≤ 10 ^ 14 * N'^2 := by nlinarith [hNle, hNpos.le, hN'pos.le]
  have hN14 : (N:ℝ) ≤ 10 ^ 14 * N' := by nlinarith [hNle, hN'pos.le]
  have hlog14 : Real.log (N:ℝ) + 1 ≤ 10 ^ 14 * (Real.log N' + 1) := by
    have hN'nn : 0 ≤ Real.log N' := Real.log_nonneg hN'1
    nlinarith [hlog2]
  calc (F_range.card : ℝ)
      ≤ (F_fsum.card : ℝ) := hcard
    _ ≤ 2 * (10:ℝ)^58 * ( (S.D^4/(P.X*S.A)) * (N:ℝ)^2
            + (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) * (N:ℝ)
            + (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) / (S.D^4/(P.X*S.A))
                * (Real.log (N:ℝ) + 1) ) := hfsum
    _ ≤ 10 ^ 14 * (2 * (10:ℝ)^58 * ( (S.D^4/(P.X*S.A)) * N'^2
            + (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) * N'
            + (S.R*(S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))) / (S.D^4/(P.X*S.A))
                * (Real.log N' + 1) )) := by
        have t1 := mul_le_mul_of_nonneg_left hNsq hκ0
        have t2 := mul_le_mul_of_nonneg_left hN14 hρ0
        have t3 := mul_le_mul_of_nonneg_left hlog14 hρκ0
        nlinarith [t1, t2, t3]
    _ ≤ 10 ^ 14 * (10 ^ 244 * ((P.H / S.Δ)
            * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2) / S.Ω ^ 8)
          + (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35
              / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω)))) := by
        apply mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 10 ^ 258 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2)
              / S.Ω ^ 8)
          + (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35
              / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω))) := by
        rw [← mul_assoc, show ((10:ℝ)^14 * 10^244 : ℝ) = 10^258 by rw [← pow_add]]

end Squarefree
