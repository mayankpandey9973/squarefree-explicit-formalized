import Squarefree.Lower.Step2CountCurv2

/-!
# §5 Step-2 curvature-regime `f`-sum (`Ra_step2_fsum_curv`)

`Ra_step2_fsum_curv` turns the per-`f` curvature count `Ra_step2_count_curv` into a per-pair count
by partitioning the triple set by `f = round(Qval)` and summing over `f ∈ Icc (-N) N`.  Unlike the
`f`-large `Ra_step2_fsum`, there is no `f`-largeness threshold: EVERY `f` (including `f = 0`) is
bounded by `Ra_step2_count_curv`.  Each fiber is bounded by the UNIFORM weight obtained from
`|f| ≤ N` (so `T_f = |f|·κ + T_curv ≤ N·κ + T_curv`) and `√(δ/T_f) ≤ √(δ/T_curv)` (since
`T_f ≥ T_curv`); summing the `2N+1` fibers gives the writeup's "per-`f` bound × #f" shape

`#S₂ ≤ (2N+1)·10²⁰⁰·(R·(δ + √(δ/T_curv)) + T_curv + 1 + N·κ)`,

with `δ = 4·δ₂₃`, `κ = D⁴/(X·A)`, `T_curv = ℓ₁ℓ₂(ℓ₂−ℓ₁)·B²/D`.
-/

open Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000 in
/-- **§5 Step-2 curvature-regime per-pair count.**  Fiberwise partition + uniform per-fiber bound. -/
theorem Ra_step2_fsum_curv {a : ℤ}
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
        (1/72) * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R) (N : ℕ) :
    ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
        ∧ (round (Qval P a dStar ℓ₁ ℓ₂ r)).natAbs ≤ N)).card : ℝ)
      ≤ (2 * (N:ℝ) + 1) * 10 ^ 200 * (S.R * (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
            + Real.sqrt (4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6))
                / (((ℓ₁:ℤ):ℝ)*((ℓ₂:ℤ):ℝ)*(((ℓ₂:ℤ):ℝ)-((ℓ₁:ℤ):ℝ))*S.B^2/S.D)))
          + (((ℓ₁:ℤ):ℝ)*((ℓ₂:ℤ):ℝ)*(((ℓ₂:ℤ):ℝ)-((ℓ₁:ℤ):ℝ))*S.B^2/S.D) + 1
          + (N:ℝ) * (S.D^4/(P.X*S.A))) := by
  classical
  have hHpos := P.H_pos; have hGpos := P.G_pos; have hUpos := P.U_pos
  have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos; have hXpos := P.X_pos
  have hDpos : (0 : ℝ) < S.D := by unfold Scale.D; positivity
  have hApos : (0 : ℝ) < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hℓ1R : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12
  set δ : ℝ := 4 * (S.Δ^2*P.G^2*P.U^20/(P.H*S.Ω^6)) with hδ_def
  have hδpos : 0 < δ := by rw [hδ_def]; positivity
  set κ : ℝ := S.D^4/(P.X*S.A) with hκ_def
  have hκpos : 0 < κ := by rw [hκ_def]; positivity
  set Tc : ℝ := ((ℓ₁:ℤ):ℝ)*((ℓ₂:ℤ):ℝ)*(((ℓ₂:ℤ):ℝ)-((ℓ₁:ℤ):ℝ))*S.B^2/S.D with hTc_def
  have hTcpos : 0 < Tc := by
    rw [hTc_def]
    have hdiff : 0 < ((ℓ₂:ℤ):ℝ) - ((ℓ₁:ℤ):ℝ) := by linarith [hℓ12R]
    have hℓ1pos : 0 < ((ℓ₁:ℤ):ℝ) := by linarith [hℓ1R]
    have hℓ2pos : 0 < ((ℓ₂:ℤ):ℝ) := by linarith [hℓ12R, hℓ1pos]
    have hnum : 0 < ((ℓ₁:ℤ):ℝ)*((ℓ₂:ℤ):ℝ)*(((ℓ₂:ℤ):ℝ)-((ℓ₁:ℤ):ℝ))*S.B^2 :=
      mul_pos (mul_pos (mul_pos hℓ1pos hℓ2pos) hdiff) (by positivity)
    exact div_pos hnum hDpos
  set g : ℕ → ℤ := fun r => round (Qval P a dStar ℓ₁ ℓ₂ r) with hg_def
  set S2 : Finset ℕ := Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
      ∧ (g r).natAbs ≤ N) with hS2_def
  -- uniform per-fiber weight
  set Hun : ℝ := 10 ^ 200 * (S.R * (δ + Real.sqrt (δ / Tc)) + Tc + 1 + (N:ℝ) * κ) with hHun_def
  have hHun_nn : 0 ≤ Hun := by
    rw [hHun_def]
    have : 0 ≤ S.R * (δ + Real.sqrt (δ / Tc)) + Tc + 1 + (N:ℝ) * κ := by
      have := Real.sqrt_nonneg (δ / Tc); positivity
    positivity
  -- Step 1: g maps S2 into Icc (-N) N
  have hmap : ∀ r ∈ S2, g r ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
    intro r hr
    rw [hS2_def, Finset.mem_filter] at hr
    have hnat : (g r).natAbs ≤ N := hr.2.2.2
    rw [Finset.mem_Icc]
    have hle : |g r| ≤ (N:ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hnat
    exact ⟨by linarith [abs_le.mp hle |>.1], by linarith [abs_le.mp hle |>.2]⟩
  -- Step 2: fiberwise card
  have hcard_eq : S2.card
      = ∑ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (S2.filter (fun r => g r = f)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  -- Step 3: per-fiber bound by Hun
  have hfiber : ∀ f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      ((S2.filter (fun r => g r = f)).card : ℝ) ≤ Hun := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hfabs : |(f:ℝ)| ≤ (N:ℝ) := by
      rw [abs_le]; constructor
      · have : (-(N:ℤ):ℝ) ≤ (f:ℝ) := by exact_mod_cast hf.1
        push_cast at this; linarith
      · have : (f:ℝ) ≤ (N:ℤ) := by exact_mod_cast hf.2
        push_cast at this; linarith
    have hcount := Ra_step2_count_curv (P := P) (S := S) hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W
      h1 hband hG1 hU1 hΔ1 hH1 hUH hΩU hUbig hΔreg hsmall Ra dStar hdStar (f := f)
    -- subset:  fiber ⊆ {round = f}
    have hsub : S2.filter (fun r => g r = f)
        ⊆ Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra) ∧ round (Qval P a dStar ℓ₁ ℓ₂ r) = f) := by
      intro r hr
      rw [Finset.mem_filter, hS2_def, Finset.mem_filter] at hr
      rw [Finset.mem_filter]
      exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2.1, by rw [hg_def] at hr; exact hr.2⟩
    have hcardle : ((S2.filter (fun r => g r = f)).card : ℝ)
        ≤ ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
            ∧ round (Qval P a dStar ℓ₁ ℓ₂ r) = f)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine le_trans hcardle (le_trans hcount ?_)
    -- bound the count weight by Hun
    rw [hHun_def, ← hδ_def, ← hTc_def]
    set Tf : ℝ := |(f:ℝ)| * S.D ^ 4 / (P.X * S.A) + Tc with hTf_def
    have hTf_ge : Tc ≤ Tf := by
      rw [hTf_def]
      have h0 : 0 ≤ |(f:ℝ)| * S.D ^ 4 / (P.X * S.A) := by positivity
      linarith
    have hsqrt_le : Real.sqrt (δ / Tf) ≤ Real.sqrt (δ / Tc) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left hδpos.le hTcpos hTf_ge
    have hTf_le : Tf ≤ Tc + (N:ℝ) * κ := by
      rw [hTf_def, hκ_def]
      have : |(f:ℝ)| * S.D ^ 4 / (P.X * S.A) ≤ (N:ℝ) * (S.D ^ 4 / (P.X * S.A)) := by
        rw [show |(f:ℝ)| * S.D ^ 4 / (P.X * S.A) = |(f:ℝ)| * (S.D ^ 4 / (P.X * S.A)) by ring]
        apply mul_le_mul_of_nonneg_right hfabs (by positivity)
      linarith
    have hweight : S.R * (δ + Real.sqrt (δ / Tf)) + Tf + 1
        ≤ S.R * (δ + Real.sqrt (δ / Tc)) + Tc + 1 + (N:ℝ) * κ := by
      have h1' : S.R * (δ + Real.sqrt (δ / Tf)) ≤ S.R * (δ + Real.sqrt (δ / Tc)) := by
        apply mul_le_mul_of_nonneg_left _ hRpos.le; linarith [hsqrt_le]
      linarith [h1', hTf_le]
    apply mul_le_mul_of_nonneg_left hweight (by norm_num)
  -- Step 4: sum the fibers
  have hsum : (S2.card : ℝ) ≤ ∑ _f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Hun := by
    rw [hcard_eq, Nat.cast_sum]
    exact Finset.sum_le_sum hfiber
  have hconst : (∑ _f ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Hun) = (2 * (N:ℝ) + 1) * Hun := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.Icc (-(N:ℤ)) (N:ℤ)).card = 2 * N + 1 := by
      rw [Int.card_Icc]; omega
    rw [hcard]; push_cast; ring
  rw [hconst] at hsum
  calc ((Ra.filter (fun r => (r + ℓ₁ ∈ Ra) ∧ (r + ℓ₂ ∈ Ra)
          ∧ (round (Qval P a dStar ℓ₁ ℓ₂ r)).natAbs ≤ N)).card : ℝ)
      = (S2.card : ℝ) := by rw [hS2_def, hg_def]
    _ ≤ (2 * (N:ℝ) + 1) * Hun := hsum
    _ = (2 * (N:ℝ) + 1) * 10 ^ 200 * (S.R * (δ + Real.sqrt (δ / Tc)) + Tc + 1 + (N:ℝ) * κ) := by
        rw [hHun_def]; ring

end Squarefree
