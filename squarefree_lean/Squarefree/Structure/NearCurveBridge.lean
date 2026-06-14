import Squarefree.Structure.ADecompAux
import Squarefree.Params
import Squarefree.Structure.DaSpacing
import Mathlib

/-!
# §3 → §6 near-curve bridge (membership transfer)

`nearcurve_membership` transfers the B1 popular-point estimate (`inDa_distInt_Ffun`,
`ADecompAux`) from the exact integer `d` to the approximated curve point `dtil(r)`, via a
mean-value (Taylor) bound on `F_a` over the dyadic window `[D, 2D]`.  This realizes the step
`F_a(d̃_a(r)) = F_a(d) + O(·)` of the writeup (lines ~1241–1335), bounding the integer-distance
of `F_a(d̃_a(r))` by `O((1 + Capx)·δ₆)` with `δ₆ = H/(Δ²Ω²)`.

The proof:
* triangle: `‖F̃‖ ≤ ‖F(d)‖ + |F(d̃) − F(d)|`;
* B1 term `‖F(d)‖ ≤ 2H/d² ≤ 2H/D² = 2(Ω²/H²)·δ₆ ≤ 2·δ₆` (using `Ω ≤ H`);
* perturbation via MVT: `|F(d̃) − F(d)| ≤ (sup|F'|)·|d̃ − d| ≤ 52·Capx·δ₆`, the scale algebra
  cancelling exactly (`X = G·H⁵`, `D = HΔ`, `A = ΔΩ`).

`C = 52` is an absolute constant; the `(1 + Capx)` factor absorbs both terms.
-/

open Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 1000000

/-- `distInt` is 1-Lipschitz: `‖u‖ ≤ ‖v‖ + |u − v|`. -/
private theorem distInt_le_add (u v : ℝ) : distInt u ≤ distInt v + |u - v| := by
  unfold distInt
  calc |u - (round u : ℝ)| ≤ |u - (round v : ℝ)| := round_le u (round v)
    _ = |(v - (round v : ℝ)) + (u - v)| := by ring_nf
    _ ≤ |v - (round v : ℝ)| + |u - v| := abs_add_le _ _

/-- `HasDerivAt` of `s ↦ X/s²` at `s ≠ 0`. -/
private theorem hasDerivAt_inv_sq (X s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t => X / t ^ 2) (-2 * X / s ^ 3) s := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s ^ 1) s := by
    simpa using (hasDerivAt_pow 2 s)
  have hsq : (s ^ 2) ≠ 0 := pow_ne_zero 2 hs
  have h := (hasDerivAt_const s X).div hpow hsq
  -- derivative is (0·s² − X·(2 s¹)) / (s²)²
  convert h using 1
  field_simp
  ring

/-- `HasDerivAt` of `s ↦ X/(s+a)²` at points where `s+a ≠ 0`. -/
private theorem hasDerivAt_inv_sq_shift (X a s : ℝ) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => X / (t + a) ^ 2) (-2 * X / (s + a) ^ 3) s := by
  have hpow : HasDerivAt (fun t : ℝ => (t + a) ^ 2) (2 * (s + a) ^ 1 * 1) s := by
    have hshift : HasDerivAt (fun t : ℝ => t + a) (1 : ℝ) s := by
      simpa using (hasDerivAt_id s).add_const a
    simpa using (hasDerivAt_pow 2 (s + a)).comp s hshift
  have hsq : ((s + a) ^ 2) ≠ 0 := pow_ne_zero 2 hsa
  have h := (hasDerivAt_const s X).div hpow hsq
  convert h using 1
  field_simp
  ring

/-- `HasDerivAt` of `s ↦ X/s² − X/(s+a)²` at points where `s ≠ 0` and `s+a ≠ 0`. -/
private theorem hasDerivAt_Ffun (X a s : ℝ) (hs : s ≠ 0) (hsa : s + a ≠ 0) :
    HasDerivAt (fun t => Ffun X a t)
      (-2 * X / s ^ 3 + 2 * X / (s + a) ^ 3) s := by
  have h1 : HasDerivAt (fun t => X / t ^ 2) (-2 * X / s ^ 3) s :=
    hasDerivAt_inv_sq X s hs
  have h2 : HasDerivAt (fun t => X / (t + a) ^ 2) (-2 * X / (s + a) ^ 3) s :=
    hasDerivAt_inv_sq_shift X a s hsa
  have h := h1.sub h2
  have hfun : (fun t => Ffun X a t) = (fun t => X / t ^ 2) - (fun t => X / (t + a) ^ 2) := by
    funext t; simp [Ffun, Pi.sub_apply]
  rw [hfun]
  convert h using 1
  ring

/-- **§3 → §6 near-curve membership bridge.** A popular `d` (so `d` and `d+a` are consecutive
`𝒟`-elements) whose curve approximant `d̃ = dtil(r)` is within `Capx·(Δ/G)(Δ³/A³)` makes
`F_a(d̃)` lie within `832·(1+Capx)·H/(Δ²Ω²)` of an integer.  The approximant window is the
widened dyadic band `[D/2, 3D]` (so the curve point may stray a constant factor outside
`[D,2D]`); the derivative bound over `[D/2,3D]` inflates by `16` (`1/s⁴ ≤ 16/D⁴`), giving
`C = 832 = 52·16`. -/
theorem nearcurve_membership : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ) (dtil : ℝ → ℝ) (r : ℕ) (d : ℤ) (Capx : ℝ),
      0 < a → S.A ≤ (a : ℝ) → (a : ℝ) ≤ 2 * S.A → S.Ω ≤ P.H → 0 ≤ Capx →
      2 * S.A ≤ S.D →
      inDa P.X P.H a d → S.D ≤ (d : ℝ) → (d : ℝ) ≤ 2 * S.D →
      S.D / 2 ≤ dtil (r : ℝ) → dtil (r : ℝ) ≤ 3 * S.D →
      |(d : ℝ) - dtil (r : ℝ)| ≤ Capx * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3) →
      distInt (Ffun P.X (a : ℝ) (dtil (r : ℝ)))
        ≤ C * (1 + Capx) * (P.H / (S.Δ ^ 2 * S.Ω ^ 2)) := by
  refine ⟨832, by norm_num, ?_⟩
  intro P S a dtil r d Capx ha hAa haA hΩH hCapx h2AD hin hDd hd2D hDdt hdt2D hdist
  -- abbreviations and positivity
  have hX : 0 < P.X := P.X_pos
  have hH : 0 < P.H := P.H_pos
  have hG : 0 < P.G := P.G_pos
  have hΔ : 0 < S.Δ := S.Δ_pos
  have hΩ : 0 < S.Ω := S.Ω_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  set dt : ℝ := dtil (r : ℝ) with hdtdef
  -- scale identities
  have hDeq : S.D = P.H * S.Δ := rfl
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hDpos : 0 < S.D := by rw [hDeq]; positivity
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hdRpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le hDpos hDd
  have hdtpos : (0 : ℝ) < dt := lt_of_lt_of_le (by positivity) hDdt
  -- δ₆ abbreviation
  set δ6 : ℝ := P.H / (S.Δ ^ 2 * S.Ω ^ 2) with hδ6def
  have hδ6pos : 0 < δ6 := by rw [hδ6def]; positivity
  --------------------------------------------------------------------------
  -- Step A: the B1 term `distInt (Ffun X a d) ≤ 2H/d² ≤ 2·δ₆`.
  --------------------------------------------------------------------------
  have hB1 : distInt (Ffun P.X (a : ℝ) (d : ℝ)) ≤ 2 * δ6 := by
    have hb := inDa_distInt_Ffun hX hdRpos ha hin
    -- 2H/d² ≤ 2H/D²
    have hd2 : S.D ^ 2 ≤ (d : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ hDpos.le hDd
    have hstep1 : 2 * P.H / (d : ℝ) ^ 2 ≤ 2 * P.H / S.D ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hd2
    -- 2H/D² = 2/(H Δ²) ≤ 2 H/(Δ²Ω²) = 2·δ₆ (using Ω² ≤ H²)
    have hΩ2 : S.Ω ^ 2 ≤ P.H ^ 2 := by apply pow_le_pow_left₀ hΩ.le hΩH
    have hstep2 : 2 * P.H / S.D ^ 2 ≤ 2 * δ6 := by
      have hrw : 2 * δ6 = (2 * P.H ^ 3) / (S.Δ ^ 2 * S.Ω ^ 2 * P.H ^ 2) := by
        rw [hδ6def]; field_simp
      rw [hDeq, hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      -- (2H)·(Δ²Ω²·H²) ≤ (2H³)·(HΔ)²  ⟺  Ω² ≤ H²
      have hgap : 0 ≤ 2 * P.H ^ 3 * S.Δ ^ 2 * (P.H ^ 2 - S.Ω ^ 2) := by
        apply mul_nonneg (by positivity); linarith [hΩ2]
      nlinarith [hgap]
    linarith [hb, hstep1, hstep2]
  --------------------------------------------------------------------------
  -- Step B: perturbation term `|Ffun X a dt - Ffun X a d| ≤ 52·Capx·δ₆` via MVT.
  --------------------------------------------------------------------------
  -- derivative bound constant Cder = 832·X·A/D⁴ (16× the `[D,2D]` value, from `1/s⁴ ≤ 16/D⁴`).
  set Cder : ℝ := 832 * P.X * S.A / S.D ^ 4 with hCderdef
  have hCdernn : 0 ≤ Cder := by rw [hCderdef]; positivity
  -- the (widened) interval and its convexity
  have hDhalfpos : 0 < S.D / 2 := by positivity
  set I : Set ℝ := Set.Icc (S.D / 2) (3 * S.D) with hIdef
  have hIconv : Convex ℝ I := convex_Icc _ _
  have hdmem : (d : ℝ) ∈ I := ⟨by linarith [hDd], by linarith [hd2D, hDpos]⟩
  have hdtmem : dt ∈ I := ⟨hDdt, hdt2D⟩
  -- on I, the derivative of Ffun is bounded by Cder
  have hderivbd : ∀ s ∈ I, ‖-2 * P.X / s ^ 3 + 2 * P.X / (s + (a : ℝ)) ^ 3‖ ≤ Cder := by
    intro s hs
    obtain ⟨hslo, hshi⟩ := hs
    have hspos : 0 < s := lt_of_lt_of_le hDhalfpos hslo
    have hsapos : 0 < s + (a : ℝ) := by linarith
    -- |g'(s)| = 2X(3s²a+3sa²+a³)/(s³(s+a)³)
    have hgval : -2 * P.X / s ^ 3 + 2 * P.X / (s + (a : ℝ)) ^ 3
        = -(2 * P.X * (3 * s ^ 2 * (a:ℝ) + 3 * s * (a:ℝ) ^ 2 + (a:ℝ) ^ 3)
            / (s ^ 3 * (s + (a:ℝ)) ^ 3)) := by
      field_simp
      ring
    rw [hgval, norm_neg, Real.norm_eq_abs]
    have hnum_nn : 0 ≤ 2 * P.X * (3 * s ^ 2 * (a:ℝ) + 3 * s * (a:ℝ) ^ 2 + (a:ℝ) ^ 3) := by
      positivity
    have hden_pos : 0 < s ^ 3 * (s + (a:ℝ)) ^ 3 := by positivity
    rw [abs_of_nonneg (by positivity)]
    -- numerator ≤ 2X·13s²a ; denominator ≥ s⁶ ; a ≤ 2A ; s ≥ D/2
    -- a ≤ 2s : since a ≤ 2A ≤ D ≤ 2s  (the new `2A ≤ D` hyp; `2s ≥ D` from `s ≥ D/2`)
    have ha2s : (a : ℝ) ≤ 2 * s := by
      have : (a : ℝ) ≤ S.D := le_trans haA h2AD
      linarith [this, hslo]
    -- numerator ≤ 2X·(13 s² a)
    have hnum_ub : 2 * P.X * (3 * s ^ 2 * (a:ℝ) + 3 * s * (a:ℝ) ^ 2 + (a:ℝ) ^ 3)
        ≤ 2 * P.X * (13 * s ^ 2 * (a:ℝ)) := by
      have h1 : 3 * s * (a:ℝ) ^ 2 ≤ 6 * s ^ 2 * (a:ℝ) := by
        nlinarith [ha2s, haR, hspos, mul_pos hspos haR]
      have h2 : (a:ℝ) ^ 3 ≤ 4 * s ^ 2 * (a:ℝ) := by
        nlinarith [ha2s, haR, hspos, mul_pos haR haR, sq_nonneg ((a:ℝ) - 2 * s)]
      nlinarith [h1, h2, hX, sq_nonneg s, haR]
    -- denominator ≥ s⁶
    have hden_lb : s ^ 6 ≤ s ^ 3 * (s + (a:ℝ)) ^ 3 := by
      have : s ^ 3 ≤ (s + (a:ℝ)) ^ 3 := by
        apply pow_le_pow_left₀ hspos.le; linarith [haR]
      nlinarith [this, pow_pos hspos 3]
    -- combine: ratio ≤ 2X·13s²a / s⁶ = 26 X a / s⁴ ≤ 26 X (2A)·(16/D⁴) = 832 X A / D⁴ = Cder
    have hratio : 2 * P.X * (3 * s ^ 2 * (a:ℝ) + 3 * s * (a:ℝ) ^ 2 + (a:ℝ) ^ 3)
        / (s ^ 3 * (s + (a:ℝ)) ^ 3) ≤ 26 * P.X * (a:ℝ) / s ^ 4 := by
      rw [div_le_div_iff₀ hden_pos (by positivity)]
      have hs4pos : (0 : ℝ) < s ^ 4 := by positivity
      calc 2 * P.X * (3 * s ^ 2 * (a:ℝ) + 3 * s * (a:ℝ) ^ 2 + (a:ℝ) ^ 3) * s ^ 4
          ≤ 2 * P.X * (13 * s ^ 2 * (a:ℝ)) * s ^ 4 := by
            apply mul_le_mul_of_nonneg_right hnum_ub hs4pos.le
        _ = 26 * P.X * (a:ℝ) * s ^ 6 := by ring
        _ ≤ 26 * P.X * (a:ℝ) * (s ^ 3 * (s + (a:ℝ)) ^ 3) := by
            apply mul_le_mul_of_nonneg_left hden_lb (by positivity)
    refine le_trans hratio ?_
    -- 26 X a / s⁴ ≤ 26 X (2A)·(16/D⁴) = 832 X A / D⁴ = Cder  (using s ≥ D/2 ⟹ s⁴ ≥ D⁴/16)
    have hs4 : S.D ^ 4 ≤ 16 * s ^ 4 := by
      have hsq : (S.D / 2) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hDhalfpos.le hslo 4
      nlinarith [hsq]
    rw [hCderdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have haA2 : (a : ℝ) ≤ 2 * S.A := haA
    calc 26 * P.X * (a:ℝ) * S.D ^ 4
        ≤ 26 * P.X * (2 * S.A) * S.D ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [haA2, hX]
      _ = 52 * P.X * S.A * S.D ^ 4 := by ring
      _ ≤ 52 * P.X * S.A * (16 * s ^ 4) := by
          apply mul_le_mul_of_nonneg_left hs4 (by positivity)
      _ = 832 * P.X * S.A * s ^ 4 := by ring
  -- MVT: |Ffun dt - Ffun d| ≤ Cder · |dt - d|
  have hMVT : |Ffun P.X (a:ℝ) dt - Ffun P.X (a:ℝ) (d:ℝ)| ≤ Cder * |dt - (d:ℝ)| := by
    have hderiv : ∀ s ∈ I, HasDerivWithinAt (fun t => Ffun P.X (a:ℝ) t)
        (-2 * P.X / s ^ 3 + 2 * P.X / (s + (a:ℝ)) ^ 3) I s := by
      intro s hs
      obtain ⟨hslo, _⟩ := hs
      have hspos : 0 < s := lt_of_lt_of_le hDhalfpos hslo
      have hsapos : 0 < s + (a:ℝ) := by linarith
      exact (hasDerivAt_Ffun P.X (a:ℝ) s (ne_of_gt hspos) (ne_of_gt hsapos)).hasDerivWithinAt
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hderivbd hIconv hdmem hdtmem
    simpa only [Real.norm_eq_abs] using h
  -- now bound Cder · |dt - d| ≤ 832 · Capx · δ₆
  have hpert : Cder * |dt - (d:ℝ)| ≤ 832 * Capx * δ6 := by
    have hdist' : |dt - (d:ℝ)| ≤ Capx * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3) := by
      rw [abs_sub_comm]; exact hdist
    have hCdist : Cder * |dt - (d:ℝ)|
        ≤ Cder * (Capx * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3)) :=
      mul_le_mul_of_nonneg_left hdist' hCdernn
    refine le_trans hCdist ?_
    -- Cder · Capx · (Δ/G)(Δ³/A³) = 832·Capx·δ₆  (scale cancellation)
    rw [hCderdef, hδ6def, hAeq, hDeq, P.X_eq_G_mul_H_pow_five]
    rw [le_iff_eq_or_lt]; left
    field_simp
  --------------------------------------------------------------------------
  -- Step C: assemble via the 1-Lipschitz triangle inequality.
  --------------------------------------------------------------------------
  have htri := distInt_le_add (Ffun P.X (a:ℝ) dt) (Ffun P.X (a:ℝ) (d:ℝ))
  have hfinal : distInt (Ffun P.X (a:ℝ) dt) ≤ 2 * δ6 + 832 * Capx * δ6 := by
    calc distInt (Ffun P.X (a:ℝ) dt)
        ≤ distInt (Ffun P.X (a:ℝ) (d:ℝ)) + |Ffun P.X (a:ℝ) dt - Ffun P.X (a:ℝ) (d:ℝ)| := htri
      _ ≤ 2 * δ6 + Cder * |dt - (d:ℝ)| := by linarith [hB1, hMVT]
      _ ≤ 2 * δ6 + 832 * Capx * δ6 := by linarith [hpert]
  -- (2 + 832 Capx)·δ₆ ≤ 832·(1+Capx)·δ₆
  rw [hdtdef] at hfinal ⊢
  refine le_trans hfinal ?_
  rw [hδ6def]
  have : 2 * (P.H / (S.Δ ^ 2 * S.Ω ^ 2)) + 832 * Capx * (P.H / (S.Δ ^ 2 * S.Ω ^ 2))
      ≤ 832 * (1 + Capx) * (P.H / (S.Δ ^ 2 * S.Ω ^ 2)) := by
    have hδ6pos' : 0 < P.H / (S.Δ ^ 2 * S.Ω ^ 2) := by positivity
    nlinarith [hCapx, hδ6pos']
  exact this

end Squarefree
