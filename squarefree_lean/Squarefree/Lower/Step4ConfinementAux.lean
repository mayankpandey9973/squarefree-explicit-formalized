import Squarefree.Lower.UpsilonMagV2

/-!
# §5 large-defect Piece-B residual helpers (`Step4Confinement` support)

Three monomial-scale helpers feeding the correction bound `|correction| ≤ 2|Σ|/d̃` of the
per-`s` derivative lower bound (`Step4Confinement.sigma_s_deriv_lb`).  All are sound v²-pin
estimates (no vacuous `Δ²U⁵/Ω³` floor).

* `b0v_ge_16` — `16|v| ≤ |b₀|` (the §5 regime gap; mirrors `psum_resid_le_v2`'s `hbig_b0v`).
* `t1_abs_le_v2` — `|ℓ₁³(2ℓ₂−ℓ₁)v³| ≤ ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²` (the leading-`P₁`-cubic `t1` bound).
* `ptwo_div_le_v2` — `|Ptwo|/d ≤ 2·ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`, via `Ptwo/d = (P₀−Mm) − t1`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 3200000

variable {P : Globals} {S : Scale P}

/-- `16|v| ≤ |b₀|` in the §5 large-defect regime (re-derived sound; mirrors the `hbig_b0v`
step of `psum_resid_le_v2`). -/
theorem b0v_ge_16 {b₀ v : ℝ}
    (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    16 * |v| ≤ |b₀| := by
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hb0lo' : S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) ≤ |b₀| := by
    have : S.B / 2000000 = S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) := by rw [hBval]; field_simp
    rw [← this]; exact hb0lo
  -- 32·10²⁶·G·U⁵ ≤ Δ
  have hgoal : 32 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ S.Δ := by
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    have hU15 : (32:ℝ) * 10 ^ 26 ≤ P.U ^ 15 := by
      have h3 : ((10:ℝ) ^ 33) ^ 15 ≤ P.U ^ 15 := pow_le_pow_left₀ (by positivity) hUbig 15
      have h2 : ((10:ℝ) ^ 33) ^ 15 = (10:ℝ) ^ 495 := by rw [← pow_mul]
      calc (32:ℝ) * 10 ^ 26 ≤ (10:ℝ) ^ 28 := by norm_num
        _ ≤ (10:ℝ) ^ 495 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 15 := h2.symm
        _ ≤ P.U ^ 15 := h3
    have step1 : 32 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ P.U ^ 15 * (P.G * P.U ^ 5) :=
      mul_le_mul_of_nonneg_right hU15 (by positivity)
    have hGG : P.G ≤ 10 ^ 15 * P.G ^ 4 := by nlinarith [hG3, hGpos, pow_pos hGpos 4]
    have step2 : P.U ^ 15 * (P.G * P.U ^ 5) ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
      nlinarith [hGG, pow_pos hUpos 20, pow_pos hUpos 15, pow_pos hUpos 5]
    calc 32 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ P.U ^ 15 * (P.G * P.U ^ 5) := step1
      _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := step2
      _ ≤ S.Δ := hDeW
  set M : ℝ := 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) with hMdef
  have hMle : 16 * M ≤ S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) := by
    rw [hMdef, le_div_iff₀ (by positivity)]
    rw [show 16 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2000000 * (P.G * S.Ω ^ 3))
          = (32 * 10 ^ 26 * (P.G * P.U ^ 5)) * S.Δ * (S.Ω ^ 3 / S.Ω ^ 3) by field_simp; ring]
    rw [div_self (by positivity : (S.Ω:ℝ) ^ 3 ≠ 0), mul_one]
    calc (32 * 10 ^ 26 * (P.G * P.U ^ 5)) * S.Δ ≤ S.Δ * S.Δ :=
          mul_le_mul_of_nonneg_right hgoal hΔpos.le
      _ = S.Δ ^ 2 := by ring
  have hchain : 16 * M ≤ |b₀| := le_trans hMle hb0lo'
  calc 16 * |v| ≤ 16 * M := by apply mul_le_mul_of_nonneg_left hv (by norm_num)
    _ ≤ |b₀| := hchain

/-- `|t1| = |ℓ₁³(2ℓ₂−ℓ₁)v³| ≤ ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²` (= T): the `t1` monomial control. -/
theorem t1_abs_le_v2 {b₀ v ℓ₁ ℓ₂ : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hb0v : 16 * |v| ≤ |b₀|) :
    |ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3|
      ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 := by
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (1:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hℓ13nn : (0:ℝ) ≤ ℓ₁ ^ 3 := by positivity
  have h2ℓ1nn : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  rw [show ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 = (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 3 by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hℓ13nn h2ℓ1nn)]
  rw [show (v:ℝ) ^ 3 = v ^ 2 * v by ring, abs_mul, abs_pow]
  rw [show (v:ℝ) ^ 2 = |v| ^ 2 by rw [sq_abs]]
  -- goal: ℓ₁³(2ℓ₂-ℓ₁)·(|v|²·|v|) ≤ ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|·|v|²
  -- reduce: (2ℓ₂-ℓ₁)|v| ≤ ℓ₂(ℓ₂-ℓ₁)|b₀| ; (2ℓ₂-ℓ₁)≤2ℓ₂, ℓ₂-ℓ₁≥1, 16|v|≤|b₀|.
  have hred : (2 * ℓ₂ - ℓ₁) * |v| ≤ ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| := by
    have h1 : (2 * ℓ₂ - ℓ₁) * |v| ≤ 2 * ℓ₂ * |v| := by
      apply mul_le_mul_of_nonneg_right (by linarith) hvnn
    have h2 : 2 * ℓ₂ * |v| ≤ 2 * ℓ₂ * (|b₀| / 16) := by
      apply mul_le_mul_of_nonneg_left (by linarith [hb0v]) (by positivity)
    have h3 : 2 * ℓ₂ * (|b₀| / 16) ≤ ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| := by
      have hx : (0:ℝ) ≤ 2 * ℓ₂ * (|b₀| / 16) :=
        mul_nonneg (by linarith [hℓ2pos]) (by linarith [hb0nn])
      have hstep : 2 * ℓ₂ * (|b₀| / 16) ≤ (ℓ₂ - ℓ₁) * (8 * (2 * ℓ₂ * (|b₀| / 16))) := by
        nlinarith [hx, h21]
      calc 2 * ℓ₂ * (|b₀| / 16) ≤ (ℓ₂ - ℓ₁) * (8 * (2 * ℓ₂ * (|b₀| / 16))) := hstep
        _ = ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| := by ring
    linarith [h1, h2, h3]
  nlinarith [mul_le_mul_of_nonneg_left hred (mul_nonneg hℓ13nn (sq_nonneg (|v|))),
    hℓ13nn, sq_nonneg (|v|)]

/-- **§5 large-defect `|Ptwo|/d ≤ 2·T` (v²-form).**  Since `Ptwo/d = (P₀ − Mm) − t1`
with `|P₀ − Mm| ≤ T` (`psum_resid_le_v2`) and `|t1| ≤ T` (`t1_abs_le_v2`),
`|Ptwo/d| ≤ T + T = 2T`. -/
theorem ptwo_div_le_v2 {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D / 2 ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |Ptwo b₀ v ℓ₁ ℓ₂| / d
      ≤ 2 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2) := by
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMmdef
  -- |P₀ − Mm| ≤ T
  have hres : |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - Mm| ≤ T :=
    psum_resid_le_v2 (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo hdD hd_pos hReg
      hG1 hU1 hUbig hDeW
  -- |t1| ≤ T
  have hb0v : 16 * |v| ≤ |b₀| := b0v_ge_16 (P := P) (S := S) hb0lo hv hG1 hU1 hUbig hDeW
  have ht1 : |ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3| ≤ T := t1_abs_le_v2 hℓ1 hℓ12 hℓ12' hb0v
  -- Ptwo/d = (P₀ − Mm) − t1
  have hsplit : Ptwo b₀ v ℓ₁ ℓ₂ / d
      = (Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - Mm) - ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 := by
    rw [hMmdef, Pone]; ring
  -- |Ptwo|/d = |Ptwo/d| ≤ |P₀−Mm| + |t1| ≤ 2T
  have habs : |Ptwo b₀ v ℓ₁ ℓ₂| / d = |Ptwo b₀ v ℓ₁ ℓ₂ / d| := by
    rw [abs_div, abs_of_pos hd_pos]
  rw [habs, hsplit]
  calc |(Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - Mm) - ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3|
      ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - Mm| + |ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3| :=
        abs_sub _ _
    _ ≤ T + T := add_le_add hres ht1
    _ = 2 * T := by ring

end Squarefree
