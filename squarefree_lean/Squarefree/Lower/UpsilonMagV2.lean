import Squarefree.Lower.UpsilonMag

/-!
# §5 Step-4: magnitude foundation, v²-form (writeup 1029–1033)

The cancellation-avoidance lower bound on `|P₁ + P₂/d|` keyed on the `b₀v²` monomial of `P₁`.
Under the LOCAL hypothesis `hvlo : 10·ℓ₂(ℓ₂−ℓ₁)b₀²/d ≤ |v|` (the cancellation-avoidance bound in
this lemma's own variables), the `b₀v²` term of `P₁` dominates: its magnitude is `3T` with
`T := ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`, while every other monomial of `P₁+P₂/d` contributes `≤ T` in total,
so `|P₁+P₂/d| ≥ 3T − T = 2T ≥ T`.

The five "other" monomials are controlled as follows (ratio to `T`):
* `P₁` `v³`-term: `≤ 2|v|/((ℓ₂−ℓ₁)|b₀|)`, tiny via `hv`/`hb0lo`/`hDeW`.
* `P₂` linear-in-`v` term: `= 5ℓ₂(ℓ₂−ℓ₁)b₀²/(d|v|) ≤ 1/2` by `hvlo`.
* `P₂` `b₀²v²`-term: `= 15ℓ₂|b₀|/d`, tiny via `hb0`/`hdD`/`hReg`.
* `P₂` `b₀v³`-term and `v⁴`-term: tiny via the scale chains.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 3200000 in
/-- **§5 Step-4 magnitude residual (v²-form).**  With the local cancellation-avoidance bound
`hvlo`, every monomial of `P₁+P₂/d` other than the leading `3·ℓ₁³ℓ₂(ℓ₂−ℓ₁)b₀v²` contributes
`≤ T := ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²` in total.  This is the shared core of both the lower bound
(`psum_abs_ge_v2`, `|P₁+P₂/d| ≥ 3T − T = 2T ≥ T`) and the upper bound (`psum_abs_le_v2`,
`|P₁+P₂/d| ≤ 3T + T = 4T`). -/
theorem psum_resid_le_v2 {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D / 2 ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2|
      ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 := by
  -- positivity / basic facts
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2pos.le
  have h21 : (1:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h2ℓ1nn : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have h32ℓnn : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hℓ13pos : 0 < ℓ₁ ^ 3 := by positivity
  have hℓ13nn : 0 ≤ ℓ₁ ^ 3 := hℓ13pos.le
  have hv2eq : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  have hb02eq : b₀ ^ 2 = |b₀| ^ 2 := (sq_abs b₀).symm
  -- Wval unfolded and B unfolded
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hDval : S.D = P.H * S.Δ := rfl
  -- a few derived numeric scale facts
  have hΔ1 : (1:ℝ) ≤ S.Δ := by
    have : (10:ℝ) ^ 15 * (P.G ^ 4 * P.U ^ 20) ≥ 1 := by
      have := one_le_pow₀ (n := 4) hG1
      have := one_le_pow₀ (n := 20) hU1
      nlinarith [one_le_pow₀ (n := 4) hG1, one_le_pow₀ (n := 20) hU1]
    linarith [hDeW]
  -- abbreviations
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  -- main term M = 3 ℓ₁³ ℓ₂ (ℓ₂-ℓ₁) b₀ v²;  |M| = 3T
  have hMabs : |3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2| = 3 * T := by
    rw [hTdef]
    rw [show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
          = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
        abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  -- R := (Pone + Ptwo/d) - M
  -- We bound |R| ≤ T by bounding the five monomials.
  -- ===== term 1:  ℓ₁³(2ℓ₂−ℓ₁)v³ ;  |t1| ≤ (1/8) T =====
  -- ratio = (2ℓ₂−ℓ₁)|v|/(ℓ₂(ℓ₂−ℓ₁)|b₀|) ≤ 2|v|/((ℓ₂−ℓ₁)|b₀|) tiny.
  -- We show |t1| ≤ ℓ₁³ ℓ₂ (ℓ₂-ℓ₁) |b₀| v² · (1/8) suffices via 2(2ℓ₂-ℓ₁)|v| ≤ ℓ₂(ℓ₂-ℓ₁)|b₀| ... use generic small bound
  -- Establish: |v| ≤ M  and  |b₀| ≥ B/2e6,  ℓ₂ ≤ W.
  -- chain A:  8·10^26 · G U⁵ ≤ Δ   (from hDeW, hUbig)
  have hΔbig : 8 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ S.Δ := by
    -- Δ ≥ 10^15 G⁴ U²⁰ = 10^15 G⁴ U⁵ · U¹⁵ ≥ 10^15 · G U⁵ · U¹⁵
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    have hU15 : (8:ℝ) * 10 ^ 26 ≤ P.U ^ 15 := by
      have h2 : ((10:ℝ) ^ 33) ^ 15 = (10:ℝ) ^ 495 := by rw [← pow_mul]
      have h3 : ((10:ℝ) ^ 33) ^ 15 ≤ P.U ^ 15 := pow_le_pow_left₀ (by positivity) hUbig 15
      have h1 : (8:ℝ) * 10 ^ 26 ≤ (10:ℝ) ^ 27 := by norm_num
      have h12 : (10:ℝ) ^ 27 ≤ (10:ℝ) ^ 495 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      calc (8:ℝ) * 10 ^ 26 ≤ (10:ℝ) ^ 27 := h1
        _ ≤ (10:ℝ) ^ 495 := h12
        _ = ((10:ℝ) ^ 33) ^ 15 := h2.symm
        _ ≤ P.U ^ 15 := h3
    -- 10^15 G⁴ U²⁰ = (10^15 / (8·10^26)) ... instead: 8·10^26 G U⁵ ≤ U¹⁵ · G U⁵ = G U²⁰ ≤ G⁴U²⁰ ≤ 10^15 G⁴U²⁰ ≤ Δ
    have step1 : 8 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ P.U ^ 15 * (P.G * P.U ^ 5) :=
      mul_le_mul_of_nonneg_right hU15 (by positivity)
    have step2 : P.U ^ 15 * (P.G * P.U ^ 5) ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
      have hGG : P.G ≤ 10 ^ 15 * P.G ^ 4 := by nlinarith [hG3, hGpos, pow_pos hGpos 4]
      nlinarith [hGG, pow_pos hUpos 20, pow_pos hUpos 15, pow_pos hUpos 5]
    calc 8 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ P.U ^ 15 * (P.G * P.U ^ 5) := step1
      _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := step2
      _ ≤ S.Δ := hDeW
  -- |b₀| ≥ B/2e6 = Δ²/(2e6 G Ω³)
  have hb0lo' : S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) ≤ |b₀| := by
    have : S.B / 2000000 = S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) := by
      rw [hBval]; field_simp
    rw [← this]; exact hb0lo
  -- |b₀| > 0
  have hb0pos : 0 < |b₀| := lt_of_lt_of_le (by positivity) hb0lo'
  have hb0ne : b₀ ≠ 0 := by
    intro h; rw [h] at hb0pos; simp at hb0pos
  -- |v| ≤ M
  set M : ℝ := 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  -- KEY tiny bound:  2 (2ℓ₂-ℓ₁) |v| ≤ ℓ₂ (ℓ₂-ℓ₁) |b₀|   (so |t1| ≤ (1/2)·ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|·... )
  -- Actually we want |t1| ≤ (1/8) T = (1/8) ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v².
  -- |t1| = ℓ₁³(2ℓ₂-ℓ₁)|v|³.  Need ℓ₁³(2ℓ₂-ℓ₁)|v|³ ≤ (1/8)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²
  --  ⟺ 8(2ℓ₂-ℓ₁)|v| ≤ ℓ₂(ℓ₂-ℓ₁)|b₀|.  Since 2ℓ₂-ℓ₁ ≤ 2ℓ₂, suffices 16|v| ≤ (ℓ₂-ℓ₁)|b₀|.
  -- (ℓ₂-ℓ₁) ≥ 1, so suffices 16|v| ≤ |b₀|.
  have hbig_b0v : 16 * |v| ≤ |b₀| := by
    -- |v| ≤ M = 1e20 Δ U⁵/Ω³ ;  |b₀| ≥ Δ²/(2e6 G Ω³).
    -- 16 M = 16e20 Δ U⁵/Ω³.  Want ≤ Δ²/(2e6 G Ω³)
    --  ⟺ 16e20 Δ U⁵/Ω³ · 2e6 G Ω³ ≤ Δ²  ⟺ 32e26 G U⁵ Δ ≤ Δ²  ⟺ 32e26 G U⁵ ≤ Δ. true by hΔbig (8e26→32e26? need 32e26).
    -- Strengthen hΔbig usage: actually we only proved 8e26 G U⁵ ≤ Δ. 32e26 needs factor 4.
    -- Use that Δ ≥ 10^15 G⁴U²⁰ ≥ huge; redo directly.
    -- 32e26 G U⁵ ≤ Δ
    have hgoal : 32 * 10 ^ 26 * (P.G * P.U ^ 5) ≤ S.Δ := by
      have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
      have hU15 : (32:ℝ) * 10 ^ 26 ≤ P.U ^ 15 := by
        have h2 : ((10:ℝ) ^ 33) ^ 15 = (10:ℝ) ^ 495 := by rw [← pow_mul]
        have h3 : ((10:ℝ) ^ 33) ^ 15 ≤ P.U ^ 15 := pow_le_pow_left₀ (by positivity) hUbig 15
        have h1 : (32:ℝ) * 10 ^ 26 ≤ (10:ℝ) ^ 28 := by norm_num
        have h12 : (10:ℝ) ^ 28 ≤ (10:ℝ) ^ 495 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        calc (32:ℝ) * 10 ^ 26 ≤ (10:ℝ) ^ 28 := h1
          _ ≤ (10:ℝ) ^ 495 := h12
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
    -- 16 M ≤ |b₀|.  16M = 16e20 Δ U⁵/Ω³ ≤ Δ²/(2e6 G Ω³) = B/2e6 ≤ |b₀|.
    have hMle : 16 * M ≤ S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) := by
      rw [hMdef, le_div_iff₀ (by positivity)]
      -- 16·(1e20 Δ U⁵/Ω³)·(2e6 G Ω³) ≤ Δ²
      rw [show 16 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2000000 * (P.G * S.Ω ^ 3))
            = (32 * 10 ^ 26 * (P.G * P.U ^ 5)) * S.Δ * (S.Ω ^ 3 / S.Ω ^ 3) by
          field_simp; ring]
      rw [div_self (by positivity : (S.Ω:ℝ) ^ 3 ≠ 0), mul_one]
      calc (32 * 10 ^ 26 * (P.G * P.U ^ 5)) * S.Δ ≤ S.Δ * S.Δ :=
            mul_le_mul_of_nonneg_right hgoal hΔpos.le
        _ = S.Δ ^ 2 := by ring
    have hchain : 16 * M ≤ |b₀| := le_trans hMle hb0lo'
    calc 16 * |v| ≤ 16 * M := by
          apply mul_le_mul_of_nonneg_left hv (by norm_num)
      _ ≤ |b₀| := hchain
  -- term1 bound
  have ht1 : |ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3| ≤ (1/8) * T := by
    rw [show ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 = (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 3 by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))]
    rw [show (v:ℝ) ^ 3 = v ^ 2 * v by ring, abs_mul, abs_pow]
    rw [hTdef, hv2eq]
    -- goal: ℓ₁³(2ℓ₂-ℓ₁)·(|v|²·|v|) ≤ (1/8)·ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|·|v|²
    -- divide by ℓ₁³|v|² ≥0:  (2ℓ₂-ℓ₁)|v| ≤ (1/8)ℓ₂(ℓ₂-ℓ₁)|b₀|
    -- from 16|v|≤|b₀|, (ℓ₂-ℓ₁)≥1, 2ℓ₂-ℓ₁≤2ℓ₂:
    have hkey : (2 * ℓ₂ - ℓ₁) * |v| ≤ (1/8) * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀|) := by
      have h1 : (2 * ℓ₂ - ℓ₁) * |v| ≤ 2 * ℓ₂ * |v| := by
        apply mul_le_mul_of_nonneg_right (by linarith) hvnn
      have h2 : 2 * ℓ₂ * |v| ≤ 2 * ℓ₂ * (|b₀| / 16) := by
        apply mul_le_mul_of_nonneg_left (by linarith [hbig_b0v]) (by positivity)
      have h3 : 2 * ℓ₂ * (|b₀| / 16) ≤ (1/8) * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀|) := by
        rw [show (1/8) * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀|) = (ℓ₂ - ℓ₁) * (2 * ℓ₂ * (|b₀|/16)) by ring]
        nlinarith [mul_nonneg hℓ2nn hb0nn, h21]
      linarith [h1, h2, h3]
    nlinarith [hkey, hℓ13pos, sq_nonneg (|v|), mul_nonneg hℓ13nn (sq_nonneg (|v|)),
      mul_pos hℓ13pos (by positivity : (0:ℝ) < |v| ^ 2 + 1)]
  -- ===== term 2:  −5ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²b₀³v/d ;  |t2| ≤ (1/2)T  via hvlo =====
  have ht2 : |(-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v) / d| ≤ (1/2) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v
          = (-(5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)) * (b₀ ^ 3 * v) by ring,
      abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2),
      abs_mul]
    have hb03 : |b₀ ^ 3| = |b₀| ^ 3 := by rw [abs_pow]
    rw [hb03]
    rw [div_le_iff₀ hd_pos, hTdef, hv2eq]
    -- goal: 5ℓ₁³ℓ₂²(ℓ₂-ℓ₁)²·(|b₀|³·|v|) ≤ (1/2)·ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²·d
    -- hvlo : 10*(ℓ₂*(ℓ₂-ℓ₁)*b₀²/d) ≤ |v|.  Turn into 10 ℓ₂(ℓ₂-ℓ₁)|b₀|² ≤ |v| d.
    have hvlo' : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| ^ 2) ≤ |v| * d := by
      have h : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) * d ≤ |v| * d :=
        mul_le_mul_of_nonneg_right hvlo hd_pos.le
      have heq : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) * d = 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2) := by
        field_simp
      rw [heq, hb02eq] at h; exact h
    -- Now: 5ℓ₁³ℓ₂²(ℓ₂-ℓ₁)²|b₀|³|v| ≤ (1/2)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²·d.
    -- Multiply hvlo' by (1/2)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v| ≥0:
    --   (1/2)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|·10ℓ₂(ℓ₂-ℓ₁)|b₀|² ≤ (1/2)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|·|v|d
    --  LHS = 5ℓ₁³ℓ₂²(ℓ₂-ℓ₁)²|b₀|³|v|, RHS = (1/2)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²d. exactly the goal.
    have hcoef : (0:ℝ) ≤ (1/2) * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * |v| := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hvlo' hcoef, hℓ13nn, hℓ2nn, h21nn, hb0nn, hvnn]
  -- ===== term 3:  −15ℓ₁³ℓ₂²(ℓ₂−ℓ₁)b₀²v²/d ;  |t3| ≤ (1/8)T  via 15ℓ₂|b₀|/d tiny =====
  -- ratio = 15 ℓ₂ |b₀| / d ;  bound 15 ℓ₂ |b₀| ≤ (1/8) d.
  have hsmall3 : 15 * ℓ₂ * |b₀| ≤ (1/8) * d := by
    -- ℓ₂ ≤ W = G U⁵ ;  |b₀| ≤ 3e12 B = 3e12 Δ²/(G Ω³) ;  d ≥ D = H Δ.
    -- 15·W·3e12 B = 45e12 G U⁵ · Δ²/(G Ω³) = 45e12 U⁵ Δ²/Ω³.
    -- (1/8) d ≥ (1/8) H Δ.  Want 45e12 U⁵ Δ²/Ω³ ≤ (1/8) H Δ ⟺ 360e12 U⁵ Δ ≤ H Ω³.
    -- hReg: Δ² U⁵ ≤ H Ω³.  Need 360e12 U⁵ Δ ≤ Δ² U⁵ ⟸ 360e12 ≤ Δ. true (Δ≥1e15).
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      rw [hBval] at hb0; exact hb0
    have hℓ2b0 : ℓ₂ * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
      mul_le_mul hℓ2W' hb0' hb0nn (by positivity)
    have heq : (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
        = 390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) := by field_simp; ring
    rw [heq] at hℓ2b0
    -- 15 ℓ₂ |b₀| ≤ 15·3e12·U⁵Δ²/Ω³ = 4.5e13 U⁵Δ²/Ω³
    have h15 : 15 * ℓ₂ * |b₀| ≤ 5850000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) := by
      nlinarith [hℓ2b0, hℓ2nn, hb0nn]
    refine le_trans h15 ?_
    -- 4.5e13 U⁵Δ²/Ω³ ≤ (1/8) d ;  d ≥ HΔ
    have hdge : P.H * S.Δ / 2 ≤ d := by rw [← hDval]; exact hdD
    -- suffices 4.5e13 U⁵Δ²/Ω³ ≤ (1/16) HΔ ≤ (1/8) d
    have hstep : 5850000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ≤ (1/16) * (P.H * S.Δ) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < S.Ω ^ 3)]
      -- 45e12 U⁵ Δ² ≤ (1/16) H Δ Ω³  ⟸ 720e12 U⁵ Δ ≤ H Ω³ via hReg, Δ≥720e12
      have hΔbd : (93600000000000000:ℝ) ≤ S.Δ :=
        by nlinarith [hΔbig, mul_pos hGpos (pow_pos hUpos 5), hGpos, pow_pos hUpos 5,
          one_le_pow₀ (n := 5) hU1, hG1]
      nlinarith [hReg, hΔbd, hΔpos, pow_pos hUpos 5, hHpos, pow_pos hΩpos 3,
        mul_pos hΔpos (pow_pos hUpos 5),
        mul_le_mul_of_nonneg_right hΔbd (by positivity : (0:ℝ) ≤ P.U ^ 5 * S.Δ)]
    linarith [hstep, hdge]
  -- term3 |t3| ≤ (1/8) T
  have ht3 : |(-15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2) / d| ≤ (1/8) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2
          = (-(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))) * (b₀ ^ 2 * v ^ 2) by ring,
      abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)), abs_mul,
      abs_pow, abs_of_nonneg (sq_nonneg v)]
    rw [div_le_iff₀ hd_pos, hTdef]
    -- 15ℓ₁³ℓ₂²(ℓ₂-ℓ₁)|b₀|²v² ≤ (1/8)·ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²·d
    -- = (1/8)·ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²·d ;  multiply hsmall3 (15ℓ₂|b₀|≤(1/8)d) by ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²? careful
    -- hsmall3·(ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²): LHS 15ℓ₂|b₀|·(ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²)=15ℓ₁³ℓ₂²(ℓ₂-ℓ₁)|b₀|²v²
    have hc : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hsmall3 hc, hℓ13nn, hℓ2nn, h21nn, hb0nn, sq_nonneg v]
  -- term4 |t4| ≤ (1/8) T ;  need 120 ℓ₂ |v| ≤ d
  have hsmall4 : 120 * ℓ₂ * |v| ≤ d := by
    -- ℓ₂ ≤ W=GU⁵ ; |v| ≤ M=1e20 ΔU⁵/Ω³ ; d ≥ HΔ.
    have hℓ2v : ℓ₂ * |v| ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) := by
      rw [← hMdef]; exact mul_le_mul hℓ2W' hv hvnn (by positivity)
    have h120 : 120 * ℓ₂ * |v| ≤ 120 * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) := by
      nlinarith [hℓ2v, hℓ2nn, hvnn]
    refine le_trans h120 ?_
    have hdge : P.H * S.Δ / 2 ≤ d := by rw [← hDval]; exact hdD
    refine le_trans ?_ hdge
    -- 120·GU⁵·1e20 ΔU⁵/Ω³ ≤ HΔ/2 ⟺ 2.4e22 G U¹⁰ ≤ HΩ³
    rw [show 120 * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
          = (156 * 10 ^ 22) * (P.G * P.U ^ 10) * S.Δ / S.Ω ^ 3 by field_simp; ring]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < S.Ω ^ 3)]
    -- 1.2e22 G U¹⁰ Δ ≤ (HΔ/2) Ω³ ⟸ 2.4e22 G U¹⁰ ≤ HΩ³ ⟸ via hReg Δ²U⁵≤HΩ³ and 2.4e22 GU⁵≤Δ²
    have hGU5Δ2 : (312 * 10 ^ 22 : ℝ) * (P.G * P.U ^ 5) ≤ S.Δ ^ 2 := by
      -- Δ ≥ 8e26 GU⁵, Δ≥1 ⟹ Δ² ≥ Δ·8e26 GU⁵ ≥ 8e26 GU⁵ ≥ 2.4e22 GU⁵
      have h1 : (8:ℝ) * 10 ^ 26 * (P.G * P.U ^ 5) ≤ S.Δ := hΔbig
      nlinarith [h1, hΔ1, mul_pos hGpos (pow_pos hUpos 5), hΔpos]
    have hkey : (312 * 10 ^ 22 : ℝ) * (P.G * P.U ^ 10) ≤ P.H * S.Ω ^ 3 := by
      -- 2.4e22 G U¹⁰ = (2.4e22 G U⁵)·U⁵ ≤ Δ²·U⁵ ≤ HΩ³
      have hm : (312 * 10 ^ 22 : ℝ) * (P.G * P.U ^ 5) * P.U ^ 5 ≤ S.Δ ^ 2 * P.U ^ 5 :=
        mul_le_mul_of_nonneg_right hGU5Δ2 (by positivity)
      have heq2 : (312 * 10 ^ 22 : ℝ) * (P.G * P.U ^ 5) * P.U ^ 5 = (312 * 10 ^ 22) * (P.G * P.U ^ 10) := by
        ring
      rw [heq2] at hm
      exact le_trans hm hReg
    nlinarith [hkey, hΔpos, mul_pos hGpos (pow_pos hUpos 10), hHpos, pow_pos hΩpos 3,
      mul_le_mul_of_nonneg_right hkey hΔpos.le]
  have ht4 : |(-5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3) / d| ≤ (1/8) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3
          = (-(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))) * (b₀ * v ^ 3) by ring,
      abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)), abs_mul]
    rw [show (v:ℝ) ^ 3 = v ^ 2 * v by ring, abs_mul, abs_pow]
    rw [div_le_iff₀ hd_pos, hTdef, hv2eq]
    -- |t4| = 5ℓ₁³ℓ₂(3ℓ₂-2ℓ₁)|b₀|·(|v|²|v|) ; goal ≤ (1/8)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²·d
    -- reduce: 5(3ℓ₂-2ℓ₁)|v| ≤ (1/8)(ℓ₂-ℓ₁)d ; 3ℓ₂-2ℓ₁≤3ℓ₂, (ℓ₂-ℓ₁)≥1, 120ℓ₂|v|≤d.
    have hred : 5 * (3 * ℓ₂ - 2 * ℓ₁) * |v| ≤ (1/8) * ((ℓ₂ - ℓ₁) * d) := by
      have h1 : 5 * (3 * ℓ₂ - 2 * ℓ₁) * |v| ≤ 15 * ℓ₂ * |v| := by
        apply mul_le_mul_of_nonneg_right _ hvnn; linarith
      have h2 : 15 * ℓ₂ * |v| ≤ (1/8) * d := by linarith [hsmall4]
      have h3 : (1/8) * d ≤ (1/8) * ((ℓ₂ - ℓ₁) * d) := by
        have : d ≤ (ℓ₂ - ℓ₁) * d := by nlinarith [h21, hd_pos.le]
        linarith
      linarith [h1, h2, h3]
    -- multiply hred by ℓ₁³ℓ₂|b₀||v|² (≥0)
    have hc : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * |b₀| * |v| ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hred hc, hℓ13nn, hℓ2nn, h21nn, hb0nn, hvnn,
      sq_nonneg (|v|)]
  -- term5 |t5| ≤ (1/8) T ;  need 40 |v|² ≤ |b₀| d
  have hsmall5 : 40 * |v| ^ 2 ≤ |b₀| * d := by
    -- |b₀| ≥ 16|v| (hbig_b0v) ;  d ≥ 120ℓ₂|v| ≥ 120|v| (ℓ₂≥1).
    have hdv : 120 * |v| ≤ d := by
      have : 120 * |v| ≤ 120 * ℓ₂ * |v| := by nlinarith [hvnn, hℓ2pos, hℓ12, hℓ1]
      linarith [this, hsmall4]
    nlinarith [hbig_b0v, hdv, hvnn, sq_nonneg (|v|), mul_nonneg hb0nn hd_pos.le]
  have ht5 : |(-(5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4) / d| ≤ (1/8) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -(5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4
          = (-((5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * v ^ 4 by ring,
      abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)), abs_pow]
    rw [div_le_iff₀ hd_pos, hTdef, hv2eq]
    -- |t5| = (5/2)ℓ₁³(2ℓ₂-ℓ₁)|v|⁴ ; goal ≤ (1/8)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²·d
    -- reduce: (5/2)(2ℓ₂-ℓ₁)|v|² ≤ (1/8)ℓ₂(ℓ₂-ℓ₁)|b₀|d ; (2ℓ₂-ℓ₁)≤2ℓ₂, (ℓ₂-ℓ₁)≥1, 40|v|²≤|b₀|d.
    have hred : (5/2) * (2 * ℓ₂ - ℓ₁) * |v| ^ 2 ≤ (1/8) * (ℓ₂ * (ℓ₂ - ℓ₁) * (|b₀| * d)) := by
      have h1 : (5/2) * (2 * ℓ₂ - ℓ₁) * |v| ^ 2 ≤ 5 * ℓ₂ * |v| ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); linarith
      have h2 : 5 * ℓ₂ * |v| ^ 2 ≤ 5 * ℓ₂ * ((|b₀| * d) / 40) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hsmall5]
      have h3 : 5 * ℓ₂ * ((|b₀| * d) / 40) ≤ (1/8) * (ℓ₂ * (ℓ₂ - ℓ₁) * (|b₀| * d)) := by
        rw [show (1/8) * (ℓ₂ * (ℓ₂ - ℓ₁) * (|b₀| * d)) = (ℓ₂ - ℓ₁) * (5 * ℓ₂ * ((|b₀| * d)/40)) by ring]
        nlinarith [h21, mul_nonneg hℓ2nn (mul_nonneg hb0nn hd_pos.le)]
      linarith [h1, h2, h3]
    -- multiply hred by ℓ₁³ (≥0)
    nlinarith [mul_le_mul_of_nonneg_left hred hℓ13nn, hℓ13nn]
  -- ===== assemble:  decompose Pone+Ptwo/d = M + (t1+t2+t3+t4+t5) =====
  -- name the five other monomials
  set t1 : ℝ := ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 with ht1def
  set t2 : ℝ := (-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v) / d with ht2def
  set t3 : ℝ := (-15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2) / d with ht3def
  set t4 : ℝ := (-5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3) / d with ht4def
  set t5 : ℝ := (-(5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4) / d with ht5def
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMmdef
  have hdecomp : Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - Mm = t1 + t2 + t3 + t4 + t5 := by
    rw [hMmdef, ht1def, ht2def, ht3def, ht4def, ht5def, Pone, Ptwo]; field_simp; ring
  -- |R| ≤ (1/8 + 1/2 + 1/8 + 1/8 + 1/8) T = (7/8) T ≤ T
  have hRabs : |t1 + t2 + t3 + t4 + t5| ≤ T := by
    have e1 : |t1 + t2 + t3 + t4 + t5| ≤ |t1 + t2 + t3 + t4| + |t5| := abs_add_le _ _
    have e2 : |t1 + t2 + t3 + t4| ≤ |t1 + t2 + t3| + |t4| := abs_add_le _ _
    have e3 : |t1 + t2 + t3| ≤ |t1 + t2| + |t3| := abs_add_le _ _
    have e4 : |t1 + t2| ≤ |t1| + |t2| := abs_add_le _ _
    linarith [e1, e2, e3, e4, ht1, ht2, ht3, ht4, ht5]
  rw [hdecomp]
  exact hRabs

set_option maxHeartbeats 3200000 in
/-- **§5 Step-4 magnitude foundation (v²-form, lower bound).**  With the local
cancellation-avoidance bound `hvlo`, the leading `b₀v²` monomial of `P₁` dominates
`|P₁+P₂/d|`.  Leading constant `1`. -/
theorem psum_abs_ge_v2 {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D / 2 ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2
      ≤ |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d| := by
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMm
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hT
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hres : |P0 - Mm| ≤ T :=
    psum_resid_le_v2 (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo hdD hd_pos hReg
      hG1 hU1 hUbig hDeW
  have hMabs : |Mm| = 3 * T := by
    rw [hMm, hT,
      show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
        = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  have htri : |Mm| - |P0 - Mm| ≤ |P0| := by
    have h := abs_sub_abs_le_abs_sub Mm (Mm - P0)
    rw [abs_sub_comm Mm P0] at h
    have h2 : Mm - (Mm - P0) = P0 := by ring
    rw [h2] at h; exact h
  rw [hMabs] at htri
  have hTnn : 0 ≤ T := by rw [hT]; positivity
  linarith [htri, hres, hTnn]

set_option maxHeartbeats 3200000 in
/-- **§5 Step-4 magnitude foundation (v²-form, upper bound).**  Companion of `psum_abs_ge_v2`:
the same five-monomial residual control gives `|P₁+P₂/d| ≤ 4·ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`. -/
theorem psum_abs_le_v2 {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D / 2 ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d|
      ≤ 4 * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2) := by
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMm
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hT
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hres : |P0 - Mm| ≤ T :=
    psum_resid_le_v2 (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo hdD hd_pos hReg
      hG1 hU1 hUbig hDeW
  have hMabs : |Mm| = 3 * T := by
    rw [hMm, hT,
      show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
        = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  have htri : |P0| ≤ |Mm| + |P0 - Mm| := by
    have h := abs_add_le (Mm) (P0 - Mm)
    have h2 : Mm + (P0 - Mm) = P0 := by ring
    rw [h2] at h; exact h
  rw [hMabs] at htri
  linarith [htri, hres]

/-- **§5 Step-4 large-defect cutoff `V₂`** (writeup 1025–1027).  The "sufficiently large `|v|`"
threshold that makes the `p₂/d`-linear monomial (the only `≍|s|` residual) negligible:
`V₂ := (Δ³/H)·G^{5/2}U^{45/2}/Ω⁶ + Δ^{1/2}·G²U¹⁰Ω`, with the half-integer powers encoded via
`Real.sqrt` (`G^{5/2}=G²√G`, `U^{45/2}=U²²√U`, `Δ^{1/2}=√Δ`). -/
noncomputable def V₂ (P : Globals) (S : Scale P) : ℝ :=
  (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U)) / S.Ω ^ 6
    + Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω)

set_option maxHeartbeats 12800000 in
/-- **§5 Step-4 SHARP magnitude residual (v²-form, large-defect cutoff).**  Under the writeup
cutoff `hVcut : V₂ ≤ |v|` (which forces `|v| ≫ floor`), *every* monomial of `P₁+P₂/d` other than
the leading `3·ℓ₁³ℓ₂(ℓ₂−ℓ₁)b₀v²` contributes a **truly small** fraction `≤ (1/10⁵⁰)·T` in total,
where `T := ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`.  Compared to `psum_resid_le_v2` (which only gives `≤ T`), the
`p₂`-linear monomial is killed by `hVcut` and the other four by the (already enormous) regime
slack `Δ ≥ 10¹⁵G⁴U²⁰`, `U ≥ 10³³`. -/
theorem psum_resid_le_sharp {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D / 2 ≤ d) (hd_pos : 0 < d)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2|
      ≤ (1 / 10 ^ 50) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2) := by
  -- positivity / basic facts
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1pos.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2pos.le
  have h21 : (1:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h21nn : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have h2ℓ1nn : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have h32ℓnn : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hℓ13pos : 0 < ℓ₁ ^ 3 := by positivity
  have hℓ13nn : 0 ≤ ℓ₁ ^ 3 := hℓ13pos.le
  have hv2eq : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  have hb02eq : b₀ ^ 2 = |b₀| ^ 2 := (sq_abs b₀).symm
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hDval : S.D = P.H * S.Δ := rfl
  have hΔ1 : (1:ℝ) ≤ S.Δ := by
    have : (10:ℝ) ^ 15 * (P.G ^ 4 * P.U ^ 20) ≥ 1 := by
      nlinarith [one_le_pow₀ (n := 4) hG1, one_le_pow₀ (n := 20) hU1]
    linarith [hDeW]
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  -- |M| = 3T
  have hMabs : |3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2| = 3 * T := by
    rw [hTdef]
    rw [show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
          = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
        abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  -- ===== HUGE-SLACK scale facts =====
  -- |b₀| ≥ B/2e6 = Δ²/(2e6 G Ω³)
  have hb0lo' : S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) ≤ |b₀| := by
    have : S.B / 2000000 = S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) := by
      rw [hBval]; field_simp
    rw [← this]; exact hb0lo
  have hb0pos : 0 < |b₀| := lt_of_lt_of_le (by positivity) hb0lo'
  set M : ℝ := 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) with hMdef
  -- chain:  4·10⁷⁸ GU⁵ ≤ Δ   (so 2·10⁵²|v| ≤ |b₀|)
  have hΔhuge : 4 * 10 ^ 78 * (P.G * P.U ^ 5) ≤ S.Δ := by
    have hU15 : (4:ℝ) * 10 ^ 78 ≤ P.U ^ 15 := by
      have h3 : ((10:ℝ) ^ 33) ^ 15 ≤ P.U ^ 15 := pow_le_pow_left₀ (by positivity) hUbig 15
      have h2 : ((10:ℝ) ^ 33) ^ 15 = (10:ℝ) ^ 495 := by rw [← pow_mul]
      calc (4:ℝ) * 10 ^ 78 ≤ (10:ℝ) ^ 79 := by norm_num
        _ ≤ (10:ℝ) ^ 495 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ = ((10:ℝ) ^ 33) ^ 15 := h2.symm
        _ ≤ P.U ^ 15 := h3
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    have step1 : 4 * 10 ^ 78 * (P.G * P.U ^ 5) ≤ P.U ^ 15 * (P.G * P.U ^ 5) :=
      mul_le_mul_of_nonneg_right hU15 (by positivity)
    have hGG : P.G ≤ 10 ^ 15 * P.G ^ 4 := by nlinarith [hG3, hGpos, pow_pos hGpos 4]
    have step2 : P.U ^ 15 * (P.G * P.U ^ 5) ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := by
      nlinarith [hGG, pow_pos hUpos 20, pow_pos hUpos 15, pow_pos hUpos 5]
    calc 4 * 10 ^ 78 * (P.G * P.U ^ 5) ≤ P.U ^ 15 * (P.G * P.U ^ 5) := step1
      _ ≤ 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) := step2
      _ ≤ S.Δ := hDeW
  -- 2·10⁵²·|v| ≤ |b₀|   (from 4·10⁷⁸ GU⁵ ≤ Δ)
  have hbig_b0v : 2 * 10 ^ 52 * |v| ≤ |b₀| := by
    have hMle : 2 * 10 ^ 52 * M ≤ S.Δ ^ 2 / (2000000 * (P.G * S.Ω ^ 3)) := by
      rw [hMdef, le_div_iff₀ (by positivity)]
      rw [show 2 * 10 ^ 52 * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) * (2000000 * (P.G * S.Ω ^ 3))
            = (4 * 10 ^ 78 * (P.G * P.U ^ 5)) * S.Δ * (S.Ω ^ 3 / S.Ω ^ 3) by
          field_simp; ring]
      rw [div_self (by positivity : (S.Ω:ℝ) ^ 3 ≠ 0), mul_one]
      calc (4 * 10 ^ 78 * (P.G * P.U ^ 5)) * S.Δ ≤ S.Δ * S.Δ :=
            mul_le_mul_of_nonneg_right hΔhuge hΔpos.le
        _ = S.Δ ^ 2 := by ring
    have hchain : 2 * 10 ^ 52 * M ≤ |b₀| := le_trans hMle hb0lo'
    calc 2 * 10 ^ 52 * |v| ≤ 2 * 10 ^ 52 * M :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ |b₀| := hchain
  -- ===== term 1:  ℓ₁³(2ℓ₂−ℓ₁)v³ ;  |t1| ≤ (1/10⁵¹) T  (ratio ≤ 2|v|/|b₀| ≪ 1) =====
  have ht1 : |ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3| ≤ (1 / 10 ^ 51) * T := by
    rw [show ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 = (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)) * v ^ 3 by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))]
    rw [show (v:ℝ) ^ 3 = v ^ 2 * v by ring, abs_mul, abs_pow]
    rw [hTdef, hv2eq]
    -- (2ℓ₂-ℓ₁)|v| ≤ (1/10⁵¹) ℓ₂(ℓ₂-ℓ₁)|b₀|  from  2·10⁵⁰|v| ≤ |b₀|, ℓ₂-ℓ₁≥1, 2ℓ₂-ℓ₁≤2ℓ₂.
    have hkey : (2 * ℓ₂ - ℓ₁) * |v| ≤ (1 / 10 ^ 51) * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀|) := by
      have h1 : (2 * ℓ₂ - ℓ₁) * |v| ≤ 2 * ℓ₂ * |v| :=
        mul_le_mul_of_nonneg_right (by linarith) hvnn
      have h2 : 2 * ℓ₂ * |v| ≤ 2 * ℓ₂ * (|b₀| / (2 * 10 ^ 52)) :=
        mul_le_mul_of_nonneg_left (by linarith [hbig_b0v]) (by positivity)
      have h3 : 2 * ℓ₂ * (|b₀| / (2 * 10 ^ 52)) ≤ (1 / 10 ^ 51) * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀|) := by
        rw [show (1 / 10 ^ 51) * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀|)
              = (ℓ₂ - ℓ₁) * (ℓ₂ * |b₀|) / 10 ^ 51 by ring,
          show 2 * ℓ₂ * (|b₀| / (2 * 10 ^ 52)) = (ℓ₂ * |b₀|) / 10 ^ 52 by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hℓ2nn hb0nn, h21,
          mul_nonneg (mul_nonneg hℓ2nn hb0nn) h21nn]
      linarith [h1, h2, h3]
    nlinarith [hkey, hℓ13pos, sq_nonneg (|v|), mul_nonneg hℓ13nn (sq_nonneg (|v|)),
      mul_pos hℓ13pos (by positivity : (0:ℝ) < |v| ^ 2 + 1)]
  -- ===== term 2:  −5ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²b₀³v/d ;  |t2| ≤ (1/10⁵¹) T  via the LARGE-DEFECT CUTOFF =====
  -- ratio = (1/2)·floor/|v| with floor = 10ℓ₂(ℓ₂-ℓ₁)b₀²/d.  hVcut ⟹ floor/|v| ≪ 1.
  -- We need 5ℓ₂(ℓ₂-ℓ₁)|b₀|²/d ≤ (1/10⁵¹)|v|, i.e. 5·10⁵¹·ℓ₂(ℓ₂-ℓ₁)|b₀|² ≤ |v|·d.
  have ht2 : |(-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v) / d| ≤ (1 / 10 ^ 51) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v
          = (-(5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)) * (b₀ ^ 3 * v) by ring,
      abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2),
      abs_mul]
    rw [show |b₀ ^ 3| = |b₀| ^ 3 by rw [abs_pow]]
    rw [div_le_iff₀ hd_pos, hTdef, hv2eq]
    -- goal: 5ℓ₁³ℓ₂²(ℓ₂-ℓ₁)²|b₀|³|v| ≤ (1/10⁵¹)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v|²·d
    -- floor bound:  5·10⁵¹·ℓ₂(ℓ₂-ℓ₁)|b₀|² ≤ |v|·d
    have hfloor : 5 * 10 ^ 51 * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| ^ 2) ≤ |v| * d := by
      -- floor ≤ 5·10⁵¹·ℓ₂(ℓ₂-ℓ₁)|b₀|² ≤ (writeup V₂-term1) · d ≤ |v| · d
      -- bound the LHS by polynomial scale facts, the RHS using d ≥ HΔ and |v| ≥ V₂.
      -- Step A: ℓ₂(ℓ₂-ℓ₁)|b₀|² ≤ (GU⁵)²·(3e12 Δ²/(GΩ³))² = 9e24 U¹⁰Δ⁴/Ω⁶
      have hℓ2sq : ℓ₂ * (ℓ₂ - ℓ₁) ≤ (130 * (P.G * P.U ^ 5)) ^ 2 := by nlinarith [hℓ2W', h21, hℓ2pos, hℓ12]
      have hb0sq : |b₀| ^ 2 ≤ (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) ^ 2 := by
        have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
          rw [hBval] at hb0; exact hb0
        nlinarith [hb0', hb0nn,
          (by positivity : (0:ℝ) ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))]
      have hfl : ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| ^ 2
          ≤ 1521 * 10 ^ 26 * (P.U ^ 10 * S.Δ ^ 4 / S.Ω ^ 6) := by
        have hmul := mul_le_mul hℓ2sq hb0sq (by positivity) (by positivity)
        have heq : (130 * (P.G * P.U ^ 5)) ^ 2 * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) ^ 2
            = 1521 * 10 ^ 26 * (P.U ^ 10 * S.Δ ^ 4 / S.Ω ^ 6) := by field_simp; ring
        rw [heq] at hmul; exact hmul
      -- Step B: V₂-term1 ≥ Δ³U²²/(HΩ⁶)  (drop √G,√U ≥ 1) ;  and |v| ≥ V₂ ≥ V₂-term1.
      have hsqG : (1:ℝ) ≤ Real.sqrt P.G := by
        rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hG1
      have hsqU : (1:ℝ) ≤ Real.sqrt P.U := by
        rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hU1
      have hV2t1 : S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6) ≤ V₂ P S := by
        rw [V₂]
        have hterm1 : S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6)
            ≤ (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U)) / S.Ω ^ 6 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          -- Δ³U²²·(HΩ⁶) ≤ (Δ³/H)·(G²√G·U²²√U)·Ω⁶·(HΩ⁶) ;  drop using G²√G√U ≥ 1
          have hfac : (1:ℝ) ≤ P.G ^ 2 * Real.sqrt P.G * Real.sqrt P.U := by
            have hG2 : (1:ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
            have hp1 : (1:ℝ) ≤ P.G ^ 2 * Real.sqrt P.G := by
              nlinarith [hG2, hsqG, (pow_pos hGpos 2).le, Real.sqrt_nonneg P.G]
            nlinarith [hp1, hsqU, mul_nonneg (pow_pos hGpos 2).le (Real.sqrt_nonneg P.G),
              Real.sqrt_nonneg P.U]
          have hRHSeq : (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
                * (P.H * S.Ω ^ 6)
              = (S.Δ ^ 3 * P.U ^ 22 * S.Ω ^ 6) * (P.G ^ 2 * Real.sqrt P.G * Real.sqrt P.U) := by
            field_simp [hHpos.ne']
            try ring
          rw [hRHSeq]
          exact le_mul_of_one_le_right (by positivity) hfac
        have hpos2 : 0 ≤ Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω) := by positivity
        linarith [hterm1, hpos2]
      -- |v| ≥ Δ³U²²/(HΩ⁶)
      have hvlo2 : S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6) ≤ |v| := le_trans hV2t1 hVcut
      have hdge : P.H * S.Δ / 2 ≤ d := by rw [← hDval]; exact hdD
      have hvd : S.Δ ^ 4 * P.U ^ 22 / S.Ω ^ 6 / 2 ≤ |v| * d := by
        have hstep := mul_le_mul hvlo2 hdge (by positivity) hvnn
        have heq : (S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6)) * (P.H * S.Δ / 2)
            = S.Δ ^ 4 * P.U ^ 22 / S.Ω ^ 6 / 2 := by field_simp
        rw [heq] at hstep; exact hstep
      -- 5·10⁵¹·(ℓ₂(ℓ₂-ℓ₁)|b₀|²) ≤ 5·10⁵¹·(9e24 U¹⁰Δ⁴/Ω⁶) ≤ Δ⁴U²²/(2Ω⁶) ≤ |v|·d
      refine le_trans ?_ hvd
      refine le_trans (mul_le_mul_of_nonneg_left hfl (by positivity)) ?_
      -- 5·10⁵¹·(9e24 U¹⁰Δ⁴/Ω⁶) ≤ Δ⁴U²²/(2Ω⁶)  ⟺ 9e76 ≤ U¹².
      have hU12 : (1521:ℝ) * 10 ^ 78 ≤ P.U ^ 12 := by
        have h3 : ((10:ℝ) ^ 33) ^ 12 ≤ P.U ^ 12 := pow_le_pow_left₀ (by positivity) hUbig 12
        have h2 : ((10:ℝ) ^ 33) ^ 12 = (10:ℝ) ^ 396 := by rw [← pow_mul]
        calc (1521:ℝ) * 10 ^ 78 ≤ (10:ℝ) ^ 82 := by norm_num
          _ ≤ (10:ℝ) ^ 396 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ = ((10:ℝ) ^ 33) ^ 12 := h2.symm
          _ ≤ P.U ^ 12 := h3
      calc 5 * 10 ^ 51 * (1521 * 10 ^ 26 * (P.U ^ 10 * S.Δ ^ 4 / S.Ω ^ 6))
          = (1521 * 10 ^ 78) * P.U ^ 10 * (S.Δ ^ 4 / S.Ω ^ 6) / 2 := by ring
        _ ≤ P.U ^ 12 * P.U ^ 10 * (S.Δ ^ 4 / S.Ω ^ 6) / 2 := by
            have hx : (0:ℝ) ≤ P.U ^ 10 * (S.Δ ^ 4 / S.Ω ^ 6) := by positivity
            nlinarith [mul_nonneg (sub_nonneg.mpr hU12) hx]
        _ = S.Δ ^ 4 * P.U ^ 22 / S.Ω ^ 6 / 2 := by rw [← pow_add]; ring
    -- multiply hfloor by (1/(2·10⁵¹))·ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀||v| ≥0
    have hcoef : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * |v| := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hfloor (by positivity :
      (0:ℝ) ≤ (1 / (2 * 10 ^ 51)) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * |v|)),
      hℓ13nn, hℓ2nn, h21nn, hb0nn, hvnn]
  -- ===== term 3:  −15ℓ₁³ℓ₂²(ℓ₂−ℓ₁)b₀²v²/d ;  |t3| ≤ (1/10⁵¹) T  (15ℓ₂|b₀| ≤ d/10⁵¹) =====
  have hsmall3 : 15 * 10 ^ 51 * (ℓ₂ * |b₀|) ≤ d := by
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      rw [hBval] at hb0; exact hb0
    have hℓ2b0 : ℓ₂ * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
      mul_le_mul hℓ2W' hb0' hb0nn (by positivity)
    have heq : (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))
        = 390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) := by field_simp; ring
    rw [heq] at hℓ2b0
    have h15 : 15 * 10 ^ 51 * (ℓ₂ * |b₀|)
        ≤ 15 * 10 ^ 51 * (390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3)) :=
      mul_le_mul_of_nonneg_left hℓ2b0 (by positivity)
    refine le_trans h15 ?_
    have hdge : P.H * S.Δ / 2 ≤ d := by rw [← hDval]; exact hdD
    refine le_trans ?_ hdge
    -- 4.5e64 U⁵Δ²/Ω³ ≤ HΔ/2 ⟺ 9e64 U⁵Δ ≤ HΩ³ ⟸ via hReg Δ²U⁵≤HΩ³ and 9e67 ≤ Δ
    rw [show 15 * 10 ^ 51 * (390000000000000 * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3))
          = (585 * 10 ^ 64) * (P.U ^ 5 * S.Δ ^ 2) / S.Ω ^ 3 by ring]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < S.Ω ^ 3)]
    have hΔbd : (90000000000000000000000000000000000000000000000000000000000000000000:ℝ) ≤ S.Δ := by
      -- Δ ≥ 10¹⁵ G⁴U²⁰ ≥ 10¹⁵·U²⁰ ≥ 10¹⁵·10^660 = 10^675 ≫ 4.5e64
      have hU20 : (10:ℝ) ^ 660 ≤ P.U ^ 20 := by
        have h3 : ((10:ℝ) ^ 33) ^ 20 ≤ P.U ^ 20 := pow_le_pow_left₀ (by positivity) hUbig 20
        have h2 : ((10:ℝ) ^ 33) ^ 20 = (10:ℝ) ^ 660 := by rw [← pow_mul]
        rw [h2] at h3; exact h3
      have hG4 : (1:ℝ) ≤ P.G ^ 4 := one_le_pow₀ hG1
      nlinarith [hDeW, hU20, hG4, pow_pos hUpos 20]
    nlinarith [hReg, hΔbd, hΔpos, pow_pos hUpos 5, hHpos, pow_pos hΩpos 3,
      mul_pos hΔpos (pow_pos hUpos 5),
      mul_le_mul_of_nonneg_right hΔbd (by positivity : (0:ℝ) ≤ P.U ^ 5 * S.Δ)]
  have ht3 : |(-15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2) / d| ≤ (1 / 10 ^ 51) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2
          = (-(15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))) * (b₀ ^ 2 * v ^ 2) by ring,
      abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁)), abs_mul,
      abs_pow, abs_of_nonneg (sq_nonneg v)]
    rw [div_le_iff₀ hd_pos, hTdef]
    -- 15ℓ₁³ℓ₂²(ℓ₂-ℓ₁)|b₀|²v² ≤ (1/10⁵¹)ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²·d
    -- = use hsmall3 : 15·10⁵¹ ℓ₂|b₀| ≤ d, times ℓ₁³ℓ₂(ℓ₂-ℓ₁)|b₀|v²/10⁵¹
    have hc : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hsmall3 (by positivity :
      (0:ℝ) ≤ (1 / 10 ^ 51) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2)),
      hℓ13nn, hℓ2nn, h21nn, hb0nn, sq_nonneg v]
  -- ===== term 4:  −5ℓ₁³ℓ₂(3ℓ₂−2ℓ₁)b₀v³/d ;  |t4| ≤ (1/10⁵¹) T  (120·10⁵¹ ℓ₂|v| ≤ d) =====
  have hsmall4 : 120 * 10 ^ 51 * (ℓ₂ * |v|) ≤ d := by
    have hℓ2v : ℓ₂ * |v| ≤ (130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)) := by
      rw [← hMdef]; exact mul_le_mul hℓ2W' hv hvnn (by positivity)
    have h120 : 120 * 10 ^ 51 * (ℓ₂ * |v|)
        ≤ 120 * 10 ^ 51 * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))) :=
      mul_le_mul_of_nonneg_left hℓ2v (by positivity)
    refine le_trans h120 ?_
    have hdge : P.H * S.Δ / 2 ≤ d := by rw [← hDval]; exact hdD
    refine le_trans ?_ hdge
    rw [show 120 * 10 ^ 51 * ((130 * (P.G * P.U ^ 5)) * (10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3)))
          = (156 * 10 ^ 73) * (P.G * P.U ^ 10) * S.Δ / S.Ω ^ 3 by field_simp; ring]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < S.Ω ^ 3)]
    have hGU5Δ2 : (312 * 10 ^ 73 : ℝ) * (P.G * P.U ^ 5) ≤ S.Δ ^ 2 := by
      have h1 : (4:ℝ) * 10 ^ 78 * (P.G * P.U ^ 5) ≤ S.Δ := hΔhuge
      nlinarith [h1, hΔ1, mul_pos hGpos (pow_pos hUpos 5), hΔpos]
    have hkey : (312 * 10 ^ 73 : ℝ) * (P.G * P.U ^ 10) ≤ P.H * S.Ω ^ 3 := by
      have hm : (312 * 10 ^ 73 : ℝ) * (P.G * P.U ^ 5) * P.U ^ 5 ≤ S.Δ ^ 2 * P.U ^ 5 :=
        mul_le_mul_of_nonneg_right hGU5Δ2 (by positivity)
      have heq2 : (312 * 10 ^ 73 : ℝ) * (P.G * P.U ^ 5) * P.U ^ 5
          = (312 * 10 ^ 73) * (P.G * P.U ^ 10) := by ring
      rw [heq2] at hm
      exact le_trans hm hReg
    nlinarith [hkey, hΔpos, mul_pos hGpos (pow_pos hUpos 10), hHpos, pow_pos hΩpos 3,
      mul_le_mul_of_nonneg_right hkey hΔpos.le]
  have ht4 : |(-5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3) / d| ≤ (1 / 10 ^ 51) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3
          = (-(5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁))) * (b₀ * v ^ 3) by ring,
      abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁)), abs_mul]
    rw [show (v:ℝ) ^ 3 = v ^ 2 * v by ring, abs_mul, abs_pow]
    rw [div_le_iff₀ hd_pos, hTdef, hv2eq]
    -- 5(3ℓ₂-2ℓ₁)|v| ≤ (1/10⁵¹)(ℓ₂-ℓ₁)d ; 3ℓ₂-2ℓ₁≤3ℓ₂, (ℓ₂-ℓ₁)≥1, 120·10⁵¹ℓ₂|v|≤d.
    have hred : 5 * (3 * ℓ₂ - 2 * ℓ₁) * |v| ≤ (1 / 10 ^ 51) * ((ℓ₂ - ℓ₁) * d) := by
      have h1 : 5 * (3 * ℓ₂ - 2 * ℓ₁) * |v| ≤ 15 * ℓ₂ * |v| :=
        mul_le_mul_of_nonneg_right (by linarith) hvnn
      have h2 : 15 * ℓ₂ * |v| ≤ (1 / 10 ^ 51) * d := by
        rw [show (1 / 10 ^ 51) * d = (1 / 10 ^ 51) * d by rfl]
        nlinarith [hsmall4, hvnn, hℓ2nn]
      have h3 : (1 / 10 ^ 51) * d ≤ (1 / 10 ^ 51) * ((ℓ₂ - ℓ₁) * d) := by
        have : d ≤ (ℓ₂ - ℓ₁) * d := by nlinarith [h21, hd_pos.le]
        nlinarith [this]
      linarith [h1, h2, h3]
    have hc : (0:ℝ) ≤ ℓ₁ ^ 3 * ℓ₂ * |b₀| * |v| ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hred hc, hℓ13nn, hℓ2nn, h21nn, hb0nn, hvnn,
      sq_nonneg (|v|)]
  -- ===== term 5:  −(5/2)ℓ₁³(2ℓ₂−ℓ₁)v⁴/d ;  |t5| ≤ (1/10⁵¹) T  (40·10⁵¹|v|² ≤ |b₀|d) =====
  have hsmall5 : 40 * 10 ^ 51 * |v| ^ 2 ≤ |b₀| * d := by
    have hdv : 120 * 10 ^ 51 * |v| ≤ d := by
      have : 120 * 10 ^ 51 * |v| ≤ 120 * 10 ^ 51 * (ℓ₂ * |v|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hvnn, hℓ2pos, hℓ12, hℓ1]
      linarith [this, hsmall4]
    nlinarith [hbig_b0v, hdv, hvnn, sq_nonneg (|v|), mul_nonneg hb0nn hd_pos.le]
  have ht5 : |(-(5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4) / d| ≤ (1 / 10 ^ 51) * T := by
    rw [abs_div, abs_of_pos hd_pos]
    rw [show -(5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4
          = (-((5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁))) * v ^ 4 by ring,
      abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)), abs_pow]
    rw [div_le_iff₀ hd_pos, hTdef, hv2eq]
    have hred : (5/2) * (2 * ℓ₂ - ℓ₁) * |v| ^ 2
        ≤ (1 / 10 ^ 51) * (ℓ₂ * (ℓ₂ - ℓ₁) * (|b₀| * d)) := by
      have h1 : (5/2) * (2 * ℓ₂ - ℓ₁) * |v| ^ 2 ≤ 5 * ℓ₂ * |v| ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have h2 : 5 * ℓ₂ * |v| ^ 2 ≤ 5 * ℓ₂ * ((|b₀| * d) / (8 * 10 ^ 51)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [le_div_iff₀ (by positivity)]; nlinarith [hsmall5]
      have h3 : 5 * ℓ₂ * ((|b₀| * d) / (8 * 10 ^ 51))
          ≤ (1 / 10 ^ 51) * (ℓ₂ * (ℓ₂ - ℓ₁) * (|b₀| * d)) := by
        rw [show (1 / 10 ^ 51) * (ℓ₂ * (ℓ₂ - ℓ₁) * (|b₀| * d))
              = (ℓ₂ - ℓ₁) * (5 * ℓ₂ * ((|b₀| * d) / (8 * 10 ^ 51))) * (8/5) by ring]
        nlinarith [h21, mul_nonneg hℓ2nn (mul_nonneg hb0nn hd_pos.le),
          mul_nonneg (mul_nonneg hℓ2nn (mul_nonneg hb0nn hd_pos.le)) h21nn]
      linarith [h1, h2, h3]
    nlinarith [mul_le_mul_of_nonneg_left hred hℓ13nn, hℓ13nn]
  -- ===== assemble =====
  set t1 : ℝ := ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 3 with ht1def
  set t2 : ℝ := (-5 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 * b₀ ^ 3 * v) / d with ht2def
  set t3 : ℝ := (-15 * ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) * b₀ ^ 2 * v ^ 2) / d with ht3def
  set t4 : ℝ := (-5 * ℓ₁ ^ 3 * ℓ₂ * (3 * ℓ₂ - 2 * ℓ₁) * b₀ * v ^ 3) / d with ht4def
  set t5 : ℝ := (-(5/2) * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * v ^ 4) / d with ht5def
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMmdef
  have hdecomp : Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d - Mm = t1 + t2 + t3 + t4 + t5 := by
    rw [hMmdef, ht1def, ht2def, ht3def, ht4def, ht5def, Pone, Ptwo]; field_simp; ring
  have hRabs : |t1 + t2 + t3 + t4 + t5| ≤ (1 / 10 ^ 50) * T := by
    have e1 : |t1 + t2 + t3 + t4 + t5| ≤ |t1 + t2 + t3 + t4| + |t5| := abs_add_le _ _
    have e2 : |t1 + t2 + t3 + t4| ≤ |t1 + t2 + t3| + |t4| := abs_add_le _ _
    have e3 : |t1 + t2 + t3| ≤ |t1 + t2| + |t3| := abs_add_le _ _
    have e4 : |t1 + t2| ≤ |t1| + |t2| := abs_add_le _ _
    -- 5·(1/10⁵¹) T = (1/(2·10⁵⁰)) T ≤ (1/10⁵⁰) T
    nlinarith [e1, e2, e3, e4, ht1, ht2, ht3, ht4, ht5, hTnn]
  rw [hMmdef] at hdecomp
  rw [hdecomp]
  exact hRabs

/-- **§5 Step-4: the large-defect cutoff implies the cancellation-avoidance floor.**
Under the writeup cutoff `hVcut : V₂ ≤ |v|`, the local floor
`10·ℓ₂(ℓ₂−ℓ₁)b₀²/d ≤ |v|` (the `hvlo` of the v²-form magnitude lemmas) holds automatically:
`10·ℓ₂(ℓ₂−ℓ₁)b₀² ≤ 9·10²⁵·U¹⁰Δ⁴/Ω⁶ ≤ Δ⁴U²²/Ω⁶ ≤ V₂·d ≤ |v|·d` (using `ℓ₂ ≤ GU⁵`,
`|b₀| ≤ 3·10¹²B`, `d ≥ D = HΔ`, `U ≥ 10³³`). -/
theorem vlo_of_vcut {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D / 2 ≤ d) (hd_pos : 0 < d)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v| := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21 : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hBval : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
  have hDval : S.D = P.H * S.Δ := rfl
  -- Step A:  ℓ₂(ℓ₂−ℓ₁)|b₀|² ≤ 9·10²⁴·U¹⁰Δ⁴/Ω⁶
  have hℓ2sq : ℓ₂ * (ℓ₂ - ℓ₁) ≤ (130 * (P.G * P.U ^ 5)) ^ 2 := by nlinarith [hℓ2W', h21, hℓ2pos, hℓ12]
  have hb0sq : |b₀| ^ 2 ≤ (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) ^ 2 := by
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      rw [hBval] at hb0; exact hb0
    nlinarith [hb0', hb0nn,
      (by positivity : (0:ℝ) ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)))]
  have hfl : ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| ^ 2 ≤ 1521 * 10 ^ 26 * (P.U ^ 10 * S.Δ ^ 4 / S.Ω ^ 6) := by
    have hmul := mul_le_mul hℓ2sq hb0sq (by positivity) (by positivity)
    have heq : (130 * (P.G * P.U ^ 5)) ^ 2 * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) ^ 2
        = 1521 * 10 ^ 26 * (P.U ^ 10 * S.Δ ^ 4 / S.Ω ^ 6) := by field_simp; ring
    rw [heq] at hmul; exact hmul
  -- Step B:  V₂-term1 ≥ Δ³U²²/(HΩ⁶), so |v|·d ≥ Δ⁴U²²/Ω⁶
  have hsqG : (1:ℝ) ≤ Real.sqrt P.G := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hG1
  have hsqU : (1:ℝ) ≤ Real.sqrt P.U := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hU1
  have hV2t1 : S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6) ≤ V₂ P S := by
    rw [V₂]
    have hterm1 : S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6)
        ≤ (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U)) / S.Ω ^ 6 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hfac : (1:ℝ) ≤ P.G ^ 2 * Real.sqrt P.G * Real.sqrt P.U := by
        have hG2 : (1:ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
        have hp1 : (1:ℝ) ≤ P.G ^ 2 * Real.sqrt P.G := by
          nlinarith [hG2, hsqG, (pow_pos hGpos 2).le, Real.sqrt_nonneg P.G]
        nlinarith [hp1, hsqU, mul_nonneg (pow_pos hGpos 2).le (Real.sqrt_nonneg P.G),
          Real.sqrt_nonneg P.U]
      have hRHSeq : (S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
            * (P.H * S.Ω ^ 6)
          = (S.Δ ^ 3 * P.U ^ 22 * S.Ω ^ 6) * (P.G ^ 2 * Real.sqrt P.G * Real.sqrt P.U) := by
        field_simp [hHpos.ne']
        try ring
      rw [hRHSeq]
      exact le_mul_of_one_le_right (by positivity) hfac
    have hpos2 : 0 ≤ Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω) := by positivity
    linarith [hterm1, hpos2]
  have hvlo2 : S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6) ≤ |v| := le_trans hV2t1 hVcut
  have hdge : P.H * S.Δ / 2 ≤ d := by rw [← hDval]; exact hdD
  have hvd : S.Δ ^ 4 * P.U ^ 22 / S.Ω ^ 6 / 2 ≤ |v| * d := by
    have hstep := mul_le_mul hvlo2 hdge (by positivity) hvnn
    have heq : (S.Δ ^ 3 * P.U ^ 22 / (P.H * S.Ω ^ 6)) * (P.H * S.Δ / 2)
        = S.Δ ^ 4 * P.U ^ 22 / S.Ω ^ 6 / 2 := by field_simp
    rw [heq] at hstep; exact hstep
  -- Step C:  10·(9·10²⁴·U¹⁰Δ⁴/Ω⁶) ≤ Δ⁴U²²/(2Ω⁶)  (⟸ 18·10²⁵ ≤ U¹²)
  have hU12 : (3042:ℝ) * 10 ^ 27 ≤ P.U ^ 12 := by
    have h3 : ((10:ℝ) ^ 33) ^ 12 ≤ P.U ^ 12 := pow_le_pow_left₀ (by positivity) hUbig 12
    have h2 : ((10:ℝ) ^ 33) ^ 12 = (10:ℝ) ^ 396 := by rw [← pow_mul]
    calc (3042:ℝ) * 10 ^ 27 ≤ (10:ℝ) ^ 31 := by norm_num
      _ ≤ (10:ℝ) ^ 396 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((10:ℝ) ^ 33) ^ 12 := h2.symm
      _ ≤ P.U ^ 12 := h3
  -- assemble:  10·ℓ₂(ℓ₂−ℓ₁)b₀² ≤ |v|·d, then divide by d
  have hkey : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2) ≤ |v| * d := by
    have hb02 : b₀ ^ 2 = |b₀| ^ 2 := (sq_abs b₀).symm
    rw [hb02]
    calc 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| ^ 2)
        ≤ 10 * (1521 * 10 ^ 26 * (P.U ^ 10 * S.Δ ^ 4 / S.Ω ^ 6)) := by
          apply mul_le_mul_of_nonneg_left hfl (by norm_num)
      _ = (3042 * 10 ^ 27) * P.U ^ 10 * (S.Δ ^ 4 / S.Ω ^ 6) / 2 := by ring
      _ ≤ P.U ^ 12 * P.U ^ 10 * (S.Δ ^ 4 / S.Ω ^ 6) / 2 := by
          have hx : (0:ℝ) ≤ P.U ^ 10 * (S.Δ ^ 4 / S.Ω ^ 6) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hU12) hx]
      _ = S.Δ ^ 4 * P.U ^ 22 / S.Ω ^ 6 / 2 := by rw [← pow_add]; ring
      _ ≤ |v| * d := hvd
  rw [show 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) = 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2) / d by ring,
    div_le_iff₀ hd_pos]
  linarith [hkey]

end Squarefree
