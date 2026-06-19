import Squarefree.Lower.UpsilonExtract
import Squarefree.Lower.UpsilonErr
import Squarefree.Lower.UpsilonMag

/-!
# §5 Step-4 s-extraction from witnesses (writeup 1033–1043)

`Upsilon_s_extract_of_witness` discharges the magnitude inputs of the rounding core
(`round_extract_core`) directly from the §5 scale lemmas, so the caller only has to supply the
two *witness* facts that come verbatim from `Upsilon_expand` / `Upsilon_near_int`:

* `hexp : |Υval − Lval| ≤ 10¹¹⁰·UpsT`  — the collapsed expansion error
  (`Upsilon_expand` composed with `upsilon_err_le`, `Lval` = the leading cubic/quartic value);
* `hnearbd : distInt Υval ≤ 45·Wval⁴/Δ` — the near-integer bound (`Upsilon_near_int`, using
  `D = HΔ` so `45·Wval⁴·H/D = 45·Wval⁴/Δ`).

The three magnitude inequalities are then automatic from the per-`r` scale hypotheses:

* `hNBsmall : 45·Wval⁴/Δ < ¼`  ⟸  `hDeW : 10¹⁵·G⁴U²⁰ ≤ Δ` (since `Wval⁴ = G⁴U²⁰`);
* `hLlo : 1 + 10¹¹⁰·UpsT ≤ |Lval|`  is **exactly** `leading_abs_ge`;
* `hLhi : |Lval| + 10¹¹⁰·UpsT + 1 ≤ 10¹¹¹·(G⁵U³⁵/Ω⁸)`  from `leading_abs_le`
  (`|Lval| ≤ 10⁸⁵·(G⁵U³⁵/Ω⁸)`) and `10¹¹⁰·UpsT ≤ 10¹¹⁰·(G⁵U³⁵/Ω⁸)` (`UpsT ≤ G⁵U³⁵/Ω⁸` from
  `hReg²`); the two pieces fit inside `10¹¹¹·(G⁵U³⁵/Ω⁸)`.

**Note on the budget constant.** The writeup states `1 ≤ |s| ≪ G⁵U³⁵/Ω⁸` (writeup 1035) with an
absolute `≪`-constant.  Made explicit, the constant that absorbs the expansion error `ERR` (which
is itself of size up to `10¹¹⁰·G⁵U³⁵/Ω⁸` in the worst X-large regime) is `10¹¹¹`, **not** the
`10⁸⁵` that bounds the leading value `|Lval|` alone (`leading_abs_le`).  The earlier scaffold
`Upsilon_s_extract` (UpsilonExtract.lean) used `10⁸⁵` for `Bnd`, which is too small to also absorb
`ERR + 1`; this from-witness form uses the correct `10¹¹¹`.
-/

namespace Squarefree

open Squarefree.Counting

set_option maxHeartbeats 1600000

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 integer extraction from witnesses** (writeup 1033–1043).  Given the two witness
facts `hexp`/`hnearbd` (verbatim conclusions of `Upsilon_expand`∘`upsilon_err_le` and
`Upsilon_near_int`) and the per-`r` scale hypotheses, the near-integer `Υval` rounds to a
**nonzero** integer `s` with `1 ≤ |s| ≤ 10¹¹¹·(G⁵U³⁵/Ω⁸)` and `|Υval − s| ≤ 45·Wval⁴/Δ`. -/
theorem Upsilon_s_extract_of_witness {a : ℝ} {ℓ₁ ℓ₂ b₀ v d Υval : ℝ}
    -- the two witness facts
    (hexp : |Υval - Lval P.X a d b₀ v ℓ₁ ℓ₂| ≤ 10 ^ 119 * UpsT P S)
    (hnearbd : distInt Υval ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ)
    -- per-`r` scale hypotheses (shared by `leading_abs_le` / `leading_abs_ge`)
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΩH : 55 * S.Ω ≤ P.H) (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hv2 : 2340000000000000 * (S.Δ ^ 2 * P.U ^ 5 / S.Ω ^ 3) ≤ |v|) :
    ∃ s : ℤ, s ≠ 0
      ∧ |(s : ℝ)| ≤ 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
      ∧ |Υval - (s : ℝ)| ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ := by
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hHpos : 0 < P.H := P.H_pos
  -- the two magnitude facts from the scale lemmas
  have hLlo : 1 + 10 ^ 119 * UpsT P S ≤ |Lval P.X a d b₀ v ℓ₁ ℓ₂| := by
    have := leading_abs_ge (S := S) (a := a) (b₀ := b₀) (v := v) (d := d)
      hAD ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ2W hdwin hb0 hv h1 hband hG1 hU1 hΔ1 hH1
      hΩU hUbig hΩH hDeW hv2
    simpa only [UpsT] using this
  have hLhi0 : |Lval P.X a d b₀ v ℓ₁ ℓ₂| ≤ 10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) :=
    leading_abs_le (S := S) (a := a) (b₀ := b₀) (v := v) (d := d)
      hAD ha0 ha_hi (lt_of_lt_of_le one_pos hℓ1) hℓ12 hℓ2W
      ⟨S.D_eps_lo hdwin.1, S.D_eps_hi hdwin.2⟩ hb0 hv
      h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
  -- regime: Δ²U⁵ ≤ HΩ³  (same chain as in the scale lemmas)
  have hGU5Ω3 : (1 : ℝ) ≤ P.G * P.U ^ 5 * S.Ω ^ 3 := by
    have hU2Ω : P.U ≤ P.U ^ 2 / S.Ω := by
      rw [le_div_iff₀ hΩpos]; nlinarith [hΩU, hUpos.le, hU1]
    have hfactor : P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) = P.G * P.U ^ 5 * S.Ω ^ 3 := by
      field_simp
    have hchain : (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) := by
      calc (1 : ℝ) ≤ P.U := hU1
        _ ≤ P.U ^ 2 / S.Ω := hU2Ω
        _ = 1 * (P.U ^ 2 / S.Ω) := by ring
        _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) :=
            mul_le_mul_of_nonneg_right hband (by positivity)
    rwa [hfactor] at hchain
  have hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3 := by
    have hHbig : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
      (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
    have hstep : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3) ≤ P.H * S.Ω ^ 3 := by
      have heq : S.Δ ^ 2 * P.U ^ 5 * (P.G * P.U ^ 5 * S.Ω ^ 3)
          = (P.G * P.U ^ 10 * S.Δ ^ 2) * S.Ω ^ 3 := by ring
      rw [heq]; exact mul_le_mul_of_nonneg_right hHbig (by positivity)
    nlinarith [hGU5Ω3, hstep, mul_pos (by positivity : (0:ℝ) < S.Δ ^ 2) (by positivity : (0:ℝ) < P.U ^ 5)]
  -- ERR = 10¹¹⁰·UpsT ≤ 10¹¹⁰·(G⁵U³⁵/Ω⁸)  (from UpsT ≤ G⁵U³⁵/Ω⁸ via hReg²)
  have hUpsT_le : UpsT P S ≤ P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8 := by
    rw [UpsT, div_le_div_iff₀ (by positivity) (by positivity)]
    -- Δ⁴G⁵U⁴⁵·Ω⁸ ≤ G⁵U³⁵·H²Ω¹⁴  ⟺  Δ⁴U¹⁰ ≤ H²Ω⁶  (hReg²)
    have hH2 : S.Δ ^ 4 * P.U ^ 10 ≤ P.H ^ 2 * S.Ω ^ 6 := by
      have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * P.U ^ 5) hReg 2
      nlinarith [this]
    nlinarith [mul_le_mul_of_nonneg_left hH2
      (by positivity : (0:ℝ) ≤ P.G ^ 5 * P.U ^ 35 * S.Ω ^ 8),
      pow_pos hUpos 35, pow_pos hΩpos 8, hGpos, hHpos]
  have hERR_le : 10 ^ 119 * UpsT P S ≤ 10 ^ 119 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) :=
    mul_le_mul_of_nonneg_left hUpsT_le (by positivity)
  -- hLhi : |Lval| + ERR + 1 ≤ 10¹¹¹·(G⁵U³⁵/Ω⁸)
  have hBudge : (0:ℝ) < P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8 := by positivity
  have hOne_le : (1:ℝ) ≤ P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8 := by
    rw [le_div_iff₀ (by positivity)]
    have hΩ8 : S.Ω ^ 8 ≤ P.U ^ 8 := pow_le_pow_left₀ hΩpos.le hΩU 8
    have hU835 : P.U ^ 8 ≤ P.U ^ 35 := pow_le_pow_right₀ hU1 (by norm_num)
    have hG5 : P.U ^ 35 ≤ P.G ^ 5 * P.U ^ 35 := by
      have : (1:ℝ) ≤ P.G ^ 5 := one_le_pow₀ hG1
      nlinarith [this, pow_pos hUpos 35]
    nlinarith [hΩ8, hU835, hG5]
  have hLhi : |Lval P.X a d b₀ v ℓ₁ ℓ₂| + 10 ^ 119 * UpsT P S + 1
      ≤ 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by
    -- |Lval| ≤ 10⁸⁵·B, ERR ≤ 10¹¹⁰·B, 1 ≤ B ;  sum ≤ (10⁸⁵+10¹¹⁰+1)·B ≤ 10¹¹¹·B
    have hsum : |Lval P.X a d b₀ v ℓ₁ ℓ₂| + 10 ^ 119 * UpsT P S + 1
        ≤ 10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
          + 10 ^ 119 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
          + 1 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by
      have h1' : (1:ℝ) ≤ 1 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by rw [one_mul]; exact hOne_le
      linarith [hLhi0, hERR_le, h1']
    refine le_trans hsum ?_
    have hcollect : 10 ^ 94 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
          + 10 ^ 119 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
          + 1 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
        = (10 ^ 94 + 10 ^ 119 + 1) * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8) := by ring
    rw [hcollect]
    apply mul_le_mul_of_nonneg_right _ hBudge.le
    norm_num
  -- hNBsmall : 45·Wval⁴/Δ < 1/4  ⟸  hDeW (180·G⁴U²⁰ < Δ)
  have hNBsmall : 10 ^ 11 * P.Wval ^ 4 / S.Δ < 1 / 4 := by
    rw [Globals.Wval]
    rw [div_lt_iff₀ hΔpos]
    -- 45·(GU⁵)⁴ < Δ/4  ⟺  180·G⁴U²⁰ < Δ  ⟸  hDeW : 10¹⁵·G⁴U²⁰ ≤ Δ
    have hWeq : (10:ℝ) ^ 11 * (P.G * P.U ^ 5) ^ 4 = 10 ^ 11 * (P.G ^ 4 * P.U ^ 20) := by ring
    rw [hWeq]
    have hGU : (0:ℝ) < P.G ^ 4 * P.U ^ 20 := by positivity
    nlinarith [hDeW, hGU]
  -- assemble via the rounding core with Bnd = 10¹¹¹·(G⁵U³⁵/Ω⁸)
  have hNBhalf : 10 ^ 11 * P.Wval ^ 4 / S.Δ < 1 / 2 := by linarith [hNBsmall]
  exact round_extract_core (Υval := Υval) (Lval := Lval P.X a d b₀ v ℓ₁ ℓ₂)
    (ERR := 10 ^ 119 * UpsT P S) (NB := 10 ^ 11 * P.Wval ^ 4 / S.Δ)
    (Bnd := 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8))
    hNBhalf hexp hnearbd hLlo hLhi

end Squarefree
