import Squarefree.Lower.Step4Magnitude
import Squarefree.Lower.Step4VCount

/-!
# §5 Step-4 large-defect `(s,v)` enumeration (writeup 1060–1064)

Piece C of the per-`s` large-`v` build: the **`v`-inversion** and the **lattice count**.

`V_s := Δ·Ω·√(|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁)))`, so `V_s² = Δ²Ω²·|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁))`
(writeup 1062, using `XAB/D⁵ = 1/(Δ²Ω²)`).

## (C1) `v_inversion`
For an integer `s` with `1 ≤ |s|`, a triple in the large-defect range whose closed form rounds
to `s` (so `|Σ_closed − s| ≤ ε`), with `ε ≤ |s|` (the writeup's "leading term dominates the
error" — carried as the explicit side hypothesis `hε`, since in general the per-`s` error need
not be `≤ |s|`), the `v`-scale is pinned two-sidedly:

  `(1/C)·V_s ≤ |v| ≤ C·V_s`   with absolute `C`.

The `B` (and `X,a,d,L`) all cancel through the identity `Xa/d⁵·B ≍ 1/(Δ²Ω²)` combined with
the leading bracket `|−4+10a/d| ≍ 4`, so the bound is purely the geometric `V_s`-scale.

## (C2) `vlattice_count`
The admissible `v ∈ ℓ₁⁻¹ℤ` with `|v| ≤ C·V_s` number `≤ 1 + 2C·ℓ₁·V_s` (writeup 1064).  This is
the pure lattice count `step4_v_count` specialised to the `V_s` confinement window.
-/

open Real Finset

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- The §5 Step-4 `v`-scale `V_s = Δ·Ω·√(|s|/(ℓ₁³ℓ₂(ℓ₂−ℓ₁)))` (writeup 1062). -/
noncomputable def V_s (S : Scale P) (s : ℤ) (ℓ₁ ℓ₂ : ℝ) : ℝ :=
  S.Δ * S.Ω * Real.sqrt (|(s : ℝ)| / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))

set_option maxHeartbeats 1600000

/-- **Raw `v²`-magnitude LOWER bound** (the `B`-cancelled half of `sigma_s_magnitude_lower`,
kept in `v²`-form rather than `|s|`-form):
`(1/(2·10⁸))·(ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v²)/(Δ²Ω²) ≤ |Σ_closed|`.  No `s`, no pin. -/
theorem sigma_v2_lower
    {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    (1 / (2 * 10 ^ 8 : ℝ)) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
      ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set L : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  have hSeq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ = Q * ((-4 + 10 * a / d) * P0) := by
    rw [Sigma_closed, hQdef, hP0def]
  have hSabs : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| = Q * (|(-4 + 10 * a / d)| * |P0|) := by
    rw [hSeq, abs_mul, abs_of_pos hQpos, abs_mul]
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_lo : 2 ≤ |(-4 + 10 * a / d)| := by rw [le_abs]; right; linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  have hP0lo : L * |b₀| * v ^ 2 ≤ |P0| := by
    have := psum_abs_ge_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo
      (S.D_half_of_eps hdD) hd_pos hReg hG1 hU1 hUbig hDeW
    rw [hLdef, hP0def]; exact this
  -- |Σ_closed| ≥ Q · (2 · (L|b₀|v²))
  have hstep1 : Q * (2 * (L * |b₀| * v ^ 2)) ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
    rw [hSabs]
    apply mul_le_mul_of_nonneg_left _ hQpos.le
    exact mul_le_mul hbr_lo hP0lo (by positivity) hbr_nn
  -- scale identity:  XAB/D⁵ = 1/(Δ²Ω²)
  have hXABD5 : P.X * S.A * S.B / S.D ^ 5 = 1 / (S.Δ ^ 2 * S.Ω ^ 2) :=
    defect_XAB_div_D5 (P := P) S
  have hd5pos : (0:ℝ) < d ^ 5 := by positivity
  have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
  -- Q · B = X·a·B/d⁵ ≥ X·(A/5)·B/(2D)⁵ = (1/160)·XAB/D⁵ = (1/160)/(Δ²Ω²)
  have hQBlo : (1 / (165 : ℝ)) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) ≤ Q * S.B := by
    rw [← hXABD5, hQdef]
    rw [show P.X * a / d ^ 5 * S.B = (P.X * a * S.B) / d ^ 5 by ring]
    rw [show (1 / (165:ℝ)) * (P.X * S.A * S.B / S.D ^ 5)
          = (P.X * (S.A / 5) * S.B) / (33 * S.D ^ 5) by ring]
    rw [div_le_div_iff₀ (by positivity) hd5pos]
    -- X·(A/5)·B·d⁵ ≤ X·a·B·(33·D⁵) ;  a ≥ A/5, d⁵ ≤ 33 D⁵.
    have hd5 : d ^ 5 ≤ 33 * S.D ^ 5 := by
      have h2e : d ^ 5 ≤ (2 * S.D * (1 + 1/10 ^ 9)) ^ 5 := pow_le_pow_left₀ hd_pos.le hd2D 5
      nlinarith [h2e, hD5pos]
    have haA : P.X * (S.A / 5) ≤ P.X * a := mul_le_mul_of_nonneg_left ha_lo hXpos.le
    nlinarith [mul_le_mul haA hd5 (by positivity : (0:ℝ) ≤ d ^ 5)
      (by positivity : (0:ℝ) ≤ P.X * a), hBpos, mul_pos hXpos ha0,
      mul_nonneg (mul_pos hXpos hApos).le hBpos.le, hD5pos,
      mul_pos (mul_pos hXpos ha0) hBpos]
  -- |b₀| ≥ B/(2·10⁶), so Q·|b₀| ≥ Q·B/(2·10⁶) ≥ (1/(160·2·10⁶))/(Δ²Ω²)
  have hQb0lo : (1 / (330000000 : ℝ)) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) ≤ Q * |b₀| := by
    have h1' : Q * (S.B / 2000000) ≤ Q * |b₀| :=
      mul_le_mul_of_nonneg_left hb0lo hQpos.le
    have h2' : (1 / (330000000:ℝ)) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) ≤ Q * (S.B / 2000000) := by
      rw [show Q * (S.B / 2000000) = (Q * S.B) / 2000000 by ring]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2000000)]
      nlinarith [hQBlo, (by positivity : (0:ℝ) < S.Δ ^ 2 * S.Ω ^ 2)]
    linarith [h1', h2']
  -- assemble: |Σ_closed| ≥ 2·Q·L·|b₀|·v² ≥ 2·(1/(330000000))·L·v²/(Δ²Ω²) = (1/(165000000))·…
  have hLv2nn : 0 ≤ L * v ^ 2 := by positivity
  have hcombine : (1 / (165000000 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
      ≤ Q * (2 * (L * |b₀| * v ^ 2)) := by
    have hmul : (1 / (330000000:ℝ)) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) * (L * v ^ 2)
        ≤ (Q * |b₀|) * (L * v ^ 2) :=
      mul_le_mul_of_nonneg_right hQb0lo hLv2nn
    have heqL : (1 / (165000000 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
        = 2 * ((1 / (330000000:ℝ)) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) * (L * v ^ 2)) := by
      field_simp; ring
    have heqR : Q * (2 * (L * |b₀| * v ^ 2)) = 2 * ((Q * |b₀|) * (L * v ^ 2)) := by ring
    rw [heqL, heqR]
    linarith [hmul]
  -- (1/(2·10⁸)) = 1/165000000? no: 2·10⁸ = 200000000.  We proved (1/165000000) ≥ (1/(2·10⁸)).
  have hconst : (1 / (2 * 10 ^ 8 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
      ≤ (1 / (165000000 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by
    apply div_le_div_of_nonneg_right ?_ (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2)
    apply mul_le_mul_of_nonneg_right _ hLv2nn
    norm_num
  calc (1 / (2 * 10 ^ 8 : ℝ)) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
      = (1 / (2 * 10 ^ 8 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by rw [hLdef]
    _ ≤ (1 / (165000000 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := hconst
    _ ≤ Q * (2 * (L * |b₀| * v ^ 2)) := hcombine
    _ ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := hstep1

/-- **Raw `v²`-magnitude UPPER bound** (the `B`-cancelled `v²`-form of the upper half of
`sigma_s_magnitude_extract`):
`|Σ_closed| ≤ 10¹⁵·(ℓ₁³ℓ₂(ℓ₂−ℓ₁)·v²)/(Δ²Ω²)`.  No `s`, no pin. -/
theorem sigma_v2_upper
    {a : ℝ} {ℓ₁ ℓ₂ b₀ v d : ℝ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂|
      ≤ (10 ^ 15 : ℝ) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set L : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  have hSeq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ = Q * ((-4 + 10 * a / d) * P0) := by
    rw [Sigma_closed, hQdef, hP0def]
  have hSabs : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| = Q * (|(-4 + 10 * a / d)| * |P0|) := by
    rw [hSeq, abs_mul, abs_of_pos hQpos, abs_mul]
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 7 := by rw [abs_le]; constructor <;> linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  have hP0nn : 0 ≤ |P0| := abs_nonneg _
  have hP0hi : |P0| ≤ 4 * (L * |b₀| * v ^ 2) := by
    have := psum_abs_le_v2 (P := P) (S := S) (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo
      (S.D_half_of_eps hdD) hd_pos hReg hG1 hU1 hUbig hDeW
    rw [hLdef, hP0def]; exact this
  -- |Σ_closed| ≤ Q · (7 · (4 · (L|b₀|v²)))
  have hstep1 : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ Q * (7 * (4 * (L * |b₀| * v ^ 2))) := by
    rw [hSabs]
    apply mul_le_mul_of_nonneg_left _ hQpos.le
    exact mul_le_mul hbr_hi hP0hi hP0nn (by norm_num)
  -- scale identity:  XAB/D⁵ = 1/(Δ²Ω²)
  have hXABD5 : P.X * S.A * S.B / S.D ^ 5 = 1 / (S.Δ ^ 2 * S.Ω ^ 2) :=
    defect_XAB_div_D5 (P := P) S
  have hd5pos : (0:ℝ) < d ^ 5 := by positivity
  have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
  -- Q·B = X·a·B/d⁵ ≤ X·(11A)·B/D⁵ = 11·XAB/D⁵ = 11/(Δ²Ω²)
  have hQBhi : Q * S.B ≤ (111/10 : ℝ) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) := by
    rw [← hXABD5, hQdef]
    rw [show P.X * a / d ^ 5 * S.B = (P.X * a * S.B) / d ^ 5 by ring]
    rw [show (111/10:ℝ) * (P.X * S.A * S.B / S.D ^ 5)
          = (P.X * ((111/10) * S.A) * S.B) / S.D ^ 5 by ring]
    rw [div_le_div_iff₀ hd5pos hD5pos]
    -- X·a·B·D⁵ ≤ X·(11.1A)·B·d⁵ ;  a ≤ 11A, D⁵(1−ε)⁵ ≤ d⁵, 11 ≤ 11.1(1−ε)⁵.
    have hD5d5 : S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5 ≤ d ^ 5 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hdD 5
    have hXAB : (0:ℝ) < P.X * S.A * S.B := by positivity
    have haA : P.X * a ≤ P.X * (11 * S.A) := mul_le_mul_of_nonneg_left ha_hi hXpos.le
    have e1 : P.X * a * S.B * S.D ^ 5 ≤ P.X * (11 * S.A) * S.B * S.D ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_right haA (mul_nonneg hBpos.le hD5pos.le)]
    have e2 : P.X * ((111/10) * S.A) * S.B * (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5)
        ≤ P.X * ((111/10) * S.A) * S.B * d ^ 5 :=
      mul_le_mul_of_nonneg_left hD5d5 (by positivity)
    have e3 : P.X * (11 * S.A) * S.B * S.D ^ 5
        ≤ P.X * ((111/10) * S.A) * S.B * (S.D ^ 5 * (1 - 1/10 ^ 9) ^ 5) := by
      nlinarith [mul_pos hXAB hD5pos]
    linarith [e1, e2, e3]
  -- |b₀| ≤ 3·10¹²·B, so Q·|b₀| ≤ 3·10¹²·Q·B ≤ 33·10¹²/(Δ²Ω²)
  have hQb0hi : Q * |b₀| ≤ (333 * 10 ^ 11 : ℝ) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) := by
    have h1' : Q * |b₀| ≤ Q * (3000000000000 * S.B) :=
      mul_le_mul_of_nonneg_left hb0 hQpos.le
    have h2' : Q * (3000000000000 * S.B) ≤ (333 * 10 ^ 11:ℝ) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) := by
      rw [show Q * (3000000000000 * S.B) = 3000000000000 * (Q * S.B) by ring]
      nlinarith [hQBhi, (by positivity : (0:ℝ) < S.Δ ^ 2 * S.Ω ^ 2)]
    linarith [h1', h2']
  -- assemble: |Σ_closed| ≤ 28·Q·L·|b₀|·v² ≤ 28·33·10¹²·L·v²/(Δ²Ω²) ≤ 10¹⁵·L·v²/(Δ²Ω²)
  have hLv2nn : 0 ≤ L * v ^ 2 := by positivity
  have hstep2 : Q * (7 * (4 * (L * |b₀| * v ^ 2)))
      ≤ (9324 * 10 ^ 11 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by
    have hmul : (Q * |b₀|) * (L * v ^ 2)
        ≤ (333 * 10 ^ 11 : ℝ) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) * (L * v ^ 2) :=
      mul_le_mul_of_nonneg_right hQb0hi hLv2nn
    have heqL : Q * (7 * (4 * (L * |b₀| * v ^ 2))) = 28 * ((Q * |b₀|) * (L * v ^ 2)) := by ring
    have heqR : (9324 * 10 ^ 11 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
        = 28 * ((333 * 10 ^ 11 : ℝ) * (1 / (S.Δ ^ 2 * S.Ω ^ 2)) * (L * v ^ 2)) := by
      field_simp; ring
    rw [heqL, heqR]
    linarith [hmul]
  have hconst : (9324 * 10 ^ 11 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2)
      ≤ (10 ^ 15 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by
    apply div_le_div_of_nonneg_right ?_ (by positivity : (0:ℝ) ≤ S.Δ ^ 2 * S.Ω ^ 2)
    apply mul_le_mul_of_nonneg_right _ hLv2nn
    norm_num
  calc |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂|
      ≤ Q * (7 * (4 * (L * |b₀| * v ^ 2))) := hstep1
    _ ≤ (9324 * 10 ^ 11 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := hstep2
    _ ≤ (10 ^ 15 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := hconst
    _ = (10 ^ 15 : ℝ) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) := by rw [hLdef]

/-- **(C1) §5 Step-4 large-defect `v`-inversion** (writeup 1062, "Gap 1").  For an integer `s`
with `1 ≤ |s|`, a triple in the large-defect range whose closed form rounds to `s`
(`|Σ_closed − s| ≤ ε`) with the error dominated by the leading term (`hε : ε ≤ |s|`), the
`v`-scale is pinned two-sidedly by `V_s`:

  `(1/(2·10¹⁵))·V_s² ≤ v²`   and   `v² ≤ (4·10⁸)·V_s²`.

(The two-sided constant is absolute; `B,X,a,d` all cancel through `Xa/d⁵·B ≍ 1/(Δ²Ω²)`.) -/
theorem v_inversion
    {a : ℝ} {ℓ₁ ℓ₂ b₀ v d ε : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂))
    (hnear : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)| ≤ ε)
    (hε : ε ≤ |(s : ℝ)|) :
    (1 / (2 * 10 ^ 15 : ℝ)) * V_s S s ℓ₁ ℓ₂ ^ 2 ≤ v ^ 2
      ∧ v ^ 2 ≤ (4 * 10 ^ 8 : ℝ) * V_s S s ℓ₁ ℓ₂ ^ 2 := by
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  set L : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  have hsnn : 0 ≤ |(s : ℝ)| := abs_nonneg _
  have hDΩ2pos : (0:ℝ) < S.Δ ^ 2 * S.Ω ^ 2 := by positivity
  -- V_s² = Δ²Ω²·|s|/L
  have hVsq : V_s S s ℓ₁ ℓ₂ ^ 2 = S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)| / L := by
    rw [V_s, hLdef]
    rw [mul_pow, mul_pow]
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ |(s : ℝ)| / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))]
    field_simp
  -- |Σ_closed| ≤ |s| + ε ≤ 2|s|  (from round = s and hε)
  have hSle : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ 2 * |(s : ℝ)| := by
    have h := abs_le.mp hnear
    -- |Σ| ≤ |Σ − s| + |s| ≤ ε + |s|
    have : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s:ℝ)| + |(s:ℝ)| := by
      have := abs_sub_abs_le_abs_sub (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) (s:ℝ)
      linarith [this]
    linarith [this, hnear, hε]
  -- |Σ_closed| ≥ |s| − ε ≥ |s|/2  (since ε ≤ |s| would give 0; need ε ≤ |s|/2... actually use hε)
  -- |Σ| ≥ |s| − |Σ − s| ≥ |s| − ε.  With hε : ε ≤ |s| this gives ≥ 0 only.  We need a
  -- positive lower bound; round = s gives |Σ − s| = distInt Σ ≤ 1/2, so |Σ| ≥ |s| − 1/2 ≥ |s|/2.
  have hSge : |(s : ℝ)| / 2 ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| := by
    -- distInt(Σ) ≤ 1/2 always, and round Σ = s, so |Σ − s| ≤ 1/2.
    have hhalf : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s:ℝ)| ≤ 1 / 2 := by
      rw [hround]
      exact abs_sub_round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
    have h := abs_sub_abs_le_abs_sub (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) (s:ℝ)
    -- |s| − |Σ| ≤ |Σ − s| ≤ 1/2, and |s| ≥ 1, so |Σ| ≥ |s| − 1/2 ≥ |s|/2.
    have h2 : |(s:ℝ)| - |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ 1 / 2 := by
      have h3 := abs_sub_abs_le_abs_sub (s:ℝ) (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      rw [abs_sub_comm (s:ℝ)] at h3
      linarith [h3, hhalf]
    nlinarith [h2, hs1]
  -- raw magnitude bounds
  have hlow := sigma_v2_lower (P := P) (S := S) (a := a) ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W
    hb0 hb0lo hv hvlo (S.D_eps_lo hdD) (S.D_eps_hi hd2D) hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
  have hupp := sigma_v2_upper (P := P) (S := S) (a := a) ha0 ha_lo ha_hi hℓ1 hℓ12 hℓ12' hℓ2W
    hb0 hb0lo hv hvlo (S.D_eps_lo hdD) (S.D_eps_hi hd2D) hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
  rw [← hLdef] at hlow hupp
  constructor
  · -- LOWER: (1/(2·10¹⁵))·V_s² ≤ v².
    -- From |Σ| ≤ 10¹⁵·L·v²/(Δ²Ω²) and |Σ| ≥ |s|/2:  |s|/2 ≤ 10¹⁵·L·v²/(Δ²Ω²)
    --  ⟹ v² ≥ (|s|·Δ²Ω²)/(2·10¹⁵·L) = (1/(2·10¹⁵))·V_s².
    have hchain : |(s:ℝ)| / 2 ≤ (10 ^ 15 : ℝ) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) :=
      le_trans hSge hupp
    rw [hVsq]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2 * S.Ω ^ 2)] at hchain
    -- hchain : |s|/2 · (Δ²Ω²) ≤ 10¹⁵ · (L v²)
    have hv2lo : S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)| / (2 * 10 ^ 15 * L) ≤ v ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * 10 ^ 15 * L)]
      nlinarith [hchain, hLpos, hDΩ2pos, hsnn]
    refine le_trans ?_ hv2lo
    rw [show (1 / (2 * 10 ^ 15 : ℝ)) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)| / L)
          = S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)| / (2 * 10 ^ 15 * L) by field_simp]
  · -- UPPER: v² ≤ (4·10⁸)·V_s².
    -- From |Σ| ≥ (1/(2·10⁸))·L·v²/(Δ²Ω²) and |Σ| ≤ 2|s|:
    --   (1/(2·10⁸))·L·v²/(Δ²Ω²) ≤ 2|s|  ⟹ v² ≤ 4·10⁸·|s|·Δ²Ω²/L = 4·10⁸·V_s².
    have hchain : (1 / (2 * 10 ^ 8 : ℝ)) * (L * v ^ 2) / (S.Δ ^ 2 * S.Ω ^ 2) ≤ 2 * |(s:ℝ)| :=
      le_trans hlow hSle
    rw [hVsq]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2 * S.Ω ^ 2)] at hchain
    -- hchain : (1/(2·10⁸))·(L v²) ≤ 2|s| · Δ²Ω²
    -- ⟹ L v² ≤ 4·10⁸·|s|·Δ²Ω²  ⟹ v² ≤ 4·10⁸·|s|·Δ²Ω²/L
    have hv2hi : v ^ 2 ≤ (4 * 10 ^ 8 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|) / L := by
      rw [le_div_iff₀ hLpos]
      nlinarith [hchain, hDΩ2pos, hsnn, hLpos]
    refine le_trans hv2hi ?_
    rw [show (4 * 10 ^ 8 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s : ℝ)| / L)
          = (4 * 10 ^ 8 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * |(s:ℝ)|) / L by ring]

/-- **(C2) §5 Step-4 large-defect lattice count** (writeup 1064).  The admissible
`v ∈ ℓ₁⁻¹ℤ` with `|v| ≤ C·V_s` number `≤ 1 + 2C·ℓ₁·V_s`.  Pure lattice count, specialising
`step4_v_count` to the `V_s`-confinement window. -/
theorem vlattice_count (C : ℝ) (s : ℤ) (ℓ₁ ℓ₂ : ℝ)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hC : 0 ≤ C)
    (Vset : Finset ℝ) (mOf : ℝ → ℤ)
    (hlat : ∀ v ∈ Vset, (mOf v : ℝ) = ℓ₁ * v)
    (hconf : ∀ v ∈ Vset, |v| ≤ C * V_s S s ℓ₁ ℓ₂) :
    (Vset.card : ℝ) ≤ 1 + 2 * C * ℓ₁ * V_s S s ℓ₁ ℓ₂ := by
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hVsnn : 0 ≤ V_s S s ℓ₁ ℓ₂ := by
    rw [V_s]
    have hΔΩ : 0 ≤ S.Δ * S.Ω := by positivity
    exact mul_nonneg hΔΩ (Real.sqrt_nonneg _)
  have hCVnn : 0 ≤ C * V_s S s ℓ₁ ℓ₂ := mul_nonneg hC hVsnn
  have h := step4_v_count ℓ₁ (C * V_s S s ℓ₁ ℓ₂) hℓ1 hCVnn Vset mOf hlat hconf
  calc (Vset.card : ℝ) ≤ 2 * ℓ₁ * (C * V_s S s ℓ₁ ℓ₂) + 1 := h
    _ = 1 + 2 * C * ℓ₁ * V_s S s ℓ₁ ℓ₂ := by ring

end Squarefree
