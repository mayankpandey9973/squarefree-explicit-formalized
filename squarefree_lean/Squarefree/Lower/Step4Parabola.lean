import Squarefree.Lower.Step4Magnitude

/-!
# §5 Step-4 large-defect "tight parabola" (writeup 1052–1058)

Piece 2 of the square-difference `v`-localization (Piece 1 = `vband_card_le`).  As a function
of `v`, the leading part of `Σ_closed` is a genuine quadratic `C·v²` with

  `C = C_r := −12·X·a·b₀·ℓ₁·ℓ₂·(ℓ₂−ℓ₁)/d⁵`,   `C·(ℓ₁v)² = (Xa/d⁵)·(−4)·3ℓ₁³ℓ₂(ℓ₂−ℓ₁)b₀v²`,

the `−4·P₁`-`v²` monomial.  The cubic, `P₂/d` and the bracket-drift corrections are
`≪ |s|` (writeup 1058).  Concretely we prove the residual

  `|Σ_closed − C_r·(ℓ₁v)²| ≤ (105/122)·|s|`,

a strict fraction of `|s|` (so `E < c` holds for the `vband_card_le` band).

## Mechanism

Write `Q := Xa/d⁵`, `Mm := 3ℓ₁³ℓ₂(ℓ₂−ℓ₁)b₀v²` (the `v²`-lead of `P₁`, with `|Mm| = 3T`,
`T := ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`), `P0 := P₁+P₂/d`.  Then `C_r·(ℓ₁v)² = Q·(−4)·Mm` and

  `Σ_closed − C_r·(ℓ₁v)² = Q·[(−4+10a/d)·(P0−Mm) + (10a/d)·Mm]`.

* `|−4+10a/d| ≤ 4` and `0 ≤ 10a/d ≤ 1/8` (`bracket_ad_small`);
* `|P0−Mm| ≤ T` (`psum_resid_le_v2`, the five-monomial residual control);
* `|Mm| = 3T`,

so `|residual| ≤ Q·(4·T + (1/8)·3T) = (35/8)·Q·T`.  The `|s|`-conversion is tight (no `10²¹`
slack) because `Σ_closed` rounds to `s`: `|Σ_closed − s| ≤ 1/2` (`abs_sub_round`), so with
`|s| ≥ 1`, `|Σ_closed| ≤ (3/2)|s|`.  As `|C_r·(ℓ₁v)²| = 12·Q·T`, the triangle inequality
`12·Q·T ≤ |Σ_closed| + (35/8)·Q·T ≤ (3/2)|s| + (35/8)·Q·T` gives `(61/8)·Q·T ≤ (3/2)|s|`,
i.e. `Q·T ≤ (12/61)|s|`, whence `|residual| ≤ (35/8)·(12/61)|s| = (105/122)|s|`.

The achieved constant `c = 105/122 ≈ 0.861` is forced (not improvable to `1/4` here) by the
`P₂`-linear `b₀³v/d` monomial of `P0−Mm`, whose cancellation-avoidance margin `hvlo` is only
`1/10` (giving that monomial `≤ (1/2)T`); a sharper `c` would need a stronger `hvlo`.
-/

namespace Squarefree

open Real Squarefree.Counting

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- **§5 Step-4 large-defect tight parabola** (writeup 1052–1058).  The closed cubic/quartic
`Σ_closed` agrees with its leading `v²` term `C_r·(ℓ₁v)²` (`C_r := −12Xab₀ℓ₁ℓ₂(ℓ₂−ℓ₁)/d⁵`) up to
an error that is a strict fraction `105/122` of `|s|`.  This is the parabola input for the
`vband_card_le` square-difference band count.  Hypotheses reuse `sigma_s_magnitude_extract`'s
set (the large-defect regime + `|v|≍V_s` pin), minus the near-int packaging not needed here. -/
theorem Sigma_closed_parabola_tight
    {a b₀ v d ℓ₁ ℓ₂ : ℝ} {s : ℤ}
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
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) :
    |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2|
      ≤ (105 / 122 : ℝ) * |(s : ℝ)| := by
  -- positivity / basic facts
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hd5pos : (0:ℝ) < d ^ 5 := by positivity
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hsnn : 0 ≤ |(s : ℝ)| := abs_nonneg _
  -- abbreviations
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMmdef
  -- |Mm| = 3T
  have hMabs : |Mm| = 3 * T := by
    rw [hMmdef, hTdef,
      show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
        = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  -- bracket bounds : 0 ≤ 10a/d ≤ 1/8, so |−4+10a/d| ≤ 4.
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  -- |P0 − Mm| ≤ T  (the five-monomial residual control)
  have hres : |P0 - Mm| ≤ T := by
    rw [hP0def, hMmdef, hTdef]
    exact psum_resid_le_v2 (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo (S.D_half_of_eps hdD) hd_pos hReg
      hG1 hU1 hUbig hDeW
  -- The leading-term identity:  C_r·(ℓ₁v)² = Q·(−4)·Mm.
  have hCr_eq : (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2
      = Q * ((-4) * Mm) := by
    rw [hQdef, hMmdef]; field_simp; ring
  -- The residual identity:  Σ_closed − C_r·(ℓ₁v)² = Q·[(−4+10a/d)·(P0−Mm) + (10a/d)·Mm].
  have hresid_eq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2
      = Q * ((-4 + 10 * a / d) * (P0 - Mm) + (10 * a / d) * Mm) := by
    rw [Sigma_closed, hCr_eq, hQdef, hP0def, hMmdef]; ring
  -- Residual term-by-term bound:  |residual| ≤ (35/8)·Q·T.
  have hresid_le : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2|
      ≤ Q * (35 / 8 * T) := by
    rw [hresid_eq, abs_mul, abs_of_pos hQpos]
    apply mul_le_mul_of_nonneg_left _ hQpos.le
    calc |(-4 + 10 * a / d) * (P0 - Mm) + (10 * a / d) * Mm|
        ≤ |(-4 + 10 * a / d) * (P0 - Mm)| + |(10 * a / d) * Mm| := abs_add_le _ _
      _ = |(-4 + 10 * a / d)| * |P0 - Mm| + |10 * a / d| * |Mm| := by rw [abs_mul, abs_mul]
      _ ≤ 4 * T + (1 / 8) * (3 * T) := by
          have hadabs : |10 * a / d| = 10 * a / d := abs_of_nonneg had0
          rw [hadabs, hMabs]
          have hpart1 : |(-4 + 10 * a / d)| * |P0 - Mm| ≤ 4 * T :=
            mul_le_mul hbr_hi hres (abs_nonneg _) (by norm_num)
          have hpart2 : 10 * a / d * (3 * T) ≤ (1 / 8) * (3 * T) :=
            mul_le_mul_of_nonneg_right hadhi (by positivity)
          linarith [hpart1, hpart2]
      _ = 35 / 8 * T := by ring
  -- The leading magnitude:  |C_r·(ℓ₁v)²| = 12·Q·T.
  have hlead_abs : |(-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2|
      = Q * (12 * T) := by
    rw [hCr_eq, abs_mul, abs_of_pos hQpos, abs_mul, hMabs]
    rw [show |(-4 : ℝ)| = 4 by norm_num]; ring
  -- Σ_closed rounds to s, so |Σ_closed − s| ≤ 1/2, hence |Σ_closed| ≤ (3/2)|s|.
  have hhalf : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)| ≤ 1 / 2 := by
    rw [hround]; exact abs_sub_round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
  have hSle : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ (3 / 2) * |(s : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) (s : ℝ)
    nlinarith [h, hhalf, hs1, hsnn]
  -- Triangle inequality on  Σ_closed = leading + residual :
  --   12·Q·T = |leading| ≤ |Σ_closed| + |residual| ≤ (3/2)|s| + (35/8)·Q·T.
  have hQT : Q * T ≤ (12 / 61) * |(s : ℝ)| := by
    have htri : Q * (12 * T) ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂|
        + |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
            - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2| := by
      rw [← hlead_abs]
      have h := abs_sub_abs_le_abs_sub
        ((-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2)
        (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      rw [abs_sub_comm
        ((-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2)] at h
      linarith [h]
    -- 12·Q·T ≤ (3/2)|s| + (35/8)·Q·T  ⟹  (61/8)·Q·T ≤ (3/2)|s|  ⟹  Q·T ≤ (12/61)|s|.
    nlinarith [htri, hSle, hresid_le, mul_nonneg hQpos.le hTnn]
  -- Assemble:  |residual| ≤ (35/8)·Q·T ≤ (35/8)·(12/61)|s| = (105/122)|s|.
  calc |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2|
      ≤ Q * (35 / 8 * T) := hresid_le
    _ = 35 / 8 * (Q * T) := by ring
    _ ≤ 35 / 8 * ((12 / 61) * |(s : ℝ)|) := by gcongr
    _ = (105 / 122 : ℝ) * |(s : ℝ)| := by ring

/-- **Helper for `Sigma_closed_parabola_sharp` (no `|s|` conversion).**  With the writeup
large-defect cutoff `hVcut : V₂ ≤ |v|`, the bracket-included residual
`Σ_closed − C'·(ℓ₁v)²` (where `C' := (Xa/d⁵)(−4+10a/d)·3ℓ₁ℓ₂(ℓ₂−ℓ₁)b₀`) is bounded by
`4·(1/10⁵⁰)·Q·T`, `Q := Xa/d⁵`, `T := ℓ₁³ℓ₂(ℓ₂−ℓ₁)|b₀|v²`.  This is the
`psum_resid_le_sharp` residual (`|Res| ≤ (1/10⁵⁰)T`) times the bracket `|−4+10a/d| ≤ 4`.
`K := 1/10⁵⁰`. -/
private theorem sigma_closed_resid_sharp
    {a b₀ v d ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ) :
    |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀) * (ℓ₁ * v) ^ 2|
      ≤ (P.X * a / d ^ 5) * (4 * ((1 / 10 ^ 50) * (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2))) := by
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMmdef
  -- bracket : |−4+10a/d| ≤ 4
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  -- sharp residual : |P0 − Mm| ≤ (1/10⁵⁰)·T
  have hres : |P0 - Mm| ≤ (1 / 10 ^ 50) * T := by
    rw [hP0def, hMmdef, hTdef]
    exact psum_resid_le_sharp (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hVcut (S.D_half_of_eps hdD) hd_pos hReg
      hG1 hU1 hUbig hDeW
  -- residual identity :  Σ_closed − C'(ℓ₁v)² = Q·(−4+10a/d)·(P0 − Mm)
  have hresid_eq : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - Q * (-4 + 10 * a / d) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀) * (ℓ₁ * v) ^ 2
      = Q * ((-4 + 10 * a / d) * (P0 - Mm)) := by
    rw [Sigma_closed, hQdef, hP0def, hMmdef]; ring
  rw [hresid_eq, abs_mul, abs_of_pos hQpos]
  apply mul_le_mul_of_nonneg_left _ hQpos.le
  calc |(-4 + 10 * a / d) * (P0 - Mm)|
      = |(-4 + 10 * a / d)| * |P0 - Mm| := abs_mul _ _
    _ ≤ 4 * ((1 / 10 ^ 50) * T) :=
        mul_le_mul hbr_hi hres (abs_nonneg _) (by norm_num)

/-- **§5 Step-4 large-defect SHARP parabola** (writeup 1052–1058).  Unlike
`Sigma_closed_parabola_tight` (whose `105/122·|s|` error is useless for the thin band), the
large-defect cutoff `hVcut : V₂ ≤ |v|` kills the only `≍|s|` residual monomial (the `P₂`-linear
`b₀³v/d` term), so subtracting the **bracket-included** quadratic
`C'·(ℓ₁v)² := (Xa/d⁵)(−4+10a/d)·3ℓ₁ℓ₂(ℓ₂−ℓ₁)b₀·(ℓ₁v)²` leaves an error `≤ (1/10²⁹)·|s|`,
genuinely `≪ |s|`.  Mechanism: `sigma_closed_resid_sharp` gives `|residual| ≤ 4·(1/10⁵⁰)·Q·T`;
the `|s|`-conversion `Q·T ≤ (12/61)|s|` is the same triangle/round argument as the tight
lemma.  `c = 48/(61·10⁵⁰) ≤ 1/10²⁹`. -/
theorem Sigma_closed_parabola_sharp
    {a b₀ v d ℓ₁ ℓ₂ : ℝ} {s : ℤ}
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ12' : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hb0lo : S.B / 2000000 ≤ |b₀|)
    (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hvlo : 10 * (ℓ₂ * (ℓ₂ - ℓ₁) * b₀ ^ 2 / d) ≤ |v|)
    (hVcut : V₂ P S ≤ |v|)
    (hdD : S.D * (1 - 1/10 ^ 9) ≤ d) (hd2D : d ≤ 2 * S.D * (1 + 1/10 ^ 9))
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hs1 : 1 ≤ |(s : ℝ)|)
    (hround : (s : ℝ) = round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)) :
    |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀) * (ℓ₁ * v) ^ 2|
      ≤ (1 / 10 ^ 29 : ℝ) * |(s : ℝ)| := by
  -- positivity / basic facts
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hd_pos : 0 < d := S.D_pos_of_eps hdD
  have hd5pos : (0:ℝ) < d ^ 5 := by positivity
  have hℓ1pos : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2pos : 0 < ℓ₂ := lt_trans hℓ1pos hℓ12
  have h21pos : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hsnn : 0 ≤ |(s : ℝ)| := abs_nonneg _
  set Q : ℝ := P.X * a / d ^ 5 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  set T : ℝ := ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * |b₀| * v ^ 2 with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  have hQTnn : 0 ≤ Q * T := mul_nonneg hQpos.le hTnn
  -- the SHARP residual bound (the banked helper):  |residual| ≤ 4·(1/10⁵⁰)·Q·T
  have hresid_le :
      |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀) * (ℓ₁ * v) ^ 2|
      ≤ Q * (4 * ((1 / 10 ^ 50) * T)) := by
    rw [hTdef, hQdef]
    exact sigma_closed_resid_sharp ha0 ha_hi hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hVcut hdD hd2D
      hReg h1 hG1 hU1 hΔ1 hΩU hUbig hDeW
  -- the `|s|`-conversion `Q·T ≤ (12/61)|s|` : identical triangle/round argument as the tight
  -- lemma, here re-derived through the (weaker) `psum_resid_le_v2` residual control.
  set Mm : ℝ := 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2 with hMmdef
  set P0 : ℝ := Pone b₀ v ℓ₁ ℓ₂ + Ptwo b₀ v ℓ₁ ℓ₂ / d with hP0def
  have hMabs : |Mm| = 3 * T := by
    rw [hMmdef, hTdef,
      show 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * b₀ * v ^ 2
        = (3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2) * b₀ by ring,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * v ^ 2)]
    ring
  obtain ⟨had0, hadhi⟩ :=
    bracket_ad_small (S := S) ha0 ha_hi hdD h1 hG1 hU1 hΔ1 hΩU hUbig
  have hbr_hi : |(-4 + 10 * a / d)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hbr_nn : 0 ≤ |(-4 + 10 * a / d)| := abs_nonneg _
  -- the (weaker) residual control |P0 − Mm| ≤ T, used only for the |s|-conversion
  have hresT : |P0 - Mm| ≤ T := by
    rw [hP0def, hMmdef, hTdef]
    exact psum_resid_le_v2 (a := a) hℓ1 hℓ12 hℓ12' hℓ2W hb0 hb0lo hv hvlo (S.D_half_of_eps hdD) hd_pos hReg
      hG1 hU1 hUbig hDeW
  -- the leading-term identity for the ORIGINAL (−4)-only quadratic
  have hCr_eq : (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2
      = Q * ((-4) * Mm) := by
    rw [hQdef, hMmdef]; field_simp; ring
  have hresid_eqv : Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2
      = Q * ((-4 + 10 * a / d) * (P0 - Mm) + (10 * a / d) * Mm) := by
    rw [Sigma_closed, hCr_eq, hQdef, hP0def, hMmdef]; ring
  have hresidv_le : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2|
      ≤ Q * (35 / 8 * T) := by
    rw [hresid_eqv, abs_mul, abs_of_pos hQpos]
    apply mul_le_mul_of_nonneg_left _ hQpos.le
    calc |(-4 + 10 * a / d) * (P0 - Mm) + (10 * a / d) * Mm|
        ≤ |(-4 + 10 * a / d) * (P0 - Mm)| + |(10 * a / d) * Mm| := abs_add_le _ _
      _ = |(-4 + 10 * a / d)| * |P0 - Mm| + |10 * a / d| * |Mm| := by rw [abs_mul, abs_mul]
      _ ≤ 4 * T + (1 / 8) * (3 * T) := by
          have hadabs : |10 * a / d| = 10 * a / d := abs_of_nonneg had0
          rw [hadabs, hMabs]
          have hpart1 : |(-4 + 10 * a / d)| * |P0 - Mm| ≤ 4 * T :=
            mul_le_mul hbr_hi hresT (abs_nonneg _) (by norm_num)
          have hpart2 : 10 * a / d * (3 * T) ≤ (1 / 8) * (3 * T) :=
            mul_le_mul_of_nonneg_right hadhi (by positivity)
          linarith [hpart1, hpart2]
      _ = 35 / 8 * T := by ring
  have hlead_abs : |(-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2|
      = Q * (12 * T) := by
    rw [hCr_eq, abs_mul, abs_of_pos hQpos, abs_mul, hMabs]
    rw [show |(-4 : ℝ)| = 4 by norm_num]; ring
  have hhalf : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂ - (s : ℝ)| ≤ 1 / 2 := by
    rw [hround]; exact abs_sub_round (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
  have hSle : |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂| ≤ (3 / 2) * |(s : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂) (s : ℝ)
    nlinarith [h, hhalf, hs1, hsnn]
  have hQT : Q * T ≤ (12 / 61) * |(s : ℝ)| := by
    have htri : Q * (12 * T) ≤ |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂|
        + |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
            - (-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2| := by
      rw [← hlead_abs]
      have h := abs_sub_abs_le_abs_sub
        ((-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2)
        (Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂)
      rw [abs_sub_comm
        ((-12 * P.X * a * b₀ * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / d ^ 5) * (ℓ₁ * v) ^ 2)] at h
      linarith [h]
    nlinarith [htri, hSle, hresidv_le, hQTnn]
  -- assemble :  |residual| ≤ 4·(1/10⁵⁰)·Q·T ≤ 4·(1/10⁵⁰)·(12/61)|s| ≤ (1/10²⁹)|s|.
  calc |Sigma_closed P.X a b₀ v d ℓ₁ ℓ₂
        - (P.X * a / d ^ 5) * (-4 + 10 * a / d) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * b₀) * (ℓ₁ * v) ^ 2|
      ≤ Q * (4 * ((1 / 10 ^ 50) * T)) := hresid_le
    _ = (4 / 10 ^ 50) * (Q * T) := by ring
    _ ≤ (4 / 10 ^ 50) * ((12 / 61) * |(s : ℝ)|) := by gcongr
    _ ≤ (1 / 10 ^ 29 : ℝ) * |(s : ℝ)| := by
        rw [show (4 / 10 ^ 50 : ℝ) * ((12 / 61) * |(s:ℝ)|)
              = ((4 / 10 ^ 50) * (12 / 61)) * |(s:ℝ)| by ring]
        apply mul_le_mul_of_nonneg_right _ hsnn
        norm_num

end Squarefree
