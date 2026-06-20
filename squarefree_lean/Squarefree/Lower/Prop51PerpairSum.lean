import Squarefree.Lower.Prop51Combine
import Squarefree.Lower.Prop51Bridge
import Squarefree.Lower.UpsilonMagV2

/-!
# §5 assembly — per-pair budget arithmetic

Pure-real arithmetic for the §5 per-pair assembly (`Prop51Assembly.lean`):

* `Bcombine_eq` — `Bcombine` in plain `G,U,Δ,Ω,H` variables (rpow residue only in
  `Δ^{1/2}, G^{15/2}, U^{95/2}`);
* `perpair_sum_le_Bcombine` — the four landed per-range conclusions (Steps 1–4 at the
  capstone constant `C = 10⁵⁷`) sum into `Bcombine` (`10¹¹⁵ + 10⁴⁰⁸ + 10²⁵⁸ + 1.6·10³⁸¹
  ≤ C₀ = 10⁴⁰⁹`, sympy-verified);
* `mbound_step2_env` / `mbound_step3_env` — the `Mbound + 3/2` envelopes pinning the
  Step-2/Step-3 `N`-caps at `ℓ₁ ≤ 130·G·U⁵`.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- `Bcombine` in plain variables: the seven landed monomials under the `10⁴⁰⁹·H/Δ` prefix. -/
theorem Bcombine_eq (ℓ₁ ℓ₂ : ℕ) :
    Bcombine P S ℓ₁ ℓ₂ = 10 ^ 409 * (P.H / S.Δ) *
      ( P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 2)
          * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
        + S.Δ ^ 2 * P.G ^ 5 * P.U ^ 45 / (P.H * S.Ω ^ 14)
        + P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω ^ 8)
        + S.Δ ^ 2 * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2) / (P.H * S.Ω ^ 8)
        + P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω)
        + P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
        + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27) ) := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hΔpos := S.Δ_pos
  set g := P.G ^ ((1 : ℝ) / 4) with hgdef
  set u := P.U ^ ((1 : ℝ) / 4) with hudef
  set dl := S.Δ ^ ((1 : ℝ) / 2) with hdldef
  set ω := S.Ω with hωdef
  have hBeq : Bcombine P S ℓ₁ ℓ₂ = 10 ^ 409 * (P.H / S.Δ) *
      ( g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
          * (1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))))
        + dl ^ 4 * g ^ 20 * u ^ 180 / (P.H * ω ^ 14)
        + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
        + dl ^ 4 * g ^ 30 * u ^ 190 / (P.H * ω ^ 8)
        + g ^ 28 * u ^ 140 / (dl * ω)
        + g ^ 56 * u ^ 300 / (dl ^ 2 * ω ^ 13)
        + dl ^ 4 * g ^ 56 * u ^ 360 / (P.H * ω ^ 27) ) := rfl
  have hg16 : g ^ 16 = P.G ^ 4 := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 16, ← Real.rpow_mul hGpos.le,
      show ((1:ℝ)/4) * (16 : ℕ) = ((4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hg20 : g ^ 20 = P.G ^ 5 := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 20, ← Real.rpow_mul hGpos.le,
      show ((1:ℝ)/4) * (20 : ℕ) = ((5 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hg28 : g ^ 28 = P.G ^ 7 := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 28, ← Real.rpow_mul hGpos.le,
      show ((1:ℝ)/4) * (28 : ℕ) = ((7 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hg30 : g ^ 30 = P.G ^ ((15 : ℝ) / 2) := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 30, ← Real.rpow_mul hGpos.le]
    norm_num
  have hg56 : g ^ 56 = P.G ^ 14 := by
    rw [hgdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/4)) 56, ← Real.rpow_mul hGpos.le,
      show ((1:ℝ)/4) * (56 : ℕ) = ((14 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hu60 : u ^ 60 = P.U ^ 15 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 60, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (60 : ℕ) = ((15 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hu140 : u ^ 140 = P.U ^ 35 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 140, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (140 : ℕ) = ((35 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hu180 : u ^ 180 = P.U ^ 45 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 180, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (180 : ℕ) = ((45 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hu190 : u ^ 190 = P.U ^ ((95 : ℝ) / 2) := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 190, ← Real.rpow_mul hUpos.le]
    norm_num
  have hu300 : u ^ 300 = P.U ^ 75 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 300, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (300 : ℕ) = ((75 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hu360 : u ^ 360 = P.U ^ 90 := by
    rw [hudef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/4)) 360, ← Real.rpow_mul hUpos.le,
      show ((1:ℝ)/4) * (360 : ℕ) = ((90 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hdl2 : dl ^ 2 = S.Δ := by
    rw [hdldef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hΔpos.le]
    norm_num
  have hdl4 : dl ^ 4 = S.Δ ^ 2 := by
    rw [hdldef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 4, ← Real.rpow_mul hΔpos.le,
      show ((1:ℝ)/2) * (4 : ℕ) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hBeq, hg16, hg20, hg28, hg30, hg56, hu60, hu140, hu180, hu190, hu300, hu360,
    hωdef, hdl4, hdl2, hdldef]

set_option maxHeartbeats 3200000 in
set_option exponentiation.threshold 600 in
/-- **§5 per-pair summation**: the four landed per-range bounds (Steps 1–4 at `C = 10⁵⁷`)
sum into `Bcombine` (constants `10¹¹⁵ + 10⁴⁰⁸ + 10²⁵⁸ + 1.6·10³⁸¹ ≤ 10⁴⁰⁹`). -/
theorem perpair_sum_le_Bcombine {ℓ₁ ℓ₂ : ℕ} (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) :
    10 ^ 55 * (S.R * (10 ^ 60 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 15 / S.Ω ^ 5)))
        * (1 + P.G * S.Ω ^ 5 / (((ℓ₁ : ℤ) : ℝ) * ((ℓ₂ : ℤ) : ℝ)
            * (((ℓ₂ : ℤ) : ℝ) - ((ℓ₁ : ℤ) : ℝ))))
      + 10 ^ 408 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
          + (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω ^ 8)))
      + 10 ^ 258 * ((P.H / S.Δ)
            * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2) / S.Ω ^ 8)
          + (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω)))
      + 80 * (2 * 10 ^ 322) * 10 ^ 57 * (P.H / S.Δ) *
          (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
            + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27))
      ≤ Bcombine P S ℓ₁ ℓ₂ := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hΔpos := S.Δ_pos
  have hHpos := P.H_pos; have hΩpos := S.Ω_pos
  have hΔ12pos : (0:ℝ) < S.Δ ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hΔpos _
  have hG152pos : (0:ℝ) < P.G ^ ((15:ℝ)/2) := Real.rpow_pos_of_pos hGpos _
  have hU952pos : (0:ℝ) < P.U ^ ((95:ℝ)/2) := Real.rpow_pos_of_pos hUpos _
  rw [Bcombine_eq]
  push_cast
  -- the seven `(H/Δ)`-weighted monomials and the `ℓ`-weight
  have hℓ1R : (1:ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) + 1 ≤ (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hw0 : (0:ℝ) ≤ 1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))) := by
    have hL : (0:ℝ) < (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) := by
      have h2 : (0:ℝ) < (ℓ₂ : ℝ) := by linarith
      have hd : (0:ℝ) < (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by linarith
      positivity
    positivity
  set w : ℝ := 1 + P.G * S.Ω ^ 5 / ((ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ))) with hwdef
  -- Step-1 conversion: `10⁵⁵·R·δ = 10¹¹⁵·(H/Δ)·M₁`
  have he1 : 10 ^ 55 * (S.R * (10 ^ 60 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 15 / S.Ω ^ 5))) * w
      = 10 ^ 115 * ((P.H / S.Δ) * (P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 2)) * w) := by
    rw [Scale.R]; field_simp
  -- the seven nonneg `(H/Δ)`-weighted slots
  have hX1 : (0:ℝ) ≤ (P.H / S.Δ) * (P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 2)) * w := by
    have : (0:ℝ) ≤ (P.H / S.Δ) * (P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 2)) := by positivity
    exact mul_nonneg this hw0
  have hX2 : (0:ℝ) ≤ (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 5 * P.U ^ 45 / (P.H * S.Ω ^ 14)) := by
    positivity
  have hX3 : (0:ℝ) ≤ (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8)) := by
    positivity
  have hX4 : (0:ℝ) ≤ (P.H / S.Δ)
      * (S.Δ ^ 2 * P.G ^ ((15:ℝ)/2) * P.U ^ ((95:ℝ)/2) / (P.H * S.Ω ^ 8)) := by positivity
  have hX5 : (0:ℝ) ≤ (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω)) := by
    positivity
  have hX6 : (0:ℝ) ≤ (P.H / S.Δ) * (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)) := by positivity
  have hX7 : (0:ℝ) ≤ (P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)) := by
    positivity
  -- split the LHS groups into the seven slot shapes (pure `ring` in the field)
  have he2 : (10:ℝ) ^ 408 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
        + (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω ^ 8)))
      = 10 ^ 408 * ((P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 5 * P.U ^ 45 / (P.H * S.Ω ^ 14)))
        + 10 ^ 408 * ((P.H / S.Δ)
            * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))) := by ring
  have he3 : (10:ℝ) ^ 258 * ((P.H / S.Δ)
          * ((S.Δ ^ 2 / P.H) * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2) / S.Ω ^ 8)
        + (P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω)))
      = 10 ^ 258 * ((P.H / S.Δ)
            * (S.Δ ^ 2 * P.G ^ ((15:ℝ)/2) * P.U ^ ((95:ℝ)/2) / (P.H * S.Ω ^ 8)))
        + 10 ^ 258 * ((P.H / S.Δ)
            * (P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω))) := by ring
  have he4 : 80 * (2 * (10:ℝ) ^ 322) * 10 ^ 57 * (P.H / S.Δ) *
        (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
          + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27))
      = 160 * 10 ^ 379 * ((P.H / S.Δ) * (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
        + 160 * 10 ^ 379
            * ((P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27))) := by
    rw [show (80 : ℝ) * (2 * 10 ^ 322) * 10 ^ 57 = 160 * 10 ^ 379 from by norm_num]
    ring
  rw [he1, he2, he3, he4]
  -- expand the RHS into the seven weighted slots and finish linearly
  rw [show 10 ^ 409 * (P.H / S.Δ) *
      ( P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 2) * w
        + S.Δ ^ 2 * P.G ^ 5 * P.U ^ 45 / (P.H * S.Ω ^ 14)
        + P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω ^ 8)
        + S.Δ ^ 2 * P.G ^ ((15 : ℝ) / 2) * P.U ^ ((95 : ℝ) / 2) / (P.H * S.Ω ^ 8)
        + P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1 : ℝ) / 2) * S.Ω)
        + P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)
        + S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27) )
    = 10 ^ 409 * ((P.H / S.Δ) * (P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 2)) * w)
      + 10 ^ 409 * ((P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 5 * P.U ^ 45 / (P.H * S.Ω ^ 14)))
      + 10 ^ 409 * ((P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8)))
      + 10 ^ 409 * ((P.H / S.Δ)
          * (S.Δ ^ 2 * P.G ^ ((15:ℝ)/2) * P.U ^ ((95:ℝ)/2) / (P.H * S.Ω ^ 8)))
      + 10 ^ 409 * ((P.H / S.Δ) * (P.G ^ 7 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω)))
      + 10 ^ 409 * ((P.H / S.Δ) * (P.G ^ 14 * P.U ^ 75 / (S.Δ * S.Ω ^ 13)))
      + 10 ^ 409 * ((P.H / S.Δ) * (S.Δ ^ 2 * P.G ^ 14 * P.U ^ 90 / (P.H * S.Ω ^ 27)))
    from by ring]
  linarith [hX1, hX2, hX3, hX4, hX5, hX6, hX7]

/-- `1 ≤ G²U¹⁵/Ω⁵` (the `Nc`-floor). -/
theorem nc_floor (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U) :
    (1:ℝ) ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 := by
  have hΩpos := S.Ω_pos; have hUpos := P.U_pos
  have hΩ5 : S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩpos.le hΩU 5
  have h15 : P.U ^ 5 ≤ P.U ^ 15 := pow_le_pow_right₀ hU1 (by norm_num)
  have hG2 : (1:ℝ) ≤ P.G ^ 2 := one_le_pow₀ hG1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hΩ5, h15, hG2, pow_pos hUpos 15]

/-- **Step-2 `N`-envelope**: `Mbound(ℓ₁, V₁) + 3/2 ≤ 10¹⁰²·G²U¹⁵/Ω⁵` at `ℓ₁ ≤ 130·G·U⁵`. -/
theorem mbound_step2_env {ℓ₁ : ℕ} (hℓ1GU : (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U) :
    Mbound P S ℓ₁ (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6))) + 3 / 2
      ≤ 10 ^ 102 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hΔpos := S.Δ_pos
  have hHpos := P.H_pos; have hΩpos := S.Ω_pos
  have hNc := nc_floor (P := P) (S := S) hG1 hU1 hΩU
  rw [Mbound]
  -- first term: `10³⁴·ℓ₁·(HGΩ/Δ³)·V₁ = 10⁹⁹·ℓ₁·G·U¹⁰/Ω⁵`
  have he : 10 ^ 34 * ((ℓ₁ : ℤ) : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3)
        * (10 ^ 65 * (S.Δ ^ 3 * P.U ^ 10 / (P.H * S.Ω ^ 6)))
      = 10 ^ 99 * (ℓ₁ : ℝ) * P.G * P.U ^ 10 / S.Ω ^ 5 := by
    push_cast; field_simp
  rw [he]
  -- `ℓ₁ ≤ 130·G·U⁵` folds it into `1.3·10¹⁰¹·G²U¹⁵/Ω⁵`
  have hfold : 10 ^ 99 * (ℓ₁ : ℝ) * P.G * P.U ^ 10 / S.Ω ^ 5
      ≤ 130 * 10 ^ 99 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    rw [show 130 * 10 ^ 99 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)
        = 130 * 10 ^ 99 * (P.G ^ 2 * P.U ^ 15) / S.Ω ^ 5 from by ring,
      div_le_div_iff_of_pos_right (by positivity)]
    have h := mul_le_mul_of_nonneg_right hℓ1GU
      (show (0:ℝ) ≤ 10 ^ 99 * P.G * P.U ^ 10 by positivity)
    nlinarith [h]
  have h32 : (3:ℝ) / 2 ≤ 3 / 2 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by nlinarith [hNc]
  have h34 : 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)
      + 130 * 10 ^ 99 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)
      + 3 / 2 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)
      ≤ 10 ^ 102 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    have hnn : (0:ℝ) ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 := by positivity
    nlinarith [hnn]
  linarith [hfold, h32, h34]

/-- **Step-3 `N`-envelope**: `Mbound(ℓ₁, 10⁶⁰·V₂) + 3/2 ≤ 10⁹⁷·(Na + Nb + Nc)` at
`ℓ₁ ≤ 130·G·U⁵`. -/
theorem mbound_step3_env {ℓ₁ : ℕ} (hℓ1GU : (ℓ₁ : ℝ) ≤ 130 * (P.G * P.U ^ 5))
    (hℓ1 : 0 < ℓ₁) (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΩU : S.Ω ≤ P.U) :
    Mbound P S ℓ₁ (10 ^ 60 * V₂ P S) + 3 / 2
      ≤ 10 ^ 97 * (P.G ^ ((9 : ℝ) / 2) * P.U ^ ((55 : ℝ) / 2) / S.Ω ^ 5)
        + 10 ^ 97 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / S.Δ ^ ((5 : ℝ) / 2))
        + 10 ^ 97 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hΔpos := S.Δ_pos
  have hHpos := P.H_pos; have hΩpos := S.Ω_pos
  have hℓpos : (0:ℝ) < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hNc := nc_floor (P := P) (S := S) hG1 hU1 hΩU
  -- rpow ↔ sqrt translations
  have hG92 : P.G ^ ((9:ℝ)/2) = P.G ^ 4 * Real.sqrt P.G := by
    rw [show (9:ℝ)/2 = ((4:ℕ):ℝ) + (1/2 : ℝ) by push_cast; ring,
      Real.rpow_add hGpos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hU552 : P.U ^ ((55:ℝ)/2) = P.U ^ 27 * Real.sqrt P.U := by
    rw [show (55:ℝ)/2 = ((27:ℕ):ℝ) + (1/2 : ℝ) by push_cast; ring,
      Real.rpow_add hUpos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hΔ52 : S.Δ ^ ((5:ℝ)/2) = S.Δ ^ 2 * Real.sqrt S.Δ := by
    rw [show (5:ℝ)/2 = ((2:ℕ):ℝ) + (1/2 : ℝ) by push_cast; ring,
      Real.rpow_add hΔpos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [Mbound, V₂, hG92, hU552, hΔ52]
  have hsΔpos : (0:ℝ) < Real.sqrt S.Δ := Real.sqrt_pos.mpr hΔpos
  have hsGnn : (0:ℝ) ≤ Real.sqrt P.G := Real.sqrt_nonneg _
  have hsUnn : (0:ℝ) ≤ Real.sqrt P.U := Real.sqrt_nonneg _
  -- split the first `Mbound` term over the two `V₂` pieces
  have hsplit : 10 ^ 34 * ((ℓ₁ : ℤ) : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3)
        * (10 ^ 60 * ((S.Δ ^ 3 / P.H) * (P.G ^ 2 * Real.sqrt P.G
              * (P.U ^ 22 * Real.sqrt P.U)) / S.Ω ^ 6
            + Real.sqrt S.Δ * (P.G ^ 2 * P.U ^ 10 * S.Ω)))
      = 10 ^ 94 * (ℓ₁ : ℝ) * (P.G ^ 3 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
            / S.Ω ^ 5
        + 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2 * Real.sqrt S.Δ)
            / S.Δ ^ 3 := by
    push_cast; field_simp
  rw [hsplit]
  have hsΔpos' : (0:ℝ) < S.Δ ^ 2 * Real.sqrt S.Δ := by positivity
  -- piece a: fold `ℓ₁ ≤ 130·G·U⁵` into `1.3·10⁹⁶·Na`
  have hpa : 10 ^ 94 * (ℓ₁ : ℝ) * (P.G ^ 3 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
        / S.Ω ^ 5
      ≤ 130 * 10 ^ 94 * (P.G ^ 4 * Real.sqrt P.G * (P.U ^ 27 * Real.sqrt P.U) / S.Ω ^ 5) := by
    rw [show 130 * 10 ^ 94 * (P.G ^ 4 * Real.sqrt P.G * (P.U ^ 27 * Real.sqrt P.U) / S.Ω ^ 5)
        = 130 * 10 ^ 94 * (P.G ^ 4 * Real.sqrt P.G * (P.U ^ 27 * Real.sqrt P.U)) / S.Ω ^ 5
        from by ring,
      div_le_div_iff_of_pos_right (by positivity)]
    have h := mul_le_mul_of_nonneg_right hℓ1GU
      (show (0:ℝ) ≤ 10 ^ 94 * (P.G ^ 3 * Real.sqrt P.G * (P.U ^ 22 * Real.sqrt P.U))
          by positivity)
    nlinarith [h]
  -- piece b: fold into `1.3·10⁹⁶·Nb`, using `√Δ·√Δ = Δ`
  have hΔsq : Real.sqrt S.Δ * Real.sqrt S.Δ = S.Δ := Real.mul_self_sqrt hΔpos.le
  have hpb : 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2 * Real.sqrt S.Δ)
        / S.Δ ^ 3
      ≤ 130 * 10 ^ 94
          * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / (S.Δ ^ 2 * Real.sqrt S.Δ)) := by
    -- move the `√Δ` to the denominator first (`√Δ/Δ³ = 1/(Δ²·√Δ)`)
    have heq : 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2 * Real.sqrt S.Δ)
          / S.Δ ^ 3
        = 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2)
          / (S.Δ ^ 2 * Real.sqrt S.Δ) := by
      rw [div_eq_div_iff (by positivity : (0:ℝ) < S.Δ ^ 3).ne' hsΔpos'.ne']
      calc 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2 * Real.sqrt S.Δ)
            * (S.Δ ^ 2 * Real.sqrt S.Δ)
          = 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2) * S.Δ ^ 2
              * (Real.sqrt S.Δ * Real.sqrt S.Δ) := by ring
        _ = 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2) * S.Δ ^ 2 * S.Δ := by
            rw [hΔsq]
        _ = 10 ^ 94 * (ℓ₁ : ℝ) * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2) * S.Δ ^ 3 := by ring
    rw [heq,
      show 130 * 10 ^ 94 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / (S.Δ ^ 2 * Real.sqrt S.Δ))
        = 130 * 10 ^ 94 * (P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15) / (S.Δ ^ 2 * Real.sqrt S.Δ)
        from by ring,
      div_le_div_iff_of_pos_right hsΔpos']
    have h := mul_le_mul_of_nonneg_right hℓ1GU
      (show (0:ℝ) ≤ 10 ^ 94 * (P.H * P.G ^ 3 * P.U ^ 10 * S.Ω ^ 2) by positivity)
    nlinarith [h]
  -- assemble: `1.3·10⁹⁶·Na + 1.3·10⁹⁶·Nb + (10³⁴ + 3/2)·Nc ≤ 10⁹⁷·(Na + Nb + Nc)`
  have hNa_nn : (0:ℝ) ≤ P.G ^ 4 * Real.sqrt P.G * (P.U ^ 27 * Real.sqrt P.U) / S.Ω ^ 5 := by
    positivity
  have hNb_nn : (0:ℝ) ≤ P.H * P.G ^ 4 * S.Ω ^ 2 * P.U ^ 15 / (S.Δ ^ 2 * Real.sqrt S.Δ) := by
    positivity
  have hNc_nn : (0:ℝ) ≤ P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 := by positivity
  have hcoefa : 130 * (10:ℝ) ^ 94 ≤ 10 ^ 97 := by norm_num
  have hca := mul_le_mul_of_nonneg_right hcoefa hNa_nn
  have hcb := mul_le_mul_of_nonneg_right hcoefa hNb_nn
  have h32 : 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) + 3 / 2
      ≤ 10 ^ 97 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
    nlinarith [hNc, hNc_nn]
  linarith [hpa, hpb, hca, hcb, h32]

end Squarefree
