import Squarefree.Lower.DefectBounds
import Squarefree.Geometry.NearCurveAux

/-!
# §5 the global defect bound `|v| ≤ 3·10¹²·ΔU⁵/Ω³` (writeup 709–728)

`v_defect_le`: the defect `v = (d₂−d) − (ℓ₂/ℓ₁)(d₁−d)` of a triple `(d,d₁,d₂)` of `D`-scale
witnesses close to `d̃(r), d̃(r+ℓ₁), d̃(r+ℓ₂)` satisfies `|v| ≤ 3·10¹²·ΔU⁵/Ω³`.

Mechanism: `ℓ₁v = S + E` where `S = ℓ₁d̃(r+ℓ₂) − ℓ₂d̃(r+ℓ₁) + (ℓ₂−ℓ₁)d̃(r)` is the smooth
2nd-difference and `E` collects the closeness errors. By `secondDividedDiff_eq_half_secondDeriv`,
`S = ℓ₁ℓ₂(ℓ₂−ℓ₁)·d̃''(ξ)/2`, so `|S/ℓ₁| ≤ ℓ₂(ℓ₂−ℓ₁)·10¹³(B/R)/2 ≤ ΔU⁵/Ω³` (via `dtilde_d2_bounds`
+ scale `B/R = Δ³/(HG²Ω⁶)` + `h1`/band); and `|E/ℓ₁| ≤ 2(ℓ₂/ℓ₁)·10¹²Δ/(GΩ³) ≤ 2·10¹²·U⁵Δ/Ω³`.
-/

open Squarefree.Counting

set_option maxHeartbeats 1600000

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 global defect bound.** -/
theorem v_defect_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ d d₁ d₂ : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : (ℓ₂ : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ r) (hr2_hi : r + (ℓ₂ : ℝ) ≤ 16 * S.R)
    (hd_close  : |(d : ℝ)  - dtilde P.X r (a : ℝ)|             ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hd1_close : |(d₁ : ℝ) - dtilde P.X (r + (ℓ₁ : ℝ)) (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hd2_close : |(d₂ : ℝ) - dtilde P.X (r + (ℓ₂ : ℝ)) (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hΩU : S.Ω ≤ P.U)
    (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    |((d₂ : ℝ) - (d : ℝ)) - ((ℓ₂ : ℝ) / (ℓ₁ : ℝ)) * ((d₁ : ℝ) - (d : ℝ))|
      ≤ 390000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
  -- abbreviations for the smooth profile
  set dt : ℝ → ℝ := fun s => dtilde P.X s (a : ℝ) with hdt_def
  -- positivity of scales
  have hHpos := P.H_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hΔpos := S.Δ_pos
  have hΩpos := S.Ω_pos
  have hRpos : 0 < S.R := by
    unfold Scale.R; positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  -- casts of the ℓ data
  have hℓ1R : (0 : ℝ) < (ℓ₁ : ℝ) := by exact_mod_cast hℓ1
  have hℓ12R : (ℓ₁ : ℝ) < (ℓ₂ : ℝ) := by exact_mod_cast hℓ12
  have hℓ1_loR : (1 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast hℓ1_lo
  have hℓ2R : (0 : ℝ) < (ℓ₂ : ℝ) := lt_trans hℓ1R hℓ12R
  have hℓ21pos : (0 : ℝ) < (ℓ₂ : ℝ) - (ℓ₁ : ℝ) := by linarith
  -- ℓ₂ ≤ G·U⁵
  have hℓ2W' : (ℓ₂ : ℝ) ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  -- nodes
  set x₁ : ℝ := r + (ℓ₁ : ℝ) with hx1_def
  set x₂ : ℝ := r + (ℓ₂ : ℝ) with hx2_def
  have hx01 : r < x₁ := by rw [hx1_def]; linarith
  have hx12 : x₁ < x₂ := by rw [hx1_def, hx2_def]; linarith
  -- STEP 1 — ContDiffOn
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hC2 : ContDiffOn ℝ 2 dt (Set.Icc r x₂) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hr0 (Set.mem_Icc.mp hx).1
    exact (dtilde_contDiffAt_r P.X_pos haR0 hxpos).contDiffWithinAt
  -- STEP 2 — second divided difference MVT
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    secondDividedDiff_eq_half_secondDeriv hx01 hx12 hC2
  -- the symmetric form
  set SYM : ℝ := dt r / ((r - x₁) * (r - x₂)) + dt x₁ / ((x₁ - r) * (x₁ - x₂))
      + dt x₂ / ((x₂ - r) * (x₂ - x₁)) with hSYM_def
  -- STEP 3 — algebraic identity
  set Sval : ℝ := (ℓ₁ : ℝ) * dt x₂ - (ℓ₂ : ℝ) * dt x₁ + ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * dt r
    with hSval_def
  -- difference values
  have hd_x1r : x₁ - r = (ℓ₁ : ℝ) := by rw [hx1_def]; ring
  have hd_x2r : x₂ - r = (ℓ₂ : ℝ) := by rw [hx2_def]; ring
  have hℓ1ne : (ℓ₁ : ℝ) ≠ 0 := ne_of_gt hℓ1R
  have hℓ2ne : (ℓ₂ : ℝ) ≠ 0 := ne_of_gt hℓ2R
  have hℓ21ne : (ℓ₂ : ℝ) - (ℓ₁ : ℝ) ≠ 0 := ne_of_gt hℓ21pos
  have hS : Sval = (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * SYM := by
    rw [hSval_def, hSYM_def]
    -- rewrite the six difference factors to ℓ-expressions
    rw [show r - x₁ = -(ℓ₁ : ℝ) by rw [hx1_def]; ring,
        show r - x₂ = -(ℓ₂ : ℝ) by rw [hx2_def]; ring,
        show x₁ - r = (ℓ₁ : ℝ) by rw [hx1_def]; ring,
        show x₁ - x₂ = -((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) by rw [hx1_def, hx2_def]; ring,
        show x₂ - r = (ℓ₂ : ℝ) by rw [hx2_def]; ring,
        show x₂ - x₁ = (ℓ₂ : ℝ) - (ℓ₁ : ℝ) by rw [hx1_def, hx2_def]; ring]
    field_simp
    ring
  -- combine with hξ_eq
  have hSval2 : Sval =
      (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * (iteratedDeriv 2 dt ξ / 2) := by
    rw [hS, hξ_eq]
  -- STEP 4 — bound d̃''(ξ)
  have hξpos : 0 < ξ := lt_trans hr0 hξ_mem.1
  have hξ_lo : (1/72) * S.R ≤ ξ := le_of_lt (lt_of_le_of_lt hr_lo hξ_mem.1)
  have hξ_hi : ξ ≤ 16 * S.R := by
    have : ξ < x₂ := hξ_mem.2
    rw [hx2_def] at this; linarith [hr2_hi]
  obtain ⟨hd2pos, _, hd2hi⟩ :=
    dtilde_d2_bounds (S := S) hAD haR0 hξpos ha_lo ha_hi hξ_lo hξ_hi
  -- iteratedDeriv over dt = iteratedDeriv over (fun s => dtilde P.X s a)
  have hd2pos' : 0 < iteratedDeriv 2 dt ξ := hd2pos
  have hd2hi' : iteratedDeriv 2 dt ξ ≤ 10000000000000 * (S.B / S.R) := hd2hi
  -- scale identity B/R
  have hBR : S.B / S.R = S.Δ ^ 3 / (P.H * P.G ^ 2 * S.Ω ^ 6) := by
    rw [Scale.B, Scale.R]; field_simp
  -- STEP 5 — bound |Sval / ℓ₁|
  have hℓfac_pos : (0 : ℝ) < (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) := by positivity
  have habsS : |Sval| =
      (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * iteratedDeriv 2 dt ξ / 2 := by
    rw [hSval2]
    rw [abs_of_nonneg]
    · ring
    · positivity
  -- |Sval|/ℓ₁
  have hSbound : |Sval| / (ℓ₁ : ℝ)
      ≤ 84500000000000000 * P.U ^ 10 * S.Δ ^ 3 / (P.H * S.Ω ^ 6) := by
    rw [habsS]
    -- |Sval|/ℓ₁ = ℓ₂(ℓ₂-ℓ₁) * d̃''(ξ)/2
    have hsimp : (ℓ₁ : ℝ) * (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * iteratedDeriv 2 dt ξ / 2
        / (ℓ₁ : ℝ)
        = (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * iteratedDeriv 2 dt ξ / 2 := by
      field_simp
    rw [hsimp]
    -- bound ℓ₂(ℓ₂-ℓ₁) ≤ (G U⁵)²
    have hℓ2sq : (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) ≤ (130 * (P.G * P.U ^ 5)) ^ 2 := by
      have h1 : (ℓ₂ : ℝ) - (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) := by linarith
      have h2 : (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) ≤ (ℓ₂ : ℝ) * (ℓ₂ : ℝ) := by
        apply mul_le_mul_of_nonneg_left h1 (le_of_lt hℓ2R)
      have h3 : (ℓ₂ : ℝ) * (ℓ₂ : ℝ) ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) := by
        apply mul_le_mul hℓ2W' hℓ2W' (le_of_lt hℓ2R) (by positivity)
      calc (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) ≤ (ℓ₂ : ℝ) * (ℓ₂ : ℝ) := h2
        _ ≤ (130 * (P.G * P.U ^ 5)) * (130 * (P.G * P.U ^ 5)) := h3
        _ = (130 * (P.G * P.U ^ 5)) ^ 2 := by ring
    -- now product bound
    have hd2nonneg : (0 : ℝ) ≤ iteratedDeriv 2 dt ξ := le_of_lt hd2pos'
    have hℓ2sqnn : (0 : ℝ) ≤ (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) := by positivity
    have hBRnn : (0 : ℝ) ≤ S.B / S.R := by rw [hBR]; positivity
    -- product of two ≤ bounds
    have hprod : (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * iteratedDeriv 2 dt ξ
        ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (10000000000000 * (S.B / S.R)) := by
      apply mul_le_mul hℓ2sq _ hd2nonneg (by positivity)
      exact hd2hi'
    -- divide by 2 and rewrite the RHS via hBR
    have hRHS : (130 * (P.G * P.U ^ 5)) ^ 2 * (10000000000000 * (S.B / S.R)) / 2
        = 84500000000000000 * P.U ^ 10 * S.Δ ^ 3 / (P.H * S.Ω ^ 6) := by
      rw [hBR]
      field_simp
      ring
    calc (ℓ₂ : ℝ) * ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * iteratedDeriv 2 dt ξ / 2
        ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (10000000000000 * (S.B / S.R)) / 2 := by
          apply div_le_div_of_nonneg_right hprod (by norm_num)
      _ = 84500000000000000 * P.U ^ 10 * S.Δ ^ 3 / (P.H * S.Ω ^ 6) := hRHS
  -- scale claim: the S-bound is ≤ Δ U⁵ / Ω³
  have hScale : (84500000000000000 : ℝ) * P.U ^ 10 * S.Δ ^ 3 / (P.H * S.Ω ^ 6)
      ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- 5e12 U^10 Δ³ Ω³ ≤ Δ U⁵ (H Ω⁶)
    -- reduce: 5e12 U⁵ Δ² ≤ H Ω³
    -- from h1: G U^10 ≤ H/Δ², so G U^10 Δ² ≤ H
    have hHbound : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < S.Δ ^ 2)).mp h1
      linarith [this]
    -- need: 5e12 ≤ G U⁵ Ω³
    have hΩleU : S.Ω ≤ P.U := hΩU
    have hUbig' : (84500000000000000 : ℝ) ≤ P.U := by
      have : (84500000000000000 : ℝ) ≤ (10:ℝ)^33 := by norm_num
      linarith [hUbig]
    -- G U⁵ Ω³ ≥ (G U³ Ω⁴) * (U² / Ω) ≥ 1 * U = U ≥ 5e12
    have hkey : (84500000000000000 : ℝ) ≤ P.G * P.U ^ 5 * S.Ω ^ 3 := by
      -- U²/Ω ≥ U  (since Ω ≤ U)
      have hU2Ω : P.U ≤ P.U ^ 2 / S.Ω := by
        rw [le_div_iff₀ hΩpos]
        nlinarith [hΩleU, hUpos.le, hU1]
      -- factoring identity
      have hfactor : P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) = P.G * P.U ^ 5 * S.Ω ^ 3 := by
        field_simp
      have hge1 : (1 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
      have hU2Ωpos : (0 : ℝ) ≤ P.U ^ 2 / S.Ω := by positivity
      -- (G U³ Ω⁴)·(U²/Ω) ≥ 1·(U²/Ω) ≥ U ≥ 5e12
      have hchain : (84500000000000000 : ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) := by
        calc (84500000000000000 : ℝ) ≤ P.U := hUbig'
          _ ≤ P.U ^ 2 / S.Ω := hU2Ω
          _ = 1 * (P.U ^ 2 / S.Ω) := by ring
          _ ≤ P.G * P.U ^ 3 * S.Ω ^ 4 * (P.U ^ 2 / S.Ω) :=
              mul_le_mul_of_nonneg_right hge1 hU2Ωpos
      rwa [hfactor] at hchain
    -- combine via intermediate G U^15 Δ³ Ω⁶
    -- LHS ≤ (G U⁵ Ω³) U^10 Δ³ Ω³ = G U^15 Δ³ Ω⁶ ≤ Δ U⁵ (G U^10 Δ²) Ω⁶ ≤ RHS
    have hposL : (0 : ℝ) ≤ P.U ^ 10 * S.Δ ^ 3 * S.Ω ^ 3 := by positivity
    have hL_le_mid : (84500000000000000 : ℝ) * P.U ^ 10 * S.Δ ^ 3 * S.Ω ^ 3
        ≤ P.G * P.U ^ 15 * S.Δ ^ 3 * S.Ω ^ 6 := by
      have := mul_le_mul_of_nonneg_right hkey hposL
      calc (84500000000000000 : ℝ) * P.U ^ 10 * S.Δ ^ 3 * S.Ω ^ 3
          = 84500000000000000 * (P.U ^ 10 * S.Δ ^ 3 * S.Ω ^ 3) := by ring
        _ ≤ (P.G * P.U ^ 5 * S.Ω ^ 3) * (P.U ^ 10 * S.Δ ^ 3 * S.Ω ^ 3) := this
        _ = P.G * P.U ^ 15 * S.Δ ^ 3 * S.Ω ^ 6 := by ring
    have hposR : (0 : ℝ) ≤ S.Δ * P.U ^ 5 * S.Ω ^ 6 := by positivity
    have hmid_le_R : P.G * P.U ^ 15 * S.Δ ^ 3 * S.Ω ^ 6
        ≤ S.Δ * P.U ^ 5 * (P.H * S.Ω ^ 6) := by
      have := mul_le_mul_of_nonneg_left hHbound hposR
      calc P.G * P.U ^ 15 * S.Δ ^ 3 * S.Ω ^ 6
          = (S.Δ * P.U ^ 5 * S.Ω ^ 6) * (P.G * P.U ^ 10 * S.Δ ^ 2) := by ring
        _ ≤ (S.Δ * P.U ^ 5 * S.Ω ^ 6) * P.H := this
        _ = S.Δ * P.U ^ 5 * (P.H * S.Ω ^ 6) := by ring
    calc (84500000000000000 : ℝ) * P.U ^ 10 * S.Δ ^ 3 * S.Ω ^ 3
        ≤ P.G * P.U ^ 15 * S.Δ ^ 3 * S.Ω ^ 6 := hL_le_mid
      _ ≤ S.Δ * P.U ^ 5 * (P.H * S.Ω ^ 6) := hmid_le_R
  -- |Sval|/ℓ₁ ≤ Δ U⁵ / Ω³
  have hSfinal : |Sval| / (ℓ₁ : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := le_trans hSbound hScale
  -- STEP 6 — the closeness error
  set E : ℝ := (ℓ₁ : ℝ) * ((d₂ : ℝ) - dt x₂) - (ℓ₂ : ℝ) * ((d₁ : ℝ) - dt x₁)
      + ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * ((d : ℝ) - dt r) with hE_def
  -- ℓ₁(d₂-d) - ℓ₂(d₁-d) = Sval + E
  have hSE : (ℓ₁ : ℝ) * ((d₂ : ℝ) - (d : ℝ)) - (ℓ₂ : ℝ) * ((d₁ : ℝ) - (d : ℝ))
      = Sval + E := by
    rw [hSval_def, hE_def]; ring
  -- bound |E|
  have hEbound : |E| / (ℓ₁ : ℝ) ≤ 260000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    -- triangle inequality
    have hδ : (0:ℝ) ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by positivity
    have hb_d2 : |(ℓ₁ : ℝ) * ((d₂ : ℝ) - dt x₂)|
        ≤ (ℓ₁ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
      rw [abs_mul, abs_of_pos hℓ1R]
      exact mul_le_mul_of_nonneg_left hd2_close (le_of_lt hℓ1R)
    have hb_d1 : |(ℓ₂ : ℝ) * ((d₁ : ℝ) - dt x₁)|
        ≤ (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
      rw [abs_mul, abs_of_pos hℓ2R]
      exact mul_le_mul_of_nonneg_left hd1_close (le_of_lt hℓ2R)
    have hb_d : |((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * ((d : ℝ) - dt r)|
        ≤ ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
      rw [abs_mul, abs_of_pos hℓ21pos]
      exact mul_le_mul_of_nonneg_left hd_close (le_of_lt hℓ21pos)
    -- |E| ≤ sum
    have htri : |E| ≤ (ℓ₁ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        + (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        + ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
      have := abs_add_three ((ℓ₁ : ℝ) * ((d₂ : ℝ) - dt x₂))
        (-((ℓ₂ : ℝ) * ((d₁ : ℝ) - dt x₁)))
        (((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * ((d : ℝ) - dt r))
      have heq : (ℓ₁ : ℝ) * ((d₂ : ℝ) - dt x₂) + -((ℓ₂ : ℝ) * ((d₁ : ℝ) - dt x₁))
          + ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * ((d : ℝ) - dt r) = E := by rw [hE_def]; ring
      rw [heq] at this
      rw [abs_neg] at this
      linarith [this, hb_d2, hb_d1, hb_d]
    -- sum of ℓ coeffs = 2 ℓ₂
    have hsum_coeff : (ℓ₁ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        + (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        + ((ℓ₂ : ℝ) - (ℓ₁ : ℝ)) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
        = 2 * (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by ring
    -- so |E| ≤ 2 ℓ₂ * δ ≤ 2 G U⁵ δ
    have hEle : |E| ≤ 2 * (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
      rw [← hsum_coeff]; exact htri
    -- 2 ℓ₂ δ ≤ 2 G U⁵ δ = 2e12 U⁵ Δ / Ω³
    have hEle2 : |E| ≤ 260000000000000 * P.U ^ 5 * S.Δ / S.Ω ^ 3 := by
      have hδ' : (0:ℝ) ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := hδ
      have hℓ2bnd : 2 * (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
          ≤ 2 * (130 * (P.G * P.U ^ 5)) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := by
        apply mul_le_mul_of_nonneg_right _ hδ'
        nlinarith [hℓ2W', hℓ2R.le]
      have heqf : 2 * (130 * (P.G * P.U ^ 5)) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
          = 260000000000000 * P.U ^ 5 * S.Δ / S.Ω ^ 3 := by
        field_simp
        ring
      calc |E| ≤ 2 * (ℓ₂ : ℝ) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := hEle
        _ ≤ 2 * (130 * (P.G * P.U ^ 5)) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) := hℓ2bnd
        _ = 260000000000000 * P.U ^ 5 * S.Δ / S.Ω ^ 3 := heqf
    -- |E|/ℓ₁ ≤ |E| ≤ 2e12 U⁵ Δ/Ω³ = 2e12 (Δ U⁵/Ω³)
    have hdivle : |E| / (ℓ₁ : ℝ) ≤ |E| := div_le_self (abs_nonneg E) hℓ1_loR
    have heqRHS : (260000000000000 : ℝ) * P.U ^ 5 * S.Δ / S.Ω ^ 3
        = 260000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by ring
    calc |E| / (ℓ₁ : ℝ) ≤ |E| := hdivle
      _ ≤ 260000000000000 * P.U ^ 5 * S.Δ / S.Ω ^ 3 := hEle2
      _ = 260000000000000 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := heqRHS
  -- STEP 7 — conclude
  -- LHS = (Sval + E)/ℓ₁
  have hLHS : ((d₂ : ℝ) - (d : ℝ)) - ((ℓ₂ : ℝ) / (ℓ₁ : ℝ)) * ((d₁ : ℝ) - (d : ℝ))
      = (Sval + E) / (ℓ₁ : ℝ) := by
    rw [← hSE]
    field_simp
  rw [hLHS]
  -- |Sval+E|/ℓ₁ ≤ |Sval|/ℓ₁ + |E|/ℓ₁
  have htriF : |(Sval + E) / (ℓ₁ : ℝ)| ≤ |Sval| / (ℓ₁ : ℝ) + |E| / (ℓ₁ : ℝ) := by
    rw [abs_div, abs_of_pos hℓ1R, ← add_div]
    exact div_le_div_of_nonneg_right (abs_add_le Sval E) hℓ1R.le
  -- final bound: |Sval|/ℓ₁ + |E|/ℓ₁ ≤ X + 2e12·X ≤ 3e12·X with X = Δ U⁵/Ω³
  set X : ℝ := S.Δ * P.U ^ 5 / S.Ω ^ 3 with hX_def
  have hXnn : (0 : ℝ) ≤ X := by rw [hX_def]; positivity
  have hfinal : |Sval| / (ℓ₁ : ℝ) + |E| / (ℓ₁ : ℝ)
      ≤ 390000000000000 * X := by
    have h1' : |Sval| / (ℓ₁ : ℝ) ≤ X := hSfinal
    have h2' : |E| / (ℓ₁ : ℝ) ≤ 260000000000000 * X := hEbound
    linarith [h1', h2', hXnn]
  linarith [htriF, hfinal]

end Squarefree
