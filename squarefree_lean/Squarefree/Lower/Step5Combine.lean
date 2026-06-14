import Mathlib

/-!
# §5 Step-5 algebraic core (writeup 1179–1216)

The "8 terms → 3 terms" reduction, in substituted variables
`g = G^{1/4}, u = U^{1/4}, dl = √Δ, ω = Ω` so all powers are integers.

The eight LHS terms are the LANDED per-range monomials (R7 reconciliation):
* `T1a = g¹⁶u⁶⁰/(dl²ω²)` — Step-1 base `G⁴U¹⁵/(ΔΩ²)`;
* `T1b = g²⁰u⁶⁰ω³/dl²` — the Step-1 `ℓ`-weight leg `t1·GΩ⁵` (the `1/L ≤ 1` collapse);
* `T2 = dl⁴g²⁰u¹⁸⁰/(Hω¹⁴)`, `T3 = g²⁰u¹⁴⁰/(dlω⁸)` — Step-2 at `G⁵` (post-δ₂₃ bump);
* `T4′ = dl⁴g³⁰u¹⁹⁰/(Hω⁸)`, `T5′ = g²⁸u¹⁴⁰/(dlω)` — Step-3 landed (payless hHbig-route)
  `(Δ²/H)G^{15/2}U^{95/2}/Ω⁸` and `G⁷U³⁵/(√ΔΩ)`;
* `T6′ = g⁶⁰u³⁰⁰/(dl²ω¹³)`, `T7′ = dl⁴g⁶⁰u³⁶⁰/(Hω²⁷)` — Step-4 capstone
  `G¹⁵U⁷⁵/(ΔΩ¹³)` and `Δ²G¹⁵U⁹⁰/(HΩ²⁷)`.

`S1 = g²⁸u¹⁶⁴/(dlω)` (= `G⁷U⁴¹/(√ΔΩ)`), the `t5′`-`G⁷` floor.

Mapping: `S1 ← {T1a,T3,T5′}`, `S2 ← {T1b,T6′}`, `S3 ← {T2,T4′,T7′}` (≤ 3 each).
This is a pure polynomial inequality.
-/

namespace Squarefree

set_option maxHeartbeats 1600000

theorem step5_combine_core (g u dl ω H : ℝ)
    (hg0 : 0 < g) (hu0 : 0 < u) (hdl0 : 0 < dl) (hω0 : 0 < ω) (hH0 : 0 < H)
    (hg1 : 1 ≤ g) (hu1 : 1 ≤ u)
    (hΩU : ω ≤ u ^ 4)                 -- Ω ≤ U
    (hband : 1 ≤ g * u ^ 3 * ω)       -- Ω ≥ G^{-1/4}U^{-3/4}
    (hΔ : g ^ 4 * u ^ 10 ≤ dl) :      -- Δ ≥ G²U⁵  (√: dl ≥ g⁴u¹⁰)
    g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2)
      + g ^ 20 * u ^ 60 * ω ^ 3 / dl ^ 2
      + dl ^ 4 * g ^ 20 * u ^ 180 / (H * ω ^ 14)
      + g ^ 20 * u ^ 140 / (dl * ω ^ 8)
      + dl ^ 4 * g ^ 30 * u ^ 190 / (H * ω ^ 8)
      + g ^ 28 * u ^ 140 / (dl * ω)
      + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)
      + dl ^ 4 * g ^ 60 * u ^ 360 / (H * ω ^ 27)
    ≤ 3 * ( g ^ 28 * u ^ 164 / (dl * ω)                    -- S1
          + g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13)            -- S2
          + dl ^ 4 * g ^ 60 * u ^ 360 / (H * ω ^ 27) ) := by  -- S3
  -- abbreviations for the three target terms
  set S1 := g ^ 28 * u ^ 164 / (dl * ω) with hS1def
  set S2 := g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13) with hS2def
  set S3 := dl ^ 4 * g ^ 60 * u ^ 360 / (H * ω ^ 27) with hS3def
  -- nonnegativity of the targets
  have hS1nn : 0 ≤ S1 := by rw [hS1def]; positivity
  have hS2nn : 0 ≤ S2 := by rw [hS2def]; positivity
  have hS3nn : 0 ≤ S3 := by rw [hS3def]; positivity
  -- T1a ≤ S1
  have hT1a : g ^ 16 * u ^ 60 / (dl ^ 2 * ω ^ 2) ≤ S1 := by
    rw [hS1def]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- core (after dividing common dl·ω):  g^16 u^60 ≤ g^28 u^164 dl ω
    have hcore : g ^ 16 * u ^ 60 ≤ g ^ 28 * u ^ 164 * (dl * ω) := by
      -- dl ω ≥ g^4 u^10 ω, so RHS ≥ g^32 u^174 ω
      have hA : g ^ 32 * u ^ 174 * ω ≤ g ^ 28 * u ^ 164 * (dl * ω) := by
        have : g ^ 28 * u ^ 164 * (g ^ 4 * u ^ 10) * ω
            ≤ g ^ 28 * u ^ 164 * dl * ω :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hΔ (by positivity)) hω0.le
        nlinarith [this]
      -- g^32 u^174 ω ≥ g^16 u^60 :  ⟺ g^16 u^114 ω ≥ 1
      have hB : g ^ 16 * u ^ 60 ≤ g ^ 32 * u ^ 174 * ω := by
        have hge1 : (1 : ℝ) ≤ g ^ 15 * u ^ 111 := by
          nlinarith [one_le_pow₀ (n := 15) hg1, one_le_pow₀ (n := 111) hu1,
            pow_pos hg0 15, pow_pos hu0 111]
        have hbandprod : (1 : ℝ) ≤ g ^ 16 * u ^ 114 * ω := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (g ^ 15 * u ^ 111) * (g * u ^ 3 * ω) :=
                  mul_le_mul hge1 hband (by norm_num) (by positivity)
            _ = g ^ 16 * u ^ 114 * ω := by ring
        have : g ^ 16 * u ^ 60 * 1 ≤ g ^ 16 * u ^ 60 * (g ^ 16 * u ^ 114 * ω) :=
          mul_le_mul_of_nonneg_left hbandprod (by positivity)
        nlinarith [this]
      linarith [hA, hB]
    nlinarith [mul_le_mul_of_nonneg_right hcore (mul_pos hdl0 hω0).le,
      mul_pos hdl0 hω0, hcore]
  -- T1b ≤ S2  (the Step-1 ℓ-weight leg t1·g⁴ω⁵)
  have hT1b : g ^ 20 * u ^ 60 * ω ^ 3 / dl ^ 2 ≤ S2 := by
    rw [hS2def, div_le_div_iff₀ (by positivity) (by positivity)]
    -- g^20 u^60 ω^3 (dl² ω^13) ≤ g^60 u^300 dl² ;  core: g^20 u^60 ω^16 ≤ g^60 u^300
    have hω16 : ω ^ 16 ≤ u ^ 64 := by
      calc ω ^ 16 ≤ (u ^ 4) ^ 16 := pow_le_pow_left₀ hω0.le hΩU 16
        _ = u ^ 64 := by ring
    have hcore : g ^ 20 * u ^ 60 * ω ^ 16 ≤ g ^ 60 * u ^ 300 := by
      have h1 : g ^ 20 * u ^ 60 * ω ^ 16 ≤ g ^ 20 * u ^ 60 * u ^ 64 := by
        nlinarith [hω16, mul_pos (pow_pos hg0 20) (pow_pos hu0 60)]
      have h2 : g ^ 20 * u ^ 60 * u ^ 64 ≤ g ^ 60 * u ^ 300 := by
        have e1 : g ^ 20 * u ^ 60 * u ^ 64 = g ^ 20 * u ^ 124 := by ring
        rw [e1]
        have hgle : g ^ 20 ≤ g ^ 60 := pow_le_pow_right₀ hg1 (by norm_num)
        have hule : u ^ 124 ≤ u ^ 300 := pow_le_pow_right₀ hu1 (by norm_num)
        calc g ^ 20 * u ^ 124 ≤ g ^ 60 * u ^ 124 :=
              mul_le_mul_of_nonneg_right hgle (by positivity)
          _ ≤ g ^ 60 * u ^ 300 := mul_le_mul_of_nonneg_left hule (by positivity)
      linarith [h1, h2]
    have hfac : g ^ 20 * u ^ 60 * ω ^ 3 * (dl ^ 2 * ω ^ 13)
        = dl ^ 2 * (g ^ 20 * u ^ 60 * ω ^ 16) := by ring
    have hfac2 : g ^ 60 * u ^ 300 * dl ^ 2 = dl ^ 2 * (g ^ 60 * u ^ 300) := by ring
    rw [hfac, hfac2]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  -- T2 ≤ S3
  have hT2 : dl ^ 4 * g ^ 20 * u ^ 180 / (H * ω ^ 14) ≤ S3 := by
    rw [hS3def, div_le_div_iff₀ (by positivity) (by positivity)]
    -- core: g^20 u^180 ω^13 ≤ g^60 u^360, with ω^13 ≤ u^52
    have hω13 : ω ^ 13 ≤ u ^ 52 := by
      calc ω ^ 13 ≤ (u ^ 4) ^ 13 := pow_le_pow_left₀ hω0.le hΩU 13
        _ = u ^ 52 := by ring
    have hcore : g ^ 20 * u ^ 180 * ω ^ 13 ≤ g ^ 60 * u ^ 360 := by
      have h1 : g ^ 20 * u ^ 180 * ω ^ 13 ≤ g ^ 20 * u ^ 180 * u ^ 52 := by
        nlinarith [hω13, mul_pos (pow_pos hg0 20) (pow_pos hu0 180)]
      have h2 : g ^ 20 * u ^ 180 * u ^ 52 ≤ g ^ 60 * u ^ 360 := by
        have e1 : g ^ 20 * u ^ 180 * u ^ 52 = g ^ 20 * u ^ 232 := by ring
        rw [e1]
        have hgle : g ^ 20 ≤ g ^ 60 := pow_le_pow_right₀ hg1 (by norm_num)
        have hule : u ^ 232 ≤ u ^ 360 := pow_le_pow_right₀ hu1 (by norm_num)
        calc g ^ 20 * u ^ 232 ≤ g ^ 60 * u ^ 232 :=
              mul_le_mul_of_nonneg_right hgle (by positivity)
          _ ≤ g ^ 60 * u ^ 360 := mul_le_mul_of_nonneg_left hule (by positivity)
      linarith [h1, h2]
    have hfac : dl ^ 4 * g ^ 20 * u ^ 180 * (H * ω ^ 27)
        = (dl ^ 4 * H * ω ^ 14) * (g ^ 20 * u ^ 180 * ω ^ 13) := by ring
    have hfac2 : dl ^ 4 * g ^ 60 * u ^ 360 * (H * ω ^ 14)
        = (dl ^ 4 * H * ω ^ 14) * (g ^ 60 * u ^ 360) := by ring
    rw [hfac, hfac2]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  -- T3 ≤ S1
  have hT3 : g ^ 20 * u ^ 140 / (dl * ω ^ 8) ≤ S1 := by
    rw [hS1def, div_le_div_iff₀ (by positivity) (by positivity)]
    -- core (divide common dl):  g^20 u^140 ω ≤ g^28 u^164 ω^8
    have hcore : g ^ 20 * u ^ 140 * ω ≤ g ^ 28 * u ^ 164 * ω ^ 8 := by
      have hbpow : (1 : ℝ) ≤ (g * u ^ 3 * ω) ^ 7 := one_le_pow₀ hband
      have hbexp : (g * u ^ 3 * ω) ^ 7 = g ^ 7 * u ^ 21 * ω ^ 7 := by ring
      have hband7 : (1 : ℝ) ≤ g ^ 7 * u ^ 21 * ω ^ 7 := by rw [← hbexp]; exact hbpow
      -- g^20 u^140 ≤ g^27 u^161 ω^7 ≤ g^28 u^164 ω^7
      have hkey : g ^ 20 * u ^ 140 ≤ g ^ 28 * u ^ 164 * ω ^ 7 := by
        have h1 : g ^ 20 * u ^ 140 * 1 ≤ g ^ 20 * u ^ 140 * (g ^ 7 * u ^ 21 * ω ^ 7) :=
          mul_le_mul_of_nonneg_left hband7 (by positivity)
        have h2 : g ^ 20 * u ^ 140 * (g ^ 7 * u ^ 21 * ω ^ 7)
            = g ^ 27 * u ^ 161 * ω ^ 7 := by ring
        have h3 : g ^ 27 * u ^ 161 * ω ^ 7 ≤ g ^ 28 * u ^ 164 * ω ^ 7 := by
          have hgle : g ^ 27 ≤ g ^ 28 := pow_le_pow_right₀ hg1 (by norm_num)
          have hule : u ^ 161 ≤ u ^ 164 := pow_le_pow_right₀ hu1 (by norm_num)
          calc g ^ 27 * u ^ 161 * ω ^ 7
              ≤ g ^ 28 * u ^ 161 * ω ^ 7 :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hgle (by positivity)) (by positivity)
            _ ≤ g ^ 28 * u ^ 164 * ω ^ 7 :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hule (by positivity)) (by positivity)
        nlinarith [h1, h2, h3]
      have h4 : (g ^ 20 * u ^ 140) * ω ≤ (g ^ 28 * u ^ 164 * ω ^ 7) * ω :=
        mul_le_mul_of_nonneg_right hkey hω0.le
      nlinarith [h4]
    nlinarith [mul_le_mul_of_nonneg_right hcore hdl0.le, hcore, hdl0]
  -- T4' ≤ S3  (Step-3 landed t4' = dl^4 g^30 u^190/(H ω^8))
  have hT4 : dl ^ 4 * g ^ 30 * u ^ 190 / (H * ω ^ 8) ≤ S3 := by
    rw [hS3def, div_le_div_iff₀ (by positivity) (by positivity)]
    -- core: g^30 u^190 ω^19 ≤ g^60 u^360, with ω^19 ≤ u^76
    have hω19 : ω ^ 19 ≤ u ^ 76 := by
      calc ω ^ 19 ≤ (u ^ 4) ^ 19 := pow_le_pow_left₀ hω0.le hΩU 19
        _ = u ^ 76 := by ring
    have hcore : g ^ 30 * u ^ 190 * ω ^ 19 ≤ g ^ 60 * u ^ 360 := by
      have h1 : g ^ 30 * u ^ 190 * ω ^ 19 ≤ g ^ 30 * u ^ 190 * u ^ 76 := by
        nlinarith [hω19, mul_pos (pow_pos hg0 30) (pow_pos hu0 190)]
      have h2 : g ^ 30 * u ^ 190 * u ^ 76 ≤ g ^ 60 * u ^ 360 := by
        have e1 : g ^ 30 * u ^ 190 * u ^ 76 = g ^ 30 * u ^ 266 := by ring
        rw [e1]
        have hgle : g ^ 30 ≤ g ^ 60 := pow_le_pow_right₀ hg1 (by norm_num)
        have hule : u ^ 266 ≤ u ^ 360 := pow_le_pow_right₀ hu1 (by norm_num)
        calc g ^ 30 * u ^ 266 ≤ g ^ 60 * u ^ 266 :=
              mul_le_mul_of_nonneg_right hgle (by positivity)
          _ ≤ g ^ 60 * u ^ 360 := mul_le_mul_of_nonneg_left hule (by positivity)
      linarith [h1, h2]
    have hfac : dl ^ 4 * g ^ 30 * u ^ 190 * (H * ω ^ 27)
        = (dl ^ 4 * H * ω ^ 8) * (g ^ 30 * u ^ 190 * ω ^ 19) := by ring
    have hfac2 : dl ^ 4 * g ^ 60 * u ^ 360 * (H * ω ^ 8)
        = (dl ^ 4 * H * ω ^ 8) * (g ^ 60 * u ^ 360) := by ring
    rw [hfac, hfac2]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  -- T5' ≤ S1  (Step-3 landed t5' = g^28 u^140/(dl ω))
  have hT5 : g ^ 28 * u ^ 140 / (dl * ω) ≤ S1 := by
    rw [hS1def, div_le_div_iff₀ (by positivity) (by positivity)]
    have hule : u ^ 140 ≤ u ^ 164 := pow_le_pow_right₀ hu1 (by norm_num)
    have hcore : g ^ 28 * u ^ 140 ≤ g ^ 28 * u ^ 164 :=
      mul_le_mul_of_nonneg_left hule (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hcore (mul_pos hdl0 hω0).le, mul_pos hdl0 hω0]
  -- T6' = S2
  have hT6 : g ^ 60 * u ^ 300 / (dl ^ 2 * ω ^ 13) ≤ S2 := le_of_eq hS2def.symm
  -- T7' = S3
  have hT7 : dl ^ 4 * g ^ 60 * u ^ 360 / (H * ω ^ 27) ≤ S3 := le_of_eq hS3def.symm
  -- combine: LHS ≤ 3·S1 + 2·S2 + 3·S3 ≤ 3·(S1+S2+S3)
  linarith [hT1a, hT1b, hT2, hT3, hT4, hT5, hT6, hT7, hS1nn, hS2nn, hS3nn]

end Squarefree
