import Squarefree.Lower.DefectUpsilon

/-!
# §5 Step-4 `Υ`-expansion error collapse (writeup 1009, 1013)

`upsilon_err_le` bounds the explicit `O(·/d⁷)` error `ERR` of `Upsilon_expand`
(the RHS of `DefectUpsilon.Upsilon_expand`) by the single writeup scale-monomial
```
ERR ≤ 10^k · (Δ⁴ · G⁵ · U⁴⁵ / (H² · Ω¹⁴)),                                    (writeup 1013)
```
under the per-`r` witness scale bounds (`a ≤ 11A`, `D ≤ d ≤ 2D`, `|b₀| ≤ 3·10¹²B`,
`|v| ≤ 10²⁰·ΔU⁵/Ω³`, `ℓ₂ ≤ W`, `ℓ₁ ≥ 1`, regime).

Mechanism: every one of the five `ERR` pieces is, after pinning each factor to its scale
bound, a constant multiple of the master monomial `W⁴·X·(ΔΩ)·M⁵/(HΔ)⁷ = T` with the
master scale `M = U⁵Δ²/Ω³`.  The dominant inner term is `a·|β|⁵`; the lower-order inner
terms `a²|β|⁴`, `a³|β|³` collapse into it via `ΔΩ ≤ M`.  The single algebraic scale
identity `upsilon_scale_id` discharges the exponent bookkeeping.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 800000


/-- The §5 Step-4 target scale-monomial `T = Δ⁴·G⁵·U⁴⁵/(H²·Ω¹⁴)` (writeup 1013). -/
noncomputable def UpsT (P : Globals) (S : Scale P) : ℝ :=
  S.Δ ^ 4 * P.G ^ 5 * P.U ^ 45 / (P.H ^ 2 * S.Ω ^ 14)

/-- Master collapse identity: `W⁴·X·(ΔΩ)·M⁵/(HΔ)⁷ = T`, with `W = GU⁵`, `M = U⁵Δ²/Ω³`. -/
theorem upsilon_scale_id (P : Globals) (S : Scale P) :
    (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
        * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / (P.H * S.Δ) ^ 7
      = UpsT P S := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold UpsT
  rw [P.X_eq_G_mul_H_pow_five]
  field_simp

/-- **Generic monomial collapse for one `ERR` piece.**  For nonnegative `pref` (the `ℓ`-prefactor),
`Amag` (the `a`-bound) and `bm` (a `|β|`-bound), with `0 ≤ a ≤ Amag`, `0 ≤ |β| ≤ bm`, the inner
cubic/quartic/quintic combination `a·|β|⁵ + a²·|β|⁴ + a³·|β|³` is `≤ 3·Amag·bm³·max(Amag,bm)²`,
and (when `Amag ≤ bm`) `≤ 3·Amag·bm⁵`. -/
theorem inner_le {a β Amag bm : ℝ}
    (ha0 : 0 ≤ a) (haA : a ≤ Amag) (hb0 : 0 ≤ |β|) (hbm : |β| ≤ bm)
    (hAb : Amag ≤ bm) :
    a * |β| ^ 5 + a ^ 2 * |β| ^ 4 + a ^ 3 * |β| ^ 3 ≤ 3 * Amag * bm ^ 5 := by
  have hAmag : 0 ≤ Amag := le_trans ha0 haA
  have hbmnn : 0 ≤ bm := le_trans hb0 hbm
  have t1 : a * |β| ^ 5 ≤ Amag * bm ^ 5 := by
    apply mul_le_mul haA (by gcongr) (by positivity) hAmag
  have t2 : a ^ 2 * |β| ^ 4 ≤ Amag * bm ^ 5 := by
    calc a ^ 2 * |β| ^ 4 ≤ Amag ^ 2 * bm ^ 4 := by
          apply mul_le_mul (by gcongr) (by gcongr) (by positivity) (by positivity)
      _ = Amag * Amag * bm ^ 4 := by ring
      _ ≤ Amag * bm * bm ^ 4 := by gcongr
      _ = Amag * bm ^ 5 := by ring
  have t3 : a ^ 3 * |β| ^ 3 ≤ Amag * bm ^ 5 := by
    calc a ^ 3 * |β| ^ 3 ≤ Amag ^ 3 * bm ^ 3 := by
          apply mul_le_mul (by gcongr) (by gcongr) (by positivity) (by positivity)
      _ = Amag * Amag ^ 2 * bm ^ 3 := by ring
      _ ≤ Amag * bm ^ 2 * bm ^ 3 := by gcongr
      _ = Amag * bm ^ 5 := by ring
  linarith [t1, t2, t3]

/-- **Single-`ERR`-piece collapse.**  A piece of the shape `pref · (c·X·inner/den)`, with the
`ℓ`-prefactor `pref ≤ W⁴`, the inner combination `inner ≤ Cin·(ΔΩ)·M⁵`, and the denominator
`den ≥ denlo > 0`, is `≤ c·Cin·(W⁴·X·(ΔΩ)·M⁵/denlo)`.  (`M = U⁵Δ²/Ω³`, `W = GU⁵`.) -/
theorem piece_le {pref inner den denlo c Cin : ℝ}
    (hpref : 0 ≤ pref) (hprefW : pref ≤ 285610000 * (P.G * P.U ^ 5) ^ 4)
    (hinner : 0 ≤ inner)
    (hinnerC : inner ≤ Cin * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5)
    (hdenlo : 0 < denlo) (hden : denlo ≤ den) (hc : 0 ≤ c) (hCin : 0 ≤ Cin) :
    pref * (c * P.X * inner / den)
      ≤ 285610000 * c * Cin * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / denlo) := by
  have hH := P.H_pos; have hG := P.G_pos; have hU := P.U_pos; have hX := P.X_pos
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have _ := hpref
  have hden0 : 0 < den := lt_of_lt_of_le hdenlo hden
  have hMpow : 0 ≤ (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by positivity
  have hWpow : 0 ≤ (P.G * P.U ^ 5) ^ 4 := by positivity
  calc pref * (c * P.X * inner / den)
      ≤ (285610000 * (P.G * P.U ^ 5) ^ 4) * (c * P.X * (Cin * (S.Δ * S.Ω)
            * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5) / denlo) := by
        gcongr
    _ = 285610000 * c * Cin * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / denlo) := by ring

/-- **Piece-5 collapse: the genuine residual `|Rres|`** (writeup 1013).  Factored out of
`upsilon_err_le` for compile speed.  `M = U⁵Δ²/Ω³` is the master scale. -/
theorem rres_le {a b₀ v d ℓ₁ ℓ₂ M : ℝ}
    (ha0 : 0 < a) (ha11 : a ≤ 11 * (S.Δ * S.Ω))
    (hℓ1R : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5)) (hd_pos : 0 < d)
    (hb0M : ℓ₂ * |b₀| ≤ 390000000000000 * M) (hvM2 : |v| ≤ 2 * 10 ^ 20 * M)
    (hΔΩM : S.Δ * S.Ω ≤ M) (hd7HΔ : (P.H * S.Δ) ^ 7 ≤ d ^ 7)
    (hMeq : M = P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) :
    |Rres P.X a b₀ v d ℓ₁ ℓ₂|
      ≤ (25 * 121 * 285610000 * (8 * (390000000000000 ^ 3 * (2 * 10 ^ 20))
          + 12 * (390000000000000 ^ 2 * (2 * 10 ^ 20) ^ 2)
          + 10 * (390000000000000 * (2 * 10 ^ 20) ^ 3)
          + 3 * ((2 * 10 ^ 20) ^ 4))) * UpsT P S := by
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  have hℓ1nn : 0 ≤ ℓ₁ := hℓ1R.le
  have hℓ2nn : 0 ≤ ℓ₂ := hℓ2R.le
  have ha0' : 0 ≤ a := ha0.le
  have hW_nn : 0 ≤ 130 * (P.G * P.U ^ 5) := by positivity
  have hM_nn : 0 ≤ M := le_trans (by positivity) hΔΩM
  have hHΔ7 : (0:ℝ) < (P.H * S.Δ) ^ 7 := by positivity
  have hUpsT_nn : 0 ≤ UpsT P S := by unfold UpsT; positivity
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have ha2 : a ^ 2 ≤ (11 * (S.Δ * S.Ω)) ^ 2 := pow_le_pow_left₀ ha0' ha11 2
  have hΔΩsq : (S.Δ * S.Ω) ^ 2 ≤ (S.Δ * S.Ω) * M := by
    nlinarith only [hΔΩM, mul_pos hΔpos hΩpos]
  -- the inner poly of `Rres`, abbreviated
  set β : ℝ := 2*b₀^3*ℓ₁^2*ℓ₂^2 - 4*b₀^3*ℓ₁*ℓ₂^3 + 2*b₀^3*ℓ₂^4
    - 6*b₀^2*ℓ₁*ℓ₂^2*v + 6*b₀^2*ℓ₂^3*v - 4*b₀*ℓ₁*ℓ₂*v^2 + 6*b₀*ℓ₂^2*v^2
    - ℓ₁*v^3 + 2*ℓ₂*v^3 with hβdef
  -- `|poly| ≤ 8ℓ₂⁴|b₀|³ + 12ℓ₂³|b₀|²|v| + 10ℓ₂²|b₀||v|² + 3ℓ₂|v|³`
  have hpolyB : |β|
      ≤ 8 * ℓ₂^4 * |b₀| ^ 3 + 12 * ℓ₂^3 * |b₀| ^ 2 * |v| + 10 * ℓ₂^2 * |b₀| * |v| ^ 2
        + 3 * ℓ₂ * |v| ^ 3 := by
    have b1 : |2*b₀^3*ℓ₁^2*ℓ₂^2| ≤ 2 * ℓ₂^4 * |b₀| ^ 3 := by
      rw [show (2:ℝ)*b₀^3*ℓ₁^2*ℓ₂^2 = 2*(ℓ₁^2*ℓ₂^2)*b₀^3 by ring, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ)<2), abs_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ₁^2*ℓ₂^2)]
      have hℓle : ℓ₁^2*ℓ₂^2 ≤ ℓ₂^4 := by
        calc ℓ₁^2*ℓ₂^2 ≤ ℓ₂^2*ℓ₂^2 := by gcongr
          _ = ℓ₂^4 := by ring
      gcongr
    have b2 : |4*b₀^3*ℓ₁*ℓ₂^3| ≤ 4 * ℓ₂^4 * |b₀| ^ 3 := by
      rw [show (4:ℝ)*b₀^3*ℓ₁*ℓ₂^3 = 4*(ℓ₁*ℓ₂^3)*b₀^3 by ring, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ)<4), abs_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ₁*ℓ₂^3)]
      have hℓle : ℓ₁*ℓ₂^3 ≤ ℓ₂^4 := by
        calc ℓ₁*ℓ₂^3 ≤ ℓ₂*ℓ₂^3 := by gcongr
          _ = ℓ₂^4 := by ring
      gcongr
    have b3 : |2*b₀^3*ℓ₂^4| ≤ 2 * ℓ₂^4 * |b₀| ^ 3 := by
      rw [show (2:ℝ)*b₀^3*ℓ₂^4 = 2*ℓ₂^4*b₀^3 by ring, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*ℓ₂^4), abs_pow]
    have b4 : |6*b₀^2*ℓ₁*ℓ₂^2*v| ≤ 6 * ℓ₂^3 * |b₀| ^ 2 * |v| := by
      rw [show (6:ℝ)*b₀^2*ℓ₁*ℓ₂^2*v = 6*(ℓ₁*ℓ₂^2)*b₀^2*v by ring, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ)<6), abs_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ₁*ℓ₂^2)]
      have hℓle : ℓ₁*ℓ₂^2 ≤ ℓ₂^3 := by
        calc ℓ₁*ℓ₂^2 ≤ ℓ₂*ℓ₂^2 := by gcongr
          _ = ℓ₂^3 := by ring
      gcongr
    have b5 : |6*b₀^2*ℓ₂^3*v| ≤ 6 * ℓ₂^3 * |b₀| ^ 2 * |v| := by
      rw [show (6:ℝ)*b₀^2*ℓ₂^3*v = 6*ℓ₂^3*b₀^2*v by ring, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 6*ℓ₂^3), abs_pow]
    have b6 : |4*b₀*ℓ₁*ℓ₂*v^2| ≤ 4 * ℓ₂^2 * |b₀| * |v| ^ 2 := by
      rw [show (4:ℝ)*b₀*ℓ₁*ℓ₂*v^2 = 4*(ℓ₁*ℓ₂)*b₀*v^2 by ring, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ)<4), abs_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ₁*ℓ₂)]
      have hℓle : ℓ₁*ℓ₂ ≤ ℓ₂^2 := by
        calc ℓ₁*ℓ₂ ≤ ℓ₂*ℓ₂ := by gcongr
          _ = ℓ₂^2 := by ring
      gcongr
    have b7 : |6*b₀*ℓ₂^2*v^2| ≤ 6 * ℓ₂^2 * |b₀| * |v| ^ 2 := by
      rw [show (6:ℝ)*b₀*ℓ₂^2*v^2 = 6*ℓ₂^2*b₀*v^2 by ring, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 6*ℓ₂^2), abs_pow]
    have b8 : |ℓ₁*v^3| ≤ 1 * ℓ₂ * |v| ^ 3 := by
      rw [abs_mul, abs_of_nonneg hℓ1nn, abs_pow, one_mul]
      have hℓle : ℓ₁ ≤ ℓ₂ := hℓ12.le
      gcongr
    have b9 : |2*ℓ₂*v^3| ≤ 2 * ℓ₂ * |v| ^ 3 := by
      rw [show (2:ℝ)*ℓ₂*v^3 = 2*ℓ₂*v^3 by ring, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*ℓ₂), abs_pow]
    have htri : |β| ≤ |2*b₀^3*ℓ₁^2*ℓ₂^2| + |4*b₀^3*ℓ₁*ℓ₂^3| + |2*b₀^3*ℓ₂^4|
        + |6*b₀^2*ℓ₁*ℓ₂^2*v| + |6*b₀^2*ℓ₂^3*v| + |4*b₀*ℓ₁*ℓ₂*v^2| + |6*b₀*ℓ₂^2*v^2|
        + |ℓ₁*v^3| + |2*ℓ₂*v^3| := by
      have e : β = 2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4
          + (-(6*b₀^2*ℓ₁*ℓ₂^2*v)) + 6*b₀^2*ℓ₂^3*v + (-(4*b₀*ℓ₁*ℓ₂*v^2)) + 6*b₀*ℓ₂^2*v^2
          + (-(ℓ₁*v^3)) + 2*ℓ₂*v^3 := by rw [hβdef]; ring
      rw [e]
      have h := abs_add_le
        (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4
          + (-(6*b₀^2*ℓ₁*ℓ₂^2*v)) + 6*b₀^2*ℓ₂^3*v + (-(4*b₀*ℓ₁*ℓ₂*v^2)) + 6*b₀*ℓ₂^2*v^2
          + (-(ℓ₁*v^3))) (2*ℓ₂*v^3)
      have t1 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2) (-(4*b₀^3*ℓ₁*ℓ₂^3))
      have t2 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3))) (2*b₀^3*ℓ₂^4)
      have t3 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4)
        (-(6*b₀^2*ℓ₁*ℓ₂^2*v))
      have t4 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4
        + (-(6*b₀^2*ℓ₁*ℓ₂^2*v))) (6*b₀^2*ℓ₂^3*v)
      have t5 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4
        + (-(6*b₀^2*ℓ₁*ℓ₂^2*v)) + 6*b₀^2*ℓ₂^3*v) (-(4*b₀*ℓ₁*ℓ₂*v^2))
      have t6 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4
        + (-(6*b₀^2*ℓ₁*ℓ₂^2*v)) + 6*b₀^2*ℓ₂^3*v + (-(4*b₀*ℓ₁*ℓ₂*v^2))) (6*b₀*ℓ₂^2*v^2)
      have t7 := abs_add_le (2*b₀^3*ℓ₁^2*ℓ₂^2 + (-(4*b₀^3*ℓ₁*ℓ₂^3)) + 2*b₀^3*ℓ₂^4
        + (-(6*b₀^2*ℓ₁*ℓ₂^2*v)) + 6*b₀^2*ℓ₂^3*v + (-(4*b₀*ℓ₁*ℓ₂*v^2)) + 6*b₀*ℓ₂^2*v^2)
        (-(ℓ₁*v^3))
      simp only [abs_neg] at h t1 t2 t3 t4 t5 t6 t7
      linarith [h, t1, t2, t3, t4, t5, t6, t7]
    linarith [htri, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  -- pairing facts
  have hvnn' : 0 ≤ |v| := abs_nonneg v
  have hℓb_nn : 0 ≤ ℓ₂ * |b₀| := by positivity
  have h3M_nn : 0 ≤ 390000000000000 * M := by positivity
  have hℓbcube : (ℓ₂ * |b₀|) ^ 3 ≤ (390000000000000 * M) ^ 3 := pow_le_pow_left₀ hℓb_nn hb0M 3
  have hℓbsq : (ℓ₂ * |b₀|) ^ 2 ≤ (390000000000000 * M) ^ 2 := pow_le_pow_left₀ hℓb_nn hb0M 2
  have hv2 : |v| ^ 2 ≤ (2 * 10 ^ 20 * M) ^ 2 := pow_le_pow_left₀ hvnn' hvM2 2
  have hv3 : |v| ^ 3 ≤ (2 * 10 ^ 20 * M) ^ 3 := pow_le_pow_left₀ hvnn' hvM2 3
  have hv4 : |v| ^ 4 ≤ (2 * 10 ^ 20 * M) ^ 4 := pow_le_pow_left₀ hvnn' hvM2 4
  have hTA : ℓ₂ ^ 4 * |b₀| ^ 3 * |v|
      ≤ (130 * (P.G * P.U ^ 5)) * (390000000000000 * M) ^ 3 * (2 * 10 ^ 20 * M) := by
    calc ℓ₂ ^ 4 * |b₀| ^ 3 * |v| = (ℓ₂ * |b₀|) ^ 3 * ℓ₂ * |v| := by ring
      _ ≤ (390000000000000 * M) ^ 3 * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) :=
          mul_le_mul (mul_le_mul hℓbcube hℓ2W' hℓ2nn (by positivity)) hvM2 hvnn' (by positivity)
      _ = (130 * (P.G * P.U ^ 5)) * (390000000000000 * M) ^ 3 * (2 * 10 ^ 20 * M) := by ring
  have hTB : ℓ₂ ^ 3 * |b₀| ^ 2 * |v| ^ 2
      ≤ (130 * (P.G * P.U ^ 5)) * (390000000000000 * M) ^ 2 * (2 * 10 ^ 20 * M) ^ 2 := by
    calc ℓ₂ ^ 3 * |b₀| ^ 2 * |v| ^ 2 = (ℓ₂ * |b₀|) ^ 2 * ℓ₂ * |v| ^ 2 := by ring
      _ ≤ (390000000000000 * M) ^ 2 * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) ^ 2 :=
          mul_le_mul (mul_le_mul hℓbsq hℓ2W' hℓ2nn (by positivity)) hv2 (by positivity)
            (by positivity)
      _ = (130 * (P.G * P.U ^ 5)) * (390000000000000 * M) ^ 2 * (2 * 10 ^ 20 * M) ^ 2 := by ring
  have hTC : ℓ₂ ^ 2 * |b₀| * |v| ^ 3
      ≤ (130 * (P.G * P.U ^ 5)) * (390000000000000 * M) * (2 * 10 ^ 20 * M) ^ 3 := by
    calc ℓ₂ ^ 2 * |b₀| * |v| ^ 3 = (ℓ₂ * |b₀|) * ℓ₂ * |v| ^ 3 := by ring
      _ ≤ (390000000000000 * M) * (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) ^ 3 :=
          mul_le_mul (mul_le_mul hb0M hℓ2W' hℓ2nn h3M_nn) hv3 (by positivity) (by positivity)
      _ = (130 * (P.G * P.U ^ 5)) * (390000000000000 * M) * (2 * 10 ^ 20 * M) ^ 3 := by ring
  have hTD : ℓ₂ * |v| ^ 4 ≤ (130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) ^ 4 :=
    mul_le_mul hℓ2W' hv4 (by positivity) hW_nn
  have hℓ13W : ℓ₁ ^ 3 ≤ (130 * (P.G * P.U ^ 5)) ^ 3 := by gcongr
  set Csum : ℝ := 8 * (390000000000000 ^ 3 * (2 * 10 ^ 20))
      + 12 * (390000000000000 ^ 2 * (2 * 10 ^ 20) ^ 2)
      + 10 * (390000000000000 * (2 * 10 ^ 20) ^ 3)
      + 3 * ((2 * 10 ^ 20) ^ 4) with hCsumdef
  have hCsum_nn : 0 ≤ Csum := by rw [hCsumdef]; positivity
  have hSigma : |v| * (8 * ℓ₂^4 * |b₀| ^ 3 + 12 * ℓ₂^3 * |b₀| ^ 2 * |v|
        + 10 * ℓ₂^2 * |b₀| * |v| ^ 2 + 3 * ℓ₂ * |v| ^ 3)
      ≤ (130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum := by
    have hexp : |v| * (8 * ℓ₂^4 * |b₀| ^ 3 + 12 * ℓ₂^3 * |b₀| ^ 2 * |v|
          + 10 * ℓ₂^2 * |b₀| * |v| ^ 2 + 3 * ℓ₂ * |v| ^ 3)
        = 8 * (ℓ₂ ^ 4 * |b₀| ^ 3 * |v|) + 12 * (ℓ₂ ^ 3 * |b₀| ^ 2 * |v| ^ 2)
          + 10 * (ℓ₂ ^ 2 * |b₀| * |v| ^ 3) + 3 * (ℓ₂ * |v| ^ 4) := by ring
    rw [hexp]
    have hbound : 8 * (ℓ₂ ^ 4 * |b₀| ^ 3 * |v|) + 12 * (ℓ₂ ^ 3 * |b₀| ^ 2 * |v| ^ 2)
          + 10 * (ℓ₂ ^ 2 * |b₀| * |v| ^ 3) + 3 * (ℓ₂ * |v| ^ 4)
        ≤ 8 * ((130 * (P.G * P.U ^ 5)) * (390000000000000 * M) ^ 3 * (2 * 10 ^ 20 * M))
          + 12 * ((130 * (P.G * P.U ^ 5)) * (390000000000000 * M) ^ 2 * (2 * 10 ^ 20 * M) ^ 2)
          + 10 * ((130 * (P.G * P.U ^ 5)) * (390000000000000 * M) * (2 * 10 ^ 20 * M) ^ 3)
          + 3 * ((130 * (P.G * P.U ^ 5)) * (2 * 10 ^ 20 * M) ^ 4) := by
      refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
      · exact mul_le_mul_of_nonneg_left hTA (by norm_num)
      · exact mul_le_mul_of_nonneg_left hTB (by norm_num)
      · exact mul_le_mul_of_nonneg_left hTC (by norm_num)
      · exact mul_le_mul_of_nonneg_left hTD (by norm_num)
    refine le_trans hbound (le_of_eq ?_)
    rw [hCsumdef]; ring
  have hRabs : |Rres P.X a b₀ v d ℓ₁ ℓ₂|
      = 25 * P.X * a ^ 2 * ℓ₁ ^ 3 * |v| * |β| / d ^ 7 := by
    rw [Rres]
    rw [show 25*P.X*a^2*ℓ₁^3*v*β / d^7
          = (25*P.X*a^2*ℓ₁^3) * v * β * (1 / d^7) by rw [hβdef]; ring]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 25*P.X*a^2*ℓ₁^3),
      abs_of_pos (by positivity : (0:ℝ) < 1 / d^7)]
    ring
  have hnumB : 25 * P.X * a ^ 2 * ℓ₁ ^ 3 * |v| * |β|
      ≤ 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
          * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) := by
    have hβnn : 0 ≤ |β| := abs_nonneg β
    have hvβ : |v| * |β| ≤ (130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum :=
      le_trans (mul_le_mul_of_nonneg_left hpolyB hvnn') hSigma
    calc 25 * P.X * a ^ 2 * ℓ₁ ^ 3 * |v| * |β|
        = (25 * P.X) * a ^ 2 * ℓ₁ ^ 3 * (|v| * |β|) := by ring
      _ ≤ (25 * P.X) * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
            * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) := by gcongr
      _ = 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
            * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) := by ring
  have hRHS_collapse : 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
          * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) / d ^ 7
      ≤ 25 * 121 * 285610000 * Csum * UpsT P S := by
    have hnumRnn : 0 ≤ 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
          * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) := by positivity
    have hstep1 : 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
            * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) / d ^ 7
        ≤ 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
            * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) / (P.H * S.Δ) ^ 7 :=
      div_le_div_of_nonneg_left hnumRnn hHΔ7 hd7HΔ
    refine le_trans hstep1 ?_
    have hnum_le : 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
            * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum)
        ≤ (25 * 121 * 285610000 * Csum)
            * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) * M ^ 5) := by
      have hrw : 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
              * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum)
          = (25 * 121 * 285610000 * Csum)
              * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) ^ 2 * M ^ 4) := by ring
      rw [hrw]
      have hbase_nn : 0 ≤ (25 * 121 * 285610000 * Csum) := by positivity
      have hstep : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) ^ 2 * M ^ 4
          ≤ (P.G * P.U ^ 5) ^ 4 * P.X * ((S.Δ * S.Ω) * M) * M ^ 4 := by gcongr
      calc (25 * 121 * 285610000 * Csum)
            * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) ^ 2 * M ^ 4)
          ≤ (25 * 121 * 285610000 * Csum)
              * ((P.G * P.U ^ 5) ^ 4 * P.X * ((S.Δ * S.Ω) * M) * M ^ 4) :=
            mul_le_mul_of_nonneg_left hstep hbase_nn
        _ = (25 * 121 * 285610000 * Csum)
              * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) * M ^ 5) := by ring
    have hfrac : 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
            * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) / (P.H * S.Δ) ^ 7
        ≤ (25 * 121 * 285610000 * Csum)
            * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) * M ^ 5)
            / (P.H * S.Δ) ^ 7 := by
      gcongr
    refine le_trans hfrac ?_
    rw [mul_div_assoc]
    have hTscale : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω) * M ^ 5 / (P.H * S.Δ) ^ 7
        = UpsT P S := by rw [hMeq]; exact upsilon_scale_id P S
    rw [hTscale]
  rw [hRabs]
  calc 25 * P.X * a ^ 2 * ℓ₁ ^ 3 * |v| * |β| / d ^ 7
      ≤ 25 * P.X * (11 * (S.Δ * S.Ω)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 3
          * ((130 * (P.G * P.U ^ 5)) * M ^ 4 * Csum) / d ^ 7 :=
        div_le_div_of_nonneg_right hnumB (by positivity)
    _ ≤ 25 * 121 * 285610000 * Csum * UpsT P S := hRHS_collapse

/-- **§5 Step-4 `Υ`-expansion error collapse** (writeup 1009, 1013).  The explicit `O(·/d⁷)`
error of `Upsilon_expand` is bounded by the single scale-monomial `T = Δ⁴G⁵U⁴⁵/(H²Ω¹⁴)`. -/
theorem upsilon_err_le {a : ℝ} {b₀ v d ℓ₁ ℓ₂ : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hdwin : S.D ≤ d ∧ d ≤ 2 * S.D)
    (hb0 : |b₀| ≤ 3000000000000 * S.B) (hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3))
    (hshift : d / 2 ≤ d + ℓ₁ * b₀)
    -- regime
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U) :
    ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4
            + a ^ 3 * |ℓ₁ * b₀| ^ 3) / d ^ 7)
      + ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4
            + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3) / d ^ 7)
      + ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (10 ^ 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
            + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) / (d + ℓ₁ * b₀) ^ 7)
      + ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (|P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (120 * (ℓ₁ * b₀) ^ 2 / d ^ 7)
          + |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
      + |Rres P.X a b₀ v d ℓ₁ ℓ₂|
      ≤ 10 ^ 119 * UpsT P S := by
  -- ===== positivity =====
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have _ := h1; have _ := hband
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hℓ1R : 0 < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : 0 < ℓ₂ := lt_trans hℓ1R hℓ12
  have hℓ21 : 0 < ℓ₂ - ℓ₁ := by linarith
  obtain ⟨hdD, hd2D⟩ := hdwin
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hb0nn : 0 ≤ |b₀| := abs_nonneg _
  have hvnn : 0 ≤ |v| := abs_nonneg _
  -- master scale `M = U⁵Δ²/Ω³`
  set M : ℝ := P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3 with hM_def
  have hM_nn : 0 ≤ M := by rw [hM_def]; positivity
  -- ℓ bounds
  have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by
    rw [Globals.Wval] at hℓ2W; linarith [hℓ2W]
  have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans hℓ12.le hℓ2W'
  have hℓ21W' : ℓ₂ - ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := by linarith [hℓ2W', hℓ1R]
  have hW_nn : 0 ≤ 130 * (P.G * P.U ^ 5) := by positivity
  -- `a ≤ 11ΔΩ ≤ M`
  have ha11 : a ≤ 11 * (S.Δ * S.Ω) := by
    have : (11 : ℝ) * S.A = 11 * (S.Δ * S.Ω) := by unfold Scale.A; ring
    linarith [ha_hi, this]
  have h11ΔΩM : 11 * (S.Δ * S.Ω) ≤ M := by
    rw [hM_def, le_div_iff₀ (by positivity)]
    have hΩ4 : S.Ω ^ 4 ≤ P.U ^ 4 := pow_le_pow_left₀ hΩpos.le hΩU 4
    have hUΔ : (11 : ℝ) ≤ P.U * S.Δ := by
      have h11U : (11 : ℝ) ≤ P.U := le_trans (by norm_num) hUbig
      nlinarith only [hΔ1, h11U, hUpos]
    have c1 : a * S.Ω ^ 3 ≤ 11 * S.Δ * S.Ω ^ 4 := by
      nlinarith only [ha11, pow_nonneg hΩpos.le 3]
    have c2 : (11 : ℝ) * S.Δ * S.Ω ^ 4 ≤ 11 * S.Δ * P.U ^ 4 :=
      mul_le_mul_of_nonneg_left hΩ4 (by positivity)
    have c3 : (11 : ℝ) * S.Δ * P.U ^ 4 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hUΔ (by positivity : (0:ℝ) ≤ S.Δ * P.U ^ 4),
        hΔpos, hUpos]
    nlinarith only [c1, c2, c3, mul_le_mul_of_nonneg_right hΩ4 (by positivity : (0:ℝ) ≤ S.Δ)]
  have hΔΩM : S.Δ * S.Ω ≤ M := by
    nlinarith only [h11ΔΩM, hM_nn, mul_pos hΔpos hΩpos]
  have haM : a ≤ M := by linarith only [ha11, h11ΔΩM]
  -- the three β-magnitudes against `M`
  have hb0M : ℓ₂ * |b₀| ≤ 390000000000000 * M := by
    have hb0' : |b₀| ≤ 3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3)) := by
      have : S.B = S.Δ ^ 2 / (P.G * S.Ω ^ 3) := rfl
      rw [this] at hb0; exact hb0
    calc ℓ₂ * |b₀| ≤ (130 * (P.G * P.U ^ 5)) * (3000000000000 * (S.Δ ^ 2 / (P.G * S.Ω ^ 3))) :=
          mul_le_mul hℓ2W' hb0' hb0nn hW_nn
      _ = 390000000000000 * M := by rw [hM_def]; field_simp; ring
  have hℓ1b0M : ℓ₁ * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right hℓ12.le hb0nn) hb0M
  have hℓ21b0M : (ℓ₂ - ℓ₁) * |b₀| ≤ 390000000000000 * M :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith : ℓ₂ - ℓ₁ ≤ ℓ₂) hb0nn) hb0M
  have hvM : |v| ≤ 10 ^ 20 * M := by
    rw [hM_def]
    refine le_trans hv ?_
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith only [hΔ1, hΔpos]
    have hnum : S.Δ * P.U ^ 5 ≤ P.U ^ 5 * S.Δ ^ 2 := by
      nlinarith only [hΔsq, pow_nonneg hUpos.le 5]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity))
      (by norm_num)
  -- |ℓ₁b₀| ≤ 3e12 M
  have habs_ℓ1 : |ℓ₁ * b₀| ≤ 390000000000000 * M := by
    rw [abs_mul, abs_of_pos hℓ1R]; exact hℓ1b0M
  -- |ℓ₂b₀+v| ≤ 2e20 M
  have habs_ℓ2v : |ℓ₂ * b₀ + v| ≤ 2 * 10 ^ 20 * M := by
    calc |ℓ₂ * b₀ + v| ≤ |ℓ₂ * b₀| + |v| := abs_add_le _ _
      _ = ℓ₂ * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ2R]
      _ ≤ 390000000000000 * M + 10 ^ 20 * M := by linarith [hb0M, hvM]
      _ ≤ 2 * 10 ^ 20 * M := by linarith [hM_nn]
  -- |(ℓ₂-ℓ₁)b₀+v| ≤ 2e20 M
  have habs_ℓ21v : |(ℓ₂ - ℓ₁) * b₀ + v| ≤ 2 * 10 ^ 20 * M := by
    calc |(ℓ₂ - ℓ₁) * b₀ + v| ≤ |(ℓ₂ - ℓ₁) * b₀| + |v| := abs_add_le _ _
      _ = (ℓ₂ - ℓ₁) * |b₀| + |v| := by rw [abs_mul, abs_of_pos hℓ21]
      _ ≤ 390000000000000 * M + 10 ^ 20 * M := by linarith [hℓ21b0M, hvM]
      _ ≤ 2 * 10 ^ 20 * M := by linarith [hM_nn]
  -- `a ≤ 11ΔΩ` as nonneg, and `11ΔΩ ≤ 2e20 M` (so it can be the `Amag` with `hAb`)
  have ha0' : 0 ≤ a := ha0.le
  have hAmag_le_b : 11 * (S.Δ * S.Ω) ≤ 2 * 10 ^ 20 * M := by
    nlinarith only [h11ΔΩM, hM_nn]
  have hAmag_le_b' : 11 * (S.Δ * S.Ω) ≤ 390000000000000 * M := by
    nlinarith only [h11ΔΩM, hM_nn]
  -- prefactor bounds (each ≤ W⁴)
  have hpre1 : ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ 285610000 * (P.G * P.U ^ 5) ^ 4 := by
    calc ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 2 := by
          gcongr
      _ = 285610000 * (P.G * P.U ^ 5) ^ 4 := by ring
  have hpre1nn : 0 ≤ ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hpre2 : ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ 285610000 * (P.G * P.U ^ 5) ^ 4 := by
    calc ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 2 := by
          gcongr
      _ = 285610000 * (P.G * P.U ^ 5) ^ 4 := by ring
  have hpre2nn : 0 ≤ ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2 := by positivity
  have hpre3 : ℓ₁ ^ 2 * ℓ₂ ^ 2 ≤ 285610000 * (P.G * P.U ^ 5) ^ 4 := by
    calc ℓ₁ ^ 2 * ℓ₂ ^ 2 ≤ (130 * (P.G * P.U ^ 5)) ^ 2 * (130 * (P.G * P.U ^ 5)) ^ 2 := by
          gcongr
      _ = 285610000 * (P.G * P.U ^ 5) ^ 4 := by ring
  have hpre3nn : 0 ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 := by positivity
  -- denominator facts
  have hHΔ7 : 0 < (P.H * S.Δ) ^ 7 := by positivity
  have hd7HΔ : (P.H * S.Δ) ^ 7 ≤ d ^ 7 := by
    have : P.H * S.Δ ≤ d := by have : S.D = P.H * S.Δ := rfl; rw [← this]; exact hdD
    exact pow_le_pow_left₀ (by positivity) this 7
  -- shift denominator: (d+ℓ₁b₀)⁷ ≥ (d/2)⁷ ≥ (HΔ/2)⁷ = (HΔ)⁷/128
  have hshift7 : (P.H * S.Δ) ^ 7 / 128 ≤ (d + ℓ₁ * b₀) ^ 7 := by
    have hdh : 0 < d / 2 := by linarith
    have h1 : (d / 2) ^ 7 ≤ (d + ℓ₁ * b₀) ^ 7 := pow_le_pow_left₀ hdh.le hshift 7
    have h2 : (P.H * S.Δ / 2) ^ 7 ≤ (d / 2) ^ 7 := by
      apply pow_le_pow_left₀ (by positivity)
      have : S.D = P.H * S.Δ := rfl; rw [← this]; linarith [hdD]
    have h3 : (P.H * S.Δ / 2) ^ 7 = (P.H * S.Δ) ^ 7 / 128 := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hshift7pos : 0 < (P.H * S.Δ) ^ 7 / 128 := by positivity
  -- the master collapse `W⁴·X·(ΔΩ)·M⁵/(HΔ)⁷ = UpsT` (in unfolded form, as `piece_le` produces)
  have hTval : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
        * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / (P.H * S.Δ) ^ 7 = UpsT P S :=
    upsilon_scale_id P S
  have hUpsT_nn : 0 ≤ UpsT P S := by unfold UpsT; positivity
  -- abbreviation for the `M`-unfolded scale block that `piece_le` produces
  have hMpow_eq : (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 = M ^ 5 := by rw [hM_def]
  -- ===========================================================
  -- PIECE 1 : term over `ℓ₁b₀`
  -- ===========================================================
  have hin1 : a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4 + a ^ 3 * |ℓ₁ * b₀| ^ 3
      ≤ (3 * 11 * 390000000000000 ^ 5) * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have := inner_le (a := a) (β := ℓ₁ * b₀) (Amag := 11 * (S.Δ * S.Ω))
      (bm := 390000000000000 * M) ha0' ha11 (abs_nonneg _) habs_ℓ1 hAmag_le_b'
    calc a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4 + a ^ 3 * |ℓ₁ * b₀| ^ 3
        ≤ 3 * (11 * (S.Δ * S.Ω)) * (390000000000000 * M) ^ 5 := this
      _ = (3 * 11 * 390000000000000 ^ 5) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  have hP1 : ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4
            + a ^ 3 * |ℓ₁ * b₀| ^ 3) / d ^ 7)
      ≤ (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)) * UpsT P S := by
    have hpc := piece_le (P := P) (S := S) (pref := ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
      (inner := a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4 + a ^ 3 * |ℓ₁ * b₀| ^ 3)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 10 ^ 4)
      (Cin := 3 * 11 * 390000000000000 ^ 5) hpre1nn hpre1
      (by positivity) hin1 hHΔ7 hd7HΔ (by norm_num) (by positivity)
    rw [hTval] at hpc
    calc ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
          * (10 ^ 4 * P.X * (a * |ℓ₁ * b₀| ^ 5 + a ^ 2 * |ℓ₁ * b₀| ^ 4
              + a ^ 3 * |ℓ₁ * b₀| ^ 3) / d ^ 7)
        ≤ 285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5) * UpsT P S := hpc
      _ = (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 2 : term over `ℓ₂b₀+v`
  -- ===========================================================
  have hin2 : a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4 + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3
      ≤ (3 * 11 * (2 * 10 ^ 20) ^ 5) * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have := inner_le (a := a) (β := ℓ₂ * b₀ + v) (Amag := 11 * (S.Δ * S.Ω))
      (bm := 2 * 10 ^ 20 * M) ha0' ha11 (abs_nonneg _) habs_ℓ2v hAmag_le_b
    calc a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4 + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3
        ≤ 3 * (11 * (S.Δ * S.Ω)) * (2 * 10 ^ 20 * M) ^ 5 := this
      _ = (3 * 11 * (2 * 10 ^ 20) ^ 5) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  have hP2 : ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
        * (10 ^ 4 * P.X * (a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4
            + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3) / d ^ 7)
      ≤ (285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5)) * UpsT P S := by
    have hpc := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
      (inner := a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4 + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 10 ^ 4)
      (Cin := 3 * 11 * (2 * 10 ^ 20) ^ 5) hpre2nn hpre2
      (by positivity) hin2 hHΔ7 hd7HΔ (by norm_num) (by positivity)
    rw [hTval] at hpc
    calc ℓ₁ ^ 2 * (ℓ₂ - ℓ₁) ^ 2
          * (10 ^ 4 * P.X * (a * |ℓ₂ * b₀ + v| ^ 5 + a ^ 2 * |ℓ₂ * b₀ + v| ^ 4
              + a ^ 3 * |ℓ₂ * b₀ + v| ^ 3) / d ^ 7)
        ≤ 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * UpsT P S := hpc
      _ = (285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5)) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 3 : term over `(ℓ₂-ℓ₁)b₀+v`, denominator `(d+ℓ₁b₀)⁷ ≥ (HΔ)⁷/128`
  -- ===========================================================
  have hTval128 : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
        * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / ((P.H * S.Δ) ^ 7 / 128) = 128 * UpsT P S := by
    have heq : (P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / ((P.H * S.Δ) ^ 7 / 128)
        = 128 * ((P.G * P.U ^ 5) ^ 4 * P.X * (S.Δ * S.Ω)
            * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 / (P.H * S.Δ) ^ 7) := by
      rw [div_div_eq_mul_div]; ring
    rw [heq, hTval]
  have hin3 : a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
        + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3
      ≤ (3 * 11 * (2 * 10 ^ 20) ^ 5) * (S.Δ * S.Ω) * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have := inner_le (a := a) (β := (ℓ₂ - ℓ₁) * b₀ + v) (Amag := 11 * (S.Δ * S.Ω))
      (bm := 2 * 10 ^ 20 * M) ha0' ha11 (abs_nonneg _) habs_ℓ21v hAmag_le_b
    calc a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
          + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3
        ≤ 3 * (11 * (S.Δ * S.Ω)) * (2 * 10 ^ 20 * M) ^ 5 := this
      _ = (3 * 11 * (2 * 10 ^ 20) ^ 5) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  have hP3 : ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (10 ^ 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
            + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) / (d + ℓ₁ * b₀) ^ 7)
      ≤ (285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * 128) * UpsT P S := by
    have hpc := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * ℓ₂ ^ 2)
      (inner := a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
        + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
      (den := (d + ℓ₁ * b₀) ^ 7) (denlo := (P.H * S.Δ) ^ 7 / 128) (c := 10 ^ 4)
      (Cin := 3 * 11 * (2 * 10 ^ 20) ^ 5) hpre3nn hpre3
      (by positivity) hin3 hshift7pos hshift7 (by norm_num) (by positivity)
    rw [hTval128] at hpc
    calc ℓ₁ ^ 2 * ℓ₂ ^ 2
          * (10 ^ 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 5 + a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
              + a ^ 3 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) / (d + ℓ₁ * b₀) ^ 7)
        ≤ 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * (128 * UpsT P S) := hpc
      _ = (285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * 128) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 4 : base-point shift correction (two sub-terms)
  -- ===========================================================
  -- rewrite the two abs values into explicit nonnegative products
  have habs4a : |P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)|
      = 4 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) := by
    rw [abs_mul, abs_of_pos hXpos]
    rw [show -4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3
          = (-(4 * a)) * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3 by ring, abs_mul, abs_neg,
        abs_of_pos (by positivity : (0:ℝ) < 4 * a), abs_pow]
    ring
  have habs4b : |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
        + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)|
      ≤ P.X * (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) := by
    rw [abs_mul, abs_of_pos hXpos]
    refine mul_le_mul_of_nonneg_left ?_ hXpos.le
    calc |10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4 + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3|
        ≤ |10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4| + |10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3| :=
          abs_add_le _ _
      _ = 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 := by
          have e1 : |10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4|
              = 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 := by
            rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 10 * a)]
          have e2 : |10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3|
              = 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 := by
            rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 10 * a ^ 2)]
          rw [e1, e2]
  -- sub-4a inner bound
  have hin4a : a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2
      ≤ (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2) * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have hsq : (ℓ₁ * b₀) ^ 2 = |ℓ₁ * b₀| ^ 2 := (sq_abs _).symm
    rw [hsq]
    have hM3 : |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 ≤ (2 * 10 ^ 20 * M) ^ 3 := by gcongr
    have hM2 : |ℓ₁ * b₀| ^ 2 ≤ (390000000000000 * M) ^ 2 := by gcongr
    calc a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀| ^ 2
        ≤ 11 * (S.Δ * S.Ω) * (2 * 10 ^ 20 * M) ^ 3 * (390000000000000 * M) ^ 2 := by
          apply mul_le_mul (mul_le_mul ha11 hM3 (by positivity) (by positivity)) hM2
            (by positivity) (by positivity)
      _ = (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  -- sub-4b inner bound
  have hin4b : (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
        * |ℓ₁ * b₀|
      ≤ (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
          + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * (S.Δ * S.Ω)
          * (P.U ^ 5 * S.Δ ^ 2 / S.Ω ^ 3) ^ 5 := by
    have hM4 : |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 ≤ (2 * 10 ^ 20 * M) ^ 4 := by gcongr
    have hM3 : |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 ≤ (2 * 10 ^ 20 * M) ^ 3 := by gcongr
    have ha2 : a ^ 2 ≤ (11 * (S.Δ * S.Ω)) ^ 2 := by
      have := pow_le_pow_left₀ ha0' ha11 2; exact this
    -- term A: 10a|β|⁴|ℓ₁b₀|
    have hA : 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 * |ℓ₁ * b₀|
        ≤ (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by
      calc 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 * |ℓ₁ * b₀|
          ≤ 10 * (11 * (S.Δ * S.Ω)) * (2 * 10 ^ 20 * M) ^ 4 * (390000000000000 * M) := by
            gcongr
        _ = (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by ring
    -- term B: 10a²|β|³|ℓ₁b₀| ≤ … using (ΔΩ)² ≤ (ΔΩ)·M
    have hB : 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀|
        ≤ (10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by
      have hΔΩsq : (S.Δ * S.Ω) ^ 2 ≤ (S.Δ * S.Ω) * M :=
        by nlinarith only [hΔΩM, mul_pos hΔpos hΩpos]
      calc 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀|
          ≤ 10 * (11 * (S.Δ * S.Ω)) ^ 2 * (2 * 10 ^ 20 * M) ^ 3 * (390000000000000 * M) := by
            gcongr
        _ = (10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * ((S.Δ * S.Ω) ^ 2) * M ^ 4 := by ring
        _ ≤ (10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * ((S.Δ * S.Ω) * M) * M ^ 4 := by
            gcongr
        _ = (10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by ring
    calc (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3) * |ℓ₁ * b₀|
        = 10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 * |ℓ₁ * b₀|
          + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * |ℓ₁ * b₀| := by ring
      _ ≤ (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5
          + (10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by
            linarith [hA, hB]
      _ = (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
            + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * (S.Δ * S.Ω) * M ^ 5 := by ring
      _ = _ := by rw [hMpow_eq]
  -- assemble piece 4
  have hP4 : ℓ₁ ^ 2 * ℓ₂ ^ 2
        * (|P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (120 * (ℓ₁ * b₀) ^ 2 / d ^ 7)
          + |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
      ≤ (285610000 * 480 * (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2)
          + 285610000 * 64 * (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
              + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000)) * UpsT P S := by
    -- sub-4a as a `piece_le`
    have hpc4a := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * ℓ₂ ^ 2)
      (inner := a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 480)
      (Cin := 11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2) hpre3nn hpre3
      (by positivity) hin4a hHΔ7 hd7HΔ (by norm_num) (by positivity)
    have hpc4b := piece_le (P := P) (S := S) (pref := ℓ₁ ^ 2 * ℓ₂ ^ 2)
      (inner := (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
        * |ℓ₁ * b₀|)
      (den := d ^ 7) (denlo := (P.H * S.Δ) ^ 7) (c := 64)
      (Cin := 10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
          + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) hpre3nn hpre3
      (by positivity) hin4b hHΔ7 hd7HΔ (by norm_num) (by positivity)
    rw [hTval] at hpc4a hpc4b
    -- rewrite the two abs sub-terms of the goal
    have hd7pos : (0:ℝ) < d ^ 7 := by positivity
    -- sub-4a literal = pref * (480 X inner4a / d⁷)
    have hsub4a : ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (-4 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)|
          * (120 * (ℓ₁ * b₀) ^ 2 / d ^ 7))
        = ℓ₁ ^ 2 * ℓ₂ ^ 2 * (480 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2) / d ^ 7) := by
      rw [habs4a]; ring
    -- sub-4b literal ≤ pref * (64 X inner4b / d⁷)
    have hsub4b : ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
            + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
        ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 * (64 * P.X
            * ((10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
                * |ℓ₁ * b₀|) / d ^ 7) := by
      have hfac : |P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
            + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7)
          ≤ (P.X * (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3))
            * (64 * |ℓ₁ * b₀| / d ^ 7) := by
        gcongr
      calc ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
          ≤ ℓ₁ ^ 2 * ℓ₂ ^ 2 * ((P.X * (10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4
              + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)) * (64 * |ℓ₁ * b₀| / d ^ 7)) := by
            exact mul_le_mul_of_nonneg_left hfac hpre3nn
        _ = ℓ₁ ^ 2 * ℓ₂ ^ 2 * (64 * P.X
              * ((10 * a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 4 + 10 * a ^ 2 * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3)
                  * |ℓ₁ * b₀|) / d ^ 7) := by ring
    rw [mul_add, hsub4a]
    calc ℓ₁ ^ 2 * ℓ₂ ^ 2 * (480 * P.X * (a * |(ℓ₂ - ℓ₁) * b₀ + v| ^ 3 * (ℓ₁ * b₀) ^ 2) / d ^ 7)
          + ℓ₁ ^ 2 * ℓ₂ ^ 2 * (|P.X * (10 * a * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 4
              + 10 * a ^ 2 * ((ℓ₂ - ℓ₁) * b₀ + v) ^ 3)| * (64 * |ℓ₁ * b₀| / d ^ 7))
        ≤ 285610000 * 480 * (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2) * UpsT P S
          + 285610000 * 64 * (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
              + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000) * UpsT P S := by
          exact add_le_add hpc4a (le_trans hsub4b hpc4b)
      _ = (285610000 * 480 * (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2)
            + 285610000 * 64 * (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
                + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000)) * UpsT P S := by ring
  -- ===========================================================
  -- PIECE 5 : the genuine residual `|Rres|`  (factored into `rres_le`)
  -- ===========================================================
  set Csum : ℝ := 8 * (390000000000000 ^ 3 * (2 * 10 ^ 20))
      + 12 * (390000000000000 ^ 2 * (2 * 10 ^ 20) ^ 2)
      + 10 * (390000000000000 * (2 * 10 ^ 20) ^ 3)
      + 3 * ((2 * 10 ^ 20) ^ 4) with hCsumdef
  have hvM2 : |v| ≤ 2 * 10 ^ 20 * M := by linarith only [hvM, hM_nn]
  have hP5 : |Rres P.X a b₀ v d ℓ₁ ℓ₂| ≤ 25 * 121 * 285610000 * Csum * UpsT P S :=
    rres_le ha0 ha11 hℓ1R hℓ12 hℓ2W' hd_pos hb0M hvM2 hΔΩM hd7HΔ hM_def
  -- ===========================================================
  -- FINAL ASSEMBLY : sum the five piece bounds
  -- ===========================================================
  have hconst : (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)
      + 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5)
      + 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * 128
      + (285610000 * 480 * (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2)
          + 285610000 * 64 * (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
              + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000))
      + 25 * 121 * 285610000 * Csum : ℝ) ≤ 10 ^ 119 := by
    rw [hCsumdef]; norm_num
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hP1 hP2) hP3) hP4) hP5
  refine le_trans hsum ?_
  rw [show (10:ℝ) ^ 119 * UpsT P S = 10 ^ 119 * UpsT P S by ring]
  calc 285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5) * UpsT P S
        + 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * UpsT P S
        + 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * 128 * UpsT P S
        + (285610000 * 480 * (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2)
            + 285610000 * 64 * (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
                + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000)) * UpsT P S
        + 25 * 121 * 285610000 * Csum * UpsT P S
      = (285610000 * 10 ^ 4 * (3 * 11 * 390000000000000 ^ 5)
          + 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5)
          + 285610000 * 10 ^ 4 * (3 * 11 * (2 * 10 ^ 20) ^ 5) * 128
          + (285610000 * 480 * (11 * (2 * 10 ^ 20) ^ 3 * 390000000000000 ^ 2)
              + 285610000 * 64 * (10 * 11 * (2 * 10 ^ 20) ^ 4 * 390000000000000
                  + 10 * 121 * (2 * 10 ^ 20) ^ 3 * 390000000000000))
          + 25 * 121 * 285610000 * Csum) * UpsT P S := by ring
    _ ≤ 10 ^ 119 * UpsT P S := by
        exact mul_le_mul_of_nonneg_right hconst hUpsT_nn

end Squarefree
