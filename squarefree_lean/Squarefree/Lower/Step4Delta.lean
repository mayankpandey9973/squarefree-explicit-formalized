import Squarefree.Lower.Step4Phase
import Squarefree.Lower.Step4Reduce
import Squarefree.Lower.Step4VTerm
import Squarefree.Lower.DefectExpandV
import Squarefree.Lower.DefectReplace
import Squarefree.Lower.QNearInt

/-!
# §5 Step-4 per-`r` near-integer bound (writeup 1067, 1071, 1083)

`phiv_delta_le` is the Step-4 analogue of `phif_delta_le`: it bounds
`distInt(φ_v) ≤ C·(1/Δ)G⁴U¹⁵/Ω⁵ = C·δ`, the writeup's `δ` (line 1083), for any integer
`f` within the `Q_distInt_le` slack of `𝒬` (in practice `f = round 𝒬`).

The structure mirrors `phif_dist_le`/`phif_delta_le` but is **pref-free** (`φ_v` carries no
`d̃⁴/6Xa` prefactor) and uses `f` directly rather than the discrete witness `M = ℓ₁v`.
The exact identity (see `phiv_dist_le` below) is

  `φ_v − f = (𝒬 − f) + (LEAD − 𝒬) + 6ℓ₁Xav·(1/d̃⁴ − 1/d⁴) + (PHID − φ)`

with `PHID = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xab₀²/d⁵` and `LEAD = 6ℓ₁Xav/d⁴ − PHID`.  The four pieces are
bounded by `Q_distInt_le`-slack (piece 1, via `hf`), `Q_gen_expand` (piece 2), a tight
re-scale of the `v_replace_le` mechanism (piece 3), and `phi_d_replace` (piece 4).
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 Step-4 per-`r` reduction (algebraic core).** Pref-free analogue of `phif_dist_le`. -/
private theorem phiv_dist_le {a : ℤ} {r : ℝ} {ℓ₁ ℓ₂ b₀ v 𝒬 : ℝ} {d : ℝ} {f : ℤ}
    (ha : 0 < (a : ℝ)) (hd : 0 < d) (hℓ1 : 0 < ℓ₁)
    (hdt : 0 < dtilde P.X r (a : ℝ))
    (_h𝒬 : 𝒬 = ℓ₁ * Fab P.X (a : ℝ) (ℓ₂ * b₀ + v) d - ℓ₂ * Fab P.X (a : ℝ) (ℓ₁ * b₀) d) :
    distInt (phiv P.X (a : ℝ) ℓ₁ ℓ₂ v r)
      ≤ |(f : ℝ) - 𝒬|
        + |𝒬 - (6 * ℓ₁ * P.X * (a : ℝ) * v / d ^ 4
                - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * b₀ ^ 2 / d ^ 5)|
        + |phi P.X (a : ℝ) ℓ₁ ℓ₂ r
            - 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * b₀ ^ 2 / d ^ 5|
        + 6 * ℓ₁ * P.X * (a : ℝ) * |v|
            * |1 / (dtilde P.X r (a : ℝ)) ^ 4 - 1 / d ^ 4| := by
  have hX0 : P.X ≠ 0 := ne_of_gt P.X_pos
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdt0 : dtilde P.X r (a : ℝ) ≠ 0 := ne_of_gt hdt
  set dt := dtilde P.X r (a : ℝ) with hdt_def
  set φ := phi P.X (a : ℝ) ℓ₁ ℓ₂ r with hφ_def
  set PHID := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a : ℝ) * b₀ ^ 2 / d ^ 5 with hPHID_def
  set LEAD := 6 * ℓ₁ * P.X * (a : ℝ) * v / d ^ 4 - PHID with hLEAD_def
  -- the EXACT identity
  have hident : phiv P.X (a : ℝ) ℓ₁ ℓ₂ v r - (f : ℝ)
      = ((f : ℝ) - 𝒬) * (-1) + (𝒬 - LEAD) * (-1)
        + (6 * ℓ₁ * P.X * (a : ℝ) * v) * (1 / dt ^ 4 - 1 / d ^ 4)
        + (φ - PHID) * (-1) := by
    rw [hLEAD_def, phiv, hdt_def]
    field_simp
    ring
  refine le_trans (distInt_le_intDist (phiv P.X (a : ℝ) ℓ₁ ℓ₂ v r) f) ?_
  rw [hident]
  -- per-term absolute-value rewrites
  have e1 : |((f : ℝ) - 𝒬) * (-1)| = |(f : ℝ) - 𝒬| := by rw [abs_mul]; simp
  have e2 : |(𝒬 - LEAD) * (-1)| = |𝒬 - LEAD| := by rw [abs_mul]; simp
  have e4 : |(φ - PHID) * (-1)| = |φ - PHID| := by rw [abs_mul]; simp
  have hpref_pos : (0:ℝ) < 6 * ℓ₁ * P.X * (a : ℝ) := by
    have := P.X_pos; positivity
  have e3 : |(6 * ℓ₁ * P.X * (a : ℝ) * v) * (1 / dt ^ 4 - 1 / d ^ 4)|
      = 6 * ℓ₁ * P.X * (a : ℝ) * |v| * |1 / dt ^ 4 - 1 / d ^ 4| := by
    rw [abs_mul]
    rw [show (6 * ℓ₁ * P.X * (a : ℝ) * v) = (6 * ℓ₁ * P.X * (a : ℝ)) * v by ring,
      abs_mul, abs_of_pos hpref_pos]
  -- triangle inequality, regrouping into the goal order
  calc |((f : ℝ) - 𝒬) * (-1) + (𝒬 - LEAD) * (-1)
            + 6 * ℓ₁ * P.X * (a : ℝ) * v * (1 / dt ^ 4 - 1 / d ^ 4) + (φ - PHID) * (-1)|
      ≤ |((f : ℝ) - 𝒬) * (-1)| + |(𝒬 - LEAD) * (-1)|
          + |6 * ℓ₁ * P.X * (a : ℝ) * v * (1 / dt ^ 4 - 1 / d ^ 4)| + |(φ - PHID) * (-1)| := by
        refine le_trans (abs_add_le _ _) ?_
        refine add_le_add ?_ (le_refl _)
        refine le_trans (abs_add_le _ _) ?_
        refine add_le_add ?_ (le_refl _)
        exact abs_add_le _ _
    _ = |(f : ℝ) - 𝒬| + |𝒬 - LEAD| + |phi P.X (a : ℝ) ℓ₁ ℓ₂ r - PHID|
          + 6 * ℓ₁ * P.X * (a : ℝ) * |v| * |1 / dt ^ 4 - 1 / d ^ 4| := by
        rw [e1, e2, e4, e3, hφ_def]; ring

/-- **§5 Step-4 per-`r` δ bound** (writeup 1067, 1071, 1083).  For any integer `f` within the
`Q_distInt_le` slack of `𝒬` (in practice `f = round 𝒬`),
`distInt(φ_v) ≤ 10⁷⁰·(1/Δ)G⁴U¹⁵/Ω⁵`, the writeup's `δ`.

Added vs the bare signature: the two `Q_gen_expand` Taylor windows `hwin2`, `hwin1`, and the
non-degeneracy `hℓ2bv_ne : ℓ₂b₀+v ≠ 0`, `hd1ned : d₁ ≠ d` (mirroring what `phif_delta_le`
needs to invoke `Q_gen_expand`). -/
theorem phiv_delta_le {a : ℤ} {r : ℝ}
    {ℓ₁ ℓ₂ b₀ v 𝒬 : ℝ} {d d₁ d₂ : ℝ} {f : ℤ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a:ℝ)) (ha_hi : (a:ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr1_hi : r + ℓ₁ ≤ 16 * S.R)
    (hℓ1pos : 0 < ℓ₁) (hℓ1_lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * P.Wval)
    (hd_win : S.D ≤ d ∧ d ≤ 2 * S.D) (hd1_win : S.D ≤ d₁ ∧ d₁ ≤ 2 * S.D)
    (hd2_win : S.D ≤ d₂ ∧ d₂ ≤ 2 * S.D)
    (hd_close  : |d  - dtilde P.X r        (a:ℝ)| ≤ 1000000000000 * (S.Δ/(P.G*S.Ω^3)))
    (hd1_close : |d₁ - dtilde P.X (r+ℓ₁)   (a:ℝ)| ≤ 1000000000000 * (S.Δ/(P.G*S.Ω^3)))
    (hb0def : ℓ₁ * b₀ = d₁ - d)
    (hv : |v| ≤ 10^20 * (S.Δ * P.U^5 / S.Ω^3))
    (hb0 : |b₀| ≤ 3000000000000 * S.B)
    (h𝒬 : 𝒬 = ℓ₁ * Fab P.X (a:ℝ) (ℓ₂*b₀+v) d - ℓ₂ * Fab P.X (a:ℝ) (ℓ₁*b₀) d)
    (hf : (f:ℝ) = 𝒬 ∨ |(f:ℝ) - 𝒬| ≤ ℓ₁*(2*P.H/d^2 + 2*P.H/d₂^2) + ℓ₂*(2*P.H/d^2 + 2*P.H/d₁^2))
    (hd1ned : d₁ ≠ d) (hℓ2bv_ne : ℓ₂ * b₀ + v ≠ 0)
    (hwin2 : 4 * ((a:ℝ) + |ℓ₂*b₀+v|) ≤ d) (hwin1 : 4 * ((a:ℝ) + ℓ₁*|b₀|) ≤ d)
    (h1 : P.G * P.U^10 ≤ P.H / S.Δ^2) (hΔreg : P.G^2 * P.U^5 ≤ S.Δ)
    (hband : 1 ≤ P.G * P.U^3 * S.Ω^4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (hUH : P.U ^ 9 ≤ P.G ^ 7 * P.H ^ 2) :
    Counting.distInt (phiv P.X (a:ℝ) ℓ₁ ℓ₂ v r)
      ≤ (10:ℝ)^70 * ((1 / S.Δ) * P.G^4 * P.U^15 / S.Ω^5) := by
  -- ===== positivity / casts =====
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hUpos : 0 < P.U := P.U_pos
  have hXpos : 0 < P.X := P.X_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hDpos : 0 < S.D := by unfold Scale.D; positivity
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha0
  have hℓ12R : ℓ₁ < ℓ₂ := hℓ12
  have hℓ1W : ℓ₁ ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12) hℓ2W
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  have hr_hi : r ≤ 16 * S.R := by linarith [hℓ1pos.le]
  have hdD : S.D ≤ d := hd_win.1
  have hd2D : d ≤ 2 * S.D := hd_win.2
  have hd_pos : 0 < d := lt_of_lt_of_le hDpos hdD
  have hdt_pos : 0 < dtilde P.X r (a:ℝ) := dtilde_pos hXpos haR hr0
  -- ===== STEP A : algebraic reduction =====
  have hreduce := phiv_dist_le (P := P) (a := a) (r := r) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (b₀ := b₀) (v := v) (𝒬 := 𝒬) (f := f) (d := d) haR hd_pos hℓ1pos hdt_pos h𝒬
  refine le_trans hreduce ?_
  set PHID : ℝ := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * (a:ℝ) * b₀ ^ 2 / d ^ 5 with hPHID_def
  set LEAD : ℝ := 6 * ℓ₁ * P.X * (a:ℝ) * v / d ^ 4 - PHID with hLEAD_def
  set δ4 : ℝ := (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5 with hδ4_def
  have hδ4_pos : 0 < δ4 := by rw [hδ4_def]; positivity
  -- ===== PIECE 1 : |f - 𝒬| ≤ δ4 =====
  have hp1 : |(f:ℝ) - 𝒬| ≤ δ4 := by
    have hfb : |(f:ℝ) - 𝒬|
        ≤ ℓ₁*(2*P.H/d^2 + 2*P.H/d₂^2) + ℓ₂*(2*P.H/d^2 + 2*P.H/d₁^2) := by
      rcases hf with heq | hb
      · rw [heq, sub_self, abs_zero]
        have hd1pos : 0 < d₁ := lt_of_lt_of_le hDpos hd1_win.1
        have hd2pos : 0 < d₂ := lt_of_lt_of_le hDpos hd2_win.1
        have : 0 ≤ ℓ₁*(2*P.H/d^2 + 2*P.H/d₂^2) := by
          apply mul_nonneg hℓ1pos.le; positivity
        have : 0 ≤ ℓ₂*(2*P.H/d^2 + 2*P.H/d₁^2) := by
          apply mul_nonneg (le_trans hℓ1pos.le hℓ12.le); positivity
        linarith
      · exact hb
    refine le_trans hfb ?_
    -- inner sum ≤ 8HGU⁵/D²,  then 8HGU⁵/D² = 8GU⁵/(HΔ²) ≤ δ4
    have hd1D : S.D ≤ d₁ := hd1_win.1
    have hd2D : S.D ≤ d₂ := hd2_win.1
    have hHd2 : 2 * P.H / d ^ 2 ≤ 2 * P.H / S.D ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hDpos.le hdD 2)
    have hHd1 : 2 * P.H / d₁ ^ 2 ≤ 2 * P.H / S.D ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hDpos.le hd1D 2)
    have hHd2' : 2 * P.H / d₂ ^ 2 ≤ 2 * P.H / S.D ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hDpos.le hd2D 2)
    have hpair1 : 2 * P.H / d ^ 2 + 2 * P.H / d₂ ^ 2 ≤ 4 * P.H / S.D ^ 2 := by
      have : 2 * P.H / S.D ^ 2 + 2 * P.H / S.D ^ 2 = 4 * P.H / S.D ^ 2 := by ring
      linarith [hHd2, hHd2']
    have hpair2 : 2 * P.H / d ^ 2 + 2 * P.H / d₁ ^ 2 ≤ 4 * P.H / S.D ^ 2 := by
      have : 2 * P.H / S.D ^ 2 + 2 * P.H / S.D ^ 2 = 4 * P.H / S.D ^ 2 := by ring
      linarith [hHd2, hHd1]
    have hℓ2W' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
    have hℓ1W' : ℓ₁ ≤ 130 * (P.G * P.U ^ 5) := le_trans (le_of_lt hℓ12) hℓ2W'
    have h4Hnn : 0 ≤ 4 * P.H / S.D ^ 2 := by positivity
    have hinner : ℓ₁*(2*P.H/d^2 + 2*P.H/d₂^2) + ℓ₂*(2*P.H/d^2 + 2*P.H/d₁^2)
        ≤ 1040 * P.H * (P.G * P.U ^ 5) / S.D ^ 2 := by
      have t1 := mul_le_mul_of_nonneg_left hpair1 hℓ1pos.le
      have t2 := mul_le_mul_of_nonneg_left hpair2 (le_trans hℓ1pos.le hℓ12.le)
      have u1 := mul_le_mul_of_nonneg_right hℓ1W' h4Hnn
      have u2 := mul_le_mul_of_nonneg_right hℓ2W' h4Hnn
      have : (130 * (P.G * P.U ^ 5)) * (4 * P.H / S.D ^ 2)
            + (130 * (P.G * P.U ^ 5)) * (4 * P.H / S.D ^ 2)
          = 1040 * P.H * (P.G * P.U ^ 5) / S.D ^ 2 := by ring
      linarith [t1, t2, u1, u2, this]
    refine le_trans hinner ?_
    -- 8HGU⁵/D² ≤ δ4 = G⁴U¹⁵/(ΔΩ⁵)
    rw [show S.D = P.H * S.Δ from rfl, hδ4_def]
    rw [show 1040 * P.H * (P.G * P.U ^ 5) / (P.H * S.Δ) ^ 2
          = 1040 * (P.G * P.U ^ 5) / (P.H * S.Δ ^ 2) by field_simp]
    rw [show (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5
          = P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 5) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- 8GU⁵·(ΔΩ⁵) ≤ G⁴U¹⁵·(HΔ²)  reduce: 8Ω⁵ ≤ G³U¹⁰HΔ
    have hΩ5 : S.Ω ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ hΩpos.le hΩU 5
    have hU10 : (1040:ℝ) ≤ P.U ^ 10 := by
      have : (10:ℝ) ^ 10 ≤ P.U ^ 10 := pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) hUbig) 10
      exact le_trans (by norm_num) this
    have hG3 : (1:ℝ) ≤ P.G ^ 3 := one_le_pow₀ hG1
    have h8U5 : (1040:ℝ) ≤ P.U ^ 5 := by
      have : (10:ℝ) ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) hUbig) 5
      exact le_trans (by norm_num) this
    have hcore : (1040:ℝ) * S.Ω ^ 5 ≤ P.G ^ 3 * P.U ^ 10 * P.H * S.Δ := by
      have hstep : (1040:ℝ) * S.Ω ^ 5 ≤ P.U ^ 10 := by
        calc (1040:ℝ) * S.Ω ^ 5 ≤ P.U ^ 5 * P.U ^ 5 :=
              mul_le_mul h8U5 hΩ5 (pow_nonneg hΩpos.le 5) (pow_nonneg hUpos.le 5)
          _ = P.U ^ 10 := by ring
      have hub : P.U ^ 10 ≤ P.G ^ 3 * P.U ^ 10 * P.H * S.Δ := by
        have h1' : (1:ℝ) * P.U ^ 10 * 1 * 1 ≤ P.G ^ 3 * P.U ^ 10 * P.H * S.Δ := by
          gcongr
        linarith [h1']
      linarith [hstep, hub]
    -- goal: 8*G*U⁵·(ΔΩ⁵) ≤ G⁴U¹⁵·(HΔ²);  hcore: 8Ω⁵ ≤ G³U¹⁰HΔ, ×(GU⁵Δ)
    have hbridge := mul_le_mul_of_nonneg_right hcore
      (by positivity : (0:ℝ) ≤ P.G * P.U ^ 5 * S.Δ)
    calc 1040 * (P.G * P.U ^ 5) * (S.Δ * S.Ω ^ 5)
        = 1040 * S.Ω ^ 5 * (P.G * P.U ^ 5 * S.Δ) := by ring
      _ ≤ (P.G ^ 3 * P.U ^ 10 * P.H * S.Δ) * (P.G * P.U ^ 5 * S.Δ) := hbridge
      _ = P.G ^ 4 * P.U ^ 15 * (P.H * S.Δ ^ 2) := by ring
  -- ===== PIECE 2 : |𝒬 - LEAD| ≤ 10⁶⁶·δ4 =====
  have hℓ1b₀ne : ℓ₁ * b₀ ≠ 0 := by rw [hb0def]; exact sub_ne_zero.mpr hd1ned
  have hQ := Q_gen_expand (X := P.X) (a := (a:ℝ)) (b₀ := b₀) (v := v) (d := d)
    (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hXpos haR hd_pos hℓ1pos hℓ12 hℓ2bv_ne hℓ1b₀ne hwin2 hwin1
  rw [← h𝒬, ← hPHID_def, ← hLEAD_def] at hQ
  have hp2 : |𝒬 - LEAD| ≤ 10 ^ 68 * δ4 := by
    refine le_trans hQ ?_
    rw [hδ4_def]
    exact qgen_pieceV_le (P := P) (S := S) (a := a) (r := r) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      (b₀ := b₀) (v := v) (d := d) ha0 ha_lo ha_hi hℓ1pos hℓ12 hℓ2W ⟨hdD, hd2D⟩
      hb0 hv h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig
  -- ===== PIECE 4 : |phi - PHID| ≤ δ4 =====
  have hℓ2W'' : ℓ₂ ≤ 130 * (P.G * P.U ^ 5) := by rw [Globals.Wval] at hℓ2W; exact hℓ2W
  have hb0eq : b₀ = (d₁ - d) / ℓ₁ := by field_simp; linarith [hb0def]
  have hR := phi_d_replace (P := P) (S := S) (a := a) (r := r) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (d := d) (d₁ := d₁) hAD ha0 ha_lo ha_hi hℓ1pos hℓ1_lo hℓ12 hℓ2W'' hr_lo hr1_hi
    hd_win hd1_win hd_close hd1_close h1 hband hG1 hU1 hΔ1 hUH
  rw [← hb0eq, ← hPHID_def] at hR
  have hp4 : |phi P.X (a:ℝ) ℓ₁ ℓ₂ r - PHID| ≤ δ4 := by
    rw [abs_sub_comm]
    refine le_trans hR ?_
    -- 10⁴⁰·(1/Δ)G³U¹⁰/Ω⁵ ≤ δ4 = (1/Δ)G⁴U¹⁵/Ω⁵, need 10⁴⁰ ≤ GU⁵
    rw [hδ4_def]
    rw [show (10:ℝ) ^ 45 * ((1 / S.Δ) * P.G ^ 3 * P.U ^ 10 / S.Ω ^ 5)
          = 10 ^ 45 * (P.G ^ 3 * P.U ^ 10) / (S.Δ * S.Ω ^ 5) by field_simp]
    rw [show (1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5
          = P.G ^ 4 * P.U ^ 15 / (S.Δ * S.Ω ^ 5) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- 10⁴⁰·(G³U¹⁰)·(ΔΩ⁵) ≤ (G⁴U¹⁵)·(ΔΩ⁵)  reduce 10⁴⁰ ≤ GU⁵
    have hGU5 : (10:ℝ) ^ 45 ≤ P.G * P.U ^ 5 := by
      have h5 : ((10:ℝ) ^ 33) ^ 5 ≤ P.U ^ 5 := pow_le_pow_left₀ (by norm_num) hUbig 5
      calc (10:ℝ) ^ 45 ≤ ((10:ℝ) ^ 33) ^ 5 := by norm_num
        _ ≤ P.U ^ 5 := h5
        _ = 1 * P.U ^ 5 := by ring
        _ ≤ P.G * P.U ^ 5 := by gcongr
    have hbridge := mul_le_mul_of_nonneg_right hGU5
      (by positivity : (0:ℝ) ≤ P.G ^ 3 * P.U ^ 10 * (S.Δ * S.Ω ^ 5))
    calc (10:ℝ) ^ 45 * (P.G ^ 3 * P.U ^ 10) * (S.Δ * S.Ω ^ 5)
        = 10 ^ 45 * (P.G ^ 3 * P.U ^ 10 * (S.Δ * S.Ω ^ 5)) := by ring
      _ ≤ (P.G * P.U ^ 5) * (P.G ^ 3 * P.U ^ 10 * (S.Δ * S.Ω ^ 5)) := hbridge
      _ = P.G ^ 4 * P.U ^ 15 * (S.Δ * S.Ω ^ 5) := by ring
  -- ===== PIECE 3 : v-term ≤ δ4 =====
  have hp3 : 6 * ℓ₁ * P.X * (a:ℝ) * |v| * |1 / (dtilde P.X r (a:ℝ)) ^ 4 - 1 / d ^ 4| ≤ δ4 := by
    rw [hδ4_def]
    exact vterm_le (P := P) (S := S) (a := a) (r := r) (ℓ₁ := ℓ₁) (v := v) (d := d)
      hAD ha0 ha_lo ha_hi hr_lo hr_hi hℓ1pos hℓ1W hd_win hd_close hv hΔreg hG1 hU1 hΔ1 hH1 hΩU hUbig
  -- ===== ASSEMBLE =====
  have hsum : |(f:ℝ) - 𝒬| + |𝒬 - LEAD| + |phi P.X (a:ℝ) ℓ₁ ℓ₂ r - PHID|
        + 6 * ℓ₁ * P.X * (a:ℝ) * |v| * |1 / (dtilde P.X r (a:ℝ)) ^ 4 - 1 / d ^ 4|
      ≤ (10:ℝ) ^ 70 * δ4 := by
    have hcombine : δ4 + 10 ^ 68 * δ4 + δ4 + δ4 ≤ (10:ℝ) ^ 70 * δ4 := by
      have hc : (1:ℝ) + 10 ^ 68 + 1 + 1 ≤ 10 ^ 70 := by norm_num
      have h := mul_le_mul_of_nonneg_right hc hδ4_pos.le
      calc δ4 + 10 ^ 68 * δ4 + δ4 + δ4 = (1 + 10 ^ 68 + 1 + 1) * δ4 := by ring
        _ ≤ 10 ^ 70 * δ4 := h
    linarith [hp1, hp2, hp4, hp3, hcombine]
  refine le_trans hsum (le_of_eq ?_)
  rw [hδ4_def]

end Squarefree
