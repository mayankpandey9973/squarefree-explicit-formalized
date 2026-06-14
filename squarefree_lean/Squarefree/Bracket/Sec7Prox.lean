import Squarefree.Lower.DefectClose

/-!
# §7 proximity producer (G1 ruling D4, unit U3): `ftil_prox`

md 1301/1317: the §6-side proximity `|F_a(d_a^*(r)) − f̃_a(r)| ≪ H/A²` sizing the N3 branch
band, with `f̃_a(r) = F_a(d̃_a(r))` (md 1301).  Mean value of `F_a` in `d`:
`F_a'(t) = −2X/t³ + 2X/(t+a)³` (`Ffun_hasDerivAt_d`), bounded on the segment between
`d ∈ [D,2D]` and `d̃ ∈ [D/10,18D]` (`dtilde_asymp_D`) by `6Xa/(t³(t+a)) ≤ 66·10⁴·XA/D⁴`,
times `|d − d̃| ≤ 10¹²·Δ/(GΩ³)` (`dtilde_close`).  Sympy-exact key identity:
`(XA/D⁴)·(Δ/(GΩ³)) = H/A²`; constant chain `66·10⁴·10¹² = 6.6·10¹⁷ ≤ 10¹⁸`.
-/

namespace Squarefree

open Real

/-- MVT for `F_a` on `[p,q]` with `0 < p`: an interior `c` with
`F_a(q) − F_a(p) = F_a'(c)·(q − p)`. -/
private theorem Ffun_mvt_prox {X a p q : ℝ} (ha : 0 < a) (hp : 0 < p) (hpq : p < q) :
    ∃ c, p < c ∧ c < q ∧
      Ffun X a q - Ffun X a p = (-2 * X / c ^ 3 + 2 * X / (c + a) ^ 3) * (q - p) := by
  have hcont : ContinuousOn (fun t => Ffun X a t) (Set.Icc p q) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hp hs.1
    exact (Ffun_contDiffAt (ne_of_gt hs0) (by positivity)).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ioo p q, HasDerivAt (fun t => Ffun X a t)
      (-2 * X / s ^ 3 + 2 * X / (s + a) ^ 3) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hp hs.1
    exact Ffun_hasDerivAt_d X a s (ne_of_gt hs0) (by positivity)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => Ffun X a t) _ hpq hcont hderiv
  refine ⟨c, hc.1, hc.2, ?_⟩
  rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hpq))]

/-- Derivative envelope on the window: for `c ≥ D/10` and `a ∈ [A/5, 11A]`,
`|F_a'(c)| ≤ 66·10⁴·X·A/D⁴` (uses `3c²+3ca+a² ≤ 3(c+a)²`). -/
private theorem Ffun_deriv_window_bound {P : Globals} {S : Scale P} {a c : ℝ}
    (ha0 : 0 < a) (ha_hi : a ≤ 11 * S.A) (hc_lo : S.D / 10 ≤ c) :
    |(-2 * P.X / c ^ 3 + 2 * P.X / (c + a) ^ 3)| ≤ 660000 * P.X * S.A / S.D ^ 4 := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hDpos : 0 < S.D := by rw [show S.D = P.H * S.Δ from rfl]; positivity
  have hApos : 0 < S.A := by rw [show S.A = S.Δ * S.Ω from rfl]; positivity
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc_lo
  have hca : 0 < c + a := by linarith
  -- the derivative is ≤ 0, so the abs is the reversed difference
  have hval : -2 * P.X / c ^ 3 + 2 * P.X / (c + a) ^ 3 ≤ 0 := by
    have hpow : c ^ 3 ≤ (c + a) ^ 3 := pow_le_pow_left₀ hc0.le (by linarith) 3
    have h1 : 2 * P.X / (c + a) ^ 3 ≤ 2 * P.X / c ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hca 3) (pow_pos hc0 3)]
      exact mul_le_mul_of_nonneg_left hpow (by linarith)
    have hneg : -2 * P.X / c ^ 3 = -(2 * P.X / c ^ 3) := by ring
    linarith [h1, hneg.le, hneg.ge]
  rw [abs_of_nonpos hval]
  have hrw : -(-2 * P.X / c ^ 3 + 2 * P.X / (c + a) ^ 3)
      = 2 * P.X * ((c + a) ^ 3 - c ^ 3) / (c ^ 3 * (c + a) ^ 3) := by
    field_simp
    ring
  rw [hrw]
  -- numerator: (c+a)³ − c³ = a(3c²+3ca+a²) ≤ 3a(c+a)²
  have hnum : 2 * P.X * ((c + a) ^ 3 - c ^ 3) ≤ 2 * P.X * (3 * a * (c + a) ^ 2) := by
    have hcube : (c + a) ^ 3 - c ^ 3 ≤ 3 * a * (c + a) ^ 2 := by
      nlinarith [mul_pos (mul_pos ha0 ha0) hc0, mul_pos (mul_pos ha0 ha0) ha0]
    exact mul_le_mul_of_nonneg_left hcube (by linarith)
  have hden : (0:ℝ) < c ^ 3 * (c + a) ^ 3 := by positivity
  have hstep1 : 2 * P.X * ((c + a) ^ 3 - c ^ 3) / (c ^ 3 * (c + a) ^ 3)
      ≤ 6 * P.X * a / (c ^ 3 * (c + a)) := by
    have heq : 2 * P.X * (3 * a * (c + a) ^ 2) / (c ^ 3 * (c + a) ^ 3)
        = 6 * P.X * a / (c ^ 3 * (c + a)) := by
      field_simp
      ring
    calc 2 * P.X * ((c + a) ^ 3 - c ^ 3) / (c ^ 3 * (c + a) ^ 3)
        ≤ 2 * P.X * (3 * a * (c + a) ^ 2) / (c ^ 3 * (c + a) ^ 3) := by gcongr
      _ = 6 * P.X * a / (c ^ 3 * (c + a)) := heq
  -- window step: c³(c+a) ≥ (D/10)⁴, a ≤ 11A
  have hstep2 : 6 * P.X * a / (c ^ 3 * (c + a)) ≤ 660000 * P.X * S.A / S.D ^ 4 := by
    have hc4 : (S.D / 10) ^ 3 * (S.D / 10) ≤ c ^ 3 * (c + a) := by
      have h1 : (S.D / 10) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (by positivity) hc_lo 3
      have h2 : S.D / 10 ≤ c + a := by linarith
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hdenc : (0:ℝ) < c ^ 3 * (c + a) := by positivity
    rw [div_le_div_iff₀ hdenc (by positivity : (0:ℝ) < S.D ^ 4)]
    have hL : 6 * P.X * a * S.D ^ 4 ≤ 66 * P.X * S.A * S.D ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ S.D ^ 4)
      nlinarith [hX, ha_hi]
    have hR : 660000 * P.X * S.A * ((S.D / 10) ^ 3 * (S.D / 10))
        ≤ 660000 * P.X * S.A * (c ^ 3 * (c + a)) :=
      mul_le_mul_of_nonneg_left hc4 (by positivity)
    have hkey : 660000 * P.X * S.A * ((S.D / 10) ^ 3 * (S.D / 10))
        = 66 * P.X * S.A * S.D ^ 4 := by ring
    linarith [hL, hR, hkey.le, hkey.ge]
  linarith [hstep1, hstep2]

/-- **§7 proximity producer** (md 1301/1317, ruling D4 unit U3).  For a `RaWitness`-window
denominator `d ∈ [D, 2D]` with `|R_a(d) − r| ≤ 14H/D`, `a ∈ [A/5, 11A]`, `r ∈ [R/72, 16R]`:
`|F_a(d) − F_a(d̃_a(r))| ≤ 10¹⁸·(H/A²)`  — mean value of `F_a` in `d` × `dtilde_close`. -/
theorem ftil_prox {P : Globals} {S : Scale P} {a : ℤ} {r d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hrd : |Rfun P.X (a : ℝ) d - r| ≤ 14 * P.H / S.D) :
    |Ffun P.X (a : ℝ) d - Ffun P.X (a : ℝ) (dtilde P.X r (a : ℝ))| ≤
      10 ^ 18 * (P.H / S.A ^ 2) := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hDpos : 0 < S.D := by rw [show S.D = P.H * S.Δ from rfl]; positivity
  have hApos : 0 < S.A := by rw [show S.A = S.Δ * S.Ω from rfl]; positivity
  have hRpos : 0 < S.R := by
    rw [show S.R = P.H * P.G * S.Ω ^ 3 / S.Δ from rfl]; positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr_lo
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdtdef
  -- closeness and windows
  have hclose : |d - dt| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi hdD hd2D hrd
  obtain ⟨hwlo, hwhi⟩ := dtilde_asymp_D (P := P) (S := S) (a := (a : ℝ)) (r := r)
    hAD haR hr0 ha_lo ha_hi hr_lo hr_hi
  have hdlo : S.D / 10 ≤ d := by linarith
  -- key identity: (X·A/D⁴)·(Δ/(GΩ³)) = H/A²  (sympy-exact)
  have hiden : P.X * S.A / S.D ^ 4 * (S.Δ / (P.G * S.Ω ^ 3)) = P.H / S.A ^ 2 := by
    rw [show S.A = S.Δ * S.Ω from rfl, show S.D = P.H * S.Δ from rfl,
      P.X_eq_G_mul_H_pow_five]
    field_simp
  -- the MVT factorization, both orientations
  have hfact : ∃ c, S.D / 10 ≤ c ∧
      |Ffun P.X (a : ℝ) d - Ffun P.X (a : ℝ) dt|
        = |(-2 * P.X / c ^ 3 + 2 * P.X / (c + (a : ℝ)) ^ 3)| * |d - dt| := by
    rcases lt_trichotomy d dt with hlt | heq | hgt
    · obtain ⟨c, hc1, _, hslope⟩ :=
        Ffun_mvt_prox (X := P.X) haR (lt_of_lt_of_le (by positivity) hdlo) hlt
      refine ⟨c, by linarith, ?_⟩
      rw [show Ffun P.X (a : ℝ) d - Ffun P.X (a : ℝ) dt
          = -(Ffun P.X (a : ℝ) dt - Ffun P.X (a : ℝ) d) by ring, abs_neg, hslope,
        abs_mul, abs_sub_comm dt d]
    · refine ⟨S.D / 10, le_refl _, ?_⟩
      rw [heq, sub_self, sub_self, abs_zero]
      exact (mul_zero _).symm
    · obtain ⟨c, hc1, _, hslope⟩ :=
        Ffun_mvt_prox (X := P.X) haR (lt_of_lt_of_le (by positivity) hwlo) hgt
      refine ⟨c, by linarith, ?_⟩
      rw [hslope, abs_mul]
  obtain ⟨c, hc_lo, hABS⟩ := hfact
  rw [hABS]
  -- envelope × closeness, then the identity collapse
  calc |(-2 * P.X / c ^ 3 + 2 * P.X / (c + (a : ℝ)) ^ 3)| * |d - dt|
      ≤ (660000 * P.X * S.A / S.D ^ 4) * (1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) :=
        mul_le_mul (Ffun_deriv_window_bound haR ha_hi hc_lo) hclose (abs_nonneg _)
          (by positivity)
    _ = 660000000000000000 * (P.X * S.A / S.D ^ 4 * (S.Δ / (P.G * S.Ω ^ 3))) := by ring
    _ = 660000000000000000 * (P.H / S.A ^ 2) := by rw [hiden]
    _ ≤ 10 ^ 18 * (P.H / S.A ^ 2) := by
        have : (0:ℝ) ≤ P.H / S.A ^ 2 := by positivity
        nlinarith [this]

end Squarefree
