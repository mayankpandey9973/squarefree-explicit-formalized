import Squarefree.Lower.DefectRegime

/-!
# §5 curve closeness: `d → d̃ₐ(r)` (writeup ~696, Prop 3.2 error)

For a `RaWitness` denominator `d ∈ [D, 2D]` with `|R_a(d) − r| ≤ 14H/D`, the smooth inverse
`d̃ₐ(r) = dtilde P.X r a` satisfies `|d − d̃ₐ(r)| ≤ 10¹²·Δ/(GΩ³)`.

This is the §5 analogue of §6's `ftil_dtilde_close` (`Squarefree/Upper/Regime6.lean`), but for
the wider scale window `A/5 ≤ a ≤ 11A`, with the `d̃`-window `D/10 ≤ d̃ ≤ 18D` derived internally
from `dtilde_asymp_D`.  The argument is a mean-value bound: `R_a(d) − R_a(d̃) = R_a'(ξ)·(d − d̃)`
for an interior `ξ`, a lower bound `|R_a'(ξ)| ≥ R/(1.5·10¹⁰·D)`, and division.
-/

namespace Squarefree

open Real


/-- **MVT slope identity** for `R_a` on `[p,q]` (`0 < p < q`): there is an interior point `c`
with `R_a(q) − R_a(p) = R_a'(c)·(q − p)`, where `R_a'(c) = −2 X a³ (2c+a)/(c³(c+a)³)`. -/
private theorem Rfun_mvt_close {X a p q : ℝ} (_hX : 0 < X) (ha : 0 < a) (hp : 0 < p) (hpq : p < q) :
    ∃ c, p < c ∧ c < q ∧
      Rfun X a q - Rfun X a p
        = (-2 * X * a ^ 3 * (2 * c + a) / (c ^ 3 * (c + a) ^ 3)) * (q - p) := by
  have hcont : ContinuousOn (fun t => Rfun X a t) (Set.Icc p q) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hp hs.1
    exact (Rfun_contDiffAt (ne_of_gt hs0) (by positivity)).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ioo p q, HasDerivAt (fun t => Rfun X a t)
      (-2 * X * a ^ 3 * (2 * s + a) / (s ^ 3 * (s + a) ^ 3)) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hp hs.1
    exact Rfun_hasDerivAt_d X a s (ne_of_gt hs0) (by positivity)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => Rfun X a t) _ hpq hcont hderiv
  refine ⟨c, hc.1, hc.2, ?_⟩
  rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hpq))]

/-- **Curve closeness** (writeup ~696).  For `a ∈ [A/5, 11A]`, real `d ∈ [D,2D]` with
`|R_a(d) − r| ≤ 14H/D` and `r ≍ R`, the inverse point `d̃ₐ(r)` (whose `[D/10, 18D]` window is
derived from `dtilde_asymp_D`) satisfies `|d − d̃ₐ(r)| ≤ 10¹²·(Δ/(GΩ³))`. -/
theorem dtilde_close {P : Globals} {S : Scale P} {a : ℤ} {r : ℝ} {d : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hr_hi : r ≤ 16 * S.R)
    (hdD : S.D ≤ d) (hd2D : d ≤ 2 * S.D)
    (hrd : |Rfun P.X (a : ℝ) d - r| ≤ 14 * P.H / S.D) :
    |d - dtilde P.X r (a : ℝ)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
  have hX := P.X_pos
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hAeq : S.A = S.Δ * S.Ω := rfl
  have hDeq : S.D = P.H * S.Δ := rfl
  have hApos : 0 < S.A := by rw [hAeq]; positivity
  have hDpos : 0 < S.D := by rw [hDeq]; positivity
  have hXA3 : P.X * S.A ^ 3 = S.R * S.D ^ 4 := by
    rw [Scale.R, hAeq, hDeq, P.X_eq_G_mul_H_pow_five]; field_simp
  have hRpos : 0 < S.R := by
    have : 0 < S.R * S.D ^ 4 := by rw [← hXA3]; positivity
    nlinarith only [this, pow_pos hDpos 4]
  -- r > 0  (from (1/72)·R ≤ r and R > 0)
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  -- d̃ window from dtilde_asymp_D
  obtain ⟨hwlo, hwhi⟩ := dtilde_asymp_D (P := P) (S := S) (a := (a : ℝ)) (r := r)
    hAD haR hr0 ha_lo ha_hi hr_lo hr_hi
  set dt : ℝ := dtilde P.X r (a : ℝ) with hdtdef
  have hdtpos : 0 < dt := dtilde_pos hX haR hr0
  have hRdt : Rfun P.X (a : ℝ) dt = r := dtilde_spec hX haR hr0
  -- A ≤ D/10  (from 10A ≤ D)
  have hAD10 : S.A ≤ S.D / 10 := by linarith [hAD]
  -- a ≤ 11·D/10  (from a ≤ 11A and A ≤ D/10), so c + a ≤ 20D on the window
  have ha11D : (a : ℝ) ≤ 11 * S.D / 10 := by linarith only [ha_hi, hAD10]
  -- target RHS equals 14·10¹¹·H/R ≤ 10¹²·H/R  bound; we land on 2.1·10¹¹·H/R
  have hHR : P.H / S.R = S.Δ / (P.G * S.Ω ^ 3) := by rw [Scale.R]; field_simp
  -- lower bound on |R_a'(c)| for c ∈ [D/10, 18D]: |R_a'(c)| ≥ R/(15000000000 D)
  have hderiv_lb : ∀ c : ℝ, S.D / 10 ≤ c → c ≤ 18 * S.D →
      S.R / (15000000000 * S.D)
        ≤ 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3) := by
    intro c hclo hchi
    have hc0 : 0 < c := by linarith [hDpos]
    have hca : 0 < c + (a:ℝ) := by linarith [haR]
    rw [div_le_div_iff₀ (by have := hDpos; positivity) (mul_pos (pow_pos hc0 3) (pow_pos hca 3))]
    -- denominator upper bound: c³(c+a)³ ≤ (18D)³(20D)³ = 46656000 D⁶
    have hcub : c ^ 3 * (c + (a:ℝ)) ^ 3 ≤ 46656000 * S.D ^ 6 := by
      have h1 : c ≤ 18 * S.D := hchi
      have h2 : c + (a:ℝ) ≤ 20 * S.D := by linarith [ha11D]
      have hc3 : c ^ 3 ≤ (18 * S.D) ^ 3 := pow_le_pow_left₀ hc0.le h1 3
      have hca3 : (c + (a:ℝ)) ^ 3 ≤ (20 * S.D) ^ 3 := pow_le_pow_left₀ hca.le h2 3
      calc c ^ 3 * (c + (a:ℝ)) ^ 3 ≤ (18 * S.D) ^ 3 * (20 * S.D) ^ 3 :=
            mul_le_mul hc3 hca3 (by positivity) (by positivity)
        _ = 46656000 * S.D ^ 6 := by ring
    -- numerator lower bound: 2 X a³ (2c+a) ≥ 2 X (A/5)³ (2·D/10) = (2/625) X A³ D = (2/625) R D⁵
    have hXa3 : P.X * (S.A / 5) ^ 3 ≤ P.X * (a:ℝ) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hX.le
      exact pow_le_pow_left₀ (by positivity) ha_lo 3
    have hnum_lb : (2 / 625) * S.R * S.D ^ 5 ≤ 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) := by
      have h2cD : S.D / 5 ≤ 2 * c + (a:ℝ) := by linarith [hclo, haR]
      have hstep : 2 * (P.X * (S.A / 5) ^ 3) * (S.D / 5)
          ≤ 2 * (P.X * (a:ℝ) ^ 3) * (2 * c + (a:ℝ)) :=
        mul_le_mul (by linarith [hXa3]) h2cD (by positivity) (by positivity)
      have heq : 2 * (P.X * (S.A / 5) ^ 3) * (S.D / 5) = (2 / 625) * S.R * S.D ^ 5 := by
        have : P.X * (S.A / 5) ^ 3 = (P.X * S.A ^ 3) / 125 := by ring
        rw [this, hXA3]; ring
      linarith [hstep, heq.symm.le, heq.le]
    -- combine: R·c³(c+a)³ ≤ R·46656000 D⁶ ;  15000000000 D·(num) ≥ 15000000000 D·(2/625) R D⁵
    calc S.R * (c ^ 3 * (c + (a:ℝ)) ^ 3) ≤ S.R * (46656000 * S.D ^ 6) :=
          mul_le_mul_of_nonneg_left hcub hRpos.le
      _ ≤ (15000000000 * S.D) * ((2 / 625) * S.R * S.D ^ 5) := by
            have h6 : (0:ℝ) ≤ S.R * S.D ^ 6 := by positivity
            nlinarith only [h6]
      _ ≤ (15000000000 * S.D) * (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ))) :=
          mul_le_mul_of_nonneg_left hnum_lb (by have := hDpos; positivity)
      _ = 2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) * (15000000000 * S.D) := by ring
  -- target: |d - dt| ≤ 2.1·10¹¹·H/R ≤ 10¹²·H/R = 10¹²·Δ/(GΩ³)
  have hbound : |d - dt| ≤ 210000000000 * P.H / S.R := by
    rcases lt_trichotomy d dt with hlt | heq | hgt
    · -- d < dt
      obtain ⟨c, hc1, hc2, hslope⟩ := Rfun_mvt_close hX haR (by linarith [hDpos] : 0 < d) hlt
      have hclo : S.D / 10 ≤ c := by linarith [hdD, hc1, hDpos]
      have hchi : c ≤ 18 * S.D := by linarith [hwhi, hc2]
      have hc0 : 0 < c := by linarith [hDpos, hclo]
      have hcden : 0 < c ^ 3 * (c + (a:ℝ)) ^ 3 := by positivity
      have hdiff : Rfun P.X (a:ℝ) d - r
          = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := by
        have hs : Rfun P.X (a:ℝ) dt - Rfun P.X (a:ℝ) d
            = (-2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) :=
          hslope
        rw [← hRdt]
        have hneg : Rfun P.X (a:ℝ) d - Rfun P.X (a:ℝ) dt
            = -(Rfun P.X (a:ℝ) dt - Rfun P.X (a:ℝ) d) := by ring
        rw [hneg, hs]; ring
      have hderlb := hderiv_lb c hclo hchi
      have habs : |Rfun P.X (a:ℝ) d - r|
          = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := by
        rw [hdiff, abs_of_pos (mul_pos (div_pos (by positivity) hcden) (by linarith [hlt]))]
      have hge : S.R / (15000000000 * S.D) * (dt - d) ≤ 14 * P.H / S.D := by
        calc S.R / (15000000000 * S.D) * (dt - d)
            ≤ (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) :=
              mul_le_mul_of_nonneg_right hderlb (by linarith [hlt])
          _ = |Rfun P.X (a:ℝ) d - r| := habs.symm
          _ ≤ 14 * P.H / S.D := hrd
      rw [abs_of_nonpos (by linarith [hlt])]
      have hRD : 0 < S.R / (15000000000 * S.D) := by positivity
      have hmul : (dt - d) ≤ (14 * P.H / S.D) / (S.R / (15000000000 * S.D)) := by
        rw [le_div_iff₀ hRD]; linarith [hge]
      have hsimp : (14 * P.H / S.D) / (S.R / (15000000000 * S.D)) = 210000000000 * P.H / S.R := by
        field_simp; ring
      linarith [hmul, hsimp.le, hsimp.ge]
    · rw [heq, sub_self, abs_zero]; positivity
    · -- dt < d
      obtain ⟨c, hc1, hc2, hslope⟩ := Rfun_mvt_close hX haR hdtpos hgt
      have hclo : S.D / 10 ≤ c := by linarith [hwlo, hc1]
      have hchi : c ≤ 18 * S.D := by linarith [hd2D, hc2, hDpos]
      have hc0 : 0 < c := by linarith [hDpos, hclo]
      have hcden : 0 < c ^ 3 * (c + (a:ℝ)) ^ 3 := by positivity
      have hdiff : Rfun P.X (a:ℝ) d - r
          = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (dt - d) := by
        have hs : Rfun P.X (a:ℝ) d - Rfun P.X (a:ℝ) dt
            = (-2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (d - dt) :=
          hslope
        rw [← hRdt, hs]; ring
      have hderlb := hderiv_lb c hclo hchi
      have habs : |Rfun P.X (a:ℝ) d - r|
          = (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (d - dt) := by
        rw [hdiff, abs_of_nonpos (by
          apply mul_nonpos_of_nonneg_of_nonpos (by positivity); linarith [hgt])]
        ring
      have hge : S.R / (15000000000 * S.D) * (d - dt) ≤ 14 * P.H / S.D := by
        calc S.R / (15000000000 * S.D) * (d - dt)
            ≤ (2 * P.X * (a:ℝ) ^ 3 * (2 * c + (a:ℝ)) / (c ^ 3 * (c + (a:ℝ)) ^ 3)) * (d - dt) :=
              mul_le_mul_of_nonneg_right hderlb (by linarith [hgt])
          _ = |Rfun P.X (a:ℝ) d - r| := habs.symm
          _ ≤ 14 * P.H / S.D := hrd
      rw [abs_of_nonneg (by linarith [hgt])]
      have hRD : 0 < S.R / (15000000000 * S.D) := by positivity
      have hmul : (d - dt) ≤ (14 * P.H / S.D) / (S.R / (15000000000 * S.D)) := by
        rw [le_div_iff₀ hRD]; linarith [hge]
      have hsimp : (14 * P.H / S.D) / (S.R / (15000000000 * S.D)) = 210000000000 * P.H / S.R := by
        field_simp; ring
      linarith [hmul, hsimp.le, hsimp.ge]
  -- 2.1·10¹¹·H/R ≤ 10¹²·H/R = 10¹²·Δ/(GΩ³)
  calc |d - dt| ≤ 210000000000 * P.H / S.R := hbound
    _ ≤ 1000000000000 * P.H / S.R := by
        gcongr
        linarith only [hH.le]
    _ = 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by rw [← hHR]; ring

end Squarefree
