import Squarefree.Lower.DefectBounds

/-!
# §5 finite-difference `b̃ₐ(r)` of the defect-inverse `d̃ₐ`

We formalize the §5 finite difference (writeup line 690)

  `b̃ₐ(r) = (d̃ₐ(r+ℓ) − d̃ₐ(r))/ℓ`,

its differentiability (`HasDerivAt`, the finite difference of `d̃ₐ'`), and — via the mean
value theorem applied to `d̃ₐ` on `[r, r+ℓ]` together with `dtilde_d1_bounds` — its sign and
two-sided absolute scale `b̃ₐ(r) < 0` and `B/10⁶ ≤ |b̃ₐ(r)| ≤ 10⁶·B`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- The §5 finite-difference `b̃ₐ(r) = (d̃ₐ(r+ℓ) − d̃ₐ(r))/ℓ` (writeup 690). -/
noncomputable def bt (X a ℓ r : ℝ) : ℝ := (dtilde X (r + ℓ) a - dtilde X r a) / ℓ

/-- `b̃ₐ` is differentiable, with derivative the finite difference of `d̃ₐ'`. -/
theorem bt_hasDerivAt {X a ℓ r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r)
    (hrl : 0 < r + ℓ) (hℓ : ℓ ≠ 0) :
    HasDerivAt (fun s => bt X a ℓ s)
      ((deriv (fun s => dtilde X s a) (r + ℓ) - deriv (fun s => dtilde X s a) r) / ℓ) r := by
  -- `g1 s = d̃ₐ(s+ℓ)`, the composition with the shift `s ↦ s + ℓ`.
  have hshift : HasDerivAt (fun s => s + ℓ) 1 r := (hasDerivAt_id r).add_const ℓ
  have hdtil_rl : HasDerivAt (fun s => dtilde X s a)
      (deriv (fun s => dtilde X s a) (r + ℓ)) (r + ℓ) := by
    rw [(dtilde_r_hasDerivAt hX ha hrl).deriv]; exact dtilde_r_hasDerivAt hX ha hrl
  have hg1 : HasDerivAt (fun s => dtilde X (s + ℓ) a)
      (deriv (fun s => dtilde X s a) (r + ℓ)) r := by
    have := hdtil_rl.comp r hshift
    simpa using this
  -- `g2 s = d̃ₐ(s)`.
  have hg2 : HasDerivAt (fun s => dtilde X s a)
      (deriv (fun s => dtilde X s a) r) r := by
    rw [(dtilde_r_hasDerivAt hX ha hr).deriv]; exact dtilde_r_hasDerivAt hX ha hr
  -- subtract and divide by the constant `ℓ`.
  have hsub := (hg1.sub hg2).div_const ℓ
  simpa only [bt] using hsub

/-- Sign and two-sided scale of `b̃ₐ`: `b̃ₐ(r) < 0` and `B/10⁶ ≤ |b̃ₐ(r)| ≤ 10⁶·B`. -/
theorem bt_abs_bounds {P : Globals} {S : Scale P} {a ℓ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a) (hℓpos : 0 < ℓ)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ ≤ 16 * S.R) :
    bt P.X a ℓ r < 0
      ∧ S.B / 1000000 ≤ |bt P.X a ℓ r|
      ∧ |bt P.X a ℓ r| ≤ 1000000 * S.B := by
  have hRpos : 0 < S.R := by
    unfold Scale.R; have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  have hab : r < r + ℓ := by linarith
  set f : ℝ → ℝ := fun s => dtilde P.X s a with hf_def
  set f' : ℝ → ℝ := fun s => deriv (fun t => dtilde P.X t a) s with hf'_def
  -- continuity on the closed interval and differentiability on the open interval
  have hfc : ContinuousOn f (Set.Icc r (r + ℓ)) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hr0 hx.1
    exact (dtilde_r_hasDerivAt P.X_pos ha0 hxpos).continuousAt.continuousWithinAt
  have hff' : ∀ x ∈ Set.Ioo r (r + ℓ), HasDerivAt f (f' x) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hr0 hx.1
    have h := dtilde_r_hasDerivAt P.X_pos ha0 hxpos
    simp only [hf'_def, hf_def]
    rw [h.deriv]; exact h
  -- mean value theorem: get the interior point `c`
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f f' hab hfc hff'
  -- the slope equals `bt`
  have hslope : (f (r + ℓ) - f r) / ((r + ℓ) - r) = bt P.X a ℓ r := by
    rw [hf_def, bt]; congr 1; ring
  rw [hslope] at hc_eq
  -- so `bt = f' c = deriv f c`
  have hbt_eq : bt P.X a ℓ r = deriv (fun s => dtilde P.X s a) c := by
    rw [← hc_eq, hf'_def]
  -- `c` lies in the §5 window
  have hc_lo : (1/72) * S.R ≤ c := le_trans hr_lo (le_of_lt hc_mem.1)
  have hc_hi : c ≤ 16 * S.R := le_trans (le_of_lt hc_mem.2) hrl_hi
  have hc_pos : 0 < c := lt_trans hr0 hc_mem.1
  -- abs bounds from `dtilde_d1_bounds`
  obtain ⟨hb_lo, hb_hi⟩ := dtilde_d1_bounds hAD ha0 hc_pos ha_lo ha_hi hc_lo hc_hi
  rw [← hbt_eq] at hb_lo hb_hi
  -- sign: `bt = deriv f c = closed form < 0`
  have hsign : bt P.X a ℓ r < 0 := by
    rw [hbt_eq, (dtilde_r_hasDerivAt P.X_pos ha0 hc_pos).deriv]
    have hd : 0 < dtilde P.X c a := dtilde_pos P.X_pos ha0 hc_pos
    have hnum : 0 < dtilde P.X c a * (dtilde P.X c a + a) := by positivity
    have hden : 0 < 2 * c * (a + 2 * dtilde P.X c a) := by positivity
    have : -dtilde P.X c a * (dtilde P.X c a + a) / (2 * c * (a + 2 * dtilde P.X c a))
        = -(dtilde P.X c a * (dtilde P.X c a + a) / (2 * c * (a + 2 * dtilde P.X c a))) := by
      ring
    rw [this]
    simp only [neg_lt, neg_zero]
    exact div_pos hnum hden
  exact ⟨hsign, hb_lo, hb_hi⟩

/-- The second derivative of `b̃ₐ` is the finite difference of `d̃ₐ''`. -/
theorem bt_iteratedDeriv2 {X a ℓ r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r)
    (hrl : 0 < r + ℓ) (hℓ : ℓ ≠ 0) :
    iteratedDeriv 2 (fun s => bt X a ℓ s) r
      = (iteratedDeriv 2 (fun s => dtilde X s a) (r + ℓ)
          - iteratedDeriv 2 (fun s => dtilde X s a) r) / ℓ := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- on the open window `U`, `deriv (bt)` is the finite difference of `deriv (dtilde)`.
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr, hrl⟩
  have hee : deriv (fun s => bt X a ℓ s)
      =ᶠ[nhds r] (fun s => (deriv (fun t => dtilde X t a) (s + ℓ)
          - deriv (fun t => dtilde X t a) s) / ℓ) := by
    refine Filter.eventuallyEq_of_mem hU ?_
    intro s hs
    exact (bt_hasDerivAt hX ha hs.1 hs.2 hℓ).deriv
  rw [hee.deriv_eq]
  -- differentiate the finite difference of `d̃ₐ'`.
  have hshift : HasDerivAt (fun s => deriv (fun t => dtilde X t a) (s + ℓ))
      (iteratedDeriv 2 (fun u => dtilde X u a) (r + ℓ)) r := by
    have hadd : HasDerivAt (fun s => s + ℓ) 1 r := (hasDerivAt_id r).add_const ℓ
    have := (dtilde_deriv_hasDerivAt hX ha hrl).comp r hadd
    simpa using this
  have hbase : HasDerivAt (fun s => deriv (fun t => dtilde X t a) s)
      (iteratedDeriv 2 (fun u => dtilde X u a) r) r :=
    dtilde_deriv_hasDerivAt hX ha hr
  exact ((hshift.sub hbase).div_const ℓ).deriv

/-- **The discrete slope bound** `|(dℓ − d)/ℓ| ≤ 3·10¹²·B`, for `D`-scale witnesses
`d ≈ d̃(r)`, `dℓ ≈ d̃(r+ℓ)` of gap `ℓ ≥ 1`.  Reusable extraction of `phi_distInt_le_unif`'s
PART A: `(dℓ−d)/ℓ = b̃ + ((dℓ−d̃(r+ℓ)) − (d−d̃(r)))/ℓ`, with `|b̃| ≤ 10⁶B` (`bt_abs_bounds`)
and `|·−b̃| ≤ 2·10¹²·Δ/(GΩ³) ≤ 2·10¹²·B` (closeness, `ℓ≥1`, `B = Δ²/(GΩ³)`, `Δ≥1`). -/
theorem bzero_le {P : Globals} {S : Scale P} {a : ℝ} {r ℓ d dℓ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓpos : 0 < ℓ) (hℓ_lo : 1 ≤ ℓ)
    (hr_lo : (1/72) * S.R ≤ r) (hrl_hi : r + ℓ ≤ 16 * S.R)
    (hd_close  : |d  - dtilde P.X r (a)|       ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hdℓ_close : |dℓ - dtilde P.X (r + ℓ) (a)| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hG1 : 1 ≤ P.G) (hΔ1 : 1 ≤ S.Δ) :
    |(dℓ - d) / ℓ| ≤ 3000000000000 * S.B := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
  have hGΩ : 0 < P.G * S.Ω ^ 3 := by
    have := P.G_pos; have := S.Ω_pos; positivity
  have hBpos : 0 < S.B := by rw [Scale.B]; have := S.Δ_pos; positivity
  obtain ⟨_, _, hbt_hi⟩ :=
    bt_abs_bounds (P := P) (S := S) (a := a) (ℓ := ℓ) (r := r)
      hAD ha0 hℓpos ha_lo ha_hi hr_lo hrl_hi
  rw [bt] at hbt_hi
  set b₀ : ℝ := (dℓ - d) / ℓ with hb₀_def
  set bt₀ : ℝ := (dtilde P.X (r + ℓ) (a) - dtilde P.X r (a)) / ℓ with hbt_def
  have hΔB : S.Δ / (P.G * S.Ω ^ 3) ≤ S.B := by
    rw [Scale.B, div_le_div_iff₀ hGΩ hGΩ]
    have hΔsq : S.Δ ≤ S.Δ ^ 2 := by nlinarith [S.Δ_pos, hΔ1]
    exact mul_le_mul_of_nonneg_right hΔsq hGΩ.le
  have hdiff : |b₀ - bt₀| ≤ 2000000000000 * S.B := by
    have heq : b₀ - bt₀
        = ((dℓ - dtilde P.X (r + ℓ) (a)) - (d - dtilde P.X r (a))) / ℓ := by
      rw [hb₀_def, hbt_def]; field_simp; ring
    rw [heq, abs_div, abs_of_pos hℓpos]
    have hnum : |(dℓ - dtilde P.X (r + ℓ) (a)) - (d - dtilde P.X r (a))|
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
      calc |(dℓ - dtilde P.X (r + ℓ) (a)) - (d - dtilde P.X r (a))|
          ≤ |dℓ - dtilde P.X (r + ℓ) (a)| + |d - dtilde P.X r (a)| := abs_sub _ _
        _ ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
              + 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := add_le_add hdℓ_close hd_close
        _ = 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by ring
    have hstep : |(dℓ - dtilde P.X (r + ℓ) (a)) - (d - dtilde P.X r (a))| / ℓ
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
      rw [div_le_iff₀ hℓpos]
      have hnn : (0:ℝ) ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by
        have := S.Δ_pos; positivity
      have hle : 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
          ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) * ℓ := by
        have := mul_le_mul_of_nonneg_left hℓ_lo hnn; simpa using this
      exact le_trans hnum hle
    calc |(dℓ - dtilde P.X (r + ℓ) (a)) - (d - dtilde P.X r (a))| / ℓ
        ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := hstep
      _ ≤ 2000000000000 * S.B := mul_le_mul_of_nonneg_left hΔB (by norm_num)
  have htri : |b₀| ≤ |bt₀| + |b₀ - bt₀| := by
    have h := abs_add_le bt₀ (b₀ - bt₀)
    have he : bt₀ + (b₀ - bt₀) = b₀ := by ring
    rwa [he] at h
  have hsum : |b₀| ≤ 1000000 * S.B + 2000000000000 * S.B := le_trans htri (add_le_add hbt_hi hdiff)
  have hfact : (1000000:ℝ) * S.B + 2000000000000 * S.B = 2000001000000 * S.B := by ring
  have hmono : (2000001000000:ℝ) * S.B ≤ 3000000000000 * S.B :=
    mul_le_mul_of_nonneg_right (by norm_num) hBpos.le
  rw [hfact] at hsum
  linarith [hsum, hmono]

end Squarefree
