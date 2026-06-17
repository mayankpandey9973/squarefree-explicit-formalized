import Squarefree.Bracket.Sec7MonExpData

/-!
# §7 N9′ family lemmas A–B at m=3 (Φ″ endgame): `f₁` shift and first difference

The m=3-specific siblings of `build_f1_exp`/`build_d1f1_exp` (Sec7MonExpFam1.lean), on the
looser `sec7_cExp3` budget.  They reuse the EXISTING order-5 residual data (`e₁D` to order 5)
since at `m = 3` the diff-depth is `f₁ = ord 3`, `Δf₁ = ord 4` (both ≤ 5).  The m ≤ 2 path
(`build_f1_exp`/`build_d1f1_exp`, on `sec7_cExp`) is left untouched.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

namespace Sec7RaExpData

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a} {j : ℤ}
variable {h₁ h₂ h₃ : ℤ}

/-- **N9′ family A, m=3** (md 1607–12): the shifted `f₁` expansion, graded `m ≤ 3`, on the
`sec7_cExp3` budget. -/
theorem build_f1_exp3 (RE : Sec7RaExpData P S W a Ph j)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          Ph.f1D j 0 (t + sec7_hSum h₁ h₂ h₃) -
            (RE.c₁ * S.T₁ * (t / S.R) ^ (-(1:ℝ)) -
              RE.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
        sec7_cExp3 * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
          S.T₁ * sec7_relErrF P S) / S.R ^ m := by
  intro m hm r hr
  have hR : 0 < S.R := sec7_R_pos S
  have hT : 0 < S.T₁ := sec7_T₁_pos S
  have hrel : 0 < sec7_relErrF P S := sec7_relErrF_pos P S
  set hSv : ℝ := sec7_hSum h₁ h₂ h₃ with hSv_def
  have hSv3 : (3:ℝ) ≤ hSv := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hSv0 : (0:ℝ) ≤ hSv := by linarith
  have hrmid : r ∈ sec7_rWinMid S W := sec7_rWin_subset_mid S hW hr
  set M : ℕ → ℝ → ℝ := sec7_powMonD S.R (RE.c₁ * S.T₁) (-1) with hM
  set G : ℕ → ℝ → ℝ :=
    fun k t => RE.e₁D k (t + hSv) + (M k (t + hSv) - M k t - hSv * M (k + 1) t) with hG
  -- membership of displaced points
  have hmem : ∀ x ∈ sec7_rWinMid S W, ∀ d : ℝ, |d| ≤ 3 * hSv →
      x + d ∈ sec7_rWinWide S W :=
    fun x hx d hd => sec7_mem_wide_of_near hx (by
      rw [hSv_def] at hd
      exact le_trans hd hshift)
  -- the graded derivative chain on the mid window
  have hchain : ∀ k < 3, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (G k) (G (k + 1) x) x := by
    intro k hk x hx
    have hxw : x ∈ sec7_rWinWide S W := by
      simpa using hmem x hx 0 (by rw [abs_zero]; linarith)
    have hxsw : x + hSv ∈ sec7_rWinWide S W :=
      hmem x hx hSv (by rw [abs_of_nonneg hSv0]; linarith)
    have hx0 : 0 < x := sec7_rWinWide_pos hpad hxw
    have hxs0 : 0 < x + hSv := sec7_rWinWide_pos hpad hxsw
    have d1 : HasDerivAt (fun t => RE.e₁D k (t + hSv)) (RE.e₁D (k + 1) (x + hSv)) x := by
      have := (RE.e₁D_deriv k (by omega) (x + hSv) hxsw).comp x
        ((hasDerivAt_id x).add_const hSv)
      simpa using this
    have d2 : HasDerivAt (fun t => M k (t + hSv)) (M (k + 1) (x + hSv)) x := by
      have := (sec7_powMonD_hasDerivAt hR (RE.c₁ * S.T₁) (-1) k hxs0).comp x
        ((hasDerivAt_id x).add_const hSv)
      simpa [hM] using this
    have d3 : HasDerivAt (M k) (M (k + 1) x) x :=
      sec7_powMonD_hasDerivAt hR _ _ k hx0
    have d4 : HasDerivAt (fun t => hSv * M (k + 1) t) (hSv * M (k + 2) x) x :=
      (sec7_powMonD_hasDerivAt hR _ _ (k + 1) hx0).const_mul hSv
    have := d1.add ((d2.sub d3).sub d4)
    simpa [hG] using this
  -- explicit grade-0/1 monomials
  have hM0 : ∀ s : ℝ, M 0 s = RE.c₁ * S.T₁ * (s / S.R) ^ (-(1:ℝ)) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod (-1) 0 = 1 from rfl]
    norm_num
  have hM1 : ∀ s : ℝ, M 1 s = -(RE.c₁ * S.T₁ / S.R) * (s / S.R) ^ (-(2:ℝ)) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod (-1) 1 = -1 from by norm_num [sec7_aprod]]
    norm_num
    ring
  -- grade-0 identification with the target function
  have hG0 : (fun t => Ph.f1D j 0 (t + hSv) -
      (RE.c₁ * S.T₁ * (t / S.R) ^ (-(1:ℝ)) -
        RE.c₁ * hSv * (S.T₁ / S.R) * (t / S.R) ^ (-(2:ℝ)))) = G 0 := by
    funext t
    simp only [hG, RE.e₁D_zero, hM0, hM1]
    ring
  rw [hG0, sec7_iteratedDeriv_eq_of_chain (sec7_rWinMid_isOpen S W) hchain m hm r hrmid]
  -- bound the two parts
  have hrsw : r + hSv ∈ sec7_rWinWide S W :=
    hmem r hrmid hSv (by rw [abs_of_nonneg hSv0]; linarith)
  have he : |RE.e₁D m (r + hSv)| ≤ sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S :=
    RE.e₁D_bound m (by omega) _ hrsw
  set B : ℝ := |RE.c₁| * S.T₁ * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) /
    S.R ^ (m + 2) with hB
  have hcWpos : (0:ℝ) < 2 * sec7_cWin := by norm_num [sec7_cWin]
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hIccmem : ∀ x ∈ Icc r (r + hSv), x ∈ sec7_rWinWide S W := by
    intro x hx
    have : x = r + (x - r) := by ring
    rw [this]
    exact hmem r hrmid (x - r)
      (by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2])
  have htay : |M m (r + hSv) - M m r - hSv * M (m + 1) r| ≤ B * hSv ^ 2 := by
    apply sec7_taylor2_le hSv0 hBnn
    · exact fun x hx => sec7_powMonD_hasDerivAt hR _ _ m
        (sec7_rWinWide_pos hpad (hIccmem x hx))
    · exact fun x hx => sec7_powMonD_hasDerivAt hR _ _ (m + 1)
        (sec7_rWinWide_pos hpad (hIccmem x hx))
    · intro x hx
      have hbd := sec7_powMonD_wide_bound (c := RE.c₁ * S.T₁) (α := -1) (k := m + 2)
        (by have h0 : (0:ℝ) ≤ (m:ℝ) := by positivity
            push_cast; linarith) hpad (hIccmem x hx)
      have hexp : ((m + 2 : ℕ) : ℝ) - (-1) = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_natCast] at hbd
      have habs : |RE.c₁ * S.T₁| = |RE.c₁| * S.T₁ := by
        rw [abs_mul, abs_of_pos hT]
      rw [habs] at hbd
      calc |M (m + 2) x| ≤ |RE.c₁| * S.T₁ * |sec7_aprod (-1) (m + 2)| / S.R ^ (m + 2) *
            (2 * sec7_cWin) ^ (m + 3) := by rw [hM]; exact hbd
        _ = B := by rw [hB]; ring
  -- assemble and compare with the target bound
  have hsplit : |G m r| ≤ sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S + B * hSv ^ 2 := by
    have : |G m r| ≤ |RE.e₁D m (r + hSv)| + |M m (r + hSv) - M m r - hSv * M (m + 1) r| := by
      simp only [hG]
      exact abs_add_le _ _
    linarith [he, htay]
  refine le_trans hsplit ?_
  -- numerics
  have haprod : |sec7_aprod (-1) (m + 2)| ≤ 120 := by
    interval_cases m <;> norm_num [sec7_aprod]
  have hpowle : ((2:ℝ) * sec7_cWin) ^ (m + 3) ≤ (2 * sec7_cWin) ^ 6 :=
    pow_le_pow_right₀ (by norm_num [sec7_cWin]) (by omega)
  have hc : |RE.c₁| ≤ 4 := RE.c₁_hi
  have hcoef : |RE.c₁| * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) ≤
      sec7_cExp3 := by
    have p1 : (0:ℝ) ≤ |RE.c₁| := abs_nonneg _
    have p2 : (0:ℝ) ≤ |sec7_aprod (-1) (m + 2)| := abs_nonneg _
    have p3 : (0:ℝ) ≤ ((2:ℝ) * sec7_cWin) ^ (m + 3) := by positivity
    have h480 : |RE.c₁| * |sec7_aprod (-1) (m + 2)| ≤ 480 := by nlinarith
    have h1 : |RE.c₁| * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) ≤
        480 * (2 * sec7_cWin) ^ 6 :=
      le_trans (mul_le_mul_of_nonneg_right h480 p3)
        (mul_le_mul_of_nonneg_left hpowle (by norm_num))
    refine le_trans h1 ?_
    norm_num [sec7_cWin, sec7_cExp3]
  have hkey1 : sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S ≤
      sec7_cExp3 * (S.T₁ * sec7_relErrF P S) / S.R ^ m := by
    have hIn : sec7_cExpIn ≤ sec7_cExp3 := by norm_num [sec7_cExpIn, sec7_cExp3]
    have hmono : (0:ℝ) ≤ S.T₁ * sec7_relErrF P S / S.R ^ m := by positivity
    calc sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S
        = sec7_cExpIn * (S.T₁ * sec7_relErrF P S / S.R ^ m) := by ring
      _ ≤ sec7_cExp3 * (S.T₁ * sec7_relErrF P S / S.R ^ m) :=
          mul_le_mul_of_nonneg_right hIn hmono
      _ = sec7_cExp3 * (S.T₁ * sec7_relErrF P S) / S.R ^ m := by ring
  have hkey2 : B * hSv ^ 2 ≤ sec7_cExp3 * (hSv ^ 2 * S.T₁ / S.R ^ 2) / S.R ^ m := by
    have hmono : (0:ℝ) ≤ hSv ^ 2 * S.T₁ / S.R ^ (m + 2) := by positivity
    calc B * hSv ^ 2
        = |RE.c₁| * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) *
            (hSv ^ 2 * S.T₁ / S.R ^ (m + 2)) := by rw [hB]; ring
      _ ≤ sec7_cExp3 * (hSv ^ 2 * S.T₁ / S.R ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right hcoef hmono
      _ = sec7_cExp3 * (hSv ^ 2 * S.T₁ / S.R ^ 2) / S.R ^ m := by
          rw [pow_add]
          field_simp
  calc sec7_cExpIn * (S.T₁ / S.R ^ m) * sec7_relErrF P S + B * hSv ^ 2
      ≤ sec7_cExp3 * (S.T₁ * sec7_relErrF P S) / S.R ^ m +
        sec7_cExp3 * (hSv ^ 2 * S.T₁ / S.R ^ 2) / S.R ^ m := by linarith [hkey1, hkey2]
    _ = sec7_cExp3 * (hSv ^ 2 * S.T₁ / S.R ^ 2 + S.T₁ * sec7_relErrF P S) / S.R ^ m := by
        ring

/-- **N9′ family B, m=3** (md 1613–17): the differenced `f₁` expansion, graded `m ≤ 3`,
generic in the step `h ∈ {h₁, h₂, h₃}`, on the `sec7_cExp3` budget. -/
theorem build_d1f1_exp3 (RE : Sec7RaExpData P S W a Ph j)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃) {h : ℤ} (hh : 1 ≤ h)
    (hhle : (h : ℝ) ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff1 (h : ℝ) (Ph.f1D j 0) (t + sec7_hSum h₁ h₂ h₃ - h) -
            (-(RE.c₁ * h * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
        sec7_cExp3 * ((h : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
          (h : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m := by
  intro m hm r hr
  have hR : 0 < S.R := sec7_R_pos S
  have hT : 0 < S.T₁ := sec7_T₁_pos S
  have hrel : 0 < sec7_relErrF P S := sec7_relErrF_pos P S
  set hSv : ℝ := sec7_hSum h₁ h₂ h₃ with hSv_def
  have hSv3 : (3:ℝ) ≤ hSv := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hSv0 : (0:ℝ) ≤ hSv := by linarith
  have hv1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hv0 : (0:ℝ) ≤ (h:ℝ) := by linarith
  have hrmid : r ∈ sec7_rWinMid S W := sec7_rWin_subset_mid S hW hr
  set M : ℕ → ℝ → ℝ := sec7_powMonD S.R (RE.c₁ * S.T₁) (-1) with hM
  set G : ℕ → ℝ → ℝ := fun k t => (RE.e₁D k (t + hSv) - RE.e₁D k (t + (hSv - h))) +
    (M k (t + hSv) - M k (t + (hSv - h)) - (h:ℝ) * M (k + 1) t) with hG
  have hmem : ∀ x ∈ sec7_rWinMid S W, ∀ d : ℝ, |d| ≤ 3 * hSv →
      x + d ∈ sec7_rWinWide S W :=
    fun x hx d hd => sec7_mem_wide_of_near hx (by
      rw [hSv_def] at hd
      exact le_trans hd hshift)
  -- the graded derivative chain on the mid window
  have hchain : ∀ k < 3, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (G k) (G (k + 1) x) x := by
    intro k hk x hx
    have hxw : x ∈ sec7_rWinWide S W := by
      simpa using hmem x hx 0 (by rw [abs_zero]; linarith)
    have hxsw : x + hSv ∈ sec7_rWinWide S W :=
      hmem x hx hSv (by rw [abs_of_nonneg hSv0]; linarith)
    have hxmw : x + (hSv - h) ∈ sec7_rWinWide S W :=
      hmem x hx (hSv - h) (by rw [abs_of_nonneg (by linarith)]; linarith)
    have hx0 : 0 < x := sec7_rWinWide_pos hpad hxw
    have hxs0 : 0 < x + hSv := sec7_rWinWide_pos hpad hxsw
    have hxm0 : 0 < x + (hSv - h) := sec7_rWinWide_pos hpad hxmw
    have d1 : HasDerivAt (fun t => RE.e₁D k (t + hSv)) (RE.e₁D (k + 1) (x + hSv)) x := by
      have := (RE.e₁D_deriv k (by omega) (x + hSv) hxsw).comp x
        ((hasDerivAt_id x).add_const hSv)
      simpa using this
    have d2 : HasDerivAt (fun t => RE.e₁D k (t + (hSv - h)))
        (RE.e₁D (k + 1) (x + (hSv - h))) x := by
      have := (RE.e₁D_deriv k (by omega) (x + (hSv - h)) hxmw).comp x
        ((hasDerivAt_id x).add_const (hSv - h))
      simpa using this
    have d3 : HasDerivAt (fun t => M k (t + hSv)) (M (k + 1) (x + hSv)) x := by
      have := (sec7_powMonD_hasDerivAt hR (RE.c₁ * S.T₁) (-1) k hxs0).comp x
        ((hasDerivAt_id x).add_const hSv)
      simpa [hM] using this
    have d4 : HasDerivAt (fun t => M k (t + (hSv - h))) (M (k + 1) (x + (hSv - h))) x := by
      have := (sec7_powMonD_hasDerivAt hR (RE.c₁ * S.T₁) (-1) k hxm0).comp x
        ((hasDerivAt_id x).add_const (hSv - h))
      simpa [hM] using this
    have d5 : HasDerivAt (fun t => (h:ℝ) * M (k + 1) t) ((h:ℝ) * M (k + 2) x) x :=
      (sec7_powMonD_hasDerivAt hR _ _ (k + 1) hx0).const_mul (h:ℝ)
    have := (d1.sub d2).add ((d3.sub d4).sub d5)
    simpa [hG] using this
  -- explicit grade-0/1 monomials
  have hM0 : ∀ s : ℝ, M 0 s = RE.c₁ * S.T₁ * (s / S.R) ^ (-(1:ℝ)) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod (-1) 0 = 1 from rfl]
    norm_num
  have hM1 : ∀ s : ℝ, M 1 s = -(RE.c₁ * S.T₁ / S.R) * (s / S.R) ^ (-(2:ℝ)) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod (-1) 1 = -1 from by norm_num [sec7_aprod]]
    norm_num
    ring
  -- grade-0 identification
  have hG0 : (fun t => diff1 (h : ℝ) (Ph.f1D j 0) (t + hSv - h) -
      (-(RE.c₁ * h * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) = G 0 := by
    funext t
    have harg2 : t + hSv - (h:ℝ) = t + (hSv - h) := by ring
    simp only [hG, RE.e₁D_zero, hM0, hM1, diff1, harg2]
    ring_nf
  rw [hG0, sec7_iteratedDeriv_eq_of_chain (sec7_rWinMid_isOpen S W) hchain m hm r hrmid]
  -- memberships along [r, r + hSv]
  have hIccmem : ∀ x ∈ Icc r (r + hSv), x ∈ sec7_rWinWide S W := by
    intro x hx
    have : x = r + (x - r) := by ring
    rw [this]
    exact hmem r hrmid (x - r)
      (by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2])
  -- e-part bound (MVT on [r + (hSv − h), r + hSv])
  have heIcc : ∀ x ∈ Icc (r + (hSv - h)) (r + hSv), x ∈ sec7_rWinWide S W := by
    intro x hx
    exact hIccmem x ⟨by linarith [hx.1, hv1], hx.2⟩
  have hederiv : ∀ x ∈ Icc (r + (hSv - h)) (r + hSv),
      HasDerivAt (RE.e₁D m) (RE.e₁D (m + 1) x) x :=
    fun x hx => RE.e₁D_deriv m (by omega) x (heIcc x hx)
  have hebound : ∀ x ∈ Icc (r + (hSv - h)) (r + hSv),
      |RE.e₁D (m + 1) x| ≤ sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S :=
    fun x hx => RE.e₁D_bound (m + 1) (by omega) x (heIcc x hx)
  have he : |RE.e₁D m (r + hSv) - RE.e₁D m (r + (hSv - h))| ≤
      sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S * (h:ℝ) := by
    have := sec7_abs_sub_le_of_deriv (g := RE.e₁D m) (g' := RE.e₁D (m + 1))
      (a := r + (hSv - h)) (b := r + hSv) (by linarith) hederiv hebound
    calc |RE.e₁D m (r + hSv) - RE.e₁D m (r + (hSv - h))|
        ≤ sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S *
          (r + hSv - (r + (hSv - h))) := this
      _ = sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S * (h:ℝ) := by ring
  -- monomial part: Taylor-2 at r + (hSv − h) plus MVT realignment
  set B : ℝ := |RE.c₁| * S.T₁ * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) /
    S.R ^ (m + 2) with hB
  have hcWpos : (0:ℝ) < 2 * sec7_cWin := by norm_num [sec7_cWin]
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hMbd : ∀ x ∈ Icc r (r + hSv), |M (m + 2) x| ≤ B := by
    intro x hx
    have hbd := sec7_powMonD_wide_bound (c := RE.c₁ * S.T₁) (α := -1) (k := m + 2)
      (by have h0 : (0:ℝ) ≤ (m:ℝ) := by positivity
          push_cast; linarith) hpad (hIccmem x hx)
    have hexp : ((m + 2 : ℕ) : ℝ) - (-1) = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast] at hbd
    have habs : |RE.c₁ * S.T₁| = |RE.c₁| * S.T₁ := by rw [abs_mul, abs_of_pos hT]
    rw [habs] at hbd
    calc |M (m + 2) x| ≤ |RE.c₁| * S.T₁ * |sec7_aprod (-1) (m + 2)| / S.R ^ (m + 2) *
          (2 * sec7_cWin) ^ (m + 3) := by rw [hM]; exact hbd
      _ = B := by rw [hB]; ring
  have htay : |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) (r + (hSv - h))| ≤
      B * (h:ℝ) ^ 2 := by
    have := sec7_taylor2_le (g := M m) (g' := M (m + 1)) (g'' := M (m + 2))
      (s := r + (hSv - h)) (h := (h:ℝ)) hv0 hBnn
      (fun x hx => sec7_powMonD_hasDerivAt hR _ _ m
        (sec7_rWinWide_pos hpad (hIccmem x ⟨by linarith [hx.1, hv1], by linarith [hx.2]⟩)))
      (fun x hx => sec7_powMonD_hasDerivAt hR _ _ (m + 1)
        (sec7_rWinWide_pos hpad (hIccmem x ⟨by linarith [hx.1, hv1], by linarith [hx.2]⟩)))
      (fun x hx => hMbd x ⟨by linarith [hx.1, hv1], by linarith [hx.2]⟩)
    calc |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) (r + (hSv - h))|
        = |M m (r + (hSv - h) + h) - M m (r + (hSv - h)) -
            (h:ℝ) * M (m + 1) (r + (hSv - h))| := by rw [show r + (hSv - (h:ℝ)) + h = r + hSv from by ring]
      _ ≤ B * (h:ℝ) ^ 2 := this
  have hmvt : |M (m + 1) (r + (hSv - h)) - M (m + 1) r| ≤ B * (hSv - h) := by
    have := sec7_abs_sub_le_of_deriv (g := M (m + 1)) (g' := M (m + 2))
      (a := r) (b := r + (hSv - h)) (by linarith)
      (fun x hx => sec7_powMonD_hasDerivAt hR _ _ (m + 1)
        (sec7_rWinWide_pos hpad (hIccmem x ⟨hx.1, by linarith [hx.2]⟩)))
      (fun x hx => hMbd x ⟨hx.1, by linarith [hx.2]⟩)
    calc |M (m + 1) (r + (hSv - h)) - M (m + 1) r| ≤ B * (r + (hSv - h) - r) := this
      _ = B * (hSv - h) := by ring
  have hmon : |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) r| ≤
      B * (h:ℝ) * hSv := by
    have htri : |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) r| ≤
        |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) (r + (hSv - h))| +
        (h:ℝ) * |M (m + 1) (r + (hSv - h)) - M (m + 1) r| := by
      have habs2 : (h:ℝ) * |M (m + 1) (r + (hSv - h)) - M (m + 1) r| =
          |(h:ℝ) * (M (m + 1) (r + (hSv - h)) - M (m + 1) r)| := by
        rw [abs_mul, abs_of_nonneg hv0]
      rw [habs2]
      calc |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) r|
          = |(M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) (r + (hSv - h))) +
            (h:ℝ) * (M (m + 1) (r + (hSv - h)) - M (m + 1) r)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hsq : B * (h:ℝ) ^ 2 + (h:ℝ) * (B * (hSv - h)) = B * (h:ℝ) * hSv := by ring
    calc |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) r|
        ≤ B * (h:ℝ) ^ 2 + (h:ℝ) * (B * (hSv - h)) := by
          have := mul_le_mul_of_nonneg_left hmvt hv0
          linarith [htay, this]
      _ = B * (h:ℝ) * hSv := hsq
  -- assemble
  have hsplit : |G m r| ≤ sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S * (h:ℝ) +
      B * (h:ℝ) * hSv := by
    have h1 : |G m r| ≤ |RE.e₁D m (r + hSv) - RE.e₁D m (r + (hSv - h))| +
        |M m (r + hSv) - M m (r + (hSv - h)) - (h:ℝ) * M (m + 1) r| := by
      simp only [hG]
      exact abs_add_le _ _
    linarith [he, hmon]
  refine le_trans hsplit ?_
  -- numerics
  have haprod : |sec7_aprod (-1) (m + 2)| ≤ 120 := by
    interval_cases m <;> norm_num [sec7_aprod]
  have hpowle : ((2:ℝ) * sec7_cWin) ^ (m + 3) ≤ (2 * sec7_cWin) ^ 6 :=
    pow_le_pow_right₀ (by norm_num [sec7_cWin]) (by omega)
  have hc : |RE.c₁| ≤ 4 := RE.c₁_hi
  have hcoef : |RE.c₁| * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) ≤
      sec7_cExp3 := by
    have p1 : (0:ℝ) ≤ |RE.c₁| := abs_nonneg _
    have p2 : (0:ℝ) ≤ |sec7_aprod (-1) (m + 2)| := abs_nonneg _
    have p3 : (0:ℝ) ≤ ((2:ℝ) * sec7_cWin) ^ (m + 3) := by positivity
    have h480 : |RE.c₁| * |sec7_aprod (-1) (m + 2)| ≤ 480 := by nlinarith
    have h1 : |RE.c₁| * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) ≤
        480 * (2 * sec7_cWin) ^ 6 :=
      le_trans (mul_le_mul_of_nonneg_right h480 p3)
        (mul_le_mul_of_nonneg_left hpowle (by norm_num))
    refine le_trans h1 ?_
    norm_num [sec7_cWin, sec7_cExp3]
  have hkey1 : sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S * (h:ℝ) ≤
      sec7_cExp3 * ((h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m := by
    have hIn : sec7_cExpIn ≤ sec7_cExp3 := by norm_num [sec7_cExpIn, sec7_cExp3]
    have hmono : (0:ℝ) ≤ (h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S / S.R ^ m := by positivity
    calc sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S * (h:ℝ)
        = sec7_cExpIn * ((h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S / S.R ^ m) := by
          rw [pow_succ]
          field_simp
      _ ≤ sec7_cExp3 * ((h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S / S.R ^ m) :=
          mul_le_mul_of_nonneg_right hIn hmono
      _ = sec7_cExp3 * ((h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m := by ring
  have hkey2 : B * (h:ℝ) * hSv ≤
      sec7_cExp3 * ((h:ℝ) * hSv * S.T₁ / S.R ^ 2) / S.R ^ m := by
    have hmono : (0:ℝ) ≤ (h:ℝ) * hSv * S.T₁ / S.R ^ (m + 2) := by positivity
    calc B * (h:ℝ) * hSv
        = |RE.c₁| * |sec7_aprod (-1) (m + 2)| * (2 * sec7_cWin) ^ (m + 3) *
            ((h:ℝ) * hSv * S.T₁ / S.R ^ (m + 2)) := by rw [hB]; ring
      _ ≤ sec7_cExp3 * ((h:ℝ) * hSv * S.T₁ / S.R ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right hcoef hmono
      _ = sec7_cExp3 * ((h:ℝ) * hSv * S.T₁ / S.R ^ 2) / S.R ^ m := by
          rw [pow_add]
          field_simp
  calc sec7_cExpIn * (S.T₁ / S.R ^ (m + 1)) * sec7_relErrF P S * (h:ℝ) + B * (h:ℝ) * hSv
      ≤ sec7_cExp3 * ((h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m +
        sec7_cExp3 * ((h:ℝ) * hSv * S.T₁ / S.R ^ 2) / S.R ^ m := by linarith [hkey1, hkey2]
    _ = sec7_cExp3 * ((h:ℝ) * hSv * S.T₁ / S.R ^ 2 +
        (h:ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m := by ring

end Sec7RaExpData

end Squarefree
