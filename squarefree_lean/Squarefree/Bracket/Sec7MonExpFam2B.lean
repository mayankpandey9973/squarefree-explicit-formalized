import Squarefree.Bracket.Sec7MonExpData

/-!
# §7 N9′ family lemma C at m=3 (Φ″ endgame): the `B_i` double differences of `f₂`

The m=3-specific sibling of `build_B_exp` (Sec7MonExpFam2.lean), on the looser `sec7_cExp3Lead`
budget.  It reuses the EXISTING order-5 residual data (`e₂D` to order 5): at `m = 3` the
diff-depth is `B = ord 5 ≤ 5`.  The m ≤ 2 path (`build_B_exp`, on `sec7_cExp`) is untouched.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

namespace Sec7RaExpData

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a} {j : ℤ}
variable {h₁ h₂ h₃ : ℤ}

/-- **N9′ family C, m=3** (md 1618–22): the double-differenced `f₂` expansion at a
`ξ`-shifted point, graded `m ≤ 3`, generic in the steps `(p, q)` and shift `ξ`, on the
`sec7_cExp3Lead` budget. -/
theorem build_B_exp3 (RE : Sec7RaExpData P S W a Ph j)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃) {p q : ℤ} {ξ : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : (p : ℝ) + q ≤ sec7_hSum h₁ h₂ h₃)
    (hξ : |ξ| ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff1 (p : ℝ) (diff1 (q : ℝ) (Ph.f2D 0)) (t + ξ) -
            (-(3/16) * RE.c₂ * p * q * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) r| ≤
        sec7_cExp3Lead * ((p : ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
          (p : ℝ) * q * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ m := by
  intro m hm r hr
  have hR : 0 < S.R := sec7_R_pos S
  have hT : 0 < S.T₂ := sec7_T₂_pos S
  have hrel : 0 < sec7_relErr P S := sec7_relErr_pos P S
  set hSv : ℝ := sec7_hSum h₁ h₂ h₃ with hSv_def
  have hSv3 : (3:ℝ) ≤ hSv := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hSv0 : (0:ℝ) ≤ hSv := by linarith
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  obtain ⟨hξlo, hξhi⟩ := abs_le.mp hξ
  have hrmid : r ∈ sec7_rWinMid S W := sec7_rWin_subset_mid S hW hr
  set M : ℕ → ℝ → ℝ := sec7_powMonD S.R (RE.c₂ * S.T₂) (3/4) with hM
  set G : ℕ → ℝ → ℝ := fun k t => diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D k)) (t + ξ) +
    (diff1 (p:ℝ) (diff1 (q:ℝ) (M k)) (t + ξ) - (p:ℝ) * q * M (k + 2) t) with hG
  have hmem : ∀ x ∈ sec7_rWinMid S W, ∀ d : ℝ, |d| ≤ 3 * hSv →
      x + d ∈ sec7_rWinWide S W :=
    fun x hx d hd => sec7_mem_wide_of_near hx (by
      rw [hSv_def] at hd
      exact le_trans hd hshift)
  -- membership of all displaced points x + ξ + θp·p + θq·q, θ ∈ [0,1]
  have hdisp : ∀ x ∈ sec7_rWinMid S W, ∀ d : ℝ, ξ ≤ d → d ≤ ξ + p + q →
      x + d ∈ sec7_rWinWide S W := by
    intro x hx d hd1 hd2
    apply hmem x hx d
    rw [abs_le]
    constructor <;> nlinarith
  have hseg : ∀ x ∈ sec7_rWinMid S W, ∀ y : ℝ, ξ ≤ y - x → y - x ≤ ξ + p + q →
      y ∈ sec7_rWinWide S W := by
    intro x hx y h1 h2
    have hy : y = x + (y - x) := by ring
    rw [hy]
    exact hdisp x hx (y - x) h1 h2
  -- derivative chains for the shifted double differences (k < 5 of e₂D; any k of M)
  have heDD : ∀ k < 4, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (fun t => diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D k)) (t + ξ))
        (diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D (k + 1))) (x + ξ)) x := by
    intro k hk x hx
    have hd : HasDerivAt (diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D k)))
        (diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D (k + 1))) (x + ξ)) (x + ξ) := by
      apply sec7_diff1_hasDerivAt <;>
        apply sec7_diff1_hasDerivAt <;>
        exact RE.e₂D_deriv k (by omega) _
          (hseg x hx _ (by linarith) (by linarith))
    have := hd.comp x ((hasDerivAt_id x).add_const ξ)
    simpa using this
  have hMDD : ∀ k, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (fun t => diff1 (p:ℝ) (diff1 (q:ℝ) (M k)) (t + ξ))
        (diff1 (p:ℝ) (diff1 (q:ℝ) (M (k + 1))) (x + ξ)) x := by
    intro k x hx
    have hd : HasDerivAt (diff1 (p:ℝ) (diff1 (q:ℝ) (M k)))
        (diff1 (p:ℝ) (diff1 (q:ℝ) (M (k + 1))) (x + ξ)) (x + ξ) := by
      apply sec7_diff1_hasDerivAt <;>
        apply sec7_diff1_hasDerivAt <;>
        exact sec7_powMonD_hasDerivAt hR _ _ _
          (sec7_rWinWide_pos hpad (hseg x hx _ (by linarith) (by linarith)))
    have := hd.comp x ((hasDerivAt_id x).add_const ξ)
    simpa using this
  -- the graded derivative chain on the mid window
  have hchain : ∀ k < 3, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (G k) (G (k + 1) x) x := by
    intro k hk x hx
    have hxw : x ∈ sec7_rWinWide S W := by
      simpa using hmem x hx 0 (by rw [abs_zero]; linarith)
    have hx0 : 0 < x := sec7_rWinWide_pos hpad hxw
    have d3 : HasDerivAt (fun t => (p:ℝ) * q * M (k + 2) t) ((p:ℝ) * q * M (k + 3) x) x :=
      (sec7_powMonD_hasDerivAt hR _ _ (k + 2) hx0).const_mul ((p:ℝ) * q)
    have := (heDD k (by omega) x hx).add ((hMDD k x hx).sub d3)
    simpa [hG] using this
  -- explicit monomials
  have hM0 : ∀ s : ℝ, M 0 s = RE.c₂ * S.T₂ * (s / S.R) ^ ((3:ℝ)/4) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod (3/4) 0 = 1 from rfl]
    norm_num
  have hM2 : ∀ s : ℝ, M 2 s =
      -(3/16) * RE.c₂ * (S.T₂ / S.R ^ 2) * (s / S.R) ^ (-(5:ℝ)/4) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod (3/4) 2 = -(3/16) from by norm_num [sec7_aprod]]
    rw [show (3:ℝ)/4 - ((2:ℕ):ℝ) = -(5:ℝ)/4 from by push_cast; norm_num]
    ring
  -- grade-0 identification
  have hG0 : (fun t => diff1 (p:ℝ) (diff1 (q:ℝ) (Ph.f2D 0)) (t + ξ) -
      (-(3/16) * RE.c₂ * p * q * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) = G 0 := by
    funext t
    simp only [hG, diff1, RE.e₂D_zero, hM0, hM2]
    ring
  rw [hG0, sec7_iteratedDeriv_eq_of_chain (sec7_rWinMid_isOpen S W) hchain m hm r hrmid]
  -- wide membership of the MVT segments
  have hsegmem : ∀ x : ℝ, ξ ≤ x - r → x - r ≤ ξ + p + q → x ∈ sec7_rWinWide S W := by
    intro x h1 h2
    have : x = r + (x - r) := by ring
    rw [this]
    exact hdisp r hrmid (x - r) h1 h2
  -- e-part bound: two nested first-difference MVT inequalities
  set C : ℝ := sec7_cExpIn * (S.T₂ / S.R ^ (m + 2)) * sec7_relErr P S with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg sec7_cExpIn_pos.le
      (div_nonneg hT.le (pow_nonneg hR.le _))) hrel.le
  have hepart : |diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D m)) (r + ξ)| ≤ C * q * p := by
    apply sec7_diff1_abs_le hp0.le
    · intro x hx
      apply sec7_diff1_hasDerivAt <;>
        exact RE.e₂D_deriv m (by omega) _
          (hsegmem _ (by linarith [hx.1]) (by linarith [hx.2]))
    · intro x hx
      apply sec7_diff1_abs_le hq0.le
      · intro y hy
        exact RE.e₂D_deriv (m + 1) (by omega) _
          (hsegmem _ (by linarith [hx.1, hy.1]) (by linarith [hx.2, hy.2]))
      · intro y hy
        rw [hC]
        exact RE.e₂D_bound (m + 2) (by omega) _
          (hsegmem _ (by linarith [hx.1, hy.1]) (by linarith [hx.2, hy.2]))
  -- monomial sup bound at order m+3
  set B : ℝ := |RE.c₂| * S.T₂ * |sec7_aprod (3/4) (m + 3)| * (2 * sec7_cWin) ^ (m + 3) /
    S.R ^ (m + 3) with hB
  have hcWpos : (0:ℝ) < 2 * sec7_cWin := by norm_num [sec7_cWin]
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hMbd : ∀ x ∈ sec7_rWinWide S W, |M (m + 3) x| ≤ B := by
    intro x hx
    have hbd := sec7_powMonD_wide_bound (c := RE.c₂ * S.T₂) (α := 3/4) (k := m + 3)
      (by have h0 : (0:ℝ) ≤ (m:ℝ) := by positivity
          push_cast; linarith) hpad hx
    have hexple : (2 * sec7_cWin) ^ (((m + 3 : ℕ) : ℝ) - 3/4) ≤
        ((2 * sec7_cWin) ^ (m + 3) : ℝ) := by
      have h1 : (2 * sec7_cWin) ^ (((m + 3 : ℕ) : ℝ) - 3/4) ≤
          (2 * sec7_cWin) ^ (((m + 3 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num [sec7_cWin]) (by linarith)
      rwa [Real.rpow_natCast] at h1
    have habs : |RE.c₂ * S.T₂| = |RE.c₂| * S.T₂ := by rw [abs_mul, abs_of_pos hT]
    rw [habs] at hbd
    have hcnn : (0:ℝ) ≤ |RE.c₂| * S.T₂ * |sec7_aprod (3/4) (m + 3)| / S.R ^ (m + 3) := by
      positivity
    calc |M (m + 3) x| ≤ |RE.c₂| * S.T₂ * |sec7_aprod (3/4) (m + 3)| / S.R ^ (m + 3) *
          (2 * sec7_cWin) ^ (((m + 3 : ℕ) : ℝ) - 3/4) := by
          rw [hM]
          convert hbd using 2
          try ring
      _ ≤ |RE.c₂| * S.T₂ * |sec7_aprod (3/4) (m + 3)| / S.R ^ (m + 3) *
          (2 * sec7_cWin) ^ (m + 3) := mul_le_mul_of_nonneg_left hexple hcnn
      _ = B := by rw [hB]; ring
  -- ball membership around r
  have hball : ∀ x : ℝ, |x - r| ≤ 2 * hSv → x ∈ sec7_rWinWide S W := by
    intro x hx
    have : x = r + (x - r) := by ring
    rw [this]
    exact hmem r hrmid (x - r) (by linarith [hx])
  -- exact double MVT for the monomial double difference
  obtain ⟨ζ₁, hζ₁, hA1⟩ := sec7_diff_eq_mul_deriv (g := diff1 (q:ℝ) (M m))
    (g' := diff1 (q:ℝ) (M (m + 1))) (s := r + ξ) (h := (p:ℝ)) hp0
    (by
      intro x hx
      apply sec7_diff1_hasDerivAt <;>
        · rw [hM]
          apply sec7_powMonD_hasDerivAt hR
          apply sec7_rWinWide_pos hpad
          apply hsegmem
          all_goals nlinarith [hx.1, hx.2])
  obtain ⟨ζ₂, hζ₂, hA2⟩ := sec7_diff_eq_mul_deriv (g := M (m + 1))
    (g' := M (m + 2)) (s := ζ₁) (h := (q:ℝ)) hq0
    (by
      intro x hx
      rw [hM]
      apply sec7_powMonD_hasDerivAt hR
      apply sec7_rWinWide_pos hpad
      apply hsegmem
      all_goals nlinarith [hx.1, hx.2, hζ₁.1, hζ₁.2])
  have hζ₂lo : r + ξ < ζ₂ := lt_trans hζ₁.1 hζ₂.1
  have hζ₂hi : ζ₂ < r + ξ + p + q := by
    have := hζ₂.2
    have := hζ₁.2
    linarith
  have hDD : diff1 (p:ℝ) (diff1 (q:ℝ) (M m)) (r + ξ) = (p:ℝ) * q * M (m + 2) ζ₂ := by
    have e1 : diff1 (p:ℝ) (diff1 (q:ℝ) (M m)) (r + ξ) =
        (p:ℝ) * diff1 (q:ℝ) (M (m + 1)) ζ₁ := by
      have h0 : diff1 (q:ℝ) (M m) (r + ξ + p) - diff1 (q:ℝ) (M m) (r + ξ) =
          (p:ℝ) * diff1 (q:ℝ) (M (m + 1)) ζ₁ := hA1
      simpa [diff1] using h0
    have e2 : diff1 (q:ℝ) (M (m + 1)) ζ₁ = (q:ℝ) * M (m + 2) ζ₂ := by
      have h0 : M (m + 1) (ζ₁ + q) - M (m + 1) ζ₁ = (q:ℝ) * M (m + 2) ζ₂ := hA2
      simpa [diff1] using h0
    rw [e1, e2]; ring
  -- the second-order monomial drift from ζ₂ back to r
  have hMderiv : ∀ x : ℝ, |x - r| ≤ 2 * hSv → HasDerivAt (M (m + 2)) (M (m + 3) x) x := by
    intro x hx
    rw [hM]
    exact sec7_powMonD_hasDerivAt hR _ _ (m + 2) (sec7_rWinWide_pos hpad (hball x hx))
  have hdrift : |M (m + 2) ζ₂ - M (m + 2) r| ≤ B * (2 * hSv) := by
    rcases le_total r ζ₂ with hc | hc
    · have hin : ∀ x ∈ Icc r ζ₂, |x - r| ≤ 2 * hSv := by
        intro x hx
        rw [abs_of_nonneg (by linarith [hx.1])]
        have := hx.2
        nlinarith
      have := sec7_abs_sub_le_of_deriv (g := M (m + 2)) (g' := M (m + 3))
        (a := r) (b := ζ₂) hc (fun x hx => hMderiv x (hin x hx))
        (fun x hx => hMbd x (hball x (hin x hx)))
      calc |M (m + 2) ζ₂ - M (m + 2) r| ≤ B * (ζ₂ - r) := this
        _ ≤ B * (2 * hSv) := by
            apply mul_le_mul_of_nonneg_left _ hBnn
            nlinarith
    · have hin : ∀ x ∈ Icc ζ₂ r, |x - r| ≤ 2 * hSv := by
        intro x hx
        rw [abs_of_nonpos (by linarith [hx.2])]
        have := hx.1
        nlinarith
      have := sec7_abs_sub_le_of_deriv (g := M (m + 2)) (g' := M (m + 3))
        (a := ζ₂) (b := r) hc (fun x hx => hMderiv x (hin x hx))
        (fun x hx => hMbd x (hball x (hin x hx)))
      calc |M (m + 2) ζ₂ - M (m + 2) r| = |M (m + 2) r - M (m + 2) ζ₂| := abs_sub_comm _ _
        _ ≤ B * (r - ζ₂) := this
        _ ≤ B * (2 * hSv) := by
            apply mul_le_mul_of_nonneg_left _ hBnn
            nlinarith
  have hmon : |diff1 (p:ℝ) (diff1 (q:ℝ) (M m)) (r + ξ) - (p:ℝ) * q * M (m + 2) r| ≤
      (p:ℝ) * q * (B * (2 * hSv)) := by
    rw [hDD]
    have h0 : (p:ℝ) * q * M (m + 2) ζ₂ - (p:ℝ) * q * M (m + 2) r =
        (p:ℝ) * q * (M (m + 2) ζ₂ - M (m + 2) r) := by ring
    rw [h0, abs_mul, abs_of_pos (mul_pos hp0 hq0)]
    exact mul_le_mul_of_nonneg_left hdrift (mul_pos hp0 hq0).le
  -- assemble
  have hsplit : |G m r| ≤ C * q * p + (p:ℝ) * q * (B * (2 * hSv)) := by
    have h1 : |G m r| ≤ |diff1 (p:ℝ) (diff1 (q:ℝ) (RE.e₂D m)) (r + ξ)| +
        |diff1 (p:ℝ) (diff1 (q:ℝ) (M m)) (r + ξ) - (p:ℝ) * q * M (m + 2) r| := by
      simp only [hG]
      exact abs_add_le _ _
    linarith [hepart, hmon]
  refine le_trans hsplit ?_
  -- numerics
  have haprod : |sec7_aprod (3/4) (m + 3)| ≤ 8 := by
    interval_cases m <;> norm_num [sec7_aprod]
  have hpowle : ((2:ℝ) * sec7_cWin) ^ (m + 3) ≤ (2 * sec7_cWin) ^ 6 :=
    pow_le_pow_right₀ (by norm_num [sec7_cWin]) (by omega)
  have hc : |RE.c₂| ≤ 4 := RE.c₂_hi
  have hcoef : 2 * (|RE.c₂| * |sec7_aprod (3/4) (m + 3)| * (2 * sec7_cWin) ^ (m + 3)) ≤
      sec7_cExp3Lead := by
    have p1 : (0:ℝ) ≤ |RE.c₂| := abs_nonneg _
    have p2 : (0:ℝ) ≤ |sec7_aprod (3/4) (m + 3)| := abs_nonneg _
    have p3 : (0:ℝ) ≤ ((2:ℝ) * sec7_cWin) ^ (m + 3) := by positivity
    have h32 : |RE.c₂| * |sec7_aprod (3/4) (m + 3)| ≤ 32 := by nlinarith
    have h1 : |RE.c₂| * |sec7_aprod (3/4) (m + 3)| * (2 * sec7_cWin) ^ (m + 3) ≤
        32 * (2 * sec7_cWin) ^ 6 :=
      le_trans (mul_le_mul_of_nonneg_right h32 p3)
        (mul_le_mul_of_nonneg_left hpowle (by norm_num))
    have h2 : (0:ℝ) ≤ 32 * (2 * sec7_cWin) ^ 6 := by positivity
    calc 2 * (|RE.c₂| * |sec7_aprod (3/4) (m + 3)| * (2 * sec7_cWin) ^ (m + 3)) ≤
        2 * (32 * (2 * sec7_cWin) ^ 6) := by linarith
      _ ≤ sec7_cExp3Lead := by norm_num [sec7_cWin, sec7_cExp3Lead]
  have hkey1 : C * q * p ≤
      sec7_cExp3Lead * ((p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S) / S.R ^ m := by
    have hIn : sec7_cExpIn ≤ sec7_cExp3Lead := by norm_num [sec7_cExpIn, sec7_cExp3Lead]
    have hmono : (0:ℝ) ≤ (p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S / S.R ^ m := by
      positivity
    calc C * q * p
        = sec7_cExpIn * ((p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S / S.R ^ m) := by
          rw [hC, pow_add]
          field_simp
          try ring
      _ ≤ sec7_cExp3Lead * ((p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S / S.R ^ m) :=
          mul_le_mul_of_nonneg_right hIn hmono
      _ = sec7_cExp3Lead * ((p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S) / S.R ^ m := by
          ring
  have hkey2 : (p:ℝ) * q * (B * (2 * hSv)) ≤
      sec7_cExp3Lead * ((p:ℝ) * q * hSv * S.T₂ / S.R ^ 3) / S.R ^ m := by
    have hmono : (0:ℝ) ≤ (p:ℝ) * q * hSv * S.T₂ / S.R ^ (m + 3) := by positivity
    calc (p:ℝ) * q * (B * (2 * hSv))
        = 2 * (|RE.c₂| * |sec7_aprod (3/4) (m + 3)| * (2 * sec7_cWin) ^ (m + 3)) *
            ((p:ℝ) * q * hSv * S.T₂ / S.R ^ (m + 3)) := by rw [hB]; ring
      _ ≤ sec7_cExp3Lead * ((p:ℝ) * q * hSv * S.T₂ / S.R ^ (m + 3)) :=
          mul_le_mul_of_nonneg_right hcoef hmono
      _ = sec7_cExp3Lead * ((p:ℝ) * q * hSv * S.T₂ / S.R ^ 3) / S.R ^ m := by
          rw [pow_add]
          field_simp
  calc C * q * p + (p:ℝ) * q * (B * (2 * hSv))
      ≤ sec7_cExp3Lead * ((p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S) / S.R ^ m +
        sec7_cExp3Lead * ((p:ℝ) * q * hSv * S.T₂ / S.R ^ 3) / S.R ^ m := by
        linarith [hkey1, hkey2]
    _ = sec7_cExp3Lead * ((p:ℝ) * q * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
        (p:ℝ) * q * hSv * S.T₂ / S.R ^ 3) / S.R ^ m := by ring
end Sec7RaExpData

end Squarefree
