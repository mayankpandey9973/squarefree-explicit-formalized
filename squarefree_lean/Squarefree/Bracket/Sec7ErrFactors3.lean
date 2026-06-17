import Squarefree.Bracket.Sec7ErrFactors
import Squarefree.Bracket.Sec7ErrCaps3

/-!
# §7 N11 order-3 factor bounds (Φ″ endgame)

The `m = 3` siblings of the value bounds in `Sec7ErrFactors.lean`: the same chain
identification + `Sec7MonExp` graded fields, but graded `k ≤ 3` and consuming the
`_exp3` fields (LEADING families `f1/d1f1/B` on `sec7_cExp3Lead`, RESIDUAL families
`B03/d3f3` on `sec7_cExp3`), and the order-3 caps `sec7E_cap*_3`.  Only the order-3 master
family `sec7_err_deriv_bound_m3` (Sec7ErrBound3) consumes these.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

section Factors

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a}
  {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}

variable (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)

/-- `cExp3·relErr ≤ 1` from the strip smallness. -/
theorem sec7E_cExp3_rel (hrel : sec7_relErr P S * 10 ^ 143 ≤ 1) :
    sec7_cExp3 * sec7_relErr P S ≤ 1 := by
  have h0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hc : sec7_cExp3 ≤ (10 : ℝ) ^ 143 := by norm_num [sec7_cExp3]
  calc sec7_cExp3 * sec7_relErr P S ≤ 10 ^ 143 * sec7_relErr P S :=
        mul_le_mul_of_nonneg_right hc h0
    _ = sec7_relErr P S * 10 ^ 143 := by ring
    _ ≤ 1 := hrel

/-- `cExp3Lead·relErr ≤ 1` from the strip smallness. -/
theorem sec7E_cExp3Lead_rel (hrel : sec7_relErr P S * 10 ^ 143 ≤ 1) :
    sec7_cExp3Lead * sec7_relErr P S ≤ 1 := by
  have h0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hc : sec7_cExp3Lead ≤ (10 : ℝ) ^ 143 := by norm_num [sec7_cExp3Lead]
  calc sec7_cExp3Lead * sec7_relErr P S ≤ 10 ^ 143 * sec7_relErr P S :=
        mul_le_mul_of_nonneg_right hc h0
    _ = sec7_relErr P S * 10 ^ 143 := by ring
    _ ≤ 1 := hrel

section Chains

variable (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
  (hW : 0 < W)
  (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
  (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))

include hh₁ hh₂ hh₃ hW hpad hshift

/-- `cExp3·h_Σ ≤ R` from the envelope smallness. -/
theorem sec7E_cExp3_hS (hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R) :
    sec7_cExp3 * sec7_hSum h₁ h₂ h₃ ≤ S.R := by
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  calc sec7_cExp3 * sec7_hSum h₁ h₂ h₃ ≤ 10 ^ 149 * sec7_hSum h₁ h₂ h₃ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        norm_num [sec7_cExp3]
    _ = sec7_hSum h₁ h₂ h₃ * 10 ^ 149 := by ring
    _ ≤ S.R := hSR

/-- `cExp3Lead·h_Σ ≤ R` from the envelope smallness. -/
theorem sec7E_cExp3Lead_hS (hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R) :
    sec7_cExp3Lead * sec7_hSum h₁ h₂ h₃ ≤ S.R := by
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  calc sec7_cExp3Lead * sec7_hSum h₁ h₂ h₃ ≤ 10 ^ 149 * sec7_hSum h₁ h₂ h₃ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        norm_num [sec7_cExp3Lead]
    _ = sec7_hSum h₁ h₂ h₃ * 10 ^ 149 := by ring
    _ ≤ S.R := hSR

/-! ## Order-3 value bounds of the error families -/

theorem sec7E_eA_bound3 : ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
    |sec7E_eA ME k r| ≤
      sec7_cExp3Lead * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
        S.T₁ * sec7_relErrF P S) / S.R ^ k := by
  intro k hk r hr
  have h0 : ∀ x ∈ sec7_rWinMid S W,
      (fun t => Ph.f1D j 0 (t + sec7_hSum h₁ h₂ h₃) -
        (ME.c₁ * S.T₁ * (t / S.R) ^ (-(1:ℝ)) -
          ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R) * (t / S.R) ^ (-(2:ℝ)))) x =
      sec7E_eA ME 0 x := by
    intro x _
    simp only [sec7E_eA, sec7E_M1, sec7_powMonD_zero, sec7_powMon]
    rw [show Ph.f1D j 0 (x + sec7_hSum h₁ h₂ h₃) =
      ME.f1C 0 (x + sec7_hSum h₁ h₂ h₃) from (ME.f1C_zero _).symm]
    ring
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0
    (sec7E_eA_chain ME hh₁ hh₂ hh₃ hpad hshift) k (by omega) r (sec7_rWin_subset_mid S hW hr)
  rw [← hid]
  exact ME.f1_exp3 k hk r hr

theorem sec7E_eQ_bound3 {h : ℤ} (hh : 1 ≤ h) (hhle : (h:ℝ) ≤ sec7_hSum h₁ h₂ h₃)
    (hfield : ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff1 (h : ℝ) (Ph.f1D j 0) (t + sec7_hSum h₁ h₂ h₃ - h) -
            (-(ME.c₁ * h * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) r| ≤
        sec7_cExp3Lead * ((h : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
          (h : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ m) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_eQ ME h k r| ≤
        sec7_cExp3Lead * ((h : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
          (h : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S) / S.R ^ k := by
  intro k hk r hr
  have h0 : ∀ x ∈ sec7_rWinMid S W,
      (fun t => diff1 (h : ℝ) (Ph.f1D j 0) (t + sec7_hSum h₁ h₂ h₃ - h) -
        (-(ME.c₁ * h * (S.T₁ / S.R)) * (t / S.R) ^ (-(2:ℝ)))) x =
      sec7E_eQ ME h 0 x := by
    intro x _
    simp only [sec7E_eQ, sec7E_N, sec7_powMonD_zero, sec7_powMon]
    rw [show Ph.f1D j 0 = ME.f1C 0 from (funext ME.f1C_zero).symm]
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0
    (sec7E_eQ_chain ME hh₁ hh₂ hh₃ hpad hshift hh hhle) k (by omega) r
    (sec7_rWin_subset_mid S hW hr)
  rw [← hid]
  exact hfield k hk r hr

theorem sec7E_eK_bound3 {g h : ℤ} (hg : 1 ≤ g) (hh : 1 ≤ h)
    (hgle : (g:ℝ) ≤ sec7_hSum h₁ h₂ h₃) (hhle : (h:ℝ) ≤ sec7_hSum h₁ h₂ h₃)
    {ξ : ℝ} (hξ : |ξ| ≤ sec7_hSum h₁ h₂ h₃)
    (hfield : ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff1 (g : ℝ) (diff1 (h : ℝ) (Ph.f2D 0)) (t + ξ) -
            (-(3/16) * ME.c₂ * g * h * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) r| ≤
        sec7_cExp3Lead * ((g : ℝ) * h * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
          (g : ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ m) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_eK ME g h ξ k r| ≤
        sec7_cExp3Lead * ((g : ℝ) * h * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
          (g : ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ k := by
  intro k hk r hr
  have h0 : ∀ x ∈ sec7_rWinMid S W,
      (fun t => diff1 (g : ℝ) (diff1 (h : ℝ) (Ph.f2D 0)) (t + ξ) -
        (-(3/16) * ME.c₂ * g * h * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) x =
      sec7E_eK ME g h ξ 0 x := by
    intro x _
    simp only [sec7E_eK, sec7E_L, sec7_powMonD_zero, sec7_powMon]
    rw [show Ph.f2D 0 = ME.f2C 0 from (funext ME.f2C_zero).symm]
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0
    (sec7E_eK_chain ME hh₁ hh₂ hh₃ hpad hshift hg hh hgle hhle hξ) k (by omega) r
    (sec7_rWin_subset_mid S hW hr)
  rw [← hid]
  exact hfield k hk r hr

theorem sec7E_eB0_bound3 : ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
    |sec7E_eB0 ME k r| ≤
      sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
        sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) / S.R ^ k := by
  intro k hk r hr
  have h0 : ∀ x ∈ sec7_rWinMid S W,
      (fun t => diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) t -
        (15/64) * ME.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) *
          (t / S.R) ^ (-(9:ℝ)/4)) x = sec7E_eB0 ME 0 x := by
    intro x _
    simp only [sec7E_eB0, sec7E_M0, sec7_powMonD_zero, sec7_powMon]
    rw [show Ph.f2D 0 = ME.f2C 0 from (funext ME.f2C_zero).symm]
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0
    (sec7E_eB0_chain ME hh₁ hh₂ hh₃ hpad hshift) k (by omega) r (sec7_rWin_subset_mid S hW hr)
  rw [← hid]
  exact ME.B03_exp3 k hk r hr

theorem sec7E_eP3_bound3 : ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
    |sec7E_eP3 ME k r| ≤
      sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
        sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₃ / S.R ^ 4) / S.R ^ k := by
  intro k hk r hr
  have h0 : ∀ x ∈ sec7_rWinMid S W,
      (fun t => diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) t -
        (-(45/64) * ME.c₃ * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) *
          (t / S.R) ^ (-(13:ℝ)/4))) x = sec7E_eP3 ME 0 x := by
    intro x _
    simp only [sec7E_eP3, sec7E_M3, sec7_powMonD_zero, sec7_powMon]
    rw [show Ph.f3D j 0 = ME.f3C 0 from (funext ME.f3C_zero).symm]
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0
    (sec7E_eP3_chain ME hh₁ hh₂ hh₃ hpad hshift) k (by omega) r (sec7_rWin_subset_mid S hW hr)
  rw [← hid]
  exact ME.d3f3_exp3 k hk r hr

/-! ## Order-3 value bounds of the monomial factors -/

omit hshift in
theorem sec7E_M1_bound3 (hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_M1 ME k r| ≤ 10 ^ 15 * S.T₁ / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT1 := sec7_T₁_pos S
  have hwide := sec7E_rWin_subset_wide (S := S) hW hr
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have b1 := sec7_powMonD_val_bound (S := S) (c := ME.c₁ * S.T₁)
    (by linarith : (-(1:ℝ)) - (k:ℝ) ≤ 0) (sec7E_cap1_3 k hk) hpad hwide
  have b2 := sec7_powMonD_val_bound (S := S)
    (c := -(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)))
    (by linarith : (-(2:ℝ)) - (k:ℝ) ≤ 0) (sec7E_cap2_3 k hk) hpad hwide
  have hc1 : |ME.c₁| ≤ 4 := ME.c₁_window.2
  have hc10 : 0 ≤ |ME.c₁| := abs_nonneg _
  have hTR : 0 < S.T₁ / S.R := div_pos hT1 hR
  have habs1 : |ME.c₁ * S.T₁| ≤ 4 * S.T₁ := by
    rw [abs_mul, abs_of_pos hT1]
    nlinarith
  have habs2 : |-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))| ≤
      4 * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃),
      abs_of_pos hTR]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1
      (by linarith : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃)) hTR.le]
  have hsmall : 4 * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) * 10 ^ 18 ≤ S.T₁ := by
    rw [show 4 * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) * 10 ^ 18
        = 4 * 10 ^ 18 * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R from by ring,
      div_le_iff₀ hR]
    have h1 : (4 * 10 ^ 18 : ℝ) * sec7_hSum h₁ h₂ h₃ ≤ S.R := by
      calc (4 * 10 ^ 18 : ℝ) * sec7_hSum h₁ h₂ h₃
          ≤ 10 ^ 149 * sec7_hSum h₁ h₂ h₃ :=
            mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
        _ = sec7_hSum h₁ h₂ h₃ * 10 ^ 149 := by ring
        _ ≤ S.R := hSR
    nlinarith
  have hnum : |ME.c₁ * S.T₁| * 10 ^ 14 +
      |-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))| * 10 ^ 18 ≤ 10 ^ 15 * S.T₁ := by
    have p1 : |ME.c₁ * S.T₁| * 10 ^ 14 ≤ 4 * S.T₁ * 10 ^ 14 :=
      mul_le_mul_of_nonneg_right habs1 (by norm_num)
    have p2 : |-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))| * 10 ^ 18 ≤
        4 * (sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R)) * 10 ^ 18 :=
      mul_le_mul_of_nonneg_right habs2 (by norm_num)
    nlinarith
  calc |sec7E_M1 ME k r|
      ≤ |sec7_powMonD S.R (ME.c₁ * S.T₁) (-(1:ℝ)) k r| +
        |sec7_powMonD S.R (-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))) (-(2:ℝ)) k r| := by
        simp only [sec7E_M1]
        exact abs_add_le _ _
    _ ≤ |ME.c₁ * S.T₁| * 10 ^ 14 / S.R ^ k +
        |-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))| * 10 ^ 18 / S.R ^ k :=
        add_le_add b1 b2
    _ = (|ME.c₁ * S.T₁| * 10 ^ 14 +
        |-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))| * 10 ^ 18) / S.R ^ k :=
        (add_div _ _ _).symm
    _ ≤ 10 ^ 15 * S.T₁ / S.R ^ k := by gcongr

omit hh₁ hh₂ hh₃ hshift in
theorem sec7E_N_bound3 {h : ℤ} (hh : 1 ≤ h) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_N ME h k r| ≤ 4 * 10 ^ 18 * ((h:ℝ) * (S.T₁ / S.R)) / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT1 := sec7_T₁_pos S
  have hwide := sec7E_rWin_subset_wide (S := S) hW hr
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hv1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hTR : 0 < S.T₁ / S.R := div_pos hT1 hR
  have b := sec7_powMonD_val_bound (S := S) (c := -(ME.c₁ * (h:ℝ) * (S.T₁ / S.R)))
    (by linarith : (-(2:ℝ)) - (k:ℝ) ≤ 0) (sec7E_cap2_3 k hk) hpad hwide
  have hc1 : |ME.c₁| ≤ 4 := ME.c₁_window.2
  have hc10 : 0 ≤ |ME.c₁| := abs_nonneg _
  have habs : |-(ME.c₁ * (h:ℝ) * (S.T₁ / S.R))| ≤ 4 * ((h:ℝ) * (S.T₁ / S.R)) := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (h:ℝ)),
      abs_of_pos hTR]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1
      (by linarith : (0:ℝ) ≤ (h:ℝ))) hTR.le]
  calc |sec7E_N ME h k r| = |sec7_powMonD S.R (-(ME.c₁ * (h:ℝ) * (S.T₁ / S.R)))
        (-(2:ℝ)) k r| := by rw [sec7E_N]
    _ ≤ |-(ME.c₁ * (h:ℝ) * (S.T₁ / S.R))| * 10 ^ 18 / S.R ^ k := b
    _ ≤ 4 * ((h:ℝ) * (S.T₁ / S.R)) * 10 ^ 18 / S.R ^ k := by gcongr
    _ = 4 * 10 ^ 18 * ((h:ℝ) * (S.T₁ / S.R)) / S.R ^ k := by ring_nf

omit hshift in
theorem sec7E_M0_bound3 :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_M0 ME k r| ≤
        10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT2 := sec7_T₂_pos S
  have hwide := sec7E_rWin_subset_wide (S := S) hW hr
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hPv : (1:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
    have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
    have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
    have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
    unfold sec7_Pprod
    have h12 : (1:ℝ) ≤ (h₁:ℝ) * h₂ := by nlinarith
    nlinarith [h12, a3]
  have hTR : 0 < S.T₂ / S.R ^ 3 := by positivity
  have b := sec7_powMonD_val_bound (S := S)
    (c := (15/64) * ME.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3))
    (by linarith : (-(9:ℝ)/4) - (k:ℝ) ≤ 0) (sec7E_cap9_3 k hk) hpad hwide
  have hc2 : |ME.c₂| ≤ 4 := ME.c₂_window.2
  have hc20 : 0 ≤ |ME.c₂| := abs_nonneg _
  have habs : |(15/64) * ME.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)| ≤
      (15/16) * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) := by
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃), abs_of_pos hTR,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ (15:ℝ)/64)]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2
      (by linarith : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃)) hTR.le]
  calc |sec7E_M0 ME k r| = |sec7_powMonD S.R
        ((15/64) * ME.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) (-(9:ℝ)/4) k r| := by
        rw [sec7E_M0]
    _ ≤ |(15/64) * ME.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)| *
        (10 ^ 19) / S.R ^ k := b
    _ ≤ (15/16) * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) * (10 ^ 19) / S.R ^ k := by
        gcongr
    _ ≤ 10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) / S.R ^ k := by
        gcongr ?_ / _
        nlinarith [mul_pos (lt_of_lt_of_le one_pos hPv) hTR,
          mul_nonneg (by linarith : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃) hTR.le]

omit hh₁ hh₂ hh₃ hshift in
theorem sec7E_L_bound3 {g h : ℤ} (hg : 1 ≤ g) (hh : 1 ≤ h) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_L ME g h k r| ≤
        2 * 10 ^ 15 * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT2 := sec7_T₂_pos S
  have hwide := sec7E_rWin_subset_wide (S := S) hW hr
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hv1 : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hv2 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hTR : 0 < S.T₂ / S.R ^ 2 := by positivity
  have b := sec7_powMonD_val_bound (S := S)
    (c := -(3/16) * ME.c₂ * (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2))
    (by linarith : (-(5:ℝ)/4) - (k:ℝ) ≤ 0) (sec7E_cap5_3 k hk) hpad hwide
  have hc2 : |ME.c₂| ≤ 4 := ME.c₂_window.2
  have hc20 : 0 ≤ |ME.c₂| := abs_nonneg _
  have habs : |-(3/16) * ME.c₂ * (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)| ≤
      (3/4) * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ (g:ℝ)),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ (h:ℝ)), abs_of_pos hTR,
      show |(-((3:ℝ)/16))| = (3:ℝ)/16 from by norm_num]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc2 (by linarith : (0:ℝ) ≤ (g:ℝ)))
      (by linarith : (0:ℝ) ≤ (h:ℝ))) hTR.le]
  calc |sec7E_L ME g h k r| = |sec7_powMonD S.R
        (-(3/16) * ME.c₂ * (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) (-(5:ℝ)/4) k r| := by
        rw [sec7E_L]
    _ ≤ |-(3/16) * ME.c₂ * (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)| *
        (2 * 10 ^ 15) / S.R ^ k := b
    _ ≤ (3/4) * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) * (2 * 10 ^ 15) / S.R ^ k := by gcongr
    _ ≤ 2 * 10 ^ 15 * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) / S.R ^ k := by
        gcongr ?_ / _
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (g:ℝ))
          (by linarith : (0:ℝ) ≤ (h:ℝ))) hTR.le]

omit hshift in
theorem sec7E_T6_bound3 :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_T6 ME k r| ≤
        8 * 10 ^ 26 * (sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
          (S.T₁ * S.T₂ / S.R ^ 4)) / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT1 := sec7_T₁_pos S
  have hT2 := sec7_T₂_pos S
  have hwide := sec7E_rWin_subset_wide (S := S) hW hr
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hPv : (1:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
    have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
    have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
    have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
    unfold sec7_Pprod
    have h12 : (1:ℝ) ≤ (h₁:ℝ) * h₂ := by nlinarith
    nlinarith [h12, a3]
  have hTR : 0 < S.T₁ * S.T₂ / S.R ^ 4 := by positivity
  have b := sec7_powMonD_val_bound (S := S)
    (c := -((15/64) * ME.c₁ * ME.c₂ * sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
      (S.T₁ * S.T₂ / S.R ^ 4)))
    (by linarith : (-(17:ℝ)/4) - (k:ℝ) ≤ 0) (sec7E_cap17_3 k hk) hpad hwide
  have hc1 : |ME.c₁| ≤ 4 := ME.c₁_window.2
  have hc2 : |ME.c₂| ≤ 4 := ME.c₂_window.2
  have hc10 : 0 ≤ |ME.c₁| := abs_nonneg _
  have hc20 : 0 ≤ |ME.c₂| := abs_nonneg _
  have habs : |-((15/64) * ME.c₁ * ME.c₂ * sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
      (S.T₁ * S.T₂ / S.R ^ 4))| ≤
      4 * (sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ * (S.T₁ * S.T₂ / S.R ^ 4)) := by
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃), abs_of_pos hTR,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ (15:ℝ)/64)]
    have hq : |ME.c₁| * |ME.c₂| ≤ 16 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hq (by linarith : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃))
      (by linarith : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃)) hTR.le,
      mul_nonneg (mul_nonneg
        (by linarith : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃)
        (by linarith : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃)) hTR.le]
  calc |sec7E_T6 ME k r| ≤ |-((15/64) * ME.c₁ * ME.c₂ * sec7_hSum h₁ h₂ h₃ *
        sec7_Pprod h₁ h₂ h₃ * (S.T₁ * S.T₂ / S.R ^ 4))| * (2 * 10 ^ 26) / S.R ^ k := by
        rw [sec7E_T6]
        exact b
    _ ≤ 4 * (sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ * (S.T₁ * S.T₂ / S.R ^ 4)) *
        (2 * 10 ^ 26) / S.R ^ k := by gcongr
    _ = 8 * 10 ^ 26 * (sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
        (S.T₁ * S.T₂ / S.R ^ 4)) / S.R ^ k := by ring_nf

/-! ## Order-3 composite second-factor bounds -/

theorem sec7E_gB_bound3 (hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R)
    (hcrel3 : sec7_cExp3 * sec7_relErr P S ≤ 1) {ρ₀ : ℤ}
    (hρ₀ : |(ρ₀:ℝ)| ≤ sec7_cCarry) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_gB ME ρ₀ k r| ≤
        (2 * 10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) +
          (if ρ₀ = 0 then 0 else 1) * sec7_cCarry) / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT2 := sec7_T₂_pos S
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hPv : (1:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
    have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
    have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
    have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
    unfold sec7_Pprod
    have h12 : (1:ℝ) ≤ (h₁:ℝ) * h₂ := by nlinarith
    nlinarith [h12, a3]
  have hPT : (0:ℝ) < sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) := by
    have : (0:ℝ) < S.T₂ / S.R ^ 3 := by positivity
    nlinarith
  have hcc : |(ρ₀:ℝ)| ≤ (if ρ₀ = 0 then 0 else 1) * sec7_cCarry := by
    by_cases h0 : ρ₀ = 0
    · subst h0; simp
    · rw [if_neg h0, one_mul]; exact hρ₀
  have hcb := sec7_constF_bound hcc hR k r
  have heb := sec7E_eB0_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift k hk r hr
  have hmb := sec7E_M0_bound3 ME hh₁ hh₂ hh₃ hW hpad k hk r hr
  have hcoll : sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
      sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) ≤
      2 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) := by
    have p1 : sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S) ≤
        sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) := by
      nlinarith [mul_le_mul_of_nonneg_right hcrel3 hPT.le]
    have p2 : sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) ≤
        sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) := by
      have hce := sec7E_cExp3_hS hh₁ hh₂ hh₃ hW hpad hshift hSR
      rw [show sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) =
          sec7_cExp3 * sec7_hSum h₁ h₂ h₃ * (sec7_Pprod h₁ h₂ h₃ * S.T₂) / S.R ^ 4
          from by ring,
        show sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) =
          S.R * (sec7_Pprod h₁ h₂ h₃ * S.T₂) / S.R ^ 4 from by
            rw [pow_succ]
            field_simp]
      have hPT2 : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ * S.T₂ := by nlinarith
      gcongr
    nlinarith
  have hsplit : sec7E_gB ME ρ₀ k r =
      (sec7E_eB0 ME k r + sec7E_M0 ME k r) + sec7_constF (ρ₀:ℝ) k r := by
    simp only [sec7E_gB, sec7E_eB0]
    ring
  calc |sec7E_gB ME ρ₀ k r|
      ≤ |sec7E_eB0 ME k r| + |sec7E_M0 ME k r| + |sec7_constF (ρ₀:ℝ) k r| := by
        rw [hsplit]
        exact le_trans (abs_add_le _ _)
          (by linarith [abs_add_le (sec7E_eB0 ME k r) (sec7E_M0 ME k r)])
    _ ≤ (sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
          sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) +
        10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) +
        (if ρ₀ = 0 then 0 else 1) * sec7_cCarry) / S.R ^ k := by
        rw [add_div, add_div]
        exact add_le_add (add_le_add heb hmb) hcb
    _ ≤ (2 * 10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) +
        (if ρ₀ = 0 then 0 else 1) * sec7_cCarry) / S.R ^ k := by
        gcongr (?_ : ℝ) / _
        nlinarith [hcoll, hPT]

theorem sec7E_gK_bound3 (hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R)
    (hcrel3L : sec7_cExp3Lead * sec7_relErr P S ≤ 1) {g h : ℤ} (hg : 1 ≤ g) (hh : 1 ≤ h)
    (hgle : (g:ℝ) ≤ sec7_hSum h₁ h₂ h₃) (hhle : (h:ℝ) ≤ sec7_hSum h₁ h₂ h₃)
    {ξ : ℝ} (hξ : |ξ| ≤ sec7_hSum h₁ h₂ h₃) {c : ℝ}
    (hc : |c| ≤ sec7_cFib * (1 + (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)))
    (hfield : ∀ m ≤ 3, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff1 (g : ℝ) (diff1 (h : ℝ) (Ph.f2D 0)) (t + ξ) -
            (-(3/16) * ME.c₂ * g * h * (S.T₂ / S.R ^ 2) * (t / S.R) ^ (-(5:ℝ)/4))) r| ≤
        sec7_cExp3Lead * ((g : ℝ) * h * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
          (g : ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) / S.R ^ m) :
    ∀ k ≤ 3, ∀ r ∈ sec7_rWin S W,
      |sec7E_gK ME g h ξ c k r| ≤
        (3 * 10 ^ 15 * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) / S.R ^ k := by
  intro k hk r hr
  have hR := sec7_R_pos S
  have hT2 := sec7_T₂_pos S
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hv1 : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hv2 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hgT : (0:ℝ) < (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2) := by
    have ht : (0:ℝ) < S.T₂ / S.R ^ 2 := by positivity
    exact mul_pos (mul_pos (lt_of_lt_of_le one_pos hv1) (lt_of_lt_of_le one_pos hv2)) ht
  have hcb := sec7_constF_bound hc hR k r
  have heb := sec7E_eK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hg hh hgle hhle hξ hfield k hk r hr
  have hlb := sec7E_L_bound3 ME hW hpad hg hh k hk r hr
  have hcoll : sec7_cExp3Lead * ((g:ℝ) * h * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
      (g:ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) ≤
      2 * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) := by
    have p1 : sec7_cExp3Lead * ((g:ℝ) * h * (S.T₂ / S.R ^ 2) * sec7_relErr P S) ≤
        (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hcrel3L hgT.le]
    have p2 : sec7_cExp3Lead * ((g:ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) ≤
        (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2) := by
      have hce := sec7E_cExp3Lead_hS hh₁ hh₂ hh₃ hW hpad hshift hSR
      rw [show sec7_cExp3Lead * ((g:ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) =
          sec7_cExp3Lead * sec7_hSum h₁ h₂ h₃ * ((g:ℝ) * h * S.T₂) / S.R ^ 3 from by ring,
        show (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2) =
          S.R * ((g:ℝ) * h * S.T₂) / S.R ^ 3 from by
            rw [pow_succ]
            field_simp]
      have hgT2 : (0:ℝ) ≤ (g:ℝ) * h * S.T₂ :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hT2.le
      gcongr
    nlinarith
  have hsplit : sec7E_gK ME g h ξ c k r =
      (sec7E_eK ME g h ξ k r + sec7E_L ME g h k r) + sec7_constF c k r := by
    simp only [sec7E_gK, sec7E_eK]
    ring
  calc |sec7E_gK ME g h ξ c k r|
      ≤ |sec7E_eK ME g h ξ k r| + |sec7E_L ME g h k r| + |sec7_constF c k r| := by
        rw [hsplit]
        exact le_trans (abs_add_le _ _)
          (by linarith [abs_add_le (sec7E_eK ME g h ξ k r) (sec7E_L ME g h k r)])
    _ ≤ (sec7_cExp3Lead * ((g:ℝ) * h * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
          (g:ℝ) * h * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3) +
        2 * 10 ^ 15 * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) +
        sec7_cFib * (1 + (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2))) / S.R ^ k := by
        rw [add_div, add_div]
        exact add_le_add (add_le_add heb hlb) hcb
    _ ≤ (3 * 10 ^ 15 * ((g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) / S.R ^ k := by
        gcongr (?_ : ℝ) / _
        have hFib : sec7_cFib = 10 ^ 10 := by norm_num [sec7_cFib]
        nlinarith [hcoll, hgT]

end Chains

end Factors

end Squarefree
