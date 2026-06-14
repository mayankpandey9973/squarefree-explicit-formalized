import Squarefree.Bracket.Sec7ErrPieces

/-!
# §7 phase differentiability

Shared regularity layer for the phase `sec7_Phi`: the phase is represented by a
grade-`0,1,2` derivative jet on the open mid-window, and the same mechanism identifies the
principal and error jets.  Consumers use the `iteratedDeriv` lemmas on the count window.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

section PhiDeriv

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a}
  {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}

private noncomputable def sec7Phi_A
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) : ℕ → ℝ → ℝ := fun k t =>
  ME.f1C k (t + sec7_hSum h₁ h₂ h₃)

private noncomputable def sec7Phi_Q
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃) (h : ℤ) : ℕ → ℝ → ℝ := fun k t =>
  diff1 (h : ℝ) (ME.f1C k) (t + sec7_hSum h₁ h₂ h₃ - (h : ℝ))

/-- The grade-`m` Leibniz jet of the §7 phase `Φ`.  At grade `0` this is `sec7_Phi`;
grades `1,2` are the derivatives produced by the wide-window chains. -/
noncomputable def sec7_PhiJet
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℕ → ℝ → ℝ := fun k t =>
  diff3 (h₁ : ℝ) h₂ h₃ (ME.f3C k) t
    + sec7_leib (sec7Phi_A ME) (sec7E_gB ME ρ₀) k t
    + sec7_leib (sec7Phi_Q ME h₁)
        (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁ : ℝ) - u₁)) k t
    + sec7_leib (sec7Phi_Q ME h₂)
        (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂ : ℝ) - u₂)) k t
    + sec7_leib (sec7Phi_Q ME h₃)
        (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃ : ℝ) - u₃)) k t

/-- The explicit derivative jet of the eq-(7.5) principal part. -/
noncomputable def sec7_principalJet
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℕ → ℝ → ℝ := fun k t =>
  sec7_powMonD S.R (ME.c₁ * (ρ₀ : ℝ) * S.T₁) (-(1 : ℝ)) k t
    + sec7_powMonD S.R (ME.Bcoef ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) (-(2 : ℝ)) k t
    + sec7_powMonD S.R
        (ME.Cstar * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13 : ℝ) / 4) k t

/-- The derivative jet of `Err := Φ - principal`. -/
noncomputable def sec7_ErrJet
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) : ℕ → ℝ → ℝ := fun k t =>
  sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k t
    - sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k t

private theorem sec7Phi_A_chain
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    ∀ k < 2, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7Phi_A ME k) (sec7Phi_A ME (k + 1) x) x := by
  intro k hk x hx
  have hSv3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  exact sec7E_shift_chain ME.f1C_deriv hshift hk hx
    (by rw [abs_of_nonneg (by linarith)]; linarith)

private theorem sec7Phi_Q_chain
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {h : ℤ} (hh : 1 ≤ h) (hhle : (h : ℝ) ≤ sec7_hSum h₁ h₂ h₃) :
    ∀ k < 2, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7Phi_Q ME h k) (sec7Phi_Q ME h (k + 1) x) x := by
  intro k hk x hx
  have hSv3 : (3 : ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hv1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have h1' : HasDerivAt
      (fun t => diff1 (h : ℝ) (ME.f1C k) (t + (sec7_hSum h₁ h₂ h₃ - (h : ℝ))))
      (diff1 (h : ℝ) (ME.f1C (k + 1)) (x + (sec7_hSum h₁ h₂ h₃ - (h : ℝ)))) x :=
    sec7E_d1shift_chain ME.f1C_deriv hshift hk hx
      (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [show sec7_hSum h₁ h₂ h₃ - (h : ℝ) + h =
            sec7_hSum h₁ h₂ h₃ from by ring, abs_of_nonneg (by linarith)]; linarith)
  have hfun :
      (fun t => diff1 (h : ℝ) (ME.f1C k) (t + sec7_hSum h₁ h₂ h₃ - (h : ℝ))) =
        fun t => diff1 (h : ℝ) (ME.f1C k)
          (t + (sec7_hSum h₁ h₂ h₃ - (h : ℝ))) := by
    funext t
    congr 1
    ring
  have hval :
      diff1 (h : ℝ) (ME.f1C (k + 1)) (x + sec7_hSum h₁ h₂ h₃ - (h : ℝ)) =
        diff1 (h : ℝ) (ME.f1C (k + 1)) (x + (sec7_hSum h₁ h₂ h₃ - (h : ℝ))) := by
    congr 1
    ring
  change HasDerivAt (fun t => diff1 (h : ℝ) (ME.f1C k)
      (t + sec7_hSum h₁ h₂ h₃ - (h : ℝ)))
    (diff1 (h : ℝ) (ME.f1C (k + 1)) (x + sec7_hSum h₁ h₂ h₃ - (h : ℝ))) x
  rw [hfun, hval]
  exact h1'

/-- Grade-0 identity for the phase jet. -/
theorem sec7_PhiJet_zero
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) (r : ℝ) :
    sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r =
      sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 0 r := by
  simp only [sec7_PhiJet, sec7Phi_A, sec7Phi_Q, sec7_Phi, sec7_leib_zero,
    sec7E_gB, sec7E_gK, sec7_constF_zero]
  rw [show Ph.f1D j 0 = ME.f1C 0 from (funext ME.f1C_zero).symm,
    show Ph.f2D 0 = ME.f2C 0 from (funext ME.f2C_zero).symm,
    show Ph.f3D j 0 = ME.f3C 0 from (funext ME.f3C_zero).symm]
  ring

/-- Grade-0 identity for the principal-part jet. -/
theorem sec7_principalJet_zero
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) (r : ℝ) :
    ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r =
      sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 0 r := by
  simp only [sec7_principalJet, Sec7MonExp.principal, sec7_powMonD_zero, sec7_powMon]

/-- Grade-0 identity for the error jet. -/
theorem sec7_ErrJet_zero
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) (r : ℝ) :
    ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r =
      sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 0 r := by
  simp only [sec7_ErrJet, Sec7MonExp.Err]
  rw [sec7_PhiJet_zero ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r,
    sec7_principalJet_zero ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ r]

/-- The phase jet is a derivative chain through order two on the open mid-window. -/
theorem sec7_PhiJet_chain
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ k < 2, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k)
        (sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (k + 1) x) x := by
  have a1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hh₁
  have a2 : (1 : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hh₂
  have a3 : (1 : ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hh₃
  have hle₁ : (h₁ : ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₁ : ℝ) ≤ (h₁ : ℝ) + h₂ + h₃
    linarith
  have hle₂ : (h₂ : ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₂ : ℝ) ≤ (h₁ : ℝ) + h₂ + h₃
    linarith
  have hle₃ : (h₃ : ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₃ : ℝ) ≤ (h₁ : ℝ) + h₂ + h₃
    linarith
  intro k hk x hx
  have c1 := sec7E_diff3_chain ME.f3C_deriv hh₁ hh₂ hh₃ hshift hk hx
  have c2 := sec7_leib_deriv (sec7Phi_A_chain ME hh₁ hh₂ hh₃ hshift)
    (sec7E_gB_chain ME hh₁ hh₂ hh₃ hshift ρ₀) k hk x hx
  have c3 := sec7_leib_deriv (sec7Phi_Q_chain ME hh₁ hh₂ hh₃ hshift hh₁ hle₁)
    (sec7E_gK_chain ME hh₁ hh₂ hh₃ hshift hh₂ hh₃ hle₂ hle₃ hξ₁ ((ρ₁ : ℝ) - u₁))
      k hk x hx
  have c4 := sec7_leib_deriv (sec7Phi_Q_chain ME hh₁ hh₂ hh₃ hshift hh₂ hle₂)
    (sec7E_gK_chain ME hh₁ hh₂ hh₃ hshift hh₁ hh₃ hle₁ hle₃ hξ₂ ((ρ₂ : ℝ) - u₂))
      k hk x hx
  have c5 := sec7_leib_deriv (sec7Phi_Q_chain ME hh₁ hh₂ hh₃ hshift hh₃ hle₃)
    (sec7E_gK_chain ME hh₁ hh₂ hh₃ hshift hh₁ hh₂ hle₁ hle₂ hξ₃ ((ρ₃ : ℝ) - u₃))
      k hk x hx
  simpa only [sec7_PhiJet] using ((((c1.add c2).add c3).add c4).add c5)

/-- The principal-part jet is a derivative chain through order two on the open mid-window. -/
theorem sec7_principalJet_chain
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ k < 2, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k)
        (sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  simp only [sec7_principalJet]
  exact ((sec7_powMonD_hasDerivAt hR _ _ k hx0).add
    (sec7_powMonD_hasDerivAt hR _ _ k hx0)).add
    (sec7_powMonD_hasDerivAt hR _ _ k hx0)

/-- The error jet is a derivative chain through order two on the open mid-window. -/
theorem sec7_ErrJet_chain
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ k < 2, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k)
        (sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (k + 1) x) x := by
  intro k hk x hx
  simpa only [sec7_ErrJet] using
    (sec7_PhiJet_chain ME hh₁ hh₂ hh₃ hξ₁ hξ₂ hξ₃ hshift
      ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k hk x hx).sub
      (sec7_principalJet_chain ME hpad ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ k hk x hx)

/-- On the count window, `iteratedDeriv m Φ` is the phase jet for `m ≤ 2`. -/
theorem sec7_Phi_iteratedDeriv_eq
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      iteratedDeriv m
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        sec7_PhiJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ m r := by
  intro m hm r hr
  exact sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W)
    (fun x _ => sec7_PhiJet_zero ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x)
    (sec7_PhiJet_chain ME hh₁ hh₂ hh₃ hξ₁ hξ₂ hξ₃ hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    m hm r (sec7_rWin_subset_mid S hW hr)

/-- On the count window, `iteratedDeriv m principal` is the principal jet for `m ≤ 2`. -/
theorem sec7_principal_iteratedDeriv_eq
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hW : 0 < W)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      iteratedDeriv m (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        sec7_principalJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ m r := by
  intro m hm r hr
  exact sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W)
    (fun x _ => sec7_principalJet_zero ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x)
    (sec7_principalJet_chain ME hpad ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    m hm r (sec7_rWin_subset_mid S hW hr)

/-- On the count window, `iteratedDeriv m Err` is the error jet for `m ≤ 2`. -/
theorem sec7_Err_iteratedDeriv_eq
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        sec7_ErrJet ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ m r := by
  intro m hm r hr
  exact sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W)
    (fun x _ => sec7_ErrJet_zero ME ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x)
    (sec7_ErrJet_chain ME hh₁ hh₂ hh₃ hξ₁ hξ₂ hξ₃ hpad hshift ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃)
    m hm r (sec7_rWin_subset_mid S hW hr)

/-- The reusable split `Φ^(m) = principal^(m) + Err^(m)` on the count window, for `m ≤ 2`. -/
theorem sec7_Phi_iteratedDeriv_eq_principal_add_Err
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      iteratedDeriv m
          (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
        iteratedDeriv m (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r
          + iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r := by
  intro m hm r hr
  rw [sec7_Phi_iteratedDeriv_eq ME hh₁ hh₂ hh₃ hξ₁ hξ₂ hξ₃ hW hshift
      ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ m hm r hr,
    sec7_principal_iteratedDeriv_eq ME hW hpad ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ m hm r hr,
    sec7_Err_iteratedDeriv_eq ME hh₁ hh₂ hh₃ hξ₁ hξ₂ hξ₃ hW hpad hshift
      ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ m hm r hr]
  simp only [sec7_ErrJet]
  ring

/-- The second-derivative split needed by N12b/N13/N17. -/
theorem sec7_Phi_iteratedDeriv_two_eq_principal_add_Err
    (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (hW : 0 < W)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) {r : ℝ} (hr : r ∈ sec7_rWin S W) :
    iteratedDeriv 2
        (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r =
      iteratedDeriv 2 (ME.principal ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r
        + iteratedDeriv 2 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r :=
  sec7_Phi_iteratedDeriv_eq_principal_add_Err ME hh₁ hh₂ hh₃ hξ₁ hξ₂ hξ₃ hW hpad hshift
    ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ 2 (by norm_num) r hr

end PhiDeriv

end Squarefree
