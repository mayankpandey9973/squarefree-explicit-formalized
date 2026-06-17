import Squarefree.Bracket.Sec7ErrFactors3

/-!
# §7 N11 — the order-3 `Err^{(3)}` bound (Φ″ endgame, two-constant split)

`sec7_err_deriv_bound_m3`: at `m = 3` and `ρ₀ = 0`,
`|Err^{(3)}(r)| ≤ cErr3Lead·errScale_LEAD/R³ + cErr3Res·errScale_RES/R³`.

The single-constant `m ≤ 2` route (`sec7_err_deriv_bound`, `sec7E_cErr = 10⁴²`) cannot be
re-pinned at order 3: the order-6 residual families `B03/d3f3` carry `sec7_cExp3 = 10³¹`,
which fails the `1/cSub`-domination ceiling.  The two-scale split charges the `cExp3Lead`
LEADING slots at `cErr3Lead = 10⁴⁴` and the residual-carrying slots at `cErr3Res = 10⁵²`.

Assembled constants (sympy-banked): LEAD `= 2.4·10³⁷ ≤ 10⁴⁴`, RES `= 8.96·10⁴⁶ ≤ 10⁵²`;
no `cExp3`-residual lands on a LEAD slot.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

/-- **N11 order-3 numeric assembly** (two-constant; ρ₀ = 0).  The ten group numerators of
`Err^{(3)}` against the LEAD slots at `10⁴⁴` and the RES slots at `10⁵²`. -/
private theorem sec7E_num_final_m3 {T1 T2 T3 R hS Pv relF rel a b c : ℝ}
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hR : 0 < R) (hhS : 3 ≤ hS) (hPv : 1 ≤ Pv)
    (hrelF : 0 ≤ relF) (hrel : 0 ≤ rel)
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (ha : a ≤ hS) (hb : b ≤ hS) (hc : c ≤ hS)
    (habc : a * b * c = Pv) (hT3 : T1 * T2 = T3)
    (hSR : hS * 10 ^ 149 ≤ R) :
    10 ^ 31 * (Pv * (T3 / R ^ 3) * relF + Pv * hS * T3 / R ^ 4)
      + 8 * ((10 ^ 26 * (hS ^ 2 * T1 / R ^ 2 + T1 * relF)) *
          (2 * 10 ^ 19 * (Pv * (T2 / R ^ 3))))
      + 8 * ((10 ^ 15 * T1) *
          (10 ^ 31 * (Pv * (T2 / R ^ 3) * rel + Pv * hS * T2 / R ^ 4)))
      + 8 * ((10 ^ 26 * (a * hS * T1 / R ^ 2 + a * (T1 / R) * relF)) *
          (3 * 10 ^ 15 * (b * c * (T2 / R ^ 2)) + 10 ^ 10))
      + 8 * ((4 * 10 ^ 18 * (a * (T1 / R))) *
          (10 ^ 26 * (b * c * (T2 / R ^ 2) * rel + b * c * hS * T2 / R ^ 3)))
      + 8 * ((10 ^ 26 * (b * hS * T1 / R ^ 2 + b * (T1 / R) * relF)) *
          (3 * 10 ^ 15 * (a * c * (T2 / R ^ 2)) + 10 ^ 10))
      + 8 * ((4 * 10 ^ 18 * (b * (T1 / R))) *
          (10 ^ 26 * (a * c * (T2 / R ^ 2) * rel + a * c * hS * T2 / R ^ 3)))
      + 8 * ((10 ^ 26 * (c * hS * T1 / R ^ 2 + c * (T1 / R) * relF)) *
          (3 * 10 ^ 15 * (a * b * (T2 / R ^ 2)) + 10 ^ 10))
      + 8 * ((4 * 10 ^ 18 * (c * (T1 / R))) *
          (10 ^ 26 * (a * b * (T2 / R ^ 2) * rel + a * b * hS * T2 / R ^ 3)))
      + 8 * 10 ^ 26 * (hS * Pv * (T1 * T2 / R ^ 4))
    ≤ 10 ^ 44 * (hS * (T1 / R) * relF + hS ^ 2 * T1 / R ^ 2)
      + 10 ^ 52 * (Pv * (T3 / R ^ 3) * relF + Pv * (T3 / R ^ 3) * rel +
          Pv * hS * (T3 / R ^ 4)) := by
  subst hT3
  subst habc
  have hhS0 : (0:ℝ) ≤ hS := by linarith
  have ha0 : (0:ℝ) ≤ a := by linarith
  have hb0 : (0:ℝ) ≤ b := by linarith
  have hc0 : (0:ℝ) ≤ c := by linarith
  have hs2ann : (0:ℝ) ≤ hS * (T1 / R) * relF := by positivity
  have hs2bFnn : (0:ℝ) ≤ a * b * c * (T1 * T2 / R ^ 3) * relF := by positivity
  have hs2bnn : (0:ℝ) ≤ a * b * c * (T1 * T2 / R ^ 3) * rel := by positivity
  have hs3nn : (0:ℝ) ≤ hS ^ 2 * T1 / R ^ 2 := by positivity
  have hs4nn : (0:ℝ) ≤ a * b * c * hS * (T1 * T2 / R ^ 4) := by positivity
  have hT1R2 : (0:ℝ) ≤ T1 / R ^ 2 := by positivity
  have hT1R : (0:ℝ) ≤ T1 / R := by positivity
  -- damping: 16·10⁴⁵·hS ≤ R (covers the G2 cross coefficient)
  have hdamp : (16:ℝ) * 10 ^ 45 * hS ≤ R := by
    calc (16:ℝ) * 10 ^ 45 * hS = hS * (16 * 10 ^ 45) := by ring
      _ ≤ hS * 10 ^ 149 := by
          apply mul_le_mul_of_nonneg_left _ hhS0
          norm_num
      _ ≤ R := hSR
  have bt1 : 16 * 10 ^ 45 * ((hS ^ 2 * T1 / R ^ 2) * (a * b * c * (T2 / R ^ 3))) ≤
      a * b * c * hS * (T1 * T2 / R ^ 4) := by
    rw [show 16 * 10 ^ 45 * ((hS ^ 2 * T1 / R ^ 2) * (a * b * c * (T2 / R ^ 3))) =
        (16 * 10 ^ 45 * hS) * (hS * T1 * (a * b * c) * T2) / R ^ 5 from by ring,
      show a * b * c * hS * (T1 * T2 / R ^ 4) =
        R * (hS * T1 * (a * b * c) * T2) / R ^ 5 from by
        rw [pow_succ]
        field_simp]
    have hX : (0:ℝ) ≤ hS * T1 * (a * b * c) * T2 := by positivity
    gcongr
  -- group bounds, slot form
  have HG1 : 10 ^ 31 * (a * b * c * (T1 * T2 / R ^ 3) * relF +
      a * b * c * hS * (T1 * T2) / R ^ 4) =
      10 ^ 31 * (a * b * c * (T1 * T2 / R ^ 3) * relF) +
        10 ^ 31 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by ring
  have HG2 : 8 * ((10 ^ 26 * (hS ^ 2 * T1 / R ^ 2 + T1 * relF)) *
      (2 * 10 ^ 19 * (a * b * c * (T2 / R ^ 3)))) ≤
      16 * 10 ^ 45 * (a * b * c * (T1 * T2 / R ^ 3) * relF) +
        a * b * c * hS * (T1 * T2 / R ^ 4) := by
    have key : 8 * ((10 ^ 26 * (hS ^ 2 * T1 / R ^ 2 + T1 * relF)) *
        (2 * 10 ^ 19 * (a * b * c * (T2 / R ^ 3)))) =
        16 * 10 ^ 45 * ((hS ^ 2 * T1 / R ^ 2) * (a * b * c * (T2 / R ^ 3))) +
        16 * 10 ^ 45 * (a * b * c * (T1 * T2 / R ^ 3) * relF) := by ring
    linarith [bt1, key]
  have HG3 : 8 * ((10 ^ 15 * T1) *
      (10 ^ 31 * (a * b * c * (T2 / R ^ 3) * rel + a * b * c * hS * T2 / R ^ 4))) =
      8 * 10 ^ 46 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        8 * 10 ^ 46 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by ring
  have HG4 : ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u ≤ hS → u * (v * w) = a * b * c →
      8 * ((10 ^ 26 * (u * hS * T1 / R ^ 2 + u * (T1 / R) * relF)) *
        (3 * 10 ^ 15 * (v * w * (T2 / R ^ 2)) + 10 ^ 10)) ≤
      24 * 10 ^ 41 * (a * b * c * hS * (T1 * T2 / R ^ 4)) +
        24 * 10 ^ 41 * (a * b * c * (T1 * T2 / R ^ 3) * relF) +
        8 * 10 ^ 36 * (hS ^ 2 * T1 / R ^ 2) + 8 * 10 ^ 36 * (hS * (T1 / R) * relF) := by
    intro u v w hu0 hv0 hw0 hule huvw
    have key : 8 * ((10 ^ 26 * (u * hS * T1 / R ^ 2 + u * (T1 / R) * relF)) *
        (3 * 10 ^ 15 * (v * w * (T2 / R ^ 2)) + 10 ^ 10)) =
        24 * 10 ^ 41 * ((u * (v * w)) * hS * (T1 * T2 / R ^ 4)) +
        24 * 10 ^ 41 * ((u * (v * w)) * (T1 * T2 / R ^ 3) * relF) +
        8 * 10 ^ 36 * (u * hS * T1 / R ^ 2) + 8 * 10 ^ 36 * (u * (T1 / R) * relF) := by
      ring
    rw [huvw] at key
    have b1 : u * hS * T1 / R ^ 2 ≤ hS ^ 2 * T1 / R ^ 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hule) hhS0) hT1.le]
    have b2 : u * (T1 / R) * relF ≤ hS * (T1 / R) * relF := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hule) hT1R) hrelF]
    linarith [key, b1, b2]
  have HG5 : ∀ u v w : ℝ, u * (v * w) = a * b * c →
      8 * ((4 * 10 ^ 18 * (u * (T1 / R))) *
        (10 ^ 26 * (v * w * (T2 / R ^ 2) * rel + v * w * hS * T2 / R ^ 3))) =
      32 * 10 ^ 44 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        32 * 10 ^ 44 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by
    intro u v w huvw
    have key : 8 * ((4 * 10 ^ 18 * (u * (T1 / R))) *
        (10 ^ 26 * (v * w * (T2 / R ^ 2) * rel + v * w * hS * T2 / R ^ 3))) =
        32 * 10 ^ 44 * ((u * (v * w)) * (T1 * T2 / R ^ 3) * rel) +
        32 * 10 ^ 44 * ((u * (v * w)) * hS * (T1 * T2 / R ^ 4)) := by ring
    rw [huvw] at key
    exact key
  have HG6 : 8 * 10 ^ 26 * (hS * (a * b * c) * (T1 * T2 / R ^ 4)) =
      8 * 10 ^ 26 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by ring
  have h41 := HG4 a b c ha0 hb0 hc0 ha (by ring)
  have h42 := HG4 b a c hb0 ha0 hc0 hb (by ring)
  have h43 := HG4 c a b hc0 ha0 hb0 hc (by ring)
  have h51 := HG5 a b c (by ring)
  have h52 := HG5 b a c (by ring)
  have h53 := HG5 c a b (by ring)
  have hRHS : 10 ^ 44 * (hS * (T1 / R) * relF + hS ^ 2 * T1 / R ^ 2) +
      10 ^ 52 * (a * b * c * (T1 * T2 / R ^ 3) * relF + a * b * c * (T1 * T2 / R ^ 3) * rel +
        a * b * c * hS * (T1 * T2 / R ^ 4)) =
      10 ^ 44 * (hS * (T1 / R) * relF) + 10 ^ 44 * (hS ^ 2 * T1 / R ^ 2) +
        10 ^ 52 * (a * b * c * (T1 * T2 / R ^ 3) * relF) +
        10 ^ 52 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        10 ^ 52 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by ring
  linarith [le_of_eq HG1, HG2, le_of_eq HG3, h41, h42, h43,
    le_of_eq h51, le_of_eq h52, le_of_eq h53, le_of_eq HG6, le_of_eq hRHS,
    hs2ann, hs2bFnn, hs2bnn, hs3nn, hs4nn]

/-- **N11 order-3** (Φ″ endgame, two-constant split): at `m = 3` and `ρ₀ = 0`,
`|Err^{(3)}(r)| ≤ cErr3Lead·errScale_LEAD/R³ + cErr3Res·errScale_RES/R³` on the count window.
The hypothesis pack mirrors `sec7_err_deriv_bound`; the extra `hρ₀eq : ρ₀ = 0` kills the
stand-alone `T₁·relErrF` slot.  Assembled constants: LEAD `= 2.4·10³⁷ ≤ cErr3Lead = 10⁴⁴`,
RES `= 8.96·10⁴⁶ ≤ cErr3Res = 10⁵²`. -/
theorem sec7_err_deriv_bound_m3 {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a}
    {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ} (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Env : Sec7Envelope P S W) (hj : sec7_jBand P S j)
    (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hW : 0 < W)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (hrel143 : sec7_relErr P S * 10 ^ 143 ≤ 1)
    (hrelF143 : sec7_relErrF P S * 10 ^ 143 ≤ 1)
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ) (hρ₀eq : ρ₀ = 0)
    (hρ₀ : |(ρ₀ : ℝ)| ≤ sec7_cCarry)
    (hρ₁ : |(ρ₁ : ℝ)| ≤ sec7_cCarry) (hρ₂ : |(ρ₂ : ℝ)| ≤ sec7_cCarry)
    (hρ₃ : |(ρ₃ : ℝ)| ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) :
    ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv 3 (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cErr3Lead * sec7_errScale_LEAD P S h₁ h₂ h₃ / S.R ^ 3 +
          sec7_cErr3Res * sec7_errScale_RES P S h₁ h₂ h₃ / S.R ^ 3 := by
  have hh₁ : 1 ≤ h₁ := hbox.1.1
  have hh₂ : 1 ≤ h₂ := hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := hbox.2.2.1
  have hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R := sec7_hSum_R_small Env hbox
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT2 : 0 < S.T₂ := sec7_T₂_pos S
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hrelF0 : 0 ≤ sec7_relErrF P S := (sec7_relErrF_pos P S).le
  have hcrel3 : sec7_cExp3 * sec7_relErr P S ≤ 1 := sec7E_cExp3_rel hrel143
  have hcrel3L : sec7_cExp3Lead * sec7_relErr P S ≤ 1 := sec7E_cExp3Lead_rel hrel143
  have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
  have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
  have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
  have hle₁ : (h₁:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₁:ℝ) ≤ (h₁:ℝ) + h₂ + h₃; linarith
  have hle₂ : (h₂:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₂:ℝ) ≤ (h₁:ℝ) + h₂ + h₃; linarith
  have hle₃ : (h₃:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₃:ℝ) ≤ (h₁:ℝ) + h₂ + h₃; linarith
  have hc₁ : |(ρ₁:ℝ) - u₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by
    rw [abs_sub_comm]; exact hu₁
  have hc₂ : |(ρ₂:ℝ) - u₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by
    rw [abs_sub_comm]; exact hu₂
  have hc₃ : |(ρ₃:ℝ) - u₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)) := by
    rw [abs_sub_comm]; exact hu₃
  intro r hr
  set F : ℕ → ℝ → ℝ := fun k t =>
    sec7E_eP3 ME k t
    + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) k t
    + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) k t
    + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) k t
    + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) k t
    + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) k t
    + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) k t
    + sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) k t
    + sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) k t
    + sec7E_T6 ME k t with hFdef
  have hchain : ∀ k < 3, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (F k) (F (k + 1) x) x := by
    intro k hk x hx
    have c1 := sec7E_eP3_chain ME hh₁ hh₂ hh₃ hpad hshift k hk x hx
    have c2 := sec7_leib_deriv (sec7E_eA_chain ME hh₁ hh₂ hh₃ hpad hshift)
      (sec7E_gB_chain ME hh₁ hh₂ hh₃ hshift ρ₀) k hk x hx
    have c3 := sec7_leib_deriv (sec7E_M1_chain ME hpad)
      (sec7E_eB0_chain ME hh₁ hh₂ hh₃ hpad hshift) k hk x hx
    have c4 := sec7_leib_deriv (sec7E_eQ_chain ME hh₁ hh₂ hh₃ hpad hshift hh₁ hle₁)
      (sec7E_gK_chain ME hh₁ hh₂ hh₃ hshift hh₂ hh₃ hle₂ hle₃ hξ₁ ((ρ₁:ℝ) - u₁)) k hk x hx
    have c5 := sec7_leib_deriv (sec7E_N_chain ME hpad h₁)
      (sec7E_eK_chain ME hh₁ hh₂ hh₃ hpad hshift hh₂ hh₃ hle₂ hle₃ hξ₁) k hk x hx
    have c6 := sec7_leib_deriv (sec7E_eQ_chain ME hh₁ hh₂ hh₃ hpad hshift hh₂ hle₂)
      (sec7E_gK_chain ME hh₁ hh₂ hh₃ hshift hh₁ hh₃ hle₁ hle₃ hξ₂ ((ρ₂:ℝ) - u₂)) k hk x hx
    have c7 := sec7_leib_deriv (sec7E_N_chain ME hpad h₂)
      (sec7E_eK_chain ME hh₁ hh₂ hh₃ hpad hshift hh₁ hh₃ hle₁ hle₃ hξ₂) k hk x hx
    have c8 := sec7_leib_deriv (sec7E_eQ_chain ME hh₁ hh₂ hh₃ hpad hshift hh₃ hle₃)
      (sec7E_gK_chain ME hh₁ hh₂ hh₃ hshift hh₁ hh₂ hle₁ hle₂ hξ₃ ((ρ₃:ℝ) - u₃)) k hk x hx
    have c9 := sec7_leib_deriv (sec7E_N_chain ME hpad h₃)
      (sec7E_eK_chain ME hh₁ hh₂ hh₃ hpad hshift hh₁ hh₂ hle₁ hle₂ hξ₃) k hk x hx
    have c10 := sec7E_T6_chain ME hpad k hk x hx
    simp only [hFdef]
    exact ((((((((c1.add c2).add c3).add c4).add c5).add c6).add c7).add c8).add
      c9).add c10
  have h0 : ∀ x ∈ sec7_rWinMid S W,
      ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ x = F 0 x := by
    intro x hx
    have hx0 : 0 < x := sec7E_mid_pos hpad hx
    have hxR : 0 < x / S.R := div_pos hx0 hR
    have e1 : (x / S.R) ^ (-(1:ℝ)) * (x / S.R) ^ (-(9:ℝ)/4) =
        (x / S.R) ^ (-(13:ℝ)/4) := by
      rw [← Real.rpow_add hxR]; norm_num
    have e2 : (x / S.R) ^ (-(2:ℝ)) * (x / S.R) ^ (-(5:ℝ)/4) =
        (x / S.R) ^ (-(13:ℝ)/4) := by
      rw [← Real.rpow_add hxR]; norm_num
    have e3 : (x / S.R) ^ (-(2:ℝ)) * (x / S.R) ^ (-(9:ℝ)/4) =
        (x / S.R) ^ (-(17:ℝ)/4) := by
      rw [← Real.rpow_add hxR]; norm_num
    have hT3 : S.T₃ = S.T₁ * S.T₂ := (sec7_T₁_mul_T₂ S).symm
    simp only [hFdef, Sec7MonExp.Err, sec7_Phi, Sec7MonExp.principal, Sec7MonExp.Bcoef,
      Sec7MonExp.Cstar, sec7_leib_zero, sec7E_eP3, sec7E_eA, sec7E_eQ, sec7E_eK,
      sec7E_eB0, sec7E_gB, sec7E_gK, sec7E_M1, sec7E_N, sec7E_L, sec7E_M0, sec7E_M3,
      sec7E_T6, sec7_constF_zero, sec7_powMonD_zero, sec7_powMon]
    rw [show Ph.f1D j 0 = ME.f1C 0 from (funext ME.f1C_zero).symm,
      show Ph.f2D 0 = ME.f2C 0 from (funext ME.f2C_zero).symm,
      show Ph.f3D j 0 = ME.f3C 0 from (funext ME.f3C_zero).symm, hT3]
    simp only [sec7_hSum, sec7_Pprod]
    linear_combination
      ((15:ℝ)/64 * ME.c₁ * ME.c₂ * ((h₁:ℝ) * h₂ * h₃) * S.T₁ * S.T₂ / S.R ^ 3) * e1
      + ((9:ℝ)/16 * ME.c₁ * ME.c₂ * ((h₁:ℝ) * h₂ * h₃) * S.T₁ * S.T₂ / S.R ^ 3) * e2
      - ((15:ℝ)/64 * ME.c₁ * ME.c₂ * ((h₁:ℝ) + h₂ + h₃) * ((h₁:ℝ) * h₂ * h₃) *
          S.T₁ * S.T₂ / S.R ^ 4) * e3
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0 hchain
    3 (le_refl 3) r (sec7_rWin_subset_mid S hW hr)
  rw [hid]
  have hcExp3L0 : (0:ℝ) ≤ sec7_cExp3Lead := sec7_cExp3Lead_pos.le
  have hcExp30 : (0:ℝ) ≤ sec7_cExp3 := sec7_cExp3_pos.le
  have hcF0 : (0:ℝ) ≤ sec7_cFib := by norm_num [sec7_cFib]
  have h10 : (0:ℝ) ≤ (h₁:ℝ) := by linarith
  have h20 : (0:ℝ) ≤ (h₂:ℝ) := by linarith
  have h30 : (0:ℝ) ≤ (h₃:ℝ) := by linarith
  have hS0 : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by linarith
  have hPv0 : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := mul_nonneg (mul_nonneg h10 h20) h30
  have nT1R : (0:ℝ) ≤ S.T₁ / S.R := div_nonneg hT1.le hR.le
  have nT2R2 : (0:ℝ) ≤ S.T₂ / S.R ^ 2 := div_nonneg hT2.le (pow_nonneg hR.le 2)
  have nT2R3 : (0:ℝ) ≤ S.T₂ / S.R ^ 3 := div_nonneg hT2.le (pow_nonneg hR.le 3)
  have hb1 := sec7E_eP3_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift 3 (le_refl 3) r hr
  have hgBb : ∀ k ≤ 3, |sec7E_gB ME ρ₀ k r| ≤
      (2 * 10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3))) / S.R ^ k := by
    intro k hk
    have h := sec7E_gB_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel3 hρ₀ k hk r hr
    rw [hρ₀eq] at h ⊢
    simpa using h
  have hb2 := sec7_leib_bound3
    (a := sec7_cExp3Lead * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 + S.T₁ * sec7_relErrF P S))
    (b := 2 * 10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3))) hR
    (mul_nonneg hcExp3L0 (add_nonneg
      (div_nonneg (mul_nonneg (sq_nonneg _) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg hT1.le hrelF0)))
    (mul_nonneg (by norm_num) (mul_nonneg hPv0 nT2R3))
    (fun k hk => sec7E_eA_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift k hk r hr)
    hgBb 3 (le_refl 3)
  have hb3 := sec7_leib_bound3 (a := 10 ^ 15 * S.T₁)
    (b := sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S + sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4)) hR
    (mul_nonneg (by norm_num) hT1.le)
    (mul_nonneg hcExp30 (add_nonneg
      (mul_nonneg (mul_nonneg hPv0 nT2R3) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg hPv0 hS0) hT2.le) (pow_nonneg hR.le 4))))
    (fun k hk => sec7E_M1_bound3 ME hh₁ hh₂ hh₃ hW hpad hSR k hk r hr)
    (fun k hk => sec7E_eB0_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift k hk r hr) 3 (le_refl 3)
  have hb4 := sec7_leib_bound3 (a := sec7_cExp3Lead * ((h₁ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 + (h₁ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S))
    (b := 3 * 10 ^ 15 * ((h₂:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) hR
    (mul_nonneg hcExp3L0 (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg h10 hS0) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg (mul_nonneg h10 nT1R) hrelF0)))
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg h20 h30) nT2R2)) hcF0)
    (fun k hk => sec7E_eQ_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hh₁ hle₁ ME.d1f1_exp₁₃ k hk r hr)
    (fun k hk => sec7E_gK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel3L hh₂ hh₃ hle₂ hle₃ hξ₁
      hc₁ ME.B_exp₁₃ k hk r hr) 3 (le_refl 3)
  have hb5 := sec7_leib_bound3 (a := 4 * 10 ^ 18 * ((h₁:ℝ) * (S.T₁ / S.R)))
    (b := sec7_cExp3Lead * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S + (h₂ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)) hR
    (mul_nonneg (by norm_num) (mul_nonneg h10 nT1R))
    (mul_nonneg hcExp3L0 (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h20 h30) nT2R2) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h20 h30) hS0) hT2.le)
        (pow_nonneg hR.le 3))))
    (fun k hk => sec7E_N_bound3 ME hW hpad hh₁ k hk r hr)
    (fun k hk => sec7E_eK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hh₂ hh₃ hle₂ hle₃ hξ₁
      ME.B_exp₁₃ k hk r hr) 3 (le_refl 3)
  have hb6 := sec7_leib_bound3 (a := sec7_cExp3Lead * ((h₂ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 + (h₂ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S))
    (b := 3 * 10 ^ 15 * ((h₁:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) hR
    (mul_nonneg hcExp3L0 (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg h20 hS0) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg (mul_nonneg h20 nT1R) hrelF0)))
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg h10 h30) nT2R2)) hcF0)
    (fun k hk => sec7E_eQ_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hh₂ hle₂ ME.d1f1_exp₂₃ k hk r hr)
    (fun k hk => sec7E_gK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel3L hh₁ hh₃ hle₁ hle₃ hξ₂
      hc₂ ME.B_exp₂₃ k hk r hr) 3 (le_refl 3)
  have hb7 := sec7_leib_bound3 (a := 4 * 10 ^ 18 * ((h₂:ℝ) * (S.T₁ / S.R)))
    (b := sec7_cExp3Lead * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S + (h₁ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)) hR
    (mul_nonneg (by norm_num) (mul_nonneg h20 nT1R))
    (mul_nonneg hcExp3L0 (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h10 h30) nT2R2) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h10 h30) hS0) hT2.le)
        (pow_nonneg hR.le 3))))
    (fun k hk => sec7E_N_bound3 ME hW hpad hh₂ k hk r hr)
    (fun k hk => sec7E_eK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hh₁ hh₃ hle₁ hle₃ hξ₂
      ME.B_exp₂₃ k hk r hr) 3 (le_refl 3)
  have hb8 := sec7_leib_bound3 (a := sec7_cExp3Lead * ((h₃ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 + (h₃ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S))
    (b := 3 * 10 ^ 15 * ((h₁:ℝ) * (h₂:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) hR
    (mul_nonneg hcExp3L0 (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg h30 hS0) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg (mul_nonneg h30 nT1R) hrelF0)))
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg h10 h20) nT2R2)) hcF0)
    (fun k hk => sec7E_eQ_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hh₃ hle₃ ME.d1f1_exp₃₃ k hk r hr)
    (fun k hk => sec7E_gK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel3L hh₁ hh₂ hle₁ hle₂ hξ₃
      hc₃ ME.B_exp₃₃ k hk r hr) 3 (le_refl 3)
  have hb9 := sec7_leib_bound3 (a := 4 * 10 ^ 18 * ((h₃:ℝ) * (S.T₁ / S.R)))
    (b := sec7_cExp3Lead * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) * sec7_relErr P S + (h₁ : ℝ) * h₂ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)) hR
    (mul_nonneg (by norm_num) (mul_nonneg h30 nT1R))
    (mul_nonneg hcExp3L0 (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h10 h20) nT2R2) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h10 h20) hS0) hT2.le)
        (pow_nonneg hR.le 3))))
    (fun k hk => sec7E_N_bound3 ME hW hpad hh₃ k hk r hr)
    (fun k hk => sec7E_eK_bound3 ME hh₁ hh₂ hh₃ hW hpad hshift hh₁ hh₂ hle₁ hle₂ hξ₃
      ME.B_exp₃₃ k hk r hr) 3 (le_refl 3)
  have hb10 := sec7E_T6_bound3 ME hh₁ hh₂ hh₃ hW hpad 3 (le_refl 3) r hr
  have htri : |F 3 r| ≤
      |sec7E_eP3 ME 3 r|
      + |sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r|
      + |sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r|
      + |sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r|
      + |sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r|
      + |sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) 3 r|
      + |sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) 3 r|
      + |sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) 3 r|
      + |sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) 3 r|
      + |sec7E_T6 ME 3 r| := by
    simp only [hFdef]
    have t9 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) 3 r
      + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) 3 r
      + sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) 3 r
      + sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) 3 r) (sec7E_T6 ME 3 r)
    have t8 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) 3 r
      + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) 3 r
      + sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) 3 r)
      (sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) 3 r)
    have t7 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) 3 r
      + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) 3 r)
      (sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) 3 r)
    have t6 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) 3 r)
      (sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) 3 r)
    have t5 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r)
      (sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) 3 r)
    have t4 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r)
      (sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) 3 r)
    have t3 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r)
      (sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) 3 r)
    have t2 := abs_add_le (sec7E_eP3 ME 3 r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r)
      (sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) 3 r)
    have t1 := abs_add_le (sec7E_eP3 ME 3 r)
      (sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) 3 r)
    linarith
  have hPv1 : (1:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
    unfold sec7_Pprod
    have h12 : (1:ℝ) ≤ (h₁:ℝ) * h₂ := by nlinarith
    nlinarith [h12, a3]
  have hnum := sec7E_num_final_m3 (T1 := S.T₁) (T2 := S.T₂) (T3 := S.T₃) (R := S.R)
    (hS := sec7_hSum h₁ h₂ h₃) (Pv := sec7_Pprod h₁ h₂ h₃)
    (relF := sec7_relErrF P S) (rel := sec7_relErr P S)
    (a := (h₁:ℝ)) (b := (h₂:ℝ)) (c := (h₃:ℝ))
    hT1 hT2 hR hSv3 hPv1 hrelF0 hrel0 a1 a2 a3 hle₁ hle₂ hle₃
    (by unfold sec7_Pprod; ring) (sec7_T₁_mul_T₂ S) hSR
  calc |F 3 r|
      ≤ (sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
            sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₃ / S.R ^ 4)
        + 8 * ((sec7_cExp3Lead * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
              S.T₁ * sec7_relErrF P S)) *
            (2 * 10 ^ 19 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3))))
        + 8 * ((10 ^ 15 * S.T₁) *
            (sec7_cExp3 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
              sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4)))
        + 8 * ((sec7_cExp3Lead * ((h₁ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
              (h₁ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S)) *
            (3 * 10 ^ 15 * ((h₂:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib))
        + 8 * ((4 * 10 ^ 18 * ((h₁:ℝ) * (S.T₁ / S.R))) *
            (sec7_cExp3Lead * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
              (h₂ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)))
        + 8 * ((sec7_cExp3Lead * ((h₂ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
              (h₂ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S)) *
            (3 * 10 ^ 15 * ((h₁:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib))
        + 8 * ((4 * 10 ^ 18 * ((h₂:ℝ) * (S.T₁ / S.R))) *
            (sec7_cExp3Lead * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
              (h₁ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)))
        + 8 * ((sec7_cExp3Lead * ((h₃ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
              (h₃ : ℝ) * (S.T₁ / S.R) * sec7_relErrF P S)) *
            (3 * 10 ^ 15 * ((h₁:ℝ) * (h₂:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib))
        + 8 * ((4 * 10 ^ 18 * ((h₃:ℝ) * (S.T₁ / S.R))) *
            (sec7_cExp3Lead * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
              (h₁ : ℝ) * h₂ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)))
        + 8 * 10 ^ 26 * (sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
            (S.T₁ * S.T₂ / S.R ^ 4))) / S.R ^ 3 := by
        rw [add_div, add_div, add_div, add_div, add_div, add_div, add_div, add_div,
          add_div]
        exact le_trans htri (by gcongr)
    _ ≤ sec7_cErr3Lead * sec7_errScale_LEAD P S h₁ h₂ h₃ / S.R ^ 3 +
          sec7_cErr3Res * sec7_errScale_RES P S h₁ h₂ h₃ / S.R ^ 3 := by
        rw [← add_div]
        gcongr (?_ : ℝ) / _
        simp only [sec7_cErr3Lead, sec7_cErr3Res, sec7_errScale_LEAD, sec7_errScale_RES,
          sec7_cExp3, sec7_cExp3Lead, sec7_cFib]
        exact hnum

end Squarefree
