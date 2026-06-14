import Squarefree.Bracket.Sec7ErrFactors

/-!
# §7 N11 — the `Err^{(m)}` bound (md 1666–82)

`sec7_err_deriv_bound`: `|Err^{(m)}(r)| ≤ cErr·errScale/Rᵐ` for `m ≤ 2` on the count
window.  The theorem statement lived in `Sec7PhaseExp.lean` as the N11 stub; it sits here
because its proof needs the wide-window chain machinery (`Sec7MonExpAux`/`Sec7MonExpData`),
which imports `Sec7PhaseExp`.  Route (interface ruling 2026-06-12): the eq-(7.5) remainder
is regrouped into ten graded Leibniz products of the `Sec7MonExp` error/monomial families
(`Sec7ErrPieces.lean`); chains identify `iteratedDeriv m Err` with the grade-`m` family on
the open mid window; the value bounds collapse into the four `errScale` slots.

Ledger (re-pin 2026-06-12, `tools/sec7_ledger.py` N11 block): slot floor `≈ 8.8·10⁴⁰`
(binding: `Nᵢ·eKᵢ` at `3·1.6·10⁴⁰` plus `eA·(B₀₃+ρ₀)` at `4·10⁴⁰`), `sec7_cErr = 10⁴²`
(≥11× margin), coupled `sec7_cSub = 10⁴⁴ ≥ 2.6·cErr` (corner capacity `10^{64.3}`).
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

/-- **N11 numeric assembly** (abstract scalar form; ledger-banked).  The ten group
numerators against the four `errScale` slots at `cErr = 10⁴²`. -/
private theorem sec7E_num_final {T1 T2 T3 R hS Pv rel ind a b c : ℝ}
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hR : 0 < R) (hhS : 3 ≤ hS) (hPv : 1 ≤ Pv)
    (hrel : 0 ≤ rel) (hind0 : 0 ≤ ind) (hind1 : ind ≤ 1)
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (ha : a ≤ hS) (hb : b ≤ hS) (hc : c ≤ hS)
    (habc : a * b * c = Pv) (hT3 : T1 * T2 = T3)
    (hSR : hS * 10 ^ 149 ≤ R) :
    10 ^ 25 * (Pv * (T3 / R ^ 3) * rel + Pv * hS * T3 / R ^ 4)
      + 4 * ((10 ^ 25 * (hS ^ 2 * T1 / R ^ 2 + T1 * rel)) *
          (10 ^ 15 * (Pv * (T2 / R ^ 3)) + ind * 10 ^ 6))
      + 4 * ((10 ^ 11 * T1) *
          (10 ^ 25 * (Pv * (T2 / R ^ 3) * rel + Pv * hS * T2 / R ^ 4)))
      + 4 * ((10 ^ 25 * (a * hS * T1 / R ^ 2 + a * (T1 / R) * rel)) *
          (14 * 10 ^ 10 * (b * c * (T2 / R ^ 2)) + 10 ^ 10))
      + 4 * ((4 * 10 ^ 14 * (a * (T1 / R))) *
          (10 ^ 25 * (b * c * (T2 / R ^ 2) * rel + b * c * hS * T2 / R ^ 3)))
      + 4 * ((10 ^ 25 * (b * hS * T1 / R ^ 2 + b * (T1 / R) * rel)) *
          (14 * 10 ^ 10 * (a * c * (T2 / R ^ 2)) + 10 ^ 10))
      + 4 * ((4 * 10 ^ 14 * (b * (T1 / R))) *
          (10 ^ 25 * (a * c * (T2 / R ^ 2) * rel + a * c * hS * T2 / R ^ 3)))
      + 4 * ((10 ^ 25 * (c * hS * T1 / R ^ 2 + c * (T1 / R) * rel)) *
          (14 * 10 ^ 10 * (a * b * (T2 / R ^ 2)) + 10 ^ 10))
      + 4 * ((4 * 10 ^ 14 * (c * (T1 / R))) *
          (10 ^ 25 * (a * b * (T2 / R ^ 2) * rel + a * b * hS * T2 / R ^ 3)))
      + 4 * 10 ^ 22 * (hS * Pv * (T1 * T2 / R ^ 4))
    ≤ 10 ^ 42 * (ind * T1 * rel + (hS * (T1 / R) + Pv * (T3 / R ^ 3)) * rel
        + hS ^ 2 * T1 / R ^ 2 + Pv * hS * (T3 / R ^ 4)) := by
  subst hT3
  subst habc
  have hhS0 : (0:ℝ) ≤ hS := by linarith
  have ha0 : (0:ℝ) ≤ a := by linarith
  have hb0 : (0:ℝ) ≤ b := by linarith
  have hc0 : (0:ℝ) ≤ c := by linarith
  have hs1nn : (0:ℝ) ≤ ind * T1 * rel := by positivity
  have hs2ann : (0:ℝ) ≤ hS * (T1 / R) * rel := by positivity
  have hs2bnn : (0:ℝ) ≤ a * b * c * (T1 * T2 / R ^ 3) * rel := by positivity
  have hs3nn : (0:ℝ) ≤ hS ^ 2 * T1 / R ^ 2 := by positivity
  have hs4nn : (0:ℝ) ≤ a * b * c * hS * (T1 * T2 / R ^ 4) := by positivity
  have hT1R2 : (0:ℝ) ≤ T1 / R ^ 2 := by positivity
  have hT1R : (0:ℝ) ≤ T1 / R := by positivity
  -- damping: 4·10⁴⁰·hS ≤ R
  have hdamp : (4:ℝ) * 10 ^ 40 * hS ≤ R := by
    calc (4:ℝ) * 10 ^ 40 * hS = hS * (4 * 10 ^ 40) := by ring
      _ ≤ hS * 10 ^ 149 := by
          apply mul_le_mul_of_nonneg_left _ hhS0
          norm_num
      _ ≤ R := hSR
  -- G2's damped cross term
  have bt1 : 4 * 10 ^ 40 * ((hS ^ 2 * T1 / R ^ 2) * (a * b * c * (T2 / R ^ 3))) ≤
      a * b * c * hS * (T1 * T2 / R ^ 4) := by
    rw [show 4 * 10 ^ 40 * ((hS ^ 2 * T1 / R ^ 2) * (a * b * c * (T2 / R ^ 3))) =
        (4 * 10 ^ 40 * hS) * (hS * T1 * (a * b * c) * T2) / R ^ 5 from by ring,
      show a * b * c * hS * (T1 * T2 / R ^ 4) =
        R * (hS * T1 * (a * b * c) * T2) / R ^ 5 from by
        rw [pow_succ]
        field_simp]
    have hX : (0:ℝ) ≤ hS * T1 * (a * b * c) * T2 := by positivity
    gcongr
  -- group bounds, slot form
  have HG1 : 10 ^ 25 * (a * b * c * (T1 * T2 / R ^ 3) * rel +
      a * b * c * hS * (T1 * T2) / R ^ 4) =
      10 ^ 25 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        10 ^ 25 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by
    ring
  have HG2 : 4 * ((10 ^ 25 * (hS ^ 2 * T1 / R ^ 2 + T1 * rel)) *
      (10 ^ 15 * (a * b * c * (T2 / R ^ 3)) + ind * 10 ^ 6)) ≤
      4 * 10 ^ 40 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        a * b * c * hS * (T1 * T2 / R ^ 4) +
        4 * 10 ^ 31 * (hS ^ 2 * T1 / R ^ 2) + 4 * 10 ^ 31 * (ind * T1 * rel) := by
    have key : 4 * ((10 ^ 25 * (hS ^ 2 * T1 / R ^ 2 + T1 * rel)) *
        (10 ^ 15 * (a * b * c * (T2 / R ^ 3)) + ind * 10 ^ 6)) =
        4 * 10 ^ 40 * ((hS ^ 2 * T1 / R ^ 2) * (a * b * c * (T2 / R ^ 3))) +
        4 * 10 ^ 40 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        4 * 10 ^ 31 * (ind * (hS ^ 2 * T1 / R ^ 2)) +
        4 * 10 ^ 31 * (ind * T1 * rel) := by
      ring
    have hindS3 : ind * (hS ^ 2 * T1 / R ^ 2) ≤ hS ^ 2 * T1 / R ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hind1) hs3nn]
    linarith [bt1, key, hindS3]
  have HG3 : 4 * ((10 ^ 11 * T1) *
      (10 ^ 25 * (a * b * c * (T2 / R ^ 3) * rel + a * b * c * hS * T2 / R ^ 4))) =
      4 * 10 ^ 36 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        4 * 10 ^ 36 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by
    ring
  have HG4 : ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u ≤ hS → u * (v * w) = a * b * c →
      4 * ((10 ^ 25 * (u * hS * T1 / R ^ 2 + u * (T1 / R) * rel)) *
        (14 * 10 ^ 10 * (v * w * (T2 / R ^ 2)) + 10 ^ 10)) ≤
      56 * 10 ^ 35 * (a * b * c * hS * (T1 * T2 / R ^ 4)) +
        56 * 10 ^ 35 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        4 * 10 ^ 35 * (hS ^ 2 * T1 / R ^ 2) + 4 * 10 ^ 35 * (hS * (T1 / R) * rel) := by
    intro u v w hu0 hv0 hw0 hule huvw
    have key : 4 * ((10 ^ 25 * (u * hS * T1 / R ^ 2 + u * (T1 / R) * rel)) *
        (14 * 10 ^ 10 * (v * w * (T2 / R ^ 2)) + 10 ^ 10)) =
        56 * 10 ^ 35 * ((u * (v * w)) * hS * (T1 * T2 / R ^ 4)) +
        56 * 10 ^ 35 * ((u * (v * w)) * (T1 * T2 / R ^ 3) * rel) +
        4 * 10 ^ 35 * (u * hS * T1 / R ^ 2) + 4 * 10 ^ 35 * (u * (T1 / R) * rel) := by
      ring
    rw [huvw] at key
    have b1 : u * hS * T1 / R ^ 2 ≤ hS ^ 2 * T1 / R ^ 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hule) hhS0) hT1.le]
    have b2 : u * (T1 / R) * rel ≤ hS * (T1 / R) * rel := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hule) hT1R) hrel]
    linarith [key, b1, b2]
  have HG5 : ∀ u v w : ℝ, u * (v * w) = a * b * c →
      4 * ((4 * 10 ^ 14 * (u * (T1 / R))) *
        (10 ^ 25 * (v * w * (T2 / R ^ 2) * rel + v * w * hS * T2 / R ^ 3))) =
      16 * 10 ^ 39 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        16 * 10 ^ 39 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by
    intro u v w huvw
    have key : 4 * ((4 * 10 ^ 14 * (u * (T1 / R))) *
        (10 ^ 25 * (v * w * (T2 / R ^ 2) * rel + v * w * hS * T2 / R ^ 3))) =
        16 * 10 ^ 39 * ((u * (v * w)) * (T1 * T2 / R ^ 3) * rel) +
        16 * 10 ^ 39 * ((u * (v * w)) * hS * (T1 * T2 / R ^ 4)) := by
      ring
    rw [huvw] at key
    exact key
  have HG6 : 4 * 10 ^ 22 * (hS * (a * b * c) * (T1 * T2 / R ^ 4)) =
      4 * 10 ^ 22 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by
    ring
  have h41 := HG4 a b c ha0 hb0 hc0 ha (by ring)
  have h42 := HG4 b a c hb0 ha0 hc0 hb (by ring)
  have h43 := HG4 c a b hc0 ha0 hb0 hc (by ring)
  have h51 := HG5 a b c (by ring)
  have h52 := HG5 b a c (by ring)
  have h53 := HG5 c a b (by ring)
  -- final assembly: slot coefficients ≤ 10⁴²
  have hRHS : 10 ^ 42 * (ind * T1 * rel +
      (hS * (T1 / R) + a * b * c * (T1 * T2 / R ^ 3)) * rel
      + hS ^ 2 * T1 / R ^ 2 + a * b * c * hS * (T1 * T2 / R ^ 4)) =
      10 ^ 42 * (ind * T1 * rel) + 10 ^ 42 * (hS * (T1 / R) * rel) +
        10 ^ 42 * (a * b * c * (T1 * T2 / R ^ 3) * rel) +
        10 ^ 42 * (hS ^ 2 * T1 / R ^ 2) +
        10 ^ 42 * (a * b * c * hS * (T1 * T2 / R ^ 4)) := by
    ring
  linarith [le_of_eq HG1, HG2, le_of_eq HG3, h41, h42, h43,
    le_of_eq h51, le_of_eq h52, le_of_eq h53, le_of_eq HG6, le_of_eq hRHS,
    hs1nn, hs2ann, hs2bnn, hs3nn, hs4nn]


/-- **N11** (md 1666–82): `|Err^{(m)}(r)| ≤ cErr · errScale / Rᵐ` for `m ≤ 2` on the count
window.  Hypotheses: the N9 bundle, the realignment-shift sizes `|ξᵢ| ≤ h_Σ` (md 1547–53,
as carried by `Sec7ZeroHyp`), carry sizes `ρᵢ = O(1)` (md 1556, ARB-1: including the top
carry `ρ₀`), and fiber sizes `|uᵢ − ρᵢ| ≪ 1 + h_jh_k T₂/R²` (md 1560–70).  ARB-1 (A2/A3):
the absorption hypothesis `habs` is DROPPED — the Taylor term is explicit in `errScale`. -/
theorem sec7_err_deriv_bound {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ}
    {Ph : Sec7Phase P S W a}
    {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ} (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)
    (Env : Sec7Envelope P S W) (hj : sec7_jBand P S j)
    (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hW : 0 < W)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    (ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ)
    (hρ₀ : |(ρ₀ : ℝ)| ≤ sec7_cCarry)
    (hρ₁ : |(ρ₁ : ℝ)| ≤ sec7_cCarry) (hρ₂ : |(ρ₂ : ℝ)| ≤ sec7_cCarry)
    (hρ₃ : |(ρ₃ : ℝ)| ≤ sec7_cCarry)
    (hu₁ : |(u₁ : ℝ) - ρ₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₂ : |(u₂ : ℝ) - ρ₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)))
    (hu₃ : |(u₃ : ℝ) - ρ₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (ME.Err ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃) r| ≤
        sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ m := by
  -- box and smallness facts
  have hh₁ : 1 ≤ h₁ := hbox.1.1
  have hh₂ : 1 ≤ h₂ := hbox.2.1.1
  have hh₃ : 1 ≤ h₃ := hbox.2.2.1
  have hSR : sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R := sec7_hSum_R_small Env hbox
  have hrel150 : sec7_relErr P S * 10 ^ 150 ≤ 1 :=
    sec7_relErr_le Env (sec7_W_ge_one hbox)
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hR : 0 < S.R := sec7_R_pos S
  have hT1 : 0 < S.T₁ := sec7_T₁_pos S
  have hT2 : 0 < S.T₂ := sec7_T₂_pos S
  have hrel0 : 0 ≤ sec7_relErr P S := (sec7_relErr_pos P S).le
  have hcrel : sec7_cExp * sec7_relErr P S ≤ 1 :=
    sec7E_cExp_rel hrel150
  have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
  have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
  have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
  have hle₁ : (h₁:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₁:ℝ) ≤ (h₁:ℝ) + h₂ + h₃
    linarith
  have hle₂ : (h₂:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₂:ℝ) ≤ (h₁:ℝ) + h₂ + h₃
    linarith
  have hle₃ : (h₃:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by
    show (h₃:ℝ) ≤ (h₁:ℝ) + h₂ + h₃
    linarith
  -- constant-factor bounds for the gK families
  have hc₁ : |(ρ₁:ℝ) - u₁| ≤ sec7_cFib * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by
    rw [abs_sub_comm]; exact hu₁
  have hc₂ : |(ρ₂:ℝ) - u₂| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by
    rw [abs_sub_comm]; exact hu₂
  have hc₃ : |(ρ₃:ℝ) - u₃| ≤ sec7_cFib * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)) := by
    rw [abs_sub_comm]; exact hu₃
  intro m hm r hr
  -- the master graded family of the eq-(7.5) remainder
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
  -- its chain on the mid window
  have hchain : ∀ k < 2, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (F k) (F (k + 1) x) x := by
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
  -- grade-0 identity on the mid window (the eq-(7.5) regrouping)
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
  -- identify the iterated derivative with the family
  have hid := sec7_iteratedDeriv_eq_of_chain_eqOn (sec7_rWinMid_isOpen S W) h0 hchain
    m hm r (sec7_rWin_subset_mid S hW hr)
  rw [hid]
  -- per-group value bounds at r
  have hcExp0 : (0:ℝ) ≤ sec7_cExp := sec7_cExp_pos.le
  have hcC0 : (0:ℝ) ≤ sec7_cCarry := by norm_num [sec7_cCarry]
  have hcF0 : (0:ℝ) ≤ sec7_cFib := by norm_num [sec7_cFib]
  have hind0 : (0:ℝ) ≤ (if ρ₀ = 0 then (0:ℝ) else 1) := by split <;> norm_num
  have hind1 : (if ρ₀ = 0 then (0:ℝ) else 1) ≤ 1 := by split <;> norm_num
  have h10 : (0:ℝ) ≤ (h₁:ℝ) := by linarith
  have h20 : (0:ℝ) ≤ (h₂:ℝ) := by linarith
  have h30 : (0:ℝ) ≤ (h₃:ℝ) := by linarith
  have hS0 : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by linarith
  have hPv0 : (0:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ :=
    mul_nonneg (mul_nonneg h10 h20) h30
  have nT1R : (0:ℝ) ≤ S.T₁ / S.R := div_nonneg hT1.le hR.le
  have nT2R2 : (0:ℝ) ≤ S.T₂ / S.R ^ 2 := div_nonneg hT2.le (pow_nonneg hR.le 2)
  have nT2R3 : (0:ℝ) ≤ S.T₂ / S.R ^ 3 := div_nonneg hT2.le (pow_nonneg hR.le 3)
  have hb1 := sec7E_eP3_bound ME hh₁ hh₂ hh₃ hW hpad hshift m hm r hr
  have hb2 := sec7_leib_bound (a := sec7_cExp * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 + S.T₁ * sec7_relErr P S))
    (b := 10 ^ 15 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) + (if ρ₀ = 0 then 0 else 1) * sec7_cCarry) hR
    (mul_nonneg hcExp0 (add_nonneg
      (div_nonneg (mul_nonneg (sq_nonneg _) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg hT1.le hrel0)))
    (add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hPv0 nT2R3))
      (mul_nonneg hind0 hcC0))
    (fun k hk => sec7E_eA_bound ME hh₁ hh₂ hh₃ hW hpad hshift k hk r hr)
    (fun k hk => sec7E_gB_bound ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel hρ₀ k hk r hr) m hm
  have hb3 := sec7_leib_bound (a := 10 ^ 11 * S.T₁)
    (b := sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S + sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4)) hR
    (mul_nonneg (by norm_num) hT1.le)
    (mul_nonneg hcExp0 (add_nonneg
      (mul_nonneg (mul_nonneg hPv0 nT2R3) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg hPv0 hS0) hT2.le) (pow_nonneg hR.le 4))))
    (fun k hk => sec7E_M1_bound ME hh₁ hh₂ hh₃ hW hpad hSR k hk r hr)
    (fun k hk => sec7E_eB0_bound ME hh₁ hh₂ hh₃ hW hpad hshift k hk r hr) m hm
  have hb4 := sec7_leib_bound (a := sec7_cExp * ((h₁ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 + (h₁ : ℝ) * (S.T₁ / S.R) * sec7_relErr P S))
    (b := 14 * 10 ^ 10 * ((h₂:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) hR
    (mul_nonneg hcExp0 (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg h10 hS0) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg (mul_nonneg h10 nT1R) hrel0)))
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg h20 h30) nT2R2)) hcF0)
    (fun k hk => sec7E_eQ_bound ME hh₁ hh₂ hh₃ hW hpad hshift hh₁ hle₁ ME.d1f1_exp₁ k hk r hr)
    (fun k hk => sec7E_gK_bound ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel hh₂ hh₃ hle₂ hle₃ hξ₁
      hc₁ ME.B_exp₁ k hk r hr) m hm
  have hb5 := sec7_leib_bound (a := 4 * 10 ^ 14 * ((h₁:ℝ) * (S.T₁ / S.R)))
    (b := sec7_cExp * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S + (h₂ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)) hR
    (mul_nonneg (by norm_num) (mul_nonneg h10 nT1R))
    (mul_nonneg hcExp0 (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h20 h30) nT2R2) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h20 h30) hS0) hT2.le)
        (pow_nonneg hR.le 3))))
    (fun k hk => sec7E_N_bound ME hW hpad hh₁ k hk r hr)
    (fun k hk => sec7E_eK_bound ME hh₁ hh₂ hh₃ hW hpad hshift hh₂ hh₃ hle₂ hle₃ hξ₁
      ME.B_exp₁ k hk r hr) m hm
  have hb6 := sec7_leib_bound (a := sec7_cExp * ((h₂ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 + (h₂ : ℝ) * (S.T₁ / S.R) * sec7_relErr P S))
    (b := 14 * 10 ^ 10 * ((h₁:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) hR
    (mul_nonneg hcExp0 (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg h20 hS0) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg (mul_nonneg h20 nT1R) hrel0)))
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg h10 h30) nT2R2)) hcF0)
    (fun k hk => sec7E_eQ_bound ME hh₁ hh₂ hh₃ hW hpad hshift hh₂ hle₂ ME.d1f1_exp₂ k hk r hr)
    (fun k hk => sec7E_gK_bound ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel hh₁ hh₃ hle₁ hle₃ hξ₂
      hc₂ ME.B_exp₂ k hk r hr) m hm
  have hb7 := sec7_leib_bound (a := 4 * 10 ^ 14 * ((h₂:ℝ) * (S.T₁ / S.R)))
    (b := sec7_cExp * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S + (h₁ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)) hR
    (mul_nonneg (by norm_num) (mul_nonneg h20 nT1R))
    (mul_nonneg hcExp0 (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h10 h30) nT2R2) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h10 h30) hS0) hT2.le)
        (pow_nonneg hR.le 3))))
    (fun k hk => sec7E_N_bound ME hW hpad hh₂ k hk r hr)
    (fun k hk => sec7E_eK_bound ME hh₁ hh₂ hh₃ hW hpad hshift hh₁ hh₃ hle₁ hle₃ hξ₂
      ME.B_exp₂ k hk r hr) m hm
  have hb8 := sec7_leib_bound (a := sec7_cExp * ((h₃ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 + (h₃ : ℝ) * (S.T₁ / S.R) * sec7_relErr P S))
    (b := 14 * 10 ^ 10 * ((h₁:ℝ) * (h₂:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib) hR
    (mul_nonneg hcExp0 (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg h30 hS0) hT1.le) (pow_nonneg hR.le 2))
      (mul_nonneg (mul_nonneg h30 nT1R) hrel0)))
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg h10 h20) nT2R2)) hcF0)
    (fun k hk => sec7E_eQ_bound ME hh₁ hh₂ hh₃ hW hpad hshift hh₃ hle₃ ME.d1f1_exp₃ k hk r hr)
    (fun k hk => sec7E_gK_bound ME hh₁ hh₂ hh₃ hW hpad hshift hSR hcrel hh₁ hh₂ hle₁ hle₂ hξ₃
      hc₃ ME.B_exp₃ k hk r hr) m hm
  have hb9 := sec7_leib_bound (a := 4 * 10 ^ 14 * ((h₃:ℝ) * (S.T₁ / S.R)))
    (b := sec7_cExp * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) * sec7_relErr P S + (h₁ : ℝ) * h₂ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)) hR
    (mul_nonneg (by norm_num) (mul_nonneg h30 nT1R))
    (mul_nonneg hcExp0 (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h10 h20) nT2R2) hrel0)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h10 h20) hS0) hT2.le)
        (pow_nonneg hR.le 3))))
    (fun k hk => sec7E_N_bound ME hW hpad hh₃ k hk r hr)
    (fun k hk => sec7E_eK_bound ME hh₁ hh₂ hh₃ hW hpad hshift hh₁ hh₂ hle₁ hle₂ hξ₃
      ME.B_exp₃ k hk r hr) m hm
  have hb10 := sec7E_T6_bound ME hh₁ hh₂ hh₃ hW hpad m hm r hr
  -- triangle over the ten summands
  have htri : |F m r| ≤
      |sec7E_eP3 ME m r|
      + |sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r|
      + |sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r|
      + |sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r|
      + |sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r|
      + |sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) m r|
      + |sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) m r|
      + |sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) m r|
      + |sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) m r|
      + |sec7E_T6 ME m r| := by
    simp only [hFdef]
    have t9 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) m r
      + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) m r
      + sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) m r
      + sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) m r) (sec7E_T6 ME m r)
    have t8 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) m r
      + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) m r
      + sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) m r)
      (sec7_leib (sec7E_N ME h₃) (sec7E_eK ME h₁ h₂ ξ₃) m r)
    have t7 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) m r
      + sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) m r)
      (sec7_leib (sec7E_eQ ME h₃) (sec7E_gK ME h₁ h₂ ξ₃ ((ρ₃:ℝ) - u₃)) m r)
    have t6 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r
      + sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) m r)
      (sec7_leib (sec7E_N ME h₂) (sec7E_eK ME h₁ h₃ ξ₂) m r)
    have t5 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r
      + sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r)
      (sec7_leib (sec7E_eQ ME h₂) (sec7E_gK ME h₁ h₃ ξ₂ ((ρ₂:ℝ) - u₂)) m r)
    have t4 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r
      + sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r)
      (sec7_leib (sec7E_N ME h₁) (sec7E_eK ME h₂ h₃ ξ₁) m r)
    have t3 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r
      + sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r)
      (sec7_leib (sec7E_eQ ME h₁) (sec7E_gK ME h₂ h₃ ξ₁ ((ρ₁:ℝ) - u₁)) m r)
    have t2 := abs_add_le (sec7E_eP3 ME m r
      + sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r)
      (sec7_leib (sec7E_M1 ME) (sec7E_eB0 ME) m r)
    have t1 := abs_add_le (sec7E_eP3 ME m r)
      (sec7_leib (sec7E_eA ME) (sec7E_gB ME ρ₀) m r)
    linarith
  -- assemble over the common denominator and close with the banked numeric inequality
  have hcErr : sec7_cErr = (10:ℝ) ^ 42 := by norm_num [sec7_cErr]
  have hPv1 : (1:ℝ) ≤ sec7_Pprod h₁ h₂ h₃ := by
    unfold sec7_Pprod
    have h12 : (1:ℝ) ≤ (h₁:ℝ) * h₂ := by nlinarith
    nlinarith [h12, a3]
  have hnum := sec7E_num_final (T1 := S.T₁) (T2 := S.T₂) (T3 := S.T₃) (R := S.R)
    (hS := sec7_hSum h₁ h₂ h₃) (Pv := sec7_Pprod h₁ h₂ h₃) (rel := sec7_relErr P S)
    (ind := if ρ₀ = 0 then (0:ℝ) else 1) (a := (h₁:ℝ)) (b := (h₂:ℝ)) (c := (h₃:ℝ))
    hT1 hT2 hR hSv3 hPv1 hrel0 hind0 hind1 a1 a2 a3 hle₁ hle₂ hle₃
    (by unfold sec7_Pprod; ring) (sec7_T₁_mul_T₂ S) hSR
  calc |F m r|
      ≤ (sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErr P S +
            sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₃ / S.R ^ 4)
        + 4 * ((sec7_cExp * ((sec7_hSum h₁ h₂ h₃) ^ 2 * S.T₁ / S.R ^ 2 +
              S.T₁ * sec7_relErr P S)) *
            (10 ^ 15 * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) +
              (if ρ₀ = 0 then 0 else 1) * sec7_cCarry))
        + 4 * ((10 ^ 11 * S.T₁) *
            (sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
              sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4)))
        + 4 * ((sec7_cExp * ((h₁ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
              (h₁ : ℝ) * (S.T₁ / S.R) * sec7_relErr P S)) *
            (14 * 10 ^ 10 * ((h₂:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib))
        + 4 * ((4 * 10 ^ 14 * ((h₁:ℝ) * (S.T₁ / S.R))) *
            (sec7_cExp * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
              (h₂ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)))
        + 4 * ((sec7_cExp * ((h₂ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
              (h₂ : ℝ) * (S.T₁ / S.R) * sec7_relErr P S)) *
            (14 * 10 ^ 10 * ((h₁:ℝ) * (h₃:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib))
        + 4 * ((4 * 10 ^ 14 * ((h₂:ℝ) * (S.T₁ / S.R))) *
            (sec7_cExp * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
              (h₁ : ℝ) * h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)))
        + 4 * ((sec7_cExp * ((h₃ : ℝ) * sec7_hSum h₁ h₂ h₃ * S.T₁ / S.R ^ 2 +
              (h₃ : ℝ) * (S.T₁ / S.R) * sec7_relErr P S)) *
            (14 * 10 ^ 10 * ((h₁:ℝ) * (h₂:ℝ) * (S.T₂ / S.R ^ 2)) + sec7_cFib))
        + 4 * ((4 * 10 ^ 14 * ((h₃:ℝ) * (S.T₁ / S.R))) *
            (sec7_cExp * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) * sec7_relErr P S +
              (h₁ : ℝ) * h₂ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 3)))
        + 4 * 10 ^ 22 * (sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
            (S.T₁ * S.T₂ / S.R ^ 4))) / S.R ^ m := by
        rw [add_div, add_div, add_div, add_div, add_div, add_div, add_div, add_div,
          add_div]
        exact le_trans htri (by gcongr)
    _ ≤ sec7_cErr * sec7_errScale P S h₁ h₂ h₃ ρ₀ / S.R ^ m := by
        gcongr (?_ : ℝ) / _
        rw [hcErr]
        unfold sec7_errScale
        simp only [sec7_cExp, sec7_cCarry, sec7_cFib]
        exact hnum


end Squarefree
