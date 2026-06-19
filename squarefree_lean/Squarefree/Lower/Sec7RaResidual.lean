import Squarefree.Lower.Sec7DBreveScale
import Squarefree.Lower.DefectDeriv5
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# §7 residual helpers

Lower-level analytic facts for the §7 `f₂` residual expansion.
-/

namespace Squarefree

open Set

set_option maxHeartbeats 2000000

private noncomputable def sec7_ra_hCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 2
  | 2 => -1 / 4
  | 3 => 3 / 8
  | 4 => -15 / 16
  | 5 => 105 / 32
  | 6 => -945 / 64
  | _ => 0

private noncomputable def sec7_ra_hScale : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 4
  | 2 => 3 / 8
  | 3 => 15 / 16
  | 4 => 105 / 32
  | 5 => 945 / 64
  | 6 => 10395 / 128
  | _ => 0

private noncomputable def sec7_ra_sqrtScale : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 2
  | 2 => 1 / 4
  | 3 => 3 / 8
  | 4 => 15 / 16
  | 5 => 105 / 32
  | 6 => 945 / 64
  | _ => 0

private noncomputable def sec7_ra_inv2Scale : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 24
  | 4 => 120
  | 5 => 720
  | 6 => 5040
  | _ => 0

private noncomputable def sec7_ra_hsqScale : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => 1 / 4
  | 2 => 1 / 2
  | 3 => 3 / 2
  | 4 => 6
  | 5 => 30
  | 6 => 180
  | _ => 0

private noncomputable def sec7_ra_A3Scale : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 3 / 4
  | 3 => 15 / 8
  | 4 => 105 / 16
  | 5 => 945 / 32
  | 6 => 10395 / 64
  | _ => 0

noncomputable def sec7_ra_A1Scale : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 30
  | _ => 0

private noncomputable def sec7_ra_A1Q (a t : ℝ) : ℝ :=
  a ^ 2 + 3 * a * t + 3 * t ^ 2

private noncomputable def sec7_ra_A1Qpoly (a : ℝ) : Polynomial ℝ :=
  Polynomial.C (a ^ 2) + Polynomial.C (3 * a) * Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2

private noncomputable def sec7_ra_A1P : ℕ → ℝ → ℝ → ℝ
  | 0, a, t => t ^ 2 * (a + t) ^ 2
  | 1, a, t => t * (a + t) * (a + 2 * t) *
      (2 * a ^ 2 + 3 * a * t + 3 * t ^ 2)
  | 2, a, t => 2 * (a ^ 6 + 6 * a ^ 5 * t + 15 * a ^ 4 * t ^ 2 +
      27 * a ^ 3 * t ^ 3 + 36 * a ^ 2 * t ^ 4 + 27 * a * t ^ 5 + 9 * t ^ 6)
  | 3, a, t => -6 * a ^ 4 * (a + 2 * t) * (a ^ 2 + 6 * a * t + 6 * t ^ 2)
  | 4, a, t => 24 * a ^ 4 *
      (a ^ 4 + 15 * a ^ 3 * t + 60 * a ^ 2 * t ^ 2 + 90 * a * t ^ 3 + 45 * t ^ 4)
  | 5, a, t => -1080 * a ^ 4 * t * (a + t) * (a + 2 * t) *
      (a + 3 * t) * (2 * a + 3 * t)
  | _, _, _ => 0

private noncomputable def sec7_ra_A1Ppoly : ℕ → ℝ → Polynomial ℝ
  | 0, a => Polynomial.X ^ 2 * (Polynomial.C a + Polynomial.X) ^ 2
  | 1, a => Polynomial.X * (Polynomial.C a + Polynomial.X) *
      (Polynomial.C a + Polynomial.C 2 * Polynomial.X) *
      (Polynomial.C (2 * a ^ 2) + Polynomial.C (3 * a) * Polynomial.X +
        Polynomial.C 3 * Polynomial.X ^ 2)
  | 2, a => Polynomial.C 2 * (Polynomial.C (a ^ 6) + Polynomial.C (6 * a ^ 5) *
      Polynomial.X + Polynomial.C (15 * a ^ 4) * Polynomial.X ^ 2 +
      Polynomial.C (27 * a ^ 3) * Polynomial.X ^ 3 +
      Polynomial.C (36 * a ^ 2) * Polynomial.X ^ 4 +
      Polynomial.C (27 * a) * Polynomial.X ^ 5 + Polynomial.C 9 * Polynomial.X ^ 6)
  | 3, a => Polynomial.C (-6 * a ^ 4) * (Polynomial.C a + Polynomial.C 2 * Polynomial.X) *
      (Polynomial.C (a ^ 2) + Polynomial.C (6 * a) * Polynomial.X +
        Polynomial.C 6 * Polynomial.X ^ 2)
  | 4, a => Polynomial.C (24 * a ^ 4) * (Polynomial.C (a ^ 4) +
      Polynomial.C (15 * a ^ 3) * Polynomial.X + Polynomial.C (60 * a ^ 2) *
      Polynomial.X ^ 2 + Polynomial.C (90 * a) * Polynomial.X ^ 3 +
      Polynomial.C 45 * Polynomial.X ^ 4)
  | 5, a => Polynomial.C (-1080 * a ^ 4) * Polynomial.X * (Polynomial.C a + Polynomial.X) *
      (Polynomial.C a + Polynomial.C 2 * Polynomial.X) *
      (Polynomial.C a + Polynomial.C 3 * Polynomial.X) *
      (Polynomial.C (2 * a) + Polynomial.C 3 * Polynomial.X)
  | _, _ => 0

private noncomputable def sec7_ra_A1E (X a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -a * sec7_ra_A1P k a t / (6 * X * (sec7_ra_A1Q a t) ^ (k + 1))

private theorem sec7_ra_A1Qpoly_eval (a t : ℝ) :
    (sec7_ra_A1Qpoly a).eval t = sec7_ra_A1Q a t := by
  simp [sec7_ra_A1Qpoly, sec7_ra_A1Q]

private theorem sec7_ra_A1Ppoly_eval {k : ℕ} (hk : k ≤ 5) (a t : ℝ) :
    (sec7_ra_A1Ppoly k a).eval t = sec7_ra_A1P k a t := by
  interval_cases k <;> simp [sec7_ra_A1Ppoly, sec7_ra_A1P]

private theorem sec7_ra_A1E_hasDerivAt {X a r : ℝ} {m : ℕ}
    (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) (hm : m < 5) :
    HasDerivAt (sec7_ra_A1E X a m) (sec7_ra_A1E X a (m + 1) r) r := by
  have hmle : m ≤ 5 := le_of_lt hm
  have hQpos : 0 < sec7_ra_A1Q a r := by
    unfold sec7_ra_A1Q
    positivity
  have hPraw : HasDerivAt (fun t : ℝ => sec7_ra_A1P m a t)
      ((sec7_ra_A1Ppoly m a).derivative.eval r) r := by
    have hp := (sec7_ra_A1Ppoly m a).hasDerivAt r
    have hev : (fun t : ℝ => (sec7_ra_A1Ppoly m a).eval t) =
        fun t : ℝ => sec7_ra_A1P m a t := by
      funext t
      exact sec7_ra_A1Ppoly_eval hmle a t
    simpa [hev]
      using hp
  have hP : HasDerivAt (fun t : ℝ => -a * sec7_ra_A1P m a t)
      (-a * (sec7_ra_A1Ppoly m a).derivative.eval r) r :=
    hPraw.const_mul (-a)
  have hQraw : HasDerivAt (fun t : ℝ => sec7_ra_A1Q a t)
      ((sec7_ra_A1Qpoly a).derivative.eval r) r := by
    simpa [sec7_ra_A1Qpoly_eval]
      using (sec7_ra_A1Qpoly a).hasDerivAt r
  have hden : HasDerivAt (fun t : ℝ => 6 * X * (sec7_ra_A1Q a t) ^ (m + 1))
      (6 * X * ((m + 1 : ℕ) * (sec7_ra_A1Q a r) ^ m *
        ((sec7_ra_A1Qpoly a).derivative.eval r))) r := by
    simpa [Nat.succ_eq_add_one]
      using ((hQraw.pow (m + 1)).const_mul (6 * X))
  have hmain := hP.fun_div hden (by positivity)
  convert hmain using 1
  interval_cases m <;>
    simp [sec7_ra_A1E, sec7_ra_A1P, sec7_ra_A1Q, sec7_ra_A1Ppoly,
      sec7_ra_A1Qpoly] <;>
    field_simp [hX.ne', hQpos.ne'] <;>
    simp only [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_C,
      Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero] <;>
    ring_nf

private noncomputable def sec7_ra_hsqInvScale : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => 3 / 4
  | 2 => 3
  | 3 => 15
  | 4 => 90
  | 5 => 630
  | 6 => 5040
  | _ => 0

noncomputable def sec7_ra_rhoScale : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => 5 / 4
  | 2 => 15 / 2
  | 3 => 105 / 2
  | 4 => 420
  | 5 => 3780
  | 6 => 37800
  | _ => 0

noncomputable def sec7_ra_B3q (X a j : ℝ) (d : ℝ) : ℝ :=
  dBreve X a (Ffun X a d + j)

private theorem sec7_ra_B3q_zero {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    sec7_ra_B3q X a 0 d = d := by
  simpa [sec7_ra_B3q] using dBreve_spec (X := X) (a := a) (d := d) hX ha hd

theorem sec7_ra_B3q_Ffun_eq {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    Ffun P.X a (sec7_ra_B3q P.X a j d) = Ffun P.X a d + j := by
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a) (t := Ffun P.X a d + j)
      hAD ha_lo ha_hi hshift
  simpa [sec7_ra_B3q] using himg

theorem sec7_ra_B3q_close_Icc {X a d j : ℝ}
    (hclose : |sec7_ra_B3q X a j d - d| ≤ d / 100) :
    (99 / 100 : ℝ) * d ≤ sec7_ra_B3q X a j d ∧
      sec7_ra_B3q X a j d ≤ (101 / 100 : ℝ) * d := by
  rcases abs_le.mp hclose with ⟨hlo, hhi⟩
  constructor
  · have hbase : d - d / 100 ≤ sec7_ra_B3q X a j d := by linarith
    nlinarith
  · have hbase : sec7_ra_B3q X a j d ≤ d + d / 100 := by linarith
    nlinarith

theorem sec7_ra_Ffun_mvt_local {X a p q : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hpq : p < q) :
    ∃ c, p < c ∧ c < q ∧
      Ffun X a q - Ffun X a p = deriv (fun t => Ffun X a t) c * (q - p) := by
  have hcont : ContinuousOn (fun t => Ffun X a t) (Set.Icc p q) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hp hs.1
    exact (Ffun_contDiffAt (X := X) (a := a) (d := s) (ne_of_gt hs0)
      (by positivity)).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ioo p q,
      HasDerivAt (fun t => Ffun X a t) (deriv (fun t => Ffun X a t) s) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hp hs.1
    have h := Ffun_hasDerivAt_d X a s (ne_of_gt hs0) (by positivity)
    rw [h.deriv]
    exact h
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope (fun t => Ffun X a t) _ hpq hcont hderiv
  refine ⟨c, hc.1, hc.2, ?_⟩
  rw [hslope]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hpq))]

private theorem sec7_ra_Ffun_deriv_mvt_local {X a p q : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hpq : p < q) :
    ∃ c, p < c ∧ c < q ∧
      deriv (fun t => Ffun X a t) q - deriv (fun t => Ffun X a t) p =
        iteratedDeriv 2 (fun t => Ffun X a t) c * (q - p) := by
  let g : ℝ → ℝ := fun t => -2 * X / t ^ 3 + 2 * X / (t + a) ^ 3
  have hcont : ContinuousOn g (Set.Icc p q) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hp hs.1
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hsa : s + a ≠ 0 := ne_of_gt (add_pos hspos ha)
    have hleft : ContinuousAt (fun t : ℝ => -2 * X / t ^ 3) s := by
      exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 hs0)
    have hright : ContinuousAt (fun t : ℝ => 2 * X / (t + a) ^ 3) s := by
      exact continuousAt_const.div ((continuousAt_id.add continuousAt_const).pow 3)
        (pow_ne_zero 3 hsa)
    simpa [g] using (hleft.add hright).continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ioo p q,
      HasDerivAt g (iteratedDeriv 2 (fun t => Ffun X a t) s) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hp hs.1
    have hraw := Ffun_hasDerivAt2_d X a s (ne_of_gt hs0) (by positivity)
    simpa [g, Ffun_iteratedDeriv2_d X a s (ne_of_gt hs0) (by positivity)] using hraw
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ hpq hcont hderiv
  refine ⟨c, hc.1, hc.2, ?_⟩
  have hpne : p ≠ 0 := ne_of_gt hp
  have hqpos : 0 < q := lt_trans hp hpq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hpder := (Ffun_hasDerivAt_d X a p hpne (by positivity)).deriv
  have hqder := (Ffun_hasDerivAt_d X a q hqne (by positivity)).deriv
  have hgdiff : g q - g p = iteratedDeriv 2 (fun t => Ffun X a t) c * (q - p) := by
    rw [hslope]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hpq))]
  simpa [g, hpder, hqder] using hgdiff

private theorem sec7_ra_Ffun_deriv1_lower_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    X * a / (1000 * d ^ 4) ≤ |deriv (fun t => Ffun X a t) z| := by
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ 11 * z := by nlinarith
  obtain ⟨hlow, _hhigh⟩ :=
    Ffun_deriv1_abs_bounds (X := X) (a := a) (d := z) hX ha hzpos haz
  have hzpow_le : z ^ 4 ≤ ((101 / 100 : ℝ) * d) ^ 4 :=
    pow_le_pow_left₀ hzpos.le hzhi 4
  have hden_le : 288 * z ^ 4 ≤ 1000 * d ^ 4 := by
    calc
      288 * z ^ 4 ≤ 288 * (((101 / 100 : ℝ) * d) ^ 4) := by gcongr
      _ = (288 * (101 / 100 : ℝ) ^ 4) * d ^ 4 := by ring
      _ ≤ 1000 * d ^ 4 := by
        gcongr
        norm_num
  have hcmp : X * a / (1000 * d ^ 4) ≤ X * a / (288 * z ^ 4) := by
    have hnum_nonneg : 0 ≤ X * a := by positivity
    have hden_left : 0 < 288 * z ^ 4 := by positivity
    have hden_right : 0 < 1000 * d ^ 4 := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hden_right hden_left).2 hden_le) hnum_nonneg
  exact le_trans hcmp hlow

private theorem sec7_ra_Ffun_deriv1_lower_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    X * a / d ^ 4 ≤ |deriv (fun t => Ffun X a t) z| := by
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have hza_pos : 0 < z + a := by positivity
  rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := z) hX ha hzpos]
  have hpoly_lo : 6 * z ^ 2 ≤ 2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) := by
    nlinarith [sq_nonneg a, mul_nonneg ha.le hzpos.le]
  have hza_hi : z + a ≤ (151 / 100 : ℝ) * d := by nlinarith
  have hza_pow : (z + a) ^ 3 ≤ ((151 / 100 : ℝ) * d) ^ 3 :=
    pow_le_pow_left₀ hza_pos.le hza_hi 3
  have hz_den_piece : z * (z + a) ^ 3 ≤ 6 * d ^ 4 := by
    calc
      z * (z + a) ^ 3 ≤ ((101 / 100 : ℝ) * d) * (((151 / 100 : ℝ) * d) ^ 3) := by
        exact mul_le_mul hzhi hza_pow (by positivity) (by positivity)
      _ = ((101 / 100 : ℝ) * (151 / 100 : ℝ) ^ 3) * d ^ 4 := by ring
      _ ≤ 6 * d ^ 4 := by
        gcongr
        norm_num
  have hden_core :
      z ^ 3 * (z + a) ^ 3 ≤ 2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by
    calc
      z ^ 3 * (z + a) ^ 3 = z ^ 2 * (z * (z + a) ^ 3) := by ring
      _ ≤ z ^ 2 * (6 * d ^ 4) := by gcongr
      _ = (6 * z ^ 2) * d ^ 4 := by ring
      _ ≤ 2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by gcongr
  rw [div_le_div_iff₀ (pow_pos hd 4) (by positivity : 0 < z ^ 3 * (z + a) ^ 3)]
  calc
    X * a * (z ^ 3 * (z + a) ^ 3)
        ≤ X * a * (2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4) :=
      mul_le_mul_of_nonneg_left hden_core (by positivity)
    _ = 2 * X * a * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by ring

private theorem sec7_ra_Ffun_deriv2_upper_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |iteratedDeriv 2 (fun t => Ffun X a t) z| ≤ 200 * X * a / d ^ 5 := by
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  rw [Ffun_deriv2_abs_eq (X := X) (a := a) (d := z) hX ha hzpos]
  have ha_le_d : a ≤ d := by nlinarith
  have hz_le_2d : z ≤ 2 * d := by nlinarith
  have ha_sq : a ^ 2 ≤ (d / 2) ^ 2 := pow_le_pow_left₀ ha.le ha2 2
  have hz_sq : z ^ 2 ≤ ((101 / 100 : ℝ) * d) ^ 2 := pow_le_pow_left₀ hzpos.le hzhi 2
  have haz : a * z ≤ (d / 2) * ((101 / 100 : ℝ) * d) := by
    exact mul_le_mul ha2 hzhi hzpos.le (by positivity)
  have hquad : a ^ 2 + 2 * a * z + 2 * z ^ 2 ≤ 4 * d ^ 2 := by
    nlinarith only [ha_sq, hz_sq, haz]
  have hlin : a + 2 * z ≤ 3 * d := by nlinarith
  have hnum_core :
      6 * X * a * (a + 2 * z) * (a ^ 2 + 2 * a * z + 2 * z ^ 2)
        ≤ 72 * X * a * d ^ 3 := by
    calc
      6 * X * a * (a + 2 * z) * (a ^ 2 + 2 * a * z + 2 * z ^ 2)
          ≤ 6 * X * a * (3 * d) * (4 * d ^ 2) := by
        gcongr
      _ = 72 * X * a * d ^ 3 := by ring
  have hzpow4_lo : ((99 / 100 : ℝ) * d) ^ 4 ≤ z ^ 4 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (99 / 100 : ℝ) * d) hzlo 4
  have hza_pow4_lo : z ^ 4 ≤ (z + a) ^ 4 :=
    pow_le_pow_left₀ hzpos.le (by linarith) 4
  have hden_half : d ^ 8 ≤ 2 * (z ^ 4 * (z + a) ^ 4) := by
    have hden_lo :
        (((99 / 100 : ℝ) * d) ^ 4) * (((99 / 100 : ℝ) * d) ^ 4) ≤
          z ^ 4 * (z + a) ^ 4 := by
      exact mul_le_mul hzpow4_lo (le_trans hzpow4_lo hza_pow4_lo) (by positivity) (by positivity)
    calc
      d ^ 8 ≤ 2 * ((((99 / 100 : ℝ) * d) ^ 4) * (((99 / 100 : ℝ) * d) ^ 4)) := by
        rw [show (((99 / 100 : ℝ) * d) ^ 4) * (((99 / 100 : ℝ) * d) ^ 4) =
            (99 / 100 : ℝ) ^ 8 * d ^ 8 by ring]
        have hd8_nonneg : 0 ≤ d ^ 8 := by positivity
        nlinarith only [hd8_nonneg]
      _ ≤ 2 * (z ^ 4 * (z + a) ^ 4) := by gcongr
  have hden_pos : 0 < z ^ 4 * (z + a) ^ 4 := by positivity
  rw [div_le_div_iff₀ hden_pos (pow_pos hd 5)]
  calc
    (6 * X * a * (a + 2 * z) * (a ^ 2 + 2 * a * z + 2 * z ^ 2)) * d ^ 5
        ≤ (72 * X * a * d ^ 3) * d ^ 5 := by gcongr
    _ = 72 * X * a * d ^ 8 := by ring
    _ ≤ 200 * X * a * (z ^ 4 * (z + a) ^ 4) := by
      have hmain := mul_le_mul_of_nonneg_left hden_half (by positivity : 0 ≤ 100 * X * a)
      have hmain' : 100 * X * a * d ^ 8 ≤ 200 * X * a * (z ^ 4 * (z + a) ^ 4) := by
        calc
          100 * X * a * d ^ 8 ≤ 100 * X * a * (2 * (z ^ 4 * (z + a) ^ 4)) := hmain
          _ = 200 * X * a * (z ^ 4 * (z + a) ^ 4) := by ring
      have h72 : 72 * X * a * d ^ 8 ≤ 100 * X * a * d ^ 8 := by
        gcongr
        norm_num
      exact le_trans h72 hmain'

theorem sec7_ra_Ffun_upper_base_sharp {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    |deriv (fun t => Ffun X a t) d| ≤ 7 * X * a / d ^ 4 ∧
      |iteratedDeriv 2 (fun t => Ffun X a t) d| ≤ 26 * X * a / d ^ 5 ∧
      |iteratedDeriv 3 (fun t => Ffun X a t) d| ≤ 128 * X * a / d ^ 6 ∧
      |iteratedDeriv 4 (fun t => Ffun X a t) d| ≤ 800 * X * a / d ^ 7 ∧
      |iteratedDeriv 5 (fun t => Ffun X a t) d| ≤ 6000 * X * a / d ^ 8 := by
  have hXa_nonneg : 0 ≤ X * a := (mul_pos hX ha).le
  have hda_pos : 0 < d + a := by positivity
  have hF1 : |deriv (fun t => Ffun X a t) d| ≤ 7 * X * a / d ^ 4 := by
    rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := d) hX ha hd]
    have hpoly : 2 * d * (a ^ 2 + 3 * a * d + 3 * d ^ 2) ≤ 7 * (d + a) ^ 3 := by
      have hnon : 0 ≤
          7 * (d + a) ^ 3 - 2 * d * (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by
        ring_nf
        positivity
      linarith
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 3 * (d + a) ^ 3)
      (pow_pos hd 4)]
    calc
      (2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) * d ^ 4
          = (X * a * d ^ 3) * (2 * d * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) := by
            ring
      _ ≤ (X * a * d ^ 3) * (7 * (d + a) ^ 3) := by
            exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 7 * X * a * (d ^ 3 * (d + a) ^ 3) := by ring
  have hF2 :
      |iteratedDeriv 2 (fun t => Ffun X a t) d| ≤ 26 * X * a / d ^ 5 := by
    rw [Ffun_deriv2_abs_eq (X := X) (a := a) (d := d) hX ha hd]
    have hpoly :
        6 * d * (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2) ≤
          26 * (d + a) ^ 4 := by
      have hnon : 0 ≤ 26 * (d + a) ^ 4 -
          6 * d * (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2) := by
        ring_nf
        positivity
      linarith
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 4 * (d + a) ^ 4)
      (pow_pos hd 5)]
    calc
      (6 * X * a * (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2)) * d ^ 5
          = (X * a * d ^ 4) *
              (6 * d * (a + 2 * d) * (a ^ 2 + 2 * a * d + 2 * d ^ 2)) := by
            ring
      _ ≤ (X * a * d ^ 4) * (26 * (d + a) ^ 4) := by
            exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 26 * X * a * (d ^ 4 * (d + a) ^ 4) := by ring
  have hF3 :
      |iteratedDeriv 3 (fun t => Ffun X a t) d| ≤ 128 * X * a / d ^ 6 := by
    rw [Ffun_deriv3_abs_eq (X := X) (a := a) (d := d) hX ha hd]
    have hpoly :
        24 * d *
            (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 +
              5 * d ^ 4) ≤ 128 * (d + a) ^ 5 := by
      have hnon : 0 ≤ 128 * (d + a) ^ 5 -
          24 * d *
            (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 +
              5 * d ^ 4) := by
        ring_nf
        positivity
      linarith
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 5 * (d + a) ^ 5)
      (pow_pos hd 6)]
    calc
      (24 * X * a *
          (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 + 10 * a * d ^ 3 +
            5 * d ^ 4)) * d ^ 6
          = (X * a * d ^ 5) *
              (24 * d *
                (a ^ 4 + 5 * a ^ 3 * d + 10 * a ^ 2 * d ^ 2 +
                  10 * a * d ^ 3 + 5 * d ^ 4)) := by
            ring
      _ ≤ (X * a * d ^ 5) * (128 * (d + a) ^ 5) := by
            exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 128 * X * a * (d ^ 5 * (d + a) ^ 5) := by ring
  have hF4 :
      |iteratedDeriv 4 (fun t => Ffun X a t) d| ≤ 800 * X * a / d ^ 7 := by
    rw [Ffun_deriv4_abs_eq (X := X) (a := a) (d := d) hX ha hd]
    have hpoly :
        120 * d * (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) *
            (a ^ 2 + 3 * a * d + 3 * d ^ 2) ≤ 800 * (d + a) ^ 6 := by
      have hnon : 0 ≤ 800 * (d + a) ^ 6 -
          120 * d * (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) *
            (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by
        ring_nf
        positivity
      linarith
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 6 * (d + a) ^ 6)
      (pow_pos hd 7)]
    calc
      (120 * X * a * (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) *
          (a ^ 2 + 3 * a * d + 3 * d ^ 2)) * d ^ 7
          = (X * a * d ^ 6) *
              (120 * d * (a + 2 * d) * (a ^ 2 + a * d + d ^ 2) *
                (a ^ 2 + 3 * a * d + 3 * d ^ 2)) := by
            ring
      _ ≤ (X * a * d ^ 6) * (800 * (d + a) ^ 6) := by
            exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 800 * X * a * (d ^ 6 * (d + a) ^ 6) := by ring
  have hF5 :
      |iteratedDeriv 5 (fun t => Ffun X a t) d| ≤ 6000 * X * a / d ^ 8 := by
    rw [Ffun_deriv5_abs_eq (X := X) (a := a) (d := d) hX ha hd]
    have hpoly :
        720 * d *
            (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
              + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6) ≤
          6000 * (d + a) ^ 7 := by
      have hnon : 0 ≤ 6000 * (d + a) ^ 7 -
          720 * d *
            (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
              + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6) := by
        ring_nf
        positivity
      linarith
    rw [div_le_div_iff₀ (by positivity : 0 < d ^ 7 * (d + a) ^ 7)
      (pow_pos hd 8)]
    calc
      (720 * X * a *
          (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 + 35 * a ^ 3 * d ^ 3
            + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 + 7 * d ^ 6)) * d ^ 8
          = (X * a * d ^ 7) *
              (720 * d *
                (a ^ 6 + 7 * a ^ 5 * d + 21 * a ^ 4 * d ^ 2 +
                  35 * a ^ 3 * d ^ 3 + 35 * a ^ 2 * d ^ 4 + 21 * a * d ^ 5 +
                  7 * d ^ 6)) := by
            ring
      _ ≤ (X * a * d ^ 7) * (6000 * (d + a) ^ 7) := by
            exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 6000 * X * a * (d ^ 7 * (d + a) ^ 7) := by ring
  exact ⟨hF1, hF2, hF3, hF4, hF5⟩

private theorem sec7_ra_Ffun_deriv1_lower_25 {X a z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hz : 0 < z) (haz : a ≤ (51 / 100 : ℝ) * z) :
    (5 / 2 : ℝ) * X * a / z ^ 4 ≤ |deriv (fun t => Ffun X a t) z| := by
  rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := z) hX ha hz]
  have hz2_nonneg : 0 ≤ z ^ 2 := by positivity
  have hz3_nonneg : 0 ≤ z ^ 3 := by positivity
  have ha_z2 : a * z ^ 2 ≤ (51 / 100 : ℝ) * z ^ 3 := by
    calc
      a * z ^ 2 ≤ ((51 / 100 : ℝ) * z) * z ^ 2 :=
        mul_le_mul_of_nonneg_right haz hz2_nonneg
      _ = (51 / 100 : ℝ) * z ^ 3 := by ring
  have ha2 : a ^ 2 ≤ ((51 / 100 : ℝ) * z) ^ 2 :=
    pow_le_pow_left₀ ha.le haz 2
  have ha2_z : a ^ 2 * z ≤ (51 / 100 : ℝ) ^ 2 * z ^ 3 := by
    calc
      a ^ 2 * z ≤ (((51 / 100 : ℝ) * z) ^ 2) * z :=
        mul_le_mul_of_nonneg_right ha2 hz.le
      _ = (51 / 100 : ℝ) ^ 2 * z ^ 3 := by ring
  have ha3 : a ^ 3 ≤ ((51 / 100 : ℝ) * z) ^ 3 :=
    pow_le_pow_left₀ ha.le haz 3
  have ha3' : a ^ 3 ≤ (51 / 100 : ℝ) ^ 3 * z ^ 3 := by
    simpa [mul_pow] using ha3
  have hbad :
      3 * a * z ^ 2 + 11 * a ^ 2 * z + 5 * a ^ 3 ≤ 7 * z ^ 3 := by
    have hconst :
        3 * (51 / 100 : ℝ) + 11 * (51 / 100 : ℝ) ^ 2 +
            5 * (51 / 100 : ℝ) ^ 3 ≤ 7 := by
      norm_num
    nlinarith only [ha_z2, ha2_z, ha3', hconst, hz3_nonneg]
  have hpoly :
      5 * (z + a) ^ 3 ≤ 4 * z * (a ^ 2 + 3 * a * z + 3 * z ^ 2) := by
    have hnon : 0 ≤
        4 * z * (a ^ 2 + 3 * a * z + 3 * z ^ 2) - 5 * (z + a) ^ 3 := by
      ring_nf
      nlinarith only [hbad]
    linarith
  rw [div_le_div_iff₀ (pow_pos hz 4) (by positivity : 0 < z ^ 3 * (z + a) ^ 3)]
  calc
    ((5 / 2 : ℝ) * X * a) * (z ^ 3 * (z + a) ^ 3)
        = (X * a * z ^ 3 / 2) * (5 * (z + a) ^ 3) := by ring
    _ ≤ (X * a * z ^ 3 / 2) *
          (4 * z * (a ^ 2 + 3 * a * z + 3 * z ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (2 * X * a * (a ^ 2 + 3 * a * z + 3 * z ^ 2)) * z ^ 4 := by ring

private theorem sec7_ra_B3_qdiff_sharp {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3q P.X a j d - d| ≤ |j| * d ^ 4 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hCpos : 0 < P.X * a / d ^ 4 := by
    exact div_pos (mul_pos P.X_pos ha0) (pow_pos hd 4)
  have hscale_eq :
      |j| / (P.X * a / d ^ 4) = |j| * d ^ 4 / (P.X * a) := by
    field_simp [P.X_pos.ne', ne_of_gt ha0, ne_of_gt hd]
  by_cases hsame : qd = d
  · rw [hsame, sub_self, abs_zero]
    exact div_nonneg (by positivity) (le_of_lt (mul_pos P.X_pos ha0))
  have hprod : P.X * a / d ^ 4 * |qd - d| ≤ |j| := by
    rcases lt_or_gt_of_ne hsame with hlt | hlt
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := qd) (q := d) ha0
          (lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1) hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := le_trans hqwin.1 (le_of_lt hc_lo)
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) (by nlinarith)
      have hder :=
        sec7_ra_Ffun_deriv1_lower_sharp_close (X := P.X) (a := a) (d := d) (z := c)
          P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hj : j = -(Ffun P.X a d - Ffun P.X a qd) := by
          rw [hqspec]
          ring
        rw [hj, abs_neg, hc_mvt, abs_mul, abs_sub_comm]
      rw [hj_abs]
      exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := d) (q := qd) ha0 hd hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := by nlinarith
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) hqwin.2
      have hder :=
        sec7_ra_Ffun_deriv1_lower_sharp_close (X := P.X) (a := a) (d := d) (z := c)
          P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hj : j = Ffun P.X a qd - Ffun P.X a d := by
          rw [hqspec]
          ring
        rw [hj, hc_mvt, abs_mul]
      rw [hj_abs]
      exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
  calc
    |qd - d| ≤ |j| / (P.X * a / d ^ 4) := by
      rw [le_div_iff₀ hCpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    _ = |j| * d ^ 4 / (P.X * a) := hscale_eq

private noncomputable def sec7_ra_B3SharpScale : ℕ → ℝ
  | 0 => 1000
  | 1 => 1000
  | 2 => 10 ^ 4
  | 3 => 10 ^ 6
  | 4 => 10 ^ 7
  | 5 => 10 ^ 7
  | _ => 0

private theorem sec7_ra_B3_bound_sharp_k0 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 0 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScale 0 * |j| * d ^ 4 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hiter0 :
      iteratedDeriv 0 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d = qd - d := by
    simp [hqd_def, sec7_ra_B3q]
  have hCpos : 0 < P.X * a / (1000 * d ^ 4) := by
    exact div_pos (mul_pos P.X_pos ha0) (by positivity)
  have hscale_eq :
      |j| / (P.X * a / (1000 * d ^ 4)) =
        sec7_ra_B3SharpScale 0 * |j| * d ^ 4 / (P.X * a) := by
    simp [sec7_ra_B3SharpScale]
    field_simp [P.X_pos.ne', ne_of_gt ha0, ne_of_gt hd]
  by_cases hsame : qd = d
  · rw [hiter0, hsame, sub_self, abs_zero]
    simp [sec7_ra_B3SharpScale]
    exact div_nonneg (by positivity) (le_of_lt (mul_pos P.X_pos ha0))
  have hprod :
      P.X * a / (1000 * d ^ 4) * |qd - d| ≤ |j| := by
    rcases lt_or_gt_of_ne hsame with hlt | hlt
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := qd) (q := d) ha0
          (lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1) hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := le_trans hqwin.1 (le_of_lt hc_lo)
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) (by nlinarith)
      have hder :=
        sec7_ra_Ffun_deriv1_lower_close (X := P.X) (a := a) (d := d) (z := c)
          P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hj : j = -(Ffun P.X a d - Ffun P.X a qd) := by
          rw [hqspec]
          ring
        rw [hj, abs_neg, hc_mvt, abs_mul, abs_sub_comm]
      rw [hj_abs]
      exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := d) (q := qd) ha0 hd hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := by nlinarith
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) hqwin.2
      have hder :=
        sec7_ra_Ffun_deriv1_lower_close (X := P.X) (a := a) (d := d) (z := c)
          P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hj : j = Ffun P.X a qd - Ffun P.X a d := by
          rw [hqspec]
          ring
        rw [hj, hc_mvt, abs_mul]
      rw [hj_abs]
      exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
  rw [hiter0]
  calc
    |qd - d| ≤ |j| / (P.X * a / (1000 * d ^ 4)) := by
      rw [le_div_iff₀ hCpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    _ = sec7_ra_B3SharpScale 0 * |j| * d ^ 4 / (P.X * a) := hscale_eq

private noncomputable def sec7_ra_B3Scale : ℕ → ℝ
  | 0 => 10 ^ 20
  | 1 => 10 ^ 40
  | 2 => 10 ^ 120
  | 3 => 10 ^ 130
  | 4 => 10 ^ 140
  | 5 => 10 ^ 143
  | _ => 0

private noncomputable def sec7_ra_B3HScale : ℕ → ℝ
  | 1 => sec7_cPh
  | 2 => 10 ^ 80
  | 3 => 10 ^ 100
  | 4 => 10 ^ 100
  | 5 => 10 ^ 100
  | _ => 0

private theorem sec7_ra_XA_div_D3_eq_F {P : Globals} (S : Scale P) :
    P.X * S.A / S.D ^ 3 = S.F := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  rw [Scale.A, Scale.D, Scale.F, P.X_eq_G_mul_H_pow_five]
  field_simp

private theorem sec7_ra_B3_k0_scale {P : Globals} {S : Scale P} {a d : ℝ}
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d) :
    sec7_cPh * S.D / S.F ≤ sec7_ra_B3Scale 0 * d ^ 4 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hd_lo
  have hDle : S.D ≤ 16 * d := by linarith [hd_lo]
  have hD4 : S.D ^ 4 ≤ (16 * d) ^ 4 := pow_le_pow_left₀ hDpos.le hDle 4
  have hD4' : S.D ^ 4 ≤ 16 ^ 4 * d ^ 4 := by
    calc
      S.D ^ 4 ≤ (16 * d) ^ 4 := hD4
      _ = 16 ^ 4 * d ^ 4 := by ring
  have hprod : a * S.D ^ 4 ≤ (11 * S.A) * (16 ^ 4 * d ^ 4) :=
    mul_le_mul ha_hi hD4' (by positivity) (by positivity)
  have hconst : sec7_cPh * (11 * 16 ^ 4) ≤ sec7_ra_B3Scale 0 := by
    norm_num [sec7_cPh, sec7_ra_B3Scale]
  have hleft_nonneg : 0 ≤ sec7_cPh * P.X :=
    mul_nonneg sec7_cPh_pos.le P.X_pos.le
  have hright_nonneg : 0 ≤ P.X * S.A * d ^ 4 :=
    mul_nonneg (mul_nonneg P.X_pos.le hApos.le) (pow_nonneg hd0.le 4)
  have hnum :
      sec7_cPh * S.D ^ 4 * (P.X * a) ≤
        sec7_ra_B3Scale 0 * d ^ 4 * (P.X * S.A) := by
    calc
      sec7_cPh * S.D ^ 4 * (P.X * a)
          = (sec7_cPh * P.X) * (a * S.D ^ 4) := by ring
      _ ≤ (sec7_cPh * P.X) * ((11 * S.A) * (16 ^ 4 * d ^ 4)) :=
          mul_le_mul_of_nonneg_left hprod hleft_nonneg
      _ = (sec7_cPh * (11 * 16 ^ 4)) * (P.X * S.A * d ^ 4) := by ring
      _ ≤ sec7_ra_B3Scale 0 * (P.X * S.A * d ^ 4) :=
          mul_le_mul_of_nonneg_right hconst hright_nonneg
      _ = sec7_ra_B3Scale 0 * d ^ 4 * (P.X * S.A) := by ring
  calc
    sec7_cPh * S.D / S.F
        = sec7_cPh * S.D ^ 4 / (P.X * S.A) := by
          rw [← sec7_ra_XA_div_D3_eq_F S]
          field_simp [P.X_pos.ne', hApos.ne', hDpos.ne']
    _ ≤ sec7_ra_B3Scale 0 * d ^ 4 / (P.X * a) := by
          rw [div_le_div_iff₀ (mul_pos P.X_pos hApos) (mul_pos P.X_pos ha0)]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hnum

private theorem sec7_ra_B3_bound_k0 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 0 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3Scale 0 * |j| * d ^ 4 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < S.D / 16) hd_lo
  set C : ℝ := sec7_cPh * S.D / S.F with hC_def
  set g : ℝ → ℝ := fun s => dBreve P.X a (Ffun P.X a d + s) with hg_def
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      HasDerivAt g (dBreve' P.X a (Ffun P.X a d + s)) s := by
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, _hlo, _hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hdb :=
      dBreve_hasDerivAt_Ffun (X := P.X) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) P.X_pos ha0 dBreve_pos
    have hdb_at : HasDerivAt (dBreve P.X a)
        (dBreve' P.X a (Ffun P.X a d + s)) (Ffun P.X a d + s) := by
      simpa [himg] using hdb
    have hlin : HasDerivAt (fun y : ℝ => Ffun P.X a d + y) 1 s := by
      simpa using (hasDerivAt_id s).const_add (Ffun P.X a d)
    have hcomp := hdb_at.comp s hlin
    simpa [g, hg_def, himg] using hcomp
  have hbound : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      |dBreve' P.X a (Ffun P.X a d + s)| ≤ C := by
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    have hscale :=
      (dBreve_sec7_tWin_scale (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin).1.2
    rw [show P.H * S.Δ = S.D by rfl] at hscale
    rw [hC_def, le_div_iff₀ hFpos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale
  have hmvt :=
    (convex_uIcc (0 : ℝ) j).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hderiv s hs).hasDerivWithinAt)
      (fun s hs => by simpa [Real.norm_eq_abs] using hbound s hs)
      (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hmvt_abs : |g j - g 0| ≤ C * |j| := by
    simpa [Real.norm_eq_abs] using hmvt
  have hg0 : g 0 = d := by
    rw [hg_def]
    simpa using dBreve_spec P.X_pos ha0 hd0
  have hscaleC : C ≤ sec7_ra_B3Scale 0 * d ^ 4 / (P.X * a) := by
    simpa [hC_def] using
      sec7_ra_B3_k0_scale (P := P) (S := S) (a := a) (d := d)
        ha_lo ha_hi hd_lo
  have hmain : |g j - d| ≤ sec7_ra_B3Scale 0 * |j| * d ^ 4 / (P.X * a) := by
    calc
      |g j - d| = |g j - g 0| := by rw [hg0]
      _ ≤ C * |j| := hmvt_abs
      _ ≤ (sec7_ra_B3Scale 0 * d ^ 4 / (P.X * a)) * |j| :=
          mul_le_mul_of_nonneg_right hscaleC (abs_nonneg j)
      _ = sec7_ra_B3Scale 0 * |j| * d ^ 4 / (P.X * a) := by ring
  simpa [g, hg_def, iteratedDeriv_zero] using hmain

theorem sec7_ra_B3_bound_k0_public {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd_lo : S.D / 16 ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 0 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ (10 ^ 20 : ℝ) * |j| * d ^ 4 / (P.X * a) := by
  simpa [sec7_ra_B3Scale] using
    sec7_ra_B3_bound_k0 (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd_lo hseg

noncomputable def sec7_ra_dBreveD (X a : ℝ) : ℕ → ℝ → ℝ
  | 0 => dBreve X a
  | 1 => dBreve' X a
  | 2 => dBreve'' X a
  | 3 => dBreve''' X a
  | 4 => dBreve'''' X a
  | 5 => dBreve''''' X a
  | 6 => dBreve'''''' X a
  | _ => fun _ => 0

noncomputable def sec7_ra_B3H (X a j : ℝ) (l : ℕ) (d : ℝ) : ℝ :=
  sec7_ra_dBreveD X a l (Ffun X a d + j) -
    sec7_ra_dBreveD X a l (Ffun X a d)

private theorem sec7_ra_dBreve_contDiffAt5_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 5 (dBreve X a) (Ffun X a d) := by
  have hda : d + a ≠ 0 := by positivity
  have hfcd : ContDiffAt ℝ 5 (fun t => Ffun X a t) d :=
    Ffun_contDiffAt5 (X := X) (a := a) (d := d) (ne_of_gt hd) hda
  have hraw : HasDerivAt (fun t => Ffun X a t)
      (-2 * X / d ^ 3 + 2 * X / (d + a) ^ 3) d :=
    Ffun_hasDerivAt_d X a d (ne_of_gt hd) hda
  have hfder : HasDerivAt (fun t => Ffun X a t)
      (deriv (fun t => Ffun X a t) d) d := by
    rw [hraw.deriv]
    exact hraw
  have hder_ne : deriv (fun t => Ffun X a t) d ≠ 0 := by
    have hpos : 0 < |deriv (fun t => Ffun X a t) d| := by
      rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := d) hX ha hd]
      positivity
    exact abs_pos.mp hpos
  let e : ℝ ≃L[ℝ] ℝ :=
    (ContinuousLinearEquiv.unitsEquivAut ℝ)
      (Units.mk0 (deriv (fun t => Ffun X a t) d) hder_ne)
  have hf' : HasFDerivAt (fun t => Ffun X a t) (e : ℝ →L[ℝ] ℝ) d := by
    simpa [e] using hfder.hasFDerivAt_equiv hder_ne
  have hn : ((5 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have hsmooth : ContDiffAt ℝ 5 (hfcd.localInverse hf' hn) (Ffun X a d) :=
    hfcd.to_localInverse hf' hn
  have hleft : ∀ᶠ x in nhds d, dBreve X a (Ffun X a x) = x := by
    filter_upwards [eventually_gt_nhds hd] with x hx
    exact dBreve_spec (X := X) (a := a) (d := x) hX ha hx
  have hstrict : HasStrictFDerivAt (fun t => Ffun X a t) (e : ℝ →L[ℝ] ℝ) d :=
    hfcd.hasStrictFDerivAt' hf' hn
  have heq : dBreve X a =ᶠ[nhds (Ffun X a d)] hfcd.localInverse hf' hn := by
    simpa [ContDiffAt.localInverse] using hstrict.localInverse_unique (g := dBreve X a) hleft
  exact hsmooth.congr_of_eventuallyEq heq

theorem sec7_ra_dBreve_contDiffAt5_Ffun_public {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 5 (dBreve X a) (Ffun X a d) :=
  sec7_ra_dBreve_contDiffAt5_Ffun hX ha hd

private theorem sec7_ra_dBreve_contDiffAt6_Ffun {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 6 (dBreve X a) (Ffun X a d) := by
  have hda : d + a ≠ 0 := by positivity
  have hfcd : ContDiffAt ℝ 6 (fun t => Ffun X a t) d :=
    Ffun_contDiffAt6 (X := X) (a := a) (d := d) (ne_of_gt hd) hda
  have hraw : HasDerivAt (fun t => Ffun X a t)
      (-2 * X / d ^ 3 + 2 * X / (d + a) ^ 3) d :=
    Ffun_hasDerivAt_d X a d (ne_of_gt hd) hda
  have hfder : HasDerivAt (fun t => Ffun X a t)
      (deriv (fun t => Ffun X a t) d) d := by
    rw [hraw.deriv]
    exact hraw
  have hder_ne : deriv (fun t => Ffun X a t) d ≠ 0 := by
    have hpos : 0 < |deriv (fun t => Ffun X a t) d| := by
      rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := d) hX ha hd]
      positivity
    exact abs_pos.mp hpos
  let e : ℝ ≃L[ℝ] ℝ :=
    (ContinuousLinearEquiv.unitsEquivAut ℝ)
      (Units.mk0 (deriv (fun t => Ffun X a t) d) hder_ne)
  have hf' : HasFDerivAt (fun t => Ffun X a t) (e : ℝ →L[ℝ] ℝ) d := by
    simpa [e] using hfder.hasFDerivAt_equiv hder_ne
  have hn : ((6 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have hsmooth : ContDiffAt ℝ 6 (hfcd.localInverse hf' hn) (Ffun X a d) :=
    hfcd.to_localInverse hf' hn
  have hleft : ∀ᶠ x in nhds d, dBreve X a (Ffun X a x) = x := by
    filter_upwards [eventually_gt_nhds hd] with x hx
    exact dBreve_spec (X := X) (a := a) (d := x) hX ha hx
  have hstrict : HasStrictFDerivAt (fun t => Ffun X a t) (e : ℝ →L[ℝ] ℝ) d :=
    hfcd.hasStrictFDerivAt' hf' hn
  have heq : dBreve X a =ᶠ[nhds (Ffun X a d)] hfcd.localInverse hf' hn := by
    simpa [ContDiffAt.localInverse] using hstrict.localInverse_unique (g := dBreve X a) hleft
  exact hsmooth.congr_of_eventuallyEq heq

theorem sec7_ra_dBreve_contDiffAt6_Ffun_public {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ 6 (dBreve X a) (Ffun X a d) :=
  sec7_ra_dBreve_contDiffAt6_Ffun hX ha hd

private theorem sec7_ra_Ffun_dBreve_eventually {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ y in nhds (Ffun X a d), Ffun X a (dBreve X a y) = y := by
  have hda : d + a ≠ 0 := by positivity
  have hfcd : ContDiffAt ℝ 5 (fun t => Ffun X a t) d :=
    Ffun_contDiffAt5 (X := X) (a := a) (d := d) (ne_of_gt hd) hda
  have hraw : HasDerivAt (fun t => Ffun X a t)
      (-2 * X / d ^ 3 + 2 * X / (d + a) ^ 3) d :=
    Ffun_hasDerivAt_d X a d (ne_of_gt hd) hda
  have hfder : HasDerivAt (fun t => Ffun X a t)
      (deriv (fun t => Ffun X a t) d) d := by
    rw [hraw.deriv]
    exact hraw
  have hder_ne : deriv (fun t => Ffun X a t) d ≠ 0 := by
    have hpos : 0 < |deriv (fun t => Ffun X a t) d| := by
      rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := d) hX ha hd]
      positivity
    exact abs_pos.mp hpos
  let e : ℝ ≃L[ℝ] ℝ :=
    (ContinuousLinearEquiv.unitsEquivAut ℝ)
      (Units.mk0 (deriv (fun t => Ffun X a t) d) hder_ne)
  have hf' : HasFDerivAt (fun t => Ffun X a t) (e : ℝ →L[ℝ] ℝ) d := by
    simpa [e] using hfder.hasFDerivAt_equiv hder_ne
  have hn : ((5 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have hleft : ∀ᶠ x in nhds d, dBreve X a (Ffun X a x) = x := by
    filter_upwards [eventually_gt_nhds hd] with x hx
    exact dBreve_spec (X := X) (a := a) (d := x) hX ha hx
  have hstrict : HasStrictFDerivAt (fun t => Ffun X a t) (e : ℝ →L[ℝ] ℝ) d :=
    hfcd.hasStrictFDerivAt' hf' hn
  have heq : dBreve X a =ᶠ[nhds (Ffun X a d)] hfcd.localInverse hf' hn := by
    simpa [ContDiffAt.localInverse] using hstrict.localInverse_unique (g := dBreve X a) hleft
  have hright := hstrict.eventually_right_inverse
  filter_upwards [heq, hright] with y hy hfy
  rw [hy]
  exact hfy

private theorem sec7_ra_B3q_hasDerivAt {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    HasDerivAt (fun t => sec7_ra_B3q P.X a j t)
      (deriv (fun t => Ffun P.X a t) d /
        deriv (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d)) d := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqpos : 0 < qd := by
    rw [hqd_def, sec7_ra_B3q]
    exact dBreve_pos
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hFraw_d : HasDerivAt (fun t => Ffun P.X a t)
      (-2 * P.X / d ^ 3 + 2 * P.X / (d + a) ^ 3) d :=
    Ffun_hasDerivAt_d P.X a d (ne_of_gt hd) (by positivity)
  have hFd : HasDerivAt (fun t => Ffun P.X a t)
      (deriv (fun t => Ffun P.X a t) d) d := by
    rw [hFraw_d.deriv]
    exact hFraw_d
  have hFj : HasDerivAt (fun t => Ffun P.X a t + j)
      (deriv (fun t => Ffun P.X a t) d) d := by
    simpa using hFd.add_const j
  have hdb_shift : HasDerivAt (dBreve P.X a)
      (dBreve' P.X a (Ffun P.X a d + j)) (Ffun P.X a d + j) := by
    have h := dBreve_hasDerivAt_Ffun (X := P.X) (a := a) (d := qd)
      P.X_pos ha0 hqpos
    simpa [hqspec] using h
  have hraw : HasDerivAt (fun t => sec7_ra_B3q P.X a j t)
      (deriv (fun t => Ffun P.X a t) d * dBreve' P.X a (Ffun P.X a d + j)) d := by
    simpa [sec7_ra_B3q, mul_comm] using hdb_shift.comp d hFj
  have hFraw_q : HasDerivAt (fun t => Ffun P.X a t)
      (-2 * P.X / qd ^ 3 + 2 * P.X / (qd + a) ^ 3) qd :=
    Ffun_hasDerivAt_d P.X a qd (ne_of_gt hqpos) (by positivity)
  have hFq : HasDerivAt (fun t => Ffun P.X a t)
      (deriv (fun t => Ffun P.X a t) qd) qd := by
    rw [hFraw_q.deriv]
    exact hFraw_q
  have hshift_y : ∀ᶠ y in nhds (Ffun P.X a d + j), Ffun P.X a (dBreve P.X a y) = y := by
    have h := sec7_ra_Ffun_dBreve_eventually (X := P.X) (a := a) (d := qd)
      P.X_pos ha0 hqpos
    simpa [hqspec] using h
  have harg_cont : ContinuousAt (fun r => Ffun P.X a r + j) d :=
    hFraw_d.continuousAt.add continuousAt_const
  have hloc :
      (fun t => Ffun P.X a (sec7_ra_B3q P.X a j t))
        =ᶠ[nhds d] (fun t => Ffun P.X a t + j) := by
    filter_upwards [Filter.Tendsto.eventually harg_cont hshift_y] with t ht
    simpa [sec7_ra_B3q] using ht
  have hcomp := hFq.comp d hraw
  have heq :
      deriv (fun t => Ffun P.X a t) qd *
          (deriv (fun t => Ffun P.X a t) d * dBreve' P.X a (Ffun P.X a d + j))
        = deriv (fun t => Ffun P.X a t) d := by
    calc
      deriv (fun t => Ffun P.X a t) qd *
          (deriv (fun t => Ffun P.X a t) d * dBreve' P.X a (Ffun P.X a d + j))
          = deriv (fun t => Ffun P.X a (sec7_ra_B3q P.X a j t)) d := hcomp.deriv.symm
      _ = deriv (fun t => Ffun P.X a t + j) d := Filter.EventuallyEq.deriv_eq hloc
      _ = deriv (fun t => Ffun P.X a t) d := hFj.deriv
  have hFq_ne : deriv (fun t => Ffun P.X a t) qd ≠ 0 := by
    have hpos : 0 < |deriv (fun t => Ffun P.X a t) qd| := by
      rw [Ffun_deriv1_abs_eq (X := P.X) (a := a) (d := qd) P.X_pos ha0 hqpos]
      have hpoly : 0 < a ^ 2 + 3 * a * qd + 3 * qd ^ 2 := by positivity
      have hnum : 0 < 2 * P.X * a * (a ^ 2 + 3 * a * qd + 3 * qd ^ 2) := by
        exact mul_pos (mul_pos (mul_pos (by norm_num) P.X_pos) ha0) hpoly
      have hden : 0 < qd ^ 3 * (qd + a) ^ 3 := by positivity
      exact div_pos hnum hden
    exact abs_pos.mp hpos
  have hval :
      deriv (fun t => Ffun P.X a t) d * dBreve' P.X a (Ffun P.X a d + j) =
        deriv (fun t => Ffun P.X a t) d /
          deriv (fun t => Ffun P.X a t) qd := by
    field_simp [hFq_ne]
    nlinarith only [heq]
  rw [hqd_def] at hval
  simpa [hval]
    using hraw

private theorem sec7_ra_B3_iteratedDeriv1_implicit_eq {P : Globals} {S : Scale P}
    {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      deriv (fun t => Ffun P.X a t) d /
        deriv (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d) - 1 := by
  have hq := sec7_ra_B3q_hasDerivAt (P := P) (S := S) (a := a) (d := d) (j := j)
    hAD ha_lo ha_hi hd hshift
  have hB := hq.sub (hasDerivAt_id d)
  rw [iteratedDeriv_one]
  simpa [sec7_ra_B3q] using hB.deriv

private theorem sec7_ra_B3_bound_sharp_k1 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScale 1 * |j| * d ^ 3 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hqpos : 0 < qd := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1
  let F1d : ℝ := deriv (fun t => Ffun P.X a t) d
  let F1q : ℝ := deriv (fun t => Ffun P.X a t) qd
  have hF1q_lower : P.X * a / d ^ 4 ≤ |F1q| := by
    simpa [F1q] using
      (sec7_ra_Ffun_deriv1_lower_sharp_close (X := P.X) (a := a) (d := d) (z := qd)
        P.X_pos ha0 hd ha2 hqwin.1 hqwin.2)
  have hF1q_abs_pos : 0 < |F1q| :=
    lt_of_lt_of_le (div_pos (mul_pos P.X_pos ha0) (pow_pos hd 4)) hF1q_lower
  have hF1q_ne : F1q ≠ 0 := abs_pos.mp hF1q_abs_pos
  have hF1diff :
      |F1d - F1q| ≤ (200 * P.X * a / d ^ 5) * |qd - d| := by
    by_cases hsame : qd = d
    · simp [F1d, F1q, hsame]
    rcases lt_or_gt_of_ne hsame with hlt | hlt
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_deriv_mvt_local (X := P.X) (a := a) (p := qd) (q := d) ha0 hqpos hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := le_trans hqwin.1 (le_of_lt hc_lo)
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) (by nlinarith)
      have hF2 :=
        sec7_ra_Ffun_deriv2_upper_sharp_close (X := P.X) (a := a) (d := d) (z := c)
          P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hmvt_abs : |F1d - F1q| =
          |iteratedDeriv 2 (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hm : F1d - F1q =
            iteratedDeriv 2 (fun t => Ffun P.X a t) c * (d - qd) := by
          simpa [F1d, F1q] using hc_mvt
        rw [hm, abs_mul, abs_sub_comm]
      rw [hmvt_abs]
      exact mul_le_mul_of_nonneg_right hF2 (abs_nonneg _)
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_deriv_mvt_local (X := P.X) (a := a) (p := d) (q := qd) ha0 hd hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := by nlinarith
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) hqwin.2
      have hF2 :=
        sec7_ra_Ffun_deriv2_upper_sharp_close (X := P.X) (a := a) (d := d) (z := c)
          P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hmvt_abs : |F1d - F1q| =
          |iteratedDeriv 2 (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hm : F1q - F1d =
            iteratedDeriv 2 (fun t => Ffun P.X a t) c * (qd - d) := by
          simpa [F1d, F1q] using hc_mvt
        rw [← abs_neg (F1d - F1q)]
        have hneg : -(F1d - F1q) = F1q - F1d := by ring
        rw [hneg, hm, abs_mul]
      rw [hmvt_abs]
      exact mul_le_mul_of_nonneg_right hF2 (abs_nonneg _)
  have hqdiff :=
    sec7_ra_B3_qdiff_sharp (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose
  have hiter :=
    sec7_ra_B3_iteratedDeriv1_implicit_eq (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd hshift
  rw [hiter]
  have hdiv_eq : F1d / F1q - 1 = (F1d - F1q) / F1q := by
    field_simp [hF1q_ne]
  rw [show deriv (fun t => Ffun P.X a t) d = F1d by rfl]
  rw [show deriv (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d) = F1q by
    rw [← hqd_def]]
  rw [hdiv_eq, abs_div]
  have hratio :
      |F1d - F1q| / |F1q| ≤ 200 * |qd - d| / d := by
    have hnum_nonneg : 0 ≤ (200 * P.X * a / d ^ 5) * |qd - d| := by
      have hcoef : 0 ≤ 200 * P.X * a := by
        exact mul_nonneg (mul_nonneg (by norm_num) P.X_pos.le) ha0.le
      exact mul_nonneg (div_nonneg hcoef (le_of_lt (pow_pos hd 5))) (abs_nonneg _)
    calc
      |F1d - F1q| / |F1q|
          ≤ ((200 * P.X * a / d ^ 5) * |qd - d|) / |F1q| := by
        exact div_le_div_of_nonneg_right hF1diff (abs_nonneg _)
      _ ≤ ((200 * P.X * a / d ^ 5) * |qd - d|) / (P.X * a / d ^ 4) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ hF1q_abs_pos (div_pos (mul_pos P.X_pos ha0) (pow_pos hd 4))).2
            hF1q_lower)
          hnum_nonneg
      _ = 200 * |qd - d| / d := by
        field_simp [P.X_pos.ne', ne_of_gt ha0, ne_of_gt hd]
  calc
    |F1d - F1q| / |F1q| ≤ 200 * |qd - d| / d := hratio
    _ ≤ 200 * (|j| * d ^ 4 / (P.X * a)) / d := by
      gcongr
    _ = 200 * |j| * d ^ 3 / (P.X * a) := by
      field_simp [P.X_pos.ne', ne_of_gt ha0, ne_of_gt hd]
    _ ≤ sec7_ra_B3SharpScale 1 * |j| * d ^ 3 / (P.X * a) := by
      simp [sec7_ra_B3SharpScale]
      gcongr
      · exact mul_nonneg P.X_pos.le ha0.le
      · norm_num

private theorem sec7_ra_dBreve_deriv1_Ffun_eq {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve' X a (Ffun X a d) = (deriv (fun t => Ffun X a t) d)⁻¹ := by
  have hFraw : HasDerivAt (fun t => Ffun X a t)
      (-2 * X / d ^ 3 + 2 * X / (d + a) ^ 3) d :=
    Ffun_hasDerivAt_d X a d (ne_of_gt hd) (by positivity)
  have hF : HasDerivAt (fun t => Ffun X a t)
      (deriv (fun t => Ffun X a t) d) d := by
    rw [hFraw.deriv]
    exact hFraw
  have hdb := dBreve_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  have hcomp := hdb.comp d hF
  have hloc :
      (fun t => dBreve X a (Ffun X a t)) =ᶠ[nhds d] (fun t => t) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    exact dBreve_spec hX ha ht
  have hprod :
      dBreve' X a (Ffun X a d) * deriv (fun t => Ffun X a t) d = 1 := by
    calc
      dBreve' X a (Ffun X a d) * deriv (fun t => Ffun X a t) d
          = deriv (dBreve X a ∘ Ffun X a) d := hcomp.deriv.symm
      _ = deriv (fun t : ℝ => t) d := Filter.EventuallyEq.deriv_eq hloc
      _ = 1 := by simp
  have hF_ne : deriv (fun t => Ffun X a t) d ≠ 0 := by
    have hpos : 0 < |deriv (fun t => Ffun X a t) d| := by
      rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := d) hX ha hd]
      have hpoly : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
      have hnum : 0 < 2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by
        exact mul_pos (mul_pos (mul_pos (by norm_num) hX) ha) hpoly
      have hden : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
      exact div_pos hnum hden
    exact abs_pos.mp hpos
  calc
    dBreve' X a (Ffun X a d)
        = dBreve' X a (Ffun X a d) *
            (deriv (fun t => Ffun X a t) d *
              (deriv (fun t => Ffun X a t) d)⁻¹) := by
            rw [mul_inv_cancel₀ hF_ne, mul_one]
    _ = (dBreve' X a (Ffun X a d) * deriv (fun t => Ffun X a t) d) *
          (deriv (fun t => Ffun X a t) d)⁻¹ := by ring
    _ = (deriv (fun t => Ffun X a t) d)⁻¹ := by rw [hprod, one_mul]

theorem sec7_ra_A1_identity {X a d : ℝ} (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    -dBreve' X a (Ffun X a d) - d ^ 2 * (d + a) ^ 2 / (6 * X * a) =
      -a * d ^ 2 * (d + a) ^ 2 /
        (6 * X * (a ^ 2 + 3 * a * d + 3 * d ^ 2)) := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hQ : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [sec7_ra_dBreve_deriv1_Ffun_eq hX ha hd]
  rw [Ffun_deriv_d X a d hdne hda]
  rw [Ffun_deriv1_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hQ]
  ring

private theorem sec7_ra_Ffun_deriv_hasDerivAt {X a d : ℝ}
    (hd : d ≠ 0) (hda : d + a ≠ 0) :
    HasDerivAt (deriv (fun t => Ffun X a t))
      (iteratedDeriv 2 (fun t => Ffun X a t) d) d := by
  have hloc :
      deriv (fun t => Ffun X a t)
        =ᶠ[nhds d] (fun t => -2 * X / t ^ 3 + 2 * X / (t + a) ^ 3) := by
    have hopen : IsOpen {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} :=
      (isOpen_ne.preimage continuous_id).inter
        (isOpen_ne.preimage (continuous_id.add continuous_const))
    have hmem : d ∈ {t : ℝ | t ≠ 0 ∧ t + a ≠ 0} := ⟨hd, hda⟩
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
    intro t ht
    exact (Ffun_hasDerivAt_d X a t ht.1 ht.2).deriv
  have hraw : HasDerivAt (fun t => -2 * X / t ^ 3 + 2 * X / (t + a) ^ 3)
      (iteratedDeriv 2 (fun t => Ffun X a t) d) d := by
    simpa [Ffun_iteratedDeriv2_d X a d hd hda]
      using Ffun_hasDerivAt2_d X a d hd hda
  exact hraw.congr_of_eventuallyEq hloc

private theorem sec7_ra_Ffun_deriv_ne {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    deriv (fun t => Ffun X a t) d ≠ 0 := by
  have hpos : 0 < |deriv (fun t => Ffun X a t) d| := by
    rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := d) hX ha hd]
    have hpoly : 0 < a ^ 2 + 3 * a * d + 3 * d ^ 2 := by positivity
    have hnum : 0 < 2 * X * a * (a ^ 2 + 3 * a * d + 3 * d ^ 2) := by
      exact mul_pos (mul_pos (mul_pos (by norm_num) hX) ha) hpoly
    have hden : 0 < d ^ 3 * (d + a) ^ 3 := by positivity
    exact div_pos hnum hden
  exact abs_pos.mp hpos

private theorem sec7_ra_dBreve_deriv2_Ffun_eq {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve'' X a (Ffun X a d) =
      - iteratedDeriv 2 (fun t => Ffun X a t) d /
        (deriv (fun t => Ffun X a t) d) ^ 3 := by
  have hFraw : HasDerivAt (fun t => Ffun X a t)
      (-2 * X / d ^ 3 + 2 * X / (d + a) ^ 3) d :=
    Ffun_hasDerivAt_d X a d (ne_of_gt hd) (by positivity)
  have hF : HasDerivAt (fun t => Ffun X a t)
      (deriv (fun t => Ffun X a t) d) d := by
    rw [hFraw.deriv]
    exact hFraw
  have hF_ne : deriv (fun t => Ffun X a t) d ≠ 0 :=
    sec7_ra_Ffun_deriv_ne hX ha hd
  have hdb1 := dBreve_deriv1_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  have hlhs := hdb1.comp d hF
  have hFder := sec7_ra_Ffun_deriv_hasDerivAt (X := X) (a := a) (d := d)
    (ne_of_gt hd) (by positivity)
  have hrhs : HasDerivAt (fun t => (deriv (fun u => Ffun X a u) t)⁻¹)
      (- iteratedDeriv 2 (fun t => Ffun X a t) d /
        (deriv (fun t => Ffun X a t) d) ^ 2) d := by
    simpa using hFder.inv hF_ne
  have hloc :
      (dBreve' X a ∘ Ffun X a) =ᶠ[nhds d]
        (fun t => (deriv (fun u => Ffun X a u) t)⁻¹) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    exact sec7_ra_dBreve_deriv1_Ffun_eq hX ha ht
  have hprod :
      dBreve'' X a (Ffun X a d) * deriv (fun t => Ffun X a t) d =
        - iteratedDeriv 2 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 2 := by
    calc
      dBreve'' X a (Ffun X a d) * deriv (fun t => Ffun X a t) d
          = deriv (dBreve' X a ∘ Ffun X a) d := hlhs.deriv.symm
      _ = deriv (fun t => (deriv (fun u => Ffun X a u) t)⁻¹) d :=
          Filter.EventuallyEq.deriv_eq hloc
      _ = - iteratedDeriv 2 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 2 := hrhs.deriv
  calc
    dBreve'' X a (Ffun X a d)
        = (dBreve'' X a (Ffun X a d) * deriv (fun t => Ffun X a t) d) /
          deriv (fun t => Ffun X a t) d := by
            field_simp [hF_ne]
    _ = (- iteratedDeriv 2 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 2) /
          deriv (fun t => Ffun X a t) d := by rw [hprod]
    _ = - iteratedDeriv 2 (fun t => Ffun X a t) d /
        (deriv (fun t => Ffun X a t) d) ^ 3 := by
          field_simp [hF_ne]

private theorem sec7_ra_dBreve_deriv2_image_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve'' X a (Ffun X a z)| ≤ 2 * d ^ 7 / (X * a) ^ 2 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (51 / 100 : ℝ) * z := by nlinarith
  have hF2 := (sec7_ra_Ffun_upper_base_sharp (X := X) (a := a) (d := z) hX ha hz).2.1
  have hF1lo :=
    sec7_ra_Ffun_deriv1_lower_25 (X := X) (a := a) (z := z) hX ha hz haz
  have hF1pos : 0 < |deriv (fun t => Ffun X a t) z| := by
    exact lt_of_lt_of_le
      (div_pos (mul_pos (mul_pos (by norm_num) hX) ha) (pow_pos hz 4)) hF1lo
  have hF1pow :
      ((5 / 2 : ℝ) * X * a / z ^ 4) ^ 3 ≤
        |deriv (fun t => Ffun X a t) z| ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hF1lo 3
  have hden_pos : 0 < ((5 / 2 : ℝ) * X * a / z ^ 4) ^ 3 := by positivity
  have hz7_le : z ^ 7 ≤ ((101 / 100 : ℝ) * d) ^ 7 :=
    pow_le_pow_left₀ hz.le hzhi 7
  rw [sec7_ra_dBreve_deriv2_Ffun_eq (X := X) (a := a) (d := z) hX ha hz]
  rw [abs_div, abs_neg, abs_pow]
  calc
    |iteratedDeriv 2 (fun t => Ffun X a t) z| / |deriv (fun t => Ffun X a t) z| ^ 3
        ≤ (26 * X * a / z ^ 5) / |deriv (fun t => Ffun X a t) z| ^ 3 := by
          exact div_le_div_of_nonneg_right hF2 (pow_nonneg (abs_nonneg _) 3)
    _ ≤ (26 * X * a / z ^ 5) / (((5 / 2 : ℝ) * X * a / z ^ 4) ^ 3) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            ((inv_le_inv₀ (pow_pos hF1pos 3) hden_pos).2 hF1pow)
            (by positivity)
    _ = (208 / 125 : ℝ) * z ^ 7 / (X * a) ^ 2 := by
          field_simp [hX.ne', ha.ne', hz.ne']
          ring
    _ ≤ (208 / 125 : ℝ) * (((101 / 100 : ℝ) * d) ^ 7) / (X * a) ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz7_le (by norm_num))
            (sq_nonneg (X * a))
    _ ≤ 2 * d ^ 7 / (X * a) ^ 2 := by
          have hconst : (208 / 125 : ℝ) * (101 / 100 : ℝ) ^ 7 ≤ 2 := by
            norm_num
          have hd7_nonneg : 0 ≤ d ^ 7 := by positivity
          have hnum :
              (208 / 125 : ℝ) * (((101 / 100 : ℝ) * d) ^ 7) ≤ 2 * d ^ 7 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 7) =
                (101 / 100 : ℝ) ^ 7 * d ^ 7 by ring]
            nlinarith
          exact div_le_div_of_nonneg_right hnum (sq_nonneg (X * a))

private theorem sec7_ra_dBreve_deriv3_Ffun_eq {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve''' X a (Ffun X a d) =
      3 * (iteratedDeriv 2 (fun t => Ffun X a t) d) ^ 2 /
          (deriv (fun t => Ffun X a t) d) ^ 5 -
        iteratedDeriv 3 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 4 := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hP : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [dBreve_deriv3_factor_image (X := X) (a := a) (d := d) hX ha hd]
  rw [Ffun_deriv_d X a d hdne hda,
    Ffun_iteratedDeriv2_d X a d hdne hda,
    Ffun_iteratedDeriv3_d X a d hdne hda]
  rw [Ffun_deriv1_factor X a d hdne hda,
    Ffun_deriv2_factor X a d hdne hda,
    Ffun_deriv3_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hP]
  ring

private theorem sec7_ra_dBreve_deriv3_image_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve''' X a (Ffun X a z)| ≤ 2 * d ^ 10 / (X * a) ^ 3 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (51 / 100 : ℝ) * z := by nlinarith
  set P : ℝ :=
    5 * a ^ 6 + 40 * a ^ 5 * z + 140 * a ^ 4 * z ^ 2 +
      284 * a ^ 3 * z ^ 3 + 352 * a ^ 2 * z ^ 4 + 252 * a * z ^ 5 +
      84 * z ^ 6 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hP_nonneg : 0 ≤ P := by
    rw [hP_def]
    positivity
  have hQ_pos : 0 < Q := by
    rw [hQ_def]
    positivity
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 5 ≤ Q ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 5
  have ha2' : a ^ 2 ≤ ((51 / 100 : ℝ) * z) ^ 2 :=
    pow_le_pow_left₀ ha.le haz 2
  have ha3' : a ^ 3 ≤ ((51 / 100 : ℝ) * z) ^ 3 :=
    pow_le_pow_left₀ ha.le haz 3
  have ha4' : a ^ 4 ≤ ((51 / 100 : ℝ) * z) ^ 4 :=
    pow_le_pow_left₀ ha.le haz 4
  have ha5' : a ^ 5 ≤ ((51 / 100 : ℝ) * z) ^ 5 :=
    pow_le_pow_left₀ ha.le haz 5
  have ha6' : a ^ 6 ≤ ((51 / 100 : ℝ) * z) ^ 6 :=
    pow_le_pow_left₀ ha.le haz 6
  have hP_bound : P ≤ 400 * z ^ 6 := by
    have h1 : a ^ 6 ≤ (51 / 100 : ℝ) ^ 6 * z ^ 6 := by simpa [mul_pow] using ha6'
    have h2 : a ^ 5 * z ≤ (51 / 100 : ℝ) ^ 5 * z ^ 6 := by
      calc
        a ^ 5 * z ≤ (((51 / 100 : ℝ) * z) ^ 5) * z :=
          mul_le_mul_of_nonneg_right ha5' hz.le
        _ = (51 / 100 : ℝ) ^ 5 * z ^ 6 := by ring
    have h3 : a ^ 4 * z ^ 2 ≤ (51 / 100 : ℝ) ^ 4 * z ^ 6 := by
      calc
        a ^ 4 * z ^ 2 ≤ (((51 / 100 : ℝ) * z) ^ 4) * z ^ 2 :=
          mul_le_mul_of_nonneg_right ha4' (by positivity)
        _ = (51 / 100 : ℝ) ^ 4 * z ^ 6 := by ring
    have h4 : a ^ 3 * z ^ 3 ≤ (51 / 100 : ℝ) ^ 3 * z ^ 6 := by
      calc
        a ^ 3 * z ^ 3 ≤ (((51 / 100 : ℝ) * z) ^ 3) * z ^ 3 :=
          mul_le_mul_of_nonneg_right ha3' (by positivity)
        _ = (51 / 100 : ℝ) ^ 3 * z ^ 6 := by ring
    have h5 : a ^ 2 * z ^ 4 ≤ (51 / 100 : ℝ) ^ 2 * z ^ 6 := by
      calc
        a ^ 2 * z ^ 4 ≤ (((51 / 100 : ℝ) * z) ^ 2) * z ^ 4 :=
          mul_le_mul_of_nonneg_right ha2' (by positivity)
        _ = (51 / 100 : ℝ) ^ 2 * z ^ 6 := by ring
    have h6 : a * z ^ 5 ≤ (51 / 100 : ℝ) * z ^ 6 := by
      calc
        a * z ^ 5 ≤ ((51 / 100 : ℝ) * z) * z ^ 5 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = (51 / 100 : ℝ) * z ^ 6 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, pow_nonneg hz.le 6]
  have hza_bound : (z + a) ^ 2 ≤ ((151 / 100 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (151 / 100 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hcore :
      3 * (z + a) ^ 2 * P ≤ 12 * 3 ^ 5 * z ^ 8 := by
    calc
      3 * (z + a) ^ 2 * P
          ≤ 3 * (((151 / 100 : ℝ) * z) ^ 2) * (400 * z ^ 6) := by
            gcongr
      _ = (3 * (151 / 100 : ℝ) ^ 2 * 400) * z ^ 8 := by ring
      _ ≤ 12 * 3 ^ 5 * z ^ 8 := by
            have hconst : (3 * (151 / 100 : ℝ) ^ 2 * 400) ≤ 12 * 3 ^ 5 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hz.le 8)]
  have hnum_core :
      3 * z ^ 7 * (z + a) ^ 7 * P ≤ 12 * z ^ 10 * Q ^ 5 := by
    calc
      3 * z ^ 7 * (z + a) ^ 7 * P
          = z ^ 7 * (z + a) ^ 5 * (3 * (z + a) ^ 2 * P) := by ring
      _ ≤ z ^ 7 * (z + a) ^ 5 * (12 * 3 ^ 5 * z ^ 8) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 12 * z ^ 10 * (((3 : ℝ) * z * (z + a)) ^ 5) := by ring
      _ ≤ 12 * z ^ 10 * Q ^ 5 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz10_le : z ^ 10 ≤ ((101 / 100 : ℝ) * d) ^ 10 :=
    pow_le_pow_left₀ hz.le hzhi 10
  rw [dBreve_deriv3_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      3 * z ^ 7 * (z + a) ^ 7 * P / (8 * X ^ 3 * a ^ 3 * Q ^ 5)
        ≤ (3 / 2 : ℝ) * z ^ 10 / (X * a) ^ 3 := by
    have hden_left : 0 < 8 * X ^ 3 * a ^ 3 * Q ^ 5 := by positivity
    have hden_right : 0 < (X * a) ^ 3 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 3 * a ^ 3)
    linarith [hmul]
  calc
    3 * z ^ 7 * (z + a) ^ 7 * P / (8 * X ^ 3 * a ^ 3 * Q ^ 5)
        ≤ (3 / 2 : ℝ) * z ^ 10 / (X * a) ^ 3 := hstep
    _ ≤ (3 / 2 : ℝ) * (((101 / 100 : ℝ) * d) ^ 10) / (X * a) ^ 3 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz10_le (by norm_num))
            (by positivity : 0 ≤ (X * a) ^ 3)
    _ ≤ 2 * d ^ 10 / (X * a) ^ 3 := by
          have hnum :
              (3 / 2 : ℝ) * (((101 / 100 : ℝ) * d) ^ 10) ≤ 2 * d ^ 10 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 10) =
                (101 / 100 : ℝ) ^ 10 * d ^ 10 by ring]
            have hconst : (3 / 2 : ℝ) * (101 / 100 : ℝ) ^ 10 ≤ 2 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 10)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

private theorem sec7_ra_dBreve_deriv4_Ffun_eq {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve'''' X a (Ffun X a d) =
      -15 * (iteratedDeriv 2 (fun t => Ffun X a t) d) ^ 3 /
          (deriv (fun t => Ffun X a t) d) ^ 7 +
        10 * iteratedDeriv 2 (fun t => Ffun X a t) d *
          iteratedDeriv 3 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 6 -
        iteratedDeriv 4 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 5 := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hP : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [dBreve_deriv4_factor_image (X := X) (a := a) (d := d) hX ha hd]
  rw [Ffun_deriv_d X a d hdne hda,
    Ffun_iteratedDeriv2_d X a d hdne hda,
    Ffun_iteratedDeriv3_d X a d hdne hda,
    Ffun_iteratedDeriv4_d X a d hdne hda]
  rw [Ffun_deriv1_factor X a d hdne hda,
    Ffun_deriv2_factor X a d hdne hda,
    Ffun_deriv3_factor X a d hdne hda,
    Ffun_deriv4_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hP]
  ring

private theorem sec7_ra_dBreve_deriv4_image_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve'''' X a (Ffun X a z)| ≤ 6 * d ^ 13 / (X * a) ^ 4 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (51 / 100 : ℝ) * z := by nlinarith
  set P : ℝ :=
    7 * a ^ 8 + 70 * a ^ 7 * z + 322 * a ^ 6 * z ^ 2 +
      912 * a ^ 5 * z ^ 3 + 1728 * a ^ 4 * z ^ 4 + 2232 * a ^ 3 * z ^ 5 +
      1920 * a ^ 2 * z ^ 6 + 1008 * a * z ^ 7 + 252 * z ^ 8 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 7 ≤ Q ^ 7 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 7
  have ha2' : a ^ 2 ≤ ((51 / 100 : ℝ) * z) ^ 2 :=
    pow_le_pow_left₀ ha.le haz 2
  have ha3' : a ^ 3 ≤ ((51 / 100 : ℝ) * z) ^ 3 :=
    pow_le_pow_left₀ ha.le haz 3
  have ha4' : a ^ 4 ≤ ((51 / 100 : ℝ) * z) ^ 4 :=
    pow_le_pow_left₀ ha.le haz 4
  have ha5' : a ^ 5 ≤ ((51 / 100 : ℝ) * z) ^ 5 :=
    pow_le_pow_left₀ ha.le haz 5
  have ha6' : a ^ 6 ≤ ((51 / 100 : ℝ) * z) ^ 6 :=
    pow_le_pow_left₀ ha.le haz 6
  have ha7' : a ^ 7 ≤ ((51 / 100 : ℝ) * z) ^ 7 :=
    pow_le_pow_left₀ ha.le haz 7
  have ha8' : a ^ 8 ≤ ((51 / 100 : ℝ) * z) ^ 8 :=
    pow_le_pow_left₀ ha.le haz 8
  have hP_bound : P ≤ 2000 * z ^ 8 := by
    have h1 : a ^ 8 ≤ (51 / 100 : ℝ) ^ 8 * z ^ 8 := by simpa [mul_pow] using ha8'
    have h2 : a ^ 7 * z ≤ (51 / 100 : ℝ) ^ 7 * z ^ 8 := by
      calc
        a ^ 7 * z ≤ (((51 / 100 : ℝ) * z) ^ 7) * z :=
          mul_le_mul_of_nonneg_right ha7' hz.le
        _ = (51 / 100 : ℝ) ^ 7 * z ^ 8 := by ring
    have h3 : a ^ 6 * z ^ 2 ≤ (51 / 100 : ℝ) ^ 6 * z ^ 8 := by
      calc
        a ^ 6 * z ^ 2 ≤ (((51 / 100 : ℝ) * z) ^ 6) * z ^ 2 :=
          mul_le_mul_of_nonneg_right ha6' (by positivity)
        _ = (51 / 100 : ℝ) ^ 6 * z ^ 8 := by ring
    have h4 : a ^ 5 * z ^ 3 ≤ (51 / 100 : ℝ) ^ 5 * z ^ 8 := by
      calc
        a ^ 5 * z ^ 3 ≤ (((51 / 100 : ℝ) * z) ^ 5) * z ^ 3 :=
          mul_le_mul_of_nonneg_right ha5' (by positivity)
        _ = (51 / 100 : ℝ) ^ 5 * z ^ 8 := by ring
    have h5 : a ^ 4 * z ^ 4 ≤ (51 / 100 : ℝ) ^ 4 * z ^ 8 := by
      calc
        a ^ 4 * z ^ 4 ≤ (((51 / 100 : ℝ) * z) ^ 4) * z ^ 4 :=
          mul_le_mul_of_nonneg_right ha4' (by positivity)
        _ = (51 / 100 : ℝ) ^ 4 * z ^ 8 := by ring
    have h6 : a ^ 3 * z ^ 5 ≤ (51 / 100 : ℝ) ^ 3 * z ^ 8 := by
      calc
        a ^ 3 * z ^ 5 ≤ (((51 / 100 : ℝ) * z) ^ 3) * z ^ 5 :=
          mul_le_mul_of_nonneg_right ha3' (by positivity)
        _ = (51 / 100 : ℝ) ^ 3 * z ^ 8 := by ring
    have h7 : a ^ 2 * z ^ 6 ≤ (51 / 100 : ℝ) ^ 2 * z ^ 8 := by
      calc
        a ^ 2 * z ^ 6 ≤ (((51 / 100 : ℝ) * z) ^ 2) * z ^ 6 :=
          mul_le_mul_of_nonneg_right ha2' (by positivity)
        _ = (51 / 100 : ℝ) ^ 2 * z ^ 8 := by ring
    have h8 : a * z ^ 7 ≤ (51 / 100 : ℝ) * z ^ 8 := by
      calc
        a * z ^ 7 ≤ ((51 / 100 : ℝ) * z) * z ^ 7 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = (51 / 100 : ℝ) * z ^ 8 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, pow_nonneg hz.le 8]
  have hza_bound : (z + a) ^ 2 ≤ ((151 / 100 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (151 / 100 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hlin_bound : a + 2 * z ≤ (251 / 100 : ℝ) * z := by nlinarith
  have hcore :
      15 * (z + a) ^ 2 * (a + 2 * z) * P ≤ 80 * 3 ^ 7 * z ^ 11 := by
    calc
      15 * (z + a) ^ 2 * (a + 2 * z) * P
          ≤ 15 * (((151 / 100 : ℝ) * z) ^ 2) *
              ((251 / 100 : ℝ) * z) * (2000 * z ^ 8) := by
            gcongr
      _ = (15 * (151 / 100 : ℝ) ^ 2 * (251 / 100 : ℝ) * 2000) * z ^ 11 := by
            ring
      _ ≤ 80 * 3 ^ 7 * z ^ 11 := by
            have hconst : 15 * (151 / 100 : ℝ) ^ 2 * (251 / 100 : ℝ) * 2000 ≤
                80 * 3 ^ 7 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P ≤ 80 * z ^ 13 * Q ^ 7 := by
    calc
      15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P
          = z ^ 9 * (z + a) ^ 7 * (15 * (z + a) ^ 2 * (a + 2 * z) * P) := by
            ring
      _ ≤ z ^ 9 * (z + a) ^ 7 * (80 * 3 ^ 7 * z ^ 11) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 80 * z ^ 13 * (((3 : ℝ) * z * (z + a)) ^ 7) := by ring
      _ ≤ 80 * z ^ 13 * Q ^ 7 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz13_le : z ^ 13 ≤ ((101 / 100 : ℝ) * d) ^ 13 :=
    pow_le_pow_left₀ hz.le hzhi 13
  rw [dBreve_deriv4_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P /
          (16 * X ^ 4 * a ^ 4 * Q ^ 7)
        ≤ 5 * z ^ 13 / (X * a) ^ 4 := by
    have hden_left : 0 < 16 * X ^ 4 * a ^ 4 * Q ^ 7 := by
      rw [hQ_def]
      positivity
    have hden_right : 0 < (X * a) ^ 4 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 4 * a ^ 4)
    linarith [hmul]
  calc
    15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P /
          (16 * X ^ 4 * a ^ 4 * Q ^ 7)
        ≤ 5 * z ^ 13 / (X * a) ^ 4 := hstep
    _ ≤ 5 * (((101 / 100 : ℝ) * d) ^ 13) / (X * a) ^ 4 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz13_le (by norm_num))
            (by positivity)
    _ ≤ 6 * d ^ 13 / (X * a) ^ 4 := by
          have hnum : 5 * (((101 / 100 : ℝ) * d) ^ 13) ≤ 6 * d ^ 13 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 13) =
                (101 / 100 : ℝ) ^ 13 * d ^ 13 by ring]
            have hconst : 5 * (101 / 100 : ℝ) ^ 13 ≤ 6 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 13)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

private theorem sec7_ra_dBreve_deriv5_Ffun_eq {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    dBreve''''' X a (Ffun X a d) =
      105 * (iteratedDeriv 2 (fun t => Ffun X a t) d) ^ 4 /
          (deriv (fun t => Ffun X a t) d) ^ 9 -
        105 * (iteratedDeriv 2 (fun t => Ffun X a t) d) ^ 2 *
          iteratedDeriv 3 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 8 +
        10 * (iteratedDeriv 3 (fun t => Ffun X a t) d) ^ 2 /
          (deriv (fun t => Ffun X a t) d) ^ 7 +
        15 * iteratedDeriv 2 (fun t => Ffun X a t) d *
          iteratedDeriv 4 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 7 -
        iteratedDeriv 5 (fun t => Ffun X a t) d /
          (deriv (fun t => Ffun X a t) d) ^ 6 := by
  have hda : d + a ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hane : a ≠ 0 := ne_of_gt ha
  have hdne : d ≠ 0 := ne_of_gt hd
  have hP : a ^ 2 + 3 * a * d + 3 * d ^ 2 ≠ 0 := by positivity
  rw [dBreve_deriv5_factor_image (X := X) (a := a) (d := d) hX ha hd]
  rw [Ffun_deriv_d X a d hdne hda,
    Ffun_iteratedDeriv2_d X a d hdne hda,
    Ffun_iteratedDeriv3_d X a d hdne hda,
    Ffun_iteratedDeriv4_d X a d hdne hda,
    Ffun_iteratedDeriv5_d X a d hdne hda]
  rw [Ffun_deriv1_factor X a d hdne hda,
    Ffun_deriv2_factor X a d hdne hda,
    Ffun_deriv3_factor X a d hdne hda,
    Ffun_deriv4_factor X a d hdne hda,
    Ffun_deriv5_factor X a d hdne hda]
  field_simp [hXne, hane, hdne, hda, hP]
  ring

private theorem sec7_ra_dBreve_deriv5_image_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve''''' X a (Ffun X a z)| ≤ 25 * d ^ 16 / (X * a) ^ 5 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (51 / 100 : ℝ) * z := by nlinarith
  set P : ℝ :=
    21 * a ^ 12 + 336 * a ^ 11 * z + 2520 * a ^ 10 * z ^ 2 +
      11852 * a ^ 9 * z ^ 3 + 39104 * a ^ 8 * z ^ 4 +
      95348 * a ^ 7 * z ^ 5 + 175964 * a ^ 6 * z ^ 6 +
      247424 * a ^ 5 * z ^ 7 + 262988 * a ^ 4 * z ^ 8 +
      206160 * a ^ 3 * z ^ 9 + 113304 * a ^ 2 * z ^ 10 +
      39312 * a * z ^ 11 + 6552 * z ^ 12 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 9 ≤ Q ^ 9 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 9
  have hP_bound : P ≤ 120000 * z ^ 12 := by
    have h1 : a ^ 12 ≤ (51 / 100 : ℝ) ^ 12 * z ^ 12 := by
      simpa [mul_pow] using pow_le_pow_left₀ ha.le haz 12
    have h2 : a ^ 11 * z ≤ (51 / 100 : ℝ) ^ 11 * z ^ 12 := by
      calc
        a ^ 11 * z ≤ (((51 / 100 : ℝ) * z) ^ 11) * z :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 11) hz.le
        _ = (51 / 100 : ℝ) ^ 11 * z ^ 12 := by ring
    have h3 : a ^ 10 * z ^ 2 ≤ (51 / 100 : ℝ) ^ 10 * z ^ 12 := by
      calc
        a ^ 10 * z ^ 2 ≤ (((51 / 100 : ℝ) * z) ^ 10) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 10) (by positivity)
        _ = (51 / 100 : ℝ) ^ 10 * z ^ 12 := by ring
    have h4 : a ^ 9 * z ^ 3 ≤ (51 / 100 : ℝ) ^ 9 * z ^ 12 := by
      calc
        a ^ 9 * z ^ 3 ≤ (((51 / 100 : ℝ) * z) ^ 9) * z ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 9) (by positivity)
        _ = (51 / 100 : ℝ) ^ 9 * z ^ 12 := by ring
    have h5 : a ^ 8 * z ^ 4 ≤ (51 / 100 : ℝ) ^ 8 * z ^ 12 := by
      calc
        a ^ 8 * z ^ 4 ≤ (((51 / 100 : ℝ) * z) ^ 8) * z ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 8) (by positivity)
        _ = (51 / 100 : ℝ) ^ 8 * z ^ 12 := by ring
    have h6 : a ^ 7 * z ^ 5 ≤ (51 / 100 : ℝ) ^ 7 * z ^ 12 := by
      calc
        a ^ 7 * z ^ 5 ≤ (((51 / 100 : ℝ) * z) ^ 7) * z ^ 5 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 7) (by positivity)
        _ = (51 / 100 : ℝ) ^ 7 * z ^ 12 := by ring
    have h7 : a ^ 6 * z ^ 6 ≤ (51 / 100 : ℝ) ^ 6 * z ^ 12 := by
      calc
        a ^ 6 * z ^ 6 ≤ (((51 / 100 : ℝ) * z) ^ 6) * z ^ 6 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 6) (by positivity)
        _ = (51 / 100 : ℝ) ^ 6 * z ^ 12 := by ring
    have h8 : a ^ 5 * z ^ 7 ≤ (51 / 100 : ℝ) ^ 5 * z ^ 12 := by
      calc
        a ^ 5 * z ^ 7 ≤ (((51 / 100 : ℝ) * z) ^ 5) * z ^ 7 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 5) (by positivity)
        _ = (51 / 100 : ℝ) ^ 5 * z ^ 12 := by ring
    have h9 : a ^ 4 * z ^ 8 ≤ (51 / 100 : ℝ) ^ 4 * z ^ 12 := by
      calc
        a ^ 4 * z ^ 8 ≤ (((51 / 100 : ℝ) * z) ^ 4) * z ^ 8 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 4) (by positivity)
        _ = (51 / 100 : ℝ) ^ 4 * z ^ 12 := by ring
    have h10 : a ^ 3 * z ^ 9 ≤ (51 / 100 : ℝ) ^ 3 * z ^ 12 := by
      calc
        a ^ 3 * z ^ 9 ≤ (((51 / 100 : ℝ) * z) ^ 3) * z ^ 9 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 3) (by positivity)
        _ = (51 / 100 : ℝ) ^ 3 * z ^ 12 := by ring
    have h11 : a ^ 2 * z ^ 10 ≤ (51 / 100 : ℝ) ^ 2 * z ^ 12 := by
      calc
        a ^ 2 * z ^ 10 ≤ (((51 / 100 : ℝ) * z) ^ 2) * z ^ 10 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 2) (by positivity)
        _ = (51 / 100 : ℝ) ^ 2 * z ^ 12 := by ring
    have h12 : a * z ^ 11 ≤ (51 / 100 : ℝ) * z ^ 12 := by
      calc
        a * z ^ 11 ≤ ((51 / 100 : ℝ) * z) * z ^ 11 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = (51 / 100 : ℝ) * z ^ 12 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      pow_nonneg hz.le 12]
  have hza_bound : (z + a) ^ 2 ≤ ((151 / 100 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (151 / 100 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hcore :
      45 * (z + a) ^ 2 * P ≤ 640 * 3 ^ 9 * z ^ 14 := by
    calc
      45 * (z + a) ^ 2 * P
          ≤ 45 * (((151 / 100 : ℝ) * z) ^ 2) * (120000 * z ^ 12) := by
            gcongr
      _ = (45 * (151 / 100 : ℝ) ^ 2 * 120000) * z ^ 14 := by ring
      _ ≤ 640 * 3 ^ 9 * z ^ 14 := by
            have hconst : 45 * (151 / 100 : ℝ) ^ 2 * 120000 ≤ 640 * 3 ^ 9 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      45 * z ^ 11 * (z + a) ^ 11 * P ≤ 640 * z ^ 16 * Q ^ 9 := by
    calc
      45 * z ^ 11 * (z + a) ^ 11 * P
          = z ^ 11 * (z + a) ^ 9 * (45 * (z + a) ^ 2 * P) := by ring
      _ ≤ z ^ 11 * (z + a) ^ 9 * (640 * 3 ^ 9 * z ^ 14) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 640 * z ^ 16 * (((3 : ℝ) * z * (z + a)) ^ 9) := by ring
      _ ≤ 640 * z ^ 16 * Q ^ 9 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz16_le : z ^ 16 ≤ ((101 / 100 : ℝ) * d) ^ 16 :=
    pow_le_pow_left₀ hz.le hzhi 16
  rw [dBreve_deriv5_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      45 * z ^ 11 * (z + a) ^ 11 * P / (32 * X ^ 5 * a ^ 5 * Q ^ 9)
        ≤ 20 * z ^ 16 / (X * a) ^ 5 := by
    have hden_left : 0 < 32 * X ^ 5 * a ^ 5 * Q ^ 9 := by
      rw [hQ_def]
      positivity
    have hden_right : 0 < (X * a) ^ 5 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 5 * a ^ 5)
    linarith [hmul]
  calc
    45 * z ^ 11 * (z + a) ^ 11 * P / (32 * X ^ 5 * a ^ 5 * Q ^ 9)
        ≤ 20 * z ^ 16 / (X * a) ^ 5 := hstep
    _ ≤ 20 * (((101 / 100 : ℝ) * d) ^ 16) / (X * a) ^ 5 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz16_le (by norm_num))
            (by positivity)
    _ ≤ 25 * d ^ 16 / (X * a) ^ 5 := by
          have hnum : 20 * (((101 / 100 : ℝ) * d) ^ 16) ≤ 25 * d ^ 16 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 16) =
                (101 / 100 : ℝ) ^ 16 * d ^ 16 by ring]
            have hconst : 20 * (101 / 100 : ℝ) ^ 16 ≤ 25 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 16)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

private theorem sec7_ra_dBreve_deriv6_image_sharp_close {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve'''''' X a (Ffun X a z)| ≤ 150 * d ^ 19 / (X * a) ^ 6 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (51 / 100 : ℝ) * z := by nlinarith
  set P : ℝ :=
    33 * a ^ 14 + 594 * a ^ 13 * z + 5082 * a ^ 12 * z ^ 2 +
      27688 * a ^ 11 * z ^ 3 + 107664 * a ^ 10 * z ^ 4 +
      315840 * a ^ 9 * z ^ 5 + 719656 * a ^ 8 * z ^ 6 +
      1291968 * a ^ 7 * z ^ 7 + 1834488 * a ^ 6 * z ^ 8 +
      2049144 * a ^ 5 * z ^ 9 + 1772544 * a ^ 4 * z ^ 10 +
      1152144 * a ^ 3 * z ^ 11 + 532728 * a ^ 2 * z ^ 12 +
      157248 * a * z ^ 13 + 22464 * z ^ 14 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 11 ≤ Q ^ 11 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 11
  have hP_bound : P ≤ 700000 * z ^ 14 := by
    have h1 : a ^ 14 ≤ (51 / 100 : ℝ) ^ 14 * z ^ 14 := by
      simpa [mul_pow] using pow_le_pow_left₀ ha.le haz 14
    have h2 : a ^ 13 * z ≤ (51 / 100 : ℝ) ^ 13 * z ^ 14 := by
      calc
        a ^ 13 * z ≤ (((51 / 100 : ℝ) * z) ^ 13) * z :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 13) hz.le
        _ = (51 / 100 : ℝ) ^ 13 * z ^ 14 := by ring
    have h3 : a ^ 12 * z ^ 2 ≤ (51 / 100 : ℝ) ^ 12 * z ^ 14 := by
      calc
        a ^ 12 * z ^ 2 ≤ (((51 / 100 : ℝ) * z) ^ 12) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 12) (by positivity)
        _ = (51 / 100 : ℝ) ^ 12 * z ^ 14 := by ring
    have h4 : a ^ 11 * z ^ 3 ≤ (51 / 100 : ℝ) ^ 11 * z ^ 14 := by
      calc
        a ^ 11 * z ^ 3 ≤ (((51 / 100 : ℝ) * z) ^ 11) * z ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 11) (by positivity)
        _ = (51 / 100 : ℝ) ^ 11 * z ^ 14 := by ring
    have h5 : a ^ 10 * z ^ 4 ≤ (51 / 100 : ℝ) ^ 10 * z ^ 14 := by
      calc
        a ^ 10 * z ^ 4 ≤ (((51 / 100 : ℝ) * z) ^ 10) * z ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 10) (by positivity)
        _ = (51 / 100 : ℝ) ^ 10 * z ^ 14 := by ring
    have h6 : a ^ 9 * z ^ 5 ≤ (51 / 100 : ℝ) ^ 9 * z ^ 14 := by
      calc
        a ^ 9 * z ^ 5 ≤ (((51 / 100 : ℝ) * z) ^ 9) * z ^ 5 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 9) (by positivity)
        _ = (51 / 100 : ℝ) ^ 9 * z ^ 14 := by ring
    have h7 : a ^ 8 * z ^ 6 ≤ (51 / 100 : ℝ) ^ 8 * z ^ 14 := by
      calc
        a ^ 8 * z ^ 6 ≤ (((51 / 100 : ℝ) * z) ^ 8) * z ^ 6 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 8) (by positivity)
        _ = (51 / 100 : ℝ) ^ 8 * z ^ 14 := by ring
    have h8 : a ^ 7 * z ^ 7 ≤ (51 / 100 : ℝ) ^ 7 * z ^ 14 := by
      calc
        a ^ 7 * z ^ 7 ≤ (((51 / 100 : ℝ) * z) ^ 7) * z ^ 7 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 7) (by positivity)
        _ = (51 / 100 : ℝ) ^ 7 * z ^ 14 := by ring
    have h9 : a ^ 6 * z ^ 8 ≤ (51 / 100 : ℝ) ^ 6 * z ^ 14 := by
      calc
        a ^ 6 * z ^ 8 ≤ (((51 / 100 : ℝ) * z) ^ 6) * z ^ 8 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 6) (by positivity)
        _ = (51 / 100 : ℝ) ^ 6 * z ^ 14 := by ring
    have h10 : a ^ 5 * z ^ 9 ≤ (51 / 100 : ℝ) ^ 5 * z ^ 14 := by
      calc
        a ^ 5 * z ^ 9 ≤ (((51 / 100 : ℝ) * z) ^ 5) * z ^ 9 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 5) (by positivity)
        _ = (51 / 100 : ℝ) ^ 5 * z ^ 14 := by ring
    have h11 : a ^ 4 * z ^ 10 ≤ (51 / 100 : ℝ) ^ 4 * z ^ 14 := by
      calc
        a ^ 4 * z ^ 10 ≤ (((51 / 100 : ℝ) * z) ^ 4) * z ^ 10 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 4) (by positivity)
        _ = (51 / 100 : ℝ) ^ 4 * z ^ 14 := by ring
    have h12 : a ^ 3 * z ^ 11 ≤ (51 / 100 : ℝ) ^ 3 * z ^ 14 := by
      calc
        a ^ 3 * z ^ 11 ≤ (((51 / 100 : ℝ) * z) ^ 3) * z ^ 11 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 3) (by positivity)
        _ = (51 / 100 : ℝ) ^ 3 * z ^ 14 := by ring
    have h13 : a ^ 2 * z ^ 12 ≤ (51 / 100 : ℝ) ^ 2 * z ^ 14 := by
      calc
        a ^ 2 * z ^ 12 ≤ (((51 / 100 : ℝ) * z) ^ 2) * z ^ 12 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 2) (by positivity)
        _ = (51 / 100 : ℝ) ^ 2 * z ^ 14 := by ring
    have h14 : a * z ^ 13 ≤ (51 / 100 : ℝ) * z ^ 14 := by
      calc
        a * z ^ 13 ≤ ((51 / 100 : ℝ) * z) * z ^ 13 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = (51 / 100 : ℝ) * z ^ 14 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      pow_nonneg hz.le 14]
  have hza_bound : (z + a) ^ 2 ≤ ((151 / 100 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (151 / 100 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hlin_bound : a + 2 * z ≤ (251 / 100 : ℝ) * z := by nlinarith
  have hcore :
      315 * (z + a) ^ 2 * (a + 2 * z) * P ≤ 7168 * 3 ^ 11 * z ^ 17 := by
    calc
      315 * (z + a) ^ 2 * (a + 2 * z) * P
          ≤ 315 * (((151 / 100 : ℝ) * z) ^ 2) *
              ((251 / 100 : ℝ) * z) * (700000 * z ^ 14) := by
            gcongr
      _ = (315 * (151 / 100 : ℝ) ^ 2 * (251 / 100 : ℝ) * 700000) * z ^ 17 := by
            ring
      _ ≤ 7168 * 3 ^ 11 * z ^ 17 := by
            have hconst : 315 * (151 / 100 : ℝ) ^ 2 * (251 / 100 : ℝ) * 700000 ≤
                7168 * 3 ^ 11 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P ≤
        7168 * z ^ 19 * Q ^ 11 := by
    calc
      315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P
          = z ^ 13 * (z + a) ^ 11 * (315 * (z + a) ^ 2 * (a + 2 * z) * P) := by
            ring
      _ ≤ z ^ 13 * (z + a) ^ 11 * (7168 * 3 ^ 11 * z ^ 17) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 7168 * z ^ 19 * (((3 : ℝ) * z * (z + a)) ^ 11) := by ring
      _ ≤ 7168 * z ^ 19 * Q ^ 11 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz19_le : z ^ 19 ≤ ((101 / 100 : ℝ) * d) ^ 19 :=
    pow_le_pow_left₀ hz.le hzhi 19
  rw [dBreve_deriv6_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P /
          (64 * X ^ 6 * a ^ 6 * Q ^ 11)
        ≤ 112 * z ^ 19 / (X * a) ^ 6 := by
    have hden_left : 0 < 64 * X ^ 6 * a ^ 6 * Q ^ 11 := by
      rw [hQ_def]
      positivity
    have hden_right : 0 < (X * a) ^ 6 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 6 * a ^ 6)
    linarith [hmul]
  calc
    315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P /
          (64 * X ^ 6 * a ^ 6 * Q ^ 11)
        ≤ 112 * z ^ 19 / (X * a) ^ 6 := hstep
    _ ≤ 112 * (((101 / 100 : ℝ) * d) ^ 19) / (X * a) ^ 6 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz19_le (by norm_num))
            (by positivity)
    _ ≤ 150 * d ^ 19 / (X * a) ^ 6 := by
          have hnum : 112 * (((101 / 100 : ℝ) * d) ^ 19) ≤ 150 * d ^ 19 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 19) =
                (101 / 100 : ℝ) ^ 19 * d ^ 19 by ring]
            have hconst : 112 * (101 / 100 : ℝ) ^ 19 ≤ 150 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 19)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

private theorem sec7_ra_dBreve_iteratedDeriv1_eventually {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    iteratedDeriv 1 (dBreve X a) =ᶠ[nhds (Ffun X a d)] dBreve' X a := by
  have hright := sec7_ra_Ffun_dBreve_eventually (X := X) (a := a) (d := d) hX ha hd
  filter_upwards [hright] with y hy
  rw [iteratedDeriv_one]
  have h := dBreve_hasDerivAt_Ffun (X := X) (a := a) (d := dBreve X a y)
    hX ha dBreve_pos
  have hder : deriv (dBreve X a) (Ffun X a (dBreve X a y)) =
      dBreve' X a (Ffun X a (dBreve X a y)) := h.deriv
  simpa [hy] using hder

private theorem sec7_ra_dBreve_iteratedDeriv2_eventually {X a d : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    iteratedDeriv 2 (dBreve X a) =ᶠ[nhds (Ffun X a d)] dBreve'' X a := by
  have hright := sec7_ra_Ffun_dBreve_eventually (X := X) (a := a) (d := d) hX ha hd
  filter_upwards [hright] with y hy
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  have hev := sec7_ra_dBreve_iteratedDeriv1_eventually
    (X := X) (a := a) (d := dBreve X a y) hX ha dBreve_pos
  have hev_y : iteratedDeriv 1 (dBreve X a) =ᶠ[nhds y] dBreve' X a := by
    simpa [hy] using hev
  have h := dBreve_deriv1_hasDerivAt_Ffun (X := X) (a := a) (d := dBreve X a y)
    hX ha dBreve_pos
  calc
    deriv (iteratedDeriv 1 (dBreve X a)) y
        = deriv (dBreve' X a) y := Filter.EventuallyEq.deriv_eq hev_y
    _ = dBreve'' X a y := by simpa [hy] using h.deriv

private theorem sec7_ra_dBreveD_hasDerivAt_Ffun {X a d : ℝ} {l : ℕ}
    (hl : l ≤ 5) (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    HasDerivAt (sec7_ra_dBreveD X a l)
      (sec7_ra_dBreveD X a (l + 1) (Ffun X a d)) (Ffun X a d) := by
  interval_cases l
  · simpa [sec7_ra_dBreveD] using dBreve_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  · simpa [sec7_ra_dBreveD] using
      dBreve_deriv1_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  · simpa [sec7_ra_dBreveD] using
      dBreve_deriv2_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  · simpa [sec7_ra_dBreveD] using
      dBreve_deriv3_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  · simpa [sec7_ra_dBreveD] using
      dBreve_deriv4_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd
  · simpa [sec7_ra_dBreveD] using
      dBreve_deriv5_hasDerivAt_Ffun (X := X) (a := a) (d := d) hX ha hd

theorem sec7_ra_B3H_hasDerivAt {P : Globals} {S : Scale P} {a d j : ℝ} {l : ℕ}
    (hl : l ≤ 5) (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    HasDerivAt (sec7_ra_B3H P.X a j l)
      (deriv (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j (l + 1) d) d := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hFraw := Ffun_hasDerivAt_d P.X a d (ne_of_gt hd) (by positivity)
  have hF : HasDerivAt (fun t => Ffun P.X a t)
      (deriv (fun t => Ffun P.X a t) d) d := by
    rw [hFraw.deriv]
    exact hFraw
  have hFj : HasDerivAt (fun t => Ffun P.X a t + j)
      (deriv (fun t => Ffun P.X a t) d) d := by
    simpa using hF.add_const j
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
      (t := Ffun P.X a d + j) hAD ha_lo ha_hi hshift
  have hdb_shift : HasDerivAt (sec7_ra_dBreveD P.X a l)
      (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + j)) (Ffun P.X a d + j) := by
    have h :=
      sec7_ra_dBreveD_hasDerivAt_Ffun (X := P.X) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + j)) hl P.X_pos ha0 dBreve_pos
    simpa [himg] using h
  have hdb_base : HasDerivAt (sec7_ra_dBreveD P.X a l)
      (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d)) (Ffun P.X a d) :=
    sec7_ra_dBreveD_hasDerivAt_Ffun (X := P.X) (a := a) (d := d) hl P.X_pos ha0 hd
  have hmain := (hdb_shift.comp d hFj).sub (hdb_base.comp d hF)
  convert hmain using 1
  · simp [sec7_ra_B3H]
    ring

private theorem sec7_ra_B3H_mvt_bound {P : Globals} {S : Scale P} {a d j C : ℝ} {l : ℕ}
    (hl : l ≤ 5) (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S)
    (hbound : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      |sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + s)| ≤ C) :
    |sec7_ra_B3H P.X a j l d| ≤ C * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set g : ℝ → ℝ := fun s => sec7_ra_dBreveD P.X a l (Ffun P.X a d + s) with hg_def
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      HasDerivAt g (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + s)) s := by
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, _hlo, _hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hdb :=
      sec7_ra_dBreveD_hasDerivAt_Ffun (X := P.X) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) hl P.X_pos ha0 dBreve_pos
    have hdb_at : HasDerivAt (sec7_ra_dBreveD P.X a l)
        (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + s))
        (Ffun P.X a d + s) := by
      simpa [himg] using hdb
    have hlin : HasDerivAt (fun y : ℝ => Ffun P.X a d + y) 1 s := by
      simpa using (hasDerivAt_id s).const_add (Ffun P.X a d)
    simpa [g, hg_def] using hdb_at.comp s hlin
  have hmvt :=
    (convex_uIcc (0 : ℝ) j).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hderiv s hs).hasDerivWithinAt)
      (fun s hs => by simpa [Real.norm_eq_abs] using hbound s hs)
      (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hmvt_abs : |g j - g 0| ≤ C * |j| := by
    simpa [Real.norm_eq_abs] using hmvt
  simpa [g, hg_def, sec7_ra_B3H] using hmvt_abs

private theorem sec7_ra_B3_segment_preimage_close {P : Globals} {S : Scale P}
    {a d j s : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100)
    (hs : s ∈ Set.uIcc (0 : ℝ) j) :
    ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
      (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hqpos : 0 < qd := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1
  have hcont : ContinuousOn (fun u => Ffun P.X a u) (Set.uIcc d qd) := by
    intro u hu
    have hu_pos : 0 < u := by
      rcases le_total d qd with hdq | hqd
      · rw [uIcc_of_le hdq] at hu
        exact lt_of_lt_of_le hd hu.1
      · rw [uIcc_of_ge hqd] at hu
        exact lt_of_lt_of_le hqpos hu.1
    exact (Ffun_contDiffAt (X := P.X) (a := a) (d := u) (ne_of_gt hu_pos)
      (by positivity)).continuousAt.continuousWithinAt
  have hyu : Ffun P.X a d + s ∈ Set.uIcc (Ffun P.X a d) (Ffun P.X a qd) := by
    rw [hqspec]
    rcases le_total (0 : ℝ) j with hj | hj
    · rw [uIcc_of_le hj] at hs
      rw [uIcc_of_le (by linarith : Ffun P.X a d ≤ Ffun P.X a d + j)]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · rw [uIcc_of_ge hj] at hs
      rw [uIcc_of_ge (by linarith : Ffun P.X a d + j ≤ Ffun P.X a d)]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rcases intermediate_value_uIcc hcont hyu with ⟨u, huI, hu_eq⟩
  have hu_close : (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
    rcases le_total d qd with hdq | hqd
    · rw [uIcc_of_le hdq] at huI
      constructor
      · nlinarith [hd, huI.1]
      · exact le_trans huI.2 hqwin.2
    · rw [uIcc_of_ge hqd] at huI
      constructor
      · exact le_trans hqwin.1 huI.1
      · nlinarith [hd, huI.2]
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hu_close.1
  exact ⟨u, hu_pos, hu_eq, hu_close.1, hu_close.2⟩

private theorem sec7_ra_B3H_mvt_bound_image {P : Globals} {S : Scale P}
    {a d j C : ℝ} {l : ℕ}
    (hl : l ≤ 5) (ha_lo : S.A / 5 ≤ a)
    (hpre : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
        (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d)
    (hbound : ∀ u, 0 < u →
      (99 / 100 : ℝ) * d ≤ u → u ≤ (101 / 100 : ℝ) * d →
      |sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a u)| ≤ C) :
    |sec7_ra_B3H P.X a j l d| ≤ C * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set g : ℝ → ℝ := fun s => sec7_ra_dBreveD P.X a l (Ffun P.X a d + s) with hg_def
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      HasDerivAt g (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + s)) s := by
    intro s hs
    rcases hpre s hs with ⟨u, hu0, hu_eq, _hulo, _huhi⟩
    have hdb :=
      sec7_ra_dBreveD_hasDerivAt_Ffun (X := P.X) (a := a)
        (d := u) hl P.X_pos ha0 hu0
    have hdb_at : HasDerivAt (sec7_ra_dBreveD P.X a l)
        (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + s))
        (Ffun P.X a d + s) := by
      simpa [← hu_eq] using hdb
    have hlin : HasDerivAt (fun y : ℝ => Ffun P.X a d + y) 1 s := by
      simpa using (hasDerivAt_id s).const_add (Ffun P.X a d)
    simpa [g, hg_def] using hdb_at.comp s hlin
  have hbnd : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      |sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a d + s)| ≤ C := by
    intro s hs
    rcases hpre s hs with ⟨u, hu0, hu_eq, hulo, huhi⟩
    simpa [← hu_eq] using hbound u hu0 hulo huhi
  have hmvt :=
    (convex_uIcc (0 : ℝ) j).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hderiv s hs).hasDerivWithinAt)
      (fun s hs => by simpa [Real.norm_eq_abs] using hbnd s hs)
      (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hmvt_abs : |g j - g 0| ≤ C * |j| := by
    simpa [Real.norm_eq_abs] using hmvt
  simpa [g, hg_def, sec7_ra_B3H] using hmvt_abs

private theorem sec7_ra_B3H_bounds_sharp {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3H P.X a j 1 d| ≤ (2 * d ^ 7 / (P.X * a) ^ 2) * |j| ∧
      |sec7_ra_B3H P.X a j 2 d| ≤ (2 * d ^ 10 / (P.X * a) ^ 3) * |j| ∧
      |sec7_ra_B3H P.X a j 3 d| ≤ (6 * d ^ 13 / (P.X * a) ^ 4) * |j| ∧
      |sec7_ra_B3H P.X a j 4 d| ≤ (25 * d ^ 16 / (P.X * a) ^ 5) * |j| ∧
      |sec7_ra_B3H P.X a j 5 d| ≤ (150 * d ^ 19 / (P.X * a) ^ 6) * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hpre : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
        (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
    intro s hs
    exact sec7_ra_B3_segment_preimage_close (P := P) (S := S) (a := a) (d := d)
      (j := j) (s := s) hAD ha_lo ha_hi hd hshift hclose hs
  have hH1 : |sec7_ra_B3H P.X a j 1 d| ≤
      (2 * d ^ 7 / (P.X * a) ^ 2) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 2 * d ^ 7 / (P.X * a) ^ 2) (l := 1) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv2_image_sharp_close (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  have hH2 : |sec7_ra_B3H P.X a j 2 d| ≤
      (2 * d ^ 10 / (P.X * a) ^ 3) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 2 * d ^ 10 / (P.X * a) ^ 3) (l := 2) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv3_image_sharp_close (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  have hH3 : |sec7_ra_B3H P.X a j 3 d| ≤
      (6 * d ^ 13 / (P.X * a) ^ 4) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 6 * d ^ 13 / (P.X * a) ^ 4) (l := 3) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv4_image_sharp_close (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  have hH4 : |sec7_ra_B3H P.X a j 4 d| ≤
      (25 * d ^ 16 / (P.X * a) ^ 5) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 25 * d ^ 16 / (P.X * a) ^ 5) (l := 4) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv5_image_sharp_close (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  have hH5 : |sec7_ra_B3H P.X a j 5 d| ≤
      (150 * d ^ 19 / (P.X * a) ^ 6) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 150 * d ^ 19 / (P.X * a) ^ 6) (l := 5) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv6_image_sharp_close (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  exact ⟨hH1, hH2, hH3, hH4, hH5⟩

theorem sec7_ra_iteratedDeriv_eq_of_chain {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) {n : ℕ}
    (hd : ∀ m < n, ∀ r ∈ s, HasDerivAt (F m) (F (m + 1) r) r) :
    ∀ m ≤ n, ∀ r ∈ s, iteratedDeriv m (F 0) r = F m r := by
  intro m
  induction m with
  | zero => intro _ r _; simp
  | succ m ih =>
      intro hm r hr
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv m (F 0) =ᶠ[nhds r] F m :=
        Filter.eventuallyEq_of_mem (hs.mem_nhds hr)
          (fun x hx => ih (le_of_lt (Nat.lt_of_succ_le hm)) x hx)
      rw [hev.deriv_eq]
      exact (hd m (Nat.lt_of_succ_le hm) r hr).deriv

private theorem sec7_ra_A1_model_iteratedDeriv_eq {X a d : ℝ} {k : ℕ}
    (hk : k ≤ 5) (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) :
    iteratedDeriv k
        (fun t : ℝ => -a * t ^ 2 * (t + a) ^ 2 /
          (6 * X * (a ^ 2 + 3 * a * t + 3 * t ^ 2))) d =
      sec7_ra_A1E X a k d := by
  have hchain : ∀ m < 5, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (sec7_ra_A1E X a m) (sec7_ra_A1E X a (m + 1) r) r := by
    intro m hm r hr
    exact sec7_ra_A1E_hasDerivAt (X := X) (a := a) (r := r) hX ha hr hm
  have hiter := sec7_ra_iteratedDeriv_eq_of_chain (F := sec7_ra_A1E X a)
    isOpen_Ioi hchain k hk d hd
  have hfun : (fun t : ℝ => -a * t ^ 2 * (t + a) ^ 2 /
          (6 * X * (a ^ 2 + 3 * a * t + 3 * t ^ 2))) = sec7_ra_A1E X a 0 := by
    funext t
    simp [sec7_ra_A1E, sec7_ra_A1P, sec7_ra_A1Q]
    ring
  rw [hfun]
  exact hiter

private theorem sec7_ra_A1E_bound {X a d : ℝ} {k : ℕ}
    (hk : k ≤ 5) (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (had : a ≤ d) :
    |sec7_ra_A1E X a k d|
      ≤ sec7_ra_A1Scale k * a * d ^ 2 / (X * d ^ k) := by
  have hQpos : 0 < sec7_ra_A1Q a d := by
    unfold sec7_ra_A1Q
    positivity
  have hQlo : 3 * d ^ 2 ≤ sec7_ra_A1Q a d := by
    unfold sec7_ra_A1Q
    have had0 : 0 ≤ a * d := mul_nonneg ha.le hd.le
    nlinarith [sq_nonneg a, had0]
  have hQpow2 : (3 * d ^ 2) ^ 2 ≤ (sec7_ra_A1Q a d) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hQlo 2
  have hQpow3 : (3 * d ^ 2) ^ 3 ≤ (sec7_ra_A1Q a d) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hQlo 3
  have hQpow4 : (3 * d ^ 2) ^ 4 ≤ (sec7_ra_A1Q a d) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hQlo 4
  have hQpow5 : (3 * d ^ 2) ^ 5 ≤ (sec7_ra_A1Q a d) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hQlo 5
  have hQpow6 : (3 * d ^ 2) ^ 6 ≤ (sec7_ra_A1Q a d) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hQlo 6
  have hdenpos : 0 < 6 * X * (sec7_ra_A1Q a d) ^ (k + 1) := by positivity
  rw [sec7_ra_A1E, abs_div, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos hdenpos]
  interval_cases k
  · have hsum : (a + d) ^ 2 ≤ 4 * d ^ 2 := by
      nlinarith [sq_nonneg (d - a)]
    have hP :
        |d ^ 2 * (a + d) ^ 2| ≤ 4 * d ^ 4 := by
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg d) (sq_nonneg (a + d)))]
      calc
        d ^ 2 * (a + d) ^ 2 ≤ d ^ 2 * (4 * d ^ 2) := by gcongr
        _ = 4 * d ^ 4 := by ring
    simp [sec7_ra_A1Scale, sec7_ra_A1P, sec7_ra_A1Q]
    field_simp [hX.ne', hd.ne', hQpos.ne']
    nlinarith [hP, hQlo, ha, hd, hX]
  · have h1 : a + d ≤ 2 * d := by nlinarith
    have h2 : a + 2 * d ≤ 3 * d := by nlinarith
    have h3 : 2 * a ^ 2 + 3 * a * d + 3 * d ^ 2 ≤ 8 * d ^ 2 := by
      nlinarith [sq_nonneg (d - a), mul_nonneg ha.le hd.le]
    have hP :
        d * (a + d) * (a + 2 * d) *
            (2 * a ^ 2 + 3 * a * d + 3 * d ^ 2) ≤ 48 * d ^ 5 := by
      calc
        d * (a + d) * (a + 2 * d) *
            (2 * a ^ 2 + 3 * a * d + 3 * d ^ 2)
            ≤ d * (2 * d) * (3 * d) * (8 * d ^ 2) := by gcongr
        _ = 48 * d ^ 5 := by ring
    change
      a *
          |d * (a + d) * (a + 2 * d) *
            (2 * a ^ 2 + 3 * a * d + 3 * d ^ 2)| /
          (6 * X * (sec7_ra_A1Q a d) ^ 2) ≤
        1 * a * d ^ 2 / (X * d ^ 1)
    rw [abs_of_nonneg (by positivity)]
    field_simp [hX.ne', hd.ne', hQpos.ne']
    nlinarith [hP, hQpow2, ha, hd, hX]
  · have ha6 : a ^ 6 ≤ d ^ 6 := by gcongr
    have ha5 : a ^ 5 * d ≤ d ^ 6 := by
      calc
        a ^ 5 * d ≤ d ^ 5 * d := by gcongr
        _ = d ^ 6 := by ring
    have ha4 : a ^ 4 * d ^ 2 ≤ d ^ 6 := by
      calc
        a ^ 4 * d ^ 2 ≤ d ^ 4 * d ^ 2 := by gcongr
        _ = d ^ 6 := by ring
    have ha3 : a ^ 3 * d ^ 3 ≤ d ^ 6 := by
      calc
        a ^ 3 * d ^ 3 ≤ d ^ 3 * d ^ 3 := by gcongr
        _ = d ^ 6 := by ring
    have ha2 : a ^ 2 * d ^ 4 ≤ d ^ 6 := by
      calc
        a ^ 2 * d ^ 4 ≤ d ^ 2 * d ^ 4 := by gcongr
        _ = d ^ 6 := by ring
    have ha1 : a * d ^ 5 ≤ d ^ 6 := by
      calc
        a * d ^ 5 ≤ d * d ^ 5 := by gcongr
        _ = d ^ 6 := by ring
    have hP :
        2 * (a ^ 6 + 6 * a ^ 5 * d + 15 * a ^ 4 * d ^ 2 +
            27 * a ^ 3 * d ^ 3 + 36 * a ^ 2 * d ^ 4 + 27 * a * d ^ 5 +
            9 * d ^ 6) ≤ 242 * d ^ 6 := by
      nlinarith
    change
      a *
          |2 * (a ^ 6 + 6 * a ^ 5 * d + 15 * a ^ 4 * d ^ 2 +
            27 * a ^ 3 * d ^ 3 + 36 * a ^ 2 * d ^ 4 + 27 * a * d ^ 5 +
            9 * d ^ 6)| /
          (6 * X * (sec7_ra_A1Q a d) ^ 3) ≤
        2 * a * d ^ 2 / (X * d ^ 2)
    rw [abs_of_nonneg (by positivity)]
    field_simp [hX.ne', hd.ne', hQpos.ne']
    nlinarith [hP, hQpow3, ha, hd, hX]
  · have h2 : a + 2 * d ≤ 3 * d := by nlinarith
    have h3 : a ^ 2 + 6 * a * d + 6 * d ^ 2 ≤ 13 * d ^ 2 := by
      nlinarith [sq_nonneg (d - a), mul_nonneg ha.le hd.le]
    have hP :
        6 * a ^ 4 * (a + 2 * d) * (a ^ 2 + 6 * a * d + 6 * d ^ 2)
          ≤ 234 * d ^ 7 := by
      calc
        6 * a ^ 4 * (a + 2 * d) * (a ^ 2 + 6 * a * d + 6 * d ^ 2)
            ≤ 6 * d ^ 4 * (3 * d) * (13 * d ^ 2) := by gcongr
        _ = 234 * d ^ 7 := by ring
    change
      a *
          |-6 * a ^ 4 * (a + 2 * d) *
            (a ^ 2 + 6 * a * d + 6 * d ^ 2)| /
          (6 * X * (sec7_ra_A1Q a d) ^ 4) ≤
        1 * a * d ^ 2 / (X * d ^ 3)
    rw [abs_of_nonpos (by
      have hnon : 0 ≤ 6 * a ^ 4 * (a + 2 * d) *
          (a ^ 2 + 6 * a * d + 6 * d ^ 2) := by positivity
      nlinarith)]
    field_simp [hX.ne', hd.ne', hQpos.ne']
    nlinarith [hP, hQpow4, ha, hd, hX]
  · have ha4 : a ^ 4 ≤ d ^ 4 := by gcongr
    have ha3 : a ^ 3 * d ≤ d ^ 4 := by
      calc
        a ^ 3 * d ≤ d ^ 3 * d := by gcongr
        _ = d ^ 4 := by ring
    have ha2 : a ^ 2 * d ^ 2 ≤ d ^ 4 := by
      calc
        a ^ 2 * d ^ 2 ≤ d ^ 2 * d ^ 2 := by gcongr
        _ = d ^ 4 := by ring
    have ha1 : a * d ^ 3 ≤ d ^ 4 := by
      calc
        a * d ^ 3 ≤ d * d ^ 3 := by gcongr
        _ = d ^ 4 := by ring
    have hpoly :
        a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 + 90 * a * d ^ 3 +
            45 * d ^ 4 ≤ 211 * d ^ 4 := by
      nlinarith
    have hP :
        24 * a ^ 4 *
          (a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 +
            90 * a * d ^ 3 + 45 * d ^ 4) ≤ 5064 * d ^ 8 := by
      calc
        24 * a ^ 4 *
          (a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 +
            90 * a * d ^ 3 + 45 * d ^ 4)
            ≤ 24 * d ^ 4 * (211 * d ^ 4) := by gcongr
        _ = 5064 * d ^ 8 := by ring
    have hPscaled :
        24 * a ^ 4 * d ^ 2 *
          (a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 +
            90 * a * d ^ 3 + 45 * d ^ 4) ≤ 5064 * d ^ 10 := by
      calc
        24 * a ^ 4 * d ^ 2 *
          (a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 +
            90 * a * d ^ 3 + 45 * d ^ 4)
            = (24 * a ^ 4 *
            (a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 +
              90 * a * d ^ 3 + 45 * d ^ 4)) * d ^ 2 := by ring
        _ ≤ (5064 * d ^ 8) * d ^ 2 := by gcongr
        _ = 5064 * d ^ 10 := by ring
    have hPscaled' :
        a ^ 4 * 24 * d ^ 2 *
            (a * (a * (a * (a + 15 * d) + d ^ 2 * 60) + d ^ 3 * 90) +
              d ^ 4 * 45) ≤ 5064 * d ^ 10 := by
      convert hPscaled using 1
      ring
    have hQpow5' : 243 * d ^ 10 ≤ (sec7_ra_A1Q a d) ^ 5 := by
      convert hQpow5 using 1
      ring
    change
      a *
          |24 * a ^ 4 *
            (a ^ 4 + 15 * a ^ 3 * d + 60 * a ^ 2 * d ^ 2 +
              90 * a * d ^ 3 + 45 * d ^ 4)| /
          (6 * X * (sec7_ra_A1Q a d) ^ 5) ≤
        4 * a * d ^ 2 / (X * d ^ 4)
    rw [abs_of_nonneg (by positivity)]
    field_simp [hX.ne', hd.ne', hQpos.ne']
    have hlower : 5832 * d ^ 10 ≤ 6 * (sec7_ra_A1Q a d) ^ 5 * 4 := by
      calc
        5832 * d ^ 10 = 6 * (243 * d ^ 10) * 4 := by ring
        _ ≤ 6 * (sec7_ra_A1Q a d) ^ 5 * 4 := by gcongr
    have hd10 : 0 ≤ d ^ 10 := by positivity
    nlinarith [hlower, hPscaled', hd10]
  · have h1 : a + d ≤ 2 * d := by nlinarith
    have h2 : a + 2 * d ≤ 3 * d := by nlinarith
    have h3 : a + 3 * d ≤ 4 * d := by nlinarith
    have h4 : 2 * a + 3 * d ≤ 5 * d := by nlinarith
    have hP :
        1080 * a ^ 4 * d * (a + d) * (a + 2 * d) *
            (a + 3 * d) * (2 * a + 3 * d) ≤ 129600 * d ^ 9 := by
      calc
        1080 * a ^ 4 * d * (a + d) * (a + 2 * d) *
            (a + 3 * d) * (2 * a + 3 * d)
            ≤ 1080 * d ^ 4 * d * (2 * d) * (3 * d) * (4 * d) * (5 * d) := by
            gcongr
        _ = 129600 * d ^ 9 := by ring
    have hPscaled :
        1080 * a ^ 4 * d ^ 4 * (a + d) * (a + 2 * d) *
            (a + 3 * d) * (2 * a + 3 * d) ≤ 129600 * d ^ 12 := by
      calc
        1080 * a ^ 4 * d ^ 4 * (a + d) * (a + 2 * d) *
            (a + 3 * d) * (2 * a + 3 * d)
            = (1080 * a ^ 4 * d * (a + d) * (a + 2 * d) *
                (a + 3 * d) * (2 * a + 3 * d)) * d ^ 3 := by ring
        _ ≤ (129600 * d ^ 9) * d ^ 3 := by gcongr
        _ = 129600 * d ^ 12 := by ring
    have hPscaled' :
        a ^ 4 * 1080 * d ^ 4 * (a + d) * (a + d * 2) *
            (a + d * 3) * (a * 2 + d * 3) ≤ 129600 * d ^ 12 := by
      convert hPscaled using 1
      ring
    have hQpow6' : 729 * d ^ 12 ≤ (sec7_ra_A1Q a d) ^ 6 := by
      convert hQpow6 using 1
      ring
    change
      a *
          |-1080 * a ^ 4 * d * (a + d) * (a + 2 * d) *
            (a + 3 * d) * (2 * a + 3 * d)| /
          (6 * X * (sec7_ra_A1Q a d) ^ 6) ≤
        30 * a * d ^ 2 / (X * d ^ 5)
    rw [abs_of_nonpos (by
      have hnon : 0 ≤ 1080 * a ^ 4 * d * (a + d) *
          (a + 2 * d) * (a + 3 * d) * (2 * a + 3 * d) := by positivity
      nlinarith)]
    field_simp [hX.ne', hd.ne', hQpos.ne']
    have hlower : 131220 * d ^ 12 ≤ 6 * (sec7_ra_A1Q a d) ^ 6 * 30 := by
      calc
        131220 * d ^ 12 = 6 * (729 * d ^ 12) * 30 := by ring
        _ ≤ 6 * (sec7_ra_A1Q a d) ^ 6 * 30 := by gcongr
    have hd12 : 0 ≤ d ^ 12 := by positivity
    nlinarith [hlower, hPscaled', hd12]

theorem sec7_ra_A1_bound {X a d : ℝ} {k : ℕ}
    (hk : k ≤ 5) (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (had : a ≤ d) :
    |iteratedDeriv k
        (fun t : ℝ => -dBreve' X a (Ffun X a t) -
          t ^ 2 * (t + a) ^ 2 / (6 * X * a)) d|
      ≤ sec7_ra_A1Scale k * a * d ^ 2 / (X * d ^ k) := by
  have heqv :
      (fun t : ℝ => -dBreve' X a (Ffun X a t) -
          t ^ 2 * (t + a) ^ 2 / (6 * X * a)) =ᶠ[nhds d]
        fun t : ℝ => -a * t ^ 2 * (t + a) ^ 2 /
          (6 * X * (a ^ 2 + 3 * a * t + 3 * t ^ 2)) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    exact sec7_ra_A1_identity (X := X) (a := a) (d := t) hX ha ht
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heqv]
  rw [sec7_ra_A1_model_iteratedDeriv_eq (X := X) (a := a) (d := d)
    (k := k) hk hX ha hd]
  exact sec7_ra_A1E_bound (X := X) (a := a) (d := d) (k := k) hk hX ha hd had

theorem sec7_ra_B3H_chain_open {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    ∃ s : Set ℝ, IsOpen s ∧ d ∈ s ∧
      (∀ r ∈ s, 0 < r) ∧
      ∀ l ≤ 5, ∀ r ∈ s,
        HasDerivAt (sec7_ra_B3H P.X a j l)
          (deriv (fun t => Ffun P.X a t) r * sec7_ra_B3H P.X a j (l + 1) r) r := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  obtain ⟨himg_shift, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
      (t := Ffun P.X a d + j) hAD ha_lo ha_hi hshift
  have hbase_y :=
    sec7_ra_Ffun_dBreve_eventually (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
  have hshift_y :
      ∀ᶠ y in nhds (Ffun P.X a d + j), Ffun P.X a (dBreve P.X a y) = y := by
    have h :=
      sec7_ra_Ffun_dBreve_eventually (X := P.X) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + j)) P.X_pos ha0 dBreve_pos
    simpa [himg_shift] using h
  have hF_cont : ContinuousAt (fun r => Ffun P.X a r) d :=
    (Ffun_contDiffAt5 (X := P.X) (a := a) (d := d) (ne_of_gt hd)
      (by positivity : d + a ≠ 0)).continuousAt
  have hbase_r :
      ∀ᶠ r in nhds d, Ffun P.X a (dBreve P.X a (Ffun P.X a r)) = Ffun P.X a r :=
    Filter.Tendsto.eventually hF_cont hbase_y
  have hshift_cont : ContinuousAt (fun r => Ffun P.X a r + j) d :=
    hF_cont.add continuousAt_const
  have hshift_r :
      ∀ᶠ r in nhds d,
        Ffun P.X a (dBreve P.X a (Ffun P.X a r + j)) = Ffun P.X a r + j :=
    Filter.Tendsto.eventually hshift_cont hshift_y
  have hpos_r : ∀ᶠ r in nhds d, 0 < r := eventually_gt_nhds hd
  have hall :
      ∀ᶠ r in nhds d,
        0 < r ∧
          Ffun P.X a (dBreve P.X a (Ffun P.X a r)) = Ffun P.X a r ∧
          Ffun P.X a (dBreve P.X a (Ffun P.X a r + j)) = Ffun P.X a r + j :=
    hpos_r.and (hbase_r.and hshift_r)
  rw [eventually_nhds_iff] at hall
  rcases hall with ⟨s, hs_sub, hs_open, hsd⟩
  refine ⟨s, hs_open, hsd, fun r hrs => (hs_sub r hrs).1, ?_⟩
  intro l hl r hrs
  have hr := hs_sub r hrs
  have hFraw := Ffun_hasDerivAt_d P.X a r (ne_of_gt hr.1)
    (by exact ne_of_gt (add_pos hr.1 ha0))
  have hF : HasDerivAt (fun t => Ffun P.X a t)
      (deriv (fun t => Ffun P.X a t) r) r := by
    rw [hFraw.deriv]
    exact hFraw
  have hFj : HasDerivAt (fun t => Ffun P.X a t + j)
      (deriv (fun t => Ffun P.X a t) r) r := by
    simpa using hF.add_const j
  have hdb_shift : HasDerivAt (sec7_ra_dBreveD P.X a l)
      (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a r + j)) (Ffun P.X a r + j) := by
    have h :=
      sec7_ra_dBreveD_hasDerivAt_Ffun (X := P.X) (a := a)
        (d := dBreve P.X a (Ffun P.X a r + j)) hl P.X_pos ha0 dBreve_pos
    rw [hr.2.2] at h
    simpa using h
  have hdb_base : HasDerivAt (sec7_ra_dBreveD P.X a l)
      (sec7_ra_dBreveD P.X a (l + 1) (Ffun P.X a r)) (Ffun P.X a r) := by
    have h :=
      sec7_ra_dBreveD_hasDerivAt_Ffun (X := P.X) (a := a)
        (d := dBreve P.X a (Ffun P.X a r)) hl P.X_pos ha0 dBreve_pos
    rw [hr.2.1] at h
    simpa using h
  have hmain := (hdb_shift.comp r hFj).sub (hdb_base.comp r hF)
  convert hmain using 1
  · simp [sec7_ra_B3H]
    ring

private noncomputable def sec7_ra_B3E (P : Globals) (a j : ℝ) : ℕ → ℝ → ℝ
  | 0 => sec7_ra_B3H P.X a j 0
  | 1 => fun d =>
      iteratedDeriv 1 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d
  | 2 => fun d =>
      iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d
  | 3 => fun d =>
      iteratedDeriv 3 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
        3 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 3 * sec7_ra_B3H P.X a j 3 d
  | 4 => fun d =>
      iteratedDeriv 4 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
        (4 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
            iteratedDeriv 3 (fun t => Ffun P.X a t) d +
          3 * iteratedDeriv 2 (fun t => Ffun P.X a t) d ^ 2) *
          sec7_ra_B3H P.X a j 2 d +
        6 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 2 *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 3 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 4 * sec7_ra_B3H P.X a j 4 d
  | 5 => fun d =>
      iteratedDeriv 5 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
        (5 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
            iteratedDeriv 4 (fun t => Ffun P.X a t) d +
          10 * iteratedDeriv 2 (fun t => Ffun P.X a t) d *
            iteratedDeriv 3 (fun t => Ffun P.X a t) d) *
          sec7_ra_B3H P.X a j 2 d +
        5 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
          (2 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
              iteratedDeriv 3 (fun t => Ffun P.X a t) d +
            3 * iteratedDeriv 2 (fun t => Ffun P.X a t) d ^ 2) *
          sec7_ra_B3H P.X a j 3 d +
        10 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 3 *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 4 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 5 * sec7_ra_B3H P.X a j 5 d
  | 6 => fun d =>
      iteratedDeriv 6 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
        (6 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
            iteratedDeriv 5 (fun t => Ffun P.X a t) d +
          15 * iteratedDeriv 2 (fun t => Ffun P.X a t) d *
            iteratedDeriv 4 (fun t => Ffun P.X a t) d +
          10 * iteratedDeriv 3 (fun t => Ffun P.X a t) d ^ 2) *
          sec7_ra_B3H P.X a j 2 d +
        (15 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 2 *
            iteratedDeriv 4 (fun t => Ffun P.X a t) d +
          60 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
            iteratedDeriv 2 (fun t => Ffun P.X a t) d *
            iteratedDeriv 3 (fun t => Ffun P.X a t) d +
          15 * iteratedDeriv 2 (fun t => Ffun P.X a t) d ^ 3) *
          sec7_ra_B3H P.X a j 3 d +
        (20 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 3 *
            iteratedDeriv 3 (fun t => Ffun P.X a t) d +
          45 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 2 *
            iteratedDeriv 2 (fun t => Ffun P.X a t) d ^ 2) *
          sec7_ra_B3H P.X a j 4 d +
        15 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 4 *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 5 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 6 * sec7_ra_B3H P.X a j 6 d
  | _ => fun _ => 0

theorem sec7_ra_Ffun_iter_hasDerivAt {P : Globals} {a r : ℝ} {m : ℕ}
    (ha : 0 < a) (hr : 0 < r) (hm : m < 6) :
    HasDerivAt (iteratedDeriv m (fun t => Ffun P.X a t))
      (iteratedDeriv (m + 1) (fun t => Ffun P.X a t) r) r := by
  rw [iteratedDeriv_succ]
  refine (?_ : DifferentiableAt ℝ (iteratedDeriv m (fun t => Ffun P.X a t)) r).hasDerivAt
  have hg : ContDiffAt ℝ 6 (fun t => Ffun P.X a t) r :=
    Ffun_contDiffAt6 (X := P.X) (a := a) (d := r) (ne_of_gt hr)
      (by exact ne_of_gt (add_pos hr ha))
  have hF : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun t => Ffun P.X a t)) r := by
    exact hg.differentiableAt_iteratedFDeriv (by exact_mod_cast hm)
  rw [iteratedDeriv_eq_equiv_comp]
  exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm.differentiableAt).comp r hF

private theorem sec7_ra_B3E_hasDerivAt {P : Globals} {a j r : ℝ} {m : ℕ}
    (ha : 0 < a) (hr : 0 < r) (hm : m < 6)
    (hH : ∀ l ≤ 5,
      HasDerivAt (sec7_ra_B3H P.X a j l)
        (iteratedDeriv 1 (fun t => Ffun P.X a t) r * sec7_ra_B3H P.X a j (l + 1) r) r) :
    HasDerivAt (sec7_ra_B3E P a j m) (sec7_ra_B3E P a j (m + 1) r) r := by
  interval_cases m
  · simpa [sec7_ra_B3E] using hH 0 (by norm_num)
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hH1 := hH 1 (by norm_num)
    have hmain := hF1.mul hH1
    convert hmain using 1
    simp [sec7_ra_B3E]
    ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hH1 := hH 1 (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hterm1 := hF2.mul hH1
    have hterm2 := (hF1.pow 2).mul hH2
    have hmain := hterm1.add hterm2
    convert hmain using 1
    simp [sec7_ra_B3E]
    ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hF3 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 3)
      ha hr (by norm_num)
    have hH1 := hH 1 (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hH3 := hH 3 (by norm_num)
    have hterm1 := hF3.mul hH1
    have hterm2 := ((hF1.mul hF2).mul hH2).const_mul 3
    have hterm3 := (hF1.pow 3).mul hH3
    have hmain := (hterm1.add hterm2).add hterm3
    convert hmain using 1
    all_goals
      first
      | funext x
        simp [sec7_ra_B3E]
        ring_nf
      | simp [sec7_ra_B3E]
        ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hF3 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 3)
      ha hr (by norm_num)
    have hF4 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 4)
      ha hr (by norm_num)
    have hH1 := hH 1 (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hH3 := hH 3 (by norm_num)
    have hH4 := hH 4 (by norm_num)
    have hterm1 := hF4.mul hH1
    have hcoef2a := (hF1.mul hF3).const_mul 4
    have hcoef2b := (hF2.pow 2).const_mul 3
    have hterm2 := (hcoef2a.add hcoef2b).mul hH2
    have hcoef3 := ((hF1.pow 2).mul hF2).const_mul 6
    have hterm3 := hcoef3.mul hH3
    have hterm4 := (hF1.pow 4).mul hH4
    have hmain := ((hterm1.add hterm2).add hterm3).add hterm4
    convert hmain using 1
    all_goals
      first
      | funext x
        simp [sec7_ra_B3E]
        ring_nf
      | simp [sec7_ra_B3E]
        ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hF3 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 3)
      ha hr (by norm_num)
    have hF4 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 4)
      ha hr (by norm_num)
    have hF5 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 5)
      ha hr (by norm_num)
    have hH1 := hH 1 (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hH3 := hH 3 (by norm_num)
    have hH4 := hH 4 (by norm_num)
    have hH5 := hH 5 (by norm_num)
    have hterm1 := hF5.mul hH1
    have hcoef2a := (hF1.mul hF4).const_mul 5
    have hcoef2b := (hF2.mul hF3).const_mul 10
    have hterm2 := (hcoef2a.add hcoef2b).mul hH2
    have hcoef3a := ((hF1.pow 2).mul hF3).const_mul 10
    have hcoef3b := (hF1.mul (hF2.pow 2)).const_mul 15
    have hterm3 := (hcoef3a.add hcoef3b).mul hH3
    have hcoef4 := ((hF1.pow 3).mul hF2).const_mul 10
    have hterm4 := hcoef4.mul hH4
    have hterm5 := (hF1.pow 5).mul hH5
    have hmain := ((((hterm1.add hterm2).add hterm3).add hterm4).add hterm5)
    convert hmain using 1
    all_goals
      first
      | funext x
        simp [sec7_ra_B3E]
        ring_nf
      | simp [sec7_ra_B3E]
        ring_nf

private theorem sec7_ra_B3_iteratedDeriv_eq {P : Globals} {S : Scale P} {a d j : ℝ} {k : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hshift : Ffun P.X a d + j ∈ sec7_tWin S) (hk : k ≤ 6) :
    iteratedDeriv k (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      sec7_ra_B3E P a j k d := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  obtain ⟨s, hs_open, hds, hs_pos, hHchain⟩ :=
    sec7_ra_B3H_chain_open (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd hshift
  have hEchain :
      ∀ m < 6, ∀ r ∈ s,
        HasDerivAt (sec7_ra_B3E P a j m) (sec7_ra_B3E P a j (m + 1) r) r := by
    intro m hm r hrs
    have hH' : ∀ l ≤ 5,
        HasDerivAt (sec7_ra_B3H P.X a j l)
          (iteratedDeriv 1 (fun t => Ffun P.X a t) r *
            sec7_ra_B3H P.X a j (l + 1) r) r := by
      intro l hl
      simpa [iteratedDeriv_one] using hHchain l hl r hrs
    exact sec7_ra_B3E_hasDerivAt (P := P) (a := a) (j := j) (r := r) (m := m)
      ha0 (hs_pos r hrs) hm hH'
  have hH_iter :
      iteratedDeriv k (sec7_ra_B3E P a j 0) d = sec7_ra_B3E P a j k d :=
    sec7_ra_iteratedDeriv_eq_of_chain (F := sec7_ra_B3E P a j) hs_open hEchain
      k hk d hds
  have hB_ev :
      (fun t => dBreve P.X a (Ffun P.X a t + j) - t)
        =ᶠ[nhds d] sec7_ra_B3E P a j 0 := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    have hspec : dBreve P.X a (Ffun P.X a t) = t :=
      dBreve_spec P.X_pos ha0 ht
    simp [sec7_ra_B3E, sec7_ra_B3H, sec7_ra_dBreveD, hspec]
  calc
    iteratedDeriv k (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d
        = iteratedDeriv k (sec7_ra_B3E P a j 0) d :=
          Filter.EventuallyEq.iteratedDeriv_eq k hB_ev
    _ = sec7_ra_B3E P a j k d := hH_iter

private theorem sec7_ra_B3H_bound {P : Globals} {S : Scale P} {a d j : ℝ} {l : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S)
    (hl1 : 1 ≤ l) (hl5 : l ≤ 5) :
    |sec7_ra_B3H P.X a j l d| ≤
      (sec7_ra_B3HScale l * S.D / S.F ^ (l + 1)) * |j| := by
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  interval_cases l
  · refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_ra_B3HScale 1 * S.D / S.F ^ (1 + 1)) (l := 1)
      (by norm_num) hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    have hscale :=
      (dBreve_sec7_tWin_scale (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin).2.2
    have hscale' : S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d + s)| ≤ sec7_cPh * S.D := by
      have hDcomm : S.Δ * P.H = S.D := by
        rw [mul_comm]
        rfl
      simpa [hDcomm, mul_assoc, mul_left_comm, mul_comm] using hscale
    rw [sec7_ra_dBreveD, sec7_ra_B3HScale]
    rw [le_div_iff₀ (pow_pos hFpos 2)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  · refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_ra_B3HScale 2 * S.D / S.F ^ (2 + 1)) (l := 2)
      (by norm_num) hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, hlo, hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hscale :=
      (dBreve_deriv3_scale_sec7_image (P := P) (S := S) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) hAD ha_lo ha_hi hlo hhi).2
    have hscale' :
        S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d + s)| ≤
          (10 ^ 80 : ℝ) * S.D := by
      simpa [himg, show P.H * S.Δ = S.D by rfl, mul_assoc, mul_left_comm, mul_comm]
        using hscale
    rw [sec7_ra_dBreveD, sec7_ra_B3HScale]
    rw [le_div_iff₀ (pow_pos hFpos 3)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  · refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_ra_B3HScale 3 * S.D / S.F ^ (3 + 1)) (l := 3)
      (by norm_num) hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, hlo, hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hscale :=
      (dBreve_deriv4_scale_sec7_image (P := P) (S := S) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) hAD ha_lo ha_hi hlo hhi).2
    have hscale' :
        S.F ^ 4 * |dBreve'''' P.X a (Ffun P.X a d + s)| ≤
          (10 ^ 100 : ℝ) * S.D := by
      simpa [himg, show P.H * S.Δ = S.D by rfl, mul_assoc, mul_left_comm, mul_comm]
        using hscale
    rw [sec7_ra_dBreveD, sec7_ra_B3HScale]
    rw [le_div_iff₀ (pow_pos hFpos 4)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  · refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_ra_B3HScale 4 * S.D / S.F ^ (4 + 1)) (l := 4)
      (by norm_num) hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, hlo, hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hscale :=
      (dBreve_deriv5_scale_wide_image (P := P) (S := S) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) hAD ha_lo ha_hi hlo hhi).2
    have hscale' :
        S.F ^ 5 * |dBreve''''' P.X a (Ffun P.X a d + s)| ≤
          (10 ^ 100 : ℝ) * S.D := by
      simpa [himg, show P.H * S.Δ = S.D by rfl, mul_assoc, mul_left_comm, mul_comm]
        using hscale
    rw [sec7_ra_dBreveD, sec7_ra_B3HScale]
    rw [le_div_iff₀ (pow_pos hFpos 5)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  · refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_ra_B3HScale 5 * S.D / S.F ^ (5 + 1)) (l := 5)
      (by norm_num) hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, hlo, hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hscale :=
      (dBreve_deriv6_scale_wide_image (P := P) (S := S) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) hAD ha_lo ha_hi hlo hhi).2
    have hscale' :
        S.F ^ 6 * |dBreve'''''' P.X a (Ffun P.X a d + s)| ≤
          (10 ^ 100 : ℝ) * S.D := by
      simpa [himg, show P.H * S.Δ = S.D by rfl, mul_assoc, mul_left_comm, mul_comm]
        using hscale
    rw [sec7_ra_dBreveD, sec7_ra_B3HScale]
    rw [le_div_iff₀ (pow_pos hFpos 6)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'

private theorem sec7_ra_B3_iteratedDeriv2_eq {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
        deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hda : d + a ≠ 0 := by positivity
  obtain ⟨himg, _hlo, _hhi⟩ :=
    dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
      (t := Ffun P.X a d + j) hAD ha_lo ha_hi hshift
  have hf0 : ContDiffAt ℝ 2 (fun t => Ffun P.X a t) d :=
    Ffun_contDiffAt (X := P.X) (a := a) (d := d) (ne_of_gt hd) hda
  have hfj : ContDiffAt ℝ 2 (fun t => Ffun P.X a t + j) d :=
    hf0.add contDiffAt_const
  have hg_base : ContDiffAt ℝ 2 (dBreve P.X a) (Ffun P.X a d) :=
    (sec7_ra_dBreve_contDiffAt5_Ffun (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd).of_le (by norm_num : ((2 : ℕ) : WithTop ℕ∞) ≤ 5)
  have hg_shift : ContDiffAt ℝ 2 (dBreve P.X a) (Ffun P.X a d + j) := by
    have h := (sec7_ra_dBreve_contDiffAt5_Ffun (X := P.X) (a := a)
      (d := dBreve P.X a (Ffun P.X a d + j)) P.X_pos ha0 dBreve_pos).of_le
        (by norm_num : ((2 : ℕ) : WithTop ℕ∞) ≤ 5)
    simpa [himg] using h
  have hcont_shift : ContDiffAt ℝ 2
      (fun t => dBreve P.X a (Ffun P.X a t + j)) d :=
    ContDiffAt.comp (x := d) (f := fun t => Ffun P.X a t + j)
      (g := dBreve P.X a) hg_shift hfj
  have hcont_base : ContDiffAt ℝ 2
      (fun t => dBreve P.X a (Ffun P.X a t)) d :=
    ContDiffAt.comp (x := d) (f := fun t => Ffun P.X a t)
      (g := dBreve P.X a) hg_base hf0
  have hB_ev :
      (fun t => dBreve P.X a (Ffun P.X a t + j) - t)
        =ᶠ[nhds d]
      (fun t => dBreve P.X a (Ffun P.X a t + j) -
        dBreve P.X a (Ffun P.X a t)) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    rw [dBreve_spec (X := P.X) (a := a) (d := t) P.X_pos ha0 ht]
  have hiter_sub :
      iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j)) d -
          iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t)) d := by
    calc
      iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d
          = iteratedDeriv 2
              (fun t => dBreve P.X a (Ffun P.X a t + j) -
                dBreve P.X a (Ffun P.X a t)) d :=
            Filter.EventuallyEq.iteratedDeriv_eq 2 hB_ev
      _ = iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j)) d -
          iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t)) d :=
            iteratedDeriv_fun_sub hcont_shift hcont_base
  have hFraw := Ffun_hasDerivAt_d P.X a d (ne_of_gt hd) hda
  have hF : HasDerivAt (fun t => Ffun P.X a t)
      (deriv (fun t => Ffun P.X a t) d) d := by
    rw [hFraw.deriv]
    exact hFraw
  have hder_j : deriv (fun t => Ffun P.X a t + j) d =
      deriv (fun t => Ffun P.X a t) d := (hF.add_const j).deriv
  have hiter2_j : iteratedDeriv 2 (fun t => Ffun P.X a t + j) d =
      iteratedDeriv 2 (fun t => Ffun P.X a t) d := by
    rw [show (fun t : ℝ => Ffun P.X a t + j) =
        fun t : ℝ => (fun u => Ffun P.X a u) t + (fun _ : ℝ => j) t by rfl]
    rw [iteratedDeriv_fun_add hf0 contDiffAt_const]
    simp [iteratedDeriv_const]
  have hd1_base : deriv (dBreve P.X a) (Ffun P.X a d) =
      dBreve' P.X a (Ffun P.X a d) :=
    (dBreve_hasDerivAt_Ffun (X := P.X) (a := a) (d := d) P.X_pos ha0 hd).deriv
  have hd2_base : iteratedDeriv 2 (dBreve P.X a) (Ffun P.X a d) =
      dBreve'' P.X a (Ffun P.X a d) :=
    Filter.EventuallyEq.eq_of_nhds
      (sec7_ra_dBreve_iteratedDeriv2_eventually (X := P.X) (a := a) (d := d)
        P.X_pos ha0 hd)
  have hd1_shift : deriv (dBreve P.X a) (Ffun P.X a d + j) =
      dBreve' P.X a (Ffun P.X a d + j) := by
    have h := dBreve_hasDerivAt_Ffun (X := P.X) (a := a)
      (d := dBreve P.X a (Ffun P.X a d + j)) P.X_pos ha0 dBreve_pos
    simpa [himg] using h.deriv
  have hd2_shift : iteratedDeriv 2 (dBreve P.X a) (Ffun P.X a d + j) =
      dBreve'' P.X a (Ffun P.X a d + j) := by
    have hev := sec7_ra_dBreve_iteratedDeriv2_eventually (X := P.X) (a := a)
      (d := dBreve P.X a (Ffun P.X a d + j)) P.X_pos ha0 dBreve_pos
    exact Filter.EventuallyEq.eq_of_nhds (by simpa [himg] using hev)
  have hcomp_shift := iteratedDeriv_comp_two (𝕜 := ℝ)
    (g := dBreve P.X a) (f := fun t => Ffun P.X a t + j) (x := d)
    hg_shift hfj
  have hcomp_base := iteratedDeriv_comp_two (𝕜 := ℝ)
    (g := dBreve P.X a) (f := fun t => Ffun P.X a t) (x := d)
    hg_base hf0
  rw [hiter_sub]
  change iteratedDeriv 2 ((dBreve P.X a) ∘ (fun t => Ffun P.X a t + j)) d -
      iteratedDeriv 2 ((dBreve P.X a) ∘ (fun t => Ffun P.X a t)) d =
    iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
      deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d
  rw [hcomp_shift, hcomp_base]
  rw [hd2_shift, hd1_shift, hd2_base, hd1_base, hder_j, hiter2_j]
  simp [sec7_ra_B3H, sec7_ra_dBreveD]
  ring

private theorem sec7_ra_B3_iteratedDeriv2_implicit_eq {P : Globals} {S : Scale P}
    {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      iteratedDeriv 2 (fun t => Ffun P.X a t) d /
          deriv (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d) -
        deriv (fun t => Ffun P.X a t) d ^ 2 *
          iteratedDeriv 2 (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d) /
          deriv (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d) ^ 3 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqpos : 0 < qd := by
    rw [hqd_def, sec7_ra_B3q]
    exact dBreve_pos
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hd_ne : deriv (fun t => Ffun P.X a t) d ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hd
  have hq_ne : deriv (fun t => Ffun P.X a t) qd ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hqpos
  have hiter := sec7_ra_B3_iteratedDeriv2_eq (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd hshift
  rw [hiter]
  simp only [sec7_ra_B3H, sec7_ra_dBreveD]
  rw [show Ffun P.X a d + j = Ffun P.X a qd by rw [hqspec]]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hd]
  field_simp [hd_ne, hq_ne]
  ring

private theorem sec7_ra_B3_bound_sharp_k2 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScale 2 * |j| * d ^ 2 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hAden_pos : 0 < P.X * a := mul_pos P.X_pos ha0
  have hiter := sec7_ra_B3_iteratedDeriv2_eq (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd hshift
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, _hF3, _hF4, _hF5⟩
  rcases sec7_ra_B3H_bounds_sharp (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2, _hH3, _hH4, _hH5⟩
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF1sq : |deriv (fun t => Ffun P.X a t) d| ^ 2 ≤
      (7 * P.X * a / d ^ 4) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hF1ub_nonneg).2 hF1
  calc
    |iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
            deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d| := by
          rw [hiter]
    _ ≤ |iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d| +
        |deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d| := abs_add_le _ _
    _ = |iteratedDeriv 2 (fun t => Ffun P.X a t) d| *
          |sec7_ra_B3H P.X a j 1 d| +
        |deriv (fun t => Ffun P.X a t) d| ^ 2 *
          |sec7_ra_B3H P.X a j 2 d| := by
          rw [abs_mul, abs_mul, abs_pow]
    _ ≤ (26 * P.X * a / d ^ 5) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 2 * ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
          exact add_le_add
            (mul_le_mul hF2 hH1 (abs_nonneg _) hF2ub_nonneg)
            (mul_le_mul hF1sq hH2 (abs_nonneg _) (sq_nonneg _))
    _ = 150 * |j| * d ^ 2 / (P.X * a) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ ≤ sec7_ra_B3SharpScale 2 * |j| * d ^ 2 / (P.X * a) := by
          simp [sec7_ra_B3SharpScale]
          gcongr
          norm_num

private theorem sec7_ra_B3_iteratedDeriv3_implicit_eq {P : Globals} {S : Scale P}
    {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    let qd := sec7_ra_B3q P.X a j d
    let F1d := deriv (fun t => Ffun P.X a t) d
    let F2d := iteratedDeriv 2 (fun t => Ffun P.X a t) d
    let F3d := iteratedDeriv 3 (fun t => Ffun P.X a t) d
    let F1q := deriv (fun t => Ffun P.X a t) qd
    let F2q := iteratedDeriv 2 (fun t => Ffun P.X a t) qd
    let F3q := iteratedDeriv 3 (fun t => Ffun P.X a t) qd
    iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      - (F1d ^ 3 * F1q * F3q - 3 * F1d ^ 3 * F2q ^ 2 +
          3 * F1d * F2d * F1q ^ 2 * F2q - F3d * F1q ^ 4) / F1q ^ 5 := by
  dsimp
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqpos : 0 < qd := by
    rw [hqd_def, sec7_ra_B3q]
    exact dBreve_pos
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hd_ne : deriv (fun t => Ffun P.X a t) d ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hd
  have hq_ne : deriv (fun t => Ffun P.X a t) qd ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hqpos
  have hiter := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
    (d := d) (j := j) (k := 3) hAD ha_lo ha_hi hd hshift (by norm_num)
  rw [hiter]
  simp only [sec7_ra_B3E, sec7_ra_B3H, sec7_ra_dBreveD]
  rw [iteratedDeriv_one]
  rw [show Ffun P.X a d + j = Ffun P.X a qd by rw [hqspec]]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv3_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv3_Ffun_eq P.X_pos ha0 hd]
  field_simp [hd_ne, hq_ne]
  ring

private theorem sec7_ra_B3_bound_sharp_k3 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScale 3 * |j| * d / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hAden_pos : 0 < P.X * a := mul_pos P.X_pos ha0
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  have hiter :
      iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F3 * H1 + 3 * F1 * F2 * H2 + F1 ^ 3 * H3 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 3) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, H1, H2, H3, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, _hF4, _hF5⟩
  rcases sec7_ra_B3H_bounds_sharp (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2, hH3, _hH4, _hH5⟩
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 128 * P.X * a / d ^ 6 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hterm1 : |F3 * H1| ≤
      (128 * P.X * a / d ^ 6) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF3 hH1 (abs_nonneg _) hF3ub_nonneg
  have hterm2 : |3 * F1 * F2 * H2| ≤
      3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) *
        ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    gcongr
  have hF1pow3 : |F1| ^ 3 ≤ (7 * P.X * a / d ^ 4) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 3
  have hterm3 : |F1 ^ 3 * H3| ≤
      (7 * P.X * a / d ^ 4) ^ 3 * ((6 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow3 hH3 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 3)
  calc
    |iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F3 * H1 + 3 * F1 * F2 * H2 + F1 ^ 3 * H3| := by rw [hiter]
    _ ≤ |F3 * H1| + |3 * F1 * F2 * H2| + |F1 ^ 3 * H3| := by
          calc
            |F3 * H1 + 3 * F1 * F2 * H2 + F1 ^ 3 * H3|
                ≤ |F3 * H1 + 3 * F1 * F2 * H2| + |F1 ^ 3 * H3| := abs_add_le _ _
            _ ≤ |F3 * H1| + |3 * F1 * F2 * H2| + |F1 ^ 3 * H3| := by
                  linarith [abs_add_le (F3 * H1) (3 * F1 * F2 * H2)]
    _ ≤ (128 * P.X * a / d ^ 6) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) *
          ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 3 * ((6 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
          linarith [hterm1, hterm2, hterm3]
    _ = 3406 * |j| * d / (P.X * a) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ ≤ sec7_ra_B3SharpScale 3 * |j| * d / (P.X * a) := by
          simp [sec7_ra_B3SharpScale]
          gcongr
          norm_num

private theorem sec7_ra_B3_iteratedDeriv4_implicit_eq {P : Globals} {S : Scale P}
    {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    let qd := sec7_ra_B3q P.X a j d
    let F1d := deriv (fun t => Ffun P.X a t) d
    let F2d := iteratedDeriv 2 (fun t => Ffun P.X a t) d
    let F3d := iteratedDeriv 3 (fun t => Ffun P.X a t) d
    let F4d := iteratedDeriv 4 (fun t => Ffun P.X a t) d
    let F1q := deriv (fun t => Ffun P.X a t) qd
    let F2q := iteratedDeriv 2 (fun t => Ffun P.X a t) qd
    let F3q := iteratedDeriv 3 (fun t => Ffun P.X a t) qd
    let F4q := iteratedDeriv 4 (fun t => Ffun P.X a t) qd
    iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      - (F1d ^ 4 * F1q ^ 2 * F4q - 10 * F1d ^ 4 * F1q * F2q * F3q +
          15 * F1d ^ 4 * F2q ^ 3 + 6 * F1d ^ 2 * F2d * F1q ^ 3 * F3q -
          18 * F1d ^ 2 * F2d * F1q ^ 2 * F2q ^ 2 +
          4 * F1d * F3d * F1q ^ 4 * F2q +
          3 * F2d ^ 2 * F1q ^ 4 * F2q - F4d * F1q ^ 6) / F1q ^ 7 := by
  dsimp
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqpos : 0 < qd := by
    rw [hqd_def, sec7_ra_B3q]
    exact dBreve_pos
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hd_ne : deriv (fun t => Ffun P.X a t) d ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hd
  have hq_ne : deriv (fun t => Ffun P.X a t) qd ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hqpos
  have hiter := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
    (d := d) (j := j) (k := 4) hAD ha_lo ha_hi hd hshift (by norm_num)
  rw [hiter]
  simp only [sec7_ra_B3E, sec7_ra_B3H, sec7_ra_dBreveD]
  rw [iteratedDeriv_one]
  rw [show Ffun P.X a d + j = Ffun P.X a qd by rw [hqspec]]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv3_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv3_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv4_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv4_Ffun_eq P.X_pos ha0 hd]
  field_simp [hd_ne, hq_ne]
  ring

private theorem sec7_ra_B3_bound_sharp_k4 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScale 4 * |j| / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  have hiter :
      iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
          6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 4) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, H1, H2, H3, H4, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, _hF5⟩
  rcases sec7_ra_B3H_bounds_sharp (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2, hH3, hH4, _hH5⟩
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 128 * P.X * a / d ^ 6 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF4ub_nonneg : 0 ≤ 800 * P.X * a / d ^ 7 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 800) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 7)
  have hF1pow2 : |F1| ^ 2 ≤ (7 * P.X * a / d ^ 4) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 2
  have hF1pow4 : |F1| ^ 4 ≤ (7 * P.X * a / d ^ 4) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 4
  have hF2pow2 : |F2| ^ 2 ≤ (26 * P.X * a / d ^ 5) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF2 2
  have hcoef2 : |4 * F1 * F3 + 3 * F2 ^ 2| ≤
      4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
        3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    calc
      |4 * F1 * F3 + 3 * F2 ^ 2|
          ≤ |4 * F1 * F3| + |3 * F2 ^ 2| := abs_add_le _ _
      _ = 4 * |F1| * |F3| + 3 * |F2| ^ 2 := by
            rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2 := by
            gcongr
  have hterm1 : |F4 * H1| ≤
      (800 * P.X * a / d ^ 7) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF4 hH1 (abs_nonneg _) hF4ub_nonneg
  have hterm2 : |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| ≤
      (4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) *
        ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    have hcoef_nonneg : 0 ≤
        4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2 := by positivity
    exact mul_le_mul hcoef2 hH2 (abs_nonneg _) hcoef_nonneg
  have hterm3 : |6 * F1 ^ 2 * F2 * H3| ≤
      6 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) *
        ((6 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    gcongr
  have hterm4 : |F1 ^ 4 * H4| ≤
      (7 * P.X * a / d ^ 4) ^ 4 * ((25 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow4 hH4 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 4)
  calc
    |iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
            6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4| := by rw [hiter]
    _ ≤ |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
        |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := by
          calc
            |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
                6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4|
                ≤ |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
                    6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := abs_add_le _ _
            _ ≤ |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
                |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := by
                  linarith [abs_add_le (F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2)
                    (6 * F1 ^ 2 * F2 * H3),
                    abs_add_le (F4 * H1) ((4 * F1 * F3 + 3 * F2 ^ 2) * H2)]
    _ ≤ (800 * P.X * a / d ^ 7) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2) *
          ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        6 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) *
          ((6 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 4 * ((25 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4]
    _ = 118713 * |j| / (P.X * a) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ ≤ sec7_ra_B3SharpScale 4 * |j| / (P.X * a) := by
          simp [sec7_ra_B3SharpScale]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (118713 : ℝ) ≤ 10 ^ 7) (abs_nonneg j))
            (mul_pos P.X_pos ha0).le

private theorem sec7_ra_B3_iteratedDeriv5_implicit_eq {P : Globals} {S : Scale P}
    {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a)
    (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S) :
    let qd := sec7_ra_B3q P.X a j d
    let F1d := deriv (fun t => Ffun P.X a t) d
    let F2d := iteratedDeriv 2 (fun t => Ffun P.X a t) d
    let F3d := iteratedDeriv 3 (fun t => Ffun P.X a t) d
    let F4d := iteratedDeriv 4 (fun t => Ffun P.X a t) d
    let F5d := iteratedDeriv 5 (fun t => Ffun P.X a t) d
    let F1q := deriv (fun t => Ffun P.X a t) qd
    let F2q := iteratedDeriv 2 (fun t => Ffun P.X a t) qd
    let F3q := iteratedDeriv 3 (fun t => Ffun P.X a t) qd
    let F4q := iteratedDeriv 4 (fun t => Ffun P.X a t) qd
    let F5q := iteratedDeriv 5 (fun t => Ffun P.X a t) qd
    iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
      - (F1d ^ 5 * F1q ^ 3 * F5q - 15 * F1d ^ 5 * F1q ^ 2 * F2q * F4q -
          10 * F1d ^ 5 * F1q ^ 2 * F3q ^ 2 +
          105 * F1d ^ 5 * F1q * F2q ^ 2 * F3q -
          105 * F1d ^ 5 * F2q ^ 4 +
          10 * F1d ^ 3 * F2d * F1q ^ 4 * F4q -
          100 * F1d ^ 3 * F2d * F1q ^ 3 * F2q * F3q +
          150 * F1d ^ 3 * F2d * F1q ^ 2 * F2q ^ 3 +
          10 * F1d ^ 2 * F3d * F1q ^ 5 * F3q -
          30 * F1d ^ 2 * F3d * F1q ^ 4 * F2q ^ 2 +
          15 * F1d * F2d ^ 2 * F1q ^ 5 * F3q -
          45 * F1d * F2d ^ 2 * F1q ^ 4 * F2q ^ 2 +
          5 * F1d * F4d * F1q ^ 6 * F2q +
          10 * F2d * F3d * F1q ^ 6 * F2q - F5d * F1q ^ 8) / F1q ^ 9 := by
  dsimp
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqpos : 0 < qd := by
    rw [hqd_def, sec7_ra_B3q]
    exact dBreve_pos
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hd_ne : deriv (fun t => Ffun P.X a t) d ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hd
  have hq_ne : deriv (fun t => Ffun P.X a t) qd ≠ 0 :=
    sec7_ra_Ffun_deriv_ne P.X_pos ha0 hqpos
  have hiter := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
    (d := d) (j := j) (k := 5) hAD ha_lo ha_hi hd hshift (by norm_num)
  rw [hiter]
  simp only [sec7_ra_B3E, sec7_ra_B3H, sec7_ra_dBreveD]
  rw [iteratedDeriv_one]
  rw [show Ffun P.X a d + j = Ffun P.X a qd by rw [hqspec]]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv1_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv2_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv3_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv3_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv4_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv4_Ffun_eq P.X_pos ha0 hd]
  rw [sec7_ra_dBreve_deriv5_Ffun_eq P.X_pos ha0 hqpos]
  rw [sec7_ra_dBreve_deriv5_Ffun_eq P.X_pos ha0 hd]
  field_simp [hd_ne, hq_ne]
  ring

private theorem sec7_ra_B3_bound_sharp_k5 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScale 5 * |j| / (d * (P.X * a)) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let F5 : ℝ := iteratedDeriv 5 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  let H5 : ℝ := sec7_ra_B3H P.X a j 5 d
  have hiter :
      iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
          5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
          10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 5) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, F5, H1, H2, H3, H4, H5, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, hF5⟩
  rcases sec7_ra_B3H_bounds_sharp (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2, hH3, hH4, hH5⟩
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 128 * P.X * a / d ^ 6 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF4ub_nonneg : 0 ≤ 800 * P.X * a / d ^ 7 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 800) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 7)
  have hF5ub_nonneg : 0 ≤ 6000 * P.X * a / d ^ 8 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6000) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 8)
  have hF1pow3 : |F1| ^ 3 ≤ (7 * P.X * a / d ^ 4) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 3
  have hF1pow5 : |F1| ^ 5 ≤ (7 * P.X * a / d ^ 4) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 5
  have hF2pow2 : |F2| ^ 2 ≤ (26 * P.X * a / d ^ 5) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF2 2
  have hcoef2a : |5 * F1 * F4| ≤
      5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    gcongr
  have hcoef2b : |10 * F2 * F3| ≤
      10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    gcongr
  have hcoef2 : |5 * F1 * F4 + 10 * F2 * F3| ≤
      5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
        10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) := by
    calc
      |5 * F1 * F4 + 10 * F2 * F3| ≤ |5 * F1 * F4| + |10 * F2 * F3| :=
        abs_add_le _ _
      _ ≤ 5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
          10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) :=
        add_le_add hcoef2a hcoef2b
  have hcoef2_nonneg : 0 ≤
      5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
        10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hF1ub_nonneg) hF4ub_nonneg)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hF2ub_nonneg) hF3ub_nonneg)
  have hinnera : |2 * F1 * F3| ≤
      2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  have hinnerb : |3 * F2 ^ 2| ≤ 3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul_of_nonneg_left hF2pow2 (by norm_num)
  have hinner : |2 * F1 * F3 + 3 * F2 ^ 2| ≤
      2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
        3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    calc
      |2 * F1 * F3 + 3 * F2 ^ 2| ≤ |2 * F1 * F3| + |3 * F2 ^ 2| := abs_add_le _ _
      _ ≤ 2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2 := add_le_add hinnera hinnerb
  have hinner_nonneg : 0 ≤
      2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
        3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF1ub_nonneg) hF3ub_nonneg)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _))
  have hcoef3 : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2)| ≤
      5 * (7 * P.X * a / d ^ 4) *
        (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    have hleft : 5 * |F1| ≤ 5 * (7 * P.X * a / d ^ 4) :=
      mul_le_mul_of_nonneg_left hF1 (by norm_num)
    simpa [mul_assoc] using
      (mul_le_mul hleft hinner (abs_nonneg _)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hF1ub_nonneg))
  have hcoef3_nonneg : 0 ≤
      5 * (7 * P.X * a / d ^ 4) *
        (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hF1ub_nonneg) hinner_nonneg
  have hcoef4 : |10 * F1 ^ 3 * F2| ≤
      10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5) := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    have hleft : 10 * |F1| ^ 3 ≤ 10 * (7 * P.X * a / d ^ 4) ^ 3 :=
      mul_le_mul_of_nonneg_left hF1pow3 (by norm_num)
    simpa [mul_assoc] using
      (mul_le_mul hleft hF2 (abs_nonneg _)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (pow_nonneg hF1ub_nonneg 3)))
  have hcoef4_nonneg : 0 ≤ 10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5) :=
    mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (pow_nonneg hF1ub_nonneg 3))
      hF2ub_nonneg
  have hterm1 : |F5 * H1| ≤
      (6000 * P.X * a / d ^ 8) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF5 hH1 (abs_nonneg _) hF5ub_nonneg
  have hterm2 : |(5 * F1 * F4 + 10 * F2 * F3) * H2| ≤
      (5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
          10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6)) *
        ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef2 hH2 (abs_nonneg _) hcoef2_nonneg
  have hterm3 : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| ≤
      (5 * (7 * P.X * a / d ^ 4) *
          (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2)) *
        ((6 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef3 hH3 (abs_nonneg _) hcoef3_nonneg
  have hterm4 : |10 * F1 ^ 3 * F2 * H4| ≤
      (10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5)) *
        ((25 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef4 hH4 (abs_nonneg _) hcoef4_nonneg
  have hterm5 : |F1 ^ 5 * H5| ≤
      (7 * P.X * a / d ^ 4) ^ 5 * ((150 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow5 hH5 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 5)
  calc
    |iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
            5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
            10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5| := by rw [hiter]
    _ ≤ |F5 * H1| + |(5 * F1 * F4 + 10 * F2 * F3) * H2| +
        |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| +
        |10 * F1 ^ 3 * F2 * H4| + |F1 ^ 5 * H5| := by
          linarith [abs_add_le
            (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
              5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
              10 * F1 ^ 3 * F2 * H4) (F1 ^ 5 * H5),
            abs_add_le
              (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
                5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3)
              (10 * F1 ^ 3 * F2 * H4),
            abs_add_le
              (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2)
              (5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3),
            abs_add_le (F5 * H1) ((5 * F1 * F4 + 10 * F2 * F3) * H2)]
    _ ≤ (6000 * P.X * a / d ^ 8) * ((2 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
            10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6)) *
          ((2 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (5 * (7 * P.X * a / d ^ 4) *
            (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
              3 * (26 * P.X * a / d ^ 5) ^ 2)) *
          ((6 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5)) *
          ((25 * d ^ 16 / (P.X * a) ^ 5) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 5 * ((150 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4, hterm5]
    _ = 5687310 * |j| / (d * (P.X * a)) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ ≤ sec7_ra_B3SharpScale 5 * |j| / (d * (P.X * a)) := by
          simp [sec7_ra_B3SharpScale]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (5687310 : ℝ) ≤ 10 ^ 7) (abs_nonneg j))
            (mul_pos hd (mul_pos P.X_pos ha0)).le

theorem sec7_ra_B3_bound_sharp_public {P : Globals} {S : Scale P} {a d j : ℝ} {k : ℕ}
    (hk : k ≤ 5)
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d / 2)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |dBreve P.X a (Ffun P.X a d + j) - d| ≤ d / 100) :
    |iteratedDeriv k (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d| ≤
      match k with
      | 0 => (1000 : ℝ) * |j| * d ^ 4 / (P.X * a)
      | 1 => (1000 : ℝ) * |j| * d ^ 3 / (P.X * a)
      | 2 => (10 ^ 4 : ℝ) * |j| * d ^ 2 / (P.X * a)
      | 3 => (10 ^ 6 : ℝ) * |j| * d / (P.X * a)
      | 4 => (10 ^ 7 : ℝ) * |j| / (P.X * a)
      | 5 => (10 ^ 7 : ℝ) * |j| / (d * (P.X * a))
      | _ => 0 := by
  have hclose' : |sec7_ra_B3q P.X a j d - d| ≤ d / 100 := by
    simpa [sec7_ra_B3q] using hclose
  interval_cases k
  · simpa [sec7_ra_B3SharpScale] using
      sec7_ra_B3_bound_sharp_k0 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScale] using
      sec7_ra_B3_bound_sharp_k1 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScale] using
      sec7_ra_B3_bound_sharp_k2 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScale] using
      sec7_ra_B3_bound_sharp_k3 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScale] using
      sec7_ra_B3_bound_sharp_k4 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScale] using
      sec7_ra_B3_bound_sharp_k5 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'

private noncomputable def sec7_ra_B3SharpScaleAled : ℕ → ℝ
  | 0 => 2
  | 1 => 120
  | 2 => 17600
  | 3 => 1176600
  | 4 => 144344400
  | 5 => 30084656000
  | 6 => 60985797208000
  | _ => 0

private theorem sec7_ra_Ffun_deriv1_lower_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    X * a / (2 * d ^ 4) ≤ |deriv (fun t => Ffun X a t) z| := by
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have hza_pos : 0 < z + a := by positivity
  rw [Ffun_deriv1_abs_eq (X := X) (a := a) (d := z) hX ha hzpos]
  have hza_hi : z + a ≤ (201 / 100 : ℝ) * d := by nlinarith
  have hz3_le : z ^ 3 ≤ ((101 / 100 : ℝ) * d) ^ 3 :=
    pow_le_pow_left₀ hzpos.le hzhi 3
  have hza3_le : (z + a) ^ 3 ≤ ((201 / 100 : ℝ) * d) ^ 3 :=
    pow_le_pow_left₀ hza_pos.le hza_hi 3
  have hpoly_lo : 3 * z ^ 2 ≤ a ^ 2 + 3 * a * z + 3 * z ^ 2 := by
    nlinarith [sq_nonneg a, mul_nonneg ha.le hzpos.le]
  have hz2_lo : ((99 / 100 : ℝ) * d) ^ 2 ≤ z ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (99 / 100 : ℝ) * d) hzlo 2
  have hden_core :
      z ^ 3 * (z + a) ^ 3 ≤
        4 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by
    calc
      z ^ 3 * (z + a) ^ 3
          ≤ ((101 / 100 : ℝ) * d) ^ 3 * (((201 / 100 : ℝ) * d) ^ 3) := by
            exact mul_le_mul hz3_le hza3_le (by positivity) (by positivity)
      _ = ((101 / 100 : ℝ) ^ 3 * (201 / 100 : ℝ) ^ 3) * d ^ 6 := by ring
      _ ≤ 12 * ((99 / 100 : ℝ) ^ 2 * d ^ 2) * d ^ 4 := by
            have hconst :
                (101 / 100 : ℝ) ^ 3 * (201 / 100 : ℝ) ^ 3 ≤
                  12 * (99 / 100 : ℝ) ^ 2 := by
              norm_num
            have hd6_nonneg : 0 ≤ d ^ 6 := by positivity
            nlinarith
      _ = 12 * (((99 / 100 : ℝ) * d) ^ 2) * d ^ 4 := by ring
      _ ≤ 12 * z ^ 2 * d ^ 4 := by gcongr
      _ = 4 * (3 * z ^ 2) * d ^ 4 := by ring
      _ ≤ 4 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by gcongr
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * d ^ 4)
    (by positivity : 0 < z ^ 3 * (z + a) ^ 3)]
  calc
    X * a * (z ^ 3 * (z + a) ^ 3)
        ≤ X * a * (4 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4) :=
      mul_le_mul_of_nonneg_left hden_core (by positivity)
    _ = (2 * X * a * (a ^ 2 + 3 * a * z + 3 * z ^ 2)) * (2 * d ^ 4) := by ring

private theorem sec7_ra_B3_qdiff_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3q P.X a j d - d| ≤ 2 * |j| * d ^ 4 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hCpos : 0 < P.X * a / (2 * d ^ 4) := by
    exact div_pos (mul_pos P.X_pos ha0) (by positivity)
  have hscale_eq :
      |j| / (P.X * a / (2 * d ^ 4)) = 2 * |j| * d ^ 4 / (P.X * a) := by
    field_simp [P.X_pos.ne', ne_of_gt ha0, ne_of_gt hd]
  by_cases hsame : qd = d
  · rw [hsame, sub_self, abs_zero]
    exact div_nonneg (by positivity) (le_of_lt (mul_pos P.X_pos ha0))
  have hprod : P.X * a / (2 * d ^ 4) * |qd - d| ≤ |j| := by
    rcases lt_or_gt_of_ne hsame with hlt | hlt
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := qd) (q := d) ha0
          (lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1) hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := le_trans hqwin.1 (le_of_lt hc_lo)
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) (by nlinarith)
      have hder :=
        sec7_ra_Ffun_deriv1_lower_sharp_close_aled (X := P.X) (a := a) (d := d)
          (z := c) P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hj : j = -(Ffun P.X a d - Ffun P.X a qd) := by
          rw [hqspec]
          ring
        rw [hj, abs_neg, hc_mvt, abs_mul, abs_sub_comm]
      rw [hj_abs]
      exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := d) (q := qd) ha0 hd hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := by nlinarith
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) hqwin.2
      have hder :=
        sec7_ra_Ffun_deriv1_lower_sharp_close_aled (X := P.X) (a := a) (d := d)
          (z := c) P.X_pos ha0 hd ha2 hc_win_lo hc_win_hi
      have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hj : j = Ffun P.X a qd - Ffun P.X a d := by
          rw [hqspec]
          ring
        rw [hj, hc_mvt, abs_mul]
      rw [hj_abs]
      exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
  calc
    |qd - d| ≤ |j| / (P.X * a / (2 * d ^ 4)) := by
      rw [le_div_iff₀ hCpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    _ = 2 * |j| * d ^ 4 / (P.X * a) := hscale_eq

private theorem sec7_ra_B3_bound_sharp_aled_k0 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 0 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 0 * |j| * d ^ 4 / (P.X * a) := by
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hiter0 :
      iteratedDeriv 0 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d = qd - d := by
    simp [hqd_def, sec7_ra_B3q]
  rw [hiter0]
  simpa [sec7_ra_B3SharpScaleAled] using
    sec7_ra_B3_qdiff_sharp_aled (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose

private theorem sec7_ra_Ffun_deriv2_upper_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (_hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |iteratedDeriv 2 (fun t => Ffun X a t) z| ≤ 30 * X * a / d ^ 5 := by
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have hF2 := (sec7_ra_Ffun_upper_base_sharp (X := X) (a := a) (d := z)
    hX ha hzpos).2.1
  have hz5_lo : ((99 / 100 : ℝ) * d) ^ 5 ≤ z ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (99 / 100 : ℝ) * d) hzlo 5
  calc
    |iteratedDeriv 2 (fun t => Ffun X a t) z| ≤ 26 * X * a / z ^ 5 := hF2
    _ ≤ 30 * X * a / d ^ 5 := by
      rw [div_le_div_iff₀ (pow_pos hzpos 5) (pow_pos hd 5)]
      calc
        (26 * X * a) * d ^ 5
            ≤ (30 * X * a) * (((99 / 100 : ℝ) * d) ^ 5) := by
              have hconst : (26 : ℝ) ≤ 30 * (99 / 100 : ℝ) ^ 5 := by norm_num
              have hXa_pos : 0 < X * a := mul_pos hX ha
              have hd5_nonneg : 0 ≤ d ^ 5 := by positivity
              rw [show (((99 / 100 : ℝ) * d) ^ 5) =
                  (99 / 100 : ℝ) ^ 5 * d ^ 5 by ring]
              nlinarith
        _ ≤ (30 * X * a) * z ^ 5 := by gcongr

private theorem sec7_ra_B3_bound_sharp_aled_k1 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 1 * |j| * d ^ 3 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hqpos : 0 < qd := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1
  let F1d : ℝ := deriv (fun t => Ffun P.X a t) d
  let F1q : ℝ := deriv (fun t => Ffun P.X a t) qd
  have hF1q_lower : P.X * a / (2 * d ^ 4) ≤ |F1q| := by
    simpa [F1q] using
      (sec7_ra_Ffun_deriv1_lower_sharp_close_aled (X := P.X) (a := a) (d := d)
        (z := qd) P.X_pos ha0 hd ha2 hqwin.1 hqwin.2)
  have hF1q_abs_pos : 0 < |F1q| :=
    lt_of_lt_of_le (div_pos (mul_pos P.X_pos ha0) (by positivity : 0 < 2 * d ^ 4))
      hF1q_lower
  have hF1q_ne : F1q ≠ 0 := abs_pos.mp hF1q_abs_pos
  have hF1diff :
      |F1d - F1q| ≤ (30 * P.X * a / d ^ 5) * |qd - d| := by
    by_cases hsame : qd = d
    · simp [F1d, F1q, hsame]
    rcases lt_or_gt_of_ne hsame with hlt | hlt
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_deriv_mvt_local (X := P.X) (a := a) (p := qd) (q := d) ha0 hqpos hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := le_trans hqwin.1 (le_of_lt hc_lo)
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) (by nlinarith)
      have hF2 :=
        sec7_ra_Ffun_deriv2_upper_sharp_close_aled (X := P.X) (a := a) (d := d)
          (z := c) P.X_pos ha0 hd hc_win_lo hc_win_hi
      have hmvt_abs : |F1d - F1q| =
          |iteratedDeriv 2 (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hm : F1d - F1q =
            iteratedDeriv 2 (fun t => Ffun P.X a t) c * (d - qd) := by
          simpa [F1d, F1q] using hc_mvt
        rw [hm, abs_mul, abs_sub_comm]
      rw [hmvt_abs]
      exact mul_le_mul_of_nonneg_right hF2 (abs_nonneg _)
    · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
        sec7_ra_Ffun_deriv_mvt_local (X := P.X) (a := a) (p := d) (q := qd) ha0 hd hlt
      have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := by nlinarith
      have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) hqwin.2
      have hF2 :=
        sec7_ra_Ffun_deriv2_upper_sharp_close_aled (X := P.X) (a := a) (d := d)
          (z := c) P.X_pos ha0 hd hc_win_lo hc_win_hi
      have hmvt_abs : |F1d - F1q| =
          |iteratedDeriv 2 (fun t => Ffun P.X a t) c| * |qd - d| := by
        have hm : F1q - F1d =
            iteratedDeriv 2 (fun t => Ffun P.X a t) c * (qd - d) := by
          simpa [F1d, F1q] using hc_mvt
        rw [← abs_neg (F1d - F1q)]
        have hneg : -(F1d - F1q) = F1q - F1d := by ring
        rw [hneg, hm, abs_mul]
      rw [hmvt_abs]
      exact mul_le_mul_of_nonneg_right hF2 (abs_nonneg _)
  have hqdiff :=
    sec7_ra_B3_qdiff_sharp_aled (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd ha2 hshift hclose
  have hiter :=
    sec7_ra_B3_iteratedDeriv1_implicit_eq (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd hshift
  rw [hiter]
  have hdiv_eq : F1d / F1q - 1 = (F1d - F1q) / F1q := by
    field_simp [hF1q_ne]
  rw [show deriv (fun t => Ffun P.X a t) d = F1d by rfl]
  rw [show deriv (fun t => Ffun P.X a t) (sec7_ra_B3q P.X a j d) = F1q by
    rw [← hqd_def]]
  rw [hdiv_eq, abs_div]
  have hratio :
      |F1d - F1q| / |F1q| ≤ 60 * |qd - d| / d := by
    have hnum_nonneg : 0 ≤ (30 * P.X * a / d ^ 5) * |qd - d| := by
      have hcoef_nonneg : 0 ≤ 30 * P.X * a / d ^ 5 := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) P.X_pos.le) ha0.le)
          (pow_nonneg hd.le 5)
      exact mul_nonneg hcoef_nonneg (abs_nonneg _)
    calc
      |F1d - F1q| / |F1q|
          ≤ ((30 * P.X * a / d ^ 5) * |qd - d|) / |F1q| := by
        exact div_le_div_of_nonneg_right hF1diff (abs_nonneg _)
      _ ≤ ((30 * P.X * a / d ^ 5) * |qd - d|) / (P.X * a / (2 * d ^ 4)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ hF1q_abs_pos
            (div_pos (mul_pos P.X_pos ha0) (by positivity : 0 < 2 * d ^ 4))).2 hF1q_lower)
          hnum_nonneg
      _ = 60 * |qd - d| / d := by
        field_simp [P.X_pos.ne', ha0.ne', hd.ne']
        ring
  calc
    |F1d - F1q| / |F1q| ≤ 60 * |qd - d| / d := hratio
    _ ≤ 60 * (2 * |j| * d ^ 4 / (P.X * a)) / d := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqdiff (by norm_num : (0 : ℝ) ≤ 60)) hd.le
    _ = sec7_ra_B3SharpScaleAled 1 * |j| * d ^ 3 / (P.X * a) := by
      simp [sec7_ra_B3SharpScaleAled]
      field_simp [P.X_pos.ne', ha0.ne', hd.ne']
      ring

private theorem sec7_ra_dBreve_deriv2_image_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve'' X a (Ffun X a z)| ≤ 300 * d ^ 7 / (X * a) ^ 2 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have hF2 :=
    sec7_ra_Ffun_deriv2_upper_sharp_close_aled (X := X) (a := a) (d := d)
      (z := z) hX ha hd hzlo hzhi
  have hF1lo :=
    sec7_ra_Ffun_deriv1_lower_sharp_close_aled (X := X) (a := a) (d := d)
      (z := z) hX ha hd ha2 hzlo hzhi
  have hF1pos : 0 < |deriv (fun t => Ffun X a t) z| := by
    exact lt_of_lt_of_le
      (div_pos (mul_pos hX ha) (by positivity : 0 < 2 * d ^ 4)) hF1lo
  have hF1pow :
      (X * a / (2 * d ^ 4)) ^ 3 ≤
        |deriv (fun t => Ffun X a t) z| ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hF1lo 3
  have hden_pos : 0 < (X * a / (2 * d ^ 4)) ^ 3 := by positivity
  rw [sec7_ra_dBreve_deriv2_Ffun_eq (X := X) (a := a) (d := z) hX ha hz]
  rw [abs_div, abs_neg, abs_pow]
  calc
    |iteratedDeriv 2 (fun t => Ffun X a t) z| / |deriv (fun t => Ffun X a t) z| ^ 3
        ≤ (30 * X * a / d ^ 5) / |deriv (fun t => Ffun X a t) z| ^ 3 := by
          exact div_le_div_of_nonneg_right hF2 (pow_nonneg (abs_nonneg _) 3)
    _ ≤ (30 * X * a / d ^ 5) / ((X * a / (2 * d ^ 4)) ^ 3) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            ((inv_le_inv₀ (pow_pos hF1pos 3) hden_pos).2 hF1pow)
            (by positivity)
    _ = 240 * d ^ 7 / (X * a) ^ 2 := by
          field_simp [hX.ne', ha.ne', hd.ne']
          ring
    _ ≤ 300 * d ^ 7 / (X * a) ^ 2 := by
          gcongr
          norm_num

private theorem sec7_ra_dBreve_deriv3_image_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve''' X a (Ffun X a z)| ≤ 200 * d ^ 10 / (X * a) ^ 3 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (2 : ℝ) * z := by nlinarith
  set P : ℝ :=
    5 * a ^ 6 + 40 * a ^ 5 * z + 140 * a ^ 4 * z ^ 2 +
      284 * a ^ 3 * z ^ 3 + 352 * a ^ 2 * z ^ 4 + 252 * a * z ^ 5 +
      84 * z ^ 6 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_pos : 0 < Q := by
    rw [hQ_def]
    positivity
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 5 ≤ Q ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 5
  have hP_bound : P ≤ 10000 * z ^ 6 := by
    have h1 : a ^ 6 ≤ (2 : ℝ) ^ 6 * z ^ 6 := by
      simpa [mul_pow] using pow_le_pow_left₀ ha.le haz 6
    have h2 : a ^ 5 * z ≤ (2 : ℝ) ^ 5 * z ^ 6 := by
      calc
        a ^ 5 * z ≤ (((2 : ℝ) * z) ^ 5) * z :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 5) hz.le
        _ = (2 : ℝ) ^ 5 * z ^ 6 := by ring
    have h3 : a ^ 4 * z ^ 2 ≤ (2 : ℝ) ^ 4 * z ^ 6 := by
      calc
        a ^ 4 * z ^ 2 ≤ (((2 : ℝ) * z) ^ 4) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 4) (by positivity)
        _ = (2 : ℝ) ^ 4 * z ^ 6 := by ring
    have h4 : a ^ 3 * z ^ 3 ≤ (2 : ℝ) ^ 3 * z ^ 6 := by
      calc
        a ^ 3 * z ^ 3 ≤ (((2 : ℝ) * z) ^ 3) * z ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 3) (by positivity)
        _ = (2 : ℝ) ^ 3 * z ^ 6 := by ring
    have h5 : a ^ 2 * z ^ 4 ≤ (2 : ℝ) ^ 2 * z ^ 6 := by
      calc
        a ^ 2 * z ^ 4 ≤ (((2 : ℝ) * z) ^ 2) * z ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 2) (by positivity)
        _ = (2 : ℝ) ^ 2 * z ^ 6 := by ring
    have h6 : a * z ^ 5 ≤ 2 * z ^ 6 := by
      calc
        a * z ^ 5 ≤ ((2 : ℝ) * z) * z ^ 5 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = 2 * z ^ 6 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, pow_nonneg hz.le 6]
  have hza_bound : (z + a) ^ 2 ≤ ((3 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (3 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hcore :
      3 * (z + a) ^ 2 * P ≤ 1200 * 3 ^ 5 * z ^ 8 := by
    calc
      3 * (z + a) ^ 2 * P
          ≤ 3 * (((3 : ℝ) * z) ^ 2) * (10000 * z ^ 6) := by
            gcongr
      _ = (3 * (3 : ℝ) ^ 2 * 10000) * z ^ 8 := by ring
      _ ≤ 1200 * 3 ^ 5 * z ^ 8 := by
            have hconst : 3 * (3 : ℝ) ^ 2 * 10000 ≤ 1200 * 3 ^ 5 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      3 * z ^ 7 * (z + a) ^ 7 * P ≤ 1200 * z ^ 10 * Q ^ 5 := by
    calc
      3 * z ^ 7 * (z + a) ^ 7 * P
          = z ^ 7 * (z + a) ^ 5 * (3 * (z + a) ^ 2 * P) := by ring
      _ ≤ z ^ 7 * (z + a) ^ 5 * (1200 * 3 ^ 5 * z ^ 8) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 1200 * z ^ 10 * (((3 : ℝ) * z * (z + a)) ^ 5) := by ring
      _ ≤ 1200 * z ^ 10 * Q ^ 5 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz10_le : z ^ 10 ≤ ((101 / 100 : ℝ) * d) ^ 10 :=
    pow_le_pow_left₀ hz.le hzhi 10
  rw [dBreve_deriv3_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      3 * z ^ 7 * (z + a) ^ 7 * P / (8 * X ^ 3 * a ^ 3 * Q ^ 5)
        ≤ 150 * z ^ 10 / (X * a) ^ 3 := by
    have hden_left : 0 < 8 * X ^ 3 * a ^ 3 * Q ^ 5 := by positivity
    have hden_right : 0 < (X * a) ^ 3 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 3 * a ^ 3)
    linarith [hmul]
  calc
    3 * z ^ 7 * (z + a) ^ 7 * P / (8 * X ^ 3 * a ^ 3 * Q ^ 5)
        ≤ 150 * z ^ 10 / (X * a) ^ 3 := hstep
    _ ≤ 150 * (((101 / 100 : ℝ) * d) ^ 10) / (X * a) ^ 3 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz10_le (by norm_num))
            (by positivity : 0 ≤ (X * a) ^ 3)
    _ ≤ 200 * d ^ 10 / (X * a) ^ 3 := by
          have hnum :
              150 * (((101 / 100 : ℝ) * d) ^ 10) ≤ 200 * d ^ 10 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 10) =
                (101 / 100 : ℝ) ^ 10 * d ^ 10 by ring]
            have hconst : 150 * (101 / 100 : ℝ) ^ 10 ≤ 200 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 10)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

theorem sec7_ra_B3H_bounds12_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3H P.X a j 1 d| ≤ (300 * d ^ 7 / (P.X * a) ^ 2) * |j| ∧
      |sec7_ra_B3H P.X a j 2 d| ≤ (200 * d ^ 10 / (P.X * a) ^ 3) * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hpre : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
        (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
    intro s hs
    exact sec7_ra_B3_segment_preimage_close (P := P) (S := S) (a := a) (d := d)
      (j := j) (s := s) hAD ha_lo ha_hi hd hshift hclose hs
  have hH1 : |sec7_ra_B3H P.X a j 1 d| ≤
      (300 * d ^ 7 / (P.X * a) ^ 2) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 300 * d ^ 7 / (P.X * a) ^ 2) (l := 1) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv2_image_sharp_close_aled (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  have hH2 : |sec7_ra_B3H P.X a j 2 d| ≤
      (200 * d ^ 10 / (P.X * a) ^ 3) * |j| := by
    refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := 200 * d ^ 10 / (P.X * a) ^ 3) (l := 2) (by norm_num)
      ha_lo hpre ?_
    intro u hu0 hulo huhi
    simpa [sec7_ra_dBreveD] using
      sec7_ra_dBreve_deriv3_image_sharp_close_aled (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hulo huhi
  exact ⟨hH1, hH2⟩

private theorem sec7_ra_B3_bound_sharp_aled_k2 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 2 * |j| * d ^ 2 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hiter := sec7_ra_B3_iteratedDeriv2_eq (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd hshift
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, _hF3, _hF4, _hF5⟩
  rcases sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2⟩
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF1sq : |deriv (fun t => Ffun P.X a t) d| ^ 2 ≤
      (7 * P.X * a / d ^ 4) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hF1ub_nonneg).2 hF1
  calc
    |iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
            deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d| := by
          rw [hiter]
    _ ≤ |iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d| +
        |deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d| := abs_add_le _ _
    _ = |iteratedDeriv 2 (fun t => Ffun P.X a t) d| *
          |sec7_ra_B3H P.X a j 1 d| +
        |deriv (fun t => Ffun P.X a t) d| ^ 2 *
          |sec7_ra_B3H P.X a j 2 d| := by
          rw [abs_mul, abs_mul, abs_pow]
    _ ≤ (26 * P.X * a / d ^ 5) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 2 * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
          exact add_le_add
            (mul_le_mul hF2 hH1 (abs_nonneg _) hF2ub_nonneg)
            (mul_le_mul hF1sq hH2 (abs_nonneg _) (sq_nonneg _))
    _ = 17600 * |j| * d ^ 2 / (P.X * a) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ = sec7_ra_B3SharpScaleAled 2 * |j| * d ^ 2 / (P.X * a) := by
          simp [sec7_ra_B3SharpScaleAled]

private theorem sec7_ra_dBreve_deriv4_image_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve'''' X a (Ffun X a z)| ≤ 3000 * d ^ 13 / (X * a) ^ 4 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (2 : ℝ) * z := by nlinarith
  set P : ℝ :=
    7 * a ^ 8 + 70 * a ^ 7 * z + 322 * a ^ 6 * z ^ 2 +
      912 * a ^ 5 * z ^ 3 + 1728 * a ^ 4 * z ^ 4 + 2232 * a ^ 3 * z ^ 5 +
      1920 * a ^ 2 * z ^ 6 + 1008 * a * z ^ 7 + 252 * z ^ 8 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 7 ≤ Q ^ 7 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 7
  have hP_bound : P ≤ 120000 * z ^ 8 := by
    have h1 : a ^ 8 ≤ (2 : ℝ) ^ 8 * z ^ 8 := by
      simpa [mul_pow] using pow_le_pow_left₀ ha.le haz 8
    have h2 : a ^ 7 * z ≤ (2 : ℝ) ^ 7 * z ^ 8 := by
      calc
        a ^ 7 * z ≤ (((2 : ℝ) * z) ^ 7) * z :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 7) hz.le
        _ = (2 : ℝ) ^ 7 * z ^ 8 := by ring
    have h3 : a ^ 6 * z ^ 2 ≤ (2 : ℝ) ^ 6 * z ^ 8 := by
      calc
        a ^ 6 * z ^ 2 ≤ (((2 : ℝ) * z) ^ 6) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 6) (by positivity)
        _ = (2 : ℝ) ^ 6 * z ^ 8 := by ring
    have h4 : a ^ 5 * z ^ 3 ≤ (2 : ℝ) ^ 5 * z ^ 8 := by
      calc
        a ^ 5 * z ^ 3 ≤ (((2 : ℝ) * z) ^ 5) * z ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 5) (by positivity)
        _ = (2 : ℝ) ^ 5 * z ^ 8 := by ring
    have h5 : a ^ 4 * z ^ 4 ≤ (2 : ℝ) ^ 4 * z ^ 8 := by
      calc
        a ^ 4 * z ^ 4 ≤ (((2 : ℝ) * z) ^ 4) * z ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 4) (by positivity)
        _ = (2 : ℝ) ^ 4 * z ^ 8 := by ring
    have h6 : a ^ 3 * z ^ 5 ≤ (2 : ℝ) ^ 3 * z ^ 8 := by
      calc
        a ^ 3 * z ^ 5 ≤ (((2 : ℝ) * z) ^ 3) * z ^ 5 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 3) (by positivity)
        _ = (2 : ℝ) ^ 3 * z ^ 8 := by ring
    have h7 : a ^ 2 * z ^ 6 ≤ (2 : ℝ) ^ 2 * z ^ 8 := by
      calc
        a ^ 2 * z ^ 6 ≤ (((2 : ℝ) * z) ^ 2) * z ^ 6 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 2) (by positivity)
        _ = (2 : ℝ) ^ 2 * z ^ 8 := by ring
    have h8 : a * z ^ 7 ≤ 2 * z ^ 8 := by
      calc
        a * z ^ 7 ≤ ((2 : ℝ) * z) * z ^ 7 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = 2 * z ^ 8 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, pow_nonneg hz.le 8]
  have hza_bound : (z + a) ^ 2 ≤ ((3 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (3 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hlin_bound : a + 2 * z ≤ (4 : ℝ) * z := by nlinarith
  have hcore :
      15 * (z + a) ^ 2 * (a + 2 * z) * P ≤ 32000 * 3 ^ 7 * z ^ 11 := by
    calc
      15 * (z + a) ^ 2 * (a + 2 * z) * P
          ≤ 15 * (((3 : ℝ) * z) ^ 2) * ((4 : ℝ) * z) * (120000 * z ^ 8) := by
            gcongr
      _ = (15 * (3 : ℝ) ^ 2 * 4 * 120000) * z ^ 11 := by ring
      _ ≤ 32000 * 3 ^ 7 * z ^ 11 := by
            have hconst : 15 * (3 : ℝ) ^ 2 * 4 * 120000 ≤ 32000 * 3 ^ 7 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P ≤ 32000 * z ^ 13 * Q ^ 7 := by
    calc
      15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P
          = z ^ 9 * (z + a) ^ 7 * (15 * (z + a) ^ 2 * (a + 2 * z) * P) := by
            ring
      _ ≤ z ^ 9 * (z + a) ^ 7 * (32000 * 3 ^ 7 * z ^ 11) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 32000 * z ^ 13 * (((3 : ℝ) * z * (z + a)) ^ 7) := by ring
      _ ≤ 32000 * z ^ 13 * Q ^ 7 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz13_le : z ^ 13 ≤ ((101 / 100 : ℝ) * d) ^ 13 :=
    pow_le_pow_left₀ hz.le hzhi 13
  rw [dBreve_deriv4_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P /
          (16 * X ^ 4 * a ^ 4 * Q ^ 7)
        ≤ 2000 * z ^ 13 / (X * a) ^ 4 := by
    have hden_left : 0 < 16 * X ^ 4 * a ^ 4 * Q ^ 7 := by
      rw [hQ_def]
      positivity
    have hden_right : 0 < (X * a) ^ 4 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 4 * a ^ 4)
    linarith [hmul]
  calc
    15 * z ^ 9 * (z + a) ^ 9 * (a + 2 * z) * P /
          (16 * X ^ 4 * a ^ 4 * Q ^ 7)
        ≤ 2000 * z ^ 13 / (X * a) ^ 4 := hstep
    _ ≤ 2000 * (((101 / 100 : ℝ) * d) ^ 13) / (X * a) ^ 4 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz13_le (by norm_num))
            (by positivity)
    _ ≤ 3000 * d ^ 13 / (X * a) ^ 4 := by
          have hnum : 2000 * (((101 / 100 : ℝ) * d) ^ 13) ≤ 3000 * d ^ 13 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 13) =
                (101 / 100 : ℝ) ^ 13 * d ^ 13 by ring]
            have hconst : 2000 * (101 / 100 : ℝ) ^ 13 ≤ 3000 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 13)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

theorem sec7_ra_B3H_bound3_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3H P.X a j 3 d| ≤ (3000 * d ^ 13 / (P.X * a) ^ 4) * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hpre : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
        (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
    intro s hs
    exact sec7_ra_B3_segment_preimage_close (P := P) (S := S) (a := a) (d := d)
      (j := j) (s := s) hAD ha_lo ha_hi hd hshift hclose hs
  refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
    (j := j) (C := 3000 * d ^ 13 / (P.X * a) ^ 4) (l := 3) (by norm_num)
    ha_lo hpre ?_
  intro u hu0 hulo huhi
  simpa [sec7_ra_dBreveD] using
    sec7_ra_dBreve_deriv4_image_sharp_close_aled (X := P.X) (a := a) (d := d)
      (z := u) P.X_pos ha0 hd ha2 hulo huhi

private theorem sec7_ra_B3_bound_sharp_aled_k3 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 3 * |j| * d / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  have hiter :
      iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F3 * H1 + 3 * F1 * F2 * H2 + F1 ^ 3 * H3 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 3) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, H1, H2, H3, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, _hF4, _hF5⟩
  rcases sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2⟩
  have hH3 := sec7_ra_B3H_bound3_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 128 * P.X * a / d ^ 6 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hterm1 : |F3 * H1| ≤
      (128 * P.X * a / d ^ 6) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF3 hH1 (abs_nonneg _) hF3ub_nonneg
  have hterm2 : |3 * F1 * F2 * H2| ≤
      3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) *
        ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    gcongr
  have hF1pow3 : |F1| ^ 3 ≤ (7 * P.X * a / d ^ 4) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 3
  have hterm3 : |F1 ^ 3 * H3| ≤
      (7 * P.X * a / d ^ 4) ^ 3 * ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow3 hH3 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 3)
  calc
    |iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F3 * H1 + 3 * F1 * F2 * H2 + F1 ^ 3 * H3| := by rw [hiter]
    _ ≤ |F3 * H1| + |3 * F1 * F2 * H2| + |F1 ^ 3 * H3| := by
          calc
            |F3 * H1 + 3 * F1 * F2 * H2 + F1 ^ 3 * H3|
                ≤ |F3 * H1 + 3 * F1 * F2 * H2| + |F1 ^ 3 * H3| := abs_add_le _ _
            _ ≤ |F3 * H1| + |3 * F1 * F2 * H2| + |F1 ^ 3 * H3| := by
                  linarith [abs_add_le (F3 * H1) (3 * F1 * F2 * H2)]
    _ ≤ (128 * P.X * a / d ^ 6) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) *
          ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 3 * ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
          linarith [hterm1, hterm2, hterm3]
    _ = 1176600 * |j| * d / (P.X * a) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ = sec7_ra_B3SharpScaleAled 3 * |j| * d / (P.X * a) := by
          simp [sec7_ra_B3SharpScaleAled]

private theorem sec7_ra_dBreve_deriv5_image_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve''''' X a (Ffun X a z)| ≤ 50000 * d ^ 16 / (X * a) ^ 5 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (2 : ℝ) * z := by nlinarith
  set P : ℝ :=
    21 * a ^ 12 + 336 * a ^ 11 * z + 2520 * a ^ 10 * z ^ 2 +
      11852 * a ^ 9 * z ^ 3 + 39104 * a ^ 8 * z ^ 4 +
      95348 * a ^ 7 * z ^ 5 + 175964 * a ^ 6 * z ^ 6 +
      247424 * a ^ 5 * z ^ 7 + 262988 * a ^ 4 * z ^ 8 +
      206160 * a ^ 3 * z ^ 9 + 113304 * a ^ 2 * z ^ 10 +
      39312 * a * z ^ 11 + 6552 * z ^ 12 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 9 ≤ Q ^ 9 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 9
  have hP_bound : P ≤ 60000000 * z ^ 12 := by
    have h1 : a ^ 12 ≤ (2 : ℝ) ^ 12 * z ^ 12 := by
      simpa [mul_pow] using pow_le_pow_left₀ ha.le haz 12
    have h2 : a ^ 11 * z ≤ (2 : ℝ) ^ 11 * z ^ 12 := by
      calc
        a ^ 11 * z ≤ (((2 : ℝ) * z) ^ 11) * z :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 11) hz.le
        _ = (2 : ℝ) ^ 11 * z ^ 12 := by ring
    have h3 : a ^ 10 * z ^ 2 ≤ (2 : ℝ) ^ 10 * z ^ 12 := by
      calc
        a ^ 10 * z ^ 2 ≤ (((2 : ℝ) * z) ^ 10) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 10) (by positivity)
        _ = (2 : ℝ) ^ 10 * z ^ 12 := by ring
    have h4 : a ^ 9 * z ^ 3 ≤ (2 : ℝ) ^ 9 * z ^ 12 := by
      calc
        a ^ 9 * z ^ 3 ≤ (((2 : ℝ) * z) ^ 9) * z ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 9) (by positivity)
        _ = (2 : ℝ) ^ 9 * z ^ 12 := by ring
    have h5 : a ^ 8 * z ^ 4 ≤ (2 : ℝ) ^ 8 * z ^ 12 := by
      calc
        a ^ 8 * z ^ 4 ≤ (((2 : ℝ) * z) ^ 8) * z ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 8) (by positivity)
        _ = (2 : ℝ) ^ 8 * z ^ 12 := by ring
    have h6 : a ^ 7 * z ^ 5 ≤ (2 : ℝ) ^ 7 * z ^ 12 := by
      calc
        a ^ 7 * z ^ 5 ≤ (((2 : ℝ) * z) ^ 7) * z ^ 5 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 7) (by positivity)
        _ = (2 : ℝ) ^ 7 * z ^ 12 := by ring
    have h7 : a ^ 6 * z ^ 6 ≤ (2 : ℝ) ^ 6 * z ^ 12 := by
      calc
        a ^ 6 * z ^ 6 ≤ (((2 : ℝ) * z) ^ 6) * z ^ 6 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 6) (by positivity)
        _ = (2 : ℝ) ^ 6 * z ^ 12 := by ring
    have h8 : a ^ 5 * z ^ 7 ≤ (2 : ℝ) ^ 5 * z ^ 12 := by
      calc
        a ^ 5 * z ^ 7 ≤ (((2 : ℝ) * z) ^ 5) * z ^ 7 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 5) (by positivity)
        _ = (2 : ℝ) ^ 5 * z ^ 12 := by ring
    have h9 : a ^ 4 * z ^ 8 ≤ (2 : ℝ) ^ 4 * z ^ 12 := by
      calc
        a ^ 4 * z ^ 8 ≤ (((2 : ℝ) * z) ^ 4) * z ^ 8 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 4) (by positivity)
        _ = (2 : ℝ) ^ 4 * z ^ 12 := by ring
    have h10 : a ^ 3 * z ^ 9 ≤ (2 : ℝ) ^ 3 * z ^ 12 := by
      calc
        a ^ 3 * z ^ 9 ≤ (((2 : ℝ) * z) ^ 3) * z ^ 9 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 3) (by positivity)
        _ = (2 : ℝ) ^ 3 * z ^ 12 := by ring
    have h11 : a ^ 2 * z ^ 10 ≤ (2 : ℝ) ^ 2 * z ^ 12 := by
      calc
        a ^ 2 * z ^ 10 ≤ (((2 : ℝ) * z) ^ 2) * z ^ 10 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 2) (by positivity)
        _ = (2 : ℝ) ^ 2 * z ^ 12 := by ring
    have h12 : a * z ^ 11 ≤ 2 * z ^ 12 := by
      calc
        a * z ^ 11 ≤ ((2 : ℝ) * z) * z ^ 11 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = 2 * z ^ 12 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      pow_nonneg hz.le 12]
  have hza_bound : (z + a) ^ 2 ≤ ((3 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (3 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hcore :
      45 * (z + a) ^ 2 * P ≤ 1312000 * 3 ^ 9 * z ^ 14 := by
    calc
      45 * (z + a) ^ 2 * P
          ≤ 45 * (((3 : ℝ) * z) ^ 2) * (60000000 * z ^ 12) := by
            gcongr
      _ = (45 * (3 : ℝ) ^ 2 * 60000000) * z ^ 14 := by ring
      _ ≤ 1312000 * 3 ^ 9 * z ^ 14 := by
            have hconst : 45 * (3 : ℝ) ^ 2 * 60000000 ≤ 1312000 * 3 ^ 9 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      45 * z ^ 11 * (z + a) ^ 11 * P ≤ 1312000 * z ^ 16 * Q ^ 9 := by
    calc
      45 * z ^ 11 * (z + a) ^ 11 * P
          = z ^ 11 * (z + a) ^ 9 * (45 * (z + a) ^ 2 * P) := by ring
      _ ≤ z ^ 11 * (z + a) ^ 9 * (1312000 * 3 ^ 9 * z ^ 14) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 1312000 * z ^ 16 * (((3 : ℝ) * z * (z + a)) ^ 9) := by ring
      _ ≤ 1312000 * z ^ 16 * Q ^ 9 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz16_le : z ^ 16 ≤ ((101 / 100 : ℝ) * d) ^ 16 :=
    pow_le_pow_left₀ hz.le hzhi 16
  rw [dBreve_deriv5_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      45 * z ^ 11 * (z + a) ^ 11 * P / (32 * X ^ 5 * a ^ 5 * Q ^ 9)
        ≤ 41000 * z ^ 16 / (X * a) ^ 5 := by
    have hden_left : 0 < 32 * X ^ 5 * a ^ 5 * Q ^ 9 := by
      rw [hQ_def]
      positivity
    have hden_right : 0 < (X * a) ^ 5 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 5 * a ^ 5)
    linarith [hmul]
  calc
    45 * z ^ 11 * (z + a) ^ 11 * P / (32 * X ^ 5 * a ^ 5 * Q ^ 9)
        ≤ 41000 * z ^ 16 / (X * a) ^ 5 := hstep
    _ ≤ 41000 * (((101 / 100 : ℝ) * d) ^ 16) / (X * a) ^ 5 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz16_le (by norm_num))
            (by positivity)
    _ ≤ 50000 * d ^ 16 / (X * a) ^ 5 := by
          have hnum : 41000 * (((101 / 100 : ℝ) * d) ^ 16) ≤ 50000 * d ^ 16 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 16) =
                (101 / 100 : ℝ) ^ 16 * d ^ 16 by ring]
            have hconst : 41000 * (101 / 100 : ℝ) ^ 16 ≤ 50000 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 16)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

theorem sec7_ra_B3H_bound4_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3H P.X a j 4 d| ≤ (50000 * d ^ 16 / (P.X * a) ^ 5) * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hpre : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
        (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
    intro s hs
    exact sec7_ra_B3_segment_preimage_close (P := P) (S := S) (a := a) (d := d)
      (j := j) (s := s) hAD ha_lo ha_hi hd hshift hclose hs
  refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
    (j := j) (C := 50000 * d ^ 16 / (P.X * a) ^ 5) (l := 4) (by norm_num)
    ha_lo hpre ?_
  intro u hu0 hulo huhi
  simpa [sec7_ra_dBreveD] using
    sec7_ra_dBreve_deriv5_image_sharp_close_aled (X := P.X) (a := a) (d := d)
      (z := u) P.X_pos ha0 hd ha2 hulo huhi

private theorem sec7_ra_B3_bound_sharp_aled_k4 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 4 * |j| / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  have hiter :
      iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
          6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 4) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, H1, H2, H3, H4, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, _hF5⟩
  rcases sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2⟩
  have hH3 := sec7_ra_B3H_bound3_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH4 := sec7_ra_B3H_bound4_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 128 * P.X * a / d ^ 6 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF4ub_nonneg : 0 ≤ 800 * P.X * a / d ^ 7 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 800) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 7)
  have hF1pow2 : |F1| ^ 2 ≤ (7 * P.X * a / d ^ 4) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 2
  have hF1pow4 : |F1| ^ 4 ≤ (7 * P.X * a / d ^ 4) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 4
  have hF2pow2 : |F2| ^ 2 ≤ (26 * P.X * a / d ^ 5) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF2 2
  have hcoef2 : |4 * F1 * F3 + 3 * F2 ^ 2| ≤
      4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
        3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    calc
      |4 * F1 * F3 + 3 * F2 ^ 2|
          ≤ |4 * F1 * F3| + |3 * F2 ^ 2| := abs_add_le _ _
      _ = 4 * |F1| * |F3| + 3 * |F2| ^ 2 := by
            rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2 := by
            gcongr
  have hterm1 : |F4 * H1| ≤
      (800 * P.X * a / d ^ 7) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF4 hH1 (abs_nonneg _) hF4ub_nonneg
  have hterm2 : |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| ≤
      (4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) *
        ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    have hcoef_nonneg : 0 ≤
        4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2 := by positivity
    exact mul_le_mul hcoef2 hH2 (abs_nonneg _) hcoef_nonneg
  have hterm3 : |6 * F1 ^ 2 * F2 * H3| ≤
      6 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) *
        ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    gcongr
  have hterm4 : |F1 ^ 4 * H4| ≤
      (7 * P.X * a / d ^ 4) ^ 4 * ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow4 hH4 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 4)
  calc
    |iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
            6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4| := by rw [hiter]
    _ ≤ |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
        |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := by
          calc
            |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
                6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4|
                ≤ |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
                    6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := abs_add_le _ _
            _ ≤ |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
                |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := by
                  linarith [abs_add_le (F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2)
                    (6 * F1 ^ 2 * F2 * H3),
                    abs_add_le (F4 * H1) ((4 * F1 * F3 + 3 * F2 ^ 2) * H2)]
    _ ≤ (800 * P.X * a / d ^ 7) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2) *
          ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        6 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) *
          ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 4 * ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4]
    _ = 144344400 * |j| / (P.X * a) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ = sec7_ra_B3SharpScaleAled 4 * |j| / (P.X * a) := by
          simp [sec7_ra_B3SharpScaleAled]

private theorem sec7_ra_dBreve_deriv6_image_sharp_close_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |dBreve'''''' X a (Ffun X a z)| ≤ 1500000 * d ^ 19 / (X * a) ^ 6 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (2 : ℝ) * z := by nlinarith
  set P : ℝ :=
    33 * a ^ 14 + 594 * a ^ 13 * z + 5082 * a ^ 12 * z ^ 2 +
      27688 * a ^ 11 * z ^ 3 + 107664 * a ^ 10 * z ^ 4 +
      315840 * a ^ 9 * z ^ 5 + 719656 * a ^ 8 * z ^ 6 +
      1291968 * a ^ 7 * z ^ 7 + 1834488 * a ^ 6 * z ^ 8 +
      2049144 * a ^ 5 * z ^ 9 + 1772544 * a ^ 4 * z ^ 10 +
      1152144 * a ^ 3 * z ^ 11 + 532728 * a ^ 2 * z ^ 12 +
      157248 * a * z ^ 13 + 22464 * z ^ 14 with hP_def
  set Q : ℝ := a ^ 2 + 3 * a * z + 3 * z ^ 2 with hQ_def
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ Q := by
    rw [hQ_def]
    nlinarith [sq_nonneg a]
  have hQpow_lower : ((3 : ℝ) * z * (z + a)) ^ 11 ≤ Q ^ 11 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * z * (z + a)) hQ_lower 11
  have hP_bound : P ≤ 1000000000 * z ^ 14 := by
    have h1 : a ^ 14 ≤ (2 : ℝ) ^ 14 * z ^ 14 := by
      simpa [mul_pow] using pow_le_pow_left₀ ha.le haz 14
    have h2 : a ^ 13 * z ≤ (2 : ℝ) ^ 13 * z ^ 14 := by
      calc
        a ^ 13 * z ≤ (((2 : ℝ) * z) ^ 13) * z :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 13) hz.le
        _ = (2 : ℝ) ^ 13 * z ^ 14 := by ring
    have h3 : a ^ 12 * z ^ 2 ≤ (2 : ℝ) ^ 12 * z ^ 14 := by
      calc
        a ^ 12 * z ^ 2 ≤ (((2 : ℝ) * z) ^ 12) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 12) (by positivity)
        _ = (2 : ℝ) ^ 12 * z ^ 14 := by ring
    have h4 : a ^ 11 * z ^ 3 ≤ (2 : ℝ) ^ 11 * z ^ 14 := by
      calc
        a ^ 11 * z ^ 3 ≤ (((2 : ℝ) * z) ^ 11) * z ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 11) (by positivity)
        _ = (2 : ℝ) ^ 11 * z ^ 14 := by ring
    have h5 : a ^ 10 * z ^ 4 ≤ (2 : ℝ) ^ 10 * z ^ 14 := by
      calc
        a ^ 10 * z ^ 4 ≤ (((2 : ℝ) * z) ^ 10) * z ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 10) (by positivity)
        _ = (2 : ℝ) ^ 10 * z ^ 14 := by ring
    have h6 : a ^ 9 * z ^ 5 ≤ (2 : ℝ) ^ 9 * z ^ 14 := by
      calc
        a ^ 9 * z ^ 5 ≤ (((2 : ℝ) * z) ^ 9) * z ^ 5 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 9) (by positivity)
        _ = (2 : ℝ) ^ 9 * z ^ 14 := by ring
    have h7 : a ^ 8 * z ^ 6 ≤ (2 : ℝ) ^ 8 * z ^ 14 := by
      calc
        a ^ 8 * z ^ 6 ≤ (((2 : ℝ) * z) ^ 8) * z ^ 6 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 8) (by positivity)
        _ = (2 : ℝ) ^ 8 * z ^ 14 := by ring
    have h8 : a ^ 7 * z ^ 7 ≤ (2 : ℝ) ^ 7 * z ^ 14 := by
      calc
        a ^ 7 * z ^ 7 ≤ (((2 : ℝ) * z) ^ 7) * z ^ 7 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 7) (by positivity)
        _ = (2 : ℝ) ^ 7 * z ^ 14 := by ring
    have h9 : a ^ 6 * z ^ 8 ≤ (2 : ℝ) ^ 6 * z ^ 14 := by
      calc
        a ^ 6 * z ^ 8 ≤ (((2 : ℝ) * z) ^ 6) * z ^ 8 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 6) (by positivity)
        _ = (2 : ℝ) ^ 6 * z ^ 14 := by ring
    have h10 : a ^ 5 * z ^ 9 ≤ (2 : ℝ) ^ 5 * z ^ 14 := by
      calc
        a ^ 5 * z ^ 9 ≤ (((2 : ℝ) * z) ^ 5) * z ^ 9 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 5) (by positivity)
        _ = (2 : ℝ) ^ 5 * z ^ 14 := by ring
    have h11 : a ^ 4 * z ^ 10 ≤ (2 : ℝ) ^ 4 * z ^ 14 := by
      calc
        a ^ 4 * z ^ 10 ≤ (((2 : ℝ) * z) ^ 4) * z ^ 10 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 4) (by positivity)
        _ = (2 : ℝ) ^ 4 * z ^ 14 := by ring
    have h12 : a ^ 3 * z ^ 11 ≤ (2 : ℝ) ^ 3 * z ^ 14 := by
      calc
        a ^ 3 * z ^ 11 ≤ (((2 : ℝ) * z) ^ 3) * z ^ 11 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 3) (by positivity)
        _ = (2 : ℝ) ^ 3 * z ^ 14 := by ring
    have h13 : a ^ 2 * z ^ 12 ≤ (2 : ℝ) ^ 2 * z ^ 14 := by
      calc
        a ^ 2 * z ^ 12 ≤ (((2 : ℝ) * z) ^ 2) * z ^ 12 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haz 2) (by positivity)
        _ = (2 : ℝ) ^ 2 * z ^ 14 := by ring
    have h14 : a * z ^ 13 ≤ 2 * z ^ 14 := by
      calc
        a * z ^ 13 ≤ ((2 : ℝ) * z) * z ^ 13 :=
          mul_le_mul_of_nonneg_right haz (by positivity)
        _ = 2 * z ^ 14 := by ring
    rw [hP_def]
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      pow_nonneg hz.le 14]
  have hza_bound : (z + a) ^ 2 ≤ ((3 : ℝ) * z) ^ 2 := by
    have hza : z + a ≤ (3 : ℝ) * z := by nlinarith
    exact pow_le_pow_left₀ (by positivity : 0 ≤ z + a) hza 2
  have hlin_bound : a + 2 * z ≤ (4 : ℝ) * z := by nlinarith
  have hcore :
      315 * (z + a) ^ 2 * (a + 2 * z) * P ≤ 70000000 * 3 ^ 11 * z ^ 17 := by
    calc
      315 * (z + a) ^ 2 * (a + 2 * z) * P
          ≤ 315 * (((3 : ℝ) * z) ^ 2) * ((4 : ℝ) * z) * (1000000000 * z ^ 14) := by
            gcongr
      _ = (315 * (3 : ℝ) ^ 2 * 4 * 1000000000) * z ^ 17 := by ring
      _ ≤ 70000000 * 3 ^ 11 * z ^ 17 := by
            have hconst :
                315 * (3 : ℝ) ^ 2 * 4 * 1000000000 ≤ 70000000 * 3 ^ 11 := by
              norm_num
            exact mul_le_mul_of_nonneg_right hconst (by positivity)
  have hnum_core :
      315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P ≤
        70000000 * z ^ 19 * Q ^ 11 := by
    calc
      315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P
          = z ^ 13 * (z + a) ^ 11 * (315 * (z + a) ^ 2 * (a + 2 * z) * P) := by
            ring
      _ ≤ z ^ 13 * (z + a) ^ 11 * (70000000 * 3 ^ 11 * z ^ 17) := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 70000000 * z ^ 19 * (((3 : ℝ) * z * (z + a)) ^ 11) := by ring
      _ ≤ 70000000 * z ^ 19 * Q ^ 11 := by
            exact mul_le_mul_of_nonneg_left hQpow_lower (by positivity)
  have hz19_le : z ^ 19 ≤ ((101 / 100 : ℝ) * d) ^ 19 :=
    pow_le_pow_left₀ hz.le hzhi 19
  rw [dBreve_deriv6_abs_factor_image (X := X) (a := a) (d := z) hX ha hz]
  rw [← hP_def, ← hQ_def]
  have hstep :
      315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P /
          (64 * X ^ 6 * a ^ 6 * Q ^ 11)
        ≤ 1093750 * z ^ 19 / (X * a) ^ 6 := by
    have hden_left : 0 < 64 * X ^ 6 * a ^ 6 * Q ^ 11 := by
      rw [hQ_def]
      positivity
    have hden_right : 0 < (X * a) ^ 6 := by positivity
    rw [div_le_div_iff₀ hden_left hden_right]
    have hmul := mul_le_mul_of_nonneg_right hnum_core (by positivity : 0 ≤ X ^ 6 * a ^ 6)
    linarith [hmul]
  calc
    315 * z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * P /
          (64 * X ^ 6 * a ^ 6 * Q ^ 11)
        ≤ 1093750 * z ^ 19 / (X * a) ^ 6 := hstep
    _ ≤ 1093750 * (((101 / 100 : ℝ) * d) ^ 19) / (X * a) ^ 6 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz19_le (by norm_num))
            (by positivity)
    _ ≤ 1500000 * d ^ 19 / (X * a) ^ 6 := by
          have hnum : 1093750 * (((101 / 100 : ℝ) * d) ^ 19) ≤
              1500000 * d ^ 19 := by
            rw [show (((101 / 100 : ℝ) * d) ^ 19) =
                (101 / 100 : ℝ) ^ 19 * d ^ 19 by ring]
            have hconst : 1093750 * (101 / 100 : ℝ) ^ 19 ≤ 1500000 := by
              norm_num
            linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 19)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

theorem sec7_ra_B3H_bound5_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3H P.X a j 5 d| ≤ (1500000 * d ^ 19 / (P.X * a) ^ 6) * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hpre : ∀ s ∈ Set.uIcc (0 : ℝ) j,
      ∃ u, 0 < u ∧ Ffun P.X a u = Ffun P.X a d + s ∧
        (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
    intro s hs
    exact sec7_ra_B3_segment_preimage_close (P := P) (S := S) (a := a) (d := d)
      (j := j) (s := s) hAD ha_lo ha_hi hd hshift hclose hs
  refine sec7_ra_B3H_mvt_bound_image (P := P) (S := S) (a := a) (d := d)
    (j := j) (C := 1500000 * d ^ 19 / (P.X * a) ^ 6) (l := 5) (by norm_num)
    ha_lo hpre ?_
  intro u hu0 hulo huhi
  simpa [sec7_ra_dBreveD] using
    sec7_ra_dBreve_deriv6_image_sharp_close_aled (X := P.X) (a := a) (d := d)
      (z := u) P.X_pos ha0 hd ha2 hulo huhi

private noncomputable def sec7_ra_dBreve6ImagePoly (a z : ℝ) : ℝ :=
  33 * a ^ 14 + 594 * a ^ 13 * z + 5082 * a ^ 12 * z ^ 2 +
    27688 * a ^ 11 * z ^ 3 + 107664 * a ^ 10 * z ^ 4 +
    315840 * a ^ 9 * z ^ 5 + 719656 * a ^ 8 * z ^ 6 +
    1291968 * a ^ 7 * z ^ 7 + 1834488 * a ^ 6 * z ^ 8 +
    2049144 * a ^ 5 * z ^ 9 + 1772544 * a ^ 4 * z ^ 10 +
    1152144 * a ^ 3 * z ^ 11 + 532728 * a ^ 2 * z ^ 12 +
    157248 * a * z ^ 13 + 22464 * z ^ 14

private noncomputable def sec7_ra_dBreve6ImagePolyDeriv (a z : ℝ) : ℝ :=
  594 * a ^ 13 + 2 * 5082 * a ^ 12 * z +
    3 * 27688 * a ^ 11 * z ^ 2 + 4 * 107664 * a ^ 10 * z ^ 3 +
    5 * 315840 * a ^ 9 * z ^ 4 + 6 * 719656 * a ^ 8 * z ^ 5 +
    7 * 1291968 * a ^ 7 * z ^ 6 + 8 * 1834488 * a ^ 6 * z ^ 7 +
    9 * 2049144 * a ^ 5 * z ^ 8 + 10 * 1772544 * a ^ 4 * z ^ 9 +
    11 * 1152144 * a ^ 3 * z ^ 10 + 12 * 532728 * a ^ 2 * z ^ 11 +
    13 * 157248 * a * z ^ 12 + 14 * 22464 * z ^ 13

private theorem sec7_ra_dBreve6ImagePoly_bound_aled {a d z : ℝ}
    (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) :
    sec7_ra_dBreve6ImagePoly a z ≤ 12000000 * z ^ 14 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (102 / 100 : ℝ) * z := by nlinarith
  have hpow (n : ℕ) : a ^ n ≤ (((102 / 100 : ℝ) * z) ^ n) :=
    pow_le_pow_left₀ ha.le haz n
  unfold sec7_ra_dBreve6ImagePoly
  calc
    33 * a ^ 14 + 594 * a ^ 13 * z + 5082 * a ^ 12 * z ^ 2 +
        27688 * a ^ 11 * z ^ 3 + 107664 * a ^ 10 * z ^ 4 +
        315840 * a ^ 9 * z ^ 5 + 719656 * a ^ 8 * z ^ 6 +
        1291968 * a ^ 7 * z ^ 7 + 1834488 * a ^ 6 * z ^ 8 +
        2049144 * a ^ 5 * z ^ 9 + 1772544 * a ^ 4 * z ^ 10 +
        1152144 * a ^ 3 * z ^ 11 + 532728 * a ^ 2 * z ^ 12 +
        157248 * a * z ^ 13 + 22464 * z ^ 14
      ≤ 33 * (((102 / 100 : ℝ) * z) ^ 14) +
        594 * (((102 / 100 : ℝ) * z) ^ 13) * z +
        5082 * (((102 / 100 : ℝ) * z) ^ 12) * z ^ 2 +
        27688 * (((102 / 100 : ℝ) * z) ^ 11) * z ^ 3 +
        107664 * (((102 / 100 : ℝ) * z) ^ 10) * z ^ 4 +
        315840 * (((102 / 100 : ℝ) * z) ^ 9) * z ^ 5 +
        719656 * (((102 / 100 : ℝ) * z) ^ 8) * z ^ 6 +
        1291968 * (((102 / 100 : ℝ) * z) ^ 7) * z ^ 7 +
        1834488 * (((102 / 100 : ℝ) * z) ^ 6) * z ^ 8 +
        2049144 * (((102 / 100 : ℝ) * z) ^ 5) * z ^ 9 +
        1772544 * (((102 / 100 : ℝ) * z) ^ 4) * z ^ 10 +
        1152144 * (((102 / 100 : ℝ) * z) ^ 3) * z ^ 11 +
        532728 * (((102 / 100 : ℝ) * z) ^ 2) * z ^ 12 +
        157248 * (((102 / 100 : ℝ) * z)) * z ^ 13 + 22464 * z ^ 14 := by
          gcongr
    _ ≤ 12000000 * z ^ 14 := by
          rw [show
            33 * (((102 / 100 : ℝ) * z) ^ 14) +
              594 * (((102 / 100 : ℝ) * z) ^ 13) * z +
              5082 * (((102 / 100 : ℝ) * z) ^ 12) * z ^ 2 +
              27688 * (((102 / 100 : ℝ) * z) ^ 11) * z ^ 3 +
              107664 * (((102 / 100 : ℝ) * z) ^ 10) * z ^ 4 +
              315840 * (((102 / 100 : ℝ) * z) ^ 9) * z ^ 5 +
              719656 * (((102 / 100 : ℝ) * z) ^ 8) * z ^ 6 +
              1291968 * (((102 / 100 : ℝ) * z) ^ 7) * z ^ 7 +
              1834488 * (((102 / 100 : ℝ) * z) ^ 6) * z ^ 8 +
              2049144 * (((102 / 100 : ℝ) * z) ^ 5) * z ^ 9 +
              1772544 * (((102 / 100 : ℝ) * z) ^ 4) * z ^ 10 +
              1152144 * (((102 / 100 : ℝ) * z) ^ 3) * z ^ 11 +
              532728 * (((102 / 100 : ℝ) * z) ^ 2) * z ^ 12 +
              157248 * (((102 / 100 : ℝ) * z)) * z ^ 13 + 22464 * z ^ 14 =
              (33 * (102 / 100 : ℝ) ^ 14 + 594 * (102 / 100 : ℝ) ^ 13 +
                5082 * (102 / 100 : ℝ) ^ 12 + 27688 * (102 / 100 : ℝ) ^ 11 +
                107664 * (102 / 100 : ℝ) ^ 10 + 315840 * (102 / 100 : ℝ) ^ 9 +
                719656 * (102 / 100 : ℝ) ^ 8 + 1291968 * (102 / 100 : ℝ) ^ 7 +
                1834488 * (102 / 100 : ℝ) ^ 6 + 2049144 * (102 / 100 : ℝ) ^ 5 +
                1772544 * (102 / 100 : ℝ) ^ 4 + 1152144 * (102 / 100 : ℝ) ^ 3 +
                532728 * (102 / 100 : ℝ) ^ 2 + 157248 * (102 / 100 : ℝ) +
                22464) * z ^ 14 by ring]
          have hconst :
              33 * (102 / 100 : ℝ) ^ 14 + 594 * (102 / 100 : ℝ) ^ 13 +
                5082 * (102 / 100 : ℝ) ^ 12 + 27688 * (102 / 100 : ℝ) ^ 11 +
                107664 * (102 / 100 : ℝ) ^ 10 + 315840 * (102 / 100 : ℝ) ^ 9 +
                719656 * (102 / 100 : ℝ) ^ 8 + 1291968 * (102 / 100 : ℝ) ^ 7 +
                1834488 * (102 / 100 : ℝ) ^ 6 + 2049144 * (102 / 100 : ℝ) ^ 5 +
                1772544 * (102 / 100 : ℝ) ^ 4 + 1152144 * (102 / 100 : ℝ) ^ 3 +
                532728 * (102 / 100 : ℝ) ^ 2 + 157248 * (102 / 100 : ℝ) +
                22464 ≤ 12000000 := by
            norm_num
          exact mul_le_mul_of_nonneg_right hconst (pow_nonneg hz.le 14)

private theorem sec7_ra_dBreve6ImagePolyDeriv_bound_aled {a d z : ℝ}
    (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) :
    sec7_ra_dBreve6ImagePolyDeriv a z ≤ 100000000 * z ^ 13 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have haz : a ≤ (102 / 100 : ℝ) * z := by nlinarith
  have hpow (n : ℕ) : a ^ n ≤ (((102 / 100 : ℝ) * z) ^ n) :=
    pow_le_pow_left₀ ha.le haz n
  unfold sec7_ra_dBreve6ImagePolyDeriv
  calc
    594 * a ^ 13 + 2 * 5082 * a ^ 12 * z +
        3 * 27688 * a ^ 11 * z ^ 2 + 4 * 107664 * a ^ 10 * z ^ 3 +
        5 * 315840 * a ^ 9 * z ^ 4 + 6 * 719656 * a ^ 8 * z ^ 5 +
        7 * 1291968 * a ^ 7 * z ^ 6 + 8 * 1834488 * a ^ 6 * z ^ 7 +
        9 * 2049144 * a ^ 5 * z ^ 8 + 10 * 1772544 * a ^ 4 * z ^ 9 +
        11 * 1152144 * a ^ 3 * z ^ 10 + 12 * 532728 * a ^ 2 * z ^ 11 +
        13 * 157248 * a * z ^ 12 + 14 * 22464 * z ^ 13
      ≤ 594 * (((102 / 100 : ℝ) * z) ^ 13) +
        2 * 5082 * (((102 / 100 : ℝ) * z) ^ 12) * z +
        3 * 27688 * (((102 / 100 : ℝ) * z) ^ 11) * z ^ 2 +
        4 * 107664 * (((102 / 100 : ℝ) * z) ^ 10) * z ^ 3 +
        5 * 315840 * (((102 / 100 : ℝ) * z) ^ 9) * z ^ 4 +
        6 * 719656 * (((102 / 100 : ℝ) * z) ^ 8) * z ^ 5 +
        7 * 1291968 * (((102 / 100 : ℝ) * z) ^ 7) * z ^ 6 +
        8 * 1834488 * (((102 / 100 : ℝ) * z) ^ 6) * z ^ 7 +
        9 * 2049144 * (((102 / 100 : ℝ) * z) ^ 5) * z ^ 8 +
        10 * 1772544 * (((102 / 100 : ℝ) * z) ^ 4) * z ^ 9 +
        11 * 1152144 * (((102 / 100 : ℝ) * z) ^ 3) * z ^ 10 +
        12 * 532728 * (((102 / 100 : ℝ) * z) ^ 2) * z ^ 11 +
        13 * 157248 * (((102 / 100 : ℝ) * z)) * z ^ 12 +
        14 * 22464 * z ^ 13 := by
          gcongr
    _ ≤ 100000000 * z ^ 13 := by
          rw [show
            594 * (((102 / 100 : ℝ) * z) ^ 13) +
              2 * 5082 * (((102 / 100 : ℝ) * z) ^ 12) * z +
              3 * 27688 * (((102 / 100 : ℝ) * z) ^ 11) * z ^ 2 +
              4 * 107664 * (((102 / 100 : ℝ) * z) ^ 10) * z ^ 3 +
              5 * 315840 * (((102 / 100 : ℝ) * z) ^ 9) * z ^ 4 +
              6 * 719656 * (((102 / 100 : ℝ) * z) ^ 8) * z ^ 5 +
              7 * 1291968 * (((102 / 100 : ℝ) * z) ^ 7) * z ^ 6 +
              8 * 1834488 * (((102 / 100 : ℝ) * z) ^ 6) * z ^ 7 +
              9 * 2049144 * (((102 / 100 : ℝ) * z) ^ 5) * z ^ 8 +
              10 * 1772544 * (((102 / 100 : ℝ) * z) ^ 4) * z ^ 9 +
              11 * 1152144 * (((102 / 100 : ℝ) * z) ^ 3) * z ^ 10 +
              12 * 532728 * (((102 / 100 : ℝ) * z) ^ 2) * z ^ 11 +
              13 * 157248 * (((102 / 100 : ℝ) * z)) * z ^ 12 +
              14 * 22464 * z ^ 13 =
              (594 * (102 / 100 : ℝ) ^ 13 + 2 * 5082 * (102 / 100 : ℝ) ^ 12 +
                3 * 27688 * (102 / 100 : ℝ) ^ 11 +
                4 * 107664 * (102 / 100 : ℝ) ^ 10 +
                5 * 315840 * (102 / 100 : ℝ) ^ 9 +
                6 * 719656 * (102 / 100 : ℝ) ^ 8 +
                7 * 1291968 * (102 / 100 : ℝ) ^ 7 +
                8 * 1834488 * (102 / 100 : ℝ) ^ 6 +
                9 * 2049144 * (102 / 100 : ℝ) ^ 5 +
                10 * 1772544 * (102 / 100 : ℝ) ^ 4 +
                11 * 1152144 * (102 / 100 : ℝ) ^ 3 +
                12 * 532728 * (102 / 100 : ℝ) ^ 2 +
                13 * 157248 * (102 / 100 : ℝ) + 14 * 22464) * z ^ 13 by ring]
          have hconst :
              594 * (102 / 100 : ℝ) ^ 13 + 2 * 5082 * (102 / 100 : ℝ) ^ 12 +
                3 * 27688 * (102 / 100 : ℝ) ^ 11 +
                4 * 107664 * (102 / 100 : ℝ) ^ 10 +
                5 * 315840 * (102 / 100 : ℝ) ^ 9 +
                6 * 719656 * (102 / 100 : ℝ) ^ 8 +
                7 * 1291968 * (102 / 100 : ℝ) ^ 7 +
                8 * 1834488 * (102 / 100 : ℝ) ^ 6 +
                9 * 2049144 * (102 / 100 : ℝ) ^ 5 +
                10 * 1772544 * (102 / 100 : ℝ) ^ 4 +
                11 * 1152144 * (102 / 100 : ℝ) ^ 3 +
                12 * 532728 * (102 / 100 : ℝ) ^ 2 +
                13 * 157248 * (102 / 100 : ℝ) + 14 * 22464 ≤ 100000000 := by
            norm_num
          exact mul_le_mul_of_nonneg_right hconst (pow_nonneg hz.le 13)

noncomputable def sec7_ra_dBreve6ImageQ (a z : ℝ) : ℝ :=
  a ^ 2 + 3 * a * z + 3 * z ^ 2

noncomputable def sec7_ra_dBreve6ImageU (a z : ℝ) : ℝ :=
  z ^ 13 * (z + a) ^ 13 * (a + 2 * z) * sec7_ra_dBreve6ImagePoly a z

noncomputable def sec7_ra_dBreve6ImageUDeriv (a z : ℝ) : ℝ :=
  13 * z ^ 12 * (z + a) ^ 13 * (a + 2 * z) *
      sec7_ra_dBreve6ImagePoly a z +
    13 * z ^ 13 * (z + a) ^ 12 * (a + 2 * z) *
      sec7_ra_dBreve6ImagePoly a z +
    2 * z ^ 13 * (z + a) ^ 13 * sec7_ra_dBreve6ImagePoly a z +
    z ^ 13 * (z + a) ^ 13 * (a + 2 * z) *
      sec7_ra_dBreve6ImagePolyDeriv a z

noncomputable def sec7_ra_dBreve6ImageK (X a z : ℝ) : ℝ :=
  (315 / (64 * X ^ 6 * a ^ 6)) *
    (sec7_ra_dBreve6ImageU a z / sec7_ra_dBreve6ImageQ a z ^ 11)

private theorem sec7_ra_hasDerivAt_const_mul_pow (c z : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => c * x ^ n) (c * (n : ℝ) * z ^ (n - 1)) z := by
  simpa [mul_assoc] using ((hasDerivAt_id z).pow n).const_mul c

private theorem sec7_ra_dBreve6ImagePoly_hasDerivAt (a z : ℝ) :
    HasDerivAt (sec7_ra_dBreve6ImagePoly a)
      (sec7_ra_dBreve6ImagePolyDeriv a z) z := by
  have h1 := sec7_ra_hasDerivAt_const_mul_pow (594 * a ^ 13) z 1
  have h2 := sec7_ra_hasDerivAt_const_mul_pow (5082 * a ^ 12) z 2
  have h3 := sec7_ra_hasDerivAt_const_mul_pow (27688 * a ^ 11) z 3
  have h4 := sec7_ra_hasDerivAt_const_mul_pow (107664 * a ^ 10) z 4
  have h5 := sec7_ra_hasDerivAt_const_mul_pow (315840 * a ^ 9) z 5
  have h6 := sec7_ra_hasDerivAt_const_mul_pow (719656 * a ^ 8) z 6
  have h7 := sec7_ra_hasDerivAt_const_mul_pow (1291968 * a ^ 7) z 7
  have h8 := sec7_ra_hasDerivAt_const_mul_pow (1834488 * a ^ 6) z 8
  have h9 := sec7_ra_hasDerivAt_const_mul_pow (2049144 * a ^ 5) z 9
  have h10 := sec7_ra_hasDerivAt_const_mul_pow (1772544 * a ^ 4) z 10
  have h11 := sec7_ra_hasDerivAt_const_mul_pow (1152144 * a ^ 3) z 11
  have h12 := sec7_ra_hasDerivAt_const_mul_pow (532728 * a ^ 2) z 12
  have h13 := sec7_ra_hasDerivAt_const_mul_pow (157248 * a) z 13
  have h14 := sec7_ra_hasDerivAt_const_mul_pow 22464 z 14
  have h0 : HasDerivAt (fun _ : ℝ => 33 * a ^ 14) 0 z := hasDerivAt_const z _
  have hsum :=
    ((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add
      h9).add h10).add h11).add h12).add h13).add h14)
  convert hsum using 1
  · funext x
    simp [sec7_ra_dBreve6ImagePoly]
  · simp [sec7_ra_dBreve6ImagePolyDeriv]
    ring

private theorem sec7_ra_dBreve6ImageU_hasDerivAt (a z : ℝ) :
    HasDerivAt (sec7_ra_dBreve6ImageU a)
      (sec7_ra_dBreve6ImageUDeriv a z) z := by
  have hz13 : HasDerivAt (fun x : ℝ => x ^ 13) (13 * z ^ 12) z := by
    simpa using (hasDerivAt_id z).pow 13
  have hza13 : HasDerivAt (fun x : ℝ => (x + a) ^ 13) (13 * (z + a) ^ 12) z := by
    simpa using ((hasDerivAt_id z).add_const a).pow 13
  have hlin : HasDerivAt (fun x : ℝ => a + 2 * x) 2 z := by
    have hraw := (hasDerivAt_const z a).add ((hasDerivAt_id z).const_mul 2)
    convert hraw using 1
    ring
  have hpoly := sec7_ra_dBreve6ImagePoly_hasDerivAt a z
  have hmain := (((hz13.mul hza13).mul hlin).mul hpoly)
  convert hmain using 1
  · simp [sec7_ra_dBreve6ImageUDeriv]
    ring

private theorem sec7_ra_dBreve6ImageQ_hasDerivAt (a z : ℝ) :
    HasDerivAt (sec7_ra_dBreve6ImageQ a) (3 * a + 6 * z) z := by
  have h1 : HasDerivAt (fun x : ℝ => 3 * a * x) (3 * a) z := by
    simpa [mul_assoc] using (hasDerivAt_id z).const_mul (3 * a)
  have h2 : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (6 * z) z := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_id z).pow 2
    convert hpow.const_mul 3 using 1
    ring
  have h0 : HasDerivAt (fun _ : ℝ => a ^ 2) 0 z := hasDerivAt_const z _
  have hsum := (h0.add h1).add h2
  convert hsum using 1
  ring

theorem sec7_ra_dBreve6ImageK_hasDerivAt {X a z : ℝ}
    (hX : X ≠ 0) (ha : a ≠ 0)
    (hQ : sec7_ra_dBreve6ImageQ a z ≠ 0) :
    HasDerivAt (sec7_ra_dBreve6ImageK X a)
      ((315 / (64 * X ^ 6 * a ^ 6)) *
        (sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 -
          11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
            sec7_ra_dBreve6ImageQ a z ^ 12)) z := by
  have hU := sec7_ra_dBreve6ImageU_hasDerivAt a z
  have hQder := sec7_ra_dBreve6ImageQ_hasDerivAt a z
  have hQpow := hQder.pow 11
  have hQpow_ne : sec7_ra_dBreve6ImageQ a z ^ 11 ≠ 0 := pow_ne_zero 11 hQ
  have hraw := hU.div hQpow hQpow_ne
  have hmain := hraw.const_mul (315 / (64 * X ^ 6 * a ^ 6))
  convert hmain using 1
  · simp only [Pi.pow_apply, Nat.cast_ofNat]
    field_simp [hX, ha, hQ]
    ring_nf

theorem sec7_ra_dBreve6ImageK_eq {X a z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hz : 0 < z) :
    dBreve'''''' X a (Ffun X a z) = sec7_ra_dBreve6ImageK X a z := by
  have hQ : sec7_ra_dBreve6ImageQ a z ≠ 0 := by
    unfold sec7_ra_dBreve6ImageQ
    positivity
  rw [dBreve_deriv6_factor_image (X := X) (a := a) (d := z) hX ha hz]
  simp [sec7_ra_dBreve6ImageK, sec7_ra_dBreve6ImageU, sec7_ra_dBreve6ImageQ,
    sec7_ra_dBreve6ImagePoly]
  field_simp [hX.ne', ha.ne', hQ]

theorem sec7_ra_dBreve6ImageK_deriv_bound_aled {X a d z : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hd : 0 < d) (ha2 : a ≤ d)
    (hzlo : (99 / 100 : ℝ) * d ≤ z) (hzhi : z ≤ (101 / 100 : ℝ) * d) :
    |(315 / (64 * X ^ 6 * a ^ 6)) *
        (sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 -
          11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
            sec7_ra_dBreve6ImageQ a z ^ 12)|
      ≤ 1500000 * d ^ 18 / (X * a) ^ 6 := by
  have hz : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
  have hza_pos : 0 < z + a := by positivity
  have haz : a ≤ (102 / 100 : ℝ) * z := by nlinarith
  have hza_hi : z + a ≤ (202 / 100 : ℝ) * z := by nlinarith
  have ha2z_hi : a + 2 * z ≤ (302 / 100 : ℝ) * z := by nlinarith
  have hQp_hi : 3 * a + 6 * z ≤ (906 / 100 : ℝ) * z := by nlinarith
  have hza2_core :
      (z + a) ^ 2 * (a + 2 * z) ≤
        (((202 / 100 : ℝ) * z) ^ 2) * (((302 / 100 : ℝ) * z)) := by
    have hsq : (z + a) ^ 2 ≤ (((202 / 100 : ℝ) * z) ^ 2) :=
      pow_le_pow_left₀ hza_pos.le hza_hi 2
    exact mul_le_mul hsq ha2z_hi (by positivity) (by positivity)
  have hza1_core :
      (z + a) * (a + 2 * z) ≤
        (((202 / 100 : ℝ) * z)) * (((302 / 100 : ℝ) * z)) := by
    exact mul_le_mul hza_hi ha2z_hi (by positivity)
      (by positivity : 0 ≤ (202 / 100 : ℝ) * z)
  have hrec_core :
      (z + a) * (a + 2 * z) * (3 * a + 6 * z) ≤
        (((202 / 100 : ℝ) * z)) * (((302 / 100 : ℝ) * z)) *
          (((906 / 100 : ℝ) * z)) := by
    exact mul_le_mul hza1_core hQp_hi (by positivity) (by positivity)
  have hP := sec7_ra_dBreve6ImagePoly_bound_aled (a := a) (d := d) (z := z)
    ha hd ha2 hzlo
  have hPd := sec7_ra_dBreve6ImagePolyDeriv_bound_aled (a := a) (d := d) (z := z)
    ha hd ha2 hzlo
  have hQ_lower : (3 : ℝ) * z * (z + a) ≤ sec7_ra_dBreve6ImageQ a z := by
    unfold sec7_ra_dBreve6ImageQ
    nlinarith [sq_nonneg a]
  have hQ_pos : 0 < sec7_ra_dBreve6ImageQ a z := by
    unfold sec7_ra_dBreve6ImageQ
    positivity
  have hQbase_pos : 0 < (3 : ℝ) * z * (z + a) := by positivity
  have hQ11_lower : ((3 : ℝ) * z * (z + a)) ^ 11 ≤
      sec7_ra_dBreve6ImageQ a z ^ 11 :=
    pow_le_pow_left₀ hQbase_pos.le hQ_lower 11
  have hQ12_lower : ((3 : ℝ) * z * (z + a)) ^ 12 ≤
      sec7_ra_dBreve6ImageQ a z ^ 12 :=
    pow_le_pow_left₀ hQbase_pos.le hQ_lower 12
  have hT1 :
      13 * z ^ 12 * (z + a) ^ 13 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePoly a z
        ≤ 30000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
    calc
      13 * z ^ 12 * (z + a) ^ 13 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePoly a z
          ≤ 13 * z ^ 12 * (z + a) ^ 13 * (a + 2 * z) *
              (12000000 * z ^ 14) := by gcongr
      _ = 13 * 12000000 * z ^ 26 * (z + a) ^ 11 *
            ((z + a) ^ 2 * (a + 2 * z)) := by ring
      _ ≤ 13 * 12000000 * z ^ 26 * (z + a) ^ 11 *
            ((((202 / 100 : ℝ) * z) ^ 2) * (((302 / 100 : ℝ) * z))) := by
            gcongr
      _ = (13 * 12000000 * (202 / 100 : ℝ) ^ 2 * (302 / 100 : ℝ)) *
            z ^ 29 * (z + a) ^ 11 := by ring
      _ ≤ 30000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
            rw [show 30000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) =
              (30000 * (3 : ℝ) ^ 11) * z ^ 29 * (z + a) ^ 11 by ring]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by norm_num :
                  13 * 12000000 * (202 / 100 : ℝ) ^ 2 * (302 / 100 : ℝ) ≤
                    30000 * (3 : ℝ) ^ 11)
                (pow_nonneg hz.le 29))
              (pow_nonneg hza_pos.le 11)
  have hT2 :
      13 * z ^ 13 * (z + a) ^ 12 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePoly a z
        ≤ 20000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
    calc
      13 * z ^ 13 * (z + a) ^ 12 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePoly a z
          ≤ 13 * z ^ 13 * (z + a) ^ 12 * (a + 2 * z) *
              (12000000 * z ^ 14) := by gcongr
      _ = 13 * 12000000 * z ^ 27 * (z + a) ^ 11 *
            ((z + a) * (a + 2 * z)) := by ring
      _ ≤ 13 * 12000000 * z ^ 27 * (z + a) ^ 11 *
            ((((202 / 100 : ℝ) * z)) * (((302 / 100 : ℝ) * z))) := by
            gcongr
      _ = (13 * 12000000 * (202 / 100 : ℝ) * (302 / 100 : ℝ)) *
            z ^ 29 * (z + a) ^ 11 := by ring
      _ ≤ 20000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
            rw [show 20000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) =
              (20000 * (3 : ℝ) ^ 11) * z ^ 29 * (z + a) ^ 11 by ring]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by norm_num :
                  13 * 12000000 * (202 / 100 : ℝ) * (302 / 100 : ℝ) ≤
                    20000 * (3 : ℝ) ^ 11)
                (pow_nonneg hz.le 29))
              (pow_nonneg hza_pos.le 11)
  have hT3 :
      2 * z ^ 13 * (z + a) ^ 13 * sec7_ra_dBreve6ImagePoly a z
        ≤ 10000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
    calc
      2 * z ^ 13 * (z + a) ^ 13 * sec7_ra_dBreve6ImagePoly a z
          ≤ 2 * z ^ 13 * (z + a) ^ 13 * (12000000 * z ^ 14) := by
            gcongr
      _ = 2 * 12000000 * z ^ 27 * (z + a) ^ 11 * (z + a) ^ 2 := by ring
      _ ≤ 2 * 12000000 * z ^ 27 * (z + a) ^ 11 *
            (((202 / 100 : ℝ) * z) ^ 2) := by
            gcongr
      _ = (2 * 12000000 * (202 / 100 : ℝ) ^ 2) * z ^ 29 * (z + a) ^ 11 := by
            ring
      _ ≤ 10000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
            rw [show 10000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) =
              (10000 * (3 : ℝ) ^ 11) * z ^ 29 * (z + a) ^ 11 by ring]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by norm_num :
                  2 * 12000000 * (202 / 100 : ℝ) ^ 2 ≤ 10000 * (3 : ℝ) ^ 11)
                (pow_nonneg hz.le 29))
              (pow_nonneg hza_pos.le 11)
  have hT4 :
      z ^ 13 * (z + a) ^ 13 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePolyDeriv a z
        ≤ 40000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
    calc
      z ^ 13 * (z + a) ^ 13 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePolyDeriv a z
          ≤ z ^ 13 * (z + a) ^ 13 * (a + 2 * z) *
              (100000000 * z ^ 13) := by gcongr
      _ = 100000000 * z ^ 26 * (z + a) ^ 11 *
            ((z + a) ^ 2 * (a + 2 * z)) := by ring
      _ ≤ 100000000 * z ^ 26 * (z + a) ^ 11 *
            ((((202 / 100 : ℝ) * z) ^ 2) * (((302 / 100 : ℝ) * z))) := by
            gcongr
      _ = (100000000 * (202 / 100 : ℝ) ^ 2 * (302 / 100 : ℝ)) *
            z ^ 29 * (z + a) ^ 11 := by ring
      _ ≤ 40000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
            rw [show 40000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) =
              (40000 * (3 : ℝ) ^ 11) * z ^ 29 * (z + a) ^ 11 by ring]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by norm_num :
                  100000000 * (202 / 100 : ℝ) ^ 2 * (302 / 100 : ℝ) ≤
                    40000 * (3 : ℝ) ^ 11)
                (pow_nonneg hz.le 29))
              (pow_nonneg hza_pos.le 11)
  have hUd_le :
      sec7_ra_dBreve6ImageUDeriv a z ≤
        100000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := by
    unfold sec7_ra_dBreve6ImageUDeriv
    linarith [hT1, hT2, hT3, hT4]
  have hUd_nonneg : 0 ≤ sec7_ra_dBreve6ImageUDeriv a z := by
    unfold sec7_ra_dBreve6ImageUDeriv sec7_ra_dBreve6ImagePoly sec7_ra_dBreve6ImagePolyDeriv
    positivity
  have hUd_div :
      sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 ≤
        100000 * z ^ 18 := by
    rw [div_le_iff₀ (pow_pos hQ_pos 11)]
    calc
      sec7_ra_dBreve6ImageUDeriv a z
          ≤ 100000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 11) := hUd_le
      _ ≤ 100000 * z ^ 18 * sec7_ra_dBreve6ImageQ a z ^ 11 := by
            gcongr
  have hU_rec :
      11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z)
        ≤ 50000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 12) := by
    unfold sec7_ra_dBreve6ImageU
    calc
      11 * (z ^ 13 * (z + a) ^ 13 * (a + 2 * z) *
          sec7_ra_dBreve6ImagePoly a z) * (3 * a + 6 * z)
          ≤ 11 * (z ^ 13 * (z + a) ^ 13 * (a + 2 * z) *
              (12000000 * z ^ 14)) * (3 * a + 6 * z) := by gcongr
      _ = 11 * 12000000 * z ^ 27 * (z + a) ^ 12 *
            ((z + a) * (a + 2 * z) * (3 * a + 6 * z)) := by ring
      _ ≤ 11 * 12000000 * z ^ 27 * (z + a) ^ 12 *
            ((((202 / 100 : ℝ) * z)) * (((302 / 100 : ℝ) * z)) *
              (((906 / 100 : ℝ) * z))) := by
            gcongr
      _ = (11 * 12000000 * (202 / 100 : ℝ) * (302 / 100 : ℝ) *
            (906 / 100 : ℝ)) * z ^ 30 * (z + a) ^ 12 := by ring
      _ ≤ 50000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 12) := by
            rw [show 50000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 12) =
              (50000 * (3 : ℝ) ^ 12) * z ^ 30 * (z + a) ^ 12 by ring]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by norm_num :
                  11 * 12000000 * (202 / 100 : ℝ) * (302 / 100 : ℝ) *
                      (906 / 100 : ℝ) ≤
                    50000 * (3 : ℝ) ^ 12)
                (pow_nonneg hz.le 30))
              (pow_nonneg hza_pos.le 12)
  have hU_nonneg : 0 ≤ sec7_ra_dBreve6ImageU a z := by
    unfold sec7_ra_dBreve6ImageU sec7_ra_dBreve6ImagePoly
    positivity
  have hRec_nonneg :
      0 ≤ 11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
        sec7_ra_dBreve6ImageQ a z ^ 12 := by
    positivity
  have hRec_div :
      11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
          sec7_ra_dBreve6ImageQ a z ^ 12 ≤
        50000 * z ^ 18 := by
    rw [div_le_iff₀ (pow_pos hQ_pos 12)]
    calc
      11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z)
          ≤ 50000 * z ^ 18 * (((3 : ℝ) * z * (z + a)) ^ 12) := hU_rec
      _ ≤ 50000 * z ^ 18 * sec7_ra_dBreve6ImageQ a z ^ 12 := by
            gcongr
  have hA_nonneg :
      0 ≤ sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 :=
    div_nonneg hUd_nonneg (pow_nonneg hQ_pos.le 11)
  have hdiff :
      |sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 -
          11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
            sec7_ra_dBreve6ImageQ a z ^ 12|
        ≤ 150000 * z ^ 18 := by
    let A : ℝ := sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11
    let B : ℝ := 11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
      sec7_ra_dBreve6ImageQ a z ^ 12
    have htri : |A - B| ≤ A + B := by
      refine abs_sub_le_iff.2 ⟨?_, ?_⟩
      · dsimp [A, B]
        linarith [hRec_nonneg]
      · dsimp [A, B]
        linarith [hA_nonneg]
    have hsum : A + B ≤ 150000 * z ^ 18 := by
      dsimp [A, B]
      linarith [hUd_div, hRec_div]
    exact le_trans (by simpa [A, B] using htri) hsum
  have hC_nonneg : 0 ≤ 315 / (64 * X ^ 6 * a ^ 6) := by positivity
  have hz18_le : z ^ 18 ≤ (((101 / 100 : ℝ) * d) ^ 18) :=
    pow_le_pow_left₀ hz.le hzhi 18
  calc
    |(315 / (64 * X ^ 6 * a ^ 6)) *
        (sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 -
          11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
            sec7_ra_dBreve6ImageQ a z ^ 12)|
        = (315 / (64 * X ^ 6 * a ^ 6)) *
          |sec7_ra_dBreve6ImageUDeriv a z / sec7_ra_dBreve6ImageQ a z ^ 11 -
            11 * sec7_ra_dBreve6ImageU a z * (3 * a + 6 * z) /
              sec7_ra_dBreve6ImageQ a z ^ 12| := by
            rw [abs_mul, abs_of_nonneg hC_nonneg]
    _ ≤ (315 / (64 * X ^ 6 * a ^ 6)) * (150000 * z ^ 18) := by
          exact mul_le_mul_of_nonneg_left hdiff hC_nonneg
    _ ≤ (315 / (64 * X ^ 6 * a ^ 6)) *
          (150000 * (((101 / 100 : ℝ) * d) ^ 18)) := by
          gcongr
    _ ≤ 1500000 * d ^ 18 / (X * a) ^ 6 := by
          field_simp [hX.ne', ha.ne']
          have hconst : 315 * (150000 * (101 / 100 : ℝ) ^ 18) ≤
              1500000 * 64 := by
            norm_num
          linarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hd.le 18)]

private theorem sec7_ra_B3H_bound6_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |sec7_ra_B3H P.X a j 6 d| ≤
      (3000000 * d ^ 22 / (P.X * a) ^ 7) * |j| := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  set qd := sec7_ra_B3q P.X a j d with hqd_def
  have hqspec : Ffun P.X a qd = Ffun P.X a d + j := by
    rw [hqd_def]
    exact sec7_ra_B3q_Ffun_eq (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hshift
  have hqwin :
      (99 / 100 : ℝ) * d ≤ qd ∧ qd ≤ (101 / 100 : ℝ) * d := by
    simpa [hqd_def] using
      (sec7_ra_B3q_close_Icc (X := P.X) (a := a) (d := d) (j := j) hclose)
  have hqpos : 0 < qd := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1
  set L : ℝ := 1500000 * d ^ 18 / (P.X * a) ^ 6 with hL_def
  have hderiv : ∀ u ∈ Set.uIcc qd d,
      HasDerivAt (sec7_ra_dBreve6ImageK P.X a)
        ((315 / (64 * P.X ^ 6 * a ^ 6)) *
          (sec7_ra_dBreve6ImageUDeriv a u / sec7_ra_dBreve6ImageQ a u ^ 11 -
            11 * sec7_ra_dBreve6ImageU a u * (3 * a + 6 * u) /
              sec7_ra_dBreve6ImageQ a u ^ 12)) u := by
    intro u hu
    have hu_pos : 0 < u := by
      rcases le_total qd d with hqd_le | hd_le
      · rw [uIcc_of_le hqd_le] at hu
        exact lt_of_lt_of_le hqpos hu.1
      · rw [uIcc_of_ge hd_le] at hu
        exact lt_of_lt_of_le hd hu.1
    have hQ : sec7_ra_dBreve6ImageQ a u ≠ 0 := by
      unfold sec7_ra_dBreve6ImageQ
      positivity
    exact sec7_ra_dBreve6ImageK_hasDerivAt (X := P.X) (a := a) (z := u)
      P.X_pos.ne' ha0.ne' hQ
  have hbound : ∀ u ∈ Set.uIcc qd d,
      |(315 / (64 * P.X ^ 6 * a ^ 6)) *
        (sec7_ra_dBreve6ImageUDeriv a u / sec7_ra_dBreve6ImageQ a u ^ 11 -
          11 * sec7_ra_dBreve6ImageU a u * (3 * a + 6 * u) /
            sec7_ra_dBreve6ImageQ a u ^ 12)| ≤ L := by
    intro u hu
    have hu_close : (99 / 100 : ℝ) * d ≤ u ∧ u ≤ (101 / 100 : ℝ) * d := by
      rcases le_total qd d with hqd_le | hd_le
      · rw [uIcc_of_le hqd_le] at hu
        constructor
        · exact le_trans hqwin.1 hu.1
        · linarith [hd, hu.2]
      · rw [uIcc_of_ge hd_le] at hu
        constructor
        · linarith [hd, hu.1]
        · exact le_trans hu.2 hqwin.2
    simpa [L, hL_def] using
      sec7_ra_dBreve6ImageK_deriv_bound_aled (X := P.X) (a := a) (d := d)
        (z := u) P.X_pos ha0 hd ha2 hu_close.1 hu_close.2
  have hmvt :=
    (convex_uIcc qd d).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hderiv u hu).hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]; exact hbound u hu)
      (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hKdiff : |sec7_ra_dBreve6ImageK P.X a d - sec7_ra_dBreve6ImageK P.X a qd| ≤
      L * |d - qd| := by
    simpa [Real.norm_eq_abs] using hmvt
  have hH_eq :
      sec7_ra_B3H P.X a j 6 d =
        sec7_ra_dBreve6ImageK P.X a qd - sec7_ra_dBreve6ImageK P.X a d := by
    rw [sec7_ra_B3H, sec7_ra_dBreveD]
    rw [show Ffun P.X a d + j = Ffun P.X a qd by rw [hqspec]]
    rw [sec7_ra_dBreve6ImageK_eq (X := P.X) (a := a) (z := qd) P.X_pos ha0 hqpos]
    rw [sec7_ra_dBreve6ImageK_eq (X := P.X) (a := a) (z := d) P.X_pos ha0 hd]
  have hqdiff := sec7_ra_B3_qdiff_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hL_nonneg : 0 ≤ L := by
    rw [hL_def]
    positivity
  calc
    |sec7_ra_B3H P.X a j 6 d|
        = |sec7_ra_dBreve6ImageK P.X a qd - sec7_ra_dBreve6ImageK P.X a d| := by
          rw [hH_eq]
    _ = |sec7_ra_dBreve6ImageK P.X a d - sec7_ra_dBreve6ImageK P.X a qd| := by
          rw [abs_sub_comm]
    _ ≤ L * |d - qd| := hKdiff
    _ = L * |qd - d| := by rw [abs_sub_comm]
    _ ≤ L * (2 * |j| * d ^ 4 / (P.X * a)) := by
          exact mul_le_mul_of_nonneg_left hqdiff hL_nonneg
    _ = (3000000 * d ^ 22 / (P.X * a) ^ 7) * |j| := by
          rw [hL_def]
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring

private theorem sec7_ra_B3_bound_sharp_aled_k5 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 5 * |j| / (d * (P.X * a)) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let F5 : ℝ := iteratedDeriv 5 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  let H5 : ℝ := sec7_ra_B3H P.X a j 5 d
  have hiter :
      iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
          5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
          10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 5) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, F5, H1, H2, H3, H4, H5, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, hF5⟩
  rcases sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2⟩
  have hH3 := sec7_ra_B3H_bound3_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH4 := sec7_ra_B3H_bound4_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH5 := sec7_ra_B3H_bound5_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 26 * P.X * a / d ^ 5 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 128 * P.X * a / d ^ 6 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF4ub_nonneg : 0 ≤ 800 * P.X * a / d ^ 7 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 800) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 7)
  have hF5ub_nonneg : 0 ≤ 6000 * P.X * a / d ^ 8 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6000) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 8)
  have hF1pow3 : |F1| ^ 3 ≤ (7 * P.X * a / d ^ 4) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 3
  have hF1pow5 : |F1| ^ 5 ≤ (7 * P.X * a / d ^ 4) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 5
  have hF2pow2 : |F2| ^ 2 ≤ (26 * P.X * a / d ^ 5) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF2 2
  have hcoef2a : |5 * F1 * F4| ≤
      5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    gcongr
  have hcoef2b : |10 * F2 * F3| ≤
      10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    gcongr
  have hcoef2 : |5 * F1 * F4 + 10 * F2 * F3| ≤
      5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
        10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) := by
    calc
      |5 * F1 * F4 + 10 * F2 * F3| ≤ |5 * F1 * F4| + |10 * F2 * F3| :=
        abs_add_le _ _
      _ ≤ 5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
          10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) :=
        add_le_add hcoef2a hcoef2b
  have hcoef2_nonneg : 0 ≤
      5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
        10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hF1ub_nonneg) hF4ub_nonneg)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hF2ub_nonneg) hF3ub_nonneg)
  have hinnera : |2 * F1 * F3| ≤
      2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  have hinnerb : |3 * F2 ^ 2| ≤ 3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul_of_nonneg_left hF2pow2 (by norm_num)
  have hinner : |2 * F1 * F3 + 3 * F2 ^ 2| ≤
      2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
        3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    calc
      |2 * F1 * F3 + 3 * F2 ^ 2| ≤ |2 * F1 * F3| + |3 * F2 ^ 2| := abs_add_le _ _
      _ ≤ 2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2 := add_le_add hinnera hinnerb
  have hinner_nonneg : 0 ≤
      2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
        3 * (26 * P.X * a / d ^ 5) ^ 2 := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF1ub_nonneg) hF3ub_nonneg)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _))
  have hcoef3 : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2)| ≤
      5 * (7 * P.X * a / d ^ 4) *
        (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    have hleft : 5 * |F1| ≤ 5 * (7 * P.X * a / d ^ 4) :=
      mul_le_mul_of_nonneg_left hF1 (by norm_num)
    simpa [mul_assoc] using
      (mul_le_mul hleft hinner (abs_nonneg _)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hF1ub_nonneg))
  have hcoef3_nonneg : 0 ≤
      5 * (7 * P.X * a / d ^ 4) *
        (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hF1ub_nonneg) hinner_nonneg
  have hcoef4 : |10 * F1 ^ 3 * F2| ≤
      10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5) := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    have hleft : 10 * |F1| ^ 3 ≤ 10 * (7 * P.X * a / d ^ 4) ^ 3 :=
      mul_le_mul_of_nonneg_left hF1pow3 (by norm_num)
    simpa [mul_assoc] using
      (mul_le_mul hleft hF2 (abs_nonneg _)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (pow_nonneg hF1ub_nonneg 3)))
  have hcoef4_nonneg : 0 ≤ 10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5) :=
    mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (pow_nonneg hF1ub_nonneg 3))
      hF2ub_nonneg
  have hterm1 : |F5 * H1| ≤
      (6000 * P.X * a / d ^ 8) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF5 hH1 (abs_nonneg _) hF5ub_nonneg
  have hterm2 : |(5 * F1 * F4 + 10 * F2 * F3) * H2| ≤
      (5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
          10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6)) *
        ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef2 hH2 (abs_nonneg _) hcoef2_nonneg
  have hterm3 : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| ≤
      (5 * (7 * P.X * a / d ^ 4) *
          (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2)) *
        ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef3 hH3 (abs_nonneg _) hcoef3_nonneg
  have hterm4 : |10 * F1 ^ 3 * F2 * H4| ≤
      (10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5)) *
        ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef4 hH4 (abs_nonneg _) hcoef4_nonneg
  have hterm5 : |F1 ^ 5 * H5| ≤
      (7 * P.X * a / d ^ 4) ^ 5 * ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow5 hH5 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 5)
  calc
    |iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
            5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
            10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5| := by rw [hiter]
    _ ≤ |F5 * H1| + |(5 * F1 * F4 + 10 * F2 * F3) * H2| +
        |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| +
        |10 * F1 ^ 3 * F2 * H4| + |F1 ^ 5 * H5| := by
          linarith [abs_add_le
            (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
              5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
              10 * F1 ^ 3 * F2 * H4) (F1 ^ 5 * H5),
            abs_add_le
              (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
                5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3)
              (10 * F1 ^ 3 * F2 * H4),
            abs_add_le
              (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2)
              (5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3),
            abs_add_le (F5 * H1) ((5 * F1 * F4 + 10 * F2 * F3) * H2)]
    _ ≤ (6000 * P.X * a / d ^ 8) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
            10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6)) *
          ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (5 * (7 * P.X * a / d ^ 4) *
            (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
              3 * (26 * P.X * a / d ^ 5) ^ 2)) *
          ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5)) *
          ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 5 * ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4, hterm5]
    _ = 30084656000 * |j| / (d * (P.X * a)) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ = sec7_ra_B3SharpScaleAled 5 * |j| / (d * (P.X * a)) := by
          simp [sec7_ra_B3SharpScaleAled]

private theorem sec7_ra_B3_bound_sharp_aled_k6 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 6 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3SharpScaleAled 6 * |j| / (d ^ 2 * (P.X * a)) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hX : (0 : ℝ) < P.X := P.X_pos
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let F5 : ℝ := iteratedDeriv 5 (fun t => Ffun P.X a t) d
  let F6 : ℝ := iteratedDeriv 6 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  let H5 : ℝ := sec7_ra_B3H P.X a j 5 d
  let H6 : ℝ := sec7_ra_B3H P.X a j 6 d
  have hiter :
      iteratedDeriv 6 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F6 * H1 + (6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2 +
          (15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3 +
          (20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4 +
          15 * F1 ^ 4 * F2 * H5 + F1 ^ 6 * H6 := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 6) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, F5, F6, H1, H2, H3, H4, H5, H6, sec7_ra_B3E] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, hF5⟩
  have hF6 : |F6| ≤ 197009794800 * P.X * a / d ^ 9 :=
    (Ffun_deriv6_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by linarith)).2
  rcases sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a) (d := d)
      (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose with ⟨hH1, hH2⟩
  have hH3 := sec7_ra_B3H_bound3_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH4 := sec7_ra_B3H_bound4_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH5 := sec7_ra_B3H_bound5_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH6 := sec7_ra_B3H_bound6_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have htri3 : ∀ x y z : ℝ, |x + y + z| ≤ |x| + |y| + |z| := by
    intro x y z
    calc |x + y + z| ≤ |x + y| + |z| := abs_add_le _ _
      _ ≤ |x| + |y| + |z| := by have := abs_add_le x y; linarith
  -- coefficient bound for H2
  have hc2 : |6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2| ≤
      6 * (7 * P.X * a / d ^ 4) * (6000 * P.X * a / d ^ 8) +
        15 * (26 * P.X * a / d ^ 5) * (800 * P.X * a / d ^ 7) +
        10 * (128 * P.X * a / d ^ 6) ^ 2 := by
    refine (htri3 _ _ _).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]; gcongr
    · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15)]; gcongr
    · rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]; gcongr
  have hc2nn : 0 ≤ 6 * (7 * P.X * a / d ^ 4) * (6000 * P.X * a / d ^ 8) +
        15 * (26 * P.X * a / d ^ 5) * (800 * P.X * a / d ^ 7) +
        10 * (128 * P.X * a / d ^ 6) ^ 2 := by positivity
  -- coefficient bound for H3
  have hc3 : |15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3| ≤
      15 * (7 * P.X * a / d ^ 4) ^ 2 * (800 * P.X * a / d ^ 7) +
        60 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) +
        15 * (26 * P.X * a / d ^ 5) ^ 3 := by
    refine (htri3 _ _ _).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15)]; gcongr
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 60)]; gcongr
    · rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15)]; gcongr
  have hc3nn : 0 ≤ 15 * (7 * P.X * a / d ^ 4) ^ 2 * (800 * P.X * a / d ^ 7) +
        60 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) +
        15 * (26 * P.X * a / d ^ 5) ^ 3 := by positivity
  -- coefficient bound for H4
  have hc4 : |20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2| ≤
      20 * (7 * P.X * a / d ^ 4) ^ 3 * (128 * P.X * a / d ^ 6) +
        45 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) ^ 2 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20)]; gcongr
    · rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 45)]; gcongr
  have hc4nn : 0 ≤ 20 * (7 * P.X * a / d ^ 4) ^ 3 * (128 * P.X * a / d ^ 6) +
        45 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) ^ 2 := by positivity
  -- coefficient bound for H5
  have hc5 : |15 * F1 ^ 4 * F2| ≤
      15 * (7 * P.X * a / d ^ 4) ^ 4 * (26 * P.X * a / d ^ 5) := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15)]; gcongr
  have hc5nn : 0 ≤ 15 * (7 * P.X * a / d ^ 4) ^ 4 * (26 * P.X * a / d ^ 5) := by positivity
  -- coefficient bound for H6
  have hc6 : |F1 ^ 6| ≤ (7 * P.X * a / d ^ 4) ^ 6 := by
    rw [abs_pow]; gcongr
  have hG6nn : 0 ≤ 197009794800 * P.X * a / d ^ 9 := by positivity
  -- term bounds
  have hterm1 : |F6 * H1| ≤
      (197009794800 * P.X * a / d ^ 9) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) := by
    rw [abs_mul]; exact mul_le_mul hF6 hH1 (abs_nonneg _) hG6nn
  have hterm2 : |(6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2| ≤
      (6 * (7 * P.X * a / d ^ 4) * (6000 * P.X * a / d ^ 8) +
          15 * (26 * P.X * a / d ^ 5) * (800 * P.X * a / d ^ 7) +
          10 * (128 * P.X * a / d ^ 6) ^ 2) *
        ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]; exact mul_le_mul hc2 hH2 (abs_nonneg _) hc2nn
  have hterm3 : |(15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3| ≤
      (15 * (7 * P.X * a / d ^ 4) ^ 2 * (800 * P.X * a / d ^ 7) +
          60 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) +
          15 * (26 * P.X * a / d ^ 5) ^ 3) *
        ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul]; exact mul_le_mul hc3 hH3 (abs_nonneg _) hc3nn
  have hterm4 : |(20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4| ≤
      (20 * (7 * P.X * a / d ^ 4) ^ 3 * (128 * P.X * a / d ^ 6) +
          45 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) ^ 2) *
        ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul]; exact mul_le_mul hc4 hH4 (abs_nonneg _) hc4nn
  have hterm5 : |15 * F1 ^ 4 * F2 * H5| ≤
      (15 * (7 * P.X * a / d ^ 4) ^ 4 * (26 * P.X * a / d ^ 5)) *
        ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
    rw [abs_mul]; exact mul_le_mul hc5 hH5 (abs_nonneg _) hc5nn
  have hterm6 : |F1 ^ 6 * H6| ≤
      (7 * P.X * a / d ^ 4) ^ 6 * ((3000000 * d ^ 22 / (P.X * a) ^ 7) * |j|) := by
    rw [abs_mul]; exact mul_le_mul hc6 hH6 (abs_nonneg _) (by positivity)
  calc
    |iteratedDeriv 6 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F6 * H1 + (6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2 +
            (15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3 +
            (20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4 +
            15 * F1 ^ 4 * F2 * H5 + F1 ^ 6 * H6| := by rw [hiter]
    _ ≤ |F6 * H1| + |(6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2| +
        |(15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3| +
        |(20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4| +
        |15 * F1 ^ 4 * F2 * H5| + |F1 ^ 6 * H6| := by
          linarith [abs_add_le
            (F6 * H1 + (6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2 +
              (15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3 +
              (20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4 +
              15 * F1 ^ 4 * F2 * H5) (F1 ^ 6 * H6),
            abs_add_le
              (F6 * H1 + (6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2 +
                (15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3 +
                (20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4) (15 * F1 ^ 4 * F2 * H5),
            abs_add_le
              (F6 * H1 + (6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2 +
                (15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3)
              ((20 * F1 ^ 3 * F3 + 45 * F1 ^ 2 * F2 ^ 2) * H4),
            abs_add_le
              (F6 * H1 + (6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2)
              ((15 * F1 ^ 2 * F4 + 60 * F1 * F2 * F3 + 15 * F2 ^ 3) * H3),
            abs_add_le (F6 * H1)
              ((6 * F1 * F5 + 15 * F2 * F4 + 10 * F3 ^ 2) * H2)]
    _ ≤ (197009794800 * P.X * a / d ^ 9) * ((300 * d ^ 7 / (P.X * a) ^ 2) * |j|) +
        (6 * (7 * P.X * a / d ^ 4) * (6000 * P.X * a / d ^ 8) +
            15 * (26 * P.X * a / d ^ 5) * (800 * P.X * a / d ^ 7) +
            10 * (128 * P.X * a / d ^ 6) ^ 2) *
          ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (15 * (7 * P.X * a / d ^ 4) ^ 2 * (800 * P.X * a / d ^ 7) +
            60 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6) +
            15 * (26 * P.X * a / d ^ 5) ^ 3) *
          ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (20 * (7 * P.X * a / d ^ 4) ^ 3 * (128 * P.X * a / d ^ 6) +
            45 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) ^ 2) *
          ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) +
        (15 * (7 * P.X * a / d ^ 4) ^ 4 * (26 * P.X * a / d ^ 5)) *
          ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 6 * ((3000000 * d ^ 22 / (P.X * a) ^ 7) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6]
    _ = 60985797208000 * |j| / (d ^ 2 * (P.X * a)) := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ = sec7_ra_B3SharpScaleAled 6 * |j| / (d ^ 2 * (P.X * a)) := by
          simp [sec7_ra_B3SharpScaleAled]

theorem sec7_ra_B3_bound_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ} {k : ℕ}
    (hk : k ≤ 6)
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |dBreve P.X a (Ffun P.X a d + j) - d| ≤ d / 100) :
    |iteratedDeriv k (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d| ≤
      match k with
      | 0 => (2 : ℝ) * |j| * d ^ 4 / (P.X * a)
      | 1 => (120 : ℝ) * |j| * d ^ 3 / (P.X * a)
      | 2 => (17600 : ℝ) * |j| * d ^ 2 / (P.X * a)
      | 3 => (1176600 : ℝ) * |j| * d / (P.X * a)
      | 4 => (144344400 : ℝ) * |j| / (P.X * a)
      | 5 => (30084656000 : ℝ) * |j| / (d * (P.X * a))
      | 6 => (60985797208000 : ℝ) * |j| / (d ^ 2 * (P.X * a))
      | _ => 0 := by
  have hclose' : |sec7_ra_B3q P.X a j d - d| ≤ d / 100 := by
    simpa [sec7_ra_B3q] using hclose
  interval_cases k
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k0 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k1 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k2 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k3 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k4 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k5 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B3SharpScaleAled] using
      sec7_ra_B3_bound_sharp_aled_k6 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'

private theorem sec7_ra_B3_k2_scale {P : Globals} {S : Scale P} {a d : ℝ}
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hd_lo : S.D / 16 ≤ d) :
    (11310 * P.X * a / d ^ 5) * (sec7_cPh * S.D / S.F ^ 2) +
        (314 * P.X * a / d ^ 4) ^ 2 * ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)
      ≤ sec7_ra_B3Scale 2 * d ^ 2 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hDle : S.D ≤ 16 * d := by linarith [hd_lo]
  have hD7 : S.D ^ 7 ≤ 16 ^ 7 * d ^ 7 := by
    have hpow : S.D ^ 7 ≤ (16 * d) ^ 7 := pow_le_pow_left₀ hDpos.le hDle 7
    calc
      S.D ^ 7 ≤ (16 * d) ^ 7 := hpow
      _ = 16 ^ 7 * d ^ 7 := by ring
  have hD10 : S.D ^ 10 ≤ 16 ^ 10 * d ^ 10 := by
    have hpow : S.D ^ 10 ≤ (16 * d) ^ 10 := pow_le_pow_left₀ hDpos.le hDle 10
    calc
      S.D ^ 10 ≤ (16 * d) ^ 10 := hpow
      _ = 16 ^ 10 * d ^ 10 := by ring
  have ha2 : a ^ 2 ≤ (11 * S.A) ^ 2 := pow_le_pow_left₀ ha0.le ha_hi 2
  have ha3 : a ^ 3 ≤ (11 * S.A) ^ 3 := pow_le_pow_left₀ ha0.le ha_hi 3
  have hprod1 : a ^ 2 * S.D ^ 7 ≤ (11 * S.A) ^ 2 * (16 ^ 7 * d ^ 7) :=
    mul_le_mul ha2 hD7 (by positivity) (by positivity)
  have hprod2 : a ^ 3 * S.D ^ 10 ≤ (11 * S.A) ^ 3 * (16 ^ 10 * d ^ 10) :=
    mul_le_mul ha3 hD10 (by positivity) (by positivity)
  have hterm1 :
      (11310 * P.X * a / d ^ 5) * (sec7_cPh * S.D / S.F ^ 2)
        ≤ (10 ^ 40 : ℝ) * d ^ 2 / (P.X * a) := by
    calc
      (11310 * P.X * a / d ^ 5) * (sec7_cPh * S.D / S.F ^ 2)
          = (11310 * sec7_cPh) * a * S.D ^ 7 / (P.X * S.A ^ 2 * d ^ 5) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((11310 * sec7_cPh) * (11 ^ 2 * 16 ^ 7)) * d ^ 2 / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod1
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 11310) sec7_cPh_pos.le)
            rw [show P.X * S.A ^ 2 * d ^ 5 = P.X * (S.A ^ 2 * d ^ 5) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (sq_pos_of_pos hApos) (pow_pos hd 5)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 40 : ℝ) * d ^ 2 / (P.X * a) := by
            have hconst : (11310 * sec7_cPh : ℝ) * (11 ^ 2 * 16 ^ 7) ≤ 10 ^ 40 := by
              norm_num [sec7_cPh]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le
  have hterm2 :
      (314 * P.X * a / d ^ 4) ^ 2 * ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)
        ≤ (10 ^ 110 : ℝ) * d ^ 2 / (P.X * a) := by
    calc
      (314 * P.X * a / d ^ 4) ^ 2 * ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)
          = (314 ^ 2 * (10 ^ 80 : ℝ)) * a ^ 2 * S.D ^ 10 /
              (P.X * S.A ^ 3 * d ^ 8) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((314 ^ 2 * (10 ^ 80 : ℝ)) * (11 ^ 3 * 16 ^ 10)) *
            d ^ 2 / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod2
              (by positivity : 0 ≤ (314 ^ 2 * (10 ^ 80 : ℝ)))
            rw [show P.X * S.A ^ 3 * d ^ 8 = P.X * (S.A ^ 3 * d ^ 8) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 3) (pow_pos hd 8)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 110 : ℝ) * d ^ 2 / (P.X * a) := by
            have hconst : (314 ^ 2 * (10 ^ 80 : ℝ)) * (11 ^ 3 * 16 ^ 10) ≤
                10 ^ 110 := by
              norm_num
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le
  calc
    (11310 * P.X * a / d ^ 5) * (sec7_cPh * S.D / S.F ^ 2) +
        (314 * P.X * a / d ^ 4) ^ 2 * ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)
        ≤ (10 ^ 40 : ℝ) * d ^ 2 / (P.X * a) +
          (10 ^ 110 : ℝ) * d ^ 2 / (P.X * a) := add_le_add hterm1 hterm2
    _ ≤ sec7_ra_B3Scale 2 * d ^ 2 / (P.X * a) := by
          have hconst : (10 ^ 40 : ℝ) + 10 ^ 110 ≤ sec7_ra_B3Scale 2 := by
            norm_num [sec7_ra_B3Scale]
          calc
            (10 ^ 40 : ℝ) * d ^ 2 / (P.X * a) + 10 ^ 110 * d ^ 2 / (P.X * a)
                = ((10 ^ 40 : ℝ) + 10 ^ 110) * d ^ 2 / (P.X * a) := by ring
            _ ≤ sec7_ra_B3Scale 2 * d ^ 2 / (P.X * a) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le

private theorem sec7_ra_B3_k3_scale {P : Globals} {S : Scale P} {a d : ℝ}
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hd_lo : S.D / 16 ≤ d) :
    (542904 * P.X * a / d ^ 6) * (sec7_cPh * S.D / S.F ^ 2) +
        (3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) +
        (314 * P.X * a / d ^ 4) ^ 3 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
      ≤ sec7_ra_B3Scale 3 * d / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hDle : S.D ≤ 16 * d := by linarith [hd_lo]
  have hD7 : S.D ^ 7 ≤ 16 ^ 7 * d ^ 7 := by
    have hpow : S.D ^ 7 ≤ (16 * d) ^ 7 := pow_le_pow_left₀ hDpos.le hDle 7
    calc
      S.D ^ 7 ≤ (16 * d) ^ 7 := hpow
      _ = 16 ^ 7 * d ^ 7 := by ring
  have hD10 : S.D ^ 10 ≤ 16 ^ 10 * d ^ 10 := by
    have hpow : S.D ^ 10 ≤ (16 * d) ^ 10 := pow_le_pow_left₀ hDpos.le hDle 10
    calc
      S.D ^ 10 ≤ (16 * d) ^ 10 := hpow
      _ = 16 ^ 10 * d ^ 10 := by ring
  have hD13 : S.D ^ 13 ≤ 16 ^ 13 * d ^ 13 := by
    have hpow : S.D ^ 13 ≤ (16 * d) ^ 13 := pow_le_pow_left₀ hDpos.le hDle 13
    calc
      S.D ^ 13 ≤ (16 * d) ^ 13 := hpow
      _ = 16 ^ 13 * d ^ 13 := by ring
  have ha2 : a ^ 2 ≤ (11 * S.A) ^ 2 := pow_le_pow_left₀ ha0.le ha_hi 2
  have ha3 : a ^ 3 ≤ (11 * S.A) ^ 3 := pow_le_pow_left₀ ha0.le ha_hi 3
  have ha4 : a ^ 4 ≤ (11 * S.A) ^ 4 := pow_le_pow_left₀ ha0.le ha_hi 4
  have hprod1 : a ^ 2 * S.D ^ 7 ≤ (11 * S.A) ^ 2 * (16 ^ 7 * d ^ 7) :=
    mul_le_mul ha2 hD7 (by positivity) (by positivity)
  have hprod2 : a ^ 3 * S.D ^ 10 ≤ (11 * S.A) ^ 3 * (16 ^ 10 * d ^ 10) :=
    mul_le_mul ha3 hD10 (by positivity) (by positivity)
  have hprod3 : a ^ 4 * S.D ^ 13 ≤ (11 * S.A) ^ 4 * (16 ^ 13 * d ^ 13) :=
    mul_le_mul ha4 hD13 (by positivity) (by positivity)
  have hterm1 :
      (542904 * P.X * a / d ^ 6) * (sec7_cPh * S.D / S.F ^ 2)
        ≤ (10 ^ 129 : ℝ) * d / (P.X * a) := by
    calc
      (542904 * P.X * a / d ^ 6) * (sec7_cPh * S.D / S.F ^ 2)
          = (542904 * sec7_cPh) * a * S.D ^ 7 / (P.X * S.A ^ 2 * d ^ 6) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((542904 * sec7_cPh) * (11 ^ 2 * 16 ^ 7)) * d / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod1
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 542904) sec7_cPh_pos.le)
            rw [show P.X * S.A ^ 2 * d ^ 6 = P.X * (S.A ^ 2 * d ^ 6) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (sq_pos_of_pos hApos) (pow_pos hd 6)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 129 : ℝ) * d / (P.X * a) := by
            have hconst : (542904 * sec7_cPh : ℝ) * (11 ^ 2 * 16 ^ 7) ≤ 10 ^ 129 := by
              norm_num [sec7_cPh]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le
  have hterm2 :
      (3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)
        ≤ (10 ^ 129 : ℝ) * d / (P.X * a) := by
    calc
      (3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)
          = (3 * 314 * 11310 * (10 ^ 80 : ℝ)) * a ^ 2 * S.D ^ 10 /
              (P.X * S.A ^ 3 * d ^ 9) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((3 * 314 * 11310 * (10 ^ 80 : ℝ)) * (11 ^ 3 * 16 ^ 10)) *
            d / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod2
              (by positivity : 0 ≤ (3 * 314 * 11310 * (10 ^ 80 : ℝ)))
            rw [show P.X * S.A ^ 3 * d ^ 9 = P.X * (S.A ^ 3 * d ^ 9) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 3) (pow_pos hd 9)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 129 : ℝ) * d / (P.X * a) := by
            have hconst : (3 * 314 * 11310 * (10 ^ 80 : ℝ)) * (11 ^ 3 * 16 ^ 10) ≤
                10 ^ 129 := by
              norm_num
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le
  have hterm3 :
      (314 * P.X * a / d ^ 4) ^ 3 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
        ≤ (10 ^ 129 : ℝ) * d / (P.X * a) := by
    calc
      (314 * P.X * a / d ^ 4) ^ 3 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
          = (314 ^ 3 * (10 ^ 100 : ℝ)) * a ^ 3 * S.D ^ 13 /
              (P.X * S.A ^ 4 * d ^ 12) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((314 ^ 3 * (10 ^ 100 : ℝ)) * (11 ^ 4 * 16 ^ 13)) *
            d / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod3
              (by positivity : 0 ≤ (314 ^ 3 * (10 ^ 100 : ℝ)))
            rw [show P.X * S.A ^ 4 * d ^ 12 = P.X * (S.A ^ 4 * d ^ 12) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 4) (pow_pos hd 12)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 129 : ℝ) * d / (P.X * a) := by
            have hconst : (314 ^ 3 * (10 ^ 100 : ℝ)) * (11 ^ 4 * 16 ^ 13) ≤
                10 ^ 129 := by
              norm_num
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le
  calc
    (542904 * P.X * a / d ^ 6) * (sec7_cPh * S.D / S.F ^ 2) +
        (3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) +
        (314 * P.X * a / d ^ 4) ^ 3 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
        ≤ (10 ^ 129 : ℝ) * d / (P.X * a) +
          (10 ^ 129 : ℝ) * d / (P.X * a) +
          (10 ^ 129 : ℝ) * d / (P.X * a) := add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ sec7_ra_B3Scale 3 * d / (P.X * a) := by
          have hconst : (3 * (10 ^ 129) : ℝ) ≤ sec7_ra_B3Scale 3 := by
            norm_num [sec7_ra_B3Scale]
          calc
            (10 ^ 129 : ℝ) * d / (P.X * a) + 10 ^ 129 * d / (P.X * a) +
                10 ^ 129 * d / (P.X * a)
                = (3 * (10 ^ 129) : ℝ) * d / (P.X * a) := by ring
            _ ≤ sec7_ra_B3Scale 3 * d / (P.X * a) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le

private theorem sec7_ra_B3_k4_scale {P : Globals} {S : Scale P} {a d : ℝ}
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hd_lo : S.D / 16 ≤ d) :
    (32574360 * P.X * a / d ^ 7) * (sec7_cPh * S.D / S.F ^ 2) +
        ((4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) +
        (6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) +
        (314 * P.X * a / d ^ 4) ^ 4 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)
      ≤ sec7_ra_B3Scale 4 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hDle : S.D ≤ 16 * d := by linarith [hd_lo]
  have hD7 : S.D ^ 7 ≤ 16 ^ 7 * d ^ 7 := by
    have hpow : S.D ^ 7 ≤ (16 * d) ^ 7 := pow_le_pow_left₀ hDpos.le hDle 7
    calc
      S.D ^ 7 ≤ (16 * d) ^ 7 := hpow
      _ = 16 ^ 7 * d ^ 7 := by ring
  have hD10 : S.D ^ 10 ≤ 16 ^ 10 * d ^ 10 := by
    have hpow : S.D ^ 10 ≤ (16 * d) ^ 10 := pow_le_pow_left₀ hDpos.le hDle 10
    calc
      S.D ^ 10 ≤ (16 * d) ^ 10 := hpow
      _ = 16 ^ 10 * d ^ 10 := by ring
  have hD13 : S.D ^ 13 ≤ 16 ^ 13 * d ^ 13 := by
    have hpow : S.D ^ 13 ≤ (16 * d) ^ 13 := pow_le_pow_left₀ hDpos.le hDle 13
    calc
      S.D ^ 13 ≤ (16 * d) ^ 13 := hpow
      _ = 16 ^ 13 * d ^ 13 := by ring
  have hD16 : S.D ^ 16 ≤ 16 ^ 16 * d ^ 16 := by
    have hpow : S.D ^ 16 ≤ (16 * d) ^ 16 := pow_le_pow_left₀ hDpos.le hDle 16
    calc
      S.D ^ 16 ≤ (16 * d) ^ 16 := hpow
      _ = 16 ^ 16 * d ^ 16 := by ring
  have ha2 : a ^ 2 ≤ (11 * S.A) ^ 2 := pow_le_pow_left₀ ha0.le ha_hi 2
  have ha3 : a ^ 3 ≤ (11 * S.A) ^ 3 := pow_le_pow_left₀ ha0.le ha_hi 3
  have ha4 : a ^ 4 ≤ (11 * S.A) ^ 4 := pow_le_pow_left₀ ha0.le ha_hi 4
  have ha5 : a ^ 5 ≤ (11 * S.A) ^ 5 := pow_le_pow_left₀ ha0.le ha_hi 5
  have hprod1 : a ^ 2 * S.D ^ 7 ≤ (11 * S.A) ^ 2 * (16 ^ 7 * d ^ 7) :=
    mul_le_mul ha2 hD7 (by positivity) (by positivity)
  have hprod2 : a ^ 3 * S.D ^ 10 ≤ (11 * S.A) ^ 3 * (16 ^ 10 * d ^ 10) :=
    mul_le_mul ha3 hD10 (by positivity) (by positivity)
  have hprod3 : a ^ 4 * S.D ^ 13 ≤ (11 * S.A) ^ 4 * (16 ^ 13 * d ^ 13) :=
    mul_le_mul ha4 hD13 (by positivity) (by positivity)
  have hprod4 : a ^ 5 * S.D ^ 16 ≤ (11 * S.A) ^ 5 * (16 ^ 16 * d ^ 16) :=
    mul_le_mul ha5 hD16 (by positivity) (by positivity)
  have hterm1 :
      (32574360 * P.X * a / d ^ 7) * (sec7_cPh * S.D / S.F ^ 2)
        ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
    calc
      (32574360 * P.X * a / d ^ 7) * (sec7_cPh * S.D / S.F ^ 2)
          = (32574360 * sec7_cPh) * a * S.D ^ 7 / (P.X * S.A ^ 2 * d ^ 7) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((32574360 * sec7_cPh) * (11 ^ 2 * 16 ^ 7)) / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod1
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32574360) sec7_cPh_pos.le)
            rw [show P.X * S.A ^ 2 * d ^ 7 = P.X * (S.A ^ 2 * d ^ 7) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (sq_pos_of_pos hApos) (pow_pos hd 7)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
            have hconst : (32574360 * sec7_cPh : ℝ) * (11 ^ 2 * 16 ^ 7) ≤
                10 ^ 139 := by
              norm_num [sec7_cPh]
            exact div_le_div_of_nonneg_right hconst (mul_pos P.X_pos ha0).le
  have hterm2 :
      ((4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
          3 * (11310 * P.X * a / d ^ 5) ^ 2) *
        ((10 ^ 80 : ℝ) * S.D / S.F ^ 3))
        ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
    calc
      ((4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
          3 * (11310 * P.X * a / d ^ 5) ^ 2) *
        ((10 ^ 80 : ℝ) * S.D / S.F ^ 3))
          = (((4 * 314 * 542904 + 3 * 11310 ^ 2) * (10 ^ 80 : ℝ)) *
              a ^ 2 * S.D ^ 10) / (P.X * S.A ^ 3 * d ^ 10) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ (((4 * 314 * 542904 + 3 * 11310 ^ 2) * (10 ^ 80 : ℝ)) *
            (11 ^ 3 * 16 ^ 10)) / (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod2
              (by positivity :
                0 ≤ ((4 * 314 * 542904 + 3 * 11310 ^ 2) * (10 ^ 80 : ℝ)))
            rw [show P.X * S.A ^ 3 * d ^ 10 = P.X * (S.A ^ 3 * d ^ 10) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 3) (pow_pos hd 10)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
            have hconst :
                ((4 * 314 * 542904 + 3 * 11310 ^ 2) * (10 ^ 80 : ℝ)) *
                  (11 ^ 3 * 16 ^ 10) ≤ 10 ^ 139 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst (mul_pos P.X_pos ha0).le
  have hterm3 :
      (6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
        ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
    calc
      (6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
          = (6 * 314 ^ 2 * 11310 * (10 ^ 100 : ℝ)) * a ^ 3 * S.D ^ 13 /
              (P.X * S.A ^ 4 * d ^ 13) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((6 * 314 ^ 2 * 11310 * (10 ^ 100 : ℝ)) * (11 ^ 4 * 16 ^ 13)) /
            (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod3
              (by positivity : 0 ≤ (6 * 314 ^ 2 * 11310 * (10 ^ 100 : ℝ)))
            rw [show P.X * S.A ^ 4 * d ^ 13 = P.X * (S.A ^ 4 * d ^ 13) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 4) (pow_pos hd 13)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
            have hconst : (6 * 314 ^ 2 * 11310 * (10 ^ 100 : ℝ)) *
                (11 ^ 4 * 16 ^ 13) ≤ 10 ^ 139 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst (mul_pos P.X_pos ha0).le
  have hterm4 :
      (314 * P.X * a / d ^ 4) ^ 4 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)
        ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
    calc
      (314 * P.X * a / d ^ 4) ^ 4 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)
          = (314 ^ 4 * (10 ^ 100 : ℝ)) * a ^ 4 * S.D ^ 16 /
              (P.X * S.A ^ 5 * d ^ 16) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((314 ^ 4 * (10 ^ 100 : ℝ)) * (11 ^ 5 * 16 ^ 16)) /
            (P.X * a) := by
            have hmul := mul_le_mul_of_nonneg_left hprod4
              (by positivity : 0 ≤ (314 ^ 4 * (10 ^ 100 : ℝ)))
            rw [show P.X * S.A ^ 5 * d ^ 16 = P.X * (S.A ^ 5 * d ^ 16) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 5) (pow_pos hd 16)))
              (mul_pos P.X_pos ha0)]
            linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
      _ ≤ (10 ^ 139 : ℝ) / (P.X * a) := by
            have hconst : (314 ^ 4 * (10 ^ 100 : ℝ)) * (11 ^ 5 * 16 ^ 16) ≤
                10 ^ 139 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst (mul_pos P.X_pos ha0).le
  calc
    (32574360 * P.X * a / d ^ 7) * (sec7_cPh * S.D / S.F ^ 2) +
        ((4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) +
        (6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) +
        (314 * P.X * a / d ^ 4) ^ 4 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)
        ≤ (10 ^ 139 : ℝ) / (P.X * a) + (10 ^ 139 : ℝ) / (P.X * a) +
          (10 ^ 139 : ℝ) / (P.X * a) + (10 ^ 139 : ℝ) / (P.X * a) :=
            add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
    _ ≤ sec7_ra_B3Scale 4 / (P.X * a) := by
          have hconst : (4 * (10 ^ 139) : ℝ) ≤ sec7_ra_B3Scale 4 := by
            norm_num [sec7_ra_B3Scale]
          calc
            (10 ^ 139 : ℝ) / (P.X * a) + 10 ^ 139 / (P.X * a) +
                10 ^ 139 / (P.X * a) + 10 ^ 139 / (P.X * a)
                = (4 * (10 ^ 139) : ℝ) / (P.X * a) := by ring
            _ ≤ sec7_ra_B3Scale 4 / (P.X * a) :=
                div_le_div_of_nonneg_right hconst (mul_pos P.X_pos ha0).le

private theorem sec7_ra_B3_k5_scale {P : Globals} {S : Scale P} {a d : ℝ}
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hd_lo : S.D / 16 ≤ d) :
    (2345354640 * P.X * a / d ^ 8) * (sec7_cPh * S.D / S.F ^ 2) +
        ((5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
            10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) +
        (5 * (314 * P.X * a / d ^ 4) *
            (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
              3 * (11310 * P.X * a / d ^ 5) ^ 2)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) +
        (10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 5) +
        (314 * P.X * a / d ^ 4) ^ 5 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 6)
      ≤ sec7_ra_B3Scale 5 / (d * (P.X * a)) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hDle : S.D ≤ 16 * d := by linarith [hd_lo]
  have hD7 : S.D ^ 7 ≤ 16 ^ 7 * d ^ 7 := by
    have hpow : S.D ^ 7 ≤ (16 * d) ^ 7 := pow_le_pow_left₀ hDpos.le hDle 7
    calc
      S.D ^ 7 ≤ (16 * d) ^ 7 := hpow
      _ = 16 ^ 7 * d ^ 7 := by ring
  have hD10 : S.D ^ 10 ≤ 16 ^ 10 * d ^ 10 := by
    have hpow : S.D ^ 10 ≤ (16 * d) ^ 10 := pow_le_pow_left₀ hDpos.le hDle 10
    calc
      S.D ^ 10 ≤ (16 * d) ^ 10 := hpow
      _ = 16 ^ 10 * d ^ 10 := by ring
  have hD13 : S.D ^ 13 ≤ 16 ^ 13 * d ^ 13 := by
    have hpow : S.D ^ 13 ≤ (16 * d) ^ 13 := pow_le_pow_left₀ hDpos.le hDle 13
    calc
      S.D ^ 13 ≤ (16 * d) ^ 13 := hpow
      _ = 16 ^ 13 * d ^ 13 := by ring
  have hD16 : S.D ^ 16 ≤ 16 ^ 16 * d ^ 16 := by
    have hpow : S.D ^ 16 ≤ (16 * d) ^ 16 := pow_le_pow_left₀ hDpos.le hDle 16
    calc
      S.D ^ 16 ≤ (16 * d) ^ 16 := hpow
      _ = 16 ^ 16 * d ^ 16 := by ring
  have hD19 : S.D ^ 19 ≤ 16 ^ 19 * d ^ 19 := by
    have hpow : S.D ^ 19 ≤ (16 * d) ^ 19 := pow_le_pow_left₀ hDpos.le hDle 19
    calc
      S.D ^ 19 ≤ (16 * d) ^ 19 := hpow
      _ = 16 ^ 19 * d ^ 19 := by ring
  have ha2 : a ^ 2 ≤ (11 * S.A) ^ 2 := pow_le_pow_left₀ ha0.le ha_hi 2
  have ha3 : a ^ 3 ≤ (11 * S.A) ^ 3 := pow_le_pow_left₀ ha0.le ha_hi 3
  have ha4 : a ^ 4 ≤ (11 * S.A) ^ 4 := pow_le_pow_left₀ ha0.le ha_hi 4
  have ha5 : a ^ 5 ≤ (11 * S.A) ^ 5 := pow_le_pow_left₀ ha0.le ha_hi 5
  have ha6 : a ^ 6 ≤ (11 * S.A) ^ 6 := pow_le_pow_left₀ ha0.le ha_hi 6
  have hprod1 : a ^ 2 * S.D ^ 7 ≤ (11 * S.A) ^ 2 * (16 ^ 7 * d ^ 7) :=
    mul_le_mul ha2 hD7 (by positivity) (by positivity)
  have hprod2 : a ^ 3 * S.D ^ 10 ≤ (11 * S.A) ^ 3 * (16 ^ 10 * d ^ 10) :=
    mul_le_mul ha3 hD10 (by positivity) (by positivity)
  have hprod3 : a ^ 4 * S.D ^ 13 ≤ (11 * S.A) ^ 4 * (16 ^ 13 * d ^ 13) :=
    mul_le_mul ha4 hD13 (by positivity) (by positivity)
  have hprod4 : a ^ 5 * S.D ^ 16 ≤ (11 * S.A) ^ 5 * (16 ^ 16 * d ^ 16) :=
    mul_le_mul ha5 hD16 (by positivity) (by positivity)
  have hprod5 : a ^ 6 * S.D ^ 19 ≤ (11 * S.A) ^ 6 * (16 ^ 19 * d ^ 19) :=
    mul_le_mul ha6 hD19 (by positivity) (by positivity)
  have htarget_pos : 0 < d * (P.X * a) := mul_pos hd (mul_pos P.X_pos ha0)
  have hterm1 :
      (2345354640 * P.X * a / d ^ 8) * (sec7_cPh * S.D / S.F ^ 2)
        ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
    calc
      (2345354640 * P.X * a / d ^ 8) * (sec7_cPh * S.D / S.F ^ 2)
          = (2345354640 * sec7_cPh) * a * S.D ^ 7 /
              (P.X * S.A ^ 2 * d ^ 8) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((2345354640 * sec7_cPh) * (11 ^ 2 * 16 ^ 7)) /
            (d * (P.X * a)) := by
            have hmul := mul_le_mul_of_nonneg_left hprod1
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2345354640) sec7_cPh_pos.le)
            rw [show P.X * S.A ^ 2 * d ^ 8 = P.X * (S.A ^ 2 * d ^ 8) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (sq_pos_of_pos hApos) (pow_pos hd 8)))
              htarget_pos]
            linarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg P.X_pos.le hd.le)]
      _ ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
            have hconst : (2345354640 * sec7_cPh : ℝ) * (11 ^ 2 * 16 ^ 7) ≤
                10 ^ 142 := by
              norm_num [sec7_cPh]
            exact div_le_div_of_nonneg_right hconst htarget_pos.le
  have hterm2 :
      ((5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
          10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6)) *
        ((10 ^ 80 : ℝ) * S.D / S.F ^ 3))
        ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
    calc
      ((5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
          10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6)) *
        ((10 ^ 80 : ℝ) * S.D / S.F ^ 3))
          = (((5 * 314 * 32574360 + 10 * 11310 * 542904) * (10 ^ 80 : ℝ)) *
              a ^ 2 * S.D ^ 10) / (P.X * S.A ^ 3 * d ^ 11) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ (((5 * 314 * 32574360 + 10 * 11310 * 542904) * (10 ^ 80 : ℝ)) *
            (11 ^ 3 * 16 ^ 10)) / (d * (P.X * a)) := by
            have hmul := mul_le_mul_of_nonneg_left hprod2
              (by positivity :
                0 ≤ ((5 * 314 * 32574360 + 10 * 11310 * 542904) *
                  (10 ^ 80 : ℝ)))
            rw [show P.X * S.A ^ 3 * d ^ 11 = P.X * (S.A ^ 3 * d ^ 11) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 3) (pow_pos hd 11)))
              htarget_pos]
            linarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg P.X_pos.le hd.le)]
      _ ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
            have hconst :
                ((5 * 314 * 32574360 + 10 * 11310 * 542904) * (10 ^ 80 : ℝ)) *
                  (11 ^ 3 * 16 ^ 10) ≤ 10 ^ 142 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst htarget_pos.le
  have hterm3 :
      (5 * (314 * P.X * a / d ^ 4) *
          (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2)) *
        ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
        ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
    calc
      (5 * (314 * P.X * a / d ^ 4) *
          (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2)) *
        ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)
          = (5 * 314 * (2 * 314 * 542904 + 3 * 11310 ^ 2) *
              (10 ^ 100 : ℝ)) * a ^ 3 * S.D ^ 13 /
              (P.X * S.A ^ 4 * d ^ 14) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((5 * 314 * (2 * 314 * 542904 + 3 * 11310 ^ 2) *
              (10 ^ 100 : ℝ)) * (11 ^ 4 * 16 ^ 13)) /
            (d * (P.X * a)) := by
            have hmul := mul_le_mul_of_nonneg_left hprod3
              (by positivity :
                0 ≤ (5 * 314 * (2 * 314 * 542904 + 3 * 11310 ^ 2) *
                  (10 ^ 100 : ℝ)))
            rw [show P.X * S.A ^ 4 * d ^ 14 = P.X * (S.A ^ 4 * d ^ 14) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 4) (pow_pos hd 14)))
              htarget_pos]
            linarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg P.X_pos.le hd.le)]
      _ ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
            have hconst :
                (5 * 314 * (2 * 314 * 542904 + 3 * 11310 ^ 2) *
                    (10 ^ 100 : ℝ)) * (11 ^ 4 * 16 ^ 13) ≤ 10 ^ 142 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst htarget_pos.le
  have hterm4 :
      (10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)
        ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
    calc
      (10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)
          = (10 * 314 ^ 3 * 11310 * (10 ^ 100 : ℝ)) * a ^ 4 * S.D ^ 16 /
              (P.X * S.A ^ 5 * d ^ 17) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((10 * 314 ^ 3 * 11310 * (10 ^ 100 : ℝ)) * (11 ^ 5 * 16 ^ 16)) /
            (d * (P.X * a)) := by
            have hmul := mul_le_mul_of_nonneg_left hprod4
              (by positivity : 0 ≤ (10 * 314 ^ 3 * 11310 * (10 ^ 100 : ℝ)))
            rw [show P.X * S.A ^ 5 * d ^ 17 = P.X * (S.A ^ 5 * d ^ 17) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 5) (pow_pos hd 17)))
              htarget_pos]
            linarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg P.X_pos.le hd.le)]
      _ ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
            have hconst : (10 * 314 ^ 3 * 11310 * (10 ^ 100 : ℝ)) *
                (11 ^ 5 * 16 ^ 16) ≤ 10 ^ 142 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst htarget_pos.le
  have hterm5 :
      (314 * P.X * a / d ^ 4) ^ 5 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 6)
        ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
    calc
      (314 * P.X * a / d ^ 4) ^ 5 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 6)
          = (314 ^ 5 * (10 ^ 100 : ℝ)) * a ^ 5 * S.D ^ 19 /
              (P.X * S.A ^ 6 * d ^ 20) := by
            rw [← sec7_ra_XA_div_D3_eq_F S]
            field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
      _ ≤ ((314 ^ 5 * (10 ^ 100 : ℝ)) * (11 ^ 6 * 16 ^ 19)) /
            (d * (P.X * a)) := by
            have hmul := mul_le_mul_of_nonneg_left hprod5
              (by positivity : 0 ≤ (314 ^ 5 * (10 ^ 100 : ℝ)))
            rw [show P.X * S.A ^ 6 * d ^ 20 = P.X * (S.A ^ 6 * d ^ 20) by ring]
            rw [div_le_div_iff₀
              (mul_pos P.X_pos (mul_pos (pow_pos hApos 6) (pow_pos hd 20)))
              htarget_pos]
            linarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg P.X_pos.le hd.le)]
      _ ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) := by
            have hconst : (314 ^ 5 * (10 ^ 100 : ℝ)) * (11 ^ 6 * 16 ^ 19) ≤
                10 ^ 142 := by
              norm_num
            exact div_le_div_of_nonneg_right hconst htarget_pos.le
  calc
    (2345354640 * P.X * a / d ^ 8) * (sec7_cPh * S.D / S.F ^ 2) +
        ((5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
            10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) +
        (5 * (314 * P.X * a / d ^ 4) *
            (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
              3 * (11310 * P.X * a / d ^ 5) ^ 2)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) +
        (10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 5) +
        (314 * P.X * a / d ^ 4) ^ 5 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 6)
        ≤ (10 ^ 142 : ℝ) / (d * (P.X * a)) +
          (10 ^ 142 : ℝ) / (d * (P.X * a)) +
          (10 ^ 142 : ℝ) / (d * (P.X * a)) +
          (10 ^ 142 : ℝ) / (d * (P.X * a)) +
          (10 ^ 142 : ℝ) / (d * (P.X * a)) :=
            add_le_add (add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4)
              hterm5
    _ ≤ sec7_ra_B3Scale 5 / (d * (P.X * a)) := by
          have hconst : (5 * (10 ^ 142) : ℝ) ≤ sec7_ra_B3Scale 5 := by
            norm_num [sec7_ra_B3Scale]
          calc
            (10 ^ 142 : ℝ) / (d * (P.X * a)) + 10 ^ 142 / (d * (P.X * a)) +
                10 ^ 142 / (d * (P.X * a)) + 10 ^ 142 / (d * (P.X * a)) +
                10 ^ 142 / (d * (P.X * a))
                = (5 * (10 ^ 142) : ℝ) / (d * (P.X * a)) := by ring
            _ ≤ sec7_ra_B3Scale 5 / (d * (P.X * a)) :=
                div_le_div_of_nonneg_right hconst htarget_pos.le

private theorem sec7_ra_B3_k1_scale {P : Globals} {S : Scale P} {a d : ℝ}
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) (hd : 0 < d)
    (hd_lo : S.D / 16 ≤ d) :
    (314 * P.X * a / d ^ 4) * (sec7_cPh * S.D / S.F ^ 2)
      ≤ sec7_ra_B3Scale 1 * d ^ 3 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hDpos : 0 < S.D := S.D_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hDle : S.D ≤ 16 * d := by linarith [hd_lo]
  have hD7 : S.D ^ 7 ≤ (16 * d) ^ 7 := pow_le_pow_left₀ hDpos.le hDle 7
  have hD7' : S.D ^ 7 ≤ 16 ^ 7 * d ^ 7 := by
    calc
      S.D ^ 7 ≤ (16 * d) ^ 7 := hD7
      _ = 16 ^ 7 * d ^ 7 := by ring
  have ha2 : a ^ 2 ≤ (11 * S.A) ^ 2 := pow_le_pow_left₀ ha0.le ha_hi 2
  have hprod : a ^ 2 * S.D ^ 7 ≤ (11 * S.A) ^ 2 * (16 ^ 7 * d ^ 7) :=
    mul_le_mul ha2 hD7' (by positivity) (by positivity)
  have hconst : (314 * sec7_cPh : ℝ) * (11 ^ 2 * 16 ^ 7) ≤ sec7_ra_B3Scale 1 := by
    norm_num [sec7_cPh, sec7_ra_B3Scale]
  calc
    (314 * P.X * a / d ^ 4) * (sec7_cPh * S.D / S.F ^ 2)
        = (314 * sec7_cPh) * a * S.D ^ 7 / (P.X * S.A ^ 2 * d ^ 4) := by
          rw [← sec7_ra_XA_div_D3_eq_F S]
          field_simp [P.X_pos.ne', hApos.ne', ha0.ne', hd.ne', hDpos.ne']
    _ ≤ ((314 * sec7_cPh) * (11 ^ 2 * 16 ^ 7)) * d ^ 3 / (P.X * a) := by
          have hmul := mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 314) sec7_cPh_pos.le)
          rw [show P.X * S.A ^ 2 * d ^ 4 = P.X * (S.A ^ 2 * d ^ 4) by ring]
          rw [div_le_div_iff₀
            (mul_pos P.X_pos (mul_pos (sq_pos_of_pos hApos) (pow_pos hd 4)))
            (mul_pos P.X_pos ha0)]
          linarith [mul_le_mul_of_nonneg_left hmul P.X_pos.le]
    _ ≤ sec7_ra_B3Scale 1 * d ^ 3 / (P.X * a) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hconst (by positivity)) (mul_pos P.X_pos ha0).le

private theorem sec7_ra_B3_bound_k1 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hd_lo : S.D / 16 ≤ d) (had : a ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3Scale 1 * |j| * d ^ 3 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hshift : Ffun P.X a d + j ∈ sec7_tWin S := hseg j Set.right_mem_uIcc
  have hev :
      (fun t => dBreve P.X a (Ffun P.X a t + j) - t)
        =ᶠ[nhds d] sec7_ra_B3H P.X a j 0 := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    have hspec : dBreve P.X a (Ffun P.X a t) = t := dBreve_spec P.X_pos ha0 ht
    simp [sec7_ra_B3H, sec7_ra_dBreveD, hspec]
  have hiter :
      iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        deriv (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d := by
    calc
      iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d
          = iteratedDeriv 1 (sec7_ra_B3H P.X a j 0) d := by
            exact Filter.EventuallyEq.iteratedDeriv_eq 1 hev
      _ = deriv (sec7_ra_B3H P.X a j 0) d := by rw [iteratedDeriv_one]
      _ = deriv (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d := by
            exact (sec7_ra_B3H_hasDerivAt (P := P) (S := S) (a := a) (d := d)
              (j := j) (l := 0) (by norm_num) hAD ha_lo ha_hi hd hshift).deriv
  have hH1 : |sec7_ra_B3H P.X a j 1 d| ≤
      (sec7_cPh * S.D / S.F ^ 2) * |j| := by
    refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_cPh * S.D / S.F ^ 2) (l := 1) (by norm_num)
      hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    have hscale :=
      (dBreve_sec7_tWin_scale (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin).2.2
    have hscale' : S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d + s)| ≤ sec7_cPh * S.D := by
      have hDcomm : S.Δ * P.H = S.D := by
        rw [mul_comm]
        rfl
      simpa [hDcomm, mul_assoc, mul_left_comm, mul_comm] using hscale
    rw [sec7_ra_dBreveD]
    rw [le_div_iff₀ (pow_pos hFpos 2)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  obtain ⟨_hFlo, hFhi⟩ :=
    Ffun_deriv1_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had])
  have hscale := sec7_ra_B3_k1_scale (P := P) (S := S) (a := a) (d := d)
    ha_lo ha_hi hd hd_lo
  calc
    |iteratedDeriv 1 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |deriv (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d| := by rw [hiter]
    _ = |deriv (fun t => Ffun P.X a t) d| * |sec7_ra_B3H P.X a j 1 d| := by rw [abs_mul]
    _ ≤ (314 * P.X * a / d ^ 4) * ((sec7_cPh * S.D / S.F ^ 2) * |j|) := by
          exact mul_le_mul hFhi hH1
            (abs_nonneg _)
            (div_nonneg
              (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 314) P.X_pos.le) ha0.le)
              (pow_nonneg hd.le 4))
    _ = ((314 * P.X * a / d ^ 4) * (sec7_cPh * S.D / S.F ^ 2)) * |j| := by ring
    _ ≤ (sec7_ra_B3Scale 1 * d ^ 3 / (P.X * a)) * |j| :=
          mul_le_mul_of_nonneg_right hscale (abs_nonneg j)
    _ = sec7_ra_B3Scale 1 * |j| * d ^ 3 / (P.X * a) := by ring

private theorem sec7_ra_B3_bound_k2 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hd_lo : S.D / 16 ≤ d) (had : a ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3Scale 2 * |j| * d ^ 2 / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have hFpos : 0 < S.F := by
    have hH := P.H_pos
    have hG := P.G_pos
    have hΔ := S.Δ_pos
    have hΩ := S.Ω_pos
    unfold Scale.F
    positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hshift : Ffun P.X a d + j ∈ sec7_tWin S := hseg j Set.right_mem_uIcc
  have hiter := sec7_ra_B3_iteratedDeriv2_eq (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd hshift
  have hH1 : |sec7_ra_B3H P.X a j 1 d| ≤
      (sec7_cPh * S.D / S.F ^ 2) * |j| := by
    refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := sec7_cPh * S.D / S.F ^ 2) (l := 1) (by norm_num)
      hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    have hscale :=
      (dBreve_sec7_tWin_scale (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin).2.2
    have hscale' : S.F ^ 2 * |dBreve'' P.X a (Ffun P.X a d + s)| ≤ sec7_cPh * S.D := by
      have hDcomm : S.Δ * P.H = S.D := by
        rw [mul_comm]
        rfl
      simpa [hDcomm, mul_assoc, mul_left_comm, mul_comm] using hscale
    rw [sec7_ra_dBreveD]
    rw [le_div_iff₀ (pow_pos hFpos 2)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  have hH2 : |sec7_ra_B3H P.X a j 2 d| ≤
      ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j| := by
    refine sec7_ra_B3H_mvt_bound (P := P) (S := S) (a := a) (d := d)
      (j := j) (C := (10 ^ 80 : ℝ) * S.D / S.F ^ 3) (l := 2) (by norm_num)
      hAD ha_lo ha_hi hseg ?_
    intro s hs
    have htWin : Ffun P.X a d + s ∈ sec7_tWin S := hseg s hs
    obtain ⟨himg, hlo, hhi⟩ :=
      dBreve_sec7_tWin_image (P := P) (S := S) (a := a)
        (t := Ffun P.X a d + s) hAD ha_lo ha_hi htWin
    have hscale :=
      (dBreve_deriv3_scale_sec7_image (P := P) (S := S) (a := a)
        (d := dBreve P.X a (Ffun P.X a d + s)) hAD ha_lo ha_hi hlo hhi).2
    have hscale' :
        S.F ^ 3 * |dBreve''' P.X a (Ffun P.X a d + s)| ≤
          (10 ^ 80 : ℝ) * S.D := by
      simpa [himg, show P.H * S.Δ = S.D by rfl, mul_assoc, mul_left_comm, mul_comm]
        using hscale
    rw [sec7_ra_dBreveD]
    rw [le_div_iff₀ (pow_pos hFpos 3)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale'
  obtain ⟨_hF1lo, hF1hi⟩ :=
    Ffun_deriv1_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had])
  obtain ⟨_hF2lo, hF2hi⟩ :=
    Ffun_deriv2_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had])
  have hF1ub_nonneg : 0 ≤ 314 * P.X * a / d ^ 4 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 314) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 11310 * P.X * a / d ^ 5 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 11310) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF1sq : |deriv (fun t => Ffun P.X a t) d| ^ 2 ≤
      (314 * P.X * a / d ^ 4) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hF1ub_nonneg).2 hF1hi
  have hscale := sec7_ra_B3_k2_scale (P := P) (S := S) (a := a) (d := d)
    ha_lo ha_hi hd hd_lo
  calc
    |iteratedDeriv 2 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d +
            deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d| := by
          rw [hiter]
    _ ≤ |iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 1 d| +
        |deriv (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 2 d| := abs_add_le _ _
    _ = |iteratedDeriv 2 (fun t => Ffun P.X a t) d| * |sec7_ra_B3H P.X a j 1 d| +
        |deriv (fun t => Ffun P.X a t) d| ^ 2 * |sec7_ra_B3H P.X a j 2 d| := by
          rw [abs_mul, abs_mul, abs_pow]
    _ ≤ (11310 * P.X * a / d ^ 5) * ((sec7_cPh * S.D / S.F ^ 2) * |j|) +
        (314 * P.X * a / d ^ 4) ^ 2 * (((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j|) := by
          exact add_le_add
            (mul_le_mul hF2hi hH1 (abs_nonneg _) hF2ub_nonneg)
            (mul_le_mul
              hF1sq hH2 (abs_nonneg _) (sq_nonneg _))
    _ = ((11310 * P.X * a / d ^ 5) * (sec7_cPh * S.D / S.F ^ 2) +
        (314 * P.X * a / d ^ 4) ^ 2 * ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) * |j| := by ring
    _ ≤ (sec7_ra_B3Scale 2 * d ^ 2 / (P.X * a)) * |j| :=
          mul_le_mul_of_nonneg_right hscale (abs_nonneg j)
    _ = sec7_ra_B3Scale 2 * |j| * d ^ 2 / (P.X * a) := by ring

private theorem sec7_ra_B3_bound_k3 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hd_lo : S.D / 16 ≤ d) (had : a ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3Scale 3 * |j| * d / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hshift : Ffun P.X a d + j ∈ sec7_tWin S := hseg j Set.right_mem_uIcc
  have hiter :
      iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        iteratedDeriv 3 (fun t => Ffun P.X a t) d *
            sec7_ra_B3H P.X a j 1 d +
          3 * deriv (fun t => Ffun P.X a t) d *
              iteratedDeriv 2 (fun t => Ffun P.X a t) d *
              sec7_ra_B3H P.X a j 2 d +
          deriv (fun t => Ffun P.X a t) d ^ 3 *
              sec7_ra_B3H P.X a j 3 d := by
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 3) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [sec7_ra_B3E] using h
  have hH1 : |sec7_ra_B3H P.X a j 1 d| ≤
      (sec7_cPh * S.D / S.F ^ 2) * |j| := by
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 1) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH2 : |sec7_ra_B3H P.X a j 2 d| ≤
      ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j| := by
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 2) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH3 : |sec7_ra_B3H P.X a j 3 d| ≤
      ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) * |j| := by
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 3) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  obtain ⟨_hF1lo, hF1hi⟩ :=
    Ffun_deriv1_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF2lo, hF2hi⟩ :=
    Ffun_deriv2_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF3lo, hF3hi⟩ :=
    Ffun_deriv3_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  have hF1ub_nonneg : 0 ≤ 314 * P.X * a / d ^ 4 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 314) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 11310 * P.X * a / d ^ 5 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 11310) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 542904 * P.X * a / d ^ 6 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 542904) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF1F2 :
      |deriv (fun t => Ffun P.X a t) d| *
          |iteratedDeriv 2 (fun t => Ffun P.X a t) d| ≤
        (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5) :=
    mul_le_mul hF1hi hF2hi (abs_nonneg _) hF1ub_nonneg
  have hcoef2 :
      3 * |deriv (fun t => Ffun P.X a t) d| *
          |iteratedDeriv 2 (fun t => Ffun P.X a t) d| ≤
        3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5) := by
    have h := mul_le_mul_of_nonneg_left hF1F2 (by norm_num : (0 : ℝ) ≤ 3)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hF1cube :
      |deriv (fun t => Ffun P.X a t) d| ^ 3 ≤
        (314 * P.X * a / d ^ 4) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1hi 3
  have hscale := sec7_ra_B3_k3_scale (P := P) (S := S) (a := a) (d := d)
    ha_lo ha_hi hd hd_lo
  calc
    |iteratedDeriv 3 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |iteratedDeriv 3 (fun t => Ffun P.X a t) d *
              sec7_ra_B3H P.X a j 1 d +
            3 * deriv (fun t => Ffun P.X a t) d *
                iteratedDeriv 2 (fun t => Ffun P.X a t) d *
                sec7_ra_B3H P.X a j 2 d +
            deriv (fun t => Ffun P.X a t) d ^ 3 *
                sec7_ra_B3H P.X a j 3 d| := by
          rw [hiter]
    _ ≤ |iteratedDeriv 3 (fun t => Ffun P.X a t) d *
            sec7_ra_B3H P.X a j 1 d| +
        |3 * deriv (fun t => Ffun P.X a t) d *
            iteratedDeriv 2 (fun t => Ffun P.X a t) d *
            sec7_ra_B3H P.X a j 2 d| +
        |deriv (fun t => Ffun P.X a t) d ^ 3 *
            sec7_ra_B3H P.X a j 3 d| := by
          calc
            |iteratedDeriv 3 (fun t => Ffun P.X a t) d *
                  sec7_ra_B3H P.X a j 1 d +
                3 * deriv (fun t => Ffun P.X a t) d *
                    iteratedDeriv 2 (fun t => Ffun P.X a t) d *
                    sec7_ra_B3H P.X a j 2 d +
                deriv (fun t => Ffun P.X a t) d ^ 3 *
                    sec7_ra_B3H P.X a j 3 d|
                ≤ |iteratedDeriv 3 (fun t => Ffun P.X a t) d *
                    sec7_ra_B3H P.X a j 1 d +
                  3 * deriv (fun t => Ffun P.X a t) d *
                      iteratedDeriv 2 (fun t => Ffun P.X a t) d *
                      sec7_ra_B3H P.X a j 2 d| +
                    |deriv (fun t => Ffun P.X a t) d ^ 3 *
                      sec7_ra_B3H P.X a j 3 d| := abs_add_le _ _
            _ ≤ (|iteratedDeriv 3 (fun t => Ffun P.X a t) d *
                    sec7_ra_B3H P.X a j 1 d| +
                  |3 * deriv (fun t => Ffun P.X a t) d *
                    iteratedDeriv 2 (fun t => Ffun P.X a t) d *
                    sec7_ra_B3H P.X a j 2 d|) +
                    |deriv (fun t => Ffun P.X a t) d ^ 3 *
                      sec7_ra_B3H P.X a j 3 d| :=
                  by
                    have h := abs_add_le
                      (iteratedDeriv 3 (fun t => Ffun P.X a t) d *
                        sec7_ra_B3H P.X a j 1 d)
                      (3 * deriv (fun t => Ffun P.X a t) d *
                        iteratedDeriv 2 (fun t => Ffun P.X a t) d *
                        sec7_ra_B3H P.X a j 2 d)
                    linarith
            _ = |iteratedDeriv 3 (fun t => Ffun P.X a t) d *
                    sec7_ra_B3H P.X a j 1 d| +
                  |3 * deriv (fun t => Ffun P.X a t) d *
                    iteratedDeriv 2 (fun t => Ffun P.X a t) d *
                    sec7_ra_B3H P.X a j 2 d| +
                  |deriv (fun t => Ffun P.X a t) d ^ 3 *
                    sec7_ra_B3H P.X a j 3 d| := by ring
    _ = |iteratedDeriv 3 (fun t => Ffun P.X a t) d| *
          |sec7_ra_B3H P.X a j 1 d| +
        (3 * |deriv (fun t => Ffun P.X a t) d| *
            |iteratedDeriv 2 (fun t => Ffun P.X a t) d|) *
          |sec7_ra_B3H P.X a j 2 d| +
        |deriv (fun t => Ffun P.X a t) d| ^ 3 *
          |sec7_ra_B3H P.X a j 3 d| := by
          simp [abs_mul, abs_pow]
    _ ≤ (542904 * P.X * a / d ^ 6) * ((sec7_cPh * S.D / S.F ^ 2) * |j|) +
        (3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5)) *
          (((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j|) +
        (314 * P.X * a / d ^ 4) ^ 3 *
          (((10 ^ 100 : ℝ) * S.D / S.F ^ 4) * |j|) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul hF3hi hH1 (abs_nonneg _) hF3ub_nonneg)
              (mul_le_mul hcoef2 hH2 (abs_nonneg _)
                (by positivity : 0 ≤ 3 * (314 * P.X * a / d ^ 4) *
                  (11310 * P.X * a / d ^ 5))))
            (mul_le_mul hF1cube hH3 (abs_nonneg _)
              (pow_nonneg hF1ub_nonneg 3))
    _ = ((542904 * P.X * a / d ^ 6) * (sec7_cPh * S.D / S.F ^ 2) +
        (3 * (314 * P.X * a / d ^ 4) * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) +
        (314 * P.X * a / d ^ 4) ^ 3 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 4)) * |j| := by
          ring
    _ ≤ (sec7_ra_B3Scale 3 * d / (P.X * a)) * |j| :=
          mul_le_mul_of_nonneg_right hscale (abs_nonneg j)
    _ = sec7_ra_B3Scale 3 * |j| * d / (P.X * a) := by ring

private theorem sec7_ra_B3_bound_k4 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hd_lo : S.D / 16 ≤ d) (had : a ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3Scale 4 * |j| / (P.X * a) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hshift : Ffun P.X a d + j ∈ sec7_tWin S := hseg j Set.right_mem_uIcc
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  have hiter :
      iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
          6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4 := by
    dsimp [F1, F2, F3, F4, H1, H2, H3, H4]
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 4) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [sec7_ra_B3E] using h
  have hH1 : |H1| ≤ (sec7_cPh * S.D / S.F ^ 2) * |j| := by
    dsimp [H1]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 1) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH2 : |H2| ≤ ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j| := by
    dsimp [H2]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 2) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH3 : |H3| ≤ ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) * |j| := by
    dsimp [H3]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 3) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH4 : |H4| ≤ ((10 ^ 100 : ℝ) * S.D / S.F ^ 5) * |j| := by
    dsimp [H4]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 4) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  obtain ⟨_hF1lo, hF1hi_raw⟩ :=
    Ffun_deriv1_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF2lo, hF2hi_raw⟩ :=
    Ffun_deriv2_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF3lo, hF3hi_raw⟩ :=
    Ffun_deriv3_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF4lo, hF4hi_raw⟩ :=
    Ffun_deriv4_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  have hF1hi : |F1| ≤ 314 * P.X * a / d ^ 4 := by simpa [F1] using hF1hi_raw
  have hF2hi : |F2| ≤ 11310 * P.X * a / d ^ 5 := by simpa [F2] using hF2hi_raw
  have hF3hi : |F3| ≤ 542904 * P.X * a / d ^ 6 := by simpa [F3] using hF3hi_raw
  have hF4hi : |F4| ≤ 32574360 * P.X * a / d ^ 7 := by simpa [F4] using hF4hi_raw
  have hF1ub_nonneg : 0 ≤ 314 * P.X * a / d ^ 4 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 314) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 11310 * P.X * a / d ^ 5 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 11310) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 542904 * P.X * a / d ^ 6 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 542904) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF4ub_nonneg : 0 ≤ 32574360 * P.X * a / d ^ 7 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32574360) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 7)
  have hF1F3 : |F1| * |F3| ≤
      (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) :=
    mul_le_mul hF1hi hF3hi (abs_nonneg _) hF1ub_nonneg
  have hF2sq : |F2| ^ 2 ≤ (11310 * P.X * a / d ^ 5) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF2hi 2
  have hcoef2_abs : |4 * F1 * F3 + 3 * F2 ^ 2| ≤
      4 * |F1| * |F3| + 3 * |F2| ^ 2 := by
    calc
      |4 * F1 * F3 + 3 * F2 ^ 2| ≤ |4 * F1 * F3| + |3 * F2 ^ 2| :=
        abs_add_le _ _
      _ = 4 * |F1| * |F3| + 3 * |F2| ^ 2 := by
        simp [abs_mul, abs_pow]
  have hcoef2 :
      4 * |F1| * |F3| + 3 * |F2| ^ 2 ≤
        4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
          3 * (11310 * P.X * a / d ^ 5) ^ 2 := by
    have h2a := mul_le_mul_of_nonneg_left hF1F3 (by norm_num : (0 : ℝ) ≤ 4)
    have h2b := mul_le_mul_of_nonneg_left hF2sq (by norm_num : (0 : ℝ) ≤ 3)
    exact add_le_add
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2a)
      h2b
  have hF1sqF2 : |F1| ^ 2 * |F2| ≤
      (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5) :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hF1hi 2) hF2hi
      (abs_nonneg _) (pow_nonneg hF1ub_nonneg 2)
  have hcoef3 :
      6 * |F1| ^ 2 * |F2| ≤
        6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5) := by
    have h := mul_le_mul_of_nonneg_left hF1sqF2 (by norm_num : (0 : ℝ) ≤ 6)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hF1four : |F1| ^ 4 ≤ (314 * P.X * a / d ^ 4) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1hi 4
  have htri :
      |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
          6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4| ≤
        |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
          |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := by
    calc
      |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
          6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4|
          ≤ |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
              6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := abs_add_le _ _
      _ ≤ (|F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
            |6 * F1 ^ 2 * F2 * H3|) + |F1 ^ 4 * H4| := by
            have h := abs_add_le (F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2)
              (6 * F1 ^ 2 * F2 * H3)
            linarith
      _ ≤ ((|F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2|) +
            |6 * F1 ^ 2 * F2 * H3|) + |F1 ^ 4 * H4| := by
            have h := abs_add_le (F4 * H1) ((4 * F1 * F3 + 3 * F2 ^ 2) * H2)
            linarith
      _ = |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
          |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := by ring
  have hterm2_abs : |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| ≤
      (4 * |F1| * |F3| + 3 * |F2| ^ 2) * |H2| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hcoef2_abs (abs_nonneg H2)
  have hterm3_abs : |6 * F1 ^ 2 * F2 * H3| =
      (6 * |F1| ^ 2 * |F2|) * |H3| := by
    simp [abs_mul, abs_pow]
  have hterm1_abs : |F4 * H1| = |F4| * |H1| := by
    rw [abs_mul]
  have hterm4_abs : |F1 ^ 4 * H4| = |F1| ^ 4 * |H4| := by
    simp [abs_mul, abs_pow]
  have hscale := sec7_ra_B3_k4_scale (P := P) (S := S) (a := a) (d := d)
    ha_lo ha_hi hd hd_lo
  calc
    |iteratedDeriv 4 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
            6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4| := by rw [hiter]
    _ ≤ |F4| * |H1| + (4 * |F1| * |F3| + 3 * |F2| ^ 2) * |H2| +
        (6 * |F1| ^ 2 * |F2|) * |H3| + |F1| ^ 4 * |H4| := by
          calc
            |F4 * H1 + (4 * F1 * F3 + 3 * F2 ^ 2) * H2 +
                6 * F1 ^ 2 * F2 * H3 + F1 ^ 4 * H4|
                ≤ |F4 * H1| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H2| +
                  |6 * F1 ^ 2 * F2 * H3| + |F1 ^ 4 * H4| := htri
            _ ≤ |F4| * |H1| + (4 * |F1| * |F3| + 3 * |F2| ^ 2) * |H2| +
                  (6 * |F1| ^ 2 * |F2|) * |H3| + |F1| ^ 4 * |H4| := by
                  rw [hterm1_abs, hterm3_abs, hterm4_abs]
                  exact add_le_add
                    (add_le_add (add_le_add le_rfl hterm2_abs) le_rfl)
                    le_rfl
    _ ≤ (32574360 * P.X * a / d ^ 7) * ((sec7_cPh * S.D / S.F ^ 2) * |j|) +
        (4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2) *
          (((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j|) +
        (6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5)) *
          (((10 ^ 100 : ℝ) * S.D / S.F ^ 4) * |j|) +
        (314 * P.X * a / d ^ 4) ^ 4 *
          (((10 ^ 100 : ℝ) * S.D / S.F ^ 5) * |j|) := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (mul_le_mul hF4hi hH1 (abs_nonneg _) hF4ub_nonneg)
                (mul_le_mul hcoef2 hH2 (abs_nonneg _)
                  (by positivity :
                    0 ≤ 4 * (314 * P.X * a / d ^ 4) *
                        (542904 * P.X * a / d ^ 6) +
                      3 * (11310 * P.X * a / d ^ 5) ^ 2)))
              (mul_le_mul hcoef3 hH3 (abs_nonneg _)
                (by positivity :
                  0 ≤ 6 * (314 * P.X * a / d ^ 4) ^ 2 *
                    (11310 * P.X * a / d ^ 5))))
            (mul_le_mul hF1four hH4 (abs_nonneg _)
              (pow_nonneg hF1ub_nonneg 4))
    _ = ((32574360 * P.X * a / d ^ 7) * (sec7_cPh * S.D / S.F ^ 2) +
        ((4 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) +
        (6 * (314 * P.X * a / d ^ 4) ^ 2 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) +
        (314 * P.X * a / d ^ 4) ^ 4 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 5)) * |j| := by
          ring
    _ ≤ (sec7_ra_B3Scale 4 / (P.X * a)) * |j| :=
          mul_le_mul_of_nonneg_right hscale (abs_nonneg j)
    _ = sec7_ra_B3Scale 4 * |j| / (P.X * a) := by ring

private theorem sec7_ra_B3_bound_k5 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hd_lo : S.D / 16 ≤ d) (had : a ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
      ≤ sec7_ra_B3Scale 5 * |j| / (d * (P.X * a)) := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hshift : Ffun P.X a d + j ∈ sec7_tWin S := hseg j Set.right_mem_uIcc
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let F5 : ℝ := iteratedDeriv 5 (fun t => Ffun P.X a t) d
  let H1 : ℝ := sec7_ra_B3H P.X a j 1 d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  let H5 : ℝ := sec7_ra_B3H P.X a j 5 d
  have hiter :
      iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d =
        F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
          5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
          10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5 := by
    dsimp [F1, F2, F3, F4, F5, H1, H2, H3, H4, H5]
    have h := sec7_ra_B3_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 5) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [sec7_ra_B3E] using h
  have hH1 : |H1| ≤ (sec7_cPh * S.D / S.F ^ 2) * |j| := by
    dsimp [H1]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 1) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH2 : |H2| ≤ ((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j| := by
    dsimp [H2]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 2) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH3 : |H3| ≤ ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) * |j| := by
    dsimp [H3]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 3) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH4 : |H4| ≤ ((10 ^ 100 : ℝ) * S.D / S.F ^ 5) * |j| := by
    dsimp [H4]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 4) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  have hH5 : |H5| ≤ ((10 ^ 100 : ℝ) * S.D / S.F ^ 6) * |j| := by
    dsimp [H5]
    simpa [sec7_ra_B3HScale] using
      (sec7_ra_B3H_bound (P := P) (S := S) (a := a) (d := d) (j := j)
        (l := 5) hAD ha_lo ha_hi hseg (by norm_num) (by norm_num))
  obtain ⟨_hF1lo, hF1hi_raw⟩ :=
    Ffun_deriv1_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF2lo, hF2hi_raw⟩ :=
    Ffun_deriv2_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF3lo, hF3hi_raw⟩ :=
    Ffun_deriv3_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF4lo, hF4hi_raw⟩ :=
    Ffun_deriv4_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  obtain ⟨_hF5lo, hF5hi_raw⟩ :=
    Ffun_deriv5_abs_bounds (X := P.X) (a := a) (d := d) P.X_pos ha0 hd
      (by nlinarith [had, hd])
  have hF1hi : |F1| ≤ 314 * P.X * a / d ^ 4 := by simpa [F1] using hF1hi_raw
  have hF2hi : |F2| ≤ 11310 * P.X * a / d ^ 5 := by simpa [F2] using hF2hi_raw
  have hF3hi : |F3| ≤ 542904 * P.X * a / d ^ 6 := by simpa [F3] using hF3hi_raw
  have hF4hi : |F4| ≤ 32574360 * P.X * a / d ^ 7 := by simpa [F4] using hF4hi_raw
  have hF5hi : |F5| ≤ 2345354640 * P.X * a / d ^ 8 := by simpa [F5] using hF5hi_raw
  have hF1ub_nonneg : 0 ≤ 314 * P.X * a / d ^ 4 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 314) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  have hF2ub_nonneg : 0 ≤ 11310 * P.X * a / d ^ 5 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 11310) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 5)
  have hF3ub_nonneg : 0 ≤ 542904 * P.X * a / d ^ 6 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 542904) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 6)
  have hF4ub_nonneg : 0 ≤ 32574360 * P.X * a / d ^ 7 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32574360) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 7)
  have hF5ub_nonneg : 0 ≤ 2345354640 * P.X * a / d ^ 8 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2345354640) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 8)
  have hF1F4 : |F1| * |F4| ≤
      (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) :=
    mul_le_mul hF1hi hF4hi (abs_nonneg _) hF1ub_nonneg
  have hF2F3 : |F2| * |F3| ≤
      (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6) :=
    mul_le_mul hF2hi hF3hi (abs_nonneg _) hF2ub_nonneg
  have hcoef2_abs : |5 * F1 * F4 + 10 * F2 * F3| ≤
      5 * |F1| * |F4| + 10 * |F2| * |F3| := by
    calc
      |5 * F1 * F4 + 10 * F2 * F3| ≤ |5 * F1 * F4| + |10 * F2 * F3| :=
        abs_add_le _ _
      _ = 5 * |F1| * |F4| + 10 * |F2| * |F3| := by
        simp [abs_mul]
  have hcoef2 :
      5 * |F1| * |F4| + 10 * |F2| * |F3| ≤
        5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
          10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6) := by
    have h2a := mul_le_mul_of_nonneg_left hF1F4 (by norm_num : (0 : ℝ) ≤ 5)
    have h2b := mul_le_mul_of_nonneg_left hF2F3 (by norm_num : (0 : ℝ) ≤ 10)
    exact add_le_add
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2a)
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2b)
  have hF1F3 : |F1| * |F3| ≤
      (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) :=
    mul_le_mul hF1hi hF3hi (abs_nonneg _) hF1ub_nonneg
  have hF2sq : |F2| ^ 2 ≤ (11310 * P.X * a / d ^ 5) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF2hi 2
  have hinner_abs : |2 * F1 * F3 + 3 * F2 ^ 2| ≤
      2 * |F1| * |F3| + 3 * |F2| ^ 2 := by
    calc
      |2 * F1 * F3 + 3 * F2 ^ 2| ≤ |2 * F1 * F3| + |3 * F2 ^ 2| :=
        abs_add_le _ _
      _ = 2 * |F1| * |F3| + 3 * |F2| ^ 2 := by
        simp [abs_mul, abs_pow]
  have hinner :
      2 * |F1| * |F3| + 3 * |F2| ^ 2 ≤
        2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
          3 * (11310 * P.X * a / d ^ 5) ^ 2 := by
    have h3a := mul_le_mul_of_nonneg_left hF1F3 (by norm_num : (0 : ℝ) ≤ 2)
    have h3b := mul_le_mul_of_nonneg_left hF2sq (by norm_num : (0 : ℝ) ≤ 3)
    exact add_le_add
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using h3a)
      h3b
  have hcoef3_abs : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2)| ≤
      5 * |F1| * (2 * |F1| * |F3| + 3 * |F2| ^ 2) := by
    calc
      |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2)| =
          5 * |F1| * |2 * F1 * F3 + 3 * F2 ^ 2| := by
        simp [abs_mul]
      _ ≤ 5 * |F1| * (2 * |F1| * |F3| + 3 * |F2| ^ 2) :=
        mul_le_mul_of_nonneg_left hinner_abs (by positivity)
  have hcoef3 :
      5 * |F1| * (2 * |F1| * |F3| + 3 * |F2| ^ 2) ≤
        5 * (314 * P.X * a / d ^ 4) *
          (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
            3 * (11310 * P.X * a / d ^ 5) ^ 2) := by
    have hleft : 5 * |F1| ≤ 5 * (314 * P.X * a / d ^ 4) := by
      exact mul_le_mul_of_nonneg_left hF1hi (by norm_num : (0 : ℝ) ≤ 5)
    exact mul_le_mul hleft hinner
      (by positivity : 0 ≤ 2 * |F1| * |F3| + 3 * |F2| ^ 2)
      (by positivity : 0 ≤ 5 * (314 * P.X * a / d ^ 4))
  have hF1cubeF2 : |F1| ^ 3 * |F2| ≤
      (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5) :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hF1hi 3) hF2hi
      (abs_nonneg _) (pow_nonneg hF1ub_nonneg 3)
  have hcoef4 :
      10 * |F1| ^ 3 * |F2| ≤
        10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5) := by
    have h := mul_le_mul_of_nonneg_left hF1cubeF2 (by norm_num : (0 : ℝ) ≤ 10)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hF1five : |F1| ^ 5 ≤ (314 * P.X * a / d ^ 4) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1hi 5
  have htri :
      |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
          5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
          10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5| ≤
        |F5 * H1| + |(5 * F1 * F4 + 10 * F2 * F3) * H2| +
          |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| +
          |10 * F1 ^ 3 * F2 * H4| + |F1 ^ 5 * H5| := by
    calc
      |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
          5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
          10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5|
          ≤ |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
              5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
              10 * F1 ^ 3 * F2 * H4| + |F1 ^ 5 * H5| := abs_add_le _ _
      _ ≤ (|F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
              5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| +
            |10 * F1 ^ 3 * F2 * H4|) + |F1 ^ 5 * H5| := by
            have h := abs_add_le
              (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
                5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3)
              (10 * F1 ^ 3 * F2 * H4)
            linarith
      _ ≤ ((|F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2| +
              |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3|) +
            |10 * F1 ^ 3 * F2 * H4|) + |F1 ^ 5 * H5| := by
            have h := abs_add_le
              (F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2)
              (5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3)
            linarith
      _ ≤ (((|F5 * H1| + |(5 * F1 * F4 + 10 * F2 * F3) * H2|) +
              |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3|) +
            |10 * F1 ^ 3 * F2 * H4|) + |F1 ^ 5 * H5| := by
            have h := abs_add_le (F5 * H1) ((5 * F1 * F4 + 10 * F2 * F3) * H2)
            linarith
      _ = |F5 * H1| + |(5 * F1 * F4 + 10 * F2 * F3) * H2| +
          |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| +
          |10 * F1 ^ 3 * F2 * H4| + |F1 ^ 5 * H5| := by ring
  have hterm1_abs : |F5 * H1| = |F5| * |H1| := by
    rw [abs_mul]
  have hterm2_abs : |(5 * F1 * F4 + 10 * F2 * F3) * H2| ≤
      (5 * |F1| * |F4| + 10 * |F2| * |F3|) * |H2| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hcoef2_abs (abs_nonneg H2)
  have hterm3_abs : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| ≤
      (5 * |F1| * (2 * |F1| * |F3| + 3 * |F2| ^ 2)) * |H3| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hcoef3_abs (abs_nonneg H3)
  have hterm4_abs : |10 * F1 ^ 3 * F2 * H4| =
      (10 * |F1| ^ 3 * |F2|) * |H4| := by
    simp [abs_mul, abs_pow]
  have hterm5_abs : |F1 ^ 5 * H5| = |F1| ^ 5 * |H5| := by
    simp [abs_mul, abs_pow]
  have hscale := sec7_ra_B3_k5_scale (P := P) (S := S) (a := a) (d := d)
    ha_lo ha_hi hd hd_lo
  calc
    |iteratedDeriv 5 (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d|
        = |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
            5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
            10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5| := by rw [hiter]
    _ ≤ |F5| * |H1| + (5 * |F1| * |F4| + 10 * |F2| * |F3|) * |H2| +
        (5 * |F1| * (2 * |F1| * |F3| + 3 * |F2| ^ 2)) * |H3| +
        (10 * |F1| ^ 3 * |F2|) * |H4| + |F1| ^ 5 * |H5| := by
          calc
            |F5 * H1 + (5 * F1 * F4 + 10 * F2 * F3) * H2 +
                5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3 +
                10 * F1 ^ 3 * F2 * H4 + F1 ^ 5 * H5|
                ≤ |F5 * H1| + |(5 * F1 * F4 + 10 * F2 * F3) * H2| +
                  |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H3| +
                  |10 * F1 ^ 3 * F2 * H4| + |F1 ^ 5 * H5| := htri
            _ ≤ |F5| * |H1| + (5 * |F1| * |F4| + 10 * |F2| * |F3|) * |H2| +
                (5 * |F1| * (2 * |F1| * |F3| + 3 * |F2| ^ 2)) * |H3| +
                (10 * |F1| ^ 3 * |F2|) * |H4| + |F1| ^ 5 * |H5| := by
                  rw [hterm1_abs, hterm4_abs, hterm5_abs]
                  exact add_le_add
                    (add_le_add
                      (add_le_add
                        (add_le_add le_rfl hterm2_abs)
                        hterm3_abs)
                      le_rfl)
                    le_rfl
    _ ≤ (2345354640 * P.X * a / d ^ 8) * ((sec7_cPh * S.D / S.F ^ 2) * |j|) +
        (5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
            10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6)) *
          (((10 ^ 80 : ℝ) * S.D / S.F ^ 3) * |j|) +
        (5 * (314 * P.X * a / d ^ 4) *
            (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
              3 * (11310 * P.X * a / d ^ 5) ^ 2)) *
          (((10 ^ 100 : ℝ) * S.D / S.F ^ 4) * |j|) +
        (10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5)) *
          (((10 ^ 100 : ℝ) * S.D / S.F ^ 5) * |j|) +
        (314 * P.X * a / d ^ 4) ^ 5 *
          (((10 ^ 100 : ℝ) * S.D / S.F ^ 6) * |j|) := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (add_le_add
                  (mul_le_mul hF5hi hH1 (abs_nonneg _) hF5ub_nonneg)
                  (mul_le_mul hcoef2 hH2 (abs_nonneg _)
                    (by positivity :
                      0 ≤ 5 * (314 * P.X * a / d ^ 4) *
                          (32574360 * P.X * a / d ^ 7) +
                        10 * (11310 * P.X * a / d ^ 5) *
                          (542904 * P.X * a / d ^ 6))))
                (mul_le_mul hcoef3 hH3 (abs_nonneg _)
                  (by positivity :
                    0 ≤ 5 * (314 * P.X * a / d ^ 4) *
                      (2 * (314 * P.X * a / d ^ 4) *
                          (542904 * P.X * a / d ^ 6) +
                        3 * (11310 * P.X * a / d ^ 5) ^ 2))))
              (mul_le_mul hcoef4 hH4 (abs_nonneg _)
                (by positivity :
                  0 ≤ 10 * (314 * P.X * a / d ^ 4) ^ 3 *
                    (11310 * P.X * a / d ^ 5))))
            (mul_le_mul hF1five hH5 (abs_nonneg _)
              (pow_nonneg hF1ub_nonneg 5))
    _ = ((2345354640 * P.X * a / d ^ 8) * (sec7_cPh * S.D / S.F ^ 2) +
        ((5 * (314 * P.X * a / d ^ 4) * (32574360 * P.X * a / d ^ 7) +
            10 * (11310 * P.X * a / d ^ 5) * (542904 * P.X * a / d ^ 6)) *
          ((10 ^ 80 : ℝ) * S.D / S.F ^ 3)) +
        (5 * (314 * P.X * a / d ^ 4) *
            (2 * (314 * P.X * a / d ^ 4) * (542904 * P.X * a / d ^ 6) +
              3 * (11310 * P.X * a / d ^ 5) ^ 2)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 4) +
        (10 * (314 * P.X * a / d ^ 4) ^ 3 * (11310 * P.X * a / d ^ 5)) *
          ((10 ^ 100 : ℝ) * S.D / S.F ^ 5) +
        (314 * P.X * a / d ^ 4) ^ 5 * ((10 ^ 100 : ℝ) * S.D / S.F ^ 6)) * |j| := by
          ring
    _ ≤ (sec7_ra_B3Scale 5 / (d * (P.X * a))) * |j| :=
          mul_le_mul_of_nonneg_right hscale (abs_nonneg j)
    _ = sec7_ra_B3Scale 5 * |j| / (d * (P.X * a)) := by ring

theorem sec7_ra_B3_bound_public {P : Globals} {S : Scale P} {a d j : ℝ} {k : ℕ}
    (hk : k ≤ 5)
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hd_lo : S.D / 16 ≤ d) (had : a ≤ d)
    (hseg : ∀ s ∈ Set.uIcc (0 : ℝ) j, Ffun P.X a d + s ∈ sec7_tWin S) :
    |iteratedDeriv k (fun t => dBreve P.X a (Ffun P.X a t + j) - t) d| ≤
      match k with
      | 0 => (10 ^ 20 : ℝ) * |j| * d ^ 4 / (P.X * a)
      | 1 => (10 ^ 40 : ℝ) * |j| * d ^ 3 / (P.X * a)
      | 2 => (10 ^ 120 : ℝ) * |j| * d ^ 2 / (P.X * a)
      | 3 => (10 ^ 130 : ℝ) * |j| * d / (P.X * a)
      | 4 => (10 ^ 140 : ℝ) * |j| / (P.X * a)
      | 5 => (10 ^ 143 : ℝ) * |j| / (d * (P.X * a))
      | _ => 0 := by
  interval_cases k
  · simpa [sec7_ra_B3Scale] using
      sec7_ra_B3_bound_k0 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd_lo hseg
  · simpa [sec7_ra_B3Scale] using
      sec7_ra_B3_bound_k1 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd hd_lo had hseg
  · simpa [sec7_ra_B3Scale] using
      sec7_ra_B3_bound_k2 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd hd_lo had hseg
  · simpa [sec7_ra_B3Scale] using
      sec7_ra_B3_bound_k3 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd hd_lo had hseg
  · simpa [sec7_ra_B3Scale] using
      sec7_ra_B3_bound_k4 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd hd_lo had hseg
  · simpa [sec7_ra_B3Scale] using
      sec7_ra_B3_bound_k5 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd hd_lo had hseg

private theorem sec7_ra_residual_rho_factor {X a d : ℝ} (hd : 0 < d) (ha : 0 < a) :
    Ffun X a d - 2 * X * a / (d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2)) =
      X * a * (Real.sqrt (d + a) - Real.sqrt d) ^ 2 / (d ^ 2 * (d + a) ^ 2) := by
  have hda : 0 < d + a := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd
  have hdane : d + a ≠ 0 := ne_of_gt hda
  have hsqrtd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hsqrtda : 0 < Real.sqrt (d + a) := Real.sqrt_pos.2 hda
  have hd32 : d ^ ((3 : ℝ) / 2) = d * Real.sqrt d := by
    rw [Real.rpow_div_two_eq_sqrt (x := d) (r := 3) hd.le]
    rw [show Real.sqrt d ^ (3 : ℝ) = d * Real.sqrt d by
      rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hsqrtd,
        Real.rpow_two, Real.rpow_one, Real.sq_sqrt hd.le]]
  have hda32 : (d + a) ^ ((3 : ℝ) / 2) = (d + a) * Real.sqrt (d + a) := by
    rw [Real.rpow_div_two_eq_sqrt (x := d + a) (r := 3) hda.le]
    rw [show Real.sqrt (d + a) ^ (3 : ℝ) = (d + a) * Real.sqrt (d + a) by
      rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hsqrtda,
        Real.rpow_two, Real.rpow_one, Real.sq_sqrt hda.le]]
  rw [Ffun_factor' X a d hdne hdane, hd32, hda32]
  field_simp [hdne, hdane, ne_of_gt hsqrtd, ne_of_gt hsqrtda]
  set p := Real.sqrt d
  set q := Real.sqrt (d + a)
  have hp2 : p ^ 2 = d := by simpa [p] using Real.sq_sqrt hd.le
  have hq2 : q ^ 2 = d + a := by simpa [q] using Real.sq_sqrt hda.le
  have ha_pq : a = q ^ 2 - p ^ 2 := by rw [hq2, hp2]; ring
  rw [← hq2, ← hp2, ha_pq]
  ring

private theorem sec7_ra_residual_rho_factor_rpow {X a d : ℝ} (hd : 0 < d) (ha : 0 < a) :
    Ffun X a d - 2 * X * a / (d ^ ((3 : ℝ) / 2) * (d + a) ^ ((3 : ℝ) / 2)) =
      X * a * (((Real.sqrt (d + a) - Real.sqrt d) ^ 2 * d ^ (-2 : ℝ))
        * (d + a) ^ (-2 : ℝ)) := by
  have hda : 0 < d + a := by linarith
  rw [sec7_ra_residual_rho_factor (X := X) (a := a) (d := d) hd ha]
  have hdneg : d ^ (-2 : ℝ) = (d ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hd.le]
    rw [show d ^ (2 : ℝ) = d ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  have hdaneg : (d + a) ^ (-2 : ℝ) = ((d + a) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hda.le]
    rw [show (d + a) ^ (2 : ℝ) = (d + a) ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  rw [hdneg, hdaneg]
  field_simp [ne_of_gt hd, ne_of_gt hda]

private theorem sec7_ra_h_iteratedDeriv_eq {a d : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hd : 0 < d) :
    iteratedDeriv k (fun t => Real.sqrt (t + a) - Real.sqrt t) d =
      sec7_ra_hCoeff k * ((d + a) ^ ((1 : ℝ) / 2 - k) - d ^ ((1 : ℝ) / 2 - k)) := by
  have hda : 0 < d + a := by linarith
  have hfun :
      (fun t : ℝ => Real.sqrt (t + a) - Real.sqrt t)
        = fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2) - t ^ ((1 : ℝ) / 2) := by
    funext t
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hfun]
  have hshift :
      iteratedDeriv k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d =
        (descPochhammer ℝ k).eval ((1 : ℝ) / 2) * (d + a) ^ ((1 : ℝ) / 2 - k) := by
    rw [show iteratedDeriv k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d =
        iteratedDeriv k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (d + a) by
      simpa using congrFun
        (iteratedDeriv_comp_add_const k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) a) d]
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const ((1 : ℝ) / 2) (d + a) k
  have hid :
      iteratedDeriv k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) d =
        (descPochhammer ℝ k).eval ((1 : ℝ) / 2) * d ^ ((1 : ℝ) / 2 - k) := by
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const ((1 : ℝ) / 2) d k
  have hf : ContDiffAt ℝ k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d :=
    (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (ne_of_gt hda)
  have hg : ContDiffAt ℝ k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) d :=
    contDiffAt_id.rpow_const_of_ne (ne_of_gt hd)
  rw [iteratedDeriv_fun_sub hf hg, hshift, hid]
  have hcoeff : (descPochhammer ℝ k).eval ((1 : ℝ) / 2) = sec7_ra_hCoeff k := by
    interval_cases k <;>
      simp [sec7_ra_hCoeff, descPochhammer_eval_eq_prod_range] <;> norm_num
  rw [hcoeff]
  ring

private theorem sec7_ra_rpow_forward_abs_le {p a d : ℝ}
    (hd : 0 < d) (ha : 0 ≤ a) (hp : p - 1 ≤ 0) :
    |(d + a) ^ p - d ^ p| ≤ |p| * d ^ (p - 1) * a := by
  have hdd : d ≤ d + a := by linarith
  have hderiv : ∀ x ∈ Icc d (d + a),
      HasDerivAt (fun y : ℝ => y ^ p) (p * x ^ (p - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le hd hx.1)))
  have hbnd : ∀ x ∈ Icc d (d + a), |p * x ^ (p - 1)| ≤ |p| * d ^ (p - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hd hx.1
    have hxpow_nonneg : 0 ≤ x ^ (p - 1) := (Real.rpow_pos_of_pos hx0 _).le
    have hpow : x ^ (p - 1) ≤ d ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos hd hx.1 hp
    calc
      |p * x ^ (p - 1)| = |p| * x ^ (p - 1) := by
        rw [abs_mul, abs_of_nonneg hxpow_nonneg]
      _ ≤ |p| * d ^ (p - 1) := mul_le_mul_of_nonneg_left hpow (abs_nonneg p)
  have hmvt := (convex_Icc d (d + a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => y ^ p) (f' := fun x : ℝ => p * x ^ (p - 1))
    (C := |p| * d ^ (p - 1))
    (fun x hx => (hderiv x hx).hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hbnd x hx)
    (left_mem_Icc.mpr hdd) (right_mem_Icc.mpr hdd)
  simpa [Real.norm_eq_abs, abs_of_nonneg ha, add_sub_cancel_left] using hmvt

theorem sec7_ra_h_atomic_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    iteratedDeriv k (fun t => Real.sqrt (t + a) - Real.sqrt t) d =
        sec7_ra_hCoeff k * ((d + a) ^ ((1 : ℝ) / 2 - k) - d ^ ((1 : ℝ) / 2 - k))
      ∧ |iteratedDeriv k (fun t => Real.sqrt (t + a) - Real.sqrt t) d|
        ≤ sec7_ra_hScale k * a * d ^ ((-1 : ℝ) / 2 - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have heq := sec7_ra_h_iteratedDeriv_eq (a := a) (d := d) hk ha hd
  constructor
  · exact heq
  · rw [heq]
    set p : ℝ := (1 : ℝ) / 2 - k with hp_def
    set Δ : ℝ := (d + a) ^ p - d ^ p with hΔ_def
    have hp : p - 1 ≤ 0 := by
      rw [hp_def]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hdiff : |Δ| ≤ |p| * d ^ (p - 1) * a := by
      rw [hΔ_def]
      exact sec7_ra_rpow_forward_abs_le (p := p) hd ha.le hp
    have hscale : |sec7_ra_hCoeff k| * |p| = sec7_ra_hScale k := by
      rw [hp_def]
      interval_cases k <;> norm_num [sec7_ra_hCoeff, sec7_ra_hScale]
    have hexp : p - 1 = (-1 : ℝ) / 2 - k := by
      rw [hp_def]
      ring
    calc
      |sec7_ra_hCoeff k * Δ| = |sec7_ra_hCoeff k| * |Δ| := by rw [abs_mul]
      _ ≤ |sec7_ra_hCoeff k| * (|p| * d ^ (p - 1) * a) :=
          mul_le_mul_of_nonneg_left hdiff (abs_nonneg (sec7_ra_hCoeff k))
      _ = sec7_ra_hScale k * a * d ^ ((-1 : ℝ) / 2 - k) := by
          rw [← hscale, hexp]
          ring

private theorem sec7_ra_sqrt_bound {d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t : ℝ => Real.sqrt t) d|
      ≤ sec7_ra_sqrtScale k * d ^ ((1 : ℝ) / 2 - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  rw [show (fun t : ℝ => Real.sqrt t) = fun t : ℝ => t ^ ((1 : ℝ) / 2) by
    funext t
    rw [Real.sqrt_eq_rpow]]
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  have hcoeff : |(descPochhammer ℝ k).eval ((1 : ℝ) / 2)| = sec7_ra_sqrtScale k := by
    interval_cases k <;>
      simp [sec7_ra_sqrtScale, descPochhammer_eval_eq_prod_range] <;> norm_num
  have hpow_nonneg : 0 ≤ d ^ ((1 : ℝ) / 2 - k) := (Real.rpow_pos_of_pos hd _).le
  rw [abs_mul, hcoeff, abs_of_nonneg hpow_nonneg]

private theorem sec7_ra_inv2_bound {d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t : ℝ => t ^ (-2 : ℝ)) d|
      ≤ sec7_ra_inv2Scale k * d ^ ((-2 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  have hcoeff : |(descPochhammer ℝ k).eval (-2 : ℝ)| = sec7_ra_inv2Scale k := by
    interval_cases k <;>
      simp [sec7_ra_inv2Scale, descPochhammer_eval_eq_prod_range] <;> norm_num
  have hpow_nonneg : 0 ≤ d ^ ((-2 : ℝ) - k) := (Real.rpow_pos_of_pos hd _).le
  rw [abs_mul, hcoeff, abs_of_nonneg hpow_nonneg]

private theorem sec7_ra_shift_inv2_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t : ℝ => (t + a) ^ (-2 : ℝ)) d|
      ≤ sec7_ra_inv2Scale k * d ^ ((-2 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have hda : 0 < d + a := by linarith
  have hle : d ≤ d + a := by linarith
  have hq : (-2 : ℝ) - k ≤ 0 := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hpow_le : (d + a) ^ ((-2 : ℝ) - k) ≤ d ^ ((-2 : ℝ) - k) :=
    Real.rpow_le_rpow_of_nonpos hd hle hq
  rw [show iteratedDeriv k (fun t : ℝ => (t + a) ^ (-2 : ℝ)) d =
      iteratedDeriv k (fun t : ℝ => t ^ (-2 : ℝ)) (d + a) by
    simpa using congrFun
      (iteratedDeriv_comp_add_const k (fun t : ℝ => t ^ (-2 : ℝ)) a) d]
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  have hcoeff : |(descPochhammer ℝ k).eval (-2 : ℝ)| = sec7_ra_inv2Scale k := by
    interval_cases k <;>
      simp [sec7_ra_inv2Scale, descPochhammer_eval_eq_prod_range] <;> norm_num
  have hpow_nonneg : 0 ≤ (d + a) ^ ((-2 : ℝ) - k) := (Real.rpow_pos_of_pos hda _).le
  calc
    |(descPochhammer ℝ k).eval (-2 : ℝ) * (d + a) ^ ((-2 : ℝ) - k)|
        = sec7_ra_inv2Scale k * (d + a) ^ ((-2 : ℝ) - k) := by
          rw [abs_mul, hcoeff, abs_of_nonneg hpow_nonneg]
    _ ≤ sec7_ra_inv2Scale k * d ^ ((-2 : ℝ) - k) :=
        mul_le_mul_of_nonneg_left hpow_le (by
          interval_cases k <;> norm_num [sec7_ra_inv2Scale])

private theorem sec7_ra_h_contDiffAt {a d : ℝ} {k : ℕ} (ha : 0 < a) (hd : 0 < d) :
    ContDiffAt ℝ k (fun t => Real.sqrt (t + a) - Real.sqrt t) d := by
  have hda : 0 < d + a := by linarith
  have h1 : ContDiffAt ℝ k (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2)) d :=
    (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (ne_of_gt hda)
  have h2 : ContDiffAt ℝ k (fun t : ℝ => t ^ ((1 : ℝ) / 2)) d :=
    contDiffAt_id.rpow_const_of_ne (ne_of_gt hd)
  have hsub := h1.sub h2
  have hfun :
      (fun t : ℝ => (t + a) ^ ((1 : ℝ) / 2) - t ^ ((1 : ℝ) / 2))
        = fun t : ℝ => Real.sqrt (t + a) - Real.sqrt t := by
    funext t
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rwa [hfun] at hsub

private theorem sec7_ra_hsq_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2) d|
      ≤ sec7_ra_hsqScale k * a ^ 2 * d ^ ((-1 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set h : ℝ → ℝ := fun t => Real.sqrt (t + a) - Real.sqrt t
  have hh : ContDiffAt ℝ k h d := by
    simpa [h] using sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
  have hpow_eq : (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2) =
      fun t => h t * h t := by
    funext t
    simp [h, sq]
  rw [hpow_eq, iteratedDeriv_fun_mul hh hh]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d|
        ≤ (k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i)
            * a ^ 2 * d ^ ((-1 : ℝ) - k) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 6 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 6 := le_trans (Nat.sub_le k i) hk
    have hb_i := (sec7_ra_h_atomic_bound (a := a) (d := d) (d_lo := d_lo)
      (k := i) hi5 ha hdlo hlo).2
    have hb_ki := (sec7_ra_h_atomic_bound (a := a) (d := d) (d_lo := d_lo)
      (k := k - i) hki5 ha hdlo hlo).2
    have hb_i' : |iteratedDeriv i h d| ≤ sec7_ra_hScale i * a * d ^ ((-1 : ℝ) / 2 - i) := by
      simpa [h] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) h d|
          ≤ sec7_ra_hScale (k - i) * a * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [h, hcast] using hb_ki
    have hpow :
        d ^ (((-1 : ℝ) / 2 - i) + ((-1 : ℝ) / 2 - ((k : ℝ) - i))) =
          d ^ ((-1 : ℝ) - k) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((-1 : ℝ) / 2 - i) * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)) =
          d ^ ((-1 : ℝ) - k) := by
      rw [← Real.rpow_add hd, hpow]
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) (by
      have hscale_i_nonneg : 0 ≤ sec7_ra_hScale i := by
        interval_cases i <;> norm_num [sec7_ra_hScale]
      have hnon : 0 ≤ sec7_ra_hScale i * a * d ^ ((-1 : ℝ) / 2 - i) := by
        exact mul_nonneg (mul_nonneg hscale_i_nonneg ha.le) (Real.rpow_pos_of_pos hd _).le
      exact hnon)
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i h d * iteratedDeriv (k - i) h d|
          = (k.choose i : ℝ) * (|iteratedDeriv i h d| * |iteratedDeriv (k - i) h d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_hScale i * a * d ^ ((-1 : ℝ) / 2 - i)) *
              (sec7_ra_hScale (k - i) * a * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i) * a ^ 2) *
            (d ^ ((-1 : ℝ) / 2 - i) * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i)
            * a ^ 2 * d ^ ((-1 : ℝ) - k) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_hScale i * sec7_ra_hScale (k - i))
        = sec7_ra_hsqScale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_hScale, sec7_ra_hsqScale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

private theorem sec7_ra_A3_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t => t - Real.sqrt (t * (t + a))) d|
      ≤ sec7_ra_A3Scale k * a * d ^ (-(k : ℝ)) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set p : ℝ → ℝ := fun t => Real.sqrt t
  set h : ℝ → ℝ := fun t => Real.sqrt (t + a) - Real.sqrt t
  have hp : ContDiffAt ℝ k p d := by
    simpa [p, Real.sqrt_eq_rpow] using
      (contDiffAt_id.rpow_const_of_ne (n := k) (p := ((1 : ℝ) / 2)) (ne_of_gt hd))
  have hh : ContDiffAt ℝ k h d := by
    simpa [h] using sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
  have heqv :
      (fun t => t - Real.sqrt (t * (t + a))) =ᶠ[nhds d] fun t => -(p t * h t) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    have hta : 0 < t + a := by linarith
    have hsqt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    calc
      t - Real.sqrt (t * (t + a))
          = t - Real.sqrt t * Real.sqrt (t + a) := by
              rw [Real.sqrt_mul ht.le (t + a)]
      _ = -(p t * h t) := by
              rw [← hsqt]
              simp [p, h]
              ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heqv]
  rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_mul hp hh, abs_neg]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i p d * iteratedDeriv (k - i) h d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i p d * iteratedDeriv (k - i) h d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i p d * iteratedDeriv (k - i) h d|
        ≤ (k.choose i : ℝ) * sec7_ra_sqrtScale i * sec7_ra_hScale (k - i)
            * a * d ^ (-(k : ℝ)) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 6 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 6 := le_trans (Nat.sub_le k i) hk
    have hb_i := sec7_ra_sqrt_bound (d := d) (d_lo := d_lo) (k := i) hi5 hdlo hlo
    have hb_ki := (sec7_ra_h_atomic_bound (a := a) (d := d) (d_lo := d_lo)
      (k := k - i) hki5 ha hdlo hlo).2
    have hb_i' :
        |iteratedDeriv i p d| ≤ sec7_ra_sqrtScale i * d ^ ((1 : ℝ) / 2 - i) := by
      simpa [p] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) h d|
          ≤ sec7_ra_hScale (k - i) * a * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [h, hcast] using hb_ki
    have hpow :
        d ^ (((1 : ℝ) / 2 - i) + ((-1 : ℝ) / 2 - ((k : ℝ) - i))) =
          d ^ (-(k : ℝ)) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((1 : ℝ) / 2 - i) * d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)) =
          d ^ (-(k : ℝ)) := by
      rw [← Real.rpow_add hd, hpow]
    have hleft_nonneg : 0 ≤ sec7_ra_sqrtScale i * d ^ ((1 : ℝ) / 2 - i) := by
      have hscale : 0 ≤ sec7_ra_sqrtScale i := by
        interval_cases i <;> norm_num [sec7_ra_sqrtScale]
      exact mul_nonneg hscale (Real.rpow_pos_of_pos hd _).le
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) hleft_nonneg
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i p d * iteratedDeriv (k - i) h d|
          = (k.choose i : ℝ) * (|iteratedDeriv i p d| * |iteratedDeriv (k - i) h d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_sqrtScale i * d ^ ((1 : ℝ) / 2 - i)) *
              (sec7_ra_hScale (k - i) * a *
                d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_sqrtScale i * sec7_ra_hScale (k - i) * a) *
            (d ^ ((1 : ℝ) / 2 - i) *
              d ^ ((-1 : ℝ) / 2 - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_sqrtScale i * sec7_ra_hScale (k - i)
            * a * d ^ (-(k : ℝ)) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_sqrtScale i * sec7_ra_hScale (k - i))
        = sec7_ra_A3Scale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_sqrtScale, sec7_ra_hScale,
        sec7_ra_A3Scale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

theorem sec7_ra_A3_bound_public {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 5) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t => t - Real.sqrt (t * (t + a))) d|
      ≤ (30 : ℝ) * a * d ^ (-(k : ℝ)) := by
  have hraw := sec7_ra_A3_bound (a := a) (d := d) (d_lo := d_lo) (k := k)
    (hk.trans (by norm_num)) ha hdlo hlo
  have hscale : sec7_ra_A3Scale k ≤ (30 : ℝ) := by
    interval_cases k <;> norm_num [sec7_ra_A3Scale]
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have htail : 0 ≤ a * d ^ (-(k : ℝ)) :=
    mul_nonneg ha.le (Real.rpow_pos_of_pos hd _).le
  calc
    |iteratedDeriv k (fun t => t - Real.sqrt (t * (t + a))) d|
        ≤ sec7_ra_A3Scale k * (a * d ^ (-(k : ℝ))) := by
          simpa [mul_assoc] using hraw
    _ ≤ (30 : ℝ) * (a * d ^ (-(k : ℝ))) :=
          mul_le_mul_of_nonneg_right hscale htail
    _ = (30 : ℝ) * a * d ^ (-(k : ℝ)) := by ring

/-- Order-6 public A₃ bound: same shape as `sec7_ra_A3_bound_public` but valid up
to `k = 6`, with the looser absolute scale `10395/64 = max_{k≤6} A3Scale k`. -/
theorem sec7_ra_A3_bound_public6 {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k (fun t => t - Real.sqrt (t * (t + a))) d|
      ≤ (10395 / 64 : ℝ) * a * d ^ (-(k : ℝ)) := by
  have hraw := sec7_ra_A3_bound (a := a) (d := d) (d_lo := d_lo) (k := k)
    hk ha hdlo hlo
  have hscale : sec7_ra_A3Scale k ≤ (10395 / 64 : ℝ) := by
    interval_cases k <;> norm_num [sec7_ra_A3Scale]
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have htail : 0 ≤ a * d ^ (-(k : ℝ)) :=
    mul_nonneg ha.le (Real.rpow_pos_of_pos hd _).le
  calc
    |iteratedDeriv k (fun t => t - Real.sqrt (t * (t + a))) d|
        ≤ sec7_ra_A3Scale k * (a * d ^ (-(k : ℝ))) := by
          simpa [mul_assoc] using hraw
    _ ≤ (10395 / 64 : ℝ) * (a * d ^ (-(k : ℝ))) :=
          mul_le_mul_of_nonneg_right hscale htail
    _ = (10395 / 64 : ℝ) * a * d ^ (-(k : ℝ)) := by ring

private theorem sec7_ra_hsq_inv_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k
        (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ)) d|
      ≤ sec7_ra_hsqInvScale k * a ^ 2 * d ^ ((-3 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set f : ℝ → ℝ := fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2
  set g : ℝ → ℝ := fun t => t ^ (-2 : ℝ)
  have hf : ContDiffAt ℝ k f d := by
    have hh := sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
    simpa [f, sq] using hh.mul hh
  have hg : ContDiffAt ℝ k g d := by
    simpa [g] using contDiffAt_id.rpow_const_of_ne (n := k) (p := (-2 : ℝ)) (ne_of_gt hd)
  have hfun :
      (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ)) =
        fun t => f t * g t := by
    funext t
    simp [f, g]
  rw [hfun, iteratedDeriv_fun_mul hf hg]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ (k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-3 : ℝ) - k) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 6 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 6 := le_trans (Nat.sub_le k i) hk
    have hb_i := sec7_ra_hsq_bound (a := a) (d := d) (d_lo := d_lo)
      (k := i) hi5 ha hdlo hlo
    have hb_ki := sec7_ra_inv2_bound (d := d) (d_lo := d_lo)
      (k := k - i) hki5 hdlo hlo
    have hb_i' : |iteratedDeriv i f d| ≤ sec7_ra_hsqScale i * a ^ 2 * d ^ ((-1 : ℝ) - i) := by
      simpa [f] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) g d|
          ≤ sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [g, hcast] using hb_ki
    have hpow :
        d ^ (((-1 : ℝ) - i) + ((-2 : ℝ) - ((k : ℝ) - i))) =
          d ^ ((-3 : ℝ) - k) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((-1 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) =
          d ^ ((-3 : ℝ) - k) := by
      rw [← Real.rpow_add hd, hpow]
    have hleft_nonneg : 0 ≤ sec7_ra_hsqScale i * a ^ 2 * d ^ ((-1 : ℝ) - i) := by
      have hscale : 0 ≤ sec7_ra_hsqScale i := by
        interval_cases i <;> norm_num [sec7_ra_hsqScale]
      exact mul_nonneg (mul_nonneg hscale (sq_nonneg a)) (Real.rpow_pos_of_pos hd _).le
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) hleft_nonneg
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
          = (k.choose i : ℝ) * (|iteratedDeriv i f d| * |iteratedDeriv (k - i) g d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_hsqScale i * a ^ 2 * d ^ ((-1 : ℝ) - i)) *
              (sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i) * a ^ 2) *
            (d ^ ((-1 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-3 : ℝ) - k) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_hsqScale i * sec7_ra_inv2Scale (k - i))
        = sec7_ra_hsqInvScale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_hsqScale, sec7_ra_inv2Scale,
        sec7_ra_hsqInvScale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

private theorem sec7_ra_rho_model_bound {a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (ha : 0 < a) (hdlo : 0 < d_lo) (hlo : d_lo ≤ d) :
    |iteratedDeriv k
        (fun t => ((Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ))
          * (t + a) ^ (-2 : ℝ)) d|
      ≤ sec7_ra_rhoScale k * a ^ 2 * d ^ ((-5 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  have hda : 0 < d + a := by linarith
  set f : ℝ → ℝ := fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ)
  set g : ℝ → ℝ := fun t => (t + a) ^ (-2 : ℝ)
  have hf : ContDiffAt ℝ k f d := by
    have hh := sec7_ra_h_contDiffAt (a := a) (d := d) (k := k) ha hd
    have hhsq : ContDiffAt ℝ k (fun t => (Real.sqrt (t + a) - Real.sqrt t) ^ 2) d := by
      simpa [sq] using hh.mul hh
    have hinv : ContDiffAt ℝ k (fun t : ℝ => t ^ (-2 : ℝ)) d :=
      contDiffAt_id.rpow_const_of_ne (n := k) (p := (-2 : ℝ)) (ne_of_gt hd)
    simpa [f] using hhsq.mul hinv
  have hg : ContDiffAt ℝ k g d := by
    simpa [g] using
      (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (n := k) (p := (-2 : ℝ))
        (ne_of_gt hda)
  rw [show (fun t => ((Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ))
          * (t + a) ^ (-2 : ℝ)) = fun t => f t * g t by
    funext t
    simp [f, g]]
  rw [iteratedDeriv_fun_mul hf hg]
  have hsum_abs :
      |∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine hsum_abs.trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
        ≤ (k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-5 : ℝ) - k) := by
    intro i hi
    have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi5 : i ≤ 6 := le_trans hi_le_k hk
    have hki5 : k - i ≤ 6 := le_trans (Nat.sub_le k i) hk
    have hb_i := sec7_ra_hsq_inv_bound (a := a) (d := d) (d_lo := d_lo)
      (k := i) hi5 ha hdlo hlo
    have hb_ki := sec7_ra_shift_inv2_bound (a := a) (d := d) (d_lo := d_lo)
      (k := k - i) hki5 ha hdlo hlo
    have hb_i' : |iteratedDeriv i f d| ≤ sec7_ra_hsqInvScale i * a ^ 2 * d ^ ((-3 : ℝ) - i) := by
      simpa [f] using hb_i
    have hb_ki' :
        |iteratedDeriv (k - i) g d|
          ≤ sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) := by
      have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := Nat.cast_sub hi_le_k
      simpa [g, hcast] using hb_ki
    have hpow :
        d ^ (((-3 : ℝ) - i) + ((-2 : ℝ) - ((k : ℝ) - i))) =
          d ^ ((-5 : ℝ) - k) := by
      congr 1
      ring
    have hpowmul :
        d ^ ((-3 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)) =
          d ^ ((-5 : ℝ) - k) := by
      rw [← Real.rpow_add hd, hpow]
    have hleft_nonneg : 0 ≤ sec7_ra_hsqInvScale i * a ^ 2 * d ^ ((-3 : ℝ) - i) := by
      have hscale : 0 ≤ sec7_ra_hsqInvScale i := by
        interval_cases i <;> norm_num [sec7_ra_hsqInvScale]
      exact mul_nonneg (mul_nonneg hscale (sq_nonneg a)) (Real.rpow_pos_of_pos hd _).le
    have hmul := mul_le_mul hb_i' hb_ki' (abs_nonneg _) hleft_nonneg
    have hchoose_nonneg : 0 ≤ (k.choose i : ℝ) := by positivity
    calc
      |(k.choose i : ℝ) * iteratedDeriv i f d * iteratedDeriv (k - i) g d|
          = (k.choose i : ℝ) * (|iteratedDeriv i f d| * |iteratedDeriv (k - i) g d|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hchoose_nonneg]
            ring
      _ ≤ (k.choose i : ℝ) *
            ((sec7_ra_hsqInvScale i * a ^ 2 * d ^ ((-3 : ℝ) - i)) *
              (sec7_ra_inv2Scale (k - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i)))) :=
          mul_le_mul_of_nonneg_left hmul hchoose_nonneg
      _ = ((k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i) * a ^ 2) *
            (d ^ ((-3 : ℝ) - i) * d ^ ((-2 : ℝ) - ((k : ℝ) - i))) := by
          ring
      _ = (k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i)
            * a ^ 2 * d ^ ((-5 : ℝ) - k) := by
          rw [hpowmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  have hconst :
      (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * sec7_ra_hsqInvScale i * sec7_ra_inv2Scale (k - i))
        = sec7_ra_rhoScale k := by
    interval_cases k <;>
      norm_num [Finset.sum_range_succ, Nat.choose, sec7_ra_hsqInvScale, sec7_ra_inv2Scale,
        sec7_ra_rhoScale]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hconst]

theorem sec7_ra_rho_tower {X a d d_lo : ℝ} {k : ℕ}
    (hk : k ≤ 6) (hX : 0 < X) (ha : 0 < a) (hdlo : 0 < d_lo)
    (hlo : d_lo ≤ d) (_had : a ≤ d) :
    |iteratedDeriv k
        (fun t => Ffun X a t
          - 2 * X * a / (t ^ ((3 : ℝ) / 2) * (t + a) ^ ((3 : ℝ) / 2))) d|
      ≤ sec7_ra_rhoScale k * X * a ^ 3 * d ^ ((-5 : ℝ) - k) := by
  have hd : 0 < d := lt_of_lt_of_le hdlo hlo
  set model : ℝ → ℝ :=
    fun t => ((Real.sqrt (t + a) - Real.sqrt t) ^ 2 * t ^ (-2 : ℝ))
      * (t + a) ^ (-2 : ℝ)
  have heqv :
      (fun t => Ffun X a t
          - 2 * X * a / (t ^ ((3 : ℝ) / 2) * (t + a) ^ ((3 : ℝ) / 2)))
        =ᶠ[nhds d] fun t => X * a * model t := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    simpa [model] using sec7_ra_residual_rho_factor_rpow (X := X) (a := a) (d := t) ht ha
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heqv]
  rw [iteratedDeriv_const_mul_field]
  have hmodel := sec7_ra_rho_model_bound (a := a) (d := d) (d_lo := d_lo)
    (k := k) hk ha hdlo hlo
  have hXa_nonneg : 0 ≤ X * a := (mul_pos hX ha).le
  calc
    |X * a * iteratedDeriv k model d| = X * a * |iteratedDeriv k model d| := by
      rw [abs_mul, abs_of_nonneg hXa_nonneg]
    _ ≤ X * a * (sec7_ra_rhoScale k * a ^ 2 * d ^ ((-5 : ℝ) - k)) :=
      mul_le_mul_of_nonneg_left hmodel hXa_nonneg
    _ = sec7_ra_rhoScale k * X * a ^ 3 * d ^ ((-5 : ℝ) - k) := by
      ring

end Squarefree
