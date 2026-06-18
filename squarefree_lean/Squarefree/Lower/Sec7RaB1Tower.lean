import Squarefree.Lower.Sec7RaResidual

/-!
# §7 `f₁` B1 shift tower

The sharp aled B1 tower split from `Sec7RaResidual`.
-/

namespace Squarefree

open Set

private noncomputable def sec7_ra_B1SharpScaleAled : ℕ → ℝ
  | 0 => 300
  | 1 => 1400
  | 2 => 152200
  | 3 => 18813600
  | 4 => 4000696000
  | 5 => 191061040000
  | _ => 0

private theorem sec7_ra_B1_bound_sharp_aled_k0 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 0
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
      ≤ sec7_ra_B1SharpScaleAled 0 * |j| * d ^ 7 / (P.X * a) ^ 2 := by
  have hH1 := (sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose).1
  simp only [iteratedDeriv_zero]
  rw [show -dBreve' P.X a (Ffun P.X a d + j) + dBreve' P.X a (Ffun P.X a d) =
      -(dBreve' P.X a (Ffun P.X a d + j) - dBreve' P.X a (Ffun P.X a d)) by ring]
  rw [abs_neg]
  calc
    |dBreve' P.X a (Ffun P.X a d + j) - dBreve' P.X a (Ffun P.X a d)|
        ≤ (300 * d ^ 7 / (P.X * a) ^ 2) * |j| := by
          simpa [sec7_ra_B3H, sec7_ra_dBreveD] using hH1
    _ = sec7_ra_B1SharpScaleAled 0 * |j| * d ^ 7 / (P.X * a) ^ 2 := by
          simp [sec7_ra_B1SharpScaleAled]
          ring

private theorem sec7_ra_B1_bound_sharp_aled_k1 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 1
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
      ≤ sec7_ra_B1SharpScaleAled 1 * |j| * d ^ 6 / (P.X * a) ^ 2 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  have hH1der := sec7_ra_B3H_hasDerivAt (P := P) (S := S) (a := a)
    (d := d) (j := j) (l := 1) (by norm_num) hAD ha_lo ha_hi hd hshift
  have hiter :
      iteratedDeriv 1
          (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
            dBreve' P.X a (Ffun P.X a t)) d =
        -(deriv (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d) := by
    have hB_eq :
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) =
          fun t => -sec7_ra_B3H P.X a j 1 t := by
      funext t
      simp [sec7_ra_B3H, sec7_ra_dBreveD]
      ring
    rw [iteratedDeriv_one, hB_eq]
    simpa using hH1der.neg.deriv
  have hF1 := (sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
    P.X_pos ha0 hd).1
  have hH2 := (sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose).2
  have hF1ub_nonneg : 0 ≤ 7 * P.X * a / d ^ 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) P.X_pos.le) ha0.le)
      (pow_nonneg hd.le 4)
  calc
    |iteratedDeriv 1
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
        = |deriv (fun t => Ffun P.X a t) d| * |sec7_ra_B3H P.X a j 2 d| := by
          rw [hiter, abs_neg, abs_mul]
    _ ≤ (7 * P.X * a / d ^ 4) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
          exact mul_le_mul hF1 hH2 (abs_nonneg _) hF1ub_nonneg
    _ = sec7_ra_B1SharpScaleAled 1 * |j| * d ^ 6 / (P.X * a) ^ 2 := by
          simp [sec7_ra_B1SharpScaleAled]
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring

private noncomputable def sec7_ra_B1E (P : Globals) (a j : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun d => -sec7_ra_B3H P.X a j 1 d
  | 1 => fun d =>
      -(iteratedDeriv 1 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d)
  | 2 => fun d =>
      -(iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 2 * sec7_ra_B3H P.X a j 3 d)
  | 3 => fun d =>
      -(iteratedDeriv 3 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d +
        3 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 3 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 3 * sec7_ra_B3H P.X a j 4 d)
  | 4 => fun d =>
      -(iteratedDeriv 4 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d +
        (4 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
            iteratedDeriv 3 (fun t => Ffun P.X a t) d +
          3 * iteratedDeriv 2 (fun t => Ffun P.X a t) d ^ 2) *
          sec7_ra_B3H P.X a j 3 d +
        6 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 2 *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 4 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 4 * sec7_ra_B3H P.X a j 5 d)
  | 5 => fun d =>
      -(iteratedDeriv 5 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 2 d +
        (5 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
            iteratedDeriv 4 (fun t => Ffun P.X a t) d +
          10 * iteratedDeriv 2 (fun t => Ffun P.X a t) d *
            iteratedDeriv 3 (fun t => Ffun P.X a t) d) *
          sec7_ra_B3H P.X a j 3 d +
        5 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
          (2 * iteratedDeriv 1 (fun t => Ffun P.X a t) d *
              iteratedDeriv 3 (fun t => Ffun P.X a t) d +
            3 * iteratedDeriv 2 (fun t => Ffun P.X a t) d ^ 2) *
          sec7_ra_B3H P.X a j 4 d +
        10 * iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 3 *
          iteratedDeriv 2 (fun t => Ffun P.X a t) d * sec7_ra_B3H P.X a j 5 d +
        iteratedDeriv 1 (fun t => Ffun P.X a t) d ^ 5 * sec7_ra_B3H P.X a j 6 d)
  | _ => fun _ => 0

private theorem sec7_ra_B1E_hasDerivAt {P : Globals} {a j r : ℝ} {m : ℕ}
    (ha : 0 < a) (hr : 0 < r) (hm : m < 5)
    (hH : ∀ l ≤ 5,
      HasDerivAt (sec7_ra_B3H P.X a j l)
        (iteratedDeriv 1 (fun t => Ffun P.X a t) r * sec7_ra_B3H P.X a j (l + 1) r) r) :
    HasDerivAt (sec7_ra_B1E P a j m) (sec7_ra_B1E P a j (m + 1) r) r := by
  interval_cases m
  · simpa [sec7_ra_B1E] using (hH 1 (by norm_num)).neg
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hmain := (hF1.mul hH2).neg
    convert hmain using 1
    simp [sec7_ra_B1E]
    ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hH3 := hH 3 (by norm_num)
    have hterm1 := hF2.mul hH2
    have hterm2 := (hF1.pow 2).mul hH3
    have hmain := (hterm1.add hterm2).neg
    convert hmain using 1
    simp [sec7_ra_B1E]
    ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hF3 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 3)
      ha hr (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hH3 := hH 3 (by norm_num)
    have hH4 := hH 4 (by norm_num)
    have hterm1 := hF3.mul hH2
    have hterm2 := ((hF1.mul hF2).mul hH3).const_mul 3
    have hterm3 := (hF1.pow 3).mul hH4
    have hmain := ((hterm1.add hterm2).add hterm3).neg
    convert hmain using 1
    all_goals
      first
      | funext x
        simp [sec7_ra_B1E]
        ring_nf
      | simp [sec7_ra_B1E]
        ring_nf
  · have hF1 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 1)
      ha hr (by norm_num)
    have hF2 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 2)
      ha hr (by norm_num)
    have hF3 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 3)
      ha hr (by norm_num)
    have hF4 := sec7_ra_Ffun_iter_hasDerivAt (P := P) (a := a) (r := r) (m := 4)
      ha hr (by norm_num)
    have hH2 := hH 2 (by norm_num)
    have hH3 := hH 3 (by norm_num)
    have hH4 := hH 4 (by norm_num)
    have hH5 := hH 5 (by norm_num)
    have hterm1 := hF4.mul hH2
    have hcoef2a := (hF1.mul hF3).const_mul 4
    have hcoef2b := (hF2.pow 2).const_mul 3
    have hterm2 := (hcoef2a.add hcoef2b).mul hH3
    have hcoef3 := ((hF1.pow 2).mul hF2).const_mul 6
    have hterm3 := hcoef3.mul hH4
    have hterm4 := (hF1.pow 4).mul hH5
    have hmain := (((hterm1.add hterm2).add hterm3).add hterm4).neg
    convert hmain using 1
    all_goals
      first
      | funext x
        simp [sec7_ra_B1E]
        ring_nf
      | simp [sec7_ra_B1E]
        ring_nf

private theorem sec7_ra_B1_iteratedDeriv_eq {P : Globals} {S : Scale P} {a d j : ℝ} {k : ℕ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (hshift : Ffun P.X a d + j ∈ sec7_tWin S) (hk : k ≤ 5) :
    iteratedDeriv k
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d =
      sec7_ra_B1E P a j k d := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  obtain ⟨s, hs_open, hds, hs_pos, hHchain⟩ :=
    sec7_ra_B3H_chain_open (P := P) (S := S) (a := a) (d := d) (j := j)
      hAD ha_lo ha_hi hd hshift
  have hEchain :
      ∀ m < 5, ∀ r ∈ s,
        HasDerivAt (sec7_ra_B1E P a j m) (sec7_ra_B1E P a j (m + 1) r) r := by
    intro m hm r hrs
    have hH' : ∀ l ≤ 5,
        HasDerivAt (sec7_ra_B3H P.X a j l)
          (iteratedDeriv 1 (fun t => Ffun P.X a t) r *
            sec7_ra_B3H P.X a j (l + 1) r) r := by
      intro l hl
      simpa [iteratedDeriv_one] using hHchain l hl r hrs
    exact sec7_ra_B1E_hasDerivAt (P := P) (a := a) (j := j) (r := r) (m := m)
      ha0 (hs_pos r hrs) hm hH'
  have hB_iter :
      iteratedDeriv k (sec7_ra_B1E P a j 0) d = sec7_ra_B1E P a j k d :=
    sec7_ra_iteratedDeriv_eq_of_chain (F := sec7_ra_B1E P a j) hs_open hEchain
      k hk d hds
  have hB_eq :
      (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
        dBreve' P.X a (Ffun P.X a t)) =
        sec7_ra_B1E P a j 0 := by
    funext t
    simp [sec7_ra_B1E, sec7_ra_B3H, sec7_ra_dBreveD]
    ring
  rw [hB_eq]
  exact hB_iter

private theorem sec7_ra_B1_bound_sharp_aled_k2 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 2
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
      ≤ sec7_ra_B1SharpScaleAled 2 * |j| * d ^ 5 / (P.X * a) ^ 2 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  have hiter :
      iteratedDeriv 2
          (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
            dBreve' P.X a (Ffun P.X a t)) d =
        -(F2 * H2 + F1 ^ 2 * H3) := by
    have h := sec7_ra_B1_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 2) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, H2, H3, sec7_ra_B1E, iteratedDeriv_one] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, _hF3, _hF4, _hF5⟩
  have hH2 := (sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose).2
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
  have hF1pow2 : |F1| ^ 2 ≤ (7 * P.X * a / d ^ 4) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 2
  have hterm1 : |F2 * H2| ≤
      (26 * P.X * a / d ^ 5) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF2 hH2 (abs_nonneg _) hF2ub_nonneg
  have hterm2 : |F1 ^ 2 * H3| ≤
      (7 * P.X * a / d ^ 4) ^ 2 * ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow2 hH3 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 2)
  calc
    |iteratedDeriv 2
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
        = |F2 * H2 + F1 ^ 2 * H3| := by rw [hiter, abs_neg]
    _ ≤ |F2 * H2| + |F1 ^ 2 * H3| := abs_add_le _ _
    _ ≤ (26 * P.X * a / d ^ 5) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 2 * ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
          exact add_le_add hterm1 hterm2
    _ = sec7_ra_B1SharpScaleAled 2 * |j| * d ^ 5 / (P.X * a) ^ 2 := by
          simp [sec7_ra_B1SharpScaleAled]
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring

private theorem sec7_ra_B1_bound_sharp_aled_k3 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 3
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
      ≤ sec7_ra_B1SharpScaleAled 3 * |j| * d ^ 4 / (P.X * a) ^ 2 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  have hiter :
      iteratedDeriv 3
          (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
            dBreve' P.X a (Ffun P.X a t)) d =
        -(F3 * H2 + 3 * F1 * F2 * H3 + F1 ^ 3 * H4) := by
    have h := sec7_ra_B1_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 3) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, H2, H3, H4, sec7_ra_B1E, iteratedDeriv_one] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, _hF4, _hF5⟩
  have hH2 := (sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose).2
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
  have hF1pow3 : |F1| ^ 3 ≤ (7 * P.X * a / d ^ 4) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hF1 3
  have hcoef2 : |3 * F1 * F2| ≤
      3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    gcongr
  have hcoef2_nonneg : 0 ≤ 3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hF1ub_nonneg) hF2ub_nonneg
  have hterm1 : |F3 * H2| ≤
      (128 * P.X * a / d ^ 6) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF3 hH2 (abs_nonneg _) hF3ub_nonneg
  have hterm2 : |3 * F1 * F2 * H3| ≤
      (3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5)) *
        ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef2 hH3 (abs_nonneg _) hcoef2_nonneg
  have hterm3 : |F1 ^ 3 * H4| ≤
      (7 * P.X * a / d ^ 4) ^ 3 * ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow3 hH4 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 3)
  calc
    |iteratedDeriv 3
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
        = |F3 * H2 + 3 * F1 * F2 * H3 + F1 ^ 3 * H4| := by rw [hiter, abs_neg]
    _ ≤ |F3 * H2| + |3 * F1 * F2 * H3| + |F1 ^ 3 * H4| := by
          linarith [abs_add_le (F3 * H2 + 3 * F1 * F2 * H3) (F1 ^ 3 * H4),
            abs_add_le (F3 * H2) (3 * F1 * F2 * H3)]
    _ ≤ (128 * P.X * a / d ^ 6) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (3 * (7 * P.X * a / d ^ 4) * (26 * P.X * a / d ^ 5)) *
          ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 3 * ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
          linarith [hterm1, hterm2, hterm3]
    _ = sec7_ra_B1SharpScaleAled 3 * |j| * d ^ 4 / (P.X * a) ^ 2 := by
          simp [sec7_ra_B1SharpScaleAled]
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring

private theorem sec7_ra_B1_bound_sharp_aled_k4 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 4
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
      ≤ sec7_ra_B1SharpScaleAled 4 * |j| * d ^ 3 / (P.X * a) ^ 2 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  let H5 : ℝ := sec7_ra_B3H P.X a j 5 d
  have hiter :
      iteratedDeriv 4
          (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
            dBreve' P.X a (Ffun P.X a t)) d =
        -(F4 * H2 + (4 * F1 * F3 + 3 * F2 ^ 2) * H3 +
          6 * F1 ^ 2 * F2 * H4 + F1 ^ 4 * H5) := by
    have h := sec7_ra_B1_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 4) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, H2, H3, H4, H5, sec7_ra_B1E, iteratedDeriv_one] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, _hF5⟩
  have hH2 := (sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose).2
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
  have hterm1 : |F4 * H2| ≤
      (800 * P.X * a / d ^ 7) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF4 hH2 (abs_nonneg _) hF4ub_nonneg
  have hterm2 : |(4 * F1 * F3 + 3 * F2 ^ 2) * H3| ≤
      (4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2) *
        ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul]
    have hcoef_nonneg : 0 ≤
        4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
          3 * (26 * P.X * a / d ^ 5) ^ 2 := by positivity
    exact mul_le_mul hcoef2 hH3 (abs_nonneg _) hcoef_nonneg
  have hterm3 : |6 * F1 ^ 2 * F2 * H4| ≤
      6 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) *
        ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    gcongr
  have hterm4 : |F1 ^ 4 * H5| ≤
      (7 * P.X * a / d ^ 4) ^ 4 * ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow4 hH5 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 4)
  calc
    |iteratedDeriv 4
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
        = |F4 * H2 + (4 * F1 * F3 + 3 * F2 ^ 2) * H3 +
            6 * F1 ^ 2 * F2 * H4 + F1 ^ 4 * H5| := by rw [hiter, abs_neg]
    _ ≤ |F4 * H2| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H3| +
        |6 * F1 ^ 2 * F2 * H4| + |F1 ^ 4 * H5| := by
          calc
            |F4 * H2 + (4 * F1 * F3 + 3 * F2 ^ 2) * H3 +
                6 * F1 ^ 2 * F2 * H4 + F1 ^ 4 * H5|
                ≤ |F4 * H2 + (4 * F1 * F3 + 3 * F2 ^ 2) * H3 +
                    6 * F1 ^ 2 * F2 * H4| + |F1 ^ 4 * H5| := abs_add_le _ _
            _ ≤ |F4 * H2| + |(4 * F1 * F3 + 3 * F2 ^ 2) * H3| +
                |6 * F1 ^ 2 * F2 * H4| + |F1 ^ 4 * H5| := by
                  linarith [abs_add_le (F4 * H2 + (4 * F1 * F3 + 3 * F2 ^ 2) * H3)
                    (6 * F1 ^ 2 * F2 * H4),
                    abs_add_le (F4 * H2) ((4 * F1 * F3 + 3 * F2 ^ 2) * H3)]
    _ ≤ (800 * P.X * a / d ^ 7) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (4 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2) *
          ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        6 * (7 * P.X * a / d ^ 4) ^ 2 * (26 * P.X * a / d ^ 5) *
          ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 4 * ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4]
    _ = sec7_ra_B1SharpScaleAled 4 * |j| * d ^ 3 / (P.X * a) ^ 2 := by
          simp [sec7_ra_B1SharpScaleAled]
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring

private theorem sec7_ra_B1_bound_sharp_aled_k5 {P : Globals} {S : Scale P} {a d j : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |sec7_ra_B3q P.X a j d - d| ≤ d / 100) :
    |iteratedDeriv 5
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
      ≤ sec7_ra_B1SharpScaleAled 5 * |j| * d ^ 2 / (P.X * a) ^ 2 := by
  have hApos : 0 < S.A := by
    unfold Scale.A
    exact mul_pos S.Δ_pos S.Ω_pos
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < S.A / 5) ha_lo
  let F1 : ℝ := deriv (fun t => Ffun P.X a t) d
  let F2 : ℝ := iteratedDeriv 2 (fun t => Ffun P.X a t) d
  let F3 : ℝ := iteratedDeriv 3 (fun t => Ffun P.X a t) d
  let F4 : ℝ := iteratedDeriv 4 (fun t => Ffun P.X a t) d
  let F5 : ℝ := iteratedDeriv 5 (fun t => Ffun P.X a t) d
  let H2 : ℝ := sec7_ra_B3H P.X a j 2 d
  let H3 : ℝ := sec7_ra_B3H P.X a j 3 d
  let H4 : ℝ := sec7_ra_B3H P.X a j 4 d
  let H5 : ℝ := sec7_ra_B3H P.X a j 5 d
  let H6 : ℝ := sec7_ra_B3H P.X a j 6 d
  have hiter :
      iteratedDeriv 5
          (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
            dBreve' P.X a (Ffun P.X a t)) d =
        -(F5 * H2 + (5 * F1 * F4 + 10 * F2 * F3) * H3 +
          5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4 +
          10 * F1 ^ 3 * F2 * H5 + F1 ^ 5 * H6) := by
    have h := sec7_ra_B1_iteratedDeriv_eq (P := P) (S := S) (a := a)
      (d := d) (j := j) (k := 5) hAD ha_lo ha_hi hd hshift (by norm_num)
    simpa [F1, F2, F3, F4, F5, H2, H3, H4, H5, H6, sec7_ra_B1E,
      iteratedDeriv_one] using h
  rcases sec7_ra_Ffun_upper_base_sharp (X := P.X) (a := a) (d := d)
      P.X_pos ha0 hd with ⟨hF1, hF2, hF3, hF4, hF5⟩
  have hH2 := (sec7_ra_B3H_bounds12_sharp_aled (P := P) (S := S) (a := a)
    (d := d) (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose).2
  have hH3 := sec7_ra_B3H_bound3_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH4 := sec7_ra_B3H_bound4_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hH5 := sec7_ra_B3H_bound5_sharp_aled (P := P) (S := S) (a := a) (d := d)
    (j := j) hAD ha_lo ha_hi hd ha2 hshift hclose
  have hF1lower : ∀ {z : ℝ}, (99 / 100 : ℝ) * d ≤ z → z ≤ (101 / 100 : ℝ) * d →
      P.X * a / d ^ 4 ≤ |deriv (fun t => Ffun P.X a t) z| := by
    intro z hzlo hzhi
    have hzpos : 0 < z := lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hzlo
    have hza_pos : 0 < z + a := by positivity
    rw [Ffun_deriv1_abs_eq (X := P.X) (a := a) (d := z) P.X_pos ha0 hzpos]
    have hQ_nonneg : 0 ≤ a ^ 2 + 3 * a * z + 3 * z ^ 2 := by positivity
    have ha_z : a ≤ (100 / 99 : ℝ) * z := by linarith [ha2, hzlo]
    have ha2z :
        a ^ 2 * z ≤ (((100 / 99 : ℝ) * z) ^ 2) * z := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0.le ha_z 2) hzpos.le
    have ha3 : a ^ 3 ≤ (((100 / 99 : ℝ) * z) ^ 3) :=
      pow_le_pow_left₀ ha0.le ha_z 3
    have hcube :
        (z + a) ^ 3 ≤
          (3 / 2 : ℝ) * z * (a ^ 2 + 3 * a * z + 3 * z ^ 2) := by
      have hconst : (2 * (100 / 99 : ℝ) ^ 3 + 3 * (100 / 99 : ℝ) ^ 2) ≤ 7 := by
        norm_num
      have hconstz :
          (2 * (100 / 99 : ℝ) ^ 3 + 3 * (100 / 99 : ℝ) ^ 2) * z ^ 3 ≤
            7 * z ^ 3 := by
        exact mul_le_mul_of_nonneg_right hconst (pow_nonneg hzpos.le 3)
      have hpos_term : 0 ≤ 3 * a * z ^ 2 := by positivity
      have hnonneg :
          0 ≤ 3 * z * (a ^ 2 + 3 * a * z + 3 * z ^ 2) -
            2 * (z + a) ^ 3 := by
        nlinarith only [ha2z, ha3, hconstz, hpos_term]
      linarith
    have hz4_le : z ^ 4 ≤ (((101 / 100 : ℝ) * d) ^ 4) :=
      pow_le_pow_left₀ hzpos.le hzhi 4
    have hden_core :
        z ^ 3 * (z + a) ^ 3 ≤
          2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by
      calc
        z ^ 3 * (z + a) ^ 3
            ≤ z ^ 3 * ((3 / 2 : ℝ) * z *
                (a ^ 2 + 3 * a * z + 3 * z ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hcube (pow_nonneg hzpos.le 3)
        _ = (3 / 2 : ℝ) * z ^ 4 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) := by ring
        _ ≤ (3 / 2 : ℝ) * (((101 / 100 : ℝ) * d) ^ 4) *
              (a ^ 2 + 3 * a * z + 3 * z ^ 2) := by
              have hmul := mul_le_mul_of_nonneg_right hz4_le hQ_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 3 / 2)
        _ = ((3 / 2 : ℝ) * (101 / 100 : ℝ) ^ 4) *
              (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by ring
        _ ≤ 2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 := by
              have hconst : (3 / 2 : ℝ) * (101 / 100 : ℝ) ^ 4 ≤ 2 := by
                norm_num
              have hright : 0 ≤ (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4 :=
                mul_nonneg hQ_nonneg (pow_nonneg hd.le 4)
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_right hconst hright
    rw [div_le_div_iff₀ (pow_pos hd 4) (by positivity : 0 < z ^ 3 * (z + a) ^ 3)]
    calc
      P.X * a * (z ^ 3 * (z + a) ^ 3)
          ≤ P.X * a * (2 * (a ^ 2 + 3 * a * z + 3 * z ^ 2) * d ^ 4) :=
            mul_le_mul_of_nonneg_left hden_core (mul_pos P.X_pos ha0).le
      _ = (2 * P.X * a * (a ^ 2 + 3 * a * z + 3 * z ^ 2)) * d ^ 4 := by ring
  have hqdiff1 : |sec7_ra_B3q P.X a j d - d| ≤ |j| * d ^ 4 / (P.X * a) := by
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
      field_simp [P.X_pos.ne', ha0.ne', hd.ne']
    by_cases hsame : qd = d
    · rw [hsame, sub_self, abs_zero]
      exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hd.le 4))
        (mul_pos P.X_pos ha0).le
    have hprod : P.X * a / d ^ 4 * |qd - d| ≤ |j| := by
      rcases lt_or_gt_of_ne hsame with hlt | hlt
      · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
          sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := qd) (q := d) ha0
            (lt_of_lt_of_le (by positivity : 0 < (99 / 100 : ℝ) * d) hqwin.1) hlt
        have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := le_trans hqwin.1 (le_of_lt hc_lo)
        have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) (by linarith)
        have hder := hF1lower hc_win_lo hc_win_hi
        have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
          have hj : j = -(Ffun P.X a d - Ffun P.X a qd) := by
            rw [hqspec]
            ring
          rw [hj, abs_neg, hc_mvt, abs_mul, abs_sub_comm]
        rw [hj_abs]
        exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
      · obtain ⟨c, hc_lo, hc_hi, hc_mvt⟩ :=
          sec7_ra_Ffun_mvt_local (X := P.X) (a := a) (p := d) (q := qd) ha0 hd hlt
        have hc_win_lo : (99 / 100 : ℝ) * d ≤ c := by linarith
        have hc_win_hi : c ≤ (101 / 100 : ℝ) * d := le_trans (le_of_lt hc_hi) hqwin.2
        have hder := hF1lower hc_win_lo hc_win_hi
        have hj_abs : |j| = |deriv (fun t => Ffun P.X a t) c| * |qd - d| := by
          have hj : j = Ffun P.X a qd - Ffun P.X a d := by
            rw [hqspec]
            ring
          rw [hj, hc_mvt, abs_mul]
        rw [hj_abs]
        exact mul_le_mul_of_nonneg_right hder (abs_nonneg _)
    calc
      |sec7_ra_B3q P.X a j d - d| = |qd - d| := by rw [hqd_def]
      _ ≤ |j| / (P.X * a / d ^ 4) := by
        rw [le_div_iff₀ hCpos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      _ = |j| * d ^ 4 / (P.X * a) := hscale_eq
  have hH6 : |H6| ≤ (1500000 * d ^ 22 / (P.X * a) ^ 7) * |j| := by
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
        H6 = sec7_ra_dBreve6ImageK P.X a qd - sec7_ra_dBreve6ImageK P.X a d := by
      change sec7_ra_B3H P.X a j 6 d =
        sec7_ra_dBreve6ImageK P.X a qd - sec7_ra_dBreve6ImageK P.X a d
      rw [sec7_ra_B3H, sec7_ra_dBreveD]
      rw [show Ffun P.X a d + j = Ffun P.X a qd by rw [hqspec]]
      rw [sec7_ra_dBreve6ImageK_eq (X := P.X) (a := a) (z := qd) P.X_pos ha0 hqpos]
      rw [sec7_ra_dBreve6ImageK_eq (X := P.X) (a := a) (z := d) P.X_pos ha0 hd]
    have hL_nonneg : 0 ≤ L := by
      rw [hL_def]
      positivity
    calc
      |H6| = |sec7_ra_dBreve6ImageK P.X a qd - sec7_ra_dBreve6ImageK P.X a d| := by
        rw [hH_eq]
      _ = |sec7_ra_dBreve6ImageK P.X a d - sec7_ra_dBreve6ImageK P.X a qd| := by
        rw [abs_sub_comm]
      _ ≤ L * |d - qd| := hKdiff
      _ = L * |qd - d| := by rw [abs_sub_comm]
      _ ≤ L * (|j| * d ^ 4 / (P.X * a)) := by
        have hqdiff_qd : |qd - d| ≤ |j| * d ^ 4 / (P.X * a) := by
          simpa [hqd_def] using hqdiff1
        exact mul_le_mul_of_nonneg_left hqdiff_qd hL_nonneg
      _ = (1500000 * d ^ 22 / (P.X * a) ^ 7) * |j| := by
        rw [hL_def]
        field_simp [P.X_pos.ne', ha0.ne', hd.ne']
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
  have hterm1 : |F5 * H2| ≤
      (6000 * P.X * a / d ^ 8) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hF5 hH2 (abs_nonneg _) hF5ub_nonneg
  have hterm2 : |(5 * F1 * F4 + 10 * F2 * F3) * H3| ≤
      (5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
          10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6)) *
        ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef2 hH3 (abs_nonneg _) hcoef2_nonneg
  have hterm3 : |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4| ≤
      (5 * (7 * P.X * a / d ^ 4) *
          (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
            3 * (26 * P.X * a / d ^ 5) ^ 2)) *
        ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef3 hH4 (abs_nonneg _) hcoef3_nonneg
  have hterm4 : |10 * F1 ^ 3 * F2 * H5| ≤
      (10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5)) *
        ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) := by
    rw [abs_mul]
    exact mul_le_mul hcoef4 hH5 (abs_nonneg _) hcoef4_nonneg
  have hterm5 : |F1 ^ 5 * H6| ≤
      (7 * P.X * a / d ^ 4) ^ 5 * ((1500000 * d ^ 22 / (P.X * a) ^ 7) * |j|) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hF1pow5 hH6 (abs_nonneg _) (pow_nonneg hF1ub_nonneg 5)
  calc
    |iteratedDeriv 5
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d|
        = |F5 * H2 + (5 * F1 * F4 + 10 * F2 * F3) * H3 +
            5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4 +
            10 * F1 ^ 3 * F2 * H5 + F1 ^ 5 * H6| := by rw [hiter, abs_neg]
    _ ≤ |F5 * H2| + |(5 * F1 * F4 + 10 * F2 * F3) * H3| +
        |5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4| +
        |10 * F1 ^ 3 * F2 * H5| + |F1 ^ 5 * H6| := by
          linarith [abs_add_le
            (F5 * H2 + (5 * F1 * F4 + 10 * F2 * F3) * H3 +
              5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4 +
              10 * F1 ^ 3 * F2 * H5) (F1 ^ 5 * H6),
            abs_add_le
              (F5 * H2 + (5 * F1 * F4 + 10 * F2 * F3) * H3 +
                5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4)
              (10 * F1 ^ 3 * F2 * H5),
            abs_add_le
              (F5 * H2 + (5 * F1 * F4 + 10 * F2 * F3) * H3)
              (5 * F1 * (2 * F1 * F3 + 3 * F2 ^ 2) * H4),
            abs_add_le (F5 * H2) ((5 * F1 * F4 + 10 * F2 * F3) * H3)]
    _ ≤ (6000 * P.X * a / d ^ 8) * ((200 * d ^ 10 / (P.X * a) ^ 3) * |j|) +
        (5 * (7 * P.X * a / d ^ 4) * (800 * P.X * a / d ^ 7) +
            10 * (26 * P.X * a / d ^ 5) * (128 * P.X * a / d ^ 6)) *
          ((3000 * d ^ 13 / (P.X * a) ^ 4) * |j|) +
        (5 * (7 * P.X * a / d ^ 4) *
            (2 * (7 * P.X * a / d ^ 4) * (128 * P.X * a / d ^ 6) +
              3 * (26 * P.X * a / d ^ 5) ^ 2)) *
          ((50000 * d ^ 16 / (P.X * a) ^ 5) * |j|) +
        (10 * (7 * P.X * a / d ^ 4) ^ 3 * (26 * P.X * a / d ^ 5)) *
          ((1500000 * d ^ 19 / (P.X * a) ^ 6) * |j|) +
        (7 * P.X * a / d ^ 4) ^ 5 *
          ((1500000 * d ^ 22 / (P.X * a) ^ 7) * |j|) := by
          linarith [hterm1, hterm2, hterm3, hterm4, hterm5]
    _ = 165850540000 * |j| * d ^ 2 / (P.X * a) ^ 2 := by
          field_simp [P.X_pos.ne', ha0.ne', hd.ne']
          ring
    _ ≤ sec7_ra_B1SharpScaleAled 5 * |j| * d ^ 2 / (P.X * a) ^ 2 := by
          simp [sec7_ra_B1SharpScaleAled]
          have hnum :
              165850540000 * |j| * d ^ 2 ≤ 191061040000 * |j| * d ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by norm_num : (165850540000 : ℝ) ≤ 191061040000) (abs_nonneg j))
              (pow_nonneg hd.le 2)
          exact div_le_div_of_nonneg_right hnum (sq_nonneg _)

theorem sec7_ra_B1_bound_sharp_aled {P : Globals} {S : Scale P} {a d j : ℝ} {k : ℕ}
    (hk : k ≤ 5)
    (hAD : 10 * S.A ≤ S.D) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hd : 0 < d) (ha2 : a ≤ d)
    (hshift : Ffun P.X a d + j ∈ sec7_tWin S)
    (hclose : |dBreve P.X a (Ffun P.X a d + j) - d| ≤ d / 100) :
    |iteratedDeriv k
        (fun t => -dBreve' P.X a (Ffun P.X a t + j) +
          dBreve' P.X a (Ffun P.X a t)) d| ≤
      match k with
      | 0 => (300 : ℝ) * |j| * d ^ 7 / (P.X * a) ^ 2
      | 1 => (1400 : ℝ) * |j| * d ^ 6 / (P.X * a) ^ 2
      | 2 => (152200 : ℝ) * |j| * d ^ 5 / (P.X * a) ^ 2
      | 3 => (18813600 : ℝ) * |j| * d ^ 4 / (P.X * a) ^ 2
      | 4 => (4000696000 : ℝ) * |j| * d ^ 3 / (P.X * a) ^ 2
      | 5 => (191061040000 : ℝ) * |j| * d ^ 2 / (P.X * a) ^ 2
      | _ => 0 := by
  have hclose' : |sec7_ra_B3q P.X a j d - d| ≤ d / 100 := by
    simpa [sec7_ra_B3q] using hclose
  interval_cases k
  · simpa [sec7_ra_B1SharpScaleAled] using
      sec7_ra_B1_bound_sharp_aled_k0 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B1SharpScaleAled] using
      sec7_ra_B1_bound_sharp_aled_k1 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B1SharpScaleAled] using
      sec7_ra_B1_bound_sharp_aled_k2 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B1SharpScaleAled] using
      sec7_ra_B1_bound_sharp_aled_k3 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B1SharpScaleAled] using
      sec7_ra_B1_bound_sharp_aled_k4 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'
  · simpa [sec7_ra_B1SharpScaleAled] using
      sec7_ra_B1_bound_sharp_aled_k5 (P := P) (S := S) (a := a) (d := d) (j := j)
        hAD ha_lo ha_hi hd ha2 hshift hclose'


end Squarefree
