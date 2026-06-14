import Squarefree.Bracket.Sec7MonExpData

/-!
# §7 N11 support layer — Leibniz-graded families and envelope smallness

Machinery for `sec7_err_deriv_bound` (N11, `Sec7ErrBound.lean`): an `EqOn`-variant of the
graded chain identification, constant families and order-2 Leibniz product families with
their chains and value bounds, a uniform value bound for the graded power monomials, and
the two envelope-derived smallness facts the N11 ledger uses:
* `sec7_hSum_R_small` — `h_Σ·10¹⁴⁹ ≤ R`, from `n6·n7 = R⁴` (exact monomial identity;
  log-free entries only, so no `X ≥ 1` is needed);
* `sec7_relErr_le` — `(Ω/H)·10¹⁵⁰ ≤ 1`, from `n6` and `R·T₁ = A² > 1`.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

/-- **`EqOn` variant of the graded chain identification**: if `f` agrees with `F 0` on an
open set `s` and `F` is a derivative chain on `s`, then `iteratedDeriv m f = F m` on `s`. -/
theorem sec7_iteratedDeriv_eq_of_chain_eqOn {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) {n : ℕ} (h0 : ∀ x ∈ s, f x = F 0 x)
    (hd : ∀ m < n, ∀ r ∈ s, HasDerivAt (F m) (F (m + 1) r) r) :
    ∀ m ≤ n, ∀ r ∈ s, iteratedDeriv m f r = F m r := by
  intro m
  induction m with
  | zero => intro _ r hr; simpa using h0 r hr
  | succ m ih =>
    intro hm r hr
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m f =ᶠ[nhds r] F m :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hr)
        (fun x hx => ih (le_of_lt (Nat.lt_of_succ_le hm)) x hx)
    rw [hev.deriv_eq]
    exact (hd m (Nat.lt_of_succ_le hm) r hr).deriv

/-! ## Constant families -/

/-- The graded family of a constant: value `c` at grade 0, zero above. -/
def sec7_constF (c : ℝ) : ℕ → ℝ → ℝ := fun k _ => if k = 0 then c else 0

@[simp] theorem sec7_constF_zero (c : ℝ) (t : ℝ) : sec7_constF c 0 t = c := rfl

theorem sec7_constF_deriv (c : ℝ) (m : ℕ) (r : ℝ) :
    HasDerivAt (sec7_constF c m) (sec7_constF c (m + 1) r) r := by
  have : sec7_constF c (m + 1) r = 0 := by simp [sec7_constF]
  rw [this]
  exact hasDerivAt_const r _

theorem sec7_constF_bound {c B R : ℝ} (hc : |c| ≤ B) (hR : 0 < R) (k : ℕ) (t : ℝ) :
    |sec7_constF c k t| ≤ B / R ^ k := by
  have hB : 0 ≤ B := le_trans (abs_nonneg c) hc
  cases k with
  | zero => simpa [sec7_constF] using hc
  | succ k =>
    simp only [sec7_constF, if_neg (Nat.succ_ne_zero k), abs_zero]
    positivity

/-! ## Order-2 Leibniz product families -/

/-- The Leibniz product family: grade `k` is `∑_{i≤k} C(k,i)·F_i·G_{k−i}`. -/
noncomputable def sec7_leib (F G : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun k t =>
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * F i t * G (k - i) t

theorem sec7_leib_zero (F G : ℕ → ℝ → ℝ) (t : ℝ) :
    sec7_leib F G 0 t = F 0 t * G 0 t := by
  simp [sec7_leib]

private theorem sec7_leib_one (F G : ℕ → ℝ → ℝ) (t : ℝ) :
    sec7_leib F G 1 t = F 0 t * G 1 t + F 1 t * G 0 t := by
  simp [sec7_leib, Finset.sum_range_succ]

private theorem sec7_leib_two (F G : ℕ → ℝ → ℝ) (t : ℝ) :
    sec7_leib F G 2 t = F 0 t * G 2 t + 2 * (F 1 t * G 1 t) + F 2 t * G 0 t := by
  simp [sec7_leib, Finset.sum_range_succ]
  ring

/-- The Leibniz family is a derivative chain (order 2) on any set where both factor
families are chains. -/
theorem sec7_leib_deriv {F G : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ m < 2, ∀ r ∈ s, HasDerivAt (F m) (F (m + 1) r) r)
    (hG : ∀ m < 2, ∀ r ∈ s, HasDerivAt (G m) (G (m + 1) r) r) :
    ∀ m < 2, ∀ r ∈ s, HasDerivAt (sec7_leib F G m) (sec7_leib F G (m + 1) r) r := by
  intro m hm r hr
  interval_cases m
  · -- grade 0 → 1
    have h := (hF 0 (by norm_num) r hr).mul (hG 0 (by norm_num) r hr)
    have hfun : (fun t => F 0 t * G 0 t) = sec7_leib F G 0 := by
      funext t; rw [sec7_leib_zero]
    have hval : F 1 r * G 0 r + F 0 r * G 1 r = sec7_leib F G 1 r := by
      rw [sec7_leib_one]; ring
    rw [← hfun, ← hval]
    exact h
  · -- grade 1 → 2
    have h1 := (hF 0 (by norm_num) r hr).mul (hG 1 (by norm_num) r hr)
    have h2 := (hF 1 (by norm_num) r hr).mul (hG 0 (by norm_num) r hr)
    have h := h1.add h2
    have hfun : (fun t => F 0 t * G 1 t + F 1 t * G 0 t) = sec7_leib F G 1 := by
      funext t; rw [sec7_leib_one]
    have hval : F 1 r * G 1 r + F 0 r * G 2 r + (F 2 r * G 0 r + F 1 r * G 1 r) =
        sec7_leib F G 2 r := by
      rw [sec7_leib_two]; ring
    rw [← hfun, ← hval]
    exact h

/-- Value bound for the Leibniz family from uniform graded factor bounds:
`|F_k| ≤ a/R^k`, `|G_k| ≤ b/R^k` (`k ≤ 2`) give `|leib m| ≤ 4ab/R^m` (`m ≤ 2`). -/
theorem sec7_leib_bound {F G : ℕ → ℝ → ℝ} {R a b : ℝ} {t : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hFb : ∀ k ≤ 2, |F k t| ≤ a / R ^ k) (hGb : ∀ k ≤ 2, |G k t| ≤ b / R ^ k) :
    ∀ m ≤ 2, |sec7_leib F G m t| ≤ 4 * (a * b) / R ^ m := by
  have key : ∀ i j : ℕ, i + j ≤ 2 → |F i t * G j t| ≤ a * b / R ^ (i + j) := by
    intro i j hij
    rw [abs_mul, pow_add]
    have h1 := hFb i (by omega)
    have h2 := hGb j (by omega)
    have hF0 : 0 ≤ |F i t| := abs_nonneg _
    have hG0 : 0 ≤ |G j t| := abs_nonneg _
    have hRi : 0 < R ^ i := pow_pos hR i
    have hRj : 0 < R ^ j := pow_pos hR j
    calc |F i t| * |G j t| ≤ (a / R ^ i) * (b / R ^ j) := by
          exact mul_le_mul h1 h2 hG0 (by positivity)
      _ = a * b / (R ^ i * R ^ j) := by field_simp
  intro m hm
  have hRm : 0 < R ^ m := pow_pos hR m
  rw [mul_div_assoc]
  interval_cases m
  · rw [sec7_leib_zero]
    have k1 : |F 0 t * G 0 t| ≤ a * b / R ^ 0 := key 0 0 (by norm_num)
    have hab : 0 ≤ a * b / R ^ 0 := by positivity
    linarith
  · rw [sec7_leib_one]
    have k1 : |F 0 t * G 1 t| ≤ a * b / R ^ 1 := key 0 1 (by norm_num)
    have k2 : |F 1 t * G 0 t| ≤ a * b / R ^ 1 := key 1 0 (by norm_num)
    have hab : 0 ≤ a * b / R ^ 1 := by positivity
    calc |F 0 t * G 1 t + F 1 t * G 0 t| ≤ |F 0 t * G 1 t| + |F 1 t * G 0 t| :=
          abs_add_le _ _
      _ ≤ 4 * (a * b / R ^ 1) := by linarith
  · rw [sec7_leib_two]
    have k1 : |F 0 t * G 2 t| ≤ a * b / R ^ 2 := key 0 2 (by norm_num)
    have k2 : |F 1 t * G 1 t| ≤ a * b / R ^ 2 := key 1 1 (by norm_num)
    have k3 : |F 2 t * G 0 t| ≤ a * b / R ^ 2 := key 2 0 (by norm_num)
    have hab : 0 ≤ a * b / R ^ 2 := by positivity
    calc |F 0 t * G 2 t + 2 * (F 1 t * G 1 t) + F 2 t * G 0 t|
        ≤ |F 0 t * G 2 t + 2 * (F 1 t * G 1 t)| + |F 2 t * G 0 t| := abs_add_le _ _
      _ ≤ |F 0 t * G 2 t| + |2 * (F 1 t * G 1 t)| + |F 2 t * G 0 t| := by
          linarith [abs_add_le (F 0 t * G 2 t) (2 * (F 1 t * G 1 t))]
      _ = |F 0 t * G 2 t| + 2 * |F 1 t * G 1 t| + |F 2 t * G 0 t| := by
          rw [abs_mul]; norm_num
      _ ≤ 4 * (a * b / R ^ 2) := by linarith

/-! ## Uniform value bound for the graded power monomials -/

/-- Value bound on the wide window with a banked numeric cap `K` for
`|aprod α k| · (2cWin)^{(k:ℝ)−α}`. -/
theorem sec7_powMonD_val_bound {P : Globals} {S : Scale P} {W c α : ℝ} {k : ℕ} {K : ℝ}
    (hαk : α - (k : ℝ) ≤ 0)
    (hK : |sec7_aprod α k| * (2 * sec7_cWin) ^ ((k : ℝ) - α) ≤ K)
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    {x : ℝ} (hx : x ∈ sec7_rWinWide S W) :
    |sec7_powMonD S.R c α k x| ≤ |c| * K / S.R ^ k := by
  have hR : 0 < S.R := sec7_R_pos S
  have h := sec7_powMonD_wide_bound (c := c) (α := α) (k := k) hαk hpad hx
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hRk : 0 < S.R ^ k := pow_pos hR k
  calc |sec7_powMonD S.R c α k x|
      ≤ |c| * |sec7_aprod α k| / S.R ^ k * (2 * sec7_cWin) ^ ((k : ℝ) - α) := h
    _ = |c| * (|sec7_aprod α k| * (2 * sec7_cWin) ^ ((k : ℝ) - α)) / S.R ^ k := by
        ring
    _ ≤ |c| * K / S.R ^ k := by gcongr

/-! ## Envelope smallness (log-free entries only) -/

/-- `W ≥ 1` from the shift box. -/
theorem sec7_W_ge_one {W : ℝ} {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    (1 : ℝ) ≤ W := by
  have h1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hbox.1.1
  linarith [hbox.1.2]

/-- `h_Σ ≤ 3W⁴` from the shift box (`W ≥ 1`). -/
theorem sec7_hSum_le_3W4 {W : ℝ} {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_hSum h₁ h₂ h₃ ≤ 3 * W ^ 4 := by
  have hW : (1 : ℝ) ≤ W := sec7_W_ge_one hbox
  have hW14 : W ≤ W ^ 4 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have hW24 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW (by omega)
  have e1 : (h₁ : ℝ) ≤ W ^ 4 := le_trans hbox.1.2 hW14
  have e2 : (h₂ : ℝ) ≤ W ^ 4 := le_trans hbox.2.1.2 hW24
  have e3 : (h₃ : ℝ) ≤ W ^ 4 := hbox.2.2.2
  unfold sec7_hSum
  linarith

/-- **N11 smallness 1** (envelope `n6·n7 = R⁴`, exact): `h_Σ · 10¹⁴⁹ ≤ R`. -/
theorem sec7_hSum_R_small {P : Globals} {S : Scale P} {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (Env : Sec7Envelope P S W) (hbox : sec7_shiftBox W h₁ h₂ h₃) :
    sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ S.R := by
  have hW : (1 : ℝ) ≤ W := sec7_W_ge_one hbox
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hx : 0 < S.x := by unfold Scale.x; positivity
  have hR : 0 < S.R := sec7_R_pos S
  -- n6 · n7, after cancelling Ω⁴ > 0:  envC2² W⁸⁴ ≤ H²x²G⁴Ω¹²
  have h67 : sec7_envC2 ^ 2 * W ^ 84 ≤ P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := by
    have h6 := Env.n6
    have h7 := Env.n7
    have hC0 : (0:ℝ) ≤ sec7_envC2 := sec7_envC2_pos.le
    have hprod : (sec7_envC2 * (W ^ 30 * S.Ω ^ 4)) * (sec7_envC2 * W ^ 54) ≤
        (P.H * S.x) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) := by
      have hr0 : 0 ≤ sec7_envC2 * W ^ 54 :=
        mul_nonneg hC0 (pow_nonneg (le_trans zero_le_one hW) 54)
      exact mul_le_mul h6 h7 hr0 (by positivity)
    have h84 : (sec7_envC2 ^ 2 * W ^ 84) * S.Ω ^ 4 ≤
        (P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12) * S.Ω ^ 4 := by
      calc (sec7_envC2 ^ 2 * W ^ 84) * S.Ω ^ 4
          = (sec7_envC2 * (W ^ 30 * S.Ω ^ 4)) * (sec7_envC2 * W ^ 54) := by ring
        _ ≤ (P.H * S.x) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) := hprod
        _ = (P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12) * S.Ω ^ 4 := by ring
    exact le_of_mul_le_mul_right h84 (by positivity)
  -- identity: H²x²G⁴Ω¹² = R⁴
  have hid : P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 = S.R ^ 4 := by
    unfold Scale.x Scale.R
    field_simp
  -- W²⁴ ≤ W⁸⁴ and (10¹⁵⁰W⁶)⁴ = envC2²W²⁴
  have hWmono : W ^ 24 ≤ W ^ 84 := pow_le_pow_right₀ hW (by omega)
  have hkey : ((10:ℝ) ^ 150 * W ^ 6) ^ 4 ≤ S.R ^ 4 := by
    have hC : sec7_envC2 ^ 2 = ((10:ℝ) ^ 150) ^ 4 := by
      rw [sec7_envC2, ← pow_mul, ← pow_mul]
    have hC2 : (0:ℝ) ≤ sec7_envC2 ^ 2 := pow_nonneg sec7_envC2_pos.le 2
    calc ((10:ℝ) ^ 150 * W ^ 6) ^ 4 = sec7_envC2 ^ 2 * W ^ 24 := by
          rw [hC]; ring
      _ ≤ sec7_envC2 ^ 2 * W ^ 84 := mul_le_mul_of_nonneg_left hWmono hC2
      _ ≤ P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := h67
      _ = S.R ^ 4 := hid
  have hroot : (10:ℝ) ^ 150 * W ^ 6 ≤ S.R := by
    exact le_of_pow_le_pow_left₀ (by norm_num) hR.le hkey
  -- conclude via h_Σ ≤ 3W⁴ ≤ 3W⁶
  have hh3 : sec7_hSum h₁ h₂ h₃ ≤ 3 * W ^ 6 := by
    have := sec7_hSum_le_3W4 hbox
    have hW46 : W ^ 4 ≤ W ^ 6 := pow_le_pow_right₀ hW (by omega)
    linarith
  have hc149 : (0:ℝ) < 10 ^ 149 := pow_pos (by norm_num) 149
  have hW6 : (0:ℝ) ≤ W ^ 6 := pow_nonneg (le_trans zero_le_one hW) 6
  calc sec7_hSum h₁ h₂ h₃ * 10 ^ 149 ≤ 3 * W ^ 6 * 10 ^ 149 :=
        mul_le_mul_of_nonneg_right hh3 hc149.le
    _ ≤ (10:ℝ) ^ 150 * W ^ 6 := by
        have h10 : (10:ℝ) ^ 150 = 10 ^ 149 * 10 := by rw [← pow_succ]
        rw [h10]
        calc 3 * W ^ 6 * 10 ^ 149 = (3 * 10 ^ 149) * W ^ 6 := by ring
          _ ≤ (10 ^ 149 * 10) * W ^ 6 := by
              apply mul_le_mul_of_nonneg_right _ hW6
              linarith
    _ ≤ S.R := hroot

/-- **N11 smallness 2** (envelope `n6` + `R·T₁ = A² > 1`): `(Ω/H) · 10¹⁵⁰ ≤ 1`. -/
theorem sec7_relErr_le {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_relErr P S * 10 ^ 150 ≤ 1 := by
  have hH := P.H_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hC : 0 < sec7_envC2 := sec7_envC2_pos
  -- n6 with W³⁰ ≥ 1: envC2·Ω⁴ ≤ Hx
  have hn6 : sec7_envC2 * S.Ω ^ 4 ≤ P.H * S.x := by
    have h6 := Env.n6
    have hW30 : (1:ℝ) ≤ W ^ 30 := one_le_pow₀ hW
    have h0 : 0 ≤ sec7_envC2 * S.Ω ^ 4 :=
      mul_nonneg hC.le (pow_nonneg hΩ.le 4)
    calc sec7_envC2 * S.Ω ^ 4 ≤ sec7_envC2 * S.Ω ^ 4 * W ^ 30 :=
          le_mul_of_one_le_right h0 hW30
      _ = sec7_envC2 * (W ^ 30 * S.Ω ^ 4) := by ring
      _ ≤ P.H * S.x := h6
  -- Hx·Δ² = H²
  have hHx : P.H * S.x * S.Δ ^ 2 = P.H ^ 2 := by
    unfold Scale.x
    field_simp
  -- Δ²Ω² = R·T₁ > 1
  have hA : 1 < S.Δ ^ 2 * S.Ω ^ 2 := by
    have h1 := Env.R_gt_one
    have h2 := Env.T1_gt_one
    have h3 : 1 < S.R * S.T₁ := by nlinarith
    have h4 : S.R * S.T₁ = S.Δ ^ 2 * S.Ω ^ 2 := by
      rw [sec7_R_mul_T₁ S]; unfold Scale.A; ring
    rw [h4] at h3; exact h3
  -- envC2·Ω² ≤ envC2·Ω⁴Δ² ≤ H²
  have hkey : sec7_envC2 * S.Ω ^ 2 ≤ P.H ^ 2 := by
    have h1 : S.Ω ^ 2 ≤ S.Ω ^ 4 * S.Δ ^ 2 := by
      have h0 : (0:ℝ) ≤ S.Ω ^ 2 := pow_nonneg hΩ.le 2
      have := le_mul_of_one_le_right h0 hA.le
      calc S.Ω ^ 2 ≤ S.Ω ^ 2 * (S.Δ ^ 2 * S.Ω ^ 2) := this
        _ = S.Ω ^ 4 * S.Δ ^ 2 := by ring
    have h2 : sec7_envC2 * (S.Ω ^ 4 * S.Δ ^ 2) ≤ P.H ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn6 (pow_nonneg hΔ.le 2)
      calc sec7_envC2 * (S.Ω ^ 4 * S.Δ ^ 2) = sec7_envC2 * S.Ω ^ 4 * S.Δ ^ 2 := by
            ring
        _ ≤ P.H * S.x * S.Δ ^ 2 := this
        _ = P.H ^ 2 := hHx
    calc sec7_envC2 * S.Ω ^ 2 ≤ sec7_envC2 * (S.Ω ^ 4 * S.Δ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hC.le
      _ ≤ P.H ^ 2 := h2
  -- square root
  have hΩH : (10:ℝ) ^ 150 * S.Ω ≤ P.H := by
    have hsq : ((10:ℝ) ^ 150 * S.Ω) ^ 2 ≤ P.H ^ 2 := by
      have hCid : sec7_envC2 = ((10:ℝ) ^ 150) ^ 2 := by
        rw [sec7_envC2, ← pow_mul]
      calc ((10:ℝ) ^ 150 * S.Ω) ^ 2 = sec7_envC2 * S.Ω ^ 2 := by rw [hCid]; ring
        _ ≤ P.H ^ 2 := hkey
    exact le_of_pow_le_pow_left₀ (by norm_num) hH.le hsq
  -- conclude for relErr = Ω/H
  unfold sec7_relErr
  rw [div_mul_eq_mul_div, div_le_one hH]
  linarith

end Squarefree
