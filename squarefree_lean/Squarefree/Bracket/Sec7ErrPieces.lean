import Squarefree.Bracket.Sec7ErrAux

/-!
# §7 N11 piece layer — error/monomial families of the eq-(7.5) remainder

N11-internal (only `Sec7ErrFactors.lean`/`Sec7ErrBound.lean` should use these): the
chain-transport lemmas (wide → mid window), the banked numeric caps for the power
monomials, the graded error/monomial families of the five differenced expansions
(md 1607–33) built from the `Sec7MonExp` witness chains `f1C/f2C/f3C`, and their
derivative chains on the open mid window.  Value bounds live in `Sec7ErrFactors.lean`.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

section Pieces

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a}
  {j h₁ h₂ h₃ : ℤ} {ξ₁ ξ₂ ξ₃ : ℝ}

/-! ## Chain transport from the wide window to the mid window -/

/-- Base-point derivative: a wide-window chain differentiates at any point displaced
from the mid window by at most `3h_Σ` (under `hshift`). -/
theorem sec7E_basePt {F : ℕ → ℝ → ℝ}
    (hF : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (F m) (F (m + 1) r) r)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {k : ℕ} (hk : k < 3) {x : ℝ} (hx : x ∈ sec7_rWinMid S W)
    {d : ℝ} (hd : |d| ≤ 3 * sec7_hSum h₁ h₂ h₃) :
    HasDerivAt (F k) (F (k + 1) (x + d)) (x + d) :=
  hF k (by omega) (x + d) (sec7_mem_wide_of_near hx (le_trans hd hshift))

/-- Shifted-family chain: `t ↦ F k (t + d)`. -/
theorem sec7E_shift_chain {F : ℕ → ℝ → ℝ}
    (hF : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (F m) (F (m + 1) r) r)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {k : ℕ} (hk : k < 3) {x : ℝ} (hx : x ∈ sec7_rWinMid S W)
    {d : ℝ} (hd : |d| ≤ 3 * sec7_hSum h₁ h₂ h₃) :
    HasDerivAt (fun t => F k (t + d)) (F (k + 1) (x + d)) x := by
  have := (sec7E_basePt hF hshift hk hx hd).comp x ((hasDerivAt_id x).add_const d)
  simpa using this

/-- One-difference-at-a-shift chain: `t ↦ (Δ_h F_k)(t + d)`, provided both `d` and
`d + h` are `≤ 3h_Σ`-displacements. -/
theorem sec7E_d1shift_chain {F : ℕ → ℝ → ℝ}
    (hF : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (F m) (F (m + 1) r) r)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {k : ℕ} (hk : k < 3) {x : ℝ} (hx : x ∈ sec7_rWinMid S W)
    {d h : ℝ} (hd : |d| ≤ 3 * sec7_hSum h₁ h₂ h₃)
    (hdh : |d + h| ≤ 3 * sec7_hSum h₁ h₂ h₃) :
    HasDerivAt (fun t => diff1 h (F k) (t + d)) (diff1 h (F (k + 1)) (x + d)) x := by
  have h1 : HasDerivAt (fun t => F k (t + (d + h))) (F (k + 1) (x + (d + h))) x :=
    sec7E_shift_chain hF hshift hk hx hdh
  have h2 : HasDerivAt (fun t => F k (t + d)) (F (k + 1) (x + d)) x :=
    sec7E_shift_chain hF hshift hk hx hd
  have hfun : (fun t => diff1 h (F k) (t + d)) =
      fun t => F k (t + (d + h)) - F k (t + d) := by
    funext t
    simp only [diff1]
    ring_nf
  have hval : diff1 h (F (k + 1)) (x + d) = F (k + 1) (x + (d + h)) - F (k + 1) (x + d) := by
    simp only [diff1]
    ring_nf
  rw [hfun, hval]
  exact h1.sub h2

/-- Two-differences-at-a-shift chain: `t ↦ (Δ_{g}Δ_{h} F_k)(t + d)`. -/
theorem sec7E_d2shift_chain {F : ℕ → ℝ → ℝ}
    (hF : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (F m) (F (m + 1) r) r)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {k : ℕ} (hk : k < 3) {x : ℝ} (hx : x ∈ sec7_rWinMid S W)
    {d g h : ℝ} (hd : |d| ≤ 3 * sec7_hSum h₁ h₂ h₃)
    (hdh : |d + h| ≤ 3 * sec7_hSum h₁ h₂ h₃)
    (hdg : |d + g| ≤ 3 * sec7_hSum h₁ h₂ h₃)
    (hdgh : |d + g + h| ≤ 3 * sec7_hSum h₁ h₂ h₃) :
    HasDerivAt (fun t => diff1 g (diff1 h (F k)) (t + d))
      (diff1 g (diff1 h (F (k + 1))) (x + d)) x := by
  have h1 : HasDerivAt (fun t => diff1 h (F k) (t + (d + g)))
      (diff1 h (F (k + 1)) (x + (d + g))) x :=
    sec7E_d1shift_chain hF hshift hk hx hdg
      (by rwa [show d + g + h = d + g + h from rfl] at hdgh)
  have h2 : HasDerivAt (fun t => diff1 h (F k) (t + d))
      (diff1 h (F (k + 1)) (x + d)) x :=
    sec7E_d1shift_chain hF hshift hk hx hd hdh
  have hfun : (fun t => diff1 g (diff1 h (F k)) (t + d)) =
      fun t => diff1 h (F k) (t + (d + g)) - diff1 h (F k) (t + d) := by
    funext t
    simp only [diff1]
    ring_nf
  have hval : diff1 g (diff1 h (F (k + 1))) (x + d) =
      diff1 h (F (k + 1)) (x + (d + g)) - diff1 h (F (k + 1)) (x + d) := by
    simp only [diff1]
    ring_nf
  rw [hfun, hval]
  exact h1.sub h2

/-- Triple-difference chain: `t ↦ (Δ_{h₁,h₂,h₃} F_k)(t)`. -/
theorem sec7E_diff3_chain {F : ℕ → ℝ → ℝ}
    (hF : ∀ m < 4, ∀ r ∈ sec7_rWinWide S W, HasDerivAt (F m) (F (m + 1) r) r)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {k : ℕ} (hk : k < 3) {x : ℝ} (hx : x ∈ sec7_rWinMid S W) :
    HasDerivAt (fun t => diff3 (h₁ : ℝ) h₂ h₃ (F k) t)
      (diff3 (h₁ : ℝ) h₂ h₃ (F (k + 1)) x) x := by
  have a1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
  have a2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
  have a3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hSdef : sec7_hSum h₁ h₂ h₃ = (h₁:ℝ) + h₂ + h₃ := rfl
  have hd2 : HasDerivAt (fun t => diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F k)) (t + 0))
      (diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F (k + 1))) (x + 0)) x := by
    apply sec7E_d2shift_chain hF hshift hk hx <;>
      [skip; skip; skip; skip] <;>
      · rw [abs_of_nonneg (by linarith)]
        rw [hSdef] at *
        linarith
  have hd2' : HasDerivAt (fun t => diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F k)) (t + (h₁:ℝ)))
      (diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F (k + 1))) (x + (h₁:ℝ))) x := by
    apply sec7E_d2shift_chain hF hshift hk hx <;>
      · rw [abs_of_nonneg (by linarith)]
        rw [hSdef] at *
        linarith
  have hfun : (fun t => diff3 (h₁ : ℝ) h₂ h₃ (F k) t) =
      fun t => diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F k)) (t + (h₁:ℝ)) -
        diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F k)) (t + 0) := by
    funext t
    simp only [diff3, diff1]
    ring_nf
  have hval : diff3 (h₁ : ℝ) h₂ h₃ (F (k + 1)) x =
      diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F (k + 1))) (x + (h₁:ℝ)) -
        diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (F (k + 1))) (x + 0) := by
    simp only [diff3, diff1]
    ring_nf
  rw [hfun, hval]
  exact hd2'.sub hd2

/-- Mid-window points are positive (mid ⊆ wide). -/
theorem sec7E_mid_pos
    (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    {x : ℝ} (hx : x ∈ sec7_rWinMid S W) : 0 < x := by
  have hR : 0 < S.R := sec7_R_pos S
  simp only [sec7_rWinMid, Set.mem_Ioo] at hx
  nlinarith [hx.1, hpad, hR]

/-! ## Banked numeric caps for the monomial factors (`tools/sec7_ledger.py`, N11 block) -/

theorem sec7E_cap1 : ∀ k ≤ 2,
    |sec7_aprod (-(1:ℝ)) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(1:ℝ))) ≤ (2 * 10 ^ 10 : ℝ) := by
  intro k hk
  interval_cases k
  · have he : ((0:ℕ):ℝ) - (-(1:ℝ)) = ((1:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]
  · have he : ((1:ℕ):ℝ) - (-(1:ℝ)) = ((2:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]
  · have he : ((2:ℕ):ℝ) - (-(1:ℝ)) = ((3:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]

theorem sec7E_cap2 : ∀ k ≤ 2,
    |sec7_aprod (-(2:ℝ)) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(2:ℝ))) ≤ (10 ^ 14 : ℝ) := by
  intro k hk
  interval_cases k
  · have he : ((0:ℕ):ℝ) - (-(2:ℝ)) = ((2:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]
  · have he : ((1:ℕ):ℝ) - (-(2:ℝ)) = ((3:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]
  · have he : ((2:ℕ):ℝ) - (-(2:ℝ)) = ((4:ℕ):ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    norm_num [sec7_aprod, sec7_cWin]

/-- Quarter-power cap helper: from `aprod`-value `≤ A`, `(2cWin)^q ≤ b⁴`, `A·b ≤ K`. -/
private theorem sec7E_capq {α : ℝ} {k q : ℕ} {A b K : ℝ}
    (he : ((k:ℝ) - α) = ((q:ℕ):ℝ) / 4) (hA : |sec7_aprod α k| ≤ A) (hA0 : 0 ≤ A)
    (hb : 0 ≤ b) (hbq : (2 * sec7_cWin) ^ q ≤ b ^ 4) (hK : A * b ≤ K) :
    |sec7_aprod α k| * (2 * sec7_cWin) ^ ((k:ℝ) - α) ≤ K := by
  rw [he]
  have h1 := sec7_rpow_quarter_le hb hbq
  calc |sec7_aprod α k| * (2 * sec7_cWin) ^ (((q:ℕ):ℝ) / 4)
      ≤ A * b := by
        apply mul_le_mul hA h1
          (Real.rpow_nonneg (by norm_num [sec7_cWin]) _) hA0
    _ ≤ K := hK

theorem sec7E_cap5 : ∀ k ≤ 2,
    |sec7_aprod (-(5:ℝ)/4) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(5:ℝ)/4)) ≤
      (16 * 10 ^ 10 : ℝ) := by
  intro k hk
  interval_cases k
  · exact sec7E_capq (q := 5) (A := 1) (b := 14 * 10 ^ 3) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)
  · exact sec7E_capq (q := 9) (A := 5/4) (b := 75 * 10 ^ 6) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)
  · exact sec7E_capq (q := 13) (A := 45/16) (b := 54 * 10 ^ 9) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)

theorem sec7E_cap9 : ∀ k ≤ 2,
    |sec7_aprod (-(9:ℝ)/4) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(9:ℝ)/4)) ≤
      (9 * 10 ^ 14 : ℝ) := by
  intro k hk
  interval_cases k
  · exact sec7E_capq (q := 9) (A := 1) (b := 75 * 10 ^ 6) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)
  · exact sec7E_capq (q := 13) (A := 9/4) (b := 54 * 10 ^ 9) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)
  · exact sec7E_capq (q := 17) (A := 117/16) (b := 12 * 10 ^ 13) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)

theorem sec7E_cap17 : ∀ k ≤ 2,
    |sec7_aprod (-(17:ℝ)/4) k| * (2 * sec7_cWin) ^ ((k:ℝ) - (-(17:ℝ)/4)) ≤
      (10 ^ 22 : ℝ) := by
  intro k hk
  interval_cases k
  · exact sec7E_capq (q := 17) (A := 1) (b := 12 * 10 ^ 13) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)
  · exact sec7E_capq (q := 21) (A := 17/4) (b := 4 * 10 ^ 17) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)
  · exact sec7E_capq (q := 25) (A := 357/16) (b := 43 * 10 ^ 19) (by norm_num)
      (by norm_num [sec7_aprod]) (by norm_num) (by norm_num)
      (by norm_num [sec7_cWin]) (by norm_num)

/-- `sec7_rWin ⊆ sec7_rWinWide`. -/
theorem sec7E_rWin_subset_wide (hW : 0 < W) : sec7_rWin S W ⊆ sec7_rWinWide S W := by
  intro r hr
  have hpad_pos : 0 < W + W ^ 2 + W ^ 4 := by positivity
  simp only [sec7_rWin, Set.mem_Icc] at hr
  simp only [sec7_rWinWide, Set.mem_Ioo]
  constructor <;> [linarith [hr.1]; linarith [hr.2]]

/-! ## The graded factor families (N11-internal) -/

variable (ME : Sec7MonExp P S W a Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃)

/-- Monomial pair of the shifted `f₁` expansion (md 1607–12), graded. -/
noncomputable def sec7E_M1 : ℕ → ℝ → ℝ := fun k t =>
  sec7_powMonD S.R (ME.c₁ * S.T₁) (-(1:ℝ)) k t +
    sec7_powMonD S.R (-(ME.c₁ * sec7_hSum h₁ h₂ h₃ * (S.T₁ / S.R))) (-(2:ℝ)) k t

/-- Error family of the shifted `f₁` expansion. -/
noncomputable def sec7E_eA : ℕ → ℝ → ℝ := fun k t =>
  ME.f1C k (t + sec7_hSum h₁ h₂ h₃) - sec7E_M1 ME k t

/-- Monomial of the differenced `f₁` expansion (md 1613–17), graded; generic step `h`. -/
noncomputable def sec7E_N (h : ℤ) : ℕ → ℝ → ℝ :=
  sec7_powMonD S.R (-(ME.c₁ * (h:ℝ) * (S.T₁ / S.R))) (-(2:ℝ))

/-- Error family of the differenced `f₁` expansion. -/
noncomputable def sec7E_eQ (h : ℤ) : ℕ → ℝ → ℝ := fun k t =>
  diff1 (h:ℝ) (ME.f1C k) (t + sec7_hSum h₁ h₂ h₃ - (h:ℝ)) - sec7E_N ME h k t

/-- Monomial of the `B_i` expansion (md 1618–22), graded; generic pair `(g, h)`. -/
noncomputable def sec7E_L (g h : ℤ) : ℕ → ℝ → ℝ :=
  sec7_powMonD S.R (-(3/16) * ME.c₂ * (g:ℝ) * (h:ℝ) * (S.T₂ / S.R ^ 2)) (-(5:ℝ)/4)

/-- Error family of the `B_i` expansion at the realignment shift `ξ`. -/
noncomputable def sec7E_eK (g h : ℤ) (ξ : ℝ) : ℕ → ℝ → ℝ := fun k t =>
  diff1 (g:ℝ) (diff1 (h:ℝ) (ME.f2C k)) (t + ξ) - sec7E_L ME g h k t

/-- Monomial of the `B₀₃` expansion (md 1623–27), graded. -/
noncomputable def sec7E_M0 : ℕ → ℝ → ℝ :=
  sec7_powMonD S.R ((15/64) * ME.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3)) (-(9:ℝ)/4)

/-- Error family of the `B₀₃` expansion. -/
noncomputable def sec7E_eB0 : ℕ → ℝ → ℝ := fun k t =>
  diff3 (h₁:ℝ) h₂ h₃ (ME.f2C k) t - sec7E_M0 ME k t

/-- Monomial of the `Δ_{h₁,h₂,h₃}f₃` expansion (md 1628–33), graded. -/
noncomputable def sec7E_M3 : ℕ → ℝ → ℝ :=
  sec7_powMonD S.R (-(45/64) * ME.c₃ * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3)) (-(13:ℝ)/4)

/-- Error family of the `Δ_{h₁,h₂,h₃}f₃` expansion. -/
noncomputable def sec7E_eP3 : ℕ → ℝ → ℝ := fun k t =>
  diff3 (h₁:ℝ) h₂ h₃ (ME.f3C k) t - sec7E_M3 ME k t

/-- The leftover pure monomial `−(15/64)c₁c₂h_ΣP(T₁T₂/R⁴)y^{−17/4}` of the eq-(7.5)
regrouping, graded. -/
noncomputable def sec7E_T6 : ℕ → ℝ → ℝ :=
  sec7_powMonD S.R
    (-((15/64) * ME.c₁ * ME.c₂ * sec7_hSum h₁ h₂ h₃ * sec7_Pprod h₁ h₂ h₃ *
      (S.T₁ * S.T₂ / S.R ^ 4))) (-(17:ℝ)/4)

/-- Second factor of the `B₀₃` product: `B₀₃ + ρ₀`, graded. -/
noncomputable def sec7E_gB (ρ₀ : ℤ) : ℕ → ℝ → ℝ := fun k t =>
  diff3 (h₁:ℝ) h₂ h₃ (ME.f2C k) t + sec7_constF (ρ₀:ℝ) k t

/-- Second factor of the `B_i` products: `B_i + (ρ_i − u_i)`, graded. -/
noncomputable def sec7E_gK (g h : ℤ) (ξ : ℝ) (c : ℝ) : ℕ → ℝ → ℝ := fun k t =>
  diff1 (g:ℝ) (diff1 (h:ℝ) (ME.f2C k)) (t + ξ) + sec7_constF c k t

/-! ## Chains of the factor families on the mid window -/

section Chains

variable (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
  (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
  (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))

include hh₁ hh₂ hh₃ hpad hshift

theorem sec7E_eA_chain :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (sec7E_eA ME k) (sec7E_eA ME (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have h1 : HasDerivAt (fun t => ME.f1C k (t + sec7_hSum h₁ h₂ h₃))
      (ME.f1C (k + 1) (x + sec7_hSum h₁ h₂ h₃)) x :=
    sec7E_shift_chain ME.f1C_deriv hshift hk hx
      (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h2 : HasDerivAt (sec7E_M1 ME k) (sec7E_M1 ME (k + 1) x) x := by
    simp only [sec7E_M1]
    exact (sec7_powMonD_hasDerivAt hR _ _ k hx0).add
      (sec7_powMonD_hasDerivAt hR _ _ k hx0)
  simpa only [sec7E_eA] using h1.sub h2

theorem sec7E_eQ_chain {h : ℤ} (hh : 1 ≤ h) (hhle : (h:ℝ) ≤ sec7_hSum h₁ h₂ h₃) :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_eQ ME h k) (sec7E_eQ ME h (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hv1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have h1' : HasDerivAt
      (fun t => diff1 (h:ℝ) (ME.f1C k) (t + (sec7_hSum h₁ h₂ h₃ - (h:ℝ))))
      (diff1 (h:ℝ) (ME.f1C (k + 1)) (x + (sec7_hSum h₁ h₂ h₃ - (h:ℝ)))) x :=
    sec7E_d1shift_chain ME.f1C_deriv hshift hk hx
      (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [show sec7_hSum h₁ h₂ h₃ - (h:ℝ) + h = sec7_hSum h₁ h₂ h₃ from by ring,
            abs_of_nonneg (by linarith)]; linarith)
  have h1 : HasDerivAt
      (fun t => diff1 (h:ℝ) (ME.f1C k) (t + sec7_hSum h₁ h₂ h₃ - (h:ℝ)))
      (diff1 (h:ℝ) (ME.f1C (k + 1)) (x + sec7_hSum h₁ h₂ h₃ - (h:ℝ))) x := by
    have hfun : (fun t => diff1 (h:ℝ) (ME.f1C k) (t + sec7_hSum h₁ h₂ h₃ - (h:ℝ))) =
        fun t => diff1 (h:ℝ) (ME.f1C k) (t + (sec7_hSum h₁ h₂ h₃ - (h:ℝ))) := by
      funext t
      congr 1
      ring
    have hval : diff1 (h:ℝ) (ME.f1C (k + 1)) (x + sec7_hSum h₁ h₂ h₃ - (h:ℝ)) =
        diff1 (h:ℝ) (ME.f1C (k + 1)) (x + (sec7_hSum h₁ h₂ h₃ - (h:ℝ))) := by
      congr 1
      ring
    rw [hfun, hval]
    exact h1'
  have h2 : HasDerivAt (sec7E_N ME h k) (sec7E_N ME h (k + 1) x) x := by
    simp only [sec7E_N]
    exact sec7_powMonD_hasDerivAt hR _ _ k hx0
  simpa only [sec7E_eQ] using h1.sub h2

theorem sec7E_eK_chain {g h : ℤ} (hg : 1 ≤ g) (hh : 1 ≤ h)
    (hgle : (g:ℝ) ≤ sec7_hSum h₁ h₂ h₃) (hhle : (h:ℝ) ≤ sec7_hSum h₁ h₂ h₃)
    {ξ : ℝ} (hξ : |ξ| ≤ sec7_hSum h₁ h₂ h₃) :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_eK ME g h ξ k) (sec7E_eK ME g h ξ (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hv1 : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hv2 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hξ' := abs_le.mp hξ
  have h1 : HasDerivAt
      (fun t => diff1 (g:ℝ) (diff1 (h:ℝ) (ME.f2C k)) (t + ξ))
      (diff1 (g:ℝ) (diff1 (h:ℝ) (ME.f2C (k + 1))) (x + ξ)) x :=
    sec7E_d2shift_chain ME.f2C_deriv hshift hk hx
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
  have h2 : HasDerivAt (sec7E_L ME g h k) (sec7E_L ME g h (k + 1) x) x := by
    simp only [sec7E_L]
    exact sec7_powMonD_hasDerivAt hR _ _ k hx0
  simpa only [sec7E_eK] using h1.sub h2

theorem sec7E_eB0_chain :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_eB0 ME k) (sec7E_eB0 ME (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  have h1 := sec7E_diff3_chain ME.f2C_deriv hh₁ hh₂ hh₃ hshift hk hx
  have h2 : HasDerivAt (sec7E_M0 ME k) (sec7E_M0 ME (k + 1) x) x := by
    simp only [sec7E_M0]
    exact sec7_powMonD_hasDerivAt hR _ _ k hx0
  simpa only [sec7E_eB0] using h1.sub h2

theorem sec7E_eP3_chain :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_eP3 ME k) (sec7E_eP3 ME (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  have h1 := sec7E_diff3_chain ME.f3C_deriv hh₁ hh₂ hh₃ hshift hk hx
  have h2 : HasDerivAt (sec7E_M3 ME k) (sec7E_M3 ME (k + 1) x) x := by
    simp only [sec7E_M3]
    exact sec7_powMonD_hasDerivAt hR _ _ k hx0
  simpa only [sec7E_eP3] using h1.sub h2

omit hpad in
theorem sec7E_gB_chain (ρ₀ : ℤ) :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_gB ME ρ₀ k) (sec7E_gB ME ρ₀ (k + 1) x) x := by
  intro k hk x hx
  have h1 := sec7E_diff3_chain ME.f2C_deriv hh₁ hh₂ hh₃ hshift hk hx
  simpa only [sec7E_gB] using h1.add (sec7_constF_deriv (ρ₀:ℝ) k x)

omit hpad in
theorem sec7E_gK_chain {g h : ℤ} (hg : 1 ≤ g) (hh : 1 ≤ h)
    (hgle : (g:ℝ) ≤ sec7_hSum h₁ h₂ h₃) (hhle : (h:ℝ) ≤ sec7_hSum h₁ h₂ h₃)
    {ξ : ℝ} (hξ : |ξ| ≤ sec7_hSum h₁ h₂ h₃) (c : ℝ) :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_gK ME g h ξ c k) (sec7E_gK ME g h ξ c (k + 1) x) x := by
  intro k hk x hx
  have hSv3 : (3:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hv1 : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hv2 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hξ' := abs_le.mp hξ
  have h1 : HasDerivAt
      (fun t => diff1 (g:ℝ) (diff1 (h:ℝ) (ME.f2C k)) (t + ξ))
      (diff1 (g:ℝ) (diff1 (h:ℝ) (ME.f2C (k + 1))) (x + ξ)) x :=
    sec7E_d2shift_chain ME.f2C_deriv hshift hk hx
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
      (by rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2])
  simpa only [sec7E_gK] using h1.add (sec7_constF_deriv c k x)

omit hh₁ hh₂ hh₃ hshift in
theorem sec7E_T6_chain :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_T6 ME k) (sec7E_T6 ME (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  simpa only [sec7E_T6] using
    sec7_powMonD_hasDerivAt hR _ _ k (sec7E_mid_pos hpad hx)

omit hh₁ hh₂ hh₃ hshift in
theorem sec7E_M1_chain :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_M1 ME k) (sec7E_M1 ME (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  have hx0 : 0 < x := sec7E_mid_pos hpad hx
  simp only [sec7E_M1]
  exact (sec7_powMonD_hasDerivAt hR _ _ k hx0).add (sec7_powMonD_hasDerivAt hR _ _ k hx0)

omit hh₁ hh₂ hh₃ hshift in
theorem sec7E_N_chain (h : ℤ) :
    ∀ k < 3, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (sec7E_N ME h k) (sec7E_N ME h (k + 1) x) x := by
  intro k hk x hx
  have hR : 0 < S.R := sec7_R_pos S
  simpa only [sec7E_N] using sec7_powMonD_hasDerivAt hR _ _ k (sec7E_mid_pos hpad hx)

end Chains

end Pieces

end Squarefree
