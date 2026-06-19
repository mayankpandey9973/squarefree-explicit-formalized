import Squarefree.Bracket.Sec7Defs
import Squarefree.Bracket.Sec7DiffMVT
import Squarefree.Bracket.Sec7PhaseExp

/-!
# §7 carry/fiber cover machinery (plan node N7, md 1545–70)

Support for `sec7_carry_fiber_cover` (Bracket/Sec7Branch.lean): the floor-carry
combinatorics (`Δ²{f} = Δ²f + carry`), the lattice fiber count through the monotone
drivers `B_i(r) = Δ_{h_j,h_k}f₂(r+ξ_i)` (eq 7.2: `≤ 4 + 2·cPh·S·T₂/R²` joint values,
since all three are driven by the constant-sign `f₂'''`), and the full cover core.
-/

open Classical Finset Squarefree.FiniteDiff

namespace Squarefree

/-- The 4-corner floor combination converting `Δ_{h₂,h₃}f` into `Δ_{h₂,h₃}{f}`
(md 1545–53: the integer carry of one second difference). -/
noncomputable def sec7_carry2 (f : ℝ → ℝ) (h₂ h₃ x : ℝ) : ℤ :=
  -⌊f (x + h₂ + h₃)⌋ + ⌊f (x + h₂)⌋ + ⌊f (x + h₃)⌋ - ⌊f x⌋

/-- `Δ_{h₂,h₃}{f}(x) = Δ_{h₂,h₃}f(x) + carry` (md 1550–53). -/
theorem sec7_carry2_eq (f : ℝ → ℝ) (h₂ h₃ x : ℝ) :
    diff1 h₂ (diff1 h₃ (fun t => Int.fract (f t))) x =
      diff1 h₂ (diff1 h₃ f) x + (sec7_carry2 f h₂ h₃ x : ℝ) := by
  simp only [diff1, Int.fract, sec7_carry2]
  push_cast
  ring

/-- `Δ_{h₁,h₂,h₃}{f}(x) = Δ_{h₁,h₂,h₃}f(x) + (carry(x+h₁) − carry(x))` (md 1547–49:
the top carry `ρ₀`). -/
theorem sec7_carry3_eq (f : ℝ → ℝ) (h₁ h₂ h₃ x : ℝ) :
    diff3 h₁ h₂ h₃ (fun t => Int.fract (f t)) x =
      diff3 h₁ h₂ h₃ f x
        + ((sec7_carry2 f h₂ h₃ (x + h₁) - sec7_carry2 f h₂ h₃ x : ℤ) : ℝ) := by
  simp only [diff3, diff1, Int.fract, sec7_carry2]
  push_cast
  ring

/-- **Fiber count (eq 7.2, md 1554–65)**: the floors of three drivers `B_i`, all
monotone in the same direction `σ` and bounded by `M_i` on `[lo, hi]`, take at most
`4 + 2(M₁+M₂+M₃)` distinct joint values. -/
private theorem sec7_fiber_count {lo hi : ℤ} (hlohi : lo ≤ hi)
    (B₁ B₂ B₃ : ℝ → ℝ) (σ M₁ M₂ M₃ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hb₁ : ∀ r ∈ Finset.Icc lo hi, |B₁ (r : ℝ)| ≤ M₁)
    (hb₂ : ∀ r ∈ Finset.Icc lo hi, |B₂ (r : ℝ)| ≤ M₂)
    (hb₃ : ∀ r ∈ Finset.Icc lo hi, |B₃ (r : ℝ)| ≤ M₃)
    (hm₁ : ∀ r ∈ Finset.Icc lo hi, ∀ r' ∈ Finset.Icc lo hi, r ≤ r' →
      σ * B₁ (r : ℝ) ≤ σ * B₁ (r' : ℝ))
    (hm₂ : ∀ r ∈ Finset.Icc lo hi, ∀ r' ∈ Finset.Icc lo hi, r ≤ r' →
      σ * B₂ (r : ℝ) ≤ σ * B₂ (r' : ℝ))
    (hm₃ : ∀ r ∈ Finset.Icc lo hi, ∀ r' ∈ Finset.Icc lo hi, r ≤ r' →
      σ * B₃ (r : ℝ) ≤ σ * B₃ (r' : ℝ)) :
    (((Finset.Icc lo hi).image fun r : ℤ =>
        (⌊B₁ (r : ℝ)⌋, ⌊B₂ (r : ℝ)⌋, ⌊B₃ (r : ℝ)⌋)).card : ℝ) ≤
      4 + 2 * (M₁ + M₂ + M₃) := by
  have hloI : lo ∈ Finset.Icc lo hi := Finset.mem_Icc.mpr ⟨le_refl lo, hlohi⟩
  have hhiI : hi ∈ Finset.Icc lo hi := Finset.mem_Icc.mpr ⟨hlohi, le_refl hi⟩
  obtain ⟨a1l, a1r⟩ := abs_le.mp (hb₁ lo hloI)
  obtain ⟨b1l, b1r⟩ := abs_le.mp (hb₁ hi hhiI)
  obtain ⟨a2l, a2r⟩ := abs_le.mp (hb₂ lo hloI)
  obtain ⟨b2l, b2r⟩ := abs_le.mp (hb₂ hi hhiI)
  obtain ⟨a3l, a3r⟩ := abs_le.mp (hb₃ lo hloI)
  obtain ⟨b3l, b3r⟩ := abs_le.mp (hb₃ hi hhiI)
  have fl1 := Int.floor_le (B₁ (lo : ℝ)); have fl1' := Int.floor_le (B₁ (hi : ℝ))
  have fg1 := Int.sub_one_lt_floor (B₁ (lo : ℝ))
  have fg1' := Int.sub_one_lt_floor (B₁ (hi : ℝ))
  have fl2 := Int.floor_le (B₂ (lo : ℝ)); have fl2' := Int.floor_le (B₂ (hi : ℝ))
  have fg2 := Int.sub_one_lt_floor (B₂ (lo : ℝ))
  have fg2' := Int.sub_one_lt_floor (B₂ (hi : ℝ))
  have fl3 := Int.floor_le (B₃ (lo : ℝ)); have fl3' := Int.floor_le (B₃ (hi : ℝ))
  have fg3 := Int.sub_one_lt_floor (B₃ (lo : ℝ))
  have fg3' := Int.sub_one_lt_floor (B₃ (hi : ℝ))
  rcases hσ with rfl | rfl
  · -- `σ = 1`: the floors are non-decreasing
    have hcnt := card_image_mono3 hlohi (fun r => ⌊B₁ (r : ℝ)⌋) (fun r => ⌊B₂ (r : ℝ)⌋)
      (fun r => ⌊B₃ (r : ℝ)⌋)
      (fun r hr r' hr' hle => Int.floor_le_floor (by simpa using hm₁ r hr r' hr' hle))
      (fun r hr r' hr' hle => Int.floor_le_floor (by simpa using hm₂ r hr r' hr' hle))
      (fun r hr r' hr' hle => Int.floor_le_floor (by simpa using hm₃ r hr r' hr' hle))
    have hcast := (Int.cast_le (R := ℝ)).mpr hcnt
    push_cast at hcast
    linarith
  · -- `σ = -1`: the negated floors are non-decreasing; pass through the negation
    have hneg : (((Finset.Icc lo hi).image fun r : ℤ =>
        (⌊B₁ (r : ℝ)⌋, ⌊B₂ (r : ℝ)⌋, ⌊B₃ (r : ℝ)⌋)).card) ≤
        (((Finset.Icc lo hi).image fun r : ℤ =>
          (-⌊B₁ (r : ℝ)⌋, -⌊B₂ (r : ℝ)⌋, -⌊B₃ (r : ℝ)⌋)).card) := by
      refine le_trans (le_of_eq rfl)
        (card_image_factor _ _ (fun v : ℤ × ℤ × ℤ => (-v.1, -v.2.1, -v.2.2)) ?_)
      intro r hr r' hr' he
      simp only [Prod.mk.injEq] at he ⊢
      omega
    have hmono : ∀ (B : ℝ → ℝ),
        (∀ r ∈ Finset.Icc lo hi, ∀ r' ∈ Finset.Icc lo hi, r ≤ r' →
          (-1 : ℝ) * B (r : ℝ) ≤ (-1) * B (r' : ℝ)) →
        ∀ r ∈ Finset.Icc lo hi, ∀ r' ∈ Finset.Icc lo hi, r ≤ r' →
          -⌊B (r : ℝ)⌋ ≤ -⌊B (r' : ℝ)⌋ := by
      intro B hm r hr r' hr' hle
      have := hm r hr r' hr' hle
      have hBle : B (r' : ℝ) ≤ B (r : ℝ) := by linarith
      have := Int.floor_le_floor hBle
      omega
    have hcnt := card_image_mono3 hlohi (fun r => -⌊B₁ (r : ℝ)⌋) (fun r => -⌊B₂ (r : ℝ)⌋)
      (fun r => -⌊B₃ (r : ℝ)⌋) (hmono B₁ hm₁) (hmono B₂ hm₂) (hmono B₃ hm₃)
    have hcast := (Int.cast_le (R := ℝ)).mpr hcnt
    push_cast at hcast
    have hneg' := (Nat.cast_le (α := ℝ)).mpr hneg
    push_cast at hneg'
    linarith

/-- **Per-pair driver facts** (md 1560–65): on the wide count window the second-difference
driver `t ↦ Δ_{hA,hB}f₂(t+ξ)` is bounded by `cPh·(T₂/R²)·hB·hA`, and `σ·(driver)` is
non-decreasing, `σ` being the constant sign of `f₂'''`. -/
private theorem sec7_pair_driver {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} (Ph : Sec7Phase P S W a)
    {hA hB : ℤ} {ξ σ M : ℝ}
    (eA : (0:ℝ) ≤ (hA : ℝ)) (eB : (0:ℝ) ≤ (hB : ℝ))
    (hABM : (hA : ℝ) + (hB : ℝ) + |ξ| ≤ M)
    (hσ3 : ∀ t ∈ sec7_rWin S W, 0 ≤ σ * Ph.f2D 3 t)
    (hwin : ∀ y : ℝ, S.R / 72 - M ≤ y → y ≤ 16 * S.R + M → y ∈ sec7_rWin S W) :
    (∀ x : ℝ, S.R / 72 ≤ x → x ≤ 16 * S.R →
      |diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 0)) (x + ξ)| ≤
        sec7_cPh * (S.T₂ / S.R ^ 2) * (hB : ℝ) * (hA : ℝ)) ∧
    (∀ x y : ℝ, S.R / 72 ≤ x → y ≤ 16 * S.R → x ≤ y →
      σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 0)) (x + ξ) ≤
        σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 0)) (y + ξ)) := by
  have hξ1 : -(|ξ|) ≤ ξ := neg_abs_le ξ
  have hξ2 : ξ ≤ |ξ| := le_abs_self ξ
  have hM0 : 0 ≤ M := le_trans (by positivity) hABM
  have hf0 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f2D 0) (Ph.f2D 1 t) t :=
    fun t ht => Ph.f2D_hasDeriv 0 (by norm_num) t ht
  have hf1 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f2D 1) (Ph.f2D 2 t) t :=
    fun t ht => Ph.f2D_hasDeriv 1 (by norm_num) t ht
  have hf2 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f2D 2) (Ph.f2D 3 t) t :=
    fun t ht => Ph.f2D_hasDeriv 2 (by norm_num) t ht
  have hb2 : ∀ t ∈ sec7_rWin S W, |Ph.f2D 2 t| ≤ sec7_cPh * (S.T₂ / S.R ^ 2) :=
    fun t ht => Ph.f2D_hi 2 (by norm_num) t ht
  constructor
  · intro x hx1 hx2
    exact abs_diff2_le hf0 hf1 hb2 eA eB
      (hwin _ (by linarith) (by linarith))
      (hwin _ (by linarith) (by linarith))
  · intro x y hx1 hy2 hxy
    -- the derivative of `σ·driver` is `σ·Δ_{hA,hB}f₂'(t+ξ) ≥ 0` (nested signed MVT)
    have hCnn : ∀ t ∈ Set.Icc x y,
        0 ≤ σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 1)) (t + ξ) := by
      intro t ht
      have ht1 : S.R / 72 ≤ t := le_trans hx1 ht.1
      have ht2 : t ≤ 16 * S.R := le_trans ht.2 hy2
      have hnn := diff2_nonneg (f := fun u => σ * Ph.f2D 1 u)
        (f' := fun u => σ * Ph.f2D 2 u) (f'' := fun u => σ * Ph.f2D 3 u)
        (fun u hu => (hf1 u hu).const_mul σ)
        (fun u hu => (hf2 u hu).const_mul σ)
        (fun u hu => hσ3 u hu) eA eB
        (hwin (t + ξ) (by linarith) (by linarith))
        (hwin (t + ξ + (hA : ℝ) + (hB : ℝ)) (by linarith) (by linarith))
      have hlin : diff1 (hA : ℝ) (diff1 (hB : ℝ) (fun u => σ * Ph.f2D 1 u)) (t + ξ) =
          σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 1)) (t + ξ) := by
        simp only [diff1]; ring
      rw [hlin] at hnn
      exact hnn
    have hd : ∀ t ∈ Set.Icc x y,
        HasDerivAt (fun s => σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 0)) (s + ξ))
          (σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 1)) (t + ξ)) t := by
      intro t ht
      have ht1 : S.R / 72 ≤ t := le_trans hx1 ht.1
      have ht2 : t ≤ 16 * S.R := le_trans ht.2 hy2
      have hpt : ∀ c : ℝ, 0 ≤ c → c ≤ (hA : ℝ) + (hB : ℝ) →
          HasDerivAt (fun s : ℝ => Ph.f2D 0 (s + (ξ + c))) (Ph.f2D 1 (t + (ξ + c))) t := by
        intro c hc1 hc2
        have hmemc : t + (ξ + c) ∈ sec7_rWin S W :=
          hwin _ (by linarith) (by linarith)
        simpa using (hf0 _ hmemc).comp t ((hasDerivAt_id t).add_const (ξ + c))
      have h00 := hpt 0 le_rfl (by linarith)
      have hA0 := hpt (hA : ℝ) eA (by linarith)
      have hB0 := hpt (hB : ℝ) eB (by linarith)
      have hAB := hpt ((hA : ℝ) + (hB : ℝ)) (by linarith) le_rfl
      have hcomb := ((hAB.sub hB0).sub (hA0.sub h00)).const_mul σ
      have hfeq : (fun s => σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 0)) (s + ξ)) =
          (fun s : ℝ => σ * (Ph.f2D 0 (s + (ξ + ((hA : ℝ) + (hB : ℝ))))
            - Ph.f2D 0 (s + (ξ + (hB : ℝ)))
            - (Ph.f2D 0 (s + (ξ + (hA : ℝ))) - Ph.f2D 0 (s + (ξ + 0))))) := by
        funext s; simp only [diff1]; ring_nf
      have hveq : σ * diff1 (hA : ℝ) (diff1 (hB : ℝ) (Ph.f2D 1)) (t + ξ) =
          σ * (Ph.f2D 1 (t + (ξ + ((hA : ℝ) + (hB : ℝ))))
            - Ph.f2D 1 (t + (ξ + (hB : ℝ)))
            - (Ph.f2D 1 (t + (ξ + (hA : ℝ))) - Ph.f2D 1 (t + (ξ + 0)))) := by
        simp only [diff1]; ring_nf
      rw [hfeq, hveq]
      exact hcomb
    have key := diff1_nonneg hd hCnn (by linarith : (0:ℝ) ≤ y - x)
      (Set.left_mem_Icc.2 hxy)
      (by rw [show x + (y - x) = y by ring]; exact Set.right_mem_Icc.2 hxy)
    simp only [diff1, show x + (y - x) = y by ring] at key
    simp only [diff1]
    linarith

set_option maxHeartbeats 1600000 in
set_option exponentiation.threshold 700 in
/-- **N7 core** (md 1545–70): the carry/fiber cover, proved, together with the sharp
zero-top-carry subcover.  `sec7_carry_fiber_cover` (Bracket/Sec7Branch.lean) delegates to
the first projection; the zero-branch cover delegates to the second. -/
theorem sec7_carry_fiber_cover_core {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} (Ph : Sec7Phase P S W a) (Env : Sec7Envelope P S W) {j : ℤ}
    (_hj : sec7_jBand P S j) {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) {ξ₁ ξ₂ ξ₃ : ℝ}
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    {M : ℝ} (hM : 2 * (W + W ^ 2 + W ^ 4) ≤ M)
    (hwin : ∀ y : ℝ, S.R / 72 - M ≤ y → y ≤ 16 * S.R + M → y ∈ sec7_rWin S W) :
    (∃ Λ : Finset ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ)),
      (Λ.card : ℝ) ≤ sec7_cMult * sec7_cPh * (1 + sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)) ∧
      (∀ pc ∈ Λ,
        (|(pc.1.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.1 : ℝ)| ≤ sec7_cCarry ∧
          |(pc.1.2.2.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.2.2 : ℝ)| ≤ sec7_cCarry) ∧
        (|(pc.2.1.1 : ℝ) - pc.1.2.1| ≤ sec7_cPh * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.1 : ℝ) - pc.1.2.2.1| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.2 : ℝ) - pc.1.2.2.2| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) ∧
        Set.Icc pc.2.2.1 pc.2.2.2 ⊆ Set.Icc (S.R / 72) (16 * S.R)) ∧
      (∀ r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋, ∃ pc ∈ Λ,
        (r : ℝ) ∈ Set.Icc pc.2.2.1 pc.2.2.2 ∧
        diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + pc.1.1 ∧
        diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
          diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
            - pc.2.1.1 + pc.1.2.1 ∧
        diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
          diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
            - pc.2.1.2.1 + pc.1.2.2.1 ∧
        diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
          diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
            - pc.2.1.2.2 + pc.1.2.2.2)) ∧
    ∃ Λ : Finset ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ)),
      (Λ.card : ℝ) ≤ 343 *
        (4 + 2 * (sec7_cPh * (sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)))) ∧
      (∀ pc ∈ Λ, pc.1.1 = 0) ∧
      (∀ pc ∈ Λ,
        (|(pc.1.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.1 : ℝ)| ≤ sec7_cCarry ∧
          |(pc.1.2.2.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.2.2 : ℝ)| ≤ sec7_cCarry) ∧
        (|(pc.2.1.1 : ℝ) - pc.1.2.1| ≤ sec7_cPh * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.1 : ℝ) - pc.1.2.2.1| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.2 : ℝ) - pc.1.2.2.2| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) ∧
        Set.Icc pc.2.2.1 pc.2.2.2 ⊆ Set.Icc (S.R / 72) (16 * S.R)) ∧
      (∀ r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋,
        diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + (0 : ℝ) →
        ∃ pc ∈ Λ,
          (r : ℝ) ∈ Set.Icc pc.2.2.1 pc.2.2.2 ∧
          diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
            diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + pc.1.1 ∧
          diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
            diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
              - pc.2.1.1 + pc.1.2.1 ∧
          diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
            diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
              - pc.2.1.2.1 + pc.1.2.2.1 ∧
          diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
            diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
              - pc.2.1.2.2 + pc.1.2.2.2) := by
  classical
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hR : (0:ℝ) < S.R := by unfold Scale.R; positivity
  have hx : (0:ℝ) < S.x := by unfold Scale.x; positivity
  have hT2 : (0:ℝ) < S.T₂ := by unfold Scale.T₂ Scale.F; positivity
  have e1 : (1:ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hbox.1.1
  have e2 : (1:ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hbox.2.1.1
  have e3 : (1:ℝ) ≤ (h₃ : ℝ) := by exact_mod_cast hbox.2.2.1
  have u1b : (h₁ : ℝ) ≤ W := hbox.1.2
  have u2b : (h₂ : ℝ) ≤ W ^ 2 := hbox.2.1.2
  have u3b : (h₃ : ℝ) ≤ W ^ 4 := hbox.2.2.2
  have hW1 : (1:ℝ) ≤ W := le_trans e1 u1b
  have hSsym0 : (0:ℝ) ≤ sec7_Ssym h₁ h₂ h₃ := by simp only [sec7_Ssym]; nlinarith
  set lo : ℤ := ⌈S.R / 72⌉ with hlo
  set hi : ℤ := ⌊16 * S.R⌋ with hhi
  rcases le_or_gt lo hi with hlohi | hlohi
  swap
  · -- empty count window: the empty cover
    refine ⟨⟨∅, ?_, ?_, ?_⟩, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      have hq : (0:ℝ) ≤ sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5) :=
        div_nonneg hSsym0 (by positivity)
      simp only [sec7_cMult, sec7_cPh]
      nlinarith
    · intro pc hpc
      simp at hpc
    · intro r hr
      rw [Finset.mem_Icc] at hr
      exact absurd (le_trans hr.1 hr.2) (not_le.mpr hlohi)
    · refine ⟨∅, ?_, ?_, ?_, ?_⟩
      · simp only [Finset.card_empty, Nat.cast_zero]
        have hq : (0:ℝ) ≤ sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5) :=
          div_nonneg hSsym0 (by positivity)
        simp only [sec7_cPh]
        nlinarith
      · intro pc hpc
        simp at hpc
      · intro pc hpc
        simp at hpc
      · intro r hr _hzero
        rw [Finset.mem_Icc] at hr
        exact absurd (le_trans hr.1 hr.2) (not_le.mpr hlohi)
  -- A1 margin facts from the envelope (n6 × n7, log-free): `R ≥ 10¹⁵⁰·W²¹` and
  -- `GΩ⁵R ≥ 10¹⁵⁰·W²⁷`
  have hRW : (10:ℝ) ^ 150 * W ^ 21 ≤ S.R := by
    have hprod : (sec7_envC2 * (W ^ 30 * S.Ω ^ 4)) * (sec7_envC2 * W ^ 54)
        ≤ (P.H * S.x) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) :=
      mul_le_mul Env.n6 Env.n7
        (by have := sec7_envC2_pos; positivity) (by positivity)
    have hRid : (P.H * S.x) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) = S.R ^ 4 * S.Ω ^ 4 := by
      unfold Scale.x Scale.R
      field_simp
    rw [hRid, show (sec7_envC2 * (W ^ 30 * S.Ω ^ 4)) * (sec7_envC2 * W ^ 54)
      = (sec7_envC2 ^ 2 * W ^ 84) * S.Ω ^ 4 by ring] at hprod
    have hcan : ((10:ℝ) ^ 150 * W ^ 21) ^ 4 ≤ S.R ^ 4 := by
      have := le_of_mul_le_mul_right hprod (by positivity : (0:ℝ) < S.Ω ^ 4)
      calc ((10:ℝ) ^ 150 * W ^ 21) ^ 4 = sec7_envC2 ^ 2 * W ^ 84 := by
            simp only [sec7_envC2]; ring
        _ ≤ S.R ^ 4 := this
    exact le_of_pow_le_pow_left₀ (by norm_num) hR.le hcan
  have hGR : (10:ℝ) ^ 150 * W ^ 27 ≤ P.G * S.Ω ^ 5 * S.R := by
    have hid : P.H * S.x * P.G ^ 4 * S.Ω ^ 16 = (P.G * S.Ω ^ 5 * S.R) ^ 2 := by
      unfold Scale.x Scale.R
      field_simp
    have hcan : ((10:ℝ) ^ 150 * W ^ 27) ^ 2 ≤ (P.G * S.Ω ^ 5 * S.R) ^ 2 := by
      calc ((10:ℝ) ^ 150 * W ^ 27) ^ 2 = sec7_envC2 * W ^ 54 := by
            simp only [sec7_envC2]; ring
        _ ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := Env.n7
        _ = _ := hid
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hcan
  have hW21 : W ≤ W ^ 21 ∧ W ^ 2 ≤ W ^ 21 ∧ W ^ 4 ≤ W ^ 21 := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using pow_le_pow_right₀ hW1 (by norm_num : 1 ≤ 21)
    · exact pow_le_pow_right₀ hW1 (by norm_num)
    · exact pow_le_pow_right₀ hW1 (by norm_num)
  have hMR : W + W ^ 2 + W ^ 4 ≤ S.R / 1000 := by
    obtain ⟨q1, q2, q3⟩ := hW21
    linarith only [hRW, q1, q2, q3, hR]
  have hWin : ∀ y : ℝ, S.R / 144 - 2 * (W + W ^ 2 + W ^ 4) ≤ y →
      y ≤ 40 * S.R + 2 * (W + W ^ 2 + W ^ 4) → y ∈ sec7_rWin S W := by
    intro y hy1 hy2
    simp [sec7_rWin, hy1, hy2]
  have hmemr : ∀ r ∈ Finset.Icc lo hi, S.R / 72 ≤ (r : ℝ) ∧ (r : ℝ) ≤ 16 * S.R := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hc1 : S.R / 72 ≤ ((lo : ℤ) : ℝ) := by rw [hlo]; exact Int.le_ceil _
    have hc2 : ((hi : ℤ) : ℝ) ≤ 16 * S.R := by rw [hhi]; exact Int.floor_le _
    exact ⟨le_trans hc1 (by exact_mod_cast hr.1), le_trans (by exact_mod_cast hr.2) hc2⟩
  -- constant sign of `f₂'''` on the padded window
  have hf3ne : ∀ t ∈
      Set.Icc (S.R / 144 - 2 * (W + W ^ 2 + W ^ 4))
        (40 * S.R + 2 * (W + W ^ 2 + W ^ 4)), Ph.f2D 3 t ≠ 0 := by
    intro t ht h0
    have htWin : t ∈ sec7_rWin S W := by simpa [sec7_rWin] using ht
    have hlo3 := Ph.f2D_lo 3 (by norm_num) t htWin
    rw [h0, abs_zero, mul_zero] at hlo3
    have hp : (0:ℝ) < S.T₂ / S.R ^ 3 := by positivity
    linarith
  have hcont3 : ContinuousOn (Ph.f2D 3)
      (Set.Icc (S.R / 144 - 2 * (W + W ^ 2 + W ^ 4))
        (40 * S.R + 2 * (W + W ^ 2 + W ^ 4))) := by
    intro t ht
    have htWin : t ∈ sec7_rWin S W := by simpa [sec7_rWin] using ht
    exact ((Ph.f2D_hasDeriv 3 (by norm_num) t htWin).continuousAt).continuousWithinAt
  obtain ⟨σ, hσpm, hσ3Icc⟩ := exists_sign_of_ne_zero hcont3 hf3ne
  have hσ3 : ∀ t ∈ sec7_rWin S W, 0 ≤ σ * Ph.f2D 3 t := by
    intro t ht
    exact hσ3Icc t (by simpa [sec7_rWin] using ht)
  -- the three pair drivers
  obtain ⟨hbd₁, hmono₁⟩ := sec7_pair_driver Ph (hA := h₂) (hB := h₃) (ξ := ξ₁) (σ := σ)
    (M := M) (by linarith) (by linarith)
    (by simp only [sec7_hSum] at hξ₁; linarith) hσ3 hwin
  obtain ⟨hbd₂, hmono₂⟩ := sec7_pair_driver Ph (hA := h₁) (hB := h₃) (ξ := ξ₂) (σ := σ)
    (M := M) (by linarith) (by linarith)
    (by simp only [sec7_hSum] at hξ₂; linarith) hσ3 hwin
  obtain ⟨hbd₃, hmono₃⟩ := sec7_pair_driver Ph (hA := h₁) (hB := h₂) (ξ := ξ₃) (σ := σ)
    (M := M) (by linarith) (by linarith)
    (by simp only [sec7_hSum] at hξ₃; linarith) hσ3 hwin
  -- fract-difference size facts (no window needed)
  have habsF2 : ∀ (cA cB x : ℝ),
      |diff1 cA (diff1 cB (fun t => Int.fract (Ph.f2D 0 t))) x| ≤ 2 := by
    intro cA cB x
    have hg1 := abs_diff1_fract_le cB (Ph.f2D 0) (x + cA)
    have hg2 := abs_diff1_fract_le cB (Ph.f2D 0) x
    refine le_trans (abs_sub _ _) ?_
    linarith
  have habsF3 : ∀ x : ℝ,
      |diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) x| ≤ 4 := by
    intro x
    have hg1 := habsF2 (h₂ : ℝ) (h₃ : ℝ) (x + h₁)
    have hg2 := habsF2 (h₂ : ℝ) (h₃ : ℝ) x
    refine le_trans (abs_sub _ _) ?_
    linarith
  -- `|Δ³f₂(r)| ≤ 1` on the window (the md-1556 `ρ₀ = O(1)`; uses `GΩ⁵R ≥ 10¹⁵⁰W²⁷`)
  have hf0 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f2D 0) (Ph.f2D 1 t) t :=
    fun t ht => Ph.f2D_hasDeriv 0 (by norm_num) t ht
  have hf1 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f2D 1) (Ph.f2D 2 t) t :=
    fun t ht => Ph.f2D_hasDeriv 1 (by norm_num) t ht
  have hf2 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f2D 2) (Ph.f2D 3 t) t :=
    fun t ht => Ph.f2D_hasDeriv 2 (by norm_num) t ht
  have habsD3 : ∀ r ∈ Finset.Icc lo hi,
      |diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ)| ≤ 1 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hmemr r hr
    have hb3 : ∀ t ∈ sec7_rWin S W, |Ph.f2D 3 t| ≤ sec7_cPh * (S.T₂ / S.R ^ 3) :=
      fun t ht => Ph.f2D_hi 3 (by norm_num) t ht
    have h := abs_diff3_le hf0 hf1 hf2 hb3 (by linarith) (by linarith) (by linarith)
      (hWin (r : ℝ) (by linarith) (by linarith))
      (hWin ((r : ℝ) + h₁ + h₂ + h₃) (by linarith) (by linarith))
    refine le_trans h ?_
    have hT3 : S.T₂ / S.R ^ 3 = 1 / (P.G * S.Ω ^ 5 * S.R) := by
      rw [show S.R ^ 3 = S.R ^ 2 * S.R by ring, ← div_div, sec7_T₂_div_R_sq, div_div]
    rw [hT3]
    have hprod : (h₃ : ℝ) * h₂ * h₁ ≤ W ^ 27 := by
      have q1 : (h₃ : ℝ) * h₂ ≤ W ^ 4 * W ^ 2 :=
        mul_le_mul u3b u2b (by linarith) (by positivity)
      have q2 : (h₃ : ℝ) * h₂ * h₁ ≤ W ^ 4 * W ^ 2 * W :=
        mul_le_mul q1 u1b (by linarith) (by positivity)
      have q3 : W ^ 4 * W ^ 2 * W ≤ W ^ 27 := by
        rw [show W ^ 4 * W ^ 2 * W = W ^ 7 by ring]
        exact pow_le_pow_right₀ hW1 (by norm_num)
      linarith
    have hGR5pos : (0:ℝ) < P.G * S.Ω ^ 5 * S.R := by positivity
    rw [show sec7_cPh * (1 / (P.G * S.Ω ^ 5 * S.R)) * (h₃ : ℝ) * h₂ * h₁
      = sec7_cPh * ((h₃ : ℝ) * h₂ * h₁) / (P.G * S.Ω ^ 5 * S.R) by ring,
      div_le_one hGR5pos]
    simp only [sec7_cPh]
    have hW27 : (0:ℝ) ≤ W ^ 27 := by positivity
    linarith only [hGR, hprod, hW27]
  -- the cover data
  set q1 : ℤ → ℤ :=
    fun r => ⌊diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)⌋ with hq1
  set q2 : ℤ → ℤ :=
    fun r => ⌊diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)⌋ with hq2
  set q3 : ℤ → ℤ :=
    fun r => ⌊diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)⌋ with hq3
  set p0 : ℤ → ℤ := fun r => sec7_carry2 (Ph.f2D 0) (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + (h₁ : ℝ))
    - sec7_carry2 (Ph.f2D 0) (h₂ : ℝ) (h₃ : ℝ) (r : ℝ) with hp0
  set p1 : ℤ → ℤ :=
    fun r => q1 r + sec7_carry2 (Ph.f2D 0) (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₁) with hp1
  set p2 : ℤ → ℤ :=
    fun r => q2 r + sec7_carry2 (Ph.f2D 0) (h₁ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₂) with hp2
  set p3 : ℤ → ℤ :=
    fun r => q3 r + sec7_carry2 (Ph.f2D 0) (h₁ : ℝ) (h₂ : ℝ) ((r : ℝ) + ξ₃) with hp3
  set pcf : ℤ → (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ) := fun r =>
    ((p0 r, p1 r, p2 r, p3 r), (q1 r, q2 r, q3 r), (S.R / 72, 16 * S.R)) with hpcf
  -- real values of the carries
  have hρ0val : ∀ r : ℤ, ((p0 r : ℤ) : ℝ) =
      diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ)
        - diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) := by
    intro r
    rw [sec7_carry3_eq (Ph.f2D 0) (h₁ : ℝ) (h₂ : ℝ) (h₃ : ℝ) (r : ℝ)]
    simp only [hp0]
    push_cast
    ring
  have hρval : ∀ (cA cB : ℤ) (ξ : ℝ) (r : ℤ),
      ((⌊diff1 (cA : ℝ) (diff1 (cB : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ)⌋
          + sec7_carry2 (Ph.f2D 0) (cA : ℝ) (cB : ℝ) ((r : ℝ) + ξ) : ℤ) : ℝ) =
        diff1 (cA : ℝ) (diff1 (cB : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ)
          - Int.fract (diff1 (cA : ℝ) (diff1 (cB : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ)) := by
    intro cA cB ξ r
    have h := sec7_carry2_eq (Ph.f2D 0) (cA : ℝ) (cB : ℝ) ((r : ℝ) + ξ)
    have hfr := Int.self_sub_floor (diff1 (cA : ℝ) (diff1 (cB : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ))
    push_cast
    linarith
  have hdval : ∀ (cA cB : ℤ) (ξ : ℝ) (r : ℤ),
      ((⌊diff1 (cA : ℝ) (diff1 (cB : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ)⌋ : ℤ) : ℝ)
        - ((⌊diff1 (cA : ℝ) (diff1 (cB : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ)⌋
            + sec7_carry2 (Ph.f2D 0) (cA : ℝ) (cB : ℝ) ((r : ℝ) + ξ) : ℤ) : ℝ) =
        diff1 (cA : ℝ) (diff1 (cB : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ)
          - diff1 (cA : ℝ) (diff1 (cB : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ) := by
    intro cA cB ξ r
    have h := sec7_carry2_eq (Ph.f2D 0) (cA : ℝ) (cB : ℝ) ((r : ℝ) + ξ)
    push_cast
    linarith
  -- the carry bounds
  have hkey : ∀ r ∈ Finset.Icc lo hi,
      |((p0 r : ℤ) : ℝ)| ≤ 5 ∧ |((p1 r : ℤ) : ℝ)| ≤ 3 ∧ |((p2 r : ℤ) : ℝ)| ≤ 3 ∧
        |((p3 r : ℤ) : ℝ)| ≤ 3 := by
    intro r hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hρ0val r]
      have hg1 := habsF3 (r : ℝ)
      have hg2 := habsD3 r hr
      refine le_trans (abs_sub _ _) (by linarith)
    · rw [hp1, hq1]
      rw [hρval h₂ h₃ ξ₁ r]
      have hg1 := habsF2 (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₁)
      have hg2 := abs_fract_le (diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁))
      refine le_trans (abs_sub _ _) (by linarith)
    · rw [hp2, hq2]
      rw [hρval h₁ h₃ ξ₂ r]
      have hg1 := habsF2 (h₁ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₂)
      have hg2 := abs_fract_le (diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂))
      refine le_trans (abs_sub _ _) (by linarith)
    · rw [hp3, hq3]
      rw [hρval h₁ h₂ ξ₃ r]
      have hg1 := habsF2 (h₁ : ℝ) (h₂ : ℝ) ((r : ℝ) + ξ₃)
      have hg2 := abs_fract_le (diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃))
      refine le_trans (abs_sub _ _) (by linarith)
  refine ⟨⟨(Finset.Icc lo hi).image pcf, ?_, ?_, ?_⟩, ?_⟩
  · -- the count: `Λ ⊆ ρ-box ×ˢ fiber-image ×ˢ {interval}`, then eq (7.2)
    have hsubset : (Finset.Icc lo hi).image pcf ⊆
        (Finset.Icc (-5:ℤ) 5 ×ˢ Finset.Icc (-3:ℤ) 3 ×ˢ Finset.Icc (-3:ℤ) 3
            ×ˢ Finset.Icc (-3:ℤ) 3) ×ˢ
          ((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)) ×ˢ
          ({(S.R / 72, 16 * S.R)} : Finset (ℝ × ℝ)) := by
      intro pc hpc
      simp only [Finset.mem_image] at hpc
      obtain ⟨r, hr, rfl⟩ := hpc
      obtain ⟨hk0, hk1, hk2, hk3⟩ := hkey r hr
      simp only [hpcf, Finset.mem_product]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, Finset.mem_image_of_mem _ hr,
        Finset.mem_singleton_self _⟩
      · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk0))
      · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk1))
      · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk2))
      · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk3))
    have hucard : (((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)).card : ℝ) ≤
        4 + 2 * (sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
          + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
          + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ)) :=
      sec7_fiber_count hlohi
        (fun t => diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (t + ξ₁))
        (fun t => diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (t + ξ₂))
        (fun t => diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) (t + ξ₃))
        σ _ _ _ hσpm
        (fun r hr => hbd₁ (r : ℝ) (hmemr r hr).1 (hmemr r hr).2)
        (fun r hr => hbd₂ (r : ℝ) (hmemr r hr).1 (hmemr r hr).2)
        (fun r hr => hbd₃ (r : ℝ) (hmemr r hr).1 (hmemr r hr).2)
        (fun r hr r' hr' hle => hmono₁ (r : ℝ) (r' : ℝ) (hmemr r hr).1 (hmemr r' hr').2
          (by exact_mod_cast hle))
        (fun r hr r' hr' hle => hmono₂ (r : ℝ) (r' : ℝ) (hmemr r hr).1 (hmemr r' hr').2
          (by exact_mod_cast hle))
        (fun r hr r' hr' hle => hmono₃ (r : ℝ) (r' : ℝ) (hmemr r hr).1 (hmemr r' hr').2
          (by exact_mod_cast hle))
    have hc11 : (Finset.Icc (-5:ℤ) 5).card = 11 := by rw [Int.card_Icc]; rfl
    have hc7 : (Finset.Icc (-3:ℤ) 3).card = 7 := by rw [Int.card_Icc]; rfl
    calc (((Finset.Icc lo hi).image pcf).card : ℝ)
        ≤ (((Finset.Icc (-5:ℤ) 5 ×ˢ Finset.Icc (-3:ℤ) 3 ×ˢ Finset.Icc (-3:ℤ) 3
              ×ˢ Finset.Icc (-3:ℤ) 3) ×ˢ
            ((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)) ×ˢ
            ({(S.R / 72, 16 * S.R)} : Finset (ℝ × ℝ))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
      _ = 3773 * (((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)).card : ℝ) := by
          rw [Finset.card_product, Finset.card_product, Finset.card_product,
            Finset.card_product, Finset.card_product, Finset.card_singleton, hc11, hc7]
          push_cast
          ring
      _ ≤ 3773 * (4 + 2 * (sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
            + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
            + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ))) :=
          mul_le_mul_of_nonneg_left hucard (by norm_num)
      _ ≤ sec7_cMult * sec7_cPh * (1 + sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)) := by
          have hsum : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
              + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
              + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ)
              = sec7_cPh * (sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)) := by
            rw [show S.T₂ / S.R ^ 2 = 1 / (P.G * S.Ω ^ 5) from sec7_T₂_div_R_sq S]
            simp only [sec7_Ssym]
            field_simp
            ring
          rw [hsum]
          have hq : (0:ℝ) ≤ sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5) :=
            div_nonneg hSsym0 (by positivity)
          simp only [sec7_cMult, sec7_cPh, sec7_cPh]
          nlinarith
  · -- per-piece carry/fiber sizes and the interval inclusion
    intro pc hpc
    simp only [Finset.mem_image] at hpc
    obtain ⟨r, hr, rfl⟩ := hpc
    obtain ⟨hk0, hk1, hk2, hk3⟩ := hkey r hr
    obtain ⟨hr1, hr2⟩ := hmemr r hr
    have hcC : sec7_cCarry = (10:ℝ) ^ 6 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact le_trans hk0 (by rw [hcC]; norm_num)
    · exact le_trans hk1 (by rw [hcC]; norm_num)
    · exact le_trans hk2 (by rw [hcC]; norm_num)
    · exact le_trans hk3 (by rw [hcC]; norm_num)
    · -- `|u₁ − ρ₁| ≤ cFib·(1 + h₂h₃·T₂/R²)`
      show |((q1 r : ℤ) : ℝ) - ((p1 r : ℤ) : ℝ)| ≤
        sec7_cPh * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))
      rw [hp1, hq1, hdval h₂ h₃ ξ₁ r]
      have hg1 := hbd₁ (r : ℝ) hr1 hr2
      have hg2 := habsF2 (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₁)
      refine le_trans (abs_sub _ _) ?_
      have hq : (0:ℝ) ≤ (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have he : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
          = sec7_cPh * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by ring
      simp only [sec7_cPh, sec7_cPh] at he ⊢
      linarith [he ▸ hg1]
    · show |((q2 r : ℤ) : ℝ) - ((p2 r : ℤ) : ℝ)| ≤
        sec7_cPh * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))
      rw [hp2, hq2, hdval h₁ h₃ ξ₂ r]
      have hg1 := hbd₂ (r : ℝ) hr1 hr2
      have hg2 := habsF2 (h₁ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₂)
      refine le_trans (abs_sub _ _) ?_
      have hq : (0:ℝ) ≤ (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have he : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
          = sec7_cPh * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by ring
      simp only [sec7_cPh, sec7_cPh] at he ⊢
      linarith [he ▸ hg1]
    · show |((q3 r : ℤ) : ℝ) - ((p3 r : ℤ) : ℝ)| ≤
        sec7_cPh * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))
      rw [hp3, hq3, hdval h₁ h₂ ξ₃ r]
      have hg1 := hbd₃ (r : ℝ) hr1 hr2
      have hg2 := habsF2 (h₁ : ℝ) (h₂ : ℝ) ((r : ℝ) + ξ₃)
      refine le_trans (abs_sub _ _) ?_
      have hq : (0:ℝ) ≤ (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have he : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ)
          = sec7_cPh * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)) := by ring
      simp only [sec7_cPh, sec7_cPh] at he ⊢
      linarith [he ▸ hg1]
    · exact fun y hy => hy
  · -- the cover and the on-piece fixed-integer-data identities
    intro r hr
    refine ⟨pcf r, Finset.mem_image_of_mem _ hr, ?_, ?_, ?_, ?_, ?_⟩
    · exact Set.mem_Icc.mpr (hmemr r hr)
    · show diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
        diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + ((p0 r : ℤ) : ℝ)
      rw [hρ0val r]
      ring
    · show diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
        diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
          - ((q1 r : ℤ) : ℝ) + ((p1 r : ℤ) : ℝ)
      rw [hp1, hq1]
      rw [sec7_carry2_eq (Ph.f2D 0) (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₁)]
      push_cast
      ring
    · show diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
        diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
          - ((q2 r : ℤ) : ℝ) + ((p2 r : ℤ) : ℝ)
      rw [hp2, hq2]
      rw [sec7_carry2_eq (Ph.f2D 0) (h₁ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₂)]
      push_cast
      ring
    · show diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
        diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
          - ((q3 r : ℤ) : ℝ) + ((p3 r : ℤ) : ℝ)
      rw [hp3, hq3]
      rw [sec7_carry2_eq (Ph.f2D 0) (h₁ : ℝ) (h₂ : ℝ) ((r : ℝ) + ξ₃)]
      push_cast
      ring
  · refine ⟨((Finset.Icc lo hi).filter (fun r : ℤ => p0 r = 0)).image pcf,
      ?_, ?_, ?_, ?_⟩
    · -- sharp zero-top-carry count: `{0} × [-3,3]^3 × fiber × interval`
      have hsubset : ((Finset.Icc lo hi).filter (fun r : ℤ => p0 r = 0)).image pcf ⊆
          (({(0 : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-3:ℤ) 3 ×ˢ Finset.Icc (-3:ℤ) 3
              ×ˢ Finset.Icc (-3:ℤ) 3) ×ˢ
            ((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)) ×ˢ
            ({(S.R / 72, 16 * S.R)} : Finset (ℝ × ℝ)) := by
        intro pc hpc
        simp only [Finset.mem_image] at hpc
        obtain ⟨r, hr0, rfl⟩ := hpc
        obtain ⟨hr, hp0z⟩ := Finset.mem_filter.mp hr0
        obtain ⟨_hk0, hk1, hk2, hk3⟩ := hkey r hr
        simp only [hpcf, Finset.mem_product]
        refine ⟨⟨?_, ?_, ?_, ?_⟩, Finset.mem_image_of_mem _ hr,
          Finset.mem_singleton_self _⟩
        · simp [hp0z]
        · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk1))
        · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk2))
        · exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast hk3))
      have hucard : (((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)).card : ℝ) ≤
          4 + 2 * (sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
            + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
            + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ)) :=
        sec7_fiber_count hlohi
          (fun t => diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (t + ξ₁))
          (fun t => diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) (t + ξ₂))
          (fun t => diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) (t + ξ₃))
          σ _ _ _ hσpm
          (fun r hr => hbd₁ (r : ℝ) (hmemr r hr).1 (hmemr r hr).2)
          (fun r hr => hbd₂ (r : ℝ) (hmemr r hr).1 (hmemr r hr).2)
          (fun r hr => hbd₃ (r : ℝ) (hmemr r hr).1 (hmemr r hr).2)
          (fun r hr r' hr' hle => hmono₁ (r : ℝ) (r' : ℝ) (hmemr r hr).1 (hmemr r' hr').2
            (by exact_mod_cast hle))
          (fun r hr r' hr' hle => hmono₂ (r : ℝ) (r' : ℝ) (hmemr r hr).1 (hmemr r' hr').2
            (by exact_mod_cast hle))
          (fun r hr r' hr' hle => hmono₃ (r : ℝ) (r' : ℝ) (hmemr r hr).1 (hmemr r' hr').2
            (by exact_mod_cast hle))
      have hc7 : (Finset.Icc (-3:ℤ) 3).card = 7 := by rw [Int.card_Icc]; rfl
      calc ((((Finset.Icc lo hi).filter (fun r : ℤ => p0 r = 0)).image pcf).card : ℝ)
          ≤ (((({(0 : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-3:ℤ) 3 ×ˢ
                  Finset.Icc (-3:ℤ) 3 ×ˢ Finset.Icc (-3:ℤ) 3) ×ˢ
              ((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)) ×ˢ
              ({(S.R / 72, 16 * S.R)} : Finset (ℝ × ℝ))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
        _ = 343 * (((Finset.Icc lo hi).image fun r : ℤ => (q1 r, q2 r, q3 r)).card : ℝ) := by
            rw [Finset.card_product, Finset.card_product, Finset.card_product,
              Finset.card_product, Finset.card_product, Finset.card_singleton,
              Finset.card_singleton, hc7]
            push_cast
            ring
        _ ≤ 343 * (4 + 2 * (sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
              + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
              + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ))) :=
            mul_le_mul_of_nonneg_left hucard (by norm_num)
        _ ≤ 343 *
            (4 + 2 * (sec7_cPh * (sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)))) := by
            have hsum : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
                + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
                + sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ)
                = sec7_cPh * (sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)) := by
              rw [show S.T₂ / S.R ^ 2 = 1 / (P.G * S.Ω ^ 5) from sec7_T₂_div_R_sq S]
              simp only [sec7_Ssym]
              field_simp
              ring
            rw [hsum]
    · intro pc hpc
      simp only [Finset.mem_image] at hpc
      obtain ⟨r, hr0, rfl⟩ := hpc
      exact (Finset.mem_filter.mp hr0).2
    · intro pc hpc
      simp only [Finset.mem_image] at hpc
      obtain ⟨r, hr0, rfl⟩ := hpc
      obtain ⟨hr, _hp0z⟩ := Finset.mem_filter.mp hr0
      obtain ⟨hk0, hk1, hk2, hk3⟩ := hkey r hr
      obtain ⟨hr1, hr2⟩ := hmemr r hr
      have hcC : sec7_cCarry = (10:ℝ) ^ 6 := rfl
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact le_trans hk0 (by rw [hcC]; norm_num)
      · exact le_trans hk1 (by rw [hcC]; norm_num)
      · exact le_trans hk2 (by rw [hcC]; norm_num)
      · exact le_trans hk3 (by rw [hcC]; norm_num)
      · show |((q1 r : ℤ) : ℝ) - ((p1 r : ℤ) : ℝ)| ≤
          sec7_cPh * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))
        rw [hp1, hq1, hdval h₂ h₃ ξ₁ r]
        have hg1 := hbd₁ (r : ℝ) hr1 hr2
        have hg2 := habsF2 (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₁)
        refine le_trans (abs_sub _ _) ?_
        have hq : (0:ℝ) ≤ (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
        have he : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₂ : ℝ)
            = sec7_cPh * ((h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by ring
        simp only [sec7_cPh, sec7_cPh] at he ⊢
        linarith [he ▸ hg1]
      · show |((q2 r : ℤ) : ℝ) - ((p2 r : ℤ) : ℝ)| ≤
          sec7_cPh * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2))
        rw [hp2, hq2, hdval h₁ h₃ ξ₂ r]
        have hg1 := hbd₂ (r : ℝ) hr1 hr2
        have hg2 := habsF2 (h₁ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₂)
        refine le_trans (abs_sub _ _) ?_
        have hq : (0:ℝ) ≤ (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2) :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
        have he : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₃ : ℝ) * (h₁ : ℝ)
            = sec7_cPh * ((h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) := by ring
        simp only [sec7_cPh, sec7_cPh] at he ⊢
        linarith [he ▸ hg1]
      · show |((q3 r : ℤ) : ℝ) - ((p3 r : ℤ) : ℝ)| ≤
          sec7_cPh * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))
        rw [hp3, hq3, hdval h₁ h₂ ξ₃ r]
        have hg1 := hbd₃ (r : ℝ) hr1 hr2
        have hg2 := habsF2 (h₁ : ℝ) (h₂ : ℝ) ((r : ℝ) + ξ₃)
        refine le_trans (abs_sub _ _) ?_
        have hq : (0:ℝ) ≤ (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2) :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
        have he : sec7_cPh * (S.T₂ / S.R ^ 2) * (h₂ : ℝ) * (h₁ : ℝ)
            = sec7_cPh * ((h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2)) := by ring
        simp only [sec7_cPh, sec7_cPh] at he ⊢
        linarith [he ▸ hg1]
      · exact fun y hy => hy
    · intro r hr hzero
      have hp0z : p0 r = 0 := by
        have hcast : ((p0 r : ℤ) : ℝ) = 0 := by
          rw [hρ0val r]
          linarith
        exact_mod_cast hcast
      refine ⟨pcf r, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr, hp0z⟩),
        ?_, ?_, ?_, ?_, ?_⟩
      · exact Set.mem_Icc.mpr (hmemr r hr)
      · show diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + ((p0 r : ℤ) : ℝ)
        rw [hρ0val r]
        ring
      · show diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
          diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
            - ((q1 r : ℤ) : ℝ) + ((p1 r : ℤ) : ℝ)
        rw [hp1, hq1]
        rw [sec7_carry2_eq (Ph.f2D 0) (h₂ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₁)]
        push_cast
        ring
      · show diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
          diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
            - ((q2 r : ℤ) : ℝ) + ((p2 r : ℤ) : ℝ)
        rw [hp2, hq2]
        rw [sec7_carry2_eq (Ph.f2D 0) (h₁ : ℝ) (h₃ : ℝ) ((r : ℝ) + ξ₂)]
        push_cast
        ring
      · show diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
          diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
            - ((q3 r : ℤ) : ℝ) + ((p3 r : ℤ) : ℝ)
        rw [hp3, hq3]
        rw [sec7_carry2_eq (Ph.f2D 0) (h₁ : ℝ) (h₂ : ℝ) ((r : ℝ) + ξ₃)]
        push_cast
        ring

end Squarefree
