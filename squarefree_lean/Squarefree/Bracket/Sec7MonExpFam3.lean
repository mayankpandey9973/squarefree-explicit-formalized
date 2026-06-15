import Squarefree.Bracket.Sec7MonExpData

/-!
# §7 N9′ family lemmas D: the triple differences `B₀₃`, `Δf₃` (md 1623–33)

The differenced-monomial expansion lemmas consumed by the N9′ constructor
(`sec7_monExp_build`, `Sec7MonExpBuild.lean`); see `Sec7MonExpData.lean` for the input
pack and the A3 gate provenance.  N9′-internal: only the constructor should use these.
-/

open Classical Finset Set Real Squarefree.FiniteDiff

namespace Squarefree

set_option maxHeartbeats 1600000

namespace Sec7RaExpData

variable {P : Globals} {S : Scale P} {W : ℝ} {a : ℤ} {Ph : Sec7Phase P S W a} {j : ℤ}
variable {h₁ h₂ h₃ : ℤ}

/-- **N9′ family D, generic core** (md 1623–33): the graded triple-difference expansion
of a piece `f = c·T·y^α + e` with graded error chains `e`, against the leading monomial
`c·(∏_{i<3}(α−i))·P·(T/R³)·y^{α−3}`.  `Ap` bounds the falling factorials to order 6, `Kb`
the window power `(2cWin)^{6−α}`, and `|c|·Ap·Kb ≤ cExp` is the sympy-banked budget. -/
private theorem build_diff3_generic {P : Globals} {S : Scale P} {W : ℝ} {h₁ h₂ h₃ : ℤ}
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4))
    {f : ℝ → ℝ} {e : ℕ → ℝ → ℝ} {c α T Ap Kb rel : ℝ}
    (hT : 0 < T) (hα1 : α ≤ 1) (hrel : 0 < rel)
    (he0 : ∀ t, e 0 t = f t - c * T * (t / S.R) ^ α)
    (hed : ∀ m < 5, ∀ x ∈ sec7_rWinWide S W, HasDerivAt (e m) (e (m + 1) x) x)
    (heb : ∀ m ≤ 5, ∀ x ∈ sec7_rWinWide S W,
      |e m x| ≤ sec7_cExpIn * (T / S.R ^ m) * rel)
    (hap : ∀ k ≤ 6, |sec7_aprod α k| ≤ Ap)
    (hKb : (2 * sec7_cWin) ^ ((6:ℝ) - α) ≤ Kb)
    (hcoefb : |c| * Ap * Kb ≤ sec7_cExp) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t => diff3 (h₁:ℝ) h₂ h₃ f t -
          c * sec7_aprod α 3 * sec7_Pprod h₁ h₂ h₃ * (T / S.R ^ 3) *
            (t / S.R) ^ (α - 3)) r| ≤
        sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (T / S.R ^ 3) * rel +
          sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * T / S.R ^ 4) / S.R ^ m := by
  intro m hm r hr
  have hR : 0 < S.R := sec7_R_pos S
  have hcWpos : (0:ℝ) < 2 * sec7_cWin := by norm_num [sec7_cWin]
  set hSv : ℝ := sec7_hSum h₁ h₂ h₃ with hSv_def
  have hSv3 : (3:ℝ) ≤ hSv := sec7_hSum_ge3 hh₁ hh₂ hh₃
  have hSv0 : (0:ℝ) ≤ hSv := by linarith
  have hv1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hh₁
  have hv2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hh₂
  have hv3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hh₃
  have hsum : hSv = (h₁:ℝ) + h₂ + h₃ := by rw [hSv_def]; rfl
  set PP : ℝ := sec7_Pprod h₁ h₂ h₃ with hPP
  have hPPval : PP = (h₁:ℝ) * h₂ * h₃ := by rw [hPP]; rfl
  have hPP1 : (1:ℝ) ≤ PP := by
    rw [hPPval]
    have h12 : (1:ℝ) ≤ (h₁:ℝ) * h₂ := by nlinarith
    nlinarith
  have hPP0 : (0:ℝ) < PP := by linarith
  have hrmid : r ∈ sec7_rWinMid S W := sec7_rWin_subset_mid S hW hr
  set M : ℕ → ℝ → ℝ := sec7_powMonD S.R (c * T) α with hM
  set G : ℕ → ℝ → ℝ := fun k t => diff3 (h₁:ℝ) h₂ h₃ (e k) t +
    (diff3 (h₁:ℝ) h₂ h₃ (M k) t - PP * M (k + 3) t) with hG
  have hmem : ∀ x ∈ sec7_rWinMid S W, ∀ d : ℝ, |d| ≤ 3 * hSv →
      x + d ∈ sec7_rWinWide S W :=
    fun x hx d hd => sec7_mem_wide_of_near hx (by
      rw [hSv_def] at hd
      exact le_trans hd hshift)
  have hseg : ∀ x ∈ sec7_rWinMid S W, ∀ y : ℝ, 0 ≤ y - x → y - x ≤ hSv →
      y ∈ sec7_rWinWide S W := by
    intro x hx y hd1 hd2
    have hy : y = x + (y - x) := by ring
    rw [hy]
    exact hmem x hx (y - x) (by rw [abs_of_nonneg hd1]; linarith)
  -- derivative chains of the triple differences
  have heDDD : ∀ k < 4, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (diff3 (h₁:ℝ) h₂ h₃ (e k)) (diff3 (h₁:ℝ) h₂ h₃ (e (k + 1)) x) x := by
    intro k hk x hx
    simp only [diff3]
    apply sec7_diff1_hasDerivAt <;> apply sec7_diff1_hasDerivAt <;>
      apply sec7_diff1_hasDerivAt <;>
      exact hed k (by omega) _
        (hseg x hx _ (by linarith) (by rw [hsum]; linarith))
  have hMDDD : ∀ k, ∀ x ∈ sec7_rWinMid S W,
      HasDerivAt (diff3 (h₁:ℝ) h₂ h₃ (M k)) (diff3 (h₁:ℝ) h₂ h₃ (M (k + 1)) x) x := by
    intro k x hx
    simp only [diff3]
    apply sec7_diff1_hasDerivAt <;> apply sec7_diff1_hasDerivAt <;>
      apply sec7_diff1_hasDerivAt <;>
      exact sec7_powMonD_hasDerivAt hR _ _ _ (sec7_rWinWide_pos hpad
        (hseg x hx _ (by linarith) (by rw [hsum]; linarith)))
  have hchain : ∀ k < 2, ∀ x ∈ sec7_rWinMid S W, HasDerivAt (G k) (G (k + 1) x) x := by
    intro k hk x hx
    have hxw : x ∈ sec7_rWinWide S W := by
      simpa using hmem x hx 0 (by rw [abs_zero]; linarith)
    have hx0 : 0 < x := sec7_rWinWide_pos hpad hxw
    have d3 : HasDerivAt (fun t => PP * M (k + 3) t) (PP * M (k + 4) x) x :=
      (sec7_powMonD_hasDerivAt hR _ _ (k + 3) hx0).const_mul PP
    have := (heDDD k (by omega) x hx).add ((hMDDD k x hx).sub d3)
    simpa [hG] using this
  -- explicit grade-0/3 monomials
  have hM0 : ∀ s : ℝ, M 0 s = c * T * (s / S.R) ^ α := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    rw [show sec7_aprod α 0 = 1 from rfl]
    norm_num
  have hM3 : ∀ s : ℝ, M 3 s = c * T * sec7_aprod α 3 / S.R ^ 3 * (s / S.R) ^ (α - 3) := by
    intro s; rw [hM]; unfold sec7_powMonD sec7_powMon
    norm_num
  -- grade-0 identification
  have hG0 : (fun t => diff3 (h₁:ℝ) h₂ h₃ f t -
      c * sec7_aprod α 3 * PP * (T / S.R ^ 3) * (t / S.R) ^ (α - 3)) = G 0 := by
    funext t
    simp only [hG, diff3, diff1, he0, hM0, hM3]
    ring
  rw [hG0, sec7_iteratedDeriv_eq_of_chain (sec7_rWinMid_isOpen S W) hchain m hm r hrmid]
  have hsegr : ∀ y : ℝ, 0 ≤ y - r → y - r ≤ hSv → y ∈ sec7_rWinWide S W :=
    hseg r hrmid
  -- e-part bound: three nested first-difference MVT inequalities
  set C : ℝ := sec7_cExpIn * (T / S.R ^ (m + 3)) * rel with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg sec7_cExpIn_pos.le
      (div_nonneg hT.le (pow_nonneg hR.le _))) hrel.le
  have hepart : |diff3 (h₁:ℝ) h₂ h₃ (e m) r| ≤ C * h₃ * h₂ * h₁ := by
    simp only [diff3]
    apply sec7_diff1_abs_le (by linarith : (0:ℝ) ≤ (h₁:ℝ))
    · intro y hy
      apply sec7_diff1_hasDerivAt <;> apply sec7_diff1_hasDerivAt <;>
        exact hed m (by omega) _
          (hsegr _ (by linarith [hy.1]) (by rw [hsum]; linarith [hy.2]))
    · intro y hy
      apply sec7_diff1_abs_le (by linarith : (0:ℝ) ≤ (h₂:ℝ))
      · intro z hz
        apply sec7_diff1_hasDerivAt <;>
          exact hed (m + 1) (by omega) _
            (hsegr _ (by linarith [hy.1, hz.1]) (by rw [hsum]; linarith [hy.2, hz.2]))
      · intro z hz
        apply sec7_diff1_abs_le (by linarith : (0:ℝ) ≤ (h₃:ℝ))
        · intro w hw
          exact hed (m + 2) (by omega) _
            (hsegr _ (by linarith [hy.1, hz.1, hw.1])
              (by rw [hsum]; linarith [hy.2, hz.2, hw.2]))
        · intro w hw
          rw [hC]
          exact heb (m + 3) (by omega) _
            (hsegr _ (by linarith [hy.1, hz.1, hw.1])
              (by rw [hsum]; linarith [hy.2, hz.2, hw.2]))
  -- monomial sup bound at order m+4
  have hAp0 : (0:ℝ) ≤ Ap := le_trans (abs_nonneg _) (hap 0 (by omega))
  have hKb0 : (0:ℝ) ≤ Kb :=
    le_trans (Real.rpow_pos_of_pos hcWpos _).le hKb
  set B : ℝ := |c| * T * Ap * Kb / S.R ^ (m + 4) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    have : (0:ℝ) ≤ |c| * T * Ap * Kb :=
      mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c) hT.le) hAp0) hKb0
    exact div_nonneg this (pow_nonneg hR.le _)
  have hMbd : ∀ x ∈ sec7_rWinWide S W, |M (m + 4) x| ≤ B := by
    intro x hx
    have hbd := sec7_powMonD_wide_bound (c := c * T) (α := α) (k := m + 4)
      (by have h0 : (0:ℝ) ≤ (m:ℝ) := by positivity
          push_cast; linarith) hpad hx
    have hexple : (2 * sec7_cWin) ^ (((m + 4 : ℕ) : ℝ) - α) ≤ Kb := by
      refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num [sec7_cWin]) ?_) hKb
      have hm6 : ((m + 4 : ℕ) : ℝ) ≤ 6 := by
        have : ((m + 4 : ℕ) : ℝ) = (m:ℝ) + 4 := by push_cast; ring
        rw [this]
        have : (m:ℝ) ≤ 2 := by exact_mod_cast hm
        linarith
      linarith
    have habs : |c * T| = |c| * T := by rw [abs_mul, abs_of_pos hT]
    have hcoefnn : (0:ℝ) ≤ |c * T| * |sec7_aprod α (m + 4)| / S.R ^ (m + 4) := by
      positivity
    have h1 : |c| * T * |sec7_aprod α (m + 4)| ≤ |c| * T * Ap :=
      mul_le_mul_of_nonneg_left (hap (m + 4) (by omega))
        (mul_nonneg (abs_nonneg c) hT.le)
    calc |M (m + 4) x| ≤ |c * T| * |sec7_aprod α (m + 4)| / S.R ^ (m + 4) *
          (2 * sec7_cWin) ^ (((m + 4 : ℕ) : ℝ) - α) := by rw [hM]; exact hbd
      _ ≤ |c * T| * |sec7_aprod α (m + 4)| / S.R ^ (m + 4) * Kb :=
          mul_le_mul_of_nonneg_left hexple hcoefnn
      _ ≤ |c| * T * Ap / S.R ^ (m + 4) * Kb := by
          rw [habs]
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right h1 (pow_nonneg hR.le _)) hKb0
      _ = B := by rw [hB]; ring
  -- exact triple MVT for the monomial triple difference
  have hMch : ∀ k, ∀ y : ℝ, 0 ≤ y - r → y - r ≤ hSv →
      HasDerivAt (M k) (M (k + 1) y) y := by
    intro k y hd1 hd2
    rw [hM]
    exact sec7_powMonD_hasDerivAt hR _ _ k (sec7_rWinWide_pos hpad (hsegr y hd1 hd2))
  obtain ⟨ζ₁, hζ₁, hA1⟩ := sec7_diff_eq_mul_deriv
    (g := diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (M m)))
    (g' := diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (M (m + 1)))) (s := r) (h := (h₁:ℝ))
    (by linarith)
    (by
      intro y hy
      apply sec7_diff1_hasDerivAt <;> apply sec7_diff1_hasDerivAt <;>
        exact hMch m _ (by linarith [hy.1]) (by rw [hsum]; linarith [hy.2]))
  obtain ⟨ζ₂, hζ₂, hA2⟩ := sec7_diff_eq_mul_deriv
    (g := diff1 (h₃:ℝ) (M (m + 1))) (g' := diff1 (h₃:ℝ) (M (m + 2))) (s := ζ₁)
    (h := (h₂:ℝ)) (by linarith)
    (by
      intro y hy
      apply sec7_diff1_hasDerivAt <;>
        exact hMch (m + 1) _ (by linarith [hy.1, hζ₁.1])
          (by rw [hsum]; linarith [hy.2, hζ₁.2]))
  obtain ⟨ζ₃, hζ₃, hA3⟩ := sec7_diff_eq_mul_deriv
    (g := M (m + 2)) (g' := M (m + 3)) (s := ζ₂) (h := (h₃:ℝ)) (by linarith)
    (by
      intro y hy
      exact hMch (m + 2) _ (by linarith [hy.1, hζ₁.1, hζ₂.1])
        (by rw [hsum]; linarith [hy.2, hζ₁.2, hζ₂.2]))
  have hζ₃lo : r < ζ₃ := by linarith [hζ₁.1, hζ₂.1, hζ₃.1]
  have hζ₃hi : ζ₃ - r ≤ hSv := by rw [hsum]; linarith [hζ₁.2, hζ₂.2, hζ₃.2]
  have hDD : diff3 (h₁:ℝ) h₂ h₃ (M m) r = PP * M (m + 3) ζ₃ := by
    have e1 : diff3 (h₁:ℝ) h₂ h₃ (M m) r =
        (h₁:ℝ) * diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (M (m + 1))) ζ₁ := by
      have h0 := hA1
      simpa [diff3, diff1] using h0
    have e2 : diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (M (m + 1))) ζ₁ =
        (h₂:ℝ) * diff1 (h₃:ℝ) (M (m + 2)) ζ₂ := by
      have h0 := hA2
      simpa [diff1] using h0
    have e3 : diff1 (h₃:ℝ) (M (m + 2)) ζ₂ = (h₃:ℝ) * M (m + 3) ζ₃ := by
      have h0 := hA3
      simpa [diff1] using h0
    rw [e1, e2, e3, hPPval]; ring
  -- drift of the order-(m+3) monomial from ζ₃ back to r
  have hdrift : |M (m + 3) ζ₃ - M (m + 3) r| ≤ B * hSv := by
    have hin : ∀ x ∈ Icc r ζ₃, x ∈ sec7_rWinWide S W := by
      intro x hx
      exact hsegr x (by linarith [hx.1]) (by linarith [hx.2, hζ₃hi])
    have := sec7_abs_sub_le_of_deriv (g := M (m + 3)) (g' := M (m + 4))
      (a := r) (b := ζ₃) hζ₃lo.le
      (fun x hx => by
        rw [hM]
        exact sec7_powMonD_hasDerivAt hR _ _ (m + 3)
          (sec7_rWinWide_pos hpad (hin x hx)))
      (fun x hx => hMbd x (hin x hx))
    calc |M (m + 3) ζ₃ - M (m + 3) r| ≤ B * (ζ₃ - r) := this
      _ ≤ B * hSv := mul_le_mul_of_nonneg_left hζ₃hi hBnn
  have hmon : |diff3 (h₁:ℝ) h₂ h₃ (M m) r - PP * M (m + 3) r| ≤ PP * (B * hSv) := by
    rw [hDD]
    have h0 : PP * M (m + 3) ζ₃ - PP * M (m + 3) r =
        PP * (M (m + 3) ζ₃ - M (m + 3) r) := by ring
    rw [h0, abs_mul, abs_of_pos hPP0]
    exact mul_le_mul_of_nonneg_left hdrift hPP0.le
  -- assemble
  have hsplit : |G m r| ≤ C * h₃ * h₂ * h₁ + PP * (B * hSv) := by
    have h1 : |G m r| ≤ |diff3 (h₁:ℝ) h₂ h₃ (e m) r| +
        |diff3 (h₁:ℝ) h₂ h₃ (M m) r - PP * M (m + 3) r| := by
      simp only [hG]
      exact abs_add_le _ _
    linarith [hepart, hmon]
  refine le_trans hsplit ?_
  -- numerics
  have hkey1 : C * h₃ * h₂ * h₁ ≤
      sec7_cExp * (PP * (T / S.R ^ 3) * rel) / S.R ^ m := by
    have hIn : sec7_cExpIn ≤ sec7_cExp := by norm_num [sec7_cExpIn, sec7_cExp]
    have hmono : (0:ℝ) ≤ PP * (T / S.R ^ 3) * rel / S.R ^ m := by
      have h0 : (0:ℝ) ≤ PP * (T / S.R ^ 3) * rel :=
        mul_nonneg (mul_nonneg hPP0.le
          (div_nonneg hT.le (pow_nonneg hR.le _))) hrel.le
      exact div_nonneg h0 (pow_nonneg hR.le _)
    calc C * h₃ * h₂ * h₁
        = sec7_cExpIn * (PP * (T / S.R ^ 3) * rel / S.R ^ m) := by
          rw [hC, hPPval, pow_add]
          field_simp
          try ring
      _ ≤ sec7_cExp * (PP * (T / S.R ^ 3) * rel / S.R ^ m) :=
          mul_le_mul_of_nonneg_right hIn hmono
      _ = sec7_cExp * (PP * (T / S.R ^ 3) * rel) / S.R ^ m := by ring
  have hkey2 : PP * (B * hSv) ≤ sec7_cExp * (PP * hSv * T / S.R ^ 4) / S.R ^ m := by
    have hmono : (0:ℝ) ≤ PP * hSv * T / S.R ^ (m + 4) := by
      have h0 : (0:ℝ) ≤ PP * hSv * T :=
        mul_nonneg (mul_nonneg hPP0.le hSv0) hT.le
      exact div_nonneg h0 (pow_nonneg hR.le _)
    calc PP * (B * hSv)
        = |c| * Ap * Kb * (PP * hSv * T / S.R ^ (m + 4)) := by rw [hB]; ring
      _ ≤ sec7_cExp * (PP * hSv * T / S.R ^ (m + 4)) :=
          mul_le_mul_of_nonneg_right hcoefb hmono
      _ = sec7_cExp * (PP * hSv * T / S.R ^ 4) / S.R ^ m := by
          rw [pow_add]
          field_simp
  calc C * h₃ * h₂ * h₁ + PP * (B * hSv)
      ≤ sec7_cExp * (PP * (T / S.R ^ 3) * rel) / S.R ^ m +
        sec7_cExp * (PP * hSv * T / S.R ^ 4) / S.R ^ m := by linarith [hkey1, hkey2]
    _ = sec7_cExp * (PP * (T / S.R ^ 3) * rel +
        PP * hSv * T / S.R ^ 4) / S.R ^ m := by ring

/-- **N9′ family D, `B₀₃` instance** (md 1623–27): the triple-differenced `f₂` expansion,
graded `m ≤ 2`. -/
theorem build_B03_exp (RE : Sec7RaExpData P S W a Ph j)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) t -
            (15/64) * RE.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) *
              (t / S.R) ^ (-(9:ℝ)/4)) r| ≤
        sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) * sec7_relErr P S +
          sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₂ / S.R ^ 4) / S.R ^ m := by
  intro m hm r hr
  have hgen := build_diff3_generic hh₁ hh₂ hh₃ hW hpad hshift (f := Ph.f2D 0) (e := RE.e₂D)
    (c := RE.c₂) (α := (3:ℝ)/4) (T := S.T₂) (Ap := 8) (Kb := (2 * sec7_cWin) ^ 6)
    (sec7_T₂_pos S) (by norm_num) (sec7_relErr_pos P S) RE.e₂D_zero RE.e₂D_deriv
    RE.e₂D_bound
    (by intro k hk; interval_cases k <;> norm_num [sec7_aprod])
    (by
      have h1 := Real.rpow_le_rpow_of_exponent_le
        (show (1:ℝ) ≤ 2 * sec7_cWin by norm_num [sec7_cWin])
        (show (6:ℝ) - 3/4 ≤ ((6:ℕ):ℝ) by norm_num)
      rwa [Real.rpow_natCast] at h1)
    (by
      have hc := RE.c₂_hi
      have hKnn : (0:ℝ) ≤ (2 * sec7_cWin) ^ 6 := by positivity
      have h1 : |RE.c₂| * 8 * (2 * sec7_cWin) ^ 6 ≤ 4 * 8 * (2 * sec7_cWin) ^ 6 := by
        nlinarith [abs_nonneg RE.c₂]
      refine le_trans h1 ?_
      norm_num [sec7_cWin, sec7_cExp])
    m hm r hr
  have hfun : (fun t => diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) t -
      (15/64) * RE.c₂ * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) *
        (t / S.R) ^ (-(9:ℝ)/4)) =
      (fun t => diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) t -
      RE.c₂ * sec7_aprod ((3:ℝ)/4) 3 * sec7_Pprod h₁ h₂ h₃ * (S.T₂ / S.R ^ 3) *
        (t / S.R) ^ ((3:ℝ)/4 - 3)) := by
    funext t
    rw [show sec7_aprod ((3:ℝ)/4) 3 = 15/64 from by norm_num [sec7_aprod],
      show (3:ℝ)/4 - 3 = -(9:ℝ)/4 from by norm_num]
    ring
  rw [hfun]
  exact hgen

/-- **N9′ family D, `Δf₃` instance** (md 1628–33): the triple-differenced `f₃` expansion,
graded `m ≤ 2`. -/
theorem build_d3f3_exp (RE : Sec7RaExpData P S W a Ph j)
    (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) (hh₃ : 1 ≤ h₃)
    (hW : 0 < W) (hpad : 6 * (W + W ^ 2 + W ^ 4) ≤ S.R / 288)
    (hshift : 3 * sec7_hSum h₁ h₂ h₃ ≤ 3 * (W + W ^ 2 + W ^ 4)) :
    ∀ m ≤ 2, ∀ r ∈ sec7_rWin S W,
      |iteratedDeriv m (fun t =>
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) t -
            (-(45/64) * (3 * RE.c₁ * RE.c₂) * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) *
              (t / S.R) ^ (-(13:ℝ)/4))) r| ≤
        sec7_cExp * (sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) * sec7_relErrF P S +
          sec7_Pprod h₁ h₂ h₃ * sec7_hSum h₁ h₂ h₃ * S.T₃ / S.R ^ 4) / S.R ^ m := by
  intro m hm r hr
  have hgen := build_diff3_generic hh₁ hh₂ hh₃ hW hpad hshift (f := Ph.f3D j 0) (e := RE.e₃D)
    (c := 3 * RE.c₁ * RE.c₂) (α := -(1:ℝ)/4) (T := S.T₃) (Ap := 51)
    (Kb := 10 ^ 21)
    (sec7_T₃_pos S) (by norm_num) (sec7_relErrF_pos P S) RE.e₃D_zero RE.e₃D_deriv
    RE.e₃D_bound
    (by intro k hk; interval_cases k <;> norm_num [sec7_aprod])
    (by
      have h1 : ((6:ℝ) - -(1:ℝ)/4) = ((25:ℕ):ℝ) / 4 := by push_cast; norm_num
      rw [h1]
      apply sec7_rpow_quarter_le (by norm_num)
      norm_num [sec7_cWin])
    (by
      have hc1 := RE.c₁_hi
      have hc2 := RE.c₂_hi
      have habs : |3 * RE.c₁ * RE.c₂| = 3 * |RE.c₁| * |RE.c₂| := by
        rw [abs_mul, abs_mul]; norm_num
      have h48 : |3 * RE.c₁ * RE.c₂| ≤ 48 := by
        rw [habs]
        nlinarith [abs_nonneg RE.c₁, abs_nonneg RE.c₂]
      have h1 : |3 * RE.c₁ * RE.c₂| * 51 * (10:ℝ) ^ 21 ≤ 48 * 51 * (10:ℝ) ^ 21 := by
        nlinarith
      refine le_trans h1 ?_
      norm_num [sec7_cExp])
    m hm r hr
  have hfun : (fun t => diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) t -
      (-(45/64) * (3 * RE.c₁ * RE.c₂) * sec7_Pprod h₁ h₂ h₃ * (S.T₃ / S.R ^ 3) *
        (t / S.R) ^ (-(13:ℝ)/4))) =
      (fun t => diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) t -
      3 * RE.c₁ * RE.c₂ * sec7_aprod (-(1:ℝ)/4) 3 * sec7_Pprod h₁ h₂ h₃ *
        (S.T₃ / S.R ^ 3) * (t / S.R) ^ (-(1:ℝ)/4 - 3)) := by
    funext t
    rw [show sec7_aprod (-(1:ℝ)/4) 3 = -(45/64) from by norm_num [sec7_aprod],
      show -(1:ℝ)/4 - 3 = -(13:ℝ)/4 from by norm_num]
    ring
  rw [hfun]
  exact hgen
end Sec7RaExpData

end Squarefree
