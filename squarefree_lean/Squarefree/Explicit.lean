import Squarefree.Main

/-!
# Effective Theorem 10.1 — explicit threshold

This file upgrades `Squarefree.theorem_10_1` (the `∃ X₀` form, proved in `Squarefree.Main`) to an
*effective* statement: instead of an unspecified existential threshold, it exposes a closed-form
threshold `X0eff ε` built from the explicit short-interval witnesses
`Mob.countSI_X0`, `Mob.countSI_C`, `Mob.countSI_u`.

The proof mirrors `theorem_10_1`'s body verbatim, with the explicit constants substituted for the
obtained existential witnesses and the threshold exposed via `X0eff`.
-/

open Classical

namespace Squarefree

/-- Effective gap parameter `g(ε) = 2/18187 − 5·min(ε, 1/90935)`. -/
noncomputable def gEff (ε : ℝ) : ℝ := 2 / 18187 - 5 * min ε (1 / 90935)

/-- Explicit threshold for the effective Theorem 10.1. -/
noncomputable def X0eff (ε : ℝ) : ℝ :=
  max (max (Mob.countSI_X0 (gEff ε))
           ((Mob.countSI_C (gEff ε) * Real.pi ^ 2 / 6) ^ (1 / Mob.countSI_u (gEff ε)) + 1)) 1

/-- **Effective Theorem 10.1.** For all `X ≥ X0eff ε` (an explicit, closed-form threshold), the
interval `[X, X + X^{1/5 − 2/90935 + ε}]` contains a squarefree number. -/
theorem theorem_10_1_effective (ε : ℝ) (hε : 0 < ε) :
    ∀ X : ℝ, X0eff ε ≤ X →
      ∃ n : ℕ, Squarefree n ∧ (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + X ^ (1/5 - 2/90935 + ε : ℝ) := by
  intro X hX
  -- Step 1: WLOG ε small.  Set ε' := min ε (1/90935); then 0 < ε' ≤ ε and ε' < 2/90935.
  set ε' : ℝ := min ε (1 / 90935) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'lt : ε' < 2 / 90935 := by
    have : ε' ≤ 1 / 90935 := min_le_right _ _
    linarith
  -- Step 2: g := gEff ε = 2/18187 - 5·ε'.  Then 0 < g < 2/18187 and (1-g)/5 = 1/5 - 2/90935 + ε'.
  set g : ℝ := gEff ε with hgdef
  have hgval : g = 2 / 18187 - 5 * ε' := by rw [hgdef]; unfold gEff; rw [← hε'def]
  have hg : 0 < g := by rw [hgval]; nlinarith [hε'lt]
  have hg' : g < 2 / 18187 := by rw [hgval]; linarith [hε'pos]
  have hexp : (1 - g) / 5 = 1 / 5 - 2 / 90935 + ε' := by rw [hgval]; ring
  -- Positivity of the explicit witnesses (the dedicated lemmas are `private`; re-prove inline).
  have hu : 0 < Mob.countSI_u g := by
    have huk : 0 < Squarefree.keyDyadic_u g := Squarefree.keyDyadic_u_pos g hg hg'
    have he : (0 : ℝ) < (1 - g) / 5 / 2 := by linarith [hg']
    unfold Mob.countSI_u
    have := lt_min huk he
    linarith
  have hC : 0 < Mob.countSI_C g := by
    have hCk : 0 < Squarefree.keyDyadic_C g := Squarefree.keyDyadic_C_pos g hg hg'
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have huk : 0 < Squarefree.keyDyadic_u g := Squarefree.keyDyadic_u_pos g hg hg'
    have hduk : 0 < Squarefree.keyDyadic_u g - Mob.countSI_u g := by
      have h1 : Mob.countSI_u g < Squarefree.keyDyadic_u g := by
        unfold Mob.countSI_u
        have hm : min (Squarefree.keyDyadic_u g) ((1 - g) / 5 / 2)
            ≤ Squarefree.keyDyadic_u g := min_le_left _ _
        linarith
      linarith
    have hdeu : 0 < (1 - g) / 5 - Mob.countSI_u g := by
      have h2 : Mob.countSI_u g < (1 - g) / 5 := by
        unfold Mob.countSI_u
        have hm : min (Squarefree.keyDyadic_u g) ((1 - g) / 5 / 2)
            ≤ (1 - g) / 5 / 2 := min_le_right _ _
        linarith
      linarith
    unfold Mob.countSI_C
    have h1 : 0 ≤ (Squarefree.keyDyadic_C g + 1)
        * (1 + (Squarefree.keyDyadic_u g - Mob.countSI_u g)⁻¹ / (2 * Real.log 2)) := by positivity
    have h2 : 0 ≤ ((1 - g) / 5 - Mob.countSI_u g)⁻¹ / (2 * Real.log 2) := by positivity
    linarith
  -- Step 3: the explicit counting bound, folded onto local abbreviations u, C, X0.
  have hX₀bound := Mob.count_short_interval_explicit g hg hg'
  set u : ℝ := Mob.countSI_u g with hudef
  set C : ℝ := Mob.countSI_C g with hCdef
  set X0 : ℝ := Mob.countSI_X0 g with hX0def
  have hπ : 0 < 6 / Real.pi ^ 2 := by positivity
  -- Step 4: choose X₁ so that C / X^u < 6/π² for X ≥ X₁, giving positivity of the count.
  set X₁ : ℝ := (C * Real.pi ^ 2 / 6) ^ (1 / u) + 1 with hX₁def
  -- Bridge: the explicit threshold equals the `max (max X0 X₁) 1` shape used below.
  have hX0eff : X0eff ε = max (max X0 X₁) 1 := by
    unfold X0eff
    rw [show gEff ε = g from hgdef.symm, ← hX0def, ← hCdef, ← hudef, ← hX₁def]
  rw [hX0eff] at hX
  have hX0le : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1le : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX1' : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1'
  -- H := X^((1-g)/5) = X^(1/5 - 2/90935 + ε') and H > 0.
  set H : ℝ := X ^ ((1 - g) / 5) with hHdef
  have hHpos : 0 < H := Real.rpow_pos_of_pos hXpos _
  -- From the counting bound, |S - 6/π²·H| ≤ C·H/X^u.
  have hbound := hX₀bound X hX0le
  set S : ℝ := ∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + H⌋,
      (if Squarefree n.toNat then (1 : ℝ) else 0) with hSdef
  have hXupos : 0 < X ^ u := Real.rpow_pos_of_pos hXpos u
  have hkey : C / X ^ u < 6 / Real.pi ^ 2 := by
    have hbase : 0 < C * Real.pi ^ 2 / 6 := by positivity
    have hXgt : (C * Real.pi ^ 2 / 6) ^ (1 / u) < X := by
      have : (C * Real.pi ^ 2 / 6) ^ (1 / u) < X₁ := by rw [hX₁def]; linarith
      exact lt_of_lt_of_le this hX1le
    have hmono : ((C * Real.pi ^ 2 / 6) ^ (1 / u)) ^ u < X ^ u :=
      Real.rpow_lt_rpow (by positivity) hXgt hu
    rw [← Real.rpow_mul (le_of_lt hbase), one_div, inv_mul_cancel₀ (ne_of_gt hu),
      Real.rpow_one] at hmono
    have hπpos : 0 < Real.pi ^ 2 := by positivity
    rw [div_lt_div_iff₀ hXupos hπpos]
    nlinarith [hmono, hXupos, hπpos]
  -- The sum S is positive.
  have hSpos : 0 < S := by
    have habs := abs_le.mp hbound
    have hlow : 6 / Real.pi ^ 2 * H - C * H / X ^ u ≤ S := by linarith [habs.1]
    have : 0 < 6 / Real.pi ^ 2 * H - C * H / X ^ u := by
      have : C * H / X ^ u = (C / X ^ u) * H := by ring
      rw [this]
      have : (C / X ^ u) * H < (6 / Real.pi ^ 2) * H :=
        mul_lt_mul_of_pos_right hkey hHpos
      linarith
    linarith
  -- Step 5: positive sum ⇒ some term is positive ⇒ Squarefree at that index.
  have hex : ∃ n ∈ Finset.Icc ⌈X⌉ ⌊X + H⌋,
      (if Squarefree n.toNat then (1 : ℝ) else 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : S = 0 := Finset.sum_eq_zero hcon
    rw [this] at hSpos
    exact lt_irrefl _ hSpos
  obtain ⟨n, hnmem, hne⟩ := hex
  have hsf : Squarefree n.toNat := by
    by_contra h
    simp [h] at hne
  -- Step 6: extract the bounds on n from membership.
  rw [Finset.mem_Icc] at hnmem
  obtain ⟨hnlo, hnhi⟩ := hnmem
  have hceilpos : (1 : ℤ) ≤ ⌈X⌉ := by
    rw [Int.one_le_ceil_iff]; exact hXpos
  have hn1 : (1 : ℤ) ≤ n := le_trans hceilpos hnlo
  have hnnonneg : (0 : ℤ) ≤ n := le_trans (by norm_num) hn1
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have h : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hnnonneg
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    exact this
  refine ⟨n.toNat, hsf, ?_, ?_⟩
  · -- X ≤ n.toNat
    rw [hcast]
    have hXle : (X : ℝ) ≤ (⌈X⌉ : ℝ) := Int.le_ceil X
    have : ((⌈X⌉ : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
    linarith
  · -- n.toNat ≤ X + X^(1/5-2/90935+ε)
    rw [hcast]
    have hnle : (n : ℝ) ≤ (⌊X + H⌋ : ℝ) := by exact_mod_cast hnhi
    have hfloor : (⌊X + H⌋ : ℝ) ≤ X + H := Int.floor_le (X + H)
    have hHval : H = X ^ (1 / 5 - 2 / 90935 + ε' : ℝ) := by rw [hHdef, hexp]
    have hHle : H ≤ X ^ (1 / 5 - 2 / 90935 + ε : ℝ) := by
      rw [hHval]
      exact Real.rpow_le_rpow_of_exponent_le hX1' (by linarith [hε'le])
    linarith

end Squarefree
