import Mathlib
import Squarefree.DCard
import Squarefree.DyadicAssembly
import Squarefree.Mobius
import Squarefree.MobiusAssembly

/-!
# Top of the proof spine — main statements

Faithful `sorry`-stubbed statements of the paper's headline results, kept verbatim from
`../explicit_writeup.md` lines 4–26 (Theorem) and 2241–2255 (Thm 10.1). These elaborate but
are not yet proved; each `sorry` is tagged `STUB: <name>`. See `CLAUDE.md` §3/§4.

`dCard` is defined in `Squarefree.DCard` (split out to break the import cycle with the
structural/optimization layers); `key_dyadic_estimate` below is assembled from those layers via
`Squarefree.DyadicAssembly.key_dyadic_assembly`.
-/

open Classical Finset

namespace Squarefree

/-- §1 key estimate: every dyadic scale `H/U ≪ D ≪ X^{1/2}` has `#𝒟[D,2D] ≪ H/U`. -/
theorem key_dyadic_estimate (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ D : ℝ, X ^ ((1 - g) / 5) / X ^ u ≤ D → D ≤ X ^ (1/2 : ℝ) →
        (dCard X (X ^ ((1 - g) / 5)) D : ℝ) ≤ C * X ^ ((1 - g) / 5) / X ^ u :=
  key_dyadic_assembly g hg hg'

/-- Main analytic theorem (§Theorem): `∑_{X≤n≤X+H} μ²(n) = 6/π² · H + O(H/U)`. -/
theorem squarefree_count_short_interval (g : ℝ) (hg : 0 < g) (hg' : g < 2 / 18977) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      |(∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + X ^ ((1 - g) / 5)⌋,
            (if Squarefree n.toNat then (1 : ℝ) else 0))
          - 6 / Real.pi ^ 2 * X ^ ((1 - g) / 5)|
        ≤ C * X ^ ((1 - g) / 5) / X ^ u :=
  Squarefree.Mob.count_short_interval g hg hg'

/-- Theorem 10.1: a squarefree number in `[X, X + X^{1/5 − 2/94885 + ε}]` for large `X`. -/
theorem theorem_10_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, Squarefree n ∧ (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + X ^ (1/5 - 2/94885 + ε : ℝ) := by
  -- Step 1: WLOG ε small.  Set ε' := min ε (1/94885); then 0 < ε' ≤ ε and ε' < 2/94885.
  set ε' : ℝ := min ε (1 / 94885) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'lt : ε' < 2 / 94885 := by
    have : ε' ≤ 1 / 94885 := min_le_right _ _
    linarith
  -- Step 2: g := 2/18977 - 5·ε'.  Then 0 < g < 2/18977 and (1-g)/5 = 1/5 - 2/94885 + ε'.
  set g : ℝ := 2 / 18977 - 5 * ε' with hgdef
  have hg : 0 < g := by
    rw [hgdef]; nlinarith [hε'lt]
  have hg' : g < 2 / 18977 := by
    rw [hgdef]; linarith [hε'pos]
  have hexp : (1 - g) / 5 = 1 / 5 - 2 / 94885 + ε' := by
    rw [hgdef]; ring
  -- Step 3: invoke the counting theorem.
  obtain ⟨u, hu, C, hC, X₀, hX₀⟩ := squarefree_count_short_interval g hg hg'
  -- Step 4: choose X₁ so that C / X^u < 6/π² for X ≥ X₁, giving positivity of the count.
  have hπ : 0 < 6 / Real.pi ^ 2 := by positivity
  -- We want X^u > C·π²/6, i.e. X > (C·π²/6)^(1/u).
  set X₁ : ℝ := (C * Real.pi ^ 2 / 6) ^ (1 / u) + 1 with hX₁def
  refine ⟨max (max X₀ X₁) 1, fun X hX => ?_⟩
  have hX0 : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX1' : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1'
  -- H := X^((1-g)/5) = X^(1/5 - 2/94885 + ε') and H > 0.
  set H : ℝ := X ^ ((1 - g) / 5) with hHdef
  have hHpos : 0 < H := Real.rpow_pos_of_pos hXpos _
  -- From the counting bound, |S - 6/π²·H| ≤ C·H/X^u.
  have hbound := hX₀ X hX0
  -- Lower bound on the sum S.
  set S : ℝ := ∑ n ∈ Finset.Icc ⌈X⌉ ⌊X + H⌋,
      (if Squarefree n.toNat then (1 : ℝ) else 0) with hSdef
  -- C / X^u < 6/π².
  have hXupos : 0 < X ^ u := Real.rpow_pos_of_pos hXpos u
  have hkey : C / X ^ u < 6 / Real.pi ^ 2 := by
    -- X > (C·π²/6)^(1/u), and X^u monotone, gives X^u > C·π²/6.
    have hbase : 0 < C * Real.pi ^ 2 / 6 := by positivity
    have hXgt : (C * Real.pi ^ 2 / 6) ^ (1 / u) < X := by
      have : (C * Real.pi ^ 2 / 6) ^ (1 / u) < X₁ := by rw [hX₁def]; linarith
      exact lt_of_lt_of_le this hX1
    -- X^u > ((C·π²/6)^(1/u))^u = C·π²/6.
    have hmono : ((C * Real.pi ^ 2 / 6) ^ (1 / u)) ^ u < X ^ u :=
      Real.rpow_lt_rpow (by positivity) hXgt hu
    rw [← Real.rpow_mul (le_of_lt hbase), one_div, inv_mul_cancel₀ (ne_of_gt hu),
      Real.rpow_one] at hmono
    -- so C·π²/6 < X^u, hence C/X^u < 6/π².
    have hπpos : 0 < Real.pi ^ 2 := by positivity
    rw [div_lt_div_iff₀ hXupos hπpos]
    nlinarith [hmono, hXupos, hπpos]
  -- The sum S is positive.
  have hSpos : 0 < S := by
    -- |S - 6/π²·H| ≤ C·H/X^u  ⇒  S ≥ 6/π²·H - C·H/X^u = H·(6/π² - C/X^u) > 0.
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
    push_neg at hcon
    have : S = 0 := Finset.sum_eq_zero hcon
    rw [this] at hSpos
    exact lt_irrefl _ hSpos
  obtain ⟨n, hnmem, hne⟩ := hex
  -- The nonzero term means the `if` condition holds.
  have hsf : Squarefree n.toNat := by
    by_contra h
    simp [h] at hne
  -- Step 6: extract the bounds on n from membership.
  rw [Finset.mem_Icc] at hnmem
  obtain ⟨hnlo, hnhi⟩ := hnmem
  -- n ≥ ⌈X⌉ ≥ 1 (since X ≥ 1), so n ≥ 0 and (n.toNat : ℝ) = (n : ℝ).
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
  · -- X ≤ n.toNat : from ⌈X⌉ ≤ n and X ≤ ⌈X⌉.
    rw [hcast]
    have hXle : (X : ℝ) ≤ (⌈X⌉ : ℝ) := Int.le_ceil X
    have : ((⌈X⌉ : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
    linarith
  · -- n.toNat ≤ X + X^(1/5-2/94885+ε) : from n ≤ ⌊X+H⌋ ≤ X+H and H ≤ X^(...+ε).
    rw [hcast]
    have hnle : (n : ℝ) ≤ (⌊X + H⌋ : ℝ) := by exact_mod_cast hnhi
    have hfloor : (⌊X + H⌋ : ℝ) ≤ X + H := Int.floor_le (X + H)
    -- H = X^((1-g)/5) = X^(1/5-2/94885+ε') ≤ X^(1/5-2/94885+ε).
    have hHval : H = X ^ (1 / 5 - 2 / 94885 + ε' : ℝ) := by rw [hHdef, hexp]
    have hHle : H ≤ X ^ (1 / 5 - 2 / 94885 + ε : ℝ) := by
      rw [hHval]
      exact Real.rpow_le_rpow_of_exponent_le hX1' (by linarith [hε'le])
    linarith

end Squarefree
