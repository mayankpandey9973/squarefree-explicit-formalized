import Squarefree.Upper.Regime6
import Squarefree.Upper.Regime6LowF
import Squarefree.Upper.Regime6Count
import Mathlib

/-!
# §6 regime: double-counting swap and assembly of Prop 6.1

This file performs the `a ↔ r` swap (writeup line 1250–1251) reducing the `a`-sum
`∑_{a∼A} #ℛ_a` to a sum over `r` of the per-`r` integer counts, and (in the low-curvature
branch `F < 1`) the elementary algebra collapsing the resulting bound to `C·(Ω + R)`.

See `../explicit_writeup.md` lines 1230–1308 and `math_audit.md` §6.
-/

open Classical Finset
open Squarefree.Counting

namespace Squarefree

set_option maxHeartbeats 1000000

/-- The §6 near-integer width `δ₀ = H/(Δ²Ω²) = x/Ω²`. -/
noncomputable def delta0 {P : Globals} (S : Scale P) : ℝ := P.H / (S.Δ ^ 2 * S.Ω ^ 2)

theorem delta0_pos {P : Globals} (S : Scale P) : 0 < delta0 S := by
  have := P.H_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold delta0; positivity

/-- **`R·δ₀·A/F = Ω`** (exact scale identity, writeup line 1288). -/
theorem R_delta0_A_div_F {P : Globals} (S : Scale P) :
    S.R * delta0 S * S.A / S.F = S.Ω := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold delta0 Scale.R Scale.A Scale.F
  field_simp

/-- **Swap + near-integer transfer** (writeup line 1250–1251).  Under the §6 hypotheses, the
`a`-sum of `#ℛ_a` is bounded by the sum over the `r`-window `[0, ⌊16R⌋]` of the per-`r` integer
counts `#{a ∈ [⌈A⌉, ⌊2A⌋] : ‖f̃ₐ(r)‖ ≤ K₀δ₀}`. -/
theorem prop6_swap {P : Globals} {S : Scale P}
    (hAD : 10 * S.A ≤ S.D) (hΩfloor : (500 : ℝ) ≤ P.G * P.H * S.Ω ^ 3)
    (RaOf : ℤ → Finset ℕ)
    (hwit : ∀ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, (0 < a) ∧ ∀ r ∈ RaOf a, RaWitness P S a r) :
    (∑ a ∈ Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋, ((RaOf a).card : ℝ)) ≤
      ∑ r ∈ Finset.Icc ⌈(1/72) * S.R⌉₊ ⌊16 * S.R⌋₊,
        (((Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋).filter
            (fun (n : ℤ) => distInt (ftil P.X (r : ℝ) (n : ℝ)) ≤ K0 * delta0 S)).card : ℝ) := by
  classical
  have hX := P.X_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hRpos : 0 < S.R := by rw [Scale.R]; have := P.H_pos; have := P.G_pos; positivity
  set Ua : Finset ℕ := Finset.Icc ⌈(1/72) * S.R⌉₊ ⌊16 * S.R⌋₊ with hUadef
  set Ia : Finset ℤ := Finset.Icc ⌈S.A⌉ ⌊2 * S.A⌋ with hIadef
  set δ : ℝ := K0 * delta0 S with hδdef
  -- Step 1: each RaOf a ⊆ Ua.filter (predicate at a)
  have hsub : ∀ a ∈ Ia, RaOf a ⊆ Ua.filter (fun (r : ℕ) => distInt (ftil P.X (r:ℝ) (a:ℝ)) ≤ δ) := by
    intro a haI r hr
    obtain ⟨ha0, hwa⟩ := hwit a haI
    have hwr : RaWitness P S a r := hwa r hr
    -- a ∈ [A, 2A]
    obtain ⟨haIl, haIr⟩ := Finset.mem_Icc.mp haI
    have haA : S.A ≤ (a : ℝ) := le_trans (Int.le_ceil S.A) (by exact_mod_cast haIl)
    have haA2 : (a : ℝ) ≤ 2 * S.A := le_trans (by exact_mod_cast haIr) (Int.floor_le (2 * S.A))
    -- (1/72)R ≤ r ≤ 16R as naturals
    obtain ⟨_d, _, _, _, _, hrlo, hrhi⟩ := id hwr
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [hUadef, Finset.mem_Icc]
      refine ⟨Nat.ceil_le.mpr hrlo, Nat.le_floor hrhi⟩
    · -- transfer via ftil_near_integer
      have htrans := ftil_near_integer (P := P) (S := S) (a := a) (r := r)
        hAD hΩfloor ha0 haA haA2 hwr
      rw [show δ = K0 * delta0 S from hδdef, delta0]
      exact htrans
  -- Step 2: #RaOf a ≤ #(filter)
  have hcard_le : ∀ a ∈ Ia,
      ((RaOf a).card : ℝ)
        ≤ ((Ua.filter (fun (r : ℕ) => distInt (ftil P.X (r:ℝ) (a:ℝ)) ≤ δ)).card : ℝ) := by
    intro a haI
    have := Finset.card_le_card (hsub a haI)
    exact Nat.cast_le.mpr this
  -- Step 3: sum over a, then swap
  calc (∑ a ∈ Ia, ((RaOf a).card : ℝ))
      ≤ ∑ a ∈ Ia, ((Ua.filter (fun (r : ℕ) => distInt (ftil P.X (r:ℝ) (a:ℝ)) ≤ δ)).card : ℝ) :=
        Finset.sum_le_sum hcard_le
    _ = ∑ a ∈ Ia, ∑ r ∈ Ua, (if distInt (ftil P.X (r:ℝ) (a:ℝ)) ≤ δ then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro r _; split <;> simp
    _ = ∑ r ∈ Ua, ∑ a ∈ Ia, (if distInt (ftil P.X (r:ℝ) (a:ℝ)) ≤ δ then (1:ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ r ∈ Ua, ((Ia.filter (fun (n : ℤ) => distInt (ftil P.X (r:ℝ) (n:ℝ)) ≤ δ)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro a _; split <;> simp

end Squarefree
