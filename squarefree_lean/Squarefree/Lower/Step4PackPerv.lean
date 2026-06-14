import Squarefree.Lower.Step4Compose
import Squarefree.Lower.Step4Hperv
import Squarefree.Lower.Step4WBridge

/-!
# §5 Step-4 packed per-`(s,v)` count: `hperv` for `step4_fibre_branch_le`

`step4_hperv` (bare-`Rδ` window count) + `step4_W_from_Vs` (the `V_s`-pin → `hvlarge`/`hWhi`/
`hWlo` bridge, `Lr = ℓ₁ℓ₂(ℓ₂−ℓ₁)`), quantified over the fibre: every `w`-slice of `Fib`
numbers at most `10²⁰⁰·(b + dc/√n)` with `b = HG⁵U¹⁵/(Δ²Ω²)`, `dc = G⁴U¹⁵/Ω⁴·√(ℓ₁ℓ₂(ℓ₂−ℓ₁))`.
-/

open Real Finset Squarefree.Counting

namespace Squarefree

/-- **§5 Step-4 packed `hperv`.**  Per-`r` window/near-integer witnesses (`hmem`), the absolute
defect lower bound (`hv2`) and the `V_s` squared pin (`hpin_lo`/`hpin_hi`) over the fibre give,
for every `w`, the slice count `≤ 10²⁰⁰·(b + dc/√n)`, `b = HG⁵U¹⁵/(Δ²Ω²)`,
`dc = G⁴U¹⁵/Ω⁴·√(ℓ₁ℓ₂(ℓ₂−ℓ₁))` — the `hperv` input of `step4_fibre_branch_le`. -/
theorem step4_pack_perv {P : Globals} {S : Scale P} {a ℓ₁ ℓ₂ r₀ r₁ δ : ℝ} {n : ℕ}
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H) (hΩU : S.Ω ≤ P.U)
    (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hδhalf : δ ≤ 1 / 2)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hReg : S.Δ ^ 2 * P.U ^ 5 ≤ P.H * S.Ω ^ 3)
    (hDeW : 10 ^ 27 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ)
    (hAD : 10 * S.A ≤ S.D)
    (ha0 : 0 < a) (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hℓ2W : ℓ₂ ≤ 130 * (P.G * P.U ^ 5))
    (hr0_lo : (1/72) * S.R ≤ r₀) (hr01 : r₀ ≤ r₁) (hr1_hi : r₁ + ℓ₁ ≤ 16 * S.R)
    (hδ : δ = 10 ^ 70 * ((1 / S.Δ) * P.G ^ 4 * P.U ^ 15 / S.Ω ^ 5))
    (hn : 1 ≤ n) (hnN : (n:ℝ) ≤ 10 ^ 57 * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * P.U ^ 10 / S.Ω ^ 8)
    (Fib : Finset ℕ) (vOf : ℕ → ℝ)
    (hmem : ∀ r ∈ Fib, r₀ ≤ (r:ℝ) ∧ (r:ℝ) ≤ r₁ ∧
        distInt (phiv P.X a ℓ₁ ℓ₂ (vOf r) (r:ℝ)) ≤ δ)
    (hVcut : ∀ r ∈ Fib, V₂ P S ≤ |vOf r|)
    (hpin_lo : ∀ r ∈ Fib,
        (1/150 : ℝ) * (S.Δ ^ 2 * S.Ω ^ 2 * (n:ℝ)) ≤ ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * vOf r ^ 2)
    (hpin_hi : ∀ r ∈ Fib,
        ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) * vOf r ^ 2 ≤ 1000000 * (S.Δ ^ 2 * S.Ω ^ 2 * (n:ℝ))) :
    ∀ w : ℝ, ((Fib.filter (fun r => vOf r = w)).card : ℝ)
      ≤ 10 ^ 200 * (P.H * P.G ^ 5 * P.U ^ 15 / (S.Δ ^ 2 * S.Ω ^ 2)
          + (P.G ^ 4 * P.U ^ 15 / S.Ω ^ 4 * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
              / Real.sqrt (n:ℝ)) := by
  intro w
  by_cases hcase : ∃ r ∈ Fib, vOf r = w
  · obtain ⟨r', hr', hr'w⟩ := hcase
    have hℓ12' : ℓ₁ < ℓ₂ := by linarith
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hDeW15 : 10 ^ 15 * (P.G ^ 4 * P.U ^ 20) ≤ S.Δ :=
      le_trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hDeW
    obtain ⟨hvlarge, hWhi, hWlo⟩ := step4_W_from_Vs hG1 hUbig hReg hDeW15 ha0 ha_lo ha_hi
      hℓ1lo hℓ12' hℓ2W hn1 (by simpa only [hr'w] using hVcut r' hr')
      (by simpa only [hr'w] using hpin_lo r' hr') (by simpa only [hr'w] using hpin_hi r' hr')
    have h12 : (1:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
    have hP12 : (1:ℝ) ≤ ℓ₁ * ℓ₂ := by nlinarith
    have hLrlo : (1:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by nlinarith
    exact step4_hperv hG1 hU1 hUbig hΔ1 hH1 hΩU hband hδhalf h1 hDeW hAD ha0 ha_lo ha_hi
      hℓ1lo hℓ12'
      (by linarith) hvlarge hr0_lo hr01 hr1_hi hδ hLrlo hn1 hnN hWhi hWlo _
      (fun r hr => by
        obtain ⟨hrF, hrw⟩ := Finset.mem_filter.mp hr
        simpa only [hrw] using hmem r hrF)
  · have hempty : Fib.filter (fun r => vOf r = w) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun r hr h => hcase ⟨r, hr, h⟩
    rw [hempty]
    have hH0 := P.H_pos; have hG0 := P.G_pos; have hU0 := P.U_pos
    have hΔ0 := S.Δ_pos; have hΩ0 := S.Ω_pos
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Squarefree
