import Squarefree.Params

/-!
# §5 Step-4 band-edge pays (`1 ≤ G·U³·Ω⁴` primitives)

The band lower-edge hypothesis `hband : 1 ≤ G·U³·Ω⁴` (writeup: `D ≥ X^{1/2}`-side of the
dyadic band) replaces the unfaithful `1 ≤ Ω`.  Each "pay" converts an inverse Ω-power into
explicit `G·U`-budget: `Ω⁻⁴ᵏ ≤ GᵏU³ᵏ` from powers of `hband`, and odd Ω-powers cost one
extra `U` each via `Ω ≤ U` (no case split on `Ω ≶ 1`).
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- Pay `Ω⁻⁸`: `1 ≤ G²U⁶Ω⁸`. -/
theorem band_pay8 (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) :
    (1:ℝ) ≤ P.G ^ 2 * P.U ^ 6 * S.Ω ^ 8 := by
  calc (1:ℝ) ≤ (P.G * P.U ^ 3 * S.Ω ^ 4) ^ 2 := one_le_pow₀ hband
    _ = P.G ^ 2 * P.U ^ 6 * S.Ω ^ 8 := by ring

/-- Pay `Ω⁻¹²`: `1 ≤ G³U⁹Ω¹²`. -/
theorem band_pay12 (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) :
    (1:ℝ) ≤ P.G ^ 3 * P.U ^ 9 * S.Ω ^ 12 := by
  calc (1:ℝ) ≤ (P.G * P.U ^ 3 * S.Ω ^ 4) ^ 3 := one_le_pow₀ hband
    _ = P.G ^ 3 * P.U ^ 9 * S.Ω ^ 12 := by ring

/-- Pay `Ω⁻³`: `1 ≤ GU⁴Ω³` (one `U` for the odd drop, via `Ω ≤ U`). -/
theorem band_pay3 (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hΩU : S.Ω ≤ P.U) :
    (1:ℝ) ≤ P.G * P.U ^ 4 * S.Ω ^ 3 := by
  have hΩpos := S.Ω_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  calc (1:ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband
    _ = P.G * P.U ^ 3 * S.Ω ^ 3 * S.Ω := by ring
    _ ≤ P.G * P.U ^ 3 * S.Ω ^ 3 * P.U :=
        mul_le_mul_of_nonneg_left hΩU (by positivity)
    _ = P.G * P.U ^ 4 * S.Ω ^ 3 := by ring

/-- Pay `Ω⁻⁶`: `1 ≤ G²U⁸Ω⁶` (two `U`s for the even-but-not-4-divisible drop). -/
theorem band_pay6 (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hΩU : S.Ω ≤ P.U) :
    (1:ℝ) ≤ P.G ^ 2 * P.U ^ 8 * S.Ω ^ 6 := by
  have hΩpos := S.Ω_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hΩ2 : S.Ω ^ 2 ≤ P.U ^ 2 := pow_le_pow_left₀ hΩpos.le hΩU 2
  calc (1:ℝ) ≤ P.G ^ 2 * P.U ^ 6 * S.Ω ^ 8 := band_pay8 hband
    _ = P.G ^ 2 * P.U ^ 6 * S.Ω ^ 6 * S.Ω ^ 2 := by ring
    _ ≤ P.G ^ 2 * P.U ^ 6 * S.Ω ^ 6 * P.U ^ 2 :=
        mul_le_mul_of_nonneg_left hΩ2 (by positivity)
    _ = P.G ^ 2 * P.U ^ 8 * S.Ω ^ 6 := by ring

/-- Pay `Ω⁻¹¹`: `1 ≤ G³U¹⁰Ω¹¹` (one `U` for the odd drop). -/
theorem band_pay11 (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) (hΩU : S.Ω ≤ P.U) :
    (1:ℝ) ≤ P.G ^ 3 * P.U ^ 10 * S.Ω ^ 11 := by
  have hΩpos := S.Ω_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  calc (1:ℝ) ≤ P.G ^ 3 * P.U ^ 9 * S.Ω ^ 12 := band_pay12 hband
    _ = P.G ^ 3 * P.U ^ 9 * S.Ω ^ 11 * S.Ω := by ring
    _ ≤ P.G ^ 3 * P.U ^ 9 * S.Ω ^ 11 * P.U :=
        mul_le_mul_of_nonneg_left hΩU (by positivity)
    _ = P.G ^ 3 * P.U ^ 10 * S.Ω ^ 11 := by ring

/-- Pay `Ω⁻⁴`: `1 ≤ GU³Ω⁴` is `hband` itself (alias for uniform call sites). -/
theorem band_pay4 (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4) :
    (1:ℝ) ≤ P.G * P.U ^ 3 * S.Ω ^ 4 := hband

end Squarefree
