import Squarefree.Lower.Prop51Scale

/-!
# §5 Step-3 tight f-sum: exact monomial identities
The six `ρ/κ`-leg monomial identities (`monρ_Na/Nb/Nc`, `monκ_Na/Nb/Nc`) in
√-variables, consumed by `step3_fsum_le_t4t5`.
-/

namespace Squarefree

open Finset

variable {P : Globals} {S : Scale P}


/-- **ρ·Na = T4'** (in √-variables): `(d²g⁶v⁴⁰/ω³)·(g⁹v⁵⁵/ω⁵) = d²g¹⁵v⁹⁵/ω⁸`. Exact. -/
theorem monρ_Na {g v d ω : ℝ} (hω0 : 0 < ω) :
    (d ^ 2 * g ^ 6 * v ^ 40 / ω ^ 3) * (g ^ 9 * v ^ 55 / ω ^ 5)
      = d ^ 2 * g ^ 15 * v ^ 95 / ω ^ 8 := by
  rw [div_mul_div_comm]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **ρ·Nb = T5'** (in √-variables):
`(d²g⁶v⁴⁰/ω³)·(H g⁸ ω² v³⁰/d⁵) = H g¹⁴v⁷⁰/(d³ω)`. Exact (needs `d,ω ≠ 0`). -/
theorem monρ_Nb {g v d ω H : ℝ} (hd0 : 0 < d) (hω0 : 0 < ω) :
    (d ^ 2 * g ^ 6 * v ^ 40 / ω ^ 3) * (H * g ^ 8 * ω ^ 2 * v ^ 30 / d ^ 5)
      = H * g ^ 14 * v ^ 70 / (d ^ 3 * ω) := by
  rw [div_mul_div_comm]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **ρ·Nc ≤ T4'** (in √-variables):
`(d²g⁶v⁴⁰/ω³)·(g⁴v³⁰/ω⁵) ≤ d²g¹⁵v⁹⁵/ω⁸`, ratio `1/(g⁵v²⁵) ≤ 1`. -/
theorem monρ_Nc {g v d ω : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hg1 : 1 ≤ g) (hv1 : 1 ≤ v) :
    (d ^ 2 * g ^ 6 * v ^ 40 / ω ^ 3) * (g ^ 4 * v ^ 30 / ω ^ 5)
      ≤ d ^ 2 * g ^ 15 * v ^ 95 / ω ^ 8 := by
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have hg5 : (1:ℝ) ≤ g ^ 5 := one_le_pow₀ hg1
  have hv25 : (1:ℝ) ≤ v ^ 25 := one_le_pow₀ hv1
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul hg5 hv25 (by norm_num) (by positivity))
    (show (0:ℝ) ≤ d ^ 2 * g ^ 10 * v ^ 70 * ω ^ 8 by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le]

/-- **κ·Na ≤ ρ** (in √-variables, PAYLESS via the `hHbig`-route):
`(d⁶/(H g²ω))·(g⁹v⁵⁵/ω⁵) ≤ d²g⁶v⁴⁰/ω³`.
Needs only `hkey2 : d⁸g²v³⁰ ≤ H²ω⁶` — the √-variable square of `Δ²√G·U^{15/2} ≤ HΩ³`,
which the caller derives from `hHbig : 10¹¹²·Δ⁴G⁵U⁴⁵ ≤ H²Ω¹⁴` plus `Ω ≤ U`, `G,U ≥ 1`. -/
theorem monκ_Na {g v d ω H : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hH0 : 0 < H) (hkey2 : d ^ 8 * g ^ 2 * v ^ 30 ≤ H ^ 2 * ω ^ 6) :
    (d ^ 6 / (H * g ^ 2 * ω)) * (g ^ 9 * v ^ 55 / ω ^ 5)
      ≤ d ^ 2 * g ^ 6 * v ^ 40 / ω ^ 3 := by
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  -- after clearing: d⁶ g⁹ v⁵⁵ · ω³ ≤ d²g⁶v⁴⁰ · (H g²ω·ω⁵), i.e. d⁴·g·v¹⁵ ≤ H·ω³.
  have hkey : d ^ 4 * g * v ^ 15 ≤ H * ω ^ 3 := by
    have h2 : (d ^ 4 * g * v ^ 15) ^ 2 ≤ (H * ω ^ 3) ^ 2 := by
      calc (d ^ 4 * g * v ^ 15) ^ 2 = d ^ 8 * g ^ 2 * v ^ 30 := by ring
        _ ≤ H ^ 2 * ω ^ 6 := hkey2
        _ = (H * ω ^ 3) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h2
  nlinarith [mul_le_mul_of_nonneg_right hkey
    (show (0:ℝ) ≤ d ^ 2 * g ^ 8 * v ^ 40 * ω ^ 3 by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le, hH0.le]

/-- **κ·Nb ≤ ρ** (in √-variables): `(d⁶/(H g²ω))·(H g⁸ ω² v³⁰/d⁵) ≤ d²g⁶v⁴⁰/ω³`.
Needs `ω ≤ v²`, `v ≥ 1`, `d ≥ 1`. -/
theorem monκ_Nb {g v d ω H : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hH0 : 0 < H) (hv1 : 1 ≤ v) (hd1 : 1 ≤ d) (hωv2 : ω ≤ v ^ 2) :
    (d ^ 6 / (H * g ^ 2 * ω)) * (H * g ^ 8 * ω ^ 2 * v ^ 30 / d ^ 5)
      ≤ d ^ 2 * g ^ 6 * v ^ 40 / ω ^ 3 := by
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  -- after clearing: d⁶ H g⁸ ω² v³⁰ · ω³ ≤ d²g⁶v⁴⁰ · (H g²ω·d⁵)
  -- i.e. ω⁴ ≤ d v¹⁰.  From ω ≤ v² (ω⁴ ≤ v⁸ ≤ v¹⁰), d ≥ 1.
  have hω4 : ω ^ 4 ≤ v ^ 8 := by
    have h := pow_le_pow_left₀ hω0.le hωv2 4
    calc ω ^ 4 ≤ (v ^ 2) ^ 4 := h
      _ = v ^ 8 := by ring
  have hkey : ω ^ 4 ≤ d * v ^ 10 := by
    have hv8 : v ^ 8 ≤ v ^ 10 := by
      nlinarith [one_le_pow₀ (n := 2) hv1, pow_nonneg hv0.le 8]
    have hdv : v ^ 10 ≤ d * v ^ 10 := by nlinarith [hd1, pow_nonneg hv0.le 10]
    linarith [hω4, hv8, hdv]
  nlinarith [mul_le_mul_of_nonneg_right hkey
    (show (0:ℝ) ≤ H * d ^ 6 * g ^ 8 * v ^ 30 * ω by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le, hH0.le]

/-- **κ·Nc ≤ ρ** (in √-variables): `(d⁶/(H g²ω))·(g⁴v³⁰/ω⁵) ≤ d²g⁶v⁴⁰/ω³`.
Needs `d⁴g²v²⁰ ≤ H`, `g,v ≥ 1`, and the pay fact `1 ≤ g²v⁸ω³` (absorbed into the
`g⁴v¹⁰` slack — no bump needed on this leg). -/
theorem monκ_Nc {g v d ω H : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hH0 : 0 < H) (hg1 : 1 ≤ g) (hv1 : 1 ≤ v) (hpay : 1 ≤ g ^ 2 * v ^ 8 * ω ^ 3)
    (hHbig : d ^ 4 * g ^ 2 * v ^ 20 ≤ H) :
    (d ^ 6 / (H * g ^ 2 * ω)) * (g ^ 4 * v ^ 30 / ω ^ 5)
      ≤ d ^ 2 * g ^ 6 * v ^ 40 / ω ^ 3 := by
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  -- after clearing: d⁶ g⁴ v³⁰ · ω³ ≤ d²g⁶v⁴⁰ · (H g²ω·ω⁵), i.e. d⁴ ≤ H g⁴ v¹⁰ ω³.
  -- d⁴ ≤ d⁴g²v²⁰ ≤ H ≤ H g⁴ v¹⁰ ω³.
  have hge1 : (1:ℝ) ≤ g ^ 2 * v ^ 20 := by
    have h1 : (1:ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    have h2 : (1:ℝ) ≤ v ^ 20 := one_le_pow₀ hv1
    nlinarith [h1, h2]
  have hd4 : d ^ 4 ≤ H := by
    calc d ^ 4 = d ^ 4 * 1 := by ring
      _ ≤ d ^ 4 * (g ^ 2 * v ^ 20) := mul_le_mul_of_nonneg_left hge1 (by positivity)
      _ = d ^ 4 * g ^ 2 * v ^ 20 := by ring
      _ ≤ H := hHbig
  have hbump : (1:ℝ) ≤ g ^ 4 * v ^ 10 * ω ^ 3 := by
    have hg2v2 : (1:ℝ) ≤ g ^ 2 * v ^ 2 := by
      nlinarith [one_le_pow₀ (n := 2) hg1, one_le_pow₀ (n := 2) hv1, pow_nonneg hv0.le 2]
    calc (1:ℝ) ≤ g ^ 2 * v ^ 8 * ω ^ 3 := hpay
      _ = (g ^ 2 * v ^ 8 * ω ^ 3) * 1 := by ring
      _ ≤ (g ^ 2 * v ^ 8 * ω ^ 3) * (g ^ 2 * v ^ 2) :=
          mul_le_mul_of_nonneg_left hg2v2 (by positivity)
      _ = g ^ 4 * v ^ 10 * ω ^ 3 := by ring
  have hd4' : d ^ 4 ≤ H * g ^ 4 * v ^ 10 * ω ^ 3 := by
    calc d ^ 4 ≤ H := hd4
      _ = H * 1 := by ring
      _ ≤ H * (g ^ 4 * v ^ 10 * ω ^ 3) := mul_le_mul_of_nonneg_left hbump hH0.le
      _ = H * g ^ 4 * v ^ 10 * ω ^ 3 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hd4'
    (show (0:ℝ) ≤ d ^ 2 * g ^ 4 * v ^ 30 * ω ^ 3 by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le, hH0.le]

end Squarefree
