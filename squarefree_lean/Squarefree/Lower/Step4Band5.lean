import Squarefree.Lower.Step4DiamHybrid
import Squarefree.Lower.Step4Weight5
import Squarefree.Lower.Step4VsBand

/-!
# §5 Step-4 five-slot band coefficients + master funnel

Coefficient definitions (`cE2hyb`, `cChyb`, `Ecap4`, `cEhyb`) for the five-slot band
collapse, the `band_master` funnel inequality, the `cE2hyb` majorant, and the per-fibre
five-slot factorization `vsum_le_weight5` (clone of `vsum_le_weight4add`).
-/

open Real

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- Five-slot `cE₂`-coefficient (the `n`-linear room), hybrid form. -/
noncomputable def cE2hyb (P : Globals) (S : Scale P) (a ℓ₁ ℓ₂ : ℝ) : ℝ :=
  10^12 * a * P.G * S.Ω^4 * (2*ℓ₂ - ℓ₁) / (S.Δ * (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))^2)

/-- The degree-3 (`V³·B`) piece of the fixed Vmax-scale cap, doubled.  It is `n`-FREE, so it
is RE-SLOTTED into the constant room `cChyb` (the `cE`-slot's `√n`-weight overshoots it). -/
noncomputable def Ecap4p3 (P : Globals) (S : Scale P) (ℓ₁ ℓ₂ : ℝ) : ℝ :=
  2 * (77*(P.G*S.Ω/S.Δ^4)
       * (5*ℓ₁^3*ℓ₂*(3*ℓ₂-2*ℓ₁)*(3000000000000*S.B)*(Vmax P S)^3) / S.D)

/-- Five-slot `cC`-coefficient (the constant room), hybrid form: the `B³`-monomial plus the
re-slotted degree-3 cap piece `4a·Ecap4p3/√L`. -/
noncomputable def cChyb (P : Globals) (S : Scale P) (a ℓ₁ ℓ₂ : ℝ) : ℝ :=
  10^44 * a * P.G * S.Ω^2 * (ℓ₁*ℓ₂*(ℓ₂-ℓ₁)) * S.B^3 / (S.Δ^3 * S.D)
    + 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))

/-- The fixed (Vmax-scale) additive cap for the `cE`-slot: flat-coefficient drift at `Vmax`
plus the capped `p₂` degree-4 rest, doubled (the degree-3 piece lives in `Ecap4p3`). -/
noncomputable def Ecap4a (P : Globals) (S : Scale P) (a ℓ₁ ℓ₂ : ℝ) : ℝ :=
  2 * (20*(a/S.D)^2*(Cref P S ℓ₁ ℓ₂*(S.A/a)^2)*(ℓ₁*Vmax P S)^2
       + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(Vmax P S)^4)/S.D)

/-- Five-slot `cE`-coefficient: gap/slope drift + smoothing + the fixed cap `Ecap4a`, all over
`√(ℓ₁ℓ₂(ℓ₂−ℓ₁))`. -/
noncomputable def cEhyb (P : Globals) (S : Scale P) (a ℓ₁ ℓ₂ gap : ℝ) : ℝ :=
  (10^10*a*P.G*S.Ω^3*gap/S.Δ^2 + 10^35*a*P.G*S.Ω^3*ℓ₂*S.B^2/(S.Δ^2*S.D)
    + 4*a*Ecap4a P S a ℓ₁ ℓ₂) / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))

/-- `Ĉ = Cref·(A/a)²·ℓ₁² = 3ℓ₁²·(ℓ₁ℓ₂(ℓ₂−ℓ₁))/a²` (mirror of `hCa2` in `Vs_pin`). -/
private theorem Chat_eq {a ℓ₁ ℓ₂ : ℝ} (ha : 0 < a) :
    Cref P S ℓ₁ ℓ₂ * (S.A/a)^2 * ℓ₁^2 = 3*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/a^2 := by
  have hΔne : S.Δ ≠ 0 := S.Δ_pos.ne'
  have hΩne : S.Ω ≠ 0 := S.Ω_pos.ne'
  have hane : a ≠ 0 := ha.ne'
  rw [show Cref P S ℓ₁ ℓ₂ = 3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) / (S.Δ ^ 2 * S.Ω ^ 2) from rfl,
    show S.A = S.Δ * S.Ω from rfl]
  field_simp

/-- **Master band funnel.**  With the leading coefficient `Ĉ = 3ℓ₁²Lv/a²` and the pin
`n/(2Ĉ) ≤ Vlo²`, the kernel shape `2ℓ₁·(T/Ĉ)/Vlo` is dominated by `2aT/(√Lv·√n)`. -/
theorem band_master {ℓ₁ a Lv Ĉ Vlo n T : ℝ} (ha : 0 < a) (hL : 1 ≤ Lv) (hℓ₁ : 1 ≤ ℓ₁)
    (hĈ : Ĉ = 3*ℓ₁^2*Lv/a^2) (hVlo : 0 < Vlo) (hn : 1 ≤ n)
    (hpin : n / (2*Ĉ) ≤ Vlo^2) (hT : 0 ≤ T) :
    2*ℓ₁*(T/Ĉ)/Vlo ≤ 2*a*T / (Real.sqrt Lv * Real.sqrt n) := by
  have hℓ₁0 : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ₁
  have hLv0 : (0:ℝ) < Lv := lt_of_lt_of_le one_pos hL
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have hĈ0 : (0:ℝ) < Ĉ := by rw [hĈ]; positivity
  have hsLv : 0 < Real.sqrt Lv := Real.sqrt_pos.mpr hLv0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hCa : Ĉ * a^2 = 3*ℓ₁^2*Lv := by
    rw [hĈ]; exact div_mul_cancel₀ _ (pow_ne_zero 2 ha.ne')
  have hpin' : n ≤ 2*Ĉ*Vlo^2 := by
    rw [div_le_iff₀ (by positivity)] at hpin; linarith
  have key : ℓ₁ * Real.sqrt Lv * Real.sqrt n ≤ a * Ĉ * Vlo := by
    have hCan : Ĉ * a^2 * n = 3*ℓ₁^2*Lv*n := by rw [hCa]
    have h1 : Ĉ*a^2*n ≤ Ĉ*a^2*(2*Ĉ*Vlo^2) :=
      mul_le_mul_of_nonneg_left hpin' (by positivity)
    have hsq : (ℓ₁ * Real.sqrt Lv * Real.sqrt n)^2 ≤ (a * Ĉ * Vlo)^2 := by
      have e1 : (ℓ₁ * Real.sqrt Lv * Real.sqrt n)^2 = ℓ₁^2 * Lv * n := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hLv0.le, Real.sq_sqrt hn0.le]
      rw [e1]
      nlinarith [h1, hCan, sq_nonneg (a * Ĉ * Vlo),
        mul_nonneg (mul_nonneg (sq_nonneg ℓ₁) hLv0.le) hn0.le]
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
  rw [show 2*ℓ₁*(T/Ĉ)/Vlo = 2*ℓ₁*T/(Ĉ*Vlo) by rw [mul_div_assoc', div_div],
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (by linarith : (0:ℝ) ≤ 2*T)]

/-- `cE2hyb` majorant: with `a ≤ 11A` and `ℓ₂ ≥ ℓ₁ + 1`, the `n`-linear coefficient is at most
`10¹⁸·G·Ω⁵/(ℓ₁·ℓ₁ℓ₂(ℓ₂−ℓ₁))`. -/
theorem cE2hyb_le_majorant {a ℓ₁ ℓ₂ : ℝ} (ha0 : 0 < a) (ha_hi : a ≤ 11*S.A)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) :
    cE2hyb P S a ℓ₁ ℓ₂ ≤ 10^18 * P.G * S.Ω^5 / (ℓ₁ * (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))) := by
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hG := P.G_pos
  have hℓ1R : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2R : (0:ℝ) < ℓ₂ := by linarith
  have hgapR : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hLpos : (0:ℝ) < ℓ₁*ℓ₂*(ℓ₂-ℓ₁) := mul_pos (mul_pos hℓ1R hℓ2R) hgapR
  have h2l : (0:ℝ) < 2*ℓ₂ - ℓ₁ := by linarith
  have ha' : a ≤ 11*(S.Δ*S.Ω) := by rw [show S.A = S.Δ*S.Ω from rfl] at ha_hi; exact ha_hi
  have hkey : 11*10^12*((2*ℓ₂-ℓ₁)*ℓ₁) ≤ 10^18*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁)) := by
    nlinarith [mul_nonneg (mul_nonneg hℓ1R.le hℓ2R.le) (by linarith : (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1),
      mul_nonneg (mul_nonneg hℓ1R.le (by linarith : (0:ℝ) ≤ ℓ₂ - 2)) hgapR.le,
      hLpos.le]
  unfold cE2hyb
  rw [div_le_div_iff₀ (mul_pos hΔ (pow_pos hLpos 2)) (mul_pos hℓ1R hLpos)]
  have H1 := mul_le_mul_of_nonneg_right ha'
    (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 10^12*P.G*S.Ω^4) h2l.le)
      (mul_nonneg hℓ1R.le hLpos.le))
  have H2 := mul_le_mul_of_nonneg_right hkey
    (mul_nonneg (by positivity : (0:ℝ) ≤ P.G*S.Ω^5*S.Δ) hLpos.le)
  nlinarith [H1, H2]

/-- **Per-fibre five-slot factorization (clone of `vsum_le_weight4add`).**  The v-count
`vc ≤ 2 + ev/√n + cE·√n + cE₂·n + cC` times the per-`(s,v)` count `Cv ≤ K_C·(b + dc/√n)`
gives the per-`s`-fibre five-slot count `vc·Cv ≤ K_C·weight5 b ev dc cE cE₂ cC n`. -/
theorem vsum_le_weight5 {K_C vc Cv b ev dc cE cE₂ cC n : ℝ}
    (hKC : 0 ≤ K_C) (hb : 0 ≤ b) (hdc : 0 ≤ dc)
    (hvc_nn : 0 ≤ vc) (hcE₂ : 0 ≤ cE₂) (hcC : 0 ≤ cC) (hn : 0 ≤ n)
    (hvc : vc ≤ 2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC)
    (hCcol : Cv ≤ K_C * (b + dc / Real.sqrt n)) :
    vc * Cv ≤ K_C * weight5 b ev dc cE cE₂ cC n := by
  rw [weight5]
  have hsqrt_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hbase_nn : 0 ≤ b + dc / Real.sqrt n := by positivity
  have hRHS_nn : 0 ≤ K_C * (b + dc / Real.sqrt n) := mul_nonneg hKC hbase_nn
  calc vc * Cv
      ≤ vc * (K_C * (b + dc / Real.sqrt n)) := mul_le_mul_of_nonneg_left hCcol hvc_nn
    _ ≤ (2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC)
          * (K_C * (b + dc / Real.sqrt n)) :=
        mul_le_mul_of_nonneg_right hvc hRHS_nn
    _ = K_C * ((2 + ev / Real.sqrt n + cE * Real.sqrt n + cE₂ * n + cC)
          * (b + dc / Real.sqrt n)) := by ring

/-! ### Five-slot piece bounds feeding the band collapse -/

/-- `√(ℓ₁³ℓ₂(ℓ₂−ℓ₁)) = ℓ₁·√(ℓ₁ℓ₂(ℓ₂−ℓ₁))` (from `L₃ = ℓ₁²·L`). -/
private theorem sqrtL3_eq {ℓ₁ ℓ₂ : ℝ} (hℓ1 : 0 ≤ ℓ₁) :
    Real.sqrt (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)) = ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by
  rw [show ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁) = ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) by ring,
    Real.sqrt_mul (sq_nonneg ℓ₁), Real.sqrt_sq hℓ1]

/-- `√(n/L₃) = √n / (ℓ₁·√L)`. -/
private theorem sqrt_box_eq {ℓ₁ ℓ₂ n : ℝ} (hℓ1 : 0 ≤ ℓ₁) (hn : 0 ≤ n) :
    Real.sqrt (n / (ℓ₁ ^ 3 * ℓ₂ * (ℓ₂ - ℓ₁)))
      = Real.sqrt n / (ℓ₁ * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by
  rw [Real.sqrt_div hn, sqrtL3_eq hℓ1]

/-- Kernel K1: `Vbox/(√L·√n) = 10³ΔΩ/(ℓ₁·L)` (n-free). -/
private theorem vbox_div_st {ℓ₁ ℓ₂ n : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    Vbox S ℓ₁ ℓ₂ n / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = 1000 * S.Δ * S.Ω / (ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have hL : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  have hsL : (0:ℝ) < Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := Real.sqrt_pos.mpr hL
  have hsn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hss : Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
      = ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := Real.mul_self_sqrt hL.le
  rw [Vbox, sqrt_box_eq hℓ1p.le hn0.le]
  field_simp
  linear_combination -hss

/-- Kernel K2: `Vbox²/(√L·√n) = (10⁶Δ²Ω²/(ℓ₁²L))·(√n/√L)`. -/
private theorem vbox_sq_div_st {ℓ₁ ℓ₂ n : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    (Vbox S ℓ₁ ℓ₂ n) ^ 2 / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = (10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2 / (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))
          * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hlt : ℓ₁ < ℓ₂ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have htt : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  rw [Vbox_sq hn0.le hℓ1 hlt, div_div, div_mul_div_comm,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2 * Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
    * ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) * htt

/-- Kernel K3: `Vbox³/(√L·√n) = 10⁹Δ³Ω³·n/(ℓ₁³L²)`. -/
private theorem vbox_cube_div_st {ℓ₁ ℓ₂ n : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hn : 1 ≤ n) :
    (Vbox S ℓ₁ ℓ₂ n) ^ 3 / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = 10 ^ 9 * S.Δ ^ 3 * S.Ω ^ 3 * n / (ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ^ 2) := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hlt : ℓ₁ < ℓ₂ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  rw [show (Vbox S ℓ₁ ℓ₂ n) ^ 3 / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = (Vbox S ℓ₁ ℓ₂ n) ^ 2
        * (Vbox S ℓ₁ ℓ₂ n / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)) by ring,
    Vbox_sq hn0.le hℓ1 hlt, vbox_div_st hℓ1 hℓ12 hn]
  field_simp
  ring

/-- P1 (err slot): exact, `2a·4err/(√L√n) = (8a·err/√L)/√n`. -/
private theorem band5_piece_err {a err ℓ₁ ℓ₂ n : ℝ} :
    2 * a * (4 * err) / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ (8 * a * err / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) / Real.sqrt n := by
  apply le_of_eq
  rw [div_div]
  ring

/-- P2 (cubic → n-slot): `2a·(2·EcubV(Vbox))/(√L√n) ≤ cE2hyb·n` (616·10⁹ ≤ 10¹²). -/
private theorem band5_piece_cub {a ℓ₁ ℓ₂ n : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    2 * a * (2 * Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ cE2hyb P S a ℓ₁ ℓ₂ * n := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have h2l : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hkey : 2 * a * (2 * Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = (616 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)))
        * ((Vbox S ℓ₁ ℓ₂ n) ^ 3
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)) := by
    unfold Step4EcubV; ring
  rw [hkey, vbox_cube_div_st hℓ1 hℓ12 hn]
  have hLHS : (616 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁)))
        * (10 ^ 9 * S.Δ ^ 3 * S.Ω ^ 3 * n / (ℓ₁ ^ 3 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ^ 2))
      = 616 * 10 ^ 9 * (a * P.G * S.Ω ^ 4 * (2 * ℓ₂ - ℓ₁) * n
          / (S.Δ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ^ 2)) := by
    field_simp
  rw [hLHS]
  unfold cE2hyb
  rw [show 10 ^ 12 * a * P.G * S.Ω ^ 4 * (2 * ℓ₂ - ℓ₁) / (S.Δ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ^ 2) * n
      = 10 ^ 12 * (a * P.G * S.Ω ^ 4 * (2 * ℓ₂ - ℓ₁) * n
          / (S.Δ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ^ 2)) from by ring]
  have hZ : (0:ℝ) ≤ a * P.G * S.Ω ^ 4 * (2 * ℓ₂ - ℓ₁) * n
      / (S.Δ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) ^ 2) := by positivity
  exact mul_le_mul_of_nonneg_right (by norm_num) hZ

/-- P3 (recon → √n-slot): `2a·4·recon(Vbox)/(√L√n) ≤ (10¹⁰aGΩ³gap/Δ²)/√L·√n` (1848·10⁶ ≤ 10¹⁰). -/
private theorem band5_piece_recon {a ℓ₁ ℓ₂ gap n : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hgap : 0 ≤ gap) (hn : 1 ≤ n) :
    2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap
        * (ℓ₁ * Vbox S ℓ₁ ℓ₂ n) ^ 2))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2)
          / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  rw [show 2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap
        * (ℓ₁ * Vbox S ℓ₁ ℓ₂ n) ^ 2))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = (1848 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap * ℓ₁ ^ 2)
        * ((Vbox S ℓ₁ ℓ₂ n) ^ 2
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)) from by ring,
    vbox_sq_div_st hℓ1 hℓ12 hn]
  have hLHS : (1848 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap * ℓ₁ ^ 2)
        * (10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2 / (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
            * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))
      = 1848 * 10 ^ 6 * (a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2
          * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) := by
    field_simp
  rw [hLHS, show (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2)
          / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n
      = 10 ^ 10 * (a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2
          * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) from by ring]
  have hZ : (0:ℝ) ≤ a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2
      * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by positivity
  exact mul_le_mul_of_nonneg_right (by norm_num) hZ

/-- P4 (p₂ V²-monomial → √n-slot): `2a·4·77(GΩ/Δ⁴)·C₂(Bx)·Vbox²/D/(√L√n) ≤
(10³⁵aGΩ³ℓ₂B²/(Δ²D))/√L·√n` (83160·10³⁰ ≤ 10³⁵). -/
private theorem band5_piece_p2t2 {a ℓ₁ ℓ₂ n : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4)
        * P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * (Vbox S ℓ₁ ℓ₂ n) ^ 2 / S.D))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D))
          / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hDne : S.D ≠ 0 := hD.ne'
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  rw [show 2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4)
        * P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * (Vbox S ℓ₁ ℓ₂ n) ^ 2 / S.D))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = (9240 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))
          * (3000000000000 * S.B) ^ 2 / S.D)
        * ((Vbox S ℓ₁ ℓ₂ n) ^ 2
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n))
      from by unfold P2HybCoeff2; ring, vbox_sq_div_st hℓ1 hℓ12 hn]
  have hLHS : (9240 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁))
          * (3000000000000 * S.B) ^ 2 / S.D)
        * (10 ^ 6 * S.Δ ^ 2 * S.Ω ^ 2 / (ℓ₁ ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))
            * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))
      = 83160 * 10 ^ 30 * (a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)
          * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) := by
    field_simp
    ring
  rw [hLHS, show (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D))
          / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n
      = 10 ^ 35 * (a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)
          * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)))) from by ring]
  have hZ : (0:ℝ) ≤ a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D)
      * (Real.sqrt n / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))) := by positivity
  exact mul_le_mul_of_nonneg_right (by norm_num) hZ

/-- P5 (p₂ V-monomial → constant slot): `2a·4·77(GΩ/Δ⁴)·C₁(Bx)·Vbox/D/(√L√n)` fits the
`B³`-monomial part of `cChyb` (83160·10³⁹ ≤ 10⁴⁴; n-free). -/
private theorem band5_piece_p2t1 {a ℓ₁ ℓ₂ n : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4)
        * P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * Vbox S ℓ₁ ℓ₂ n / S.D))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3
          / (S.Δ ^ 3 * S.D) := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hB : (0:ℝ) < S.B := by unfold Scale.B; positivity
  have hDne : S.D ≠ 0 := hD.ne'
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  rw [show 2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4)
        * P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * Vbox S ℓ₁ ℓ₂ n / S.D))
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = (3080 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
          * (3000000000000 * S.B) ^ 3 / S.D)
        * (Vbox S ℓ₁ ℓ₂ n / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n))
      from by unfold P2HybCoeff1; ring, vbox_div_st hℓ1 hℓ12 hn]
  have hLHS : (3080 * a * (P.G * S.Ω / S.Δ ^ 4) * (ℓ₁ ^ 3 * ℓ₂ ^ 2 * (ℓ₂ - ℓ₁) ^ 2)
          * (3000000000000 * S.B) ^ 3 / S.D)
        * (1000 * S.Δ * S.Ω / (ℓ₁ * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))))
      = 83160 * 10 ^ 39 * (a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3
          / (S.Δ ^ 3 * S.D)) := by
    field_simp
    ring
  rw [hLHS]
  rw [show 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D)
      = 10 ^ 44 * (a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3
          / (S.Δ ^ 3 * S.D)) from by ring]
  have hZ : (0:ℝ) ≤ a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3
      / (S.Δ ^ 3 * S.D) := by positivity
  exact mul_le_mul_of_nonneg_right (by norm_num) hZ

/-- `Ecap4a ≥ 0` (flat-drift and capped degree-4 rest are both nonnegative). -/
theorem Ecap4a_nonneg {a ℓ₁ ℓ₂ : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) :
    0 ≤ Ecap4a P S a ℓ₁ ℓ₂ := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hlt : ℓ₁ < ℓ₂ := by linarith
  have hCref : (0:ℝ) ≤ Cref P S ℓ₁ ℓ₂ := (Cref_pos hℓ1p hlt).le
  have hVx : (0:ℝ) ≤ Vmax P S := Vmax_nonneg
  have h2l : (0:ℝ) ≤ 2 * ℓ₂ - ℓ₁ := by linarith
  have hflat : (0:ℝ) ≤ 20 * (a / S.D) ^ 2 * (Cref P S ℓ₁ ℓ₂ * (S.A / a) ^ 2)
      * (ℓ₁ * Vmax P S) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hCref (sq_nonneg _))) (sq_nonneg _)
  have hsecond : (0:ℝ) ≤ 77 * (P.G * S.Ω / S.Δ ^ 4)
      * (5 / 2 * ℓ₁ ^ 3 * (2 * ℓ₂ - ℓ₁) * (Vmax P S) ^ 4) / S.D := by positivity
  unfold Ecap4a
  linarith

/-- `Ecap4p3 ≥ 0`. -/
theorem Ecap4p3_nonneg {ℓ₁ ℓ₂ : ℝ} (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) :
    0 ≤ Ecap4p3 P S ℓ₁ ℓ₂ := by
  have hΔ := S.Δ_pos; have hΩ := S.Ω_pos; have hG := P.G_pos
  have hD : (0:ℝ) < S.D := by unfold Scale.D; have := P.H_pos; positivity
  have hB : (0:ℝ) < S.B := by unfold Scale.B; positivity
  have hVx : (0:ℝ) ≤ Vmax P S := Vmax_nonneg
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have h32 : (0:ℝ) ≤ 3 * ℓ₂ - 2 * ℓ₁ := by linarith
  unfold Ecap4p3
  positivity

/-- P6 (capped slot, `cE`-part): `2a·(2·Ecap4a)/(√L√n) ≤ (4a·Ecap4a/√L)·√n` — i.e. `1/√n ≤ √n`.
NOTE: the matching `cEhyb` summand must carry `4*a*Ecap4a` (see `band_collapse5` blocker). -/
private theorem band5_piece_cap {a ℓ₁ ℓ₂ n : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    2 * a * (2 * Ecap4a P S a ℓ₁ ℓ₂)
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ 4 * a * Ecap4a P S a ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n := by
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hL : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  have hsL : (0:ℝ) < Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := Real.sqrt_pos.mpr hL
  have hsn1 : (1:ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
  have hsn : (0:ℝ) < Real.sqrt n := lt_of_lt_of_le one_pos hsn1
  have hE : (0:ℝ) ≤ Ecap4a P S a ℓ₁ ℓ₂ := Ecap4a_nonneg hℓ1 hℓ12
  have hC : (0:ℝ) ≤ 4 * a * Ecap4a P S a ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by
    positivity
  have hinv : 1 / Real.sqrt n ≤ Real.sqrt n := by
    rw [div_le_iff₀ hsn]
    nlinarith [hsn1]
  calc 2 * a * (2 * Ecap4a P S a ℓ₁ ℓ₂)
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = 4 * a * Ecap4a P S a ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
          * (1 / Real.sqrt n) := by ring
    _ ≤ 4 * a * Ecap4a P S a ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hinv hC

/-- P6′ (capped slot, re-slotted `p₃`-part): `2a·(2·Ecap4p3)/(√L√n) ≤ 4a·Ecap4p3/√L`
— i.e. `1/√n ≤ 1` (the constant room; n-free landing). -/
private theorem band5_piece_capP3 {a ℓ₁ ℓ₂ n : ℝ} (ha0 : 0 < a)
    (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂) (hn : 1 ≤ n) :
    2 * a * (2 * Ecap4p3 P S ℓ₁ ℓ₂)
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      ≤ 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hℓ2p : (0:ℝ) < ℓ₂ := by linarith
  have hgapp : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hL : (0:ℝ) < ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by positivity
  have hsL : (0:ℝ) < Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := Real.sqrt_pos.mpr hL
  have hsn1 : (1:ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
  have hsn : (0:ℝ) < Real.sqrt n := lt_of_lt_of_le one_pos hsn1
  have hE : (0:ℝ) ≤ Ecap4p3 P S ℓ₁ ℓ₂ := Ecap4p3_nonneg hℓ1 hℓ12
  have hC : (0:ℝ) ≤ 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := by
    positivity
  have hinv : 1 / Real.sqrt n ≤ 1 := by
    rw [div_le_one hsn]; exact hsn1
  calc 2 * a * (2 * Ecap4p3 P S ℓ₁ ℓ₂)
        / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
      = 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁))
          * (1 / Real.sqrt n) := by ring
    _ ≤ 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * 1 :=
        mul_le_mul_of_nonneg_left hinv hC
    _ = 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := mul_one _

/-- **Five-slot band collapse.**  `band_master` funnels the kernel `2ℓ₁·(T/Ĉ)/Vlo` into
`2aT/(√L·√n)`; the six piece bounds then land each budget fragment in its slot:
`(8a·err/√L)/√n + cEhyb·√n + cE2hyb·n + cChyb`. -/
theorem band_collapse5 {a ℓ₁ ℓ₂ gap err Vlo Ĉ n : ℝ}
    (ha0 : 0 < a) (hℓ1 : 1 ≤ ℓ₁) (hℓ12 : ℓ₁ + 1 ≤ ℓ₂)
    (hgap : 0 ≤ gap) (herr : 0 ≤ err) (hn : 1 ≤ n)
    (hĈdef : Ĉ = Cref P S ℓ₁ ℓ₂ * (S.A/a)^2 * ℓ₁^2)
    (hVlo : 0 < Vlo) (hpin : n / (2*Ĉ) ≤ Vlo^2) :
    2*ℓ₁ * ((4*err + 2*(Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n)
        + 2*Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ n))) / Ĉ) / Vlo
      ≤ (8*a*err / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))) / Real.sqrt n
        + cEhyb P S a ℓ₁ ℓ₂ gap * Real.sqrt n
        + cE2hyb P S a ℓ₁ ℓ₂ * n
        + cChyb P S a ℓ₁ ℓ₂ := by
  have hℓ1p : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1
  have hlt : ℓ₁ < ℓ₂ := by linarith
  have hA : (1:ℝ) ≤ ℓ₁ * ℓ₂ := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ₁ - 1) (by linarith : (0:ℝ) ≤ ℓ₂ - 1)]
  have hLv1 : (1:ℝ) ≤ ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ₁ * ℓ₂ - 1)
      (by linarith : (0:ℝ) ≤ ℓ₂ - ℓ₁ - 1)]
  have hVb : (0:ℝ) ≤ Vbox S ℓ₁ ℓ₂ n := Vbox_nonneg
  have hT0 : (0:ℝ) ≤ 4*err + 2*(Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n)
      + 2*Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ n)) := by
    have h1 := Step4EcubV_nonneg (P := P) (S := S) hℓ1 hlt hVb
    have h2 := Step4EremHyb_nonneg (P := P) (S := S) (a := a) hℓ1 hlt hgap hVb
    linarith
  have hĈeq : Ĉ = 3*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/a^2 := by rw [hĈdef]; exact Chat_eq ha0
  refine (band_master ha0 hLv1 hℓ1 hĈeq hVlo hn hpin hT0).trans ?_
  have hsplit : 2*a*(4*err + 2*(Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n)
        + 2*Step4EremHyb P S a ℓ₁ ℓ₂ gap (Vbox S ℓ₁ ℓ₂ n)))
        / (Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁)) * Real.sqrt n)
      = (8*a*err / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))) / Real.sqrt n
        + 2 * a * (2 * Step4EcubV P S ℓ₁ ℓ₂ (Vbox S ℓ₁ ℓ₂ n))
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
        + 2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4) * (3 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * gap
            * (ℓ₁ * Vbox S ℓ₁ ℓ₂ n) ^ 2))
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
        + 2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4)
            * P2HybCoeff2 ℓ₁ ℓ₂ (3000000000000 * S.B) * (Vbox S ℓ₁ ℓ₂ n) ^ 2 / S.D))
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
        + 2 * a * (4 * (77 * (P.G * S.Ω / S.Δ ^ 4)
            * P2HybCoeff1 ℓ₁ ℓ₂ (3000000000000 * S.B) * Vbox S ℓ₁ ℓ₂ n / S.D))
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
        + 2 * a * (2 * Ecap4a P S a ℓ₁ ℓ₂)
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n)
        + 2 * a * (2 * Ecap4p3 P S ℓ₁ ℓ₂)
            / (Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n) := by
    unfold Step4EremHyb E0_p2_hyb P2CapRest Ecap4a Ecap4p3
    ring
  rw [hsplit]
  have h2 := band5_piece_cub (P := P) (S := S) ha0 hℓ1 hℓ12 hn
  have h3 := band5_piece_recon (P := P) (S := S) ha0 hℓ1 hℓ12 hgap hn
  have h4 := band5_piece_p2t2 (P := P) (S := S) ha0 hℓ1 hℓ12 hn
  have h5 := band5_piece_p2t1 (P := P) (S := S) ha0 hℓ1 hℓ12 hn
  have h6 := band5_piece_cap (P := P) (S := S) ha0 hℓ1 hℓ12 hn
  have h7 := band5_piece_capP3 (P := P) (S := S) ha0 hℓ1 hℓ12 hn
  have hcE : cEhyb P S a ℓ₁ ℓ₂ gap * Real.sqrt n
      = (10 ^ 10 * a * P.G * S.Ω ^ 3 * gap / S.Δ ^ 2)
          / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n
        + (10 ^ 35 * a * P.G * S.Ω ^ 3 * ℓ₂ * S.B ^ 2 / (S.Δ ^ 2 * S.D))
          / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n
        + 4 * a * Ecap4a P S a ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * Real.sqrt n := by
    unfold cEhyb
    ring
  have hcC : cChyb P S a ℓ₁ ℓ₂
      = 10 ^ 44 * a * P.G * S.Ω ^ 2 * (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) * S.B ^ 3 / (S.Δ ^ 3 * S.D)
        + 4 * a * Ecap4p3 P S ℓ₁ ℓ₂ / Real.sqrt (ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁)) := rfl
  linarith

end Squarefree
