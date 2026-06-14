import Squarefree.Lower.Prop51Scale

/-!
# §5 Step-2 scale-domination to the Step-2 `Bcombine` monomials `t2, t3`

`step2_fsum_le_t2t3` is the §5 Step-2 scale-domination lemma targeting the two Step-2
`Bcombine` monomials

* `t2 = (H/Δ)·(Δ²/H)·G⁴·U⁴⁵/Ω¹⁴`  (= `Δ·G⁴·U⁴⁵/Ω¹⁴`, the `Δ²/H` term);
* `t3 = (H/Δ)·(G^{9/2}·U³⁵/(Δ^{1/2}·Ω⁸))`  (= `H·G^{9/2}·U³⁵/(Δ^{3/2}·Ω⁸)`, the `1/√Δ` term).

It bounds the per-pair Step-2 `f`-sum

`112·(R·δ·Nf + 2·R·√(δ/κ)·√Nf + κ·Nf² + Nf)`

(with `δ = Δ²·G·U²⁰/(H·Ω⁶)`, `κ = D⁴/(X·A)`) by `10⁶⁵·(t2 + t3)`.

The `Nf`-cap is `Nf ≤ 10³⁰·(G²·U¹⁵/Ω⁵)`. Decomposition (all sympy-verified):

* `R·δ·Nf ≤ 10³⁰·t2`  (ratio `Ω⁶/U¹⁰ ≤ 1`);
* `κ·Nf² ≤ 10⁶⁰·t2`   (dominant; ratio via `Δ²·G·U¹⁰ ≤ H`);
* `2·R·√(δ/κ)·√Nf ≤ 2·10¹⁵·t3`  (radicand a perfect square `(10¹⁵·G²U^{35/2}/(√Δ·Ω⁵))²`);
* `Nf ≤ 10³⁰·t3`     (ratio via `Δ^{3/2}·Ω³ ≤ H·G^{5/2}·U²⁰`).

Sum `≤ 112·((10³⁰+10⁶⁰)·t2 + (2·10¹⁵+10³⁰)·t3) ≤ 10⁶⁵·(t2+t3)`.

Scale identities reused: `κ = Δ³/(H·G·Ω)` (`defect_D4_div_XA`), `R = H·G·Ω³/Δ`.
-/

namespace Squarefree

open Finset

variable {P : Globals} {S : Scale P}

/-- **R·δ·Nc ≤ T2** (in √-variables): `(d²g⁴v⁴⁰/ω³)·(g⁴v³⁰/ω⁵) ≤ d²g⁸v⁹⁰/ω¹⁴`,
ratio `ω⁶/v²⁰ ≤ 1` (`ω ≤ v²`). -/
private theorem mon_Rδ_Nc {g v d ω : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hg1 : 1 ≤ g) (hv1 : 1 ≤ v) (hωv2 : ω ≤ v ^ 2) :
    (d ^ 2 * g ^ 4 * v ^ 40 / ω ^ 3) * (g ^ 4 * v ^ 30 / ω ^ 5)
      ≤ d ^ 2 * g ^ 8 * v ^ 90 / ω ^ 14 := by
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  -- after clearing: d²g⁸v⁷⁰ · ω¹⁴ ≤ d²g⁸v⁹⁰ · (ω³·ω⁵) = d²g⁸v⁹⁰ ω⁸, i.e. v⁷⁰ ω⁶ ≤ v⁹⁰.
  have hω6 : ω ^ 6 ≤ v ^ 12 := by
    have h := pow_le_pow_left₀ hω0.le hωv2 6
    calc ω ^ 6 ≤ (v ^ 2) ^ 6 := h
      _ = v ^ 12 := by ring
  -- scalar key: v⁷⁰ · ω⁶ ≤ v⁹⁰
  have hkey : v ^ 70 * ω ^ 6 ≤ v ^ 90 := by
    calc v ^ 70 * ω ^ 6 ≤ v ^ 70 * v ^ 12 :=
          mul_le_mul_of_nonneg_left hω6 (by positivity)
      _ = v ^ 82 := by ring
      _ ≤ v ^ 90 := by nlinarith [one_le_pow₀ (n := 8) hv1, pow_nonneg hv0.le 82]
  -- multiply by d²g⁸ω⁸
  nlinarith [mul_le_mul_of_nonneg_left hkey
    (show (0:ℝ) ≤ d ^ 2 * g ^ 8 * ω ^ 8 by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le]

/-- **κ·Nc² ≤ T2** (in √-variables): `(d⁶/(H g²ω))·(g⁸v⁶⁰/ω¹⁰) ≤ d²g⁸v⁹⁰/ω¹⁴`.
Needs `d⁴g²v²⁰ ≤ H`, `g,v ≥ 1`, `ω ≤ v²`. -/
private theorem mon_κ_Nc2 {g v d ω H : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hH0 : 0 < H) (hg1 : 1 ≤ g) (hv1 : 1 ≤ v) (hωv2 : ω ≤ v ^ 2)
    (hHbig : d ^ 4 * g ^ 2 * v ^ 20 ≤ H) :
    (d ^ 6 / (H * g ^ 2 * ω)) * (g ^ 8 * v ^ 60 / ω ^ 10)
      ≤ d ^ 2 * g ^ 8 * v ^ 90 / ω ^ 14 := by
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  -- after clearing: d⁶ g⁸ v⁶⁰ · ω¹⁴ ≤ d²g⁸v⁹⁰ · (H g²ω·ω¹⁰), i.e. d⁴ ω³ ≤ H g² v³⁰.
  -- key: d⁴ ≤ d⁴g²v²⁰ ≤ H; ω³ ≤ v⁶ ≤ g²v³⁰; multiply.
  have hd4 : d ^ 4 ≤ H := by
    have hge1 : (1:ℝ) ≤ g ^ 2 * v ^ 20 := by
      nlinarith [one_le_pow₀ (n := 2) hg1, one_le_pow₀ (n := 20) hv1]
    calc d ^ 4 = d ^ 4 * 1 := by ring
      _ ≤ d ^ 4 * (g ^ 2 * v ^ 20) := mul_le_mul_of_nonneg_left hge1 (by positivity)
      _ = d ^ 4 * g ^ 2 * v ^ 20 := by ring
      _ ≤ H := hHbig
  have hω3 : ω ^ 3 ≤ v ^ 6 := by
    have h := pow_le_pow_left₀ hω0.le hωv2 3
    calc ω ^ 3 ≤ (v ^ 2) ^ 3 := h
      _ = v ^ 6 := by ring
  have hv6 : v ^ 6 ≤ g ^ 2 * v ^ 30 := by
    have hg2 : (1:ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    have hv24 : (1:ℝ) ≤ v ^ 24 := one_le_pow₀ hv1
    calc v ^ 6 = 1 * (1 * v ^ 6) := by ring
      _ ≤ g ^ 2 * (v ^ 24 * v ^ 6) := by
            apply mul_le_mul hg2 _ (by positivity) (by positivity)
            calc (1:ℝ) * v ^ 6 = 1 * v ^ 6 := rfl
              _ ≤ v ^ 24 * v ^ 6 := by nlinarith [hv24, pow_nonneg hv0.le 6]
      _ = g ^ 2 * v ^ 30 := by ring
  have hω3' : ω ^ 3 ≤ g ^ 2 * v ^ 30 := le_trans hω3 hv6
  have hkey : d ^ 4 * ω ^ 3 ≤ H * (g ^ 2 * v ^ 30) :=
    mul_le_mul hd4 hω3' (by positivity) hH0.le
  nlinarith [mul_le_mul_of_nonneg_left hkey
    (show (0:ℝ) ≤ d ^ 2 * g ^ 8 * v ^ 60 * ω ^ 11 by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le, hH0.le]

/-- **Nc ≤ T3** (in √-variables): `g⁴v³⁰/ω⁵ ≤ H g⁹v⁷⁰/(d³ω⁸)`.
Needs `d⁴g²v²⁰ ≤ H` (so `d³ ≤ d⁴ ≤ H`), `g,v,d ≥ 1`, `ω ≤ v²`. -/
private theorem mon_Nc_T3 {g v d ω H : ℝ} (hg0 : 0 < g) (hv0 : 0 < v) (hd0 : 0 < d) (hω0 : 0 < ω)
    (hH0 : 0 < H) (hg1 : 1 ≤ g) (hv1 : 1 ≤ v) (hd1 : 1 ≤ d) (hωv2 : ω ≤ v ^ 2)
    (hHbig : d ^ 4 * g ^ 2 * v ^ 20 ≤ H) :
    g ^ 4 * v ^ 30 / ω ^ 5 ≤ H * g ^ 9 * v ^ 70 / (d ^ 3 * ω ^ 8) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- after clearing: g⁴v³⁰ · (d³ω⁸) ≤ H g⁹v⁷⁰ · ω⁵, i.e. d³ ω³ ≤ H g⁵ v⁴⁰.
  have hd3 : d ^ 3 ≤ H := by
    have hge1 : (1:ℝ) ≤ d * g ^ 2 * v ^ 20 := by
      nlinarith [hd1, one_le_pow₀ (n := 2) hg1, one_le_pow₀ (n := 20) hv1,
        mul_le_mul (mul_le_mul hd1 (one_le_pow₀ (n := 2) hg1) (by norm_num) (by positivity))
          (one_le_pow₀ (n := 20) hv1) (by norm_num) (by positivity)]
    calc d ^ 3 = d ^ 3 * 1 := by ring
      _ ≤ d ^ 3 * (d * g ^ 2 * v ^ 20) := mul_le_mul_of_nonneg_left hge1 (by positivity)
      _ = d ^ 4 * g ^ 2 * v ^ 20 := by ring
      _ ≤ H := hHbig
  have hω3 : ω ^ 3 ≤ v ^ 6 := by
    have h := pow_le_pow_left₀ hω0.le hωv2 3
    calc ω ^ 3 ≤ (v ^ 2) ^ 3 := h
      _ = v ^ 6 := by ring
  have hv6 : v ^ 6 ≤ g ^ 5 * v ^ 40 := by
    have hg5 : (1:ℝ) ≤ g ^ 5 := one_le_pow₀ hg1
    have hv34 : (1:ℝ) ≤ v ^ 34 := one_le_pow₀ hv1
    calc v ^ 6 = 1 * (1 * v ^ 6) := by ring
      _ ≤ g ^ 5 * (v ^ 34 * v ^ 6) := by
            apply mul_le_mul hg5 _ (by positivity) (by positivity)
            nlinarith [hv34, pow_nonneg hv0.le 6]
      _ = g ^ 5 * v ^ 40 := by ring
  have hω3' : ω ^ 3 ≤ g ^ 5 * v ^ 40 := le_trans hω3 hv6
  have hkey : d ^ 3 * ω ^ 3 ≤ H * (g ^ 5 * v ^ 40) :=
    mul_le_mul hd3 hω3' (by positivity) hH0.le
  nlinarith [mul_le_mul_of_nonneg_left hkey
    (show (0:ℝ) ≤ g ^ 4 * v ^ 30 * ω ^ 5 by positivity),
    hd0.le, hg0.le, hv0.le, hω0.le, hH0.le]

set_option maxHeartbeats 1600000 in
/-- §5 Step-2 scale-domination to the two Step-2 `Bcombine` monomials `t2`, `t3`. -/
theorem step2_fsum_le_t2t3
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩ1 : 1 ≤ S.Ω) (hΩU : S.Ω ≤ P.U) (hGU : P.G ≤ P.U)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (Nf : ℝ) (hNf1 : 1 ≤ Nf)
    (hNfbd : Nf ≤ 10 ^ 30 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5)) :
    112 * ( S.R * (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6)) * Nf
          + 2 * S.R * Real.sqrt ((S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6))
                / (S.D ^ 4 / (P.X * S.A))) * Real.sqrt Nf
          + (S.D ^ 4 / (P.X * S.A)) * Nf ^ 2
          + Nf )
      ≤ 10 ^ 65 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 4 * P.U ^ 45 / S.Ω ^ 14)
          + (P.H / S.Δ) * (P.G ^ ((9:ℝ)/2) * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))) := by
  -- positivity
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos; have hXpos := P.X_pos
  have hGnn := hGpos.le; have hUnn := hUpos.le; have hHnn := hHpos.le
  have hΩnn := hΩpos.le; have hΔnn := hΔpos.le
  -- square-root building blocks: sG = √G, sU = √U, sD = √Δ
  set sG : ℝ := P.G ^ ((1 : ℝ) / 2) with hsGdef
  set sU : ℝ := P.U ^ ((1 : ℝ) / 2) with hsUdef
  set sD : ℝ := S.Δ ^ ((1 : ℝ) / 2) with hsDdef
  have hsG0 : 0 < sG := Real.rpow_pos_of_pos hGpos _
  have hsU0 : 0 < sU := Real.rpow_pos_of_pos hUpos _
  have hsD0 : 0 < sD := Real.rpow_pos_of_pos hΔpos _
  have hsG1 : 1 ≤ sG := Real.one_le_rpow hG1 (by norm_num)
  have hsU1 : 1 ≤ sU := Real.one_le_rpow hU1 (by norm_num)
  have hsD1 : 1 ≤ sD := Real.one_le_rpow hΔ1 (by norm_num)
  -- second-power collapses sG² = G etc.
  have hsG2 : sG ^ 2 = P.G := by
    rw [hsGdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hGnn]; norm_num
  have hsU2 : sU ^ 2 = P.U := by
    rw [hsUdef, ← Real.rpow_natCast (P.U ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hUnn]; norm_num
  have hsD2 : sD ^ 2 = S.Δ := by
    rw [hsDdef, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hΔnn]; norm_num
  -- half-power facts for the targets
  have hG92 : P.G ^ ((9 : ℝ) / 2) = sG ^ 9 := by
    rw [hsGdef, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/2)) 9, ← Real.rpow_mul hGnn]; norm_num
  have hΔ12 : S.Δ ^ ((1 : ℝ) / 2) = sD := hsDdef.symm
  -- √Δ as the rpow-1/2 building block
  have hsqrtΔ : Real.sqrt S.Δ = sD := by rw [hsDdef, Real.sqrt_eq_rpow]
  -- κ, R in plain monomials
  have hκval : S.D ^ 4 / (P.X * S.A) = S.Δ ^ 3 / (P.H * P.G * S.Ω) := defect_D4_div_XA S
  have hHne := ne_of_gt hHpos; have hΔne := ne_of_gt hΔpos
  have hΩne := ne_of_gt hΩpos; have hGne := ne_of_gt hGpos
  -- R·δ collapses to ρ-coeff
  have hρval : S.R * (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6))
      = P.G ^ 2 * S.Δ * P.U ^ 20 / S.Ω ^ 3 := by
    unfold Scale.R; field_simp
  -- δ/κ collapses to G²U²⁰/(Δ·Ω⁵)
  have hδκval : (S.Δ ^ 2 * P.G * P.U ^ 20 / (P.H * S.Ω ^ 6)) / (S.D ^ 4 / (P.X * S.A))
      = P.G ^ 2 * P.U ^ 20 / (S.Δ * S.Ω ^ 5) := by
    rw [hκval]; field_simp
  -- R in plain monomials: R = H·G·Ω³/Δ
  have hRval : S.R = P.H * P.G * S.Ω ^ 3 / S.Δ := by unfold Scale.R; field_simp
  -- ===== rewrite the LHS coefficients & cap to √-variables =====
  -- powers in √-variables
  have hG2 : P.G ^ 2 = sG ^ 4 := by rw [← hsG2]; ring
  have hG4 : P.G ^ 4 = sG ^ 8 := by rw [← hsG2]; ring
  have hU15 : P.U ^ 15 = sU ^ 30 := by rw [← hsU2]; ring
  have hU20 : P.U ^ 20 = sU ^ 40 := by rw [← hsU2]; ring
  have hU35 : P.U ^ 35 = sU ^ 70 := by rw [← hsU2]; ring
  have hU45 : P.U ^ 45 = sU ^ 90 := by rw [← hsU2]; ring
  have hΔ1' : S.Δ = sD ^ 2 := hsD2.symm
  have hΔ3 : S.Δ ^ 3 = sD ^ 6 := by rw [hΔ1']; ring
  have hΔ2' : S.Δ ^ 2 = sD ^ 4 := by rw [hΔ1']; ring
  -- regime fact: Δ²·G·U¹⁰ ≤ H, hence sD⁴·sG²·sU²⁰ ≤ H
  have hH_big : S.Δ ^ 2 * P.G * P.U ^ 10 ≤ P.H := by
    have hΔ2 : (0:ℝ) < S.Δ ^ 2 := by positivity
    have hkey := (le_div_iff₀ hΔ2).mp h1
    have heq : S.Δ ^ 2 * P.G * P.U ^ 10 = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
    rw [heq]; exact hkey
  have hU10 : P.U ^ 10 = sU ^ 20 := by rw [← hsU2]; ring
  have hH_big' : sD ^ 4 * sG ^ 2 * sU ^ 20 ≤ P.H := by
    calc sD ^ 4 * sG ^ 2 * sU ^ 20 = S.Δ ^ 2 * P.G * P.U ^ 10 := by rw [hΔ2', hsG2, hU10]
      _ ≤ P.H := hH_big
  -- √-variable regime facts
  have hΩsU2 : S.Ω ≤ sU ^ 2 := by rw [hsU2]; exact hΩU
  -- ===== monomial targets / coefficients in √-variables =====
  -- T2 = sD²·sG⁸·sU⁹⁰/Ω¹⁴
  have hT2eq : (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 4 * P.U ^ 45 / S.Ω ^ 14)
      = sD ^ 2 * sG ^ 8 * sU ^ 90 / S.Ω ^ 14 := by
    rw [hG4, hU45, hΔ2', hΔ1']; field_simp
  -- T3 = H·sG⁹·sU⁷⁰/(sD³·Ω⁸)
  have hT3eq : (P.H / S.Δ) * (P.G ^ ((9:ℝ)/2) * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))
      = P.H * sG ^ 9 * sU ^ 70 / (sD ^ 3 * S.Ω ^ 8) := by
    rw [hG92, hU35, hΔ12, hΔ1']; field_simp
  -- ρ-coeff = sD²·sG⁴·sU⁴⁰/Ω³
  have hρeq : P.G ^ 2 * S.Δ * P.U ^ 20 / S.Ω ^ 3 = sD ^ 2 * sG ^ 4 * sU ^ 40 / S.Ω ^ 3 := by
    rw [hG2, hΔ1', hU20]; ring
  -- κ-coeff = sD⁶/(H·sG²·Ω)
  have hκeq : S.Δ ^ 3 / (P.H * P.G * S.Ω) = sD ^ 6 / (P.H * sG ^ 2 * S.Ω) := by rw [hΔ3, hsG2]
  -- δ/κ-coeff = sG⁴·sU⁴⁰/(sD²·Ω⁵)
  have hδκeq : P.G ^ 2 * P.U ^ 20 / (S.Δ * S.Ω ^ 5) = sG ^ 4 * sU ^ 40 / (sD ^ 2 * S.Ω ^ 5) := by
    rw [hG2, hU20, hΔ1']
  -- R = H·sG²·Ω³/sD²
  have hReq : P.H * P.G * S.Ω ^ 3 / S.Δ = P.H * sG ^ 2 * S.Ω ^ 3 / sD ^ 2 := by rw [hsG2, hΔ1']
  -- Nf-cap piece Nc = sG⁴·sU³⁰/Ω⁵
  have hNceq : P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5 = sG ^ 4 * sU ^ 30 / S.Ω ^ 5 := by rw [hG2, hU15]
  -- ===== abbreviate =====
  set ρc : ℝ := sD ^ 2 * sG ^ 4 * sU ^ 40 / S.Ω ^ 3 with hρcdef
  set κc : ℝ := sD ^ 6 / (P.H * sG ^ 2 * S.Ω) with hκcdef
  set dkc : ℝ := sG ^ 4 * sU ^ 40 / (sD ^ 2 * S.Ω ^ 5) with hdkcdef
  set Rc : ℝ := P.H * sG ^ 2 * S.Ω ^ 3 / sD ^ 2 with hRcdef
  set Nc : ℝ := sG ^ 4 * sU ^ 30 / S.Ω ^ 5 with hNcdef
  set T2 : ℝ := sD ^ 2 * sG ^ 8 * sU ^ 90 / S.Ω ^ 14 with hT2def
  set T3 : ℝ := P.H * sG ^ 9 * sU ^ 70 / (sD ^ 3 * S.Ω ^ 8) with hT3def
  have hρcnn : 0 ≤ ρc := by rw [hρcdef]; positivity
  have hκcnn : 0 ≤ κc := by rw [hκcdef]; positivity
  have hdkcnn : 0 ≤ dkc := by rw [hdkcdef]; positivity
  have hRcnn : 0 ≤ Rc := by rw [hRcdef]; positivity
  have hNcnn : 0 ≤ Nc := by rw [hNcdef]; positivity
  have hT2nn : 0 ≤ T2 := by rw [hT2def]; positivity
  have hT3nn : 0 ≤ T3 := by rw [hT3def]; positivity
  have hNfnn : (0:ℝ) ≤ Nf := by linarith
  -- Nf-cap: Nf ≤ 10³⁰·Nc
  have hCap : Nf ≤ 10 ^ 30 * Nc := by rw [← hNceq]; exact hNfbd
  -- ===== rewrite goal's coefficients to √-variables =====
  rw [hρval, hδκval, hκval]
  rw [hRval]
  -- now rewrite the monomials in √-vars and the targets
  rw [hT2eq, hT3eq]
  rw [hρeq, hκeq, hδκeq, hReq]
  -- ========= term bounds =========
  -- term1 : ρc·Nf ≤ 10³⁰·T2
  have hterm1 : ρc * Nf ≤ 10 ^ 30 * T2 := by
    have hstep : ρc * Nf ≤ ρc * (10 ^ 30 * Nc) := mul_le_mul_of_nonneg_left hCap hρcnn
    have hmon : ρc * Nc ≤ T2 := by
      rw [hρcdef, hNcdef, hT2def]
      exact mon_Rδ_Nc hsG0 hsU0 hsD0 hΩpos hsG1 hsU1 hΩsU2
    calc ρc * Nf ≤ ρc * (10 ^ 30 * Nc) := hstep
      _ = 10 ^ 30 * (ρc * Nc) := by ring
      _ ≤ 10 ^ 30 * T2 := mul_le_mul_of_nonneg_left hmon (by norm_num)
  -- term3 : κc·Nf² ≤ 10⁶⁰·T2
  have hterm3 : κc * Nf ^ 2 ≤ 10 ^ 60 * T2 := by
    have hNf2 : Nf ^ 2 ≤ (10 ^ 30 * Nc) ^ 2 := by
      apply pow_le_pow_left₀ hNfnn hCap
    have hstep : κc * Nf ^ 2 ≤ κc * (10 ^ 30 * Nc) ^ 2 := mul_le_mul_of_nonneg_left hNf2 hκcnn
    have hmon : κc * (sG ^ 8 * sU ^ 60 / S.Ω ^ 10) ≤ T2 := by
      rw [hκcdef, hT2def]
      exact mon_κ_Nc2 hsG0 hsU0 hsD0 hΩpos hHpos hsG1 hsU1 hΩsU2 hH_big'
    have hNc2 : (10 ^ 30 * Nc) ^ 2 = 10 ^ 60 * (sG ^ 8 * sU ^ 60 / S.Ω ^ 10) := by
      rw [hNcdef]
      field_simp
    rw [hNc2] at hstep
    calc κc * Nf ^ 2 ≤ κc * (10 ^ 60 * (sG ^ 8 * sU ^ 60 / S.Ω ^ 10)) := hstep
      _ = 10 ^ 60 * (κc * (sG ^ 8 * sU ^ 60 / S.Ω ^ 10)) := by ring
      _ ≤ 10 ^ 60 * T2 := mul_le_mul_of_nonneg_left hmon (by norm_num)
  -- term4 : Nf ≤ 10³⁰·T3
  have hterm4 : Nf ≤ 10 ^ 30 * T3 := by
    have hmon : Nc ≤ T3 := by
      rw [hNcdef, hT3def]
      exact mon_Nc_T3 hsG0 hsU0 hsD0 hΩpos hHpos hsG1 hsU1 hsD1 hΩsU2 hH_big'
    calc Nf ≤ 10 ^ 30 * Nc := hCap
      _ ≤ 10 ^ 30 * T3 := mul_le_mul_of_nonneg_left hmon (by norm_num)
  -- term2 : 2·Rc·√(dkc)·√Nf ≤ 2·10¹⁵·T3
  -- combine sqrts: √dkc·√Nf = √(dkc·Nf), bound radicand by perfect square
  have hterm2 : 2 * Rc * Real.sqrt dkc * Real.sqrt Nf ≤ 2 * 10 ^ 15 * T3 := by
    -- √dkc·√Nf = √(dkc·Nf)
    have hsqcomb : Real.sqrt dkc * Real.sqrt Nf = Real.sqrt (dkc * Nf) :=
      (Real.sqrt_mul hdkcnn Nf).symm
    -- radicand bound: dkc·Nf ≤ 10³⁰·(sG⁸sU⁷⁰/(sD²Ω¹⁰)) = M² with M = 10¹⁵·sG⁴sU³⁵/(sD·Ω⁵)
    set M : ℝ := 10 ^ 15 * (sG ^ 4 * sU ^ 35 / (sD * S.Ω ^ 5)) with hMdef
    have hMnn : 0 ≤ M := by rw [hMdef]; positivity
    have hM2 : M ^ 2 = 10 ^ 30 * (sG ^ 8 * sU ^ 70 / (sD ^ 2 * S.Ω ^ 10)) := by
      rw [hMdef]
      field_simp
    -- dkc·Nc = sG⁸sU⁷⁰/(sD²Ω¹⁰)
    have hdkcNc : dkc * Nc = sG ^ 8 * sU ^ 70 / (sD ^ 2 * S.Ω ^ 10) := by
      rw [hdkcdef, hNcdef, div_mul_div_comm]
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    have hrad : dkc * Nf ≤ M ^ 2 := by
      have hstep : dkc * Nf ≤ dkc * (10 ^ 30 * Nc) := mul_le_mul_of_nonneg_left hCap hdkcnn
      rw [hM2]
      calc dkc * Nf ≤ dkc * (10 ^ 30 * Nc) := hstep
        _ = 10 ^ 30 * (dkc * Nc) := by ring
        _ = 10 ^ 30 * (sG ^ 8 * sU ^ 70 / (sD ^ 2 * S.Ω ^ 10)) := by rw [hdkcNc]
    have hsqrtle : Real.sqrt (dkc * Nf) ≤ M := (Real.sqrt_le_left hMnn).mpr hrad
    -- combine sqrts: √dkc·√Nf ≤ M
    have hsqprod : Real.sqrt dkc * Real.sqrt Nf ≤ M := by rw [hsqcomb]; exact hsqrtle
    -- now: 2·Rc·√(dkc·Nf) ≤ 2·Rc·M; and 2·Rc·M ≤ 2·10¹⁵·T3
    -- key scalar: Ω⁶ ≤ sG³ sU³⁵   (Ω ≤ sU², so Ω⁶ ≤ sU¹² ≤ sU³⁵; sG³ ≥ 1)
    have hΩ6 : S.Ω ^ 6 ≤ sU ^ 12 := by
      have h := pow_le_pow_left₀ hΩpos.le hΩsU2 6
      calc S.Ω ^ 6 ≤ (sU ^ 2) ^ 6 := h
        _ = sU ^ 12 := by ring
    have hsU12_35 : sU ^ 12 ≤ sU ^ 35 := pow_le_pow_right₀ hsU1 (by norm_num)
    have hsG3 : (1:ℝ) ≤ sG ^ 3 := one_le_pow₀ hsG1
    have hkeyΩ : S.Ω ^ 6 ≤ sG ^ 3 * sU ^ 35 := by
      calc S.Ω ^ 6 ≤ sU ^ 12 := hΩ6
        _ ≤ sU ^ 35 := hsU12_35
        _ = 1 * sU ^ 35 := by rw [one_mul]
        _ ≤ sG ^ 3 * sU ^ 35 :=
            mul_le_mul_of_nonneg_right hsG3 (by positivity)
    -- numerator monotonicity: P.H sG⁶ sU³⁵ Ω⁶ ≤ P.H sG⁹ sU⁷⁰
    have hfac : P.H * sG ^ 6 * sU ^ 35 * S.Ω ^ 6 ≤ P.H * sG ^ 9 * sU ^ 70 := by
      have h := mul_le_mul_of_nonneg_left hkeyΩ
        (show (0:ℝ) ≤ P.H * sG ^ 6 * sU ^ 35 by positivity)
      calc P.H * sG ^ 6 * sU ^ 35 * S.Ω ^ 6
          = (P.H * sG ^ 6 * sU ^ 35) * S.Ω ^ 6 := by ring
        _ ≤ (P.H * sG ^ 6 * sU ^ 35) * (sG ^ 3 * sU ^ 35) := h
        _ = P.H * sG ^ 9 * sU ^ 70 := by ring
    have hRcM : 2 * Rc * M ≤ 2 * 10 ^ 15 * T3 := by
      -- express both sides as single fractions over a common denominator sD³·Ω⁸
      have hL : 2 * Rc * M
          = 2 * 10 ^ 15 * (P.H * sG ^ 6 * sU ^ 35 * S.Ω ^ 6) / (sD ^ 3 * S.Ω ^ 8) := by
        rw [hRcdef, hMdef]; field_simp
      have hR : 2 * 10 ^ 15 * T3
          = 2 * 10 ^ 15 * (P.H * sG ^ 9 * sU ^ 70) / (sD ^ 3 * S.Ω ^ 8) := by
        rw [hT3def]; ring
      rw [hL, hR]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hfac (by norm_num)
    -- combine: 2·Rc·(√dkc·√Nf) ≤ 2·Rc·M ≤ 2·10¹⁵·T3
    have hreassoc : 2 * Rc * Real.sqrt dkc * Real.sqrt Nf
        = 2 * Rc * (Real.sqrt dkc * Real.sqrt Nf) := by ring
    rw [hreassoc]
    calc 2 * Rc * (Real.sqrt dkc * Real.sqrt Nf)
        ≤ 2 * Rc * M := by
          have h2Rc : 0 ≤ 2 * Rc := by positivity
          exact mul_le_mul_of_nonneg_left hsqprod h2Rc
      _ ≤ 2 * 10 ^ 15 * T3 := hRcM
  -- ===== combine all four terms =====
  -- goal: 112·(ρc·Nf + 2·Rc·√dkc·√Nf + κc·Nf² + Nf) ≤ 10⁶⁵·(T2 + T3)
  have hsum : ρc * Nf + 2 * Rc * Real.sqrt dkc * Real.sqrt Nf + κc * Nf ^ 2 + Nf
      ≤ (10 ^ 30 + 10 ^ 60) * T2 + (2 * 10 ^ 15 + 10 ^ 30) * T3 := by
    linarith [hterm1, hterm2, hterm3, hterm4]
  calc 112 * (ρc * Nf + 2 * Rc * Real.sqrt dkc * Real.sqrt Nf + κc * Nf ^ 2 + Nf)
      ≤ 112 * ((10 ^ 30 + 10 ^ 60) * T2 + (2 * 10 ^ 15 + 10 ^ 30) * T3) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 112 * (10 ^ 30 + 10 ^ 60) * T2 + 112 * (2 * 10 ^ 15 + 10 ^ 30) * T3 := by ring
    _ ≤ 10 ^ 65 * (T2 + T3) := by
        have hc2 : (112:ℝ) * (10 ^ 30 + 10 ^ 60) ≤ 10 ^ 65 := by norm_num
        have hc3 : (112:ℝ) * (2 * 10 ^ 15 + 10 ^ 30) ≤ 10 ^ 65 := by norm_num
        have h2 := mul_le_mul_of_nonneg_right hc2 hT2nn
        have h3 := mul_le_mul_of_nonneg_right hc3 hT3nn
        have hexp : (10:ℝ) ^ 65 * (T2 + T3) = 10 ^ 65 * T2 + 10 ^ 65 * T3 := by ring
        rw [hexp]
        linarith [h2, h3]

end Squarefree
