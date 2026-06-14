import Squarefree.Lower.Step4Band5

/-!
# §5 Step-4 E-part hybrid fit (B-block summands)

The two √-free summand discharges feeding the hybrid E-coefficient B-block fit
(`cEhyb·dc·N` with the `√L` of `dc` already cancelled against `cEhyb`'s `1/√L`),
plus the target-form rewrite.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

set_option maxHeartbeats 1600000

/-- Common tail: `K·C·G⁸·U⁴⁵/Ωᵐ ≤ C·Δ·G¹⁵·U⁹⁰/Ω²⁷` once the scalar fits `K ≤ U²` and
`11 ≤ m ≤ 27` (keep-net: pad `Ω^{27−m} ≤ U^{27−m} ≤ U¹⁶`; no `Ω ≥ 1` needed). -/
private theorem fitEB_tail (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (C K : ℝ) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hK : K ≤ P.U ^ 2) (m : ℕ) (hm11 : 11 ≤ m) (hm27 : m ≤ 27) :
    K * C * P.G ^ 8 * P.U ^ 45 / S.Ω ^ m ≤ C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
  have hΩpos := S.Ω_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hG815 : P.G ^ 8 ≤ P.G ^ 15 := pow_le_pow_right₀ hG1 (by norm_num)
  have hpad : S.Ω ^ (27 - m) ≤ P.U ^ 16 :=
    le_trans (pow_le_pow_left₀ hΩpos.le hΩU _) (pow_le_pow_right₀ hU1 (by omega))
  have hsplit : S.Ω ^ 27 = S.Ω ^ (27 - m) * S.Ω ^ m := by
    rw [← pow_add]; congr 1; omega
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc K * C * P.G ^ 8 * P.U ^ 45 * S.Ω ^ 27
      = (K * C * P.G ^ 8 * P.U ^ 45 * S.Ω ^ (27 - m)) * S.Ω ^ m := by rw [hsplit]; ring
    _ ≤ (P.U ^ 2 * C * P.G ^ 15 * P.U ^ 45 * P.U ^ 16) * S.Ω ^ m := by
        gcongr (?_ * C * ?_ * P.U ^ 45 * ?_) * S.Ω ^ m
    _ = C * 1 * P.G ^ 15 * P.U ^ 63 * S.Ω ^ m := by ring
    _ ≤ C * S.Δ * P.G ^ 15 * P.U ^ 63 * S.Ω ^ m := by
        gcongr C * ?_ * P.G ^ 15 * P.U ^ 63 * S.Ω ^ m
    _ ≤ C * S.Δ * P.G ^ 15 * P.U ^ 90 * S.Ω ^ m := by
        gcongr C * S.Δ * P.G ^ 15 * ?_ * S.Ω ^ m
        exact pow_le_pow_right₀ hU1 (by norm_num)

/-- Collapse `Δ²/H ≤ 1/(G·U¹⁰)` (from `h1`) and the 6-factor window `W ≤ G⁶U³⁰`,
then finish with `fitEB_tail`. -/
private theorem fitEB_pieceH (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (C K W : ℝ) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hK : 130 ^ 6 * K ≤ P.U ^ 2) (hW : W ≤ 130 ^ 6 * (P.G ^ 6 * P.U ^ 30)) :
    K * C * S.Δ ^ 2 * P.G ^ 3 * P.U ^ 25 * W / (P.H * S.Ω ^ 14)
      ≤ C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 := by
  have hΩpos := S.Ω_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hΔpos := S.Δ_pos
  have hHpos := P.H_pos
  have hfrac : S.Δ ^ 2 * P.G * P.U ^ 10 / P.H ≤ 1 := by
    rw [div_le_one hHpos]
    have hH : P.G * P.U ^ 10 * S.Δ ^ 2 ≤ P.H :=
      (le_div_iff₀ (by positivity)).mp h1
    calc S.Δ ^ 2 * P.G * P.U ^ 10 = P.G * P.U ^ 10 * S.Δ ^ 2 := by ring
      _ ≤ P.H := hH
  calc K * C * S.Δ ^ 2 * P.G ^ 3 * P.U ^ 25 * W / (P.H * S.Ω ^ 14)
      ≤ K * C * S.Δ ^ 2 * P.G ^ 3 * P.U ^ 25 * (130 ^ 6 * (P.G ^ 6 * P.U ^ 30))
          / (P.H * S.Ω ^ 14) := by
        gcongr K * C * S.Δ ^ 2 * P.G ^ 3 * P.U ^ 25 * ?_ / (P.H * S.Ω ^ 14)
    _ = ((130 ^ 6 * K) * C * P.G ^ 8 * P.U ^ 45 / S.Ω ^ 14)
          * (S.Δ ^ 2 * P.G * P.U ^ 10 / P.H) := by
        ring
    _ ≤ ((130 ^ 6 * K) * C * P.G ^ 8 * P.U ^ 45 / S.Ω ^ 14) * 1 := by
        gcongr ((130 ^ 6 * K) * C * P.G ^ 8 * P.U ^ 45 / S.Ω ^ 14) * ?_
    _ = (130 ^ 6 * K) * C * P.G ^ 8 * P.U ^ 45 / S.Ω ^ 14 := mul_one _
    _ ≤ C * S.Δ * P.G ^ 15 * P.U ^ 90 / S.Ω ^ 27 :=
        fitEB_tail hG1 hU1 hΔ1 hΩU C (130 ^ 6 * K) hC0
          (mul_nonneg (by norm_num) hK0) hK 14 (by norm_num) (by norm_num)

/-- **Hybrid E-fit, T1 (gap block).** The gap-summand of `cEhyb·dc·N` (with `√L` already
cancelled) fits twice the `t7'`-shaped target block; the factor 2 covers both gap pieces. -/
theorem step4_fitEB_T1
    (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5))
    (n C : ℝ) (hC : 1 ≤ C)
    (hncap : n ≤ C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8) (hn0 : 0 ≤ n)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11*S.A)
    (gap : ℝ) (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2*10^12*S.Δ/(P.G*S.Ω^3*ℓ₁) + 10^13*ℓ₁*S.Δ^3/(P.H*P.G^2*S.Ω^6)) :
    (10^10*a*P.G*S.Ω^3*gap/S.Δ^2) * (P.G^4*P.U^15/S.Ω^4) * n
      ≤ 2 * (C * (P.H/S.Δ) * (S.Δ^2*P.G^15*P.U^90/(P.H*S.Ω^27))) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hd0 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  have hℓ1ne : ℓ₁ ≠ 0 := ne_of_gt hℓ1pos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hGne : P.G ≠ 0 := ne_of_gt hGpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have ha' : a ≤ 11*(S.Δ*S.Ω) := by
    rw [show S.A = S.Δ*S.Ω from rfl] at ha_hi; exact ha_hi
  have hdW : ℓ₂ - ℓ₁ ≤ 130*(P.G*P.U^5) := by linarith
  -- step 1: monotone pass to the explicit caps
  have hmono : (10^10*a*P.G*S.Ω^3*gap/S.Δ^2) * (P.G^4*P.U^15/S.Ω^4) * n
      ≤ (10^10*(11*(S.Δ*S.Ω))*P.G*S.Ω^3*(2*10^12*S.Δ/(P.G*S.Ω^3*ℓ₁)
            + 10^13*ℓ₁*S.Δ^3/(P.H*P.G^2*S.Ω^6))/S.Δ^2) * (P.G^4*P.U^15/S.Ω^4)
          * (C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8) := by
    gcongr 10^10*?_*P.G*S.Ω^3*?_/S.Δ^2 * (P.G^4*P.U^15/S.Ω^4) * ?_
  -- step 2: split the capped product into the two collected gap pieces
  have hsplit : (10^10*(11*(S.Δ*S.Ω))*P.G*S.Ω^3*(2*10^12*S.Δ/(P.G*S.Ω^3*ℓ₁)
            + 10^13*ℓ₁*S.Δ^3/(P.H*P.G^2*S.Ω^6))/S.Δ^2) * (P.G^4*P.U^15/S.Ω^4)
          * (C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8)
      = 22*10^22*C*P.G^4*P.U^25*(ℓ₁^2*(ℓ₂*(ℓ₂-ℓ₁)))/S.Ω^11
        + 11*10^23*C*S.Δ^2*P.G^3*P.U^25*(ℓ₁^4*(ℓ₂*(ℓ₂-ℓ₁)))/(P.H*S.Ω^14) := by
    field_simp
    ring
  -- step 3: gap₁ piece — 4-factor window then tail
  have hK1 : (130:ℝ)^4*(22*10^22) ≤ P.U^2 := by
    calc (130:ℝ)^4*(22*10^22) ≤ (10:ℝ)^33 := by norm_num
      _ ≤ P.U := hUbig
      _ = P.U^1 := (pow_one _).symm
      _ ≤ P.U^2 := pow_le_pow_right₀ hU1 one_le_two
  have hm2 : ℓ₂*(ℓ₂-ℓ₁) ≤ (130*(P.G*P.U^5))*(130*(P.G*P.U^5)) :=
    mul_le_mul hℓ2W hdW hd0.le (by positivity)
  have hW4 : ℓ₁^2*(ℓ₂*(ℓ₂-ℓ₁)) ≤ 130^4*(P.G^4*P.U^20) := by
    have h2 : ℓ₁^2 ≤ (130*(P.G*P.U^5))^2 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 2
    calc ℓ₁^2*(ℓ₂*(ℓ₂-ℓ₁)) ≤ (130*(P.G*P.U^5))^2*((130*(P.G*P.U^5))*(130*(P.G*P.U^5))) :=
          mul_le_mul h2 hm2 (mul_nonneg (by linarith) hd0.le) (by positivity)
      _ = 130^4*(P.G^4*P.U^20) := by ring
  have hP1 : 22*10^22*C*P.G^4*P.U^25*(ℓ₁^2*(ℓ₂*(ℓ₂-ℓ₁)))/S.Ω^11
      ≤ C*S.Δ*P.G^15*P.U^90/S.Ω^27 := by
    calc 22*10^22*C*P.G^4*P.U^25*(ℓ₁^2*(ℓ₂*(ℓ₂-ℓ₁)))/S.Ω^11
        ≤ 22*10^22*C*P.G^4*P.U^25*(130^4*(P.G^4*P.U^20))/S.Ω^11 := by
          gcongr 22*10^22*C*P.G^4*P.U^25*?_/S.Ω^11
      _ = (130^4*(22*10^22))*C*P.G^8*P.U^45/S.Ω^11 := by ring
      _ ≤ C*S.Δ*P.G^15*P.U^90/S.Ω^27 :=
          fitEB_tail hG1 hU1 hΔ1 hΩU C (130^4*(22*10^22)) hC0.le (by positivity) hK1 11
            (by norm_num) (by norm_num)
  -- step 4: gap₂ piece — 6-factor window then H-collapse + tail
  have hK2 : (130:ℝ)^6*(11*10^23) ≤ P.U^2 := by
    calc (130:ℝ)^6*(11*10^23) ≤ ((10:ℝ)^33)^2 := by norm_num
      _ ≤ P.U^2 := pow_le_pow_left₀ (by norm_num) hUbig 2
  have hW6 : ℓ₁^4*(ℓ₂*(ℓ₂-ℓ₁)) ≤ 130^6*(P.G^6*P.U^30) := by
    have h4 : ℓ₁^4 ≤ (130*(P.G*P.U^5))^4 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 4
    calc ℓ₁^4*(ℓ₂*(ℓ₂-ℓ₁)) ≤ (130*(P.G*P.U^5))^4*((130*(P.G*P.U^5))*(130*(P.G*P.U^5))) :=
          mul_le_mul h4 hm2 (mul_nonneg (by linarith) hd0.le) (by positivity)
      _ = 130^6*(P.G^6*P.U^30) := by ring
  have hP2 : 11*10^23*C*S.Δ^2*P.G^3*P.U^25*(ℓ₁^4*(ℓ₂*(ℓ₂-ℓ₁)))/(P.H*S.Ω^14)
      ≤ C*S.Δ*P.G^15*P.U^90/S.Ω^27 :=
    fitEB_pieceH h1 hG1 hU1 hΔ1 hΩU C (11*10^23) _ hC0.le (by norm_num) hK2 hW6
  -- assemble
  have h2t : 2 * (C * (P.H/S.Δ) * (S.Δ^2*P.G^15*P.U^90/(P.H*S.Ω^27)))
      = 2 * (C*S.Δ*P.G^15*P.U^90/S.Ω^27) := by
    field_simp
  refine (hmono.trans (le_of_eq hsplit)).trans ?_
  linarith [hP1, hP2]

/-- **Hybrid E-fit, T2 (B²-block).** The `ℓ₂B²/D`-summand of `cEhyb·dc·N` (with `√L`
already cancelled) fits the `t7'`-shaped target block. -/
theorem step4_fitEB_T2
    (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5))
    (n C : ℝ) (hC : 1 ≤ C)
    (hncap : n ≤ C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8) (hn0 : 0 ≤ n)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11*S.A) :
    (10^35*a*P.G*S.Ω^3*ℓ₂*S.B^2/(S.Δ^2*S.D)) * (P.G^4*P.U^15/S.Ω^4) * n
      ≤ C * (P.H/S.Δ) * (S.Δ^2*P.G^15*P.U^90/(P.H*S.Ω^27)) := by
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hHpos := P.H_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hd0 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  have hℓ1ne : ℓ₁ ≠ 0 := ne_of_gt hℓ1pos
  have hΔne : S.Δ ≠ 0 := ne_of_gt hΔpos
  have hΩne : S.Ω ≠ 0 := ne_of_gt hΩpos
  have hGne : P.G ≠ 0 := ne_of_gt hGpos
  have hHne : P.H ≠ 0 := ne_of_gt hHpos
  have ha' : a ≤ 11*(S.Δ*S.Ω) := by
    rw [show S.A = S.Δ*S.Ω from rfl] at ha_hi; exact ha_hi
  have hdW : ℓ₂ - ℓ₁ ≤ 130*(P.G*P.U^5) := by linarith
  rw [show S.B = S.Δ^2/(P.G*S.Ω^3) from rfl, show S.D = P.H*S.Δ from rfl]
  -- step 1: monotone pass to the explicit caps
  have hmono : (10^35*a*P.G*S.Ω^3*ℓ₂*(S.Δ^2/(P.G*S.Ω^3))^2/(S.Δ^2*(P.H*S.Δ)))
        * (P.G^4*P.U^15/S.Ω^4) * n
      ≤ (10^35*(11*(S.Δ*S.Ω))*P.G*S.Ω^3*ℓ₂*(S.Δ^2/(P.G*S.Ω^3))^2/(S.Δ^2*(P.H*S.Δ)))
        * (P.G^4*P.U^15/S.Ω^4) * (C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8) := by
    have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
    gcongr 10^35*?_*P.G*S.Ω^3*ℓ₂*(S.Δ^2/(P.G*S.Ω^3))^2/(S.Δ^2*(P.H*S.Δ))
      * (P.G^4*P.U^15/S.Ω^4) * ?_
  -- step 2: collect the capped product
  have hcollect : (10^35*(11*(S.Δ*S.Ω))*P.G*S.Ω^3*ℓ₂*(S.Δ^2/(P.G*S.Ω^3))^2/(S.Δ^2*(P.H*S.Δ)))
        * (P.G^4*P.U^15/S.Ω^4) * (C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8)
      = 11*10^35*C*S.Δ^2*P.G^3*P.U^25*(ℓ₁^3*(ℓ₂^2*(ℓ₂-ℓ₁)))/(P.H*S.Ω^14) := by
    field_simp
  -- step 3: scalar and 6-factor window budgets, then H-collapse + tail
  have hK3 : (130:ℝ)^6*(11*10^35) ≤ P.U^2 := by
    calc (130:ℝ)^6*(11*10^35) ≤ ((10:ℝ)^33)^2 := by norm_num
      _ ≤ P.U^2 := pow_le_pow_left₀ (by norm_num) hUbig 2
  have hW6 : ℓ₁^3*(ℓ₂^2*(ℓ₂-ℓ₁)) ≤ 130^6*(P.G^6*P.U^30) := by
    have h3 : ℓ₁^3 ≤ (130*(P.G*P.U^5))^3 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 3
    have hm : ℓ₂^2*(ℓ₂-ℓ₁) ≤ (130*(P.G*P.U^5))^2*(130*(P.G*P.U^5)) :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) hℓ2W 2) hdW hd0.le (by positivity)
    calc ℓ₁^3*(ℓ₂^2*(ℓ₂-ℓ₁)) ≤ (130*(P.G*P.U^5))^3*((130*(P.G*P.U^5))^2*(130*(P.G*P.U^5))) :=
          mul_le_mul h3 hm (mul_nonneg (sq_nonneg ℓ₂) hd0.le) (by positivity)
      _ = 130^6*(P.G^6*P.U^30) := by ring
  have hP3 : 11*10^35*C*S.Δ^2*P.G^3*P.U^25*(ℓ₁^3*(ℓ₂^2*(ℓ₂-ℓ₁)))/(P.H*S.Ω^14)
      ≤ C*S.Δ*P.G^15*P.U^90/S.Ω^27 :=
    fitEB_pieceH h1 hG1 hU1 hΔ1 hΩU C (11*10^35) _ hC0.le (by norm_num) hK3 hW6
  -- assemble
  rw [show C*(P.H/S.Δ)*(S.Δ^2*P.G^15*P.U^90/(P.H*S.Ω^27))
      = C*S.Δ*P.G^15*P.U^90/S.Ω^27 from by field_simp]
  exact (hmono.trans (le_of_eq hcollect)).trans hP3

/-- **Hybrid E-fit, target form.** The summed `t7'`-shaped budget collapses to
`8·C·Δ·G¹⁵·U⁹⁰/Ω²⁷`. -/
theorem step4_fitEB_target_eq (C : ℝ) :
    8 * C * (P.H/S.Δ) * (S.Δ^2*P.G^15*P.U^90/(P.H*S.Ω^27))
      = 8 * C * S.Δ*P.G^15*P.U^90/S.Ω^27 := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  field_simp

end Squarefree
