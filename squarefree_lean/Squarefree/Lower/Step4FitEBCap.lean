import Squarefree.Lower.Step4FitEB

/-!
# §5 Step-4 E-part hybrid fit, B-block: capped summand and `cE`-fit
The `Ecap4a` collapse, flat/degree-4 capped pieces, `step4_fitEB_cap`, and the full
B-half `cEhyb` fit `step4_fit_cE_B` assembled from the `Step4FitEB` `T1`/`T2` budgets.
-/

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- Key collapse: `(a/D)²·(Cref·(A/a)²) = Cref·A²/D² = 3ℓ₁ℓ₂(ℓ₂−ℓ₁)/D²`, so the flat
`Ecap4a` summand is `a`-free. -/
private theorem Ecap4a_collapse {a ℓ₁ ℓ₂ : ℝ} (ha : a ≠ 0) :
    Ecap4a P S a ℓ₁ ℓ₂
      = 2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/S.D^2)*(ℓ₁*Vmax P S)^2
          + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(Vmax P S)^4)/S.D) := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hDne : S.D ≠ 0 := by
    rw [show S.D = P.H*S.Δ from rfl]
    exact mul_ne_zero (ne_of_gt P.H_pos) hΔne
  rw [show Ecap4a P S a ℓ₁ ℓ₂
      = 2*(20*(a/S.D)^2*(Cref P S ℓ₁ ℓ₂*(S.A/a)^2)*(ℓ₁*Vmax P S)^2
          + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(Vmax P S)^4)/S.D)
      from rfl,
    show Cref P S ℓ₁ ℓ₂ = 3*ℓ₁*ℓ₂*(ℓ₂-ℓ₁)/(S.Δ^2*S.Ω^2) from rfl,
    show S.A = S.Δ*S.Ω from rfl]
  field_simp

/-- Generic Ω²⁷-form tail: `K·C·Gᵍ·Uᵘ/Ω²⁷ ≤ C·Δ·G¹⁵·U⁹⁰/Ω²⁷` once `K ≤ U³`, `g ≤ 15`,
`u ≤ 87`. -/
private theorem fitEB_tailB (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (C K : ℝ) (hC0 : 0 ≤ C) (hK : K ≤ P.U^3) (g u : ℕ) (hg : g ≤ 14) (hu : u ≤ 87) :
    K*C*P.G^g*P.U^u/S.Ω^27 ≤ C*S.Δ*P.G^14*P.U^90/S.Ω^27 := by
  have hΩpos := S.Ω_pos
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  calc K*C*P.G^g*P.U^u/S.Ω^27
      ≤ P.U^3*C*P.G^14*P.U^87/S.Ω^27 := by
        gcongr ?_*C*?_*?_/S.Ω^27
        · exact pow_le_pow_right₀ hG1 hg
        · exact pow_le_pow_right₀ hU1 hu
    _ = C*1*P.G^14*P.U^90/S.Ω^27 := by ring
    _ ≤ C*S.Δ*P.G^14*P.U^90/S.Ω^27 := by
        gcongr C*?_*P.G^14*P.U^90/S.Ω^27

/-- Collected flat cap piece: 10-factor ℓ-window, double `h1` collapse of `H²`, tail. -/
private theorem fitEB_capFlat (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5)) (C : ℝ) (hC0 : 0 ≤ C) :
    5280*10^40*C*S.Δ*P.G^4*P.U^35*(ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)^2))/(P.H^2*S.Ω^17)
      ≤ C*S.Δ*P.G^14*P.U^90/S.Ω^27 := by
  have hΩpos := S.Ω_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hd0 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hdW : ℓ₂ - ℓ₁ ≤ 130*(P.G*P.U^5) := by linarith
  have hH : P.G*P.U^10*S.Δ^2 ≤ P.H := (le_div_iff₀ (by positivity)).mp h1
  have hW : ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)^2) ≤ P.G^10*P.U^51 := by
    have h6 : ℓ₁^6 ≤ (130*(P.G*P.U^5))^6 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 6
    have h2a : ℓ₂^2 ≤ (130*(P.G*P.U^5))^2 := pow_le_pow_left₀ (by linarith) hℓ2W 2
    have h2b : (ℓ₂-ℓ₁)^2 ≤ (130*(P.G*P.U^5))^2 := pow_le_pow_left₀ hd0.le hdW 2
    have hUpos' := P.U_pos
    have hGpos' := P.G_pos
    calc ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)^2)
        ≤ (130*(P.G*P.U^5))^6*((130*(P.G*P.U^5))^2*(130*(P.G*P.U^5))^2) :=
          mul_le_mul h6 (mul_le_mul h2a h2b (sq_nonneg _) (by positivity))
            (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
      _ = 130^10*(P.G^10*P.U^50) := by ring
      _ ≤ P.U*(P.G^10*P.U^50) :=
          mul_le_mul_of_nonneg_right (le_trans (by norm_num) hUbig) (by positivity)
      _ = P.G^10*P.U^51 := by ring
  have hK : (5280*10^40:ℝ) ≤ P.U^3 := by
    calc (5280*10^40:ℝ) ≤ ((10:ℝ)^33)^3 := by norm_num
      _ ≤ P.U^3 := pow_le_pow_left₀ (by norm_num) hUbig 3
  calc 5280*10^40*C*S.Δ*P.G^4*P.U^35*(ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)^2))/(P.H^2*S.Ω^17)
      ≤ 5280*10^40*C*S.Δ*P.G^4*P.U^35*(P.G^10*P.U^51)/(P.H^2*S.Ω^17) := by
        gcongr 5280*10^40*C*S.Δ*P.G^4*P.U^35*?_/(P.H^2*S.Ω^17)
    _ ≤ 5280*10^40*C*S.Δ*P.G^4*P.U^35*(P.G^10*P.U^51)/((P.G*P.U^10*S.Δ^2)^2*S.Ω^17) := by
        gcongr 5280*10^40*C*S.Δ*P.G^4*P.U^35*(P.G^10*P.U^51)/(?_*S.Ω^17)
        exact pow_le_pow_left₀ (by positivity) hH 2
    _ = 5280*10^40*C*P.G^12*P.U^66/(S.Δ^3*S.Ω^17) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    _ ≤ 5280*10^40*C*P.G^12*P.U^66/(1*S.Ω^17) := by
        gcongr 5280*10^40*C*P.G^12*P.U^66/(?_*S.Ω^17)
        exact one_le_pow₀ hΔ1
    _ = 5280*10^40*C*P.G^12*P.U^66*S.Ω^10/S.Ω^27 := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    _ ≤ 5280*10^40*C*P.G^12*P.U^66*P.U^10/S.Ω^27 := by
        gcongr 5280*10^40*C*P.G^12*P.U^66*?_/S.Ω^27
        exact pow_le_pow_left₀ hΩpos.le hΩU 10
    _ = 5280*10^40*C*P.G^12*P.U^76/S.Ω^27 := by ring
    _ ≤ C*S.Δ*P.G^14*P.U^90/S.Ω^27 :=
        fitEB_tailB hG1 hU1 hΔ1 C (5280*10^40) hC0 hK 12 76 (by norm_num) (by norm_num)

/-- Collected degree-4 cap piece: 9-factor ℓ-window, one `h1` collapse, tail. -/
private theorem fitEB_capP4 (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5)) (C : ℝ) (hC0 : 0 ≤ C) :
    3388*10^81*C*P.G^5*P.U^45*(ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)))/(P.H*S.Ω^22)
      ≤ C*S.Δ*P.G^14*P.U^90/S.Ω^27 := by
  have hΩpos := S.Ω_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hd0 : (0:ℝ) < ℓ₂ - ℓ₁ := by linarith
  have hdW : ℓ₂ - ℓ₁ ≤ 130*(P.G*P.U^5) := by linarith
  have hH : P.G*P.U^10*S.Δ^2 ≤ P.H := (le_div_iff₀ (by positivity)).mp h1
  have hW : ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)) ≤ P.G^9*P.U^46 := by
    have h6 : ℓ₁^6 ≤ (130*(P.G*P.U^5))^6 := pow_le_pow_left₀ hℓ1pos.le hℓ1W 6
    have h2a : ℓ₂^2 ≤ (130*(P.G*P.U^5))^2 := pow_le_pow_left₀ (by linarith) hℓ2W 2
    have hUpos' := P.U_pos
    have hGpos' := P.G_pos
    calc ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁))
        ≤ (130*(P.G*P.U^5))^6*((130*(P.G*P.U^5))^2*(130*(P.G*P.U^5))) :=
          mul_le_mul h6 (mul_le_mul h2a hdW hd0.le (by positivity))
            (mul_nonneg (sq_nonneg _) hd0.le) (by positivity)
      _ = 130^9*(P.G^9*P.U^45) := by ring
      _ ≤ P.U*(P.G^9*P.U^45) :=
          mul_le_mul_of_nonneg_right (le_trans (by norm_num) hUbig) (by positivity)
      _ = P.G^9*P.U^46 := by ring
  have hWpos : (0:ℝ) ≤ ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)) :=
    mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hd0.le)
  have hHΩ : (0:ℝ) ≤ P.H*S.Ω^22 := mul_nonneg P.H_pos.le (by positivity)
  have hK : (3388*10^81:ℝ) ≤ P.U^3 := by
    calc (3388*10^81:ℝ) ≤ ((10:ℝ)^33)^3 := by norm_num
      _ ≤ P.U^3 := pow_le_pow_left₀ (by norm_num) hUbig 3
  calc 3388*10^81*C*P.G^5*P.U^45*(ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)))/(P.H*S.Ω^22)
      ≤ 3388*10^81*C*P.G^5*P.U^45*(P.G^9*P.U^46)/(P.H*S.Ω^22) := by
        gcongr 3388*10^81*C*P.G^5*P.U^45*?_/(P.H*S.Ω^22)
    _ ≤ 3388*10^81*C*P.G^5*P.U^45*(P.G^9*P.U^46)/((P.G*P.U^10*S.Δ^2)*S.Ω^22) := by
        gcongr 3388*10^81*C*P.G^5*P.U^45*(P.G^9*P.U^46)/(?_*S.Ω^22)
    _ = 3388*10^81*C*P.G^13*P.U^81/(S.Δ^2*S.Ω^22) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    _ ≤ 3388*10^81*C*P.G^13*P.U^81/(1*S.Ω^22) := by
        gcongr 3388*10^81*C*P.G^13*P.U^81/(?_*S.Ω^22)
        exact one_le_pow₀ hΔ1
    _ = 3388*10^81*C*P.G^13*P.U^81*S.Ω^5/S.Ω^27 := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    _ ≤ 3388*10^81*C*P.G^13*P.U^81*P.U^5/S.Ω^27 := by
        gcongr 3388*10^81*C*P.G^13*P.U^81*?_/S.Ω^27
        exact pow_le_pow_left₀ hΩpos.le hΩU 5
    _ = 3388*10^81*C*P.G^13*P.U^86/S.Ω^27 := by ring
    _ ≤ C*S.Δ*P.G^14*P.U^90/S.Ω^27 :=
        fitEB_tailB hG1 hU1 hΔ1 C (3388*10^81) hC0 hK 13 86 (by norm_num) (by norm_num)

/-- Capped, def-expanded cap-summand splits into the two collected pieces (flat + p₄;
the p₃ piece is re-slotted to the constant room), each fitting one target block. -/
private theorem fitEB_capCore (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5)) (C : ℝ) (hC0 : 0 ≤ C) :
    (4*(11*(S.Δ*S.Ω))*(2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
          *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
        + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ))))
        *(P.G^4*P.U^15/S.Ω^4)*(C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8)
      ≤ 2*(C*S.Δ*P.G^14*P.U^90/S.Ω^27) := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  have hGne : P.G ≠ 0 := ne_of_gt P.G_pos
  have hf := fitEB_capFlat h1 hG1 hU1 hΔ1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W C hC0
  have hp4 := fitEB_capP4 h1 hG1 hU1 hΔ1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W C hC0
  have hsplit : (4*(11*(S.Δ*S.Ω))*(2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
          *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
        + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ))))
        *(P.G^4*P.U^15/S.Ω^4)*(C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8)
      = 5280*10^40*C*S.Δ*P.G^4*P.U^35*(ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)^2))/(P.H^2*S.Ω^17)
        + 3388*10^81*C*P.G^5*P.U^45*(ℓ₁^6*(ℓ₂^2*(ℓ₂-ℓ₁)))/(P.H*S.Ω^22) := by
    field_simp
    ring
  rw [hsplit]
  linarith [hf, hp4]

/-- **Hybrid E-fit, cap block.** The `4a·Ecap4a`-summand of `cEhyb·dc·N` (with `√L` already
cancelled) fits twice the `t7'`-shaped target block (flat + p₄ pieces). -/
theorem step4_fitEB_cap
    (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5))
    (n C : ℝ) (hC : 1 ≤ C)
    (hncap : n ≤ C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8) (hn0 : 0 ≤ n)
    (a : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11*S.A) :
    (4*a*Ecap4a P S a ℓ₁ ℓ₂) * (P.G^4*P.U^15/S.Ω^4) * n
      ≤ 2 * (C * (P.H/S.Δ) * (S.Δ^2*P.G^14*P.U^90/(P.H*S.Ω^27))) := by
  have hΔne : S.Δ ≠ 0 := ne_of_gt S.Δ_pos
  have hΩne : S.Ω ≠ 0 := ne_of_gt S.Ω_pos
  have hHne : P.H ≠ 0 := ne_of_gt P.H_pos
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hd0' : (0:ℝ) ≤ ℓ₂ - ℓ₁ := by linarith
  have hℓ2nn : (0:ℝ) ≤ ℓ₂ := by linarith
  have hC0 : (0:ℝ) ≤ C := by linarith
  have ha0' : (0:ℝ) ≤ a := ha0.le
  have hHΔ : (0:ℝ) ≤ P.H*S.Δ := (mul_pos P.H_pos S.Δ_pos).le
  have hLnn : (0:ℝ) ≤ ℓ₁*ℓ₂*(ℓ₂-ℓ₁) :=
    mul_nonneg (mul_nonneg hℓ1pos.le hℓ2nn) hd0'
  have hncnn : (0:ℝ) ≤ C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 (by positivity)) hLnn)
      (by positivity)) (by positivity)
  have ha' : a ≤ 11*(S.Δ*S.Ω) := by
    rw [show S.A = S.Δ*S.Ω from rfl] at ha_hi; exact ha_hi
  have h2ℓ : 2*ℓ₂-ℓ₁ ≤ 2*ℓ₂ := by linarith
  have h3t : 2*(C*(P.H/S.Δ)*(S.Δ^2*P.G^14*P.U^90/(P.H*S.Ω^27)))
      = 2*(C*S.Δ*P.G^14*P.U^90/S.Ω^27) := by field_simp
  have hGpos := P.G_pos
  have hUpos := P.U_pos
  have hΩpos := S.Ω_pos
  have hΔpos := S.Δ_pos
  have hHpos := P.H_pos
  rw [Ecap4a_collapse (ne_of_gt ha0),
    show Vmax P S = 10^20*(S.Δ*P.U^5/S.Ω^3) from rfl,
    show S.D = P.H*S.Δ from rfl, h3t]
  have ht1 : (0:ℝ) ≤ 20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
      *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2 :=
    mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (by linarith) (by positivity))) (sq_nonneg _)
  have ht2i : (0:ℝ) ≤ 5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg hℓ1pos.le 3)) (by linarith)) (by positivity)
  have ht2i' : (0:ℝ) ≤ 5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg hℓ1pos.le 3)) (by linarith)) (by positivity)
  have hHΔpos : (0:ℝ) < P.H*S.Δ := mul_pos P.H_pos S.Δ_pos
  have hBr0 : (0:ℝ) ≤ 2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
        *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
      + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ)) :=
    mul_nonneg (by norm_num) (add_nonneg ht1
      (div_nonneg (mul_nonneg (by positivity) ht2i) hHΔ))
  have hBr'0 : (0:ℝ) ≤ 2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
        *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
      + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ)) :=
    mul_nonneg (by norm_num) (add_nonneg ht1
      (div_nonneg (mul_nonneg (by positivity) ht2i') hHΔ))
  have hp4mono : 5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4
      ≤ 5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2ℓ (by positivity)) (by positivity)
  have hdiv : 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ)
      ≤ 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ) :=
    (div_le_div_iff_of_pos_right hHΔpos).mpr
      (mul_le_mul_of_nonneg_left hp4mono (by positivity))
  have hBrle : 2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
        *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
      + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ))
      ≤ 2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
        *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
      + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ)) := by
    linarith [hdiv]
  have h4a : 4*a*(2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
        *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
      + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂-ℓ₁)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ)))
      ≤ 4*(11*(S.Δ*S.Ω))*(2*(20*(3*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))/(P.H*S.Δ)^2)
        *(ℓ₁*(10^20*(S.Δ*P.U^5/S.Ω^3)))^2
      + 77*(P.G*S.Ω/S.Δ^4)*(5/2*ℓ₁^3*(2*ℓ₂)*(10^20*(S.Δ*P.U^5/S.Ω^3))^4)/(P.H*S.Δ))) := by
    have hstep1 := mul_le_mul_of_nonneg_left hBrle (by linarith : (0:ℝ) ≤ 4*a)
    have hstep2 := mul_le_mul_of_nonneg_right
      (by linarith [ha'] : 4*a ≤ 4*(11*(S.Δ*S.Ω))) hBr'0
    linarith [hstep1, hstep2]
  have hY0 : (0:ℝ) ≤ P.G^4*P.U^15/S.Ω^4 := by positivity
  have hfac := mul_le_mul_of_nonneg_right h4a hY0
  exact le_trans (mul_le_mul hfac hncap hn0
      (mul_nonneg (mul_nonneg (by positivity) hBr'0) hY0))
    (fitEB_capCore h1 hG1 hU1 hΔ1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W C hC0)

/-- `√L`-cancellation: `(x/√L)·(y·√L)·z = x·y·z` for `L > 0`. -/
private theorem sqrt_cancel {L x y z : ℝ} (hL : 0 < L) :
    (x / Real.sqrt L) * (y * Real.sqrt L) * z = x * y * z := by
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  field_simp

/-- **Hybrid E-coefficient B-block fit.** `cEhyb·dc·N ≤ 8·C·(H/Δ)·(Δ²G¹⁵U⁹⁰/(HΩ²⁷))`:
the `√L` of `dc` cancels `cEhyb`'s `1/√L`, and the three summands fit `2+1+3 = 6 ≤ 8`
target blocks via `step4_fitEB_T1`/`_T2`/`_cap`. -/
theorem step4_fit_cE_B
    (h1 : P.G*P.U^10 ≤ P.H/S.Δ^2)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ)^33 ≤ P.U)
    (N : ℕ) (ℓ₁ ℓ₂ : ℝ) (hℓ1lo : 1 ≤ ℓ₁) (hℓ12 : ℓ₁+1 ≤ ℓ₂)
    (hℓ1W : ℓ₁ ≤ 130*(P.G*P.U^5)) (hℓ2W : ℓ₂ ≤ 130*(P.G*P.U^5))
    (C : ℝ) (hC : 1 ≤ C)
    (hNcap : (N:ℝ) ≤ C*ℓ₁^2*(ℓ₁*ℓ₂*(ℓ₂-ℓ₁))*P.U^10/S.Ω^8)
    (a gap : ℝ) (ha0 : 0 < a) (ha_hi : a ≤ 11*S.A) (hgap0 : 0 ≤ gap)
    (hgap : gap ≤ 2*10^12*S.Δ/(P.G*S.Ω^3*ℓ₁) + 10^13*ℓ₁*S.Δ^3/(P.H*P.G^2*S.Ω^6))
    (dc : ℝ) (hdc : dc = P.G^4*P.U^15/S.Ω^4 * Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁))) :
    cEhyb P S a ℓ₁ ℓ₂ gap * dc * (N:ℝ)
      ≤ 8 * C * (P.H/S.Δ) * (S.Δ^2*P.G^14*P.U^90/(P.H*S.Ω^27)) := by
  have hℓ1pos : (0:ℝ) < ℓ₁ := lt_of_lt_of_le one_pos hℓ1lo
  have hℓ2pos : (0:ℝ) < ℓ₂ := by linarith
  have hd : (0:ℝ) < ℓ₂-ℓ₁ := by linarith
  have hL : (0:ℝ) < ℓ₁*ℓ₂*(ℓ₂-ℓ₁) := mul_pos (mul_pos hℓ1pos hℓ2pos) hd
  have hn0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hT1 := step4_fitEB_T1 h1 hG1 hU1 hΔ1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W
    (N:ℝ) C hC hNcap hn0 a ha_hi gap hgap0 hgap
  have hT2 := step4_fitEB_T2 h1 hG1 hU1 hΔ1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W
    (N:ℝ) C hC hNcap hn0 a ha_hi
  have hcap := step4_fitEB_cap h1 hG1 hU1 hΔ1 hΩU hUbig ℓ₁ ℓ₂ hℓ1lo hℓ12 hℓ1W hℓ2W
    (N:ℝ) C hC hNcap hn0 a ha0 ha_hi
  have hblock : (0:ℝ) ≤ C*(P.H/S.Δ)*(S.Δ^2*P.G^14*P.U^90/(P.H*S.Ω^27)) :=
    mul_nonneg (mul_nonneg (by linarith) (div_nonneg P.H_pos.le S.Δ_pos.le))
      (div_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg P.G_pos.le 14))
          (pow_nonneg P.U_pos.le 90))
        (mul_nonneg P.H_pos.le (pow_nonneg S.Ω_pos.le 27)))
  rw [show cEhyb P S a ℓ₁ ℓ₂ gap
      = (10^10*a*P.G*S.Ω^3*gap/S.Δ^2 + 10^35*a*P.G*S.Ω^3*ℓ₂*S.B^2/(S.Δ^2*S.D)
          + 4*a*Ecap4a P S a ℓ₁ ℓ₂) / Real.sqrt (ℓ₁*ℓ₂*(ℓ₂-ℓ₁)) from rfl,
    hdc, sqrt_cancel hL,
    show (10^10*a*P.G*S.Ω^3*gap/S.Δ^2 + 10^35*a*P.G*S.Ω^3*ℓ₂*S.B^2/(S.Δ^2*S.D)
          + 4*a*Ecap4a P S a ℓ₁ ℓ₂) * (P.G^4*P.U^15/S.Ω^4) * (N:ℝ)
      = (10^10*a*P.G*S.Ω^3*gap/S.Δ^2) * (P.G^4*P.U^15/S.Ω^4) * (N:ℝ)
        + (10^35*a*P.G*S.Ω^3*ℓ₂*S.B^2/(S.Δ^2*S.D)) * (P.G^4*P.U^15/S.Ω^4) * (N:ℝ)
        + (4*a*Ecap4a P S a ℓ₁ ℓ₂) * (P.G^4*P.U^15/S.Ω^4) * (N:ℝ) from by ring,
    show (8:ℝ) * C * (P.H/S.Δ) * (S.Δ^2*P.G^14*P.U^90/(P.H*S.Ω^27))
      = 8 * (C * (P.H/S.Δ) * (S.Δ^2*P.G^14*P.U^90/(P.H*S.Ω^27))) from by ring]
  linarith [hT1, hT2, hcap, hblock]

end Squarefree
