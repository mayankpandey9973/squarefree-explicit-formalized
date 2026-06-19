import Squarefree.Lower.Step2FsumCurv
import Squarefree.Lower.DefectScales

/-!
# §5 Step-2 curvature `f`-sum scale-domination to the `Bcombine` monomials `t2, t3`

`step2_fsum_curv_le_t2t3` collapses the curvature `f`-sum bound
`(2N+1)·10²⁰⁰·(R·δ + R·√(δ/T_curv) + T_curv + 1 + N·κ)` (`δ = 4·δ₂₃`, `κ = D⁴/(X·A)`)
into the two Step-2 monomials `t2 = (H/Δ)·(Δ²/H)·G⁵U⁴⁵/Ω¹⁴`, `t3 = (H/Δ)·G⁵U³⁵/(Δ^{1/2}Ω⁸)`,
absolute constant `10⁴⁰⁰`.  The five product terms are dispatched by the abstract monomial lemmas
`mon_t1`..`mon_t5` (each compiled independently to keep the heartbeat cost local).
-/

namespace Squarefree

open Real

/-- `w⁶ ≤ u¹⁰` from `w ≤ u`, `1 ≤ u`. -/
private theorem w6_le_u10 {w u : ℝ} (hw0 : 0 < w) (hu1 : 1 ≤ u) (hwu : w ≤ u) : w ^ 6 ≤ u ^ 10 :=
  le_trans (pow_le_pow_left₀ hw0.le hwu 6) (pow_le_pow_right₀ hu1 (by norm_num))

/-- `2n+1 ≤ 3·(10⁹⁸·g²u¹⁵/w⁵)` from the `N`-cap and `n ≥ 1`. -/
private theorem cap3 {g u w n : ℝ}
    (hn1 : 1 ≤ n) (hncap : n ≤ 10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) :
    2 * n + 1 ≤ 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) := by linarith [hncap, hn1]

/-- term 1: `(2n+1)·(4g³du²⁰/w³) ≤ 12·10⁹⁸·(dg⁵u⁴⁵/w¹⁴)`. -/
private theorem mon_t1 {g u d w n : ℝ} (hg : 0 < g) (hu : 0 < u) (hd : 0 < d) (hw : 0 < w)
    (hu1 : 1 ≤ u) (hwu : w ≤ u) (hn1 : 1 ≤ n)
    (hncap : n ≤ 10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) :
    (2 * n + 1) * (4 * g ^ 3 * d * u ^ 20 / w ^ 3) ≤ 12 * 10 ^ 98 * (d * g ^ 5 * u ^ 45 / w ^ 14) := by
  have hbase : 0 ≤ 4 * g ^ 3 * d * u ^ 20 / w ^ 3 := by positivity
  have hstep : (2 * n + 1) * (4 * g ^ 3 * d * u ^ 20 / w ^ 3)
      ≤ 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) * (4 * g ^ 3 * d * u ^ 20 / w ^ 3) :=
    mul_le_mul_of_nonneg_right (cap3 hn1 hncap) hbase
  refine le_trans hstep ?_
  rw [show 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) * (4 * g ^ 3 * d * u ^ 20 / w ^ 3)
      = 12 * 10 ^ 98 * (g ^ 5 * d * u ^ 35 / w ^ 8) by field_simp; ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (w6_le_u10 hw hu1 hwu)
    (show (0:ℝ) ≤ g ^ 5 * d * u ^ 35 * w ^ 8 by positivity)]

/-- term 3: `(2n+1)·Tc ≤ 3·10¹⁰⁵·(dg⁵u⁴⁵/w¹⁴)`, with `Tc ≤ 10⁷·g·u¹⁵·d³/(w⁶·h)` (the ×130³
ℓ-cap traffic of the Wnat-route) and `d²gu¹⁰ ≤ h`. -/
private theorem mon_t3 {g u d w h Tc n : ℝ} (hg : 0 < g) (hu : 0 < u) (hd : 0 < d) (hw : 0 < w)
    (hh : 0 < h) (hg1 : 1 ≤ g) (hu1 : 1 ≤ u) (hwu : w ≤ u) (hn1 : 1 ≤ n)
    (hH : d ^ 2 * g * u ^ 10 ≤ h)
    (hncap : n ≤ 10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) (hTcnn : 0 ≤ Tc)
    (hTchi : Tc ≤ 10 ^ 7 * (g * u ^ 15 * d ^ 3 / (w ^ 6 * h))) :
    (2 * n + 1) * Tc ≤ 3 * 10 ^ 105 * (d * g ^ 5 * u ^ 45 / w ^ 14) := by
  have hstep : (2 * n + 1) * Tc
      ≤ 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5))
          * (10 ^ 7 * (g * u ^ 15 * d ^ 3 / (w ^ 6 * h))) := by
    calc (2 * n + 1) * Tc ≤ 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) * Tc :=
          mul_le_mul_of_nonneg_right (cap3 hn1 hncap) hTcnn
      _ ≤ 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5))
            * (10 ^ 7 * (g * u ^ 15 * d ^ 3 / (w ^ 6 * h))) :=
          mul_le_mul_of_nonneg_left hTchi (by positivity)
  refine le_trans hstep ?_
  rw [show 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5))
        * (10 ^ 7 * (g * u ^ 15 * d ^ 3 / (w ^ 6 * h)))
      = 3 * 10 ^ 105 * (g ^ 3 * u ^ 30 * d ^ 3 / (h * w ^ 11)) by field_simp]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : d ^ 2 * w ^ 3 ≤ g * u ^ 15 * h := by
    have hw3 : w ^ 3 ≤ g * u ^ 15 := by
      have ha : w ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hw.le hwu 3
      nlinarith [ha, pow_le_pow_right₀ hu1 (show 3 ≤ 15 by norm_num), hg1, pow_nonneg hu.le 15]
    have hgu10 : (1:ℝ) ≤ g * u ^ 10 := by
      nlinarith [hg1, one_le_pow₀ (n := 10) hu1, pow_nonneg hu.le 10]
    have hd2h : d ^ 2 ≤ h := by
      nlinarith [hH, mul_le_mul_of_nonneg_left hgu10 (show (0:ℝ) ≤ d ^ 2 by positivity)]
    have hc1 : d ^ 2 * w ^ 3 ≤ d ^ 2 * (g * u ^ 15) := mul_le_mul_of_nonneg_left hw3 (by positivity)
    have hc2 : d ^ 2 * (g * u ^ 15) ≤ h * (g * u ^ 15) := mul_le_mul_of_nonneg_right hd2h (by positivity)
    nlinarith [hc1, hc2]
  have hkey2 : d ^ 2 * w ^ 3 ≤ g ^ 2 * u ^ 15 * h := by
    nlinarith [hkey, mul_le_mul_of_nonneg_right hg1
      (show (0:ℝ) ≤ g * u ^ 15 * h by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hkey2 (show (0:ℝ) ≤ g ^ 3 * u ^ 30 * d * w ^ 11 by positivity)]

/-- term 5: `(2n+1)·(n·κ) ≤ 3·10¹⁹⁶·(dg⁵u⁴⁵/w¹⁴)`, with `κ = d³/(hgw)` and `d²gu¹⁰ ≤ h`. -/
private theorem mon_t5 {g u d w h n : ℝ} (hg : 0 < g) (hu : 0 < u) (hd : 0 < d) (hw : 0 < w)
    (hh : 0 < h) (hg1 : 1 ≤ g) (hu1 : 1 ≤ u) (hwu : w ≤ u) (hn1 : 1 ≤ n)
    (hH : d ^ 2 * g * u ^ 10 ≤ h)
    (hncap : n ≤ 10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) :
    (2 * n + 1) * (n * (d ^ 3 / (h * g * w))) ≤ 3 * 10 ^ 196 * (d * g ^ 5 * u ^ 45 / w ^ 14) := by
  have hκpos : 0 < d ^ 3 / (h * g * w) := by positivity
  have hnn : 0 ≤ n := by linarith
  have hNN : n * n ≤ (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) ^ 2 := by nlinarith [hncap, hnn]
  have hstep : (2 * n + 1) * (n * (d ^ 3 / (h * g * w)))
      ≤ 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) ^ 2 * (d ^ 3 / (h * g * w)) := by
    have h1 : (2 * n + 1) * (n * (d ^ 3 / (h * g * w))) ≤ 3 * (n * n) * (d ^ 3 / (h * g * w)) := by
      nlinarith [mul_le_mul_of_nonneg_right (show 2 * n + 1 ≤ 3 * n by linarith)
        (show 0 ≤ n * (d ^ 3 / (h * g * w)) by positivity), hκpos.le, hn1]
    refine le_trans h1 ?_
    apply mul_le_mul_of_nonneg_right _ hκpos.le
    apply mul_le_mul_of_nonneg_left hNN (by norm_num)
  refine le_trans hstep ?_
  rw [show 3 * (10 ^ 98 * (g ^ 2 * u ^ 15 / w ^ 5)) ^ 2 * (d ^ 3 / (h * g * w))
      = 3 * 10 ^ 196 * (g ^ 3 * u ^ 30 * d ^ 3 / (h * w ^ 11)) by field_simp]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : d ^ 2 * w ^ 3 ≤ g * u ^ 15 * h := by
    have hw3 : w ^ 3 ≤ g * u ^ 15 := by
      have ha : w ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hw.le hwu 3
      nlinarith [ha, pow_le_pow_right₀ hu1 (show 3 ≤ 15 by norm_num), hg1, pow_nonneg hu.le 15]
    have hgu10 : (1:ℝ) ≤ g * u ^ 10 := by
      nlinarith [hg1, one_le_pow₀ (n := 10) hu1, pow_nonneg hu.le 10]
    have hd2h : d ^ 2 ≤ h := by
      nlinarith [hH, mul_le_mul_of_nonneg_left hgu10 (show (0:ℝ) ≤ d ^ 2 by positivity)]
    have hc1 : d ^ 2 * w ^ 3 ≤ d ^ 2 * (g * u ^ 15) := mul_le_mul_of_nonneg_left hw3 (by positivity)
    have hc2 : d ^ 2 * (g * u ^ 15) ≤ h * (g * u ^ 15) := mul_le_mul_of_nonneg_right hd2h (by positivity)
    nlinarith [hc1, hc2]
  have hkey2 : d ^ 2 * w ^ 3 ≤ g ^ 2 * u ^ 15 * h := by
    nlinarith [hkey, mul_le_mul_of_nonneg_right hg1
      (show (0:ℝ) ≤ g * u ^ 15 * h by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hkey2 (show (0:ℝ) ≤ g ^ 3 * u ^ 30 * d * w ^ 11 by positivity)]

/-- term 2 (half-power): `(2n+1)·(2h·sg⁶·w³·u¹⁰/sd³) ≤ 6·10⁹⁸·(h·sg¹⁰·u³⁵/(sd³·w⁸))`. -/
private theorem mon_t2 {sg sd u w h n : ℝ} (hsg : 0 < sg) (hsd : 0 < sd) (hu : 0 < u) (hw : 0 < w)
    (hh : 0 < h) (hu1 : 1 ≤ u) (hwu : w ≤ u) (hn1 : 1 ≤ n)
    (hncap : n ≤ 10 ^ 98 * (sg ^ 4 * u ^ 15 / w ^ 5)) :
    (2 * n + 1) * (2 * h * sg ^ 6 * w ^ 3 * u ^ 10 / sd ^ 3)
      ≤ 6 * 10 ^ 98 * (h * sg ^ 10 * u ^ 35 / (sd ^ 3 * w ^ 8)) := by
  have hbase : 0 ≤ 2 * h * sg ^ 6 * w ^ 3 * u ^ 10 / sd ^ 3 := by positivity
  have hstep : (2 * n + 1) * (2 * h * sg ^ 6 * w ^ 3 * u ^ 10 / sd ^ 3)
      ≤ 3 * (10 ^ 98 * (sg ^ 4 * u ^ 15 / w ^ 5)) * (2 * h * sg ^ 6 * w ^ 3 * u ^ 10 / sd ^ 3) :=
    mul_le_mul_of_nonneg_right (by linarith [hncap, hn1]) hbase
  refine le_trans hstep ?_
  rw [show 3 * (10 ^ 98 * (sg ^ 4 * u ^ 15 / w ^ 5)) * (2 * h * sg ^ 6 * w ^ 3 * u ^ 10 / sd ^ 3)
      = 6 * 10 ^ 98 * (h * sg ^ 10 * u ^ 25 / (sd ^ 3 * w ^ 2)) by field_simp; ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (w6_le_u10 hw hu1 hwu)
    (show (0:ℝ) ≤ h * sg ^ 10 * u ^ 25 * (sd ^ 3 * w ^ 2) by positivity)]

/-- term 4 (half-power): `(2n+1) ≤ 3·10⁹⁸·(h·sg¹⁰·u³⁵/(sd³·w⁸))`, with `sd⁴sg²u¹⁰ ≤ h`. -/
private theorem mon_t4 {sg sd u w h n : ℝ} (hsg : 0 < sg) (hsd : 0 < sd) (hu : 0 < u) (hw : 0 < w)
    (hh : 0 < h) (hsg1 : 1 ≤ sg) (hsd1 : 1 ≤ sd) (hu1 : 1 ≤ u) (hwu : w ≤ u) (hn1 : 1 ≤ n)
    (hH : sd ^ 4 * sg ^ 2 * u ^ 10 ≤ h)
    (hncap : n ≤ 10 ^ 98 * (sg ^ 4 * u ^ 15 / w ^ 5)) :
    (2 * n + 1) * 1 ≤ 3 * 10 ^ 98 * (h * sg ^ 10 * u ^ 35 / (sd ^ 3 * w ^ 8)) := by
  have hstep : (2 * n + 1) * 1 ≤ 3 * 10 ^ 98 * (sg ^ 4 * u ^ 15 / w ^ 5) := by
    have hXnn : 0 ≤ sg ^ 4 * u ^ 15 / w ^ 5 := by positivity
    nlinarith [hncap, hn1, hXnn]
  refine le_trans hstep ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- sg⁴u¹⁵·(sd³w⁸) ≤ h sg¹⁰u³⁵·w⁵  ⟸  sd³w³ ≤ h sg⁶u²⁰
  have hkey : sd ^ 3 * w ^ 3 ≤ h * sg ^ 6 * u ^ 20 := by
    have hw3 : w ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hw.le hwu 3
    have hsd3 : sd ^ 3 ≤ sd ^ 4 := by nlinarith [pow_pos hsd 3, hsd1]
    have hsg2u10 : (1:ℝ) ≤ sg ^ 2 * u ^ 10 := by
      nlinarith [one_le_pow₀ (n := 2) hsg1, one_le_pow₀ (n := 10) hu1, pow_nonneg hu.le 10]
    have hsd4h : sd ^ 4 ≤ h := by
      nlinarith [hH, mul_le_mul_of_nonneg_left hsg2u10 (show (0:ℝ) ≤ sd ^ 4 by positivity)]
    have hc1 : sd ^ 3 * w ^ 3 ≤ sd ^ 4 * u ^ 3 := mul_le_mul hsd3 hw3 (by positivity) (by positivity)
    have hc2 : sd ^ 4 * u ^ 3 ≤ h * u ^ 3 := mul_le_mul_of_nonneg_right hsd4h (by positivity)
    have hsg6u17 : (1:ℝ) ≤ sg ^ 6 * u ^ 17 := by
      nlinarith [one_le_pow₀ (n := 6) hsg1, one_le_pow₀ (n := 17) hu1, pow_nonneg hu.le 17]
    have hc3 : h * u ^ 3 ≤ h * sg ^ 6 * u ^ 20 := by
      nlinarith [mul_le_mul_of_nonneg_left hsg6u17 (show (0:ℝ) ≤ h * u ^ 3 by positivity)]
    linarith [hc1, hc2, hc3]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0:ℝ) ≤ sg ^ 4 * u ^ 15 * w ^ 5 by positivity)]

/-- **§5 Step-2 curvature `f`-sum scale-domination.** -/
theorem step2_fsum_curv_le_t2t3 {P : Globals} {S : Scale P}
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2)
    (N : ℝ) (hN1 : 1 ≤ N) (hNcap : N ≤ 10 ^ 98 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5))
    (Tc : ℝ) (hTclo : S.B ^ 2 / S.D ≤ Tc)
    (hTchi : Tc ≤ 10 ^ 7 * ((P.G * P.U ^ 5) ^ 3 * (S.B ^ 2 / S.D))) :
    (2 * N + 1) * 10 ^ 200 * (S.R * (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6))
          + Real.sqrt (4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) / Tc))
        + Tc + 1 + N * (S.D ^ 4 / (P.X * S.A)))
      ≤ 10 ^ 400 * ((P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
          + (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))) := by
  have hGpos := P.G_pos; have hUpos := P.U_pos; have hHpos := P.H_pos
  have hΩpos := S.Ω_pos; have hΔpos := S.Δ_pos; have hXpos := P.X_pos
  have hDpos : (0:ℝ) < S.D := by unfold Scale.D; positivity
  have hApos : (0:ℝ) < S.A := by unfold Scale.A; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have hBpos : 0 < S.B := by unfold Scale.B; positivity
  -- √-variables
  set sG : ℝ := P.G ^ ((1:ℝ)/2) with hsG_def
  set sD : ℝ := S.Δ ^ ((1:ℝ)/2) with hsD_def
  have hsG0 : 0 < sG := Real.rpow_pos_of_pos hGpos _
  have hsD0 : 0 < sD := Real.rpow_pos_of_pos hΔpos _
  have hsG1 : 1 ≤ sG := Real.one_le_rpow hG1 (by norm_num)
  have hsD1 : 1 ≤ sD := Real.one_le_rpow hΔ1 (by norm_num)
  have hsG2 : sG ^ 2 = P.G := by
    rw [hsG_def, ← Real.rpow_natCast (P.G ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hGpos.le]; norm_num
  have hsD2 : sD ^ 2 = S.Δ := by
    rw [hsD_def, ← Real.rpow_natCast (S.Δ ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hΔpos.le]; norm_num
  have hG10 : P.G ^ 5 = sG ^ 10 := by rw [← hsG2]; ring
  have hΔ12 : S.Δ ^ ((1:ℝ)/2) = sD := hsD_def.symm
  have hHbig : S.Δ ^ 2 * P.G * P.U ^ 10 ≤ P.H := by
    have hΔ2 : (0:ℝ) < S.Δ ^ 2 := by positivity
    linarith only [(le_div_iff₀ hΔ2).mp h1]
  -- scale identities
  have hRval : S.R = P.H * P.G * S.Ω ^ 3 / S.Δ := by unfold Scale.R; field_simp
  have hκval : S.D ^ 4 / (P.X * S.A) = S.Δ ^ 3 / (P.H * P.G * S.Ω) := defect_D4_div_XA S
  have hBDval : S.B ^ 2 / S.D = S.Δ ^ 3 / (P.G ^ 2 * S.Ω ^ 6 * P.H) := by
    unfold Scale.B Scale.D; field_simp
  set δ' : ℝ := 4 * (S.Δ ^ 2 * P.G ^ 2 * P.U ^ 20 / (P.H * S.Ω ^ 6)) with hδ'_def
  have hδ'pos : 0 < δ' := by rw [hδ'_def]; positivity
  -- targets
  have hMG : (P.H / S.Δ) * ((S.Δ ^ 2 / P.H) * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14)
      = S.Δ * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14 := by field_simp
  have hMH : (P.H / S.Δ) * (P.G ^ 5 * P.U ^ 35 / (S.Δ ^ ((1:ℝ)/2) * S.Ω ^ 8))
      = P.H * sG ^ 10 * P.U ^ 35 / (sD ^ 3 * S.Ω ^ 8) := by
    rw [hG10, hΔ12, show S.Δ = sD ^ 2 from hsD2.symm]; field_simp
  rw [hMG, hMH]
  set MG : ℝ := S.Δ * P.G ^ 5 * P.U ^ 45 / S.Ω ^ 14 with hMG_def
  set MH : ℝ := P.H * sG ^ 10 * P.U ^ 35 / (sD ^ 3 * S.Ω ^ 8) with hMH_def
  have hMGnn : 0 ≤ MG := by rw [hMG_def]; positivity
  have hMHnn : 0 ≤ MH := by rw [hMH_def]; positivity
  -- ===== √ bound:  √(δ'/Tc) ≤ 2·sG³·U¹⁰/sD =====
  have hδ'DB2 : δ' / (S.B ^ 2 / S.D) = 4 * P.G ^ 4 * P.U ^ 20 / S.Δ := by
    rw [hδ'_def, hBDval]; field_simp
  have hsqrt_bound : Real.sqrt (δ' / Tc) ≤ 2 * sG ^ 4 * P.U ^ 10 / sD := by
    have hstep : δ' / Tc ≤ 4 * P.G ^ 4 * P.U ^ 20 / S.Δ := by
      rw [← hδ'DB2]; exact div_le_div_of_nonneg_left hδ'pos.le (by positivity) hTclo
    have hsG8 : sG ^ 8 = P.G ^ 4 := by rw [show sG ^ 8 = (sG ^ 2) ^ 4 by ring, hsG2]
    have hrhs : 4 * P.G ^ 4 * P.U ^ 20 / S.Δ = (2 * sG ^ 4 * P.U ^ 10 / sD) ^ 2 := by
      rw [show (2 * sG ^ 4 * P.U ^ 10 / sD) ^ 2 = 4 * sG ^ 8 * P.U ^ 20 / sD ^ 2 by ring,
        hsG8, hsD2]
    calc Real.sqrt (δ' / Tc) ≤ Real.sqrt (4 * P.G ^ 4 * P.U ^ 20 / S.Δ) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt ((2 * sG ^ 4 * P.U ^ 10 / sD) ^ 2) := by rw [hrhs]
      _ = 2 * sG ^ 4 * P.U ^ 10 / sD := Real.sqrt_sq (by positivity)
  -- replace inner by inner'
  have hRsqrt : S.R * (δ' + Real.sqrt (δ' / Tc)) + Tc + 1 + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω))
      ≤ S.R * δ' + S.R * (2 * sG ^ 4 * P.U ^ 10 / sD) + Tc + 1
        + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω)) := by
    have hsub : S.R * (δ' + Real.sqrt (δ' / Tc)) ≤ S.R * δ' + S.R * (2 * sG ^ 4 * P.U ^ 10 / sD) := by
      rw [mul_add]
      linarith [mul_le_mul_of_nonneg_left hsqrt_bound hRpos.le]
    linarith [hsub]
  -- ===== assemble via abstract monomial lemmas =====
  -- scale-form facts for the abstract lemmas
  have hRδ_eq : S.R * δ' = 4 * P.G ^ 3 * S.Δ * P.U ^ 20 / S.Ω ^ 3 := by
    rw [hRval, hδ'_def]; field_simp
  have hR2_eq : S.R * (2 * sG ^ 4 * P.U ^ 10 / sD)
      = 2 * P.H * sG ^ 6 * S.Ω ^ 3 * P.U ^ 10 / sD ^ 3 := by
    rw [hRval, show P.G = sG ^ 2 from hsG2.symm, show S.Δ = sD ^ 2 from hsD2.symm]; field_simp
  have hG2sG4 : P.G ^ 2 = sG ^ 4 := by rw [← hsG2]; ring
  have hncapG : N ≤ 10 ^ 98 * (sG ^ 4 * P.U ^ 15 / S.Ω ^ 5) := by rw [← hG2sG4]; exact hNcap
  have hHbigsd : sD ^ 4 * sG ^ 2 * P.U ^ 10 ≤ P.H := by
    rw [show sD ^ 4 = S.Δ ^ 2 by rw [← hsD2]; ring, hsG2]; exact hHbig
  have hTcnn : 0 ≤ Tc := le_trans (by positivity) hTclo
  have hTchi' : Tc ≤ 10 ^ 7 * (P.G * P.U ^ 15 * S.Δ ^ 3 / (S.Ω ^ 6 * P.H)) := by
    refine le_trans hTchi (le_of_eq ?_)
    rw [hBDval]; field_simp
  -- the five terms
  have ht1 := mon_t1 hGpos hUpos hΔpos hΩpos hU1 hΩU hN1 hNcap
  have ht2 := mon_t2 hsG0 hsD0 hUpos hΩpos hHpos hU1 hΩU hN1 hncapG
  have ht3 := mon_t3 hGpos hUpos hΔpos hΩpos hHpos hG1 hU1 hΩU hN1 hHbig hNcap hTcnn hTchi'
  have ht4 := mon_t4 hsG0 hsD0 hUpos hΩpos hHpos hsG1 hsD1 hU1 hΩU hN1 hHbigsd hncapG
  have ht5 := mon_t5 hGpos hUpos hΔpos hΩpos hHpos hG1 hU1 hΩU hN1 hHbig hNcap
  rw [← hMG_def] at ht1 ht3 ht5
  rw [← hMH_def] at ht2 ht4
  rw [hκval]
  -- inner' bound
  have hinner' : (2 * N + 1) * (S.R * δ' + S.R * (2 * sG ^ 4 * P.U ^ 10 / sD) + Tc + 1
        + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))
      ≤ 10 ^ 197 * MG + 10 ^ 99 * MH := by
    rw [hRδ_eq, hR2_eq]
    have hexp : (2 * N + 1) * (4 * P.G ^ 3 * S.Δ * P.U ^ 20 / S.Ω ^ 3
          + 2 * P.H * sG ^ 6 * S.Ω ^ 3 * P.U ^ 10 / sD ^ 3 + Tc + 1
          + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))
        = (2 * N + 1) * (4 * P.G ^ 3 * S.Δ * P.U ^ 20 / S.Ω ^ 3)
          + (2 * N + 1) * (2 * P.H * sG ^ 6 * S.Ω ^ 3 * P.U ^ 10 / sD ^ 3)
          + (2 * N + 1) * Tc + (2 * N + 1) * 1 + (2 * N + 1) * (N * (S.Δ ^ 3 / (P.H * P.G * S.Ω))) := by
      ring
    rw [hexp]
    linarith only [ht1, ht2, ht3, ht4, ht5, hMGnn, hMHnn]
  -- final chain
  have hkey : (2 * N + 1) * 10 ^ 200 * (S.R * (δ' + Real.sqrt (δ' / Tc)) + Tc + 1
        + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))
      ≤ 10 ^ 200 * (10 ^ 197 * MG + 10 ^ 99 * MH) := by
    have h2Nnn : 0 ≤ 2 * N + 1 := by positivity
    calc (2 * N + 1) * 10 ^ 200 * (S.R * (δ' + Real.sqrt (δ' / Tc)) + Tc + 1
          + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))
        ≤ (2 * N + 1) * 10 ^ 200 * (S.R * δ' + S.R * (2 * sG ^ 4 * P.U ^ 10 / sD) + Tc + 1
            + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith [hRsqrt]
      _ = 10 ^ 200 * ((2 * N + 1) * (S.R * δ' + S.R * (2 * sG ^ 4 * P.U ^ 10 / sD) + Tc + 1
            + N * (S.Δ ^ 3 / (P.H * P.G * S.Ω)))) := by ring
      _ ≤ 10 ^ 200 * (10 ^ 197 * MG + 10 ^ 99 * MH) := by
          apply mul_le_mul_of_nonneg_left hinner' (by norm_num)
  refine le_trans hkey ?_
  have p1 : (10:ℝ) ^ 397 ≤ 10 ^ 400 := by gcongr <;> norm_num
  have p2 : (10:ℝ) ^ 299 ≤ 10 ^ 400 := by gcongr <;> norm_num
  have q1 : (10:ℝ) ^ 200 * 10 ^ 197 = 10 ^ 397 := by rw [← pow_add]
  have q2 : (10:ℝ) ^ 200 * 10 ^ 99 = 10 ^ 299 := by rw [← pow_add]
  have e : (10:ℝ) ^ 200 * (10 ^ 197 * MG + 10 ^ 99 * MH) = 10 ^ 397 * MG + 10 ^ 299 * MH := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, q1, q2]
  rw [e]
  have hg : (10:ℝ) ^ 397 * MG ≤ 10 ^ 400 * MG := mul_le_mul_of_nonneg_right p1 hMGnn
  have hh : (10:ℝ) ^ 299 * MH ≤ 10 ^ 400 * MH := mul_le_mul_of_nonneg_right p2 hMHnn
  calc (10:ℝ) ^ 397 * MG + 10 ^ 299 * MH ≤ 10 ^ 400 * MG + 10 ^ 400 * MH := add_le_add hg hh
    _ = 10 ^ 400 * (MG + MH) := by rw [mul_add]

end Squarefree
