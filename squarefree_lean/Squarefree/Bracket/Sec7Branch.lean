import Squarefree.Bracket.Sec7CarryAux
import Squarefree.Counting.FourthDerivAux
import Squarefree.Bracket.Sec7Defs
import Squarefree.Bracket.Sec7DiffMVT
import Squarefree.Bracket.Sec7PhaseExp
import Squarefree.Bracket.Sec7ZeroScale

/-!
# §7 branch decomposition (plan nodes N3, N4, N6) — Phase-1b-α SIGNATURES ONLY

md 1307–1361 (`g_j` branches, the `#𝓡_a ≤ Σ_j Σ_r 1_{‖g_j‖≤δ₀}` reduction, TRAP-1)
and md 1516–1534 (eq 7.1: third-difference product rule with error `O(S·T₁/R²)`).
-/

open Classical Finset Squarefree.FiniteDiff

namespace Squarefree

/- N3 (md 1307–1326): "For each integer j with |j| ≪ 1 + H/A² … Since
     F_a(d_a^*(r)) ∈ ℤ + O(1/(HΔ²)),
   there exists such a j with  f_a^*(r) = ⌊f̃_a(r)⌋ + j."
   PHASE-1f: `FdStar` is the real value `F_a(d_a^*(r))` (call site: `Ffun P.X (a:ℝ) (d:ℝ)`
   at the `RaWitness` defect `d`, Structure/DaSpacing.lean).
   `hnear` PRODUCER (md 1317): `inDa_distInt_Ffun` (Structure/ADecompAux.lean:49,
   `distInt (Ffun X a d) ≤ 2H/d²`) with `fStar := round (Ffun X a d)` and the `RaWitness`
   window `S.D ≤ d`; since `D = HΔ`, `2H/D² = 2/(HΔ²)` is md 1317's scale with constant 2.
   `hprox` — the §6-side proximity `|F_a(d*(r)) − f̃_a(r)| ≪ H/A²` sizing the band —
   PRODUCER: `ftil_prox` (Bracket/Sec7Prox.lean:100, ruling D4 unit U3), which yields the
   EXACT shape `≤ 10¹⁸·(H/A²)` from the `RaWitness` window data; the `j`-band then needs
   `sec7_cJ ≥ 2·10¹⁸` (G1 ruling AM-5 bump, `sec7_cJ = 10²⁰`; ledger U4). -/
/-- **N3** (md 1307–1326): near-integrality of `F_a(d*)` places `f_a^*(r)` in a §7 branch:
`∃ j, |j| ≤ sec7_cJ·(1 + H/A²)` and `f_a^*(r) = ⌊f̃_a(r)⌋ + j`.  `FdStar` is the value
`F_a(d_a^*(r))`. -/
theorem sec7_branch_exists {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} (Ph : Sec7Phase P S W a)
    (FdStar : ℝ) (fStar : ℤ)
    -- A1 gate: `2H/D² ≤ c·(H/A²)` needs the A–D separation (the caller holds it anyway,
    -- as `ftil_prox`'s own `hAD` input)
    (hAD : 10 * S.A ≤ S.D) {r : ℝ} (hr : r ∈ sec7_rWin S W)
    (hnear : |(fStar : ℝ) - FdStar| ≤ 2 * P.H / S.D ^ 2)
    -- producer: `ftil_prox` (Bracket/Sec7Prox.lean:100) — its EXACT conclusion shape
    (hprox : |FdStar - Ph.ftil r| ≤ 10 ^ 18 * (P.H / S.A ^ 2)) :
    ∃ j : ℤ, sec7_jBand P S j ∧ fStar = ⌊Ph.ftil r⌋ + j := by
  have _ := hr
  refine ⟨fStar - ⌊Ph.ftil r⌋, ?_, by ring⟩
  have hH := P.H_pos
  have hΔ := S.Δ_pos
  have hΩ := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDpos : 0 < S.D := lt_of_lt_of_le (by positivity) hAD
  have hHA : 0 < P.H / S.A ^ 2 := by positivity
  -- fract part of f̃ is < 1
  have hfr : |Ph.ftil r - ⌊Ph.ftil r⌋| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.2 (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (Ph.ftil r)]
  -- A–D separation: 2H/D² ≤ H/A²
  have hD2 : 2 * P.H / S.D ^ 2 ≤ P.H / S.A ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul hAD hAD (by positivity : (0:ℝ) ≤ 10 * S.A) hDpos.le, hH]
  -- triangle inequality and the cJ headroom
  simp only [sec7_jBand, sec7_cJ]
  push_cast
  have htri : |(fStar : ℝ) - ⌊Ph.ftil r⌋| ≤
      |(fStar : ℝ) - FdStar| + |FdStar - Ph.ftil r| + |Ph.ftil r - ⌊Ph.ftil r⌋| := by
    have := abs_sub_le ((fStar : ℝ)) FdStar (⌊Ph.ftil r⌋ : ℝ)
    have := abs_sub_le FdStar (Ph.ftil r) (⌊Ph.ftil r⌋ : ℝ)
    linarith
  have h18 : (10:ℝ) ^ 18 * (P.H / S.A ^ 2) ≤ 10 ^ 20 * (P.H / S.A ^ 2) := by
    linarith only [hHA]
  linarith only [htri, hnear, hprox, hfr, hD2, h18, hHA]

/- N4 (md 1332–1361): "Using  d_a^*(r) = d̆_a(f_a^*(r)) + O(Δ²/(H²GA))  … we may Taylor
   expand d̆_a at f̃_a(r)+j:  d̆_a(f_a^*(r)) = d̆_a(f̃_a(r)+j) − d̆_a'(f̃_a(r)+j){f̃_a(r)}
   + O(sup_{t≍F}|d̆_a''(t)|).  Since sup|d̆_a''| ≍ HΔ/F² … we obtain
     #𝓡_a ≤ Σ_{|j|≪1+H/A²} Σ_{r≍R} 1_{‖g_j(r)‖≤δ₀},  δ₀ := (Δ⁵/H³)(Δ/A)² + Δ²/(H²GA)."
   TRAP-1 + G1 ruling AM-1: the md-1352 chain `HΔ/F² = (Δ⁵/H³)(Δ/A)²` is off by G²; the md
   needs NO G-largeness, so the Taylor step is carried as the G≥1-PROVABLE `≤` hypothesis
   `hTaylor : cPh·(HΔ/F²) ≤ cPh·(Δ⁵/(H³Ω²))` (chain `HΔ/F² = (Δ⁵/(H³Ω²))·G⁻² ≤ Δ⁵/(H³Ω²)`
   for G ≥ 1; sympy-banked, ledger U4) and the conclusion threshold is renormalized to
   `sec7_cTay·δ₀` (A1 gate: cTay = 10⁷ = max(cPh, cdMar); cdMar = 10⁷ since the `hd`
   producer route has floor `2·cPh`).
   Per-`r` data: `dStar r ∈ ℤ` is the §3 popular divisor (so `‖g_j(r)‖` is small),
   `fStar r` the N3 branch integer; `hd` is md 1325 with the named margin `sec7_cdMar`.
   AM-2: the count window is the WIDE `RaWitness` window `[⌈R/72⌉, ⌊16R⌋]` (md's dyadic
   pass to `[R,2R]` happens downstream, inside the triple split's 11-window dyadic sum). -/
/-- **N4** (md 1332–1361, TRAP-1 + AM-1/AM-2): the branch reduction
`#𝓡_a ≤ Σ_{j in the §7 band} #{r ∈ [R/72,16R] : ‖g_j(r)‖ ≤ sec7_cTay·δ₀}` with
`δ₀ = sec7_delta0` (md 1360 as displayed), the Taylor step as a G≥1-provable `≤`. -/
theorem sec7_branch_reduction {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} (Ph : Sec7Phase P S W a)
    (gfun : ℤ → ℝ → ℝ)
    (hg : ∀ (j : ℤ) (r : ℝ),
      gfun j r = Ph.dBreve (Ph.ftil r + j)
        - Ph.dBreve' (Ph.ftil r + j) * Int.fract (Ph.ftil r))
    (hTaylor : sec7_cPh * (P.H * S.Δ / S.F ^ 2) ≤
      sec7_cPh * (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)))
    (Ra : Finset ℤ) (dStar fStar : ℤ → ℤ)
    (hmem : ∀ r ∈ Ra, r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hwin : ∀ r ∈ Ra, (r : ℝ) ∈ sec7_rWin S W)
    (hd : ∀ r ∈ Ra,
      |(dStar r : ℝ) - Ph.dBreve (fStar r)| ≤
        sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A)))
    (hbranch : ∀ r ∈ Ra, ∃ j : ℤ, sec7_jBand P S j ∧ fStar r = ⌊Ph.ftil (r : ℝ)⌋ + j) :
    -- P1e composition fix (N23/N24): the sum runs over `⌊·⌋`, not `⌈·⌉`, so that EVERY
    -- summand index satisfies `sec7_jBand` (an integer `j` with `|j| ≤ z` has `|j| ≤ ⌊z⌋`,
    -- so N4's own proof is unaffected, while prop_7_1 applies to each summand).
    -- P1e elaboration fix: count binder pinned `r : ℤ` (md integer count; matches prop_7_1).
    (Ra.card : ℝ) ≤
      ∑ j ∈ Finset.Icc (-⌊sec7_cJ * (1 + P.H / S.A ^ 2)⌋) ⌊sec7_cJ * (1 + P.H / S.A ^ 2)⌋,
        (((Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
            (fun r : ℤ =>
              Counting.distInt (gfun j (r : ℝ)) ≤ sec7_cTay * sec7_delta0 P S)).card : ℝ) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hF : (0:ℝ) < S.F := by unfold Scale.F; positivity
  have hA : (0:ℝ) < S.A := by unfold Scale.A; positivity
  set z : ℝ := sec7_cJ * (1 + P.H / S.A ^ 2) with hz
  set T : ℤ → Finset ℤ := fun jj => (Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋).filter
    (fun r : ℤ =>
      Counting.distInt (gfun jj (r : ℝ)) ≤ sec7_cTay * sec7_delta0 P S) with hT
  -- per-`r` analytic core: on its N3 branch the defect is `cTay·δ₀`-near an integer
  have hsub : Ra ⊆ (Finset.Icc (-⌊z⌋) ⌊z⌋).biUnion T := by
    intro r hr
    obtain ⟨j, hjB, hjeq⟩ := hbranch r hr
    have hjB' : (|j| : ℝ) ≤ z := hjB
    have hjmem : j ∈ Finset.Icc (-⌊z⌋) ⌊z⌋ := by
      have habs : |j| ≤ ⌊z⌋ := Int.le_floor.mpr (by exact_mod_cast hjB')
      rw [abs_le] at habs
      exact Finset.mem_Icc.mpr habs
    refine Finset.mem_biUnion.mpr ⟨j, hjmem, ?_⟩
    rw [hT]
    refine Finset.mem_filter.mpr ⟨hmem r hr, ?_⟩
    -- Taylor expansion of `d̆` at `f̃(r)+j`, evaluated at `f̃(r)+j−{f̃(r)}` (md 1332–43)
    have hwr := hwin r hr
    set c : ℝ := Ph.ftil (r : ℝ) + j with hc
    set s : ℝ := Int.fract (Ph.ftil (r : ℝ)) with hs
    have hs0 : 0 ≤ s := Int.fract_nonneg _
    have hs1 : s ≤ 1 := (Int.fract_lt_one _).le
    have hcw : c ∈ sec7_tWin S := by
      have := Ph.shift_mem (r : ℝ) hwr j hjB 0 (by norm_num)
      simpa [hc] using this
    have hcsw : c - s ∈ sec7_tWin S := Ph.shift_mem (r : ℝ) hwr j hjB s ⟨hs0, hs1⟩
    -- `|d̆''| ≤ cPh·HΔ/F²` on the `t`-window
    have hd2 : ∀ t ∈ Set.Icc (S.F / sec7_cWin) (sec7_cWin * S.F),
        |Ph.dBreve'' t| ≤ sec7_cPh * (P.H * S.Δ / S.F ^ 2) := by
      intro t ht
      have h := Ph.F2d''_hi t ht
      rw [show sec7_cPh * (P.H * S.Δ / S.F ^ 2)
          = sec7_cPh * (P.H * S.Δ) / S.F ^ 2 by ring, le_div_iff₀ (by positivity)]
      calc |Ph.dBreve'' t| * S.F ^ 2 = S.F ^ 2 * |Ph.dBreve'' t| := by ring
        _ ≤ sec7_cPh * (P.H * S.Δ) := h
    have htay : |Ph.dBreve (c - s) - Ph.dBreve c + Ph.dBreve' c * s| ≤
        sec7_cPh * (P.H * S.Δ / S.F ^ 2) * s ^ 2 :=
      abs_taylor1_le (fun t ht => Ph.dBreve_hasDeriv t ht)
        (fun t ht => Ph.dBreve'_hasDeriv t ht) hd2 hs0 hcsw hcw
    -- `(fStar r : ℝ) = c − s` (the N3 branch equation)
    have hfs : ((fStar r : ℤ) : ℝ) = c - s := by
      have hfl : (⌊Ph.ftil (r : ℝ)⌋ : ℝ) = Ph.ftil (r : ℝ) - s := by
        rw [hs]; linarith [Int.self_sub_fract (Ph.ftil (r : ℝ))]
      rw [hjeq]; push_cast; rw [hfl, hc]; ring
    -- assemble: `distInt ≤ |g_j(r) − dStar|`, triangle, then the two budget pieces
    have hgr : gfun j (r : ℝ) = Ph.dBreve c - Ph.dBreve' c * s := by
      rw [hg j (r : ℝ), ← hc, ← hs]
    have hdd := hd r hr
    rw [hfs] at hdd
    have h1 : Counting.distInt (gfun j (r : ℝ)) ≤ |gfun j (r : ℝ) - (dStar r : ℝ)| := by
      simpa only [Counting.distInt] using round_le (gfun j (r : ℝ)) (dStar r)
    have h2 : |gfun j (r : ℝ) - (dStar r : ℝ)| ≤
        |Ph.dBreve (c - s) - Ph.dBreve c + Ph.dBreve' c * s|
          + |(dStar r : ℝ) - Ph.dBreve (c - s)| := by
      rw [hgr, show Ph.dBreve c - Ph.dBreve' c * s - (dStar r : ℝ)
        = -(Ph.dBreve (c - s) - Ph.dBreve c + Ph.dBreve' c * s)
          + -((dStar r : ℝ) - Ph.dBreve (c - s)) by ring]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg, abs_neg]
    have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hs0, hs1]
    have h3 : sec7_cPh * (P.H * S.Δ / S.F ^ 2) * s ^ 2 ≤
        sec7_cPh * (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)) := by
      refine le_trans ?_ hTaylor
      have hpos : 0 ≤ sec7_cPh * (P.H * S.Δ / S.F ^ 2) := by
        have := sec7_cPh_pos; positivity
      nlinarith only [hpos, hs2]
    -- numeric close: `cPh·X + cdMar·Y ≤ cTay·(X + Y)` with `δ₀ = X + Y`
    have hX0 : (0:ℝ) ≤ S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2) := by positivity
    have hY0 : (0:ℝ) ≤ S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A) := by positivity
    rw [sec7_delta0_eq]
    have hc1 : sec7_cPh ≤ sec7_cTay := by norm_num [sec7_cPh, sec7_cTay]
    have hc2 : sec7_cdMar ≤ sec7_cTay := by norm_num [sec7_cdMar, sec7_cTay]
    have hc3 : (0:ℝ) < sec7_cTay := sec7_cTay_pos
    calc Counting.distInt (gfun j (r : ℝ))
        ≤ |Ph.dBreve (c - s) - Ph.dBreve c + Ph.dBreve' c * s|
            + |(dStar r : ℝ) - Ph.dBreve (c - s)| := le_trans h1 h2
      _ ≤ sec7_cPh * (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2))
            + sec7_cdMar * (S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A)) :=
          add_le_add (le_trans htay h3) hdd
      _ ≤ sec7_cTay * (S.Δ ^ 5 / (P.H ^ 3 * S.Ω ^ 2)
            + S.Δ ^ 2 / (P.H ^ 2 * P.G * S.A)) := by nlinarith only [hc1, hc2, hX0, hY0]
  -- count: `Ra ⊆ ⋃_j T j` and `card ⋃ ≤ Σ card`
  calc (Ra.card : ℝ)
      ≤ (((Finset.Icc (-⌊z⌋) ⌊z⌋).biUnion T).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ j ∈ Finset.Icc (-⌊z⌋) ⌊z⌋, (T j).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.Icc (-⌊z⌋) ⌊z⌋, ((T j).card : ℝ) := by push_cast; rfl

/- N6 (md 1516–1534, eq 7.1): "The product rule for the third difference gives
     Δ_{h₁,h₂,h₃}(f₁{f₂})(r) = f₁(r+h_Σ)·Δ_{h₁,h₂,h₃}{f₂}(r)
       + Σ_{i=1}³ Δ_{h_i}f₁(r+h_Σ−h_i)·Δ_{h_j,h_k}{f₂}(r+ξ_i) + O(ST₁/R²),
   where h_Σ = h₁+h₂+h₃, {i,j,k} = {1,2,3}, and the shifts ξ_i are bounded by h_Σ.  The
   error term contains all terms with at least two differences falling on f₁; its size
   follows from f₁^{(m)}(r) ≪ T₁/Rᵐ."
   Stated for Δ³g_j (g_j = f₃ + f₁·{f₂}, so the exact Δ³f₃ rides along), main term phrased
   exactly as the fract-level analogue of `sec7_Phi` (Sec7PhaseExp): `diff3`/`diff1∘diff1`
   on `Int.fract ∘ f2D 0`, with the same `ξ_i`-to-`(j,k)` pairing.  `S` is the symmetric
   form `sec7_Ssym = h₁h₂+h₁h₃+h₂h₃` (md 1491).  UNCERTAINTY: the ξ_i here are produced
   (existential, `|ξ_i| ≤ h_Σ`), matching how the `Sec7MonExp` bundle consumes them.
   A1 gate (two fixes): (i) the quantifier is the WIDE window `[R/72, 16R]` (all N8
   consumes) with the shift margin `hmargin : W + W² + W⁴ ≤ R/100` (md's "shifts ≪ R",
   dischargeable from the strip pack at the prop_7_1 call site) — quantifying over all of
   `rWin` put the `h`-shifted MVT points outside the `f1D` windows at the top edge;
   (ii) the error constant is `sec7_cN6 = 10²·cPh` (the ≥4 Leibniz `|T|≥2` terms plus ~3
   realignment second-differences total ≲ 40·cPh; sympy-banked, ledger U4). -/
/-- **N6 = eq (7.1)** (md 1516–1534; A1 gate): third-difference product rule for
`g_j = f₃ + f₁·{f₂}`: there are shifts `|ξ_i| ≤ h_Σ` with
`|Δ_{h₁,h₂,h₃}g_j(r) − main| ≤ sec7_cN6·S·T₁/R²` on `[R/72, 16R]`, `main` in the
`sec7_Phi`-compatible fract form. -/
theorem sec7_third_diff_product_rule {P : Globals} {S : Scale P} {a : ℤ}
    {W : ℝ} (Ph : Sec7Phase P S W a) (Env : Sec7Envelope P S W)
    {j : ℤ} (hj : sec7_jBand P S j) {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃)
    (hmargin : W + W ^ 2 + W ^ 4 ≤ S.R / 100)
    {M : ℝ} (hM : W + W ^ 2 + W ^ 4 ≤ M)
    (hwin : ∀ y : ℝ, S.R / 72 - M ≤ y → y ≤ 16 * S.R + M → y ∈ sec7_rWin S W)
    (gfun : ℤ → ℝ → ℝ)
    (hg : ∀ (j : ℤ) (r : ℝ),
      gfun j r = Ph.dBreve (Ph.ftil r + j)
        - Ph.dBreve' (Ph.ftil r + j) * Int.fract (Ph.ftil r)) :
    ∃ ξ₁ ξ₂ ξ₃ : ℝ, |ξ₁| ≤ sec7_hSum h₁ h₂ h₃ ∧ |ξ₂| ≤ sec7_hSum h₁ h₂ h₃ ∧
      |ξ₃| ≤ sec7_hSum h₁ h₂ h₃ ∧
      ∀ r ∈ Set.Icc (S.R / 72) (16 * S.R),
        |diff3 (h₁ : ℝ) h₂ h₃ (gfun j) r -
            (diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) r
              + Ph.f1D j 0 (r + sec7_hSum h₁ h₂ h₃) *
                  diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) r
              + diff1 (h₁ : ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₁) *
                  diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) (r + ξ₁)
              + diff1 (h₂ : ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₂) *
                  diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) (r + ξ₂)
              + diff1 (h₃ : ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₃) *
                  diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) (r + ξ₃))| ≤
          sec7_cN6 * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) := by
  have _ := Env
  -- real-valued shift-box facts
  have e1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hbox.1.1
  have e2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hbox.2.1.1
  have e3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hbox.2.2.1
  have u1 : (h₁:ℝ) ≤ W := hbox.1.2
  have u2 : (h₂:ℝ) ≤ W ^ 2 := hbox.2.1.2
  have u3 : (h₃:ℝ) ≤ W ^ 4 := hbox.2.2.2
  have hW1 : (1:ℝ) ≤ W := e1.trans u1
  have hW2 : (0:ℝ) ≤ W ^ 2 := sq_nonneg W
  have hW4 : (0:ℝ) ≤ W ^ 4 := by positivity
  have hSum0 : (0:ℝ) ≤ sec7_hSum h₁ h₂ h₃ := by simp only [sec7_hSum]; linarith
  -- the Leibniz shifts are exact: take ξ₁ = ξ₂ = ξ₃ = 0
  refine ⟨0, 0, 0, by simpa using hSum0, by simpa using hSum0, by simpa using hSum0, ?_⟩
  intro r hr
  obtain ⟨hr1, hr2⟩ := hr
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hR : (0:ℝ) < S.R := by unfold Scale.R; positivity
  have hT1 : (0:ℝ) < S.T₁ := by unfold Scale.T₁ Scale.F; positivity
  -- all `h`-shifted points stay in the `r ≍ R` window (`hmargin`)
  have hWin : ∀ y : ℝ, S.R / 72 ≤ y → y ≤ 16 * S.R + (W + W ^ 2 + W ^ 4) →
      y ∈ sec7_rWin S W := by
    intro y hy1 hy2
    exact hwin y (by linarith) (by linarith)
  have m0 : r ∈ sec7_rWin S W := hWin r (by linarith) (by linarith)
  have mA : r + (h₃:ℝ) ∈ sec7_rWin S W := hWin _ (by linarith) (by linarith)
  have mA' : r + (h₃:ℝ) + h₁ + h₂ ∈ sec7_rWin S W := hWin _ (by linarith) (by linarith)
  have mB : r + (h₂:ℝ) ∈ sec7_rWin S W := hWin _ (by linarith) (by linarith)
  have mB' : r + (h₂:ℝ) + h₁ + h₃ ∈ sec7_rWin S W := hWin _ (by linarith) (by linarith)
  have mC : r + (h₁:ℝ) ∈ sec7_rWin S W := hWin _ (by linarith) (by linarith)
  have mC' : r + (h₁:ℝ) + h₂ + h₃ ∈ sec7_rWin S W := hWin _ (by linarith) (by linarith)
  -- derivative and `f₁^{(m)} ≪ T₁/Rᵐ` packs on the window
  have hd0 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f1D j 0) (Ph.f1D j 1 t) t :=
    fun t ht => Ph.f1D_hasDeriv j hj 0 (by norm_num) t ht
  have hd1 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f1D j 1) (Ph.f1D j 2 t) t :=
    fun t ht => Ph.f1D_hasDeriv j hj 1 (by norm_num) t ht
  have hd2 : ∀ t ∈ sec7_rWin S W, HasDerivAt (Ph.f1D j 2) (Ph.f1D j 3 t) t :=
    fun t ht => Ph.f1D_hasDeriv j hj 2 (by norm_num) t ht
  have hb2 : ∀ t ∈ sec7_rWin S W, |Ph.f1D j 2 t| ≤ sec7_cPh * (S.T₁ / S.R ^ 2) :=
    fun t ht => Ph.f1D_hi j hj 2 (by norm_num) t ht
  have hb3 : ∀ t ∈ sec7_rWin S W, |Ph.f1D j 3 t| ≤ sec7_cPh * (S.T₁ / S.R ^ 3) :=
    fun t ht => Ph.f1D_hi j hj 3 (by norm_num) t ht
  -- MVT bounds on the f₁-factors of the `|T| ≥ 2` Leibniz terms
  have hA : |diff1 (h₁:ℝ) (diff1 (h₂:ℝ) (Ph.f1D j 0)) (r + (h₃:ℝ))| ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₂:ℝ) * (h₁:ℝ) :=
    abs_diff2_le hd0 hd1 hb2 (by linarith) (by linarith) mA mA'
  have hB : |diff1 (h₁:ℝ) (diff1 (h₃:ℝ) (Ph.f1D j 0)) (r + (h₂:ℝ))| ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₃:ℝ) * (h₁:ℝ) :=
    abs_diff2_le hd0 hd1 hb2 (by linarith) (by linarith) mB mB'
  have hCC : |diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (Ph.f1D j 0)) (r + (h₁:ℝ))| ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₃:ℝ) * (h₂:ℝ) :=
    abs_diff2_le hd0 hd1 hb2 (by linarith) (by linarith) mC mC'
  have hD : |diff3 (h₁:ℝ) h₂ h₃ (Ph.f1D j 0) r| ≤
      sec7_cPh * (S.T₁ / S.R ^ 3) * (h₃:ℝ) * (h₂:ℝ) * (h₁:ℝ) :=
    abs_diff3_le hd0 hd1 hd2 hb3 (by linarith) (by linarith) (by linarith) m0 mC'
  -- fract factors are bounded by 1
  have hv0 : |Int.fract (Ph.f2D 0 r)| ≤ 1 := abs_fract_le _
  have hv1 : |diff1 (h₁:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r| ≤ 1 :=
    abs_diff1_fract_le _ _ _
  have hv2 : |diff1 (h₂:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r| ≤ 1 :=
    abs_diff1_fract_le _ _ _
  have hv3 : |diff1 (h₃:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r| ≤ 1 :=
    abs_diff1_fract_le _ _ _
  -- `g_j = f₃ + f₁·{f₂}` pointwise
  have hgsplit : ∀ t : ℝ, gfun j t =
      Ph.f3D j 0 t + Ph.f1D j 0 t * Int.fract (Ph.f2D 0 t) := by
    intro t
    rw [hg j t, Ph.f3D_zero, Ph.f1D_zero, Ph.f2D_zero]
    ring
  -- exact discrete Leibniz identity: deviation from the main term = the four `|T| ≥ 2` terms
  have hkey : diff3 (h₁:ℝ) h₂ h₃ (gfun j) r -
      (diff3 (h₁:ℝ) h₂ h₃ (Ph.f3D j 0) r
        + Ph.f1D j 0 (r + sec7_hSum h₁ h₂ h₃) *
            diff3 (h₁:ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) r
        + diff1 (h₁:ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₁) *
            diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (fun t => Int.fract (Ph.f2D 0 t))) (r + 0)
        + diff1 (h₂:ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₂) *
            diff1 (h₁:ℝ) (diff1 (h₃:ℝ) (fun t => Int.fract (Ph.f2D 0 t))) (r + 0)
        + diff1 (h₃:ℝ) (Ph.f1D j 0) (r + sec7_hSum h₁ h₂ h₃ - h₃) *
            diff1 (h₁:ℝ) (diff1 (h₂:ℝ) (fun t => Int.fract (Ph.f2D 0 t))) (r + 0)) =
      diff1 (h₁:ℝ) (diff1 (h₂:ℝ) (Ph.f1D j 0)) (r + (h₃:ℝ)) *
          diff1 (h₃:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r
        + diff1 (h₁:ℝ) (diff1 (h₃:ℝ) (Ph.f1D j 0)) (r + (h₂:ℝ)) *
            diff1 (h₂:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r
        + diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (Ph.f1D j 0)) (r + (h₁:ℝ)) *
            diff1 (h₁:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r
        + diff3 (h₁:ℝ) h₂ h₃ (Ph.f1D j 0) r * Int.fract (Ph.f2D 0 r) := by
    simp only [hgsplit, diff3, diff1, sec7_hSum]
    ring_nf
  rw [hkey]
  -- triangle inequality over the four error terms
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) ?_
  have hbA : |diff1 (h₁:ℝ) (diff1 (h₂:ℝ) (Ph.f1D j 0)) (r + (h₃:ℝ)) *
      diff1 (h₃:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r| ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₂:ℝ) * (h₁:ℝ) := by
    rw [abs_mul]
    simpa using mul_le_mul hA hv3 (abs_nonneg _) ((abs_nonneg _).trans hA)
  have hbB : |diff1 (h₁:ℝ) (diff1 (h₃:ℝ) (Ph.f1D j 0)) (r + (h₂:ℝ)) *
      diff1 (h₂:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r| ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₃:ℝ) * (h₁:ℝ) := by
    rw [abs_mul]
    simpa using mul_le_mul hB hv2 (abs_nonneg _) ((abs_nonneg _).trans hB)
  have hbC : |diff1 (h₂:ℝ) (diff1 (h₃:ℝ) (Ph.f1D j 0)) (r + (h₁:ℝ)) *
      diff1 (h₁:ℝ) (fun t => Int.fract (Ph.f2D 0 t)) r| ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₃:ℝ) * (h₂:ℝ) := by
    rw [abs_mul]
    simpa using mul_le_mul hCC hv1 (abs_nonneg _) ((abs_nonneg _).trans hCC)
  have hbD : |diff3 (h₁:ℝ) h₂ h₃ (Ph.f1D j 0) r * Int.fract (Ph.f2D 0 r)| ≤
      sec7_cPh * (S.T₁ / S.R ^ 3) * (h₃:ℝ) * (h₂:ℝ) * (h₁:ℝ) := by
    rw [abs_mul]
    simpa using mul_le_mul hD hv0 (abs_nonneg _) ((abs_nonneg _).trans hD)
  -- the `|T| = 3` term costs one extra `h₃/R ≤ 1` (md: "≪ R"); fold it into a pair budget
  have hh3R : (h₃:ℝ) ≤ S.R := by linarith
  have h10 : (0:ℝ) ≤ (h₁:ℝ) := le_trans zero_le_one e1
  have h20 : (0:ℝ) ≤ (h₂:ℝ) := le_trans zero_le_one e2
  have h30 : (0:ℝ) ≤ (h₃:ℝ) := le_trans zero_le_one e3
  have h21 : (0:ℝ) ≤ (h₂:ℝ) * (h₁:ℝ) := mul_nonneg h20 h10
  have eD : sec7_cPh * (S.T₁ / S.R ^ 3) * (h₃:ℝ) * (h₂:ℝ) * (h₁:ℝ) ≤
      sec7_cPh * (S.T₁ / S.R ^ 2) * (h₂:ℝ) * (h₁:ℝ) := by
    have h1 : S.T₁ / S.R ^ 3 * (h₃:ℝ) ≤ S.T₁ / S.R ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hR 3) (pow_pos hR 2)]
      calc S.T₁ * (h₃:ℝ) * S.R ^ 2 = S.T₁ * S.R ^ 2 * (h₃:ℝ) := by ring
        _ ≤ S.T₁ * S.R ^ 2 * S.R :=
            mul_le_mul_of_nonneg_left hh3R
              (mul_nonneg hT1.le (pow_nonneg hR.le 2))
        _ = S.T₁ * S.R ^ 3 := by ring
    calc sec7_cPh * (S.T₁ / S.R ^ 3) * (h₃:ℝ) * (h₂:ℝ) * (h₁:ℝ)
        = sec7_cPh * (S.T₁ / S.R ^ 3 * (h₃:ℝ)) * ((h₂:ℝ) * (h₁:ℝ)) := by ring
      _ ≤ sec7_cPh * (S.T₁ / S.R ^ 2) * ((h₂:ℝ) * (h₁:ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (le_of_lt sec7_cPh_pos)) h21
      _ = sec7_cPh * (S.T₁ / S.R ^ 2) * (h₂:ℝ) * (h₁:ℝ) := by ring
  refine le_trans (add_le_add (add_le_add (add_le_add hbA hbB) hbC) (hbD.trans eD)) ?_
  -- constants: 3 pair terms + 1 folded term ≤ 2·cPh·S·T₁/R² ≤ cN6·S·T₁/R² (cN6 = 10²·cPh)
  have hQ : (0:ℝ) ≤ S.T₁ / S.R ^ 2 := div_nonneg hT1.le (pow_nonneg hR.le 2)
  have q12 : (0:ℝ) ≤ (h₁:ℝ) * (h₂:ℝ) * (S.T₁ / S.R ^ 2) :=
    mul_nonneg (mul_nonneg h10 h20) hQ
  have q13 : (0:ℝ) ≤ (h₁:ℝ) * (h₃:ℝ) * (S.T₁ / S.R ^ 2) :=
    mul_nonneg (mul_nonneg h10 h30) hQ
  have q23 : (0:ℝ) ≤ (h₂:ℝ) * (h₃:ℝ) * (S.T₁ / S.R ^ 2) :=
    mul_nonneg (mul_nonneg h20 h30) hQ
  simp only [sec7_Ssym, sec7_cPh, sec7_cN6]
  ring_nf at q12 q13 q23 ⊢
  linarith [q12, q13, q23]

/- N7 (md 1545–1570): "After fixing one of the finitely many floor-carry branches, there are
   fixed integers ρ₀,ρ₁,ρ₂,ρ₃ = O(1) such that  Δ_{h₁,h₂,h₃}{f₂}(r) = B₀₃(r) + ρ₀  and,
   after also fixing u_i = ⌊B_i(r)⌋,  Δ_{h_j,h_k}{f₂}(r+ξ_i) = B_i(r) − u_i + ρ_i.
   The triple u = (u₁,u₂,u₃) takes only  O(1 + ST₂/R²) = O(1 + S/(GΩ⁵))  (7.2)  values,
   because  B_i(r) = h_jh_k f₂''(r) + O(PT₂/R³),  f₂''(r) ≍ T₂/R² = G⁻¹Ω⁻⁵.
   The carry/fiber cover supplied by the floor-branching lemma represents each fixed branch
   and fixed u by O(1) intervals in r on which the integer data are fixed. … this O(1)
   interval count is absorbed in the factor (7.2)."
   One cover statement: pieces = (ρ, u, [p,q]); the TOTAL piece count (branches O(1) ×
   fibers (7.2) × O(1) intervals, all absorbed) is ≤ sec7_cPh·(1 + S/(GΩ⁵)) — exactly the
   harvest factor (N15/N22); per-piece carry/fiber sizes match `Sec7ZeroHyp.hρᵢ/huᵢ`
   verbatim (`sec7_cCarry`, `sec7_cPh·(1 + h_jh_k·T₂/R²)`; ledger constants in
   Sec7PhaseExp; T₂/R² = 1/(GΩ⁵) is `sec7_T₂_div_R_sq`); the on-piece fixed integer data
   are the branch identities in the fract form N8 consumes.  UNCERTAINTY: the prompt name
   `sec7_cRho` does not exist; the in-tree ledger constant is `sec7_cCarry` — reused. -/
/-- **N7 = the carry/fiber cover + (7.2)** (md 1545–1570; AM-2 wide window; ARB-1, A6:
the carry-tuple multiplicity `sec7_cMult` multiplies the COUNT — `ρ₀` ranges over ≤9 and
each `ρᵢ` over ≤7 values): a cover of the count range `[⌈R/72⌉,⌊16R⌋]` by at most
`sec7_cMult·sec7_cPh·(1 + S/(GΩ⁵))` pieces `(ρ₀,ρ₁,ρ₂,ρ₃, u₁,u₂,u₃, p, q)`,
each with carries `|ρᵢ| ≤ sec7_cCarry`, fiber sizes `|uᵢ − ρᵢ| ≤ sec7_cPh·(1 + h_jh_k·T₂/R²)`,
interval `[p,q] ⊆ [R/72,16R]`, and the fixed-integer-data branch identities on the piece. -/
theorem sec7_carry_fiber_cover {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} (Ph : Sec7Phase P S W a)
    (Env : Sec7Envelope P S W) {j : ℤ} (_hj : sec7_jBand P S j)
    {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) {ξ₁ ξ₂ ξ₃ : ℝ}
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    {M : ℝ} (hM : 2 * (W + W ^ 2 + W ^ 4) ≤ M)
    (hwin : ∀ y : ℝ, S.R / 72 - M ≤ y → y ≤ 16 * S.R + M → y ∈ sec7_rWin S W) :
    ∃ Λ : Finset ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ)),
      (Λ.card : ℝ) ≤ sec7_cMult * sec7_cPh * (1 + sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)) ∧
      (∀ pc ∈ Λ,
        (|(pc.1.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.1 : ℝ)| ≤ sec7_cCarry ∧
          |(pc.1.2.2.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.2.2 : ℝ)| ≤ sec7_cCarry) ∧
        (|(pc.2.1.1 : ℝ) - pc.1.2.1| ≤ sec7_cPh * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.1 : ℝ) - pc.1.2.2.1| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.2 : ℝ) - pc.1.2.2.2| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) ∧
        Set.Icc pc.2.2.1 pc.2.2.2 ⊆ Set.Icc (S.R / 72) (16 * S.R)) ∧
      (∀ r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋, ∃ pc ∈ Λ,
        (r : ℝ) ∈ Set.Icc pc.2.2.1 pc.2.2.2 ∧
        diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + pc.1.1 ∧
        diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
          diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
            - pc.2.1.1 + pc.1.2.1 ∧
        diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
          diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
            - pc.2.1.2.1 + pc.1.2.2.1 ∧
        diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
          diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
            - pc.2.1.2.2 + pc.1.2.2.2) :=
  (sec7_carry_fiber_cover_core Ph Env hbox hξ₁ hξ₂ hξ₃ hM hwin).1

/-- Sharp zero-top-carry subcover of N7.  This is the same carry/fiber cover restricted to
the branch `ρ₀ = 0`; the top-carry factor `11` in the aggregate cover is replaced by the
single top-carry value, giving the sharp `7^3 = 343` multiplicity. -/
theorem sec7_carry_fiber_cover_zero {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} (Ph : Sec7Phase P S W a)
    (Env : Sec7Envelope P S W) {j : ℤ} (_hj : sec7_jBand P S j)
    {h₁ h₂ h₃ : ℤ} (hbox : sec7_shiftBox W h₁ h₂ h₃) {ξ₁ ξ₂ ξ₃ : ℝ}
    (hξ₁ : |ξ₁| ≤ sec7_hSum h₁ h₂ h₃) (hξ₂ : |ξ₂| ≤ sec7_hSum h₁ h₂ h₃)
    (hξ₃ : |ξ₃| ≤ sec7_hSum h₁ h₂ h₃)
    {M : ℝ} (hM : 2 * (W + W ^ 2 + W ^ 4) ≤ M)
    (hwin : ∀ y : ℝ, S.R / 72 - M ≤ y → y ≤ 16 * S.R + M → y ∈ sec7_rWin S W) :
    ∃ Λ : Finset ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℝ × ℝ)),
      (Λ.card : ℝ) ≤ 343 *
        (4 + 2 * (sec7_cPh * (sec7_Ssym h₁ h₂ h₃ / (P.G * S.Ω ^ 5)))) ∧
      (∀ pc ∈ Λ, pc.1.1 = 0) ∧
      (∀ pc ∈ Λ,
        (|(pc.1.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.1 : ℝ)| ≤ sec7_cCarry ∧
          |(pc.1.2.2.1 : ℝ)| ≤ sec7_cCarry ∧ |(pc.1.2.2.2 : ℝ)| ≤ sec7_cCarry) ∧
        (|(pc.2.1.1 : ℝ) - pc.1.2.1| ≤ sec7_cPh * (1 + (h₂ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.1 : ℝ) - pc.1.2.2.1| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₃ * (S.T₂ / S.R ^ 2)) ∧
          |(pc.2.1.2.2 : ℝ) - pc.1.2.2.2| ≤
            sec7_cPh * (1 + (h₁ : ℝ) * h₂ * (S.T₂ / S.R ^ 2))) ∧
        Set.Icc pc.2.2.1 pc.2.2.2 ⊆ Set.Icc (S.R / 72) (16 * S.R)) ∧
      (∀ r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋,
        diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
          diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + (0 : ℝ) →
        ∃ pc ∈ Λ,
          (r : ℝ) ∈ Set.Icc pc.2.2.1 pc.2.2.2 ∧
          diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
            diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + pc.1.1 ∧
          diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
            diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁)
              - pc.2.1.1 + pc.1.2.1 ∧
          diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
            diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂)
              - pc.2.1.2.1 + pc.1.2.2.1 ∧
          diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
            diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃)
              - pc.2.1.2.2 + pc.1.2.2.2) :=
  (sec7_carry_fiber_cover_core Ph Env hbox hξ₁ hξ₂ hξ₃ hM hwin).2

/- N8 (md 1572–1587, eq 7.3/7.4): "Thus, on a fixed carry branch and a fixed fiber u,
     ‖Φ_{ρ,u}(r)‖ ≪ δ₁(h) := δ₀ + ST₁/R² = δ₀ + S/(Rx²G²Ω⁴),   (7.3)
   where  Φ_{ρ,u}(r) := Δ_{h₁,h₂,h₃}f₃(r) + f₁(r+h_Σ)(B₀₃(r)+ρ₀)
     + Σ_{i=1}³ Δ_{h_i}f₁(r+h_Σ−h_i)(B_i(r)−u_i+ρ_i).   (7.4)"
   (7.4) is `sec7_Phi` (Sec7PhaseExp) verbatim; δ₁ is `sec7_delta1` (Sec7ZeroScale) verbatim.
   "Thus" = corner near-integrality (r ∈ E₃, md 1494–97: per-corner `hcorner`, at the AM-1
   renormalized threshold `sec7_cTay·δ₀`, so `‖Δ_{h₁,h₂,h₃}g_j(r)‖ ≤ 8·cTay·δ₀`) + eq (7.1)
   (`hprod`, the N6 inner bound at r with the SAME ξ's — taken as hypothesis since N6
   produces its ξ's existentially) + the N7 branch identities (`hbr0–hbr3`, fixed integer
   data on the cover piece, with `hprod` at N6's constant `sec7_cN6`).  The conclusion
   constant is `sec7_cCal` so it feeds `sec7_zero_triple_count`'s `hδ : δ ≤ cCal·δ₁(h)`
   directly (A1 gate: cCal = 10⁹ ≥ max(8·cTay, cN6) = max(8·10⁷, 10⁸); ledger U4).
   AM-2: `r` sits in the WIDE window. -/
/-- **N8 = eq (7.3)** (md 1572–1587): on a fixed carry branch and fixed fiber,
`‖Φ_{ρ,u}(r)‖ ≤ sec7_cCal·δ₁(h)` — the threshold form `sec7_zero_triple_count` consumes. -/
theorem sec7_phi_near_int {P : Globals} {S : Scale P} {a : ℤ} {W : ℝ} (Ph : Sec7Phase P S W a)
    {j : ℤ} (hj : sec7_jBand P S j) {h₁ h₂ h₃ : ℤ}
    (hbox : sec7_shiftBox W h₁ h₂ h₃) (gfun : ℤ → ℝ → ℝ)
    (hg : ∀ (j : ℤ) (r : ℝ),
      gfun j r = Ph.dBreve (Ph.ftil r + j)
        - Ph.dBreve' (Ph.ftil r + j) * Int.fract (Ph.ftil r))
    {ξ₁ ξ₂ ξ₃ : ℝ} {ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ : ℤ} {r : ℤ}
    (hr : r ∈ Finset.Icc ⌈S.R / 72⌉ ⌊16 * S.R⌋)
    (hcorner : ∀ ε₁ ε₂ ε₃ : ℕ, ε₁ ≤ 1 → ε₂ ≤ 1 → ε₃ ≤ 1 →
      Counting.distInt (gfun j ((r : ℝ) + ε₁ * h₁ + ε₂ * h₂ + ε₃ * h₃)) ≤
        sec7_cTay * sec7_delta0 P S)
    (hprod : |diff3 (h₁ : ℝ) h₂ h₃ (gfun j) (r : ℝ) -
        (diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) (r : ℝ)
          + Ph.f1D j 0 ((r : ℝ) + sec7_hSum h₁ h₂ h₃) *
              diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ)
          + diff1 (h₁ : ℝ) (Ph.f1D j 0) ((r : ℝ) + sec7_hSum h₁ h₂ h₃ - h₁) *
              diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁)
          + diff1 (h₂ : ℝ) (Ph.f1D j 0) ((r : ℝ) + sec7_hSum h₁ h₂ h₃ - h₂) *
              diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂)
          + diff1 (h₃ : ℝ) (Ph.f1D j 0) ((r : ℝ) + sec7_hSum h₁ h₂ h₃ - h₃) *
              diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃))| ≤
      sec7_cN6 * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2))
    (hbr0 : diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ) =
      diff3 (h₁ : ℝ) h₂ h₃ (Ph.f2D 0) (r : ℝ) + ρ₀)
    (hbr1 : diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁) =
      diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₁) - u₁ + ρ₁)
    (hbr2 : diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂) =
      diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₂) - u₂ + ρ₂)
    (hbr3 : diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) =
      diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (Ph.f2D 0)) ((r : ℝ) + ξ₃) - u₃ + ρ₃) :
    Counting.distInt (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ)) ≤
      sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ := by
  have _ := hj; have _ := hg; have _ := hr
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  have hA : (0:ℝ) < S.A := by unfold Scale.A; positivity
  have hR : (0:ℝ) < S.R := by unfold Scale.R; positivity
  have hT1 : (0:ℝ) < S.T₁ := by unfold Scale.T₁ Scale.F; positivity
  have hδ0 : (0:ℝ) ≤ sec7_delta0 P S := by unfold sec7_delta0; positivity
  have e1 : (1:ℝ) ≤ (h₁:ℝ) := by exact_mod_cast hbox.1.1
  have e2 : (1:ℝ) ≤ (h₂:ℝ) := by exact_mod_cast hbox.2.1.1
  have e3 : (1:ℝ) ≤ (h₃:ℝ) := by exact_mod_cast hbox.2.2.1
  have hQ : (0:ℝ) ≤ sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2 := by
    have hS : (0:ℝ) ≤ sec7_Ssym h₁ h₂ h₃ := by simp only [sec7_Ssym]; nlinarith only [e1, e2, e3]
    exact div_nonneg (mul_nonneg hS hT1.le) (pow_nonneg hR.le 2)
  -- 8-corner near-integrality: `‖Δ_{h₁,h₂,h₃}g_j(r)‖ ≤ 8·cTay·δ₀` (md 1494–97)
  have c000 := hcorner 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  have c001 := hcorner 0 0 1 (by norm_num) (by norm_num) le_rfl
  have c010 := hcorner 0 1 0 (by norm_num) le_rfl (by norm_num)
  have c011 := hcorner 0 1 1 (by norm_num) le_rfl le_rfl
  have c100 := hcorner 1 0 0 le_rfl (by norm_num) (by norm_num)
  have c101 := hcorner 1 0 1 le_rfl (by norm_num) le_rfl
  have c110 := hcorner 1 1 0 le_rfl le_rfl (by norm_num)
  have c111 := hcorner 1 1 1 le_rfl le_rfl le_rfl
  norm_num at c000 c001 c010 c011 c100 c101 c110 c111
  have h8 : Counting.distInt (diff3 (h₁ : ℝ) h₂ h₃ (gfun j) (r : ℝ)) ≤
      8 * (sec7_cTay * sec7_delta0 P S) :=
    Counting.distInt_diff3_le c000 c001 c010 c011 c100 c101 c110 c111
  -- the N7 branch identities turn `hprod`'s main term into `Φ_{ρ,u}(r)` verbatim
  have hPhiM : sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ) =
      diff3 (h₁ : ℝ) h₂ h₃ (Ph.f3D j 0) (r : ℝ)
        + Ph.f1D j 0 ((r : ℝ) + sec7_hSum h₁ h₂ h₃) *
            diff3 (h₁ : ℝ) h₂ h₃ (fun t => Int.fract (Ph.f2D 0 t)) (r : ℝ)
        + diff1 (h₁ : ℝ) (Ph.f1D j 0) ((r : ℝ) + sec7_hSum h₁ h₂ h₃ - h₁) *
            diff1 (h₂ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₁)
        + diff1 (h₂ : ℝ) (Ph.f1D j 0) ((r : ℝ) + sec7_hSum h₁ h₂ h₃ - h₂) *
            diff1 (h₁ : ℝ) (diff1 (h₃ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₂)
        + diff1 (h₃ : ℝ) (Ph.f1D j 0) ((r : ℝ) + sec7_hSum h₁ h₂ h₃ - h₃) *
            diff1 (h₁ : ℝ) (diff1 (h₂ : ℝ) (fun t => Int.fract (Ph.f2D 0 t))) ((r : ℝ) + ξ₃) := by
    rw [hbr0, hbr1, hbr2, hbr3]
    simp only [sec7_Phi]
  -- eq (7.1) at `r`: `|Φ(r) − Δ³g_j(r)| ≤ cN6·S·T₁/R²`
  have hclose : |sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ) -
      diff3 (h₁ : ℝ) h₂ h₃ (gfun j) (r : ℝ)| ≤
      sec7_cN6 * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) := by
    rw [hPhiM, abs_sub_comm]
    exact hprod
  -- `‖p‖ ≤ ‖q‖ + |p − q|`
  have htrans : Counting.distInt
        (sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ)) ≤
      Counting.distInt (diff3 (h₁ : ℝ) h₂ h₃ (gfun j) (r : ℝ)) +
        |sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ) -
          diff3 (h₁ : ℝ) h₂ h₃ (gfun j) (r : ℝ)| := by
    set p := sec7_Phi Ph j h₁ h₂ h₃ ξ₁ ξ₂ ξ₃ ρ₀ ρ₁ ρ₂ ρ₃ u₁ u₂ u₃ (r : ℝ)
    set q := diff3 (h₁ : ℝ) h₂ h₃ (gfun j) (r : ℝ)
    simp only [Counting.distInt]
    calc |p - round p| ≤ |p - (round q : ℤ)| := round_le p (round q)
      _ ≤ |q - round q| + |p - q| := by
          have e : p - ((round q : ℤ) : ℝ) = (q - round q) + (p - q) := by ring
          rw [e]; exact abs_add_le _ _
  -- assemble at `cCal = 10⁹ ≥ max(8·cTay, cN6)`
  have hfin : 8 * (sec7_cTay * sec7_delta0 P S) +
      sec7_cN6 * (sec7_Ssym h₁ h₂ h₃ * S.T₁ / S.R ^ 2) ≤
      sec7_cCal * sec7_delta1 P S h₁ h₂ h₃ := by
    simp only [sec7_delta1, sec7_cTay, sec7_cN6, sec7_cCal]
    linarith only [hδ0, hQ]
  exact (htrans.trans (add_le_add h8 hclose)).trans hfin

end Squarefree
