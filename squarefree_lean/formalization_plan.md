### W2–W4a COMPLETE (2026-06-12) — THE WALL IS CLOSED. Proved: N3,N4,N6,N7 (+Sec7CarryAux),
N8 (Sec7Branch ZERO-SORRY), N9′ (Sec7MonExpBuild constructor, no sub-stubs; c₁∈[1/6,2/3],
c₂∈[0.84,2] ⟹ c₁c₂≠0 is a THEOREM), N10×3, N11 (Sec7ErrBound.lean:172 + ErrAux/ErrPieces/
ErrFactors; MonExp interface(a): windows [1/16,4] + graded chains f1C/f2C/f3C as fields;
N11 gained hξᵢ ≤ h_Σ binders = ZeroHyp fields, consumers unaffected). LEDGER: cErr=10⁴²
(floor 8.8e40, 11.4×), cSub=10⁴⁴ (actual coupling 2.6·cErr, 38×; margins pass at capacity
10^64.3); only {cErr,cSub} moved. Tree 8532 green. 14/22 nodes proved.
REMAINING STUBS: N12×4 (Sec7ZeroScale), N13, N17, N19, N20 (Sec7Nonzero), N15, N22
(Sec7Harvest), + BoxSum glue (sec7_triple_split, sec7_ra_data_pack). Next per DAG: W4b =
N12+N17 → G2 → W5 = N13,N19 → W6 = N20 → W7 = N15,N22 → G3 → roots auto-green → Phase 4.
⏸ HOLDING — user supplies a modified workflow from here. Oversize-file queue: Sec7Nonzero 549,
Sec7ErrFactors 513, Sec7ErrBound 525 (single-theorem), Sec7Branch ~553.
### SHARED GAP found by Codex-N17 (2026-06-13): Φ-differentiability prerequisite for N12/N13/N17
N17/N12/N13 all conclude bounds on `iteratedDeriv 2 (sec7_Phi …)` but their parent hypotheses only
BOUND `iteratedDeriv 2 ME.Err`. To use `Φ = principal + Err ⟹ Φ'' = principal'' + Err''` needs
`iteratedDeriv_add`, i.e. ContDiff ℝ 2 of Φ — currently absent. RESOLUTION (clean, no statement
change to the consumers): add ONE shared derived lemma in the Phase layer —
`sec7_Phi` is C² on sec7_rWin AND `iteratedDeriv 2 (sec7_Phi …) r = iteratedDeriv 2 ME.principal r
+ iteratedDeriv 2 (ME.Err …) r`. PROVABLE FROM EXISTING DATA: sec7_Phi (def Sec7PhaseExp:217) is a
finite-difference (diff1/diff3) combination of products of Ph.f1D/f2D/f3D at shifted points; the
Sec7Phase bundle's `f{1,2,3}D_hasDeriv` chains (m<4) make each base C³ ⟹ shifts/finite-diffs/
products/sums preserve C² ⟹ Φ is C². Sequence: finish running N12 → dispatch the differentiability
lemma (Sec7PhaseExp or a new Phase helper file) → re-dispatch N12/N17 consuming it; N13 queued
behind. DO NOT edit Sec7PhaseExp while N12 builds against it.
### 2026-06-13 Codex W4b resolution: PHI-C2 + cSub bump + N17 hξ amendment
PHI-C2 ✓ (Sec7PhiDeriv.lean, Φ''=principal''+Err'' split). scale_lower: Codex's honest X-power
report showed the gap was purely cSub pinned too small — failing monomials G·Ω⁶/H, W⁴Ω²/√(Hx) each
≤1/cSub, needed cSub≈3.2e51 vs 10⁴⁴; A6 capacity is 10^64.3 so BUMPED cSub 10⁴⁴→10⁵⁵ (def+ledger,
green, dischargeable 55≤64.3; coupling cSub≥2.6cErr kept; isolated from cTriple/cN13). N17: needs the
three hξ_i:|ξ_i|≤sec7_hSum binders (PHI-C2 split requires them; faithful md-1547–53, same as N11's
amendment) — statement amended + proved via the split. Both re-fired. NOTE the cSub bump raises the
future glue/ra_data_pack discharge obligation to 1/10⁵⁵ (A6-certified achievable, 9-decade margin).

### §7 FINAL: the F_a⁻¹ inverse-phase module (2026-06-13) — last remaining construction
All 22 §7 nodes + both engines + both harvests PROVEN. GLUE-A done (prop_7_3/ra_data_pack
amended+threaded, easy fields discharged). TWO stubs remain:
- sec7_triple_split (BoxSum:123) — assembly from GIVEN Ph + proven engines (N7/N13/N19/N20 +
  ME/ZeroHyp construction); locks prop_7_1. [Codex running.]
- sec7_phase_build (BoxSum:131) — needs a NEW §3 sub-module: the F_a⁻¹ inverse-phase package.
  §3 has R_a⁻¹ (dtilde) through 4th/5th order but NO F_a⁻¹; Ffun has only forward d-derivs
  through 2nd (PhaseDeriv:72,138). Port the R_a⁻¹ theory (DefectDeriv pattern) to F_a.
  DECOMPOSITION (sequential):
  • P1 (new file FfunHighDeriv.lean): Ffun 3rd+4th forward d-derivatives (HasDerivAt chain,
    pattern of Ffun_hasDerivAt2_d) + the |F_a^{(k)}| magnitude/scale bounds. Parallel-safe
    (new file, no edit to existing). 
  • P2 (new Sec7FInverse.lean): dBreve = F_a⁻¹ via of_local_left_inverse on Ffun + its 1–4
    inverse derivatives (inverse-deriv formulas) + the F|dBreve'|≍HΔ, F²|dBreve''|≍HΔ scale
    bounds. ⇐ P1.
  • P3: f1D/f2D/f3D families (chain rule on dBreve/ftil) + ≍ T_i/Rᵐ bounds + assemble
    Sec7Phase + shift_mem + rounded-inverse margin → sec7_phase_build green. ⇐ P2.
  Scale: substantial (multi-hundred lines), but REUSE/port not new theory. S.F = H²GΩ/Δ².
Then ● prop_7_1 (after triple_split) + prop_7_3 (after phase_build) auto-green → G3 → Phase 4.

### ⛔ STRUCTURAL FINDING (2026-06-13) — Sec7Phase scale fields unsatisfiable on the wide window
P3d/P3c, then orchestrator sympy (analytic), confirmed: the Sec7Phase fields Fd'_lo/hi, F2d''_lo/hi
(and by extension the f-family ≍T_i/Rᵐ fields) are UNSATISFIABLE on sec7_tWin = [F/cWin, cWin·F],
cWin=10³. Reason: dBreve = F_a⁻¹ has dBreve'' ∝ d⁷ (exact leading ratio = 1, sympy); the t-window
factor 10⁶ ⟹ d-window factor 100 ⟹ dBreve'' varies by 100⁷ = 10¹⁴, exceeding the cPh band
[1/cPh, cPh] = [1e-6, 1e6] (factor 10¹²). So NO function satisfies F2d''_lo ∧ F2d''_hi on sec7_tWin.
CONSEQUENCE: sec7_phase_build (and ra_data_pack) CANNOT be completed — the spec is false. Sec7Phase
P S a is (almost certainly) UNINHABITED in-regime ⟹ prop_7_1 (proven, axiom-clean) is VACUOUS, and
prop_7_3 (consumed by §8/§9) cannot be discharged as the abstraction stands.
ROOT CAUSE: the §7 windows (sec7_rWin=[R/72,16R] factor 1152; sec7_tWin factor 1e6) are WIDE, but
the phase scales are uniform only on factor-O(1) (dyadic) pieces. The counting (N13/N19) correctly
works dyadically ([p,q], q≤2p); the Sec7Phase ABSTRACTION wrongly states uniform ≍ bounds on the
wide window. RESOLUTION (structural, not new math): restate the Sec7Phase scale fields DYADIC-LOCALLY
(per factor-2 sub-window, scale evaluated locally) — satisfiable (2⁷=128 ≪ cPh) — then re-thread the
nodes that consumed the wide-window fields. Size: significant, unknown. ESCALATED to user 2026-06-13.
