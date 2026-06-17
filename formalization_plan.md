# Formalization plan: organization & attack for `explicit_writeup.md`

Companion to `math_audit.md` (which verifies the mathematics). This plan covers how to
organize a Lean/mathlib formalization of the theorem
`θ_* ≤ 1/5 - 2/94885` and the order in which to attack it.

## §7 Φ″ ENDGAME — C⁶ extension, A–E plan + DECIDED constant ledger (2026-06-16)

THE ONLY remaining sorry in the tree: `sec7_zero_few_critical` Φ″ branch (Sec7ZeroScale.lean:1969).
theorem_10_1 axioms = [propext, sorryAx, Classical.choice, Quot.sound]; sorryAx = this one stub.
Stage-0 de-risk (math-auditor ×2) VERDICT: the tight C⁶ route is GENUINELY required (the crude
C⁵/power-saving route loses an unbounded R/h factor in the residual finite-difference `diff3[e₃D]`
— NOT an hG10x-style over-tightness). Φ′ branch already PROVEN (weight r³); Φ″ mirrors it (weight r⁴).

### DECIDED CONSTANT LEDGER (path-local; existing m≤2 constants UNCHANGED)
- KEEP (m≤2 path, verbatim): `sec7_cExp=10²⁵`, `sec7_cErr=10⁴²`, `sec7_cExpIn=10²⁵`.
- NEW `sec7_cExpIn6 = 10²⁹` — residual INPUT bound at order 6 (producer const `≈ 6!·8e7·(10³)⁶ = 5.76e28`,
  margin 1.74×). The old cExpIn=10²⁵ FAILS at m=6 by 5760×, hence a separate m=6 constant.
- NEW `sec7_cExp3 = 10²⁹` — m=3 monomial-expansion ceiling. Floor = max(d3f3@m=3 = 48·|aprod(−¼,7)|·
  2000^{29/4} = 1.31e28, cExpIn6-fold = 5.76e28) = 5.76e28; margin 1.74× (7.6× vs the monomial alone).
- NEW `sec7_cErr3 = 1.3·10⁴⁵` — m=3 error-bound ceiling. Window `[assembly 9.6e44 , domination 1.76e45]`
  ⟹ margin 1.35× on EACH side. (assembly floor = 9.6e15·cExp3; domination ceiling = (1105/64)(21/4096)
  (1/512)·cSub / (16⁴·12) with cSub=10⁵⁵.)
- `sec7_leib_bound` constant 4 → 8 (= Σ_{i≤3} binom(3,i)) at the m≤3 arm.
- ⚠ TIGHT (~1.35×), NOT ≥2×. Binding driver = the r⁴-weight `16⁴` penalty (err-mult 81920 vs Φ′'s 4864,
  from r ≤ 16R on the wide window). Two ledger inputs are auditor ESTIMATES — re-confirm EXACTLY during
  build: (i) cExpIn6 producer const 5.76e28 (Stage A), (ii) err-assembly factor 9.6e15 ("env cap 4e14
  reusable at k≤3", Stage C). FALLBACK if either is larger: tighten the per-dyadic bound r ≤ 12R
  (err-mult → 27648 ⟹ ceiling 5.2e45 ⟹ ≥2× restored) or piggyback an r³-weight. Freeze these in ONE
  place (Sec7PhaseExp.lean alongside cExp/cErr) and re-check after any bump (CLAUDE.md §8).

### STAGES (strict dependency order; struct change ⇒ full rebuild each cycle)
- **A — §3 residual data C⁵ → C⁶.**
  - A0 ✅ DONE (2026-06-16, green, Lower/DefectDeriv6.lean, 372 ln): `dtilde_d6_upper : |d̃⁽⁶⁾(r)| ≤
    C₆·(D/R⁶)` with **C₆ = 1381746600000000000000000000000000000000 (≈1.38·10³⁹)** (larger than the
    10³⁵–10³⁶ guess — denom floor 72⁶·5¹¹ is big; one-sided, fine). d̃⁽⁶⁾ = 45·d̃·(d̃+a)·P₁₀/(64 r⁶
    (a+2d̃)¹¹), POSITIVE; P₁₀=231a¹⁰+4058a⁹d̃+33274a⁸d̃²+165416a⁷d̃³+548520a⁶d̃⁴+1262872a⁵d̃⁵+2039656a⁴d̃⁶
    +2278528a³d̃⁷+1683472a²d̃⁸+742560a d̃⁹+148512d̃¹⁰. + dtil5/dtil5_hasDerivAt/dtilde_r_iteratedDeriv6/
    dtilde_iteratedDeriv5_hasDerivAt. C₆≪10⁸⁰ ⟹ does NOT threaten cExpIn6 (producer const is expansion
    combinatorics, not C_m-driven; dtilde_dN_upper only feeds via the absorbed structure).
  - A1: `Sec7Defs.lean` Sec7Phase fields (290–314): `ra_e₁D/₂D/₃D_deriv` `m<5→m<6`; `…_bound` `m≤5→m≤6`
    (the m=6 bound uses cExpIn6 on its line; e₂D keeps relErr, e₁D/e₃D keep relErrF).
  - A2: `Sec7PhaseConstruct.lean` — add `…_contDiffAt6` instances (bases generic-n; dBreve6 exists);
    producers `sec7_phase_f{1,2,3}D_eq_powMonD_add_ra_e_iD` (~2967/3024/3093) `m≤5→m≤6`; the residual
    bound cores (~5479–5567) at m=6 (consume dtilde_d6, const ≤ cExpIn6); field assignments in
    `sec7_phase_concrete` (6017–6069) extended to m=6.
  - A3: `Sec7MonExpData.lean` Sec7RaExpData (108) + `sec7_raExpData_of_phase` (BoxSum.lean:124) forward
    order 6.
- **B — monomial expansion m≤2 → m≤3** (`Sec7MonExpFam{1,2,3}.lean`, `Sec7MonExpBuild.lean`): extend the
  5 `build_*_exp` to m=3 on the cExp3 path; worst = `build_d3f3_exp` (Fam3:341, the m+3=6 residual fold).
  Sec7MonExp fields B03_exp/d3f3_exp etc. at m=3.
- **C — error engine m≤2 → m≤3.** `Sec7ErrAux.lean` `sec7_leib_bound` `m≤2→m≤3` (const 4→8, interval_cases
  0..3; leib_deriv already m<3). `Sec7ErrBound.lean` `sec7_err_deriv_bound` (175) `m≤2→m≤3` on the cErr3
  path (re-derive `sec7E_num_final` for m=3, the 9 hb* calls). Confirm Sec7Nonzero T₁/10¹⁰⁰ absorbs cErr3.
- **D — order-3 principal formula.** `Sec7ZeroScale.lean` extend `sec7_zero_principal_deriv_formula` (~948)
  to order 3: `(r⁴Φ″)′` single-monomial collapse `−(1105/64)·C*·P·(T₃/R³)·y⁻⁹ᐟ⁴`.
- **E — fill the sorry.** `Sec7ZeroScale.lean` write `sec7_zero_deriv2_few` mirroring `sec7_zero_deriv_few`
  (1815–1890) with weight r⁴ (principal ≥1.729e-4·R·Cbase; E₂ = 4r³ErrJet2+r⁴ErrJet3 dominated via
  cErr3·errScale + |C*|≥21/4096; Rolle ⟹ ≤1 ≤ KZero=100), replace sorry (1969) with the call.

## STATUS — 2026-06-11: §§1,4,5,6,8,9 COMPLETE. prop_5_1 PROVED (Prop51.lean:37, axiom-clean
[propext, Classical.choice, Quot.sound], full tree green 8513 jobs). Live stubs = §7 ONLY:
prop_7_1/prop_7_3 (BoxSum.lean) + 4 BoxPowerSums power-sum stubs. GAP 3 CLOSED 2026-06-11:
chain = prop51_perpair (Prop51Assembly.lean:30; partition + 4 range counts + producer packs)
→ Ra_card_le_popular + markov_discharge (Wnat=⌈128W⌉) → prop51_combine → prop_5_1, C=10⁴¹⁵.
[Historical GAP-3/Step-4 repair ledger below — superseded, kept for reference.]

### §7 FRONTIER (2026-06-15) — 4 sorries left; the phiContDiff/phiFewCritical endgame
Residual + f-scale layers DONE (ra_e₁/₂/₃D bounds, f-scale lo/hi all green). Remaining:
`Sec7PhaseConstruct.lean` `phiContDiff` (6190), `phiFewCritical` (6193), `round_inverse_margin`
(6208); `BoxSum.lean` `sec7_phase_build` (1959, the N24-PHASE assembly consuming the above).

**ROUTE for `phiContDiff` (FORCED, faithful):** the field is currently `ContDiff ℝ 2 Φ` (GLOBAL),
but Φ is built from `dBreve = Function.invFun` ⟹ only `ContDiffOn` the inversion window, NEVER
globally C². So global ContDiff is UNDISCHARGEABLE. Fix = mirror §5's proven `step2_subset_count`
(`Lower/Step2Bands.lean:104`): field → `ContDiffOn`, and the zero-count engines bump-extend to a
global ψ internally, feed `prop43_local_explicit` (which needs global C², `NearCurveResidual:395`),
transfer counts via `ψ = Φ` on integers in the window. Tools already in `Sec7PhiSmooth.lean`:
`sec7_phi_expanded_contDiffOn` (Φ is `ContDiffOn` on a window) + `sec7_exists_global_extension`.
EXECUTION (bottom-up, green each step):
  (A) adapter `sec7_prop43_local_contDiffOn` in Sec7PhiSmooth: takes `ContDiffOn ℝ 2 f (Ioo(N/2-1)(5N/2+1))`
      + curvature on `Icc(N/2)(5N/2)` + `2≤N`, does extension internally, returns the prop43 count bound on f.
  (B/C) N19 (`Sec7Nonzero:2027`) + N13 (`Sec7Branch`, ρ₀=0): `hcd : ContDiff` → `hcdO : ContDiffOn`,
        swap the `prop43_local_explicit` call (N19 line 2165) for the adapter.
  (D) `Sec7Defs` field `phiContDiff` → ContDiffOn on a window ⊇ [R/144-1, 40R+1]; `BoxSum` wrapper
      `sec7_phase_phi_contDiff` returns ContDiffOn; call sites 1162/1690.
  (E) construct: discharge field via an ASYMMETRIC `sec7_phi_expanded_contDiffOn` — the symmetric one
      over-shrinks by M≈4(W+W²+W⁴) and misses the count edges; but h₁,h₂,h₃≥1>0 (box) ⟹ diff terms
      shrink only the UPPER window, ξ's (|ξ|≤hSum) shrink lower by ≤hSum ⟹ covers [R/144-(W+W²+W⁴),40R+…].
  (F) `phiFewCritical` — separate Rolle argument (see [[sec7-wall-phifewcritical]]); ρ₀=0 ⟹ ≤1 zero.
  (G) `round_inverse_margin` + `sec7_phase_build` assembly → prop_7_3.

> ⛔ **STRUCTURAL FINDING (2026-06-13) — Sec7Phase wide-window scale fields UNSATISFIABLE; SCOPED, FIX = Option A.**
> The `Sec7Phase` structure (Sec7Defs.lean, ~30 fields) states uniform `≍` scale bounds on the WIDE
> windows `sec7_tWin=[F/10³,10³F]`, `sec7_rWin`, `sec7_rWinWide` (all factor-10⁶ apertures). `F2d''_lo/hi`
> is FALSE there: `dBreve=F_a⁻¹` has `dBreve''(t) = (1/9)d⁷/(X²a²) + … ∝ d⁷` (sympy-confirmed, a=ΔΩ held
> fixed; equiv. `F2d'' ∝ t^{-7/3}`), so over the factor-10⁶ t-window it swings by `(10⁶)^{7/3}=10¹⁴ ≫`
> the `cPh=10⁶` band (10¹²). ⟹ `Sec7Phase` is uninhabited in-regime; `prop_7_1` is PROVEN-but-VACUOUS,
> `prop_7_3` undischargeable. The 25 sorries in `sec7_phase_build`/`Sec7PhaseConstruct` are exactly these
> unsatisfiable wide-window obligations (the field's own TODO names the fix: "move t∈sec7_tWin to the
> positive image window").
>
> **SCOPING AUDIT VERDICT (2026-06-13, read-only auditor + own sympy + ledger re-pin): FIX = Option A,
> the cheap path. GLOBAL scales SUFFICE — they do NOT need to become window-local functions of p.** On the
> engine window `[R/72,16R]` the two-sided `|f_i^{(m)}| ≍ T_i/Rᵐ` (global T_i,R) holds uniformly within
> `|falling(αᵢ,m)|·72^{|αᵢ−m|}` (α₁=−1,α₂=¾,α₃=−¼ from `ra_e*_zero`). So: **narrow the 3 windows + bump
> `cPh: 10⁶→10¹²`**; no per-p localization. The wide 10⁶ aperture was pure over-widening — the writeup's
> "r≍R"/"t≍F" IS the narrow object; no step needs the uniform wide bound. (Fallback Option B = dyadic
> `∀[p,q]⊆[R/72,16R],q≤2p` quantifier with scale pinned to sub-window, keeping cPh=10⁶ — heavier:
> Branch/CarryAux become MAJOR. NOT needed.)
>
> **RE-AUDIT (2026-06-13, 2nd global walkthrough, user-requested before any edit): GO, with one
> CORRECTION — `cPh = 10¹²`, NOT 10¹⁰.** The steepest obligation is `f1D_hi` at **m=4**: the falling
> factorial `|falling(−1,4)|=24` (which the 1st scoping dropped) gives `24·72⁵ = 4.64·10¹⁰ > 10¹⁰`, so
> 10¹⁰ is 4.6× short; 10¹¹ is the bare floor, **10¹² gives 21× margin** (sympy-confirmed). m=4 is never
> *consumed* (N6 uses f1D m=2,3; CarryAux uses f2D m=2,3) but the structure's `∀m≤4` quantifier forces it
> — cPh=10¹² is the clean fix (alt: restrict fields to m≤3, but that edits the public structure).
> WINDOW REFINEMENTS: r-window must be **ASYMMETRIC** `Icc (R/72 − 2(W+W²+W⁴)) (16R + 2(W+W²+W⁴))`, lower
> edge PINNED at R/72 (R/144 makes f1D⁴=24·144⁵=1.5·10¹², far worse); pad `2(W+W²+W⁴)` = the CarryAux:340
> margin (dominates N6's single margin), positive via N18 R≥W⁸. **KEEP tWin WIDE/decoupled** (must hold the
> f̃-image [F/25,8F] + j-band/θ for shift_mem; F2d'' fits at any cPh≥10⁷, so tWin is NOT cPh-constrained —
> do NOT narrow it to a shared cWin'). rWinMid/rWinWide = asymmetric analogues (preserve rWin⊆mid,
> mid+shift⊆wide). A single symmetric cWin' does NOT work (would tighten the §3 error-subordination 1000×).
>
> **LEDGER GATE CLEARED (own re-pin at cPh=10¹², all asserts pass):** cPh feeds ONLY (linearly, verified
> no higher power) `cTay=max(cPh,cdMar):10⁷→10¹²`, `cN6=10²cPh:10⁸→10¹⁴`, `cCal=max(8cTay,cN6):10⁹→10¹⁴`
> (recommend cCal→10¹⁵ for slack; cN6≤cCal is tight at 10¹⁴). Downstream `cBand=10²⁰=2·cMon·cCarry·72³`
> (cMon,cCarry=10⁶ are SEPARATE defs in Sec7PhaseExp.lean:38,52 — NOT cPh; =7.46·10¹⁷), `cTriple=10⁵⁶`
> (cFib,cN13), envelope `10²⁰⁰/10³⁰⁰` all cPh-independent or absorb (producer product ~10⁴⁰). N6/N8/N17/
> triple all hold. CALLER PASS (not the §5 Ω≥1 trap): prop_7_3 (BoxSum:52) hardwires count to
> [⌈R/72⌉,⌊16R⌋]; Fiber.lean builds rStar with `hrStar_band : R/72 ≤ rStar ≤ 16R` (Fiber:203,654,1010);
> §8 never hands a wider r — narrowed window IS dischargeable.
>
> **PER-NODE CHANGE CLASS:** ~8 NO-CHANGE (engines N13/N19 already dyadic via `phiFewCritical [p,q],q≤2p`;
> cube N5; harvests N15/22; box-sums N14/21; roots N23/N24 — conclusion `card≤C·(R/W)` UNCHANGED, §8 caller
> faithful), 3 MINOR (Sec7Branch, Sec7CarryAux, Sec7PhiDeriv — thread narrowed windows + bumped const),
> 1–2 MAJOR (the provider `sec7_phase_build` discharging the 25 sorries; MonExp/Err `ra_e` family — exactly
> where the sorries already live). ORDERED PLAN: (1) Sec7Defs narrow windows + cPh→10¹⁰, re-run ledger;
> (2) discharge the 25 sorries in `sec7_phase_build`; (3) MonExp/Err window swap + re-pin ra_e const;
> (4) Branch/CarryAux/PhiDeriv thread (mechanical); (5) roots/engines/cube/harvest untouched, rebuild.
> AWAITING USER DIRECTION before executing (per "scope it first, I'll direct things").
>
> **F_a⁻¹ PHASE-CONSTRUCTION SUB-DAG (current):**
> ```
>   P1 FfunHighDeriv ✅ (F''',F'''' + |F^{(k)}|≍F/Dᵏ; 669ln,0 sorry)
>      └─> P2 Sec7FInverse ✅ (dBreve=F_a⁻¹ + dBreve'..'''' + HasDerivAt chain
>      │      + F|dBreve'|≍HΔ, F²|dBreve''|≍HΔ; 581ln,0 sorry; P3c bridge added)
>      └─> P3 Sec7PhaseConstruct ⛔ (25 sorries = the wide-window fields → become
>             dischargeable ONLY after Option-A rework above) ── feeds ──>
>             sec7_phase_build (BoxSum.lean:131, STUB N24-PHASE)
>             └─> sec7_ra_data_pack (BoxSum:152) └─> prop_7_3 (blocked)
>                                                 prop_7_1 ✅ (axiom-clean, vacuous until P3 lands)
> ```
>
> NEXT REDRAWN FULL DAG + status table maintained below in "### §7 EXECUTION DAG (live)".

## §7 PLAN (2026-06-11) — contract-first, statement-chopped, audit-gated

CONSTRAINTS (binding, from CLAUDE.md §8): every statement is written and AUDITED before any proof
is attempted; no lemma may carry an ambient hypothesis outside the standing regime pack; constants
live in ONE ledger; the §8/§9 call sites are the contract.

### Phase 0 — CONTRACT (gate: no §7 proving until ✅)
- [ ] 0.1 Stub faithfulness: prop_7_1/prop_7_3 statements vs writeup (auditor).
- [ ] 0.2 Call-site dischargeability: every hypothesis of the stubs (and of every Phase-1 node)
      must be supplied by the EXISTING green call sites in §8/§9 — including the Ω<1 band and
      G-vs-U freedom (the §5 lesson). Any ambient binder in Bracket/ defs gets flagged and justified.
- [ ] 0.3 The §7 constant LEDGER: one sympy script (tools/sec7_ledger.py) holding every monomial,
      threshold, and fit of the Phase-1 DAG; updated with every statement change; re-run before
      every dispatch that touches a constant.

### Phase 1 — STATEMENT DAG (24 nodes; from the 2026-06-11 triple recon)
§7 = md 1296–1984; envelope = md 1421–1451 (use the BUNDLED envelope verbatim as ONE hypothesis);
call site = dblock_on_strip (Opt/Global.lean:46,102; supplies W := OnStripAux.Wnz, AdmissibleW, RaWitness;
strip facts G⁻²Ω^{-11/2}X^{-O(u)} ≪ x ≪ G¹⁷Ω⁻²⁶X^{O(u)}). TOPOLOGY FIXED = attempt-1's FreshRoute
(zero-carry via Lemma 4.2 ‖ nonzero-carry via local Prop 4.3 → aggregation); NO variant exploration.

Node table (id | gist | md | deps | machinery | state):
 N1  defs F,x,d̆,g_j; scales T₁,T₂,T₃ identities        1299–1386  —        §3          sympy✓
 N2  F·d̆'≍HΔ, F²·d̆''≍HΔ; f_i^{(m)}≍T_i/R^m            1327–31,1509–14 N1  §3          —
 N3  near-int ⟹ ∃j, |j|≪1+H/A², f*=⌊f̃⌋+j              1307–1326  N1       Prop 3.2    —
 N4  #𝓡_a ≤ Σ_j Σ_r 1_{‖g_j‖≤δ₀}; Taylor               1332–1361  N2,N3    —           TRAP-1
 N5  Lemma 7.2 averaged-cube lower bound                 1463–1487  —        Lemma 2.2   —
 N6  eq 7.1 third-diff product rule + O(ST₁/R²)          1516–1534  N2       —           —
 N7  carries ρ=O(1); fiber u O(1+S/(GΩ⁵)) (7.2)          1545–1570  N2,N6    floor-br.   sympy✓
 N8  eq 7.3/7.4 per-branch ‖Φ_{ρ,u}‖≪δ₁(h)              1572–1587  N4,N6,N7 —           sympy✓
 N9  monomial expansions f₁f₂f₃/B_i; rel-err X^{-c}      1589–1633  N2       §3:334      — ⚠WALL
 N10 eq 7.5; c₃=3c₁c₂ ⟹ C*=−21c₁c₂/16 ≠ 0               1634–1665  N9       inv-func    sympy✓ ⚠WALL
 N11 Err^{(m)} bound; absorb Ph_ΣT₃/R⁴                   1666–1682  N9       —           ledger ⚠WALL
 N12 ρ₀=0 scale T_{ρ,u}; Wronskian; subordinations       1686–1740  N10,N11  Wronskian   TRAP-3 ⚠WALL
 N13 per-triple Lemma 4.2 + 5 sqrt-evals + (7.6)         1740–1781  N8,N12   Lemma 4.2(log) sympy✓ ⚠WALL
 N14 10 zero-branch box sums (Σ1≪W⁷ … ΣSh_Σ≪W¹⁷)        1782–1803  —        sums        = box_sum_* stubs + sum_inv_sqrt_le
 N15 zero-branch harvest → envelope entries              1770–1825  N5,N7,N13,N14 —     sympy MANDATORY
 N16 ρ₀≠0 smallness facts (X^{-c} forms, NOT x≫GU¹⁰)     1827–1836  regime   —           TRAP-3
 N17 local pieces I_q; T_{ρ,q}≍T₁ (RT₁=A²)               1837–1868  N10,N11,N16 —       sympy✓
 N18 side conditions R≥W⁸, T₁>1, 0<δ₁<1                  1870–1911  envelope strip       sympy✓ TRAP-2b
 N19 local Prop 4.3 per piece ⟹ (7.8); log shrink-c      1911–1922  N17,N18  Prop 4.3(log) —
 N20 nonzero sqrt-term evals (3; 3rd lossy by √H ok)     1923–1934  N19      —           sympy✓
 N21 ΣS^{1/2}≪W¹⁰, ΣS^{3/2}≪W¹⁶ box sums                1938–1941  —        sums        = box_sum stubs
 N22 nonzero harvest → envelope entries                  1942–1974  N5,N7,N19–21 —      sympy MANDATORY
 N23 Prop 7.1 assembly (contradiction M>R/W)             1453–61,1973–75 N15,N22 —      —
 N24 Prop 7.3 = Σ_j over O(1+H/A²) of Prop 7.1           1977–1984  N3,N23   —           —

TRAPS (recon-verified, bound to nodes): TRAP-1 (N4): md 1352's identity off by G² — define δ₀ as
DISPLAYED (the larger Δ⁵/(H³Ω²)), Taylor step as ≤, never the 1352 identity. TRAP-2 (N13,N19): the
Lean Lemma 4.2/Prop 4.3 carry logs — absorb via shrink-c/X^{O(u)}; 2b: md 1898's G^{-69/2} is G^{-36}
(benign, T₁>1 still holds for g<1/361). TRAP-3 (N12,N16): md 1717's ambient x≫GU¹⁰ is NOT on the
strip — state the Lean hypotheses as the verified X^{-c}-smallness facts from envelope+strip
(W⁴Ω²(Hx)^{-1/2} ≤ H^{-1/4}G^{3/2}U^{49/8}X^{O(u)}), never the literal. TRAP-4 (N15,N22): the
25-vs-21 envelope overlap — bundled envelope verbatim; per-entry root-taking sympy-mandatory.

ATTEMPT-1 SALVAGE (port with per-hypothesis provenance ONLY): admissibility final-scales
(Wstar.lean:1303), inv-√ product sums (InvSqrt.lean:16,40,188 → N14/N21), the ~30 Section7Polynomial
bounds (→ N14/N21/N15/N22 arithmetic). DO NOT port the route plumbing. THE WALL attempt 1 never
closed = N9–N13 (their checklist items 24–40, the concrete phase expansion → Lemma 4.2): budget the
deepest audits + freshest derivations there; recon has already sympy-verified C* and the N13 evals.

FILE MAP (≤400 ln, one theme): Bracket/Sec7Defs (N1–N2), Sec7Branch (N3,N4,N6–N8), Sec7Cube (N5),
Sec7Phase (N9–N11), Sec7ZeroScale (N12–N13), Sec7BoxSums (N14,N21 + the 4 existing box_sum stubs),
Sec7Harvest (N15,N22), Sec7Nonzero (N16–N20), BoxSum.lean keeps prop_7_1/7_3 (N23,N24).
All 24 nodes land as `sorry -- STUB: N<k>`; N23/N24's PROOFS are written FIRST consuming the stubs —
sorries at the LEAVES, never the root.

### Phase 2 — INDEPENDENT AUDIT WAVE (gate per node)
One math-auditor per node-cluster, in parallel: faithfulness vs md; hypothesis dischargeability
from the parent node/composition; constants vs the ledger; boundary coherence with sibling nodes.
A node may enter Phase 3 only with its audit ✅. Audit findings amend statements BEFORE proofs exist
— statement changes are free at this stage.

### Phase 2G — GLOBAL WALKTHROUGH AUDITS (recurring; user-mandated 2026-06-11)
Besides the per-node gates A1–A6, a single auditor periodically walks §7's ENTIRE proof
start-to-finish (md 1296–1984 against the landed Lean), checking ACROSS node boundaries:
(i) hypothesis flow — each node's hypotheses derived EXACTLY (quantifiers + constants) from its
parents' conclusions + Sec7Envelope + regime, no orphaned assumption anywhere in the chain;
(ii) the quantitative thread — δ₀ → δ₁(h) → per-triple (7.6) → box sums → harvest margins →
contradiction constant, summed END-TO-END against the ledger (does the final C close with the
N5 cube constant and harvM? the flag-1 res-entry slack question); (iii) multiplicity bookkeeping
(j-band × 8 carries × fibers × intervals-per-fiber); (iv) caller thread (10⁻²⁵Wnz → prop_7_3 →
dblock_on_strip constant). SCHEDULE: **G1** after P1e+P1f (statements complete, before any leaf
proof); **G2** after wave W4 (before the engine nodes N13/N19); **G3** after W7 (before Phase-4
close). A G-audit failure reopens the affected statements — cheap before proofs, mandatory gate.

### Phase 3 — PROOF WAVES (leaves-first, parallel where files are disjoint)
lean-prover units under the §8 process protocol (sympy-forced arithmetic, ≤200 words prose/turn,
first Write ≤6 actions, one decl per edit, build per decl, ≤15-line reports, half-scope units).
Attempt-1 salvage is PORTED only with per-fact provenance: each ported hypothesis must cite its
writeup line or be dropped (the §5 hv2 lesson).

### Phase 4 — CLOSE
Full-tree build + axiom check on prop_7_1/prop_7_3; dashboard; prune; split; memory update.

RECON IN FLIGHT (3 units): writeup §7 statement-chop; Lean contract (stubs + call sites + machinery
+ the Σh^{-1/2} candidates); attempt-1 Wstar postmortem (salvage + hazard map — attempt 1 died here).


> ✅ STEP 2 COMPLETE 2026-06-09 — `ra_step2_range_le` (`Prop51Step2.lean:31`) green, via the slack bands engine +
> the order-4 Wronskian φ″-structure. §5: Steps 1✅,2✅,3✅.
> ⏳ STEP 4 ~99% GREEN 2026-06-09 (SquareDiff/additive port, ~31 dispatches; full green inventory + the remaining
> seam in memory [[prop51-step4-port-state]]). SEAM CORRECTED BY FULL AUDIT 2026-06-09 (sympy, per-piece): the E-budget
> must go HYBRID Vmax/V_s per piece, not just the cubic. At Vmax only {flat-drift, p2_t3, p2_t4} survive hEA (p2_t4
> MUST stay capped — ∝n² at V_s); {recon_a, recon_b, p2_t2} fail at Vmax, fit at V_s in the EXISTING cE·√n slot;
> {cubic} fits at V_s in a NEW cE₂·n slot (hEC slack G⁴U¹⁵, hED slack ΔG⁶U²⁹; crude 2·Pmaj drift suffices,
> cE₂=(616√6/3)(GΩ/Δ⁴)a⁴(2ℓ₂−ℓ₁)/L²); {p2_t1} fails BOTH at Vmax, at V_s is a NEW c_const slot whose b-product pairs
> with the **U⁹⁵ block** (folding into cE·√n leaves G^{5/2}U⁴⁸ residual — don't). So: weight4add →
> (2+ev/√n+cE√n+cE₂n+c_const)(b+dc/√n) (`step4_ssum` already has all 4 sum slots), per-piece Diam2 budget split,
> then the (otherwise-traced) compose `ra_step4_range_complete`. err-part + m=ℓ₁v units audited exact. Then GAP 3.
> DISPATCH DAG (2026-06-09/10): ✅W=`Step4Weight5`(weight5+collapse5+range_add5, 6 absorb slots, const 80);
> ✅A1=`Step4P2Hybrid`(p₂ split: t1=5ℓ₁³ℓ₂²(ℓ₂−ℓ₁)²B³·V, t2=15ℓ₁³ℓ₂²(ℓ₂−ℓ₁)B²·V², t3/t4 capped);
> ✅B=`Vbox` lemmas in `Step4VsBand` (vbox_of_pin, Vbox_sq, Vbox_cube_div_sqrt_le);
> ✅A2=`Step4DiamHybrid`(`Sigma_closed_perturb_hyb`+`step4_sqdiff_diam2_hyb`, each piece at audited box);
> ✅N1=`Step4FitCubic`(hEC/hED, majorant cE₂≤10¹⁸GΩ⁵/(ℓ₁L); NB pin const 10³ ⟹ 10⁸ was too small);
> ✅N2-routes AUDIT: all 8 absorb chains verified (recon/p2t2/cap→hEA,hEB; cC→hEE,hEF); TIGHT = p2_t3 hEA-fit
> slack 10⁻⁴³, needs h1+hDeW (hΔreg insufficient); everything else ≥10²⁴⁰ slack. ⏳BAND=`Step4Band5`
> (band_collapse5+vsum_le_weight5+cE2hyb_le_majorant; retry — 1st attempt died on output-token cap, like N1's 1st).
> ✅ ALL SIX ABSORB FITS GREEN 2026-06-10: hEA=`step4_fit_cE_A` (FitEA:853), hEB=`step4_fit_cE_B` (FitEB:522),
> hEC/hED=`step4_fit_cubic_A/B` (FitCubic:21,116; cE2hyb bridge `cE2hyb_le_majorant` Band5:83),
> hEE/hEF=`step4_fit_cC_E/F` (FitCC:50,152). Band engine COMPLETE: `band_collapse5` (Band5:408),
> `vsum_le_weight5` (Band5:111), glue `fibre_v_card_le`/`vlo_pin_of_sq` (Step4FibreCard). Spec bugs caught by
> agents: cEhyb cap-slot 2a→4a (n∈[1,2) counterexample); EA m-cap U²⁵/Ω⁸ false for p3 → sharp U¹⁵/Ω¹².
> NOTE: FitEA (910 ln) + FitEB (562 ln) over the 400-line guideline — split candidates post-completion.
> ✅ C2a = `step4_fibre_branch_le` (Step4Compose.lean:50). ✅ PACKS: W5MONO (`Step4W5Mono`),
> PACK-1 (`Step4PackPoint`: sqlo+sign+lat), PACK-2 (`Step4PackPair`: hpair via min(Vbox,Vmax)+mono),
> PACK-3 (`Step4PackPerv`: hperv, K_C=10²⁰⁰, b/dc = the frozen collapse coefficients exactly).
> ⚠️ AUDITED REGIME FACT (2026-06-10): `Step4_E_le_rho_s`'s ρ≤¼ route is UNFAITHFUL for the s₄ pin — its
> p2_t4 box-collapse term needs `16·8316·10⁵⁷ℓ₁³ℓ₂²(ℓ₂−ℓ₁)² ≤ G²Ω⁸`, not dischargeable (even ℓ=(1,2),Ω=1
> needs G≥10³¹); also hvpin_hi-circularity. CORRECT route = per-point V₂-dominance `psum_resid_le_sharp`
> (UpsilonMagV2.lean:453) under `hVcut: V₂≤|v|` (✅ landed in `step4_pack_sqlo`, Step4PackPoint.lean).
>
> ✅✅ **STEP 4 COMPLETE 2026-06-10** — `ra_step4_range_complete` (`Step4Capstone.lean:216`) GREEN, full tree
> 8410 jobs, zero new sorries. Faithful conclusion: filter.card ≤ 80·(2·10³¹²)·C·(H/Δ)·(U⁷⁵+U⁹⁵ blocks).
> Final chain: window data → sgn collation → `step4_fibre_count_le` (Step4FibreCount:84, sign split ×2)
> → ev-bridge (k=10¹¹²: the window budget's 10¹¹⁰·UpsT term IS the second ev_frozen monomial)
> → `ra_step4_range_add5` + 6 fits. Gap hypothesis UNIFIED to the `step4_hb0gap` budget form (relaxation
> threaded PackPoint→FibreCount→Capstone; E_recon margin ~10²⁹). CALLER OBLIGATIONS for GAP 3/§5 assembly:
> `hbud : step4ErrU ≤ 1/4` (global H-calibration), per-r bundle over the filter (hb0box/hvmax/hb0gap/hmem/
> hVcut with V₂var ≥ V₂ P S), N + hNlo/hNcap. See progress/summary.txt for prune candidates + oversize files.
> **NEXT: GAP 3.** QUAD-AUDIT 2026-06-10 (A: constants/Bcombine; B: S4-obligations; C: partition/Steps1–3; D: pair-sum/regime)
> — blockers, ALL mapped: **R1** U⁹⁵→U⁹⁰ de-bump (capstone t7′-side; fits have ≥U⁵ spare; then Bcombine u³²⁰→u³⁰⁰/u³⁸⁰→u³⁶⁰,
> core S2/S3, combine concl U⁹⁰→U⁸⁵/U¹⁰⁵→U¹⁰⁰; prop_5_1 concl UNCHANGED-faithful). **R2** N-cap ℓ-scaling (hNlo/hNcap
> contradictory ∀pairs; fix: drop hLcap in Step4Fiber:522, cap=10⁵⁶ℓ₁³ℓ₂(ℓ₂−ℓ₁)U¹⁰/Ω⁸, C:=10⁵⁷, hnN chain 1→10⁵⁷ thru
> FibreCount/PackPerv/Hperv vs 10²⁰⁰ headroom). **R3** hv2 floor BUG (fact 25 `1.8·10¹³Δ²U⁵/Ω³ ≤ |v|` EXCEEDS global cap
> 3·10¹²ΔU⁵/Ω³ once Δ>5.6·10⁶ ⟸ hDeW; Δ² normalization wrong; trace true need in Step4WBridge hvlarge, fix + re-thread;
> V₂var := V₂ P S is the UNIQUE partition choice — Step-3 envelope exactly calibrated, Mbound(W,V₂PS)=10³⁰(Na+Nb+Nc)).
> **R3 RESOLVED BY TRACE (2026-06-10): hv2 := 10⁶⁰·V₂ P S** (writeup 1025–1028; NOT a Δ²→Δ literal fix; s₄ filter
> cutoff V₂var := 10⁶⁰·V₂ P S discharges facts 24+25 definitionally; empty-sliver at cap is harmless). RE-THREAD:
> (R3a) re-prove `sigma_d_deriv_ub`/`Sigma_closed_d_smoothing` (Step4Smooth:82,238) + `Sigma_closed_deriv_lb`
> (Step4Deriv:117) from `psum_resid_le_sharp`+hVcut+hb0lo, conclusions UNCHANGED; retire `psum_abs_ge`,
> `ptwo_div_quarter` (FALSE at V₂-scale for large H), `leading_scale_chain`, `leading_abs_ge`, Step4Confine:60
> (Step4Confinement supersedes). (R3b+R2 MERGED — both edit Step4Fiber): fiber-extract STEP-2a → err-domination
> route (needs errB ≤ ¼ ⟸ hHbig), N-cap ℓ-scaling (drop hLcap, 10⁵⁶ℓ₁³ℓ₂(ℓ₂−ℓ₁)U¹⁰/Ω⁸, C:=10⁵⁷), hv2-form in
> Fiber/FiberErr. (R3c, after R1+R2/R3b) thread fact25/hNlo/hnN(1→10⁵⁷) through RangeComplete→PackPerv/Hperv→
> FibreCount→Capstone. (R3-check) AUDIT Step-3 at V₊ := 10⁶⁰·V₂ P S — envelope 10³⁰-slack vs the ×10¹²⁰ stretch;
> Step-3 conclusion constant inflation rides to ∃C but the THEOREM's internal fit must absorb it.
> **R4** ✅ vval=0 ⊆ ℤ-eq bridge (`Prop51Bridges.lean:24`). **R5** ✅ dstar_ne_of_gap (`Prop51Bridges.lean:63`).
> **R6-scope** ✅ + **22/23 AUDIT** ✅: fact 23 dischargeable (bt_abs_bounds + dtilde_close, margin 10⁶⁶³; new
> `bzero_lo` sibling); fact 22 → ε-window `(1−10⁻⁹)D ≤ d̃ ≤ 2(1+10⁻⁹)D` (attempt-1 used [D/3,3D]; 77-pref real
> content 44.0000002 survives; touched-decls list in audit). **R3-check** ✅: Mbound LINEAR in V₂ ⟹ factor 10⁶⁰;
> Step-3 bumps hNenv 10³⁰→10⁹⁰, concl 10¹²¹→10²⁴⁰ (dispatched); V₁<V₊ by 10⁴⁰⁷.
> ⛔ **R8 BLOCKED — CRITICAL REGIME FINDING (2026-06-10):** prop_5_1's call site (Opt/StripAux:811→Strip:413→
> Global:155→DyadicAssembly:431) applies it at Ω ∈ [c₀G^{-1/4}U^{-3/4}, …) — INCLUDING Ω < 1 — and the optimization
> budget (18977g+15315u<2) permits G > U. So hΩ1 and hGU are FALSE there; hΩ1/hΩU/hUbig/hGU are threaded through
> the ENTIRE Step-4 chain. Other 14 ambient additions ARE dischargeable (one new X₀ threshold).
> **REGIME RULING ✅ (2026-06-10, writeup 398–407/808/1163–1199/2033–2063):** standing band = G^{-1/4}U^{-3/4} ≤ Ω ≤ U
> (paper line 406). prop_5_1 FAITHFUL pack: h1, hΔreg, hpop, **hbandLo : G^{-1/4}U^{-3/4} ≤ Ω** (REQUIRED, consumers
> hold the c₀-form at Strip:133/Global:163), hΩU, hG1, hU1, hUbig(→X₀:=max(X₀,10^{33/u}) at Main:24), hUH-threadable;
> CONCLUSION UNCHANGED (no X^{Cu} — Ω-powers explicit, feed strip x ≫ G¹⁷Ω⁻²⁶X^{O(u)} at 2061; §9 binds at the
> LOWER edge). **ELIMINATE hΩ1 + hGU from the live chain** (131 occurrences, only FOUR genuine uses):
> hΩ1 genuine = Step4FitEB:29 (fitEB_tail Ω-drops), Step4Capstone:88,297 (Ω⁸/Ω⁴) — repair: pay Ω⁻¹ ≤ G^{1/4}U^{3/4}
> per dropped power via hbandLo (paper's step-5 move 1171–1178; sympy: step-5-type fits have G-room 25/4≤7);
> collapse Ω¹³/Ω²⁷ fits need only hΩU (trivial at Ω<1). hGU genuine = Step23Delta:376–379 (10⁴⁶G≤U¹⁰ — FALSE at
> G≫U) + Step3FsumTight:293–295 (√G≤√U) — repair: bump intermediate monomials 1–2 G-powers (finals G⁹/G¹⁷ have ≥3
> G-units headroom). Vs_pin/Vbox carry-free. SWEEP PLAN: SWEEP-S4 (Step4* chain: drop hΩ1/hGU from statements,
> repair the 3 genuine uses, fix call sites), SWEEP-S23 (Step-2/3 + the 2 genuine G-fixes), SWEEP-S1, then REG-3 =
> R8-redo with the corrected pack (the other 14 additions + a-window + hHbig + hlogcap as before, minus hΩ1/hGU,
> plus hbandLo). NOTE: R3a/R6-build (in flight) may carry hΩ1/hGU in new statements — sweep catches them.
> **Ω-LEDGER ✅ (2026-06-10, all chains sympy-re-derived on the band):** ONE structural change — **EA cap-p3 FAILS
> t6′ at the edge (+10²³⁰) ⟹ RE-SLOT to t7′** (nets +3, slack 10⁻⁷⁸⁴; `step4_fit_cE_A` concl → `≤ 8C(H/Δ)(t6′+t7′)`,
> range_add5 sum accepts). Local repairs: keep-Ω-net rewrites in cubic_B(+16), fitEB_tail(m=11,14: Ω^{27−m}≤U^{27−m}),
> cC_F(+13); band-pays: EA-pad hmpad (Ω⁻⁴=GU³, thread G¹ into T1/T2 G-spare), EA-capFlat (Ω⁻⁶, keep full
> 10⁴⁵G¹²U⁶⁰ Δ³-floor — bare scalar FAILS by 10¹⁰⁸·⁵), EA-capP4 (Ω⁻¹¹, pay U⁹≤U²⁵ + keep ≥G³ of hDeW²),
> ev-bridge Capstone:88 (Ω⁻⁸≤G²U⁶, slack 10⁻⁴⁷ TIGHTEST). hband (1≤GU³Ω⁴) = the primitive replacing hΩ1
> (Capstone:297 derivation deleted). NO-CHANGE list in ledger. PASS-3 = this ledger verbatim.
> ✅ SWEEP-S23 + Step-3 band-pay DONE (2026-06-10): hΩ1/hGU eliminated from Steps 1–3 chain; genuine fixes:
> δ₂₃ G-bump (t2,t3→G⁵), Step3 √G-absorb, κNa-leg pay G·U⁴ via hband+hΩU. **LANDED t-exponents for Bcombine
> reconciliation (R7): t2,t3 @ G⁵; t4′ = (Δ²/H)G^{17/2}U^{103/2}/Ω⁸-form, t5′ = G⁸U³⁹/(√ΔΩ), Step-3 const
> 10²⁴⁰; Step-4 t6′ = G¹⁵U⁷⁵/(ΔΩ¹³), t7′ = Δ²G¹⁵U⁹⁰/(HΩ²⁷), const 2·10³¹³-pending-PASS-3 (EA-p3 re-slot ⟹
> fit_cE_A mixed-block).** **R6** window facts
> 13–23 producers MISSING (dStar sign/placement, d̃-interior, b₀≥B/2·10⁶ = popularity content). **R7** Wnat≈128·Wval
> route (hWcast 2-sided, hℓ2W→128W, Step-2/3 envelope bumps 10⁹⁶→10⁹⁸). **R8** prop_5_1 statement surgery (FAITHFUL
> per D: +a-window A/5≤a≤11A, ambient pack hG1..hUbig/hΩU/hGU/hUH/hband, hDeW, NEW hHbig ~10⁵⁵Δ²G^{5/2}U^{22.5}/Ω⁷≤H
> for hbud-term2, hlogcap). **R9** final per-pair compose → Ra_card_le_popular (B:=K·Bcombine, K rides to ∃C) →
> prop51_combine → prop_5_1. GOOD NEWS: V₁ seam verbatim-coherent; partition exhaustive; hsmall/Step-2-curv ✓;
> Step-1 ℓ-weight absorbable (t1·GΩ⁵/L ≤ t6′·U⁻⁴⁹ — D) or pair_weight_sum (C); hvmax via v_defect_le; hmem via
> phiv_distInt_from_witness (+hGU); constants benign (∃C absorbs 6·K·128²).
> PROCESS NOTE (6 agent deaths, same signature): a single agent turn exceeding 32k OUTPUT tokens kills the agent
> with zero disk output. Root cause is NOT file size — it's THINKING-TOKEN explosion on heavy monomial-substitution
> algebra (agents with few tool calls died before their first Write). Mitigations that work: (a) pre-collect every
> substituted monomial form in the prompt (no open-ended "do the bookkeeping"); (b) mandate sympy-via-Bash for all
> exponent arithmetic, never in-head; (c) ≤200 words prose per turn; (d) first Write within 4 actions, one decl per
> Edit (≤50 lines), build per decl; (e) half-scope units (≤4 lemmas). BAND succeeded only after split into
> BAND-1/2/3 with these rules.

> 2026-06-09 re-audit + math re-derivation. The §5 "endgame" was mis-mapped as wiring; a from-the-md analysis fixed
> the picture. Step 4: the green range skeleton was UNFAITHFUL by U⁵ (wrong v-count) — **NOW FIXED (GAP 4a green)** —
> and the `r`-count uses the writeup's `φ_v`+Lemma 4.1 route (md 1064–1088), NOT the `Σ_s` confinement detour. Step 2:
> the green counts are the WRONG (f-large) regime; the needed curvature lower bound (md 913) is TRACTABLE via
> f-elimination → an O(1) Wronskian (sympy-verified), NOT the "10⁸⁰ crux" earlier reported. See GAP list (4a✅,4b,4c,2a,2b,3).

Build verified GREEN 2026-06-09 (root + all §5 `Lower/` modules, 8381 jobs). The ONLY `sorry`
in `Lower/` is `prop_5_1` (`Lower/Prop51.lean:37`); all ~120 supporting `Lower/` lemmas are
proven and axiom-clean. (§7 `BoxSum`/`BoxPowerSums` stubs are separate and not §5.)

### §5 architecture (RESOLVED — do not relitigate)
- **Pair-sum ×W² convention is faithful.** `#ℛ_a = Σ_{(ℓ₁,ℓ₂)∈[1,W]²} #ℛ_a(ℓ₁,ℓ₂) + O(1)` is an
  EXACT consecutive-gap partition (route (c): sum actual per-pair counts, never #pairs×worst-case).
- **Only Step 1 (v=0) carries the `(1+GΩ⁵/(ℓ₁ℓ₂(ℓ₂−ℓ₁)))` = `(1+1/L)` excess.** Summed over pairs it is
  `≤ pair_weight_sum (S≤4W) · t1·GΩ⁵ ≤ 4·t1·W²` via `GΩ⁵ ≤ W`. Steps 2/3/4 have `|v|≥1` ⟹ no `1/V` blowup.
- **Markov term** `2(M−m)/W` is folded into `½#ℛ_a` by `Ra_card_le_popular` using popularity `R/W ≤ #ℛ_a` +
  `r≍R`. Do NOT add `R/W ≤ RHS` as a lemma (it is false).
- **Benign non-sharpnesses (carried, absorbed, NOT chased):** Step-1 `δ_unif` has `U¹⁵` not the writeup `U¹⁰`
  (absorbed: `(H/Δ²)G⁴U¹⁵/Ω² ≤ (H/Δ)·target1` with U-slack); Step-3 writeup monomials `t4,t5` (lines 1173–74) are
  too small by `U⁵/G` — CORRECTED to `t4',t5'` in `Bcombine`; the Lemma-4.2 `X^{o(1)}` log is absorbed via the
  largeness hypothesis `hlogcap` (faithful X-large condition), keeping `prop_5_1`'s conclusion clean.
- **`Bcombine`** (`Prop51Combine.lean:40`) = the 7 monomials `t1..t7` (with `t4',t5'`) times the common `H/Δ`
  prefix, written in substituted vars `g=G^¼, u=U^¼, dl=√Δ, ω=Ω` so the bracket is exactly the
  `step5_combine_core` LHS. The four Step per-pair counts must sum to `≤ Bcombine`.

### Endgame chain — capstones ALL PROVEN (green)
```
prop_5_1  ⟸  prop51_combine          (B ℓ₁ℓ₂ ≤ Bcombine  ⟹  prop_5_1 RHS)        ✅ Prop51Combine.lean:58
              ⟵ per-pair B ℓ₁ℓ₂  =  fiber_le_sum_ranges  (cover by 4 v-ranges)     ✅ Prop51Partition.lean:50
                  s₁ (v=0)        : Ra_step1_v0_perpair                            ✅ Step1Perpair.lean:28
                  s₂ (0<|v|≤V₁)   : ra_step2_range_le                              ✅ Prop51Step2.lean:31  (GAP 2 COMPLETE 2026-06-09)
                  s₃ (V₁<|v|≤V₂)  : ra_step3_range_le                              ✅ Prop51Step3.lean:42
                  s₄ (V₂<|v|)     : ra_step4_range_le'                             ⏳ 4a✅ faithful U⁷⁵/U⁹⁰; 4b/4c (φ_v route) TODO
              + Ra_card_le_popular ✅ RaPartition.lean:361   pair_weight_sum ✅ PairWeightSum.lean:106
              + step5_combine_core ✅ Step5Combine.lean:17   qval_round_le/ge ✅ Prop51Bridge.lean:37,201
```

### Per-step status (what is proven)
- **Step 1 (v=0) ✅ COMPLETE.** `Ra_step1_v0_perpair`: per-pair count `≤ 10⁵⁵·(R·δ_unif)·(1+GΩ⁵/(ℓ₁ℓ₂(ℓ₂−ℓ₁)))`
  with `δ_unif = 10⁶⁰(1/Δ)G³U¹⁵/Ω⁵`. (δ-vs-1 case split; full analytic chain via `Step1{Model,Witness,Discharge,…}`.)
- **Step 2 (0<|v|≤V₁) — counts done, range lemma NOT done.** `Ra_step2_count` (`Step2Count.lean:186`, per-`f`
  round(Qval)=f count) and `Ra_step2_fsum` (`Step2Fsum.lean:181`, f-summed over `|f|≤N`) are green. Curvature
  infra (`Step2Curvature{,2,3}`, `Step2Band{Base,Cal,Curv}`) all green. MISSING: `ra_step2_range_le` (GAP 2).
- **Step 3 (V₁<|v|≤V₂) ✅ COMPLETE.** `ra_step3_range_le` at the V₂ envelope (`Na+Nb+Nc`) + `hlogcap` → `t4',t5'`;
  uses `qval_round_le`/`qval_round_ge` (v→f bridge), `Ra_step3_fsum`, `step3_fsum_le_t4t5`.
- **Step 4 (V₂<|v|) — NON-FAITHFUL + crux unassembled (deeper than a wiring gap; verified 2026-06-09).** The
  `ra_step4_range_le'` skeleton (`Prop51Step4RangePrime.lean:27`) is green but its CONCLUSION is **U⁵ too weak**
  (`G¹⁵U⁸⁰`/`G¹⁵U⁹⁵`, → `U⁹⁰`/`U¹⁰⁵` after ×W²) vs the writeup-sharp per-pair `G¹⁴U⁷⁵/(ΔΩ¹³) + (Δ²/H)G¹⁴U⁹⁰/Ω²⁷`
  (writeup 1133/1157/1186, → `U⁸⁵`/`U¹⁰⁰` after ×W², math-auditor-verified). **Root cause (auditor):** `weight4'`
  (`Prop51Step4Prime.lean:53`) pairs the CRUDE total v-count `1+vc·√n` (∝+√n) instead of the SHARP near-integer band
  count `1+err·vc/√n` (∝−1/√n), with `err = G⁴U²⁰/Δ + (Δ⁴/H²)G⁵U⁴⁵/Ω¹⁴`, `vc=ΔΩ/√L`. Same `Rδ·err·vc` coefficient,
  but the s-sum flips `Σ_{n≤N} n^{+1/2}≍S^{3/2}` (Lean) → must be `Σ n^{−1/2}≍S^{1/2}` (writeup 1126), over-counting by
  exactly `S=G⁵U³⁵/Ω⁸ = G·U⁵`. Proven bricks that DO survive: `step4_fiber_extract` (`Step4Fiber.lean:289`, s-extraction,
  `|s|≤10¹¹¹G⁵U³⁵/Ω⁸`), `v_inversion`+`vlattice_count` (`Step4Enum.lean:263,360`), `step4_perv_count`/`_card_le`
  (`Step4PervCount.lean`), `phiv_distInt_from_witness`, `step4_v_count` (`Step4VCount.lean:30`), `sigma_s_confine`
  (`Step4Confinement.lean:228`), `Sigma_closed_parabola_sharp` (`Step4Parabola.lean`). TWO real blockers remain (below).
- **Step 2 (0<|v|≤V₁) — WRONG REGIME for the range (verified 2026-06-09).** `Ra_step2_count`/`Ra_step2_fsum`
  (`Step2Count.lean:186`, `Step2Fsum.lean:181`) are the **f-LARGE** regime — they carry a hard lower threshold
  `10⁹⁰·L ≤ |round(Qval)|` (`hflarge`, routed through `T₀=|f|D⁴/(XA)`). But the range `0<|v|≤V₁` is **curvature-
  dominated**: `|Qval|` is small with NO lower f-bound (`Qval_abs_ge_from_witness` needs `V₁<|v|`, = Step 3), so for
  `ℓ~W` the entire s₂ lies BELOW the threshold and `Ra_step2_fsum` bounds only ∅. The curvature-regime count does NOT
  exist in the tree. (`Step2Curvature{,2,3}`/`Step2Band{Base,Cal,Curv}` are internal BANDS pieces, not a standalone
  threshold-free count.)

### REMAINING GAPS — the actionable §5 worklist (CORRECTED 2026-06-09; harder than first mapped)
- **✅ GAP 4a — faithful `weight4'` + collapse rewrite — DONE 2026-06-09 (GREEN).** `weight4'`
  (`Prop51Step4Prime.lean:38`) now `(1+ev/√n)(b+dc/√n)` (sharp `+1/√n` band; `b=Rδ`, `ev=err·ΔΩ/√L`,
  `dc=(G⁴U¹⁵/Ω⁴)√L`); `ra_step4_ssum_collapse'` sums `Σn^{−1/2}≤2√N` → `16C·(H/Δ)(t6'+t7')`; `ra_step4_range_le'`
  (`Prop51Step4RangePrime.lean:25`) lands the FAITHFUL `16·K_V·K_C·C·(H/Δ)(G¹⁵U⁷⁵/(ΔΩ¹³)+Δ²G¹⁵U⁹⁰/(HΩ²⁷))` with the
  C-carrying s-cap; `vsum_le_weight4'` (`Step4FsumPrime.lean:39`) updated to the sharp `hVcol: 2ℓ₁Vbnd≤K_V·ev/√n`.
- **GAP 4b — Step-4 `r`-counting: USE THE WRITEUP'S `φ_v` ROUTE (md 1064–1088), not `Σ_s` confinement.** The earlier
  "smooth-slope confinement" framing was a self-inflicted DETOUR: md **1050, 1063** state explicitly you do NOT localize
  `r` through `Σ_s` (it is flat in `r`). The writeup counts positions `r` via the auxiliary phase `φ_v` (md **1064**)
  with **Lemma 4.1** (md **1085–1088**): `#{r:‖φ_v(r)‖≪δ} ≪ Rδ + δ/(T/R)`. `φ_v'` is non-degenerate because its two
  parts scale as `r⁰` and `r^{−9/4}` (md **1084**), so this is the SAME preimage tool already green for Steps 1 & 3
  (`phiv_distInt_from_witness` exists). So 4b ≈ reuse the Step-1/3 preimage machinery on `φ_v`; the fixed-`b₀`
  `sigma_s_confine` route is abandoned. (Old crux note `prop51-step4-smooth-confine` is superseded.)
- **GAP 4c — Step-4 v-band: kernel GREEN; remaining = the band-VARIATION `diam` budget [the big port, ~3000 ln].**
  ✅ `sqdiff_band_card_le` (`Step4SqDiff.lean:149`, GREEN): the TWO-POINT square-difference kernel — `F⊆ℓ₁⁻¹ℤ`, lower-pin
  `Vlo≤|v|`, pairwise `|v²−v'²|≤diam` ⟹ `#F ≤ 2 + 2ℓ₁·diam/Vlo` (the sharp `∝1/√|s|`). ✅ downstream all GREEN/sharp:
  `ra_step4_fsum'`/`ra_step4_range_le'`/`vsum_le_weight4'`/`ra_step4_ssum_collapse'`; suppliers `step4_fiber_extract`
  (sOf), `step4_perv_card_le`/`step4_perv_count` (the `φ_v` window count `Cv`). **REMAINING = produce the FIXED `diam ≍
  (E+err)/C` (|s|-independent)** — needs the band-VARIATION estimates attempt-2 lacks (it has only the per-point
  ABSOLUTE residual `Sigma_closed_parabola_sharp ≤10⁻²⁹|s|`, ∝|s| = the wall). **COMMITTEE-VETTED PLAN (3 auditors, 2026-06-09 — sound + complete; ADDITIVE route):** `diam=(2err+2E)/C`,
  `Cref=3ℓ₁ℓ₂(ℓ₂−ℓ₁)/(Δ²Ω²)` (r-INDEP, introduce it); `E` = SIZES (magnitudes at V_s) of cubic+p₂+leading-drift, each a
  NEGATIVE X-power `ρ` (cubic `≤|s|/Δ`, drift `≍|s|t²`, `t=Ω/H`). err-part→`S^{1/2}` (faithful U⁷⁵/U⁹⁰); E-part→`ρS^{3/2}
  ≤RHS/(G³U¹⁵)` (room, md 1135). Additive (NOT Lipschitz-difference) ⟹ avoids the v-r tie; the green collapse
  `ra_step4_ssum_collapse'` already has the `√n` slot for the E-part. **6 PITFALLS:** (1) do NOT feed
  `Sigma_closed_parabola_sharp` (`≤10⁻²⁹|s|`, ABSOLUTE coeff = the `|s|`-wall) into `hpair` — use TRUE X-power sizes;
  (2) `Cref` r-INDEP (attempt-2 only has per-r `C'`); (3) `C_r∝−b₀` ⟹ add a b₀-SIGN split per fibre (shell needs `0<C`);
  (4) recenter/Vbnd seam: kernel pins `Vlo≤|v|` & outputs card, `ra_step4_fsum'` wants `|vOf|≤Vbnd∝1/√n` ⟹ `vOf:=vval−v_ref(n)`,
  `Vbnd=diam/Vlo`, expose kernel confinement; (5) m²(=(ℓ₁v)²) vs v² units — ℓ₁² rescale; (6) keep (c) the faithful poly
  majorant. **PARALLEL UNITS (4 ∥, dispatched):** A=`Step4Cref` (Cref+flatness drift, port `Sigma.lean:40,78`), B=`Step4CubicSize`
  (cubic size, port `Sigma.lean:617`), P2=`Step4P2Size` (p₂ majorant, port `SquareDiff.lean:2117`), SHELL=`Step4SqDiffShell`
  (port `abs_sq_sub_le_of_perturbed_quadratic_shell` `SquareDiff.lean:211`, pure ℝ). → **D** difference-form
  `|Sigma_closed−Cref(ℓ₁v)²|≤E` + near-int (`step4_fiber_extract`/`Sigma_closed_near_int`) + b₀-sign → `diam`. → **E**
  recenter/Vbnd bridge → `ra_step4_fsum'` → `ra_step4_range_complete`. (Attempt-1 source sorry-free in `BoundsLargeDefectMd/`.)
- **GAP 2a — Step-2 — ✅ SLACK BANDS ENGINE DONE GREEN + TRIPLE-AUDITED 2026-06-09; count chain in progress.**
  `bands_count_mono_slack` (`Counting/Bands.lean:1350`, green, axiom-clean `[propext,Classical.choice,Quot.sound]`);
  `bands_count_mono` re-derived as `cu=cl=1` (unchanged stmt — §4 unaffected); 3 dead non-slack helpers removed
  (Bands.lean 1809→1572 ln). Audits: math/degradation ✓, Lean-proof ✓, build/wiring ✓ (full tree 8410 jobs green).
  This DISSOLVES the tight-calibration crux (count inflates `cu/cl`, absorbed by the collapse slack). Step-2 count chain
  — a de-risked GRIND (no walls left), ~7 mechanical pieces: ✅ GREEN: `step2_subset_count_cal_slack`, `phif_deriv_ub_allf`
  (all-f loose upper, `cu≈10⁴³`), `phif_curvature_lower_band` (`cl` floor) [Step2CountCurv.lean:89,210,357]. REMAINING:
  the φ″-MONOTONE-PIECE structure (slack engine still needs `hmono` per piece). VERIFIED feasible (sympy): `χ″>0` and
  `m=−χ″/ψ″` STRICTLY MONOTONE (`d/dr(χ″/ψ″)=−3(a+d̃)(35a⁸+…+12480d̃⁸)/(…)<0`, all-positive) ⟹ `φ_f''` has ≤1 zero
  ⟹ `K≤1`. But proving `m_actual` monotone (finite-diff phase) needs `χ‴`→`bt‴`, whose tight correction `|bt‴−d̃⁗|≤ℓ₁sup|d̃⁵|`
  needs the **5th derivative `d̃⁵`** (codebase stops at `d̃⁴`). So: ✅ `d̃⁵` (`DefectDeriv5`), ✅ `bt‴`+error (`DefectBt3`), ✅ `phif_iteratedDeriv3_eq` (φ‴ closed form, `Step2Phi3.lean:192`).
  ✅ `χ″>0` (`Step2ChiPos.lean:108` `chi_iteratedDeriv2_pos` + `Step2ChiPosAux.lean`; ⟹ `f≥0 ⟹ φ_f″>0`). ✅ φ″-STRUCTURE NOW COMPLETE (green): `welim2_poly` (`Step2D2ZeroAux.lean:48`, the W₂ identity), `phi3_poly`
  (`Step2Phi3Poly.lean:50`, φ‴ atom form), `smooth_W2_eq`+`w2_smooth_upper`+`w2_correction_abstract` (`Step2D2Zero*`),
  `phif_d2_ratio_strictAnti` (`Step2D2Zero.lean:386`, `m` StrictMono), `deriv_two_pieces_of_strictMono`
  (`Step2D2Split.lean:94`, abstract split), `phif_d2_zero_le_one` (`Step2D2Zero.lean:440`, the ≤2-piece split; needs
  `hsmall:10¹¹⁰·ℓ₁≤R`). ⏳ REMAINING = ONLY the assembly (IN PROGRESS): `Ra_step2_count_curv` (≤2-piece split via
  `phif_d2_zero_le_one` + `step2_subset_count_cal_slack` per piece) → `Ra_step2_fsum_curv` → `ra_step2_range_le`
  (`C₂≈10³⁶⁰` absorbs `cu/cl`; collapse to `t2,t3`). [Design recap:]
  Instead of sharpening the keystone to O(1) (hard), GENERALIZE `bands_count_mono` with slack `cu≥1` (on `hd1` upper) and
  `0<cl≤1` (on `hlower` lower): `hd1: |φ'|≤cu·T/N`, `hlower: cl·T/N≤|φ'|+N|φ''|`, `hactive: 4δ<cl²·T` (STRENGTHENED — the
  `bands_count_mono_low` curvature extraction `hF0_le` needs it), conclusion `≤112·(cu·cl⁻¹)·(N(δ+√(δ/T))+T+1)`
  (`g=cu·cl⁻¹`, `g(1,1)=1`; the Lean middle `mono_low_length` is a crude length bound → `cl⁻¹`, NOT the sharp `cl^{-1/2}`).
  Re-derive `bands_count_mono` as the `cu=cl=1` instance (unchanged stmt ⟹ §4 `NearCurve`/`Bands` unaffected). With the
  LOSSY keystone `cl=1/10⁷²` + a LOOSE all-f upper `cu≈10¹⁴`, `g≈10⁸⁶`, absorbed by the 7→3 collapse's ~10¹⁹⁰ slack
  (`10¹⁹⁰/10⁸⁶=10¹⁰⁴` headroom). So Step-2 needs only: the slack engine (in progress) + a LOOSE all-f `|φ_f'|` upper
  bound (no tightness) + an O(1) `φ_f''`-zero count (monotonicity) + the count chain — NO tight constants. [old tight-calib
  crux below is SUPERSEDED.] The active-bands
  `phif_curvature_lower_curv` (`Step2CurvCurv3.lean:95`: `(1/10⁷²)(ℓ₁ℓ₂(ℓ₂−ℓ₁)B²/D)/R ≤ |φ_f'|+R|φ_f''|`, all f; `hsmall:10⁷⁸ℓ₁≤R`)
  is PROVED via the f-elimination Wronskian route below — but it is NOT sufficient for the count. The bands engine
  (`step2_subset_count_cal`/`bands_count_mono`, `Step2Model.lean:96`/`Counting/Bands.lean:1118`) needs a SINGLE `T`
  with the TIGHT two-sided sandwich `sup|φ_f'| ≤ T/N ≤ inf(|φ_f'|+N|φ_f''|)` (absolute constants, `math_audit:100`).
  Blockers (verified 2026-06-09): (1) the keystone's lower constant `1/10⁷²` is LOSSY (from the 10⁶ `d̃'` slack² + 10²⁴
  lp-duality); the TRUE constant is O(1) (sympy: smooth Wronskian ratio ∈[2.5,2.8], `χ_s''/(χ_s/r²)∈[7.1,8.6]`), so it
  CAN be sharpened — but only via tight band-relative `d̃',d̃''` bounds (current `dtilde_*_ratio_band` give [1/64,64], the
  `DefectBandLocal` ones; the global `dtilde_d1_bounds` are 10⁶-loose). (2) the only `|φ_f'|` UPPER bound `phif_deriv_ub`
  is `10¹⁴·T₀/R` and `hflarge`-only — need an all-f O(1) upper. (3) over a full dyadic block `φ_f'` varies ~81×, so
  likely need sub-dyadic r-blocks. THE REAL REMAINING Step-2 work = the tight two-sided calibration (sharpen keystone to
  O(1) + all-f tight UB + small-f `φ_f''` sign + fine blocks), THEN `Ra_step2_count_curv → Ra_step2_fsum_curv →
  ra_step2_range_le`. A substantial sub-project, NOT one dispatch. (Fallback monotone-preimage count also needs small-f
  `φ_f''` sign, which `phif_iteratedDeriv2_sign` only gives f-large.) The active-bands
  engine needs `c·T_curv/R ≤ |φ_f'|+R|φ_f''|` for ALL `f` (the f-independent floor of md **913/917/919**). This is NOT
  a "10⁸⁰ crux" — that artifact came from bounding the two summands SEPARATELY (an adversarial `f≈−χ'/ψ'` nulls
  `|φ_f'|`). The clean route (4 pieces, each mirroring existing green code):
  **(i) f-elimination [algebra]:** `φ_f=fψ+χ` (`ψ=d̃⁴/(6Xa)`, `χ=2ℓ₁ℓ₂(ℓ₂−ℓ₁)b̃²/d̃`), so `ψ''φ_f'−ψ'φ_f''=ψ''χ'−ψ'χ''=−W`
  cancels `f`; `W:=ψ'χ''−ψ''χ'` is f-free. **(ii) LP duality:** `|φ_f'|+R|φ_f''| ≥ c·|W|/|ψ''|`. **(iii) |W| lower
  bound from closed forms:** smooth phase (`b̃→d̃'`) gives (sympy-EXACT) `χ_s''=2ℓ₁ℓ₂(ℓ₂−ℓ₁)(a+d̃)²(35a⁴+241a³d̃+680a²d̃²
  +894ad̃³+468d̃⁴)d̃/(16r⁴(a+2d̃)⁶)>0` (ratio `χ_s''/(χ_s/r²)∈[7.1,8.6]`) and `W_s=−(const)(a+d̃)³(5a⁴+44a³d̃+169a²d̃²
  +280ad̃³+180d̃⁴)d̃⁵/(r⁵(a+2d̃)⁷)` sign-definite (`|W_s|/(d̃⁴χ_s/r³)∈[2.5,2.8]`) — ALL-POSITIVE-coefficient, prove by
  `nlinarith` exactly like `dtilde_mono_leading`. **(iv) finite-difference:** `b̃` vs `d̃'` differ by `O(ℓ₁ d̃'')`, a
  relative `O(W/R)≪1` perturbation (REUSE the green Step-1 W/R-smallness); the `φ_f''` correction needs `d̃''''` —
  ✅ DONE (`DefectDeriv4.lean`: `dtilde_r_iteratedDeriv4`, `dtilde_d4_upper`, green 2026-06-09). Smooth margin survives. (NB the
  prior "indefinite bracket" report came from treating `b̃,b̃',b̃''` as INDEPENDENT in-band values + testing `ℓ₁≍R`;
  both wrong — they are differences of one smooth `d̃`, and `ℓ₁≪R`.) THEN `Ra_step2_count_curv` (`step2_subset_count`
  with `T:=max(T₀,T_curv)`) + `Ra_step2_fsum_curv` + collapse at the `Mbound(ℓ₁,V₁)` cap.
- **GAP 2b — Step-2 range lemma `ra_step2_range_le` [mechanical, after 2a].** Mirror `ra_step3_range_le` using
  `qval_round_le` (easy-half V₁ cap) + `Ra_step2_fsum_curv` → `Bcombine`'s `t2,t3`. `V₁=10⁶⁵·Δ³U¹⁰/(HΩ⁶)` (=Step-3 cut).
- **GAP 3 — `prop_5_1` discharge  [wiring; S–M].** After the Step-2/Step-4 gaps:
  - **F-thread the hyps**: derive every range-lemma hypothesis (`ha_lo/ha_hi`, `hUH`, `hUbig`, `hΩ1`, `hGU`,
    `hband`, `hlogcap`, `h1`) from `prop_5_1`'s hyps + the X-large hook `16777216 ≤ G·H·Ω³` (mirror §6 `prop_6_1`
    discharge at `Strip.lean:413`).
  - **dStar** `:= Classical.choose` from `RaWitness`; discharge `hdStar`/`hwin` window data from its spec.
  - **Choose `V₁,V₂,N`** consistently across ranges 2/3/4 (`V₁` as above; `V₂,N` from the `Mbound` f-caps,
    `Prop51Bridge.lean:30`).
  - **Step-1 `1/L` excess**: `B ℓ₁ℓ₂ ≰ Bcombine` UNIFORMLY (the s₁ term has the `(1+1/L)` factor). Split
    `B = (uniform Bcombine part) + (Step-1 excess t1·GΩ⁵/L)`; sum the excess via `pair_weight_sum (≤4W)` into
    `4·t1·W² ≤ RHS term1`. This extra term is NOT yet in `prop51_combine`'s `hBle` — needs a small generalization
    (or dominate Step-1 directly with `term1:=0` fed to `step5_combine_core`).
  - **Popularity**: discharge `Ra_card_le_popular`'s `2(M−m)/W+2 ≤ #ℛ_a/2` from `R/W ≤ #ℛ_a` + `r≍R`.
  - **Public exponents — RESOLVED (auditor 2026-06-09):** `prop_5_1`'s `U⁸⁵`/`U¹⁰⁰` (terms 2,3) ARE faithful and
    provable; they come purely from Step 4. The current green `prop51_combine` lands the WEAKER `U⁹⁰`/`U¹⁰⁵` ONLY because
    it consumes the unfaithful Step-4 monomials — once GAP 4a corrects `Bcombine`'s `t6,t7` to `G¹⁵U⁷⁵`/`G¹⁵U⁹⁰`,
    `prop51_combine`'s RHS must be re-derived to `U⁸⁵`/`U¹⁰⁰` (its internal `step5_combine_core` is unaffected; only the
    `t6,t7` inputs and the stated 3-term RHS change). The final `C` is a large absolute constant (absorbs the step
    constants `10^k`, `K_V·K_C`, `√C`), NOT 6 — generalize `prop51_combine` to `B ≤ K·Bcombine ⟹ 2ΣB ≤ 6K·RHS`.

- **TYPE II COMPLETE.** `typeII_card_bound` proven via: `NearCurveTypeII.lean` (witness-line grouping + factor-2
  cover + per-denominator re-index → `Σ_q (#lines·ν)`); `typeII_denom_le`/`typeII_nu_per_line`/`typeII_harmonic_sum`
  (mathlib `harmonic_le_one_add_log`); `typeII_lines_count_per_denom` = the `(q,slope,b)` enumeration
  (MVT slope-localization `|f'(ξ)−r/q| ≤ 2√(λ/q)` + denominator-q fraction count → `≤128(qNλ+1)` lines per q);
  `typeII_b_count_per_slope ≤ 6` (the convex-argmin b-localization via `typeII_shift_loc`); `typeII_double_sum`
  (the 4-crossterm + harmonic arithmetic, honest constant `16384`). The convex-argmin crux lives in NEW file
  `NearCurveConvexArc.lean` (`convex_arc_height_le_min`: a long strip-arc of a strongly-convex fn sits within
  `4/q` of its min; Fermat + `monotoneOn_deriv` + `mul_sub_le_image_sub_of_le_deriv` + tangent-slope, all cases).
  Constants: `typeII_card_bound = 16384`, `prop43_local C = 17280` (= 512 residual + 384 Type I + 16384 Type II).
### §6 (prop_6_1) BUILD PLAN — 2026-06-04 (auditor-verified, EASIEST of the 3 live stubs)
Difficulty: prop_6_1 (§6, easiest — one nearCurve_count call) < prop_5_1 (§5, Taylor Q-computation, v=0/v≠0, ΣW² pairs)
< prop_7_3 (§7, trivial wrapper but needs prop_7_1 = the hardest carry argument). Auditor PASS: the §6 curvature
`|f̃_a|,A|∂_a f̃_a|,A²|∂²_a f̃_a| ≍ F` is SHARP (sympy: leading consts 2,−5/2,45/8; `XA/D³=F` exactly). KEY: `R_a=Xa³/(d²(d+a)²)`
factors ⟹ `d̃_a(r)` has a CLOSED FORM (`d(d+a)=√(Xa³/r)` ⟹ `d̃=(−a+√(a²+4√(Xa³/r)))/2`) — NO IFT needed.
- (a) SHARED TOOLKIT `Structure/PhaseDeriv.lean` (362 ln, reused by §5/§7). **DONE/GREEN: Stage 1+2+3a.**
  - Stage 1 ✓: F_a/R_a exact d-derivatives (`Ffun_hasDerivAt_d`, `Ffun_hasDerivAt2_d`=`6X/d⁴−6X/(d+a)⁴`, `Rfun_hasDerivAt_d`
    =`−2Xa³(2d+a)/(d³(d+a)³)`), `Rfun_factor'`(`R_a=Xa³/(d²(d+a)²)`), `Ffun/Rfun_contDiffAt`, `Rfun_deriv_neg`(R'<0).
  - Stage 2 ✓: `dtilde X r a := (−a+√(a²+4√(Xa³/r)))/2`; `dtilde_pos`, `dtilde_prod`(`d̃(d̃+a)=√(Xa³/r)`), `dtilde_spec`
    (`Rfun X a (dtilde)=r`), `dtilde_contDiffAt`(ContDiff ℝ 2 in a). NO IFT — closed form.
  - Stage 3a ✓: `ftil_closed : Ffun X a (dtilde X r a) = r·√(a²+4√(Xa³/r))/a²` (clean closed phase), `ftil_eq_aff`,
    `dtilde_two_plus`, `ftil_contDiffAt`(ContDiff ℝ 2).
  - ⚠⚠ **BLOCKER FOUND + SCOPED (2026-06-04): `nearCurve_count`'s `1≤|F''|≤2` is TOO TIGHT for §6/§5/§7.** The phase
    `f̃∝a^{−5/4}` ⟹ `f̃''∝a^{−13/4}`, so curvature varies by `5^{13/4}≈187×` over the required `[1/2,5/2]` window — INTRINSIC,
    scale-invariant; a single `≤2` call is PROVABLY impossible (even one dyadic window gives `2^{13/4}≈9.5×`). The writeup's
    Prop 4.3 is `|F''|≍1` (ratio any ABSOLUTE constant); the §4 formalization over-normalized to `[1,2]`. **FIX (trial-verified
    CONTAINED, ~1 focused day): generalize the §4 engine `2λ→c_hi·λ` (bake `c_hi:=256` into `OnTypeIArc`'s split threshold
    `δ√(q/λ)→δ√(q/(c_hi·λ))`).** KEY: this keeps the off-line gap `=d(A)/24` curvature-INDEPENDENT (trial BUILT GREEN on
    `typeI_offLine_gap`+`offLine_spacing`); the `denomCutoff=1/64`/window `/48` reconciliation is curvature-free (re-tunes
    trivially); Type II shape PRESERVED (the split value is consumed in ONE place `typeII_slope_spread`, grows a constant only).
    ~30 mechanical `2*lam→c_hi*lam` edits + 3 routine re-derivations. Affects ALL of §5/§6/§7 — do ONCE.
    **✅ DONE 2026-06-04: c_hi=256 generalization COMPLETE + GREEN.** All 11 Geometry modules generalized bottom-up;
    `nearCurve_count` public hyps now `1≤|F''|≤256` on [1/2,5/2]; `#print axioms nearCurve_count` clean (no sorryAx); Geometry
    sorry-free. Split tightened to `δ√(q/(256λ))`; off-line gap stays `d(A)/24`; `properArc'_span_le` unchanged. New constants:
    `typeII_card_bound=109158400`, `prop43_local`/`nearCurve_count C=109159296` (huge but absolute, internal to ∃C, shape preserved).
    BONUS realized: Stage 3b now EASY — just `λ≤|f̃''|≤256λ` (ratio 187≤256), no tight [1,2] norm.
  - Stage 3b SPEC (sympy+numerics nailed): **`f̃''(a) = f̃(a)·κ₂(s)/a²` EXACT**, `κ₂(s)=(32s²+78s+45)/(16(s+1)²)`,
    `s=√(ar)/(4√X)`, `f̃''>0`, `κ₂∈[2,45/16]` decreasing. Clean relation `s=1/ρ`, `ρ=4√(Xa³/r)/a²`. Numerics: ratio
    max/min of f̃'' over `[A/2,5A/2]` is `≤187` for ALL `ρ≥1` (→5^{13/4} from below), so `≤256` with margin. Regime `ρ≥16`
    (i.e. `4√(Xa³/r)≥16a²` ⟺ `s≤1/16` ⟺ `X≥16ar`) ⟹ `κ₂∈[2.768,2.8125]` (ratio 1.016), `f̃/a²=2(X/r)^{1/4}a^{−13/4}√(1+1/ρ)`
    (ratio ≤192), product `≤195<256`. ALSO use the b=√a substitution `f̃=r√(b+c)b^{−5/2}`, `c=4√(X/r)` for cleaner differentiation.
  - ✅ Stage 3b DONE: `ftil_curv_bound` (PhaseCurv.lean:337) GREEN — `∃λ, λ≤f̃''≤256λ` on `[A/2,5A/2]` under regime `16a²≤4√(Xa³/r)`
    (ρ≥16); proven via exact `ftil_iteratedDeriv2 = r(4a⁴+39a²w+90w²)/(2a⁴D³)` + the 4th-power identity `Mfun⁴=r³X/a¹³` (NO rpow).
  - ⚠ BLOCKER 2 (regime threading, 2026-06-04): the assembly hit a REGIME GAP. `ftil_curv_bound` needs `ρ≥16` ⟺ `D/A≥4.23`
    (worst case r≤8R, a=5A/2: `320AR≤X` ⟺ `(D/A)⁴≥320`). The threaded `dblock_off_strip` hyp is only `2A≤D` (ρ≥~3.6). BUT the
    application ACTUALLY has `Ω≤U` ⟹ `D/A=H/Ω≥H/U=X^{(1−g)/5−u}` with exponent ≥0.19, and `X^{1/100}≥2²⁴` ⟹ `H/U≫5`. So `D≥5A`
    HOLDS — just not threaded. FIX (faithful — the §6 range has D/A≫1): add `5*S.A≤S.D` to `prop_6_1` (Regime.lean:19), thread via
    `prop_6_1_spec` (StripAux:670), DERIVE `5A≤D` in `dblock_off_strip` (Strip.lean ~:110) from `Ω≤U` + `H/U=X^{0.19+}≥5`. Then (b)
    assembly: 1(a) `dtilde_mem`∈[D,2D] from r≍R, 1(b) `dtilde_close` `|d−d̃|≤14(Δ/G)(Δ³/A³)` via R_a-MVT, `nearcurve_membership`
    (Capx=14 ⟹ ‖f̃‖≤780δ₀, δ₀=H/Δ²Ω²); 2 swap Σ_aΣ_r + `#U≤C·R`; 3 `nearCurve_count` per-r (N=A, T=A²λ, regime from `5A≤D`);
    4 rpow algebra → 3-term bound. nearcurve_membership/ftil_curv_bound/nearCurve_count(≤256)/dtilde all GREEN inputs.
  - ✅ unblock DONE: `5*S.A≤S.D` threaded into prop_6_1 + prop_6_1_spec + derived in dblock_off_strip (`five_U_le_H`), GREEN.
  - ⚠ BLOCKER 3 (membership/regime, 2026-06-04): the assembly's per-a reduction `{a:r∈RaOf a}⊆{a:‖f̃_a(r)‖≤780δ₀}` FAILS for
    small r / r=0. `nearcurve_membership` needs `d̃_a(r)=R_a⁻¹(r) ∈[D,2D]`, but `RaWitness`'s slack `14H/D` exceeds the endpoint gap
    `R_a(D)−R_a(2D)≍HGΩ³` in the LOW regime `HGΩ³<~224`, so d̃ falls outside [D,2D] (and for r→0, F_a' blows up — inclusion genuinely
    false; r=0∈ℕ also breaks ftil/nearCurve_count). Theorem is TRUE (application is HIGH regime `HGΩ³≫1` from band+X-large ⟹ r≍R, and
    𝒟 sparse), but the abstract statement doesn't encode it. FIX (3rd regime-threading, application provides all): (1) thread a HIGH-regime
    hyp into prop_6_1 — e.g. `C ≤ H*G*Ω³` (= `R*Δ`; derive in dblock_off_strip from band `Ω≥c₀G^{−1/4}U^{−3/4}` + X-large ⟹ `HGΩ³≥c₀³X^{0.177}≫224`),
    giving `r≥c·R>0` (no r=0) and slack `<R/16`; (2) LOOSEN `nearcurve_membership`'s domain hyp `D≤d̃≤2D` → `D/2≤d̃≤3D` (minor re-tune of
    the §3 bridge: |d−d̃|≤14Δ/(GΩ³)≤D when HGΩ³≥14, so d̃∈[D−ε,2D+ε]⊆[D/2,3D]; derivative bound 52XA/D⁴ over the wider window only grows the const).
    Then the (b) assembly (reduction+swap+nearCurve_count+rpow, all sub-pieces verified sound: the 5 rpow product identities sympy-confirmed,
    the `9R≤X/(40A)` curvature-regime from `5A≤D` sound, the membership pipeline works for r≍R). RECOMMEND a math-auditor pass to pin the exact
    high-regime constant + confirm the producer (Fiber.lean) gives r≍R, then thread + loosen + assemble.
  - ✅ BLOCKER 3 FIXED (route A): RaWitness strengthened `∧ R/72≤r≤16R` (producer Fiber.lean threads existing `hrStar_band`);
    nearcurve_membership domain `[D,2D]→[D/2,3D]` (const 52→832); regime bumped `5A≤D→10A≤D`; floor `500≤GHΩ³` threaded
    (`ghΩ3_ge_500`); scalars `1≤X`,`0<u` threaded. ALL GREEN.
  - §6 ASSEMBLY ~90% (2026-06-05): `Squarefree/Upper/Regime6.lean` + `Regime6Count.lean` (~500 ln each) GREEN. DONE sub-lemmas:
    `prop6_curv_regime`, `ftil_dtilde_window`(d̃∈[D/2,3D], uses the floor), `ftil_dtilde_close`(Capx=12096), `ftil_near_integer`,
    the GLOBAL C² extension `ftil_ext`(=bump·ftil via `ContDiffBump`; `ftil_ext_contDiff`/`_eq`/`_deriv2_eq`), `prop6_count_per_r`
    (nearCurve_count applied to ftil_ext, T≍F). The 4 rpow product identities + the swap + log≤X^{Cu} are math-verified.
  - ⚠ BLOCKER 4 = the genuine §6 SIDE CONDITION (math_audit-flagged): `prop6_count_per_r` needs `hone: 1 < prop6ScaleLo·S.F`
    (nearCurve_count's `1<T`, `T≍F=H²GΩ/Δ²`). F can be `≤1` (Δ large, Ω small ⟹ F=GΩ<1 since Ω≥c₀G^{−1/4}U^{−3/4} can be <1).
    So §6 needs the Prop 4.3 `T>1` side condition — verified (writeup 1904 analogue for §7's T₁>1) only from the UNRESOLVED-STRIP
    scale constraints in the §8/§9 spine (dblock_off_strip's disjunction `hdisj`), a different layer. REMAINING: either (a) derive
    `F>1` in dblock_off_strip from `hdisj`+strip constraints + thread `1<…·F` into prop_6_1, OR (b) case-split `F>1`(main via
    prop6_count_per_r) / `F≤1`(trivial #≤(A+1)(16R+1), needs `A²≤H·X^{Cu}` — also a spine constraint), then the swap+rpow+log
    assembly closes prop_6_1. This is the deep spine-connected piece; the analytic §6 machinery is all DONE.
    f̃=r·√(√a+4√(X/r))/a^{5/4} (set p=√(X/r)); in the regime `4p≫√a` (i.e. `t=a/d̃≍A/D=Ω/H≪1`) the curvature const
    →45/8 (leading), slowly varying ⟹ ratio≤2 over `[A/2,5A/2]` (NEEDS the quantitative `t₀=A/D` small bound, parameter-heavy).
    ⚠ Needs an auditor pass to pin the EXACT two-sided statement + regime conditions + whether to subdivide `[1/2,5/2]` into O(1) pieces
    (writeup 1854 "finite local version") before building. Also need `dtilde∈[D,2D]` from `r≍R` (scale-dependent, for nearcurve_membership).
- (b) prop_6_1: reduction `#ℛ_a ≤ #{r:‖f̃_a‖≪δ}` via EXISTING `nearcurve_membership` (witness-driven, δ=x/Ω²); swap Σ_a Σ_r;
  apply `nearCurve_count` IN `a` (rescale `a↦f̃_a` to N=A,T=F, normalize `≍F→1≤|F''|≤2` on [1/2,5/2]); rpow algebra → the
  3-term bound (`xGΩ²+x^{2/3}G^{4/3}Ω^{11/3}+H^{-1/2}G^{1/2}Ω^{5/2}`, all sympy-verified exact). `dStar`(Fiber)=discrete d*_a
  ≠ smooth d̃_a — keep decoupled. `nearcurve_membership` needs `d̃_a∈[D,2D]`. Capx from Prop 3.2 (benign, inflates C only).
- §4 STATEMENTS AUDITED (2026-06-04): all 4 §4 public statements faithful + their downstream applications verified.
  `nearCurve_count` fits BOTH writeup uses exactly — §6 `prop_6_1` (`N=A,T=F`, writeup 1261) and §7 `prop_7_*`
  (`N=R,T=T_{ρ,q}`, writeup 1873–1934, which literally normalizes to `1≤|F''|≤2` on the wider interval = the Lean
  `[1/2,5/2]`; conclusion incl. log matches). `bands_count` fits §7 (writeup 1748–1771; strictly stronger — drops
  upper `|φ''|`; bakes constant-1 scale + `I⊆[N,3N]`). `preimage_count` (Lemma 4.1/2.3) is LIVE — `FourthDeriv` §2
  app sound. `prop43_local` faithful (benign `1≤N²λ` floor auto-satisfied). Orphans' only future work = `≪/≍`→
  baked-constant rescaling (writeup carries it out). NO vacuous/weakened statements, NO misapplications.
- CLEANUP: `NearCurveTypeII.lean` SPLIT (2026-06-04) into 5 files — Base(171)/Slope(226)/BCount(442)/DoubleSum(222)/
  TypeII(337), linear DAG, green, `nearCurve_count` still sorry-free. ⚠ REMAINING oversized (pre-existing Type I
  debt): `NearCurveGreedy.lean`(1199), `NearCurveStrip.lean`(637), `NearCurveAux.lean`(500), `NearCurveResidual.lean`(468),
  `NearCurveTypeI.lean`(464) — split when convenient (not blocking).
- (historical) **§4 TYPE I COMPLETE (2026-06-04).** The entire Bombieri–Pila greedy packing (hardest combinatorial core):
- **§4: Lemma 4.2 `bands_count` FULLY PROVEN** (`#print axioms` clean). **Prop 4.3 `nearCurve_count` PROVEN** ⟸
  `prop43_local` PROVEN (substitution) ⟸ {residual ✓, **TYPE I ✓ (DONE — `typeI_card_bound`/`typeI_arc_sum`
  carry NO sorryAx)**, `typeII_card_bound` (NearCurveResidual:396 — the (q,slope) harmonic-sum log crux, the LAST §4 stub)}.
- **TYPE I FAITHFUL REDESIGN — COMPLETE.** The full line-keyed greedy: (1) un-windowed strip-component machinery
  `NearCurveStrip.lean` (sorry-free: `lineRes_convex_or_concave`, `properArc'`, `properArc'_span_le`,
  `properArc'_continuous_strip`, `properArc'_side_monotone` via curvature-keyed split, `mem_properArc'_of_between`);
  (2) component-span classification `NearCurveTypeIClass.lean` (`typeISet` keyed on `properHi'−properLo' ≤ δ√(q/λ)`,
  `properArc'_span_typeI` definitional) — needed a DAG split `Proof→TypeI→Strip→TypeIClass→Packing→Greedy→Residual`;
  (3) line-keyed greedy (`witnessKey = witnessLine`, `properArc_directed_gap` CASE-A-only off-line);
  (4) the shared-base corner closed via re-anchor at the first off-line point of `A_k` (`second_point_mem_properArc'`,
  residue-contiguity from `δ<1/2` ⟹ `round(f)=P`), with `δ<1/2` obtained by a trivial case split in `typeI_card_bound`
  (`δ≥1/2` ⟹ `#typeISet ≤ N+2 ≤ C(Nδ+1)`). KEY THRESHOLD FIX: `denomCutoff` lowered `1/4 → 1/64` (faithful: writeup
  "c sufficiently small") so `q ≤ d(A)/64` is absorbable; packing window `dens/48 < dens/24` gap leaves the slack.
  All the genuine §4 ANALYSIS is PROVEN (§4.1 `preimage_count`; bridge; div-diff MVT; non-collinear spacing; residue
  counting; `majorArc_length_bound`; off-line spacing; convexity strip-components; residual `residual_card_bound`).
  NEW CONSTANTS: `denomCutoff=1/64`, `dspan` δ-floor `1/(64δ)`, `residual_card_bound=512`, Type I total `384`,
  `prop43_local C=904`.
- **§5/§6/§7 (UNCHANGED, faithful stubs)**: `prop_5_1`, `prop_6_1`, `prop_7_3` take `RaWitness` (consumed by the
  proved §8/§9 spine via `RaWitness`); `prop_7_1` orphan/flagged-deferred (needs §7 Carry.lean infra).

---
### (historical) STATUS — 2026-06-03: §4–7 STATEMENTS NOW ALL FAITHFUL (audit + fix COMPLETE); 6 stubs = honest frontier

**RESOLVED.** The 2026-06-03 audit found 4 of 6 §4–7 stubs FALSE/UNFAITHFUL; all are now FIXED and
`lake build Squarefree` is GREEN with `#print axioms theorem_10_1 = [propext, sorryAx, Classical.choice,
Quot.sound]` (no new axioms). The 6 remaining `sorry -- STUB:` are now ALL FAITHFUL (provable-in-principle
hard analysis), not false. What was done:
- §4: `bands_count` `.Finite`→`.ncard≤K`+`(K+1)` (audited); `nearCurve_count` confirmed faithful (no change).
- BRIDGE PROVEN (no stub): `inDa_distInt_Ffun` (B1, ADecompAux.lean:49) + `nearcurve_membership` (B2,
  NearCurveBridge.lean:80, C=52). The §3→§6/7 d-side→r-side near-curve machinery.
- `prop_3_2_fiber_dStar` extended to expose `RaWitness` (DaSpacing.lean — the d-side structural bundle
  `∃ d, inDa ∧ band ∧ |Rfun(d)−r|≤14H/D`), threaded through `dblock_le_sum_Ra`→`prop_*_spec`→consumers.
- `prop_6_1`, `prop_7_3`, `prop_5_1` RESTATED to take `∀ r∈Ra, RaWitness P S a r` (faithful structural
  hyp); `prop_5_1` also de-vacuified its 3 `∃c` regime/popularity hyps → bare inequalities (c=1; consumer
  has slack to strengthen if §5's eventual proof needs a larger regime constant). All conclusions UNCHANGED.
  All 3 STILL SORRIED (faithful — their internal §5/§6/§7 proofs are the remaining frontier).
- `prop_7_1` (orphan) FLAGGED-DEFERRED in BoxSum.lean: faithful form needs §7 phase infra (Carry.lean).

**Remaining frontier = the actual §4–7 PROOFS** (now honest): bands_count, nearCurve_count (§4 engine);
prop_5_1 (defect bookkeeping); prop_6_1 (build f̃_a from RaWitness via `nearcurve_membership`, curvature ≍F,
Prop 4.3 in a); prop_7_3 (g_j machinery + Prop 7.1); prop_7_1 (§7 crux, needs Carry.lean infra first).

### §4 ROADMAP (Opus math-auditor verified 2026-06-03 — route SOUND, matches md + attempt-1's finished decomp)
Prop 4.3 (`nearCurve_count`) is the scariest classical input (Bombieri–Pila points-near-curve), Lemma 4.2
(`bands_count`) is the separate band-counter. Both FAITHFUL as stated; `preimage_count` (Lemma 4.1/2.3) is
PROVEN (reuse, explicit constant `(V+2δ+1)(2δ/F+1)`). Two md soft-spots, both benign w/ clean repairs:
(i) Type II "+1" slope absorption needs `√(δ/λ)≥1` (true when Type II nonempty); (ii) Lemma 4.2's stray
`log` is a dyadic-exposition artifact — formalize the log-free `+T+1` via a **fixed 5-band** split (thresholds
`√(δT)/N, √T/N, T/(4N)`), NOT a log-many dyadic one. `f=TF(·/N)`, `λ=T/N²`.
- **Lemma 4.2** (independent, simpler): split into `(K+1)` constant-sign-φ'' pieces (φ' monotone), fixed 5
  bands by `|φ'|`, per band: `|band|` from `|φ''|` lower bd + `preimage_count`. → log-free `(K+1)(N(δ+√(δ/T))+T+1)`.
- **Prop 4.3 tiers** (each = one lean-prover unit, dependency order):
  - T0: `tripleDet_int` (`u=l₀(n₂−n₁)+l₁(n₀−n₂)+l₂(n₁−n₀)∈ℤ`, `=0⟺collinear`); **[DONE]**
    `secondDividedDiff_eq_half_secondDeriv` (`NearCurveAux.lean:20`, GREEN — 2nd divided-diff MVT `f[x₀,x₁,x₂]
    =iteratedDeriv 2 f ξ/2` via Rolle×3, was HARDEST #1/main mathlib-gap); `noncollinear_span_lower`
    (`|u|≥1 ⇒ 1≪λL³+δL ⇒ L≫min(λ^{-1/3},δ^{-1})`, builds on the MVT).
  - T1: **[DONE]** `majorArc_length_bound` (`Λlo·L²≤16δ`, NearCurveAux:313, central 2nd-diff via the MVT);
    **[DONE]** `residueClass_card_le` (`ν≤(hi-lo)/q+1`, NearCurveAux:371, needs `lo≤hi`) + `residueClass_denom_le`
    (`q≤hi-lo` from ≥2 pts, NearCurveAux:468) = the `ν≪L/q`,`q≪L` lattice-on-line facts. TODO `≤2 components`
    (reformulate COMBINATORIALLY, not topological — convex g'' const sign).
  - T2 (regimes — needs the combinatorial-assembly ENCODING designed first): `residual_card_bound`
    (5-consecutive trichotomy → `Nλ^{1/3}+Nδ+1`) [HARDEST #2]; `offLine_spacing_lower`; `typeI_card_bound`
    (disjoint intervals → `Nδ+1`); `typeII_card_bound` (convex localize + `O(qNλ+1)` slopes + harmonic
    `Σ1/q~log` → `Nδ+√(δ/λ)log(2+√(δ/λ))+1`) [HARDEST #3]; `combine_prop43` (`#S≤#S_res+2(I+II)`, back-sub `λ=T/N²`).
  - **STATUS 2026-06-03**: T0 done (`secondDividedDiff_eq_half_secondDeriv`, `noncollinear_span_lower`), T1 mostly
    done (5 primitives green in `Geometry/NearCurveAux.lean`, now 500 ln — SPLIT into analytic+combinatorial files
    soon). **`nearCurve_count` NOW PROVED** (real, no sorry) ⟸ NEW core stub `prop43_local` (`NearCurve.lean:21`,
    the λ-normalized count: `#{n∈[N,2N]:‖f(n)‖≤δ} ≤ C(Nλ^{1/3}+Nδ+√(δ/λ)log(2+√(δ/λ))+1)` given `|f''|∈[λ,2λ]` on
    `[N/2,5N/2]`). Substitution `f=TF(·/N), λ=T/N²` (chain rule + rpow/sqrt RHS algebra) DONE green. So the §4.3
    sorry is now `STUB: prop43_local`, the Bombieri–Pila major-arc core.
    NEXT: decompose `prop43_local` → residual + TypeI + TypeII + combine. mathlib GAPS confirmed+built:
    divided-diff MVT ✓, residue-class count ✓.
  - **⚠ HOLLOW-SKELETON LESSON (2026-06-03)**: a first `prop43_local` skeleton reduced it to 3 regime stubs via
    `opaque OnMajorArc`/`OnTypeI` predicates — REJECTED + reverted. An `opaque` (uninterpreted) predicate carries
    NO information, so `#(S.filter ¬OnMajorArc) ≤ C(Nλ^{1/3}+Nδ+1)` is UNPROVABLE (the set could be all of `S`).
    The build was green but the stubs were undischargeable = negative progress (1 honest stub → 3 unprovable).
    RULE: a decomposition's predicates/sets must be **CONCRETE `def`s**, never `opaque`, or the sub-stubs are
    hollow. The real encoding MUST define "on a major arc of denom ≤ c/δ" concretely WITH the connected-arc
    structure (a maximal collinear run on a small-denom line) — the connectedness is essential: a weaker
    "∃ collinear small-denom triple" def makes the residual bound provable but blows up the major set so Type I/II
    become unprovable. Concrete defs `nearSet`/`latticeY`/`collinearDet` kept in `NearCurveProof.lean`.
    NEXT real step: study attempt-1's CONCRETE `curveMajorArcDatumLocal` encoding (structure-glance) → design a
    correct concrete major-arc predicate → residual bound first (uses `noncollinear_span_lower`), then I/II.
    attempt-1 encoding (concrete, GOOD): `structure curveMajorArcDatumLocal { slope : Rat, shift : Int }` (line
    `y=slope·x+shift/slope.den`, `q=slope.den`); pt-on-line = `slope.den·ℓ_n = slope.num·n+shift`. ~4000 ln in
    `NearCurveOn.lean` + Residual/TypeI/TypeII files — the project's LARGEST/HARDEST piece.
  - **Lemma 4.2 `bands_count` PROVED ⟸ `bands_count_active`** (Bands.lean:252, the `4δ<T` regime, the band
    ASSEMBLY). Engine GREEN: `bands_count_trivial` (T≤4δ done), MVT helpers, `band_count_uniform` (per-band via
    `preimage_count`), `curvature_lower`, `card_do_eq_card_int` bridge. `bands_count_active` = split `[a,b]` into
    `≤K+1` const-sign-φ'' (monotone-φ') pieces, fixed `|φ'|`-bands (`√(δT)/N,√T/N,T/(4N)`), apply engine, sum
    (log-free). LARGE (attempt-1 ≈6500 ln) but all analytic inputs proven.
  - **§4 HONEST STATE 2026-06-03**: `nearCurve_count` PROVED ⟸ `prop43_local`; `bands_count` PROVED ⟸
    `bands_count_active`. 2 remaining §4 stubs, both CONCRETE+provable-in-principle, both ENORMOUS
    (Bombieri–Pila major-arc ~4000 ln; band assembly ~6500 ln in attempt-1). All primitives/engine/reductions GREEN.
  - **⚠ BANDS BLOCKER (2026-06-03), resolved-in-principle**: the per-band engine `band_count_uniform`
    (=`preimage_count`'s MULTIPLICATIVE `(V+2δ+1)(2δ/F+1)`) is TOO LOSSY — summed over `|φ'|`-bands it OVERCOUNTS
    unboundedly (ratio ↑ with `T/δ`); dyadic reintroduces the `log(T/δ)` (math_audit's flagged non-sharpness).
    Log-free IS provable (attempt-1 = `512(K1+K2+1)S`, no log, via per-piece `pieceFiber_count_smallT_good≤256S`).
    FIX: build a SHARP per-MONOTONE-PIECE count (NOT band-by-band) = attempt-1's
    `lemma_4_1_monotone_near_integer_count_of_deriv_pos` (DerivativeBandsCore.lean:336/511): on a monotone-`φ'`
    region, GROUP near-integer pts (consecutive same-level pts `≤2δ/F` apart, `L=⌈2δ/F⌉`; level-crossings cost
    variation `V`) ⟹ whole-region count log-free. NEXT: build that sharp monotone count (new infra beyond
    `preimage_count`), then `bands_count_active` = assemble ≤K+1 monotone pieces. `count_split` (breakpoint
    sub-additivity) already proven in Bands.lean:242.
  - **BANDS PROGRESS 2026-06-03**: `bands_count` PROVED ⟸ `bands_count_active` PROVED ⟸ {`bands_count_mono`,
    `bands_count_active_split`} (both CONCRETE, numerically-verified-TRUE stubs). Proven green: `mono_low_length`
    (Low-band curvature length `t-s ≤ 4N²F₀/T ≤ 4N√(δ/T)`). REFINED diagnosis (prev "high/low decouple" was
    partly wrong): the genuine log-elimination is the **MID band `√(δT)/N ≤ |φ'| < 4δ`** (writeup's `e^K δN/T ≪
    N√(δ/T)` step) — the real deep ~6500-ln content. Low = `mono_low_length`+`band_count_uniform(F=4δ)` (easy),
    High `|φ'|≥4δ` easy. REMAINING: `bands_count_mono` (per-piece `≤8S`, the Mid-band dyadic log-elim) +
    `bands_count_active_split` (the `≤K+1` const-sign-φ'' piece split + sum via `count_split`).
  - **BANDS PROGRESS 2 (2026-06-03)**: `bands_count_active_split` now PROVEN ⟸ `count_le_of_chain` (PROVEN —
    chain-induction over breakpoint List via `count_split`) + `exists_mono_piece_breakpoints` (concrete stub:
    `∃ L:List ℝ, L.length≤K ∧ IsChain (piece monotone-or-antitone) (a::L++[b])` — sort the `≤K` φ''-zeros, IVT
    for const-sign per gap). So `bands_count` now reduces to JUST 2 stubs: `bands_count_mono` (Mid-band, DEEP)
    + `exists_mono_piece_breakpoints` (MECHANICAL — finite-set sort + IVT).
  - **BANDS PROGRESS 3 (2026-06-03)**: `exists_mono_piece_breakpoints` now PROVEN (const_sign_of_no_zero via IVT,
    mono_or_anti_of_no_zero, geo_chain_of_sorted). Faithfulness fix: added `Set.Finite` on the φ''-zero set
    (threaded through `bands_count_active_split`/`_active`/public `bands_count`) — `ncard≤K` alone doesn't imply
    finite (infinite→ncard 0); `Finite ∧ ncard≤K` ⟺ "≤K zeros" = md's "O(1) zeros", FAITHFUL, public bound
    (C=64, log-free) unchanged, no real consumer. **`bands_count` NOW REDUCES TO A SINGLE STUB:
    `bands_count_mono`** (Bands.lean:340, per-monotone-piece `≤8(N(δ+√(δ/T))+T+1)`, the Mid-band `√(δT)/N≤|φ'|<4δ`
    dyadic log-elimination — the genuine ~6500-ln deep core). All engine/breakpoint/chain machinery GREEN.
  - **BANDS PROGRESS 4 (2026-06-03)**: `bands_count_mono` now PROVEN ⟸ single stub `bands_count_mono_band`.
    Proven green: `bands_count_mono_low` (LOW `≤4N√(δ/T)+1`), `bands_count_mono_high` (HIGH `|φ'|≥4δ`, ≤1 pt/level
    via `2δ/F<1`), `exists_crossing`/`mono_threshold_split`/`mono_abs_threshold_split` (IVT V-shape sign-split),
    `bands_count_mono_of_split` (assembly). REMAINING SINGLE CRUX = `bands_count_mono_band` (Bands.lean:392): for
    a single-sign-φ' band `√(δT)/N≤|φ'|≤T/N`, `count ≤ N√(δ/T)+2Nδ+4T+3` — the DYADIC banding `[2^j√(δT)/N,
    2^{j+1}…)` + geometric fiber sum + `log₂(4N√(δ/T))≤C(N√(δ/T)+1)` absorption (`Real.log_le_self`). HIGH part
    dischargeable by proven `bands_count_mono_high`. **`bands_count` = 1 narrow stub.** (Bands.lean now 1000 ln —
    SPLIT crossing-helpers into `Counting/MonoSplit.lean` later.) **§4 = exactly 2 core stubs: `bands_count_mono_band`
    + `prop43_local`.**
  - **BANDS PROGRESS 5 (2026-06-03)**: `bands_count_mono_band` now PROVEN (4δ-split via `exists_crossing` on
    `|φ'|`: HIGH `[4δ,T/N]` discharged by proven `bands_count_mono_high` ⟹ `≤3T+3δ+3/2`; MID delegated). Added
    `hmono` hyp threaded from call sites; `hcont_abs`/`abs_deriv_mono_or_anti` helpers. **Lemma 4.2 now = SINGLE
    stub `bands_count_mono_mid`** (Bands.lean:423): `√(δT)/N≤|φ'|≤4δ`, mono/anti, const sign, `[N,3N]`, `4δ<T`
    ⟹ `count ≤ N√(δ/T)+2Nδ+1`. The pure DYADIC band-sum `[2^j√(δT)/N,2^{j+1}…)` + `(J+1)(2δ+1)` log term,
    `⌈log₂(4N√(δ/T))⌉≤C(N√(δ/T)+1)` absorption. NOTE: `2Nδ` is TIGHT — cross term needs `ΣG_j len_j≤2·var≤4T`
    (not `len≤2N`). **§4 = exactly 2 core stubs: `bands_count_mono_mid` + `prop43_local`.**
  - **✅✅ LEMMA 4.2 (`bands_count`) FULLY PROVEN 2026-06-03** — `bands_count_mono_mid` closed (the dyadic
    `bands_dyadic_sum` recursion peeling the bottom band so the geometric fiber sum telescopes; `J` via
    `Nat.find`+`Nat.lt_two_pow_self`; log absorption `J+1 ≤ 12N√(δ/T)` using the non-empty-band floor
    `N√(δ/T)≥1/4`). Constant loosened + re-threaded: MID `≤16N√(δ/T)+56Nδ+1`, public `bands_count` `C: 64→112`,
    bound SHAPE `(N(δ+√(δ/T))+T+1)` UNCHANGED. VERIFIED: `#print axioms bands_count = [propext, Classical.choice,
    Quot.sound]` — NO sorryAx. (Bands.lean now ~1050 ln — split later.) **§4 NOW = SINGLE STUB `prop43_local`.**
  - **PROP 4.3 PROGRESS 2026-06-03**: CONCRETE major-arc encoding built (NO opaque) + RESIDUAL bound PROVEN.
    `NearCurveProof.lean` (concrete): `nearSet` (ℤ-form), `latticeY`, `collinearDet`, `structure MajorLine
    {slope:ℚ,shift:ℤ}`, `OnLine` (`q·ℓ_n=p·n+shift`)+`OnLine.sub_dvd`, `denomCutoff=1/4`, `OnMajorArc` (= MIDDLE
    of a small-denom collinear near-set triple), `residual/major/typeI/typeIISet` (concrete filters), real
    partitions `nearSet_card_split`/`majorSet_card_split`. `NearCurveResidual.lean`: `residual_card_bound` PROVEN
    (writeup 578, via `residual_five_span` trichotomy: non-collinear→`noncollinear_span_lower`; large-denom→
    `q`-separation via `OnLine.sub_dvd`; small-denom→`OnMajorArc` contradiction) + `prop43_local` ASSEMBLED via
    the 2 partitions. `NearCurveSpacing.lean`: `card_le_of_five_span` (5-span→card). `prop43_local` PROVED ⟸ 3
    CONCRETE stubs: `collinear_five_on_majorLine` (5 collinear pts → common MajorLine, rational reconstruction),
    `typeI_card_bound` (`≤8(Nδ+1)`), `typeII_card_bound` (`≤8(Nδ+√(δ/λ)log(2+√(δ/λ))+1)`). ⚠ NEXT-VERIFY: TypeI/II
    bounds' TRUTH for the triple-middle `OnMajorArc` def (the connectedness question — if the major set is too big
    a def refinement may be needed; concrete stubs so discoverable when proving, unlike the prior opaque trap).
    Residual regime (`Nλ^{1/3}+Nδ`) DONE. **§4 = bands ✅ + prop43_local ⟸ 3 concrete stubs (the §4.3 Type I/II
    counts + 1 geometry lemma).**
  - **PROP 4.3 PROGRESS 2 (2026-06-03)**: AUDITOR (opus) VERIFIED both `typeI_card_bound`/`typeII_card_bound` are
    TRUE for the concrete triple-middle `OnMajorArc` def — NO def change needed (inflation is O(1)/line, absorbed;
    and the weak def is REQUIRED by the proven residual — strengthening breaks it). TypeII log is the faithful
    target. Proof approach: TypeI = near-set spacing (writeup 534–562) + disjoint-interval packing; TypeII =
    `(q,slope)` enumeration + harmonic `Σ1/q~log`. `collinear_five_on_majorLine` now PROVEN (rational-line
    reconstruction via `Rat.num_den_mk`) ⟹ **RESIDUAL REGIME FULLY DONE**. **§4 = bands ✅ + prop43_local ⟸ 2
    stubs: `typeI_card_bound` (`≤8(Nδ+1)`, needs off-line spacing lemma) + `typeII_card_bound` (the log crux).**
  - **PROP 4.3 PROGRESS 3 (2026-06-03)**: TypeI ANALYTIC CORE PROVEN in new `Geometry/NearCurveTypeI.lean`:
    `offLine_spacing` (writeup 534–562, the off-line gap `1/(4q) ≤ |m−m₀|(2δ/L+2λL)+2λ|m−m₀|²` via MVT — REUSABLE,
    TypeII needs it) + `typeI_offLine_gap` (TypeI `B−A≤δ√(q/λ)` ⟹ off-line pts `|m−m₀|≥d(A)/24`, `d(A)=L/(qδ)`).
    `typeI_card_bound` now reduces to PURE disjoint-interval PACKING (writeup 599–605: order arcs by `n_j`, attach
    disjoint `I_j=[n_j,n_j+c₁d(A_j)]` via `typeI_offLine_gap`, `ν(A_j)≤residueClass_card_le≪δ|I_j|`, sum→2Nδ) —
    put in new `NearCurvePacking.lean`. **§4 = bands ✅ + prop43_local ⟸ `typeI_card_bound` (packing only) +
    `typeII_card_bound` (log crux, uses `offLine_spacing`).** (NearCurveTypeI.lean 457 ln — factor deriv helpers later.)
  - **PROP 4.3 PROGRESS 4 (2026-06-04)**: TypeI per-arc + disjointness PROVEN in new `Geometry/NearCurvePacking.lean`:
    `arc_residue_count` (`ν(A)≤δ·d(A)+1` via `denom_dvd_sub_of_onLine`+`onLine_window_card_le`+`residueClass_card_le`),
    `offLine_gap_arc` (integer-endpoint disjointness driver from `typeI_offLine_gap`). `typeI_card_bound` now delegates
    to single stub `typeI_arc_sum` (NearCurvePacking.lean:157) = the GREEDY maximal-disjoint-arc selection + sum
    `Σ(δd(A_j)+1)≤48Nδ+#arcs≤8(Nδ+1)` (writeup 599–605; strong-induction Finset packing — combinatorial, large).
    **§4 = bands ✅ + prop43_local ⟸ `typeI_arc_sum` (greedy packing) + `typeII_card_bound` (log crux).** Both have
    analytic/per-piece cores PROVEN; remaining is the greedy-packing combinatorics + the TypeII `(q,slope)` harmonic sum.
  - **PROP 4.3 PROGRESS 5 (2026-06-04)**: TypeI packing INPUTS all PROVEN in `NearCurvePacking.lean`:
    `arc_residue_count_sharp` (`+1`-free `ν≤(3/2)δd(A)` via `2q≤b−a`), `sum_len_le_of_disjoint_Ico` (disjoint `Ico`
    packing `Σlen≤U−L` via `volume`/`measure_biUnion_finset`), `Ico_disjoint_of_gap`. Constants re-threaded:
    `typeI_card_bound`/`typeI_arc_sum` `8→48(Nδ+1)`, `prop43_local` internal `48→88` (shape unchanged, `nearCurve_count`
    green). REMAINING `typeI_arc_sum` (NearCurvePacking.lean:251) = the GREEDY ASSEMBLY (index packing by DISTINCT
    ARCS not lines — a line can host multiple disjoint arcs; `card_biUnion_le` + per-arc sharp + `Σd(A)≤24(N+1)`).
    The hard combinatorial core (attempt-1 ~1700 ln). **§4 = bands ✅ + prop43_local ⟸ `typeI_arc_sum` (greedy
    assembly, all inputs proven) + `typeII_card_bound` (log crux).**
  - **PROP 4.3 PROGRESS 6 (2026-06-04)**: `typeI_arc_sum` now PROVEN ⟸ single stub `exists_greedyPacking`.
    `card_le_of_greedyPacking` (the final arithmetic `Σν≤(3/2)δΣdens, Σdens/24≤N+1 ⟹ ≤48(Nδ+1)`) PROVEN. Crux
    isolated behind CONCRETE `structure GreedyPacking` (fields: `G` selected set, `lo/dens/nu`, `nu_le≤(3/2)δdens`,
    `interval_subset⊆Icc N (2N+1)`, `interval_disjoint` PairwiseDisjoint Ico, `card_le_sum_nu` covering) — NOT
    opaque, all fields consumed by proven lemmas. REMAINING `exists_greedyPacking` (NearCurvePacking.lean:338) = the
    greedy leftmost-uncovered selection (disjointness from `offLine_gap_arc`, covering, per-arc from
    `arc_residue_count_sharp`) — concrete, provable-in-principle. **§4 = bands ✅ + prop43_local ⟸
    `exists_greedyPacking` (greedy construction) + `typeII_card_bound` (log crux).**
  - **PROP 4.3 PROGRESS 7 (2026-06-04)**: ALL TypeI scaffolding PROVEN in new `Geometry/NearCurveGreedy.lean`:
    witness extraction (`witnessLine/Lo/Hi`+`witness_spec` via `Classical.choose`), `densAt`, `windowResidueSet`,
    `two_denom_le_span_of_witness` (`2q≤b−a`), `windowResidueSet_card_le` (`≤(3/2)δd`), `structure GreedySel`,
    `greedyPacking_of_greedySel` (builds full `GreedyPacking` — `nu_le`+`card_le_sum_nu` via `card_biUnion_le` all
    real), `exists_greedyPacking`+`typeI_arc_sum` now REAL theorems. REMAINING `exists_greedySel`
    (NearCurveGreedy.lean:240) = `Nonempty (GreedySel)` = the pure greedy leftmost-uncovered SELECTION (G⊆typeISet,
    disjoint windows via `offLine_gap_arc`, covering via greedy maximality) — concrete `∃`, sound (not hollow).
    **§4 = bands ✅ + prop43_local ⟸ `exists_greedySel` (greedy selection) + `typeII_card_bound` (log crux).**
  - **PROP 4.3 PROGRESS 8 (2026-06-04)**: greedy SELECTION built+proven (`greedySelList`/`greedySelSet` = leftmost-
    uncovered fold; `greedySelSet_subset ⊆ typeISet` via fold invariant `mem_foldl_greedyStep`). `exists_greedySel`
    now real ⟸ single stub `greedySel_geometry` (NearCurveGreedy.lean:321) = the 3 `GreedySel` facts
    (`subset_window ∧ gap ∧ cover`). ⚠ MINOR STATEMENT FIX flagged: `GreedySel.subset_window`'s `Icc N (2N+1)` is
    too tight (leftmost pt has `g≥⌊N⌋` not `≥N`; upper needs T-vs-N scaling) — RELAX to floor-window `Icc (⌊N⌋:ℝ)
    (⌊2N⌋+1)` (the 48-const slack in `card_le_of_greedyPacking` absorbs it; thread to `GreedyPacking.interval_subset`
    + `sum_len_le_of_disjoint_Ico` call). Then `gap` (via `offLine_gap_arc`) + `cover` (greedy maximality) = the
    genuine remaining TypeI combinatorics. **§4 = bands ✅ + prop43_local ⟸ `greedySel_geometry` (gap+cover, +floor-
    window fix) + `typeII_card_bound` (log crux).**
  - **PROP 4.3 PROGRESS 9 (2026-06-04)**: `greedySel_geometry` GAP (pairwise-disjoint windows) FULLY PROVEN via
    fold invariants (`pairwise_gapRel_foldl`, `gap_of_gapRel` discharging `offLine_gap_arc`); floor-window fix done
    (`Icc ⌊N⌋ (⌊2N⌋+1)`, constants `48→72`, `prop43_local 88→112`, all green). REMAINING `greedySel_window_cover`
    (NearCurveGreedy.lean:572) isolates a ⚠ REAL FORMULATION TENSION: the greedy COVERING window `[g,g+densAt g/24)`
    and the residue-COUNTING window (arc span `[a_g,b_g]`) MISMATCH — `densAt g/24=(b−a)/(24qδ) > (b−a)` when `qδ<1/24`
    (small δ), so a "covered" pt can fall OUTSIDE `windowResidueSet g`. The writeup's "first pt of a later arc is
    OFF the earlier line" (595) is the real mechanism: distinct witness LINES meet in ≤1 pt, so disjointness holds
    except at ≤1 intersection/pair. RESOLUTION (next): refactor the greedy so COVERING uses the arc residue set
    `[a_g,b_g]` (covered ⟹ in `windowResidueSet`) while DISJOINTNESS uses off-line gap on DISTINCT LINES (handle the
    ≤1 line-intersection pt, absorbed in constants) — OR audit for a cleaner reconciliation. Concrete stub, green,
    not hollow — but needs design care, not just grinding. **§4 = bands ✅ + prop43_local ⟸ `greedySel_window_cover`
    (the cover/packing window reconciliation) + `typeII_card_bound` (log crux).**
  - **PROP 4.3 — AUDITOR RESOLUTION of the TypeI tension (2026-06-04, opus)**: the POINT-indexed greedy `cover` is
    GEOMETRICALLY FALSE; FIX = RE-INDEX the greedy by LINES / proper-arc-reps (≤1 per line). Precise design (auditor):
    keep `windowResidueSet = arc [a_g,b_g]` + `arc_residue_count_sharp` (`ν≤(3/2)δdensAt`) UNCHANGED (counting over the
    arc is FORCED — `densAt/24`-window count loses the `δ`, sympy-confirmed); change PACKING interval base `g→a_g`
    (`Ico a_g (a_g+densAt/24)`); `cover` becomes DEFINITIONAL (each TypeI pt in its OWN line's rep arc `[a_n,b_n]`);
    disjointness via `offLine_gap_arc` between reps on DISTINCT lines (valid there). REUSABLE AS-IS: `GreedyPacking`,
    `card_le_of_greedyPacking` (C=72), `arc_residue_count_sharp`, `windowResidueSet_card_le`, `offLine_gap_arc`,
    `sum_len_le_of_disjoint_Ico`, `gap_of_gapRel`. MUST CHANGE: `GreedySel`/`greedySelSet`/`isCoveredBy`/`gapRel`
    point→line-rep indexing. NEW GENUINE LEMMA: **≤2 components/line** (writeup 532): on a fixed line denom `q≤c/δ`,
    near-set pts form ≤2 `q`-spaced runs (via `g'` monotone / `|f''|≍λ` curvature — already threaded; NOT a missing
    `λ=T/N²` scale). Verdict: IMPLEMENTABLE, `#typeISet ≤ 72(Nδ+1)`. **§4 = bands ✅ + prop43_local ⟸ TypeI
    line-rep refactor (closes `greedySel_window_cover`; genuine piece = ≤2-components/line) + `typeII_card_bound`.**
  - **PROP 4.3 PROGRESS 10 (2026-06-04)**: TypeI LINE-REP REFACTOR DONE — the false point-indexed cover is GONE;
    `cover` now FULLY PROVEN (definitional via `cover_foldl`, each TypeI pt in its own line-rep's `lineSet`).
    Re-indexed `isCoveredBy`/`gapRel`/`GreedySel` point→line (`repArc g` = max-count proper-arc pt via
    `Finset.exists_max_image`); distinct-line disjointness OFF-line branch PROVEN; `onLine_eq_of_two_points`,
    `card_le_two_sum_nu` (writeup-532 factor 2) PROVEN. Constants: typeI `72→144`, `prop43_local` C `112→184` (∃C,
    faithful; the factor-2 needs only `δ<1`). REMAINING 3 concrete TypeI stubs (all TRUE): `onLine_distinct_gap`
    (NearCurveGreedy:580, ON-line disjointness branch — `g'+q_{g'}` off `D_g`), `greedySel_window` (:695, window
    `⊆[⌊N⌋,⌊2N⌋+1]` — ⚠ needs λ-vs-N scaling, `densAt/24≤1/(24√λ)`; true for the app's `λ=T/N²≥1/N²` but
    prop43_local states general λ — may need a λ floor hyp or reformulation), `line_two_components` (:718, THE
    ≤2-comp/line genuine content, `#lineSet≤2·#repArc` via convex `g''≍λ` const-sign). **§4 = bands ✅ +
    prop43_local ⟸ {onLine_distinct_gap, greedySel_window, line_two_components} (TypeI) + typeII_card_bound.**
  - **PROP 4.3 PROGRESS 11 (2026-06-04)**: the GENUINE CURVATURE CONTENT PROVEN: `iteratedDeriv2_const_sign`
    (`f''` const-sign from `|f''|≥λ`+continuity) + `lineRes_convex_or_concave` (`g=f−P_D` ConvexOn∨ConcaveOn via
    `convexOn_of_hasDerivWithinAt2_nonneg`) — the headline writeup-532 input. `line_two_components` reduced (union-
    split at the discrete `lineRes`-minimizer) to `halfRun_card_le_repArc` (NearCurveGreedy:796). ⚠ CASCADE FINDING:
    the TypeI combinatorics keeps hitting per-POINT-witness-arc vs per-LINE-maximal-run mismatches (window cap →
    line-indexing → now run-vs-window). ROOT FIX: redesign `repArc`/`windowResidueSet` to the MAXIMAL same-line
    near-set run (= the writeup's "proper arc"/component, length `≤√(δ/λ)` via `majorArc_length_bound`), then
    `halfRun ⊆ maximal run = repArc window` (provable), `ν ≤ (3/2)δd` over the run, packing intact. This is a
    witness-extraction redesign (the right design all along). GENUINE MATH (convexity, residual, off-line spacing,
    div-diff MVT) ALL PROVEN; remaining TypeI = the maximal-arc combinatorial reconciliation + the 2 mechanical
    gaps; then typeII. NearCurveGreedy.lean ~1004 ln (split convexity helpers later). **§4 = bands ✅ + prop43_local
    ⟸ TypeI maximal-arc reconciliation (3 stubs) + typeII_card_bound.**
  - **PROP 4.3 PROGRESS 12 (2026-06-04)**: MAXIMAL-ARC REDESIGN DONE — `windowResidueSet`/`densAt` now = the per-line
    PROPER MAJOR ARC (`properArc D` = larger of the ≤2 convex half-runs; `lineCarrier`/`lineMin`/`halfCarrier`/
    `properSide`). PROVEN: `line_two_components` (`#lineCarrier≤2·#properArc`), `halfRun_card_le_repArc`,
    `windowResidueSet_card_le`, `two_denom_le_properArc_span_of_three` (`2q≤span` from ≥3 pts). Packing re-threaded
    to proper arcs. REMAINING 3 TypeI stubs: `proper_major_arc_count` (NearCurveGreedy:332, reduces to `3≤#properArc`
    = writeup-516 "proper arc is a major arc w/ ≥3 pts" — ⚠ subtlety: larger HALF-RUN vs larger maximal COMPONENT;
    the ≥3 holds for the component, this stub absorbs the gap), `gap_of_gapRel` (:761, distinct-line proper-arc
    window disjointness), `greedySel_window` (:803, arc-length cap — needs `λ=T/N²` scaling absent from prop43_local's
    general-λ hyps ⟹ FIX: add λ-floor hyp `1≤N²λ` to prop43_local, supplied by the substitution `λ=T/N²,T>1`,
    faithful). ALL GENUINE MATH PROVEN (convexity/residual/off-line-spacing/MVT/≤2-components). The TypeI combinatorial
    cascade (window→line-index→run-vs-window→half-vs-component) is the deep tail of Prop 4.3 (attempt-1 ~4000 ln).
    **§4 = bands ✅ + prop43_local ⟸ {proper_major_arc_count, gap_of_gapRel, greedySel_window} + typeII_card_bound.**
  - **PROP 4.3 PROGRESS 13 (2026-06-04)**: 3 TypeI stubs → 2 (sharper). `proper_major_arc_count` FULLY PROVEN via the
    **factor-2 reframe** (the `≥3`-half-run claim was FALSE for 2-pt arcs): proved `≥2` (witness gives 3 collinear
    near-set pts ⟹ `#lineCarrier≥3` ⟹ larger half `≥2`, `three_le_lineCarrier_of_typeI`/`two_le_properArc_of_typeI`),
    then `q≤span` (`one_denom_le_properArc_span_of_two`) + new `arc_residue_count_two` (`ν≤2δd`). Constants bumped to
    keep shape: `nu_le` `3/2→2`, `card_le_of_greedyPacking`/`typeI_arc_sum`/`typeI_card_bound` `144→192`,
    `prop43_local` `184→240` (`nearCurve_count` green). `gap_of_gapRel` FULLY DERIVED ⟸ named sub-stub
    `properArc_directed_gap` (directed distinct-line gap, WLOG-order + `Ico` disjointness assembly proven).
    `greedySel_window` FULLY DERIVED ⟸ named sub-stub `densAt_le_24` (`repArc_mem_Icc` near-set base + `len/24≤1`
    containment proven). REMAINING 2 named geometric sub-stubs, both = the Type I PROPER-ARC SPAN `≤δ√(q/λ)`
    (writeup 583–585; `properArc_directed_gap`) and that + the λ-floor `√(qλ)≥1/24` (`densAt_le_24`). NOTE: the
    `interval_subset`/`densAt_le_24` cap is only valid with a λ-floor — confirmed wide proper-arc windows otherwise
    overflow `[⌊N⌋,⌊2N⌋+1]`; the floor `1≤N²λ`/`λ≥1/576` is the threaded fix (supplied by `λ=T/N²,T>1`). All builds
    green. **§4 = bands ✅ + prop43_local ⟸ {properArc_directed_gap, densAt_le_24} + typeII_card_bound.**

---
### (historical) AUDIT — 4 of 6 were FALSE/UNFAITHFUL

The Main→`theorem_10_1` spine (§1/§2/§3/§8/§9/§10) builds green with `#print axioms` reaching
only `sorryAx` + `propext`/`Classical.choice`/`Quot.sound`. BUT a 2026-06-03 audit of the 6 §4–7
stub **statements** found the green build was partly illusory: the three stubs reachable from
`theorem_10_1` were **false as written**, so their `sorry`s were undischargeable (not "hard
analysis pending" — wrong statements). Audit verdicts:

| stub | file | § | reachable? | audit verdict |
|---|---|---|---|---|
| `bands_count` | `Counting/Bands.lean` | 4 | orphan | ⚠ FIXED — `.Finite` zero-sets → `.ncard ≤ K` + `(K+1)` factor (uniform `C` was false with only `.Finite`) |
| `nearCurve_count` | `Geometry/NearCurve.lean` | 4 | orphan | ✅ faithful as-is (no change) |
| `prop_5_1` | `Lower/Prop51.lean` | 5 | **yes** (Strip) | ❌ false: `Ra` unconstrained + 3 vacuous `∃c` regime/popularity hyps |
| `prop_6_1` | `Upper/Regime.lean` | 6 | **yes** (Strip) | ❌ false: `RaOf` totally unconstrained ⇒ LHS unbounded |
| `prop_7_1` | `Bracket/BoxSum.lean` | 7 | orphan | ❌ false: `ftil/dBreve/dBreve'` arbitrary (no curvature hyps) |
| `prop_7_3` | `Bracket/BoxSum.lean` | 7 | **yes** (Global) | ❌ false: only `inDa` (d-side, wrong KIND) — missing range/injectivity + the r-side near-curve membership |

**Root cause + fix (user-chosen 2026-06-03: "full fix, bridge proven").** The faithful structural
hypothesis is **near-curve membership** (writeup 1251 `#ℛ_a ≤ Σ_{r≍R}1_{‖f̃_a(r)‖≤δ}`; 1372 the
`g_j` analog) — the *r-side* phase condition. The green `prop_3_2_fiber`/`_dStar` expose only the
*d-side* (`inDa(dStar r)` + the approximation `|dStar r−dtil r|≤C₃(Δ/G)(Δ³/A³)`, Fiber.lean ~450).
The **bridge** (writeup 1245–1251: `inDa(d)⇒‖F_a(d)‖≤O(H/D²)`, then `+`approximation`+`Taylor ⇒
`‖f̃_a(r)‖≤δ`) is unformalized — it is §5/§6/§7's own first move. Plan:
1. **[DONE]** Fix §4 engine statements (`bands_count` `K`-fix; `nearCurve_count` unchanged). Green.
2. **[TODO] Bridge lemma** (PROVE, no new stub): define `ftil = f̃_a = F_a∘d̃_a`; from
   `prop_3_2_fiber_dStar`'s data derive, per `r∈ℛ_a`, `‖f̃_a(r)‖≤δ` (δ≍H/(Δ²Ω²)) and the `g_j`
   membership (δ₀ per 1376). Lives in `Structure/Fiber.lean` (extend `_dStar` output) or a new
   `Structure/NearCurveBridge.lean`. §5 needs the d-side data (range+`inDa`+`r=R_a(dStar r)+O(1/Δ)`
   +`dStar` inj), NOT the f̃ bridge — its proof is the ℛ_a(ℓ₁,ℓ₂) defect bookkeeping (731–1224).
3. **[TODO] Restate + re-thread** `prop_6_1`(+Strip), `prop_5_1`(+Strip), `prop_7_3`(+Global).
   `prop_7_1` is DEFERRED to §7-proper (orphan; needs §7 phase infra — flagged in BoxSum.lean).
   Each restate lands together with its consumer edit so the build stays green. Consumers already
   hold the needed data internally (`dblock_le_sum_Ra` builds `RaOf` from `prop_3_2_fiber`; `Global`
   gets `Ra/dStar` from `_dStar`) — but currently FORGET it; threading it out is the re-thread work.

**REFINED ARCHITECTURE (2026-06-03) — d-side data, phase machinery INTERNAL.** Insight: all three
props take the SAME *d-side* structural data (which `prop_3_2_fiber_dStar` already proves internally),
and each prop's (stubbed) proof builds its OWN phase (`f̃_a` §6, `g_j` §7, defect §5) using the bridge.
The consumer just FORWARDS the d-side data — it does NOT construct `d̃_a` or supply a phase. The d-side
data per `r∈ℛ_a`: `range c₁R≤r≤C₁R`, `inDa(dStar r)`, `defining |Rfun X a (dStar r) − r| ≤ 14H/D` (=O(1/Δ),
the `hnear` already in Fiber.lean), (+ `dStar` injective on Ra — only §5 needs it). This is faithful
(exactly §5/§6/§7's starting data, writeup 361–363), TRUE (provable via the section analysis), and
supplyable. The §6 internal proof: from `inDa(dStar r)`+defining, construct `d̃_a`, derive the approx
`|dStar r−d̃_a r|≤C₃(Δ/G)(Δ³/A³)`, apply `nearcurve_membership` ⇒ `‖f̃_a(r)‖≤δ₆`, then curvature ≍F + Prop 4.3 in a.

**DONE (proven, green):**
- **Bridge B1** `inDa_distInt_Ffun` (`ADecompAux.lean:49`): `inDa X H a d ⇒ distInt(Ffun X a d) ≤ 2H/d²`.
- **Bridge B2** `nearcurve_membership` (`Structure/NearCurveBridge.lean:80`, C=52): given the approx
  `|d−dtil r|≤Capx·(Δ/G)(Δ³/A³)`, band, `Ω≤H`, ⇒ `distInt(Ffun X a (dtil r)) ≤ 52·(1+Capx)·H/(Δ²Ω²)`.
  (`Ffun` de-privatized in ADecompAux.) This is the §6/§7 internal tool. `δ₆ ≍ H/(Δ²Ω²)=x/Ω²`.

**TODO (each restate lands WITH its consumer edit, build stays green):**
- **Step A** — extend `prop_3_2_fiber_dStar` to ALSO expose `∀ r∈Ra, |Rfun P.X a (dStar r) − r| ≤ 14*P.H/S.D`
  (the defining relation; `hnear` is already in the proof) [+ `dStar` injectivity for §5]. Additive/low-risk.
- **prop_6_1** (+Strip): take d-side data per `(a, r∈RaOf a)`; conclusion (3-term) UNCHANGED. Internal
  proof (stub) = construct `d̃_a`, `nearcurve_membership`, curvature ≍F (F=HxGΩ), Prop 4.3 in `a`.
- **prop_7_3** (+Global): REPLACE the lone `inDa(dStar r)` with the FULL d-side data; conclusion
  `(1+H/A²)·R/W` UNCHANGED. Internal proof (stub) = `g_j` machinery + Prop 7.1, `δ₀=Δ⁵/(H³G²Ω²)+Δ²/(H²GA)`
  (the G²-form already in `prop_7_1`; md 1376 dropped a G²).
- **prop_5_1** (+Strip): d-side data + `dStar` inj; conclusion UNCHANGED. De-vacuify the 3 hyps: regime
  `c₅·(GU¹⁰)≤H/Δ²`, `c₅·(G²U⁵)≤Δ` with `c₅` a MODULE-LEVEL absolute constant (outer `∃`, NOT inner `∃c`
  — inner `∃c>0,c·lower≤upper` is VACUOUS); popularity `R/Wval≤Ra.card` (`Wval=GU⁵`✓).

**Conclusions are unchanged** (the RHS three-term / `R/W` forms were faithful); only the
HYPOTHESES change (add the structural/near-curve constraint). The §8/§9 budget still closes.
**Cross-cutting rule:** a `≫`/`≪` regime/popularity bound must use a MODULE-LEVEL absolute constant,
never a per-instance `∃c` (which is logically vacuous). This was the prop_5_1 bug and the recurring one.

**⚠ AUDIT each stub SIGNATURE before proving** (via `math-auditor`) — vindicated: the plumbing phase
found vacuous `∃`-hyps (band edge, `dtil`), trivially-true per-scale `C`, a false `1≤Δ`, a range-capping
`g`-coeff, the 256× threshold; this audit adds 4 more false §4–7 statements. Each analytic proof costs
~35–85 min / 50–470k subagent tokens — never invest before the statement is confirmed faithful + provable.

The milestones (M1–M6) and "3 sorries in attempt-1" framing below are SUPERSEDED by the above; the
§4–7 *math attack* guidance (Phases B/D/E, the §6/§7 frontier analysis) still applies to the 6 stubs.

## 0. The single most important fact

A first attempt already exists at
`../explicit_formal/squarefree_lean` and is **~99.9% complete**: 751 Lean files,
15,542 declarations, **only 3 genuine remaining `sorry`s**, with everything else *blocked*
purely on those three. The three are:

| # | Declaration | Section | Nature |
|---|-------------|---------|--------|
| 1 | `proposition_6_1_upper_regime_bound` | §6 | Apply Prop 4.3 in `a` + verify `∂_a`-size & `|F''|≍1` hypotheses for `f̃_a`. |
| 2 | `section7_local_tripleDiff_zeroTopCarry_bound_md` | §7, `ρ_0=0` | Two-monomial (`y^{-2},y^{-13/4}`) curvature ⇒ Lemma 4.2. |
| 3 | `section7_local_tripleDiff_nonzeroTopCarry_bound_md` | §7, `ρ_0≠0` | `y^{-1}`-dominated local Prop 4.3 with `1≤|F''|≤2`. |

**Implication for attack:** the genuinely hard mathematics is *narrow and known*. The §4.3
"points near a curve" lemma — usually the scariest classical input — is already DONE in
attempt 1. The two §7 *local* triple-difference curvature bounds and the §6 derivative-size
verification are the real frontier. Everything around them (the long §5 bookkeeping, the §8/§9
optimization algebra, the §1 Möbius reduction) is mechanically completable, as attempt 1 shows.

**Route decision (made 2026-06-01): clean-room re-derive.** Attempt 2 builds a fresh,
independent tree in `2explicit_2formal/` following this plan top-to-bottom. Attempt 1 is used
**only as evidence of feasibility** (e.g. confirming Prop 4.3 and §5 do close in Lean, and that
the frontier is exactly the 3 sorries above) — **not** as a source to copy proofs from. We may
glance at attempt 1's *module structure* as a sanity check, but proof content is re-derived from
the writeup. This favors clean provenance over speed; the module DAG and attack order below apply
directly.

---

## 1. Proof spine (what depends on what)

```
§1 Möbius reduction ───────────────────────────────► need: #D[D,2D] ≪ H/U  (per dyadic D, set Δ=D/H)
        │
        ├── §2 short-Δ (Δ ≤ X^{1/100}):  Lemma 2.1 (4th-deriv) ◄── Lemma 2.2 (popular diff), Lemma 2.3 (preimage)
        │
        └── Δ ≥ X^{1/100}:  §3 structural reduction in d
                 │   Lemma 3.1 (gap bound) ◄── S_{a,b} factorization
                 │   Roth R_a identity, d̃_a inverse-fn scales
                 │   Prop 3.2 (R_a → D_a map; fiber & approx)
                 ▼
            split on Δ:
              §5 (Δ small):  Prop 5.1  ──┐
              §6 (Δ large):  Prop 6.1  ──┤
                                         ▼
                                §8 Prop 8.1 (unresolved strip in x,Ω)
                                         │
              §7 (final):  Prop 7.1/7.3 ─┤   (needs Lemma 7.2 cube + local 4.2/4.3 bounds)
                                         ▼
                                §9 global optimization  ⇒  18977g+15315u<2
                                         ▼
                                §10 / Main theorem
```

Shared infrastructure used by many nodes:
- **Counting kernel**: Lemma 2.3 = Lemma 4.1 (preimage), Lemma 4.2 (derivative bands),
  Prop 4.3 (points near curve). These three are the analytic engine; §5/§6/§7 are *clients*.
- **`X^{O(u)}` budget**: the uniform "negative-exponent ⇒ `O(U^{-1})`" lemma.
- **Asymptotic-scale calculus**: `≍`/`≪` with derivative-cost-`1/R` bookkeeping for
  `d̃_a, b̃_a, f̃_a, d̆_a` and their compositions.

## 2. Module organization (LOCKED 2026-06-02)

Lean package at `squarefree_lean/` (toolchain `lean4:v4.30.0-rc1`, mathlib pinned to
`343ccbbb…` for cache reuse). Root namespace `Squarefree`. One theme per file (≤~400 lines).
Layers L0–L5 build bottom-up; `★` = analytic engine; `←frontier` = a frontier proof.

```
squarefree_lean/Squarefree/
  -- L0 Foundation (build & lock first; everything rests here)
  Params.lean         H,G,U,X,Δ,Ω,x,A,R,B,F,T₁,T₂,T₃ + all scale identities (X=GH^5,
                      R=HGΩ³/Δ, B=Δ²/(GΩ³), T₁T₂=T₃, XaB/D⁵=1/(Δ²Ω²), Tᵢ/Rʲ table)
  Asymp.lean          ≍ / ≪ calculus: a ≲ b := ∃ C>0, a ≤ C*b  (+ refl/trans/mul/add)  ★keystone
  Budget.lean         the X^{O(u)} linear-u-budget lemma: α(g)<0 ∧ u≤c(g) ⇒ term ≤ U⁻¹  ★keystone
  FiniteDiff.lean     Δ_{h₁,h₂,h₃} operator, integral/Taylor forms, ‖·‖ & floor-carry algebra
  -- L1 Analytic engine (parameter-free: abstract f, φ, N, T, δ, λ)
  Counting/Preimage.lean     Lemma 4.1 / 2.3
  Counting/PopularDiff.lean  Lemma 2.2
  Counting/FourthDeriv.lean  Lemma 2.1 (3-fold differencing)
  Counting/Bands.lean        Lemma 4.2                                   ★engine
  Geometry/NearCurve.lean    Prop 4.3 (residual / TypeI / TypeII privs)  ★engine, big
  -- L2 Structure (§3) + algebra
  Structure/SabFactor.lean   S_{a,b} factorization, R_a identity, expansions (pure `ring`)
  Structure/DaSpacing.lean   D_a, Nair–Roth, Lemma 3.1, Prop 3.2
  -- L3 Regimes
  ShortDelta.lean            §2 Prop 2.4            (client of FourthDeriv)
  Lower/Prop51.lean          §5 Prop 5.1 (split into Step1..Step5 if needed)
  Upper/Regime.lean          §6 Prop 6.1            (client of NearCurve)   ←frontier #1
  -- L4 Crux (§7): five files along the math seams (NOT trial-and-error)
  Bracket/Admissible.lean    `structure AdmissibleW` = the whole constraint envelope
  Bracket/Carry.lean         eq (7.1)–(7.5): 3rd-diff expansion, carries/fibers, C_*≠0
  Bracket/LocalZero.lean     ρ₀=0 branch → W_old                          ←frontier #2
  Bracket/LocalNonzero.lean  ρ₀≠0 branch → W_{≠0}                         ←frontier #3
  Bracket/BoxSum.lean        power-sums over (h₁,h₂,h₃) box, compare R/W; Prop 7.1, 7.3
  -- L5 Top
  Opt/Strip.lean             §8 Prop 8.1 (combine 5.1+6.1 → unresolved strip)
  Opt/Global.lean            §9 (9.1)–(9.3), W_old/W_{≠0} compare → 18977g+15315u<2
  Dyadic.lean                O(log X)=X^{O(u)} summation over D- and Ω-scales
  Main.lean                  §1 Möbius reduction + §10 assembly = theorem_10_1
```

Design invariants: (i) L0 hides all constants inside `≲`/`Budget` — section proofs never
re-derive "constant×constant". (ii) L1 engine is parameter-free; clients merely discharge its
hypotheses. (iii) §7 constraints live ONLY in `Bracket/Admissible.lean`; every §7 lemma takes
`(hW : AdmissibleW …)`. (iv) `Main` imports only top-level conclusions; section internals stay
`private`. Public theorems are named after the writeup and stated md-faithfully.

## 3. Attack order (dependency-respecting, value-first)

**Phase A — Lock the scaffolding (low risk, high leverage).**
1. `Params.lean`: define all parameters and *prove the exponent identities once*
   (`R=HGΩ³/Δ`, `B=Δ²/(GΩ³)`, `T_1T_2=T_3`, the `XaB/D^5=1/(Δ²Ω²)` family, the `T_i/R^j` table).
   Add the **`X^{O(u)}` budget lemma**: a reusable "if real exponent `α(g)<0` and `u<c(g)` then
   the term is `≤ U^{-1}`" with an explicit constant pipeline. *Everything* leans on this.
2. `Basic.lean`: finite-difference operator `Δ_{h1,h2,h3}`, its integral/Taylor formulas,
   `‖·‖` (distance to ℤ) arithmetic, floor-carry algebra.

**Phase B — The analytic engine (the reusable kernel).**
3. `Counting/Preimage.lean` (4.1), `PopularDiff.lean` (2.2), `FourthDeriv.lean` (2.1).
4. `Counting/DerivativeBands.lean` (Lemma 4.2). **Pin the statement** (with or without `log`)
   here, since §5/§6/§7 all consume it. *See audit caveat 2.*
5. `Geometry/NearCurve.lean` (Prop 4.3). Largest classical proof; isolate
   residual/Type-I/Type-II as private lemmas. Re-derive from the §4 writeup (clean-room); attempt
   1 having finished it is strong evidence it closes, but do not copy its proof.

**Phase C — Easy wins to de-risk the regime work.**
6. `ShortDelta.lean` (Prop 2.4): direct client of Lemma 2.1. Quick.
7. `Structure/SabFactor.lean`: the `S_{a,b}` factorization and `R_a` identity are pure algebra
   — formalize via `ring`/`field_simp` (sympy already confirms them). Fast, satisfying, and
   unblocks §3 + §5 + §7.
8. `Structure/DaSpacing.lean`: Lemma 3.1, Prop 3.2 (use the *stated weak* fiber bound, audit
   item 1).

**Phase D — The regimes.**
9. `Upper/Regime.lean` (Prop 6.1) — **do this early**; it is one of the 3 frontier sorries but
   is "merely" verifying `|f̃_a|, A|∂_a f̃_a|, A²|∂_a²f̃_a| ≍ F` and `|F''|≍1`, then invoking the
   already-built Prop 4.3. Good first frontier target; gives momentum and exercises the engine.
10. `Lower/` (Prop 5.1) — high *volume*, low *risk*: five steps of Taylor + exponent algebra.
    Budget the most lines here but expect no conceptual surprises. Split per Step.

**Phase E — The crux: §7.**
11. `Bracket/AdmissibleW.lean`: encode the admissibility envelope as a `structure` of
    inequalities (nine integer-power + four residual + two offset + ten nonzero-carry + §4.3
    side conditions). This is the *interface* every §7 sub-lemma references; lock it first.
12. `Bracket/Carry.lean`: eq (7.1)–(7.4), the fiber count (7.2), and the leading-monomial
    expansion (7.5) including the **`C_* = -21/16 c_1c_2 ≠ 0`** computation (sympy-verified;
    formalize the rational-coefficient combination `15/64+9/16-135/64`).
13. `Bracket/LocalZero.lean` (sorry #2): two-monomial Wronskian ⇒ scale `T_{ρ,u}`, remainder
    subordination, Lemma 4.2 application, then the box-sum producing `W_old` and residual
    constraints.
14. `Bracket/LocalNonzero.lean` (sorry #3): `y^{-1}` domination, the `O(1)`-piece local Prop 4.3
    with `1≤|F''|≤2`, side conditions `R≥W^8>1`, `T_1>1 ⇔ x³G²Ω²<H`, `0<δ_1<1`, box-sum ⇒
    `W_{≠0}` and the new constraints.
15. `Bracket/Prop73.lean`: sum over `j`.

**Phase F — Optimization & assembly.**
16. `Optimization.lean`: Prop 8.1 strip, then §9 — the `W_old/W_{≠0}` comparison, (9.1)–(9.3),
    and the reduction to `18977g+15315u<2`. Mostly inequality manipulation over the strip
    endpoints (`x=G^{-2}Ω^{-11/2}`, `x=G^{17}Ω^{-26}`, `Ω=G^{-1/4}U^{-3/4}`, `Ω=U`).
17. `Main.lean`: §1 Möbius reduction + dyadic summation (`O(log X)=X^{O(u)}` scales in both `D`
    and `Ω`) + §10 ⇒ `theorem_10_1_squarefree_interval`.

## 4. Deep-dive on the frontier (where to spend the effort)

**Prop 6.1 (§6).** The only missing content is real-analysis size bounds for
`f̃_a(r) = F_a(d̃_a(r))` *as a function of `a`*. Concretely: differentiate the explicit
`F_a(d) = X/d² - X/(d+a)²` composed with the inverse `d̃_a` (whose `a`-derivatives come from
implicit differentiation of `R_a`). Produce `≍ F = HxGΩ` for value, `A·∂_a`, `A²·∂_a²`, plus
the `|F''|≍1` normalization Prop 4.3 wants. No new ideas; careful chain-rule bookkeeping.

**§7 local bounds — the genuine crux.** Both branches reduce, *after* `Carry.lean` is in place,
to: "on `O(1)` subintervals where `y=r/R` is `≍1`, the normalized phase has controlled
curvature, so Lemma 4.2 (zero branch) / Prop 4.3 (nonzero branch) applies, and the resulting
counts summed over the rectangular `(h_1,h_2,h_3)` box with the elementary power-sums
(`Σ1≪W^7, ΣS≪W^{13}, ΣP≪W^{14}, …`, lines 1800–1819 and 1955–1957) beat `R/W`."
The crux is *not* a deep theorem — it is (i) the non-vanishing `C_*` giving genuine `y^{-13/4}`
curvature, (ii) showing every Taylor remainder is `X^{-c}`-subordinate to the working scale,
and (iii) the bookkeeping that the box-sum total `< R/W` forces the `W`-constraints. Attempt 1's
file sprawl (≈30 `Wstar*`/`Section7*` files in `Optimization/`) shows this is where iteration
happened; budget accordingly and **reuse attempt 1's decomposition** rather than reinventing.

## 5. Risks, conventions, mathlib

- **Biggest risk = `X^{O(u)}`/`≪` discipline.** Lean has no native big-O over a *budget*. Pick
  one representation in `Params.lean` (recommended: explicit constants + `u ≤ c(g)` hypotheses,
  threaded as instance/section variables) and *never* mix it with ad-hoc `Filter`/`Asymptotics`.
- **`≍` (asymptotic equality)**: define as a two-sided constant bound with absolute constants;
  keep constants out of statements (use `∃ C, …` at module boundaries only).
- **Lemma 4.2 log**: settle the statement form in Phase B (audit caveat 2).
- **Prop 3.2**: formalize the *stated weak* bound (audit item 1); don't chase the sharp `Δ^{1/3}`.
- **mathlib inputs**: `Nat.ArithmeticFunction.moebius`/squarefree (μ²) for §1; `iteratedDeriv`,
  Taylor/`taylor_mean_remainder`, MVT for the differencing; `Int.fract`/`round`/`Int.floor` for
  `‖·‖` and carries; `Finset` power-sum bounds for the box sums. No exotic dependencies.
- **Build hygiene**: keep the analytic engine (Phase B) and `Params` in their own import island
  so the heavy §7 files don't trigger full recompiles.

## 6. Suggested milestones

1. **M1 (scaffold green):** Phase A + B compile with the engine lemmas stated (proved or
   clearly-scoped `sorry`s), `Params` identities all proved.
2. **M2 (regimes-minus-frontier):** §2, §3, §5 fully proved; §6 reduced to the `∂_a`-size lemma.
3. **M3 (frontier #1):** Prop 6.1 closed.
4. **M4 (§7 zero branch):** `LocalZero` closed ⇒ `W_old` line.
5. **M5 (§7 nonzero branch):** `LocalNonzero` closed ⇒ `W_{≠0}` line. (Hardest; main novelty.)
6. **M6 (top):** §8/§9 optimization + `Main` ⇒ `theorem_10_1`, no `sorry` reachable from the top.

## 7. Route: clean-room (resolved)

Decided: clean-room re-derive in `2explicit_2formal/` (see §0). Practical consequences:
- Phase B (`NearCurve`, `DerivativeBands`) and Phase D (§5) are re-derived from the writeup, not
  ported — budget real time for Prop 4.3 even though attempt 1 shows it closes.
- The §7 frontier is "re-derive both local bounds," not "finish 2 sorries in place." Use attempt
  1's ~30-file `Bracket`/`Optimization` sprawl only as a hint about *which* sub-estimates needed
  iteration, then design a cleaner decomposition from the audit's eq (7.1)–(7.5) breakdown.
- Keep attempt 1's progress tooling idea (a `lake build` + import/`sorry` scan) so the fresh tree
  has a live dashboard from M1 onward.

### A3 GATE RULING (2026-06-11, post-restart foreground redo) — feeds arbitration #5
N10 PASS (C* = −21c₁c₂/16 independently re-derived; c₃=3c₁c₂ via exact chain rule; c₁c₂≠0 is
constructor-side at §3). N9 AMEND: Sec7MonExp must be BUILT AT THE §3 SITE (md 326–344; d̃^{(j)}≍HΔ/Rʲ
gives the C⁵ control); DELETE sec7_monExp_exists (abstract Ph admits no expansion); cExp→10²⁵.
N11 AMEND: (i) missing hρ₀ ≤ cCarry (dischargeable from N7/N8 cover); (ii) **WRITEUP ERRATUM md
1675–80**: the Ph_ΣT₃/R⁴ absorption is unsatisfiable (h_Σ/R ≍ X^{-(1-g)/10} ≫ X^{-(1-g)/5+O(u)};
LP vs all 25 envelope entries infeasible) — DROP habs (here + Sec7ZeroScale:107 field), instead add
+Pprod·hSum·T₃/R⁴ to sec7_errScale; its subordination to PT₃/R³ supplied by envelope tc4
(h_Σ/R ≤ 3/(envC·W⁴)), consistent with md 1702; (iii) cErr→10⁴⁰ (worst graded term ≈10³², chains
≈10³⁸); re-run ledger cN13/cTriple chain vs the 10⁵⁵ ceiling after bumps.
PROCESS NOTE: a Claude-Code restart killed all 6 background A-gates; disk intact (verified);
gates re-running FOREGROUND serially per user preference. A1/A5 verdicts were already applied by U4.
Remaining to re-run: A2, A4, A6. Then arbitration (#5: A3+A4+A6 constant retune vs cTriple≤10⁵⁵).
### A4 GATE RULING (2026-06-11): N12a PASS; N12b cSub→10²⁸ (floor 5.1e25; corner margins
−0.089/−0.199/−0.200, capacities ≥10⁶⁴ ✓); N12c → Sec7ZeroHyp FIELD (zero-counting needs Φ‴ —
not in graded MonExp; discharge at §3 site; principal zeros ≤1 each, KZero=100 ample);
N12d cCal SPLIT cDer=10⁹/cLow=10⁷/cTup=10¹³/cTlo=10¹⁷ (cCal=10⁹ stays as N13 δ-threshold);
N13 engine fit SOUND (q≤2p⟹[p,3p]; hactive-free via inactive-case trivial count; hmono via
N12c+IVT) but cN13→10⁴¹ (floor 1.3e40; 10¹⁴ and A6's 10¹⁵ refuted); cFib STAYS 10¹⁰ (10⁸ refuted:
producer floor 2.1e8); CEILING REBALANCE: AM-6 window factor is per-dyadic 2^{13/4} NOT 72^{13/4}
(global 72-losses already in cN13's floor) ⟹ chain 10^53.0 ≤ 10⁵⁵ ✓. hxsmall margin −0.192 ✓ but
must thread through the BoxSum caller (flag for N14/N21 sigs). habs-deletion (A3) verified clean
here (tc4 supplies; hΣ/R ≤ 3/envC; R = H^{1/2}x^{1/2}GΩ³ exact).
### A2 GATE RULING (2026-06-11): FULL PASS. N5 self-contained (3× iterated block-Cauchy-Schwarz;
generic single-level lemma Σ|E∩(E−h)| ≥ |E|²H/(4N) − |E| iterated over edges ⌊W⌋,⌊W²⌋,⌊W⁴⌋;
cCubeIn=10³ has 10⁵ slack, real floor ~64; hmargin NOT needed by N5). N14+N21: all 15 exponents
exact vs md (rule: (a,b,c) ↦ W^{(a+1)+2(b+1)+4(c+1)}); cBox=10⁴ vs worst constant 72; the 4
BoxPowerSums stubs dischargeable via sum_inv_sqrt_le + Real.sqrt_eq_rpow bridge + subadditivity.
Consumers verbatim incl. the 2·cCube=200<harvM chain. NOTE: N22-harvest pulls box_sum_S_sq from
N14's list (by design). FLAG → arbitration: hxsmall must thread/derive at sec7_triple_split
(BoxSum.lean:43) — neither StripData nor Sec7Envelope obviously implies it (A4: strip margin
−0.192, so DERIVABLE there — thread from the root pack).
### A6 GATE RULING (2026-06-11): fits 32/32 EXACT (full map banked in audit; m16→tc8 ✓; z5/m7
G²-slack via g≥0); ENVELOPE ABSORBS cN13: worst-entry need envC ≥ 18·cTriple·cBox·harvM = 10^64.26
vs 10²⁰⁰ — margin 10^135.7. AMEND (final list, supersedes prior partials): (1) log² on
n1/n2/n3/res1/res2 (currently log-free) + tc9/tc10 log¹→log² + caller log_absorb_sq (k≥2, trivial);
(2) cTriple 10⁴⁰→10⁵⁶ (chain 10^55.02 at tree cN13=10⁴³); (3) ledger 6 assert-groups stale
(cErr=10²⁵ TREE value supersedes A3-brief 10⁴⁰ — coherent w/ cSub=10²⁸; cTup=10¹⁷/cTlo=10¹²
tree-transposed-but-coherent); (4) hxsmall derivable INSIDE sec7_triple_split from StripData —
no signature change. Caller chain PASS: Budget 18977g+18675u+790Cu·u ≤ 2 reproduced exactly
(18675 = 15315+1680 fiber+1680 deflation); all 27 ratioExp vertex-minima ≥ 0; tc5 ≡ 0 by design.
NOTE: an "ARB-1" constants pass (cN13=10⁴³, cErr=10²⁵, cCal-split, habs-deletion, errScale+T₃/R⁴
term) was found ALREADY LANDED in-tree mid-audit and verified coherent. Remaining = ARB-2 (the
4 items above) → AV → W1.
### W1 COMPLETE (2026-06-12): N5 ✓ (diff_sum_lower + level_step ×3 + agg chain; Sec7Cube 400 ln
zero-sorry), N14+N21 ✓ + THE 4 LEGACY BoxPowerSums STUBS ELIMINATED (new BoxNegPowerSums.lean;
existentials carry C ≤ 100), N16 ✓ (X^{1/50}≤R/≤M strip facts), N18 ✓ (3 side conditions).
Full tree green 8520. All routes held as audited. Sec7Nonzero.lean 549 ln → Phase-4 split queue.
W2 = N3 (branch_exists), N6 (third-diff product rule), N9' (Sec7MonExp CONSTRUCTOR at §3 site —
per A3 ruling; new producer file; supplies ME to N10/N11/N12/N17 and the eventual ra_data_pack).
### RULING (2026-06-12): Sec7MonExp INTERFACE — option (a): tighten window fields to [1/16,4]
(the §3 truth; constructor discharges trivially; Cstar_lower only gains slack; no consumer sig
changes) + expose the graded witness CHAINS as fields (refactor of existing Fam proof content).
cErr RE-PIN must be LEDGER-COUPLED: re-derive the N11 floor with tight windows (~10^39.5), then
re-run the coupled asserts (cSub relation from A4's N12b errScale-route — if cSub must rise, its
capacity is 10⁶⁴; the cN13 chain; envelope need 18·cTriple·cBox·harvM) and pick the minimal
coherent assignment with ≥1 decade margin everywhere. Unit dispatches AFTER W3b releases
Sec7PhaseExp (file contention).
