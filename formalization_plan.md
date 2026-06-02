# Formalization plan: organization & attack for `explicit_writeup.md`

Companion to `math_audit.md` (which verifies the mathematics). This plan covers how to
organize a Lean/mathlib formalization of the theorem
`θ_* ≤ 1/5 - 2/94885` and the order in which to attack it.

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
