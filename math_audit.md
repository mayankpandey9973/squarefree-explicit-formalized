# Line-by-line math audit of `explicit_writeup.md`

Audited 2026-06-01. Goal: confirm the mathematics is correct and that I understand
each step well enough to formalize it. Line numbers refer to `explicit_writeup.md`
(2257 lines). Symbolic checks of the four delicate identities were done in `sympy`
and all passed (Roth identity, the `S_{a,b}` factorization, `C_* = -21/16 c1 c2`,
and the final exponent reduction to `18977 g + 15315 u < 2`).

**Verdict: the argument is correct and self-consistent.** Two minor non-sharpnesses
(both harmless and already absorbed by the global `X^{O(u)}` bookkeeping) are flagged
in §3 and §4 below. The final exponent `1/5 - 2/94885` is reached exactly.

---

## Result and parameters (lines 4–26)

- `H = X^{(1-g)/5)`, `G = X/H^5 = X^g` (check: `H^5 = X^{1-g}`, so `X/H^5 = X^g` ✓), `U = X^u`.
- Target: `Σ_{X≤n≤X+H} μ²(n) = (6/π²)H + O(H/U)` for `0<g<2/18977`.
- Note `2/94885 = 2/(5·18977)`, so `1/5 - 2/94885 = (1-g)/5` at `g = 2/18977`. Consistent ✓.
- Convention `X^{O(u)} = X^{Cu}` (absolute `C`); a quantity `X^{α(g)+O(u)}` with `α(g)<0`
  is `O(U^{-1})` once `u < -α(g)/(2C+2)`. This convention is used *everywhere*; formalization
  must track an explicit linear budget in `u`, not an existential big-O.

## §1 Initial reduction (lines 30–77) — CORRECT

- `μ²(n) = Σ_{d²|n} μ(d)`; truncate at `D_+ = 2X^{1/2}` (since `d² ≤ X+H`).
- `d ≤ D_- = H/U`: multiples of `d²` in length-`H` window = `H/d² + O(1)`.
- `d > D_-`: then `d² > H²/U² ≫ H` (uses `H ≫ U²`), so inner sum `O(1)`.
- Main term `Σ_{d≤D_-} μ(d)H/d² = (6/π²)H + O(H/D_-) + O(D_-)`; both errors `≪ H/U`
  since `D_- = H/U` and `H/D_- = U ≤ H/U`. ✓
- Reduces to: `#D[D,2D] ≪ H/U` for dyadic `H/U ≪ D ≪ X^{1/2}`. Set `Δ = D/H`.

## §2 Short-Δ range (lines 81–246) — CORRECT

**Lemma 2.2** (popular difference): gaps argument is sound — at least `m/2` consecutive
gaps are `≤ 4N/m` (else span `> N`), averaging gives `r_A(h) ≥ m²/(16N)` for some
`1 ≤ h ≤ 4N/m+1`. ✓

**Lemma 2.1** (4th-derivative counting via 3-fold differencing):
- Three applications of 2.2: `m_3 ≫ M^8/N^7`, `P = h_1h_2h_3 ≪ N^7/M^7`. ✓
- `g = Δ_{h1,h2,h3}f` has `g'(x) = P ∫_{[0,1]^3} f^{(4)}(...)`, so `|g'| ≍ PΛ`, constant sign,
  `var(g) ≪ PΛN`. ✓ (the third difference of `f'` integrates `f^{(4)}`).
- Lemma 2.3 ⇒ `m_3 ≪ 1 + PΛN + Nδ + δ/(PΛ)`. Four sub-cases:
  - `M^8/N^7 ≪ 1 ⇒ M ≪ N^{7/8}`,
  - `≪ PΛN ≪ ΛN^8/M^7 ⇒ M ≪ Λ^{1/15}N`,
  - `≪ Nδ ⇒ M ≪ Nδ^{1/8}`,
  - `≪ δ/(PΛ) ≤ δ/Λ` (**using `P ≥ 1`**) `⇒ M ≪ N^{7/8}(δ/Λ)^{1/8}`. ✓
  The asymmetric use of `P` (upper bound `≪N^7/M^7` in cases 1–3, lower bound `≥1` in
  case 4) is the one subtlety to reproduce carefully.

**Lemma 2.3 / 4.1** (preimage counting): standard, `O(V+1)` relevant residues × `O(1+δ/F)`. ✓

**Prop 2.4**: `f = X/x²`, `N=D`, `δ=H/D²`, `Λ ≍ X/D^6`. The four terms expand to
`D^{7/8} + H^{1/8}D^{3/4} + X^{-1/8}H^{1/8}D^{11/8} + X^{1/15}D^{3/5}` (all verified). For
`D ≤ HX^{1/100}` each is `X^κ` with `κ < (1-g)/5` for `g < 2/18977`, comfortably. ✓

From here on `Δ ≥ X^{1/100}`.

## §3 Structural reduction in `d` (lines 250–407) — CORRECT (one non-sharpness)

- `D_a = {d : d, d+a ∈ D consecutive with gap a}`. Dyadic pigeonhole in `a`:
  `#D[D,2D] ≪ Σ_{1≪A≪ΔU} Σ_{a~A} #D_a`. Upper limit `A ≪ ΔU` because elements of `D_a`
  are `≥a` apart, so `#D_a ≪ D/A ≪ H/U` when `A ≫ ΔU`. ✓
- Nair–Roth: among 3 consecutive elements of `D`, two are spaced
  `≫ Δ^{4/3}(H^4/X)^{1/3} = D^{4/3}/X^{1/3}`. This equals `λ^{-1/3}` with `λ = f'' ≍ X/D^4`
  — exactly the non-collinear-triple spacing of Prop 4.3. ✓ Lets us restrict
  `A ≫ Δ^{4/3}(H^4/X)^{1/3}`.

**Lemma 3.1** (gap lower bound in `D_a`): for nested `d<d+b` in `D_a`,
`b ≫ a^{-1/3}Δ^{5/3}(H^5/X)^{1/3}`.
- `J = -(b-a)m_1+(b+a)m_2-(b+a)m_3+(b-a)m_4 ∈ ℤ` with `J = S_{a,b}(d)+O((a+b)H/D²)`.
- **Exact factorization** (sympy-verified):
  `S_{a,b}(d) = X·ab(a-b)(a+b)(a+b+2d)(ab+2ad+2bd+2d²) / [d²(d+a)²(d+b)²(d+a+b)²]`.
- For `b ≫ a`, `|S| ≍ Xab³/D^5`; threshold `b_* ≍ (D^5/(Xa))^{1/3} = a^{-1/3}Δ^{5/3}(H^5/X)^{1/3}` ✓.
- Below threshold `|S| < 1/2`; error/`|S| ≪ 1/Δ` (uses `a ≫ Δ^{4/3}(H^4/X)^{1/3}`), and `S ≠ 0`
  (product of nonzero factors), giving `0 < |J| < 1`, contradiction. ✓

**Roth quantity** `R_a(d) = -(2d-a)X/d² + (2d+3a)X/(d+a)²`. **Identity (sympy-verified):**
`R_a(d) = X a³/(d²(d+a)²) = (Xa³/d⁴)(1 - 2a/d + O((a/d)²))`. ✓
- `R := XA³/(Δ⁴H⁴) = HGΩ³/Δ` ✓ (uses `X=GH^5`, `A=ΩΔ`). ` d̃_a = R_a^{-1}`,
  `d̃_a^{(j)}(ρ) ≍ HΔ/R^j` ✓.

**Prop 3.2**: map `d*_a: R_a → D_a`, `#D_a/#R_a ≪ 1 + Ω^{-8/3}G^{-2/3}`, and
`d*_a(r) = d̃_a(r) + O((Δ/G)(Δ³/A³))`.
- `R_a(d) ∈ ℤ + O(1/Δ)` (because `(2d±·)X/d²·` lands within `O(H/D)=O(1/Δ)` of an integer). ✓
- Fiber size `k`: odd-indexed subsequence is pairwise non-consecutive in `D_a`, Lemma 3.1
  gives `|d_1-d_k| ≫ k·a^{-1/3}Δ^{5/3}(H^5/X)^{1/3}`; MVT with `R_a' ≍ XA³/D^5`.
  **⚠ Non-sharpness:** the actual product is
  `|R_a(d_1)-R_a(d_k)| ≫ k·G^{2/3}Ω^{8/3}Δ^{-2/3}`, whereas line 377 writes
  `≫ (k/Δ)Ω^{8/3}G^{2/3} = k·G^{2/3}Ω^{8/3}Δ^{-1}`. Since `Δ ≥ 1`, the paper's value is
  *smaller* (weaker), so the stated `k ≪ 1+Ω^{-8/3}G^{-2/3}` is a **valid (if non-sharp)**
  upper bound; the sharp bound is a factor `Δ^{1/3}` better. **No correctness impact** — only
  the weak form is used, and downstream it is bounded by `X^{O(u)}` via `Ω ≫ G^{-1/4}U^{-3/4}`
  (`Ω^{-8/3}G^{-2/3} ≪ U²`). Formalize the stated (weak) bound.
- Approximation: Newton step error `≍ (HΔ/R)(1/Δ) = H/R = Δ⁴/(GA³) = (Δ/G)(Δ³/A³)` ✓.
- `Ω := A/Δ`; restrict `G^{-1/4}U^{-3/4} ≪ Ω ≪ U` (upper from `A ≪ ΔU`). ✓

## §4 Point-near-curve lemmas (lines 411–672) — CORRECT (one standard caveat)

**Lemma 4.2** (derivative-band counting): `|φ'|≪T/N`, `|φ'|+N|φ''| ≍ T/N`, `O(1)` zeros each ⇒
`Σ 1_{‖φ‖≤δ} ≪ N(δ+√(δ/T)) + T + 1`.
- Dyadic decomposition in `|φ'| ≍ e^{-k}T/N`: `|I_k| ≪ e^{-k}N`, `var(φ|I_k) ≍ e^{-2k}T`,
  Lemma 4.1 per band; the `e^K δN/T` term with `K = ½log(T/δ)` gives `N√(δ/T)`. ✓
- **⚠ Caveat:** the naive sum of the "+1"s over the `≈ K ≍ log(T/δ)` bands yields a stray
  `log` factor. The paper's statement omits it. This is **harmless** here: every later use
  (Prop 4.3, §6, §7) is in a range where logs are `X^{o(1)}` and explicitly "absorbed by
  shrinking `c`" / into `X^{O(u)}`. Attempt-1's `Counting/DerivativeBands.lean` is **not**
  on the remaining-sorry list, so a Lean-usable form was provable. Decide early whether the
  Lean statement carries an explicit `log`-factor or a clever log-free argument.

**Prop 4.3** (integer points near a curve, `|F''|≍1`):
`#{n~N: ‖TF(n/N)‖≤δ} ≪ (NT)^{1/3} + Nδ + N√(δ/T)·log(2+N√(δ/T)) + 1`.
- `f=TF(x/N)`, `λ=T/N² ≍ f''`. Non-collinear triple spans `≫ min(λ^{-1/3}, δ^{-1})` via
  divided-difference identity `u/[(n1-n0)(n2-n1)(n2-n0)] = f''(ξ)/2 + O(δ·Σ…)`, `|u|≥1` ⇒
  `1 ≪ λL³ + δL`. ✓
- Major arcs (rational lines `y=P(x)`, denominator `q`): `ν(A) ≪ L/q`, `q ≪ L`, `L ≪ √(δ/λ)`. ✓
- Residual set: 5 consecutive non-arc points span `≫ min(λ^{-1/3},δ^{-1})` ⇒ `≪ Nλ^{1/3}+Nδ+1`.
- Type I (`L ≤ δ√(q/λ)`): disjoint-interval packing ⇒ `≪ Nδ+1`.
- Type II (`L > δ√(q/λ)`, hence `q ≪ √(δ/λ)`): convexity localizes ⇒ `O(1)` arcs per `(q,r)`,
  `O(qNλ+1)` slopes; summing ⇒ `Nδ + √(δ/λ)log(2+√(δ/λ)) + 1`. ✓
- This is the classical "integers near a smooth curve" theorem; main term `Nλ^{1/3}=(NT)^{1/3}`.
  The most intricate *classical* lemma — but attempt-1 **completed** it (`Geometry/NearCurve.lean`,
  not on sorry list), so it is feasible. Treat as a self-contained module.

## §5 The range `Δ ≪ H^{1/2}(GU)^{-O(1)}` — Prop 5.1 (lines 676–1225) — CORRECT

Setup: `R_a(ℓ1,ℓ2)` (consecutive `R_a`-triples), `b_0, v ∈ ℓ1^{-1}ℤ`, `B = D/R ≍ Δ²/(GΩ³)`,
`v ≪ ΔU^5/Ω³`. Verified scale identities:
- `B = Δ²/(GΩ³)` ✓; `XaB/D^5 = 1/(Δ²Ω²)` (sympy-style check ✓); `XaB³/D^6 = Δ/(HG²Ω^8)` ✓.
- `Ŝ_{a,b}(d) = (X/d^5)(-4ab³ + (10ab⁴+10a²b³)/d + O(…))`, `F_{a,b}(d) = (X/d⁴)(6ab - …)`.
The five steps (zero-defect `v=0`; small-defect `0<|v|≤V_+`; monotone; large-defect via
`Υ` with cubic/quartic `p_1,p_2`; combine) are pure Taylor-expansion + exponent bookkeeping
producing the 7-term then 3-term bound
`#R_a ≪ (H/Δ)(G^9U^{51}Δ^{-1/2}Ω^{-1} + G^{17}U^{85}Δ^{-1}Ω^{-13} + (Δ²/H)G^{17}U^{100}Ω^{-27})`.
This is long but mechanical. **Note:** the final theorem (§9) routes through §7's `W_{≠0}`,
not Prop 5.1; Prop 5.1 is used only to define the unresolved strip via Prop 8.1, and
attempt-1 has it **done** (not on sorry list). Highest-volume but low-risk section.

## §6 The range `Δ ≳ H^{1/2}` — Prop 6.1 (lines 1228–1308) — CORRECT

- `f̃_a(r) = F_a(d̃_a(r))`, viewed as a function of **`a`**; claim
  `|f̃_a|, A|∂_a f̃_a|, A²|∂_a² f̃_a| ≍ F = H²GΩ/Δ² = HxGΩ`.
- Apply Prop 4.3 in `a`: `N=A`, `T=F`, `δ = H/(Δ²Ω²) = x/Ω²`. Verified term-by-term:
  `R·(H/A) = HxGΩ²`, `R·(AF)^{1/3} = Hx^{2/3}G^{4/3}Ω^{11/3}`, `R·A√(δ/F) = H^{1/2}G^{1/2}Ω^{5/2}`,
  giving the stated `Σ_{a~A}#R_a ≪ HX^{O(u)}(xGΩ² + x^{2/3}G^{4/3}Ω^{11/3} + H^{-1/2}G^{1/2}Ω^{5/2})`. ✓
- **Remaining attempt-1 sorry** is here. The math is fine; what is unfinished is the
  real-analysis verification of the three `∂_a`-size conditions and the `|F''|≍1` curvature
  hypothesis of Prop 4.3 for this specific `f̃_a`. This is the one "easy-looking but unfinished"
  piece — a good early win for attempt 2.

## §7 The final direct small-value argument (lines 1312–2000) — CORRECT; the crux

Verified scale algebra: `x=H/Δ²`, `Δ=H^{1/2}x^{-1/2}`, `R=H^{1/2}x^{1/2}GΩ³`,
`T_1=H^{1/2}x^{-3/2}(GΩ)^{-1}`, `T_2=F=HxGΩ`, `T_3=HΔ=H^{3/2}x^{-1/2}`, with
`T_1/R=x^{-2}G^{-2}Ω^{-4}`, `T_2/R²=G^{-1}Ω^{-5}`, `T_3/R³=x^{-2}G^{-3}Ω^{-9}`, `T_1T_2=T_3`. All ✓.

Structure:
- Reduce `#R_a ≤ Σ_{|j|≪1+H/A²} Σ_r 1_{‖g_j(r)‖≤δ_0}`, `g_j(r) = f_3 + f_1·{f_2}` with
  `f_3 = d̆_a(f̃_a+j)`, `f_1 = -d̆_a'(f̃_a+j)`, `f_2 = f̃_a`, `d̆_a = F_a^{-1}`.
- **Lemma 7.2** averaged popular cube over the rectangular box `h_1≤W, h_2≤W², h_3≤W⁴`
  gives `Σ|E_3| ≫ R/W` — no per-triple product lower bound needed (key change from a literal
  3-fold Lemma 2.2).
- Per triple: third difference of `f_1{f_2}` (eq 7.1) keeps integer carries `ρ_0,ρ_i` and
  fiber data `u_i`; fiber count `O(1+S/(GΩ^5))` (eq 7.2). Reduces to `‖Φ_{ρ,u}(r)‖ ≪ δ_1(h)`.
- Leading-monomial expansion (eq 7.5): with `y=r/R`, principal part is
  `c_1ρ_0T_1 y^{-1} + c_1(T_1/R)(Σh_i(u_i-ρ_i) - ρ_0 h_Σ)y^{-2} + C_* P (T_3/R³) y^{-13/4}`.
  **Key non-degeneracy (sympy-verified):** `c_3 = 3c_1c_2` (from `f_3' = -f_1 f_2'`), the
  `y^{-13/4}` coefficient is `15/64 + 9/16 - (45/64)·3 = -84/64`, so `C_* = -21/16·c_1c_2 ≠ 0`. ✓

Two branches:
- **`ρ_0 = 0`** (zero top carry): `y^{-1}` absent; two monomials `y^{-2}, y^{-13/4}` have
  nonzero Wronskian ⇒ Lemma 4.2 applies with scale `T_{ρ,u} ≍ |B_{ρ,u}| + |C_* P T_3/R³|`.
  Remainders shown subordinate (`h_Σ²T_1/R² ≪ PT_3/R³` etc. by the `W`-constraints). Summing
  over the box with the elementary sums (lines 1800–1819) yields the "old nine" constraints +
  offset constraints (7.7) + four no-absorption residual constraints. Bottleneck
  `W_old = H^{1/54}x^{1/54}G^{2/27}Ω^{8/27}`.
- **`ρ_0 ≠ 0`** (nonzero top carry): `c_1ρ_0T_1 y^{-1}` dominates; treated by a **local** Prop 4.3
  on `O(1)` pieces where `y^{-3}` varies by `O(1)`, with normalized `1 ≤ |F''| ≤ 2`. Needs the
  genuine side conditions `R ≥ W^8 > 1`, `T_1 > 1 ⇔ x³G²Ω² < H` (a real §4 side condition,
  verified in the final application from the strip, line 1904–1916), `0 < δ_1(h) < 1`. Summing
  gives the new constraints incl. bottleneck `W_{≠0} = H^{1/84}x^{5/84}G^{1/7}Ω^{11/21}`.

The full admissibility envelope (lines 1437–1467) is explicitly written in *Lean-facing*
form — nine integer-power constraints + 4 no-absorption residuals + 2 offset + 10 nonzero-carry
+ §4.3 side conditions. **This is the heart of the work and the two remaining attempt-1 sorries
(`section7_local_tripleDiff_{zero,nonzero}TopCarry_bound_md`) live exactly here.**

**Prop 7.3**: `#R_a ≪ (1+H/A²)(R/W)` by applying 7.1 over the `O(1+H/A²)` values of `j`. ✓

## §8 Consequences — Prop 8.1 (lines 2004–2079) — CORRECT

Combines Props 5.1 and 6.1. Using `D(Ω) ≪ X^{O(u)} Σ_a #R_a`:
- From 6.1: drop unless `x ≪ G^{-2}Ω^{-11/2}X^{-O(u)}` (and first term then `O(U^{-1})`).
- From 5.1: drop unless `x ≫ G^{17}Ω^{-26}X^{O(u)}` (first/third terms `O(U^{-1})` via `Δ≥X^{1/100}`).
- Unresolved **strip**: `G^{-2}Ω^{-11/2}X^{-O(u)} ≪ x ≪ G^{17}Ω^{-26}X^{O(u)}`. ✓

## §9 Global optimization (lines 2083–2237) — CORRECT; clinches the exponent

- On the strip, compare bottlenecks `W_old` vs `W_{≠0}`: `W_old/W_{≠0}` has negative `x`-exponent
  (min at `x = G^{17}Ω^{-26}`) and positive `Ω`-exponent (min at `Ω = G^{-1/4}`), giving
  `≫ X^{1/756 - 1477g/1512} ≫ 1` for `g < 2/18977` (threshold `2/1477 > 2/18977`, ✓). Hence
  `W_* = W_{≠0}` throughout. Other §7 constraints shown larger.
- `A(1+H/A²)R ≍ HGΩ⁴(1+x/Ω²)` ✓ ⇒ (9.1):
  `D(Ω)/H ≪ X^{O(u)}H^{-1/84}G^{6/7}(Ω^{73/21}x^{-5/84} + Ω^{31/21}x^{79/84})` (both terms verified).
- Term 1 worst at lower edge `x=G^{-2}Ω^{-11/2}` ⇒ condition (9.2). Term 2 worst at upper edge
  `x=G^{17}Ω^{-26}` then lower `Ω=G^{-1/4}U^{-3/4}` ⇒ condition (9.3), which dominates.
- **(9.3) reduces exactly to `18977 g + 15315 u < 2`** (sympy: `840·expr = 18977g+15315u-2`). ✓
  So for every `g < 2/18977`, small `u` works. Summing over `O(log X)=X^{O(u)}` dyadic `Ω`-scales
  and over the §1 dyadic `D`-scales, then Möbius inversion, gives the theorem.
- Final: `g = 2/18977 - 5ε ⇒ H = X^{1/5 - 2/94885 + ε}`. ✓

## §10 Summary — `θ_* ≤ 1/5 - 2/94885`. ✓

---

## Flagged items for the formalizer (all benign)

1. **Prop 3.2 fiber bound** (line 377) is non-sharp by `Δ^{1/3}` but the *stated, weaker* bound
   is valid and is the one used; formalize as written.
2. **Lemma 4.2** as literally stated may need an explicit `log(T/δ)` factor (or a sharper
   argument); either is fine since logs are `X^{o(1)}` everywhere downstream. Fix the Lean
   statement convention once, up front.
3. The `X^{O(u)}` convention is a **uniform linear `u`-budget**; choose one global mechanism
   (e.g. carry an explicit constant `C` and a hypothesis `u < c(g)`) and reuse it. Every "drop
   this term" step is an instance of the same `α(g) + O(u) < 0` lemma.
4. Many `≍`/`≪` steps hide constants that depend only on the curve `F` (with `|F''|≍1`); keep
   those constants absolute and threaded, not re-derived per call site.
