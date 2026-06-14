# Working instructions — squarefree formalization (attempt 2, clean-room)

This file is the operating manual for formalizing `explicit_writeup.md` in Lean.
Read it, follow it. Keep it short; if it grows, prune it.

## 0. Prime directive: protect context

Attempt 1 (`../explicit_formal/squarefree_lean`) reached ~99.9% but became unworkable:
dozens of scratch plan `.md`s, ~30 overlapping `Wstar*`/`Section7*` files, giant modules.
The agent drowned in its own context. **Do not repeat this.** Every rule below exists to
keep the *orchestrator's* working context small and the file tree legible.

- **You (the main session) are an orchestrator.** Hold the plan and the dependency graph.
  Delegate context-heavy work (writing/iterating proofs, grepping mathlib, parsing build
  dumps, sympy checks) to the subagents in `.claude/agents/` so their context churn stays
  out of yours. See §5.
- Never paste long build output or whole large files into your reasoning. Grep for the
  span you need. If a file is >~400 lines, that is a smell — split it.
- **One plan doc, updated in place.** `formalization_plan.md` is the single source of plan
  truth. Do NOT create `*_plan_v2.md`, `*_remaining.md`, `*_execution.md`, etc. If you need
  a checklist, keep it as a short section in the plan and edit it.
- Scratch goes in `tmp/` and is deleted when done. Never commit `tmp/`.

## 1. Layout

```
2explicit_2formal/
  explicit_writeup.md      -- the paper (source of mathematical truth; do not edit)
  math_audit.md            -- verified audit (read for "is this step correct?")
  formalization_plan.md    -- THE plan + checklist (edit in place)
  CLAUDE.md                -- this file
  .claude/agents/          -- the subagent ensemble
  squarefree_lean/         -- the Lean project (lakefile.toml lives here)  [create at M1]
    SquarefreeLean/...      -- modules, per the plan's module DAG
    tmp/                    -- scratch only; deletable
```
Build/verify from the Lean project root (`squarefree_lean/`): `lake build <Module>`.

## 2. The working loop (per lemma)

1. Pick the next item from `formalization_plan.md` (respect the dependency order: Params →
   engine → regimes → §7 → optimization → Main; milestones M1–M6).
2. State the Lean signature you intend, faithful to the md. If unsure it's faithful or the
   algebra is delicate, delegate a check to **math-auditor**.
3. If you need a mathlib/in-project API, delegate to **mathlib-scout** rather than grepping.
4. Delegate the proof to **lean-prover** with: the exact signature, the relevant md line
   range, the math sketch from `math_audit.md`, and available helper lemmas.
5. On a red build you didn't expect, delegate to **lean-build-doctor** for a concise diagnosis.
6. Update the checklist in `formalization_plan.md`. Refresh the dashboard (§6).

Do small units. One substantial lemma per delegated task. Land it green before the next.

## 3. Hard rules (non-negotiable)

- **Faithful statements.** Public/exported statements must match the md. Never weaken a public
  theorem to close a file (e.g. replacing a real bound by a trivial interval cardinality).
  If a public theorem needs a stronger local estimate, finish the estimate.
- **No cheating the kernel.** No `sorry`, `admit`, `axiom`, `native_decide`, `@[implemented_by]`,
  or `Classical`-hacks used to fake a proof. A `sorry` is allowed *only* as an explicitly
  tracked, named scaffolding stub (see §4) — never silently.
- **Green before done.** A task is finished only when `lake build` of the touched module(s)
  succeeds with no new `sorry`/`axiom` reachable from the target. Report the build result
  honestly; if it fails, say so with the error, don't claim success.
- **Don't settle / don't thrash.** If a route is wrong, switch routes (decompose into
  sub-lemmas) and keep going. But if genuinely blocked, stop and report the precise blocker
  (which decl/def is missing and why) — do not loop.
- **Small files, private helpers.** One theme per file (≤ ~400 lines). Keep helper lemmas
  `private` unless another module needs them. Don't proliferate near-duplicate files.

## 4. Scaffolding stubs (tracked sorries)

When you state a lemma before proving it, mark it: `sorry -- STUB: <plan item id>`. The
dashboard counts these. The invariant: **every `sorry` in the tree maps to a named plan
item**, and the count only goes down. No orphan sorries.

## 5. Subagents (delegate to protect context)

Spawn with the Agent tool. Each starts cold — give it everything it needs in the prompt
(signature, md line range, file paths, acceptance criteria). Relay only the distilled result
back; do not dump its transcript into your context.

- **lean-prover** — close a stated Lean goal to a green build. The workhorse.
- **mathlib-scout** — read-only: find exact mathlib/in-project lemma names, signatures, imports.
- **math-auditor** — verify a math step/identity against `explicit_writeup.md` (+ sympy);
  confirm a Lean statement is faithful before you invest in proving it.
- **lean-build-doctor** — diagnose a red/regressed build concisely; propose the minimal fix.

Prefer one focused delegation over a vague broad one. Don't spawn for trivial edits you can
do in two lines yourself.

## 6. Progress dashboard

Keep a lightweight, reproducible signal of state. Minimum: a script that runs `lake build`
and counts `sorry`/`axiom` per module, written to `squarefree_lean/progress/summary.txt`.
Refresh after landing each lemma. (Borrow the *idea* from attempt 1's `tools/`, not its code.)

## 7. Math conventions (see `formalization_plan.md` §5 for detail)

- `X^{O(u)}` is a **uniform linear budget**: model as explicit constants + a hypothesis
  `u ≤ c(g)`, threaded as section variables. One reusable "α(g)<0 ⇒ term ≤ U^{-1}" lemma.
- `≍` / `≪`: two-sided / one-sided bounds with **absolute** constants; keep constants out of
  statement conclusions (use `∃ C, …` only at module boundaries).
- Formalize the *stated* bounds, including the two benign non-sharp ones flagged in
  `math_audit.md` (Prop 3.2 fiber bound; Lemma 4.2 log) — don't chase sharper forms.

## 8. Lessons paid for in §5 (binding practice)

- **Contract-first.** Before building a section's lemmas, state its frontier proposition with the FULL
  hypothesis pack and land the caller discharging that pack against the stub. A hypothesis no caller can
  discharge must fail a build immediately — never let a sorried stub make hypotheses free.
- **No ad-hoc ambient hypotheses.** The standing regime is the writeup's (line 406: G^{-1/4}U^{-3/4} ≤ Ω ≤ U;
  no Ω≥1, no G≤U). Convenience facts must be derived lemmas, not new binders; template-copied hypothesis
  blocks are how Ω≥1 infected 130 signatures.
- **Freeze shapes, not numbers.** In delegated interfaces fix statement shapes; constants are re-derived by
  sympy at the point of use. Keep the constant/budget bookkeeping in ONE place and re-check it after any bump.
- **Audit at section entry, not exit:** statement-vs-md, call-site dischargeability, constants, boundary
  coherence — before proving.
- **Subagent turns >32k output tokens die with zero disk output** (thinking explosion on monomial algebra).
  Mitigate: sympy-via-Bash for all exponent arithmetic, ≤200 words prose/turn, first Write within 6 actions,
  one decl per edit, build per decl, half-scope units, final report ≤15 lines.

## 9. Git

- Branch off `main` before committing; commit/push only when the user asks.
- **Never** add a `Co-Authored-By: Claude/Anthropic` trailer to commits.
