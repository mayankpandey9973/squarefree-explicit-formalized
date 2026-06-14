# plan_manifest.json

This file is the machine-readable mirror of [`../../formalization_plan.md`](../../formalization_plan.md) §2: it maps each planned module to the list of public declarations the writeup expects that module to deliver.

**Convention (reconciled with the actual Lean code).** Each entry points at the *real* module path and the *real* top-level declaration name that genuinely states the writeup deliverable — which is **not always the writeup's idealized label**. A name counts as "present" only when the module source actually states it as a `theorem`/`lemma`/`def`/`structure`/`abbrev` (matched by name in the `.lean` file at that module path). When a deliverable was proven under a different decl name than the writeup label, the manifest uses the real Lean name and the writeup correspondence is noted below:

- `preimage_count` = Lemma 4.1/2.3 (`Squarefree.Counting.Preimage`)
- `fourthDeriv_count` = Lemma 2.1 (`Squarefree.Counting.FourthDeriv`)
- `bands_count` = Lemma 4.2 (`Squarefree.Counting.Bands`)
- `nearCurve_count` = Prop 4.3 (`Squarefree.Geometry.NearCurve`)
- `prop_3_2` lives in `Squarefree.Structure.Fiber` (not `DaSpacing`)
- `Sab_factor` = the `S_{a,b}` factorization (writeup 299, a `private` helper in `Squarefree.Structure.DaSpacing`)
- `Rfun_factor` = the `R_a` identity (writeup 334, `Squarefree.Structure.FiberAux`)
- `dblock_off_strip` = Prop 8.1, the unresolved-strip case (`Squarefree.Opt.Strip`)
- `dblock_bound` = §9 global optimization, the merged per-Ω block bound (`Squarefree.Opt.Global`)
- `key_dyadic_assembly` = §1 dyadic key estimate (`Squarefree.DyadicAssembly`)
- `theorem_10_1` = Theorem 10.1 (`Squarefree.Main`)

Unicode identifiers (e.g. `T₁_mul_T₂_eq_T₃`) are supported. The status visualizer reads this manifest to compute each module's `present/expected` count, surface the still-`missing` deliverables, and mark a module green/`done` only when every expected name is present and proven (no `sorry`/`STUB`/`axiom`, clean build). Edit this file whenever the planned deliverables change — add, rename, or remove names here to keep "done" honest with respect to the plan, and always point an entry at the real module+decl rather than an idealized name that does not exist in source.
