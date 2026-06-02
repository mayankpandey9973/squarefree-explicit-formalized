#!/usr/bin/env python3
"""Compute Lean formalization status for the squarefree project.

Python 3 STDLIB ONLY. Safe to run anytime: honors the bootstrap.done gate and a
flock-based build lock so two `lake build`s never run at once.

Writes <root>/progress/status.json with:
  - generated_at (ISO8601)
  - bootstrap_done (bool)
  - build_ran (bool)         -- whether we actually invoked lake build this run
  - modules: [ {module, file, layer, exists, status, theorem_count, def_count,
               sorry_count, stub_count, axiom_count, build_status, edges,
               expected_count, present_count, missing, last_checked} ... ]

Status values per module:
  planned     -- the .lean file does not exist yet
  scaffolded  -- file exists but no planned deliverable is present yet
                 (when no plan exists for the module: file exists but states NO theorem)
  error       -- lake build attributes a compile error to this file
  in-progress -- source still contains sorry / STUB: / axiom
  partial     -- some planned deliverables are present but not all (no sorry/STUB/axiom)
  done        -- every planned deliverable is present, builds, and no sorry / STUB / axiom
                 (when no plan exists: has >=1 stated theorem, builds, no sorry / STUB / axiom)
  checking    -- build is in-flight / lock busy / timed out (keep last-known)

PLAN-COMPLETENESS: for modules that have an entry in progress/plan_manifest.json,
"done" (green) means *all* expected deliverables are present and proven -- not merely that
the file compiles. `expected_count` is the number of planned deliverables; `present_count`
is how many of them are actually declared in the source; `missing` lists the rest. A module
with deliverables present but missing some is `partial` (amber). A module that compiles but
proves none of its planned deliverables is `scaffolded`. For modules with no manifest entry
the legacy theorem-count rule applies (a file with only definitions and no theorem is
`scaffolded`, not `done` -- compiling is necessary but not sufficient for "done").
"""

import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
TOOLS_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(TOOLS_DIR)  # squarefree_lean
PROGRESS = os.path.join(ROOT, "progress")
SRC_ROOT = os.path.join(ROOT, "Squarefree")
ROOT_LEAN = os.path.join(ROOT, "Squarefree.lean")
STATUS_JSON = os.path.join(PROGRESS, "status.json")
PLAN_MANIFEST = os.path.join(PROGRESS, "plan_manifest.json")
BOOTSTRAP_DONE = os.path.join(PROGRESS, "bootstrap.done")
BUILD_LOCK = os.path.join(PROGRESS, ".lakebuild.lock")
BUILD_LOG = os.path.join(PROGRESS, "build.log")

BUILD_TIMEOUT = 900  # seconds

# ---------------------------------------------------------------------------
# Authoritative planned node list: module -> (relative file, layer)
# ---------------------------------------------------------------------------
PLANNED = {
    # L0
    "Squarefree.Asymp": ("Squarefree/Asymp.lean", "L0"),
    "Squarefree.Params": ("Squarefree/Params.lean", "L0"),
    "Squarefree.Budget": ("Squarefree/Budget.lean", "L0"),
    "Squarefree.FiniteDiff": ("Squarefree/FiniteDiff.lean", "L0"),
    # L1
    "Squarefree.Counting.Preimage": ("Squarefree/Counting/Preimage.lean", "L1"),
    "Squarefree.Counting.PopularDiff": ("Squarefree/Counting/PopularDiff.lean", "L1"),
    "Squarefree.Counting.FourthDeriv": ("Squarefree/Counting/FourthDeriv.lean", "L1"),
    "Squarefree.Counting.Bands": ("Squarefree/Counting/Bands.lean", "L1"),
    "Squarefree.Geometry.NearCurve": ("Squarefree/Geometry/NearCurve.lean", "L1"),
    # L2
    "Squarefree.Structure.SabFactor": ("Squarefree/Structure/SabFactor.lean", "L2"),
    "Squarefree.Structure.DaSpacing": ("Squarefree/Structure/DaSpacing.lean", "L2"),
    # L3
    "Squarefree.ShortDelta": ("Squarefree/ShortDelta.lean", "L3"),
    "Squarefree.Lower.Prop51": ("Squarefree/Lower/Prop51.lean", "L3"),
    "Squarefree.Upper.Regime": ("Squarefree/Upper/Regime.lean", "L3"),
    # L4
    "Squarefree.Bracket.Admissible": ("Squarefree/Bracket/Admissible.lean", "L4"),
    "Squarefree.Bracket.Carry": ("Squarefree/Bracket/Carry.lean", "L4"),
    "Squarefree.Bracket.LocalZero": ("Squarefree/Bracket/LocalZero.lean", "L4"),
    "Squarefree.Bracket.LocalNonzero": ("Squarefree/Bracket/LocalNonzero.lean", "L4"),
    "Squarefree.Bracket.BoxSum": ("Squarefree/Bracket/BoxSum.lean", "L4"),
    # L5
    "Squarefree.Opt.Strip": ("Squarefree/Opt/Strip.lean", "L5"),
    "Squarefree.Opt.Global": ("Squarefree/Opt/Global.lean", "L5"),
    "Squarefree.Dyadic": ("Squarefree/Dyadic.lean", "L5"),
    "Squarefree.Main": ("Squarefree/Main.lean", "L5"),
}

# ---------------------------------------------------------------------------
# Planned fallback dependency edges (module -> list of dependency modules).
# Names here are the short labels; we resolve them to full module names below.
# ---------------------------------------------------------------------------
SHORT2FULL = {
    "Asymp": "Squarefree.Asymp",
    "Params": "Squarefree.Params",
    "Budget": "Squarefree.Budget",
    "FiniteDiff": "Squarefree.FiniteDiff",
    "Counting.Preimage": "Squarefree.Counting.Preimage",
    "Counting.PopularDiff": "Squarefree.Counting.PopularDiff",
    "Counting.FourthDeriv": "Squarefree.Counting.FourthDeriv",
    "Counting.Bands": "Squarefree.Counting.Bands",
    "Geometry.NearCurve": "Squarefree.Geometry.NearCurve",
    "Structure.SabFactor": "Squarefree.Structure.SabFactor",
    "Structure.DaSpacing": "Squarefree.Structure.DaSpacing",
    "ShortDelta": "Squarefree.ShortDelta",
    "Lower.Prop51": "Squarefree.Lower.Prop51",
    "Upper.Regime": "Squarefree.Upper.Regime",
    "Bracket.Admissible": "Squarefree.Bracket.Admissible",
    "Bracket.Carry": "Squarefree.Bracket.Carry",
    "Bracket.LocalZero": "Squarefree.Bracket.LocalZero",
    "Bracket.LocalNonzero": "Squarefree.Bracket.LocalNonzero",
    "Bracket.BoxSum": "Squarefree.Bracket.BoxSum",
    "Opt.Strip": "Squarefree.Opt.Strip",
    "Opt.Global": "Squarefree.Opt.Global",
    "Dyadic": "Squarefree.Dyadic",
    "Main": "Squarefree.Main",
}

PLANNED_EDGES_SHORT = {
    "Budget": ["Params", "Asymp"],
    "FiniteDiff": [],
    "Counting.FourthDeriv": ["FiniteDiff", "Counting.PopularDiff", "Counting.Preimage"],
    "Counting.Bands": ["Counting.Preimage"],
    "Geometry.NearCurve": ["FiniteDiff", "Counting.Preimage"],
    "Structure.SabFactor": ["Params"],
    "Structure.DaSpacing": ["Structure.SabFactor", "Params"],
    "ShortDelta": ["Counting.FourthDeriv", "Params"],
    "Lower.Prop51": ["Counting.Bands", "Structure.DaSpacing", "Params", "Budget"],
    "Upper.Regime": ["Geometry.NearCurve", "Structure.DaSpacing", "Params", "Budget"],
    "Bracket.Admissible": ["Params"],
    "Bracket.Carry": ["FiniteDiff", "Structure.DaSpacing", "Structure.SabFactor", "Params"],
    "Bracket.LocalZero": ["Bracket.Carry", "Counting.Bands", "Bracket.Admissible"],
    "Bracket.LocalNonzero": ["Bracket.Carry", "Geometry.NearCurve", "Bracket.Admissible"],
    "Bracket.BoxSum": ["Bracket.LocalZero", "Bracket.LocalNonzero", "Bracket.Admissible"],
    "Opt.Strip": ["Lower.Prop51", "Upper.Regime", "Budget"],
    "Opt.Global": ["Opt.Strip", "Bracket.BoxSum", "Budget"],
    "Dyadic": ["Budget"],
    "Main": ["Opt.Global", "Opt.Strip", "Dyadic"],
}


def planned_edges_full():
    """Return {full_module: [full_dep, ...]} from the planned fallback."""
    out = {}
    for short, deps in PLANNED_EDGES_SHORT.items():
        full = SHORT2FULL[short]
        out[full] = [SHORT2FULL[d] for d in deps]
    return out


# ---------------------------------------------------------------------------
# Plan manifest (machine-readable mirror of formalization_plan.md §2)
# ---------------------------------------------------------------------------
def load_plan_manifest():
    """Return {full_module: [expected_name, ...]} from plan_manifest.json.

    If the file is missing or unreadable, return {} so every module falls back
    to the legacy (theorem-count based) classification.
    """
    try:
        with open(PLAN_MANIFEST, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return {}
    out = {}
    if isinstance(data, dict):
        for mod, names in data.items():
            if isinstance(names, list):
                out[mod] = [str(n) for n in names]
    return out


def present_expected_names(abspath, expected_names):
    """Return the subset of `expected_names` declared in the source at abspath.

    A name is "present" when it appears as the declared identifier of a
    theorem/lemma/def/structure/abbrev/instance, allowing leading modifiers
    (private/protected/noncomputable/...) and an optional attribute block.
    Unicode identifiers (e.g. T₁_mul_T₂_eq_T₃) are supported. Declarations
    inside comments are ignored (we analyze comment-stripped code).
    """
    if not expected_names:
        return []
    try:
        with open(abspath, "r", encoding="utf-8", errors="replace") as f:
            raw = f.read()
    except OSError:
        return []
    code = strip_block_comments(raw)
    code_lines = [strip_line_comment(ln) for ln in code.splitlines()]
    present = []
    for name in expected_names:
        # Match: optional @[...], then modifiers, then keyword, then the exact
        # name as a whole token. \b is unreliable next to unicode subscripts,
        # so require a non-identifier boundary (or end of line) after the name.
        pat = re.compile(
            r"^\s*(?:@\[[^\]]*\]\s*)?"
            r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*"
            r"(?:theorem|lemma|def|structure|abbrev|instance)\s+"
            + re.escape(name)
            + r"(?![\w'])"
        )
        if any(pat.match(ln) for ln in code_lines):
            present.append(name)
    return present


# ---------------------------------------------------------------------------
# Discovery & path<->module mapping
# ---------------------------------------------------------------------------
def module_of_relpath(relpath):
    """'Squarefree/Counting/Bands.lean' -> 'Squarefree.Counting.Bands'."""
    no_ext = relpath[:-5] if relpath.endswith(".lean") else relpath
    return no_ext.replace(os.sep, ".").replace("/", ".")


def relpath_of_module(module):
    return module.replace(".", "/") + ".lean"


def discover_files():
    """Auto-discover every *.lean under Squarefree/ plus root Squarefree.lean.

    Returns {full_module: abs_path}.
    """
    found = {}
    if os.path.isfile(ROOT_LEAN):
        found["Squarefree"] = ROOT_LEAN
    if os.path.isdir(SRC_ROOT):
        for dirpath, _dirs, files in os.walk(SRC_ROOT):
            for fn in files:
                if not fn.endswith(".lean"):
                    continue
                abspath = os.path.join(dirpath, fn)
                rel = os.path.relpath(abspath, ROOT)
                found[module_of_relpath(rel)] = abspath
    return found


# ---------------------------------------------------------------------------
# Source-level facts
# ---------------------------------------------------------------------------
# Match declaration keywords at start of a line (allowing common modifiers).
DECL_THEOREM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*(theorem|lemma)\b")
DECL_DEF = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*(def|abbrev|instance|structure|inductive|class)\b")
AXIOM_RE = re.compile(r"^\s*(?:private\s+|protected\s+)?axiom\b")
# `sorry` as a token (not inside a longer identifier).
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")
STUB_RE = re.compile(r"STUB:")


def strip_block_comments(text):
    """Remove /- ... -/ block comments (handles nesting) so we don't count
    `sorry`/keywords that appear only in docstrings/comments. Line comments
    (`--`) are stripped per-line elsewhere."""
    out = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
            continue
        if two == "-/" and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def strip_line_comment(line):
    idx = line.find("--")
    if idx != -1:
        return line[:idx]
    return line


def analyze_source(abspath):
    """Return source-derived facts for a file."""
    facts = {
        "theorem_count": 0,
        "def_count": 0,
        "sorry_count": 0,
        "stub_count": 0,
        "axiom_count": 0,
        "imports": [],
    }
    try:
        with open(abspath, "r", encoding="utf-8", errors="replace") as f:
            raw = f.read()
    except OSError:
        return facts

    # Imports parsed from raw (before comment stripping is fine; imports lead lines).
    for m in re.finditer(r"^\s*import\s+(Squarefree(?:\.[A-Za-z0-9_]+)*)\s*$", raw, re.MULTILINE):
        facts["imports"].append(m.group(1))

    # STUB markers: count anywhere (they are intentional textual markers, often in comments).
    facts["stub_count"] = len(STUB_RE.findall(raw))

    # Strip block comments, then per-line strip line comments, for code-token analysis.
    code = strip_block_comments(raw)
    code_lines = [strip_line_comment(ln) for ln in code.splitlines()]
    code_no_comments = "\n".join(code_lines)

    facts["sorry_count"] = len(SORRY_RE.findall(code_no_comments))

    for ln in code_lines:
        if DECL_THEOREM.match(ln):
            facts["theorem_count"] += 1
        elif DECL_DEF.match(ln):
            facts["def_count"] += 1
        if AXIOM_RE.match(ln):
            facts["axiom_count"] += 1

    return facts


# ---------------------------------------------------------------------------
# Build (lake) handling
# ---------------------------------------------------------------------------
def bootstrap_done():
    return os.path.isfile(BOOTSTRAP_DONE)


def run_lake_build():
    """Run `lake build Squarefree` under a flock lock with a timeout.

    Returns (build_ran: bool, error_files: set[abs_or_rel_squarefree_paths],
             timed_out: bool).  error_files holds the *relative-to-root* paths
             (e.g. 'Squarefree/Foo.lean') that lake attributed an error to.
    """
    # Non-blocking lock via O_CREAT|O_EXCL-style flock. Use fcntl.
    import fcntl

    lock_fd = os.open(BUILD_LOCK, os.O_CREAT | os.O_RDWR, 0o644)
    try:
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            # Another build is in flight.
            return (False, set(), False)

        try:
            proc = subprocess.run(
                ["lake", "build", "Squarefree"],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=BUILD_TIMEOUT,
                text=True,
            )
            output = proc.stdout or ""
        except subprocess.TimeoutExpired as e:
            output = (e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")) if e.stdout else ""
            try:
                with open(BUILD_LOG, "w", encoding="utf-8") as f:
                    f.write(output)
            except OSError:
                pass
            return (False, set(), True)

        try:
            with open(BUILD_LOG, "w", encoding="utf-8") as f:
                f.write(output)
        except OSError:
            pass

        error_files = parse_error_files(output)
        return (True, error_files, False)
    finally:
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
        except OSError:
            pass
        os.close(lock_fd)


# error lines look like: /abs/.../Squarefree/Foo.lean:12:0: error: ...
ERR_LINE_RE = re.compile(r"^(?P<path>\S+\.lean):\d+:\d+:\s*error:", re.MULTILINE)


def parse_error_files(output):
    """Return a set of relpaths under Squarefree/ that have errors. Ignore
    files outside Squarefree/ (mathlib)."""
    errs = set()
    for m in ERR_LINE_RE.finditer(output):
        p = m.group("path")
        # Normalize to relative path under ROOT if possible.
        ap = os.path.normpath(p if os.path.isabs(p) else os.path.join(ROOT, p))
        try:
            rel = os.path.relpath(ap, ROOT)
        except ValueError:
            rel = p
        rel = rel.replace(os.sep, "/")
        # Only attribute to our own sources.
        if rel == "Squarefree.lean" or rel.startswith("Squarefree/"):
            errs.add(rel)
    return errs


# ---------------------------------------------------------------------------
# Status classification
# ---------------------------------------------------------------------------
def classify(exists, facts, build_known, has_error, prev_build_status,
             expected_count, present_count):
    """Return (status, build_status).

    build_known is True if we have a fresh build result this run.
    prev_build_status: build_status from a previous status.json (or None).
    expected_count/present_count: plan-manifest deliverable counts for this
    module (both 0 when the module has no manifest entry -> legacy behavior).
    """
    if not exists:
        return ("planned", "n/a")

    has_theorem = facts["theorem_count"] > 0
    has_ssa = (facts["sorry_count"] + facts["stub_count"] + facts["axiom_count"]) > 0

    # Compute build_status the same way regardless of the plan path.
    if build_known:
        build_status = "error" if has_error else "ok"
    else:
        build_status = prev_build_status or "unknown"

    # build_status acts as a stand-in for the doc's notion (error/ok/unknown).
    if build_status == "error":
        return ("error", "error")

    if expected_count == 0:
        # ----- Legacy rule (no plan entry): theorem-count based. -----
        if not has_theorem and not has_ssa:
            # No stated theorem yet (only docs / namespace / helper defs). A module that
            # merely compiles but proves nothing is a placeholder -- it is NOT "done".
            return ("scaffolded", "n/a")
        if build_status == "unknown":
            # No build info (bootstrap not done): use source-only provisional status.
            if has_ssa:
                return ("in-progress", "unknown")
            return ("done", "unknown")  # source looks complete; build unverified
        # build_status == "ok"
        if has_ssa:
            return ("in-progress", "ok")
        return ("done", "ok")

    # ----- Plan-completeness rule (expected_count > 0). -----
    # "done" now requires present == expected AND no sorry/STUB/axiom AND not error.
    if has_ssa:
        return ("in-progress", build_status)
    if present_count == 0:
        return ("scaffolded", build_status)
    if present_count < expected_count:
        return ("partial", build_status)
    # present_count == expected_count
    return ("done", build_status)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def load_prev_build_status():
    """Map module -> prev build_status, for keeping last-known on timeout."""
    out = {}
    try:
        with open(STATUS_JSON, "r", encoding="utf-8") as f:
            data = json.load(f)
        for m in data.get("modules", []):
            out[m["module"]] = m.get("build_status", "unknown")
    except (OSError, ValueError, KeyError):
        pass
    return out


def main():
    os.makedirs(PROGRESS, exist_ok=True)

    discovered = discover_files()  # module -> abspath (real files)
    prev_build = load_prev_build_status()
    plan_manifest = load_plan_manifest()  # module -> [expected_name, ...]

    # Build the universe of modules: planned list ∪ discovered.
    all_modules = set(PLANNED.keys()) | set(discovered.keys())

    boot = bootstrap_done()

    # Decide whether to build.
    build_ran = False
    error_files = set()
    timed_out = False
    if boot:
        build_ran, error_files, timed_out = run_lake_build()

    # Real edges from imports (only for discovered files); planned fallback otherwise.
    planned_full = planned_edges_full()

    modules_out = []
    now = datetime.now(timezone.utc).isoformat()

    for mod in sorted(all_modules):
        abspath = discovered.get(mod)
        exists = abspath is not None
        if mod in PLANNED:
            rel = PLANNED[mod][0]
            layer = PLANNED[mod][1]
        else:
            rel = relpath_of_module(mod)
            layer = "L?"  # discovered but not in planned list

        if exists:
            facts = analyze_source(abspath)
        else:
            facts = {
                "theorem_count": 0, "def_count": 0, "sorry_count": 0,
                "stub_count": 0, "axiom_count": 0, "imports": [],
            }

        # Edges: prefer real imports (filter to Squarefree.* that are known modules
        # or the root). Skip self-import of root pulling everything? Keep all
        # Squarefree.* imports as dependency edges.
        if exists and facts["imports"]:
            edges = [imp for imp in facts["imports"] if imp != mod]
        else:
            edges = planned_full.get(mod, [])

        # Plan-completeness: expected deliverables vs. those present in source.
        expected_names = plan_manifest.get(mod, [])
        if exists and expected_names:
            present_names = present_expected_names(abspath, expected_names)
        else:
            present_names = []
        expected_count = len(expected_names)
        present_count = len(present_names)
        missing = [n for n in expected_names if n not in present_names]

        rel_norm = rel.replace(os.sep, "/")
        has_error = build_ran and (rel_norm in error_files)
        build_known = build_ran  # only true if a fresh non-timed-out build ran

        status, build_status = classify(
            exists, facts, build_known, has_error, prev_build.get(mod),
            expected_count, present_count,
        )

        # If a build timed out while bootstrap done, mark substantive modules checking.
        if boot and timed_out and exists:
            has_theorem = facts["theorem_count"] > 0
            has_ssa = (facts["sorry_count"] + facts["stub_count"] + facts["axiom_count"]) > 0
            if has_theorem or has_ssa or present_count > 0:
                status = "checking"
                build_status = prev_build.get(mod, "unknown")

        modules_out.append({
            "module": mod,
            "file": rel_norm,
            "exists": exists,
            "layer": layer,
            "status": status,
            "build_status": build_status,
            "theorem_count": facts["theorem_count"],
            "def_count": facts["def_count"],
            "sorry_count": facts["sorry_count"],
            "stub_count": facts["stub_count"],
            "axiom_count": facts["axiom_count"],
            "edges": edges,
            "expected_count": expected_count,
            "present_count": present_count,
            "missing": missing,
            "last_checked": now,
        })

    # Totals by status.
    totals = {}
    for m in modules_out:
        totals[m["status"]] = totals.get(m["status"], 0) + 1

    out = {
        "generated_at": now,
        "bootstrap_done": boot,
        "build_ran": build_ran,
        "build_timed_out": timed_out,
        "totals": totals,
        "module_count": len(modules_out),
        "modules": modules_out,
    }

    tmp = STATUS_JSON + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    os.replace(tmp, STATUS_JSON)

    print("[gen_status] wrote %s  (bootstrap_done=%s build_ran=%s timed_out=%s)"
          % (STATUS_JSON, boot, build_ran, timed_out))
    print("[gen_status] totals: %s" % json.dumps(totals))
    return 0


if __name__ == "__main__":
    sys.exit(main())
