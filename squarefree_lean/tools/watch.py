#!/usr/bin/env python3
"""Watcher: re-run gen_status.py when Squarefree/**/*.lean changes (debounced),
and at least every 60s regardless. Also re-runs promptly once bootstrap.done
first appears (so build status kicks in without waiting a full cycle).

Stdlib only — polls mtimes, no external deps.
"""

import os
import subprocess
import sys
import time

TOOLS_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(TOOLS_DIR)
SRC_ROOT = os.path.join(ROOT, "Squarefree")
ROOT_LEAN = os.path.join(ROOT, "Squarefree.lean")
GEN = os.path.join(TOOLS_DIR, "gen_status.py")
PROGRESS = os.path.join(ROOT, "progress")
BOOTSTRAP_DONE = os.path.join(PROGRESS, "bootstrap.done")

POLL_INTERVAL = 2.0       # seconds between mtime scans
DEBOUNCE = 3.0            # seconds of quiet after a change before regenerating
MAX_INTERVAL = 60.0      # force a regen at least this often


def snapshot():
    """Return a dict of lean source path -> mtime."""
    snap = {}
    if os.path.isfile(ROOT_LEAN):
        try:
            snap[ROOT_LEAN] = os.path.getmtime(ROOT_LEAN)
        except OSError:
            pass
    if os.path.isdir(SRC_ROOT):
        for dirpath, _dirs, files in os.walk(SRC_ROOT):
            for fn in files:
                if fn.endswith(".lean"):
                    p = os.path.join(dirpath, fn)
                    try:
                        snap[p] = os.path.getmtime(p)
                    except OSError:
                        pass
    return snap


def regen(reason):
    print("[watch] regenerating (%s)" % reason, flush=True)
    try:
        subprocess.run([sys.executable, GEN], cwd=ROOT, timeout=1200)
    except subprocess.TimeoutExpired:
        print("[watch] gen_status.py timed out", flush=True)
    except Exception as e:  # noqa: BLE001
        print("[watch] gen_status.py error: %r" % e, flush=True)


def main():
    last_snap = snapshot()
    last_regen = 0.0
    pending_since = None
    last_boot = os.path.isfile(BOOTSTRAP_DONE)

    # Initial generation on startup.
    regen("startup")
    last_regen = time.time()

    while True:
        time.sleep(POLL_INTERVAL)
        now = time.time()

        cur = snapshot()
        changed = cur != last_snap
        if changed:
            last_snap = cur
            pending_since = now

        # bootstrap.done just appeared -> regen promptly to pick up builds.
        boot_now = os.path.isfile(BOOTSTRAP_DONE)
        if boot_now and not last_boot:
            last_boot = True
            regen("bootstrap.done appeared")
            last_regen = now
            pending_since = None
            continue
        last_boot = boot_now

        # Debounced change-driven regen.
        if pending_since is not None and (now - pending_since) >= DEBOUNCE:
            regen("source change")
            last_regen = now
            pending_since = None
            continue

        # Heartbeat regen at least every MAX_INTERVAL.
        if (now - last_regen) >= MAX_INTERVAL:
            regen("heartbeat")
            last_regen = now


if __name__ == "__main__":
    sys.exit(main())
