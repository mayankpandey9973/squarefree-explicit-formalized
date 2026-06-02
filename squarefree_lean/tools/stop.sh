#!/usr/bin/env bash
# Stop the status web server and the watcher (if running).
set -uo pipefail

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$TOOLS_DIR")"
PROGRESS="$ROOT/progress"

kill_pidfile() {
  local name="$1" pidfile="$2"
  if [[ -f "$pidfile" ]]; then
    local pid
    pid="$(cat "$pidfile" 2>/dev/null || true)"
    if [[ -n "${pid:-}" ]] && kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
      sleep 0.3
      kill -9 "$pid" 2>/dev/null || true
      echo "[stop] $name (pid=$pid) stopped"
    else
      echo "[stop] $name not running (stale pidfile)"
    fi
    rm -f "$pidfile"
  else
    echo "[stop] $name: no pidfile"
  fi
}

kill_pidfile "server" "$PROGRESS/server.pid"
kill_pidfile "watcher" "$PROGRESS/watch.pid"

# Best-effort: kill any stray serve.py/watch.py from this project.
pkill -f "$TOOLS_DIR/serve.py" 2>/dev/null || true
pkill -f "$TOOLS_DIR/watch.py" 2>/dev/null || true

exit 0
