#!/usr/bin/env bash
# Start (or restart) the status web server (port 8731) and the watcher as
# background processes that survive after the parent shell exits.
set -euo pipefail

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$TOOLS_DIR")"
PROGRESS="$ROOT/progress"
PORT=8731

mkdir -p "$PROGRESS"

# Stop any existing instances first for a clean (re)start.
"$TOOLS_DIR/stop.sh" || true

# --- server ---
nohup python3 "$TOOLS_DIR/serve.py" > "$PROGRESS/server.log" 2>&1 < /dev/null &
SERVER_PID=$!
disown "$SERVER_PID" 2>/dev/null || true
echo "$SERVER_PID" > "$PROGRESS/server.pid"
echo "[start] server pid=$SERVER_PID -> http://localhost:$PORT/"

# --- watcher ---
nohup python3 "$TOOLS_DIR/watch.py" > "$PROGRESS/watch.log" 2>&1 < /dev/null &
WATCH_PID=$!
disown "$WATCH_PID" 2>/dev/null || true
echo "$WATCH_PID" > "$PROGRESS/watch.pid"
echo "[start] watcher pid=$WATCH_PID"

echo "[start] done. Dashboard: http://localhost:$PORT/index.html"
