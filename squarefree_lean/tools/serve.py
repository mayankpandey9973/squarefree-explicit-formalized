#!/usr/bin/env python3
"""Serve the progress/ directory over HTTP on FIXED port 8731.

Stdlib only. Mirrors `python3 -m http.server 8731` semantics but pins the
document root to <root>/progress/ and disables caching so the dashboard always
fetches fresh status.json.
"""

import os
import sys
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

PORT = 8731
TOOLS_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(TOOLS_DIR)
PROGRESS = os.path.join(ROOT, "progress")


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=PROGRESS, **kwargs)

    def end_headers(self):
        # No-cache so polling always sees the latest status.json.
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        super().end_headers()

    def log_message(self, fmt, *args):
        # Quiet by default; uncomment to debug.
        pass


def main():
    os.chdir(PROGRESS)
    httpd = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    print("[serve] http://localhost:%d/  (root=%s)" % (PORT, PROGRESS))
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()


if __name__ == "__main__":
    sys.exit(main())
