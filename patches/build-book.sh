#!/usr/bin/env bash
# Build the single-page Verso book and ALWAYS post-process the HTML.
#
# The postprocess step is mandatory: it removes the <base href="./"> tag that
# Verso emits (and the search/redirect boilerplate). With a <base> present the
# browser resolves every #fragment ToC link against an absolute file:// location,
# so a printed PDF embeds non-portable bookmarks that open a webbrowser on each
# machine. Running postprocess after every render keeps the bookmarks internal
# and portable.
#
# Usage:  ./patches/build-book.sh
# Idempotent; safe to run multiple times.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -x "$HOME/.elan/bin/lake" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi

./patches/apply-verso-patches.sh
lake build book
lake exe book
./patches/postprocess-html.sh

python3 - "$ROOT/_out/html-single/index.html" <<'PYEOF'
import sys
html = open(sys.argv[1], encoding="utf-8").read()
assert "<base" not in html, "postprocess failed to remove <base> tag"
assert html.count('href="#') > 0, "no fragment ToC links present"
print("OK: no <base>; fragment links present.")
PYEOF
echo "Book built: $ROOT/_out/html-single/index.html"