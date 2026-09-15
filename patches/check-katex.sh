#!/usr/bin/env bash
# Verify that every piece of math in the rendered book actually compiles with the
# KaTeX build that the book ships.
#
# The book renders math client-side: `-verso-data/katex/math.js` calls
# `katex.render(..., { throwOnError: false })` on every `.math.inline` /
# `.math.display` element, so a construct KaTeX does not support is silently
# shown in red rather than failing the build.  This script extracts all those
# snippets from `_out/html-single/index.html` and re-renders them with
# `throwOnError: true` under node, reporting every failure.
#
# Usage:  ./patches/check-katex.sh        (run after ./patches/build-book.sh)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

HTML="$ROOT/_out/html-single/index.html"
KATEX="$ROOT/_out/html-single/-verso-data/katex/katex.js"
[[ -f "$HTML" ]]  || { echo "missing $HTML — run ./patches/build-book.sh first"; exit 1; }
[[ -f "$KATEX" ]] || { echo "missing $KATEX — run ./patches/build-book.sh first"; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

python3 - "$HTML" "$TMP/math.json" <<'PYEOF'
import sys, re, html, json
src = open(sys.argv[1], encoding="utf-8").read()
items = [[m.group(1), html.unescape(m.group(2))]
         for m in re.finditer(r'<code class="math (inline|display)">(.*?)</code>', src, re.S)]
json.dump(items, open(sys.argv[2], "w"))
print(f"extracted {len(items)} math snippets")
PYEOF

node - "$KATEX" "$TMP/math.json" <<'JSEOF'
const fs = require('fs');
const src = fs.readFileSync(process.argv[2], 'utf8');
const mod = { exports: {} };
const load = new Function('module', 'exports', 'window', 'document',
  src + '\nreturn module.exports;');
const katex = load(mod, mod.exports, undefined, undefined);
const items = JSON.parse(fs.readFileSync(process.argv[3], 'utf8'));
let errors = 0;
const seen = new Set();
for (const [mode, tex] of items) {
  try {
    katex.renderToString(tex, { displayMode: mode === 'display', throwOnError: true });
  } catch (e) {
    errors++;
    const key = e.message.slice(0, 120);
    if (!seen.has(key)) {
      seen.add(key);
      console.log('FAIL:', key, '||', tex.slice(0, 80).replace(/\n/g, ' '));
    }
  }
}
console.log(`checked ${items.length} snippets, ${errors} KaTeX failures`);
if (errors > 0) process.exit(1);
JSEOF

echo "OK: all math in the rendered book compiles under KaTeX."
