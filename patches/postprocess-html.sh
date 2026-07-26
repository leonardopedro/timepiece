#!/usr/bin/env bash
# Post-process the generated single-page HTML to fix navigation UX:
# 1. Remove the HTTP-redirect script (breaks file:// protocol)
# 2. Make the TOC hidden by default on desktop (toggle via hamburger)
# 3. Auto-close the TOC when a TOC link is clicked
#
# Usage: ./patches/postprocess-html.sh [_out/html-single/index.html]

set -euo pipefail

HTML="${1:-_out/html-single/index.html}"

if [[ ! -f "$HTML" ]]; then
  echo "Error: $HTML not found" >&2
  exit 1
fi

python3 - "$HTML" <<'PYEOF'
import sys, re

path = sys.argv[1]
with open(path, "r", encoding="utf-8") as f:
    html = f.read()

# 1. Remove the redirect script (first <script> block with window.location.replace)
html = re.sub(
    r'<script>\s*\(function\(\)\{.*?\}\)\(\)</script>\s*',
    '',
    html,
    count=1,
    flags=re.DOTALL,
)

# 1b. Fix leftover empty hrefs (e.g. the book-title links): with <base href="./">
# an empty href navigates to the output directory (a file listing). Point them at
# the top of the current page instead.
html = html.replace('href=""', 'href="#"')

# 1c. Repoint the <base> tag at the document itself. Verso emits <base href="./">,
# which resolves to the output *directory*; a fragment link then navigates to
# `html-single/#frag` and the browser shows the directory listing (index.html is
# "missing" from the path). Pointing the base at index.html makes fragment links
# resolve to `html-single/index.html#frag`, so they scroll in place. Relative
# resource links (book.css, -verso-data/...) still resolve to the same directory.
html = html.replace('<base href="./">', '<base href="index.html">')

# 1d. Fix the heading permalink widgets (the 🔗 next to every section). Verso emits
# href="find/?domain=Verso.Genre.Manual.section&name=ID", a server/search route that
# does not exist over file://. The `name=` value is exactly the heading's id=, so
# rewrite each permalink to a plain #ID fragment anchor.
html = html.replace(
    'href="find/?domain=Verso.Genre.Manual.section&amp;name=',
    'href="#',
)

# 2. Make TOC hidden by default: remove checked="checked" from the bookRoot toggle
html = html.replace(
    'id="--verso-manual-toc-----bookRoot" checked="checked"',
    'id="--verso-manual-toc-----bookRoot"',
)

# 3. Add JS to close TOC when a link inside it is clicked, and to toggle via hamburger
inject = """
<!-- verso-postprocess-js -->
<script>
document.addEventListener('DOMContentLoaded', function() {
  var toc = document.getElementById('toc');
  if (!toc) return;
  toc.addEventListener('click', function(e) {
    var a = e.target.closest('a[href^="#"]');
    if (a) {
      var toggle = document.getElementById('toggle-toc');
      if (toggle) toggle.checked = false;
    }
  });
});
</script>
"""

# 4. Add CSS to hide TOC on desktop by default, show on toggle
css_inject = """
<!-- verso-postprocess-css -->
<style>
/* Hide TOC on desktop by default; show when hamburger is toggled */
@media screen and (min-width: 701px) {
  .with-toc > main { padding-left: 0; }
  #toc { display: none; }
  body:has(#toggle-toc:checked) #toc { display: flex; }
  body:has(#toggle-toc:checked) .with-toc > main { padding-left: var(--verso-toc-width); }
  body:has(#toggle-toc:checked) .toc-backdrop {
    display: block; position: fixed; inset: 0; background-color: #aaa8; z-index: 9;
  }
}
</style>
"""

# Inject CSS before </head> and JS before </body> (idempotent: skip if already present)
if "verso-postprocess-css" not in html:
    html = html.replace("</head>", css_inject + "</head>", 1)
if "verso-postprocess-js" not in html:
    html = html.replace("</body>", inject + "</body>", 1)

with open(path, "w", encoding="utf-8") as f:
    f.write(html)

print(f"Patched {path}: TOC hidden by default, auto-closes on link click, redirect removed.")
PYEOF
