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

# 1c. Remove the <base> tag entirely. Verso emits <base href="./"> (a previous
# version of this script repointed it at index.html). With ANY <base> present, the
# browser resolves a fragment link #frag against the document's absolute file://
# location, so when the page is printed to PDF the bookmarks/links embed this
# machine's filesystem path (file:///media/...) and fail on every other machine.
# With no <base>, a fragment link stays a same-document anchor: the PDF gets an
# internal "go to position" link that is fully portable, and in-page scrolling still
# works whether the file is opened as index.html or via its directory. The relative
# resource links (book.css, -verso-data/...) resolve against the document's own
# directory either way, so they are unaffected. The regex removes whichever form is
# present, which also makes the step idempotent.
html = re.sub(r'<base[^>]*>', '', html, count=1)

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
  /* Full-page-wide content: remove the 47rem content cap. The single custom
     property --verso-content-max-width constrains .content-wrapper,
     main section, .header-title and .prev-next-buttons; setting it to `none`
     makes the whole page span the viewport width. */
  :root { --verso-content-max-width: none; }
  /* Printing: the fixed ToC would otherwise render as a left column on every
     printed page, main keeps a padding-left that reserves its width, and the
     fixed header would repeat the running "Timepiece" title on every page.
     Hide all three and zero the reserved padding. */
  @media print {
    #toc, .toc-backdrop, #toggle-toc-click, .header-logo-wrapper,
    header {
      display: none !important;
    }
    .with-toc > main { padding-left: 0 !important; }
    .with-toc { margin-top: 0 !important; }
    body { margin-top: 0 !important; }
  }
  /* Highlight the Mehler dictionary section (the structural backbone of the book):
     a soft callout box around the section that states the uniform-sphere-to-Fock
     dictionary in the first part. */
 section:has(h3[id$="Only-the-Mehler-Measure-on-the-Infinite-Part"]) {
   background: #f6f3ff;
   border: 1px solid #d9d2f0;
   border-radius: 8px;
   padding: 0 1.2em 0.8em 1.2em;
   margin: 1.2em 0;
 }
 section:has(h3[id$="Only-the-Mehler-Measure-on-the-Infinite-Part"]) h3 {
   color: #4b3a8f;
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
