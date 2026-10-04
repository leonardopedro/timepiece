<!-- status: unverified | tests: not run | last_verified: 2026-10-04 -->

## Status

**Not verified in the 2026-10-04 review pass.** This repository has no `.lake`
directory in the reviewed environment, so nothing here was compiled: 1202 `.lean`
files across four default build targets (`BookProof`, `Book`, `Singularity`,
`Layout`) plus a full mathlib build is a multi-hour job, and reporting a number
without running it is exactly the failure this block exists to prevent.

The block is present with an honest `unverified` status rather than absent, so the
gate can tell "not checked" from "checked and fine".

To verify:

```sh
elan toolchain install leanprover/lean4:v4.28.0 && elan default leanprover/lean4:v4.28.0
lake exe cache get
lake build                  # BookProof, Book, Singularity, Layout
```

`book.tex` and `ODE.tex` here are the **source of record**; `unfer/` carries a
synced copy and `scripts/check-book-sync` (at the workspace root, mirrored into
`unfer/scripts/`) fails if the two drift.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```