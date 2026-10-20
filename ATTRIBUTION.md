# Attribution

Borrowed patterns and components that concern *this* repo. The authoritative,
cross-repo table — including what was deliberately **not** adopted — is
the workspace ledger at `../ATTRIBUTION.md` (a path, not a link: the file
lives one level above this repo and is outside the build).

| source | licence | what was adapted | where it landed |
|---|---|---|---|
| mathlib (tag `v4.28.0`) | MIT | standard library, pinned by `lean-toolchain` | all four build targets |
| typos | Apache-2.0 | the index/graph discipline | `scripts/doc_index.py` + CI gate |
| ax | Apache-2.0 — verified from the clone at `../ax/` (`github.com/google/ax`, LICENSE read 2026-10-08; the `../test/AGENTS.md` record matches) | the `/healthz` endpoint pattern | `scripts/health.sh` |
| [prove2.me](https://prove2.me) | Apache-2.0 for public contributions — read from `https://prove2.me/terms` 2026-10-20 (public submissions, "including Lean code, theorem and definition statements, proofs", are licensed under Apache-2.0) | downloaded theorem/definition statements and their accepted community solution proofs, converted to Lean 4.28 / the pinned Mathlib; every converted file keeps a per-theorem provenance header (theorem id, statement author, solution author, submission id, platform Mathlib rev) and the Apache-2.0 notice, per `converted/README.md` | `converted/Prove2me/` (compiled conversions), `converted/blocked/` + `converted/Prove2me/AnalyticNt/` (the blocked SW-port chain; the original `Downloads/` tree was removed by the owner's 2026-10-20 Downloads → converted migration) |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (tag `v4.32.2`, commit `6a380f0c`) | Apache-2.0 — LICENSE read firsthand 2026-10-20 | verbatim port of the first-order Euler–Maclaurin section (split out of `Mertens.lean` upstream) and the Siegel–Walfisz SW-port definition bundles, with Mathlib API drift repaired and each local change listed in the file header | `converted/Definitions/Def_SWPort_000.lean`, `Def_SWPort_001.lean`, `converted/Prove2me/AnalyticNt/SWPort_Zeta0EqZeta.lean`, `converted/blocked/AnalyticNt/SWPort_Zeta0EqZeta.lean` (pre-migration originals under `Downloads/_deps/` + `Downloads/analytic-nt/`, removed 2026-10-20) |
| [openai/math](https://github.com/openai/math) (commit `1581d4c`) | Apache-2.0 — LICENSE read firsthand 2026-10-20 | definition bundles produced by skeleton subtraction from `lean/OAI/Analysis/…` (imports rewritten to platform modules); the generator's "adapted from an external source" boilerplate names no source, so the commit id in each file header plus this row carry the ledger | `converted/Definitions/Def_OAI_*.lean` (pre-migration originals under `Downloads/_deps/Definitions/`, removed 2026-10-20) |

## Notes

`book.tex` and `ODE.tex` here are the **source of record** for the shared
LaTeX corpus; `unfer/` carries a synced copy and `scripts/check-book-sync` fails
if they drift.

The Lean toolchain is pinned to **4.28.0 by githash** (`7e01a1bf`), which no
nixpkgs pin reproduces exactly — provision it with elan, not from a package
manager.
