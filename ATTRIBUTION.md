# Attribution

Borrowed patterns and components that concern *this* repo. The authoritative,
cross-repo table — including what was deliberately **not** adopted — is
[`../ATTRIBUTION.md`](../ATTRIBUTION.md).

| source | licence | what was adapted | where it landed |
|---|---|---|---|
| mathlib (tag `v4.28.0`) | MIT | standard library, pinned by `lean-toolchain` | all four build targets |
| typos | Apache-2.0 | the index/graph discipline | `scripts/doc_index.py` + CI gate |

## Notes

`book.tex` and `ODE.tex` here are the **source of record** for the shared
LaTeX corpus; `unfer/` carries a synced copy and `scripts/check-book-sync` fails
if they drift.

The Lean toolchain is pinned to **4.28.0 by githash** (`7e01a1bf`), which no
nixpkgs pin reproduces exactly — provision it with elan, not from a package
manager.
