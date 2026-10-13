# TODO ledger — reviewed code markers

Policy (PLAN_CROSS_PROJECT_REVIEW_2026-10-12 §B1): code files (`*.rs`,
`*.sh`, `*.py`, `*.toml`) carry **no** `TODO`/`FIXME`/`HACK`/`XXX`
marker unless the file is listed below with the reviewed reason.
Markdown (including the Book and its status tables) is out of scan
scope by policy — historical/proof-in-progress prose is the Lean
specialist's domain, not a gate's.
`scripts/check-todo-ledger` enforces this.

The ledger starts empty because the initial full-tree scan found every
"TODO" in this repo to be markdown prose, not code debt.

| file | why markers are allowed |
|---|---|
