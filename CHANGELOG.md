# Changelog

All notable changes to the timepiece formalization repo.
Changelog discipline adapted from `../typos` / `../velysterm` (Apache-2.0):
keep an `Unreleased` section at the top, append dated entries; history seeded
from `git log --date=short`. **No Lean code was written for this entry —
proof work stays with the LLM-Lean4-specialist per CONSOLIDATED_PLAN.md.**

## [Unreleased]

- Cross-project review improvements: `scripts/doc_index.py` (doc index +
  backlinks, `DOC_INDEX.md`, freshness gate `--check`, `--backlinks`/`--search`
  queries), `scripts/health.sh` (one-command health over the existing gates),
  `CHANGELOG.md` (this file); versioned `state/doc_index.json` committed so
  `--check` works on a fresh clone; Python bytecode git-ignored.

## History (newest first, seeded from `git log`)

- 2026-09-24 `8901a58` Land the SM closure wave: unconditional sm_h_esa, its Kato/Hermite instrument, and the doctrine read-through
- 2026-09-23 `ad27fc9` Land the BRST book charge, the SM chapter stack, and the sector-ESA wave
- 2026-09-23 `9df9db3` Hand the bosonic Faris–Lavine proof to the Lean4 specialist (§2026-09-23e)
- 2026-09-21 `501168c` Ground the QG and QYM final-Hamiltonian chapters in the manuscript's recursion
- 2026-09-21 `5e83b2a` Ground the dGamma-ESA chapter in the manuscript's recursive Fock-space and convolution
- 2026-09-21 `8e0bce3` Merge the core-transfer / dGamma-ESA and gauge waves; register the reuse re-run
- 2026-09-18 `8a509e4` Register the reuse re-run for the offline specialist, with the matcher's blind spot
- 2026-09-18 `0dd06e4` Say what each Faris-Lavine proof actually compares, and give N verbatim
- 2026-09-18 `59c00df` Merge the Navier-Stokes operator wave and state the final-Hamiltonian convention once
- 2026-09-17 `4b27c40` Give the specialist a build gate that never runs a full lake build
- 2026-09-17 `0e45eb0` Record that the Faris-Lavine criterion lifts together with its comparison operator
- 2026-09-17 `f4daeee` Record the nested Fock space and its Hamiltonian as definitions of record for NS and QG
- 2026-09-17 `d19235d` Distinguish the one-particle Hamiltonian from its number-conserving Fock lift
- 2026-09-17 `255df9a` Say what the reduced squares actually are, in the operator language
- 2026-09-17 `fda50e0` Correct the reduced Hamiltonian: the square of a form is its modulus square
- 2026-09-17 `4c5c502` Record the Fourier-elimination wave and stop the Lagrangian half from being read as done
- 2026-09-15 `3eb5559` Give the derivative-gauge chapters a Lake target of their own, as a view of the part that contains them
- 2026-09-15 `0116fb6` Explain the derivative-variable gauge fixing for Navier-Stokes and gravity in the book
- 2026-09-15 `17d43e6` Give every BookProof part a Lake target, including the Pauli-Grover chapter
- 2026-09-15 `3bff2d6` Keep the Aristotle round's file-copy note as bkPrompts.md
- 2026-09-15 `a5fcf4a` Merge the Aristotle snapshot: split chapters into component parts
- 2026-09-15 `21737fd` Index the Pauli-Grover chapter in the declaration graph
- 2026-09-15 `1cd6496` Reintegrate the Pauli-Grover chapter with its source and book chapter
- 2026-09-15 `ad8a977` Sync timepiece with origin/main (112 commits)
- 2026-09-15 `fa8429b` Checkpoint local Aristotle merge before syncing with origin/main
- 2026-09-09 `da60037` Sync: audit consolidation, new BookProof chapters, v4.33 refinements
- 2026-09-06 `61595bc` Merge Aristotle 2026-09-06 wave: band calculus to arbitrary order, YM band bounds, ghost sector, QED index, resolvent min-max ladder
- 2026-08-31 `9047440` BookProof: merge QG QG-2/QG-3.2 and QYM-1 proof wave; wire two missing modules; refresh book and plan
- 2026-08-29 `6d32809` Plan 29f v2: correct ESA status — 1D lemma and localization already proved; conformal-factor sign analysis decides the open deficiency input
- 2026-08-29 `b200b4a` Plan 29f: ESA of the full QG one-particle operator via separable specialization
- 2026-08-29 `36bed62` Plan + QG module: correct the finite-speed ESA citation (Chernoff, not Strichartz)
- 2026-08-29 `6daf882` Plan: work order for the LLM-Lean4-specialist — complete QG and the QYM mass gap
- 2026-08-29 `c005c32` Book: pedagogically reference the new QED, NS-fibre-gap, and vielbein proofs
- 2026-08-29 `0d9f811` Copy Aristotle 2026-08-29 proof wave into BookProof and merge plan
- 2026-08-29 `c35121f` Make unfer_contracts fully self-contained: vendor .cdb derivations, verify nanoda
- 2026-08-29 `d10dc1a` unfer_contracts: final llbc sync + document charon byte-nondeterminism
- 2026-08-29 `7461d89` unfer_contracts: sync regenerated Aeneas llbc; fix vendored regen script
- 2026-08-29 `f634861` F7: GitBook drift check (scripts/check-gitbook-drift) + AGENTS.md layout fix
- 2026-08-29 `8f43e12` FEDERATION_DEEP_REVIEW: record F6 toolchain pin (rust-toolchain.toml, 1.97.1)
- 2026-08-29 `221478a` FEDERATION_DEEP_REVIEW: reframe F2 in release terms; record CI release-mode change
- 2026-08-29 `33f9d11` FEDERATION_DEEP_REVIEW: record the F2 heavy-tests release-mode fix
- 2026-08-29 `19e1688` Federation review, timepiece CI + verify gate, and two numerics book pages
- 2026-08-28 `e792f49` Merge Fock gap-chain proof wave and pin the full-exponential QG enclosure doctrine
- 2026-08-28 `352abe4` AGENTS.md: add mass-gap formalization section with vendored bundle docs
- 2026-08-28 `d511d5a` Mass-gap formalization: outer-enclosure doctrine, self-contained bundle, Aeneas refresh
