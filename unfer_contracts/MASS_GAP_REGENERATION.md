# Self-contained mass-gap regeneration bundle

This directory is the complete non-Lean input bundle for the mass-gap
formalization. It was copied from the current numerical implementation so the
Lean4 specialist can work from `timepiece` alone.

## Object of record

The physical object is the 3D gauge-fixed QYM one-particle Hamiltonian `h`,
including its inner pair terms. If positivity requires a shift, apply only the
allowed scalar shift. The final nested-Fock Hamiltonian is

```text
H = Σᵢⱼ hᵢⱼ C†(eᵢ) A(eⱼ).
```

The outer annihilation operator kills the outer vacuum, so the full theory has
the exact outer-vacuum ground. Squeezed inner states are one-particle
spectral diagnostics, not full-theory ground states.

Numerical approximations use the SIRK–Hashimoto algorithm. Lattice code and
occupation-parity certificates are not inputs to this formalization.

## Included inputs

- `MASS_GAP_SPEC.md`: proof-facing contract and code-to-mathematics map.
- `fock_sirk/src/`: current certificate, SIRK seam, and pure specification
  sources (reference text — the specialist never compiles Rust).
- `fock_sirk/tests/`: current QYM and certificate regression tests
  (reference text — run by the planner in `../unfer`, never by the
  specialist).
- `sirk_core_model/`: Aeneas-supported pure SIRK core, regeneration script,
  and committed generated artifacts.  The vendored `aeneas_sirk.sh` is a
  working standalone copy (regenerates end-to-end, exit 0) for the planner;
  the specialist consumes only the generated `aeneas/SirkCoreModel.lean`.
- `docs/*.cdb`: the Cadabra2 derivation notebooks (`yang_mills_hamiltonian`,
  `qg_starobinsky_hamiltonian`, `qg_starobinsky_vielbein_hamiltonian`).
  **Reference text only — never run.**  The specialist has no Cadabra2; the
  operative algebra is stated inline in `MASS_GAP_SPEC.md`.
- `prob_kernel/tests/fixtures/gap_certificate.ndjson`: the `lean4export`
  fixture, **nanoda-verified by the planner** (2026-08-29: all 12 `verify::`
  tests green).  Retained as input data until regenerated after source
  changes.

## Division of labour (who does what)

**The Lean4 specialist needs no Rust compiler and never reads `../unfer`.**
Every executable step that involves Rust — running the numerical suites,
emitting fresh NDJSON, running nanoda, regenerating the Aeneas model — is the
**planner's job**, done in `../unfer` and re-vendored here. The specialist's
surface is exactly: this bundle (spec + fixtures + generated Lean model) plus
the Lean proof modules, verified by `lake env lean` on the touched module
and `#print axioms`.

## Regeneration gate (planner — after any Rust change)

After a Rust Hamiltonian, outer-enclosure, solver, or certificate change in
`../unfer`, the planner must:

1. Run the corrected QYM/QED/QG/NS numerical suites in `../unfer` and emit
   fresh NDJSON.
2. Record source revision, Hamiltonian constructor, coupling, truncation,
   Krylov order, shifts, and a cryptographic hash of the emitted data.
3. Re-run `../unfer/sirk_core_model/scripts/aeneas_sirk.sh` (the vendored
   `sirk_core_model/aeneas_sirk.sh` is a working standalone copy of the same
   script) and inspect that the generated Lean model is complete rather than
   partial.
4. Re-export the Lean theorem instantiation using the generated certificate
   data.
5. Run nanoda through `prob_kernel::verify::verify_export` (the
   `gap_certificate_proof_verifies_in_nanoda` test) on the emitted export.
6. Replace the vendored fixture and generated artifacts, and update
   `STATUS.md`, only after both Aeneas and nanoda succeed.

The old fixture is not evidence for a corrected implementation. A successful
finite certificate still does not prove the continuum mass gap; the
one-particle positivity/edge theorem and its outer `dΓ` lift remain separate
formal obligations.

**Status 2026-08-29:** gate steps 3 and 5 are green on the current bundle —
`cargo test -p prob_kernel --lib verify::` passes all 12 tests including
`gap_certificate_proof_verifies_in_nanoda`, and the vendored
`sirk_core_model/aeneas_sirk.sh` runs end-to-end (exit 0, 7 expected f64
errors, `SirkCoreModel.lean` byte-identical to committed).

## Regeneration log

### 2026-08-29 — Aeneas model re-run (source rev `1767a52` in `../unfer`)

- Ran `sirk_core_model/aeneas_sirk.sh` against the live `../unfer` core
  (`unfer/sirk_core_model/scripts/aeneas_sirk.sh`). Charon extracted the
  pure core to `.llbc`; Aeneas emitted the partial Lean model (7 expected
  f64-arithmetic errors, `sorry` bodies — the documented honesty boundary).
- **Script bug fixed in both copies** (`aeneas_sirk.sh`): Aeneas exits
  non-zero on the expected errors, which under `set -e` aborted the script
  *before* the rename steps — the `aeneas/` outputs were never refreshed.
  The fix captures the exit status and only treats a run that produces no
  `Lib.lean` at all as fatal.
- Result: `aeneas/SirkCoreModel.lean` and `aeneas/sirk_core_model.llbc`
  regenerated; byte-identical to the vendored copies (the vendored bundle
  was already current — the *live* repo's committed artifacts were stale,
  carrying line numbers from an older `src/lib.rs`).
- **Charon `.llbc` output is byte-nondeterministic between runs**: two runs
  from the same `src/lib.rs` produce the same declaration sets (25 funs, 7
  types, 5 traits, 6 impls, 3 globals, 46 item names) but a different
  serialized `ordered_decls` key ordering, so the `.llbc` bytes differ run
  to run. This is expected; the generated `SirkCoreModel.lean` (the artifact
  the Lean specialist consumes) is byte-identical across runs. Do not treat
  a differing `.llbc` byte layout as a source change.
- Cleanup: the stale crate-root `Lib.lean`/`lib.llbc` duplicates (tracked
  since `e0dfb3d`, superseded by the `aeneas/` normalization) were removed
  by the script's own `mv`; README documents only the `aeneas/` outputs.
