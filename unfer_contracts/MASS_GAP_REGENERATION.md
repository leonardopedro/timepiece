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
  sources.
- `fock_sirk/tests/`: current QYM and certificate regression tests.
- `sirk_core_model/`: Aeneas-supported pure SIRK core, regeneration script,
  and committed generated artifacts.
- `prob_kernel/tests/fixtures/gap_certificate.ndjson`: prior certificate
  fixture, retained as input data only until regenerated after source changes.

## Required regeneration gate

After any Rust Hamiltonian, outer-enclosure, solver, or certificate change:

1. Run the current QYM certificate tests and emit fresh NDJSON.
2. Record source revision, Hamiltonian constructor, coupling, truncation,
   Krylov order, shifts, and a cryptographic hash of the emitted data.
3. Run `sirk_core_model/aeneas_sirk.sh` from this bundle and inspect that the
   generated Lean model is complete rather than partial.
4. Export the Lean theorem instantiation using the generated certificate data.
5. Run nanoda through the local `prob_kernel::verify::verify_export` workflow.
6. Replace the fixture and update `STATUS.md` only after both Aeneas and
   nanoda succeed.

The old fixture is not evidence for a corrected implementation. A successful
finite certificate still does not prove the continuum mass gap; the
one-particle positivity/edge theorem and its outer `dΓ` lift remain separate
formal obligations.
