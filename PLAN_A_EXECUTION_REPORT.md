# Plan A Book Formalization — execution report

## Implemented

### A1 — Solovay/Kopperman finite-head tensor core

`BookProof/ChapterSolovay.lean` now contains:

- `headSumEquiv`, the explicit equivalence
  `InnerHead (N₁ + N₂) ≃ InnerHead N₁ × InnerHead N₂`;
- `tensorHeadObservable` and
  `tensorHeadObservable_dependsOnlyOnHead`;
- `stateMeasure_isProbability` and `stateMeasure_finite_marginal`, valid for an
  arbitrary probability law on the finite head;
- the readable finite-integral headline `tensor_language_decidable`;
- atomlessness of the selected tail prior (`tailMeasure_singleton`);
- an explicit measure-preserving tail symmetry interface,
  `mehler_invariant_under_finite_orthogonal`;
- `TailPriorAdmissible`, `only_mehler_on_tail`, and
  `head_vs_tail_admissibility`.

The current repository models `InnerTail` as the abstract substrate
`L²([0,1])` with a chosen atomless probability measure. It does not provide a
coordinate-level Gaussian realization of that measure or Mathlib infrastructure
for the requested Hilbert tensor identification
`L²(X) ⊗ L²(Y) ≅ L²(X × Y)`. Consequently, this execution does **not** claim a
unit-square/unit-interval measure isomorphism, Mehler coordinate splitting,
finite-rank orthogonal characterization, or cross-dimensional padding theorem.
The invariance theorem is deliberately stated at the honest
measure-preserving-symmetry interface. Likewise, `only_mehler_on_tail` packages
the three requested properties and does not assert an unsupported uniqueness
claim.

`BookProof/ChapterJointUnitary.lean` adds
`finite_purification_linearization`, the finite-dimensional unitary realization
supported by the repository's existing Gram–Schmidt theorem. It does not claim
a dilation theorem for every bounded nonlinear map, which would be false without
additional hypotheses and a precise dilation construction.

### A2 — Further claims

New modules:

- `BookProof/ChapterProbabilityInterface.lean`: transport of probability laws
  and events through measurable equivalences, including inverse transport and
  preservation of probability;
- `BookProof/ChapterCountableDefinability.lean`: countability of values denoted
  by a countable syntax, existence of a real outside that range, and the
  non-uniqueness of nondegenerate interval constraints;
- `BookProof/ChapterKopperman.lean`: readable all-model separability and
  standard `Π⁰₂` truth-invariance headlines; full infinitary
  completeness/compactness remains explicitly outside the represented syntax;
- `BookProof/ChapterFiniteArithmeticPrior.lean`: exact bounded arithmetic plus
  a normalized finite Bayesian prior on hypotheses beyond the table.

Extended modules:

- `BookProof/ChapterBornPhaseFiber.lean`: square-root normalization, finite
  `L²` average versus maximal-error control, and commutativity of multiplication
  operators;
- `BookProof/ChapterJointUnitary.lean`: finite purification/linearization.

The requested density decomposition was already fully present in
`BookProof/ChapterDensitySpectral.lean` as
`density_iff_exists_unitary_diagonal`; it was reused rather than duplicated.

### A3 — readable headline types

Short, readable headline declarations were introduced in the modules above,
notably `tensor_language_decidable`, `finite_purification_linearization`,
`all_formalism_models_separable`, and `standard_pi02_truth_invariant`. Existing
free-field audit-only `#check` files were not duplicated or rewritten.

### A4 — read-only Singularity cross-check

No `Singularity/*.lean` file was modified.

The checked files `Singularity/Hamiltonian.lean`, `Singularity/Esa.lean`, and
`Singularity/Singularity.lean` contain no `sorry` or `admit`. Their current
statements support the repository's finite certificate/interface model.

A prose discrepancy remains in `Book/OdeSingularity.lean`: it says
`nelson_essential_self_adjoint` and `weyl_symmetrization_self_adjoint` are
placeholders. The current Lean sources instead contain proved finite-model
statements. Under Plan A's hard constraint, `Book/*.lean` was left untouched;
the prose should be updated by the prose-maintenance track. The analytic Stone,
Nelson, unbounded-operator, and spectral-measure claims remain outside those
finite statements, as documented in the source files.
