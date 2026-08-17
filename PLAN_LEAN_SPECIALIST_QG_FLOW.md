# PLAN_LEAN_SPECIALIST_QG_FLOW.md — Quantum Gravity: the densitized route

This is the plan item requested by `CONSOLIDATED_PLAN.md` §10.3 ("Suggested next
step"), written in the style of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`: Part A the
change of variables, Part B the flat principal part, Part C the finite (mode)
realization with its analytic conclusions, Part D the continuum theorem as a
**named hypothesis, never an axiom**.

**Status (2026-08-17): executed.**  Every headline below is proved,
`sorry`-free and `axiom`-free, in `BookProof/ChapterQuantumGravityDensitized.lean`;
the module is registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` (`#print axioms`, only `propext`,
`Classical.choice`, `Quot.sound`) and cited from `Book/DiffeomorphismsGravity.lean`.

## The setting

The manuscript's final, 3D gauge-fixed gravity Hamiltonian
(`book.tex` §"Classical Hamiltonian" / §"Quantum Hamiltonian", ~8138–8310) has the
singular kinetic terms

```
H = (1/16e) S^{ab} S_ab − (1/24e) P² + …,      e = det e_i^a,
```

which are not defined as operators on a fixed domain where the tetrad degenerates.
The route is the canonical change of variables to densitized tetrads
`y = √e`, `ẽ_i^a = √e · e_i^a`.

## Part A — the change of variables

| Item | Lean name | Status |
| :-- | :-- | :--: |
| A.1 the new coordinate `y = √e`, `y² = e` | `densY`, `densY_sq` | PROVED |
| A.2 its derivative `∂y/∂e = 1/(2√e)` | `hasDerivAt_densY`, `deriv_densY` | PROVED |
| A.3 the absorption identity `1/e = 4(∂y/∂e)²` | `inv_eq_four_mul_deriv_densY_sq` | PROVED |
| A.4 the two singular terms in densitized form | `kinetic_absorption`, `conformal_absorption` | PROVED |
| A.5 the densitized tetrad `ẽ = √e·e`, its determinant, the inverse map | `densTetrad`, `densTetrad_det`, `densTetrad_recover` | PROVED |
| A.6 the singularity is real (`1/e → ∞`) and the new coordinate is regular (`y → 0`) | `tendsto_inv_det_atTop`, `tendsto_densY_zero` | PROVED |

**Correction to the plan prose.**  `CONSOLIDATED_PLAN.md` §10.1 writes the
absorption identity as `1/e = (∂y/∂e)²`.  The honest identity carries a factor
`4`: `∂√e/∂e = 1/(2√e)`, so `(∂y/∂e)² = 1/(4e)`.  A.3 states the corrected form.

## Part B — the flat principal part

| Item | Lean name | Status |
| :-- | :-- | :--: |
| B.1 the principal symbol `(1/16)Σξ_a² − (1/24)ξ_y²` | `qgSymbol`, `qgSymbol_homogeneous` | PROVED |
| B.2 the constant field-space metric and its non-degeneracy | `qgMetric`, `qgMetric_det_ne_zero` | PROVED |
| B.3 the symbol is the form of that metric | `qgSymbol_eq_metric_form` | PROVED |
| B.4 hyperbolic, not elliptic: the symbol is indefinite | `qgSymbol_pos`, `qgSymbol_neg`, `qgSymbol_indefinite` | PROVED |
| B.5 flatness: a constant metric has vanishing Christoffel symbols, so the point transformation adds no "quantum potential" | `christoffel`, `christoffel_eq_zero_of_const`, `qgMetric_christoffel_zero` | PROVED |
| B.6 the 2nd + 1st + 0th operator-order decomposition, as the scaling law of the full symbol | `qgFullSymbol`, `qgFullSymbol_scaling` | PROVED |

## Part C — the mode (Hermite-basis) realization

In the oscillator basis the fiber operator is multiplication by the mode symbol
`λ_k = (1/16)a_k² − (1/24)b_k² + V_k` on its maximal domain in `ℓ²(ℕ)`.

| Item | Lean name | Status |
| :-- | :-- | :--: |
| C.1 the mode symbol and the fiber operator | `qgModeSymbol`, `qgModeHamiltonian` | PROVED |
| C.2 essential self-adjointness on the maximal domain (via the *proved* Faris–Lavine criterion) | `qgModeHamiltonian_essentiallySelfAdjoint` | PROVED |
| C.3 trivial deficiency at **every** non-real `z` — the conclusion Strichartz supplies in the continuum | `mulHamiltonian_deficiencyTrivialAt`, `qgModeHamiltonian_deficiencyTrivialAt` | PROVED |
| C.4 the realization is genuinely unbounded | `qgModeHamiltonian_not_bounded` | PROVED |

## Part D — Strichartz as a named hypothesis

| Item | Lean name | Status |
| :-- | :-- | :--: |
| D.1 the deduction step: finite-speed / unique continuation ⟹ ESA | `strichartz_esa_of_finiteSpeed` | PROVED (hypothesis named) |
| D.2 the hypothesis is satisfiable (Part C satisfies it) | `strichartz_finiteSpeed_satisfiable` | PROVED |
| D.3 the alternative route through the proved Faris–Lavine criterion | `qg_esa_of_farisLavine` | PROVED (hypotheses named) |
| D.4 transfer along the half-density unitary: ESA of the flat operator ⟹ ESA of the physical one | `densitized_hasZeroDeficiencyOn_transfer` | PROVED |
| D.5 the half-density unitary itself, **constructed** rather than assumed | `measurePreserving_qgSquare`, `measurePreserving_qgSqrt`, `halfDensityUnitary`, `qg_halfDensity_transfer` | PROVED |

**D.5 (added 2026-08-17).**  The conformal part of the change of variables,
`e = y²`, is measure preserving from the Jacobian-weighted measure `2y dy` on
`(0,∞)` to Lebesgue measure `de`, the weight `2y` being the square of the
half-density factor `√(2y)`.  Composition with `y ↦ y²` is therefore a genuine
unitary `L²((0,∞), de) ≃ L²((0,∞), 2y dy)`, and D.4 is instantiated at it
(`qg_halfDensity_transfer`).  This is in
`BookProof/ChapterQuantumGravityHalfDensity.lean`, `sorry`-free and
`axiom`-free.  It removes the last bullet of the honest boundary below ("the
transfer theorem takes that unitary as data") for the conformal factor.

Reference for D.1: R. S. Strichartz, *Essential self-adjointness of powers of
generators of hyperbolic equations*, J. Funct. Anal. **13** (1973) 82–93.  It is a
hypothesis of the theorem, not an `axiom`, exactly as `ns_esa_of_farisLavine` is
in the Navier–Stokes plan.

## Honest boundary (unchanged from `CONSOLIDATED_PLAN.md` §10.3)

* **Not claimed:** essential self-adjointness of the continuum gravity operator on
  `L²(ℝ⁸⁴ × ℤ₂¹⁹)`, global existence, or any unitary-evolution result for it.
* The continuum conclusion needs the finite-speed propagation statement for the
  flat d'Alembertian with a polynomial potential; that is the analytic core, and
  it enters only as the explicit hypothesis of D.1.
* The **gauge/BRST sector** is not covered by the transfer argument alone: a full
  BRST-reduced transfer needs the unitary to preserve the physical subspace, which
  the `1/e`-absorption gives for the kinetic/conformal part but which must be
  checked for `H₁ − Ṽ` under the full constraint structure.
* The raw point map `e ↦ (y, ẽ)` is not by itself a Hilbert-space unitary; the
  Jacobian half-density factor `|J|^{−1/2}` is what makes D.4 applicable.  The
  transfer theorem takes that unitary as data.
