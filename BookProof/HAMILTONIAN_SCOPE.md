# Reading the Hamiltonian proofs — scope at 2026-11-15

This is a source-reading guide. No Lean build, axiom audit or numerical run was
performed for this documentation wave. The work order is
[the 2026-11-15 entry in the consolidated plan](../CONSOLIDATED_PLAN.md).
The theorem statements, including their hypotheses, remain the proof contracts.

## The object to identify before using a theorem

For QYM, QED, QG and NS the final Hamiltonian has the same outer shape:

$$H=d\Gamma(h)=\sum_{ij}\langle e_i,h e_j\rangle C^\dagger(e_i)A(e_j).$$

Creation acts on the left, annihilation on the right. The inner space can itself
be a field Fock space. Every kinetic, interaction, ordering and scalar term of
its specified operator belongs to **inner** `h` before enclosure. The displayed
matrix sum is shorthand on a justified core; an infinite sum is not a domain
construction. On outer particle number `n`, the realization is the sum of `h`
acting on each tensor factor, restricted to the intended statistics.

- QYM. Inner operator and reusable proof: Complete gauge-fixed kinetic plus magnetic square,
  including cubic cross and quartic terms; [nonabelian ESA](Qym/ChapterYangMillsNonAbelianEsa.lean),
  [gap lift](Qym/ChapterYangMillsFockGapChain.lean). Boundary: ESA of the defined operator is
  separate from physical representation identification and absolute coercivity.

- QED. Inner operator and reusable proof: [Abelian
  consolidation](Qed/ChapterQedAbelianConsolidation.lean) and [photon
  dispersion](Qed/ChapterQedFockGapChain.lean). Boundary: Photon/abelian theorems do not construct
  all charged-matter interactions; infrared accumulation obstructs a strict photon gap.

- QG. Inner operator and reusable proof: R² vielbein realization with
  `V(φ)=M⁴/(16α)(1-exp(-sqrt(2/3)φ/M))²`, no Taylor expansion, and every interaction; [eliminated
  model](Qg/ChapterQgFullEliminated.lean), [sector enclosure](Qg/ChapterQgSymmetricSector.lean).
  Boundary: Exact-wall fibers, base-gravity cross-term and densitized/flat models require separate
  intertwiners to identify the full coupled record.

- NS. Inner operator and reusable proof: Positive eliminated sum-of-squares realization,
  `h=H_visc+H_advect`; [one-body enclosure](Ns/ChapterNsOneBodyDGamma.lean). Boundary: Signed
  Koopman and Lagrangian comparison generators have separate statements; the six-coordinate parcel
  does not construct all cross-momentum products.

- Real scalar λφ⁴. Inner operator and reusable proof: the continuous-momentum
  `h = ½p_φ² + ½(k₁²+k₂²+k₃²)φ² + (λ/4)(φ²−v²)²` on `L²(ℝ³_k × ℝ_φ)`, with the
  one-particle ESA ([Mehler core](Phi4/ChapterScalarMehler.lean)), the unconditional inner gap
  and unique outer vacuum ground state ([momentum gap](Phi4/ChapterScalarMomentumGap.lean),
  [outer energy](Phi4/ChapterScalarEnergy.lean)), the two-sided return interval at `t=1/100`
  ([rank-2 orbit](Phi4/ChapterScalarMomOrbit.lean)), and the outer shift law
  `dΓ(h+cI)=dΓ(h)+c·N_out` with its one-particle sector identification
  ([sector ops](Phi4/ChapterScalarSectorOps.lean)). Boundary: the frozen periodic lattice
  (`siteModel`, `twoSite`) and the static-jet comparison (`jetModel`) are not this object.


## Consequences of the enclosure

- `HΩ=0` follows from the right annihilator, without positivity. Ground status
  additionally needs `h≥0`. A negative inner direction defeats the outer ground
  claim; on bosonic outer Fock space repeated occupation is unbounded below.
- If `h≥mI`, `m>0`, on the **whole** inner space, the nonvacuum sector floor is
  at least `m`. A lower bound off an inner ground vector or `E₁-E₀>0` is a
  different target. Inner zero modes have nonvacuum outer occupations of energy
  zero, so the full ground projection need not be the vacuum projection.
- `dΓ(h+cI)=dΓ(h)+c N_out`; restoring or removing an inner scalar changes the
  model. It is not a harmless choice of the outer zero of energy.
- Form products inside first: `dΓ(B²)` generally differs from `dΓ(B)²`, which
  includes cross-particle terms. At outer occupation two, `B=I` already gives
  `2` versus `4`. Inner pair terms can change inner occupation while outer
  number stays conserved. Outer quadraticity does not discard inner interactions.
- Apply the existing core/closure and second-quantization machinery to the
  identified `h`. ESA gives a determined unitary dynamics; it gives neither
  positivity nor a mass gap. A failed sufficient comparison estimate does not
  refute ESA proved by another route.

## Spatial products: an NS/QG obligation inside the inner operator

For the Mathlib convention `exp(-2πi⟨x,q⟩)`, the differentiated leg contributes
`2πi q_m`:

$$\mathcal F(f\partial_m g)(Q)
 =\int \hat f(Q-q)\,2\pi i q_m\,\hat g(q)\,dq.$$

[The Schwartz convolution proof](ChapterNsAdvectionConvolution.lean) proves this
identity with its regularity hypotheses. Spatial momentum `q` is not the
canonical momentum `-i∂/∂u` on field configuration space. Products still couple
momenta after eliminating derivative coordinates. Multiple factors require
iterated convolutions; a vielbein inverse or full exponential cannot be
silently replaced by a finite Taylor polynomial.

[The NS determinant convolution](Ns/ChapterNsLagrangianDetConvolution.lean)
retains cross-mode minors. [The new grid reconstruction](Ns/ChapterNsVolDomReconstruction.lean)
proves orthogonality for commensurate, distinguishable dual-lattice labels and
characterizes aliasing in all three directions. It assumes those labels and
constancy of the residual in its single-mode specialization. A diagonal
same-parcel symbol or momentum-block Gram matrix proves a reduced model until
its full convolution operator, measure and core are intertwined. Apply this
elimination device to NS/QG only; it does not redefine the QYM/QED proof tracks.

## New proofs to reuse, rather than request again

- [Degree enumeration](Toolbox/ChapterDegreeEnumeration.lean), [basis
  bridge](Toolbox/ChapterHermiteBridgePhases.lean), [QYM core
  gates](Qym/ChapterYangMillsCoreBasisGates.lean). Now available: `exists_degreeCompatible`,
  `coreBasis_eq_hermBasisN`, phase `1`, and the row/column gates for the constructed basis. Still
  separate: The weighted commutator gate for the full QYM matrix.

- [Quartic entry](Toolbox/ChapterHermiteQuarticEntry.lean),
  [sharpness](Toolbox/ChapterFockWeightedGateSharpness.lean). Now available: Exact quartic Hermite
  entry and a one-entry model refutation. Still separate: Actual QYM coefficient and
  non-cancellation; not a refutation of physical ESA.

- [Resolvent transfer](Sirk/ChapterResolventTransfer.lean), [Ritz
  certificates](Sirk/ChapterRitzCertificate.lean), [tables](Sirk/ChapterSirkGapTable.lean). Now
  available: Compression-based second-edge separation, shrinking Temple bands, explicit sufficient
  order, unified scaled rows; exact example order `1`. Still separate: Physical resolvent, edge
  identification, complementary form bound and full-space approximation/tail control.

- [SM remainder](Sm/ChapterSmIndexGhostRemainder.lean), [quartet](Sm/ChapterSmQuartet.lean). Now
  available: First-slot sum split by gauge summand, weak coefficient `-1`, positivity characterized
  on representatives. Still separate: A physical metric, its Krein compatibility and sign, reducing
  Hamiltonian domains; generic nonzero coefficients do not rule out all homotopies.

- [Infinite covariance](OSReconstruction/HalfSpaceInfiniteBandedCovariance.lean), [finite
  norm](OSReconstruction/HalfSpaceChainBandHSNorm.lean). Now available: Autocorrelation,
  sum-of-squares positivity, row norm and finite-volume HS norm. Still separate: Consistent Gaussian
  law, reflection positivity and physical OS-generator identification; no global infinite-volume HS
  conclusion.

