import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Gauge Symmetry and Dissipative Dynamics" =>
%%%
tag := "gauge-symmetry"
%%%

# Orientation and Status

:::paragraph
The opening chapter of the field-theory part, and one of its two vocabulary
chapters: *gauge* is the redundancy of a many-to-one parametrization — exactly
the freedom {ref "born-fiber"}[the fiber chapter] isolated algebraically — and
the BRST machinery is how that redundancy is carried into dynamics. The other
vocabulary chapter is {ref "free-field"}[the free-field construction]; the rest
of the part assumes both.
:::

:::paragraph
The route: Born redundancy, orbit coverage and uniqueness, a worked translation
example, invariant observables and the Mehler measure map, then constraints,
BRST cohomology and dynamics. We distinguish the physical reduction from SIRK
compression and read the numerical constraint probes with those definitions.
The abelian field-strength identities, dissipative examples, parametrizations,
Casimir constraints and averaging complete the chapter. The
{ref "gribov-ambiguity"}[Gribov chapter] keeps global and mass-gap claims separate.
:::

:::paragraph
The proofs are spread over `BookProof/BRSTNilpotent`, `BookProof/GhostField`,
`BookProof/BrstReducedTransfer`, `BookProof/FreeFieldConstraint`,
`BookProof/IrreversibleDynamics`, and the gauge-fixing and Casimir-averaging
chapters. The derivative-variable constructions in NS/QG are historical
presentations alongside the current Fourier elimination route; neither is a
substitute for proving the physical gauge reduction of the interacting model.
:::

# The Idea: Gauge Is a Redundancy of the Parametrization

:::paragraph
The wave-function parametrization of a probability measure is *many-to-one*. The
same distribution $`p(x) = |\Psi(x)|^2` is reproduced by many different
wave-functions, and the freedom between them is a *gauge symmetry*: a group of
transformations of the wave-function that leave the probabilities unchanged. This
chapter studies that redundancy and its consequences. A measurable
representative map can impose an exact constraint by pushing a prior forward;
a null constraint surface under the original prior is then no contradiction.
Constructing that map for the actual field model is an additional obligation.
The wave-function parametrization also extends to classical dissipative dynamics. The verified content here is the finite,
algebraic core of that story: the gauge redundancy of the Born map, the identity
showing constraints that commute with the Hamiltonian are conserved, the
nilpotency of the BRST charge (which makes the gauge-invariant algebra
well-defined), and the abelian case where the Gribov ambiguity does not arise.
:::

# The Gauge Redundancy of the Born Parametrization

:::paragraph
Over $`\mathbb{R}^n`, the Born map sends a (normalized) wave-function to its
squared components, $`x \mapsto (x_k)^2` under the constraint
$`\sum_k x_k^2 = 1`. The manuscript stresses that *"two wave-functions are always
related by a rotation of the hypersphere"* — the parametrization is a surjection
of the sphere onto the simplex, and it is never a bijection. The first, minimal
source of redundancy is the *antipodal* map: replacing $`x` by $`-x` leaves every
Born probability unchanged:
:::

```
#check @BookProof.ChapterFreeFieldBornGauge.bornMap_neg
#check @BookProof.ChapterFreeFieldBornGauge.bornMap_not_injOn_sphere
```

:::paragraph
The second states the redundancy as a *group*: the full diagonal sign group
$`\{-1,+1\}^n` acts by coordinate-wise reflections $`x_k \mapsto s_k x_k`, each
an isometry of the sphere, and the born image is invariant under the whole group:
:::

```
#check @BookProof.ChapterFreeFieldBornSignGauge.signFlip
#check @BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip
```

:::paragraph
So the gauge group of the real Born parametrization contains at least the finite
abelian group $`\{-1,+1\}^n`; the antipodal map is the special case $`s \equiv -1`.
This is a verified redundancy relative to the specified Born probability map.
A generic sphere rotation can change the labelled Born probabilities; it is
not thereby a gauge transformation. Likewise, invariance of a Gaussian prior
under a rotation does not make that rotation a gauge symmetry of every chosen
observable. The map or observable algebra being held fixed must be named.
:::

# Comprehensive Fixing: Keep Every Physical Orbit

:::paragraph
Let a gauge group $`G` act on a configuration carrier $`X`. Two configurations
represent the same physical configuration when they lie in the same orbit.
A fixing is a subset $`S\subseteq X`. The manuscript uses two independent
conditions:
:::

| Condition | Meaning | What it controls |
| :--- | :--- | :--- |
| comprehensive | every orbit meets $`S` | no orbit is omitted |
| complete | each orbit meets $`S` at most once | no duplicate representatives |

:::paragraph
Comprehensiveness is the essential condition for retaining all physical
configurations. Completeness is an additional choice of representation. A
comprehensive but incomplete fixing is useful: it retains redundant points and
requires observables to agree on points of the same orbit. The full carrier
$`S=X` is the simplest comprehensive fixing. Under a nontrivial free action it
is incomplete, while its gauge-invariant observable algebra is perfectly defined.
Completeness concerns representative points; it does not itself exclude
stabilizers. The separate `MovesEveryPointOfSpectrum` predicate expresses
freeness in this part of the formalization.
:::

```
#check @BookProof.ChapterGaugeIncompleteFixing.univ_isComprehensiveGaugeFixing
#check @BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete
#check @BookProof.ChapterGaugeIncompleteFixing.physicalSubalgebra
#check @BookProof.ChapterGaugeIncompleteFixing.isPhysicalObservable_iff_factors
```

# A Worked Example: Integer Translations

:::paragraph
Take $`G=\mathbb Z` acting on $`\mathbb R` by $`n\cdot x=x+n`.
A physical observable satisfies $`f(x+n)=f(x)`. The four possible combinations
of coverage and uniqueness are concrete:
:::

| Fixing $`S` | Comprehensive? | Complete? |
| :--- | :--- | :--- |
| $`\mathbb R` | yes | no |
| $`[0,1)` | yes | yes |
| $`\{0\}` | no | yes |
| $`\{0,1\}` | no | no |

:::paragraph
On the whole line, keep the periodicity condition. On $`[0,1)`, each orbit
has one representative, so any real-valued function extends uniquely to a
periodic function on the line. On $`\{0\}`, entire orbits such as
$`1/2+\mathbb Z` disappear: removing redundancy has also removed physical
information. Thus “fewer coordinates” is not an adequate acceptance test for
a fixing. The unit-cell and four-way classification theorems formalize this
example at the level of sets and functions.
:::

```
#check @BookProof.ChapterGaugeComprehensiveFixing.unitCell_isComprehensiveGaugeFixing
#check @BookProof.ChapterGaugeComprehensiveFixing.unitCell_isCompleteGaugeFixing'
#check @BookProof.ChapterGaugeComprehensiveFixing.shift_gaugeFixing_classification
```

# Restricting Observables, Rather Than Deleting States

:::paragraph
For an invariant function $`f:X\to\mathbb R`, restriction to a comprehensive
$`S` loses no information: equality on $`S` implies equality everywhere.
On an incomplete $`S`, an arbitrary function extends to an invariant function
exactly when its values respect the remaining orbit identifications. If $`S`
is also complete, this compatibility requirement is automatic. The restriction
map is then a bijection between invariant functions on $`X` and functions on
$`S`. These are statements about all real functions; measurability, boundedness
and operator domains require further hypotheses.
:::

```
#check @BookProof.ChapterGaugeIncompleteFixing.physical_ext_of_comprehensive
#check @BookProof.ChapterGaugeIncompleteFixing.exists_physical_extension
#check @BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive
#check @BookProof.ChapterGaugeComprehensiveFixing.physical_extension_iff_complete
#check @BookProof.ChapterGaugeComprehensiveFixing.existsUnique_physical_extension_of_complete
#check @BookProof.ChapterGaugeComprehensiveFixing.exists_physical_ne_agreeing_of_not_comprehensive
#check @BookProof.ChapterGaugeComprehensiveFixing.exists_not_extendable_of_not_complete
```

:::paragraph
The Hilbert-space version concerns operators commuting with a specified unitary
gauge action. Such an operator has the same expectation in gauge-related
vectors. This does not require every representing vector to be gauge invariant,
and it does not construct a positive BRST physical Hilbert space. The observable
commutant and the state cohomology are related constructions with distinct inputs.
:::

```
#check @BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer
#check @BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant
```

# Mehler Probability: Exact Constraints Need a Measure Map

:::paragraph
In {ref "solovay-tensor"}[the Mehler–Kopperman framework], the Gaussian prior
lives on a coordinate probability space and its square-integrable
wave-functions form a Hilbert space. A finite channel factor tensors with that
space. Neither a tensor factor nor Gaussian concentration supplies a gauge
section, a constraint projector or a physical inner product. The physical
observable algebra must first be specified on the actual model.
:::

:::paragraph
Suppose a measurable map $`q:X\to X` takes each configuration to a
representative in $`S` on the same orbit. The induced law is
$`\nu=q_*\mu`. It gives $`S` full measure when the support condition is
measurable, and preserves expectations of invariant observables because
$`f\circ q=f`. For example, translations of the second coordinate of
$`\mathbb R^2` admit $`q(x,y)=(x,0)`. A two-coordinate standard Gaussian
pushes forward to a Gaussian in $`x` and a point mass at $`y=0`, even though
the original Gaussian gives that line measure zero. This is a pushforward law,
not conditioning by dividing by the probability of that null line.
:::

```
#check @BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet
#check @BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection
```

:::paragraph
Pullback by $`q` preserves $`L^2` norms relative to the pushed-forward law.
Identifying its image with the intended physical wave-functions, and
transporting the Hamiltonian, still require proofs. A Gaussian reference need
not be invariant under a translation gauge action; equality of physical
expectations under the representative map is the relevant condition in this
example. With finite orthogonal coordinate rotations, Mehler invariance is
available from the foundation chapter. A different transformation needs its
own measure or density calculation. Finite-query reduction alone does not
supply a measurable or computable orbit selector.
:::

# Set Representatives, Topology and Auxiliary Variables

:::paragraph
A set of representatives always exists by classical choice. The formal
construction `orbitRepresentatives` uses `Quotient.out`; it proves coverage
and uniqueness as sets. It supplies no measurable, continuous or effective
selector and no formula for the physical measure.
:::

```
#check @BookProof.ChapterGaugeComprehensiveFixing.orbitRepresentatives_isComprehensiveGaugeFixing
#check @BookProof.ChapterGaugeComprehensiveFixing.orbitRepresentatives_isCompleteGaugeFixing'
#check @BookProof.ChapterGaugeComprehensiveFixing.exists_comprehensive_complete_gaugeFixing
```

:::paragraph
The topology theorem has a precise, narrower conclusion. On a nonempty
preconnected carrier with a nontrivial free action, a complete comprehensive
subset cannot be *clopen*. This excludes a continuous Boolean indicator for
that subset. It does not rule out every continuous representative map or
smooth slice. For instance, $`y=0` in the translation example above is closed
but not open, and $`q(x,y)=(x,0)` is continuous. The theorem is an elementary
topological obstruction, not a global field-theoretic Gribov theorem.
:::

```
#check @BookProof.ChapterGaugeComprehensiveFixing.not_isClopen_of_complete_comprehensive
#check @BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator
#check @BookProof.ChapterGaugeComprehensiveFixing.unitCell_not_isClopen
```

:::paragraph
Adjoining a group-valued auxiliary variable gives another proved construction.
For the diagonal action on $`X\times G`, every orbit meets $`X\times\{1\}`
exactly once: $`(x,g)` is represented by $`(g^{-1}\cdot x,1)`.
This is a complete comprehensive fixing of the *extended* action. Its quotient
is parametrized by $`X`, rather than automatically by the original $`X/G`.
Equivalence to the original physical model needs the additional constraints
or a contractible-pair argument, together with compatible measure and dynamics.
Introducing an auxiliary coordinate alone does not establish that equivalence.
:::

```
#check @BookProof.ChapterGaugeComprehensiveFixing.spuriousSection_isComprehensiveGaugeFixing
#check @BookProof.ChapterGaugeComprehensiveFixing.spuriousSection_isCompleteGaugeFixing'
```

# First-Class Constraints as Gauge Generators

:::paragraph
A first-class constraint family closes under the relevant bracket. To realize
it as a quantum gauge action, one must also construct the operators, their
common domains and the unitary action where appropriate. Physical observables
are invariant under the declared action; the state construction must be
specified separately. The manuscript emphasizes that an invariant observable
algebra can exist even when its representing Hilbert space has no normalizable
invariant vector. That is compatible with the commutant formulation above;
it does not itself produce a physical state or a BRST quotient metric.
:::

:::paragraph
Formalizing constraints requires the notion of a *conditional probability*: given
a marginal $`p(x) > 0`, the regular conditional probability
$`p(y|x) = p(x,y)/p(x)` is a genuine probability distribution on $`Y`, and the
joint distribution factors as marginal times conditional. These are the verified
facts that make "conditioning on a constraint" a well-defined operation:
:::

```
#check @BookProof.ChapterConditional.pCond
#check @BookProof.ChapterConditional.pCond_sum_one
#check @BookProof.ChapterConditional.pJoint_eq_cond_mul_marg
```

:::paragraph
Because it is always possible to define such regular conditional probabilities in
a standard measure space, the manuscript argues that exact constraints can in
principle be implemented without giving the constrained space null measure. The
verified finite-dimensional content is the conditional-probability core above.
:::

:::paragraph
Spatial derivative coordinates require a separate decision. Earlier NS/QG
presentations adjoin independent jets and study abelian auxiliary charges.
Adjoining a variable does not by itself turn its defining relation into a
first-class gauge symmetry; the charge algebra and equivalence of the extended
system must be proved. The current route in
{ref "fourier-elimination"}[NS Fourier elimination] and
{ref "qg-elimination"}[QG elimination] substitutes the derivative relations
when defining the operator. Coordinate-space products with spatial derivatives
become momentum-space convolutions. This is an NS/QG construction; it does not
replace the QYM/QED field-strength operator dictionary.
:::

:::paragraph
Eliminating an auxiliary derivative coordinate, solving a second-class pressure
constraint, and reducing a genuine Gauss-law gauge action are different tasks.
A modewise substitution theorem proves the identity stated for its defined
realization. Matching the full spatial product, domains and physical observables
requires the convolution and operator-core bridge. For QG this must retain the
vielbein, the full $`R^2` exponential and its interactions, without a Taylor
replacement. A scalaron fiber alone is a comparison, not that full model.
:::

# Constraints That Commute with the Hamiltonian Are Conserved

:::paragraph
The key dynamical identity comes from the free-field section of the manuscript
(the momentum constraint `i D_x = 0`). If a constraint $`D` commutes with the
Hamiltonian $`H` — $`\{D,H\} = 0` — then the constrained quantity is *conserved*
by the Hamiltonian flow: for every operator $`A`,
:::

$$`\bigl\{\{D,A\},H\bigr\} = -\{D,\{H,A\}\}.`

:::paragraph
This is a direct consequence of the Jacobi identity together with $`\{D,H\}=0`.
Its meaning is that the set of $`D`-invariant observables is closed under
evolution by $`H`: the constraint is preserved. A conserved quantity is not
automatically a gauge generator; that interpretation also needs the declared
action and its redundant observables. The verified statement is the general
algebraic fact, with the book's two literal instances (for the field $`\varphi^{(0)}` and the
momentum $`p_{(1)}`):
:::

```
#check @BookProof.FreeFieldConstraint.bracket
#check @BookProof.FreeFieldConstraint.bracket_jacobi
#check @BookProof.FreeFieldConstraint.constraint_commutation_identity
#check @BookProof.FreeFieldConstraint.constraint_preserved_under_bracket
```

# The BRST Charge and the Ghost Field

:::paragraph
The manuscript's gauge-mechanics example quantizes a classical gauge system on the
Hilbert space $`L^2(\mathbb{R}^2 \times \mathbb{Z}_2)`,
where the $`\mathbb{Z}_2` factor is the ghost degree of freedom. The gauge
generator is the charge $`Q = \pi\phi + \pi^*\phi^*`, and the BRST charge is
$`\Omega = (\pi\phi + \pi^*\phi^*)\,\psi^\dagger` with the ghost field $`\psi`
satisfying the canonical anticommutation relation $`\{\psi,\psi^\dagger\}=1`.
The wave-function itself need not be gauge invariant — only the observables must
commute with $`Q`. The manuscript separates the gauge generator from the
gauge-invariant algebra by requiring the latter to be a subalgebra of the
commutative von Neumann algebra generated by $`\phi,\phi^*,k`.
:::

:::paragraph
The verified content is the ghost-field algebra and the single property that makes
the whole BRST construction well-defined: the nilpotency of the BRST charge,
$`\Omega^2 = 0`. Concretely, on the two-dimensional $`\mathbb{Z}_2` Fock factor
the ghost operators are the matrices
:::

$$`\psi = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}, \qquad
  \psi^\dagger = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix},`

:::paragraph
with $`\psi^2 = 0`, $`\psi^{\dagger 2} = 0` (Pauli exclusion), and the canonical
anticommutation relation $`\{\psi,\psi^\dagger\} = 1`; the number operator
$`N = \psi^\dagger\psi` is an orthogonal projection, so the ghost occupation is
$`0` or $`1`:
:::

```
#check @BookProof.GhostField.psi
#check @BookProof.GhostField.psiDag
#check @BookProof.GhostField.psi_sq
#check @BookProof.GhostField.car
#check @BookProof.GhostField.numberOp_idempotent
#check @BookProof.GhostField.numberOp_selfAdjoint
```

:::paragraph
The nilpotency itself holds abstractly in any ring: if the ghost factor $`f` is
square-zero and the bosonic field factor $`b` commutes with it, then the composite
$`\Omega = b\cdot f` satisfies $`\Omega^2 = 0`. With $`f = \psi^\dagger` and $`b`
the divergence field factor this is the book's $`\Omega^2 = 0`. For the
non-abelian case, the cubic ghost term $`Q = \sum_{a,b,e} f_{abe}\,
(\psi_a^\dagger\psi_b^\dagger\psi_e)` of the BRST charge also squares to zero,
given the canonical anticommutation relations and structure constants that are
antisymmetric in their first two indices and satisfy the Jacobi identity:
:::

```
#check @BookProof.GhostField.brst_charge_nilpotent
#check @BookProof.BRSTNilpotent.GhostCAR
#check @BookProof.BRSTNilpotent.Q
#check @BookProof.BRSTNilpotent.brst_charge_nilpotent
```

:::paragraph
Nilpotency of the declared charge makes its algebraic cohomology well defined.
The ghost identities above are reusable pieces. For a full coupled charge,
the Gauss representation and cross terms must also be checked, as in the
book-charge construction discussed in {ref "standard-model"}[the SM chapter].
Identifying this state cohomology with the intended physical observable theory,
its metric and dynamics is the next step, rather than a consequence of a ghost
matrix identity alone.
:::

# The Reduced Dynamics on BRST Cohomology

:::paragraph
Nilpotency makes the cohomology well defined; it does not yet say that the
*dynamics* respects it. That is a separate requirement, and it is the one the
manuscript's transfer operator has to meet: the evolution must map the physical
(BRST-closed) subspace to itself, and it must not mix physical states with
pure-gauge (BRST-exact) ones, so that it descends to the quotient. Writing
$`\mathrm{ker}\,\Omega` for the closed states and $`\overline{\mathrm{ran}\,\Omega}`
for the exact ones — the closure is what makes the quotient a topological object —
the BRST cohomology is $`\mathrm{ker}\,\Omega/\overline{\mathrm{ran}\,\Omega}`:
:::

```
#check @BookProof.BrstReducedTransfer.physicalStates
#check @BookProof.BrstReducedTransfer.exactStates
#check @BookProof.BrstReducedTransfer.exactStates_le_physicalStates
#check @BookProof.BrstReducedTransfer.Cohomology
```

:::paragraph
Any bounded operator commuting with $`\Omega` preserves both subspaces — for the
exact states this needs a continuity argument, since the range is only dense in its
closure — and therefore induces a linear map on the cohomology. Applied to a
one-parameter family this gives the *reduced transfer*: a one-parameter group of
linear automorphisms of the BRST cohomology, which moreover preserves the quotient
(BRST) norm when the family is isometric.
:::

```
#check @BookProof.BrstReducedTransfer.physicalStates_invariant
#check @BookProof.BrstReducedTransfer.exactStates_invariant
#check @BookProof.BrstReducedTransfer.reducedMap
#check @BookProof.BrstReducedTransfer.transfer
#check @BookProof.BrstReducedTransfer.transfer_comp
#check @BookProof.BrstReducedTransfer.transfer_bijective
#check @BookProof.BrstReducedTransfer.infDist_exactStates_eq_of_comm_explicit
```

:::paragraph
The case of interest is the unitary group $`e^{-itT}` of an unbounded self-adjoint
Hamiltonian commuting with the BRST charge — the half-density evolution of the
quantization chapters. It maps the physical subspace to itself, it moves two states
that differ by a gauge vector to two states that still differ by a gauge vector, and
the induced group on cohomology is norm-preserving:
:::

```
#check @BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_of_comm_explicit
#check @BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_of_comm_explicit
#check @BookProof.BrstReducedTransfer.stoneTransfer
#check @BookProof.BrstReducedTransfer.stoneTransfer_comp
#check @BookProof.BrstReducedTransfer.stoneTransfer_bijective
#check @BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_of_comm_explicit
```

:::paragraph
The first transfer package assumes a bounded nilpotent charge. The unbounded
charge case is also available: `ChapterBrstReducedTransferUnbounded` treats a
closed densely defined charge, with domain preservation and strong commutation
by the evolution group. A formal commutator on a core alone does not supply
those hypotheses.
:::

```
#check @BookProof.BrstReducedTransferUnbounded.DomPreserve
#check @BookProof.BrstReducedTransferUnbounded.StrongCommute
#check @BookProof.BrstReducedTransferUnbounded.transfer_comp
#check @BookProof.BrstReducedTransferUnbounded.stoneTransfer
```

# A BRST Quotient Still Needs Its Physical Metric

:::paragraph
Nilpotency supplies $`\operatorname{im}Q\subseteq\ker Q`. The completed
Hilbert quotient uses the closure of the exact space, subject to the charge's
domain conditions. A positive ambient Hilbert quotient norm can then be
studied. An indefinite ghost construction instead needs a charge form
$`[x,y]_\eta=\langle x,\eta y\rangle` which descends to the quotient and
is positive there with the required null space. These are distinct metric
claims. The intended physical ghost-number degree and a nonzero physical
state must also be identified.
:::

:::paragraph
The finite SM quartet package decomposes closed vectors through
$`Qb+bQ=I-P_{\rm harm}`. Its canonical homotopy identifies harmonic
representatives with $`\ker Q\cap(\operatorname{im}Q)^\perp` in the ambient
Hilbert metric. This algebra does not identify them with the physical transverse
field modes or prove positivity of an indefinite charge form. Existing
positivity equivalences leave the metric and sign assumptions explicit.
:::

```
#check @BookProof.SmQuartet.smPhysProjFormula_range
#check @BookProof.SmQuartet.smPhysicalPositivity_iff_physForm
#check @BookProof.SmQuartet.smPhysicalPositivity_iff_parityNorms
```

:::paragraph
Ghost grading, metric and physical projection must be named separately. The
current specialist plan records a consistency check: if $`U^2=I`,
$`UQ=-QU`, $`Q^2=0`, and $`Q` is symmetric for the form with $`\eta=U`,
substituting $`y=UQx` gives $`\|Qx\|^2=0`. Thus these global premises force
$`Q=0`. Likewise an even $`b` with $`QbQ=Q` would make an odd $`Q` both
even and odd, again forcing zero. The source now contains the latter
obstruction as `even_homotopy_imp_charge_eq_zero`, and an averaged invariant
projection construction. These additions have not been compiled by this
book-editing wave. The metric consistency calculation remains a specialist
verification task. A physical nonzero-charge construction needs compatible
metric and homotopy choices; success under vacuous premises is not a no-ghost
theorem. `SM_ESA_COMPLETION_PLAN.md` SM1/SM4 and the appendix specify the tasks.
:::

```
#check @BookProof.SmQuartet.BrstQuartet.even_homotopy_imp_charge_eq_zero
#check @BookProof.SmQuartet.BrstQuartet.exists_invariant_projection
```

:::paragraph
The averaged projection commutes with the grading and projects onto a specified
invariant subspace. Its existence is an algebraic complement construction; it
does not supply positivity, a bounded operator in infinite dimension, or a
projection reducing the physical Hamiltonian.
:::

# From Physical Inner Dynamics to the Outer Hamiltonian

:::paragraph
Once the physical inner space and its self-adjoint generator $`h_{\rm phys}`
are identified, the final nested-Fock Hamiltonian is
:::

$$`H_{\rm final}=d\Gamma_{\rm out}(h_{\rm phys})
=\sum_{i,j}C^\dagger(e_i)(h_{\rm phys})_{ij}A(e_j).`

:::paragraph
Creation is on the left and annihilation on the right. Every inner interaction
and constant is retained. A restriction or quotient must intertwine the closed
inner dynamics before it is used in this enclosure. A parity decomposition is
not a BRST quotient; a graded outer statistics construction is another step.
The right annihilator kills the outer vacuum, while an outer-vacuum ground
requires $`h_{\rm phys}\ge0` and a strict vacuum gap requires an absolute
positive lower bound. Neither orbit coverage nor gauge fixing alone supplies
those bounds. For an unreduced operator, label its enclosure accordingly until
the physical identification is proved.
:::

# SIRK Compression Is a Separate Approximation

:::paragraph
Write $`P_{\rm num}=VV^*` for a retained numerical subspace. It is not the
physical projector or a representative map. Even for a nilpotent full charge,
$`Q_m=V^*QV` need not be nilpotent: on compatible domains,
:::

$$`Q_m^2=-V^*Q(I-P_{\rm num})QV.`

:::paragraph
A nonzero compressed square can therefore reflect discarded directions.
Conversely a tiny retained charge can reflect a window that misses charged
states. Check full images outside the window and specify the complete charge
before interpreting either result. Physical reduction and compression commute
only when the required invariant subspaces and intertwiners are proved.
:::

:::paragraph
For a bounded charge commuting with the exact unitary flow, an evolution error
$`\|\psi_m(t)-\psi(t)\|\le\varepsilon(t)` gives
$`\|Q\psi_m(t)\|\le\|Q\psi(0)\|+\|Q\|\varepsilon(t)`.
For an unbounded charge, state-norm error alone cannot supply this estimate;
control in its graph norm or a suitable bounded observable is needed. The
{ref "sirk-reliability"}[reliability chapter] distinguishes proved Galerkin
leakage bounds from the new full-action bound proposed for the actual rational
joint solver. Increasing Krylov rank alone is not a proof of physicality.
:::

# What the Current Numerical Tests Establish

:::paragraph
The `unfer` complete-SM path assembles the full independent-coordinate E1
inner operator and uses joint rational SIRK, including actual shifted solves.
It retains inner constants and supports graded outer states. The present
numerical windows are not a constructed physical BRST quotient. Historical
measurements in `../unfer/docs/SM_FULL_IMPLEMENTATION.md`, interpreted by its
2026-11-15 scope note, illustrate the difference:
:::

| Recorded diagnostic | Interpretation |
| :--- | :--- |
| electric penalty floor $`9` | zero-point floor of that probe, not a physical gap |
| density-probe $`\|Q^2\psi\|\simeq0.1392044` | incomplete charge probe is not nilpotent |
| 44-state-band $`\|(I-P)HP\|\simeq0.6234982` | the selected band does not reduce that $`H` |

:::paragraph
The density probe omits the full nonabelian ghost completion; the source test
expects its nonzero square. The failure is not evidence that an actual complete
SM charge cannot exist. Similarly, a longitudinal kinetic subtraction is a
comparison until its constraint solution, induced interactions and measure are
derived. Generic compression defects and this incomplete-charge defect must
not be conflated. No test was rerun for this documentation edit.
:::

:::paragraph
The next evidence comes from `../unfer/docs/SM_RESEARCH_PLAN.md` N7–N10:
match the actual Mehler/operator dictionary; bound full-action evolution error;
construct and test the joint gauge/Higgs/matter/ghost charge; then check its
metric, ghost number and dynamics on nonzero physical representatives. The
specialist must report truncation, solve, rounding and charge-model errors
separately. Finite toy identities and historical passes remain useful oracles;
they do not certify the complete physical theory.
:::

# The Abelian Case: No Gribov Ambiguity

:::paragraph
The abelian identity proved here is local gauge invariance of the curl:
$`F_{jk}=\delta_jA_k-\delta_kA_j` is unchanged by
$`A\mapsto A+\partial\theta` when the derivations commute. It is not by
itself a construction of a globally complete gauge slice. Boundary conditions,
zero modes and the intended gauge group still have to be specified. The
{ref "gribov-ambiguity"}[next gauge chapter] keeps this distinction explicit.
:::

```
#check @BookProof.FreeEMField.emFieldStrength
#check @BookProof.FreeEMField.emFieldStrength_gauge_invariant
#check @BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute
```

:::paragraph
The last statement is the reduction itself: when the connection components
commute, the non-abelian field strength loses its quadratic correction and becomes
the linear abelian one — which is why the Hamiltonian is quadratic in the fields
in this case.
:::

# Dissipative Dynamics: Irreversibility Without a Classical Hamiltonian

:::paragraph
The manuscript also uses the wave-function parametrization to describe *classical
dissipative dynamics*. Its example is two classical coupled oscillators with
different frequencies and different damping constants,
:::

$$`\ddot{x}_1 + \lambda_1 \dot{x}_1 + \omega_1^2 x_1 - c_2 x_2 = 0, \qquad
  \ddot{x}_2 + \lambda_2 \dot{x}_2 + \omega_2^2 x_2 - c_1 x_1 = 0.`

:::paragraph
This motion cannot be derived from a Lagrangian, and so has no classical
Hamiltonian without enlarging the system; yet because a probability measure
exists for the system, we can still define a *quantum* Hamiltonian and quantum
constraints — which are more general than the classical ones because they do not
need to commute with the variables defining the sample space. The system is
dissipative (the energy is not conserved) but the degrees of freedom do not
disappear, so the *probability* is conserved. The manuscript's slogan is that
"the quantum formalism is the most general formalism whenever there is a
conserved probability."
:::

:::paragraph
The verified content here is the *dissipative* (irreversible, non-conservative)
character of such dynamics, which is what obliges one to work with a probability
measure rather than a conserved energy. In a *finite* world a deterministic
self-map is injective iff surjective iff bijective, so there is no
injective-but-not-surjective (i.e. irreversible, dissipative) map at all — the
discrete counterpart of the manuscript's remark that "the rationals are not
enough":
:::

```
#check @BookProof.IrreversibleDynamics.finite_injective_iff_surjective
#check @BookProof.IrreversibleDynamics.finite_no_irreversible
```

:::paragraph
On an infinite state space such a map exists. The concrete dissipative example is
the halving map $`x \mapsto x/2` on the unit interval: it is *injective* (no two
points collapse together) but *not surjective* onto its domain (the point $`1` is
not hit), hence irreversible — the halving of an interval is genuinely
"dissipative", shrinking its length by a factor of two — yet it is *non-singular*:
it maps every interval of positive length to a set of positive measure, so no
probability mass is lost. This is exactly the manuscript's *"a process with a
dissipative time-evolution is irreversible: the deterministic time-evolution is
not an invertible function (it is injective but not surjective). Then there is
time asymmetry"*:
:::

```
#check @BookProof.IrreversibleDynamics.dissipative_injective
#check @BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval
#check @BookProof.IrreversibleDynamics.dissipative_volume_Icc
#check @BookProof.IrreversibleDynamics.dissipative_nonsingular_Icc
```

:::paragraph
This is the precise sense in which dissipative dynamics escapes the classical
Hamiltonian framework while remaining within the wave-function parametrization:
the dynamics is irreversible (injective, not surjective) and loses energy, but
since it is non-singular it conserves probability, and that conserved probability
is all the quantum formalism needs.
:::

:::paragraph
The manuscript's *specific* dissipative system is the damped coupled oscillator,
and its energy balance is proved rather than read off. For a solution of
$`\ddot x + \lambda\dot x + \omega^2 x = 0` the energy $`E = \tfrac12\dot x^2 +
\tfrac12\omega^2 x^2` obeys $`\dot E = -\lambda\dot x^2`, so it is non-increasing for
non-negative damping, and it is *not* constant at any instant at which the damping
is positive and the oscillator moves. The coupled system of the manuscript,

$$`\ddot{x}_1 + \lambda_1 \dot{x}_1 + \omega_1^2 x_1 - c_2 x_2 = 0, \qquad
  \ddot{x}_2 + \lambda_2 \dot{x}_2 + \omega_2^2 x_2 - c_1 x_1 = 0,`

satisfies the same identity, $`\dot E = -\lambda_1\dot x_1^2 - \lambda_2\dot x_2^2`,
with monotonicity and non-conservation inherited. An explicit critically damped
solution shows the statement is not vacuous: its energy is strictly decreasing. And
the total probability is conserved by *any* measurable deterministic evolution, so
energy loss and probability conservation are not in tension.
:::

```
#check @BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy
#check @BookProof.DampedOscillatorEnergy.dampedEnergy_antitone
#check @BookProof.DampedOscillatorEnergy.dampedEnergy_not_constant_of_damped
#check @BookProof.DampedOscillatorEnergy.hasDerivAt_coupledEnergy
#check @BookProof.DampedOscillatorEnergy.coupledEnergy_antitone
#check @BookProof.DampedOscillatorEnergy.coupledEnergy_not_constant_of_damped
#check @BookProof.DampedOscillatorEnergy.criticallyDamped_energy
#check @BookProof.DampedOscillatorEnergy.criticallyDamped_energy_strictAnti
#check @BookProof.DampedOscillatorEnergy.total_probability_conserved
```

# Parametrizations Are Gauge Symmetries

:::paragraph
A more structural reading of the same phenomenon: *every* parametrization carries a
gauge group. For a map $`\pi : X \to Y` the group is the set of permutations of the
parameter space that fix the parametrized point, `fiberGauge π`; its orbits are
exactly the fibers, and its invariant observables are exactly the functions of the
parametrized point. The group is trivial precisely when the parametrization is
redundant-free, and the two axes above reappear as injectivity of the
parametrization on the gauge fixing (completeness) and surjectivity onto the
fibers (comprehensiveness).
:::

```
#check @BookProof.ChapterGaugeParametrization.fiberGauge
#check @BookProof.ChapterGaugeParametrization.orbit_eq_fiber
#check @BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through
#check @BookProof.ChapterGaugeParametrization.fiberGauge_eq_bot_iff
#check @BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff
#check @BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing'_iff_injOn
#check @BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn
```

# Casimir Constraints and Gauge Averaging

:::paragraph
The manuscript's device for imposing *all* constraints at once is the quadratic
Casimir of a family of Hermitian generators. That it works is a theorem here: the
expectation of the Casimir in a state is the sum of the squared norms of the
constraint expectations, so its kernel is *exactly* the intersection of the kernels
of the individual constraints — setting the single Casimir to zero really does
impose every constraint.
:::

```
#check @BookProof.ChapterGaugeCasimirAverage.casimir_apply
#check @BookProof.ChapterGaugeCasimirAverage.inner_casimir
#check @BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff
#check @BookProof.ChapterGaugeCasimirAverage.ker_casimir
```

:::paragraph
Averaging is the other half: the Haar average (for a right-invariant measure) and
the finite normalized average of any observable are gauge-invariant, normalized on
the constants, and fix the observables that were already invariant — averaging is a
projection onto invariant functions under the stated measure assumptions.
The probability normalization used to fix constants is a separate hypothesis;
a normalized invariant Haar law is not supplied for every gauge group.
Pointwise limits preserve invariance under a fixed action. This does not prove
absence of quantum gauge anomalies: a regularized interacting model must also
supply a compatible action, charge algebra and measure. The pushforward theorem
separately preserves invariant expectations when a measurable representative
map is already available.
:::

```
#check @BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable
#check @BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable
#check @BookProof.ChapterGaugeCasimirAverage.finiteGaugeAverage_isPhysicalObservable
#check @BookProof.ChapterGaugeCasimirAverage.finiteGaugeAverage_of_isPhysicalObservable
#check @BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto
#check @BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet
#check @BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection
```

# Reading the Results Together

Comprehensive fixing retains every orbit. An incomplete comprehensive fixing
retains redundancy while identifying physical observables through their orbit
values. The set-level coverage and extension theorems establish this part of
the programme. Mehler probability adds a reference law and wave-function
Hilbert space; physical reduction needs the actual measurable map or BRST
construction, positive physical metric and compatible closed dynamics.

SIRK then approximates the identified generator. Its retained subspace,
constraint diagnostics and numerical error bounds have to be related to that
physical construction. The existing transfer and leakage theorems supply
interfaces; the full field-model instances and algorithm-specific certificates
remain separate specialist tasks in {ref "proof-plans"}[the appendix].
