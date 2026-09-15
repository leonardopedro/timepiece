import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Gauge Symmetry and Dissipative Dynamics" =>
%%%
tag := "gauge-symmetry"
%%%

# The Idea: Gauge Is a Redundancy of the Parametrization

:::paragraph
The wave-function parametrization of a probability measure is *many-to-one*. The
same distribution $`p(x) = |\Psi(x)|^2` is reproduced by many different
wave-functions, and the freedom between them is a *gauge symmetry*: a group of
transformations of the wave-function that leave the probabilities unchanged. This
chapter studies that redundancy and its consequences. The manuscript's thesis is
that the wave-function parametrization lets us implement gauge symmetries as
*exact constraints* in a standard probability space *without* giving the
constrained space null measure, and that the same parametrization extends to
classical dissipative dynamics. The verified content here is the finite,
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
This is the concrete, verified seed of the manuscript's claim that the
parametrization is genuinely redundant — a surjection with fibers, never a
bijection.
:::

# First-Class Constraints as Gauge Generators

:::paragraph
The manuscript's "gauge transformations, constrained systems and conditioned
probability" section develops the general picture: a *first-class constraint* is
the generator of a unitary gauge group, all of whose operators are constrained to
be the identity. The dynamical content is that an observable must commute with the
gauge generator, and therefore the *gauge-invariant algebra* is what is
constrained — not the Hilbert space, and not the individual wave-function (the
manuscript quotes Dirac on the "standard ket" that cannot be gauge invariant).
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
evolution by $`H` — a constraint that commutes with the Hamiltonian is preserved,
which is exactly what makes it a *gauge* constraint rather than a merely
initial-condition-imposed one. The verified statement is the general algebraic
fact, with the book's two literal instances (for the field $`\varphi^{(0)}` and the
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
$`\Omega = (\pi\phi + \pi^*\phi^*)\,\psi^\dagger` with the ghost field $`\psi`$
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
This nilpotency is what makes the BRST cohomology — and hence the physical,
gauge-invariant algebra that the manuscript proposes as the definition of the
constrained theory — well defined. It is the concrete counterpart of the
manuscript's claim that the gauge generators of the group "cannot be interpreted
literally": the physical content lives in the gauge-invariant (cohomological)
algebra, not in the individual wave-function.
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
#check @BookProof.BrstReducedTransfer.infDist_exactStates_eq
```

:::paragraph
The case of interest is the unitary group $`e^{-itT}` of an unbounded self-adjoint
Hamiltonian commuting with the BRST charge — the half-density evolution of the
quantization chapters. It maps the physical subspace to itself, it moves two states
that differ by a gauge vector to two states that still differ by a gauge vector, and
the induced group on cohomology is norm-preserving:
:::

```
#check @BookProof.BrstReducedTransfer.stoneU_mem_physicalStates
#check @BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates
#check @BookProof.BrstReducedTransfer.stoneTransfer
#check @BookProof.BrstReducedTransfer.stoneTransfer_comp
#check @BookProof.BrstReducedTransfer.stoneTransfer_bijective
#check @BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq
```

:::paragraph
What is *not* claimed here is a construction of the concrete gauge-fixed field-space
Hamiltonian and its ghost-sector BRST charge; the reduction statement above is what
such a construction has to feed. Nor does the exactness of the reduced dynamics say
anything about the *truncated* dynamics, which does leak out of the physical subspace
— that leakage is bounded separately in the reliability chapter.
:::

# The Abelian Case: No Gribov Ambiguity

:::paragraph
The manuscript contrasts gauge symmetry with anomalies and discusses the Gribov
ambiguity — the fact that the Dirac bracket requires a gauge-fixing that is both
*complete* and *unconstrained*, which is not always possible. For the abelian
(electromagnetic) case the situation is clean: reducing the non-abelian
structure constants to zero, the field strength becomes the linear abelian curl,
which is *gauge invariant* — invariant under the shift $`A_j \mapsto A_j +
\partial_j\theta`, the curl of a gradient vanishing by commutativity of the
partial derivatives. This is the manuscript's "no Gribov ambiguity" for the
abelian theory:
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

# Summary

The gauge symmetry of the wave-function parametrization is a redundancy of the
coordinates, not a new physical phenomenon. Concretely:

 * the Born map is a surjection of the sphere onto the simplex that is never a
   bijection, with at least the diagonal sign group $`\{-1,+1\}^n` in its fiber;
 * constraints that commute with the Hamiltonian are conserved, by the
   constraint-commutation identity (Jacobi);
 * the BRST charge is nilpotent, $`\Omega^2 = 0`, so the gauge-invariant algebra
   is well-defined — one never needs the wave-function itself to be gauge
   invariant;
 * in the abelian limit the field strength is gauge invariant and the Gribov
   ambiguity does not arise.