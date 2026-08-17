import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Quantization Due to Time-Evolution: Yang–Mills and Classical Statistical Field Theory" =>
%%%
tag := "quantization-time-evolution"
%%%

# The Problem

:::paragraph
The manuscript observes that Quantum Yang–Mills theory, Classical Statistical
Field Theory (for Hamiltonians non-polynomial in the fields) and Quantum Gravity
all suffer from severe mathematical inconsistencies. Its proposal is to define a
class of statistical field theories where the probability distribution of the
infinite-dimensional phase-space is defined by a wave-function in a Fock space,
allowing non-polynomial Hamiltonians; and to define gauge symmetries through
algebraic ideals. The verified content here is the algebraic core of that
programme: the structure constants and Jacobi identity of $`SU(3)`, the field
strength and Bianchi identity, the Weyl/CCR quantization relations that arise
from time-evolution, the nilpotent BRST charge, and the positive-definite
Weyl-gauge Hamiltonian.
:::

# The Structure Constants of SU(3)

:::paragraph
Non-abelian gauge theory is controlled by the structure constants $`f_{abc}` of
the gauge group. For unitary generators $`T_a` with $`\operatorname{tr}(T_a T_b) =
\tfrac12\delta_{ab}` and $`[T_a,T_b] = if_{abc} T_c`, the structure constants are
*totally antisymmetric* and satisfy the *Jacobi identity* — the algebraic
conditions that make the Lie algebra of $`SU(3)` consistent:
:::

```
#check @BookProof.YangMillsSU3.TraceOrthonormal
#check @BookProof.YangMillsSU3.ClosesWithStructureConstants
#check @BookProof.YangMillsSU3.structureConstant_formula
#check @BookProof.YangMillsSU3.structureConstant_totally_antisymmetric
#check @BookProof.YangMillsSU3.structureConstant_jacobi
```

:::paragraph
Concretely, the Gell-Mann matrices $`\lambda^a` are hermitian, traceless and
$`\operatorname{tr}(\lambda^a\lambda^b) = 2\delta_{ab}`, and the generators
$`T_a = \tfrac12\lambda^a` realize the abstract orthonormal structure:
:::

```
#check @BookProof.ChapterGellMann.gellMann_isHermitian
#check @BookProof.ChapterGellMann.gellMann_trace_orthonormal
#check @BookProof.ChapterGellMann.su3gen_traceOrthonormal
```

# The Field Strength and the Bianchi Identity

:::paragraph
The covariant derivative $`D_j = \partial_j + a_j` and the field strength
$`F_{jk} = \{D_j, D_k\}` satisfy the key identity: the commutator of two
covariant derivatives is multiplication by the field strength, and the field
strength is antisymmetric. The Bianchi identity $`\varepsilon_{ijk}[D_i,[D_j,D_k]] = 0`
is the cyclic Jacobi identity for double commutators:
:::

```
#check @BookProof.YangMillsFieldStrength.nonabelian_fieldStrength
#check @BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm
#check @BookProof.YangMillsBianchi.bianchi
#check @BookProof.YangMillsBianchi.bianchi_fieldStrength
```

:::paragraph
Specializing to the book's connection $`a_j = -igA_j` recovers the physical
field-strength combination $`F^book_{jk} = (\partial_j A_k - \partial_k A_j) -
ig[A_j,A_k]`:
:::

```
#check @BookProof.YangMillsFieldStrength.Fbook
#check @BookProof.YangMillsFieldStrength.commutator_eq_coupling
```

# Quantization Arises from Time-Evolution: the Weyl Relations

:::paragraph
The manuscript's central slogan is that quantization comes from *time-evolution*
rather than being imposed. The verified content is the finite Heisenberg/Weyl
algebra: position $`X`, momentum $`Y` and central $`Z` obey the CCR
$`[X,Y] = Z`, $`Z` is central with $`Z^2 = 0`, and the Weyl relation
$`e^{aX}e^{bY} = e^{aX + bY + (ab/2)Z}` encodes the exponentiated commutation:
:::

```
#check @BookProof.QuantizationWeyl.comm_XY
#check @BookProof.QuantizationWeyl.Zgen_central
#check @BookProof.QuantizationWeyl.Heis_mul
#check @BookProof.QuantizationWeyl.weyl
#check @BookProof.QuantizationWeyl.weyl_shift
```

:::paragraph
The conjugation identity $`e^{aX}e^{bY}e^{-aX} = e^{bY + abZ}` is the
quantization-by-time-evolution statement: acting by a momentum translation shifts
the position coordinate by the commutator.
:::

# The Nilpotent BRST Charge

:::paragraph
Gauge symmetries are defined through algebraic ideals, and the physical
(gauge-invariant) algebra is the BRST cohomology — which is well-defined because
the BRST charge is nilpotent, $`\Omega^2 = 0`. The cubic ghost part
$`Q = \sum_{a,b,e} f_{abe}(\chi_a\chi_b\beta_e)` of the charge squares to zero,
given the canonical anticommutation relations and the Jacobi identity for the
structure constants:
:::

```
#check @BookProof.BRSTNilpotent.GhostCAR
#check @BookProof.BRSTNilpotent.Q
#check @BookProof.BRSTNilpotent.brst_charge_nilpotent
```

:::paragraph
At the level of the single fermionic ghost factor, the operators $`\psi, \psi^\dagger`
satisfy $`\{\psi,\psi^\dagger\} = 1`, $`\psi^2 = 0`, and the abstract nilpotency
$`(b\cdot f)^2 = 0` for a commuting $`b` and square-zero $`f`:
:::

```
#check @BookProof.GhostField.car
#check @BookProof.GhostField.psi_sq
#check @BookProof.GhostField.brst_charge_nilpotent
```

:::paragraph
The super-bracket $`\{a,b\} = ab - (-1)^{pq}ba` with Koszul sign makes the
graded algebra a Lie superalgebra, satisfying the graded Jacobi identity — the
algebraic skeleton of the fermionic ghost structure:
:::

```
#check @BookProof.ChapterSuperBracket.sbracket
#check @BookProof.ChapterSuperBracket.super_jacobi
#check @BookProof.ChapterSuperBracket.commutator_jacobi
```

# The Weyl-Gauge Hamiltonian Is Positive

:::paragraph
In the Weyl gauge the Yang–Mills Hamiltonian density is
$`H_W = \tfrac12\sum_i \pi_i^2 + \tfrac12\sum_a B_a^2` — a sum of squares of
self-adjoint operators — hence a *positive* operator: every expectation value is
non-negative. This is the fact the manuscript invokes for the mass-gap discussion:
:::

```
#check @BookProof.WeylHamiltonian.weylHamiltonian
#check @BookProof.WeylHamiltonian.weylHamiltonian_isPositive
#check @BookProof.WeylHamiltonian.weylHamiltonian_expectation_nonneg
#check @BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint
```

# The Weyl-Gauge Quadratic Form and the Friedrichs Route

:::paragraph
Positivity of the Weyl-gauge Hamiltonian is the hypothesis of the *Friedrichs
extension theorem*: a densely defined symmetric operator that is bounded below has
a canonical positive self-adjoint extension. For the unbounded (densely defined)
version the sum-of-squares structure survives: on a domain left invariant by the
electric and magnetic field operators, $`H = \tfrac12\sum_i\pi_i^2 +
\tfrac12\sum_a B_a^2` is symmetric and its quadratic form is
$`q(x) = \tfrac12\sum_i\|\pi_i x\|^2 + \tfrac12\sum_a\|B_a x\|^2 \ge 0`:
:::

```
#check @BookProof.YangMillsFriedrichs.weylOpDom
#check @BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn
#check @BookProof.YangMillsFriedrichs.weylOpDom_quadForm
#check @BookProof.YangMillsFriedrichs.weylOpDom_quadForm_nonneg
```

:::paragraph
The analytic heart of the Friedrichs construction is that the form
$`\langle x,y\rangle_H = \langle x,y\rangle + \langle x, Hy\rangle` is a genuine
inner product dominating the ambient norm, and that it is *closable*: a sequence
that is Cauchy in the form norm and tends to $`0` in the ambient space has form
norm tending to $`0`, so the closed form — and with it the extension — is well
defined. This is proved here in general and applied to the Weyl-gauge form:
:::

```
#check @BookProof.YangMillsFriedrichs.formInner
#check @BookProof.YangMillsFriedrichs.formNormSq_ge_normSq
#check @BookProof.YangMillsFriedrichs.re_formInner_sq_le
#check @BookProof.YangMillsFriedrichs.form_closable
#check @BookProof.YangMillsFriedrichs.weylForm_closable
```

:::paragraph
The Friedrichs theorem itself is carried as a *named hypothesis* (Friedrichs 1934;
Reed–Simon Thm X.23), never as an axiom, and is shown to be satisfiable; the
conclusion for the Weyl-gauge Hamiltonian is conditional on it. Nothing is claimed
about the continuum Yang–Mills operator, and the mass gap remains out of scope.
The Hashimoto/SIRK order-$`n` approximations supply the proved supporting facts —
the best-approximation error is antitone in the order and, for a cyclic seed,
tends to $`0` — while the identification of the limit with the Friedrichs
extension is recorded as a conjecture, not a theorem:
:::

```
#check @BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension
#check @BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded
#check @BookProof.YangMillsFriedrichs.friedrichs_hypothesis_satisfiable
#check @BookProof.YangMillsFriedrichs.weyl_friedrichs_extension
#check @BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_antitone
#check @BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_tendsto_zero
```

:::paragraph
In the *bounded* regime the named hypothesis is no longer needed: the positive
self-adjoint extension is constructed outright as the continuous extension of the
operator from its dense domain, and the construction applies to genuinely proper
dense domains (in $`\ell^2(\mathbb{N})` the span of the canonical basis is dense
but misses every vector of infinite support):
:::

```
#check @BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded
#check @BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_proper_domain_example
```

:::paragraph
In the same regime the Hashimoto/SIRK limit becomes an operator limit: the
order-$`n` compressions $`P_n A P_n` converge strongly to $`A` for any cyclic
seed, and no other bounded operator agrees with the limit on the Krylov flag, so
the infinite Hashimoto limit recovers exactly the positive self-adjoint extension
of the Weyl-gauge Hamiltonian. The unbounded continuum case remains open:
:::

```
#check @BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto
#check @BookProof.YangMillsFriedrichsLimit.sirk_limit_unique
#check @BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension
#check @BookProof.YangMillsFriedrichsLimit.weyl_friedrichs_bounded
```

:::paragraph
The same analysis can be run in the *Hermite (oscillator) basis* rather than
along a Krylov flag, and there it takes its classical Rayleigh–Ritz shape.
Truncating to the span of the first $`m` basis vectors replaces the Hamiltonian
by its compression $`P_m H P_m`, and on that subspace the compression carries
exactly the energy form of $`H`; the resulting Ritz values are antitone in $`m`
and converge to the infimum of the energy form over the whole finite-mode
domain. Neither statement needs a boundedness hypothesis:
:::

```
#check @BookProof.HermiteGalerkin.inner_galerkinCompression
#check @BookProof.HermiteGalerkin.ritzInf_antitone
#check @BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf
#check @BookProof.HermiteGalerkin.ritzInf_extension_le
#check @BookProof.HermiteGalerkin.exists_mem_galerkinSpan
#check @BookProof.HermiteGalerkin.galerkinProj_tendsto
```

:::paragraph
In the bounded regime the truncations converge in the strong *resolvent* sense —
$`(P_m A P_m - z)^{-1} \to (A - z)^{-1}` strongly at every non-real $`z` — and the
positive self-adjoint extension the algorithm converges to is the only one there
is, so no boundary condition has to be supplied to the algorithm. The finite-mode
domain is a proper dense subspace, so this is not the degenerate case of an
operator already defined everywhere. As everywhere above, the unbounded case is
not claimed:
:::

```
#check @BookProof.HermiteGalerkin.resolvent_tendsto_of_strong_tendsto
#check @BookProof.HermiteGalerkin.galerkinResolvent_tendsto
#check @BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique
#check @BookProof.HermiteGalerkin.hermiteGalerkin_selects_friedrichs
#check @BookProof.HermiteGalerkin.finiteModeDomain_ne_top
```

# Summary

The algebraic core of the manuscript's quantization programme:

 * the totally antisymmetric structure constants and the Jacobi identity of $`SU(3)`, realized by the Gell-Mann generators;
 * the field-strength and Bianchi identities for the covariant derivative;
 * quantization as arising from time-evolution via the Heisenberg/Weyl relations;
 * the nilpotent BRST charge (and the graded Jacobi identity of the super-bracket) defining the gauge-invariant algebra;
 * the positive-definite Weyl-gauge Hamiltonian;
 * the densely-defined Weyl-gauge Hamiltonian, its sum-of-squares quadratic form and the closability of that form — the Friedrichs route to a self-adjoint extension, with the Friedrichs theorem itself carried as a named hypothesis.

:::paragraph
The manuscript's Navier–Stokes existence/uniqueness thesis is deliberately *not*
carried by any theorem in this book. What *is* formalized is the finite subset of
the same programme that the free-field thread supports — the truncated
Navier–Stokes Hamiltonian with a complete, norm-preserving flow and a unique
global Cauchy solution, the nilpotent BRST divergence constraint, the Lagrangian
(volume-preservation) change of variables, and the Faris–Lavine commutator
criterion as the named-hypothesis route to essential self-adjointness. See the
section "The Navier–Stokes Hamiltonian: a Complete Flow on the Truncation" in
`Book/FreeField.lean`.
:::