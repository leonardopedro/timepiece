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
The Friedrichs theorem itself was first carried as a *named hypothesis*
(Friedrichs 1934; Reed–Simon Thm X.23), never as an axiom, and shown to be
satisfiable; the conclusion for the Weyl-gauge Hamiltonian was conditional on it.
That hypothesis is now *discharged outright* — see the section "The Friedrichs
Extension Without a Boundedness Hypothesis" below — so the statements in this
block are the conditional forms that the unconditional theorem supersedes. Nothing is claimed
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

# The Friedrichs Extension Without a Boundedness Hypothesis

:::paragraph
The two constructions above build the positive self-adjoint extension only in the
*bounded* regime. The general theorem needs no boundedness at all, and it is
proved here. The domain is retyped with the form inner product
$`\langle x,y\rangle_1 = \langle x,y\rangle + \langle x, Hy\rangle`; symmetry makes
it Hermitian and positivity makes it positive definite, so the domain becomes an
inner product space whose completion is a Hilbert space. Its inclusion into the
ambient space is norm-decreasing, so it extends continuously, and the key identity
$`\langle x, k\rangle_1 = \langle x + Hx, \iota k\rangle` — closability of the form
in disguise — shows that extension is *injective*: the form completion adds no
ghost vectors.
:::

```
#check @BookProof.FriedrichsExtension.PosSymOp
#check @BookProof.FriedrichsExtension.FormDom.norm_toAmbient_le
#check @BookProof.FriedrichsExtension.FormDom.inner_coe_eq
#check @BookProof.FriedrichsExtension.FormDom.formExt_injective
```

:::paragraph
Riesz representation in the form space then produces the resolvent
$`S = (H+1)^{-1}` as a bounded, injective, positive, self-adjoint operator of norm
at most one which sends $`x + Hx` back to $`x`, and the project's own
shift-invert converse turns $`S` into the extension $`A = S^{-1} - 1`. The result
is the Friedrichs extension theorem as a *theorem*: every densely defined,
symmetric, positive operator on a complex Hilbert space has a positive
self-adjoint extension — in particular the Weyl-gauge Yang–Mills Hamiltonian, with
no boundedness of the electric or magnetic field operators assumed:
:::

```
#check @BookProof.FriedrichsExtension.FormDom.friedrichsResolvent
#check @BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_shift
#check @BookProof.FriedrichsExtension.friedrichs_extension_exists
#check @BookProof.FriedrichsExtension.friedrichs_hypothesis_holds
#check @BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional
#check @BookProof.FriedrichsExtension.friedrichs_extension_of_semibounded_below
```

:::paragraph
The last statement is the classical form of the theorem: symmetry plus a lower
bound $`\langle x, Hx\rangle \ge -c\|x\|^2` — positivity is not needed — gives a
self-adjoint extension with the same lower bound, by the shift $`H \mapsto H + c`.
:::

:::paragraph
Combining the construction with the shift-invert theory closes the loop for the
unbounded case: in the occupation-number (Hermite) realization the extension
*exists*, its shift-invert $`R = (A+\gamma)^{-1}` is bounded and self-adjoint, the
Galerkin truncations of $`R` converge to it strongly and in the resolvent sense,
and $`R` determines $`A` — so the infinite Hashimoto/SIRK limit selects exactly
the constructed extension. The construction is not vacuous: it applies to the
genuinely unbounded diagonal operator $`A e_n = n e_n` on $`\ell^2(\mathbb{N})`.
What stays outside is, as always, the mass gap:
:::

```
#check @BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
#check @BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs
#check @BookProof.FriedrichsExtension.unbounded_friedrichs_example
```

# The Field-Space Realization on the Product Hermite Core

:::paragraph
The statements above are formulated for abstract electric and magnetic operators
on the finite-mode domain of an orthonormal basis. The field-space realization
makes them concrete on $`L^2(\mathbb{R}^{99})`, the configuration space with
$`99 = 3 + 24 + 72` coordinates: three spatial coordinates, the $`24 = 3\times 8`
gauge fields $`A_{j,a}` and the $`72 = 3\times3\times8` independent derivative
coordinates $`\partial_j A_{k,a}`. The core is the span of the *product Hermite
functions* — equivalently, of all $`p(x)\,e^{-\|x\|^2/4}` with $`p` a polynomial,
since the products $`\prod_i He_{\alpha_i}(x_i)` of probabilists' Hermite
polynomials span the whole polynomial ring. The map
$`p \mapsto p\,e^{-\|x\|^2/4}` is injective, the core is dense, and Gram–Schmidt
turns the enumerated monomials into an orthonormal basis whose finite-mode domain
is exactly the core:
:::

```
#check @BookProof.HermiteProductCore.pgMap_injective
#check @BookProof.HermiteProductCore.polyGaussCore_dense
#check @BookProof.HermiteProductCore.gaussInt_pderiv
#check @BookProof.HermiteProductCore.hermiteMv
#check @BookProof.HermiteProductCore.polyGaussCore_eq_hermiteSpan
#check @BookProof.HermiteProductCore.coreBasis
#check @BookProof.HermiteProductCore.span_range_coreBasis
```

:::paragraph
On that core the fields act as genuine operators: multiplication by the
coordinate $`A_{j,a}`, the momentum $`\pi = -i\,\partial/\partial A` (symmetric
by Gaussian integration by parts), and the magnetic field
$`B_{ia} = \varepsilon_{ijk}(\partial_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})`, which
is multiplication by a polynomial with *real* coefficients and hence symmetric.
The coordinate and momentum operators do not commute — $`[A_j, \pi_j] = i` — so
products of them are Weyl ordered as $`\tfrac12(PQ+QP)`, and the Weyl-ordered
product of two symmetric operators is symmetric:
:::

```
#check @BookProof.YangMillsHermite.mulOp_polySym
#check @BookProof.YangMillsHermite.momOp_polySym
#check @BookProof.YangMillsHermite.commutator_coord_mom
#check @BookProof.YangMillsHermite.weylProd_polySym
#check @BookProof.YangMillsHermite.magPoly
#check @BookProof.YangMillsHermite.realCoeff_magPoly
```

:::paragraph
The Hamiltonian is taken in the *positive* sum-of-squares convention
$`H_1 = \tfrac12\sum \pi^2 + \tfrac12\sum B^2` (the manuscript writes
$`-\tfrac12\pi\pi - \tfrac12 BB`; the positive sign is the one bounded below, to
which the Friedrichs machinery applies). It is well defined, symmetric and
positive on the core, its quadratic form is a sum of squares, and therefore the
Friedrichs extension theorem and the Hashimoto/SIRK selection theorem apply to
the concrete field-space operator:
:::

```
#check @BookProof.YangMillsHermite.ymHamiltonian
#check @BookProof.YangMillsHermite.ymHamiltonian_quadForm
#check @BookProof.YangMillsHermite.ymHamiltonian_symmetricOn
#check @BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg
#check @BookProof.YangMillsHermite.ym_hermite_friedrichs_extension
#check @BookProof.YangMillsHermite.ym_hermite_hashimoto_selects
```

:::paragraph
Finally the one-particle Hamiltonian is *second quantized* on the
finite-occupation states over the core. The Fock space is $`\ell^2` over the
configurations $`\mathbb{N} \to_0 \mathbb{N}` (occupation numbers, finitely many
modes excited); the ladder operators satisfy $`[a_j, a_j^\dagger] = 1` and the
adjoint pairing $`\langle a_j^\dagger u, v\rangle = \langle u, a_j v\rangle`,
and $`d\Gamma(A) = \sum_{j,k} \langle e_j, A e_k\rangle a_j^\dagger a_k`
restricts on the one-particle sector to $`A` itself. Hermiticity and positivity
of the one-particle matrix make $`d\Gamma(A)` symmetric and positive on the
dense finite-occupation domain, so it too has a positive self-adjoint
(Friedrichs) extension — in particular for the field-space Yang–Mills
$`H_1 = \tfrac12\sum \pi^2 + \tfrac12\sum B^2`:
:::

```
#check @BookProof.FockSecondQuantization.ccr_annA_creA
#check @BookProof.FockSecondQuantization.inner_creA_left
#check @BookProof.FockSecondQuantization.dGamma
#check @BookProof.FockSecondQuantization.dGamma_one_particle
#check @BookProof.FockSecondQuantization.dGammaOp_symmetricOn
#check @BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
#check @BookProof.FockSecondQuantization.secondQuantization_friedrichs
#check @BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
#check @BookProof.FockSecondQuantization.finiteModeDomain_fockBasisN
#check @BookProof.FockSecondQuantization.dGamma_hashimoto_selects
#check @BookProof.FockSecondQuantization.secondQuantization_hashimoto_selects
#check @BookProof.FockSecondQuantization.ym_fock_hashimoto_selects
```

:::paragraph
No mass gap and no global existence statement is claimed anywhere in this
section.
:::

# Summary

The algebraic core of the manuscript's quantization programme:

 * the totally antisymmetric structure constants and the Jacobi identity of $`SU(3)`, realized by the Gell-Mann generators;
 * the field-strength and Bianchi identities for the covariant derivative;
 * quantization as arising from time-evolution via the Heisenberg/Weyl relations;
 * the nilpotent BRST charge (and the graded Jacobi identity of the super-bracket) defining the gauge-invariant algebra;
 * the positive-definite Weyl-gauge Hamiltonian;
 * the densely-defined Weyl-gauge Hamiltonian, its sum-of-squares quadratic form and the closability of that form — the Friedrichs route to a self-adjoint extension;
 * the Friedrichs extension theorem itself, proved with no boundedness hypothesis, and the resulting unbounded statement: the Weyl-gauge Hamiltonian has a positive self-adjoint extension and the infinite Hashimoto/SIRK limit selects exactly that extension;
 * the field-space realization of that Hamiltonian on the dense product Hermite
   core of $`L^2(\mathbb{R}^{99})`, with the coordinate, momentum and
   magnetic-field operators defined concretely, the canonical commutation
   relation and the Weyl ordering it forces, and the Friedrichs/Hashimoto
   theorems instantiated by it.

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