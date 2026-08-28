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
The new gap-proof layer makes the logical order precise. `ChapterRitzCertificate.lean` turns a finite Ritz value and residual into a spectral band using Temple's inequality, but only with a separation hypothesis. `ChapterTempleSeparationNecessary.lean` proves that this hypothesis cannot be removed: Rayleigh data and residuals alone do not control an unseen lower eigenvalue. `ChapterBandEnclosure.lean` and `ChapterFockOneParticleGap.lean` then state the conditional bridge from compatible finite bands to the one-particle edge.
:::

:::paragraph
For the mass-gap route, distinguish the real one-particle Hamiltonian from its finite
certificate and from the outer-particle Fock lift. The positivity below is the input for
shifting the one-particle operator and applying the Friedrichs/Hashimoto construction;
it is not, by itself, a statement that a finite numerical gap has already transferred to
the full Hamiltonian.
:::

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
`BookProof/ChapterFriedrichsFormGap.lean` supplies the form-theoretic part of this route. The claim is that a semibounded symmetric quadratic form determines a positive Friedrichs extension and that the finite form restrictions preserve the variational information needed for a gap. The proof uses closability, form-domain inclusion, and the variational characterization; it does not identify a continuum gap without a separate convergence theorem.
:::

:::paragraph
Because the one-particle Hamiltonian is bounded below, choose an energy origin so that
`h₊ ≥ μ I` for some `μ > 0`. For free outer particles this changes the Fock Hamiltonian
by `μ N`, not by a vacuum constant: `N Ω = 0`, while every non-vacuum finite-particle
energy is a sum of strictly positive one-particle energies. Thus the physical observable
for the remaining mass-gap theorem is the lowest positive one-particle energy, measured
through the creation/destruction sandwich and then lifted by `dGamma`.
:::


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
The perturbative boundary is now explicit in `ChapterFockFieldPerturbation.lean` and `ChapterFockInteractionStability.lean`. The first develops the field-level form estimates needed to compare a reference Fock Hamiltonian with a perturbation. The second proves that a relative form bound degrades a positive edge by a controlled amount, and gives the bounded-interaction corollary. Pair creation is allowed by the abstract bounded theorem, but the physical unbounded interaction still needs its own form estimate.
:::

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
Finally the one-particle Hamiltonian is *enclosed and second quantized* on the
outer finite-occupation states over the inner core. This is the final-Hamiltonian
convention for QYM, QED, QG, and NS: retain the complete inner `h` (including
inner pair terms), and write the outer operator with creation on the left and
annihilation on the right. The Fock space is $`\ell^2` over the
configurations $`\mathbb{N} \to_0 \mathbb{N}` (occupation numbers, finitely many
modes excited); the ladder operators satisfy $`[a_j, a_j^\dagger] = 1` and the
adjoint pairing $`\langle a_j^\dagger u, v\rangle = \langle u, a_j v\rangle`,
and $`d\Gamma(A) = \sum_{j,k} \langle e_j, A e_k\rangle C_j^\dagger A_k`
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
The manuscript's Hilbert space is not the symmetric Fock space alone but the
*graded* tensor product $`\Gamma^s \otimes \Gamma^a` of a symmetric (bosonic)
and an antisymmetric (fermionic, ghost) factor, on which the creation and
annihilation operators form a graded Lie superalgebra. The antisymmetric factor
is built in `BookProof.FermionFock`: a fermionic configuration *is* its finite
set of occupied modes (so the Pauli principle is part of the type), the
Jordan–Wigner sign $`(-1)^{\#\{i \in S : i < j\}}` gives the creation and
annihilation operators, and they satisfy all four canonical *anti*commutation
relations, are formal adjoints of each other, and second quantize exactly as in
the bosonic case — with the same Friedrichs extension and Hashimoto/SIRK
selection theorems. The abstract ghost relations `GhostCAR` assumed by the BRST
chapter are realized by these operators, so the nilpotency $`Q^2 = 0` holds for
a concrete operator algebra:
:::

```
#check @BookProof.FermionFock.car_annF_creF_self
#check @BookProof.FermionFock.creF_creF_self
#check @BookProof.FermionFock.car_annF_annF
#check @BookProof.FermionFock.car_annF_creF_of_ne
#check @BookProof.FermionFock.inner_creF_left
#check @BookProof.FermionFock.dGammaF_one_particle
#check @BookProof.FermionFock.dGammaF_friedrichs_extension
#check @BookProof.FermionFock.secondQuantizationF_friedrichs
#check @BookProof.FermionFock.dGammaF_hashimoto_selects
#check @BookProof.FermionFock.parityF_involutive
#check @BookProof.FermionFock.ghostCAR_creF_annF
#check @BookProof.FermionFock.brst_charge_nilpotent_fermiFock
```

:::paragraph
Putting the two factors together, `BookProof.GradedFock` realizes the graded
Fock space as $`\ell^2` over the pairs (bosonic configuration, fermionic
occupied set), lifts the operators of either factor to it — operators on
different factors commute — and proves the manuscript's *single unified graded
relation*: with the Koszul sign $`\varepsilon(p,q) = (-1)^{pq}` of the
super-bracket, $`⟦a(p,j), a^\dagger(q,k)⟧ = \delta_{pq}\delta_{jk}`, which is
the bosonic *commutator* CCR when both operators are even, the fermionic
*anticommutator* CAR when both are odd, and $`0` across the two sectors. The
fermion-number parity $`(-1)^{N_f}` is the $`\mathbb{Z}_2` grading operator: an
involution that commutes with the bosonic operators, anticommutes with the
fermionic ones, and splits the graded Fock space into its even and odd parts:
:::

```
#check @BookProof.GradedFock.liftFst_liftSnd_comm
#check @BookProof.GradedFock.super_canonical
#check @BookProof.GradedFock.super_canonical_cre
#check @BookProof.GradedFock.super_canonical_ann
#check @BookProof.GradedFock.gradeOp_involutive
#check @BookProof.GradedFock.gradeOp_bcre
#check @BookProof.GradedFock.gradeOp_fcre
#check @BookProof.GradedFock.even_add_odd
#check @BookProof.GradedFock.gradeOp_evenPart
#check @BookProof.GradedFock.gradeOp_oddPart
```

:::paragraph
The analytic half of that construction lives on the graded space itself, not
factorwise. `BookProof.GradedFriedrichs` shows that the total graded Hamiltonian
$`d\Gamma^s(A) \otimes 1 + 1 \otimes d\Gamma^a(B)` is densely defined, symmetric
and positive on $`\ell^2(\mathrm{Conf} \times \mathrm{FConf})` and therefore has
a positive self-adjoint (Friedrichs) extension, and
`BookProof.GradedHashimoto` adds the two structural facts the two factors
already had: the Hamiltonian is an *even* operator — it commutes with the
$`\mathbb{Z}_2` grading $`(-1)^{N_f}` and so preserves the even and the odd
subspace — and the Hashimoto/SIRK shift-invert limit selects exactly its
Friedrichs extension, with the Galerkin truncations converging strongly and in
the resolvent sense. The total number operator $`N_b \otimes 1 + 1 \otimes N_f`
is a concrete instance, so neither statement is vacuous.
:::

```
#check @BookProof.GradedFriedrichs.gradedHamiltonian_friedrichs_extension
#check @BookProof.GradedFriedrichs.gradedSecondQuantization_friedrichs
#check @BookProof.GradedFriedrichs.gradedNumber_one_particle
#check @BookProof.GradedHashimoto.gradedHamiltonianAlg_otimes
#check @BookProof.GradedHashimoto.gradeOp_gradedHamiltonianAlg
#check @BookProof.GradedHashimoto.gradedHamiltonianAlg_evenPart
#check @BookProof.GradedHashimoto.gradedHamiltonianAlg_oddPart
#check @BookProof.GradedHashimoto.graded_hashimoto_selects
#check @BookProof.GradedHashimoto.gradedSecondQuantization_hashimoto_selects
#check @BookProof.GradedHashimoto.gradedNumber_hashimoto_selects
#check @BookProof.GradedHashimoto.graded_stone_flow
#check @BookProof.GradedHashimoto.gradedNumber_stone_flow
```

:::paragraph
Each of these positive self-adjoint extensions now yields a *complete unitary
flow*. `BookProof.ChapterStoneBridge` packages the passage from a selected
self-adjoint extension to the one-parameter group Stone's theorem guarantees as
the `IsStoneFlow` structure ($`U 0 = 1`, the group law, isometry of each $`U t`,
and the Schrödinger equation on the domain), and
`BookProof.ChapterStoneFlows` applies it to the concrete Fock Hamiltonian: the
second-quantized Yang–Mills generator $`d\Gamma(\tfrac12\sum\pi^2 +
\tfrac12\sum B^2)` on the finite-occupation domain over the product Hermite core
has the complete unitary flow `ym_fock_stone_flow` — global in $`t`, unitary,
and agreeing with the Schrödinger evolution on the domain. This is the precise
formal content of the manuscript's "wave-function evolution" of the gauge field
configuration: the Fock representation is unitary, hence probability-conserving,
at every instant.
:::

```
#check @BookProof.StoneFlows.ym_fock_stone_flow
```

:::paragraph
No continuum mass gap and no global existence statement is claimed anywhere in this
section. The full nested-Fock ground-state statement is structural: once the
sector one-particle operator is shifted positive and enclosed as
$`H=\\sum_{i,j}h_{ij}C_i^\\dagger A_j`, the outer vacuum is exactly the ground;
what remains analytic is the identification and convergence of the positive
one-particle edge.
:::

# Summary

:::paragraph
The complete proof architecture is therefore: establish the one-particle edge under explicit spectral or Friedrichs hypotheses; enclose finite SIRK/Ritz data with Temple separation; prove stability of the finite bands; lift the positive one-particle operator with `dGamma`; and, only then, address unbounded interactions by form methods. `ChapterFockNumberPreservingGap.lean` proves the free number-preserving lift for arbitrary one-particle Hamiltonians, while `ChapterFockInteractionStability.lean` gives the quantitative bounded/form-bounded extension. `ChapterSpectralGapStability.lean` handles operator-norm perturbation and limits. `ChapterRoadmapAudit.lean` records the audited dependencies. The remaining Lean4-specialist work is to instantiate these abstractions for the concrete 3D gauge-fixed QYM operator and prove the required convergence and separation hypotheses.
:::

The algebraic core of the manuscript's quantization programme:

 * the totally antisymmetric structure constants and the Jacobi identity of $`SU(3)`, realized by the Gell-Mann generators;
 * the field-strength and Bianchi identities for the covariant derivative;
 * quantization as arising from time-evolution via the Heisenberg/Weyl relations;
 * the nilpotent BRST charge (and the graded Jacobi identity of the super-bracket) defining the gauge-invariant algebra;
 * the positive-definite Weyl-gauge Hamiltonian;
 * the densely-defined Weyl-gauge Hamiltonian, its sum-of-squares quadratic form and the closability of that form — the Friedrichs route to a self-adjoint extension;
 * the Friedrichs extension theorem itself, proved with no boundedness hypothesis, and the resulting unbounded statement: the Weyl-gauge Hamiltonian has a positive self-adjoint extension and the infinite Hashimoto/SIRK limit selects exactly that extension;
*  the field-space realization of that Hamiltonian on the dense product Hermite
   core of $`L^2(\mathbb{R}^{99})`, with the coordinate, momentum and
   magnetic-field operators defined concretely, the canonical commutation
   relation and the Weyl ordering it forces, and the Friedrichs/Hashimoto
   theorems instantiated by it;
 *  the fermionic (CAR) factor $`\Gamma^a` with its own Friedrichs and
   Hashimoto theorems, the concrete realization of the BRST ghost relations, and
   the graded Fock space $`\Gamma^s \otimes \Gamma^a` on which one Koszul-signed
   formula (`super_canonical`) yields the bosonic CCR, the fermionic CAR and the
   vanishing mixed brackets at once, together with the $`\mathbb{Z}_2` grading;
 *  the second-quantized Fock form of the same Hamiltonian and its complete
   unitary flow `ym_fock_stone_flow` — the Stone bridge turning each positive
   self-adjoint extension into a global, norm-preserving Schrödinger evolution.

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