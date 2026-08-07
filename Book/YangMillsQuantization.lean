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

# Summary

The algebraic core of the manuscript's quantization programme:

 * the totally antisymmetric structure constants and the Jacobi identity of $`SU(3)`, realized by the Gell-Mann generators;
 * the field-strength and Bianchi identities for the covariant derivative;
 * quantization as arising from time-evolution via the Heisenberg/Weyl relations;
 * the nilpotent BRST charge (and the graded Jacobi identity of the super-bracket) defining the gauge-invariant algebra;
 * the positive-definite Weyl-gauge Hamiltonian.