import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Physical Parity Transformation and Antiparticles" =>
%%%
tag := "physical-parity"
%%%

# The Question

:::paragraph
The manuscript's chapter on the physical parity transformation develops the old
observation that there is a basis where CP becomes a parity transformation, and
that Majorana spinors (and the Majorana basis) make the real-rep structure
explicit. Its central claims are: at the quantum level all fields are self-adjoint
operators hence *real* representations — every particle is its own antiparticle;
in a Majorana basis CP and P both become (order-4) parity transformations; and the
Standard Model can be rebuilt with Majorana fermions where parity is broken only
by the CKM matrix, forcing the double cover $`\operatorname{Pin}(3,1)`. The
verified content here is the algebraic structure of that programme.
:::

# The Order-Four Parity Transformation and the Double Cover

:::paragraph
The manuscript's key technical claim is that the physical parity transformation
has *order four* — not order two — and that this selects the double cover
$`\operatorname{Pin}(3,1)` (where $`\gamma^0` squares to $`-1`) over
$`\operatorname{Pin}(1,3)` (where it squares to $`+1`). The Higgs parity $`i\sigma_2`
and the fermion parity $`i\gamma^0` both have order exactly four:
:::

```
#check @BookProof.ChapterParity.higgsParity_order_four
#check @BookProof.ChapterParity.fermionParity_order_four
#check @BookProof.ChapterParity.dgamma0_sq
```

:::paragraph
At the level of the discrete subgroup, the quaternion generators
$`i\gamma^0, \gamma^0\gamma^5, i\gamma^5` satisfy $`i^2 = j^2 = k^2 = -1`,
$`ij = k`, and generate the 8-element nonabelian group $`\Omega \cong Q_8`. The
covering map $`\Lambda : \Omega \to \Delta` is a homomorphism that is *two-to-one*
— $`\Omega` is the double cover of the discrete parity × time-reversal group:
:::

```
#check @BookProof.ChapterPinOmega.Omega
#check @BookProof.ChapterPinOmega.Omega_card
#check @BookProof.ChapterPinOmega.Omega_mul_closed
#check @BookProof.ChapterPinOmega.noncomm
#check @BookProof.ChapterPinDoubleCover.LamZ_surjective
#check @BookProof.ChapterPinDoubleCover.LamZ_hom
#check @BookProof.ChapterPinDoubleCover.LamZ_fiber_card
```

:::paragraph
The order-four parity acting simultaneously on the whole Standard-Model matter
content generates the $`\mathbb{Z}_4` background-symmetry factor:
:::

```
#check @BookProof.ChapterParityZ4.combinedParity
#check @BookProof.ChapterParityZ4.combinedParity_order_four
#check @BookProof.ChapterParityZ4.combinedParity_orderOf
#check @BookProof.ChapterParityQL.QLParity_order_four
```

# Every Particle Is Its Own Antiparticle

:::paragraph
The manuscript's Majorana claim — that at the quantum level fields are real
representations, so a particle is its own antiparticle — is captured by the
self-adjointness of the Clifford field operators. A field operator
$`a(v) = \iota Q v` generating the Clifford algebra of a real Hilbert space is
explicitly self-adjoint and satisfies the canonical anticommutation relation:
:::

```
#check @BookProof.MajoranaClifford.a
#check @BookProof.MajoranaClifford.a_sq
#check @BookProof.MajoranaClifford.a_selfAdjoint
#check @BookProof.MajoranaClifford.car
#check @BookProof.MajoranaClifford.a_map_selfAdjoint
```

:::paragraph
The reality structure is made precise by the Higgs bidoublet: complex conjugation
on a single $`SU(2)` doublet is pseudoreal ($`\sigma_2\sigma_2^* = -1`), while
*pseudoreal ⊗ pseudoreal = real*, so the Higgs bidoublet $`(\tau_2 \otimes \sigma_2)`
carries a genuine real structure — the Higgs is a real representation:
:::

```
#check @BookProof.ChapterParityHiggs.pauli2_pseudoreal
#check @BookProof.ChapterParityHiggs.pseudoreal_kron_pseudoreal_real
#check @BookProof.ChapterParityHiggs.higgs_real_structure
#check @BookProof.ChapterParitySU2.su2_conj_inner
```

# CP and the Parity-Breaking Term

:::paragraph
The manuscript traces parity (CP) violation to a single algebraic source. In the
most general Lorentz-covariant Dirac mass term
$`iH = \partial\cdot\gamma\gamma^0 + i\gamma^0 m_1 + \gamma^0\gamma^5 m_2`, the
term $`m_2` (the $`\gamma^0\gamma^5` part) is *parity-odd*, while the $`m_1` term
is parity-even. Setting $`m_2 = 0` recovers exact parity invariance; a nonzero
$`m_2` is the sole source of CP violation:
:::

```
#check @BookProof.ChapterCPTParity.parity_Kin
#check @BookProof.ChapterCPTParity.parity_MassA
#check @BookProof.ChapterCPTParity.parity_MassB
#check @BookProof.ChapterCPTParity.parity_diracHamOp
#check @BookProof.ChapterCPTParity.parity_diracHamOp_invariant
```

:::paragraph
The manuscript connects this to the structure of $`SU(3)`: complex conjugation on
the Gell-Mann generators is a *nontrivial* $`\mathbb{Z}_2` outer automorphism
(realized by the sign pattern that negates $`\lambda^2`), which is the algebraic
seed of CP violation in the quark sector:
:::

```
#check @BookProof.ChapterParitySU3.gellMann_conj_involutive
#check @BookProof.ChapterParitySU3.gellMann_bracket_conj
#check @BookProof.ChapterParitySU3.gellMann_conj_nontrivial
#check @BookProof.ChapterParity.gellMann_conj
```

# Chiral Structure and the Quark-Doublet Parity

:::paragraph
The manuscript rebuilds the electroweak sector with a definite chirality. The
chirality operator $`\chi = (i\sigma_3)\otimes(i\gamma^5)` is an involution
($`\chi^2 = 1`) with trace zero (equal eigenspaces, "divide by 2"), and the
projector $`P = \tfrac12(1-\chi)` selects the left-handed states:
:::

```
#check @BookProof.ChapterParityChirality.chi
#check @BookProof.ChapterParityChirality.chi_sq
#check @BookProof.ChapterParityChirality.chi_trace
#check @BookProof.ChapterParityChirality.QLProj
#check @BookProof.ChapterParityChirality.chirality_iff
```

:::paragraph
The hypercharge phase group is realized with the *real* matrix $`i\gamma^5` in
place of the imaginary unit: $`U(1)_Y` becomes $`e^{\vartheta i\gamma^5} =
\cos\vartheta\cdot 1 + \sin\vartheta\cdot i\gamma^5`, which is a genuine abelian
group:
:::

```
#check @BookProof.ChapterParityHypercharge.mgamma5_real
#check @BookProof.ChapterParityHypercharge.hyperPhase_add
#check @BookProof.ChapterParityHypercharge.hyperPhase_neg_mul
```

# Majorana Quantization

:::paragraph
The manuscript's Majorana quantization uses a compatible complex structure $`J`
(with $`(iJ)^2 = 1`) to split the real Hilbert space into annihilation and
creation directions via the projections $`\tfrac12(1 \pm iJ)`. The verified facts
are that $`J` is unitary, the projections are orthogonal and span the identity,
and annihilation combinations lie in the $`-i`-eigenspace:
:::

```
#check @BookProof.ChapterParityMajoranaQuant.J_unitary
#check @BookProof.ChapterParityMajoranaQuant.annihProj
#check @BookProof.ChapterParityMajoranaQuant.proj_add
#check @BookProof.ChapterParityMajoranaQuant.J_annih
#check @BookProof.ChapterParityMajoranaQuant.stdJ
```

# The Custodial Symmetry

:::paragraph
The custodial $`SU(2)` structure is governed by Schur's lemma: any matrix
commuting with all of $`\sigma_1,\sigma_2,\sigma_3` is scalar, and
$`\{1,\sigma_1,\sigma_2,\sigma_3\}` are linearly independent — the 
four-dimensional custodial commutant:
:::

```
#check @BookProof.ChapterParityCustodial.commutant_pauli_scalar
#check @BookProof.ChapterParityCustodial.pauli_basis_indep
```

:::paragraph
This commutant statement is a special case of a general irreducibility theorem. On
a nonzero *finite-dimensional* complex space, an operator commuting with an
*irreducible* system of operators is necessarily a scalar: over $`\mathbb{C}` the
commuting operator has an eigenvalue, its eigenspace is invariant under the system
and hence — by irreducibility — everything, so the operator acts as that scalar.
This is Schur's lemma, and discharging it in finite dimensions turns the book's
`IsSchurUnitary` hypothesis into a theorem:
:::

```
#check @BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible
#check @BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible
```

:::paragraph
For the concrete $`4\times 4` Majorana model of the manuscript, Pauli's fundamental
theorem is itself a finite computation, not an external input: the commutant of the
four matrices $`i\gamma^\mu` is exactly the set of scalar matrices — the
representation is irreducible. The proof is elementary: two diagonal elements of the
gamma algebra separate the four basis vectors, forcing a commuting matrix to be
diagonal, and the off-diagonal gammas then identify all four diagonal entries:
:::

```
#check @BookProof.ChapterGammaCommutant.gamma_commutant_scalar
#check @BookProof.ChapterGammaCommutant.gamma_commutant_eq_scalars
#check @BookProof.ChapterGammaCommutant.gamma_intertwiner_unique
```

# Summary

The algebraic core of the manuscript's parity/antiparticles chapter:

 * the physical parity is an order-four transformation, selecting the double cover $`\operatorname{Pin}(3,1)`;
 * the discrete Pin subgroup $`\Omega \cong Q_8` double-covers $`\Delta`;
 * Majorana self-adjointness: every particle is its own antiparticle, and the Higgs is a real representation;
 * CP violation traced to the parity-odd $`m_2` term and the nontrivial $`SU(3)` conjugation automorphism;
 * the chiral structure and the real-matrix hypercharge phase group;
 * Majorana quantization by a compatible complex structure.