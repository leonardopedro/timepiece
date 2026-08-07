import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Real Representations, the CPT Theorem and the Relativistic Position Operator" =>
%%%
tag := "real-representations"
%%%

# The Question

:::paragraph
The manuscript's chapter on real representations asks how Lorentz covariance and
quantum mechanics are compatible. It begins from two mutually compatible
formalisms: a theory invariant under diffeomorphisms (which includes Poincaré
invariance, with tetrad fields corresponding to a Minkowski space-time), and a
theory that only needs to be Poincaré invariant. Its central theses are that
*real* representations are fundamental, that the CPT theorem follows from the
most general Lorentz-covariant mass term, and that the relativistic position
operator is real exactly for spin-$`\tfrac12`. The verified content here captures
the algebraic spine of those claims.
:::

# The Lorentz Group and Its Discrete Subgroup

:::paragraph
The behaviour of symmetries is governed by the Lorentz group $`O(1,3)` of
matrices preserving the Minkowski metric $`\eta = \operatorname{diag}(1,-1,-1,-1)`.
Its key structural facts are that it is a group (closed under inverse), that every
element has determinant $`\pm 1`, and that it carries a discrete subgroup
$`\Delta = \{1, \eta, -\eta, -1\}` — the parity × time-reversal factor, a copy of
the Klein four-group:
:::

```
#check @BookProof.LorentzGroup.IsLorentz
#check @BookProof.LorentzGroup.isLorentz_inv
#check @BookProof.LorentzGroup.lorentz_det_sq_one
#check @BookProof.LorentzGroup.Delta
#check @BookProof.LorentzGroup.delta_card_four
```

:::paragraph
Inside $`O(1,3)` lives the proper orthochronous subgroup
$`SO^+(1,3) = \{\lambda : \det\lambda = 1,\ \lambda^0{}_0 > 0\}`, which is *normal*
in $`O(1,3)`, and every Lorentz matrix factors uniquely as $`\lambda = \delta s`
with $`\delta \in \Delta` and $`s \in SO^+(1,3)`:
:::

```
#check @BookProof.LorentzOrthochronous.IsProperOrthochronous
#check @BookProof.LorentzOrthochronous.isPO_conj
#check @BookProof.LorentzDecomp.lorentz_delta_decomp
#check @BookProof.LorentzDecomp.lorentz_delta_decomp_unique
```

# Real Representations of the Lorentz Group

:::paragraph
The manuscript's key structural claim is that the finite-dimensional
representations of $`SL(2,\mathbb{C})` are real, and that the Dirac/Majorana
algebra decomposes into a direct sum of real invariant subspaces. In the Clifford
algebra $`\operatorname{Mat}(4\times4,\mathbb{R})`, conjugation by the discrete Pin
subgroup $`\Omega` preserves four mutually orthogonal real subspaces — the
$`(1/2,1/2)` vector representation, the $`(1,0)` antisymmetric part, a
pseudo-real part, and a two-dimensional piece — which together span the whole
algebra as an internal direct sum:
:::

```
#check @BookProof.ChapterLorentzRealRep.WHalf_invariant
#check @BookProof.ChapterLorentzRealRepSum.gram_half10R
#check @BookProof.ChapterLorentzRealRepSum.finrank_WHalf
#check @BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add
#check @BookProof.ChapterLorentzRealRepDirect.WFam_isInternal
#check @BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant
```

:::paragraph
The headline $`16 = 4 + 6 + 4 + 2` (an internal direct sum, each summand
invariant under conjugation by the discrete Pin subgroup) is the algebraic content
of "real representations": the Clifford algebra splits into real invariant pieces,
each of which is the carrier of a real, and hence *real*, representation.
:::

# Pauli Matrices and the Double Cover

:::paragraph
The bridge from $`SL(2,\mathbb{C})` to the Lorentz group is the hermitian-matrix
parametrization of Minkowski 4-vectors, $`X = x_\mu \sigma^\mu` with
$`\det X = \langle x, x\rangle`. Spinor conjugation $`X \mapsto T^\dagger X T`
preserves the Minkowski form (so $`\Upsilon(T)` is Lorentz), and the map is
two-to-one — $`T` and $`-T` induce the same conjugation, which is the $`\pm 1`
kernel of the double cover; restricting to $`SU(2)` gives the $`SU(2) \to SO(3)`
double cover:
:::

```
#check @BookProof.ChapterPauliLorentz.hermMat
#check @BookProof.ChapterPauliLorentz.det_hermMat
#check @BookProof.ChapterPauliLorentz.spinorMap_preserves_mink
#check @BookProof.ChapterPauliSU2.spinorAction_neg
#check @BookProof.ChapterPauliSU2.su2_preserves_spatialNormSq
```

# The Poincaré Group and the Little Group

:::paragraph
Moving to the full Poincaré (inhomogeneous) group, the manuscript builds it as a
semidirect product of translations and the Lorentz group, and analyzes
representations by their *little group* — the stabilizer of a reference momentum.
The verified facts are the Poincaré semidirect product law, the little group as a
centralizer, and the $`SE(2)` translation subgroup that appears for the massless
lightlike case:
:::

```
#check @BookProof.ChapterIPin.IPin
#check @BookProof.ChapterIPin.ipin_right
#check @BookProof.ChapterIPin.ipin_left
#check @BookProof.ChapterLittleGroup.littleGroup
#check @BookProof.ChapterLittleGroup.prop79
#check @BookProof.ChapterSE2.Nmat_mul
#check @BookProof.ChapterSE2.NmatHom
```

# Majorana Spinors and the CPT Theorem

:::paragraph
The manuscript's CPT theorem falls out of the most general Lorentz-covariant Dirac
mass term $`iH = \partial\cdot\gamma\,\gamma^0 + i\gamma^0 m_1 +
\gamma^0\gamma^5 m_2`. The verified facts are: the Hamiltonian is self-adjoint,
its square is the relativistic mass shell $`D^2 = -(k^2 + m_1^2 + m_2^2)\cdot 1`,
the term $`m_2` is parity-odd (the sole source of CP violation), and the whole
operator is PT/CPT invariant. Setting $`m_2 = 0` recovers exact parity invariance:
:::

```
#check @BookProof.ChapterCPTHamiltonian.diracHamOp
#check @BookProof.ChapterCPTHamiltonian.diracHamOp_conjTranspose
#check @BookProof.ChapterCPTHamiltonian.diracHamOp_sq
#check @BookProof.ChapterCPTParity.parity_MassB
#check @BookProof.ChapterCPTParity.parity_diracHamOp
#check @BookProof.ChapterCPTParity.parity_diracHamOp_invariant
#check @BookProof.ChapterCPTPT.cpt_diracHamOp
```

:::paragraph
Majorana spinors make the real-rep thesis concrete: a field operator
$`a(v) = \iota Q v` generating a Clifford algebra is *self-adjoint*, so a particle
is its own antiparticle. The canonical anticommutation relation is
$`\{a(v), a(w)\} = 2\langle v,w\rangle\cdot 1`, and real symmetries preserve
self-adjointness:
:::

```
#check @BookProof.MajoranaClifford.a
#check @BookProof.MajoranaClifford.a_sq
#check @BookProof.MajoranaClifford.car
#check @BookProof.MajoranaClifford.a_selfAdjoint
#check @BookProof.MajoranaClifford.a_map_selfAdjoint
```

:::paragraph
The manuscript also develops the Majorana–Fourier machinery: the unitary boost
blocks, the energy–momentum transform, and the intertwining of the Dirac operator
with the inverse boost. Each is verified as a unitarity or intertwining statement:
:::

```
#check @BookProof.ChapterMajoranaFourier.majoranaFourier_boostBlock_unitary
#check @BookProof.ChapterMajoranaProp61.prop61_isUnit
#check @BookProof.ChapterMajoranaProp74.prop74_intertwine
#check @BookProof.ChapterMajoranaProp76.energyMomentum_unitary
#check @BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary
```

# The Relativistic Position Operator

:::paragraph
The manuscript's corollary is that a localizable representation of the Poincaré
group is irreducible iff it is real and massive spin-$`\tfrac12` (or massless
helicity-$`\tfrac12`), in which case the position operator matches the coordinates
of the Dirac equation. The verified algebraic fact underpinning the obstruction is
that the time-component generator $`i\gamma^0` does *not* commute with the spatial
generators $`(i\gamma^i)(i\gamma^0)`, while it *does* commute with the rotation
generators $`(i\gamma^i)(i\gamma^j)` (consistent with the massive little group
$`SU(2)`):
:::

```
#check @BookProof.ChapterLocalization.gamma0_not_comm_spatial
#check @BookProof.ChapterLocalization.comm_gamma0_rotation
```

:::paragraph
This is the load-bearing algebraic fact behind the claim that no closed position
operator exists for the complex/spin-1 case while one does for the real spin-$`\tfrac12`
case: the obstructed generators are precisely those that fail to commute with the
time generator.
:::

# The Bosonic CCR

:::paragraph
For completeness, the manuscript's quantization section records the bosonic
canonical commutation relations that replace the fermionic anticommutators. The
verified content is that the CCR $`[a(v),a(w)] = (i\langle v, Jw\rangle)\cdot 1`
is symplectically invariant, that the number-operator relation
$`[cre, ann] = (2\|v\|^2)\cdot 1` holds, and that the involution swaps
annihilation and creation:
:::

```
#check @BookProof.Bosonic.BosonicCCR
#check @BookProof.Bosonic.ccr_symplectic_invariant
#check @BookProof.Bosonic.commutator_cre_ann
#check @BookProof.Bosonic.star_ann
```

# Summary

The relativistic structure of the manuscript, in its verified form:

 * the Lorentz group $`O(1,3)` with discrete subgroup $`\Delta \cong \mathbb{Z}_2\times\mathbb{Z}_2`, and $`O(1,3) = \Delta \ltimes SO^+(1,3)`;
 * real representations: the Clifford algebra splits as an internal direct sum of real invariant subspaces, $`16 = 4+6+4+2`;
 * the hermitian-matrix/double-cover bridge $`SL(2,\mathbb{C}) \to O(1,3)` and $`SU(2) \to SO(3)`;
 * the Poincaré semidirect product and its little groups (including $`SE(2)`);
 * the CPT theorem from the most general covariant mass term, with $`m_2` the parity-breaking parameter;
 * Majorana self-adjointness (particle = its own antiparticle) and the unitary Majorana–Fourier transforms;
 * the position-operator obstruction: the time generator fails to commute with spatial generators.