import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Standard Model Hamiltonian" => %%%
tag := "standard-model"
%%%

The Yang–Mills chapter quantized a single non-abelian gauge field; this chapter
puts the whole bosonic content of the Standard Model into the same frame. The
setting is the temporal (Weyl) gauge $`A_0 = W_0 = B_0 = 0`, the state space is
the nested Fock space of excitations, and the Hamiltonian of record is — as
everywhere in this development — the *outer second quantization* $`d\Gamma(h)` of
a one-particle operator $`h`, never the bare $`h`.

Proof chapters carry the content, in four generations of work. The first four
set the frame: `BookProof/ChapterSmOneParticle.lean` (the collective
coordinates and the mixing algebra), `BookProof/ChapterSmHamiltonian.lean` (the
one-particle operator), `BookProof/ChapterSmComparison.lean` (the comparison
operator of the Faris–Lavine route) and `BookProof/ChapterSmOuterFock.lean` (the
enclosure). The second generation completes the fermions:
`BookProof/ChapterSmCarAlgebra.lean` (the CAR algebra over a finite mode set),
`BookProof/ChapterSmDiracYukawa.lean` (the Dirac and Yukawa operators and the
three Faris–Lavine hypotheses for them),
`BookProof/ChapterSmDiracSpinor.lean` (the relativistic spinor content) and
`BookProof/ChapterSmComparisonFull.lean` (every summand of the comparison
operator, derivative coordinates included). The third generation closes the
honest boundaries of the first: `BookProof/ChapterSmCarContinuum.lean` (the
continuum CAR algebra over an infinite-dimensional one-particle space),
`BookProof/ChapterSmGaugeConnection.lean` (the gauge connection inside the
covariant derivative),
`BookProof/ChapterSmBrstGhost.lean` and
`BookProof/ChapterSmGaugeRepresentation.lean` (the ghost/BRST sector), and
`BookProof/ChapterSmHiggsVacuum.lean` (symmetry breaking as statics). The
fourth takes the manuscript's own BRST definition literally:
`BookProof/ChapterBookBrstYangMills.lean`,
`BookProof/ChapterBookBrstGaugeFixing.lean` and
`BookProof/ChapterBookBrstInstances.lean`. Every chapter named here is
`sorry`-free and `axiom`-free, audited by `Work/SmStandardModelAudit.lean`,
`Work/SmHonestBoundariesAudit.lean` and `Work/BookBrstAudit.lean`; the ledger
of what moved and what did not is `HONEST_BOUNDARIES_SM.md`.

# Counting the Coordinates

:::paragraph
A single Standard-Model excitation carries the spatial position, the three gauge
fields with their spatial derivatives as independent coordinates, and the Higgs
doublet written in four real components with its derivatives. The count is not
taken on trust: the nine blocks are assembled as a type and their cardinality is
computed, giving $`D_B = 163` as a theorem.

$$`3 + 24 + 72 + 9 + 27 + 3 + 9 + 4 + 12 = 163.`

The Grassmann coordinates of the fermions are deliberately *not* in that type:
the CAR algebra is a separate development, and what the fermionic sector
contributes at this level is the mixing algebra of the next section.
:::

```
#check @BookProof.SmOneParticle.SmCoord
#check @BookProof.SmOneParticle.card_smCoord
#check @BookProof.SmOneParticle.smIdx
#check @BookProof.SmOneParticle.smG
#check @BookProof.SmOneParticle.smPhi
```

# The CKM and PMNS Matrices

:::paragraph
The quark and lepton Yukawa couplings enter the Hamiltonian through two unitary
$`3\times 3` matrices: the CKM matrix in the quark sector, the PMNS matrix in the
lepton sector. What the operator theory needs from them is not their measured
angles but their *unitarity identities*, and those are the theorems here: each row
has unit length, so no entry exceeds one in modulus; a real mixing matrix is
orthogonal, $`VV^{T} = I`, the Cabibbo case; the biunitary mass matrix
$`M = U_L V^{\dagger} D U_R^{\dagger}` satisfies
$`M^{\dagger}M = U_R D^{\dagger}D\,U_R^{\dagger}`, so the mixing drops out of the
squared masses; and a mixing rotation cannot amplify a Yukawa coupling by more
than the number of generations.

The measured Wolfenstein parameters, the PMNS angles, the mass ordering and the
absolute neutrino masses are experimental input and are claimed nowhere.
:::

```
#check @BookProof.SmOneParticle.IsMixing
#check @BookProof.SmOneParticle.unitary_row_sum_normSq
#check @BookProof.SmOneParticle.unitary_entry_norm_le_one
#check @BookProof.SmOneParticle.unitary_transpose_of_real
#check @BookProof.SmOneParticle.biunitary_massSq
#check @BookProof.SmOneParticle.norm_mulVec_le_sum
#check @BookProof.SmOneParticle.yukawa_bound
```

# The One-Particle Operator

:::paragraph
The one-particle operator is built on the Gauss–polynomial core of
$`L^2(\mathbb{R}^{163})` out of genuine differentiation and multiplication
operators, exactly as the Yang–Mills one is: forty momenta — one for each gauge
and Higgs field coordinate — and forty-nine squared real field polynomials. The
squares are the twenty-four gluon magnetic components
$`B^G_{a,i} = \tfrac12\varepsilon_{ijk}(G^a_{k,j} - G^a_{j,k} + g_s f^{abc}G^b_jG^c_k)`,
the nine weak ones, the three hypercharge ones, the twelve covariant Higgs
derivatives
$`(D_i\varphi)_a = \varphi_{a,i} + g W^j_i(\tau_j/2\,\varphi)_a + g'B_i(\sigma_3/2\,\varphi)_a`,
and the Higgs wall. The structure constants are arbitrary reals, so the genuinely
non-abelian — quartic — magnetic energy is the case proved, not an abelian
simplification.

The Higgs potential appears in its square form $`\tfrac{\lambda}{4}(\lVert\varphi\rVert^2 - v^2)^2`,
which differs from $`-\tfrac{\mu^2}{2}\lVert\varphi\rVert^2 + \tfrac{\lambda}{4}\lVert\varphi\rVert^4`
by the constant $`\mu^4/4\lambda` when $`v^2 = \mu^2/\lambda`; that identity is
proved, and it is what makes the operator a sum of squares. Being a sum of
squares, it is symmetric and bounded below, and the Friedrichs extension applies
to it directly — the same route the Yang–Mills chapter takes, and the one the
doctrine prescribes whenever the inner operator is bounded below.
:::

```
#check @BookProof.SmHamiltonian.SmParams
#check @BookProof.SmHamiltonian.smMagG
#check @BookProof.SmHamiltonian.smMagW
#check @BookProof.SmHamiltonian.smMagB
#check @BookProof.SmHamiltonian.smCovD
#check @BookProof.SmHamiltonian.smWall
#check @BookProof.SmHamiltonian.card_smMom
#check @BookProof.SmHamiltonian.card_smForm
#check @BookProof.SmHamiltonian.smHamiltonian
#check @BookProof.SmHamiltonian.smHamiltonian_symmetricOn
#check @BookProof.SmHamiltonian.smHamiltonian_quadForm
#check @BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg
#check @BookProof.SmHamiltonian.sm_friedrichs_extension
#check @BookProof.SmHamiltonian.higgs_mexican_hat
#check @BookProof.SmHamiltonian.wall_sq
```

# The Comparison Operator

:::paragraph
The Faris–Lavine route — the alternative instrument, used where the inner
operator is *not* bounded below — needs a comparison operator, and for the
Standard Model that operator has a characteristic shape: the confinement is
**quartic** in the non-abelian and Higgs coordinates and **quadratic** in the
abelian field and in the derivative coordinates. One commutation with such an
$`N` removes one power of $`(q,p)`, which is what makes the two commutator
hypotheses of the criterion plausible; a purely quadratic confinement would fail
to dominate the quartic magnetic and Higgs terms.

What is proved here is the operator itself, its symmetry, and the lower bound
$`\langle x, N x\rangle \ge \lVert x\rVert^2` for $`c_0 \ge 1`. Its dynamical
part — the forty uncoupled one-dimensional factors $`-d^2/dq^2 + q^4` and
$`-d^2/dq^2 + q^2` — is essentially self-adjoint: each factor by the
bounded-below wall theorem, and their tensor sum by the chain theorem of the
second-quantization chapter.
:::

```
#check @BookProof.SmComparison.card_smConf
#check @BookProof.SmComparison.smComparison
#check @BookProof.SmComparison.smComparison_symmetricOn
#check @BookProof.SmComparison.smComparison_quadForm
#check @BookProof.SmComparison.sm_N_positive
#check @BookProof.SmComparison.quarticEsaOp
#check @BookProof.SmComparison.quadraticEsaOp
#check @BookProof.SmComparison.sm_N_dyn_esa
#check @BookProof.SmComparison.sm_N_dyn_stone_flow
```

# The Enclosure

:::paragraph
The Hamiltonian of record is the enclosure $`H = d\Gamma(h)` on the nested Fock
space $`\bigoplus_n L^2(\mathbb{R}^{163n})`: one copy of the one-particle
operator per excitation, in every particle-number sector. Symmetry and positivity
of the quadratic form are fibrewise, so they lift sector by sector; the Friedrichs
extension and its Stone flow follow, and the enclosure is block diagonal in the
particle number — the number sectors, not a spatial lattice, are what decomposes
the problem.

A statement about the bare $`h` is a one-particle statement and is labelled as
such; a statement that calls itself *the* Standard-Model Hamiltonian must exhibit
the $`d\Gamma`.
:::

```
#check @BookProof.SmOuterFock.smSectorHam
#check @BookProof.SmOuterFock.smSectorHam_symmetricOn
#check @BookProof.SmOuterFock.smSectorHam_quadForm_nonneg
#check @BookProof.SmOuterFock.smSector_friedrichs_extension
#check @BookProof.SmOuterFock.smFockSpace
#check @BookProof.SmOuterFock.smFockCore
#check @BookProof.SmOuterFock.smFockCore_dense
#check @BookProof.SmOuterFock.smFockHam
#check @BookProof.SmOuterFock.smFockHam_symmetricOn
#check @BookProof.SmOuterFock.smFockHam_quadForm_nonneg
#check @BookProof.SmOuterFock.sm_dGamma_friedrichs_extension
#check @BookProof.SmOuterFock.sm_dGamma_stone_flow
#check @BookProof.SmOuterFock.smFockHam_number_conserving
```

# The CAR Algebra of the Fermions

:::paragraph
The fermionic sector needs an algebra before it can have operators. It is built
here over a finite set of modes, on the occupation-number Fock space with one
orthonormal basis vector for each occupied set, and with the Jordan–Wigner sign
that turns commutation into *anti*commutation. The four canonical relations are
theorems: $`\{a_i, a_i^{\dagger}\} = 1`, and $`\{a_i, a_j^{\dagger}\} = 0` for
$`i \neq j`, $`\{a_i, a_j\} = 0`, $`\{a_i^{\dagger}, a_j^{\dagger}\} = 0` — the
last two containing the Pauli principle $`a_i^2 = 0`. Creation and annihilation
are mutually adjoint and are contractions, so every polynomial in them is a
bounded operator; the second quantization $`\sum_{i,j} h_{ij} a_i^{\dagger} a_j`
of a Hermitian one-particle matrix is symmetric, its diagonal case is diagonal in
the occupation basis with eigenvalue the sum of the occupied mode energies, and a
one-particle energy floor $`\mu`$ becomes a gap above the Fock vacuum. All of it
is built over a *finite* mode set — the first honest boundary — and the section
on the continuum CAR algebra below reports what it takes to remove that
restriction.
:::

```
#check @BookProof.SmCar.FermiFock
#check @BookProof.SmCar.jwSign
#check @BookProof.SmCar.annih
#check @BookProof.SmCar.creat
#check @BookProof.SmCar.car_annih_creat_self
#check @BookProof.SmCar.car_annih_creat_of_ne
#check @BookProof.SmCar.car_annih_annih
#check @BookProof.SmCar.car_creat_creat
#check @BookProof.SmCar.inner_creat_left
#check @BookProof.SmCar.norm_annih_le
#check @BookProof.SmCar.fermiBilin
#check @BookProof.SmCar.fermiBilin_symmetric
#check @BookProof.SmCar.fermiEnergy_occ
#check @BookProof.SmCar.fermi_mass_gap
```

# Dirac, Yukawa, and the Faris–Lavine Certificate

:::paragraph
On that algebra the two fermionic operators of the record can finally be written:
the Dirac operator as the second quantization of a Hermitian one-particle matrix,
the Yukawa operator as the bilinear $`zM + (zM)^{\dagger}` in a Higgs background
$`z`, with $`M = U_L V^{\dagger} D U_R^{\dagger}` the biunitary mass matrix. The
mixing algebra of the second section is exactly what bounds it: no entry of $`M`
exceeds the sum of the diagonal masses, uniformly in the mixing angles.

For this sector the three Faris–Lavine hypotheses are theorems, with explicit
constants, against the comparison operator
$`N = \sum_i \omega_i a_i^{\dagger} a_i + c_0` of the plan: the relative bound
$`\pm h \le c_1 N`, the first-commutator bound and the double-commutator bound.
Together with $`N \ge 1` and the surjectivity of $`N + 1` they feed the project's
proof of Faris–Lavine Corollary 1.1 and give essential self-adjointness of the
Dirac–Yukawa Hamiltonian. The concrete spinor content comes from the $`4\times4`
Majorana model of the CPT chapter: that one-particle matrix is Hermitian and
squares to $`(k^2 + m_1^2 + m_2^2)\cdot 1`, so its eigenvalues are the
relativistic energies $`\pm\sqrt{k^2 + m_1^2 + m_2^2}`.
:::

```
#check @BookProof.SmDiracYukawa.smDirac
#check @BookProof.SmDiracYukawa.smYukawa
#check @BookProof.SmDiracYukawa.smFermiHam
#check @BookProof.SmDiracYukawa.smFermiHam_symmetricOn
#check @BookProof.SmDiracYukawa.yukawa_entry_bound
#check @BookProof.SmDiracYukawa.smFermiN
#check @BookProof.SmDiracYukawa.sm_fermi_N_ge_one
#check @BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective
#check @BookProof.SmDiracYukawa.sm_fermi_fl_i
#check @BookProof.SmDiracYukawa.sm_fermi_fl_ii
#check @BookProof.SmDiracYukawa.sm_fermi_fl_iii
#check @BookProof.SmDiracYukawa.sm_fermi_esa
#check @BookProof.SmDiracSpinor.diracOneParticle
#check @BookProof.SmDiracSpinor.diracOneParticle_hermitian
#check @BookProof.SmDiracSpinor.diracOneParticle_sq
#check @BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq
#check @BookProof.SmDiracSpinor.diracFieldHam
#check @BookProof.SmDiracSpinor.dirac_field_esa
```

# Every Summand of the Comparison Operator

:::paragraph
The derivative coordinates of $`N_0` carry no conjugate momentum: their summand is
multiplication by $`q^2`. That is not an obstruction — multiplication by a smooth
real function is essentially self-adjoint on the compactly supported smooth core,
with no growth or boundedness hypothesis — so each derivative coordinate is a
factor of the same kind as the dynamical ones, and the chain runs over all one
hundred and sixty summands: one for each collective coordinate except the three
spatial ones, which do not appear in $`N_0`.
:::

```
#check @BookProof.SmComparisonFull.derivEsaOp
#check @BookProof.SmComparisonFull.deriv_coordinate_esa
#check @BookProof.SmComparisonFull.smFullChain
#check @BookProof.SmComparisonFull.smFullChain_length
#check @BookProof.SmComparisonFull.sm_N_full_esa
#check @BookProof.SmComparisonFull.sm_N_full_stone_flow
```

# The Higgs Vacuum, as Statics

:::paragraph
Symmetry breaking has a static half that is a theorem about the potential. The
Mexican-hat potential is bounded below by $`-\mu^4/4\lambda` and attains that
value exactly on the vacuum manifold $`\lVert\varphi\rVert^2 = \mu^2/\lambda`.
Transverse to a vacuum the potential has no quadratic term at all — it rises as
$`(\lambda/4)t^4\lVert w\rVert^4`, the flatness of the Goldstone directions —
while along the radial direction it is exactly
$`V(u) + \mu^2\lVert u\rVert^2 t^2 (1 + t + t^2/4)`, a curvature $`m^2 = 2\mu^2`.
And the covariant-derivative term at a constant vacuum is a positive
semidefinite quadratic form in the gauge fields which vanishes precisely on the
generator combinations that annihilate the vacuum: the broken generators acquire
a mass term, the unbroken ones do not.
:::

```
#check @BookProof.SmHiggsVacuum.higgsV
#check @BookProof.SmHiggsVacuum.higgsV_sq_form
#check @BookProof.SmHiggsVacuum.higgsV_ge_min
#check @BookProof.SmHiggsVacuum.higgsV_eq_min_iff
#check @BookProof.SmHiggsVacuum.higgs_goldstone
#check @BookProof.SmHiggsVacuum.higgs_radial
#check @BookProof.SmHiggsVacuum.gaugeMassForm
#check @BookProof.SmHiggsVacuum.gaugeMassForm_nonneg
#check @BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff
```

# The Continuum CAR Algebra

:::paragraph
The finite mode set of the CAR section was the honest boundary: the algebra of
the fermions was over $`n`$ modes, not over the continuum. That restriction is
gone. The mode set is now $`\mathbb{N}`$, the one-particle space the
infinite-dimensional $`\ell^2(\mathbb{N})`$, and the Fock space the
antisymmetric Fock space in its occupation-number presentation
$`\ell^2(\mathrm{Finset}\,\mathbb{N})`$ — one basis vector per *finite*
occupied set, with the same Jordan–Wigner signs. The single-mode ladder
operators carry the four anticommutation relations and mutual adjointness as
before, but the operators that matter are the **smeared** ones
$`a^{\dagger}(f)`$, $`a(f)`$ for an arbitrary $`f \in \ell^2(\mathbb{N})`$:
since $`\sum_i |f_i|`$ may diverge, $`a^{\dagger}(f)`$ is not an absolutely
convergent sum of single-mode operators, and its boundedness
$`\lVert a^{\dagger}(f)\rVert \le \lVert f\rVert`$ is the *fermionic*
boundedness with no bosonic analogue. The canonical relation holds in the
smeared form $`\{a(f), a^{\dagger}(g)\} = \langle f, g\rangle\cdot 1`$, the
map $`f \mapsto a^{\dagger}(f)\Omega`$ is a linear isometry of
$`\ell^2(\mathbb{N})`$ into the Fock space — so the algebra really is over an
infinite-dimensional one-particle space — and the same relations are proved
over an *arbitrary* separable one-particle Hilbert space presented by a
Hilbert basis indexed by $`\mathbb{N}`$, in particular over the
$`L^2(\mathbb{R}^3)`$ of a continuum field.

What is *not* claimed here: the representation constructed is the Fock
representation on the vacuum; nothing is said about inequivalent
representations, about the C\*-completion as an abstract algebra, or about a
Hamiltonian on this space.
:::

```
#check @BookProof.SmCarContinuum.Ell2
#check @BookProof.SmCarContinuum.CFock
#check @BookProof.SmCarContinuum.cAnn
#check @BookProof.SmCarContinuum.cCre
#check @BookProof.SmCarContinuum.car_cAnn_cCre_self
#check @BookProof.SmCarContinuum.car_cAnn_cCre_of_ne
#check @BookProof.SmCarContinuum.car_cAnn_cAnn
#check @BookProof.SmCarContinuum.car_cCre_cCre
#check @BookProof.SmCarContinuum.inner_cCre_left
#check @BookProof.SmCarContinuum.cCreS
#check @BookProof.SmCarContinuum.cAnnS
#check @BookProof.SmCarContinuum.norm_cCreS_le
#check @BookProof.SmCarContinuum.norm_cAnnS_le
#check @BookProof.SmCarContinuum.cCreS_add
#check @BookProof.SmCarContinuum.cCreS_smul
#check @BookProof.SmCarContinuum.car_smeared
#check @BookProof.SmCarContinuum.car_cCreS_cCreS
#check @BookProof.SmCarContinuum.car_cAnnS_cAnnS
#check @BookProof.SmCarContinuum.oneParticleIsometry
#check @BookProof.SmCarContinuum.norm_cCreS_eq
#check @BookProof.SmCarContinuum.car_hilbert
#check @BookProof.SmCarContinuum.car_hilbert_cre
#check @BookProof.SmCarContinuum.norm_carCre_le
```

# The Gauge Connection

:::paragraph
Minimal coupling, for one plane-wave matter mode in the constant
collective-coordinate background: $`D_j = i(k_j + A_j)`$ with
$`A_j = g \sum_a A^a_j T_a`$. The connection is Hermitian and $`D`$ is
anti-Hermitian; at zero coupling $`D_j = i k_j`$. The commutator
$`[D_j, D_l]`$ is — up to a factor — $`-ig^2 \sum_c (\sum_{a,b} f_{abc}
A^a_j A^b_l) T_c`$, the non-abelian field strength: the operator form of
$`W^j_{\mu\nu} = -(i/g)\,\mathrm{tr}([D_\mu,D_\nu]\tau^j)`$ of the manuscript
and of the $`g_s f^{abc} G^b_j G^c_k`$ term of the magnetic energy, now
*inside* the covariant derivative rather than asserted about it. A constant
abelian background is pure gauge, conjugating $`D`$ by a unitary conjugates the
connection, and if the adjoint action rotates the generators by a real matrix
the conjugated connection is again a connection with rotated components. On
that base sits the gauged Dirac one-particle matrix — Hermitian, equal to the
free matrix of the spinor section at zero field, splitting as free plus
interaction — and its second quantization over the twelve colour–spinor modes
is essentially self-adjoint through the very same three Faris–Lavine
hypotheses that certificate the ungaugeed operator.

What is *not* claimed here: the background is constant, so $`D_j`$ carries
$`i k_j`$ rather than an unbounded derivative, and this module’s commutator
$`[D_j, D_l]`$ therefore sees only the non-abelian part of $`F`$ ($`\partial A = 0`$);
the full $`F_{μν} = \partial_μ A_ν - \partial_ν A_μ + [A_μ, A_ν]`$ is in the tree as
$`smMagG`$/$`smMagW`$/$`smMagB`$, but there is no gauge-field dynamics and no
continuum limit of $`D`$. (The curl/continuum half is reachable by the momentum-space
convolution already used for NS and QG — not a QYM device, only for proofs of this type.)
:::

```
#check @BookProof.SmGaugeConnection.conn
#check @BookProof.SmGaugeConnection.conn_conjTranspose
#check @BookProof.SmGaugeConnection.covD_conjTranspose
#check @BookProof.SmGaugeConnection.covD_zero_coupling
#check @BookProof.SmGaugeConnection.covD_commutator
#check @BookProof.SmGaugeConnection.covD_commutator_abelian
#check @BookProof.SmGaugeConnection.covD_conj
#check @BookProof.SmGaugeConnection.conn_gauge_transform
#check @BookProof.SmGaugeConnection.diracGaugeMat
#check @BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose
#check @BookProof.SmGaugeConnection.diracGaugeMat_free
#check @BookProof.SmGaugeConnection.diracGaugeMat_split
#check @BookProof.SmGaugeConnection.diracGaugeField
#check @BookProof.SmGaugeConnection.diracGaugeField_symmetric
#check @BookProof.SmGaugeConnection.dirac_gauge_field_esa
```

# The Ghosts, the Generators, and the BRST Charge

:::paragraph
The ghost/BRST sector needed structure constants before it could have a
charge. The structure constants of $`su(3)\oplus su(2)\oplus u(1)`$ are
assembled from an $`su(3)`$ family, the Levi-Civita $`su(2)`$ family and the
abelian one, and their antisymmetry and Jacobi identity are theorems, not
data. Twelve ghosts live as the last twelve modes of the CAR algebra, with the
ghost-number operator and its commutators with the ghosts. The bridge from
matrices to operators is the identity $`[d\Gamma(A), d\Gamma(B)] =
d\Gamma([A,B])`$: the Gauss-law generators $`G_a = -i\,d\Gamma(T_a)`$ close
with the *real* structure constants, and they commute with the ghosts — they
are even. With that in hand the abstract charge
$`\Omega = \sum_a c^a G_a - \tfrac12 f_{abc} c^a c^b b_c`$ satisfies
$`\Omega^2 = 0`$ in any ring carrying ghosts with the CAR relations and
first-class constraints, hence on the joint matter–ghost Fock space of the
Standard Model.

The representation-level hypothesis is removed one step further: the Pauli
generators $`\tau_k/2`$ close with $`\varepsilon_{jkl}`$; the twelve
generators of one coloured weak doublet — $`T_a\otimes 1`$, $`1\otimes\tau_k/2`$,
$`y\cdot 1`$ — close with the structure constants; and on the eighteen-mode
Fock space (six matter modes, twelve ghosts) the Standard-Model BRST charge of
that multiplet squares to zero, with the antisymmetry and Jacobi identity of
the structure constants *derived* from the two defining relations of the
$`su(3)`$ generators rather than assumed.
:::

```
#check @BookProof.SmBrstGhost.smStruct
#check @BookProof.SmBrstGhost.smStruct_antisymm
#check @BookProof.SmBrstGhost.smStruct_jacobi
#check @BookProof.SmBrstGhost.ghostCre
#check @BookProof.SmBrstGhost.ghostAnn
#check @BookProof.SmBrstGhost.smGhostCAR
#check @BookProof.SmBrstGhost.ghostNumber
#check @BookProof.SmBrstGhost.ghostNumber_occ
#check @BookProof.SmBrstGhost.fermiBilin_lie
#check @BookProof.SmBrstGhost.matterGen_lie
#check @BookProof.SmBrstGhost.matterGen_comm_ghostCre
#check @BookProof.SmBrstGhost.matterGen_comm_ghostAnn
#check @BookProof.SmBrstGhost.smBrstCharge
#check @BookProof.SmBrstGhost.smBrstCharge_nilpotent
#check @BookProof.SmGaugeRep.su2gen
#check @BookProof.SmGaugeRep.su2gen_closes
#check @BookProof.SmGaugeRep.smGenP
#check @BookProof.SmGaugeRep.smGen
#check @BookProof.SmGaugeRep.smGen_closes
#check @BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations
#check @BookProof.SmGaugeRep.sm_brst_nilpotent_rep
```

# The BRST Charge as the Book Defines It

:::paragraph
The charge of the previous section is the abstract one, with the constraints
given as data. The manuscript itself defines the charge by a **density** —
$`\Omega(x) = \pi^\mu_a \partial_\mu \psi^\dagger_a - \pi^\mu_a f_{abc}
A_{\mu b}\psi^\dagger_c - (i/2) f_{abc}\psi^\dagger_a\psi^\dagger_b\psi_c`$,
together with $`[A_{\mu a},\pi^\nu_b] = i\delta^\nu_\mu\delta_{ab}`$ and
$`\{\psi_a,\psi^\dagger_b\} = \delta_{ab}`$ — and that definition is now
implemented on the graded state space
$`\mathbb{C}[A_{\mu a}]\otimes\Lambda(\mathbb{C}^N)`$: the canonical
relations hold in the realization, the bosonic operators commute with the
ghosts, and the three terms of the density are assembled into the book's
charge, with the derivative term written through the derivations
$`\partial_\mu`$ of the gauge algebra.

The decisive step is that the **Gauss law is derived, not assumed**: the
coefficient of the ghost $`\psi^\dagger_c`$ in the book's charge closes into
the gauge algebra, from the canonical relations, the Leibniz property of
$`\partial_\mu`$ and the Jacobi identity. Nilpotency $`\Omega^2 = 0`$ follows,
and identifying the book's charge with $`i`$ times the abstract charge shows
that the book's coefficient $`-i/2`$ of the cubic ghost term is exactly the
one nilpotency requires. On that foundation the gauge-fixing fermion
$`\Psi = i\psi_a A_{0a}`$ of the manuscript's Weyl-gauge section is built, the
generated term $`\{\Omega,\Psi\}`$ is computed in closed form — the Gauss law
contracted with $`A_0`$, the ghost kinetic term, the non-abelian ghost–field
coupling — and is proved BRST invariant, which is what allows the manuscript
to add it to the Hamiltonian. On the temporal-gauge slice $`A_0 = 0`$ that
entire BRST-exact term vanishes — $`{Ω, Ψ} = 0`$ — so the records of
$`h`$ and $`N`$ need no extra gauge-fixing or ghost summand (the accounting
identity $`bookGfTerm_eq_zero_of_Afield0`$, with the $`su(2)`$ and
Standard-Model instances; Cadabra CHECK 29–30). For pure Yang–Mills the same
identity lets the Weyl gauge work with the spatial field components only. For
quantum gravity the manuscript's three-dimensional reduction is *not* the ADM
one: the time-like vector is fixed to $`v^\mu = \delta^\mu_0`$, the ghosts of
the resulting charge are constant in the timepiece, and the charge keeps the
same functional form as the four-dimensional one — explicitly different from
the ADM BRST charge. The BRST cohomology is well defined:
$`\ker\Omega / \im\Omega`$, with $`\im\Omega \subseteq \ker\Omega`$ from
$`\Omega^2 = 0`$, the gauge-fixing term preserving both subspaces so that it
descends to the quotient, and gauge-invariant observables — anything
commuting with the constraints and the ghosts — commuting with the charge,
exemplified by the Casimir of constant gauge fields. The $`su(2)`$ and
Standard-Model instances supply the concrete algebras, their nilpotency, and
the fact that the constraints are not the zero operator.

What is *not* claimed here: the local gauge algebra is modelled by a
finite-dimensional Lie algebra with derivations $`\partial_\mu`$ (the
manuscript's totally antisymmetric $`SU(N)`$ structure constants are used), so
the Gauss law is local in that algebra rather than at every point of a
continuum space; the manuscript's operator formalism uses no Faddeev–Popov
determinant and none is constructed; and, while the cohomology is defined and
shown well defined, nothing is claimed about its *size*.
:::

```
#check @BookProof.BookBrstYangMills.GaugeAlgebra
#check @BookProof.BookBrstYangMills.Afield
#check @BookProof.BookBrstYangMills.mom
#check @BookProof.BookBrstYangMills.chiOp
#check @BookProof.BookBrstYangMills.betaOp
#check @BookProof.BookBrstYangMills.bookCCR
#check @BookProof.BookBrstYangMills.bookGhostCar
#check @BookProof.BookBrstYangMills.bookOmega
#check @BookProof.BookBrstYangMills.gaussGen_bracket
#check @BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
#check @BookProof.BookBrstYangMills.bookOmega_nilpotent
#check @BookProof.BookBrstYangMills.bookConstraintAlgebra
#check @BookProof.BookBrstGaugeFixing.bookGfFermion
#check @BookProof.BookBrstGaugeFixing.bookGfTerm
#check @BookProof.BookBrstGaugeFixing.bookGfTerm_eq
#check @BookProof.BookBrstGaugeFixing.bookGfTerm_brst_closed
#check @BookProof.BookBrstGaugeFixing.gfFermion_eq_zero
#check @BookProof.BookBrstGaugeFixing.bookGfFermion_eq_zero_of_Afield0
#check @BookProof.BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0
#check @BookProof.BookBrstGaugeFixing.physicalStates
#check @BookProof.BookBrstGaugeFixing.exactStates
#check @BookProof.BookBrstGaugeFixing.exactStates_le_physicalStates
#check @BookProof.BookBrstGaugeFixing.brstCohomology
#check @BookProof.BookBrstGaugeFixing.bookGfTerm_mem_physicalStates
#check @BookProof.BookBrstGaugeFixing.bookGfTerm_mem_exactStates
#check @BookProof.BookBrstGaugeFixing.bookOmega_comm_multOp
#check @BookProof.BookBrstGaugeFixing.casimir_bookOmega_comm
#check @BookProof.BookBrstInstances.innerDeriv_leibniz
#check @BookProof.BookBrstInstances.su2BookAlgebra
#check @BookProof.BookBrstInstances.smBookAlgebra
#check @BookProof.BookBrstInstances.su2_bookOmega_nilpotent
#check @BookProof.BookBrstInstances.sm_bookOmega_nilpotent
#check @BookProof.BookBrstInstances.su2_gaussGenPoly_ne_zero
#check @BookProof.BookBrstInstances.su2_casimir_bookOmega_comm
#check @BookProof.BookBrstInstances.su2_bookGfTerm_eq_zero_of_Afield0
#check @BookProof.BookBrstInstances.sm_bookGfTerm_eq_zero_of_Afield0
```

# What Is Not Claimed

:::paragraph
The boundaries of this chapter are as much a part of it as its theorems. The CAR
algebra, the Dirac and Yukawa operators, the continuum CAR algebra over an
infinite-dimensional one-particle space, the gauge connection inside $`D`, and
the ghost/BRST sector (including the charge as the manuscript defines it and
the accounting identity that adds no gauge-fixing summand to $`h`$ or $`N`$)
are all Lean theorems now — see the sections above and the ledger
`HONEST_BOUNDARIES_SM.md` (live list §L). Still open there: Majorana masses
and the see-saw; the three Faris–Lavine hypotheses for the *bosonic* operator
($`sm_fermi_fl_i`$/$`ii`$/$`iii`$ and $`sm_fermi_esa`$ are the fermionic
theorems; the bosonic Lean counterpart is `ChapterSmFarisLavine.lean` →
$`sm_h_esa`$ — still open, design handed to the Lean4 specialist in
`CONSOLIDATED_PLAN.md` §2026-09-23e, while the independent Friedrichs route
for that operator is already proved); no continuum spectrum or mass gap for
$`d\Gamma(h)`, no QCD mass gap; electroweak symmetry breaking as statics only — vacuum manifold,
Goldstone flatness, radial curvature, mass form of broken generators — not
dynamics (no expansion of the quantum Hamiltonian around the vacuum and no
gauge-boson mass value); no measured mixing parameter: of the CKM and PMNS
matrices only the unitarity identities and the entry bound are formalized;
and no size is claimed for the BRST cohomology.
:::
