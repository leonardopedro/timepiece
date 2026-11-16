import Mathlib
import BookProof.Toolbox.ChapterFockNumberPreservingGap
import BookProof.OSReconstruction.ObservablePrior

/-!
# C0 — the physical object manifest

Work order: `cftproof.md`, **C0** ("bind the physical object, reference state and cutoffs
once").  This module writes the binder down in Lean and proves the two identities the
work order singles out, plus the negative controls that decide whether an alleged
continuum object is the *same* object.

## What is real here, and what is not

The final regulated Hamiltonian of the manuscript is

```text
H_sigma = dGamma(h_sigma)
        = sum_ij <e_i, h_sigma e_j> Cdag(e_i) A(e_j),
```

the complete specified interacting **inner** operator `h_sigma` (inner pair terms and
scalar terms included) enclosed between outer creation on the left and outer annihilation
on the right.  `BookProof.FockSecondQuantization.dGamma` is exactly that operator on the
finite-particle Fock algebra, and the corpus's `ChapterFockNumberPreservingGap` already
proves the identities this module needs.

* `NestedSpec` is the manifest: the specified inner column family `h_sigma`, the
  **physical cutoff** `(a, L, R)`, the **solver budget** `(m, q, precision)` kept
  separate from it, the renormalized scale, the colour rank and the reference energy.
* `NestedSpec.finalHamiltonian S = dGamma S.inner` is `H_sigma`, and
  `numberOperator = dGamma numberCol` is the outer number operator
  `N_out = dGamma(1)` — *not* a separate second quantization.
* `NestedSpec.relativeGenerator S = H_sigma - E_ref • 1` is the `K_sigma` of C0; on the
  outer vacuum it is `-E_ref • Omega_out`, so the subtraction is relative dynamics and
  does not remove inner constants.

The two positive identities:

* `finalHamiltonian_shift` — **`h_sigma + c • 1` lifts to `H_sigma + c • N_out`**; the
  scalar shift produces no other outer operator.  This is C0's
  "`h+cI` changes `H` by `c N_out`", and it is why a scalar inner shift is a change of
  model rather than a normalisation.
* `finalHamiltonian_eq_of_inner_eq` and `dGamma_injective` — the inner operator is
  recoverable from the outer one, so "the same `dGamma`" is a statement about the inner
  object and not a naming convention.

The negative controls C0/C10 require:

* `shift_changes_model` — a nonzero inner constant shift changes the model
  (`H' != H`), so an allegedly equivalent manifest with a shifted constant is rejected.
* `droppedInteraction_rejected` — replacing the specified inner column family by another
  one (in particular by its free part, i.e. discarding the interaction) changes the
  operator.
* `physicalCutoff_withSolver` / `krylov_not_continuum` — enlarging the Krylov rank, the
  rational order or the arithmetic precision changes no physical cutoff, so `m -> inf`
  at fixed `a, L, R` is **not** a spacetime continuum limit.
* `unrelatedAdapter_rejected` / `mismatchedBasis_rejected` — an archive adapter whose
  family is not the manifest's, or whose OPE and reconstruction bases differ, does not
  match.  This is the `M.basis = Q.port` clause of C0's acceptance.

## Boundary, recorded rather than assumed away

`NestedSpec.inner` is a concrete column family of the corpus's finite-mode Fock algebra:
it binds the inner operator as data, **not** as a self-adjoint operator with an identified
domain, and it does not construct the growing spatial regulator family that C0 asks for.
The gauge group, representation, bare-coupling trajectory, boundary condition and prior
are not constructed here; the manifest records the colour rank and the scale that a full
manifest must also carry, and the fields are data for the specialist packets.

The archive adapter is an **inventory**, not an import: the October package
(`../OpenAI-YM-20261028`) is not present in this workspace, so no archive theorem is
assumed, ported or restated as an axiom.  `ArchiveAdapter` records the data a real adapter
must supply (the Wilson family as columns, the extraction order, and the basis/port
labels), and `AdapterMatches` is the compatibility predicate C0 requires.  Constructing
the adapter remains C0/C8 work.

Axiom footprint: no `sorry`, and every theorem rests on `propext`, `Classical.choice`,
`Quot.sound` only (`Work/ContinuumManifestAudit.lean`).
-/

noncomputable section

namespace BookProof.OSReconstruction.ContinuumManifest

open BookProof.FockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.BalabanRG
open BookProof.ReflectionPositivity

/-! ## 1. The one-particle vectors and injectivity of `dΓ` -/

/-- The one-particle state `|e_k>` in the corpus's Fock algebra. -/
def oneVec (k : ℕ) : FockAlg :=
  Finsupp.single (Finsupp.single k 1) (1 : ℂ)

theorem oneVec_ne_zero (k : ℕ) : oneVec k ≠ 0 := by
  simp [oneVec]

/-- The creation operator on the vacuum is the one-particle basis vector. -/
theorem creA_vac (k : ℕ) : creA k vac = oneVec k := by
  rw [oneVec, vac, creA_single]
  have hup : up k (0 : Conf) = Finsupp.single k 1 := rfl
  rw [hup]
  norm_num

/-- On a one-particle vector, `dΓ` is the one-particle vector of the column. -/
theorem dGamma_oneVec (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGamma col (oneVec k) = ∑ j ∈ (col k).support, (col k) j • oneVec j := by
  rw [oneVec, dGamma_one_particle]
  exact Finset.sum_congr rfl fun j _ => by rw [oneVec]

/-- Evaluating the one-particle vector at `⟨e_j|` reads off the `j`-th component. -/
theorem onePartVec_apply (v : ℕ →₀ ℂ) (j : ℕ) :
    (∑ i ∈ v.support, v i • oneVec i) (Finsupp.single j 1) = v j := by
  classical
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.smul_apply, oneVec, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro i _ hij
    have hne : (Finsupp.single i (1 : ℕ) : Conf) ≠ Finsupp.single j (1 : ℕ) := by
      intro h
      exact hij (Finsupp.single_left_inj one_ne_zero |>.mp h)
    simp only [Finsupp.smul_apply, oneVec]
    rw [Finsupp.single_eq_of_ne' hne, smul_zero]
  · intro hj
    rw [Finsupp.notMem_support_iff.mp hj, zero_smul, Finsupp.zero_apply]

/-- **`dΓ` determines its one-particle matrix**: the second quantization is injective. -/
theorem dGamma_injective : Function.Injective dGamma := by
  intro c d h
  funext k
  refine Finsupp.ext fun j => ?_
  have hk : dGamma c (oneVec k) = dGamma d (oneVec k) := by rw [h]
  rw [dGamma_oneVec, dGamma_oneVec] at hk
  have := congrArg (fun u : FockAlg => u (Finsupp.single j 1)) hk
  simpa [onePartVec_apply] using this

/-! ## 2. The manifest -/

/-- The **physical cutoff** of the regulator family: UV spacing, spatial volume and
Hermite/occupation cutoff.  These are the parameters a continuum limit must remove. -/
structure PhysicalCutoff where
  /-- physical UV spacing `a`. -/
  spacing : ℝ
  /-- spatial volume `L`. -/
  volume : ℝ
  /-- Hermite/occupation cutoff `R`. -/
  hermiteRank : ℕ

/-- The **solver budget**: Krylov rank `m`, rational order `q` and arithmetic precision.
These are approximation parameters, not spacetime cutoffs. -/
structure SolverBudget where
  /-- Krylov rank `m`. -/
  krylovRank : ℕ
  /-- rational approximation order `q`. -/
  ratOrder : ℕ
  /-- arithmetic precision (bits). -/
  precision : ℕ

/-- A **renormalized field label**: which local gauge-invariant monomial the observable
is (`label`), the smearing that localizes it, and the renormalization scale at which its
vacuum expectation is subtracted.  The scale is part of the label: an unsubtracted
smearing is not a renormalized one. -/
structure FieldLabel where
  /-- the label of the local monomial (`1`, `F_{μν}F^{μν}`, ...). -/
  label : ℕ
  /-- the smearing observable. -/
  smearing : Observable
  /-- the renormalization scale of the subtraction. -/
  scale : ℝ
  /-- the scale is positive. -/
  scale_pos : 0 < scale

namespace FieldLabel

/-- A renormalized label has a nonzero scale: `scale = 0` is the unsubtracted
smearing, which C0 does not accept as a renormalized observable. -/
theorem scale_ne_zero (L : FieldLabel) : L.scale ≠ 0 := ne_of_gt L.scale_pos

end FieldLabel

/-- **The positive-time half-space data**: the positive-time half of the lattice, the
algebra `𝔄₊` of observables depending only on it, and the smeared field labels at their
renormalization scales.  `labels_mem` is the physical constraint: only positive-time
smearings are admitted, which is the half-space OS form's hypothesis. -/
structure HalfSpaceData where
  /-- the chosen positive-time half. -/
  half : Set (Fin latticeDim)
  /-- it is the corpus's positive-time half. -/
  half_eq : half = posTimeCoords
  /-- the positive-time algebra `𝔄₊`. -/
  algebra : Subalgebra ℝ Observable
  /-- it is the corpus's `PositiveTimeAlgebra`. -/
  algebra_eq : algebra = PositiveTimeAlgebra
  /-- the smeared field labels, indexed by mode. -/
  labels : ℕ → FieldLabel
  /-- every label's smearing lies in the positive-time algebra. -/
  labels_mem : ∀ k, (labels k).smearing ∈ algebra

namespace HalfSpaceData

variable (H : HalfSpaceData)

/-- The algebra really is `𝔄₊`. -/
theorem algebra_eq_positiveTime : H.algebra = PositiveTimeAlgebra := H.algebra_eq

/-- Every label's smearing lies in `𝔄₊`, the hypothesis OS reconstruction needs. -/
theorem labels_mem_positiveTime (k : ℕ) : (H.labels k).smearing ∈ PositiveTimeAlgebra := by
  rw [← H.algebra_eq]
  exact H.labels_mem k

/-- The reflection `θ` maps each label's smearing into the past algebra: the positive
time direction is not symmetric. -/
theorem theta_labels_dependsOn_negTime (k : ℕ) :
    dependsOn (thetaObs (H.labels k).smearing) negTimeCoords :=
  thetaObs_dependsOn_negTime (H.labels_mem_positiveTime k)

/-- **A label outside `𝔄₊` is rejected**: no mode of the manifest carries it. -/
theorem label_outside_algebra_rejected (L : FieldLabel)
    (h : L.smearing ∉ H.algebra) (k : ℕ) : H.labels k ≠ L := by
  intro he
  exact h (he ▸ H.labels_mem k)

end HalfSpaceData

/-- **The manifest of the specified physical object.**  It binds the interacting inner
operator, the regulator parameters, the renormalized scale, the colour rank, the
reference energy and the positive-time observable data once; every other packet is read
against this record. -/
structure NestedSpec where
  /-- the specified inner one-particle operator `h_sigma`, as the corpus's column family
  (`inner k` is the `k`-th column of matrix elements). -/
  inner : ℕ → (ℕ →₀ ℂ)
  /-- the physical cutoff `(a, L, R)`. -/
  cutoff : PhysicalCutoff
  /-- the solver budget `(m, q, precision)`, kept separate from the cutoff. -/
  solver : SolverBudget
  /-- the renormalized observable scale. -/
  scale : ℝ
  /-- the scale is positive. -/
  scale_pos : 0 < scale
  /-- the colour rank `N_c` (e.g. `3` for the SU(3)-indexed model). -/
  colour : ℕ
  /-- the colour rank is positive. -/
  colour_pos : 0 < colour
  /-- the reference energy `E_ref` on the chosen sector. -/
  referenceEnergy : ℝ
  /-- the positive-time algebra and the smeared field labels. -/
  halfSpace : HalfSpaceData

/-- The outer number operator `N_out = dΓ(1)`. -/
def numberOperator : FockAlg →ₗ[ℂ] FockAlg := dGamma numberCol

namespace NestedSpec

variable (S : NestedSpec)

/-- The regulated Hamiltonian `H_sigma = dΓ(h_sigma)`. -/
def finalHamiltonian : FockAlg →ₗ[ℂ] FockAlg := dGamma S.inner

/-- The **relative** generator `K_sigma = H_sigma - E_ref • 1` on the chosen sector. -/
def relativeGenerator : FockAlg →ₗ[ℂ] FockAlg :=
  S.finalHamiltonian - (S.referenceEnergy : ℂ) • LinearMap.id

/-- Replacing the inner columns while keeping every other manifest datum fixed: this is
one regulator of the same family. -/
def withInner (h : ℕ → (ℕ →₀ ℂ)) : NestedSpec :=
  { S with inner := h }

/-- Replacing the solver budget while keeping the physical cutoff fixed. -/
def withSolver (b : SolverBudget) : NestedSpec :=
  { S with solver := b }

@[simp] theorem withInner_inner (h : ℕ → (ℕ →₀ ℂ)) : (S.withInner h).inner = h := rfl

@[simp] theorem withInner_cutoff (h : ℕ → (ℕ →₀ ℂ)) : (S.withInner h).cutoff = S.cutoff := rfl

@[simp] theorem withInner_referenceEnergy (h : ℕ → (ℕ →₀ ℂ)) :
    (S.withInner h).referenceEnergy = S.referenceEnergy := rfl

/-- The outer Hamiltonian of a manifest with prescribed inner columns. -/
theorem finalHamiltonian_withInner (h : ℕ → (ℕ →₀ ℂ)) :
    (S.withInner h).finalHamiltonian = dGamma h := rfl

/-- **C0: an inner scalar shift lifts to `c N_out` and to nothing else.** -/
theorem finalHamiltonian_shift (c : ℂ) :
    (S.withInner fun k => S.inner k + c • numberCol k).finalHamiltonian
      = S.finalHamiltonian + c • numberOperator := by
  rw [finalHamiltonian_withInner, finalHamiltonian, dGamma_shiftPlus, numberOperator]

/-- The relative generator of a manifest with prescribed inner columns. -/
theorem relativeGenerator_withInner (h : ℕ → (ℕ →₀ ℂ)) :
    (S.withInner h).relativeGenerator
      = dGamma h - (S.referenceEnergy : ℂ) • LinearMap.id := rfl

/-- The shift does not disappear under the reference-energy subtraction: `K` moves by the
same `c N_out`. -/
theorem relativeGenerator_shift (c : ℂ) :
    (S.withInner fun k => S.inner k + c • numberCol k).relativeGenerator
      = S.relativeGenerator + c • numberOperator := by
  rw [relativeGenerator_withInner, relativeGenerator, finalHamiltonian,
    dGamma_shiftPlus, numberOperator]
  abel

/-- The outer vacuum is killed by every second quantization, so `K_sigma` acts on it as
`-E_ref`; the reference subtraction is relative dynamics, not a change of the inner
operator. -/
theorem relativeGenerator_vac :
    S.relativeGenerator vac = -((S.referenceEnergy : ℝ) : ℂ) • vac := by
  rw [relativeGenerator, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    finalHamiltonian, dGamma_vac, zero_sub, neg_smul]

/-- Two manifests with the same inner columns have the same outer Hamiltonian. -/
theorem finalHamiltonian_eq_of_inner_eq {S T : NestedSpec} (h : S.inner = T.inner) :
    S.finalHamiltonian = T.finalHamiltonian := by
  rw [finalHamiltonian, finalHamiltonian, h]

/-- Conversely `dΓ` determines the inner columns. -/
theorem inner_eq_of_finalHamiltonian_eq {S T : NestedSpec}
    (h : S.finalHamiltonian = T.finalHamiltonian) : S.inner = T.inner :=
  dGamma_injective h

end NestedSpec

/-! ## 3. The observable dictionary: the prior and the positive-time algebra -/

/-- **The observable/prior dictionary** at a finite regulator (`cftproof.md` B0): the
joint spatial information prior together with the positive-time algebra and the
renormalized field labels.  The prior is an arbitrary joint law, so sharing information
between distinct supports is part of the dictionary rather than an assumption against it. -/
structure ObservableDictionary (n : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- the spatial information prior and its joint law. -/
  prior : SpatialPrior n Ω
  /-- the positive-time algebra and the smeared labels. -/
  halfSpace : HalfSpaceData

namespace ObservableDictionary

variable {n : ℕ} {Ω : Type*} [Fintype Ω] (D : ObservableDictionary n Ω)

/-- Every smeared label of the dictionary lies in `𝔄₊`. -/
theorem labels_mem_positiveTime (k : ℕ) :
    (D.halfSpace.labels k).smearing ∈ PositiveTimeAlgebra :=
  D.halfSpace.labels_mem_positiveTime k

/-- The dictionary's one-point proposition is normalized: `ω(prop i) = 1` at every
site of positive prior mass (B0's normalization clause). -/
theorem prior_prop_normalized (i : Fin n) (h : 0 < D.prior.mass i) :
    D.prior.expect (D.prior.prop i) = 1 :=
  D.prior.expect_prop i h

/-- The two-point function is the joint information over the product of the
marginals, so the dictionary retains the joint law rather than reducing to a product
prior. -/
theorem prior_corr_eq (i j : Fin n) (hi : 0 < D.prior.mass i) (hj : 0 < D.prior.mass j) :
    D.prior.corr i j = D.prior.joint i j / (D.prior.mass i * D.prior.mass j) :=
  D.prior.corr_eq i j hi hj

/-- A label outside `𝔄₊` is not part of the dictionary. -/
theorem label_outside_rejected (L : FieldLabel) (h : L.smearing ∉ D.halfSpace.algebra)
    (k : ℕ) : D.halfSpace.labels k ≠ L :=
  D.halfSpace.label_outside_algebra_rejected L h k

end ObservableDictionary

/-! ## 4. Negative controls -/

/-- **A nonzero inner constant shifts the model.**  `h + c • 1` is a different physical
object from `h` (C0's "`h+cI` changes `H` by `c N_out`", read as a rejection test). -/
theorem shift_changes_model (S : NestedSpec) {c : ℂ} (hc : c ≠ 0) :
    (S.withInner fun k => S.inner k + c • numberCol k).finalHamiltonian
      ≠ S.finalHamiltonian := by
  intro h
  rw [NestedSpec.finalHamiltonian_withInner, NestedSpec.finalHamiltonian,
    dGamma_shiftPlus] at h
  have hk := congrArg (fun T : FockAlg →ₗ[ℂ] FockAlg => T (oneVec 0)) h
  simp only [LinearMap.add_apply, LinearMap.smul_apply] at hk
  have hN : dGamma numberCol (oneVec 0) = oneVec 0 := by
    rw [numberCol, oneVec, dGamma_diagCol_one_particle]
    norm_num
  rw [hN] at hk
  have hzero : c • oneVec 0 = 0 := by
    have h2 : (dGamma S.inner) (oneVec 0) + c • oneVec 0
        = (dGamma S.inner) (oneVec 0) + 0 := by simpa using hk
    exact add_left_cancel h2
  rcases smul_eq_zero.mp hzero with hc' | hv
  · exact hc hc'
  · exact oneVec_ne_zero 0 hv

/-- **Discarding the interaction changes the operator**: replacing the specified inner
column family by any other one — in particular by its free part — is rejected. -/
theorem droppedInteraction_rejected (S : NestedSpec) {h : ℕ → (ℕ →₀ ℂ)} (hh : h ≠ S.inner) :
    (S.withInner h).finalHamiltonian ≠ S.finalHamiltonian := by
  intro heq
  exact hh (NestedSpec.inner_eq_of_finalHamiltonian_eq heq)

/-- Enlarging the solver budget changes no physical cutoff. -/
theorem physicalCutoff_withSolver (S : NestedSpec) (b : SolverBudget) :
    (S.withSolver b).cutoff = S.cutoff := rfl

/-- **`m -> inf` at fixed `a, L, R` is not a continuum limit**: the physical cutoff of the
enlarged-Krylov manifest is unchanged. -/
theorem krylov_not_continuum (S : NestedSpec) :
    (S.withSolver { S.solver with krylovRank := S.solver.krylovRank + 1 }).cutoff
      = S.cutoff := rfl

/-! ## 5. The archive adapter inventory -/

/-- The data an archive adapter must supply: the Wilson family as a column family, the
volume extraction order, and the reconstruction/OPE basis labels.  This is an inventory
of the October package's interface (`WilsonBridge.fromWilson`, `Order.upon`,
`Order.determined`, `Continuum.continuum`), not an import of it. -/
structure ArchiveAdapter where
  /-- the archive's Wilson family, as the same column representation. -/
  family : ℕ → (ℕ →₀ ℂ)
  /-- the extraction order on volumes. -/
  order : ℕ → ℕ
  /-- the label of the reconstruction basis `M.basis`. -/
  basisLabel : ℕ
  /-- the label of the OPE port `Q.port`. -/
  portLabel : ℕ

/-- **Compatibility of an adapter with the manifest**: the adapter's family is the
manifest's inner family (the same witness, not an unrelated existential one) and the
reconstruction and OPE bases agree (`M.basis = Q.port`). -/
def AdapterMatches (S : NestedSpec) (A : ArchiveAdapter) : Prop :=
  A.family = S.inner ∧ A.basisLabel = A.portLabel

theorem adapterMatches_iff (S : NestedSpec) (A : ArchiveAdapter) :
    AdapterMatches S A ↔ A.family = S.inner ∧ A.basisLabel = A.portLabel := Iff.rfl

/-- An archive adapter built on an unrelated family does not match. -/
theorem unrelatedAdapter_rejected (S : NestedSpec) (A : ArchiveAdapter)
    (h : A.family ≠ S.inner) : ¬ AdapterMatches S A :=
  fun hm => h hm.1

/-- An adapter whose reconstruction and OPE bases differ does not match. -/
theorem mismatchedBasis_rejected (S : NestedSpec) (A : ArchiveAdapter)
    (h : A.basisLabel ≠ A.portLabel) : ¬ AdapterMatches S A :=
  fun hm => h hm.2

/-- **C0's acceptance object**: one witness binds the specified manifest, the archive
adapter, and the observable/prior dictionary, with both compatibility proofs carried as
data.  No independently chosen family, basis, algebra or prior can be substituted
afterwards. -/
structure ContinuumWitness (n : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- the specified physical object. -/
  spec : NestedSpec
  /-- the archive adapter. -/
  adapter : ArchiveAdapter
  /-- the adapter is the specified object's adapter. -/
  compatible : AdapterMatches spec adapter
  /-- the observable/prior dictionary at the same regulator. -/
  dictionary : ObservableDictionary n Ω
  /-- the dictionary's half-space data is the manifest's, not a second choice. -/
  halfSpace_eq : dictionary.halfSpace = spec.halfSpace

namespace ContinuumWitness

variable {n : ℕ} {Ω : Type*} [Fintype Ω] (W : ContinuumWitness n Ω)

/-- The bound adapter family is the manifest's inner family. -/
theorem family_eq : W.adapter.family = W.spec.inner := W.compatible.1

/-- The bound reconstruction and OPE bases agree. -/
theorem basis_eq : W.adapter.basisLabel = W.adapter.portLabel := W.compatible.2

/-- The bound dictionary carries the manifest's positive-time algebra, not a copy. -/
theorem labels_mem_positiveTime (k : ℕ) :
    (W.spec.halfSpace.labels k).smearing ∈ PositiveTimeAlgebra :=
  W.spec.halfSpace.labels_mem_positiveTime k

/-- The witness's prior normalizes its one-point proposition. -/
theorem prior_prop_normalized (i : Fin n) (h : 0 < W.dictionary.prior.mass i) :
    W.dictionary.prior.expect (W.dictionary.prior.prop i) = 1 :=
  W.dictionary.prior_prop_normalized i h

/-- **A smearing outside the positive-time algebra cannot be relabelled into the
witness**: the dictionary's labels are the manifest's. -/
theorem label_outside_rejected (L : FieldLabel) (h : L.smearing ∉ W.spec.halfSpace.algebra)
    (k : ℕ) : W.spec.halfSpace.labels k ≠ L :=
  W.spec.halfSpace.label_outside_algebra_rejected L h k

/-- Two witnesses over the same manifest and the same basis labels carry the same family:
the witness, not a fresh existential, determines the archive side. -/
theorem family_unique {W W' : ContinuumWitness n Ω} (h : W.spec.inner = W'.spec.inner) :
    W.adapter.family = W'.adapter.family := by
  rw [family_eq W, family_eq W', h]

end ContinuumWitness

end BookProof.OSReconstruction.ContinuumManifest
