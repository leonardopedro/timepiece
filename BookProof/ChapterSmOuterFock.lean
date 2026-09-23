import Mathlib
import BookProof.ChapterSmHamiltonian
import BookProof.ChapterYangMillsFockFriedrichs

/-!
# The Standard Model Hamiltonian of record: the outer second quantization `dΓ(h)`

Step 4 of the Standard-Model work order of `CONSOLIDATED_PLAN.md` (§D6b-SM.4), in the
enclosure spelling of the Hamiltonian doctrine (§B of the 2026-09-22c state section): the
**final Hamiltonian of record is the outer second quantization of the one-particle
operator**, never the bare one-particle operator.  For the Standard Model that is

```
H = dΓ(h) :  ⊕ₙ L²(ℝ^{163 n}) → ⊕ₙ L²(ℝ^{163 n}),
```

one copy of the bosonic one-particle operator `h` of `BookProof.ChapterSmHamiltonian` per
excitation, in every particle-number sector.  A statement about the bare `h` is a
*one-particle* statement and is labelled as such there.

The route is the one the doctrine prescribes for an inner operator that is **bounded
below**: the Standard-Model `h` is a positive sum of squares — the three magnetic energies
(non-abelian included), the covariant Higgs kinetic energy and the Higgs wall — so the
Friedrichs extension applies directly, exactly as for Yang–Mills
(`BookProof.YmFockFriedrichs`), and no Faris–Lavine commutator certificate is needed.  Both
ingredients — symmetry and positivity of the quadratic form — are fibrewise, so they lift
from `L²(ℝ¹⁶³)` to the nested Fock space.

## What is proved

* `smSectorHam` — the `n`-particle Standard-Model Hamiltonian on the Gauss–polynomial core
  of `L²(ℝ^{163n})`: the `40n` momenta and the `49n` squared forms, one copy per
  excitation; `smSectorHam_symmetricOn`, `smSectorHam_quadForm_nonneg`,
  `smSector_friedrichs_extension`;
* `smFockSpace`, `smFockCore`, `smFockCore_dense`, **`smFockHam`** — the Hamiltonian of
  record on the nested Fock space and its finite-particle core;
* `smFockHam_symmetricOn`, `smFockHam_quadForm_nonneg`,
  **`sm_dGamma_friedrichs_extension`** — the enclosed Hamiltonian is symmetric, bounded
  below, and has a positive self-adjoint (Friedrichs) extension;
* `sm_dGamma_stone_flow` — the unitary time evolution it generates;
* `smFockHam_sector`, `smFockHam_number_conserving` — the enclosure is block diagonal in
  the particle number, and its restriction to the `n`-particle sector is the `n`-particle
  Hamiltonian.

## Honest boundary

As in `BookProof.ChapterSmHamiltonian`: the inner operator is the **bosonic** sector
(gauge fields, their spatial derivatives, the Higgs doublet).  The Dirac and Yukawa terms
require the CAR/Grassmann algebra and are not enclosed here; the CKM/PMNS unitarity algebra
they rest on is `BookProof.ChapterSmOneParticle`.  No spectral information, no electroweak
symmetry breaking as dynamics, and no mass gap is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmOuterFock

open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The coordinates of the `n`-particle sector -/

/-- The global coordinate of the `i`-th field-space direction of the `p`-th excitation. -/
def scoord {n : ℕ} (p : Fin n) (i : Fin 163) : Fin (n * 163) := finProdFinEquiv (p, i)

/-- The `40n` momentum labels of the `n`-particle sector. -/
def smMomFinN (n : ℕ) : (Fin n × SmMom) ≃ Fin (n * 40) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) smMomFin).trans finProdFinEquiv

/-- The `49n` form labels of the `n`-particle sector. -/
def smFormFinN (n : ℕ) : (Fin n × SmForm) ≃ Fin (n * 49) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) smFormFin).trans finProdFinEquiv

/-! ## 2. The `n`-particle Hamiltonian -/

/-- The momentum operators of the `n`-particle sector: the `40` momenta of each of the `n`
excitations. -/
def smSecPi (n : ℕ) (m : Fin (n * 40)) :
    (polyGaussCore (d := n * 163)) →ₗ[ℂ] (polyGaussCore (d := n * 163)) :=
  (coreRepPoly (n * 163)).op
    (momOp (scoord ((smMomFinN n).symm m).1 (smMomCoord ((smMomFinN n).symm m).2)))

/-- The field operators of the `n`-particle sector: multiplication by the `49` real field
polynomials of each of the `n` excitations. -/
def smSecField (P : SmParams) (n : ℕ) (r : Fin (n * 49)) :
    (polyGaussCore (d := n * 163)) →ₗ[ℂ] (polyGaussCore (d := n * 163)) :=
  (coreRepPoly (n * 163)).op
    (mulOp (smFormPoly P (scoord ((smFormFinN n).symm r).1) ((smFormFinN n).symm r).2))

theorem smSecPi_symmetricOn (n : ℕ) (m : Fin (n * 40)) :
    SymmetricOn (polyGaussCore (d := n * 163))
      ((polyGaussCore (d := n * 163)).subtype.comp (smSecPi n m)) :=
  (coreRepPoly (n * 163)).symmetricOn_op (momOp_polySym _)

theorem smSecField_symmetricOn (P : SmParams) (n : ℕ) (r : Fin (n * 49)) :
    SymmetricOn (polyGaussCore (d := n * 163))
      ((polyGaussCore (d := n * 163)).subtype.comp (smSecField P n r)) :=
  (coreRepPoly (n * 163)).symmetricOn_op (mulOp_polySym (realCoeff_smFormPoly P _ _))

/-- **The `n`-particle Standard-Model Hamiltonian** on the Gauss–polynomial core of
`L²(ℝ^{163n})`: the kinetic term of every excitation, the full magnetic energy of every
excitation (quartic in the non-abelian case), the covariant Higgs kinetic energy and the
Higgs wall of every excitation. -/
def smSectorHam (P : SmParams) (n : ℕ) :
    (polyGaussCore (d := n * 163)) →ₗ[ℂ] L2d (n * 163) :=
  weylOp (smSecPi n) (smSecField P n)

theorem smSectorHam_symmetricOn (P : SmParams) (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 163)) (smSectorHam P n) :=
  weylOpDom_symmetricOn (smSecPi_symmetricOn n) (smSecField_symmetricOn P n)

/-- **The `n`-particle Standard-Model Hamiltonian is bounded below** — its quadratic form is
a sum of squares. -/
theorem smSectorHam_quadForm_nonneg (P : SmParams) (n : ℕ)
    (x : polyGaussCore (d := n * 163)) : 0 ≤ quadForm (smSectorHam P n) x :=
  weylOpDom_quadForm_nonneg (smSecPi_symmetricOn n) (smSecField_symmetricOn P n) x

/-- **Every particle-number sector has a positive self-adjoint (Friedrichs) extension.** -/
theorem smSector_friedrichs_extension (P : SmParams) (n : ℕ) :
    ∃ (Dom : Submodule ℂ (L2d (n * 163))) (A : Dom →ₗ[ℂ] L2d (n * 163)),
      IsPositiveSelfAdjointExtension (smSectorHam P n) A :=
  friedrichs_extension_exists
    ⟨polyGaussCore, smSectorHam P n, smSectorHam_symmetricOn P n,
      smSectorHam_quadForm_nonneg P n⟩
    polyGaussCore_dense

/-! ## 3. The nested Fock space and the Hamiltonian of record -/

/-- The nested Fock space `⊕ₙ L²(ℝ^{163n})` of the Standard-Model excitations. -/
abbrev smFockSpace := lp (fun n : ℕ => L2d (n * 163)) 2

/-- The finite-particle core: finitely many sectors, each in its Gauss–polynomial core. -/
def smFockCore : Submodule ℂ smFockSpace := dsCore (fun n : ℕ => polyGaussCore (d := n * 163))

theorem smFockCore_dense :
    Dense ((smFockCore : Submodule ℂ smFockSpace) : Set smFockSpace) :=
  dsCore_dense fun _ => polyGaussCore_dense

/-- **The Standard-Model Hamiltonian of record**: the outer second quantization `dΓ(h)` of
the one-particle operator `h`, one copy per excitation in every number sector. -/
def smFockHam (P : SmParams) : smFockCore →ₗ[ℂ] smFockSpace :=
  dsOp (fun n : ℕ => smSectorHam P n)

theorem smFockHam_symmetricOn (P : SmParams) :
    SymmetricOn smFockCore (smFockHam P) :=
  dsOp_symmetricOn _ fun n => smSectorHam_symmetricOn P n

/-- **The enclosed Standard-Model Hamiltonian is bounded below**: positivity is fibrewise,
so it lifts from the one-particle Hilbert space to the nested Fock space. -/
theorem smFockHam_quadForm_nonneg (P : SmParams) (x : smFockCore) :
    0 ≤ quadForm (smFockHam P) x :=
  dsOp_quadForm_nonneg _ (fun n u => smSectorHam_quadForm_nonneg P n u) x

/-- **The Standard-Model Hamiltonian of record has a positive self-adjoint (Friedrichs)
extension.**  This is the enclosure statement: the operator is `dΓ(h)` on the nested Fock
space, not the bare one-particle `h`. -/
theorem sm_dGamma_friedrichs_extension (P : SmParams) :
    ∃ (Dom : Submodule ℂ smFockSpace) (A : Dom →ₗ[ℂ] smFockSpace),
      IsPositiveSelfAdjointExtension (smFockHam P) A :=
  friedrichs_extension_exists
    ⟨smFockCore, smFockHam P, smFockHam_symmetricOn P, smFockHam_quadForm_nonneg P⟩
    smFockCore_dense

set_option maxHeartbeats 1000000 in
-- unfolding the `lp` instances of the Fock space in the Stone construction exceeds the
-- default budget
/-- **The unitary time evolution generated by the Standard-Model Hamiltonian of record.** -/
theorem sm_dGamma_stone_flow (P : SmParams) :
    ∃ (T : UnboundedSelfAdjoint smFockSpace) (U : ℝ → (smFockSpace →L[ℂ] smFockSpace)),
      IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ := sm_dGamma_friedrichs_extension P
  obtain ⟨T, U, _, _, hflow⟩ := exists_stone_flow_of_positive smFockCore_dense hA
  exact ⟨T, U, hflow⟩

/-! ## 4. Particle-number conservation -/

/-- The restriction of the enclosed Hamiltonian to the `n`-particle sector is the
`n`-particle Hamiltonian. -/
theorem smFockHam_sector (P : SmParams) (x : smFockCore) (n : ℕ) :
    ((smFockHam P x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n
      = smSectorHam P n ⟨((x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n, x.2.2 n⟩ := rfl

/-- **The Standard-Model Hamiltonian of record conserves the particle number**: it is block
diagonal in the number sectors. -/
theorem smFockHam_number_conserving (P : SmParams) (x : smFockCore)
    {n : ℕ} (hx : ∀ m, m ≠ n → ((x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0) (m : ℕ)
    (hm : m ≠ n) : ((smFockHam P x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0 :=
  BookProof.Qg3DGaugeFL.dsOp_number_conserving _ x hx m hm

end

end BookProof.SmOuterFock
