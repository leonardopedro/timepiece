import Mathlib
import BookProof.ChapterSmOuterFock
import BookProof.ChapterSmComparisonEsa
import BookProof.ChapterYangMillsNonAbelianEsa

/-!
# The Standard-Model Hamiltonian of record is essentially self-adjoint on the outer Fock space

`BookProof/ChapterSmComparisonEsa.lean` proves that the bosonic Standard-Model one-particle
Hamiltonian `h` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝ¹⁶³)`
(`sm_h_esa`); `BookProof/ChapterSmOuterFock.lean` builds the Hamiltonian of record
`smFockHam = dΓ(h)` on the nested Fock space `⊕ₙ L²(ℝ^{163n})` and gives it a Friedrichs
extension.  This module closes the enclosure step for the bosonic sector, in both spellings
of the enclosure:

* `smSectorHam_eq_weylPoly`, **`smSectorHam_esa`** — every particle-number sector
  `smSectorHam P n` (one copy of `h` per excitation) is a Weyl-type operator with momenta in
  distinct coordinates and real polynomial fields, hence essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝ^{163n})` by the Kato-type theorem
  (`BookProof.YangMillsNonAbelianEsa.weylPoly_esa`);
* **`smFockHam_esa`** — the Hamiltonian of record `smFockHam P` is essentially self-adjoint on
  the finite-particle core `smFockCore` (a direct sum of essentially self-adjoint blocks);
* **`sm_dGamma_esa`** — in the creation-left / annihilation-right spelling
  `dΓ(h) = Σ_{i,j} h_{ij} C†(e_i) A(e_j)` of the general second quantization,
  `dΓ(h)` is essentially self-adjoint on the finite-particle domain over the
  Gauss–polynomial core, by the lift `EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa`
  applied to `sm_h_esa`.

## Honest boundary

The inner operator is the **bosonic** sector (gauge fields, their spatial derivatives, the
Higgs doublet), exactly as in `BookProof.ChapterSmOuterFock`.  The Dirac and Yukawa terms act
on the finite-dimensional CAR algebra (`BookProof.ChapterSmDiracYukawa`) and are not part of
the operator enclosed here.  No spectral information and no mass gap is claimed.  The
Friedrichs certificate (`sm_dGamma_friedrichs_extension`) and the essential
self-adjointness proved here are independent statements.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.SmFockEsa

open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmOuterFock
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.TensorCore BookProof.SecondQuantizationCore
open BookProof.YangMillsNonAbelianEsa

noncomputable section

/-! ## 1. Every particle-number sector is essentially self-adjoint -/

/-- The coordinate carrying the `m`-th momentum of the `n`-particle sector. -/
def smSecMomIdx (n : ℕ) (m : Fin (n * 40)) : Fin (n * 163) :=
  scoord ((smMomFinN n).symm m).1 (smMomCoord ((smMomFinN n).symm m).2)

/-- The `r`-th field polynomial of the `n`-particle sector. -/
def smSecFieldPoly (P : SmParams) (n : ℕ) (r : Fin (n * 49)) : MvPolynomial (Fin (n * 163)) ℂ :=
  smFormPoly P (scoord ((smFormFinN n).symm r).1) ((smFormFinN n).symm r).2

/-- The `40n` momentum-carrying coordinates of the `n`-particle sector are pairwise distinct. -/
theorem smSecMomIdx_injective (n : ℕ) : Function.Injective (smSecMomIdx n) := by
  intro m m' h
  have h1 : (((smMomFinN n).symm m).1, smMomCoord ((smMomFinN n).symm m).2)
      = (((smMomFinN n).symm m').1, smMomCoord ((smMomFinN n).symm m').2) :=
    finProdFinEquiv.injective h
  have h2 : (smMomFinN n).symm m = (smMomFinN n).symm m' :=
    Prod.ext (Prod.ext_iff.1 h1).1 (BookProof.SmFarisLavine.smMomCoord_injective
      (Prod.ext_iff.1 h1).2)
  exact (smMomFinN n).symm.injective h2

/-- The `n`-particle Standard-Model Hamiltonian is a Weyl-type operator with polynomial
fields. -/
theorem smSectorHam_eq_weylPoly (P : SmParams) (n : ℕ) :
    smSectorHam P n = weylPoly (smSecMomIdx n) (smSecFieldPoly P n) := rfl

/-- **Every particle-number sector of the Standard-Model Hamiltonian of record is essentially
self-adjoint** on the Gauss–polynomial core of `L²(ℝ^{163n})`. -/
theorem smSectorHam_esa (P : SmParams) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 163)) (smSectorHam P n) := by
  rw [smSectorHam_eq_weylPoly]
  exact weylPoly_esa (smSecMomIdx_injective n) fun r => realCoeff_smFormPoly P _ _

/-! ## 2. The Hamiltonian of record -/

/-- **The (bosonic) Standard-Model Hamiltonian of record `smFockHam = dΓ(h)` is essentially
self-adjoint on the finite-particle core of the nested Fock space `⊕ₙ L²(ℝ^{163n})`.**  This
is the enclosure statement, for every choice of couplings, structure constants and
electroweak generators. -/
theorem smFockHam_esa (P : SmParams) :
    EssentiallySelfAdjointOn smFockCore (smFockHam P) :=
  dsOp_essentiallySelfAdjointOn _ fun n => smSectorHam_esa P n

/-- **The general second quantization of the Standard-Model one-particle Hamiltonian is
essentially self-adjoint.**  `dΓ(h) = Σ_{i,j} h_{ij} C†(e_i) A(e_j)` — the bosonic
one-particle Hamiltonian enclosed between a creation on the left and an annihilation on the
right — is essentially self-adjoint on the finite-particle domain built from the
Gauss–polynomial core of `L²(ℝ¹⁶³)`. -/
theorem sm_dGamma_esa (P : SmParams) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore (L2dSpace 163) (polyGaussCore (d := 163))
        (polyGaussCore (d := 163)) n))
      (dGammaCoreOp (L2dSpace 163) (polyGaussCore (d := 163))
        (smHamiltonian P) (polyGaussCore (d := 163))) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := L2dSpace 163)
    (smHamiltonian P) polyGaussCore_dense (smHamiltonian_symmetricOn P)
    (BookProof.SmComparisonEsa.sm_h_esa P)

end

end BookProof.SmFockEsa
