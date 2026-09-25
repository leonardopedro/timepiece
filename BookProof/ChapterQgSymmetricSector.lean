import Mathlib
import BookProof.ChapterQgVielbeinScalaronGaugeFL
import BookProof.ChapterFockStatisticsEsa
import BookProof.ChapterFockStatisticsCompletion
import BookProof.ChapterEsaOneParticleDGamma

/-!
# The complete gauge-fixed quantum-gravity Hamiltonian on the symmetrized cores

The QG `secCore` spelling of the work order in `CONSOLIDATED_PLAN.md`.
`BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_core_fl` proves that the complete gauge-fixed
quantum-gravity one-particle Hamiltonian `secHam W (qgFullModes g)` — vielbein/torsion kinetic
terms, the exact exponential Einstein-frame wall `W` (no Taylor truncation) and the
scalaron–vielbein interaction terms — is essentially self-adjoint on the finite-particle core
`secCore` of `Sec GMode = ℓ²(GMode; L²(ℝ))`.  Here that one-particle statement is carried to
the enclosures:

* **`qgFull_bosonic_core_esa`** — for every particle number `n`, the `n`-particle derivation of
  `secHam` reduced to the **symmetric** tensor power is essentially self-adjoint on the
  symmetrized tensor power of `secCore` (`PermSector.essentiallySelfAdjointOn_bosonic_core`);
* **`qgFull_bosonicFock_esa`**, **`qgFull_hbosonicFock_esa`** — `dΓ(secHam)` is essentially
  self-adjoint on the bosonic Fock space over `secCore` (algebraic, and Hilbert, direct sum of
  the symmetric sectors);
* **`qgFull_dGamma_esa`** — the unsymmetrized enclosure `dΓ(secHam)` (creation left /
  annihilation right, `dGammaCoreOp`) is essentially self-adjoint on the finite-particle domain
  over `secCore`.

No transfer to a Gauss–polynomial core is used or needed: the one-particle core is `secCore`,
built from `C_c^∞` fibres, which is where `qgFull_esa_core_fl` holds.

## Honest boundary

Only the operator `secHam W (qgFullModes g)` of `ChapterQgVielbeinScalaronGaugeFL` is treated;
the 84-dimensional `qg3DHamiltonian` with the Weyl-ordered cross terms (QG-3.2(a)/(b)) is not.
No spectral information and no mass gap is claimed.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.QgSymmetricSector

open scoped TensorProduct
open BookProof.ScalaronOuterFockFL BookProof.QgVielbeinModeInstance
open BookProof.QgContinuumModeInstance BookProof.QgVielbeinScalaronGaugeFL
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.FockStatistics
open BookProof.PermSector BookProof.ReducedEsa BookProof.GroupAverage BookProof.TensorPerm
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore BookProof.ScalaronFiberFL

noncomputable section

/-- The one-particle space `Sec GMode = ℓ²(GMode; L²(ℝ))`, bundled. -/
def qgSecSpace : IPSpace := ⟨Sec GMode⟩

instance : CompleteSpace qgSecSpace.carrier := inferInstanceAs (CompleteSpace (Sec GMode))

/-- The complete gauge-fixed QG one-particle Hamiltonian, as an operator into the bundled
space. -/
def qgFullOp (W : WallPot) (g : ℝ) : secCore (ι := GMode) →ₗ[ℂ] qgSecSpace.carrier :=
  secHam W (qgFullModes g)

theorem qgFullOp_symmetricOn (W : WallPot) (g : ℝ) :
    SymmetricOn (secCore (ι := GMode)) (qgFullOp W g) :=
  secHam_symmetricOn W _

theorem qgFullOp_esa (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (secCore (ι := GMode)) (qgFullOp W g) :=
  qgFull_esa_core_fl W g

/-- **The `n`-particle derivation of the complete QG Hamiltonian on the symmetric tensor
power is essentially self-adjoint on the symmetrized core** `bosonicProj (secCore^{⊗n})`. -/
theorem qgFull_bosonic_core_esa (W : WallPot) (g : ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn
      (redDom (bosonicProj qgSecSpace n)
        (sectorCore qgSecSpace (secCore (ι := GMode)) (secCore (ι := GMode)) n))
      (bosonicCoreOp qgSecSpace (secCore (ι := GMode)) (qgFullOp W g)
        (secCore (ι := GMode)) n) :=
  essentiallySelfAdjointOn_bosonic_core_of_esa (Hs := qgSecSpace) (qgFullOp W g)
    secCore_dense (qgFullOp_symmetricOn W g) (qgFullOp_esa W g) (IsGraphCore.refl _) n

/-- **`dΓ` of the complete QG Hamiltonian is essentially self-adjoint on the bosonic Fock
space** over `secCore` (algebraic direct sum of the symmetric sectors). -/
theorem qgFull_bosonicFock_esa (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (bosonicFockDom qgSecSpace (secCore (ι := GMode)))
      (bosonicFockOp qgSecSpace (secCore (ι := GMode)) (qgFullOp W g)) :=
  bosonicFock_esa (Hs := qgSecSpace) (qgFullOp W g) secCore_dense
    (qgFullOp_symmetricOn W g) (qgFullOp_esa W g)

/-- **The same on the bosonic Fock space as a Hilbert space** (Hilbert direct sum of the
completed symmetric sectors). -/
theorem qgFull_hbosonicFock_esa (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (hbosonicFockDom qgSecSpace (secCore (ι := GMode)))
      (hbosonicFockOp qgSecSpace (secCore (ι := GMode)) (qgFullOp W g)) :=
  hbosonicFock_esa (Hs := qgSecSpace) (qgFullOp W g) secCore_dense
    (qgFullOp_symmetricOn W g) (qgFullOp_esa W g)

/-- **The enclosure `dΓ(h)` of the complete QG Hamiltonian** (creation left / annihilation
right, general second quantization) is essentially self-adjoint on the finite-particle domain
over `secCore`. -/
theorem qgFull_dGamma_esa (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore qgSecSpace (secCore (ι := GMode))
        (secCore (ι := GMode)) n))
      (dGammaCoreOp qgSecSpace (secCore (ι := GMode)) (qgFullOp W g)
        (secCore (ι := GMode))) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := qgSecSpace) (qgFullOp W g)
    secCore_dense (qgFullOp_symmetricOn W g) (qgFullOp_esa W g)

end

end BookProof.QgSymmetricSector
