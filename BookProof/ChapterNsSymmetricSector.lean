import Mathlib
import BookProof.ChapterNsOneBodyDGamma
import BookProof.ChapterNsReducedCoreEsa
import BookProof.ChapterFockStatisticsEsa
import BookProof.ChapterFockStatisticsCompletion

/-!
# The Navier–Stokes one-body generator on the symmetric (bosonic) Fock sectors

The NS instance of the symmetrization machinery (work order step “NS symmetrization” of
`CONSOLIDATED_PLAN.md`).  The one-body generator of the Fourier-eliminated Eulerian sector,
`H_sp = ½ Σ_{m<6} π_m² + ½ Σ_{r<7} (mulOp Φ_r)²` (`NsOneBody.spHam`, advection included), acts on
the Gauss–polynomial core of `L²(ℝ⁶)`.  Here:

* `spHam_eq_weylPoly` (by `rfl`), **`spHam_esa`** — `H_sp` is essentially self-adjoint on
  `polyGaussCore 6` (one-particle statement), by the Kato-type theorem
  `YangMillsNonAbelianEsa.weylPoly_esa`;
* **`nsSp_bosonic_core_esa`** — for every particle number `n`, the `n`-parcel derivation
  `Σ_p 1 ⊗ ⋯ ⊗ H_sp ⊗ ⋯ ⊗ 1` reduced to the **symmetric** tensor power (the image of the
  permutation average `bosonicProj`, the permutation representation `permRep` commuting with
  the derivation and preserving `polyGaussCore^{⊗n}`) is essentially self-adjoint on the
  symmetrized tensor power of the core — `PermSector.essentiallySelfAdjointOn_bosonic_core`
  instantiated for NS;
* **`nsSp_bosonicFock_esa`**, **`nsSp_hbosonicFock_esa`** — `dΓ(H_sp)` is essentially
  self-adjoint on the bosonic Fock space over `polyGaussCore 6` (algebraic direct sum of the
  symmetric sectors, and Hilbert direct sum of their completions);
* **`nsSp_dGamma_esa`** — the unsymmetrized enclosure `dΓ(H_sp)` (creation left / annihilation
  right, `dGammaCoreOp`) is essentially self-adjoint on the finite-particle domain.

## Honest boundary

The statements are in the `IPSpace` tensor-power spelling of the second quantization.  The
unitary identification of the `n`-parcel space `L²(ℝ^{6n})` of `nsRedFullFockHam` with the
`n`-fold tensor power of `L²(ℝ⁶)`, and the identification with the `ℓ²`-spelling
`dGammaOp (nsSpCol e ν k)` of `ChapterNsOneBodyDGamma`, are not proved here.  The operator is
the positive sum-of-squares generator; the mainstream Koopman generator is never enclosed.  No
mass gap, uniqueness or global-existence statement is made.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.NsSymmetricSector

open scoped TensorProduct
open BookProof.NsOneBody BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.GraphCore
open BookProof.TensorCore BookProof.FockStatistics BookProof.PermSector BookProof.ReducedEsa
open BookProof.GroupAverage BookProof.TensorPerm
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.YangMillsNonAbelianEsa

noncomputable section

/-- The one-body generator is a Weyl-type operator with the seven one-parcel forms. -/
theorem spHam_eq_weylPoly (nu : ℝ) (k : Fin 3 → ℝ) :
    spHam (coreRepPoly 6) nu k = weylPoly (id : Fin 6 → Fin 6) (spFormPoly nu k) := rfl

/-- **The NS one-body generator `H_sp` (advection included) is essentially self-adjoint** on
the Gauss–polynomial core of `L²(ℝ⁶)`, for every viscosity and wave vector. -/
theorem spHam_esa (nu : ℝ) (k : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 6)) (spHam (coreRepPoly 6) nu k) := by
  rw [spHam_eq_weylPoly]
  exact weylPoly_esa Function.injective_id fun r => realCoeff_spFormPoly nu k r

/-- The one-body generator as an operator into the bundled space `L²(ℝ⁶)`. -/
def nsSpOp (nu : ℝ) (k : Fin 3 → ℝ) :
    polyGaussCore (d := 6) →ₗ[ℂ] (L2dSpace 6).carrier :=
  spHam (coreRepPoly 6) nu k

theorem nsSpOp_symmetricOn (nu : ℝ) (k : Fin 3 → ℝ) :
    SymmetricOn (polyGaussCore (d := 6)) (nsSpOp nu k) :=
  spHam_symmetricOn (coreRepPoly 6) nu k

theorem nsSpOp_esa (nu : ℝ) (k : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 6)) (nsSpOp nu k) :=
  spHam_esa nu k

/-- **The `n`-parcel NS derivation on the symmetric tensor power is essentially
self-adjoint on the symmetrized core** `bosonicProj (polyGaussCore^{⊗n})`. -/
theorem nsSp_bosonic_core_esa (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn
      (redDom (bosonicProj (L2dSpace 6) n)
        (sectorCore (L2dSpace 6) (polyGaussCore (d := 6)) (polyGaussCore (d := 6)) n))
      (bosonicCoreOp (L2dSpace 6) (polyGaussCore (d := 6)) (nsSpOp nu k)
        (polyGaussCore (d := 6)) n) :=
  essentiallySelfAdjointOn_bosonic_core_of_esa (Hs := L2dSpace 6) (nsSpOp nu k)
    polyGaussCore_dense (nsSpOp_symmetricOn nu k) (nsSpOp_esa nu k) (IsGraphCore.refl _) n

/-- **`dΓ(H_sp)` is essentially self-adjoint on the bosonic Fock space** over the
Gauss–polynomial core (algebraic direct sum of the symmetric sectors). -/
theorem nsSp_bosonicFock_esa (nu : ℝ) (k : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (bosonicFockDom (L2dSpace 6) (polyGaussCore (d := 6)))
      (bosonicFockOp (L2dSpace 6) (polyGaussCore (d := 6)) (nsSpOp nu k)) :=
  bosonicFock_esa (Hs := L2dSpace 6) (nsSpOp nu k) polyGaussCore_dense
    (nsSpOp_symmetricOn nu k) (nsSpOp_esa nu k)

/-- **`dΓ(H_sp)` is essentially self-adjoint on the bosonic Fock space as a Hilbert space**
(Hilbert direct sum of the completed symmetric sectors). -/
theorem nsSp_hbosonicFock_esa (nu : ℝ) (k : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (hbosonicFockDom (L2dSpace 6) (polyGaussCore (d := 6)))
      (hbosonicFockOp (L2dSpace 6) (polyGaussCore (d := 6)) (nsSpOp nu k)) :=
  hbosonicFock_esa (Hs := L2dSpace 6) (nsSpOp nu k) polyGaussCore_dense
    (nsSpOp_symmetricOn nu k) (nsSpOp_esa nu k)

/-- **The enclosure `dΓ(H_sp)`** (creation left / annihilation right, general second
quantization) is essentially self-adjoint on the finite-particle domain over
`polyGaussCore 6`. -/
theorem nsSp_dGamma_esa (nu : ℝ) (k : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore (L2dSpace 6) (polyGaussCore (d := 6))
        (polyGaussCore (d := 6)) n))
      (dGammaCoreOp (L2dSpace 6) (polyGaussCore (d := 6)) (nsSpOp nu k)
        (polyGaussCore (d := 6))) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := L2dSpace 6) (nsSpOp nu k)
    polyGaussCore_dense (nsSpOp_symmetricOn nu k) (nsSpOp_esa nu k)

end

end BookProof.NsSymmetricSector
