import Mathlib
import BookProof.ChapterNavierStokesLagrangianCanonical
import BookProof.ChapterNsLagrangianDetFarisLavine
import BookProof.ChapterFockStatisticsEsa
import BookProof.ChapterFockStatisticsCompletion
import BookProof.ChapterYangMillsNonAbelianEsa

/-!
# The Lagrangian Navier–Stokes one-particle Hamiltonian on the outer Fock space

The project already proves essential self-adjointness (ESA) of the Lagrangian
(parcel/trajectory) one-particle Hamiltonian:

* `LagrangianCanonical.lagCan_esa` — **unconditional.**  One parcel, trajectory space
  `ℓ²(Fin 3 → ℕ)` (the Hermite/occupation realization of `L²(ℝ³)`), operator
  `h = ½ Σᵢ Pᵢ² + ν Σᵢ Qᵢ² + Σᵢ fᵢ Pᵢ` on the finite-mode (Hermite) core, for every `ν > 0`
  and every constant force `f ∈ ℝ³`.  Proof: the second-order part is `ω(N + 3/2)`,
  `ω = √(2ν)`, diagonal in the Hermite basis, hence ESA; the drift `f·P` is Kato–Rellich
  bounded with relative bound `< 1`.

* `NsLagrangianDetFL.lagKoopman_esa_of_comparison_esa` — **conditional.**  Galerkin Lagrangian
  NS with the exact determinant constraint (penalty `V_κ`); ESA of the Koopman generator
  `H_L` follows *if* the comparison operator `N_L = H_L² + E` is ESA.

This module carries both statements to the outer Fock space with the general second
quantization theorems of the project:

* `EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa` — if `A` is symmetric and ESA on a
  dense `D`, then `dΓ(A)` is ESA on the finite-particle domain `𝓕_fin(D)`
  (algebraic direct sum over `n` of the algebraic tensor powers `D^{⊗n}`);
* `FockStatistics.bosonicFock_esa` / `fermionicFock_esa` and the Hilbert-space versions
  `hbosonicFock_esa` / `hfermionicFock_esa` — the same on the symmetric / antisymmetric Fock
  spaces.

No new hypothesis enters: for `lagCan` the results are unconditional, and for the Koopman
generator they inherit exactly the hypothesis on `N_L`.

## Scope

`dΓ(h)` is the *non-interacting* (number-conserving, one-body) outer Hamiltonian
`Σ_{ij} h_{ij} a†_i a_j`: on the `n`-parcel sector it acts as
`Σ_p 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1`.  The parcel–parcel couplings of the gauge-fixed models
(`ChapterNavierStokesFullLagrangianFock`) are not of this form and are not covered.

Nothing is assumed: no `axiom`, no `sorry`.
-/

namespace BookProof.NsLagrangianOuterFock

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.FockStatistics BookProof.PermSector BookProof.ReducedEsa
open BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsNonAbelianEsa
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianCanonical
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.IkebeKato

noncomputable section

/-! ## 1. The unconditional case: the canonical Lagrangian parcel Hamiltonian -/

/-- The one-parcel trajectory space `ℓ²(Fin 3 → ℕ)`, bundled as a Hilbert space. -/
def lagOneSpace : IPSpace := ⟨L2I Vel⟩

instance : CompleteSpace lagOneSpace.carrier :=
  inferInstanceAs (CompleteSpace (L2I Vel))

/-- **The Lagrangian one-particle (one-parcel) Hamiltonian**
`h = ½ Σᵢ Pᵢ² + ν Σᵢ Qᵢ² + Σᵢ fᵢ Pᵢ` on the finite-mode (Hermite) core of `ℓ²(Fin 3 → ℕ)`. -/
def lagOneOp (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    lpFiniteModes Vel →ₗ[ℂ] lagOneSpace.carrier :=
  lagrangianCore (lagCanData nu hnu f)

theorem lagOneOp_symmetricOn (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    SymmetricOn (lpFiniteModes Vel) (lagOneOp nu hnu f) :=
  lagrangianCore_symmetricOn (lagCanData nu hnu f)

/-- The one-particle statement (restated from `lagCan_esa`). -/
theorem lagOneOp_esa (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Vel) (lagOneOp nu hnu f) :=
  lagCan_esa nu hnu f

theorem lagOne_dense :
    Dense ((lpFiniteModes Vel : Submodule ℂ (L2I Vel)) : Set (L2I Vel)) :=
  lpFiniteModes_dense

/-- **`dΓ(h)` for the Lagrangian parcel Hamiltonian is essentially self-adjoint on the
finite-particle domain of the outer Fock space** (creation left / annihilation right,
no symmetrization), built from the Hermite core of one parcel.  Unconditional: `ν > 0`,
`f ∈ ℝ³` arbitrary. -/
theorem lagOne_dGamma_esa (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore lagOneSpace (lpFiniteModes Vel)
        (lpFiniteModes Vel) n))
      (dGammaCoreOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)
        (lpFiniteModes Vel)) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := lagOneSpace)
    (lagOneOp nu hnu f) lagOne_dense (lagOneOp_symmetricOn nu hnu f) (lagOneOp_esa nu hnu f)

/-- `dΓ(h)` is symmetric on the same finite-particle domain. -/
theorem lagOne_dGamma_symmetricOn (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    SymmetricOn
      (dsCore (fun n : ℕ => fockSectorCore lagOneSpace (lpFiniteModes Vel)
        (lpFiniteModes Vel) n))
      (dGammaCoreOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)
        (lpFiniteModes Vel)) :=
  EsaOneParticle.symmetricOn_dGammaCoreOp_of_esa (Hs := lagOneSpace)
    (lagOneOp nu hnu f) (lagOneOp_symmetricOn nu hnu f)

/-- **`dΓ(h)` is essentially self-adjoint on the bosonic (symmetric) outer Fock space**
(algebraic direct sum of the symmetric sectors over the one-parcel core). -/
theorem lagOne_bosonicFock_esa (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (bosonicFockDom lagOneSpace (lpFiniteModes Vel))
      (bosonicFockOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)) :=
  bosonicFock_esa (Hs := lagOneSpace) (lagOneOp nu hnu f) lagOne_dense
    (lagOneOp_symmetricOn nu hnu f) (lagOneOp_esa nu hnu f)

/-- **`dΓ(h)` is essentially self-adjoint on the fermionic (antisymmetric) outer Fock
space.** -/
theorem lagOne_fermionicFock_esa (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (fermionicFockDom lagOneSpace (lpFiniteModes Vel))
      (fermionicFockOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)) :=
  fermionicFock_esa (Hs := lagOneSpace) (lagOneOp nu hnu f) lagOne_dense
    (lagOneOp_symmetricOn nu hnu f) (lagOneOp_esa nu hnu f)

/-- **`dΓ(h)` is essentially self-adjoint on the bosonic outer Fock space as a Hilbert
space** (Hilbert direct sum of the completed symmetric sectors). -/
theorem lagOne_hbosonicFock_esa (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (hbosonicFockDom lagOneSpace (lpFiniteModes Vel))
      (hbosonicFockOp lagOneSpace (lpFiniteModes Vel) (lagOneOp nu hnu f)) :=
  hbosonicFock_esa (Hs := lagOneSpace) (lagOneOp nu hnu f) lagOne_dense
    (lagOneOp_symmetricOn nu hnu f) (lagOneOp_esa nu hnu f)

/-! ## 2. The conditional case: the Lagrangian Koopman generator with the determinant -/

section Koopman

open BookProof.NsLagrangianDetFL

variable {K : Type*} [Fintype K] (S : LagNsData K)

/-- **Conditional outer-Fock statement for the Lagrangian Koopman generator `H_L`** (exact
determinant constraint via the penalty `V_κ`): if the comparison operator `N_L = H_L² + E` is
essentially self-adjoint on the Gauss–polynomial core, then `dΓ(H_L)` is essentially
self-adjoint on the finite-particle domain.  The hypothesis is the same as in
`lagKoopman_esa_of_comparison_esa`; nothing else is assumed. -/
theorem lagKoopman_dGamma_esa_of_comparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore (L2dSpace (lagDim K))
        (polyGaussCore (d := lagDim K)) (polyGaussCore (d := lagDim K)) n))
      (dGammaCoreOp (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K))
        (lagKoopmanOp S) (polyGaussCore (d := lagDim K))) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := L2dSpace (lagDim K))
    (lagKoopmanOp S) polyGaussCore_dense (lagKoopmanOp_symmetricOn S)
    (lagKoopman_esa_of_comparison_esa S hN)

/-- The bosonic version of the conditional statement. -/
theorem lagKoopman_bosonicFock_esa_of_comparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) :
    EssentiallySelfAdjointOn (bosonicFockDom (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K)))
      (bosonicFockOp (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K)) (lagKoopmanOp S)) :=
  bosonicFock_esa (Hs := L2dSpace (lagDim K)) (lagKoopmanOp S) polyGaussCore_dense
    (lagKoopmanOp_symmetricOn S) (lagKoopman_esa_of_comparison_esa S hN)

end Koopman

end

end BookProof.NsLagrangianOuterFock
