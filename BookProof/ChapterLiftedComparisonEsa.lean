import Mathlib
import BookProof.Ns.ChapterNsComparisonEsa
import BookProof.ChapterEsaRealShift

/-!
# NS-L-C.3 — the lifted comparison operator `dΓ(N) + 1` is essentially self-adjoint on the
finite-particle core

`CONSOLIDATED_PLAN.md` §"2026-10-15b", row NS-L-C.3 (toolbox §5, row D6b): the analytic
counterpart of the finite-dimensional shadow checked by the `pl_lifted_*` assertions
(Hermitian; form `≥ m + 1`; resolvent bound `‖(A − z)⁻¹‖ ≤ 1/|Im z|`, i.e. trivial
deficiency).

The three steps of the plan:

1. **comparison ESA on the core** — `comparison_esa_on_core`: the completed-square comparison
   operator `N = ½Σ(Pᵢ + fᵢ)² + νΣQᵢ²` of the canonical Lagrangian parcel Hamiltonian is
   essentially self-adjoint on the Hermite (finite-mode) core of `ℓ²(Fin 3 → ℕ)`
   (`BookProof.NsComparisonEsa.lagCompN_esa`).  In the canonical realization the
   Gauss–polynomial core of the plan *is* the Hermite core (finite linear combinations of the
   Hermite states `e_β`, the occupation-number realization of Gaussians times polynomials).
2. **lift** — `liftedComparison_dGamma_esa`: `dΓ(N)` is essentially self-adjoint on the
   finite-particle domain `𝓕_fin(D)` of the outer Fock space built from that core, by the
   second-quantization theorem `EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa`.
3. **the `+1`** — **`liftedComparison_esa`**: `dΓ(N) + 1` is essentially self-adjoint on
   `𝓕_fin(D)`, by the shift lemma `EsaRealShift.essentiallySelfAdjointOn_add_const` (the
   outer Fock space is complete).  Together with `liftedComparison_symmetricOn` (Hermitian)
   and the one-particle form bound `NsComparisonEsa.lagCompN_add_one_ge` (form `≥ 1`).

`liftedComparison_resolvent_deficiency` records the "resolvent bound ⇒ deficiency trivial"
shadow in its analytic form: the deficiency spaces of `dΓ(N) + 1` vanish at **every**
non-real `z`.

For the Koopman–von Neumann comparison `N_L = H_L² + E` of the Galerkin Lagrangian flow,
`lagKoopman_liftedComparison_esa_of_comparison_esa` gives the same conclusion *under the
explicit hypothesis* that `N_L` is ESA on the Gauss–polynomial core — that hypothesis is not
discharged here (see the boundary of `ChapterNsComparisonEsa`).
-/

namespace BookProof.LiftedComparisonEsa

open BookProof.FarisLavine BookProof.SecondQuantizationCore BookProof.DirectSumEsa
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianCanonical
  BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NsLagrangianOuterFock BookProof.NsComparisonEsa BookProof.EsaRealShift

noncomputable section

variable (nu : ℝ)

/-- The completed-square comparison operator, as a one-particle operator of the parcel
space `lagOneSpace`. -/
def compOneOp (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    lpFiniteModes Vel →ₗ[ℂ] lagOneSpace.carrier :=
  lagCompN nu hnu f

/-- **Step 1.**  `N` is essentially self-adjoint on the Hermite core. -/
theorem comparison_esa_on_core (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Vel) (compOneOp nu hnu f) :=
  lagCompN_esa nu hnu f

/-- The finite-particle domain `𝓕_fin(D)` of the outer Fock space over the Hermite core. -/
abbrev finCore : Submodule ℂ (lp (fun n : ℕ => fockSector lagOneSpace n) 2) :=
  dsCore (fun n : ℕ => fockSectorCore lagOneSpace (lpFiniteModes Vel) (lpFiniteModes Vel) n)

/-- The second quantization `dΓ(N)` on `𝓕_fin(D)`. -/
def liftedN (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    finCore →ₗ[ℂ] lp (fun n : ℕ => fockSector lagOneSpace n) 2 :=
  dGammaCoreOp lagOneSpace (lpFiniteModes Vel) (compOneOp nu hnu f) (lpFiniteModes Vel)

/-- **Step 2 (the lift).**  `dΓ(N)` is essentially self-adjoint on the finite-particle
domain. -/
theorem liftedComparison_dGamma_esa (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn finCore (liftedN nu hnu f) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := lagOneSpace)
    (compOneOp nu hnu f) lagOne_dense (lagCompN_symmetricOn nu hnu f)
    (comparison_esa_on_core nu hnu f)

theorem liftedN_symmetricOn (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    SymmetricOn finCore (liftedN nu hnu f) :=
  EsaOneParticle.symmetricOn_dGammaCoreOp_of_esa (Hs := lagOneSpace)
    (compOneOp nu hnu f) (lagCompN_symmetricOn nu hnu f)

/-- **The lifted comparison operator** `dΓ(N) + 1` on `𝓕_fin(D)`. -/
def liftedComparison (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    finCore →ₗ[ℂ] lp (fun n : ℕ => fockSector lagOneSpace n) 2 :=
  liftedN nu hnu f + ((1 : ℝ) : ℂ) • finCore.subtype

/-- `dΓ(N) + 1` is symmetric (Hermitian) on `𝓕_fin(D)`. -/
theorem liftedComparison_symmetricOn (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    SymmetricOn finCore (liftedComparison nu hnu f) :=
  symmetricOn_add_const (liftedN_symmetricOn nu hnu f) 1

/-- **NS-L-C.3 — `liftedComparison_esa`.**  The lifted comparison operator `dΓ(N) + 1` is
essentially self-adjoint on the finite-particle core `𝓕_fin(D)` of the outer Fock space. -/
theorem liftedComparison_esa (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn finCore (liftedComparison nu hnu f) :=
  essentiallySelfAdjointOn_add_const (liftedN_symmetricOn nu hnu f)
    (liftedComparison_dGamma_esa nu hnu f) 1

/-- The analytic form of the resolvent-bound shadow: the deficiency spaces of `dΓ(N) + 1`
vanish at every non-real `z`. -/
theorem liftedComparison_resolvent_deficiency (hnu : 0 < nu) (f : Fin 3 → ℝ) {z : ℂ}
    (hz : z.im ≠ 0) : DeficiencyTrivialAt finCore (liftedComparison nu hnu f) z :=
  deficiencyTrivialAt_of_essentiallySelfAdjointOn (liftedComparison_symmetricOn nu hnu f)
    (liftedComparison_esa nu hnu f) hz

/-! ## The Koopman–von Neumann comparison, conditionally -/

section Koopman

open BookProof.NsLagrangianDetFL BookProof.HermiteProductCore BookProof.YangMillsHermite
  BookProof.YangMillsNonAbelianEsa

variable {K : Type*} [Fintype K] (S : LagNsData K)

/-- **Conditional lifted comparison for the Koopman generator.**  *If* the comparison
operator `N_L = H_L² + E` of the Galerkin Lagrangian flow (exact determinant constraint) is
essentially self-adjoint on the Gauss–polynomial core, then `dΓ(N_L) + 1` is essentially
self-adjoint on the finite-particle core.  The hypothesis is not discharged. -/
theorem lagKoopman_liftedComparison_esa_of_comparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore (L2dSpace (lagDim K))
        (polyGaussCore (d := lagDim K)) (polyGaussCore (d := lagDim K)) n))
      (dGammaCoreOp (L2dSpace (lagDim K)) (polyGaussCore (d := lagDim K))
          (lagComparison S) (polyGaussCore (d := lagDim K))
        + ((1 : ℝ) : ℂ) • (dsCore (fun n : ℕ => fockSectorCore (L2dSpace (lagDim K))
          (polyGaussCore (d := lagDim K)) (polyGaussCore (d := lagDim K)) n)).subtype) :=
  essentiallySelfAdjointOn_add_const
    (EsaOneParticle.symmetricOn_dGammaCoreOp_of_esa (Hs := L2dSpace (lagDim K))
      (lagComparison S) (lagComparison_symmetricOn S))
    (EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := L2dSpace (lagDim K))
      (lagComparison S) polyGaussCore_dense (lagComparison_symmetricOn S) hN) 1

end Koopman

end

end BookProof.LiftedComparisonEsa
