import Mathlib
import BookProof.Qym.ChapterYangMillsWeightedGates
import BookProof.Toolbox.ChapterFockGatePhaseInvariance
import BookProof.Toolbox.ChapterHermiteProductCore
import BookProof.ChapterQuadraticFockEsa
import BookProof.Qym.ChapterYangMillsHermite
import BookProof.Toolbox.ChapterHermiteBandCalculus

/-!
# The Yang–Mills gates in `coreBasis` coordinates, from an explicit bridge hypothesis

The Yang–Mills gate theorems of `BookProof.YangMillsWeightedGates` are stated for the matrix
`ymHermCol e fabc = hermCol e (ymPoly fabc)` — the Hamiltonian in the *product Hermite* basis.
The finite-mode theorems and the certificate seam, on the other hand, work with the enumerated
Gram–Schmidt basis `coreBasis e`.  The two bases span the same core subspace of `L²(ℝ⁹⁹)`, but
they differ by one unimodular phase per level.

This module makes that difference an explicit hypothesis and carries the whole gate argument
across it:

* `BridgePhases e u` — the bridge hypothesis: every `u k` has unit modulus and
  `coreBasis e k = u k • hermBasisN e k`;
* `ymCoreCol e fabc` — **the matrix of `ymPoly fabc` in the `coreBasis` coordinates**,
  `C_{k j} = u_k ⟪coreBasis e j, T ψ_{e k}⟫`, so that the `k`-th column is the Hamiltonian
  applied to the normalized core basis vector;
* `ymCoreCol_eq_phase` — that matrix is the Hermite matrix under the diagonal phases,
  `C_{k j} = u_k conj(u_j) (ymHermCol)_{k j}`;
* `isHermCol_ymCoreCol` — it is Hermitian;
* `ymCoreCol_row_col_gates` — **the row and column gates in `coreBasis` coordinates**, with the
  same constant as in the Hermite coordinates;
* `ymCoreCol_gates_iff` — all three gates transfer, with the same constants;
* `ymCoreCol_essentiallySelfAdjointOn_core_of_ymCommBound` — **end to end**: if the bridge
  hypothesis holds and the commutator gate for `ymW` holds in the Hermite coordinates, then
  `dΓ` of the core-basis matrix is essentially self-adjoint on the finite-occupation core.

## Honest boundary

`BridgePhases` is *hypothetical here*; nothing below proves the bridge.  What is available
towards it is `BookProof.FockGramSchmidtProjection`: the Gram–Schmidt vector is the monomial
minus its projection onto the earlier spans, the product Hermite function is orthogonal to those
spans when the enumeration is degree-compatible, and any unit vector realising that orthogonal
direction gives the Gram–Schmidt vector up to a constant.  Still missing is the decomposition
`x^{e k} e^{-‖x‖²/4} = w + c • ψ_{e k}` with `w` in the earlier span together with `‖c‖ = 1`
after normalization.  What *is* proved is that the bridge hypothesis is all the gate argument
needs: the gates and the essential self-adjointness move to `coreBasis` coordinates unchanged.
-/

namespace BookProof.YangMillsCoreBasisGates

noncomputable section

open BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.QuadFockEsa
open BookProof.FockGatePhaseInvariance BookProof.YangMillsWeightedGates
  BookProof.YangMillsBandBounds
open BookProof.FockSecondQuantization BookProof.HermiteGalerkin BookProof.NavierStokesFlow
open BookProof.FarisLavine BookProof.FockWeightedSchur BookProof.HermiteBand
open BookProof.YangMillsHermite BookProof.NavierStokesFlow.DifferentialL2

/-- **The bridge hypothesis**: the core basis and the enumerated product Hermite basis differ by
one diagonal phase of unit modulus per level. -/
def BridgePhases (e : ℕ ≃ (Fin 99 →₀ ℕ)) (u : ℕ → ℂ) : Prop :=
  (∀ k, ‖u k‖ = 1) ∧ ∀ k, coreBasis e k = u k • hermBasisN e k

/-- **The matrix of the Yang–Mills Hamiltonian in `coreBasis` coordinates**: the polynomial
operator `ymPoly fabc` read through the `CoreRep` of the `coreBasis` finite-mode domain.  Its
`k`-th column is the Hamiltonian applied to the `k`-th normalized core basis vector. -/
def ymCoreCol (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℕ → (ℕ →₀ ℂ) :=
  opCol (coreBasis e) ((coreRepBasis e).op (ymPoly fabc))

/-- Under the bridge hypothesis, the polynomial representing the `k`-th core basis vector in the
`coreRepBasis` identification is `u k • ψ_{e k}`. -/
theorem coreRepBasis_symm (e : ℕ ≃ (Fin 99 →₀ ℕ)) {u : ℕ → ℂ} (hB : BridgePhases e u) (k : ℕ) :
    (coreRepBasis e).equiv.symm
        ⟨coreBasis e k, Submodule.subset_span ⟨k, rfl⟩⟩ = u k • hpsi (e k) := by
  have h1 : pgLp ((coreRepBasis e).equiv.symm
      ⟨coreBasis e k, Submodule.subset_span ⟨k, rfl⟩⟩) = coreBasis e k := by
    rw [← (coreRepBasis e).coe_symm]
  have h2 : pgLp (u k • hpsi (e k)) = coreBasis e k := by
    rw [pgLp_smul, pgLp_hpsi, ← hermBasisN_apply, ← hB.2 k]
  exact pgMap_injective (by
    rw [HermiteProductCore.pgMap_apply, HermiteProductCore.pgMap_apply, h1, h2])

/-- **The `coreBasis` matrix is the Hermite matrix under the diagonal phases.** -/
theorem ymCoreCol_eq_phase (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {u : ℕ → ℂ} (hB : BridgePhases e u) :
    PhaseRelated u (ymHermCol e fabc) (ymCoreCol e fabc) := by
  obtain ⟨hu, hbr⟩ := hB
  intro k j
  rw [ymCoreCol, ymHermCol_eq, hermCol_apply, opCol_apply, CoreRep.coe_op,
    coreRepBasis_symm e ⟨hu, hbr⟩ k, map_smul, pgLp_smul, hbr j, hermBasisN_apply,
    inner_smul_left, inner_smul_right, starRingEnd_apply]
  ring

/-- The core-basis matrix is Hermitian when the Hermite one is. -/
theorem isHermCol_ymCoreCol (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {u : ℕ → ℂ} (hB : BridgePhases e u) :
    IsHermCol (ymCoreCol e fabc) := by
  have h := ymCoreCol_eq_phase e fabc hB
  have hherm := isHermCol_ymHermCol e fabc
  intro j k
  rw [h j k, h k j, hherm k j]
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

/-- **The row and column gates hold in `coreBasis` coordinates**, from the bridge hypothesis,
with the same constant as in the Hermite coordinates. -/
theorem ymCoreCol_row_col_gates (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {u : ℕ → ℂ} (hB : BridgePhases e u) :
    ∃ K : ℝ, 0 ≤ K ∧ WRowBound (ymW e) (ymCoreCol e fabc) K ∧
      WColBound (ymW e) (ymCoreCol e fabc) K := by
  obtain ⟨K, hK0, hrow, hcol⟩ := ymHermCol_row_col_gates e fabc
  have hph := ymCoreCol_eq_phase e fabc hB
  exact ⟨K, hK0, WRowBound.phase hB.1 hph hrow, WColBound.phase hB.1 hph hcol⟩

/-- **All three gates transfer** from the Hermite coordinates to the `coreBasis` coordinates,
with the same constants. -/
theorem ymCoreCol_gates_iff (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {u : ℕ → ℂ} (hB : BridgePhases e u) {K B : ℝ} :
    (WRowBound (ymW e) (ymHermCol e fabc) K ∧ WColBound (ymW e) (ymHermCol e fabc) K ∧
        WCommBound (ymW e) (ymHermCol e fabc) B) ↔
      (WRowBound (ymW e) (ymCoreCol e fabc) K ∧ WColBound (ymW e) (ymCoreCol e fabc) K ∧
        WCommBound (ymW e) (ymCoreCol e fabc) B) :=
  gates_phase_iff hB.1 (ymCoreCol_eq_phase e fabc hB)

/-- **End to end.**  Assume the bridge hypothesis and the commutator gate for the symbol `ymW` in
the Hermite coordinates.  Then the second quantization of the Yang–Mills Hamiltonian, *as a
matrix in the `coreBasis` coordinates that the finite-mode theorems use*, is essentially
self-adjoint on the finite-occupation core. -/
theorem ymCoreCol_essentiallySelfAdjointOn_core_of_ymCommBound
    (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {u : ℕ → ℂ}
    (hB : BridgePhases e u) {B : ℝ} (hBg : WCommBound (ymW e) (ymHermCol e fabc) B) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymCoreCol e fabc)) := by
  obtain ⟨K, hK0, hrow, hcol⟩ := ymCoreCol_row_col_gates e fabc hB
  exact dGamma_essentiallySelfAdjointOn_core_w (ymW_one_le e) (isHermCol_ymCoreCol e fabc hB)
    hrow hcol hK0 (WCommBound.phase hB.1 (ymCoreCol_eq_phase e fabc hB) hBg)

end

end BookProof.YangMillsCoreBasisGates
