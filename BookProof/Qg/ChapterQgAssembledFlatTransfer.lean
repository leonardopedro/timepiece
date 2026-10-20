import Mathlib
import BookProof.Qg.ChapterQgAssembledTransfer
import BookProof.Qg.ChapterQgFlatContinuumEsa

/-!
# QG-D-C, step 2a — the assembled Hamiltonian against the continuum flat operator, without `hflat`

`CONSOLIDATED_PLAN.md` §"2026-10-17", work-order step **2a**: feed the continuum flat theorem
`qgFlatL2_deficiencyTrivialAt` (QG-D-C.1, `ChapterQgFlatContinuumEsa`) into the assembled
transfer of `ChapterQgAssembledTransfer`, so that the assembled statements no longer carry the
flat hypothesis `hflat`.

## Why the statement is not phrased at `halfDensityUnitary`

`qg_assembled_halfDensity_transfer` is stated at the constructed half-density unitary
`halfDensityUnitary : L²((0,∞), de) ≃ₗᵢ L²((0,∞), 2y dy)`, a unitary between spaces of
functions of the **single** conformal variable.  The continuum flat operator `qgFlatL2Op n`
acts on `L²(ℝⁿ × ℝ)`.  The two sides live on different Hilbert spaces, so no choice of pieces
makes `P'.total` at `halfDensityUnitary` *equal* to `qgFlatL2Op n`.  The alignment is therefore
done in the vocabulary of `DeficiencyTrivialAt` (the second option the work order names):
the physical assembled Hamiltonian, carried by **any** unitary `W` onto the flat core
`qgFlatCore n` and intertwined with `qgFlatL2Op n`, has vanishing deficiency.  The flat input
is a theorem here, not a hypothesis.

## What is proved

* `deficiencyTrivialAt_total_of_flat` — trivial deficiency of the physical assembled
  Hamiltonian at every non-real `z`;
* **`qg_assembled_flat_hasZeroDeficiencyOn`** — QG-D-C.2 without `hflat`:
  `HasZeroDeficiencyOn D P.total`, the conclusion of `qg_assembled_halfDensity_transfer`;
* `qg_assembled_flat_hasZeroDeficiencyOn_termwise` — the same from termwise intertwining
  of the four constituents with four flat-side operators that sum to `qgFlatL2Op n`
  (the shape of the hypotheses of `assembled_transfer`);
* **`qg_assembled_flat_stone_flow`** — QG-D-C.3 without `hflat`: on a dense domain the
  physical assembled Hamiltonian generates a complete unitary (Stone) flow.

The sign condition of QG-D-C.1 (`V_s`, `V_c` bounded below, entering as
`V_s(x) − V_c(y)`) is carried by the hypotheses `hqs1`, `hqc1`; for the opposite sign the
flat statement is false (`ChapterQgFlatContinuumEsa`, "Why a sign condition is part of the
statement").  The intertwining data `hmap`, `hsurj`, `hint` describe a concrete physical
realization; this module does not construct one on `L²(ℝⁿ × ℝ)`.
-/

namespace BookProof.QgAssembledFlatTransfer

open MeasureTheory
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FullEsa
open BookProof.QgAssembledTransfer BookProof.QgFlatContinuumEsa BookProof.YangMillsHermite
open BookProof.HermiteProductCore BookProof.DegSchrodinger

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Trivial deficiency at every non-real `z`** of the physical assembled Hamiltonian, when a
unitary carries its domain onto the flat core and intertwines its total with the continuum
flat operator `qgFlatL2Op n`. -/
theorem deficiencyTrivialAt_total_of_flat (n : ℕ) {D : Submodule ℂ F} (P : QgPieces D)
    (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))
    {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs) (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ)
    {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc) (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ)
    (hmap : ∀ x : D, W (x : F) ∈ qgFlatCore n)
    (hsurj : ∀ y : qgFlatCore n, ∃ x : D, W (x : F) = (y : Lp ℂ 2 _))
    (hint : ∀ x : D, qgFlatL2Op n qs bs qc bc ⟨W (x : F), hmap x⟩ = W (P.total x : F))
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt D (D.subtype.comp P.total) z :=
  (qg_flat_transfer_esa n W (D.subtype.comp P.total) hqs hqs1 bs hqc hqc1 bc hmap hsurj
    hint).2 z hz

/-- **QG-D-C.2 without `hflat`.**  The conclusion of `qg_assembled_halfDensity_transfer`,
vanishing deficiency of the physical assembled Hamiltonian, with the flat input supplied by
the continuum theorem `qgFlatL2_deficiencyTrivialAt` instead of a hypothesis. -/
theorem qg_assembled_flat_hasZeroDeficiencyOn (n : ℕ) {D : Submodule ℂ F} (P : QgPieces D)
    (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))
    {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs) (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ)
    {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc) (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ)
    (hmap : ∀ x : D, W (x : F) ∈ qgFlatCore n)
    (hsurj : ∀ y : qgFlatCore n, ∃ x : D, W (x : F) = (y : Lp ℂ 2 _))
    (hint : ∀ x : D, qgFlatL2Op n qs bs qc bc ⟨W (x : F), hmap x⟩ = W (P.total x : F)) :
    HasZeroDeficiencyOn D P.total :=
  (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn D P.total).1
    (qg_flat_transfer_esa n W (D.subtype.comp P.total) hqs hqs1 bs hqc hqc1 bc hmap hsurj
      hint).1

/-- **QG-D-C.2 without `hflat`, termwise.**  Four flat-side operators `K'`, `V'`, `Gh'`, `GF'`
on the flat core that sum to `qgFlatL2Op n` and are intertwined termwise with the kinetic,
potential, ghost and gauge-fixing constituents give vanishing deficiency of the physical
assembled Hamiltonian. -/
theorem qg_assembled_flat_hasZeroDeficiencyOn_termwise (n : ℕ) {D : Submodule ℂ F}
    (P : QgPieces D) (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))
    {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs) (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ)
    {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc) (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ)
    (K' V' Gh' GF' : qgFlatCore n →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))
    (hsum : K' + V' + Gh' + GF' = qgFlatL2Op n qs bs qc bc)
    (hmap : ∀ x : D, W (x : F) ∈ qgFlatCore n)
    (hsurj : ∀ y : qgFlatCore n, ∃ x : D, W (x : F) = (y : Lp ℂ 2 _))
    (hK : ∀ x : D, K' ⟨W (x : F), hmap x⟩ = W (P.kinetic x : F))
    (hV : ∀ x : D, V' ⟨W (x : F), hmap x⟩ = W (P.potential x : F))
    (hGh : ∀ x : D, Gh' ⟨W (x : F), hmap x⟩ = W (P.ghost x : F))
    (hGF : ∀ x : D, GF' ⟨W (x : F), hmap x⟩ = W (P.gaugeFix x : F)) :
    HasZeroDeficiencyOn D P.total := by
  refine qg_assembled_flat_hasZeroDeficiencyOn n P W hqs hqs1 bs hqc hqc1 bc hmap hsurj
    fun x => ?_
  rw [← hsum]
  simp only [LinearMap.add_apply, hK, hV, hGh, hGF, QgPieces.total, Submodule.coe_add, map_add]

open BookProof.ChapterStoneResolvent BookProof.StoneBridge BookProof.EsaClosure in
/-- **QG-D-C.3 without `hflat`.**  On a dense domain, the physical assembled Hamiltonian that a
unitary carries onto the flat core, intertwining it with `qgFlatL2Op n`, is essentially
self-adjoint and generates a complete unitary (Stone) flow. -/
theorem qg_assembled_flat_stone_flow (n : ℕ) [CompleteSpace F] {D : Submodule ℂ F}
    (hD : Dense (D : Set F)) (P : QgPieces D)
    (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))
    {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs) (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ)
    {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc) (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ)
    (hmap : ∀ x : D, W (x : F) ∈ qgFlatCore n)
    (hsurj : ∀ y : qgFlatCore n, ∃ x : D, W (x : F) = (y : Lp ℂ 2 _))
    (hint : ∀ x : D, qgFlatL2Op n qs bs qc bc ⟨W (x : F), hmap x⟩ = W (P.total x : F)) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      IsSelfAdjointExtension (D.subtype.comp P.total) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ hD (fun x y => P.total_isSymmetricDom x y)
    (qg_flat_transfer_esa n W (D.subtype.comp P.total) hqs hqs1 bs hqc hqc1 bc hmap hsurj
      hint).1

end

end BookProof.QgAssembledFlatTransfer
