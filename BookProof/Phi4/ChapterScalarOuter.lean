import BookProof.Phi4.ChapterScalarMehler
import BookProof.ChapterDiagonalDGammaEsa

/-!
# Dynamics on the completed symmetric outer Fock space

Projecting a dense tensor core with the continuous bosonic symmetrizer gives
a dense core in its range. This supplies the density input for the Stone bridge.
The empty outer sector has zero Hamiltonian even with the scalar energy constant.
-/
namespace BookProof.Phi4.Model

open TensorCore SecondQuantizationCore FockStatistics ReducedEsa GraphCore DiagonalDGamma
open YangMillsNonAbelianEsa
open DirectSumEsa HermiteProductCore FarisLavine EsaClosure ChapterStoneResolvent StoneBridge

noncomputable section

private theorem symmetricCore_dense (Hs : IPSpace) (D : Submodule ℂ Hs.carrier)
    (hd : Dense (D : Set Hs.carrier)) (n : ℕ) :
    Dense (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n) :
      Set (sector (cbosonicProj Hs n))) := by
  have hspan : Dense (Submodule.span ℂ (Set.range fun x : D => (x : Hs.carrier)) :
      Set Hs.carrier) := by simpa using hd
  have hfull : Dense (fockSectorDom Hs D n : Set (fockSector Hs n)) := by
    apply (dense_span_fockEigVec Hs D id hspan n).mono
    apply SetLike.coe_subset_coe.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact fockEigVec_mem Hs D id n f
  let P := cbosonicProj Hs n
  let f := fun x => (⟨P x, x, rfl⟩ : sector P)
  have hsur : Function.Surjective f := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hsym : P.IsSymmetric := (isReducingProjection_cbosonicProj Hs n).symm
  have hcont : Continuous f := hsym.continuous.subtype_mk _
  apply (hsur.denseRange.dense_image hcont hfull).mono
  rintro _ ⟨y, hy, rfl⟩
  exact (cpermRep Hs n).avgProj_mem (cpermRep_mem_fockSectorDom Hs D n) y hy

variable {d k r : ℕ} (M : Model d k r)

/-- Tensor products of the polynomial core remain total after symmetrization. -/
theorem outerCore_dense (d : ℕ) :
    Dense (hbosonicFockDom (L2dSpace d) polyGaussCore : Set (hbosonicFock (L2dSpace d))) :=
  dsCore_dense (D := fun n => redDom (cbosonicProj (L2dSpace d) n)
    (fockSectorDom (L2dSpace d) polyGaussCore n))
    (fun n => symmetricCore_dense (L2dSpace d) polyGaussCore (polyGaussCore_dense (d := d)) n)

theorem outer_symmetric : SymmetricOn _ M.outerHam :=
  hbosonicFock_symmetricOn (Hs := L2dSpace d) M.innerHam M.symmetric

theorem outer_flow :
    ∃ (T : UnboundedSelfAdjoint (hbosonicFock (L2dSpace d)))
      (U : ℝ → hbosonicFock (L2dSpace d) →L[ℂ] hbosonicFock (L2dSpace d)),
      IsSelfAdjointExtension M.outerHam T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa M.outerHam (outerCore_dense d) M.outer_symmetric M.outer_esa

/-- Restricting to zero outer particles annihilates every vector there. -/
theorem outer_zero_sector (x : hbosonicFockDom (L2dSpace d) polyGaussCore) :
    (M.outerHam x) 0 = 0 := by
  apply Subtype.ext
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let v : fockSectorDom Hs D 0 := redIncl (cbosonicProj Hs 0) _
    ⟨((x : hbosonicFock Hs) 0), x.property.2 0⟩
  change fockSectorOp Hs D M.innerHam 0 v = 0
  obtain ⟨z, hz, h⟩ := v.property
  rw [show fockSectorOp Hs D M.innerHam 0 v = sectorEmb Hs 0
      (sectorOp Hs D M.innerHam 0 ⟨z, hz⟩) from pushOp_apply _ _ _ _ h.symm]
  obtain ⟨s, hs⟩ := hz
  rw [sectorOp_apply Hs D M.innerHam 0 _ s hs.symm, derPow_zero, map_zero]

theorem outer_number_conserving (x : hbosonicFockDom (L2dSpace d) polyGaussCore) {n : ℕ}
    (hx : ∀ i, i ≠ n → (x : hbosonicFock (L2dSpace d)) i = 0) (i : ℕ) (hi : i ≠ n) :
    (M.outerHam x) i = 0 :=
  Qg3DGaugeFL.dsOp_number_conserving _ x hx i hi

theorem outer_vacuum_action (x : hbosonicFockDom (L2dSpace d) polyGaussCore)
    (hx : ∀ i, i ≠ 0 → (x : hbosonicFock (L2dSpace d)) i = 0) : M.outerHam x = 0 := by
  apply lp.ext
  funext i
  by_cases h : i = 0
  · subst i
    exact M.outer_zero_sector x
  · exact M.outer_number_conserving x hx i h

/-- The unit scalar in tensor degree zero, included into the completed symmetric core. -/
private def vacuumComponent (d : ℕ) :
    redDom (cbosonicProj (L2dSpace d) 0) (fockSectorDom (L2dSpace d) polyGaussCore 0) := by
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let one : ((domSpace Hs D).pow 0).carrier := (1 : ℂ)
  let z := inclPow Hs D 0 one
  have hz : z ∈ sectorDom Hs D 0 := ⟨one, rfl⟩
  refine ⟨⟨sectorEmb Hs 0 z, (mem_cbosonicSector_iff Hs 0).mpr ?_⟩,
    mem_pushDom (sectorEmb Hs 0) (⟨z, hz⟩ : sectorDom Hs D 0)⟩
  intro σ
  rw [Subsingleton.elim σ 1, (cpermRep Hs 0).act_one]

def vacuum (d : ℕ) : hbosonicFockDom (L2dSpace d) polyGaussCore :=
  ⟨lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 0 (vacuumComponent d).val,
    single_mem_dsCore (D := fun n =>
    redDom (cbosonicProj (L2dSpace d) n) (fockSectorDom (L2dSpace d) polyGaussCore n))
    0 (vacuumComponent d)⟩

theorem vacuum_norm (d : ℕ) : ‖(vacuum d : hbosonicFock (L2dSpace d))‖ = 1 := by
  change ‖lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 0
    (vacuumComponent d).val‖ = 1
  rw [lp.norm_single (by norm_num)]
  change ‖sectorEmb (L2dSpace d) 0 (inclPow (L2dSpace d) polyGaussCore 0 _)‖ = 1
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  exact norm_one (α := ℂ)

theorem vacuum_energy_zero : M.outerHam (vacuum d) = 0 := by
  apply M.outer_vacuum_action
  intro i hi
  change (lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 0
    (vacuumComponent d).val) i = 0
  rw [lp.single_apply, Pi.single_eq_of_ne hi]

end
end BookProof.Phi4.Model
