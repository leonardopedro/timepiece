import BookProof.Sm.ChapterSmOneParticle
import BookProof.Sm.ChapterSmHamiltonian
import BookProof.Sm.ChapterSmComparison
import BookProof.Sm.ChapterSmOuterFock
import BookProof.Sm.ChapterSmCarAlgebra
import BookProof.Sm.ChapterSmDiracYukawa
import BookProof.Sm.ChapterSmComparisonFull
import BookProof.ChapterSmHiggsVacuum
import BookProof.Sm.ChapterSmDiracSpinor
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the Standard-Model wave (§D6b-SM of `CONSOLIDATED_PLAN.md`): the coordinate
recount and the CKM/PMNS algebra, the bosonic one-particle Hamiltonian and its Friedrichs
extension, the comparison operator `N`, and the `dΓ(h)` enclosure on the nested Fock space.
Each line must report only `propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.SmOneParticle.card_smCoord
#audit_axioms BookProof.SmOneParticle.unitary_row_sum_normSq
#audit_axioms BookProof.SmOneParticle.unitary_entry_norm_le_one
#audit_axioms BookProof.SmOneParticle.unitary_transpose_of_real
#audit_axioms BookProof.SmOneParticle.biunitary_massSq
#audit_axioms BookProof.SmOneParticle.norm_mulVec_le_sum
#audit_axioms BookProof.SmOneParticle.yukawa_bound

#audit_axioms BookProof.SmHamiltonian.card_smMom
#audit_axioms BookProof.SmHamiltonian.card_smForm
#audit_axioms BookProof.SmHamiltonian.smHamiltonian_symmetricOn
#audit_axioms BookProof.SmHamiltonian.smHamiltonian_quadForm
#audit_axioms BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg
#audit_axioms BookProof.SmHamiltonian.sm_friedrichs_extension
#audit_axioms BookProof.SmHamiltonian.higgs_mexican_hat
#audit_axioms BookProof.SmHamiltonian.wall_sq

#audit_axioms BookProof.SmComparison.card_smConf
#audit_axioms BookProof.SmComparison.smComparison_symmetricOn
#audit_axioms BookProof.SmComparison.smComparison_quadForm
#audit_axioms BookProof.SmComparison.sm_N_positive
#audit_axioms BookProof.SmComparison.sm_N_dyn_esa
#audit_axioms BookProof.SmComparison.sm_N_dyn_stone_flow

#audit_axioms BookProof.SmOuterFock.smSectorHam_symmetricOn
#audit_axioms BookProof.SmOuterFock.smSectorHam_quadForm_nonneg
#audit_axioms BookProof.SmOuterFock.smSector_friedrichs_extension
#audit_axioms BookProof.SmOuterFock.smFockCore_dense
#audit_axioms BookProof.SmOuterFock.smFockHam_symmetricOn
#audit_axioms BookProof.SmOuterFock.smFockHam_quadForm_nonneg
#audit_axioms BookProof.SmOuterFock.sm_dGamma_friedrichs_extension
#audit_axioms BookProof.SmOuterFock.sm_dGamma_stone_flow
#audit_axioms BookProof.SmOuterFock.smFockHam_number_conserving

#audit_axioms BookProof.SmCar.car_annih_creat_self
#audit_axioms BookProof.SmCar.car_annih_creat_of_ne
#audit_axioms BookProof.SmCar.car_annih_annih
#audit_axioms BookProof.SmCar.car_creat_creat
#audit_axioms BookProof.SmCar.inner_creat_left
#audit_axioms BookProof.SmCar.norm_annih_le
#audit_axioms BookProof.SmCar.fermiBilin_symmetric
#audit_axioms BookProof.SmCar.fermiEnergy_occ
#audit_axioms BookProof.SmCar.fermi_mass_gap

#audit_axioms BookProof.SmDiracYukawa.yukawa_entry_bound
#audit_axioms BookProof.SmDiracYukawa.smFermiHam_symmetricOn
#audit_axioms BookProof.SmDiracYukawa.sm_fermi_fl_i
#audit_axioms BookProof.SmDiracYukawa.sm_fermi_fl_ii
#audit_axioms BookProof.SmDiracYukawa.sm_fermi_fl_iii
#audit_axioms BookProof.SmDiracYukawa.sm_fermi_esa

#audit_axioms BookProof.SmComparisonFull.deriv_coordinate_esa
#audit_axioms BookProof.SmComparisonFull.smFullChain_length
#audit_axioms BookProof.SmComparisonFull.sm_N_full_esa
#audit_axioms BookProof.SmComparisonFull.sm_N_full_stone_flow

#audit_axioms BookProof.SmHiggsVacuum.higgsV_ge_min
#audit_axioms BookProof.SmHiggsVacuum.higgsV_eq_min_iff
#audit_axioms BookProof.SmHiggsVacuum.higgs_goldstone
#audit_axioms BookProof.SmHiggsVacuum.higgs_radial
#audit_axioms BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff

#audit_axioms BookProof.SmDiracSpinor.diracOneParticle_hermitian
#audit_axioms BookProof.SmDiracSpinor.diracOneParticle_sq
#audit_axioms BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq
#audit_axioms BookProof.SmDiracSpinor.diracFieldHam_symmetric
#audit_axioms BookProof.SmDiracSpinor.dirac_field_esa
