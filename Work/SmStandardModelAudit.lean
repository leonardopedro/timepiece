import BookProof.ChapterSmOneParticle
import BookProof.ChapterSmHamiltonian
import BookProof.ChapterSmComparison
import BookProof.ChapterSmOuterFock
import BookProof.ChapterSmCarAlgebra
import BookProof.ChapterSmDiracYukawa
import BookProof.ChapterSmComparisonFull
import BookProof.ChapterSmHiggsVacuum
import BookProof.ChapterSmDiracSpinor

/-!
Axiom audit for the Standard-Model wave (§D6b-SM of `CONSOLIDATED_PLAN.md`): the coordinate
recount and the CKM/PMNS algebra, the bosonic one-particle Hamiltonian and its Friedrichs
extension, the comparison operator `N`, and the `dΓ(h)` enclosure on the nested Fock space.
Each line must report only `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.SmOneParticle.card_smCoord
#print axioms BookProof.SmOneParticle.unitary_row_sum_normSq
#print axioms BookProof.SmOneParticle.unitary_entry_norm_le_one
#print axioms BookProof.SmOneParticle.unitary_transpose_of_real
#print axioms BookProof.SmOneParticle.biunitary_massSq
#print axioms BookProof.SmOneParticle.norm_mulVec_le_sum
#print axioms BookProof.SmOneParticle.yukawa_bound

#print axioms BookProof.SmHamiltonian.card_smMom
#print axioms BookProof.SmHamiltonian.card_smForm
#print axioms BookProof.SmHamiltonian.smHamiltonian_symmetricOn
#print axioms BookProof.SmHamiltonian.smHamiltonian_quadForm
#print axioms BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg
#print axioms BookProof.SmHamiltonian.sm_friedrichs_extension
#print axioms BookProof.SmHamiltonian.higgs_mexican_hat
#print axioms BookProof.SmHamiltonian.wall_sq

#print axioms BookProof.SmComparison.card_smConf
#print axioms BookProof.SmComparison.smComparison_symmetricOn
#print axioms BookProof.SmComparison.smComparison_quadForm
#print axioms BookProof.SmComparison.sm_N_positive
#print axioms BookProof.SmComparison.sm_N_dyn_esa
#print axioms BookProof.SmComparison.sm_N_dyn_stone_flow

#print axioms BookProof.SmOuterFock.smSectorHam_symmetricOn
#print axioms BookProof.SmOuterFock.smSectorHam_quadForm_nonneg
#print axioms BookProof.SmOuterFock.smSector_friedrichs_extension
#print axioms BookProof.SmOuterFock.smFockCore_dense
#print axioms BookProof.SmOuterFock.smFockHam_symmetricOn
#print axioms BookProof.SmOuterFock.smFockHam_quadForm_nonneg
#print axioms BookProof.SmOuterFock.sm_dGamma_friedrichs_extension
#print axioms BookProof.SmOuterFock.sm_dGamma_stone_flow
#print axioms BookProof.SmOuterFock.smFockHam_number_conserving

#print axioms BookProof.SmCar.car_annih_creat_self
#print axioms BookProof.SmCar.car_annih_creat_of_ne
#print axioms BookProof.SmCar.car_annih_annih
#print axioms BookProof.SmCar.car_creat_creat
#print axioms BookProof.SmCar.inner_creat_left
#print axioms BookProof.SmCar.norm_annih_le
#print axioms BookProof.SmCar.fermiBilin_symmetric
#print axioms BookProof.SmCar.fermiEnergy_occ
#print axioms BookProof.SmCar.fermi_mass_gap

#print axioms BookProof.SmDiracYukawa.yukawa_entry_bound
#print axioms BookProof.SmDiracYukawa.smFermiHam_symmetricOn
#print axioms BookProof.SmDiracYukawa.sm_fermi_fl_i
#print axioms BookProof.SmDiracYukawa.sm_fermi_fl_ii
#print axioms BookProof.SmDiracYukawa.sm_fermi_fl_iii
#print axioms BookProof.SmDiracYukawa.sm_fermi_esa

#print axioms BookProof.SmComparisonFull.deriv_coordinate_esa
#print axioms BookProof.SmComparisonFull.smFullChain_length
#print axioms BookProof.SmComparisonFull.sm_N_full_esa
#print axioms BookProof.SmComparisonFull.sm_N_full_stone_flow

#print axioms BookProof.SmHiggsVacuum.higgsV_ge_min
#print axioms BookProof.SmHiggsVacuum.higgsV_eq_min_iff
#print axioms BookProof.SmHiggsVacuum.higgs_goldstone
#print axioms BookProof.SmHiggsVacuum.higgs_radial
#print axioms BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff

#print axioms BookProof.SmDiracSpinor.diracOneParticle_hermitian
#print axioms BookProof.SmDiracSpinor.diracOneParticle_sq
#print axioms BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq
#print axioms BookProof.SmDiracSpinor.diracFieldHam_symmetric
#print axioms BookProof.SmDiracSpinor.dirac_field_esa
