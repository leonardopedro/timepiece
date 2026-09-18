import BookProof.ChapterNsFourierElimination
import BookProof.ChapterNsLagrangianFourierElimination
import BookProof.ChapterQgFourierElimination
import BookProof.ChapterQgFullEliminated

/-!
# Axiom audit — the Fourier elimination of the derivative variables (NS Eulerian and Lagrangian, QG)

Every headline result of `BookProof/ChapterNsFourierElimination.lean` (the Eulerian elimination,
with the honest reduced family `redFormPoly` that squares the real *and* imaginary parts of every
surviving form, so that the advection is one of the squares) and of
`BookProof/ChapterNsLagrangianFourierElimination.lean` (the material elimination and the rank-one
degeneracy it meets) must rest on the standard axioms only:
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- The Eulerian substitution and its symbols.
#print axioms BookProof.NsFullEuler.nsElimSubst_resPoly
#print axioms BookProof.NsFullEuler.nsElimSubst_divPoly
#print axioms BookProof.NsFullEuler.fourierAdvect_eq_transfer

-- The honest reduced one-particle Hamiltonian: the advection is one of the squares.
#print axioms BookProof.NsFullEuler.realCoeff_redFormPoly
#print axioms BookProof.NsFullEuler.redFieldN_advect
#print axioms BookProof.NsFullEuler.redFieldN_div
#print axioms BookProof.NsFullEuler.redHam_symmetricOn
#print axioms BookProof.NsFullEuler.redHam_quadForm_nonneg
#print axioms BookProof.NsFullEuler.redHam_friedrichs_extension

-- The nested-Fock lift and its Faris–Lavine statement.
#print axioms BookProof.NsFullEuler.nsRedFullFockHam_quadForm_nonneg
#print axioms BookProof.NsFullEuler.nsRedFullFock_friedrichs_extension
#print axioms BookProof.NsFullEuler.nsRedFullOuterN_esa
#print axioms BookProof.NsFullEuler.nsRedFullOuterN_isPositiveSelfAdjointExtension

-- The Lagrangian elimination and the rank-one degeneracy.
#print axioms BookProof.NsLagFourier.lagElimCoord_fIdx
#print axioms BookProof.NsLagFourier.lagElimCoord_vgIdx
#print axioms BookProof.NsLagFourier.lagElimSubst_cofPoly
#print axioms BookProof.NsLagFourier.lagElimSubst_piola
#print axioms BookProof.NsLagFourier.lagElimSubst_detPoly
#print axioms BookProof.NsLagFourier.lagElimSubst_volumePoly
#print axioms BookProof.NsLagFourier.lagElimSubst_volumePoly_sq
#print axioms BookProof.NsLagFourier.lagElimSubst_lagResPoly

-- The quantum-gravity elimination of the vielbein derivative modes.
#print axioms BookProof.QgFourierElim.elimTorsion_eq_torsionCoef
#print axioms BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
#print axioms BookProof.QgFourierElim.elimGram_eq_contTorsionGram
#print axioms BookProof.QgFourierElim.qgElimModes_A
#print axioms BookProof.QgFourierElim.qgElim_esa
#print axioms BookProof.QgFourierElim.starobinsky_qgElim_esa
#print axioms BookProof.QgFourierElim.elimTorsion_ne_zero
#print axioms BookProof.QgFourierElim.formValue_dGauge_elimConfig
#print axioms BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
#print axioms BookProof.QgFourierElim.formValue_torsion_elimConfig
#print axioms BookProof.QgFourierElim.formValue_gauge3d_elimConfig

-- The full quantum-gravity Hamiltonian rebuilt on the eliminated components alone.
#print axioms BookProof.QgFullEliminated.eFormValue_eq_formValue_elimConfig
#print axioms BookProof.QgFullEliminated.eFormValue_torsion
#print axioms BookProof.QgFullEliminated.elimCoef_dGauge
#print axioms BookProof.QgFullEliminated.eGram_eq_torsion_add_gauge3d
#print axioms BookProof.QgFullEliminated.eGram_quadForm
#print axioms BookProof.QgFullEliminated.gGram_quadForm
#print axioms BookProof.QgFullEliminated.quadForm_eq_of_gauge_fixed
#print axioms BookProof.QgFullEliminated.qgElimFull_esa_farisLavine
#print axioms BookProof.QgFullEliminated.qgElimFull_esa_core_fl
#print axioms BookProof.QgFullEliminated.starobinsky_qgElimFull_esa
#print axioms BookProof.QgFullEliminated.starobinsky_qgElimFull_esa_core
#print axioms BookProof.QgFullEliminated.qgElimFull_stone_flow
#print axioms BookProof.QgFullEliminated.qgElimFull_momentum_conserving
#print axioms BookProof.QgFullEliminated.qgElimFull_number_conserving
#print axioms BookProof.QgFullEliminated.eGram_diag_ne_zero
#print axioms BookProof.QgFullEliminated.eCoupling_ne_zero
