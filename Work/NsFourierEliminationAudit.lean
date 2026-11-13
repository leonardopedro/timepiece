import BookProof.Ns.ChapterNsFourierElimination
import BookProof.Ns.ChapterNsLagrangianFourierElimination
import BookProof.Qg.ChapterQgFourierElimination
import BookProof.Qg.ChapterQgFullEliminated
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the Fourier elimination of the derivative variables (NS Eulerian and Lagrangian, QG)

Every headline result of `BookProof/Ns/ChapterNsFourierElimination.lean` (the Eulerian elimination,
with the honest reduced family `redFormPoly` that squares the real *and* imaginary parts of every
surviving form, so that the advection is one of the squares) and of
`BookProof/Ns/ChapterNsLagrangianFourierElimination.lean` (the material elimination and the rank-one
degeneracy it meets) must rest on the standard axioms only:
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- The Eulerian substitution and its symbols.
#audit_axioms BookProof.NsFullEuler.nsElimSubst_resPoly
#audit_axioms BookProof.NsFullEuler.nsElimSubst_divPoly
#audit_axioms BookProof.NsFullEuler.fourierAdvect_eq_transfer

-- The honest reduced one-particle Hamiltonian: the advection is one of the squares.
#audit_axioms BookProof.NsFullEuler.realCoeff_redFormPoly
#audit_axioms BookProof.NsFullEuler.redFieldN_advect
#audit_axioms BookProof.NsFullEuler.redFieldN_div
#audit_axioms BookProof.NsFullEuler.redHam_symmetricOn
#audit_axioms BookProof.NsFullEuler.redHam_quadForm_nonneg
#audit_axioms BookProof.NsFullEuler.redHam_friedrichs_extension

-- The nested-Fock lift and its Faris–Lavine statement.
#audit_axioms BookProof.NsFullEuler.nsRedFullFockHam_quadForm_nonneg
#audit_axioms BookProof.NsFullEuler.nsRedFullFock_friedrichs_extension
#audit_axioms BookProof.NsFullEuler.nsRedFullOuterN_esa
#audit_axioms BookProof.NsFullEuler.nsRedFullOuterN_isPositiveSelfAdjointExtension

-- The Lagrangian elimination and the rank-one degeneracy.
#audit_axioms BookProof.NsLagFourier.lagElimCoord_fIdx
#audit_axioms BookProof.NsLagFourier.lagElimCoord_vgIdx
#audit_axioms BookProof.NsLagFourier.lagElimSubst_cofPoly
#audit_axioms BookProof.NsLagFourier.lagElimSubst_piola
#audit_axioms BookProof.NsLagFourier.lagElimSubst_detPoly
#audit_axioms BookProof.NsLagFourier.lagElimSubst_volumePoly
#audit_axioms BookProof.NsLagFourier.lagElimSubst_volumePoly_sq
#audit_axioms BookProof.NsLagFourier.lagElimSubst_lagResPoly

-- The quantum-gravity elimination of the vielbein derivative modes.
#audit_axioms BookProof.QgFourierElim.elimTorsion_eq_torsionCoef
#audit_axioms BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
#audit_axioms BookProof.QgFourierElim.elimGram_eq_contTorsionGram
#audit_axioms BookProof.QgFourierElim.qgElimModes_A
#audit_axioms BookProof.QgFourierElim.qgElim_esa
#audit_axioms BookProof.QgFourierElim.starobinsky_qgElim_esa
#audit_axioms BookProof.QgFourierElim.elimTorsion_ne_zero
#audit_axioms BookProof.QgFourierElim.formValue_dGauge_elimConfig
#audit_axioms BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
#audit_axioms BookProof.QgFourierElim.formValue_torsion_elimConfig
#audit_axioms BookProof.QgFourierElim.formValue_gauge3d_elimConfig

-- The full quantum-gravity Hamiltonian rebuilt on the eliminated components alone.
#audit_axioms BookProof.QgFullEliminated.eFormValue_eq_formValue_elimConfig
#audit_axioms BookProof.QgFullEliminated.eFormValue_torsion
#audit_axioms BookProof.QgFullEliminated.elimCoef_dGauge
#audit_axioms BookProof.QgFullEliminated.eGram_eq_torsion_add_gauge3d
#audit_axioms BookProof.QgFullEliminated.eGram_quadForm
#audit_axioms BookProof.QgFullEliminated.gGram_quadForm
#audit_axioms BookProof.QgFullEliminated.quadForm_eq_of_gauge_fixed
#audit_axioms BookProof.QgFullEliminated.qgElimFull_esa_farisLavine
#audit_axioms BookProof.QgFullEliminated.qgElimFull_esa_core_fl
#audit_axioms BookProof.QgFullEliminated.starobinsky_qgElimFull_esa
#audit_axioms BookProof.QgFullEliminated.starobinsky_qgElimFull_esa_core
#audit_axioms BookProof.QgFullEliminated.qgElimFull_stone_flow
#audit_axioms BookProof.QgFullEliminated.qgElimFull_momentum_conserving
#audit_axioms BookProof.QgFullEliminated.qgElimFull_number_conserving
#audit_axioms BookProof.QgFullEliminated.eGram_diag_ne_zero
#audit_axioms BookProof.QgFullEliminated.eCoupling_ne_zero
