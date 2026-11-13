import BookProof.Qg.ChapterQgVielbeinScalaronGaugeFL
import BookProof.Qg.ChapterQg3DGaugeFarisLavine
import BookProof.ChapterEsaFarisLavineIndex
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the 2026-09-11 second-pass wave: quantum gravity with the **vielbein**, the
**full exponential scalaron potential**, the **3D gauge fixing** and the **gauge fixing of
the variables representing spatial derivatives of the fields**, essentially self-adjoint on
the outer Fock space by **Faris–Lavine only**, together with the particle-number
conservation of the outer Hamiltonian.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The complete mode model: vielbein + derivative variables + both gauge fixings + scalaron.
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.formValue_dGauge
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.formValue_gauge3d
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.torsion_eq_exact_of_gauge_fixed
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.norm_gGram_le
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_farisLavine
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_core_fl
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_esa
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_esa_core
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.secHam_number_conserving
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_momentum_conserving
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_number_conserving
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.gGram_diag_ne_zero
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.gCoef_dGauge_ne_zero
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.gCoef_gauge3d_ne_zero
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.gCoupling_ne_zero

-- The `84` jet coordinates, through Faris–Lavine, and the nested Fock space.
#audit_axioms BookProof.Qg3DGaugeFL.qgSigned_eq_sqSumOp
#audit_axioms BookProof.Qg3DGaugeFL.qgSigned_esa_fl
#audit_axioms BookProof.Qg3DGaugeFL.qg3D_esa_fl
#audit_axioms BookProof.Qg3DGaugeFL.qg3DGaugeFixed_esa_fl
#audit_axioms BookProof.Qg3DGaugeFL.qgGauge_sector_esa_fl
#audit_axioms BookProof.Qg3DGaugeFL.qgGauge_outerHam_esa_fl
#audit_axioms BookProof.Qg3DGaugeFL.dsOp_number_conserving
#audit_axioms BookProof.Qg3DGaugeFL.qgGauge_number_conserving

#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.secCore_dense
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_stone_flow
#audit_axioms BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_stone_flow
#audit_axioms BookProof.Qg3DGaugeFL.qgGauge_stone_flow
#audit_axioms BookProof.Qg3DGaugeFL.qg3DGaugeFixed_stone_flow

-- The index.
#audit_axioms BookProof.EsaFarisLavineIndex.qg84_gaugeFixed_esa_fl
#audit_axioms BookProof.EsaFarisLavineIndex.qgFull_esa_fl
#audit_axioms BookProof.EsaFarisLavineIndex.qgFull_esa_core_fl
#audit_axioms BookProof.EsaFarisLavineIndex.starobinsky_qgFull_esa_fl
