import BookProof.ChapterQgVielbeinScalaronGaugeFL
import BookProof.ChapterQg3DGaugeFarisLavine
import BookProof.ChapterEsaFarisLavineIndex

/-!
Axiom audit for the 2026-09-11 second-pass wave: quantum gravity with the **vielbein**, the
**full exponential scalaron potential**, the **3D gauge fixing** and the **gauge fixing of
the variables representing spatial derivatives of the fields**, essentially self-adjoint on
the outer Fock space by **Faris–Lavine only**, together with the particle-number
conservation of the outer Hamiltonian.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The complete mode model: vielbein + derivative variables + both gauge fixings + scalaron.
#print axioms BookProof.QgVielbeinScalaronGaugeFL.formValue_dGauge
#print axioms BookProof.QgVielbeinScalaronGaugeFL.formValue_gauge3d
#print axioms BookProof.QgVielbeinScalaronGaugeFL.torsion_eq_exact_of_gauge_fixed
#print axioms BookProof.QgVielbeinScalaronGaugeFL.norm_gGram_le
#print axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_farisLavine
#print axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_core_fl
#print axioms BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_esa
#print axioms BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_esa_core
#print axioms BookProof.QgVielbeinScalaronGaugeFL.secHam_number_conserving
#print axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_momentum_conserving
#print axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_number_conserving
#print axioms BookProof.QgVielbeinScalaronGaugeFL.gGram_diag_ne_zero
#print axioms BookProof.QgVielbeinScalaronGaugeFL.gCoef_dGauge_ne_zero
#print axioms BookProof.QgVielbeinScalaronGaugeFL.gCoef_gauge3d_ne_zero
#print axioms BookProof.QgVielbeinScalaronGaugeFL.gCoupling_ne_zero

-- The `84` jet coordinates, through Faris–Lavine, and the nested Fock space.
#print axioms BookProof.Qg3DGaugeFL.qgSigned_eq_sqSumOp
#print axioms BookProof.Qg3DGaugeFL.qgSigned_esa_fl
#print axioms BookProof.Qg3DGaugeFL.qg3D_esa_fl
#print axioms BookProof.Qg3DGaugeFL.qg3DGaugeFixed_esa_fl
#print axioms BookProof.Qg3DGaugeFL.qgGauge_sector_esa_fl
#print axioms BookProof.Qg3DGaugeFL.qgGauge_outerHam_esa_fl
#print axioms BookProof.Qg3DGaugeFL.dsOp_number_conserving
#print axioms BookProof.Qg3DGaugeFL.qgGauge_number_conserving

#print axioms BookProof.QgVielbeinScalaronGaugeFL.secCore_dense
#print axioms BookProof.QgVielbeinScalaronGaugeFL.qgFull_stone_flow
#print axioms BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_stone_flow
#print axioms BookProof.Qg3DGaugeFL.qgGauge_stone_flow
#print axioms BookProof.Qg3DGaugeFL.qg3DGaugeFixed_stone_flow

-- The index.
#print axioms BookProof.EsaFarisLavineIndex.qg84_gaugeFixed_esa_fl
#print axioms BookProof.EsaFarisLavineIndex.qgFull_esa_fl
#print axioms BookProof.EsaFarisLavineIndex.qgFull_esa_core_fl
#print axioms BookProof.EsaFarisLavineIndex.starobinsky_qgFull_esa_fl
