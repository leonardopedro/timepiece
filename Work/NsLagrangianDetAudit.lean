import BookProof.ChapterNsLagrangianDetFarisLavine

/-!
# Axiom audit: Lagrangian Navier–Stokes with the determinant constraint, through Faris–Lavine

`BookProof.ChapterNsLagrangianDetConvolution`, `BookProof.ChapterKoopmanLyapunovFarisLavine`,
`BookProof.ChapterNsLagrangianDetFarisLavine`.
-/

#print axioms BookProof.NsLagrangianDet.hasDerivAt_dispField
#print axioms BookProof.NsLagrangianDet.dispField_im
#print axioms BookProof.NsLagrangianDet.det_deformation_eq
#print axioms BookProof.NsLagrangianDet.volume_residual_eq
#print axioms BookProof.NsLagrangianDet.volPot_eval_nonneg
#print axioms BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero
#print axioms BookProof.KoopmanLyapunov.kvnGen_apply
#print axioms BookProof.KoopmanLyapunov.kvnGen_comm_mul
#print axioms BookProof.KoopmanLyapunov.commForm_kvnGen_mul_bound
#print axioms BookProof.KoopmanLyapunov.kvnGen_esa_of_lyapunov
#print axioms BookProof.NsLagrangianDetFL.lagFlux_eq
#print axioms BookProof.NsLagrangianDetFL.lagDiv_eq
#print axioms BookProof.NsLagrangianDetFL.lagKoopmanOp_symmetricOn
#print axioms BookProof.NsLagrangianDetFL.lagComparison_quadForm_ge
#print axioms BookProof.NsLagrangianDetFL.lagComparison_relBound
#print axioms BookProof.NsLagrangianDetFL.lagComparison_commForm
#print axioms BookProof.NsLagrangianDetFL.lagComparison_commForm_bound
#print axioms BookProof.NsLagrangianDetFL.lagKoopman_esa_of_comparison_esa
