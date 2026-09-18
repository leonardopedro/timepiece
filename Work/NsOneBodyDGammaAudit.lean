import BookProof.ChapterNsOneBodyDGamma

/-!
# Axiom audit — the one-body generator `H_sp = H_visc + H_advect` and its lift `dΓ(H_sp)`

Every headline result of `BookProof/ChapterNsOneBodyDGamma.lean` must rest on the standard
axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NsOneBody.redFormPoly_eq_liftParcel
#print axioms BookProof.NsOneBody.spHam_eq_visc_add_advect
#print axioms BookProof.NsOneBody.spHam_quadForm_split
#print axioms BookProof.NsOneBody.spHam_symmetricOn
#print axioms BookProof.NsOneBody.spVisc_quadForm_nonneg
#print axioms BookProof.NsOneBody.spAdvect_quadForm_nonneg
#print axioms BookProof.NsOneBody.spHam_esa_farisLavine
#print axioms BookProof.NsOneBody.spFried_isPositiveSelfAdjointExtension
#print axioms BookProof.NsOneBody.nsSpDGamma_friedrichs_extension
#print axioms BookProof.NsOneBody.nsSpDGamma_esa_farisLavine
#print axioms BookProof.NsOneBody.nsSpDGammaFried_isPositiveSelfAdjointExtension
#print axioms BookProof.NsOneBody.nsSpDGamma_number_conserving
#print axioms BookProof.NsOneBody.nsSpDGamma_one_particle
#print axioms BookProof.NsOneBody.weylOpDom_block_sum
#print axioms BookProof.NsOneBody.redHam_eq_sum_parcel
#print axioms BookProof.NsOneBody.nsRedFullFockHam_sector_sum_parcel
#print axioms BookProof.NsOneBody.redParcelHam_symmetricOn
#print axioms BookProof.NsOneBody.redParcelHam_quadForm_nonneg
#print axioms BookProof.NsOneBody.spHam_stone_flow
#print axioms BookProof.NsOneBody.nsSpDGamma_stone_flow
