import BookProof.Ns.ChapterNsOneBodyDGamma
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the one-body generator `H_sp = H_visc + H_advect` and its lift `dΓ(H_sp)`

Every headline result of `BookProof/Ns/ChapterNsOneBodyDGamma.lean` must rest on the standard
axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NsOneBody.redFormPoly_eq_liftParcel
#audit_axioms BookProof.NsOneBody.spHam_eq_visc_add_advect
#audit_axioms BookProof.NsOneBody.spHam_quadForm_split
#audit_axioms BookProof.NsOneBody.spHam_symmetricOn
#audit_axioms BookProof.NsOneBody.spVisc_quadForm_nonneg
#audit_axioms BookProof.NsOneBody.spAdvect_quadForm_nonneg
#audit_axioms BookProof.NsOneBody.spHam_esa_farisLavine
#audit_axioms BookProof.NsOneBody.spFried_isPositiveSelfAdjointExtension
#audit_axioms BookProof.NsOneBody.nsSpDGamma_friedrichs_extension
#audit_axioms BookProof.NsOneBody.nsSpDGamma_esa_farisLavine
#audit_axioms BookProof.NsOneBody.nsSpDGammaFried_isPositiveSelfAdjointExtension
#audit_axioms BookProof.NsOneBody.nsSpDGamma_number_conserving
#audit_axioms BookProof.NsOneBody.nsSpDGamma_one_particle
#audit_axioms BookProof.NsOneBody.weylOpDom_block_sum
#audit_axioms BookProof.NsOneBody.redHam_eq_sum_parcel
#audit_axioms BookProof.NsOneBody.nsRedFullFockHam_sector_sum_parcel
#audit_axioms BookProof.NsOneBody.redParcelHam_symmetricOn
#audit_axioms BookProof.NsOneBody.redParcelHam_quadForm_nonneg
#audit_axioms BookProof.NsOneBody.spHam_stone_flow
#audit_axioms BookProof.NsOneBody.nsSpDGamma_stone_flow
