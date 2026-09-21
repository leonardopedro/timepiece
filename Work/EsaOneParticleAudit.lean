import BookProof.ChapterEsaOneParticleDGamma

/-!
# Audit of the essentially-self-adjoint one-particle second quantization

Axiom check for the results of `BookProof/ChapterEsaOneParticleDGamma.lean`.  Only the
standard axioms `propext`, `Classical.choice`, `Quot.sound` may appear.
-/

open BookProof.EsaOneParticle

#print axioms BookProof.EsaOneParticle.esa_graph_le
#print axioms BookProof.EsaOneParticle.exists_pow_of_mem_corePow
#print axioms BookProof.EsaOneParticle.fockSectorCore_graph_le
#print axioms BookProof.EsaOneParticle.isGraphCore_clDom
#print axioms BookProof.EsaOneParticle.closureSelfAdjoint
#print axioms BookProof.EsaOneParticle.essentiallySelfAdjointOn_fockSectorDom_esa
#print axioms BookProof.EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa
#print axioms BookProof.EsaOneParticle.symmetricOn_dGammaCoreOp_of_esa
#print axioms BookProof.EsaOneParticle.essentiallySelfAdjointOn_of_selfAdjoint
#print axioms BookProof.EsaOneParticle.essentiallySelfAdjointOn_restrict
#print axioms BookProof.EsaOneParticle.not_isSelfAdjointOn_restrict
#print axioms BookProof.EsaOneParticle.positionCore_essentiallySelfAdjoint
#print axioms BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn
#print axioms BookProof.EsaOneParticle.dGamma_positionCore_essentiallySelfAdjoint
