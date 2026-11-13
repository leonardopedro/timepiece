import BookProof.ChapterEsaOneParticleDGamma
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Audit of the essentially-self-adjoint one-particle second quantization

Axiom check for the results of `BookProof/Toolbox/ChapterEsaOneParticleDGamma.lean`.  Only the
standard axioms `propext`, `Classical.choice`, `Quot.sound` may appear.
-/

open BookProof.EsaOneParticle

#audit_axioms BookProof.EsaOneParticle.esa_graph_le
#audit_axioms BookProof.EsaOneParticle.exists_pow_of_mem_corePow
#audit_axioms BookProof.EsaOneParticle.fockSectorCore_graph_le
#audit_axioms BookProof.EsaOneParticle.isGraphCore_clDom
#audit_axioms BookProof.EsaOneParticle.closureSelfAdjoint
#audit_axioms BookProof.EsaOneParticle.essentiallySelfAdjointOn_fockSectorDom_esa
#audit_axioms BookProof.EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa
#audit_axioms BookProof.EsaOneParticle.symmetricOn_dGammaCoreOp_of_esa
#audit_axioms BookProof.EsaOneParticle.essentiallySelfAdjointOn_of_selfAdjoint
#audit_axioms BookProof.EsaOneParticle.essentiallySelfAdjointOn_restrict
#audit_axioms BookProof.EsaOneParticle.not_isSelfAdjointOn_restrict
#audit_axioms BookProof.EsaOneParticle.positionCore_essentiallySelfAdjoint
#audit_axioms BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn
#audit_axioms BookProof.EsaOneParticle.dGamma_positionCore_essentiallySelfAdjoint
