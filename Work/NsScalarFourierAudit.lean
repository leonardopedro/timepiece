import BookProof.Ns.ChapterNsScalarFourier
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the spatial Fourier transform on the scalar one-particle space

Every result of `BookProof/Ns/ChapterNsScalarFourier.lean` must rest on the standard axioms only:
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NsScalarFourier.nsScalarFourier_norm
#audit_axioms BookProof.NsScalarFourier.nsScalarFourier_apply
#audit_axioms BookProof.NsScalarFourier.scalarFibreOp_apply
#audit_axioms BookProof.NsScalarFourier.fibreOp_fibMk
#audit_axioms BookProof.NsScalarFourier.scalarFibreOp_prodMk
#audit_axioms BookProof.NsScalarFourier.nsScalarFourier_scalarFibreOp
#audit_axioms BookProof.NsScalarFourier.nsScalarFourier_prodMk_eq
#audit_axioms BookProof.NsScalarFourier.nsScalarFourier_fibreFourier
