/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceFlowMatrixElement`.

That module derives the two-point (matrix-element) form of `hflow`: from the strong right
derivative `−H z` of every orbit at `0⁺`, the scalar orbit `τ ↦ ⟪y, P τ z⟫` has right derivative
`⟪y, −H z⟫` (`hasDerivWithinAt_inner_hsEvol`), equivalently its difference quotients converge
(`tendsto_slope_inner_hsEvol`).  Both must rest on `propext`, `Classical.choice`, `Quot.sound`
only.
-/
import BookProof.OSReconstruction.HalfSpaceFlowMatrixElement
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction
open scoped RealInnerProductSpace

#audit_axioms hasDerivWithinAt_inner_hsEvol
#audit_axioms tendsto_slope_inner_hsEvol
