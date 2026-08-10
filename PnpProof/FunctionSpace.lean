import PnpProof.Foundations
import BookProof.PhysFunctionalAnalysis

/-!
# Part 3: Function space (promoted)

**Promoted (2026-08-09).**  The mathematical content of this module has been
promoted out of `PnpProof/` into `BookProof/PhysFunctionalAnalysis.lean` (see
`PLAN_LEAN_SPECIALIST_COHERENT.md` Part G): it is general mathematics — the
measure-theoretic, functional-analytic and hyperspherical/Gaussian backbone —
reused by the QFM/Fork thread, and `PnpProof/` must be a one-way leaf of the
dependency graph.  This file is now a thin re-export so that the P≠NP
development keeps its familiar names; **no proof lives here any more**.
-/

namespace PnpProof

export PhysFunctionalAnalysis (l2_separable linf_not_separable sqrt_density_memLp
  sqrt_density_norm polynomial_dense_L2 countable_of_separated exists_l2_iso
  hilbert_classification exists_atomless_sphere_measure)

end PnpProof
