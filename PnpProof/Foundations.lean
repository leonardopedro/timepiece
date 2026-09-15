import BookProof.PhysMeasureBasis

/-!
# Part 1: Foundations — measure theory (promoted)

**Promoted (2026-08-09).**  The mathematical content of this module has been
promoted out of `PnpProof/` into `BookProof/PhysMeasureBasis.lean` (see
`PLAN_LEAN_SPECIALIST_COHERENT.md` Part G): it is general mathematics — the
measure-theoretic, functional-analytic and hyperspherical/Gaussian backbone —
reused by the QFM/Fork thread, and `PnpProof/` must be a one-way leaf of the
dependency graph.  This file is now a thin re-export so that the P≠NP
development keeps its familiar names; **no proof lives here any more**.
-/

namespace PnpProof

export PhysMeasureBasis (unitMeasure squareMeasure null_singleton_volume null_singleton
  countable_null selection_exists no_history countable_atoms atomless_mutuallySingular_atomic
  cdf_jump_separation cond_diffuse_noAtoms)

end PnpProof
