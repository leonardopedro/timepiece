import PnpProof.FunctionSpace
import PnpProof.SphereGaussian
import PnpProof.Model
import BookProof.PhysMehler

/-!
# The Kopperman formalism (promoted)

**Promoted (2026-08-09).**  The mathematical content of this module has been
promoted out of `PnpProof/` into `BookProof/PhysMehler.lean` (see
`PLAN_LEAN_SPECIALIST_COHERENT.md` Part G): it is general mathematics — the
measure-theoretic, functional-analytic and hyperspherical/Gaussian backbone —
reused by the QFM/Fork thread, and `PnpProof/` must be a one-way leaf of the
dependency graph.  This file is now a thin re-export so that the P≠NP
development keeps its familiar names; **no proof lives here any more**.
-/

namespace PnpProof.Kopperman

export PhysMehler (Formalism Substrate substrate_separable substrate_decidable_skeleton
  MehlerPrior mehler_isProbability mehler_concentrates_on_sphere admits_atomless_prior
  model_has_prior substrate_orthonormal_pair exists_atomless_prob_substrate formalismOfPrior
  prior_formalismOfPrior prior_surjective_onto_atomless nonempty_formalism_substrate
  koppermanSubstrate Pi02 interpPi02 arith_truth_invariant pi02_invariant_of_formalism
  interpPi02_eq)

/-- The concrete prior used for the model statements (`Model.prior`) is atomless:
    the realized "political choice" measure of this formalism.  This is the one
    genuinely P≠NP-specific statement of the old `Kopperman.lean`; the analytic
    core it rests on now lives in `BookProof/PhysMehler.lean`. -/
theorem modelPrior_atomless : ∀ g : C(K, ℝ), prior {g} = 0 := prior_atomless

end PnpProof.Kopperman
