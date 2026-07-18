import RiemannProof.RandomMap2

/-!
# RCP–RandomMap2 bridge

This module implements roadmap item R5 without creating an import cycle between
`SchoenfeldPRA` and `RandomMap2`.  It identifies the two marginals of the
RandomMap2 state law: the finite head has its prescribed distribution, while
the infinite tail has exactly the RCP prior `rcpPriorOnSubstrate`.  The final
theorem packages these identifications together with dimensional reduction of
cylindrical outer wave-functions.
-/

open MeasureTheory ProbabilityTheory Complex
open PnpProof.Kopperman
open SchoenfeldPRA

noncomputable section

namespace RcpRandomMapBridge

/-
The RandomMap2 tail law is definitionally the RCP substrate prior.
-/
theorem tailMeasure_eq_rcpPrior : tailMeasure = rcpPriorOnSubstrate := by
  rfl

/-
The first marginal of the RandomMap2 state law is the prescribed finite
head distribution.
-/
theorem map_fst_stateMeasure (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] :
    Measure.map Prod.fst (stateMeasure N headDist) = headDist := by
  ext s hs
  simp [stateMeasure]

/-
The second marginal of the RandomMap2 state law is exactly the RCP prior on
Kopperman's substrate.
-/
theorem map_snd_stateMeasure (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] :
    Measure.map Prod.snd (stateMeasure N headDist) = rcpPriorOnSubstrate := by
  ext s hs
  simp [stateMeasure, tailMeasure]

/-
Roadmap R5 headline: the decoupled state has the requested finite head and
RCP tail marginals, and every pair of cylindrical outer wave-functions reduces
to an `L²` inner-product integral over the finite head.
-/
theorem rcp_stateMeasure_decoupling {N : ℕ}
    {headDist : Measure (InnerHead N)} [IsProbabilityMeasure headDist]
    (Ψ₁ Ψ₂ : OuterWaveFunction N headDist)
    (hcyl₁ : dependsOnlyOnHead (Ψ₁ : InnerSpace N → ℂ))
    (hcyl₂ : dependsOnlyOnHead (Ψ₂ : InnerSpace N → ℂ)) :
    Measure.map Prod.fst (stateMeasure N headDist) = headDist ∧
    Measure.map Prod.snd (stateMeasure N headDist) = rcpPriorOnSubstrate ∧
    ∃ (g₁ g₂ : Lp ℂ 2 headDist),
      inner ℂ Ψ₁ Ψ₂ = ∫ x, g₁ x * star (g₂ x) ∂headDist := by
  exact ⟨map_fst_stateMeasure N headDist, map_snd_stateMeasure N headDist,
    outer_inner_reduces_to_head Ψ₁ Ψ₂ hcyl₁ hcyl₂⟩

#print axioms tailMeasure_eq_rcpPrior
#print axioms map_fst_stateMeasure
#print axioms map_snd_stateMeasure
#print axioms rcp_stateMeasure_decoupling

end RcpRandomMapBridge
