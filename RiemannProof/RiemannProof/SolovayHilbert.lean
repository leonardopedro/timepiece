import RiemannProof.RcpRandomMapBridge

/-!
# The complete Solovay head space

This module implements roadmap item R6 downstream of `RandomMap2`, avoiding an
import cycle with the historical `SchoenfeldPRA` module.

The complete space is deliberately the finite-head `L²` space, rather than the
full product `L²` space.  Its canonical linear-isometric lift to the product is
composition with `Prod.fst`.  Thus every represented observable is exactly
invariant under changing the Kopperman tail, and the lifted `L²` class agrees
almost everywhere with that tail-invariant representative.  This is the precise
formal content of the roadmap's claim that the outer language cannot inspect,
name, or diagonalize against an infinite tail.
-/

open MeasureTheory ProbabilityTheory Complex
open SchoenfeldPRA

noncomputable section

namespace SolovayHilbert

/-- The complete Solovay space is the `L²` space of the finite Tarski head. -/
abbrev SolovayHilbertSpace (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] := Lp ℂ 2 headDist

/-- The head projection preserves the product state measure. -/
theorem headProjection_measurePreserving (N : ℕ)
    (headDist : Measure (InnerHead N)) [IsProbabilityMeasure headDist] :
    MeasurePreserving (Prod.fst : InnerSpace N → InnerHead N)
      (stateMeasure N headDist) headDist := by
  refine ⟨measurable_fst, ?_⟩
  exact RcpRandomMapBridge.map_fst_stateMeasure N headDist

/-- Canonical linear-isometric inclusion of the complete finite-head space into
product-space outer wave-functions. -/
noncomputable def solovayLift (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] :
    SolovayHilbertSpace N headDist →ₗᵢ[ℂ] OuterWaveFunction N headDist :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst
    (headProjection_measurePreserving N headDist)

/-- A pointwise representative of a Solovay observable on the full state space.
It reads the finite head and ignores the tail. -/
def solovayObservable {N : ℕ} {headDist : Measure (InnerHead N)}
    [IsProbabilityMeasure headDist] (f : SolovayHilbertSpace N headDist) :
    InnerSpace N → ℂ := fun z => f z.1

/-- Pointwise tail invariance: changing only the infinite tail cannot change a
Solovay observable. -/
theorem solovayObservable_tail_invariant {N : ℕ}
    {headDist : Measure (InnerHead N)} [IsProbabilityMeasure headDist]
    (f : SolovayHilbertSpace N headDist) (x : InnerHead N) (u v : InnerTail) :
    solovayObservable f (x, u) = solovayObservable f (x, v) := by
  rfl

/-- The canonical `L²` lift agrees almost everywhere with the explicit
head-only representative. -/
theorem solovayLift_ae_eq_observable {N : ℕ}
    {headDist : Measure (InnerHead N)} [IsProbabilityMeasure headDist]
    (f : SolovayHilbertSpace N headDist) :
    ((solovayLift N headDist f : OuterWaveFunction N headDist) :
        InnerSpace N → ℂ) =ᵐ[stateMeasure N headDist] solovayObservable f := by
  simpa [solovayObservable, solovayLift] using
    (Lp.coeFn_compMeasurePreserving f
      (headProjection_measurePreserving N headDist))

/-- Almost-everywhere form of the cylindrical condition, appropriate for `L²`
equivalence classes. -/
def DependsOnlyOnHeadAE {N : ℕ} {headDist : Measure (InnerHead N)}
    [IsProbabilityMeasure headDist] (f : OuterWaveFunction N headDist) : Prop :=
  ∃ g : InnerHead N → ℂ,
    (f : InnerSpace N → ℂ) =ᵐ[stateMeasure N headDist] g ∘ Prod.fst

/-- **R6 headline.** Completeness does not reopen access to the infinite tail:
every element of the complete Solovay space lifts to an outer wave-function
which depends only on the finite head (up to the equality intrinsic to `L²`). -/
theorem godelian_trapdoor_sealed {N : ℕ}
    {headDist : Measure (InnerHead N)} [IsProbabilityMeasure headDist]
    (f : SolovayHilbertSpace N headDist) :
    DependsOnlyOnHeadAE (solovayLift N headDist f) := by
  refine ⟨fun x => f x, ?_⟩
  simpa [solovayObservable, Function.comp_def] using
    (solovayLift_ae_eq_observable f)

end SolovayHilbert
