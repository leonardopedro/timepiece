import BookProof.ChapterScalaronFiberFL
import BookProof.ChapterSelfAdjointCoreEsa

/-!
# Obligation (i): a Faris–Lavine comparison operator is essentially self-adjoint on its
graph core

`CONSOLIDATED_PLAN.md` §D6b keeps one standing obligation for every Faris–Lavine route in
this development: **(i)** the comparison operator `N` must be essentially self-adjoint *on
the core actually chosen*, not merely self-adjoint on its own (Friedrichs) domain.  This
chapter discharges it once and for all, in the vocabulary the route chapters use
(`BookProof.QgOuterFockFL.Comparison` and the graph core
`BookProof.QgOuterFockCoreFL.IsGraphCore`).

`BookProof.ScalaronFiberFL.isGraphCore_of_esa` already proves one direction — essential
self-adjointness on a core makes it a graph core.  Here is the converse, and hence the
equivalence:

* `comparison_essentiallySelfAdjointOn_dom` — a comparison operator is essentially
  self-adjoint on its **own domain** (it is self-adjoint there, by `Comparison.selfAdjoint`).
* `esa_of_isGraphCore` — **obligation (i)**: if `C₀ ≤ 𝒟(N)` is dense in the graph norm of
  `N` and `N` restricts to `P` on it, then `P` is essentially self-adjoint on `C₀`.
* `isGraphCore_iff_esa` — the two notions coincide: for a comparison operator, "graph core"
  and "core of essential self-adjointness" are the same thing.

So in every route chapter that already exhibits a graph core for its comparison operator —
`harmFried_isGraphCore` (the Gauss–polynomial core of the `d`-dimensional oscillator
`−Δ + ‖x‖²/4`) and `secN_isGraphCore` (the compactly-supported smooth core of the
scalaron-wall comparison) — obligation (i) is now a theorem, with no further work.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ComparisonCoreEsa

open BookProof.FarisLavine BookProof.EsaClosure
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A comparison operator is a self-adjoint extension of itself. -/
theorem comparison_isSelfAdjointExtension (C : Comparison F) :
    IsSelfAdjointExtension C.op C.op :=
  ⟨fun x => ⟨x.2, rfl⟩, C.sym, C.selfAdjoint⟩

/-- **A comparison operator is essentially self-adjoint on its own domain.** -/
theorem comparison_essentiallySelfAdjointOn_dom (C : Comparison F) :
    EssentiallySelfAdjointOn C.dom C.op :=
  BookProof.SelfAdjointCoreEsa.essentiallySelfAdjointOn_dom_of_isSelfAdjointExtension
    (comparison_isSelfAdjointExtension C)

/-- A graph core in the sense of the route chapters is a graph core in the sense of the
core-transfer chapter. -/
theorem graphCore_of_isGraphCore {C : Comparison F} {C₀ : Submodule ℂ F}
    (hgc : IsGraphCore C C₀) : BookProof.GraphCore.IsGraphCore C₀ C.op := by
  intro x ε hε
  obtain ⟨y, hy, h1, h2⟩ := hgc.approx x ε hε
  exact ⟨y, hy, by rwa [norm_sub_rev], by rwa [norm_sub_rev]⟩

/-- **Obligation (i).**  An operator that a Faris–Lavine comparison operator restricts to on
a graph core is essentially self-adjoint on that core. -/
theorem esa_of_isGraphCore (C : Comparison F) (C₀ : Submodule ℂ F) (hle : C₀ ≤ C.dom)
    (P : C₀ →ₗ[ℂ] F) (hext : ∀ p : C₀, C.op ⟨(p : F), hle p.2⟩ = P p)
    (hgc : IsGraphCore C C₀) : EssentiallySelfAdjointOn C₀ P := by
  have hrestrict : BookProof.GraphCore.restrictOp C.op hle = P :=
    LinearMap.ext fun p => hext p
  have h := BookProof.SelfAdjointCoreEsa.essentiallySelfAdjointOn_of_graphCore_selfAdjoint
    (comparison_isSelfAdjointExtension C) hle (graphCore_of_isGraphCore hgc)
  rwa [hrestrict] at h

/-- **Graph core = core of essential self-adjointness**, for a Faris–Lavine comparison
operator.  The forward direction is `BookProof.ScalaronFiberFL.isGraphCore_of_esa`. -/
theorem isGraphCore_iff_esa [CompleteSpace F] (C : Comparison F) (C₀ : Submodule ℂ F)
    (hle : C₀ ≤ C.dom)
    (P : C₀ →ₗ[ℂ] F) (hext : ∀ p : C₀, C.op ⟨(p : F), hle p.2⟩ = P p) :
    IsGraphCore C C₀ ↔ EssentiallySelfAdjointOn C₀ P :=
  ⟨esa_of_isGraphCore C C₀ hle P hext, isGraphCore_of_esa C C₀ hle P hext⟩

end BookProof.ComparisonCoreEsa
