import Mathlib

/-!
# A self-adjoint operator has no proper symmetric extension

This module records the logical step that turns one approximation into an identification.

Suppose a symmetric operator `G` is given on a dense core, so that its closure `G.closure` is the
candidate self-adjoint operator, and suppose a *second* operator `A` is known to be self-adjoint and
to satisfy `A ≤ G.closure` — that is, `A` is defined wherever `G`'s core is, agrees with `G` there,
and takes those values.  Then `A = G.closure`: there is nothing left to prove, and in particular
`G` is essentially self-adjoint.

The reason is that a self-adjoint operator is *maximal* among symmetric operators.  If `A ≤ B` with
`A` self-adjoint and `B` symmetric, then for `y ∈ B.domain` the functional
`x ↦ ⟪y, A x⟫` on `A.domain` is represented by `B y` (this is `B`'s symmetry, read through
`A ⊆ B`), so `y ∈ A†.domain = A.domain` and `A y = B y`; hence `B ≤ A`.

`eq_of_le_of_isSelfAdjoint` is the general statement, and `closure_eq_of_le` is the form used by the
S0 programme: the identification of the polynomial core with the closure of `gaussOp` needs only the
*graph-norm* approximation of polynomial classes by compactly supported `C²` classes, and not the
reverse approximation, because the polynomial core is already self-adjoint
(`BookProof.YangMillsPolyCore.polyCore_essentiallySelfAdjoint`).

## Main results

* `SymmetricOp` — a formal adjoint of itself;
* `SymmetricOp.le_adjoint` — a symmetric operator sits inside its adjoint;
* `eq_of_le_of_isSelfAdjoint` — maximality of self-adjoint operators;
* `closure_eq_of_le` — the closure identified from one inclusion.
-/

namespace BookProof.SelfAdjointMaximal

open scoped InnerProductSpace

open LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Symmetric operators**: those which are a formal adjoint of themselves, i.e.
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x`, `y` in the domain. -/
def SymmetricOp (T : E →ₗ.[𝕜] E) : Prop := T.IsFormalAdjoint T

/-- A symmetric, densely defined operator is contained in its adjoint. -/
theorem SymmetricOp.le_adjoint {T : E →ₗ.[𝕜] E} (hT : SymmetricOp T)
    (hD : Dense (T.domain : Set E)) : T ≤ T.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint hD hT

/-- **A self-adjoint operator is maximal among symmetric ones**: if `A ≤ B`, `A` is self-adjoint
and `B` is symmetric, then `A = B`.

The proof is the elementwise one.  For `y ∈ B.domain` the linear functional
`x ↦ ⟪y, A x⟫` on `A.domain` is bounded, because `A x = B x` there and `B` is symmetric, so
`A.adjoint` (which is `A`) is defined at `y` and `A y` is that functional's representative; both
`A y` and `B y` represent it, so they agree. -/
theorem eq_of_le_of_isSelfAdjoint {A B : E →ₗ.[𝕜] E} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hB : SymmetricOp B) : A = B := by
  have hAadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hdom : B.domain ≤ A.domain := by
    intro y hy
    have hex : ∃ w : E, ∀ x : A.domain, inner 𝕜 w (x : E) = inner 𝕜 y (A x) := by
      refine ⟨B ⟨y, hy⟩, fun x => ?_⟩
      have hx : (x : E) ∈ B.domain := hAB.1 x.2
      have h1 : A x = B ⟨(x : E), hx⟩ := hAB.2 rfl
      have h2 : inner 𝕜 (B ⟨y, hy⟩) (x : E) = inner 𝕜 y (B ⟨(x : E), hx⟩) :=
        hB ⟨y, hy⟩ ⟨(x : E), hx⟩
      rw [← h1] at h2
      exact h2
    have hmem : y ∈ A.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists y hex
    rwa [hAadj] at hmem
  exact LinearPMap.eq_of_le_of_domain_eq hAB (le_antisymm hAB.1 hdom)

/-- **The closure is identified from a single inclusion.**  If `A` is self-adjoint and sits inside
the closure of a symmetric `G`, then `A` *is* that closure; no second approximation is needed. -/
theorem closure_eq_of_le {A G : E →ₗ.[𝕜] E} (hAG : A ≤ G.closure) (hA : IsSelfAdjoint A)
    (hG : SymmetricOp G.closure) : A = G.closure :=
  eq_of_le_of_isSelfAdjoint hAG hA hG

end BookProof.SelfAdjointMaximal
