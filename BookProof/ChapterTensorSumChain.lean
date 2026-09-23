import Mathlib
import BookProof.ChapterTensorSumEsa

/-!
# Finitely many factors: the total tensor sum `∑ᵢ 1 ⊗ ⋯ ⊗ Aᵢ ⊗ ⋯ ⊗ 1`

`BookProof/ChapterTensorSumEsa.lean` proves the two-factor statement: for symmetric,
essentially self-adjoint `A` on `H` and `B` on `K`, the tensor sum `A ⊗ 1 + 1 ⊗ B` is
essentially self-adjoint on the algebraic tensor product of the two domains inside `H ⊗̂ K`.
Crucially the *conclusion* is of the same shape as the two *hypotheses* — symmetric,
essentially self-adjoint, densely defined on a Hilbert space — so the statement iterates.

This module performs the iteration.  `EsaOp` bundles exactly the data the two-factor theorem
consumes and produces (a Hilbert space, a dense domain, a symmetric operator on it, and
essential self-adjointness), `pair` is the two-factor theorem in that vocabulary, and `chain`
folds `pair` along a list.  The result is the total tensor sum of an arbitrary finite family
of *different* operators on *different* Hilbert spaces:

`H = A₁ ⊗ 1 ⊗ ⋯ ⊗ 1 + 1 ⊗ A₂ ⊗ 1 ⊗ ⋯ ⊗ 1 + ⋯ + 1 ⊗ ⋯ ⊗ 1 ⊗ A_n`,

the Hamiltonian of `n` non-interacting degrees of freedom, essentially self-adjoint on the
algebraic tensor product of the `n` domains, with a complete unitary flow.

## Contents

* `EsaOp` — the bundle; `pair` — the two-factor step; `pair_op_tmul` — the operator really is
  `(x ⊗ y) ↦ A x ⊗ y + x ⊗ B y`.
* `chain`, `chain_dense`, `chain_symmetric`, **`chain_esa`** — the `n`-factor tensor sum is
  densely defined, symmetric and essentially self-adjoint; `chain_stone_flow` — its unitary
  group.
* `chain_singleton`, `chain_cons` — the two recursion equations.
* `posEsaOp`, `positionChain_esa` — the concrete instance: `n` copies of the (unbounded)
  position operator of `ℓ²(ℤ)`, whose total tensor sum `k₁ + k₂ + ⋯ + kₙ` is essentially
  self-adjoint.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorSumChain

open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumEsa
  BookProof.ChapterStoneResolvent BookProof.StoneBridge BookProof.GraphCore
  BookProof.EsaClosure

noncomputable section

/-- A symmetric operator, essentially self-adjoint on a dense domain of a Hilbert space:
exactly the data the two-factor tensor-sum theorem consumes, and exactly what it produces. -/
structure EsaOp where
  /-- the Hilbert space -/
  space : IPSpace
  /-- it is complete -/
  complete : CompleteSpace space.carrier
  /-- the domain -/
  dom : Submodule ℂ space.carrier
  /-- the operator -/
  op : dom →ₗ[ℂ] space.carrier
  /-- the domain is dense -/
  dense : Dense (dom : Set space.carrier)
  /-- the operator is symmetric -/
  sym : SymmetricOn dom op
  /-- and essentially self-adjoint -/
  esa : EssentiallySelfAdjointOn dom op

/-- **The two-factor step.**  The tensor sum `A ⊗ 1 + 1 ⊗ B` of two members of the class is
again a member of the class, on the completed tensor product of the two spaces. -/
def pair (E F : EsaOp) : EsaOp :=
  haveI := E.complete
  haveI := F.complete
  { space := ⟨ctensor E.space F.space⟩
    complete := inferInstanceAs (CompleteSpace (ctensor E.space F.space))
    dom := cpairDom E.space F.space E.dom F.dom
    op := cpairOp E.space F.space E.dom F.dom E.op F.op
    dense := dense_cpairDom E.space F.space E.dom F.dom E.dense F.dense
    sym := symmetricOn_cpairOp E.space F.space E.dom F.dom E.op F.op E.sym F.sym
    esa := essentiallySelfAdjointOn_cpairDom_esa E.op F.op E.dense F.dense E.sym F.sym
      E.esa F.esa }

@[simp] theorem pair_space (E F : EsaOp) :
    (pair E F).space = ⟨ctensor E.space F.space⟩ := rfl

@[simp] theorem pair_dom (E F : EsaOp) :
    (pair E F).dom = cpairDom E.space F.space E.dom F.dom := rfl

/-- The operator of `pair E F` acts on an elementary tensor as `A x ⊗ y + x ⊗ B y`. -/
theorem pair_op_tmul (E F : EsaOp) (x : E.dom) (y : F.dom)
    (v : (pair E F).dom)
    (hv : (v : (pair E F).space.carrier)
      = pairEmb E.space F.space (inclPair E.space F.space E.dom F.dom (x ⊗ₜ[ℂ] y))) :
    (pair E F).op v
      = pairEmb E.space F.space
        ((E.op x) ⊗ₜ[ℂ] (y : F.space.carrier) + (x : E.space.carrier) ⊗ₜ[ℂ] (F.op y)) := by
  have h := cpairOp_apply E.space F.space E.dom F.dom E.op F.op v (x ⊗ₜ[ℂ] y) hv
  simpa [sumPoly_tmul] using h

/-- The total tensor sum of a nonempty finite family, by folding the two-factor step. -/
def chain : EsaOp → List EsaOp → EsaOp
  | E, [] => E
  | E, (F :: rest) => pair E (chain F rest)

@[simp] theorem chain_singleton (E : EsaOp) : chain E [] = E := rfl

@[simp] theorem chain_cons (E F : EsaOp) (L : List EsaOp) :
    chain E (F :: L) = pair E (chain F L) := rfl

/-- **The `n`-factor tensor sum is essentially self-adjoint.**  For an arbitrary finite family
of symmetric operators, each essentially self-adjoint on a dense domain of its own Hilbert
space, the total tensor sum `A₁ ⊗ 1 ⊗ ⋯ + ⋯ + 1 ⊗ ⋯ ⊗ Aₙ` is essentially self-adjoint on the
algebraic tensor product of the `n` domains.  No boundedness, no positivity, no relative
bound. -/
theorem chain_esa (E : EsaOp) (L : List EsaOp) :
    EssentiallySelfAdjointOn (chain E L).dom (chain E L).op := (chain E L).esa

/-- The same operator is symmetric. -/
theorem chain_symmetric (E : EsaOp) (L : List EsaOp) :
    SymmetricOn (chain E L).dom (chain E L).op := (chain E L).sym

/-- And densely defined. -/
theorem chain_dense (E : EsaOp) (L : List EsaOp) :
    Dense (((chain E L).dom : Submodule ℂ (chain E L).space.carrier) :
      Set (chain E L).space.carrier) := (chain E L).dense

/-- **The unitary flow of the `n`-factor tensor sum.** -/
theorem chain_stone_flow (E : EsaOp) (L : List EsaOp) :
    ∃ (G : UnboundedSelfAdjoint (chain E L).space.carrier)
      (U : ℝ → ((chain E L).space.carrier →L[ℂ] (chain E L).space.carrier)),
      IsSelfAdjointExtension (chain E L).op G.op ∧ IsStoneFlow G U :=
  haveI := (chain E L).complete
  exists_stone_flow_of_esa _ (chain E L).dense (chain E L).sym (chain E L).esa

/-! ## A genuinely unbounded instance: `n` copies of the position operator -/

section Position

open BookProof.ChapterStoneSeparable BookProof.ChapterUnboundedPosition
  BookProof.FlowDGamma BookProof.EsaOneParticle

/-- The position operator of `ℓ²(ℤ)` as a member of the class. -/
def posEsaOp : EsaOp where
  space := L2ZSpace
  complete := inferInstanceAs (CompleteSpace L2ZSpace.carrier)
  dom := (mulSA positionField).domain
  op := (mulSA positionField).op
  dense := (mulSA positionField).denseDomain
  sym := (mulSA positionField).symmetric
  esa := essentiallySelfAdjointOn_of_selfAdjoint (Hs := L2ZSpace) (mulSA positionField)

/-- **`n` non-interacting position degrees of freedom.**  The total tensor sum
`k₁ + k₂ + ⋯ + kₙ` of `n` copies of the unbounded position operator of `ℓ²(ℤ)` is essentially
self-adjoint on the algebraic tensor product of the `n` maximal domains. -/
theorem positionChain_esa (n : ℕ) :
    EssentiallySelfAdjointOn (chain posEsaOp (List.replicate n posEsaOp)).dom
      (chain posEsaOp (List.replicate n posEsaOp)).op :=
  chain_esa posEsaOp (List.replicate n posEsaOp)

/-- The one-particle operator of the previous theorem is genuinely unbounded. -/
theorem posEsaOp_not_bounded :
    ¬ ∃ C : ℝ, ∀ x : posEsaOp.dom,
      ‖posEsaOp.op x‖ ≤ C * ‖(x : posEsaOp.space.carrier)‖ :=
  mulSA_position_unbounded

end Position

end

end BookProof.TensorSumChain
