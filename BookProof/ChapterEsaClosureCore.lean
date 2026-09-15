import BookProof.ChapterEsaClosureCore.Part1
import BookProof.ChapterEsaClosureCore.Part2

/-!
# Essential self-adjointness selects a **unique** self-adjoint operator

Every essential-self-adjointness theorem of this development — the Faris–Lavine
chain of `BookProof.ChapterFarisLavine`, the Navier–Stokes sequence-space chain
(`BilinearEsa`, `AffineFiber`, `AffineBlock`, `SignFlip`, `SignedShift`,
`ThreeComponent`), the Hermite-core theorems of the gravity and Yang–Mills
routes — is stated as *trivial deficiency*: the only vector `w` with
`⟪T v, w⟫ = ± i ⟪v, w⟫` for every `v` in the core is `w = 0`
(`BookProof.FarisLavine.EssentiallySelfAdjointOn`).

That is the classical criterion, but it is a statement *about* the operator on
the core; the object the physics needs — the self-adjoint generator whose
unitary group is the flow, and the operator whose resolvent the
Hashimoto/SIRK algorithm computes — is the **closure**.  This module builds it
and proves the two facts that make "essentially self-adjoint" mean what it says:

* `exists_isSelfAdjointExtension_of_esa` — **existence**: a densely defined
  symmetric operator with trivial deficiency has a self-adjoint extension,
  namely the closure of its graph.  The construction is explicit
  (`clGraph`, `clDom`, `clExt`), and no positivity, boundedness or
  semiboundedness hypothesis is used.
* `isSelfAdjointExtension_unique_of_esa` — **uniqueness**: *any* self-adjoint
  extension of an essentially self-adjoint operator has the same domain and the
  same values.  So the closure is the only self-adjoint operator the core
  determines.

`IsSelfAdjointExtension` is the positivity-free companion of
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`;
`isSelfAdjointExtension_of_positive` records that a positive self-adjoint
extension is one.

## The Hashimoto/SIRK consequence

`BookProof.ChapterHashimotoComplexShifts` runs the shift-invert rational Krylov
algorithm at non-real shifts, where positivity of the operator is not needed —
only symmetry and the self-adjointness criterion.  Its headline
(`hashimoto_multishift_selects_friedrichs`) was nevertheless stated for a
*positive* self-adjoint extension.  `hashimoto_multishift_selects_esa` removes
the positivity hypothesis and feeds it the closure produced here: for an
essentially self-adjoint operator on a dense core, and for an arbitrary
sequence of non-real shifts, the resolvents `X_j = (γ_j − A)⁻¹` exist, are
bounded by `1/|Im γ_j|`, satisfy the resolvent identity and the SIRK relation,
have Galerkin truncations converging strongly, and each one of them determines
`A` — the *unique* self-adjoint extension — completely.

## Honest boundary

Nothing here is a statement about any particular differential operator; it is
the abstract von Neumann theory (deficiency indices `(0,0)` ⟹ unique
self-adjoint extension) that the concrete chapters instantiate.
-/
