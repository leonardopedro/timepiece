import BookProof.ChapterFriedrichsExtension.Part1
import BookProof.ChapterFriedrichsExtension.Part2

/-!
# The Friedrichs extension of an **unbounded** positive symmetric operator

`CONSOLIDATED_PLAN.md` §11.4 records two plan items that stand between the proved
Hashimoto/shift-invert machinery and the full claim *"the unbounded continuum
Weyl-gauge Hamiltonian has a Friedrichs extension, and the infinite
Hashimoto/SIRK limit selects exactly it"*.  This module closes the first one.

Until now the Friedrichs theorem entered the project in two forms:

* as a **named hypothesis**
  (`BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded`), shown
  consistent only for an operator already defined on the whole space;
* **discharged by construction, but only in the bounded regime**
  (`BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded`: a densely defined
  symmetric positive operator with `‖H x‖ ≤ C‖x‖` extends continuously).

Here the theorem is **proved with no boundedness hypothesis at all**: every
densely defined, symmetric, positive operator on a complex Hilbert space has a
positive self-adjoint extension.  The construction is the classical one, carried
out in full:

**Part A — the form space.**  The domain carries the *form inner product*
`⟪x, y⟫₁ = ⟪x, y⟫ + ⟪x, H y⟫`.  Symmetry makes it Hermitian and positivity makes
it positive definite (indeed `‖x‖ ≤ ‖x‖₁`), so `FormDom P` — the domain retyped
with that inner product — is an inner product space (`instCore`, `instIPS`), and
`FormSpace P`, its completion, is a Hilbert space.

**Part B — the form space sits inside `F`.**  The inclusion `FormDom P → F` is
norm-decreasing, so it extends to `formExt P : FormSpace P →L[ℂ] F`.  The key
identity `inner_coe_eq` — `⟪x, k⟫₁ = ⟪x + H x, formExt k⟫` for a domain vector
`x` — is the closability of the form in disguise, and it gives
`formExt_injective`: *the form completion adds no ghost vectors*.  This is the
one place where symmetry and positivity of `H` do analytic work.

**Part C — Riesz representation.**  For `u : F` the functional
`k ↦ ⟪u, formExt k⟫` is continuous on the Hilbert space `FormSpace P`, so it is
represented by a vector `formRiesz P u`, and
`friedrichsResolvent P u = formExt P (formRiesz P u)` is a bounded, injective,
positive, self-adjoint operator on `F` with `‖·‖ ≤ 1`.  It is `(H + 1)⁻¹` on the
nose: `friedrichsResolvent_shift` proves `S (x + H x) = x` for every `x` in the
domain.

**Part D — the extension.**  Feeding `S` to the project's own converse
construction `BookProof.HashimotoShiftInvert.invShiftOperator` (`A = S⁻¹ − 1`)
produces the extension, and `friedrichs_extension_exists` states it in the form
the rest of the project consumes,
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`.  Consequences:

* `friedrichs_hypothesis_holds` — the named hypothesis of
  `friedrichs_extension_of_semibounded` is a theorem, not an assumption;
* `friedrichs_extension_of_semibounded_below` — the classical statement, for a
  symmetric operator that is merely *bounded below* (`⟪x, Hx⟫ ≥ −c‖x‖²`), by the
  shift `H ↦ H + c`;
* `weyl_friedrichs_extension_unconditional` — the Weyl-gauge Yang–Mills
  Hamiltonian `½ Σ πᵢ² + ½ Σ Bₐ²` on any dense domain has a Friedrichs
  extension, with **no boundedness hypothesis** (plan item §11.4.1);
* `weyl_hashimoto_selects_friedrichs` — combining with
  `hashimoto_shiftInvert_selects_friedrichs`: in the occupation-number (Hermite)
  realization the extension *exists* and the Hashimoto/SIRK algorithm converges
  to it and to nothing else;
* `unbounded_friedrichs_example` — the construction applied to a genuinely
  unbounded operator (`A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, restricted to the finite-mode
  domain), so nothing here is vacuous.

## Scope

This is the abstract Friedrichs theorem and its application to the Weyl-gauge
Hamiltonian *as an operator on a Hilbert space*.  It does **not** claim the mass
gap, nor a differential (field-space) realization of the magnetic-field operator
`B_{i a}` — that is the second, definitional item of §11.4, settled there in
favour of the occupation-number/Hermite realization.
-/
