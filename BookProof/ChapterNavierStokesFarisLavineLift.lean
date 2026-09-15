import BookProof.ChapterNavierStokesFarisLavineLift.Part1
import BookProof.ChapterNavierStokesFarisLavineLift.Part2

/-!
# The one-particle comparison operator, and how the Faris–Lavine bounds lift

Companion to `BookProof.ChapterNavierStokesSecondQuant`, which lifts *essential
self-adjointness* from the sectors of a Fock space to the finite-particle
domain.  This module supplies the other two ingredients of the Faris–Lavine
route to essential self-adjointness of the Navier–Stokes Hamiltonian:

**1. The one-particle comparison operator.**  In the fiber space the advection
term is a *linear* vector field `V(u)`, so the natural comparison operator is
`n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I`.  `ComparisonData` packages the (symmetric) momenta
`πᵢ` and drifts `Vᵢ` on a dense domain of an arbitrary complex inner product
space, and `ComparisonData.comparison` is the operator.  Proved here:
`comparison_isSymmetricDom` (symmetry), `comparison_inner_eq` (the quadratic
form is `∑‖πᵢv‖² + ∑‖Vᵢv‖² + ‖v‖²` — no cross terms, because the squares are
squares of symmetric operators), `comparison_ge_norm_sq` (`n ≥ I`, the
positivity Faris–Lavine asks of the comparison operator) and two criteria for
essential self-adjointness: `comparison_hasZeroDeficiencyOn_of_eigenvectors`
from a total family of eigenvectors, and `diagComparison_hasZeroDeficiencyOn`,
an unconditional instance in the representation in which the `πᵢ` and `Vᵢ` are
simultaneously diagonal (the fiber momentum representation), where the operator
is also genuinely unbounded (`diagComparison_not_bounded`).

**2. How the two Faris–Lavine bounds behave when summed over particles.**  On an
`m`-particle sector the second-quantized operators are `Ĥ = ∑ₖ hₖ` and
`N̂ = ∑ₖ nₖ + I`.

* `norm_sum_le_of_pairwise` — the *operator* bound lifts with the **same**
  constant provided the domination holds *pairwise*,
  `|Re⟪hₖv, hₗv⟫| ≤ c² Re⟪nₖv, nₗv⟫` for all pairs `k, l`.
* `not_forall_norm_sum_le_of_pointwise` — and pairwise is genuinely needed: the
  naive argument "triangle inequality plus the one-particle bound" is **not**
  valid.  There are two pairs `(hₖ, nₖ)` with `‖hₖ x‖ ≤ ‖nₖ x‖` for every `x`
  and yet `‖(h₀ + h₁)x‖ > ‖(n₀ + n₁)x‖`; the step
  `∑ₖ ‖nₖ Ψ‖ ≤ ‖N̂ Ψ‖` in the informal argument is false as stated.
* `abs_re_inner_commutator_sum_le` — the *form commutator* bound, by contrast,
  lifts exactly as the informal argument says, because quadratic forms are
  additive: with `[hₖ, nₗ] = 0` for `k ≠ l` (different particles) one has
  `[Ĥ, N̂] = ∑ₖ [hₖ, nₖ]`(`commDom_sum`, `commDom_add_id`) and therefore
  `|Re⟪Ψ, [Ĥ, N̂]Ψ⟫| ≤ c₂ Re⟪Ψ, N̂Ψ⟫`.

## Scope

Nothing here claims essential self-adjointness of the continuum Navier–Stokes
generator.  The Faris–Lavine criterion itself is not proved anywhere in this
project; it enters as a named hypothesis (`ns_esa_of_farisLavine_dense`).  What
is established here is exactly which bounds survive second quantization, and in
what form.
-/
