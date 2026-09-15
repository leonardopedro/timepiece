import BookProof.ChapterHashimotoComplexShifts.Part1
import BookProof.ChapterHashimotoComplexShifts.Part2

/-!
# The Hashimoto (SIRK) algorithm with **complex, non-real, and many different shifts**

`BookProof.ChapterHashimotoShiftInvert` develops the shift-invert trick for a
*single, real, positive* shift `γ`, where invertibility of `A + γ` comes from
positivity of `A`.  The Shift-invert Rational Krylov method of Hashimoto and
Nodera is however run with

* shifts `γ` that are **complex with non-zero imaginary part** — then
  `γ I − A` is invertible for *every* self-adjoint `A`, with no positivity
  assumption at all, purely because a non-real number is at distance
  `|Im γ| > 0` from the (real) numerical range; and
* **many different shifts** `γ₁, γ₂, …`, one per step, the rational Krylov
  subspace `Q_m({X_j}, v) = span{v, X₁v, X₂X₁v, …, X_{m-1}⋯X₁v}` being built
  out of the resolvents `X_j = (γ_j I − A)⁻¹`.

This module adapts the theory to that setting.  Everything is in the same
namespace `BookProof.HashimotoShiftInvert`.

## Part 1 — the non-real shift bound

`norm_cshiftMap_ge`: `‖(γ − A)x‖ ≥ |Im γ| ‖x‖` for a **symmetric** `A`, with no
positivity.  Hence `cshiftMap_injective`.

## Part 2 — bijectivity

`cshiftRange_isClosed`, `cshiftRange_orthogonal_eq_bot`, `cshiftMap_surjective`:
for a self-adjoint `A` (symmetry plus the adjoint criterion) and non-real `γ`,
`γ − A` is a bijection of `Dom` onto the whole space.

## Part 3 — the resolvent `X = (γ − A)⁻¹`

`IsShiftInvertC`, `exists_isShiftInvertC`, `IsShiftInvertC.opNorm_le`
(`‖X‖ ≤ 1/|Im γ|`), `IsShiftInvertC.adjoint_eq` (the adjoint of `X` is the
resolvent at the conjugate shift — `X` is no longer self-adjoint, it is normal),
`shiftInvertC_determines`, `isShiftInvertC_unique`, and
`isShiftInvertC_neg_of_isShiftInvert` relating the new theory to the real
positive-shift theory of the previous chapter.

## Part 4 — many shifts

`shiftInvertC_resolvent_identity` (`X_j − X_k = (γ_k − γ_j) X_j X_k`),
`shiftInvertC_commute`, `shiftInvertC_comp_one_sub` (the SIRK relation
`X_j (I − (γ_m − γ_j) X_m) = X_m`), the rational Krylov flag `rkVec`,
`rkSpan`, and `rkSpan_den_eq` — the cleared-denominator form of Hashimoto–Nodera
Eq. (11): `∏_{i<k} (I − (γ_m − γ_i)X_m)` maps the `k`-th rational Krylov vector
to `X_m^k v`, so the rational Krylov subspace built from many shifts is a space
of *rational* functions of the single resolvent `X_m`.  `rkCompression_tendsto`
gives strong convergence of the compressions along the flag.

## Part 5 — the headline

`hashimoto_multishift_selects_friedrichs`.

## Part 6 — a genuinely unbounded example with non-real shifts

The number operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, its resolvents at arbitrary
non-real shifts, and `hashimoto_multishift_unbounded_example`.
-/
