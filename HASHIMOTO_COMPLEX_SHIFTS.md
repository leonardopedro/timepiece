# Complex (non-real) shifts and many shifts in the shift-invert theory

Module: `BookProof/ChapterHashimotoComplexShifts.lean`
Namespace: `BookProof.HashimotoShiftInvert` (the same namespace as the
single-real-shift chapter `BookProof/ChapterHashimotoShiftInvert.lean`).

The earlier chapter developed the shift-invert trick for one **real positive**
shift `c`, where invertibility of `A + c` came from positivity of `A`.  The
Shift-invert Rational Krylov (SIRK) method of Hashimoto–Nodera is run instead
with resolvents `X_j = (γ_j I − A)⁻¹` at shifts `γ_j` that

* are **complex with non-zero imaginary part**, which is what guarantees
  invertibility of `γ I − A` — for *every* self-adjoint `A`, with no positivity
  assumption; and
* **change from step to step**, the rational Krylov subspace
  `Q_m({X_j}, v) = span{v, X₁v, X₂X₁v, …, X_{m-1}⋯X₁v}` being built from the
  whole family.

This file records where each claim lives in Lean.  Everything is `sorry`-free
and every headline result is certified in `BookProof/ChapterRoadmapAudit.lean`
to depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Non-real shift ⇒ invertibility, with no positivity

| Claim | Lean name |
| --- | --- |
| `γ I − A` on the domain of `A` | `cshiftMap` |
| `‖(γ − A)x‖ ≥ \|Im γ\| ‖x‖` for symmetric `A` | `norm_cshiftMap_ge` |
| `γ − A` injective | `cshiftMap_injective` |
| range of `γ − A` closed | `cshiftRange_isClosed` |
| range of `γ − A` dense (orthogonal complement trivial) | `cshiftRange_orthogonal_eq_bot` |
| `γ − A` surjective, hence bijective | `cshiftMap_surjective` |

Only symmetry and the self-adjointness (adjoint) criterion are used; positivity
of `A` appears nowhere in this part.

## The resolvent `X = (γ I − A)⁻¹`

| Claim | Lean name |
| --- | --- |
| definition of "`X` is the resolvent of `A` at `γ`" | `IsShiftInvertC` |
| existence of `X` as a bounded everywhere-defined operator | `exists_isShiftInvertC` |
| `‖X‖ ≤ 1/\|Im γ\|` | `IsShiftInvertC.opNorm_le` (pointwise: `IsShiftInvertC.norm_apply_le`) |
| `A = γ − X⁻¹` on the range of `X` | `IsShiftInvertC.apply_eq` |
| range of `X` = domain of `A` | `IsShiftInvertC.dom_eq_range` |
| `X` injective | `IsShiftInvertC.injective` |
| `X* = (γ̄ − A)⁻¹` (for a non-real shift `X` is **not** self-adjoint) | `IsShiftInvertC.inner_adjoint` |
| `X` determines `A` (domain and values) | `shiftInvertC_determines` |
| uniqueness of `X` at a given shift | `isShiftInvertC_unique` |
| a right inverse of `γ − A` is automatically two-sided | `isShiftInvertC_of_rightInverse` |
| the real positive-shift notion is the case `γ = −c` | `isShiftInvertC_neg_of_isShiftInvert` |

## Many shifts: the rational Krylov structure

| Claim (paper) | Lean name |
| --- | --- |
| first resolvent identity `X_j − X_k = (γ_k − γ_j) X_j X_k` | `shiftInvertC_resolvent_identity` |
| resolvents at different shifts commute | `shiftInvertC_commute` |
| `X_j = (I − (γ_m − γ_j) X_m)⁻¹ X_m`, in the cleared form `X_j (I − (γ_m − γ_j) X_m) = X_m` (Sect. 4) | `shiftInvertC_comp_one_sub` |
| the rational Krylov vectors `v, X₁v, X₂X₁v, …` and their span `Q_m` (Eq. (8)) | `rkVec`, `rkSpan`, `rkSpan_mono` |
| the SIRK denominator `∏_{i<k}(I − (γ_m − γ_i) X_m)` | `sirkDen` |
| Eq. (11): the multi-shift space is a space of *rational* functions of the single resolvent `X_m`, in cleared-denominator form `∏_{i<k}(I − (γ_m − γ_i)X_m) · X_{k-1}⋯X_0 v = X_m^k v` | `sirkDen_rkVec` |
| the projections onto a dense rational Krylov flag converge strongly to `I` | `rkProj_tendsto` |
| the multi-shift compressions `P_m T P_m` converge strongly to `T` | `rkCompression`, `rkCompression_tendsto` |

## Headline

`hashimoto_multishift_selects_friedrichs`: for a symmetric Hamiltonian matrix in
a complete orthonormal basis, any positive self-adjoint extension `A` of it (no
boundedness hypothesis anywhere), and any sequence `γ : ℕ → ℂ` of shifts with
non-zero imaginary parts, there is a family of resolvents `X_j = (γ_j I − A)⁻¹`
that are bounded by `1/|Im γ_j|`, all have range equal to the domain of `A`,
satisfy the resolvent identity, commute, satisfy the SIRK relation and the
rational-function identity above, have strongly convergent Galerkin
truncations, and each of which determines `A` uniquely.

## A genuinely unbounded example with non-real shifts

For the number operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)` (built in the previous
chapter, and unbounded by `ell2ExampleMatrix_unbounded`):

| Claim | Lean name |
| --- | --- |
| complex diagonal operators on `ℓ²(ℕ, ℂ)`, bounded by `M` | `memlp_diagFunC`, `diagLinC`, `diagCLMC` |
| the coefficients `1/(γ − n)` and `(n+1)/(γ − n)` and their bounds | `resCoeff`, `preCoeff`, `resCoeff_norm_le`, `preCoeff_norm_le` |
| the resolvent at a non-real shift is the diagonal `eₙ ↦ eₙ/(γ − n)` | `ell2Resolvent`, `ell2Resolvent_isShiftInvertC` |
| all the conclusions of the headline, for an arbitrary sequence of non-real shifts, on this unbounded operator | `hashimoto_multishift_unbounded_example` |

## Scope

The resolvent bound, invertibility, the multi-shift algebra and the strong
convergence statements are proved in full generality.  Nothing here formalizes
the `φ`-functions, the Crouzeix constant, or the *rates* of Theorems 3.2, 3.3
and 4.1 of the paper: those are approximation-theoretic estimates on rational
approximation, not statements about the operators, and they are outside the
scope of this module.
