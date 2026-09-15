import BookProof.ChapterUnboundedPolar.Part1
import BookProof.ChapterUnboundedPolar.Part2

/-!
# The unbounded polar decomposition: `|Ā| = (A* Ā)^{1/2}` and `Ā = U |Ā|`

`BookProof.ChapterFriedrichsSquareFactorization` builds the composite `A* Ā` as a
linear relation `factorRel A` and proves it self-adjoint;
`BookProof.ChapterVonNeumannCore` adds the bounded inverse
`R = (1 + A* Ā)⁻¹ = resCLM A` and von Neumann's core theorem.  Both modules
recorded the same boundary: the *positive square root* `|Ā| = (A* Ā)^{1/2}` of
the unbounded operator `A* Ā`, and the polar decomposition `Ā = U |Ā|`, were not
proved, because they appear to need a functional calculus for unbounded
self-adjoint operators.

This module proves them, without any unbounded functional calculus.  The whole
construction is carried out with the **bounded** continuous functional calculus
applied to the single positive contraction `R = (1 + A* Ā)⁻¹`:

* `sqrtOp R = R^{1/2}` and `coSqrtOp R = (1 − R)^{1/2}`;
* `|Ā|` is the linear relation `absRel A = {(R^{1/2} y, (1 − R)^{1/2} y) : y}`.

Formally `|Ā| = (1 − R)^{1/2} R^{−1/2}`, which is `((R⁻¹ − 1))^{1/2} = (A* Ā)^{1/2}`,
and its domain is the range of `R^{1/2}`.

## What is proved

Part 0 — a general criterion, extracted from von Neumann's argument: a symmetric
linear relation `S` with `1 + S` surjective is self-adjoint
(`adjPairs_eq_self_of_symmetric_of_surjective`).

Part 1 — the bounded square roots of a positive contraction `R`: `sqrtOp`,
`coSqrtOp`, `midOp` with `R^{1/2} R^{1/2} = R`, `(1−R)^{1/2}(1−R)^{1/2} = 1 − R`,
the commutation `R^{1/2}(1−R)^{1/2} = (1−R)^{1/2}R^{1/2} = midOp R`, positivity,
and the invertibility of `R^{1/2} + (1 − R)^{1/2}` (its spectrum lies in `[1, √2]`).

Part 2 — `R = resCLM A` is a positive, injective contraction (`resCLM_nonneg`,
`resCLM_le_one`, `resCLM_injective`).

Part 3 — the absolute value `absRel A`: it is single-valued, symmetric, positive,
`1 + |Ā|` is surjective, hence **`|Ā|` is self-adjoint** (`adjPairs_absRel`), and
**`|Ā|² = A* Ā`** (`absRel_comp_self`).

Part 4 — the domain and the norm: `D(|Ā|) = D(Ā)` and `‖ |Ā| x ‖ = ‖Ā x‖`
(`absDom_eq_clDom`, `norm_absFun_eq`), proved from von Neumann's core theorem
applied on both sides.

Part 5 — **the polar decomposition** `Ā = U |Ā|`, with `U` a linear isometry of
`ran |Ā|` onto `ran Ā` (`exists_polar_isometry`).

Hypotheses: `F` is a complex Hilbert space, `A` is symmetric on a dense domain
`D`.  No invariance of the domain is used.
-/
