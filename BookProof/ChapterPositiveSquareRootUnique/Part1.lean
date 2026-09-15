import BookProof.Prelude
import BookProof.ChapterUnboundedPolar

/-!
# `|Ā| = (A* Ā)^{1/2}` is *the* non-negative square root — uniqueness

`BookProof.ChapterUnboundedPolar` constructs `absRel A = |Ā|`, proves it
self-adjoint and non-negative, and proves `|Ā|² = A* Ā` (`absRel_comp_self`).
What was missing — the reason `(A* Ā)^{1/2}` could only be called *a* square root
— is **uniqueness**: that no other non-negative self-adjoint relation squares to
`A* Ā`.  Classically this is read off the spectral theorem for unbounded
self-adjoint operators.  This module proves it with the **bounded** continuous
functional calculus only.

## The argument

Let `T` be a non-negative self-adjoint linear relation (`IsNonnegSelfAdjoint`).

* Part 1.  `1 + T` is injective with closed dense range, hence bijective, so it
  has an everywhere-defined inverse `invCLM T`, a positive contraction; and `T`
  is recovered from it, `T = {(C h, h − C h)}` (`rel_eq_of_invCLM_eq`).
* Part 2.  If moreover `T T ⊆ A* Ā`, then with `C = invCLM T` and
  `R = (1 + A* Ā)⁻¹` one has the **bounded** identity
  `R (1 − 2C + 2C²) = C²` (`resCLM_mul_den`): indeed for `x = C h` and
  `u = C x`, the pair `(u, h − 2x + u)` lies in `T T ⊆ A* Ā` and its coordinates
  add up to `h − 2x + 2u`.
* Part 3.  On the spectrum of `C`, which lies in `[0, 1]`, the identity says
  `R = g(C)` with `g t = t²/(2t² − 2t + 1)`, and `g` is inverted on `[0,1]` by the
  continuous `ψ r = √r/(√r + √(1−r))`.  Hence **`C = ψ(R)`** (`invCLM_eq_cfc`) —
  the inverse of `1 + T` is determined by `A` alone.
* Part 4.  Therefore any two such `T` agree; since `absRel A` is one of them,
  **`T = |Ā|`** (`eq_absRel_of_isNonnegSelfAdjoint`), and `|Ā|` is the unique
  non-negative self-adjoint square root of `A* Ā`
  (`absRel_unique_nonneg_sqrt`).

Only `A : D →ₗ[ℂ] F` on a complex Hilbert space is needed; neither density of `D`
nor symmetry of `A` enters the uniqueness statement.
-/

namespace BookProof.PositiveSquareRoot

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare BookProof.VonNeumannCore BookProof.UnboundedPolar
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end BookProof.PositiveSquareRoot
