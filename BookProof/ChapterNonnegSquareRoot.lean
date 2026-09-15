import BookProof.ChapterNonnegSquareRoot.Part1
import BookProof.ChapterNonnegSquareRoot.Part2

/-!
# The square root of an arbitrary non-negative self-adjoint linear relation

`BookProof.ChapterUnboundedPolar` constructs `|Ā| = (A* Ā)^{1/2}` and
`BookProof.ChapterPositiveSquareRootUnique` shows it is *the* non-negative
self-adjoint square root of `A* Ā`.  Both statements are about the particular
relation `factorRel A = A* Ā`.  This module removes that restriction:

> **Every non-negative self-adjoint linear relation `T` on a complex Hilbert
> space has a unique non-negative self-adjoint square root.**

The construction is the same bounded one, applied to the resolvent
`C = (1 + T)⁻¹ = invCLM hT`, which `ChapterPositiveSquareRootUnique` already
produces as an everywhere-defined positive contraction:

* `sqrtRel hT = {(C^{1/2} y, (1 − C)^{1/2} y) : y}` — formally
  `(1 − C)^{1/2} C^{−1/2} = ((C⁻¹ − 1))^{1/2} = T^{1/2}`;
* it is symmetric, `1 + T^{1/2}` is surjective, hence `T^{1/2}` is self-adjoint
  (`adjPairs_sqrtRel`), and it is non-negative
  (`isNonnegSelfAdjoint_sqrtRel`);
* **`(T^{1/2})² = T`** (`sqrtRel_comp_self`);
* **uniqueness** (`eq_sqrtRel_of_isNonnegSelfAdjoint`): if `S` is non-negative
  self-adjoint with `S S ⊆ T`, then `S = T^{1/2}`.  As in the special case, this
  is obtained from the *bounded* continuous functional calculus alone: with
  `C_S = (1 + S)⁻¹` one has the bounded identity
  `(1 + T)⁻¹ (1 − 2C_S + 2C_S²) = C_S²` (`invCLM_mul_den`), which on
  `spectrum C_S ⊆ [0,1]` says `(1 + T)⁻¹ = g(C_S)` for `g t = t²/(2t² − 2t + 1)`,
  and `g` is inverted there by `ψ r = √r/(√r + √(1−r))`, so
  `C_S = ψ((1 + T)⁻¹)` is determined by `T` alone.

`sqrtRel_unique_nonneg_sqrt` packages existence, the square, and uniqueness, and
`absRel_eq_sqrtRel` identifies the earlier `|Ā|` with `(A* Ā)^{1/2}` in this
sense.  Single-valuedness is inherited: if `T` is an operator, so is `T^{1/2}`
(`sqrtRel_snd_eq_zero_of_fst_eq_zero`).

Two further consequences are recorded.

* **The form of `T`.**  `D(T) ⊆ D(T^{1/2})` (`exists_mem_sqrtRel_of_mem`) and, for
  single-valued `T`, `⟪x, T x⟫ = ‖T^{1/2} x‖²` (`inner_eq_norm_sq_of_mem`,
  `norm_sq_eq_inner_of_mem`).
* **Commutation.**  A bounded operator commuting with `(1 + T)⁻¹` leaves both `T`
  and `T^{1/2}` invariant (`mem_of_commute`, `mem_sqrtRel_of_commute`).
* **The resolvent at every negative real.**  A positive real multiple `c T`
  (`smulRel`) of a non-negative self-adjoint relation is again one
  (`isNonnegSelfAdjoint_smulRel`, via `adjPairs_smulRel`), so the resolvent of
  `a⁻¹ T` gives, for every `a > 0`, an everywhere-defined bounded `(T + a)⁻¹`
  (`invCLMAt`) solving `a x + T x = h` uniquely (`invCLMAt_mem`,
  `invCLMAt_eq_of_mem`, `existsUnique_smul_add_mem`) with `‖(T + a)⁻¹‖ ≤ 1/a`
  (`norm_invCLMAt_le`): the spectrum of `T` misses the negative reals.
-/
