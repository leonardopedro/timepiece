/-
prove2.me platform library module `Theorems.Thm_AlmostLossless_card_collides_mul_card_le`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_AlmostLossless_card_collides_mul_card_le.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Thm stub generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing

/-!
# Two-universal hash families: the derandomised random codebook

Shannon's random-coding argument draws a codebook uniformly at random.  For
*almost-lossless source coding* the only property of the random codebook that
is ever used is that two fixed distinct source words collide with probability
`≤ 1/|M|`.  That is exactly **2-universality**, and it can be achieved by a
family whose seed is `k` field elements and whose evaluation costs `k`
multiplications — an honest "random number generator" with an explicit
complexity figure, as opposed to an exponentially large random codebook.

## Contents

* `AlmostLossless.TwoUniversal` : the defining counting inequality.
* `AlmostLossless.card_collides_mul_card_le` : union bound over the `|T|(|T|-1)`
  ordered pairs of a typical set `T`, giving
  `#{bad seeds} · |M| ≤ |T.offDiag| · |A|`.
* `AlmostLossless.collisionProb_le` : probability form, `P(bad seed) ≤
  |T.offDiag| / |M|`; the Monte-Carlo failure bound of the scheme.
* `AlmostLossless.exists_perfect_seed` : **derandomisation by the probabilistic
  method** — if `|M| > |T|(|T|-1)` then some seed is injective on the whole
  typical set, so the randomness can be removed entirely.
* `AlmostLossless.twoUniversal_dotHash` : a concrete instance, the inner-product
  family `h_a(x) = ∑ a i * x i` over `ZMod p`, proved 2-universal from the
  fact that a nonzero linear functional on `(ZMod p)^k` has all fibres of the
  same size.
-/

open AlmostLossless

open Finset

variable {S A M : Type*}

/-! ## Two-universality -/

theorem AlmostLossless.card_collides_mul_card_le[Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
    [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) :
    #{a | CollidesOn h T a} * Fintype.card M ≤ T.offDiag.card * Fintype.card A := by sorry
