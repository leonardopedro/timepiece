/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 3f5997ab-7dd8-473e-a3e7-60400260fb16
* original name       : `AlmostLossless.collisionProb_le`
* title               : Probability form of the collision bound: a uniformly random seed is bad with
* statement author    : raver1975
* solution author     : raver1975 (submission cb321fb5-f9f6-4596-8418-531db09bed17,
                        accepted 2026-09-12T15:10:36.08835+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Hashing.lean#L100
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/logos-confluence/AlmostLossless.collisionProb_le.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/AlmostLossless_collisionProb_le.diff`.
-/
-- Sol generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_card_collides_mul_card_le

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










/-! ## Expected number of false candidates (decoder work) -/




/-! ## Products of hash families -/


/-! ## A concrete 2-universal family: inner products over `ZMod p` -/


variable {p k : ℕ} [Fact p.Prime]









open AlmostLossless in
theorem _root_.Prove2me.Solution.AlmostLossless_collisionProb_le[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [DecidableEq M]
    [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) :
    (#{a | CollidesOn h T a} : ℚ) / (Fintype.card A : ℚ)
      ≤ (T.offDiag.card : ℚ) / (Fintype.card M : ℚ) := by
  have hA : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast Fintype.card_pos (α := A)
  rcases Nat.eq_zero_or_pos (Fintype.card M) with hM | hM
  · exfalso
    have : Fintype.card M ≠ 0 := Fintype.card_ne_zero (α := M)
    exact this hM
  have hMQ : (0 : ℚ) < (Fintype.card M : ℚ) := by exact_mod_cast hM
  rw [div_le_div_iff₀ hA hMQ]
  have := card_collides_mul_card_le hu T
  calc (#{a | CollidesOn h T a} : ℚ) * (Fintype.card M : ℚ)
      = ((#{a | CollidesOn h T a} * Fintype.card M : ℕ) : ℚ) := by push_cast; ring
    _ ≤ ((T.offDiag.card * Fintype.card A : ℕ) : ℚ) := by exact_mod_cast this
    _ = (T.offDiag.card : ℚ) * (Fintype.card A : ℚ) := by push_cast; ring

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open AlmostLossless
open Finset
variable {S A M : Type*}

theorem AlmostLossless.collisionProb_le[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [DecidableEq M]
    [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) :
    (#{a | CollidesOn h T a} : ℚ) / (Fintype.card A : ℚ)
      ≤ (T.offDiag.card : ℚ) / (Fintype.card M : ℚ) := by
  first
  | exact _root_.Prove2me.Solution.AlmostLossless_collisionProb_le hu T
  | (apply _root_.Prove2me.Solution.AlmostLossless_collisionProb_le <;> assumption)


end Prove2meStatement
