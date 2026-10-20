/-
prove2.me platform library module `Definitions.Def_Cryptography_ShamirSecretSharing`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Cryptography_ShamirSecretSharing.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Def bundle generated from Cryptography/ShamirSecretSharing.lean by skeleton subtraction
import Mathlib

/-!
# Shamir secret sharing

This file formalizes the algebraic and information-theoretic core of Shamir's
scheme over an arbitrary field.  A sharing polynomial has its secret as its
value at zero.  Privacy is expressed without choosing a probability API: after
fixing any values at `t - 1` nonzero locations, every possible secret has
exactly one degree-`< t` polynomial extension.  Consequently a uniformly
random sharing polynomial induces exactly the same observation distribution
for every secret.
-/

namespace ShamirSecretSharing

open Polynomial

variable {F : Type*} [Field F]

/-- The share carried by location `x` is polynomial evaluation at `x`. -/
def share (p : F[X]) (x : F) : F := p.eval x

/-- A polynomial is valid for threshold `t` and secret `secret` when its degree
is below `t` and its constant evaluation is the secret. -/
def ValidPolynomial (t : ℕ) (secret : F) (p : F[X]) : Prop :=
  p.degree < (t : WithBot ℕ) ∧ p.eval 0 = secret






end ShamirSecretSharing
