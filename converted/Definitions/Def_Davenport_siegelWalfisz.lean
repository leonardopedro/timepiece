/-
prove2.me platform library module `Definitions.Def_Davenport_siegelWalfisz`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Davenport_siegelWalfisz.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-
# Siegel–Walfisz: vocabulary (Davenport, *Multiplicative Number Theory*, 3rd ed., §§14, 18–22)

This file fixes the objects used to state the Siegel–Walfisz theorem and the results of
Davenport §§14, 18, 20, 21 that lead to it.  The character-twisted sum
`ψ(N, χ) = ∑_{n < N} Λ(n) χ(n)` is `Vino.vmSumChar q χ N` (platform definition
`Vino_dirichlet`), and `L(s, χ)` is Mathlib's `DirichletCharacter.LFunction`.

Convention: sums are over `n < N` with `N : ℕ` (as in `Vino.vmSumChar` and
`ThreePrimes.SiegelWalfisz`); Davenport sums over `n ≤ x`.  The two differ by the single
term `Λ(N) ≤ log N`, which is negligible against every error term below.
-/
import Definitions.Def_Vino_dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient

open Finset

namespace Davenport

/-- `ψ(N; q, a) = ∑_{n < N, n ≡ a (mod q)} Λ(n)`, the von Mangoldt sum over an arithmetic
progression (Davenport §20, first sentence, with `n ≤ x` replaced by `n < N`). -/
noncomputable def psiAP (N q a : ℕ) : ℝ :=
  ∑ n ∈ range N,
    if (n : ZMod q) = (a : ZMod q) then (ArithmeticFunction.vonMangoldt n : ℝ) else 0

/-- The boundary `1 - c / log (q (|t| + 2))` of the classical zero-free region for
`L(s, χ)`, `χ` a character modulo `q`, at height `t = Im s` (Davenport §14). -/
noncomputable def regionBoundary (c : ℝ) (q : ℕ) (s : ℂ) : ℝ :=
  1 - c / Real.log ((q : ℝ) * (|s.im| + 2))

/-- `s` lies in the closed region `Re s ≥ 1 - c / log (q (|Im s| + 2))`. -/
def InRegion (c : ℝ) (q : ℕ) (s : ℂ) : Prop := regionBoundary c q s ≤ s.re

/-- `E` is an *exceptional set* for `χ` (modulo `q`) with respect to the region constant `c`:
`E` has at most one element; every element of `E` is a real zero of `L(·, χ)` in `(0, 1)` lying
in the region, and such an element can exist only when `χ` is a real (quadratic) non-principal
character;
and `L(s, χ) ≠ 0` at every `s ≠ 1` of the region `Re s ≥ 1 - c / log (q (|Im s| + 2))`
outside `E`.  (Davenport §14: "at most one exceptional real zero".) -/
def IsExceptionalSet {q : ℕ} [NeZero q] (c : ℝ) (χ : DirichletCharacter ℂ q) (E : Set ℂ) :
    Prop :=
  E.Subsingleton ∧
    (∀ z ∈ E, z.im = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ InRegion c q z ∧
      DirichletCharacter.LFunction χ z = 0 ∧ χ.IsQuadratic ∧ χ ≠ 1) ∧
    ∀ s : ℂ, s ≠ 1 → InRegion c q s → s ∉ E → DirichletCharacter.LFunction χ s ≠ 0

end Davenport
