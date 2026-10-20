/-
prove2.me platform library module `Definitions.Def_Vino_primes`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Vino_primes.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Vino

/-- The von Mangoldt exponential sum `S(α, N) = ∑_{n < N} Λ(n) e(αn)`, the
prime-side generating function of the circle method. -/
noncomputable def vmSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * CircleMethod.e (α * (n : ℝ))

/-- The unweighted prime exponential sum `∑_{p < N, p prime} e(αp)`. -/
noncomputable def primeSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.range N).filter Nat.Prime, CircleMethod.e (α * (p : ℝ))

/-- Chebyshev's function `ψ(N) = ∑_{n < N} Λ(n)`. -/
noncomputable def psi (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ)

end Vino
