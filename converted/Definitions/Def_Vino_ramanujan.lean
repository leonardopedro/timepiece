/-
prove2.me platform library module `Definitions.Def_Vino_ramanujan`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Vino_ramanujan.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Vino

/-- Ramanujan's sum `c_q(n) = ∑_{a < q, (a,q) = 1} e(an/q)`. -/
noncomputable def ramanujan (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    CircleMethod.e ((a : ℝ) * (n : ℝ) / (q : ℝ))

/-- The local factor at a prime `p` of the singular series of the three primes
problem: `1 - (p-1)^{-2}` if `p ∣ n`, and `1 + (p-1)^{-3}` otherwise. -/
noncomputable def threePrimeFactor (p : ℕ) (n : ℤ) : ℝ :=
  if (p : ℤ) ∣ n then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- The `q`-th term of the singular series of the three primes problem,
`μ(q) c_q(n) / φ(q)^3`. -/
noncomputable def singTerm (q : ℕ) (n : ℤ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) * ramanujan q n / ((Nat.totient q : ℂ)) ^ 3

/-- The singular series of the three primes problem truncated to the divisors of
a modulus `Q`: `𝔖_Q(n) = ∑_{q ∣ Q} μ(q) c_q(n) / φ(q)^3`. -/
noncomputable def singSeriesDvd (Q : ℕ) (n : ℤ) : ℂ :=
  ∑ q ∈ Q.divisors, singTerm q n

/-- The singular series of the three primes problem truncated at `Q`:
`𝔖_{<Q}(n) = ∑_{1 ≤ q < Q} μ(q) c_q(n) / φ(q)^3`. -/
noncomputable def singSeriesTrunc (Q : ℕ) (n : ℤ) : ℂ :=
  ∑ q ∈ Finset.Ico 1 Q, singTerm q n

end Vino
