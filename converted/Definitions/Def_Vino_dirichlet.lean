/-
prove2.me platform library module `Definitions.Def_Vino_dirichlet`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Vino_dirichlet.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace Vino

/-- The Gauss sum `τ(χ) = ∑_{m < q} χ(m) e(m/q)` attached to a Dirichlet
character `χ` modulo `q`. -/
noncomputable def gaussE (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ Finset.range q, χ (m : ZMod q) * CircleMethod.e ((m : ℝ) / (q : ℝ))

/-- The von Mangoldt sum twisted by a Dirichlet character,
`ψ(N, χ) = ∑_{n < N} Λ(n) χ(n)`. -/
noncomputable def vmSumChar (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)

end Vino
