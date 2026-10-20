/-
prove2.me platform library module `Definitions.Def_RamanujanPetersson_tau`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_RamanujanPetersson_tau.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Prove2me.Shim.Discriminant  -- `ModularForm.discriminant` is absent from the pinned Mathlib

open UpperHalfPlane ModularFormClass  -- `qExpansion` is `ModularFormClass.qExpansion` in the pinned Mathlib

namespace RamanujanPetersson

/-- Ramanujan's tau function: `tau n` is the `n`-th Fourier coefficient, in the variable
`q = exp(2πiz)`, of the discriminant modular form `Δ(z) = η(z)^24`. -/
noncomputable def tau (n : ℕ) : ℂ :=
  (qExpansion 1 ModularForm.discriminant).coeff n

end RamanujanPetersson
