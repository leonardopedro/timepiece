/-
prove2.me platform library module `Theorems.Thm_Davenport_siegel_walfisz_char`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Davenport_siegel_walfisz_char.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_threeprimes
import Definitions.Def_Davenport_siegelWalfisz
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Totient

open Finset DirichletCharacter Vino

namespace Davenport

theorem siegel_walfisz_char : ThreePrimes.SiegelWalfisz := by sorry

end Davenport
