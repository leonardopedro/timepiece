/-
prove2.me platform library module `Definitions.Def_WordRAM_Complexity_Simulation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_WordRAM_Complexity_Simulation.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_WordRAM_Complexity_BitIO
import Definitions.Def_CookLevin_Complexity

set_option autoImplicit false

namespace WordRAM.Complexity

variable {m : Model}

structure FunctionSimulation (A : Algorithm m) (R : Nat → Nat) (c d : Nat) where
  machine : CookLevin.Machine
  tapes : Nat
  alphabet : Nat
  legal : CookLevin.TuringMachine tapes alphabet machine
  simulates : ∀ (x : List Bool) (out : List Bool),
    (runState A (R x.length) x []).halted = true →
    output? (runState A (R x.length) x []) = some out →
    let cfg := CookLevin.execute machine
      (CookLevin.startConfig2 tapes (CookLevin.boolsToSymbols x) [])
      (CookLevin.polyBound c d x.length)
    cfg.1 = machine.length ∧
      CookLevin.outputOf tapes cfg (CookLevin.polyBound c d x.length + 2) = out

structure VerifierSimulation (A : Algorithm m) (R : Nat → Nat) (c d : Nat) where
  machine : CookLevin.Machine
  tapes : Nat
  alphabet : Nat
  legal : CookLevin.TuringMachine tapes alphabet machine
  simulates : ∀ (x y : List Bool) (b : Bool),
    (runState A (R (x.length + y.length)) x y).halted = true →
    ((runState A (R (x.length + y.length)) x y).mem 4).toNat = b.toNat →
    CookLevin.DecidesIn machine tapes
      (CookLevin.boolsToSymbols x) (CookLevin.boolsToSymbols y)
      (CookLevin.polyBound c d (x.length + y.length)) b

structure PolynomialBackend where
  functions : ∀ {m} (A : Algorithm m) (a b : Nat),
    Σ c d, FunctionSimulation A (CookLevin.polyBound a b) c d
  verifiers : ∀ {m} (A : Algorithm m) (a b : Nat),
    Σ c d, VerifierSimulation A (CookLevin.polyBound a b) c d

end WordRAM.Complexity
