/-
prove2.me platform library module `Definitions.Def_WordRAM_Complexity_BitIO`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_WordRAM_Complexity_BitIO.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_WordRAM_Complexity_Programs
import Definitions.Def_CookLevin_Cost

set_option autoImplicit false

namespace WordRAM.Complexity

variable {m : Model} {w : Width}

def inputBase : Nat := 8

def initialMemory (w : Width) (x y : List Bool) : Memory w := fun a =>
  BitVec.ofNat w.bits <|
    if a = 0 then x.length
    else if a = 1 then y.length
    else if a = 2 then inputBase
    else if a < inputBase then 0
    else if a - inputBase < x.length then (x[a - inputBase]!).toNat
    else if a - inputBase - x.length < y.length then
      (y[a - inputBase - x.length]!).toNat
    else 0

def initialState (w : Width) (x y : List Bool) : State w :=
  { mem := initialMemory w x y }

def runState (A : Algorithm m) (fuel : Nat) (x y : List Bool) :
    State (A.width (x.length + y.length)) :=
  WordRAM.run (fun _ i => Fin.elim0 i)
    (A.code.lower (A.width (x.length + y.length))) fuel
    (initialState (A.width (x.length + y.length)) x y)

def wordBit? (v : Word w) : Option Bool :=
  if v.toNat = 0 then some false
  else if v.toNat = 1 then some true
  else none

def output? (s : State w) : Option (List Bool) :=
  let base := (s.mem 2).toNat
  let size := (s.mem 3).toNat
  if base + size ≤ 2 ^ w.bits then
    (List.range size).mapM fun i => wordBit? (s.mem (base + i))
  else none

def RAMComputesInTime (A : Algorithm m) (R : Nat → Nat)
    (f : List Bool → List Bool) : Prop :=
  ∀ x, let s := runState A (R x.length) x []
    s.halted = true ∧ output? s = some (f x)

def RAMDecidesInTime (A : Algorithm m) (R : Nat → Nat)
    (V : List Bool → List Bool → Bool) : Prop :=
  ∀ x y, let s := runState A (R (x.length + y.length)) x y
    s.halted = true ∧ (s.mem 4).toNat = (V x y).toNat

def RAMPolyTimeComputable (A : Algorithm m) (f : List Bool → List Bool) : Prop :=
  ∃ c d, RAMComputesInTime A (CookLevin.polyBound c d) f

def RAMPolyTimeDecidable (A : Algorithm m)
    (V : List Bool → List Bool → Bool) : Prop :=
  ∃ c d, RAMDecidesInTime A (CookLevin.polyBound c d) V

end WordRAM.Complexity
