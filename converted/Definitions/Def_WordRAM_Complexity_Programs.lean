/-
prove2.me platform library module `Definitions.Def_WordRAM_Complexity_Programs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_WordRAM_Complexity_Programs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_WordRAMEquivalence_Foundation1

set_option autoImplicit false

namespace WordRAM.Complexity

variable {m : Model}

inductive Operand where
  | immediate (value : Nat)
  | memory (address : WordRAM.Address)
  deriving DecidableEq, Repr

def Operand.lower (w : Width) : Operand → WordRAM.Operand w
  | .immediate value => .immediate (BitVec.ofNat w.bits value)
  | .memory address => .memory address

inductive Instruction (m : Model) where
  | copy (dst : WordRAM.Address) (src : Operand)
  | binary (op : WordRAM.BinOp m) (dst : WordRAM.Address) (x y : Operand)
  | bitNot (dst : WordRAM.Address) (src : Operand)
  | jump (target : Nat)
  | branch (cmp : WordRAM.Comparison) (x y : Operand) (target : Nat)
  | halt
  deriving DecidableEq, Repr

def Instruction.lower (w : Width) : Instruction m → WordRAM.Instruction w m 0
  | .copy dst src => .copy dst (src.lower w)
  | .binary op dst x y => .binary op dst (x.lower w) (y.lower w)
  | .bitNot dst src => .bitNot dst (src.lower w)
  | .jump target => .jump target
  | .branch cmp x y target => .branch cmp (x.lower w) (y.lower w) target
  | .halt => .halt

abbrev Program (m : Model) := List (Instruction m)

def Program.lower (w : Width) (code : Program m) : WordRAM.Program w m 0 :=
  code.map (Instruction.lower w)

structure Algorithm (m : Model) where
  code : Program m
  capacityCoefficient : Nat := 1
  capacityDegree : Nat := 1

def Algorithm.capacity (A : Algorithm m) (n : Nat) : Nat :=
  A.capacityCoefficient * (n + 1) ^ A.capacityDegree + n + 16

def Algorithm.width (A : Algorithm m) (n : Nat) : Width where
  bits := Nat.log2 (A.capacity n) + 1
  positive := by omega

end WordRAM.Complexity
