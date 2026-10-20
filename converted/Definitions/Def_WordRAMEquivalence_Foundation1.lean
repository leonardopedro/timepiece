/-
prove2.me platform library module `Definitions.Def_WordRAMEquivalence_Foundation1`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_WordRAMEquivalence_Foundation1.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.Data.Nat.Basic
import Definitions.Def_CookLevin_Basic

set_option autoImplicit false

/-!
WordRAM model from Hagerup with some choices...
-/
namespace WordRAM

/--
"As mentioned above, a parameter of the word RAM is its word length w, a
positive integer." -/
structure Width where
  bits : Nat
  positive : 0 < bits
  deriving DecidableEq

/--
"The content of every memory cell is an integer x in the range
{0, …, 2^w − 1}, often called a word and identified with the bit string
x_{w−1} ⋯ x_0, where x = ∑_{i=0}^{w−1} x_i · 2^i." -/
abbrev Word (w : Width) := BitVec w.bits

variable {w : Width}

/--
"Just as a usual RAM, a word RAM is assumed to have an infinite memory
consisting of cells with addresses 0, 1, 2, …, not assumed to be initialized in
any particular way." -/
abbrev Memory (w : Width) := Nat → Word w

/-- Formalization choice: a store replaces exactly one cell. -/
def Memory.write (mem : Memory w) (a : Nat) (v : Word w) : Memory w :=
  fun b => if b = a then v else mem b

/--
"At the very least, we will assume the availability of a restricted instruction
set consisting of addition, subtraction, left and right shifts, and the bitwise
Boolean operations AND, OR, and NOT, and speak of the restricted model."
"Augmenting it with just the multiplication instruction, we arrive at the
multiplication instruction set and the multiplication model."

Scope: these are the two deterministic instruction sets implemented here. -/
inductive Model where
  | restricted
  | multiplication
  deriving DecidableEq, Repr

variable {m : Model} {k : Nat}

/-- A multiplication instruction cannot be constructed in the restricted model. -/
inductive BinOp (m : Model) where
  | add | sub | shl | shr | band | bor
  | mul (enabled : m = .multiplication)
  deriving DecidableEq, Repr

/--
"The arithmetic instructions take two operand words x and y and compute a
result word z equal to (x ⊕ y) mod 2^w, where ⊕ ∈ {+, −, ·} in the case of
addition, subtraction, and multiplication, x ⊕ y = x · 2^y in the case of left
shift, and x ⊕ y = ⌊x · 2^(−y)⌋ in the case of right shift; the latter operations
can also (and more naturally) be viewed as (noncyclic) shifts of x by y bit
positions with zero filling."
"The binary Boolean operations AND and OR take two operand words x_{w−1} ⋯ x_0
and y_{w−1} ⋯ y_0 and compute z_{w−1} ⋯ z_0, where z_i = x_i ⋈ y_i, for
i = 0, …, w − 1, and ⋈ ∈ {∧, ∨}."

The paper's ⊕ is a placeholder for the chosen arithmetic operation, not XOR.
`add_spec` through `or_bit` prove the corresponding equations. -/
def BinOp.eval : BinOp m → Word w → Word w → Word w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .mul _, x, y => x * y

/--
"The instruction set is assumed to contain the usual range of load and store
instructions and conditional and unconditional jumps, and the possible forms of
operands are assumed to allow for immediate operands (i.e., literal constants)
as well as direct and indirect addressing."

Formalization choice: direct addresses are natural numbers and indirect addressing
reads a pointer word from the specified cell. -/
inductive Address where
  | direct (cell : Nat)
  | indirect (pointerCell : Nat)
  deriving DecidableEq, Repr

def Address.resolve (mem : Memory w) : Address → Nat
  | .direct a => a
  | .indirect a => (mem a).toNat

inductive Operand (w : Width) where
  | immediate (value : Word w)
  | memory (address : Address)
  deriving DecidableEq, Repr

def Operand.read (mem : Memory w) : Operand w → Word w
  | .immediate v => v
  | .memory a => mem (a.resolve mem)

inductive Comparison where
  | eq | lt | le
  deriving DecidableEq, Repr

/-- All comparisons are unsigned. -/
def Comparison.test (c : Comparison) (x y : Word w) : Bool :=
  match c with
  | .eq => x == y
  | .lt => x.toNat < y.toNat
  | .le => x.toNat ≤ y.toNat

/-- The load/store/jump/operand quotation above governs this instruction type.
"The operation NOT, finally, takes a single word operand x_{w−1} ⋯ x_0 and
produces the word z_{w−1} ⋯ z_0 with z_i = 1 − x_i, for i = 0, …, w − 1." -/
inductive Instruction (w : Width) (m : Model) (k : Nat) where
  | copy (dst : Address) (src : Operand w)
  | binary (op : BinOp m) (dst : Address) (x y : Operand w)
  | bitNot (dst : Address) (src : Operand w)
  | native (dst : Address) (index : Fin k)
  | jump (target : Nat)
  | branch (cmp : Comparison) (x y : Operand w) (target : Nat)
  | halt
  deriving DecidableEq, Repr

/--
"We adopt usual conventions for presenting input to the machine and obtaining
output from it and assume that the machine operates on its memory according to
a program that is a finite list of possibly labeled instructions with operands."

Formalization choice: input and output are supplied/read through memory aka there
is no formal input/output layout or separate input/output instruction. -/
abbrev Program (w : Width) (m : Model) (k : Nat) := List (Instruction w m k)

/--
"As a concession to reality, where the computation of such universal constants
is hardly the biggest challenge, we therefore allow a fixed number of constants
to be available free of charge; one can imagine, e.g., that each is loaded into
a register by its own new instruction."

Formalization choice: a fixed finite family depending only on width, held fixed
across inputs. Loading one constant costs one instruction -/
abbrev NativeConstants (k : Nat) := (w : Width) → Fin k → Word w

structure State (w : Width) where
  mem : Memory w
  pc : Nat := 0
  halted : Bool := false
  ticks : Nat := 0

/--
"The execution of every instruction is assumed to take constant time."

Formalization choice: normalize said constant cost to one tick. -/
def execute (constants : NativeConstants k) (i : Instruction w m k)
    (s : State w) : State w :=
  let next := { s with pc := s.pc + 1, ticks := s.ticks + 1 }
  match i with
  | .copy dst src =>
      { next with mem := s.mem.write (dst.resolve s.mem) (src.read s.mem) }
  | .binary op dst x y =>
      { next with mem := (s.mem.write (dst.resolve s.mem)
          (op.eval (x.read s.mem) (y.read s.mem))) }
  | .bitNot dst src =>
      { next with mem := s.mem.write (dst.resolve s.mem) (~~~(src.read s.mem)) }
  | .native dst index =>
      { next with mem := s.mem.write (dst.resolve s.mem) (constants w index) }
  | .jump target => { next with pc := target }
  | .branch cmp x y target =>
      { next with pc := if cmp.test (x.read s.mem) (y.read s.mem)
                        then target else s.pc + 1 }
  | .halt => { next with halted := true }

/-- `none` means explicit halt or invalid instruction fetch (distinguished by
`s.halted`). An invalid fetch is stuck, not a successful halt, and costs no step. -/
def step (constants : NativeConstants k) (p : Program w m k)
    (s : State w) : Option (State w) :=
  if s.halted then none
  else (p[s.pc]?).map (fun i => execute constants i s)

/-- Fuel is an interpreter bound, not a bound built into the abstract machine. -/
def run (constants : NativeConstants k) (p : Program w m k) : Nat → State w → State w
  | 0, s => s
  | fuel + 1, s => match step constants p s with
    | none => s
    | some t => run constants p fuel t

end WordRAM

/-! Small program-composition facts for proofs about actual wordRAM instructions. -/
namespace WordRAM

variable {w : Width} {m : Model} {k : Nat}

/-- Place a compiled instruction at a later program location, relocating jump
targets along with it. Memory addresses and operands are not changed. -/
def Instruction.relocate (offset : Nat) : Instruction w m k → Instruction w m k
  | .copy dst src => .copy dst src
  | .binary op dst x y => .binary op dst x y
  | .bitNot dst src => .bitNot dst src
  | .native dst index => .native dst index
  | .jump target => .jump (offset + target)
  | .branch cmp x y target => .branch cmp x y (offset + target)
  | .halt => .halt

end WordRAM

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def sequenceCode (p q : Program w m k) : Program w m k :=
  p ++ q.map (Instruction.relocate p.length)

end WordRAM.Uniform

/-!
A genuine instruction compiler for one TM action, independent of tape bounds,
configuration enumeration and computation time. Tape cells are interleaved with
positive stride. A register holds the absolute address of the tape head.
Overflow goes to an internal infinite loop rather than wrapping the head.
-/
namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

abbrev noConstants : NativeConstants 0 := fun _ i => Fin.elim0 i

def tapeAddress (base stride pos : Nat) : Nat := base + stride * pos

/-- Four slots per action. Local PC 4 is the continuation. In the right-move
case local PC 2 traps overflow permanently. -/
def actionCode (w : Width) (headReg base stride : Nat) (a : CookLevin.Action) :
    Program w .restricted 0 :=
  .copy (.indirect headReg) (.immediate (BitVec.ofNat w.bits a.1)) ::
    match a.2 with
    | .Stay => [.jump 4, .jump 4, .jump 4]
    | .Left =>
        [.branch .eq (.memory (.direct headReg)) (.immediate (BitVec.ofNat w.bits base)) 4,
         .binary .sub (.direct headReg) (.memory (.direct headReg))
           (.immediate (BitVec.ofNat w.bits stride)),
         .jump 4]
    | .Right =>
        [.branch .lt (.memory (.direct headReg))
           (.immediate (BitVec.ofNat w.bits (2 ^ w.bits - stride))) 3,
         .jump 2,
         .binary .add (.direct headReg) (.memory (.direct headReg))
           (.immediate (BitVec.ofNat w.bits stride))]

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def branchCode (reg : Nat) (value : Word w) (p q : Program w .restricted 0) :
    Program w .restricted 0 :=
  [.branch .eq (.memory (.direct reg)) (.immediate value) 2,
   .jump (3 + p.length)] ++
  (p.map (Instruction.relocate 2) ++
    [.jump (3 + p.length + q.length)] ++ q.map (Instruction.relocate (3 + p.length)))

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

inductive DecisionTree (w : Width) where
  | leaf (code : Program w .restricted 0)
  | test (reg : Nat) (value : Word w) (yes no : DecisionTree w)

def DecisionTree.compile : DecisionTree w → Program w .restricted 0
  | .leaf code => code
  | .test reg value yes no => branchCode reg value yes.compile no.compile

/-- Selection enumerates only a finite alphabet, not machine configurations. -/
def selectValues (reg : Nat) (values : List Nat) (next : Nat → DecisionTree w) : DecisionTree w :=
  match values with
  | [] => .leaf []
  | v :: rest => .test reg (BitVec.ofNat w.bits v) (next v) (selectValues reg rest next)

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def headRegister (j : Nat) := 1 + j
def symbolRegister (K j : Nat) := 1 + K + j
def tapeBase (K j : Nat) := 1 + 2 * K + j

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

abbrev TapeBank := Nat → CookLevin.Tape

def actionsCode (w : Width) (K : Nat) : Nat → List CookLevin.Action → Program w .restricted 0
  | _, [] => []
  | j, a :: rest => sequenceCode (actionCode w (headRegister j) (tapeBase K j) K a)
      (actionsCode w K (j + 1) rest)

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def loadCode (w : Width) (K : Nat) : Nat → Nat → Program w .restricted 0
  | _, 0 => []
  | j, n + 1 => sequenceCode
      [.copy (.direct (symbolRegister K j)) (.memory (.indirect (headRegister j)))]
      (loadCode w K (j + 1) n)

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def symbolsTree (K G : Nat) (leaf : List Nat → DecisionTree w) :
    Nat → Nat → List Nat → DecisionTree w
  | _, 0, pre => leaf pre
  | j, n + 1, pre => selectValues (symbolRegister K j) (List.range G)
      (fun x => symbolsTree K G leaf (j + 1) n (pre ++ [x]))

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def transitionCode (w : Width) (K : Nat) (transition : Nat × List CookLevin.Action) :
    Program w .restricted 0 := sequenceCode (actionsCode w K 0 transition.2)
      [.copy (.direct 0) (.immediate (BitVec.ofNat w.bits transition.1))]

def transitionTree (w : Width) (M : CookLevin.Machine) (K G : Nat) : DecisionTree w :=
  selectValues 0 (List.range M.length) (fun q =>
    symbolsTree K G (fun gs => .leaf (transitionCode w K (M[q]! gs))) 0 K [])

def tmStepCode (w : Width) (M : CookLevin.Machine) (K G : Nat) : Program w .restricted 0 :=
  sequenceCode (loadCode w K 0 K) (transitionTree w M K G).compile

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

/-- Test for the mission halting state, otherwise execute one compiled transition
and return to the test. The only halt instruction is guarded by this test. -/
def tmProgram (w : Width) (M : CookLevin.Machine) (K G : Nat) : Program w .restricted 0 :=
  [.branch .eq (.memory (.direct 0)) (.immediate (BitVec.ofNat w.bits M.length)) 2,
    .jump 3, .halt] ++
  ((tmStepCode w M K G).map (Instruction.relocate 3) ++ [.jump 0])

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def configBank (cfg : CookLevin.Config) : TapeBank := fun j => cfg.2[j]!

def HeadsFit (w : Width) (K : Nat) (cfg : CookLevin.Config) : Prop :=
  ∀ j, j < K → tapeAddress (tapeBase K j) K (configBank cfg j).2 < 2 ^ w.bits

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

/-- Direct arithmetic encoding of a configuration. This computes addresses and
copies symbols; it performs no simulation or search for an accepting run. -/
def encodeMemory (w : Width) (K : Nat) (cfg : CookLevin.Config) : Memory w := fun a =>
  if a = 0 then BitVec.ofNat w.bits cfg.1
  else if a ≤ K then
    BitVec.ofNat w.bits (tapeAddress (tapeBase K (a - 1)) K (configBank cfg (a - 1)).2)
  else if a < 1 + 2 * K then 0
  else BitVec.ofNat w.bits ((configBank cfg ((a - (1 + 2 * K)) % K)).1 ((a - (1 + 2 * K)) / K))

def encodeConfig (w : Width) (K : Nat) (cfg : CookLevin.Config) : State w :=
  {mem := encodeMemory w K cfg}

end WordRAM.Uniform

namespace WordRAM.Uniform

variable {w : Width} {m : Model} {k : Nat}

def ValidConfig (K G Q : Nat) (cfg : CookLevin.Config) : Prop :=
  cfg.2.length = K ∧ cfg.1 ≤ Q ∧ ∀ i, i < K → ∀ pos, (configBank cfg i).1 pos < G

def HeadBound (K H : Nat) (cfg : CookLevin.Config) : Prop :=
  ∀ i, i < K → (configBank cfg i).2 ≤ H

end WordRAM.Uniform

/-! A fixed-width program has a finite address footprint, even though `Memory`
is a function on all naturals. These bounds also guide finite TM encodings. -/
namespace WordRAM

variable {w : Width} {m : Model} {k : Nat}

/-- One past the literal cell, including the cell holding an indirect pointer. -/
def Address.literalBound : Address → Nat
  | .direct a | .indirect a => a + 1

def Operand.literalBound : Operand w → Nat
  | .immediate _ => 0
  | .memory a => a.literalBound

def Instruction.literalBound : Instruction w m k → Nat
  | .copy d s | .bitNot d s => max d.literalBound s.literalBound
  | .binary _ d x y => max d.literalBound (max x.literalBound y.literalBound)
  | .native d _ => d.literalBound
  | .branch _ x y _ => max x.literalBound y.literalBound
  | .jump _ | .halt => 0

def Program.literalBound (p : Program w m k) : Nat :=
  (p.map Instruction.literalBound).foldr max 0

/-- All indirect addresses fit below `2^w`; all literal addresses fit below
this program-specific bound. -/
def Program.addressBound (p : Program w m k) : Nat :=
  max (2 ^ w.bits) p.literalBound

end WordRAM
