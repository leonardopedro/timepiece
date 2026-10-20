/-
prove2.me platform library module `Definitions.Def_BinaryNat_Encoding`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_BinaryNat_Encoding.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Satisfiability
import Mathlib.Data.Nat.Bits

set_option autoImplicit false

namespace NPBinary

/-- A canonical natural-number encoding: its binary bit length in the shared
unary header format, followed by its least-significant-bit-first binary digits.
Zero has no binary digits and is encoded by the single header bit `false`.
Only the bit length is unary; the value itself is binary. -/
def encodeNat (n : Nat) : List Bool :=
  CookLevin.encodeNat n.bits.length ++ n.bits

/-- A list count in the shared unary header format, followed by the
self-delimiting binary encoding of each entry, in list order. -/
def encodeList (xs : List Nat) : List Bool :=
  CookLevin.encodeNat xs.length ++ (xs.map encodeNat).flatten

end NPBinary
