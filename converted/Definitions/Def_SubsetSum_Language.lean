/-
prove2.me platform library module `Definitions.Def_SubsetSum_Language`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_SubsetSum_Language.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_BinaryNat_Encoding
import Definitions.Def_MurtyKabadi_Reduction_SubsetSum
import Definitions.Def_CookLevin_Complexity

set_option autoImplicit false

namespace SubsetSumNP

/-- The ordered list of binary input values, followed by the binary target. -/
def encodeInstance (xs : List Nat) (target : Nat) : List Bool :=
  NPBinary.encodeList xs ++ NPBinary.encodeNat target

/-- Reuse the published indexed subset-sum predicate. Each input position can
be selected at most once; repeated values at different positions are distinct
choices. The empty selection is permitted. -/
def HasSubsetSum (xs : List Nat) (target : Nat) : Prop :=
  MurtyKabadi.Reduction.SubsetSumSolvable xs.get target

/-- Binary encodings of lists of strictly positive natural numbers admitting
an indexed subset whose sum equals the nonnegative target. Empty lists are
allowed. All strings outside this exact encoding, including encodings with
zero-valued input items, are rejected. -/
def SUBSET_SUM : CookLevin.Language := fun x =>
  ∃ (xs : List Nat) (target : Nat),
    x = encodeInstance xs target ∧
    (∀ a ∈ xs, 0 < a) ∧ HasSubsetSum xs target

end SubsetSumNP
