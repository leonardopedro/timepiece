/-
prove2.me platform library module `Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_InteractiveConsistency_OralAlgorithm_Procedure.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

/-- The condition of step (1) of the procedure (p. 230), for processor `p` with view
`τ = fun w => σ (p :: w)`, `m` faults, processor set `P` and target processor `q`: there are a
subset `Q ⊆ P` of size `> (|P| + m)/2` and a value `v` with `σ_p(p w q) = τ (w ++ [q]) = v` for
every string `w` over `Q` of length `≤ m` (including the empty string). -/
def StepOne {α V : Type*} (m : ℕ) (P : Finset α) (τ : List α → V) (q : α) : Prop :=
  ∃ Q ⊆ P, P.card + m < 2 * Q.card ∧
    ∃ v : V, ∀ w : List α, IsStringOver Q w → w.length ≤ m → τ (w ++ [q]) = v

open Classical in
/-- The recursive procedure of Section 3 (p. 230): `record m P τ q` is the value (`none` = NIL)
that a processor with view `τ` (`τ w = σ (p :: w)`) records for processor `q`, with `m` faults
and processor set `P`.
* Step (1): if `StepOne m P τ q` holds, record the common value; it equals `τ [q]` (take `w = []`).
* Step (2), `m = m' + 1`: apply the procedure for `m'` to `P.erase q` and the view
  `fun w => τ (w ++ [q])` (that is, `σ̂_p(p w) = σ_p(p w q)`), obtaining a vector indexed by
  `P.erase q`; if some value `x` is taken by at least `⌊(|P| + m)/2⌋` of its entries, record `x`,
  otherwise record NIL.
* `m = 0` and step (1) fails: record NIL. -/
noncomputable def record {α V : Type*} [DecidableEq α] :
    ℕ → Finset α → (List α → V) → α → Option V
  | 0, P, τ, q => if StepOne 0 P τ q then some (τ [q]) else none
  | m' + 1, P, τ, q =>
    if StepOne (m' + 1) P τ q then some (τ [q]) else
      if h : ∃ x : Option V, (P.card + (m' + 1)) / 2 ≤
          ((P.erase q).filter
            (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = x)).card
      then Classical.choose h else none

end InteractiveConsistency.OralAlgorithm
