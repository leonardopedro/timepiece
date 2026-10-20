/-
prove2.me platform library module `Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_InteractiveConsistency_OralAlgorithm_Scenario.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace InteractiveConsistency.OralAlgorithm

/-- `w` is a string over `S`: every letter of `w` lies in `S` (repetitions allowed). -/
def IsStringOver {α : Type*} (S : Finset α) (w : List α) : Prop :=
  ∀ x ∈ w, x ∈ S

/-- Consistency of a `k`-level scenario with the set `N` of nonfaulty processors (p. 230):
`σ (p :: q :: w) = σ (q :: w)` for every nonfaulty `q ∈ N`, every processor `p ∈ P` and every
string `w` over `P`, as long as the string `p q w` lies in the domain of a `k`-level scenario,
i.e. has length `≤ k + 1`.  The string `p₁ p₂ … p_r` is the list `[p₁, …, p_r]`. -/
def ConsistentUpTo {α V : Type*} (P N : Finset α) (k : ℕ) (σ : List α → V) : Prop :=
  ∀ q ∈ N, ∀ p ∈ P, ∀ w : List α, IsStringOver P w → w.length + 2 ≤ k + 1 →
    σ (p :: q :: w) = σ (q :: w)

/-- A family `F p` (processor `p`'s decision rule, applied to `p`'s view `fun w => σ (p :: w)`
and a processor `r`, returning a value or `none` = NIL) assures interactive consistency for `m`
faults on `(m + 1)`-level scenarios (p. 229 (1)–(2), p. 232 (i)–(ii)): for every set `N ⊆ P`
with `|N| ≥ |P| - m` and every `σ` consistent with `N` at level `m + 1`,
(i) every nonfaulty `p` computes `σ [q]` for every nonfaulty `q`, and
(ii) any two nonfaulty processors compute the same value for every `r ∈ P`. -/
def AssuresICLevel {α V : Type*} (P : Finset α) (m : ℕ)
    (F : α → (List α → V) → α → Option V) : Prop :=
  ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m → ∀ σ : List α → V,
    ConsistentUpTo P N (m + 1) σ →
      (∀ p ∈ N, ∀ q ∈ N, F p (fun w => σ (p :: w)) q = some (σ [q])) ∧
      (∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        F p (fun w => σ (p :: w)) r = F p' (fun w => σ (p' :: w)) r)

end InteractiveConsistency.OralAlgorithm
