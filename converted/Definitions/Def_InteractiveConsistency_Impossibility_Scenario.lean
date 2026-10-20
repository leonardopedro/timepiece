/-
prove2.me platform library module `Definitions.Def_InteractiveConsistency_Impossibility_Scenario`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_InteractiveConsistency_Impossibility_Scenario.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport, *Reaching agreement in the presence of faults*, J. ACM 27 (1980),
p. 232, Section 4: a string over `P`, i.e. a list all of whose letters lie in the processor set `P`.
The string `p₁p₂…p_r` of the paper is the list `[p₁, …, p_r]`, read left to right. The empty list
is the empty string, a member of `P*`. -/
def IsString {α : Type*} (P : Finset α) (w : List α) : Prop :=
  ∀ x ∈ w, x ∈ P

instance {α : Type*} [DecidableEq α] (P : Finset α) (w : List α) : Decidable (IsString P w) := by
  unfold IsString; infer_instance

/-- p. 232: the `p`-scenario `σ_p`, the restriction of the scenario `σ` to strings beginning with
`p`, presented as the map `w ↦ σ(p w)`. -/
def restrict {α V : Type*} (σ : List α → V) (p : α) : List α → V :=
  fun w => σ (p :: w)

/-- p. 232: the scenario `σ` is *consistent with* the set `N` of nonfaulty processors if for each
`q ∈ N`, `p ∈ P` and `w ∈ P*` (the empty string included), `σ(pqw) = σ(qw)`. -/
def ConsistentWith {α V : Type*} (P N : Finset α) (σ : List α → V) : Prop :=
  ∀ q ∈ N, ∀ p ∈ P, ∀ w : List α, IsString P w → σ (p :: q :: w) = σ (q :: w)

/-- p. 232: the family `{F_p | p ∈ P}` *assures interactive consistency for `m` faults* if for each
choice of `N ⊆ P` with `|N| ≥ n − m` (here `n = |P|`, written `|P| ≤ |N| + m`) and each scenario `σ`
consistent with `N`,
(i) for all `p, q ∈ N`, `F_p(σ_p, q) = σ(q)`, and
(ii) for all `p, q ∈ N` and `r ∈ P`, `F_p(σ_p, r) = F_q(σ_q, r)`.
`F p τ q` is the value processor `p` computes for `q` from the `p`-scenario `τ`; it is applied only
to `σ_p = restrict σ p`, never to `σ`. -/
def AssuresIC {α V : Type*} (P : Finset α) (m : ℕ) (F : α → (List α → V) → α → V) : Prop :=
  ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m →
    ∀ σ : List α → V, ConsistentWith P N σ →
      (∀ p ∈ N, ∀ q ∈ N, F p (restrict σ p) q = σ [q]) ∧
      (∀ p ∈ N, ∀ q ∈ N, ∀ r ∈ P, F p (restrict σ p) r = F q (restrict σ q) r)

end InteractiveConsistency.Impossibility
