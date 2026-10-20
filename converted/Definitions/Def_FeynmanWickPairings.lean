/-
prove2.me platform library module `Definitions.Def_FeynmanWickPairings`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_FeynmanWickPairings.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace FeynmanWick

/-- `IsPairing σ` says that the permutation `σ` of the `2 * n` labels
`0, 1, …, 2 * n - 1` is a fixed-point-free involution: it squares to the identity
and moves every label. Such a permutation is the same thing as a partition of the
labels into `n` unordered pairs `{i, σ i}` (a perfect matching). -/
def IsPairing {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i, σ (σ i) = i) ∧ ∀ i, σ i ≠ i

instance instDecidableIsPairing {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) :
    Decidable (IsPairing σ) :=
  inferInstanceAs (Decidable ((∀ i, σ (σ i) = i) ∧ ∀ i, σ i ≠ i))

/-- The finite set of all pairings (perfect matchings) of the `2 * n` labels. -/
def pairings (n : ℕ) : Finset (Equiv.Perm (Fin (2 * n))) :=
  Finset.univ.filter IsPairing

/-- The product of the weights `G i (σ i)` over the pairs of a pairing `σ`.
Each pair `{i, σ i}` is counted exactly once, by summing over its smaller element. -/
def pairProd {n : ℕ} (G : Fin (2 * n) → Fin (2 * n) → ℝ)
    (σ : Equiv.Perm (Fin (2 * n))) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), G i (σ i)

/-- The Wick sum of a symmetric weight `G`: the sum, over all pairings of the
`2 * n` labels, of the product of the weights of the pairs. -/
def wickSum {n : ℕ} (G : Fin (2 * n) → Fin (2 * n) → ℝ) : ℝ :=
  ∑ σ ∈ pairings n, pairProd G σ

end FeynmanWick
