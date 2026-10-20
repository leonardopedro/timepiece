/-
prove2.me platform library module `Definitions.Def_MatchingPSD`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_MatchingPSD.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingPSD.lean; bytes 16..1759
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PerfectMatchingPSD

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def IsPerfectMatching {n : ℕ} (M : Finset (Edge n)) : Prop :=
  ∀ v : Fin n, (M.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1

abbrev PerfectMatching (n : ℕ) :=
  {M : Finset (Edge n) // IsPerfectMatching M}

abbrev OddCut (n : ℕ) := {U : Finset (Fin n) // Odd U.card}

abbrev Row (n : ℕ) := Edge n ⊕ OddCut n

def Crosses {n : ℕ} (U : Finset (Fin n)) (e : Edge n) : Prop :=
  (e.1.1 ∈ U ∧ e.1.2 ∉ U) ∨ (e.1.1 ∉ U ∧ e.1.2 ∈ U)

noncomputable def crossingCount {n : ℕ} (U : Finset (Fin n))
    (M : PerfectMatching n) : ℕ := by
  classical
  exact (M.1.filter (Crosses U)).card

noncomputable def slack {n : ℕ} (i : Row n) (M : PerfectMatching n) : ℝ := by
  classical
  exact match i with
  | Sum.inl e => if e ∈ M.1 then 1 else 0
  | Sum.inr U => (crossingCount U.1 M : ℝ) - 1

/-- Real PSD factors of order `r`, without equivariance or rank-one restrictions. -/
def HasFactorization (n r : ℕ) : Prop :=
  ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
    (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
    (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
    ∀ i M, slack i M = Matrix.trace (A i * B M)

/-- The least positive order of a real PSD factorization. -/
noncomputable def psdRank (n : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ HasFactorization n r}

/-- Every positive real power is eventually smaller than the PSD rank,
uniformly over all even vertex counts. The exponentiation is real `rpow`. -/
def MainClaim : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n : ℝ) ^ C < (psdRank n : ℝ)



end PerfectMatchingPSD
end OAI
