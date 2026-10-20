/-
prove2.me platform library module `Definitions.Def_DurrettProbability_MarkovChain`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_DurrettProbability_MarkovChain.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Filter

namespace DurrettProbability

variable {S : Type*}

/-- The `n`-step transition probabilities `pⁿ(x,y)` of a transition probability `p` on a
countable state space, with `p⁰(x,y) = 1` if `x = y` and `0` otherwise.
Durrett, *Probability: Theory and Examples*, section 5.2. -/
noncomputable def stepProb [DecidableEq S] (p : S → S → ℝ) : ℕ → S → S → ℝ
  | 0, x, y => if x = y then 1 else 0
  | (n + 1), x, y => ∑' z, p x z * stepProb p n z y

/-- The first-passage probabilities `fⁿ(x,y) = P_x(T_y = n)`: `f¹(x,y) = p(x,y)` and
`fⁿ⁺¹(x,y) = ∑_{z ≠ y} p(x,z) fⁿ(z,y)`, the chain reaching `y` for the first time at step `n`. -/
noncomputable def firstPassage [DecidableEq S] (p : S → S → ℝ) : ℕ → S → S → ℝ
  | 0, _, _ => 0
  | 1, x, y => p x y
  | (n + 2), x, y => ∑' z, if z = y then 0 else p x z * firstPassage p (n + 1) z y

/-- `ρ_{xy} = P_x(T_y < ∞) = ∑_{n ≥ 1} fⁿ(x,y)`, the probability that the chain started at `x`
ever visits `y`. -/
noncomputable def hitProb [DecidableEq S] (p : S → S → ℝ) (x y : S) : ℝ :=
  ∑' n : ℕ, firstPassage p (n + 1) x y

/-- `E_y T_y = ∑_{n ≥ 1} n fⁿ(y,y)`, the expected return time to `y`. -/
noncomputable def meanReturnTime [DecidableEq S] (p : S → S → ℝ) (y : S) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * firstPassage p (n + 1) y y

/-- A state is **recurrent** when the chain returns to it with probability one, `ρ_{yy} = 1`. -/
def Recurrent [DecidableEq S] (p : S → S → ℝ) (y : S) : Prop := hitProb p y y = 1

/-- The chain is **irreducible** when every state can be reached from every other,
`ρ_{xy} > 0` for all `x, y`. -/
def Irreducible [DecidableEq S] (p : S → S → ℝ) : Prop := ∀ x y, 0 < hitProb p x y

/-- A state `x` is **aperiodic** when the greatest common divisor of
`I_x = {n ≥ 1 : pⁿ(x,x) > 0}` is `1`: the only natural number dividing every element of `I_x`
is `1`.  (For `I_x` empty this fails, as it should: the period of such a state is undefined.) -/
def Aperiodic [DecidableEq S] (p : S → S → ℝ) (x : S) : Prop :=
  ∀ d : ℕ, (∀ n : ℕ, 1 ≤ n → 0 < stepProb p n x x → d ∣ n) → d = 1

/-- `π` is a **stationary distribution** for `p`: a probability vector fixed by `p`. -/
def StationaryDist (p : S → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ (∑' x, π x) = 1 ∧ ∀ y, (∑' x, π x * p x y) = π y

/-- The standing hypotheses on a transition probability: non-negative entries and rows that are
summable and sum to one. -/
def IsTransition (p : S → S → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ (∀ x, Summable (p x)) ∧ ∀ x, (∑' y, p x y) = 1

end DurrettProbability
