/-
prove2.me platform library module `Definitions.Def_TeschlODE_HigherDim_divergence`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_HigherDim_divergence.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.2, p. 237 (proof of Lemma 8.8): the divergence
`div f(x) = ∑ᵢ ∂fᵢ/∂xᵢ(x) = tr(df(x))` of a vector field `f : ℝⁿ → ℝⁿ`. -/
noncomputable def divergence {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1) i

end TeschlODE.HigherDim
