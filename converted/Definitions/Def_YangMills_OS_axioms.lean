import Mathlib

/-!
# Euclidean (Osterwalder–Schrader) quantum field theories on `ℝ⁴` and the mass gap

This file sets up the continuum side of the Yang–Mills existence and mass gap problem:
Schwinger (Euclidean correlation) functions, the Osterwalder–Schrader axioms, non-triviality,
and the mass gap expressed as exponential clustering of the truncated two-point function.
-/

namespace YangMills

open MeasureTheory Filter Topology Finset

/-- Euclidean space-time `ℝ⁴`, realised as `Fin 4 → ℝ`; the coordinate `x 0` is Euclidean time. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- Real-valued Schwartz test functions on `ℝ⁴`. -/
abbrev TestFn : Type := SchwartzMap Spacetime ℝ

/-- The unit vector in the Euclidean time direction. -/
noncomputable def timeDir : Spacetime := Pi.single 0 1

/-- Euclidean time reflection `θ (x⁰, x⃗) = (-x⁰, x⃗)`. -/
def timeReflect (x : Spacetime) : Spacetime := Function.update x 0 (-x 0)

/-- A Euclidean motion of `ℝ⁴`: an orthogonal matrix together with a translation vector. -/
structure EuclideanMotion where
  /-- The linear part, an orthogonal `4 × 4` matrix. -/
  matrix : Matrix (Fin 4) (Fin 4) ℝ
  /-- The translation part. -/
  vector : Spacetime
  /-- Orthogonality of the linear part. -/
  orthogonal : matrix.transpose * matrix = 1

/-- The action of a Euclidean motion on a point: `x ↦ A x + b`. -/
def EuclideanMotion.apply (g : EuclideanMotion) (x : Spacetime) : Spacetime :=
  g.matrix.mulVec x + g.vector

/-- A test function is *supported at positive time* if it vanishes off `{x : 0 < x⁰}`. -/
def PosTime (f : TestFn) : Prop := ∀ x : Spacetime, f x ≠ 0 → 0 < x 0

/-- A family of Schwinger functions on `ℝ⁴` satisfying the Osterwalder–Schrader axioms.

`S n (f₀, …, f_{n-1})` is the `n`-point Euclidean correlation function smeared against the test
functions `f i`. The fields record, in order: normalisation of the `0`-point function, additivity,
homogeneity and separate continuity in each slot (a separately-continuous multilinear, i.e.
tempered-distribution, form of OS0), Euclidean invariance (OS1), reflection positivity (OS2) and
permutation symmetry (OS3). -/
structure OSTheory where
  /-- The Schwinger functions. -/
  S : (n : ℕ) → (Fin n → TestFn) → ℂ
  /-- Normalisation: the `0`-point function is `1`. -/
  norm_one : ∀ f : Fin 0 → TestFn, S 0 f = 1
  /-- Additivity in each slot. -/
  add_slot : ∀ (n : ℕ) (f : Fin n → TestFn) (i : Fin n) (g h : TestFn),
    S n (Function.update f i (g + h))
      = S n (Function.update f i g) + S n (Function.update f i h)
  /-- Homogeneity in each slot. -/
  smul_slot : ∀ (n : ℕ) (f : Fin n → TestFn) (i : Fin n) (c : ℝ) (g : TestFn),
    S n (Function.update f i (c • g)) = (c : ℂ) * S n (Function.update f i g)
  /-- Separate continuity in each slot (temperedness). -/
  cont_slot : ∀ (n : ℕ) (f : Fin n → TestFn) (i : Fin n),
    Continuous fun g : TestFn => S n (Function.update f i g)
  /-- OS1, Euclidean invariance: precomposing every test function with a Euclidean motion
  leaves the Schwinger functions unchanged. -/
  euclid_inv : ∀ (n : ℕ) (g : EuclideanMotion) (f f' : Fin n → TestFn),
    (∀ (i : Fin n) (x : Spacetime), f' i x = f i (g.apply x)) → S n f' = S n f
  /-- OS3, permutation symmetry. -/
  perm_symm : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → TestFn), S n (f ∘ σ) = S n f
  /-- OS2, reflection positivity: for finitely many families `F j` of test functions supported at
  positive time, with time-reflected copies `Fθ j`, and complex coefficients `c j`, the quadratic
  form `∑_{j,l} conj (c j) * c l * S (Fθ j, F l)` is a non-negative real number. -/
  refl_pos : ∀ (m : ℕ) (k : Fin m → ℕ) (F Fθ : (j : Fin m) → Fin (k j) → TestFn)
      (c : Fin m → ℂ),
    (∀ (j : Fin m) (i : Fin (k j)), PosTime (F j i)) →
    (∀ (j : Fin m) (i : Fin (k j)) (x : Spacetime), Fθ j i x = F j i (timeReflect x)) →
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ j : Fin m, ∑ l : Fin m,
        (starRingEnd ℂ) (c j) * c l * S (k j + k l) (Fin.append (Fθ j) (F l)) = (r : ℂ)

/-- The truncated (connected) two-point function of a Euclidean theory. -/
noncomputable def OSTheory.truncTwoPoint (Q : OSTheory) (f g : TestFn) : ℂ :=
  Q.S 2 ![f, g] - Q.S 1 ![f] * Q.S 1 ![g]

/-- A Euclidean theory is *non-trivial* if some truncated two-point function is non-zero, i.e.
the fields are genuinely correlated. -/
def OSTheory.IsNonTrivial (Q : OSTheory) : Prop :=
  ∃ f g : TestFn, Q.truncTwoPoint f g ≠ 0

/-- `Q` *has a mass gap of size at least* `Δ`: `Δ > 0` and, for all test functions `f` and `g`,
the truncated two-point function of `f` against the time translate of `g` by `t ≥ 0` decays
at least like `C e^{-Δ t}`.

This is the Euclidean (exponential clustering) formulation of the statement that the spectrum of
the Hamiltonian obtained by Osterwalder–Schrader reconstruction is contained in `{0} ∪ [Δ, ∞)`. -/
def OSTheory.HasMassGap (Q : OSTheory) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ f g : TestFn, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ) (gt : TestFn), 0 ≤ t → (∀ x : Spacetime, gt x = g (x - t • timeDir)) →
      ‖Q.truncTwoPoint f gt‖ ≤ C * Real.exp (-Δ * t)

end YangMills

