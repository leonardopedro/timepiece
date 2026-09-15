/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import Mathlib

/-!
# Gauge-variant operators have vanishing expectation values

Source: `book.tex`, chapter *"Gauge symmetry and dissipative dynamics in
probability spaces"* (line 2128) and the Yang–Mills chapter (lines 6730–6780),
where the manuscript states that

> "there is no spontaneous symmetry breaking of the (full or global) gauge
> symmetry, since the expectation-values of the gauge-variant operators
> [vanish]"

and that only gauge-*invariant* operators carry physical information, the
global charge of an abelian or non-abelian gauge theory being one of them.

This file formalizes that statement (the Elitzur-type argument) in the exact
generality in which the book uses it: a state invariant under the gauge
unitaries assigns expectation value `0` to every operator that transforms with
a non-trivial phase (more generally, a non-trivial scalar factor) under some
gauge transformation; and, dually, an operator commuting with the gauge
unitaries has a gauge-independent expectation value.

## Main results

* `expectation_eq_smul_of_covariant` — covariance transports the expectation
  value: `⟪ψ, O ψ⟫ = χ g * ⟪ψ, O ψ⟫` for a gauge-invariant state `ψ`.
* `expectation_gauge_variant_eq_zero` — **headline**: if some gauge
  transformation scales `O` by `χ g ≠ 1`, its expectation value vanishes.
* `no_spontaneous_gauge_symmetry_breaking` — the same statement phrased for a
  phase `e^{iθ}` with `θ` not a multiple of `2π` (a charged operator).
* `expectation_gauge_invariant_operator` — the complementary statement: an
  operator commuting with every gauge unitary has the same expectation value in
  every gauge copy `U g ψ` of a state, so gauge-invariant observables (e.g. the
  global charge) are well defined on gauge orbits.
-/

namespace BookProof.ChapterGaugeVariantVanishing

open scoped InnerProductSpace

variable {G : Type*} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A gauge-invariant state `ψ` and an operator `O` that is *covariant* with
scalar factor `χ g` under the gauge unitary `U g` have proportional expectation
values: `⟪ψ, O ψ⟫ = χ g ⟪ψ, O ψ⟫`. -/
theorem expectation_eq_smul_of_covariant (U : G → (V ≃ₗᵢ[ℂ] V)) (O : V →L[ℂ] V)
    (χ : G → ℂ) (ψ : V) (g : G) (hinv : U g ψ = ψ)
    (hcov : ∀ x : V, O (U g x) = χ g • U g (O x)) :
    ⟪ψ, O ψ⟫_ℂ = χ g * ⟪ψ, O ψ⟫_ℂ := by
  calc ⟪ψ, O ψ⟫_ℂ = ⟪U g ψ, O (U g ψ)⟫_ℂ := by rw [hinv]
    _ = χ g * ⟪ψ, O ψ⟫_ℂ := by
        rw [hcov ψ, inner_smul_right, LinearIsometryEquiv.inner_map_map]

/-- **Headline (book 6757–6763).** A state invariant under the gauge group gives
expectation value zero to every operator that some gauge transformation scales
by a factor different from `1`: gauge-variant operators are unobservable, so the
gauge symmetry cannot be spontaneously broken. -/
theorem expectation_gauge_variant_eq_zero (U : G → (V ≃ₗᵢ[ℂ] V)) (O : V →L[ℂ] V)
    (χ : G → ℂ) (ψ : V) (g : G) (hinv : U g ψ = ψ)
    (hcov : ∀ x : V, O (U g x) = χ g • U g (O x)) (hχ : χ g ≠ 1) :
    ⟪ψ, O ψ⟫_ℂ = 0 := by
  have h := expectation_eq_smul_of_covariant U O χ ψ g hinv hcov
  have : (1 - χ g) * ⟪ψ, O ψ⟫_ℂ = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hχ
  · exact h0

/-- The charged-operator form of the previous theorem: an operator picking up a
phase `e^{i θ}` with `θ` not a multiple of `2π` under a gauge transformation
leaving the state invariant has vanishing expectation value. -/
theorem no_spontaneous_gauge_symmetry_breaking (U : G → (V ≃ₗᵢ[ℂ] V))
    (O : V →L[ℂ] V) (ψ : V) (g : G) (θ : ℝ) (hinv : U g ψ = ψ)
    (hcov : ∀ x : V, O (U g x) = Complex.exp (θ * Complex.I) • U g (O x))
    (hθ : ∀ n : ℤ, θ ≠ n * (2 * Real.pi)) :
    ⟪ψ, O ψ⟫_ℂ = 0 := by
  refine expectation_gauge_variant_eq_zero U O (fun _ => Complex.exp (θ * Complex.I))
    ψ g hinv hcov ?_
  intro hone
  rcases Complex.exp_eq_one_iff.mp hone with ⟨n, hn⟩
  have hre : θ = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa [Complex.ext_iff, mul_comm, mul_left_comm, mul_assoc] using this
  exact hθ n hre

/-- The complementary statement: an operator that commutes with a gauge unitary
has the same expectation value in `ψ` and in the gauge copy `U g ψ`.  Thus
gauge-invariant observables — such as the global charge — are functions on the
gauge orbits, exactly as the book requires (book 6730–6740). -/
theorem expectation_gauge_invariant_operator (U : G → (V ≃ₗᵢ[ℂ] V))
    (O : V →L[ℂ] V) (ψ : V) (g : G)
    (hcomm : ∀ x : V, O (U g x) = U g (O x)) :
    ⟪U g ψ, O (U g ψ)⟫_ℂ = ⟪ψ, O ψ⟫_ℂ := by
  rw [hcomm ψ, LinearIsometryEquiv.inner_map_map]

end BookProof.ChapterGaugeVariantVanishing
