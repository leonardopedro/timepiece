import Mathlib

/-!
# Chapter GroundStateConjugation — the ground-state transform preserves the Rayleigh quotient

§21.9–§21.10 of `FockLangevinOperator` prove the pointwise identity `A(e^{Φ/2}g) = e^{Φ/2}(S g)`:
the pCNL generator on `L²(π)` is similar, through multiplication by the ground state, to the
Schrödinger operator `−Δ + V_eff`.  That identity is what makes the spectral gap a statement about
`−Δ + V_eff`, and the step from "the operators are conjugated" to "the infima of the Rayleigh
quotients agree" is the spectral step.  This chapter proves it in the finite model the corpus can
state: a finite index set with a strictly positive weight `π = F²`, an operator `S` on the weighted
side and an operator `A` on the flat side related by `A(F·g) = F·(S g)`.

## Contents

* `flatPair`, `piPair` — the two pairings, `∑ᵢ uᵢvᵢ` and `∑ᵢ πᵢuᵢvᵢ`;
* `rayleigh`, `rayleighPi` — the Rayleigh quotients of `A` in the flat pairing and of `S` in the
  `π` pairing;
* **`rayleigh_groundState`** — `rayleigh A (F·g) = rayleighPi π S g`: the substitution `f = F·g`
  preserves the quotient;
* **`flatPair_groundState`** — `⟪F·g, F⟫ = ⟪g, 1⟫_π`, so the mean-zero constraint maps to
  orthogonality to the constant;
* **`rayleigh_range_groundState`** — the sets of quotients over the two constrained subspaces are
  equal, and **`sInf_rayleigh_eq`** — so are their infima.

## Honest boundary

Finite index sets, no integration: this is the algebraic content of the spectral step, not the
`L²(π)` statement.  The corpus has no measure theory to state the latter — the passage from these
finite sums to `∫` over `ℝ^d` is not in this chapter.
-/

noncomputable section

namespace BookProof.MCMC.GroundState

open Finset

variable {ι : Type*} [Fintype ι]

/-- The flat pairing `∑ᵢ uᵢ·vᵢ`. -/
def flatPair (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

/-- The weighted pairing `∑ᵢ πᵢ·uᵢ·vᵢ`. -/
def piPair (π u v : ι → ℝ) : ℝ := ∑ i, π i * u i * v i

/-- The Rayleigh quotient of `A` at `u` in the flat pairing. -/
def rayleigh (A : (ι → ℝ) → ι → ℝ) (u : ι → ℝ) : ℝ :=
  flatPair u (A u) / flatPair u u

/-- The Rayleigh quotient of `S` at `u` in the `π` pairing. -/
def rayleighPi (π : ι → ℝ) (S : (ι → ℝ) → ι → ℝ) (u : ι → ℝ) : ℝ :=
  piPair π u (S u) / piPair π u u

theorem flatPair_zero (u : ι → ℝ) : flatPair 0 u = 0 := by
  simp [flatPair]

/-- **The conjugation preserves the Rayleigh quotient.**  If `A` is the flat-side operator and `S`
the weighted-side one, related by `A(F·g) = F·(S g)`, then the quotient of `A` at `F·g` is the
quotient of `S` at `g` in the measure `π = F²`. -/
theorem rayleigh_groundState {A S : (ι → ℝ) → ι → ℝ} {F : ι → ℝ}
    (hA : ∀ g, A (F * g) = F * S g) (g : ι → ℝ) :
    rayleigh A (F * g) = rayleighPi (fun i => F i * F i) S g := by
  unfold rayleigh rayleighPi flatPair piPair
  rw [hA g]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.mul_apply]; ring
  · exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.mul_apply]; ring

/-- The constraint transfers: `⟪F·g, F⟫` in the flat pairing is `⟪g, 1⟫` in the `π = F²` pairing. -/
theorem flatPair_groundState (F g : ι → ℝ) :
    flatPair (F * g) F = piPair (fun i => F i * F i) g 1 := by
  unfold flatPair piPair
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.mul_apply, Pi.one_apply]
  ring

/-- **The set of quotients is the same on both sides**, over the subspaces orthogonal to the ground
state (`F` on the flat side, the constant `1` on the weighted side). -/
theorem rayleigh_range_groundState {A S : (ι → ℝ) → ι → ℝ} {F : ι → ℝ}
    (hF : ∀ i, F i ≠ 0) (hA : ∀ g, A (F * g) = F * S g) :
    {q | ∃ f, rayleigh A f = q ∧ flatPair f F = 0}
      = {q | ∃ g, rayleighPi (fun i => F i * F i) S g = q
          ∧ piPair (fun i => F i * F i) g 1 = 0} := by
  ext q
  constructor
  · rintro ⟨f, hq, hcon⟩
    have hsplit : F * (f / F) = f := by
      funext i
      simp only [Pi.mul_apply, Pi.div_apply]
      exact mul_div_cancel₀ (f i) (hF i)
    refine ⟨f / F, ?_, ?_⟩
    · rw [← rayleigh_groundState hA (f / F), hsplit, hq]
    · rw [← flatPair_groundState, hsplit, hcon]
  · rintro ⟨g, hq, hcon⟩
    refine ⟨F * g, ?_, ?_⟩
    · rw [rayleigh_groundState hA, hq]
    · rw [flatPair_groundState, hcon]

/-- **The ground-state transformation preserves the infimum of the Rayleigh quotient** — the
spectral step: the gap of the generator on the weighted side is the gap of the Schrödinger operator
on the flat side. -/
theorem sInf_rayleigh_eq {A S : (ι → ℝ) → ι → ℝ} {F : ι → ℝ}
    (hF : ∀ i, F i ≠ 0) (hA : ∀ g, A (F * g) = F * S g) :
    sInf {q | ∃ f, rayleigh A f = q ∧ flatPair f F = 0}
      = sInf {q | ∃ g, rayleighPi (fun i => F i * F i) S g = q
          ∧ piPair (fun i => F i * F i) g 1 = 0} := by
  rw [rayleigh_range_groundState hF hA]

end BookProof.MCMC.GroundState
