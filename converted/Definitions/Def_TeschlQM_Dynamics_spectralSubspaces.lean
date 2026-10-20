/-
prove2.me platform library module `Definitions.Def_TeschlQM_Dynamics_spectralSubspaces`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Dynamics_spectralSubspaces.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_spectralMeasure

open MeasureTheory

namespace TeschlQM.Dynamics

/-- Teschl, p. 105, (3.83): `ℌ_ac = {ψ ∈ ℌ | μ_ψ is absolutely continuous}` (with respect to
Lebesgue measure, p. 102, (3.72)). -/
def hac {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | TeschlQM.Shared.spectralMeasure P ψ ≪ volume}

/-- Teschl, p. 105, (3.83): `ℌ_sc = {ψ ∈ ℌ | μ_ψ is singularly continuous}`: by pp. 102,
(3.72)–(3.73), `μ_ψ` is singular with respect to Lebesgue measure and continuous, i.e. it has
no atoms. -/
def hsc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | TeschlQM.Shared.spectralMeasure P ψ ⟂ₘ volume ∧ ∀ x : ℝ, TeschlQM.Shared.spectralMeasure P ψ {x} = 0}

/-- Teschl, p. 105, (3.83): `ℌ_pp = {ψ ∈ ℌ | μ_ψ is pure point}`: by p. 102, (3.73), `μ_ψ` is a
pure point (step function) measure, i.e. it is supported on a countable set. -/
def hpp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | ∃ S : Set ℝ, S.Countable ∧ TeschlQM.Shared.spectralMeasure P ψ Sᶜ = 0}

/-- Teschl, p. 127: the **continuous subspace** `ℌ_c = ℌ_ac ⊕ ℌ_sc`, the set of sums of a vector
of `ℌ_ac` and a vector of `ℌ_sc` (the two subspaces are orthogonal by Lemma 3.19, p. 105). -/
def hc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | ∃ a ∈ hac P, ∃ s ∈ hsc P, ψ = a + s}

/-- The orthogonal projection of `ℌ` onto the closed linear span of a set `S ⊆ ℌ`. Applied to
`ℌ_ac`, `ℌ_c`, `ℌ_pp`, which are closed subspaces (Lemma 3.19, p. 105), this is the projector
`P^ac`, `P^c`, `P^pp` of Teschl, pp. 102–105. -/
noncomputable def orthProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set H) : H →L[ℂ] H :=
  ((Submodule.span ℂ S).closure : Submodule ℂ H).starProjection

end TeschlQM.Dynamics
