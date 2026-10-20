/-
prove2.me platform library module `Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Dynamics_IsRelativelyCompact.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_compactOperators

namespace TeschlQM.Dynamics

/-- Teschl, p. 73, (2.66): `R` is the **resolvent** `R_A(z) = (A − z)⁻¹` of `A` at `z ∈ ρ(A)`:
`R ∈ 𝔏(ℌ)` maps `ℌ` into `𝔇(A)` and is a two-sided inverse of `A − z : 𝔇(A) → ℌ`. In particular
`z ∈ ρ(A)` iff such an `R` exists. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ) ∧
    ∀ φ : H, ∃ hφ : R φ ∈ A.domain, A ⟨R φ, hφ⟩ - z • R φ = φ

/-- Teschl, p. 128, (5.12): the (possibly unbounded) operator `K` is **relatively compact** with
respect to `A` if `K R_A(z) ∈ ℭ(ℌ)` for one `z ∈ ρ(A)`: there are `z ∈ ρ(A)` with resolvent
`R = R_A(z)` and a compact operator `C` such that `Ran R_A(z) ⊆ 𝔇(K)` (so that `K R_A(z)` is
defined on all of `ℌ`) and `K R_A(z) = C`. A bounded `K ∈ 𝔏(ℌ)` enters as
`(K : H →ₗ[ℂ] H).toPMap ⊤`. -/
def IsRelativelyCompact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K A : H →ₗ.[ℂ] H) : Prop :=
  ∃ z : ℂ, ∃ R : H →L[ℂ] H, IsResolventAt A z R ∧
    ∃ C ∈ TeschlQM.Shared.compactOperators H, ∀ φ : H, ∃ hφ : R φ ∈ K.domain, K ⟨R φ, hφ⟩ = C φ

open Classical in
/-- The value `Kψ` of a partially defined operator at `ψ ∈ 𝔇(K)`, extended by `0` outside
`𝔇(K)`. In this mission it is only evaluated at points of `𝔇(A) ⊆ 𝔇(K)` (for relatively
compact `K`), where it is `Kψ`. -/
noncomputable def applyExt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : H →ₗ.[ℂ] H) (ψ : H) : H :=
  if h : ψ ∈ K.domain then K ⟨ψ, h⟩ else 0

end TeschlQM.Dynamics
