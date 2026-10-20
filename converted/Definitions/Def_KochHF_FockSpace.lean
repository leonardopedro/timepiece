/-
prove2.me platform library module `Definitions.Def_KochHF_FockSpace`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_KochHF_FockSpace.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Second quantization on a finite orbital basis

E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, Sec. 2 (Eqs. (14)-(16), (23), (26), (33), (41)).

Fix `K` orthonormal reference orbitals `ϕ_0, …, ϕ_{K-1}`.  A one-electron orbital is its
coefficient vector `Fin K → ℂ`.  The Fock space has the orthonormal occupation-number basis
`|S⟩`, `S ⊆ {0,…,K-1}`; Fock-space vectors are functions `Finset (Fin K) → ℂ` and operators are
complex matrices indexed by `Finset (Fin K)`.
-/

noncomputable section

namespace KochHF

open Matrix

/-- Vectors in the Fock space over `K` orbitals (coefficients in the occupation-number basis). -/
abbrev FockVec (K : ℕ) := Finset (Fin K) → ℂ

/-- Linear operators on the Fock space over `K` orbitals. -/
abbrev FockOp (K : ℕ) := Matrix (Finset (Fin K)) (Finset (Fin K)) ℂ

/-- Fermion sign `(-1)^{#{j ∈ S : i < j}}`. -/
def fermiSign {K : ℕ} (i : Fin K) (S : Finset (Fin K)) : ℂ :=
  (-1) ^ (S.filter (fun j => i < j)).card

/-- Creation operator `c†_i` of the reference orbital `ϕ_i`:
`c†_i |S⟩ = (-1)^{#{j ∈ S : j > i}} |S ∪ {i}⟩` if `i ∉ S`, and `c†_i |S⟩ = 0` if `i ∈ S`. -/
def cdag {K : ℕ} (i : Fin K) : FockOp K :=
  Matrix.of fun T S => if i ∉ S ∧ T = insert i S then fermiSign i S else 0

/-- Annihilation operator `c_i`, the adjoint (conjugate transpose) of `c†_i`. -/
def cann {K : ℕ} (i : Fin K) : FockOp K := (cdag i)ᴴ

/-- The vacuum state `|0⟩` (no orbital occupied). -/
def vacuum (K : ℕ) : FockVec K := Pi.single ∅ 1

/-- The occupation-number basis state `|S⟩`. -/
def basisState {K : ℕ} (S : Finset (Fin K)) : FockVec K := Pi.single S 1

/-- Fock-space inner product `⟨ψ|φ⟩ = Σ_S conj(ψ_S) φ_S`. -/
def fockInner {K : ℕ} (ψ φ : FockVec K) : ℂ := star ψ ⬝ᵥ φ

/-- Matrix element `⟨ψ|A|φ⟩`. -/
def matEl {K : ℕ} (ψ : FockVec K) (A : FockOp K) (φ : FockVec K) : ℂ := star ψ ⬝ᵥ (A *ᵥ φ)

/-- One-electron inner product `⟨φ|χ⟩ = Σ_μ conj(φ_μ) χ_μ`. -/
def orbInner {K : ℕ} (φ χ : Fin K → ℂ) : ℂ := star φ ⬝ᵥ χ

/-- Creation operator of the orbital `|φ⟩ = Σ_μ φ_μ |ϕ_μ⟩`: `c†_φ = Σ_μ φ_μ c†_μ` (Eq. (16)). -/
def cdagOrb {K : ℕ} (φ : Fin K → ℂ) : FockOp K := ∑ μ, φ μ • cdag μ

/-- Annihilation operator of the orbital `|φ⟩`: `c_φ = Σ_μ conj(φ_μ) c_μ`. -/
def cannOrb {K : ℕ} (φ : Fin K → ℂ) : FockOp K := ∑ μ, star (φ μ) • cann μ

/-- The Slater determinant `c†_{α_N} ⋯ c†_{α_1} |0⟩` of the orbitals `α_1, …, α_N`
(Eqs. (23), (26)); the orbitals are indexed `α 0, …, α (N-1)` and `c†_{α 0}` acts first. -/
def slater {K N : ℕ} (α : Fin N → Fin K → ℂ) : FockVec K :=
  (List.ofFn fun n => cdagOrb (α n)).reverse.prod *ᵥ vacuum K

/-- `P|φ⟩ = Σ_n |α_n⟩⟨α_n|φ⟩`, the projection onto the occupied orbitals (Eq. (41)). -/
def occProj {K N : ℕ} (α : Fin N → Fin K → ℂ) (φ : Fin K → ℂ) : Fin K → ℂ :=
  ∑ n, orbInner (α n) φ • α n

/-- Second-quantized one-body operator `M̂ = Σ_{a,b} M_{ab} c†_a c_b` (Eqs. (33), (55)). -/
def oneBodyOp {K : ℕ} (M : Matrix (Fin K) (Fin K) ℂ) : FockOp K :=
  ∑ a, ∑ b, M a b • (cdag a * cann b)

end KochHF

end
