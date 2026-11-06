import Mathlib
import BookProof.OSReconstruction.PhysicalSpace

/-!
# The emergent Hamiltonian

Plan: `cftproof.md`, Phase 4.2 — "Define the time translation `τ ↦ e^{−τH}`, show `P_τ` is a
nonnegative contraction semigroup, and the Hamiltonian is self-adjoint and bounded below:
`.emergent_hamiltonian_selfAdjoint`, `.emergent_hamiltonian_nonnegative`."

## What is proved here

* `TimeTranslation` — a one-parameter group of linear maps on the observables;
* `timeTranslation_semigroup` — `T(s+t) = T(s) ∘ T(t)`;
* `osNorm_evolution_antitone` — **the evolution is a contraction in the OS seminorm** whenever
  it does not increase `⟨F,F⟩`: `‖T(σ+τ)F‖ ≤ ‖T(σ)F‖` for `τ ≥ 0`.  This is the "nonnegative
  contraction semigroup" content of Phase 4.2, stated at the level of the OS norm;
* `radical_invariant` / `timeEvolution_well_defined` — the evolution preserves the radical, hence
  **descends to the physical space** `𝔄/𝔑`.  This is what makes the Hamiltonian an operator on
  `ℋ` rather than on the unquotient algebra.

`OSReconstruction.HilbertSpace` takes this the rest of the way: it assembles `ℋ` as the
completion of `𝔄/𝔑` (`Hphys`) and extends `T(τ)` to a continuous linear map on `ℋ` with
`‖T(τ)‖ ≤ 1` (`physEvolCompletion`, `norm_physEvolCompletion_le`).

## Boundary (stated plainly)

The plan's named results `emergent_hamiltonian_selfAdjoint` and
`emergent_hamiltonian_nonnegative` are **not** claimed here, and cannot be in this development:
identifying the generator `H` with `−log P` and proving `H = H*`, `H ≥ 0` requires (i) a
strongly continuous contraction semigroup on a *complete* Hilbert space, (ii) the spectral theorem
for unbounded self-adjoint operators, and (iii) Stone/Lumer–Phillips theory.  None of (ii)–(iii)
exists in Mathlib, and the plan itself lists the spectral theorem as a prerequisite.  What *is*
proved is the part that does not need them: the semigroup law, its contractivity in the OS norm
(which is the positivity of the transfer matrix, i.e. the physical origin of `H ≥ 0`), its descent
to the quotient, its contractive extension to `ℋ`, and — in `OSReconstruction.HilbertSpace` —
**strong continuity at `0`** (`tendsto_physEvolCompletion`), derived from continuity of the
two-point function rather than assumed of the `TimeTranslation`.  So (i) is supplied once the OS
axiom of time-translation continuity is, and what remains of the plan's two named results is the
generator step (ii)–(iii): the difference quotients `(P(τ)z − z)/τ` and the integral representation
that makes their limit closed.  The remaining inputs are carried as explicit hypotheses (`hinv`,
the non-increase of the OS form; `hcont`, continuity of `τ ↦ ⟨T(τ)F,F⟩`), never as silent
assumptions.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity

noncomputable section

/-- A one-parameter group of time translations acting on observables. -/
structure TimeTranslation where
  toFun : ℝ → (Observable →ₗ[ℝ] Observable)
  map_zero : toFun 0 = LinearMap.id
  map_add : ∀ s t : ℝ, toFun (s + t) = (toFun s).comp (toFun t)

instance : CoeFun TimeTranslation (fun _ => ℝ → Observable →ₗ[ℝ] Observable) :=
  ⟨TimeTranslation.toFun⟩

/-- **The semigroup law**: `T(s+t) = T(s) ∘ T(t)`. -/
theorem timeTranslation_semigroup (T : TimeTranslation) (s t : ℝ) (F : Observable) :
    T (s + t) F = T s (T t F) := by
  rw [show T (s + t) = (T s).comp (T t) from T.map_add s t]
  rfl

/-- `T(0)` is the identity. -/
theorem timeTranslation_zero (T : TimeTranslation) (F : Observable) : T 0 F = F := by
  rw [show T 0 = LinearMap.id from T.map_zero]
  rfl

/-- **Contractivity of the evolution in the OS seminorm**: if the evolution does not increase
the OS form on the diagonal, then the OS norm is non-increasing along the evolution. -/
theorem osNorm_evolution_contractive (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin ω (T τ F) (T τ F) ≤ osBilin ω F F)
    (τ : ℝ) (F : Observable) :
    osNorm ω (T τ F) ≤ osNorm ω F := by
  simpa [osNorm] using Real.sqrt_le_sqrt (hinv τ F)

/-- Antitonicity in the evolution parameter: an infinitesimal further evolution cannot increase
the OS norm (`T(s+t) = T(s) ∘ T(t)`, so this is contractivity applied at the later time). -/
theorem osNorm_evolution_antitone (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin ω (T τ F) (T τ F) ≤ osBilin ω F F)
    (σ τ : ℝ) (F : Observable) :
    osNorm ω (T (σ + τ) F) ≤ osNorm ω (T τ F) := by
  rw [timeTranslation_semigroup]
  simpa [osNorm] using Real.sqrt_le_sqrt (hinv σ (T τ F))

/-- The evolution preserves the radical. -/
theorem radical_invariant (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin ω (T τ F) (T τ F) ≤ osBilin ω F F)
    {F : Observable} (hF : F ∈ Radical ω) (τ : ℝ) : T τ F ∈ Radical ω := by
  have h0 : osBilin ω F F = 0 := by
    have := hF F
    exact this
  refine mem_radical_of_self_eq_zero ω hRP ?_
  have hle := hinv τ F
  rw [h0] at hle
  exact le_antisymm hle (osForm_self_nonneg ω hRP _)

/-- **The evolution descends to the physical space** `𝔄/𝔑`: two observables representing the
same class evolve to observables representing the same class. -/
theorem timeEvolution_well_defined (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin ω (T τ F) (T τ F) ≤ osBilin ω F F)
    {F F' : Observable} (h : F - F' ∈ Radical ω) (τ : ℝ) :
    T τ F - T τ F' ∈ Radical ω := by
  have hmap : T τ F - T τ F' = T τ (F - F') := by
    rw [map_sub]
  rw [hmap]
  exact radical_invariant ω hRP T hinv h τ

end

end BookProof.OSReconstruction
