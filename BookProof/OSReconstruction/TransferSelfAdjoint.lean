import Mathlib
import BookProof.OSReconstruction.Generator

/-!
# Self-adjoint transfer operators force a trivial evolution

The corpus assumes contractivity of the Euclidean evolution in *both* time directions
(`hinv : ∀ τ, osBilin ω (T τ F) (T τ F) ≤ osBilin ω F F`).  Together with the group law this
makes `P(τ)` an isometry of `ℋ` (`norm_physEvolCompletion_eq`, the `ℋ`-level form of
`osBilin_evol_self`).  The transfer operator is therefore *unitary*, not merely contractive.

That has a consequence which the earlier chapters leave implicit: a self-adjoint isometry is an
**involution** (`comp_self_eq_one_of_isometry_isSelfAdjoint`), and an involutive one-parameter
family is trivial, because `P(τ) = P(τ/2) P(τ/2) = 1`.  Hence

* `physEvolCompletion_eq_one` — if every `P(τ)` is self-adjoint, then `P(τ) = 1` for **every** `τ`;
* `diffQuotGroup_eq_zero_of_selfAdjoint`, `hasGen_of_selfAdjoint` — the difference quotient vanishes
  identically, so every vector is in the domain;
* `genDomain_eq_top_of_selfAdjoint`, `generator_apply_eq_zero_of_selfAdjoint` — the generator is
  the zero operator (with domain all of `ℋ`).

So in this framework `P(τ) = e^{−τH}` with a self-adjoint `H` *is* a theorem, but only with
`H = 0`: the identity `P(τ) = e^{−τ·0}`.  The hypothesis `∀ τ, IsSelfAdjoint (P τ)` used by
`generator_isSymmetric` is satisfiable only by the trivial evolution, and the symmetric operator it
produces is `0`.  In particular the Källén–Lehmann multiplication model of
`OSReconstruction.KallenLehmannModel`, which asks for `P(τ)` to act as multiplication by
`e^{−τf}` on `L²(ν)`, is consistent with the corpus's hypotheses only when `f = 0` almost
everywhere.

## Why, and what the repair is

The physical input is wrong for negative Euclidean time: the transfer matrix of Osterwalder–Schrader
reconstruction is `e^{−τH}` for `τ ≥ 0`, a *contraction*, and its continuation to `τ < 0` is
`e^{τH}`, which is unbounded, not a contraction.  Contractivity at `−τ` is what creates the
isometry, and it fails for every nontrivial `H`.  The non-degenerate statement therefore needs the
semi-group hypothesis (contractivity for `τ ≥ 0` only, so `P(τ)` is not unitary), and there
self-adjointness of the transfer operator is the *positivity* of `e^{−τH}`, obtained from the
Friedrichs/Faris–Lavine construction rather than from Stone's theorem for a unitary group.

None of this weakens the Hamiltonian.  In real time the 4d Hamiltonian is self-adjoint --
positivity plus essential self-adjointness (Faris–Lavine/Friedrichs), unitary flow by Stone --
and `e^{−τH}` for `τ ≥ 0` is a *positive self-adjoint contraction* whose generator `A = −H` is
self-adjoint and dissipative because `H ≥ 0`.  The degeneracy above needs the negative-time half
of the family, where `e^{−τH}` continues to the unbounded `e^{τH}`; `H` itself is untouched.  The
Hamiltonian side is realized in this corpus on the nested Fock space, its sector operators being
inner Hamiltonians on the inner Fock space sandwiched between outer creation on the left and
annihilation on the right (`BookProof.sandwich`,
`BookProof.QgOuterFockOneParticle.secHam_matrix_element`), with essential self-adjointness
`qgOuterFock_esa` / `smFockHam_esa` and flow `exists_stone_flow_of_esa`.  The symmetry theorem
`generator_isSymmetric` survives the change of hypotheses: its proof uses only self-adjointness
of `P(τ)`, never the negative-time contractivity.

## Boundary

Nothing here identifies the abstract `ℋ` with the nested Fock space; it proves that the *stated*
hypotheses cannot carry a nontrivial `e^{−τH}`.  The repair is a change of hypotheses on the OS
side (a transfer semi-group on `τ ≥ 0`), after which `physEvolCompletion` must be rebuilt and the
strong-continuity proof of `HilbertSpace` re-derived from matrix element continuity without the
`−τ` sandwich.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter
open scoped Topology
open RealInnerProductSpace

noncomputable section

/-! ## The general Hilbert-space fact -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A norm-preserving continuous linear map preserves the inner product. -/
theorem inner_map_map_of_norm_map (T : E →L[ℝ] E) (hiso : ∀ x, ‖T x‖ = ‖x‖) (x y : E) :
    ⟪T x, T y⟫ = ⟪x, y⟫ :=
  (⟨(T : E →ₗ[ℝ] E), hiso⟩ : E →ₗᵢ[ℝ] E).inner_map_map x y

/-- **A self-adjoint isometry is an involution**: `T ∘ T = 1`.

Self-adjointness turns `T (T x)` into `T x` tested against `T`, and norm preservation removes the
`T` on the right, so `T (T x)` has the same inner product as `x` against every vector. -/
theorem comp_self_eq_one_of_isometry_isSelfAdjoint (T : E →L[ℝ] E)
    (hiso : ∀ x, ‖T x‖ = ‖x‖) (hsa : IsSelfAdjoint T) : T.comp T = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hinner : ∀ y : E, ⟪T (T x), y⟫ = ⟪x, y⟫ := fun y =>
    (hsa.isSymmetric (T x) y).trans (inner_map_map_of_norm_map T hiso x y)
  have hzero : ⟪T (T x) - x, T (T x) - x⟫ = 0 := by
    rw [inner_sub_left, hinner (T (T x) - x), sub_self]
  have hpoint : T (T x) = x := sub_eq_zero.1 (inner_self_eq_zero.1 hzero)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  exact hpoint

end General

/-! ## The transfer semigroup is isometric -/

/-- **`P(τ)` preserves the norm.**  Contractivity at `τ` and at `−τ`, with the group law returning
`P(−τ)(P(τ)z) = z`, sandwiches `‖P(τ)z‖` between `‖z‖` and itself. -/
theorem norm_physEvolCompletion_eq (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (z : Hphys Λ) : ‖physEvolCompletion Λ T hinv τ z‖ = ‖z‖ := by
  refine le_antisymm (physEvolCompletion_contractive Λ T hinv τ z) ?_
  have hback : physEvolCompletion Λ T hinv (-τ) (physEvolCompletion Λ T hinv τ z) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← physEvolCompletion_add, neg_add_cancel,
      physEvolCompletion_zero, ContinuousLinearMap.id_apply]
  calc ‖z‖ = ‖physEvolCompletion Λ T hinv (-τ) (physEvolCompletion Λ T hinv τ z)‖ := by
        rw [hback]
    _ ≤ ‖physEvolCompletion Λ T hinv τ z‖ := physEvolCompletion_contractive Λ T hinv (-τ) _

/-! ## Self-adjointness forces triviality -/

/-- If every transfer operator is self-adjoint, each one is an involution. -/
theorem physEvolCompletion_comp_self (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ)) (τ : ℝ) :
    (physEvolCompletion Λ T hinv τ).comp (physEvolCompletion Λ T hinv τ) = 1 :=
  comp_self_eq_one_of_isometry_isSelfAdjoint _
    (norm_physEvolCompletion_eq Λ T hinv τ) (hsa τ)

/-- **Self-adjointness of the transfer operators forces the trivial evolution**:
`P(τ) = 1` for every `τ`, since `τ = τ/2 + τ/2` and `P(τ/2)` is an involution. -/
theorem physEvolCompletion_eq_one (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ)) (τ : ℝ) :
    physEvolCompletion Λ T hinv τ = 1 := by
  have hhalf : τ = τ / 2 + τ / 2 := by ring
  rw [hhalf, physEvolCompletion_add]
  exact physEvolCompletion_comp_self Λ T hinv hsa (τ / 2)

/-- The difference quotient vanishes identically under the self-adjointness hypothesis. -/
theorem diffQuotGroup_eq_zero_of_selfAdjoint (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ))
    (τ : ℝ) (z : Hphys Λ) : diffQuotGroup Λ T hinv τ z = 0 := by
  rw [diffQuotGroup, physEvolCompletion_eq_one Λ T hinv hsa τ, ContinuousLinearMap.one_apply,
    sub_self, smul_zero]

/-- Every vector is in the domain of the generator under the self-adjointness hypothesis. -/
theorem hasGen_of_selfAdjoint (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ)) (z : Hphys Λ) :
    HasGen Λ T hinv z :=
  ⟨0, tendsto_const_nhds.congr' (Eventually.of_forall fun τ =>
    (diffQuotGroup_eq_zero_of_selfAdjoint Λ T hinv hsa τ z).symm)⟩

/-- The domain is all of `ℋ`. -/
theorem genDomain_eq_top_of_selfAdjoint (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ)) :
    genDomain Λ T hinv = ⊤ :=
  Submodule.eq_top_iff'.2 fun z => hasGen_of_selfAdjoint Λ T hinv hsa z

/-- **The generator vanishes** under the self-adjointness hypothesis: its value is `0` at every
domain point. -/
theorem generator_apply_eq_zero_of_selfAdjoint (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ))
    (z : (generator Λ T hinv).domain) : generator Λ T hinv z = 0 := by
  refine generator_apply_eq_of_tendsto Λ T hinv z ?_
  refine tendsto_const_nhds.congr' (Eventually.of_forall fun τ => ?_)
  exact (diffQuotGroup_eq_zero_of_selfAdjoint Λ T hinv hsa τ (z : Hphys Λ)).symm

end

end BookProof.OSReconstruction
