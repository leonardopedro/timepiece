import BookProof.ChapterGraphCoreTransfer
import BookProof.ChapterEsaClosureCore

/-!
# A self-adjoint operator is essentially self-adjoint on every graph core

`CONSOLIDATED_PLAN.md`, §D6b and the 2026-09-21 core-transfer wave, leaves one obligation
for the comparison operator `N` of the Faris–Lavine route: **obligation (i)**, that `N` be
essentially self-adjoint *on the core actually chosen*, not merely self-adjoint on its own
(Friedrichs) domain.  This chapter supplies the general instrument that discharges it.

Two steps, both elementary once the core-transfer principle of
`BookProof.ChapterGraphCoreTransfer` is available.

* `deficiencyTrivialAt_dom_of_isSelfAdjointExtension` /
  `essentiallySelfAdjointOn_dom_of_isSelfAdjointExtension` — a **self-adjoint operator is
  essentially self-adjoint on its own domain**: if `w` satisfies the deficiency equation at
  a non-real `z`, the self-adjointness clause puts `w` in the domain with `A w = z • w`, and
  symmetry then forces `(z - conj z)⟪w, w⟫ = 0`, hence `w = 0`.
* `essentiallySelfAdjointOn_of_graphCore_selfAdjoint` — combining this with
  `essentiallySelfAdjointOn_of_graphCore`: a self-adjoint operator restricted to **any**
  graph core of its domain is essentially self-adjoint there.

The second statement is exactly obligation (i) in general form: it turns "`N` is the
Friedrichs extension and `C₀` is dense in its graph norm" — both of which the route
chapters already prove — into "`N` is essentially self-adjoint on `C₀`".

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SelfAdjointCoreEsa

open BookProof.FarisLavine BookProof.GraphCore BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **A self-adjoint operator has trivial deficiency at every non-real point, on its own
domain.**  The deficiency equation at `z` says that `w` behaves like a domain vector with
image `z • w`; self-adjointness then makes it one, and symmetry of `A` forces
`(z - conj z)⟪w, w⟫ = 0`. -/
theorem deficiencyTrivialAt_dom_of_isSelfAdjointExtension {D Dom : Submodule ℂ F}
    {H : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsSelfAdjointExtension H A) {z : ℂ}
    (hz : z.im ≠ 0) : DeficiencyTrivialAt Dom A z := by
  intro w hw
  obtain ⟨hmem, hAw⟩ := hA.2.2 w (z • w) fun v => by rw [hw v, inner_smul_right]
  have hsym := hA.2.1 ⟨w, hmem⟩ ⟨w, hmem⟩
  rw [hAw] at hsym
  have hL : (inner ℂ (z • w) w : ℂ) = (starRingEnd ℂ) z * inner ℂ w w := by
    rw [inner_smul_left]
  have hR : (inner ℂ w (z • w) : ℂ) = z * inner ℂ w w := by rw [inner_smul_right]
  rw [hL, hR] at hsym
  have hzz : ((starRingEnd ℂ) z - z) * (inner ℂ w w : ℂ) = 0 := by
    rw [sub_mul, hsym]; ring
  have hne : ((starRingEnd ℂ) z - z) ≠ 0 := by
    intro h
    apply hz
    have him : ((starRingEnd ℂ) z - z).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.conj_im] at him
    linarith
  exact inner_self_eq_zero.mp (by
    rcases mul_eq_zero.mp hzz with h | h
    · exact absurd h hne
    · exact h)

/-- **A self-adjoint operator is essentially self-adjoint on its own domain.** -/
theorem essentiallySelfAdjointOn_dom_of_isSelfAdjointExtension {D Dom : Submodule ℂ F}
    {H : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsSelfAdjointExtension H A) :
    EssentiallySelfAdjointOn Dom A :=
  ⟨deficiencyTrivialAt_dom_of_isSelfAdjointExtension hA (by simp),
    deficiencyTrivialAt_dom_of_isSelfAdjointExtension hA (by simp)⟩

/-- **Obligation (i), in general form.**  A self-adjoint operator is essentially
self-adjoint on every subspace of its domain that is dense in the graph norm. -/
theorem essentiallySelfAdjointOn_of_graphCore_selfAdjoint {D Dom D₁ : Submodule ℂ F}
    {H : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsSelfAdjointExtension H A)
    (hle : D₁ ≤ Dom) (hcore : IsGraphCore D₁ A) :
    EssentiallySelfAdjointOn D₁ (restrictOp A hle) :=
  essentiallySelfAdjointOn_of_graphCore A hle hcore
    (essentiallySelfAdjointOn_dom_of_isSelfAdjointExtension hA)

end BookProof.SelfAdjointCoreEsa
