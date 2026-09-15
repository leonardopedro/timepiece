import Mathlib
import BookProof.ChapterGhostField
import BookProof.ChapterFreeFieldConstraint
import BookProof.ChapterContinuityUnitary
import BookProof.ChapterU
import BookProof.ChapterNavierStokesFlow.Part1

/-!
# Chapter "Free field parametrization … Navier–Stokes": the truncated
Navier–Stokes Hamiltonian generates a **complete flow**

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier–Stokes equations"*, §*"Free field parametrization in
Navier–Stokes equations"* (`book.tex` ~4133–4216).  The correspondence between
the book's text and the theorems proved here is:

* ~4151–4173, degrees of freedom, derivatives treated as fields:
  `fieldTaylor`, `field_evaluates_to_value`;
* ~4163–4170, the canonical commutation relations of the modes: `ccr_field`,
  `derivativeField_momentum`, `secondDerivativeField_momentum`;
* ~4184–4189, the Navier–Stokes Hamiltonian: `nsHamiltonian`,
  `nsHamiltonian_hermitian`;
* ~4199, "polynomial of low degree in the fields":
  `nsHamiltonian_isPolynomial` (words of length ≤ 3);
* ~4191–4197, the divergence constraint and its resolution:
  `nsDivergenceConstraint_resolution`, `nsBrst_nilpotent`;
* ~4199–4208, self-adjointness: `nsHamiltonian_hasZeroDeficiency`,
  `nsHamiltonian_hasZeroDeficiencyOn` (**truncation only**) and the conditional
  `ns_esa_of_farisLavine`, `ns_esa_of_farisLavine_dense`;
* ~4210–4216, existence and uniqueness of the solution: `nsFlow_group`,
  `nsFlow_groupOnEvolved`, `nsFlow_noBlowup` (**truncation only**); the
  differential form — the evolution equation `ψ̇ = i H_N ψ` and the unique
  solvability of its Cauchy problem — is in the companion module
  `BookProof.ChapterNavierStokesCauchy`.

## What is proved

Let `H_N` be the Navier–Stokes Hamiltonian **restricted to a finite truncation**
(finitely many field modes `u_k`, `u_{k,j}`, `u_{k,jj}`, each realized by a
Hermitian matrix on a finite-dimensional state space, the modes commuting with
one another as multiplication operators do).  Then

* `nsHamiltonian_hermitian` — `H_Nᴴ = H_N`;
* `nsHamiltonian_isPolynomial` — every term of `H_N` is a word of length at most
  three in the generators `u_k`, `π_i` (the "low degree in the fields"
  hypothesis of `book.tex` ~4199);
* `nsFlow_zero`, `nsFlow_group`, `nsFlow_unitary` — `U(t) = e^{i t H_N}` is a
  one-parameter **unitary group**, defined for *every* real time: the flow of the
  truncation is complete;
* `nsFlow_norm_preserving`, `nsFlow_noBlowup` — the flow preserves the `ℓ²` mass
  and every coefficient of the evolved state stays bounded by the initial mass,
  uniformly in `t`: **no finite-time singularity on the truncation**;
* `nsHamiltonian_hasZeroDeficiency` — the truncated Hamiltonian has vanishing
  deficiency: `H_N ψ = ± i ψ` forces `ψ = 0`.

Alongside the truncation the file records the algebraic core of the surrounding
construction: the derivatives-as-fields Taylor operator (`Part A`), the
Lagrangian change of variables and the volume-preservation constraint
(`Part B`), the BRST ghost charge (`Part E`), and the Faris–Lavine framing of
the continuum essential-self-adjointness question (`Part G`).

## What is *not* claimed

The essential self-adjointness of the **untruncated continuum** operator
`H = ∫ a†(πⁱ(u_j u_{i,j} − ν u_{i,jj}) + h.c.) a`, and with it global existence
and uniqueness for the Navier–Stokes equations, is **not** claimed anywhere in
this file.  The project's own ODE chapter is the standing warning: for `ẋ = x²`
the Hamiltonian `x²p̂ − i x̂` is a polynomial of degree 3 whose classical flow
`x₀/(1 − t x₀)` is incomplete, so a low-degree polynomial Hamiltonian need *not*
be essentially self-adjoint.  Accordingly:

* the degree bound `nsHamiltonian_isPolynomial` is recorded as a **symmetry**
  statement (a well-defined polynomial operator), never as self-adjointness;
* `HasZeroDeficiency` is the deficiency-index-`(0,0)` condition *for the operator
  itself*; on a finite-dimensional space (where the operator is bounded and
  everywhere defined) this is exactly essential self-adjointness, and it is
  proved for the truncation.  For an unbounded operator the deficiency spaces
  are those of the *adjoint*, so the finite statement does not transfer;
* `ns_esa_of_farisLavine` and its densely-defined form
  `ns_esa_of_farisLavine_dense` are **conditional**: the Faris–Lavine commutator
  criterion (Faris–Lavine 1974, Corollary 1.1; Reed–Simon Vol. II Theorem X.28)
  enters as a *named hypothesis*, never as an `axiom`, exactly as Crouzeix's
  inequality does in `BookProof.ChapterH4`.  Verifying its two analytic
  inequalities for the continuum operator is a research target, not a result of
  this file.  The hypothesis is carried in its honest form: symmetry of the
  operator is part of it, since without symmetry the criterion is contradictory
  and the conditional theorem would be vacuous
  (`farisLavine_without_symmetry_forces_trivial`), while with symmetry it is
  satisfiable (`farisLavine_holds_of_everywhereDefined`) — indeed automatic for
  everywhere-defined operators, which is precisely why the analytic content sits
  in the dense-domain predicate `HasZeroDeficiencyOn`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

namespace BookProof.NavierStokesFlow

variable {n : ℕ} (d : NSTruncation n)
/-! ## Part D — Complete flow on the truncation (no singularities) -/

/-- **D.1** The flow of the truncated Navier–Stokes Hamiltonian,
`U(t) = e^{i t H_N}`. -/
noncomputable def nsFlowUnitary (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • nsHamiltonian d)

/-- **D.2 (headline)** Every `U(t)` is **unitary**. -/
theorem nsFlow_unitary (t : ℝ) : (nsFlowUnitary d t)ᴴ * nsFlowUnitary d t = 1 :=
  BookProof.ChapterContinuityUnitary.exp_smul_I_unitary _ (nsHamiltonian_hermitian d) t

/-- **D.4** `U(0) = 1`. -/
theorem nsFlow_zero : nsFlowUnitary d 0 = 1 := by
  simp [nsFlowUnitary, NormedSpace.exp_zero]

/-- **D.3 (headline)** *The flow is complete*: `U` is a one-parameter group,
`U(s + t) = U(s) U(t)`, defined for **every** real time — there is no finite time
horizon beyond which the truncated evolution ceases to exist. -/
theorem nsFlow_group (s t : ℝ) :
    nsFlowUnitary d (s + t) = nsFlowUnitary d s * nsFlowUnitary d t := by
  have hcomm : Commute (((s : ℂ) * Complex.I) • nsHamiltonian d)
      (((t : ℂ) * Complex.I) • nsHamiltonian d) := by
    simp [Commute, SemiconjBy, smul_smul, mul_comm]
  have hsum : (((s + t : ℝ) : ℂ) * Complex.I) • nsHamiltonian d
      = ((s : ℂ) * Complex.I) • nsHamiltonian d
        + ((t : ℂ) * Complex.I) • nsHamiltonian d := by
    rw [← add_smul]
    push_cast
    ring_nf
  rw [nsFlowUnitary, hsum, Matrix.exp_add_of_commute _ _ hcomm]
  rfl

/-- **D.5** The flow is **norm preserving**: `‖ψ(t)‖ = ‖ψ(0)‖`. -/
theorem nsFlow_norm_preserving (t : ℝ) (psi : Fin n → ℂ) :
    ∑ a, ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2 = ∑ a, ‖psi a‖ ^ 2 :=
  BookProof.ChapterContinuityUnitary.unitary_preserves_normSq _ (nsFlow_unitary d t) psi

/-- **D.6 (headline)** *No finite-time singularity on the truncation*: at every
time `t` — however large — each coefficient of the evolved state is bounded by
the (conserved) initial mass. -/
theorem nsFlow_noBlowup (t : ℝ) (psi : Fin n → ℂ) (k : Fin n) :
    ‖(nsFlowUnitary d t *ᵥ psi) k‖ ^ 2 ≤ ∑ a, ‖psi a‖ ^ 2 := by
  rw [← nsFlow_norm_preserving d t psi]
  exact Finset.single_le_sum (f := fun a => ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2)
    (fun a _ => by positivity) (Finset.mem_univ k)

/-- **D.7** The complete-flow statement on states: evolving by `t₂` and then by
`t₁` is evolving by `t₁ + t₂`. -/
theorem nsFlow_groupOnEvolved (t₁ t₂ : ℝ) (psi : Fin n → ℂ) :
    nsFlowUnitary d t₁ *ᵥ (nsFlowUnitary d t₂ *ᵥ psi) = nsFlowUnitary d (t₁ + t₂) *ᵥ psi := by
  rw [nsFlow_group, Matrix.mulVec_mulVec]

/-! ## Part E — The divergence constraint and the BRST charge -/

/-- The divergence field `u_{j,j}` of the truncation. -/
noncomputable def nsDivergence : Matrix (Fin n) (Fin n) ℂ := ∑ j : Fin 3, nsGradVelocity d j j

/-- **E.1** The truncated **BRST charge** `Ω = u_{j,j} ⊗ ψ†` on the tensor
product of the bosonic state space with the two-dimensional ghost factor. -/
noncomputable def nsBrstCharge : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  nsDivergence d ⊗ₖ BookProof.GhostField.psiDag

/-- **E.1 (headline)** *The BRST charge is nilpotent*, `Ω² = 0` — the
first-class property that makes the BRST cohomology of the divergence constraint
well defined.  It reduces to the nilpotency `ψ†² = 0` of the ghost creation
operator. -/
theorem nsBrst_nilpotent : nsBrstCharge d * nsBrstCharge d = 0 := by
  rw [nsBrstCharge, ← Matrix.mul_kronecker_mul, BookProof.GhostField.psiDag_sq,
    Matrix.kronecker_zero]

/-- **E.3** The adjoint of the BRST charge is `u_{j,j} ⊗ ψ`: the charge itself is
*not* Hermitian (the ghost factor is a creation operator), which is why the
physical space is `ker Ω / im Ω` rather than an eigenspace of `Ω`. -/
theorem nsBrst_adjoint : (nsBrstCharge d)ᴴ = nsDivergence d ⊗ₖ BookProof.GhostField.psi := by
  have hD : (nsDivergence d)ᴴ = nsDivergence d := by
    simp only [nsDivergence, Matrix.conjTranspose_sum, nsGradVelocity, d.u_herm]
  have hp : (BookProof.GhostField.psiDag)ᴴ = BookProof.GhostField.psi := by
    rw [BookProof.GhostField.psiDag_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [nsBrstCharge, Matrix.conjTranspose_kronecker, hD, hp]

/-- **E.2** *The divergence constraint is resolved by the book's substitution*
(`book.tex` ~4191–4197): setting `u_{3,3} = −(u_{1,1} + u_{2,2})` solves
`∂_j u_j = u_{1,1} + u_{2,2} + u_{3,3} = 0`. -/
theorem nsDivergenceConstraint_resolution (u11 u22 u33 : ℝ) (h : u33 = -(u11 + u22)) :
    u11 + u22 + u33 = 0 := by
  rw [h]; ring

/-- The operator form of the same resolution. -/
theorem nsDivergenceConstraint_resolution_matrix (U11 U22 U33 : Matrix (Fin n) (Fin n) ℂ)
    (h : U33 = -(U11 + U22)) : U11 + U22 + U33 = 0 := by
  rw [h]; abel

/-! ## Part G — Deficiency, second quantization, and the Faris–Lavine criterion -/

section Deficiency

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Vanishing deficiency** for an operator on a complex inner-product space:
`H ψ = ± i ψ` forces `ψ = 0`, i.e. the deficiency indices are `(0, 0)`.

*Scope.* On a finite-dimensional space (a bounded, everywhere-defined operator)
this is exactly essential self-adjointness.  For an unbounded operator the
deficiency spaces are those of the **adjoint** on its own domain, so this
predicate is the finite/bounded shadow of the analytic notion. -/
def HasZeroDeficiency (H : F →ₗ[ℂ] F) : Prop :=
  (∀ v : F, H v = Complex.I • v → v = 0) ∧ (∀ v : F, H v = -(Complex.I • v) → v = 0)

/-- A symmetric operator has vanishing deficiency in the above sense: the
expectation `⟪v, Hv⟫` is real, while `⟪v, ± i v⟫` is purely imaginary. -/
theorem symmetric_hasZeroDeficiency (H : F →ₗ[ℂ] F) (hsym : H.IsSymmetric) :
    HasZeroDeficiency H := by
  constructor
  · intro v hv
    have h := hsym v v
    rw [hv, inner_smul_left, inner_smul_right] at h
    have h2 : (2 * Complex.I) * (inner ℂ v v : ℂ) = 0 := by
      simp only [Complex.conj_I] at h
      linear_combination -h
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero]))
  · intro v hv
    have h := hsym v v
    rw [hv, inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right] at h
    have h2 : (2 * Complex.I) * (inner ℂ v v : ℂ) = 0 := by
      simp only [Complex.conj_I] at h
      linear_combination h
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero]))

/-- **G.4** *The Faris–Lavine criterion, as a conditional theorem.*

`farisLavine` is the **named external input** (Faris & Lavine 1974, Corollary
1.1; Reed & Simon Vol. II, Theorem X.28 — Sears' theorem in the
quadratic-growth case): an operator relatively bounded by a comparison operator
`N`, with a form-commutator bound `|⟪ψ, [H, N] ψ⟫| ≤ c₂ |⟪ψ, N ψ⟫|`, is
essentially self-adjoint.  It enters as a hypothesis, **never as an `axiom`**,
exactly as Crouzeix's inequality does in `BookProof.ChapterH4`.

Given the criterion and the two Faris–Lavine inequalities for the pair `(H, N)`
— `H` the transformed (Lagrangian) Navier–Stokes operator of Part B, `N` the
outer number operator of `G.3` — the operator has vanishing deficiency.  Neither
inequality is proved here for the continuum operator: that is the research
target recorded in the module docstring. -/
theorem ns_esa_of_farisLavine (H N : F →ₗ[ℂ] F) (c₁ c₂ : ℝ) (hsym : H.IsSymmetric)
    (farisLavine : ∀ (H' N' : F →ₗ[ℂ] F) (a b : ℝ), H'.IsSymmetric →
      (∀ v : F, ‖H' v‖ ≤ a * ‖N' v‖) →
      (∀ v : F, ‖(inner ℂ v (H' (N' v) - N' (H' v)) : ℂ)‖ ≤ b * ‖(inner ℂ v (N' v) : ℂ)‖) →
      HasZeroDeficiency H')
    (hHbound : ∀ v : F, ‖H v‖ ≤ c₁ * ‖N v‖)
    (hCommutator : ∀ v : F,
      ‖(inner ℂ v (H (N v) - N (H v)) : ℂ)‖ ≤ c₂ * ‖(inner ℂ v (N v) : ℂ)‖) :
    HasZeroDeficiency H :=
  farisLavine H N c₁ c₂ hsym hHbound hCommutator

/-- *Why the symmetry hypothesis of `ns_esa_of_farisLavine` cannot be dropped.*
Without it the quantified criterion is **contradictory** on every nontrivial
space: `H' = i·1` and `N' = 1` satisfy both inequalities with `a = b = 1` while
`H' v = i v` for every `v`, so the criterion would force `v = 0`.  A conditional
theorem resting on that hypothesis would be vacuous, which is why the symmetry
of `H'` — part of the actual Faris–Lavine statement — is carried explicitly. -/
theorem farisLavine_without_symmetry_forces_trivial
    (crit : ∀ (H' N' : F →ₗ[ℂ] F) (a b : ℝ),
      (∀ v : F, ‖H' v‖ ≤ a * ‖N' v‖) →
      (∀ v : F, ‖(inner ℂ v (H' (N' v) - N' (H' v)) : ℂ)‖ ≤ b * ‖(inner ℂ v (N' v) : ℂ)‖) →
      HasZeroDeficiency H') (v : F) : v = 0 :=
  (crit (Complex.I • LinearMap.id) LinearMap.id 1 1 (fun v => by simp [norm_smul])
    (fun v => by simp)).1 v (by simp)

/-- *The criterion assumed by `ns_esa_of_farisLavine` is satisfiable* — hence
that theorem is **not vacuous**.  For operators defined on the whole space the
criterion is in fact automatic: symmetry alone already gives vanishing
deficiency (`symmetric_hasZeroDeficiency`), and neither Faris–Lavine inequality
is used.  The analytic content of Faris–Lavine therefore lives entirely in the
*densely defined, unbounded* setting — the predicate `HasZeroDeficiencyOn`
below, where the deficiency spaces are those of the **adjoint** and symmetry no
longer suffices.  This file proves the everywhere-defined case only. -/
theorem farisLavine_holds_of_everywhereDefined :
    ∀ (H' N' : F →ₗ[ℂ] F) (a b : ℝ), H'.IsSymmetric →
      (∀ v : F, ‖H' v‖ ≤ a * ‖N' v‖) →
      (∀ v : F, ‖(inner ℂ v (H' (N' v) - N' (H' v)) : ℂ)‖ ≤ b * ‖(inner ℂ v (N' v) : ℂ)‖) →
      HasZeroDeficiency H' :=
  fun H' _ _ _ hsym _ _ => symmetric_hasZeroDeficiency H' hsym

/-! ### Deficiency of the adjoint on a dense domain

`HasZeroDeficiency` above is the deficiency condition *for the operator itself*,
which is the right notion exactly when the operator is everywhere defined.  The
analytic notion — the one Faris–Lavine is about — asks the deficiency spaces of
the **adjoint** of an operator given on a dense domain `D` to vanish: no `w` may
satisfy `⟪H v, w⟫ = ⟪v, ± i w⟫` for all `v ∈ D` unless `w = 0`.  For `D = ⊤` the
two notions agree (`hasZeroDeficiencyOn_top_of_symmetric`); for a proper dense
domain the second is strictly stronger, and it is *not* claimed here for the
continuum Navier–Stokes operator. -/

/-- Vanishing deficiency of the **adjoint** of an operator `H` defined on the
domain `D`: if `w` satisfies `⟪H v, w⟫ = ⟪v, ± i w⟫` for every `v ∈ D` — that
is, if `w` lies in a deficiency space of `H∗` — then `w = 0`. -/
def HasZeroDeficiencyOn (D : Submodule ℂ F) (H : D →ₗ[ℂ] D) : Prop :=
  (∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (Complex.I • w)) → w = 0) ∧
    (∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (-(Complex.I • w))) → w = 0)

/-- An everywhere-defined operator, viewed as an operator on the domain `⊤`. -/
noncomputable def restrictToTop (H : F →ₗ[ℂ] F) :
    (⊤ : Submodule ℂ F) →ₗ[ℂ] (⊤ : Submodule ℂ F) :=
  LinearMap.codRestrict ⊤ (H.comp (⊤ : Submodule ℂ F).subtype) fun _ => trivial

@[simp] theorem restrictToTop_apply (H : F →ₗ[ℂ] F) (v : (⊤ : Submodule ℂ F)) :
    (restrictToTop H v : F) = H (v : F) := rfl

/-- On the **full** domain a symmetric operator already has vanishing adjoint
deficiency: testing the defining identity against `w` itself makes `⟪H w, w⟫`
both real (by symmetry) and purely imaginary, so `w = 0`.  This is the
everywhere-defined case of essential self-adjointness — and, for a proper dense
domain, exactly the step that fails without an analytic criterion such as
Faris–Lavine. -/
theorem hasZeroDeficiencyOn_top_of_symmetric (H : F →ₗ[ℂ] F) (hsym : H.IsSymmetric) :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ F) (restrictToTop H) := by
  constructor
  · intro w hw
    have h := hw ⟨w, trivial⟩
    simp only [restrictToTop_apply, inner_smul_right] at h
    have hs : (inner ℂ (H w) w : ℂ) = inner ℂ w (H w) := hsym w w
    have hc : (inner ℂ w (H w) : ℂ) = starRingEnd ℂ (inner ℂ (H w) w) :=
      (inner_conj_symm _ _).symm
    have h2 : (2 * Complex.I) * (inner ℂ w w : ℂ) = 0 := by
      have hcc : starRingEnd ℂ (inner ℂ w w : ℂ) = inner ℂ w w := inner_self_conj _
      rw [h] at hs hc
      rw [hc] at hs
      simp only [map_mul, Complex.conj_I, hcc] at hs
      linear_combination hs
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero]))
  · intro w hw
    have h := hw ⟨w, trivial⟩
    simp only [restrictToTop_apply, inner_neg_right, inner_smul_right] at h
    have hs : (inner ℂ (H w) w : ℂ) = inner ℂ w (H w) := hsym w w
    have hc : (inner ℂ w (H w) : ℂ) = starRingEnd ℂ (inner ℂ (H w) w) :=
      (inner_conj_symm _ _).symm
    have h2 : (2 * Complex.I) * (inner ℂ w w : ℂ) = 0 := by
      have hcc : starRingEnd ℂ (inner ℂ w w : ℂ) = inner ℂ w w := inner_self_conj _
      rw [h] at hs hc
      rw [hc] at hs
      simp only [map_neg, map_mul, Complex.conj_I, hcc] at hs
      linear_combination -hs
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero]))

/-- **G.4 (dense form)** *The Faris–Lavine criterion for a densely defined
operator, as a conditional theorem.*  This is the statement the continuum
Navier–Stokes question actually needs: `H` and the comparison operator `N` live
on a dense domain `D` (the finite-particle vectors), `H` is symmetric there, `H`
is relatively bounded by `N`, and the form commutator `[H, N]` is dominated by
`N`; the conclusion is that the **adjoint** has no deficiency, i.e. `H` is
essentially self-adjoint.

As in the everywhere-defined version the criterion itself is a **named
hypothesis** (Faris & Lavine 1974, Corollary 1.1; Reed & Simon Vol. II, Theorem
X.28), never an `axiom`, and the two analytic inequalities are *not* verified
here for the continuum operator: that is the research target recorded in the
module docstring.  The criterion is consistent — it holds whenever the domain is
the whole space, by `hasZeroDeficiencyOn_top_of_symmetric`. -/
theorem ns_esa_of_farisLavine_dense (D : Submodule ℂ F) (H N : D →ₗ[ℂ] D) (c₁ c₂ : ℝ)
    (farisLavine : ∀ (D' : Submodule ℂ F) (H' N' : D' →ₗ[ℂ] D') (a b : ℝ),
      Dense (D' : Set F) →
      (∀ x y : D', (inner ℂ (H' x : F) (y : F) : ℂ) = inner ℂ (x : F) (H' y : F)) →
      (∀ v : D', ‖(H' v : F)‖ ≤ a * ‖(N' v : F)‖) →
      (∀ v : D', ‖(inner ℂ (v : F) ((H' (N' v) : F) - (N' (H' v) : F)) : ℂ)‖
        ≤ b * ‖(inner ℂ (v : F) (N' v : F) : ℂ)‖) →
      HasZeroDeficiencyOn D' H')
    (hdense : Dense (D : Set F))
    (hsym : ∀ x y : D, (inner ℂ (H x : F) (y : F) : ℂ) = inner ℂ (x : F) (H y : F))
    (hHbound : ∀ v : D, ‖(H v : F)‖ ≤ c₁ * ‖(N v : F)‖)
    (hCommutator : ∀ v : D, ‖(inner ℂ (v : F) ((H (N v) : F) - (N (H v) : F)) : ℂ)‖
      ≤ c₂ * ‖(inner ℂ (v : F) (N v : F) : ℂ)‖) :
    HasZeroDeficiencyOn D H :=
  farisLavine D H N c₁ c₂ hdense hsym hHbound hCommutator

end Deficiency

/-- **G (truncation)** *The truncated Navier–Stokes Hamiltonian has vanishing
deficiency*: `H_N ψ = ± i ψ` forces `ψ = 0`.  On the finite-dimensional
truncation this **is** essential self-adjointness — the honest, provable core of
`book.tex` ~4199–4208.  Nothing is claimed here about the continuum operator. -/
theorem nsHamiltonian_hasZeroDeficiency :
    HasZeroDeficiency (Matrix.toEuclideanLin (nsHamiltonian d)) :=
  symmetric_hasZeroDeficiency _
    (Matrix.isHermitian_iff_isSymmetric.mp (nsHamiltonian_hermitian d))

/-- **G (truncation, adjoint form)** The same statement for the deficiency
spaces of the **adjoint**: no state `w` satisfies `⟪H_N v, w⟫ = ⟪v, ± i w⟫` for
all `v` except `w = 0`.  On the truncation the domain is the whole space, so
this is again essential self-adjointness; for a proper dense domain — the
continuum case — the corresponding statement is *not* proved here. -/
theorem nsHamiltonian_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
      (restrictToTop (Matrix.toEuclideanLin (nsHamiltonian d))) :=
  hasZeroDeficiencyOn_top_of_symmetric _
    (Matrix.isHermitian_iff_isSymmetric.mp (nsHamiltonian_hermitian d))

/-- **G.1** *The Navier–Stokes Hilbert space is a Fock space over a Fock space.*
The algebraic content is the exponential law `Sym(M × N) ≅ Sym M ⊗ Sym N`
(`BookProof.ChapterU.prodEquiv`): the tensor product of two Fock spaces is again
a Fock space, so the outer (trajectory-indexed) quantization of `nsSecondQuant`
below stays inside the same category and no infinite-dimensional tensor product
is needed. -/
noncomputable def nsFockOfFock (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    SymmetricAlgebra R (M × N) ≃ₐ[R] (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N) :=
  BookProof.ChapterU.prodEquiv R M N

/-- **G.1/G.2** The second-quantized ("Fock of a Fock") form of an operator: with
outer ladder operators `A_k` and single-particle kernel `h`,
`Ĥ = ∑_{k,l} h_{kl} A†_k A_l`. -/
noncomputable def nsSecondQuant {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ k : Fin m, ∑ l : Fin m, h k l • ((A k)ᴴ * A l)

/-- The outer generators: `inl k` is the creation operator `A†_k`, `inr l` the
annihilation operator `A_l`. -/
def nsOuterGen {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    Fin m ⊕ Fin m → Matrix (Fin n) (Fin n) ℂ :=
  Sum.elim (fun k => (A k)ᴴ) A

/-- **G.2 (headline)** *The second-quantized operator is at most **quadratic** in
the outer ladder operators*: it is a finite linear combination of the words
`[A†_k, A_l]`, each of length `2`.  This is the Fock-of-Fock shadow of the
degree bound `nsHamiltonian_isPolynomial`, and it is the structure the
quadratic-growth hypothesis of Faris–Lavine/Sears needs. -/
theorem ns_outer_degree_le_two {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) :
    nsSecondQuant A h
        = ∑ a : Fin m × Fin m,
            h a.1 a.2 • (([Sum.inl a.1, Sum.inr a.2].map (nsOuterGen A)).prod)
      ∧ ∀ a : Fin m × Fin m, ([Sum.inl a.1, Sum.inr a.2] : List (Fin m ⊕ Fin m)).length ≤ 2 := by
  refine ⟨?_, fun a => by simp⟩
  simp [nsSecondQuant, nsOuterGen, Fintype.sum_prod_type]

/-- **G.3** The **comparison operator** of the outer Fock layer: the number
operator `N = ∑_k A†_k A_k`, the second-quantized `∫ 𝒩X A†[X] A[X]`. -/
noncomputable def nsNumberOp {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := ∑ k : Fin m, (A k)ᴴ * A k

/-- **G.3** The comparison operator is the second quantization of the identity
kernel. -/
theorem nsNumberOp_eq_secondQuant {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    nsNumberOp A = nsSecondQuant A 1 := by
  simp [nsNumberOp, nsSecondQuant, Matrix.one_apply]

/-- **G.3** The comparison operator is positive semidefinite — the positivity the
Faris–Lavine relative bound is measured against. -/
theorem nsNumberOp_posSemidef {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (nsNumberOp A).PosSemidef := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro k _
  exact Matrix.posSemidef_conjTranspose_mul_self (A k)

end BookProof.NavierStokesFlow
