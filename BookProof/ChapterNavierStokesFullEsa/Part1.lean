import Mathlib
import BookProof.ChapterNavierStokesEsa
import BookProof.ChapterNavierStokesDeficiency

/-!
# The **full** (untruncated) Navier–Stokes Hamiltonian and its essential
self-adjointness

`BookProof.ChapterNavierStokesFlow` builds the Navier–Stokes Hamiltonian
`H = ∑_i (π_i A_i + A_i π_i)`, `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`, for a
**finite truncation**: the fifteen field modes and the three momenta are
matrices on a finite-dimensional state space.  This module removes the
truncation: the modes and momenta are now (possibly unbounded) operators on a
dense domain `D` of an arbitrary complex inner-product space, and `H` is the
same polynomial expression in them.

## What is proved here

* `NSFullData` — the untruncated data: a dense domain `D`, fifteen symmetric,
  pairwise commuting field modes and three symmetric momenta, all of them
  mapping `D` into `D`, and a viscosity `ν`.  Nothing is finite-dimensional and
  nothing is bounded.
* `NSFullData.hamiltonian_isSymmetricDom` — **the full Hamiltonian is symmetric
  on its domain**, unconditionally.
* `NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow` — **essential
  self-adjointness of the full Hamiltonian from a complete unitary flow**
  (Nelson's route), and `NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors`,
  the eigenvector route.
* `NSFullData.hasZeroDeficiencyOn_of_boundedRealization` — if the full
  Hamiltonian is the restriction of a bounded symmetric operator, it is
  essentially self-adjoint on `D`.
* **A genuinely infinite-dimensional, untruncated instance**: on `ℓ²(ℤ)`, with
  all fifteen modes realized as multiplication by bounded real velocity fields
  and the momenta as the lattice (symmetric-difference) momentum, the full
  Navier–Stokes Hamiltonian is essentially self-adjoint on the **proper** dense
  domain of finitely supported modes: `latticeFull_hasZeroDeficiencyOn`.  The
  operator is not the zero operator (`latticeFullHamiltonianCLM_ne_zero`).
* **An unbounded instance**: on `ℓ²(ℕ)`, with all modes and momenta diagonal
  with (possibly unbounded) real symbols, the full Hamiltonian is essentially
  self-adjoint on the finite-mode domain (`diagFull_hasZeroDeficiencyOn`), and
  for a suitable choice of data it is genuinely unbounded
  (`diagFull_not_bounded`).  So essential self-adjointness of the *full*
  Hamiltonian is not a boundedness phenomenon.
* **Sharpness.** `exists_nsFullData_not_hasZeroDeficiencyOn`: there is
  untruncated Navier–Stokes data on `ℓ²(ℕ)` — dense domain, symmetric pairwise
  commuting modes, symmetric momenta, positive viscosity — whose full
  Hamiltonian is **not** essentially self-adjoint.  Hence the structural
  hypotheses alone (Hermitian modes and momenta, degree ≤ 3) can never yield
  essential self-adjointness of the full operator: an analytic input such as
  completeness of the flow is indispensable.  This is the formal counterpart of
  the `ẋ = x²` warning of the ODE chapter.

## Scope

Essential self-adjointness of the *continuum* Navier–Stokes generator, and with
it global existence for Navier–Stokes, is **not** claimed: the positive results
above are unconditional for the realizations described (bounded lattice modes,
diagonal modes), and conditional — on a complete unitary flow, resp. a total
family of eigenvectors — in general, which by
`exists_nsFullData_not_hasZeroDeficiencyOn` is the best possible shape for a
statement about the abstract data.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace FullEsa

/-! ## Symmetry of domain-preserving operators -/

section SymmetricDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Symmetry of an operator that maps the domain `D` into itself. -/
def IsSymmetricDom {D : Submodule ℂ F} (A : D →ₗ[ℂ] D) : Prop :=
  ∀ x y : D, (inner ℂ ((A x : F)) (y : F) : ℂ) = inner ℂ (x : F) ((A y : F))

variable {D : Submodule ℂ F}

theorem IsSymmetricDom.add {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right, hA x y,
    hB x y]

theorem IsSymmetricDom.sub {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A - B) := by
  intro x y
  simp only [LinearMap.sub_apply, Submodule.coe_sub, inner_sub_left, inner_sub_right, hA x y,
    hB x y]

theorem IsSymmetricDom.real_smul {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (r : ℝ) :
    IsSymmetricDom ((r : ℂ) • A) := by
  intro x y
  simp only [LinearMap.smul_apply, Submodule.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hA x y]

theorem IsSymmetricDom.zero : IsSymmetricDom (0 : D →ₗ[ℂ] D) := by
  intro x y
  simp

theorem IsSymmetricDom.sum {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsSymmetricDom.zero (D := D))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hA a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

/-- The composite of two symmetric operators is symmetric *provided they
commute*. -/
theorem IsSymmetricDom.comp_of_commute {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B) := by
  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ ((B x : F)) ((A y : F)) := hA _ _
  have h2 : (inner ℂ ((B x : F)) ((A y : F)) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) := hB _ _
  have h3 : B (A y) = A (B y) := by
    have := congrArg (fun T : D →ₗ[ℂ] D => T y) hcomm
    simpa using this.symm
  simpa [h3] using h1.trans h2

/-- The **anticommutator** of two symmetric operators is symmetric — no
commutation needed.  This is what makes the Weyl-symmetrized Navier–Stokes
Hamiltonian `π A + A π` symmetric. -/
theorem IsSymmetricDom.anticomm {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) : IsSymmetricDom (A.comp B + B.comp A) := by
  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) :=
    (hA _ _).trans (hB _ _)
  have h2 : (inner ℂ ((B (A x) : F)) (y : F) : ℂ) = inner ℂ (x : F) ((A (B y) : F)) :=
    (hB _ _).trans (hA _ _)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, inner_add_left,
    inner_add_right, h1, h2]
  ring

end SymmetricDom

/-! ## Transferring vanishing deficiency along an equality of operators -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Vanishing adjoint deficiency depends only on the values of the operator. -/
theorem hasZeroDeficiencyOn_congr {D : Submodule ℂ F} {H₁ H₂ : D →ₗ[ℂ] D}
    (h : ∀ x : D, (H₁ x : F) = (H₂ x : F)) (h₁ : HasZeroDeficiencyOn D H₁) :
    HasZeroDeficiencyOn D H₂ := by
  refine ⟨fun w hw => h₁.1 w fun v => ?_, fun w hw => h₁.2 w fun v => ?_⟩ <;>
    · rw [h v]; exact hw v

/-- The restriction of a bounded operator to an invariant domain. -/
noncomputable def restrictCLM (A : F →L[ℂ] F) (D : Submodule ℂ F) (h : ∀ v : D, A (v : F) ∈ D) :
    D →ₗ[ℂ] D :=
  LinearMap.codRestrict D ((A : F →ₗ[ℂ] F).comp D.subtype) h

@[simp] theorem restrictCLM_apply (A : F →L[ℂ] F) (D : Submodule ℂ F)
    (h : ∀ v : D, A (v : F) ∈ D) (x : D) : ((restrictCLM A D h x : D) : F) = A (x : F) := rfl

/-- **A densely defined operator which is the restriction of a bounded symmetric
operator is essentially self-adjoint.** -/
theorem hasZeroDeficiencyOn_of_boundedRealization {D : Submodule ℂ F} (H : D →ₗ[ℂ] D)
    (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hdense : Dense (D : Set F))
    (hHA : ∀ x : D, (H x : F) = A (x : F)) : HasZeroDeficiencyOn D H := by
  have hinv : ∀ v : D, A (v : F) ∈ D := fun v => (hHA v) ▸ (H v).2
  refine hasZeroDeficiencyOn_congr (H₁ := restrictCLM A D hinv) (fun x => (hHA x).symm) ?_
  exact hasZeroDeficiencyOn_of_bounded_symmetric A hsym D hdense hinv

end Transfer

/-! ## The untruncated Navier–Stokes data and Hamiltonian -/

section AbstractFull

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The untruncated Navier–Stokes data.**  The fifteen field modes `u_k` and
the three momenta `π_i` of `book.tex` ~4151–4189, now as operators on a *dense
domain* `D` of an arbitrary complex inner-product space — no truncation, no
finite dimension, no boundedness.  The hypotheses are exactly the structural
ones of the truncated `NSTruncation`: the modes and momenta are symmetric on
`D`, they map `D` into itself, and the field modes commute with one another. -/
structure NSFullData (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  /-- The dense domain. -/
  D : Submodule ℂ F
  /-- The fifteen field modes. -/
  u : Fin 15 → (D →ₗ[ℂ] D)
  /-- The three momenta. -/
  mom : Fin 3 → (D →ₗ[ℂ] D)
  /-- The kinematic viscosity. -/
  nu : ℝ
  dense : Dense (D : Set F)
  u_symm : ∀ k, IsSymmetricDom (u k)
  mom_symm : ∀ i, IsSymmetricDom (mom i)
  u_comm : ∀ k l, (u k).comp (u l) = (u l).comp (u k)

namespace NSFullData

variable (d : NSFullData F)

/-- The velocity mode `u_j`. -/
def velocity (j : Fin 3) : d.D →ₗ[ℂ] d.D := d.u (nsVelIdx j)

/-- The derivative mode `u_{i,j}`. -/
def gradVelocity (i j : Fin 3) : d.D →ₗ[ℂ] d.D := d.u (nsGradIdx i j)

/-- The second-derivative mode `u_{i,jj}`. -/
def lapVelocity (i : Fin 3) : d.D →ₗ[ℂ] d.D := d.u (nsLapIdx i)

/-- The full Navier–Stokes term `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`. -/
noncomputable def advection (i : Fin 3) : d.D →ₗ[ℂ] d.D :=
  (∑ j : Fin 3, (d.velocity j).comp (d.gradVelocity i j)) - (d.nu : ℂ) • d.lapVelocity i

/-- **The full (untruncated) Navier–Stokes Hamiltonian**
`H = ∑_i (π_i A_i + A_i π_i)`, on the dense domain `D`. -/
noncomputable def hamiltonian : d.D →ₗ[ℂ] d.D :=
  ∑ i : Fin 3, ((d.mom i).comp (d.advection i) + (d.advection i).comp (d.mom i))

/-- `A_i` is symmetric on `D`: the modes are symmetric and commute, and `ν` is
real. -/
theorem advection_isSymmetricDom (i : Fin 3) : IsSymmetricDom (d.advection i) :=
  ((IsSymmetricDom.sum Finset.univ fun _ _ =>
      (d.u_symm _).comp_of_commute (d.u_symm _) (d.u_comm _ _)).sub
    ((d.u_symm _).real_smul d.nu))

/-- **The full Navier–Stokes Hamiltonian is symmetric on its domain**, with no
truncation and no boundedness assumption: each term is an anticommutator of two
symmetric operators. -/
theorem hamiltonian_isSymmetricDom : IsSymmetricDom d.hamiltonian :=
  IsSymmetricDom.sum Finset.univ fun i _ =>
    (d.mom_symm i).anticomm (d.advection_isSymmetricDom i)

/-- **Essential self-adjointness of the full Hamiltonian from a complete unitary
flow** (Nelson's criterion, specialized to the untruncated operator).  If the
full Hamiltonian generates a norm-preserving flow that is defined for *every*
real time and leaves the domain invariant, its adjoint has no deficiency. -/
theorem hasZeroDeficiencyOn_of_completeUnitaryFlow (U : ℝ → F → F)
    (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v)
    (hUD : ∀ (t : ℝ) (v : d.D), U t (v : F) ∈ d.D)
    (hderiv : ∀ (v : d.D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F))
        (Complex.I • (d.hamiltonian ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
    d.D d.hamiltonian U d.dense hnorm hU0 hUD hderiv

/-- **Essential self-adjointness of the full Hamiltonian from a total family of
eigenvectors.**  Unlike the bounded criterion this covers unbounded
Hamiltonians. -/
theorem hasZeroDeficiencyOn_of_total_eigenvectors {I : Type*} (e : I → d.D) (lam : I → ℝ)
    (heig : ∀ i, d.hamiltonian (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
    d.D d.hamiltonian e lam heig htotal

/-- **Essential self-adjointness of the full Hamiltonian when it is the
restriction of a bounded symmetric operator.** -/
theorem hasZeroDeficiencyOn_of_boundedRealization (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : d.D, (d.hamiltonian x : F) = A (x : F)) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  _root_.BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization
    d.hamiltonian A hsym d.dense hHA

end NSFullData

end AbstractFull

/-! ## An untruncated instance on `ℓ²(ℤ)`: all fifteen modes, no truncation -/

section Lattice

open BookProof.ChapterContinuityUnitaryInfinite

/-- Multiplication operators by bounded real fields commute. -/
theorem velocityOp_commute (a b : LinfZ) : Commute (velocityOp a) (velocityOp b) := by
  ext f n
  simp only [ContinuousLinearMap.mul_apply, velocityOp_apply]
  ring

theorem momentum_mem_finiteModes {f : L2Z} (hf : f ∈ finiteModes) : momentum f ∈ finiteModes := by
  have hstep := Submodule.smul_mem finiteModes (-Complex.I / 2)
    (Submodule.sub_mem finiteModes (shiftOp_mem_finiteModes 1 hf)
      (shiftOp_mem_finiteModes (-1) hf))
  simpa [momentum] using hstep

/-- The Navier–Stokes term `A_i` of the lattice realization, as a bounded
operator. -/
noncomputable def latticeAdvectionCLM (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) :
    L2Z →L[ℂ] L2Z :=
  (∑ j : Fin 3, velocityOp (v (nsVelIdx j)) * velocityOp (v (nsGradIdx i j)))
    - (nu : ℂ) • velocityOp (v (nsLapIdx i))

/-- **The full Navier–Stokes Hamiltonian of the lattice realization**, as a
bounded operator on `ℓ²(ℤ)`. -/
noncomputable def latticeFullHamiltonianCLM (v : Fin 15 → LinfZ) (nu : ℝ) : L2Z →L[ℂ] L2Z :=
  ∑ i : Fin 3, (momentum * latticeAdvectionCLM v nu i + latticeAdvectionCLM v nu i * momentum)

theorem latticeAdvectionCLM_isSelfAdjoint (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) :
    IsSelfAdjoint (latticeAdvectionCLM v nu i) := by
  have hv : ∀ k, IsSelfAdjoint (velocityOp (v k)) := fun k => velocityOp_isSelfAdjoint (v k)
  change star (latticeAdvectionCLM v nu i) = latticeAdvectionCLM v nu i
  rw [latticeAdvectionCLM, star_sub, star_smul, star_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul, (hv _).star_eq, (hv _).star_eq]
    exact (velocityOp_commute _ _).symm
  · rw [(hv _).star_eq]
    congr 1
    exact Complex.conj_ofReal nu

theorem latticeFullHamiltonianCLM_isSelfAdjoint (v : Fin 15 → LinfZ) (nu : ℝ) :
    IsSelfAdjoint (latticeFullHamiltonianCLM v nu) := by
  change star (latticeFullHamiltonianCLM v nu) = latticeFullHamiltonianCLM v nu
  rw [latticeFullHamiltonianCLM, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_add, star_mul, star_mul, (latticeAdvectionCLM_isSelfAdjoint v nu i).star_eq,
    momentum_isSelfAdjoint.star_eq]
  exact add_comm _ _

theorem latticeFullHamiltonianCLM_isSymmetric (v : Fin 15 → LinfZ) (nu : ℝ) :
    ((latticeFullHamiltonianCLM v nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (latticeFullHamiltonianCLM_isSelfAdjoint v nu)

theorem latticeAdvectionCLM_mem_finiteModes (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3)
    {f : L2Z} (hf : f ∈ finiteModes) : latticeAdvectionCLM v nu i f ∈ finiteModes := by
  simp only [latticeAdvectionCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => ?_)
    (Submodule.smul_mem _ _ (velocityOp_mem_finiteModes _ hf))
  exact velocityOp_mem_finiteModes _ (velocityOp_mem_finiteModes _ hf)

theorem latticeFullHamiltonianCLM_mem_finiteModes (v : Fin 15 → LinfZ) (nu : ℝ)
    {f : L2Z} (hf : f ∈ finiteModes) : latticeFullHamiltonianCLM v nu f ∈ finiteModes := by
  simp only [latticeFullHamiltonianCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_
  · exact momentum_mem_finiteModes (latticeAdvectionCLM_mem_finiteModes v nu i hf)
  · exact latticeAdvectionCLM_mem_finiteModes v nu i (momentum_mem_finiteModes hf)

/-- **The untruncated Navier–Stokes data on the lattice `ℓ²(ℤ)`**: all fifteen
field modes are multiplication by bounded real velocity fields, the momenta are
the symmetric-difference lattice momentum, and the domain is the *proper* dense
subspace of finitely supported modes. -/
noncomputable def latticeFullData (v : Fin 15 → LinfZ) (nu : ℝ) : NSFullData L2Z where
  D := finiteModes
  u k := restrictCLM (velocityOp (v k)) finiteModes fun f => velocityOp_mem_finiteModes _ f.2
  mom _ := restrictCLM momentum finiteModes fun f => momentum_mem_finiteModes f.2
  nu := nu
  dense := finiteModes_dense
  u_symm k := by
    intro x y
    simpa using velocityOp_isSymmetric (v k) (x : L2Z) (y : L2Z)
  mom_symm _ := by
    intro x y
    simpa using momentum_isSymmetric (x : L2Z) (y : L2Z)
  u_comm k l := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    have h := congrArg (fun T : L2Z →L[ℂ] L2Z => T (f : L2Z)) (velocityOp_commute (v k) (v l))
    simpa [restrictCLM] using h

theorem latticeFullData_advection_apply (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3)
    (x : (latticeFullData v nu).D) :
    ((latticeFullData v nu).advection i x : L2Z) = latticeAdvectionCLM v nu i (x : L2Z) := by
  simp only [NSFullData.advection, NSFullData.velocity, NSFullData.gradVelocity,
    NSFullData.lapVelocity, latticeFullData, latticeAdvectionCLM, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_sum, restrictCLM_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply]

theorem latticeFullData_hamiltonian_apply (v : Fin 15 → LinfZ) (nu : ℝ)
    (x : (latticeFullData v nu).D) :
    ((latticeFullData v nu).hamiltonian x : L2Z) = latticeFullHamiltonianCLM v nu (x : L2Z) := by
  simp only [NSFullData.hamiltonian, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.comp_apply, Submodule.coe_add, Submodule.coe_sum,
    latticeFullHamiltonianCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmom : ∀ y : (latticeFullData v nu).D,
      (((latticeFullData v nu).mom i y : (latticeFullData v nu).D) : L2Z) = momentum (y : L2Z) :=
    fun _ => rfl
  rw [hmom, latticeFullData_advection_apply, latticeFullData_advection_apply, hmom]

/-- The constant real field on the lattice, as an element of `ℓ^∞(ℤ)`. -/
noncomputable def constField (r : ℝ) : LinfZ :=
  ⟨fun _ => r, memℓp_infty ⟨|r|, by rintro s ⟨k, rfl⟩; simp⟩⟩

@[simp] theorem constField_apply (r : ℝ) (k : ℤ) : ((constField r : LinfZ) : ℤ → ℝ) k = r := rfl

/-- **The lattice realization is not degenerate**: with every field mode equal to
the constant field `1` and viscosity `1`, the full Navier–Stokes Hamiltonian is
nonzero, so the essential self-adjointness statement below is not about the zero
operator. -/
theorem latticeFullHamiltonianCLM_ne_zero :
    latticeFullHamiltonianCLM (fun _ => constField 1) 1 ≠ 0 := by
  intro hzero
  have hsingle : ((lp.single 2 (0 : ℤ) (1 : ℂ) : L2Z) : ℤ → ℂ) = Pi.single 0 1 := by
    funext k
    simp [lp.single_apply]
  have h := congrArg (fun T : L2Z →L[ℂ] L2Z =>
    ((T (lp.single 2 (0 : ℤ) (1 : ℂ)) : L2Z) : ℤ → ℂ) (-1)) hzero
  simp only [latticeFullHamiltonianCLM, latticeAdvectionCLM,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
    lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, lp.coeFn_zero, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Fin.sum_univ_three,
    momentum_apply, velocityOp_apply, constField_apply, hsingle] at h
  norm_num [Pi.single_apply] at h
  have h6 : (6 : ℂ) * Complex.I = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h6 with h' | h'
  · norm_num at h'
  · exact Complex.I_ne_zero h'

/-- **The full Navier–Stokes Hamiltonian of the lattice realization is
essentially self-adjoint** on the proper dense domain of finitely supported
modes.  This is an untruncated, infinite-dimensional statement: all fifteen
field modes and the three momenta are present, and the domain is not the whole
space (`finiteModes_ne_top`). -/
theorem latticeFull_hasZeroDeficiencyOn (v : Fin 15 → LinfZ) (nu : ℝ) :
    HasZeroDeficiencyOn (latticeFullData v nu).D (latticeFullData v nu).hamiltonian :=
  (latticeFullData v nu).hasZeroDeficiencyOn_of_boundedRealization
    (latticeFullHamiltonianCLM v nu) (latticeFullHamiltonianCLM_isSymmetric v nu)
    (latticeFullData_hamiltonian_apply v nu)

end Lattice

end FullEsa

end BookProof.NavierStokesFlow
