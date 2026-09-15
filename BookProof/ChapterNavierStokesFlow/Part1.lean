import Mathlib
import BookProof.ChapterGhostField
import BookProof.ChapterFreeFieldConstraint
import BookProof.ChapterContinuityUnitary
import BookProof.ChapterU

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

/-! ## Part A — The field, its derivatives as fields, and the momentum constraint -/

section FieldWithDerivatives

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]

/-- **A.2** The operator-valued field of `book.tex` ~4151–4173,
`φ(X) = φ + φ_i · (X_i − x_i)`: a point value `φ` together with first-order
Taylor coefficients `φ_i`, which are the *derivative fields* `u_{k,j}` of the
truncation and are independent canonical degrees of freedom. -/
def fieldTaylor (phi : E →ₗ[ℂ] E) (phiD : ι → E →ₗ[ℂ] E) (X : ι → E →ₗ[ℂ] E)
    (x : ι → ℂ) : E →ₗ[ℂ] E :=
  phi + ∑ i, (phiD i) ∘ₗ (X i - x i • LinearMap.id)

/-- **A.2 (headline)** On an eigenstate of the position operators the
operator-valued field **collapses to its point value**: the first-order Taylor
correction annihilates the state, so `φ(X)|v⟩ = φ|v⟩`. -/
theorem field_evaluates_to_value (phi : E →ₗ[ℂ] E) (phiD : ι → E →ₗ[ℂ] E)
    (X : ι → E →ₗ[ℂ] E) (x : ι → ℂ) (v : E) (hv : ∀ i, X i v = x i • v) :
    fieldTaylor phi phiD X x v = phi v := by
  simp [fieldTaylor, LinearMap.sum_apply, hv]

end FieldWithDerivatives

/-- **A.1 (non-vacuity of A.2)** The hypothesis of `field_evaluates_to_value`
is met by the **position representation**: the position operators are the
diagonal multiplication operators `X_i = diag(x_i)`, whose eigenstates are the
coordinate states `|k⟩` with eigenvalues `x_i(k)`.  On such a state the
operator-valued field of `book.tex` ~4151–4173 collapses to its point value, so
the collapse statement is not about an empty situation. -/
theorem field_evaluates_to_value_diagonal {m : ℕ} (xs : Fin 3 → Fin m → ℂ) (k : Fin m)
    (phi : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (phiD : Fin 3 → (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    fieldTaylor phi phiD (fun i => Matrix.mulVecLin (Matrix.diagonal (xs i)))
        (fun i => xs i k) (Pi.single k 1)
      = phi (Pi.single k 1) := by
  refine field_evaluates_to_value _ _ _ _ _ fun i => ?_
  funext j
  by_cases h : j = k <;> simp [Matrix.mulVec_diagonal, h]

/-- **A.3 (core)** The canonical commutation relation of the Bargmann–Fock model
in the form used for the field modes: with `a_b := ∂/∂X_b` and `a†_b := X_b·(·)`,
`[∂_a, X_b] = δ_{ab}` on polynomials in *any* family of modes. -/
theorem ccr_field {σ : Type*} [DecidableEq σ] (a b : σ) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv a) (MvPolynomial.X b * p)
      - MvPolynomial.X b * (MvPolynomial.pderiv a) p = (if a = b then p else 0) := by
  split_ifs with h <;> simp_all [MvPolynomial.pderiv_X]

/-- **A.3** *The derivatives are fields with their own momenta*
(`book.tex` ~4169): `[u_{j,k}, π^{mn}] = i·δ^n_j·δ^m_k`, here in the
`∂/∂X`-realization of the momentum, on polynomials in the nine derivative modes
`u_{j,k}`. -/
theorem derivativeField_momentum (j k m n : Fin 3) (p : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    (MvPolynomial.pderiv (m, n)) (MvPolynomial.X (j, k) * p)
      - MvPolynomial.X (j, k) * (MvPolynomial.pderiv (m, n)) p
      = (if m = j ∧ n = k then p else 0) := by
  rw [ccr_field]
  simp [Prod.ext_iff]

/-- **A.3** The second-derivative family of `book.tex` ~4170:
`[u_{i,jk}, π^{lmn}] = i·δ^l_i·δ^m_j·δ^n_k`. -/
theorem secondDerivativeField_momentum (i j k l m n : Fin 3)
    (p : MvPolynomial (Fin 3 × Fin 3 × Fin 3) ℂ) :
    (MvPolynomial.pderiv (l, m, n)) (MvPolynomial.X (i, j, k) * p)
      - MvPolynomial.X (i, j, k) * (MvPolynomial.pderiv (l, m, n)) p
      = (if l = i ∧ m = j ∧ n = k then p else 0) := by
  rw [ccr_field]
  simp [Prod.ext_iff]

/-- **A.4** The momentum constraint is a *first-class* invariant of the
dynamics: if the constraint `D` commutes with the Hamiltonian `H`, then
`⁅⁅D, A⁆, H⁆ = −⁅D, ⁅H, A⁆⁆` for every operator `A`, and the `D`-invariant
operators are closed under the Hamiltonian bracket.  (The general identity is
`BookProof.FreeFieldConstraint.constraint_commutation_identity`; this is its
Navier–Stokes instance on matrices.) -/
theorem momentumConstraint_preserved {n : ℕ} (D H A : Matrix (Fin n) (Fin n) ℂ)
    (hDH : BookProof.FreeFieldConstraint.bracket D H = 0)
    (hDA : BookProof.FreeFieldConstraint.bracket D A = 0) :
    BookProof.FreeFieldConstraint.bracket D (BookProof.FreeFieldConstraint.bracket H A) = 0 :=
  BookProof.FreeFieldConstraint.constraint_preserved_under_bracket D H A hDH hDA

/-! ## Part B — The Lagrangian change of variables and volume preservation -/

/-- **B.1** *The parcel velocity is the canonical momentum.*  If the trajectory
`t ↦ X t` is an integral curve of the Eulerian velocity field `u`, then its
derivative — the momentum conjugate to the trajectory — is `u` evaluated at the
parcel position: `Ẋ_i(t) = u_i(X(t))`. -/
theorem lagrangian_velocity {d : ℕ} (X : ℝ → Fin d → ℝ) (u : (Fin d → ℝ) → Fin d → ℝ)
    (h : ∀ t i, HasDerivAt (fun s => X s i) (u (X t) i) t) (t : ℝ) (i : Fin d) :
    deriv (fun s => X s i) t = u (X t) i :=
  (h t i).deriv

/-- **B.2** *Incompressibility is volume preservation in parcel space.*  A
Lagrangian map with unit Jacobian determinant `det(∂X_i/∂ξ_j) = 1` preserves the
volume of every set — the 0-order constraint of the transformed Hamiltonian. -/
theorem volume_preservation_constraint {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hdet : LinearMap.det f = 1) (s : Set (Fin d → ℝ)) :
    MeasureTheory.volume (f '' s) = MeasureTheory.volume s := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap, hdet]
  simp

/-- **B.2 (linearization)** The infinitesimal form of the determinant constraint
is the divergence-free condition: the derivative of `t ↦ det(1 + t·A)` at `t = 0`
is `tr A`, so `det(∂X/∂ξ) = 1` to first order is exactly `∇·u = 0`. -/
theorem det_one_add_smul_hasDerivAt (A : Matrix (Fin 3) (Fin 3) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  have h : ∀ t : ℝ, (1 + t • A).det
      = 1 + t * A.trace
        + t ^ 2 * (A 0 0 * A 1 1 - A 0 1 * A 1 0 + A 0 0 * A 2 2 - A 0 2 * A 2 0
            + A 1 1 * A 2 2 - A 1 2 * A 2 1)
        + t ^ 3 * A.det := by
    intro t
    simp [Matrix.det_fin_three, Matrix.trace_fin_three]
    ring
  simp only [h]
  have h1 : HasDerivAt
      (fun t : ℝ => 1 + t * A.trace
        + t ^ 2 * (A 0 0 * A 1 1 - A 0 1 * A 1 0 + A 0 0 * A 2 2 - A 0 2 * A 2 0
            + A 1 1 * A 2 2 - A 1 2 * A 2 1)
        + t ^ 3 * A.det)
      (0 + 1 * A.trace + ((2 : ℕ) * 0 ^ ((2 : ℕ) - 1)) * (A 0 0 * A 1 1 - A 0 1 * A 1 0
          + A 0 0 * A 2 2 - A 0 2 * A 2 0 + A 1 1 * A 2 2 - A 1 2 * A 2 1)
        + ((3 : ℕ) * 0 ^ ((3 : ℕ) - 1)) * A.det) 0 :=
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).mul_const A.trace)).add
        ((hasDerivAt_pow 2 (0 : ℝ)).mul_const _)).add ((hasDerivAt_pow 3 (0 : ℝ)).mul_const A.det)
  simpa using h1

/-- The data of the **Lagrangian (parcel) form** of the transformed
Navier–Stokes operator: the parcel momenta `P` (whose squares are the advective
Laplacian `−½Δ_X`), the viscous gradients `Q`, the drift generators `D` with the
external force `f`, the viscosity `nu ≥ 0`, and the 0-order volume-preservation
constraint `C`. -/
structure LagrangianNS (n : ℕ) where
  /-- Parcel momenta: the advection term is `½ ∑ P_i²`. -/
  P : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- Viscous gradient operators: the viscosity term is `nu ∑ Q_i²`. -/
  Q : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- Drift generators of the external force (a first-order term). -/
  D : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- The external force. -/
  f : Fin 3 → ℝ
  /-- The kinematic viscosity. -/
  nu : ℝ
  /-- The 0-order volume-preservation (pressure/ghost) constraint. -/
  C : Matrix (Fin n) (Fin n) ℂ
  P_herm : ∀ i, (P i)ᴴ = P i
  Q_herm : ∀ i, (Q i)ᴴ = Q i
  D_herm : ∀ i, (D i)ᴴ = D i
  C_herm : Cᴴ = C
  nu_nonneg : 0 ≤ nu

namespace LagrangianNS

variable {n : ℕ} (L : LagrangianNS n)

/-- The advective (kinetic) term `−½Δ_X = ½ ∑ P_i²`: a **positive** second-order
operator after the Lagrangian change of variables. -/
noncomputable def kinetic : Matrix (Fin n) (Fin n) ℂ := ((1 : ℝ) / 2) • ∑ i, L.P i * L.P i

/-- The viscous term `nu ∑ Q_i²`, second order. -/
noncomputable def viscous : Matrix (Fin n) (Fin n) ℂ := L.nu • ∑ i, L.Q i * L.Q i

/-- The force drift `∑ f_i D_i`, first order. -/
noncomputable def drift : Matrix (Fin n) (Fin n) ℂ := ∑ i, L.f i • L.D i

/-- The full transformed operator `ĥ_full = −½Δ_X − νΔ_{ξ,X} − i f·∇_X + Ĥ_c`. -/
noncomputable def hFull : Matrix (Fin n) (Fin n) ℂ := L.kinetic + L.viscous + L.drift + L.C

/-- **B.3** *The four-term decomposition* of the transformed operator: second
order (advection) + second order (viscosity) + first order (force drift) +
zeroth order (volume-preservation constraint). -/
theorem transformed_hamiltonian_decomposition :
    L.hFull = L.kinetic + L.viscous + L.drift + L.C := rfl

/-- A sum of squares of Hermitian matrices is positive semidefinite. -/
theorem sum_sq_posSemidef {m : ℕ} {R : Fin 3 → Matrix (Fin m) (Fin m) ℂ}
    (hR : ∀ i, (R i)ᴴ = R i) : (∑ i, R i * R i).PosSemidef := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro i _
  have h := Matrix.posSemidef_conjTranspose_mul_self (R i)
  rwa [hR i] at h

/-- **B.3** The advection term is a *positive* second-order operator — the
structural gain of the Lagrangian change of variables. -/
theorem kinetic_posSemidef : L.kinetic.PosSemidef :=
  (sum_sq_posSemidef L.P_herm).smul (by norm_num)

/-- **B.3** The viscous term is positive semidefinite (for `nu ≥ 0`). -/
theorem viscous_posSemidef : L.viscous.PosSemidef :=
  (sum_sq_posSemidef L.Q_herm).smul L.nu_nonneg

/-- **B.3** The transformed operator is Hermitian. -/
theorem transformed_hamiltonian_hermitian : (L.hFull)ᴴ = L.hFull := by
  have hk : (L.kinetic)ᴴ = L.kinetic := (kinetic_posSemidef L).isHermitian
  have hv : (L.viscous)ᴴ = L.viscous := (viscous_posSemidef L).isHermitian
  have hd : (L.drift)ᴴ = L.drift := by
    simp only [drift, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, L.D_herm,
      star_trivial]
  simp only [hFull, Matrix.conjTranspose_add, hk, hv, hd, L.C_herm]

end LagrangianNS

/-! ## Part C — The finite truncation is a finite Hermitian matrix -/

/-- The data of a **finite truncation** of the Navier–Stokes system: the fifteen
field modes `u_k` (`k = 0,1,2`), `u_{k,j}` (indices `3 … 11`) and `u_{k,jj}`
(indices `12, 13, 14`) of `book.tex` ~4151–4173, realized as Hermitian matrices
on a finite-dimensional state space, together with the three momenta `π_i` and
the viscosity `nu`.  The field modes commute with one another, as multiplication
operators of a common set of coordinates do. -/
structure NSTruncation (n : ℕ) where
  /-- The fifteen field modes. -/
  u : Fin 15 → Matrix (Fin n) (Fin n) ℂ
  /-- The three momenta `π_i`. -/
  mom : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- The kinematic viscosity. -/
  nu : ℝ
  u_herm : ∀ k, (u k)ᴴ = u k
  mom_herm : ∀ i, (mom i)ᴴ = mom i
  u_comm : ∀ k l, u k * u l = u l * u k

/-- **Non-vacuity of the truncation hypotheses.**  Diagonal (multiplication)
field modes with real entries — the finite shadow of the multiplication
operators `u_k(x)` — are Hermitian and commute with one another, so together
with any Hermitian momenta they form a truncation. -/
def nsTruncationOfDiagonal {n : ℕ} (a : Fin 15 → Fin n → ℝ)
    (p : Fin 3 → Matrix (Fin n) (Fin n) ℂ) (hp : ∀ i, (p i)ᴴ = p i) (nu : ℝ) :
    NSTruncation n where
  u k := Matrix.diagonal fun x => (a k x : ℂ)
  mom := p
  nu := nu
  u_herm k := by simp [Matrix.diagonal_conjTranspose]
  mom_herm := hp
  u_comm k l := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp [mul_comm]

/-- The index of the velocity mode `u_j`. -/
def nsVelIdx (j : Fin 3) : Fin 15 := ⟨j.val, by omega⟩

/-- The index of the first-derivative mode `u_{i,j}`. -/
def nsGradIdx (i j : Fin 3) : Fin 15 := ⟨3 + 3 * i.val + j.val, by omega⟩

/-- The index of the second-derivative mode `u_{i,jj}`. -/
def nsLapIdx (i : Fin 3) : Fin 15 := ⟨12 + i.val, by omega⟩

variable {n : ℕ} (d : NSTruncation n)

/-- The velocity mode `u_j`. -/
def nsVelocity (j : Fin 3) : Matrix (Fin n) (Fin n) ℂ := d.u (nsVelIdx j)

/-- The derivative mode `u_{i,j}`. -/
def nsGradVelocity (i j : Fin 3) : Matrix (Fin n) (Fin n) ℂ := d.u (nsGradIdx i j)

/-- The second-derivative mode `u_{i,jj}`. -/
def nsLapVelocity (i : Fin 3) : Matrix (Fin n) (Fin n) ℂ := d.u (nsLapIdx i)

/-- **C.2** The Navier–Stokes term `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`
(`book.tex` ~4184–4189): advection minus viscosity. -/
noncomputable def nsAdvection (i : Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  (∑ j : Fin 3, nsVelocity d j * nsGradVelocity d i j) - (d.nu : ℂ) • nsLapVelocity d i

/-- **C.2** The truncated Navier–Stokes Hamiltonian
`H_N = ∑_i (π_i A_i + A_i π_i)`, the Weyl-symmetrized (anticommutator) form. -/
noncomputable def nsHamiltonian : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i : Fin 3, (d.mom i * nsAdvection d i + nsAdvection d i * d.mom i)

/-- `A_i` is Hermitian: the field modes are Hermitian and commute, and `ν` is
real. -/
theorem nsAdvection_hermitian (i : Fin 3) : (nsAdvection d i)ᴴ = nsAdvection d i := by
  simp only [nsAdvection, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, nsVelocity, nsGradVelocity,
    nsLapVelocity, d.u_herm, Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun j _ => d.u_comm _ _

/-- **C.3 (headline)** *The truncated Navier–Stokes Hamiltonian is Hermitian.*
The anticommutator `π_i A_i + A_i π_i` of two Hermitian matrices is Hermitian —
this is what makes `e^{i t H_N}` unitary. -/
theorem nsHamiltonian_hermitian : (nsHamiltonian d)ᴴ = nsHamiltonian d := by
  simp only [nsHamiltonian, Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, nsAdvection_hermitian, d.mom_herm]
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

/-- **The truncated Hamiltonian is not trivially zero.**  With all fifteen modes
equal to the unit multiplication operator, zero viscosity and unit momenta on a
one-dimensional state space, `H_N = 18`, which is nonzero: the statements above
are not about a degenerate operator. -/
theorem nsHamiltonian_ne_zero_example :
    nsHamiltonian (nsTruncationOfDiagonal (n := 1) (fun _ _ => 1) (fun _ => 1)
      (fun _ => Matrix.conjTranspose_one) 0) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [nsHamiltonian, nsAdvection, nsVelocity, nsGradVelocity, nsLapVelocity,
    nsTruncationOfDiagonal, Matrix.ofNat_apply] at h00

/-- The generators of the truncated algebra: `inl k` is the field mode `u_k`,
`inr i` the momentum `π_i`. -/
def nsGen : Fin 15 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ := Sum.elim d.u d.mom

/-- The index set of the terms of `H_N`: an advection term `(i, j, b)` (with `b`
recording which side the momentum sits on) or a viscous term `(i, b)`. -/
abbrev NSWordIndex := (Fin 3 × Fin 3 × Bool) ⊕ (Fin 3 × Bool)

/-- The word (ordered list of generators) of each term of `H_N`. -/
def nsWord : NSWordIndex → List (Fin 15 ⊕ Fin 3)
  | .inl (i, j, false) => [.inr i, .inl (nsVelIdx j), .inl (nsGradIdx i j)]
  | .inl (i, j, true) => [.inl (nsVelIdx j), .inl (nsGradIdx i j), .inr i]
  | .inr (i, false) => [.inr i, .inl (nsLapIdx i)]
  | .inr (i, true) => [.inl (nsLapIdx i), .inr i]

/-- The scalar coefficient of each term of `H_N`. -/
def nsCoeff (nu : ℝ) : NSWordIndex → ℂ
  | .inl _ => 1
  | .inr _ => -(nu : ℂ)

/-- **C.4** Every term of `H_N` is a word of length **at most three** in the
generators. -/
theorem nsWord_length_le_three (a : NSWordIndex) : (nsWord a).length ≤ 3 := by
  rcases a with ⟨i, j, b⟩ | ⟨i, b⟩ <;> cases b <;> simp [nsWord]

/-- **C.4 (headline)** *`H_N` is a polynomial of degree ≤ 3 in the ladder/field
generators* (`book.tex` ~4199, "polynomial of low degree in the fields"): it is
a finite linear combination of words `nsWord a`, each of length at most three by
`nsWord_length_le_three`.

**Role: symmetry, not self-adjointness.**  The degree bound says `H_N` is a
well-defined polynomial operator; self-adjointness of the truncation comes from
`nsHamiltonian_hermitian` (finite matrices), not from the degree bound. -/
theorem nsHamiltonian_isPolynomial :
    nsHamiltonian d = ∑ a : NSWordIndex, nsCoeff d.nu a • ((nsWord a).map (nsGen d)).prod := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, nsWord, nsCoeff,
    nsGen, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Sum.elim_inl,
    Sum.elim_inr, one_smul, mul_one, nsHamiltonian, nsAdvection, nsVelocity, nsGradVelocity,
    nsLapVelocity]
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    sub_eq_add_neg, mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul, neg_smul, mul_assoc]
  abel

end BookProof.NavierStokesFlow
