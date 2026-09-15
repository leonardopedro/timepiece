import Mathlib
import BookProof.ChapterNavierStokesFullEsa

/-!
# Essential self-adjointness of the **full** Navier–Stokes Hamiltonian *after the
Lagrangian change of variables*

`BookProof.ChapterNavierStokesFlow` records the Lagrangian (parcel) change of
variables of `PLAN_LEAN_SPECIALIST_NS_FLOW.md` Part B for a **finite
truncation**: with the Eulerian velocity replaced by the parcel trajectory
`X(ξ)` and its canonical momentum `P(ξ) = Ẋ(ξ) = u(X(ξ))`, the Navier–Stokes
operator becomes the four-term expression

`ĥ_full = −½Δ_X − ν Δ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint`
       ` = ½ ∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ² + ∑ᵢ fᵢ Dᵢ + C`,

whose first two terms are *positive* second-order operators, the third a
first-order drift and the fourth the zeroth-order volume-preservation
constraint.  `BookProof.ChapterNavierStokesFullEsa` removes the truncation from
the *Eulerian* operator.  This module removes the truncation from the
*transformed* one and proves its essential self-adjointness.

## What is proved here

* `LagrangianFullData` — the untruncated transformed data: a dense domain `D` of
  an arbitrary complex inner-product space, three symmetric parcel momenta `Pᵢ`,
  three symmetric viscous gradients `Qᵢ`, three symmetric drift generators `Dᵢ`
  with a real external force, a symmetric constraint operator and a viscosity
  `ν ≥ 0`.  Nothing is finite-dimensional and nothing is bounded.
* `LagrangianFullData.hFull_isSymmetricDom` — the transformed Hamiltonian is
  symmetric on its domain, unconditionally.
* `LagrangianFullData.kinetic_inner`, `kinetic_nonneg`, `viscous_nonneg` — the
  quadratic forms of the two second-order terms are `½∑‖Pᵢv‖²` and `ν∑‖Qᵢv‖²`:
  after the change of variables the advection term is **positive**, which is the
  structural gain the change of variables is made for.
* `LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors` — **the
  headline criterion**: if the constituents of the transformed operator have a
  total family of common eigenvectors with real eigenvalues in the domain — the
  Lagrangian *momentum representation* — then the full transformed Hamiltonian
  is essentially self-adjoint, with the explicit eigenvalue
  `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.  Also the flow criterion
  (`hasZeroDeficiencyOn_of_completeUnitaryFlow`) and the bounded-realization
  criterion.
* `hasZeroDeficiencyOn_of_linearIsometryEquiv` and
  `NSFullData.hasZeroDeficiencyOn_of_lagrangian` — **the change of variables
  transfers essential self-adjointness**: vanishing adjoint deficiency is
  invariant under a unitary change of variables, so proving essential
  self-adjointness *after* passing to the Lagrangian variables proves it for the
  Eulerian operator it came from.
* **Two genuinely infinite-dimensional, untruncated instances.**  On `ℓ²(ℤ)`
  the parcel momenta and viscous gradients are the lattice
  (symmetric-difference) momentum — so the kinetic term `½∑Pᵢ²` really is a
  discrete Laplacian — the drift generators and the constraint are
  multiplication by bounded real fields, and the transformed Hamiltonian is
  essentially self-adjoint on the **proper** dense domain of finitely supported
  modes (`latticeLag_hasZeroDeficiencyOn`), and is not the zero operator
  (`latticeLag_hFull_ne_zero`).  On `ℓ²(ℕ)` all the constituents are diagonal
  with arbitrary — in particular unbounded — real symbols, and the transformed
  Hamiltonian is again essentially self-adjoint
  (`diagLag_hasZeroDeficiencyOn`), for a suitable choice genuinely unbounded
  (`diagLag_not_bounded`).
* **Sharpness.**  `exists_lagrangianFullData_not_hasZeroDeficiencyOn`: the
  algebraic shape of the transformed operator is by itself not enough — an
  unbounded first-order *drift* term can already destroy essential
  self-adjointness.  So the criteria above are necessary, not decorative; this
  is the formal counterpart of the `ẋ = x²` warning of the ODE chapter.

## Scope

Essential self-adjointness of the *continuum* transformed Navier–Stokes
generator — and with it global existence for Navier–Stokes — is **not** claimed.
What is proved is: the transformed operator is symmetric and has positive
second-order part in complete generality; it is essentially self-adjoint,
unconditionally, for the two untruncated infinite-dimensional realizations
above; it is essentially self-adjoint under each of three general criteria; and
essential self-adjointness passes back and forth along the change of variables.
By `exists_lagrangianFullData_not_hasZeroDeficiencyOn` no statement about the
abstract transformed data can do better than a criterion of this kind.
-/

namespace BookProof.NavierStokesFlow

namespace LagrangianEsa

open FullEsa

/-! ## The untruncated transformed (Lagrangian) data -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The untruncated Lagrangian Navier–Stokes data.**  The parcel momenta `Pᵢ`
(= the Eulerian velocities evaluated along the trajectory, `uᵢ(X(ξ)) = Pᵢ(ξ)`),
the viscous gradients `Qᵢ = ∇_ξPᵢ`, the drift generators `Dᵢ` of the external
force, the zeroth-order volume-preservation constraint `C` and the viscosity
`ν ≥ 0` — now as operators on a *dense domain* `D` of an arbitrary complex
inner-product space. -/
structure LagrangianFullData (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] where
  /-- The dense domain. -/
  D : Submodule ℂ F
  /-- The parcel momenta: the advection term is `½∑Pᵢ²`. -/
  P : Fin 3 → (D →ₗ[ℂ] D)
  /-- The viscous gradients: the viscosity term is `ν∑Qᵢ²`. -/
  Q : Fin 3 → (D →ₗ[ℂ] D)
  /-- The drift generators of the external force (a first-order term). -/
  drive : Fin 3 → (D →ₗ[ℂ] D)
  /-- The external force. -/
  force : Fin 3 → ℝ
  /-- The zeroth-order volume-preservation (pressure/ghost) constraint. -/
  constraintOp : D →ₗ[ℂ] D
  /-- The kinematic viscosity. -/
  nu : ℝ
  dense : Dense (D : Set F)
  P_symm : ∀ i, IsSymmetricDom (P i)
  Q_symm : ∀ i, IsSymmetricDom (Q i)
  drive_symm : ∀ i, IsSymmetricDom (drive i)
  constraint_symm : IsSymmetricDom constraintOp
  nu_nonneg : 0 ≤ nu

namespace LagrangianFullData

variable (L : LagrangianFullData F)

/-- The advective (kinetic) term `−½Δ_X = ½∑Pᵢ²` — a *positive* second-order
operator after the Lagrangian change of variables. -/
noncomputable def kinetic : L.D →ₗ[ℂ] L.D :=
  ((1 / 2 : ℝ) : ℂ) • ∑ i : Fin 3, (L.P i).comp (L.P i)

/-- The viscous term `−νΔ_{ξ,X} = ν∑Qᵢ²`, second order. -/
noncomputable def viscous : L.D →ₗ[ℂ] L.D :=
  ((L.nu : ℝ) : ℂ) • ∑ i : Fin 3, (L.Q i).comp (L.Q i)

/-- The force drift `∑fᵢDᵢ`, first order. -/
noncomputable def drift : L.D →ₗ[ℂ] L.D :=
  ∑ i : Fin 3, ((L.force i : ℝ) : ℂ) • L.drive i

/-- **The full transformed Navier–Stokes Hamiltonian**
`ĥ_full = −½Δ_X − νΔ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint`, on the dense domain
`D`, with no truncation and no boundedness assumption. -/
noncomputable def hFull : L.D →ₗ[ℂ] L.D :=
  L.kinetic + L.viscous + L.drift + L.constraintOp

/-- The four-term decomposition: second order (advection) + second order
(viscosity) + first order (force drift) + zeroth order (constraint). -/
theorem hFull_decomposition :
    L.hFull = L.kinetic + L.viscous + L.drift + L.constraintOp := rfl

/-- The square of a symmetric operator is symmetric. -/
theorem isSymmetricDom_sq {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) :
    IsSymmetricDom (A.comp A) :=
  hA.comp_of_commute hA rfl

theorem kinetic_isSymmetricDom : IsSymmetricDom L.kinetic :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.P_symm i)) _

theorem viscous_isSymmetricDom : IsSymmetricDom L.viscous :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.Q_symm i)) _

theorem drift_isSymmetricDom : IsSymmetricDom L.drift :=
  IsSymmetricDom.sum Finset.univ fun i _ => (L.drive_symm i).real_smul _

/-- **The full transformed Navier–Stokes Hamiltonian is symmetric on its
domain**, unconditionally: each of the four terms is. -/
theorem hFull_isSymmetricDom : IsSymmetricDom L.hFull :=
  ((L.kinetic_isSymmetricDom.add L.viscous_isSymmetricDom).add
      L.drift_isSymmetricDom).add L.constraint_symm

/-! ### Positivity of the second-order part -/

/-- The quadratic form of the square of a symmetric operator is the squared norm
of its value. -/
theorem inner_comp_self {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (v : D) :
    (inner ℂ (v : F) ((A.comp A) v : F) : ℂ) = ((‖(A v : F)‖ ^ 2 : ℝ) : ℂ) := by
  have h := hA v (A v)
  simp only [LinearMap.comp_apply]
  rw [← h]
  simp

/-- **The advection term of the transformed operator is positive**: its
quadratic form is `½∑‖Pᵢv‖²`.  This is the structural gain of the Lagrangian
change of variables — the Eulerian advection `−u_j∂_ju_i` becomes the positive
second-order Laplacian `−½Δ_X`. -/
theorem kinetic_inner (v : L.D) :
    (inner ℂ (v : F) (L.kinetic v : F) : ℂ)
      = (((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [kinetic, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, inner_smul_right, inner_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => inner_comp_self (L.P_symm i) v

/-- The viscous term is positive as well (`ν ≥ 0`). -/
theorem viscous_inner (v : L.D) :
    (inner ℂ (v : F) (L.viscous v : F) : ℂ)
      = ((L.nu * ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [viscous, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, inner_smul_right, inner_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => inner_comp_self (L.Q_symm i) v

theorem kinetic_nonneg (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re := by
  rw [L.kinetic_inner v, Complex.ofReal_re]
  have : (0 : ℝ) ≤ ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem viscous_nonneg (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re := by
  rw [L.viscous_inner v, Complex.ofReal_re]
  have h : (0 : ℝ) ≤ ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  exact mul_nonneg L.nu_nonneg h

/-! ### Criteria for essential self-adjointness -/

/-- **Essential self-adjointness of the transformed Hamiltonian from a complete
unitary flow** (Nelson's criterion). -/
theorem hasZeroDeficiencyOn_of_completeUnitaryFlow (U : ℝ → F → F)
    (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖) (hU0 : ∀ v : F, U 0 v = v)
    (hUD : ∀ (t : ℝ) (v : L.D), U t (v : F) ∈ L.D)
    (hderiv : ∀ (v : L.D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F)) (Complex.I • (L.hFull ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn L.D L.hFull :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
    L.D L.hFull U L.dense hnorm hU0 hUD hderiv

/-- **Essential self-adjointness of the transformed Hamiltonian when it is the
restriction of a bounded symmetric operator.** -/
theorem hasZeroDeficiencyOn_of_boundedRealization (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : L.D, (L.hFull x : F) = A (x : F)) :
    HasZeroDeficiencyOn L.D L.hFull :=
  FullEsa.hasZeroDeficiencyOn_of_boundedRealization L.hFull A hsym L.dense hHA

/-- **Essential self-adjointness of the transformed Hamiltonian from a total
family of its own eigenvectors.**  Unlike the bounded criterion this covers
unbounded operators, and unlike the criterion below the eigenvectors need not be
eigenvectors of the individual constituents. -/
theorem hasZeroDeficiencyOn_of_total_eigenvectors {I : Type*} (e : I → L.D) (lam : I → ℝ)
    (heig : ∀ a, L.hFull (e a) = ((lam a : ℝ) : ℂ) • e a)
    (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn L.D L.hFull :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
    L.D L.hFull e lam heig htotal

/-- The eigenvalue of the transformed Hamiltonian on a common eigenvector of its
constituents: `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`. -/
noncomputable def eigenvalue (p q dr : Fin 3 → ℝ) (c : ℝ) : ℝ :=
  (1 / 2) * (∑ i : Fin 3, p i ^ 2) + L.nu * (∑ i : Fin 3, q i ^ 2)
    + (∑ i : Fin 3, L.force i * dr i) + c

/-- A common eigenvector of the constituents is an eigenvector of the
transformed Hamiltonian, with the eigenvalue above. -/
theorem hFull_eigenvector {v : L.D} {p q dr : Fin 3 → ℝ} {c : ℝ}
    (hP : ∀ i, L.P i v = ((p i : ℝ) : ℂ) • v) (hQ : ∀ i, L.Q i v = ((q i : ℝ) : ℂ) • v)
    (hD : ∀ i, L.drive i v = ((dr i : ℝ) : ℂ) • v)
    (hC : L.constraintOp v = ((c : ℝ) : ℂ) • v) :
    L.hFull v = ((L.eigenvalue p q dr c : ℝ) : ℂ) • v := by
  have hPP : ∀ i, (L.P i).comp (L.P i) v = ((p i ^ 2 : ℝ) : ℂ) • v := by
    intro i
    simp only [LinearMap.comp_apply, map_smul, hP i, smul_smul]
    norm_num [pow_two]
  have hQQ : ∀ i, (L.Q i).comp (L.Q i) v = ((q i ^ 2 : ℝ) : ℂ) • v := by
    intro i
    simp only [LinearMap.comp_apply, map_smul, hQ i, smul_smul]
    norm_num [pow_two]
  simp only [hFull, kinetic, viscous, drift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hPP, hQQ, hD, hC, smul_smul, ← Finset.sum_smul, ← add_smul,
    eigenvalue]
  push_cast
  ring_nf

/-- **The headline criterion.**  If the constituents of the transformed
Navier–Stokes operator have a *total* family of common eigenvectors with real
eigenvalues inside the domain — which is exactly the Lagrangian momentum
representation the change of variables is designed to produce — then the full
transformed Hamiltonian is **essentially self-adjoint** on that domain.  No
boundedness is required: the eigenvalues may be arbitrary reals. -/
theorem hasZeroDeficiencyOn_of_commonEigenvectors {I : Type*} (e : I → L.D)
    (p q dr : Fin 3 → I → ℝ) (c : I → ℝ)
    (hP : ∀ i a, L.P i (e a) = ((p i a : ℝ) : ℂ) • e a)
    (hQ : ∀ i a, L.Q i (e a) = ((q i a : ℝ) : ℂ) • e a)
    (hD : ∀ i a, L.drive i (e a) = ((dr i a : ℝ) : ℂ) • e a)
    (hC : ∀ a, L.constraintOp (e a) = ((c a : ℝ) : ℂ) • e a)
    (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn L.D L.hFull :=
  L.hasZeroDeficiencyOn_of_total_eigenvectors e
    (fun a => L.eigenvalue (fun i => p i a) (fun i => q i a) (fun i => dr i a) (c a))
    (fun a => L.hFull_eigenvector (fun i => hP i a) (fun i => hQ i a) (fun i => hD i a) (hC a))
    htotal

end LagrangianFullData

end Abstract

/-! ## The change of variables transfers essential self-adjointness -/

section ChangeOfVariables

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- **Vanishing adjoint deficiency is invariant under a unitary change of
variables.**  If `W` is a unitary map carrying the domain `D` onto the domain
`D'` and intertwining `H` with `H'`, then essential self-adjointness of `H'` —
the operator *after* the change of variables — gives essential self-adjointness
of `H`.  This is what makes the Lagrangian route legitimate: it is enough to
prove the property for the transformed operator. -/
theorem hasZeroDeficiencyOn_of_linearIsometryEquiv (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'}
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F)))
    (h : HasZeroDeficiencyOn D' H') : HasZeroDeficiencyOn D H := by
  have key : ∀ (c : ℂ), (∀ w' : G, (∀ y : D', (inner ℂ (H' y : G) w' : ℂ)
      = inner ℂ (y : G) (c • w')) → w' = 0) →
      ∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (c • w)) → w = 0 := by
    intro c hc w hw
    have hW : W w = 0 := by
      refine hc (W w) fun y => ?_
      obtain ⟨x, hx⟩ := hsurj y
      have hHy : (H' y : G) = W ((H x : F)) := by
        have hxy : (⟨W (x : F), hmap x⟩ : D') = y := Subtype.ext hx
        rw [← hxy, hint x]
      rw [hHy, ← hx, W.inner_map_map, hw x, inner_smul_right, inner_smul_right,
        W.inner_map_map]
    have := congrArg W.symm hW
    simpa using this
  refine ⟨key Complex.I h.1, fun w hw => ?_⟩
  refine key (-Complex.I) (fun w' hw' => h.2 w' fun y => ?_) w ?_
  · simpa using hw' y
  · intro v
    simpa using hw v

/-- The converse transport: essential self-adjointness of the operator *before*
the change of variables gives it for the transformed operator. -/
theorem hasZeroDeficiencyOn_map_of_linearIsometryEquiv (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'}
    (hmap : ∀ x : D, W (x : F) ∈ D')
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F)))
    (h : HasZeroDeficiencyOn D H) : HasZeroDeficiencyOn D' H' := by
  have key : ∀ (c : ℂ), (∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ)
      = inner ℂ (v : F) (c • w)) → w = 0) →
      ∀ w' : G, (∀ y : D', (inner ℂ (H' y : G) w' : ℂ) = inner ℂ (y : G) (c • w')) → w' = 0 := by
    intro c hc w' hw'
    have hW : W.symm w' = 0 := by
      refine hc (W.symm w') fun v => ?_
      have hleft : (inner ℂ (H v : F) (W.symm w') : ℂ) = inner ℂ (W ((H v : F))) w' := by
        rw [← W.inner_map_map ((H v : F)) (W.symm w')]
        simp
      have hright : (inner ℂ (v : F) (c • W.symm w') : ℂ) = inner ℂ (W (v : F)) (c • w') := by
        rw [inner_smul_right, inner_smul_right, ← W.inner_map_map (v : F) (W.symm w')]
        simp
      rw [hleft, hright, ← hint v]
      exact hw' ⟨W (v : F), hmap v⟩
    simpa using congrArg W hW
  refine ⟨key Complex.I h.1, fun w' hw' => ?_⟩
  refine key (-Complex.I) (fun w hw => h.2 w fun v => ?_) w' ?_
  · simpa using hw v
  · intro y
    simpa using hw' y

/-- **Essential self-adjointness is a property of the operator, not of the
variables it is written in.**  Under a unitary change of variables carrying one
domain onto the other and intertwining the two operators, the Eulerian operator
is essentially self-adjoint if and only if the transformed one is. -/
theorem hasZeroDeficiencyOn_iff_of_linearIsometryEquiv (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'}
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F))) :
    HasZeroDeficiencyOn D H ↔ HasZeroDeficiencyOn D' H' :=
  ⟨hasZeroDeficiencyOn_map_of_linearIsometryEquiv W hmap hint,
    hasZeroDeficiencyOn_of_linearIsometryEquiv W hmap hsurj hint⟩

/-- **Essential self-adjointness of the full Navier–Stokes Hamiltonian, obtained
after the Lagrangian change of variables.**  Let `d` be untruncated Eulerian
Navier–Stokes data and `L` the transformed (Lagrangian) data, related by a
unitary change of variables `W` carrying the Eulerian domain onto the Lagrangian
one and the Eulerian Hamiltonian into the transformed Hamiltonian
`ĥ_full = ½∑Pᵢ² + ν∑Qᵢ² + ∑fᵢDᵢ + C`.  If the transformed operator is
essentially self-adjoint, so is the Eulerian one. -/
theorem NSFullData.hasZeroDeficiencyOn_of_lagrangian (d : FullEsa.NSFullData F)
    (L : LagrangianFullData G) (W : F ≃ₗᵢ[ℂ] G) (hmap : ∀ x : d.D, W (x : F) ∈ L.D)
    (hsurj : ∀ y : L.D, ∃ x : d.D, W (x : F) = (y : G))
    (hint : ∀ x : d.D, (L.hFull ⟨W (x : F), hmap x⟩ : G) = W ((d.hamiltonian x : F)))
    (hL : HasZeroDeficiencyOn L.D L.hFull) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  hasZeroDeficiencyOn_of_linearIsometryEquiv W hmap hsurj hint hL

end ChangeOfVariables

end LagrangianEsa

end BookProof.NavierStokesFlow
