import Mathlib
import BookProof.ChapterNavierStokesFullEsa
import BookProof.ChapterNavierStokesLagrangianEsa.Part1

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
/-! ## An untruncated instance on `ℓ²(ℤ)`: the kinetic term is a discrete
Laplacian -/

section Lattice

open BookProof.ChapterContinuityUnitaryInfinite FullEsa

/-- **The transformed Navier–Stokes Hamiltonian of the lattice realization**, as
a bounded operator on `ℓ²(ℤ)`: the parcel momenta and the viscous gradients are
the symmetric-difference lattice momentum (so `½∑Pᵢ²` is a discrete Laplacian),
the drift generators and the constraint are multiplication by bounded real
fields. -/
noncomputable def latticeLagCLM (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    L2Z →L[ℂ] L2Z :=
  ((1 / 2 : ℝ) : ℂ) • (∑ _i : Fin 3, momentum * momentum)
    + ((nu : ℝ) : ℂ) • (∑ _i : Fin 3, momentum * momentum)
    + (∑ i : Fin 3, ((fr i : ℝ) : ℂ) • velocityOp (v i))
    + velocityOp w

theorem latticeLagCLM_isSelfAdjoint (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    IsSelfAdjoint (latticeLagCLM v w fr nu) := by
  have hmom : IsSelfAdjoint (momentum * momentum) := by
    change star (momentum * momentum) = momentum * momentum
    rw [star_mul, momentum_isSelfAdjoint.star_eq]
  have hsum : IsSelfAdjoint (∑ _i : Fin 3, momentum * momentum) := by
    change star _ = _
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ => hmom.star_eq
  have hreal : ∀ (r : ℝ) (A : L2Z →L[ℂ] L2Z), IsSelfAdjoint A →
      IsSelfAdjoint (((r : ℝ) : ℂ) • A) := by
    intro r A hA
    change star _ = _
    rw [star_smul, hA.star_eq]
    congr 1
    exact Complex.conj_ofReal r
  have hdrift : IsSelfAdjoint (∑ i : Fin 3, ((fr i : ℝ) : ℂ) • velocityOp (v i)) := by
    change star _ = _
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (hreal (fr i) _ (velocityOp_isSelfAdjoint (v i))).star_eq
  exact (((hreal _ _ hsum).add (hreal _ _ hsum)).add hdrift).add (velocityOp_isSelfAdjoint w)

theorem latticeLagCLM_isSymmetric (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    ((latticeLagCLM v w fr nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (latticeLagCLM_isSelfAdjoint v w fr nu)

/-- **The untruncated transformed Navier–Stokes data on the lattice `ℓ²(ℤ)`**,
on the *proper* dense domain of finitely supported modes. -/
noncomputable def latticeLagData (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) : LagrangianFullData L2Z where
  D := finiteModes
  P _ := restrictCLM momentum finiteModes fun f => momentum_mem_finiteModes f.2
  Q _ := restrictCLM momentum finiteModes fun f => momentum_mem_finiteModes f.2
  drive i := restrictCLM (velocityOp (v i)) finiteModes fun f => velocityOp_mem_finiteModes _ f.2
  force := fr
  constraintOp := restrictCLM (velocityOp w) finiteModes fun f => velocityOp_mem_finiteModes _ f.2
  nu := nu
  dense := finiteModes_dense
  P_symm _ := by
    intro x y
    simpa using momentum_isSymmetric (x : L2Z) (y : L2Z)
  Q_symm _ := by
    intro x y
    simpa using momentum_isSymmetric (x : L2Z) (y : L2Z)
  drive_symm i := by
    intro x y
    simpa using velocityOp_isSymmetric (v i) (x : L2Z) (y : L2Z)
  constraint_symm := by
    intro x y
    simpa using velocityOp_isSymmetric w (x : L2Z) (y : L2Z)
  nu_nonneg := hnu

theorem latticeLagData_hFull_apply (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) (x : (latticeLagData v w fr hnu).D) :
    ((latticeLagData v w fr hnu).hFull x : L2Z) = latticeLagCLM v w fr nu (x : L2Z) := by
  simp only [LagrangianFullData.hFull, LagrangianFullData.kinetic, LagrangianFullData.viscous,
    LagrangianFullData.drift, latticeLagData, latticeLagCLM, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_add,
    Submodule.coe_smul, Submodule.coe_sum, restrictCLM_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply]

/-- **The full transformed Navier–Stokes Hamiltonian of the lattice realization
is essentially self-adjoint** on the proper dense domain of finitely supported
modes of `ℓ²(ℤ)`.  This is an untruncated, infinite-dimensional statement: the
kinetic term is the discrete Laplacian `½∑Pᵢ²`, all four terms of the
transformed operator are present, and the domain is not the whole space
(`finiteModes_ne_top`). -/
theorem latticeLag_hasZeroDeficiencyOn (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ)
    {nu : ℝ} (hnu : 0 ≤ nu) :
    HasZeroDeficiencyOn (latticeLagData v w fr hnu).D (latticeLagData v w fr hnu).hFull :=
  (latticeLagData v w fr hnu).hasZeroDeficiencyOn_of_boundedRealization
    (latticeLagCLM v w fr nu) (latticeLagCLM_isSymmetric v w fr nu)
    (latticeLagData_hFull_apply v w fr hnu)

/-- The zero field of `ℓ^∞(ℤ)`, used to exhibit the purely kinetic realization. -/
noncomputable def zeroField : LinfZ := 0

/-- **The lattice realization is not degenerate**: already the kinetic term
alone — the discrete Laplacian `½∑Pᵢ²` — is a nonzero operator, so the essential
self-adjointness statement above is not about the zero operator. -/
theorem latticeLag_hFull_ne_zero :
    (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).hFull ≠ 0 := by
  intro hzero
  set L := latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ)) with hL
  have hmem : (lp.single 2 (0 : ℤ) (1 : ℂ) : L2Z) ∈ L.D := single_mem_finiteModes 0 1
  have h := congrArg (fun T : L.D →ₗ[ℂ] L.D => ((T ⟨_, hmem⟩ : L.D) : L2Z)) hzero
  simp only [LinearMap.zero_apply, Submodule.coe_zero] at h
  rw [latticeLagData_hFull_apply] at h
  have hsingle : ((lp.single 2 (0 : ℤ) (1 : ℂ) : L2Z) : ℤ → ℂ) = Pi.single 0 1 := by
    funext k
    simp [lp.single_apply]
  have h0 := congrArg (fun g : L2Z => (g : ℤ → ℂ) 0) h
  simp only [latticeLagCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, lp.coeFn_add, lp.coeFn_smul,
    lp.coeFn_zero, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Fin.sum_univ_three,
    momentum_apply, velocityOp_apply, hsingle, zeroField] at h0
  norm_num [Pi.single_apply, Complex.ext_iff] at h0

end Lattice

/-! ## An **unbounded** untruncated instance on `ℓ²(ℕ)` -/

section Diagonal

open LpNat DiagonalEsa FullEsa

/-- The untruncated transformed Navier–Stokes data on `ℓ²(ℕ)` with **diagonal**
constituents: the symbols are arbitrary real sequences, in particular they may
be unbounded. -/
noncomputable def diagLagData (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) : LagrangianFullData L2N where
  D := lpFiniteModes ℕ
  P i := diagOp (p i)
  Q i := diagOp (q i)
  drive i := diagOp (dr i)
  force := fr
  constraintOp := diagOp c
  nu := nu
  dense := lpFiniteModes_dense
  P_symm i := diagOp_isSymmetricDom (p i)
  Q_symm i := diagOp_isSymmetricDom (q i)
  drive_symm i := diagOp_isSymmetricDom (dr i)
  constraint_symm := diagOp_isSymmetricDom c
  nu_nonneg := hnu

/-- The symbol of the diagonal transformed Hamiltonian:
`½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`. -/
noncomputable def diagLagSymbol (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    (nu : ℝ) : ℕ → ℝ :=
  fun n => (1 / 2) * (∑ i : Fin 3, p i n * p i n) + nu * (∑ i : Fin 3, q i n * q i n)
    + (∑ i : Fin 3, fr i * dr i n) + c n

theorem diagLagData_hFull (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) :
    (diagLagData p q dr c fr hnu).hFull = diagOp (diagLagSymbol p q dr c fr nu) := by
  simp only [LagrangianFullData.hFull, LagrangianFullData.kinetic, LagrangianFullData.viscous,
    LagrangianFullData.drift, diagLagData, diagOp_comp, diagOp_sum, diagOp_real_smul, diagOp_add]
  refine congrArg diagOp ?_
  funext n
  simp only [diagLagSymbol]

/-- **The full transformed Navier–Stokes Hamiltonian of the diagonal realization
is essentially self-adjoint** on the finite-mode domain of `ℓ²(ℕ)`, for
*arbitrary* — in particular unbounded — real symbols. -/
theorem diagLag_hasZeroDeficiencyOn (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    {nu : ℝ} (hnu : 0 ≤ nu) :
    HasZeroDeficiencyOn (diagLagData p q dr c fr hnu).D (diagLagData p q dr c fr hnu).hFull := by
  rw [diagLagData_hFull]
  exact diagOp_hasZeroDeficiencyOn _

/-- A purely kinetic choice of transformed data whose parcel momentum grows
linearly: the transformed Hamiltonian is `½n²`, unbounded. -/
noncomputable def diagLagUnbounded : LagrangianFullData L2N :=
  diagLagData (fun i => if i = 0 then fun n => (n : ℝ) else fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (le_refl (0 : ℝ))

theorem diagLagUnbounded_hFull :
    diagLagUnbounded.hFull = diagOp (fun n => (1 / 2) * (n : ℝ) ^ 2) := by
  unfold diagLagUnbounded
  rw [diagLagData_hFull]
  congr 1
  funext n
  simp only [diagLagSymbol, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-- **The transformed Hamiltonian can be genuinely unbounded and still
essentially self-adjoint**: essential self-adjointness after the change of
variables is not a boundedness phenomenon. -/
theorem diagLag_not_bounded :
    ¬ ∃ C : ℝ, ∀ f : diagLagUnbounded.D, ‖diagLagUnbounded.hFull f‖ ≤ C * ‖f‖ := by
  rw [diagLagUnbounded_hFull]
  refine diagOp_not_bounded _ fun C => ?_
  refine ⟨⌈|C|⌉₊ + 1, ?_⟩
  have hc : C ≤ |C| := le_abs_self C
  have hn : |C| ≤ (⌈|C|⌉₊ : ℝ) := Nat.le_ceil _
  have h0 : (0 : ℝ) ≤ (⌈|C|⌉₊ : ℝ) := Nat.cast_nonneg _
  set m : ℝ := (⌈|C|⌉₊ : ℝ) with hm
  have habs : |(1 / 2) * (((⌈|C|⌉₊ + 1 : ℕ) : ℝ)) ^ 2| = (1 / 2) * (m + 1) ^ 2 := by
    push_cast
    rw [abs_of_nonneg (by positivity)]
  rw [habs]
  nlinarith

theorem diagLagUnbounded_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn diagLagUnbounded.D diagLagUnbounded.hFull :=
  diagLag_hasZeroDeficiencyOn _ _ _ _ _ _

end Diagonal

/-! ## Sharpness: the transformed shape alone does not give ESA -/

section Sharpness

open LpNat JacobiDeficiency FullEsa

/-- Transformed Navier–Stokes data on `ℓ²(ℕ)` whose only nonzero term is the
first-order **drift**, realized by the tridiagonal (limit-circle) operator of
`BookProof.ChapterNavierStokesDeficiency`. -/
noncomputable def jacobiLagData : LagrangianFullData L2N where
  D := lpFiniteModes ℕ
  P _ := 0
  Q _ := 0
  drive i := if i = 0 then jacobiOp else 0
  force i := if i = 0 then 1 else 0
  constraintOp := 0
  nu := 0
  dense := lpFiniteModes_dense
  P_symm _ := IsSymmetricDom.zero
  Q_symm _ := IsSymmetricDom.zero
  drive_symm i := by
    by_cases hi : i = 0
    · rw [hi, if_pos rfl]
      exact fun x y => jacobiOp_symmetric x y
    · rw [if_neg hi]
      exact IsSymmetricDom.zero
  constraint_symm := IsSymmetricDom.zero
  nu_nonneg := le_refl 0

theorem jacobiLagData_hFull : jacobiLagData.hFull = jacobiOp := by
  have hP : ∀ i : Fin 3, jacobiLagData.P i = 0 := fun _ => rfl
  have hQ : ∀ i : Fin 3, jacobiLagData.Q i = 0 := fun _ => rfl
  have hC : jacobiLagData.constraintOp = 0 := rfl
  have hd0 : jacobiLagData.drive 0 = jacobiOp := by
    change (if (0 : Fin 3) = 0 then jacobiOp else 0) = jacobiOp
    rw [if_pos rfl]
  have hd1 : jacobiLagData.drive 1 = 0 := by
    change (if (1 : Fin 3) = 0 then jacobiOp else 0) = 0
    rw [if_neg (by decide)]
  have hd2 : jacobiLagData.drive 2 = 0 := by
    change (if (2 : Fin 3) = 0 then jacobiOp else 0) = 0
    rw [if_neg (by decide)]
  have hf0 : jacobiLagData.force 0 = 1 := by
    change (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) = 1
    rw [if_pos rfl]
  have hf1 : jacobiLagData.force 1 = 0 := by
    change (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  have hf2 : jacobiLagData.force 2 = 0 := by
    change (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  have hkin : jacobiLagData.kinetic = 0 := by
    simp [LagrangianFullData.kinetic, hP]
  have hvis : jacobiLagData.viscous = 0 := by
    simp [LagrangianFullData.viscous, hQ]
  have hdrift : jacobiLagData.drift = jacobiOp := by
    simp [LagrangianFullData.drift, Fin.sum_univ_three, hd0, hd1, hd2, hf0, hf1, hf2]
  simp [LagrangianFullData.hFull, hkin, hvis, hdrift, hC]

/-- **Sharpness.**  There is untruncated transformed (Lagrangian) Navier–Stokes
data — a dense domain, symmetric parcel momenta, viscous gradients, drift
generators and constraint, viscosity `ν = 0` — whose transformed Hamiltonian is
**not** essentially self-adjoint: an unbounded first-order drift term already
destroys the property.  So the positive results above cannot be improved to a
statement about the abstract transformed data; an analytic input (a total
eigenbasis / momentum representation, a complete flow, boundedness) is
indispensable.  This is the formal counterpart of the `ẋ = x²` warning of the
ODE chapter.

What the example exploits is that the abstract data imposes no relation between
the first-order drift and the positive second-order part: it allows a drift that
is not relatively bounded by the kinetic term.  Supplying that relation is
exactly the analytic (Kato–Rellich / Faris–Lavine) input the continuum problem
needs, and it is not part of the algebraic structure. -/
theorem exists_lagrangianFullData_not_hasZeroDeficiencyOn :
    ∃ L : LagrangianFullData L2N, ¬ HasZeroDeficiencyOn L.D L.hFull := by
  refine ⟨jacobiLagData, ?_⟩
  rw [jacobiLagData_hFull]
  exact jacobiOp_not_hasZeroDeficiencyOn

end Sharpness

end LagrangianEsa

end BookProof.NavierStokesFlow
