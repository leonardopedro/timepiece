import Mathlib
import BookProof.ChapterNavierStokesEsa
import BookProof.ChapterNavierStokesDeficiency
import BookProof.ChapterNavierStokesFullEsa.Part1

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
/-! ## An **unbounded** untruncated instance on `ℓ²(ℕ)` -/

section Diagonal

open LpNat DiagonalEsa

theorem diagOp_isSymmetricDom (c : ℕ → ℝ) : IsSymmetricDom (diagOp c) := by
  intro x y
  obtain ⟨Nx, hNx⟩ := exists_tail_zero x.2
  obtain ⟨Ny, hNy⟩ := exists_tail_zero y.2
  set N := max Nx Ny with hN
  have hx : ∀ n, N ≤ n → ((x : L2N) : ℕ → ℂ) n = 0 :=
    fun n hn => hNx n (le_trans (le_max_left _ _) hn)
  have hy : ∀ n, N ≤ n → ((y : L2N) : ℕ → ℂ) n = 0 :=
    fun n hn => hNy n (le_trans (le_max_right _ _) hn)
  have hlhs := inner_eq_sum_range (f := ((diagOp c x : lpFiniteModes ℕ) : L2N))
    (g := ((y : lpFiniteModes ℕ) : L2N)) (N := N)
    (by simpa using diagFun_tail_zero c hx)
  have hrhs := inner_eq_sum_range (f := ((x : lpFiniteModes ℕ) : L2N))
    (g := ((diagOp c y : lpFiniteModes ℕ) : L2N)) (N := N) hx
  rw [hlhs, hrhs]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [diagOp_coe, diagFun, map_mul, Complex.conj_ofReal]
  ring

theorem diagOp_comp (a b : ℕ → ℝ) : (diagOp a).comp (diagOp b) = diagOp (fun n => a n * b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.comp_apply, diagOp_coe, diagFun, Complex.ofReal_mul]
  ring

theorem diagOp_add (a b : ℕ → ℝ) : diagOp a + diagOp b = diagOp (fun n => a n + b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, diagOp_coe,
    diagFun, Complex.ofReal_add]
  ring

theorem diagOp_sub (a b : ℕ → ℝ) : diagOp a - diagOp b = diagOp (fun n => a n - b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.sub_apply, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, diagOp_coe,
    diagFun, Complex.ofReal_sub]
  ring

theorem diagOp_real_smul (r : ℝ) (a : ℕ → ℝ) :
    ((r : ℂ)) • diagOp a = diagOp (fun n => r * a n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.smul_apply, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, diagOp_coe, diagFun, Complex.ofReal_mul]
  ring

theorem diagOp_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) :
    (∑ i ∈ s, diagOp (a i)) = diagOp (fun n => ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
      funext n
      simp [diagFun]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, ih, diagOp_add]
      congr 1
      funext n
      rw [Finset.sum_insert hx]

/-- The untruncated Navier–Stokes data on `ℓ²(ℕ)` with **diagonal** modes and
momenta: the symbols `c k` and `p i` are arbitrary real sequences, in particular
they may be unbounded. -/
noncomputable def diagFullData (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    NSFullData L2N where
  D := lpFiniteModes ℕ
  u k := diagOp (c k)
  mom i := diagOp (p i)
  nu := nu
  dense := lpFiniteModes_dense
  u_symm k := diagOp_isSymmetricDom (c k)
  mom_symm i := diagOp_isSymmetricDom (p i)
  u_comm k l := by rw [diagOp_comp, diagOp_comp]; simp [mul_comm]

/-- The symbol of the diagonal full Navier–Stokes Hamiltonian. -/
def diagFullSymbol (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) : ℕ → ℝ := fun n =>
  ∑ i : Fin 3, 2 * (p i n *
    ((∑ j : Fin 3, c (nsVelIdx j) n * c (nsGradIdx i j) n) - nu * c (nsLapIdx i) n))

theorem diagFullData_hamiltonian (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    (diagFullData c p nu).hamiltonian = diagOp (diagFullSymbol c p nu) := by
  simp only [NSFullData.hamiltonian, NSFullData.advection, NSFullData.velocity,
    NSFullData.gradVelocity, NSFullData.lapVelocity, diagFullData, diagOp_comp, diagOp_sum,
    diagOp_real_smul, diagOp_sub, diagOp_add]
  congr 1
  funext n
  simp only [diagFullSymbol]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The full Navier–Stokes Hamiltonian of the diagonal realization is
essentially self-adjoint** on the finite-mode domain of `ℓ²(ℕ)`, for *arbitrary*
— in particular unbounded — real symbols. -/
theorem diagFull_hasZeroDeficiencyOn (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    HasZeroDeficiencyOn (diagFullData c p nu).D (diagFullData c p nu).hamiltonian := by
  rw [diagFullData_hamiltonian]
  exact diagOp_hasZeroDeficiencyOn _

/-- A choice of data whose full Hamiltonian is **unbounded**: the first momentum
grows linearly, the viscous mode is constant. -/
noncomputable def diagUnboundedData : NSFullData L2N :=
  diagFullData (fun k => if k = nsLapIdx 0 then fun _ => 1 else fun _ => 0)
    (fun i => if i = 0 then fun n => (n : ℝ) else fun _ => 0) 1

/-- **The full Navier–Stokes Hamiltonian can be genuinely unbounded and still
essentially self-adjoint.** -/
theorem diagUnboundedData_hamiltonian :
    diagUnboundedData.hamiltonian = diagOp (fun n => -(2 * (n : ℝ))) := by
  unfold diagUnboundedData
  rw [diagFullData_hamiltonian]
  congr 1
  funext n
  simp only [diagFullSymbol, Fin.sum_univ_three]
  norm_num [nsVelIdx, nsGradIdx, nsLapIdx, Fin.ext_iff]

theorem diagFull_not_bounded :
    ¬ ∃ C : ℝ, ∀ f : diagUnboundedData.D, ‖diagUnboundedData.hamiltonian f‖ ≤ C * ‖f‖ := by
  rw [diagUnboundedData_hamiltonian]
  refine diagOp_not_bounded _ fun C => ?_
  refine ⟨⌈|C|⌉₊ + 1, ?_⟩
  have hc : C ≤ |C| := le_abs_self C
  have hn : |C| ≤ (⌈|C|⌉₊ : ℝ) := Nat.le_ceil _
  have h0 : (0 : ℝ) ≤ (⌈|C|⌉₊ : ℝ) := Nat.cast_nonneg _
  have habs : |-(2 * ((⌈|C|⌉₊ + 1 : ℕ) : ℝ))| = 2 * ((⌈|C|⌉₊ : ℝ) + 1) := by
    push_cast
    rw [abs_neg, abs_of_nonneg (by linarith)]
  rw [habs]
  linarith

theorem diagUnbounded_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn diagUnboundedData.D diagUnboundedData.hamiltonian :=
  diagFull_hasZeroDeficiencyOn _ _ _

end Diagonal

/-! ## Sharpness: the structural hypotheses alone do not give ESA -/

section Sharpness

open LpNat JacobiDeficiency

/-- The constant field modes of the counterexample: `u_{0,jj} = -1/2`, all other
modes zero. -/
noncomputable def jacobiMode (k : Fin 15) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  if k = nsLapIdx 0 then ((-1 / 2 : ℝ) : ℂ) • LinearMap.id else 0

/-- The momenta of the counterexample: `π₀` is the tridiagonal operator, the
other two vanish. -/
noncomputable def jacobiMom (i : Fin 3) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  if i = 0 then jacobiOp else 0

theorem jacobiMode_lap : jacobiMode (nsLapIdx 0) = ((-1 / 2 : ℝ) : ℂ) • LinearMap.id :=
  if_pos rfl

theorem jacobiMode_of_ne {k : Fin 15} (h : k ≠ nsLapIdx 0) : jacobiMode k = 0 := if_neg h

theorem jacobiMom_zero : jacobiMom 0 = jacobiOp := if_pos rfl

theorem jacobiMom_of_ne {i : Fin 3} (h : i ≠ 0) : jacobiMom i = 0 := if_neg h

theorem jacobiMode_isSymmetricDom (k : Fin 15) : IsSymmetricDom (jacobiMode k) := by
  by_cases hk : k = nsLapIdx 0
  · rw [hk, jacobiMode_lap]
    exact IsSymmetricDom.real_smul
      (A := (LinearMap.id : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ)) (fun _ _ => rfl) (-1 / 2)
  · rw [jacobiMode_of_ne hk]
    exact IsSymmetricDom.zero

theorem jacobiMode_comm (k l : Fin 15) :
    (jacobiMode k).comp (jacobiMode l) = (jacobiMode l).comp (jacobiMode k) := by
  by_cases hk : k = nsLapIdx 0
  · by_cases hl : l = nsLapIdx 0
    · rw [hk, hl]
    · rw [jacobiMode_of_ne hl, LinearMap.comp_zero, LinearMap.zero_comp]
  · rw [jacobiMode_of_ne hk, LinearMap.comp_zero, LinearMap.zero_comp]

/-- Untruncated Navier–Stokes data on `ℓ²(ℕ)` whose full Hamiltonian is the
tridiagonal operator of `BookProof.ChapterNavierStokesDeficiency`: the field
modes are constants (a uniform velocity field with a constant viscous mode
`u_{0,jj} = −1/2`) and the first momentum is the Jacobi operator. -/
noncomputable def jacobiFullData : NSFullData L2N where
  D := lpFiniteModes ℕ
  u := jacobiMode
  mom := jacobiMom
  nu := 1
  dense := lpFiniteModes_dense
  u_symm := jacobiMode_isSymmetricDom
  mom_symm i := by
    by_cases hi : i = 0
    · rw [hi, jacobiMom_zero]
      exact fun x y => jacobiOp_symmetric x y
    · rw [jacobiMom_of_ne hi]
      exact IsSymmetricDom.zero
  u_comm := jacobiMode_comm

theorem jacobiFullData_hamiltonian : jacobiFullData.hamiltonian = jacobiOp := by
  have hvel : ∀ j : Fin 3, jacobiFullData.velocity j = 0 := by
    intro j
    have h : nsVelIdx j ≠ nsLapIdx 0 := by
      fin_cases j <;> decide
    exact jacobiMode_of_ne h
  have hlap0 : jacobiFullData.lapVelocity 0 = ((-1 / 2 : ℝ) : ℂ) • LinearMap.id :=
    jacobiMode_lap
  have hlapne : ∀ i : Fin 3, i ≠ 0 → jacobiFullData.lapVelocity i = 0 := by
    intro i hi
    refine jacobiMode_of_ne ?_
    fin_cases i
    · exact absurd rfl hi
    · decide
    · decide
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, (jacobiFullData.velocity j).comp (jacobiFullData.gradVelocity i j)) = 0 := by
    intro i
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hvel j, LinearMap.zero_comp]
  have hnu : ((jacobiFullData.nu : ℝ) : ℂ) = 1 := by
    change ((1 : ℝ) : ℂ) = 1
    norm_num
  have hadv0 : jacobiFullData.advection 0 = ((1 / 2 : ℝ) : ℂ) • LinearMap.id := by
    rw [NSFullData.advection, hsum 0, hlap0, hnu, zero_sub, smul_smul, one_mul]
    norm_num
  have hadvne : ∀ i : Fin 3, i ≠ 0 → jacobiFullData.advection i = 0 := by
    intro i hi
    rw [NSFullData.advection, hsum i, hlapne i hi, smul_zero, sub_zero]
  have hmom0 : jacobiFullData.mom 0 = jacobiOp := jacobiMom_zero
  have hmomne : ∀ i : Fin 3, i ≠ 0 → jacobiFullData.mom i = 0 := fun i hi => jacobiMom_of_ne hi
  rw [NSFullData.hamiltonian, Fin.sum_univ_three, hadv0, hmom0,
    hadvne 1 (by decide), hmomne 1 (by decide), hadvne 2 (by decide), hmomne 2 (by decide)]
  simp only [LinearMap.comp_zero, add_zero,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp]
  rw [← add_smul]
  norm_num

/-- **Sharpness of the criteria above.**  There is untruncated Navier–Stokes
data — a dense domain, symmetric pairwise commuting field modes, symmetric
momenta, viscosity `ν = 1` — whose full Hamiltonian is **not** essentially
self-adjoint.  So no proof of essential self-adjointness of the full
Navier–Stokes Hamiltonian can rest on the structural hypotheses alone: an
analytic input (completeness of the flow, a total eigenbasis, boundedness, or a
criterion such as Faris–Lavine) is indispensable. -/
theorem exists_nsFullData_not_hasZeroDeficiencyOn :
    ∃ d : NSFullData L2N, ¬ HasZeroDeficiencyOn d.D d.hamiltonian := by
  refine ⟨jacobiFullData, ?_⟩
  rw [jacobiFullData_hamiltonian]
  exact jacobiOp_not_hasZeroDeficiencyOn

end Sharpness

end FullEsa

end BookProof.NavierStokesFlow
