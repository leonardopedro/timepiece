import Mathlib
import BookProof.ChapterNavierStokesFullEsa
import BookProof.ChapterNavierStokesCarleman.Part1

/-!
# Carleman's criterion, and an **unbounded, non-commuting** full Navier–Stokes
Hamiltonian that is essentially self-adjoint

`BookProof.ChapterNavierStokesFullEsa` proves essential self-adjointness of the
full (untruncated) Navier–Stokes Hamiltonian in two infinite-dimensional
realizations: a *bounded* one on `ℓ²(ℤ)`, and an *unbounded but diagonal* one on
`ℓ²(ℕ)`, where the momenta commute with the field modes.  Neither carries the
genuine difficulty of the continuum problem, in which the momentum does **not**
commute with the (possibly unbounded) velocity field.

This module supplies that case.  On the half-line lattice `ℓ²(ℕ)` the momentum
is the symmetric-difference operator `(p f)_n = -(i/2)(f_{n+1} - f_{n-1})`, the
field modes are multiplication by arbitrary real sequences — bounded or not —
and the Weyl-symmetrized Navier–Stokes Hamiltonian
`H = ∑_i (π_i A_i + A_i π_i)` is then a **tridiagonal (Jacobi) operator** whose
off-diagonal couplings are `c_n = -(i/2)(α_n + α_{n+1})`, `α` the total
Navier–Stokes symbol `∑_i (∑_j u_j u_{i,j} − ν u_{i,jj})`.

* `tridiagOp` — the tridiagonal operator with complex couplings `c`, on the
  finite-mode domain of `ℓ²(ℕ)`; `tridiagOp_isSymmetricDom` its symmetry.
* `tridiag_hasZeroDeficiencyOn_of_carleman` — **Carleman's criterion**: if
  `∑ 1/|c_n| = ∞` then the tridiagonal operator is essentially self-adjoint.
  The proof is the classical Wronskian argument: a deficiency vector `w`
  satisfies `c_n w_{n+1} + \bar c_{n-1} w_{n-1} = ± i w_n`, whose Wronskian
  telescopes to `2i ∑_{m ≤ n} |w_m|²`, forcing
  `|w_n| |w_{n+1}| ≥ (∑_{m ≤ n₀} |w_m|²)/|c_n|`; summing contradicts
  `∑ 1/|c_n| = ∞` because `∑ |w_n| |w_{n+1}| ≤ ‖w‖²`.
* `halfLineFullData` — the untruncated Navier–Stokes data on `ℓ²(ℕ)` with the
  symmetric-difference momentum and arbitrary real field modes, and
  `halfLineFullData_hamiltonian`, the identification of its full Hamiltonian
  with a tridiagonal operator.
* `halfLineFull_hasZeroDeficiencyOn` — **the headline**: the full Navier–Stokes
  Hamiltonian of this realization is essentially self-adjoint whenever the
  Navier–Stokes symbol satisfies Carleman's growth condition.
* `linearFull_hasZeroDeficiencyOn` together with `linearFull_not_bounded` — a
  concrete instance: a velocity/viscous field growing **linearly** gives an
  unbounded full Navier–Stokes Hamiltonian, with non-commuting momentum and
  field modes, which is essentially self-adjoint.

*The dichotomy.*  Carleman's condition is a growth restriction: `α_n ∼ n`
diverges (`∑ 1/n = ∞`) and gives essential self-adjointness, while for a field
growing fast enough the sum converges and the criterion is silent — as it must
be, since `BookProof.ChapterNavierStokesDeficiency` exhibits a tridiagonal
operator with geometrically growing couplings that is *not* essentially
self-adjoint, and `BookProof.ChapterNavierStokesFullEsa` realizes it as a full
Navier–Stokes Hamiltonian.  This is the lattice form of the ODE chapter's
`ẋ = x²` warning: quadratic (and faster) growth of the field can destroy
essential self-adjointness, subquadratic growth cannot.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace Carleman

open LpNat DiagonalEsa FullEsa
/-! ## The half-line realization of the full Navier–Stokes Hamiltonian -/

section HalfLine

open NSFullData

/-- **The half-line momentum**: the symmetric-difference operator
`(p f)_n = -(i/2)(f_{n+1} - f_{n-1})` (with `f_{-1} = 0`), which is exactly the
tridiagonal operator with the constant coupling `-i/2`. -/
noncomputable def momOp : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  tridiagOp (fun _ => -(Complex.I / 2))

theorem momOp_isSymmetricDom : IsSymmetricDom momOp := tridiagOp_isSymmetricDom _

/-- The couplings produced by Weyl-symmetrizing the half-line momentum against
multiplication by the real sequence `a`. -/
noncomputable def nsCoupling (a : ℕ → ℝ) : ℕ → ℂ := fun n =>
  -(Complex.I / 2) * ((a n : ℂ) + (a (n + 1) : ℂ))

theorem tridiagOp_add (c c' : ℕ → ℂ) :
    tridiagOp c + tridiagOp c' = tridiagOp (fun n => c n + c' n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  cases n with
  | zero => simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply,
      tridiagOp_coe, tridiagFun]; ring
  | succ m => simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply,
      tridiagOp_coe, tridiagFun, map_add]; ring

theorem tridiagOp_sum {ι : Type*} (s : Finset ι) (cc : ι → ℕ → ℂ) :
    (∑ i ∈ s, tridiagOp (cc i)) = tridiagOp (fun n => ∑ i ∈ s, cc i n) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
      funext n
      cases n with
      | zero => simp [tridiagFun]
      | succ m => simp [tridiagFun]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, ih, tridiagOp_add]
      congr 1
      funext n
      rw [Finset.sum_insert hx]

/-- **The Weyl-symmetrized product is tridiagonal.**  Symmetrizing the half-line
momentum against multiplication by a real sequence `a` gives the tridiagonal
operator with couplings `-(i/2)(a_n + a_{n+1})`. -/
theorem weyl_momOp_diagOp (a : ℕ → ℝ) :
    momOp.comp (diagOp a) + (diagOp a).comp momOp = tridiagOp (nsCoupling a) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  cases n with
  | zero =>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, lp.coeFn_add,
        Pi.add_apply, momOp, tridiagOp_coe, diagOp_coe, tridiagFun, diagFun, nsCoupling]
      ring
  | succ m =>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, lp.coeFn_add,
        Pi.add_apply, momOp, tridiagOp_coe, diagOp_coe, tridiagFun, diagFun, nsCoupling,
        map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofNat, Complex.conj_ofReal,
        map_add]
      ring

/-- **The untruncated Navier–Stokes data on the half-line lattice**: the fifteen
field modes are multiplication by *arbitrary* — in particular unbounded — real
sequences, and each of the three momenta is the symmetric-difference momentum,
which does **not** commute with the modes. -/
noncomputable def halfLineFullData (c : Fin 15 → ℕ → ℝ) (nu : ℝ) : NSFullData L2N where
  D := lpFiniteModes ℕ
  u k := diagOp (c k)
  mom _ := momOp
  nu := nu
  dense := lpFiniteModes_dense
  u_symm k := diagOp_isSymmetricDom (c k)
  mom_symm _ := momOp_isSymmetricDom
  u_comm k l := by rw [diagOp_comp, diagOp_comp]; simp [mul_comm]

/-- The Navier–Stokes term `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}` as a real
sequence. -/
def halfLineAlpha (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) : ℕ → ℝ := fun n =>
  (∑ j : Fin 3, c (nsVelIdx j) n * c (nsGradIdx i j) n) - nu * c (nsLapIdx i) n

/-- The total Navier–Stokes symbol `∑_i A_i`. -/
def halfLineSymbol (c : Fin 15 → ℕ → ℝ) (nu : ℝ) : ℕ → ℝ := fun n =>
  ∑ i : Fin 3, halfLineAlpha c nu i n

theorem halfLineFullData_advection (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) :
    (halfLineFullData c nu).advection i = diagOp (halfLineAlpha c nu i) := by
  simp only [NSFullData.advection, NSFullData.velocity, NSFullData.gradVelocity,
    NSFullData.lapVelocity, halfLineFullData, diagOp_comp, diagOp_sum, diagOp_real_smul,
    diagOp_sub]
  rfl

/-- **The full Navier–Stokes Hamiltonian of the half-line realization is a
tridiagonal (Jacobi) operator**, with couplings `-(i/2)(α_n + α_{n+1})` for the
total Navier–Stokes symbol `α`. -/
theorem halfLineFullData_hamiltonian (c : Fin 15 → ℕ → ℝ) (nu : ℝ) :
    (halfLineFullData c nu).hamiltonian = tridiagOp (nsCoupling (halfLineSymbol c nu)) := by
  have h : ∀ i : Fin 3,
      ((halfLineFullData c nu).mom i).comp ((halfLineFullData c nu).advection i)
        + ((halfLineFullData c nu).advection i).comp ((halfLineFullData c nu).mom i)
        = tridiagOp (nsCoupling (halfLineAlpha c nu i)) := by
    intro i
    rw [halfLineFullData_advection]
    exact weyl_momOp_diagOp _
  rw [NSFullData.hamiltonian, Finset.sum_congr rfl (fun i _ => h i), tridiagOp_sum]
  congr 1
  funext n
  simp only [nsCoupling, halfLineSymbol, Complex.ofReal_sum]
  rw [show (∑ i : Fin 3, ((halfLineAlpha c nu i n : ℝ) : ℂ))
        + (∑ i : Fin 3, ((halfLineAlpha c nu i (n + 1) : ℝ) : ℂ))
      = ∑ i : Fin 3, (((halfLineAlpha c nu i n : ℝ) : ℂ)
          + ((halfLineAlpha c nu i (n + 1) : ℝ) : ℂ)) from Finset.sum_add_distrib.symm,
    Finset.mul_sum]

/-- **The headline.**  The full (untruncated) Navier–Stokes Hamiltonian of the
half-line realization — unbounded modes, non-commuting momentum — is essentially
self-adjoint on the finite-mode domain of `ℓ²(ℕ)` as soon as the Navier–Stokes
symbol satisfies Carleman's growth condition. -/
theorem halfLineFull_hasZeroDeficiencyOn (c : Fin 15 → ℕ → ℝ) (nu : ℝ)
    (hcar : ¬ Summable fun n => 1 / ‖nsCoupling (halfLineSymbol c nu) n‖) :
    HasZeroDeficiencyOn (halfLineFullData c nu).D (halfLineFullData c nu).hamiltonian := by
  rw [halfLineFullData_hamiltonian]
  exact tridiag_hasZeroDeficiencyOn_of_carleman _ hcar

/-! ### A concrete unbounded instance: a linearly growing field -/

/-- The field modes of the linear instance: the viscous mode `u_{0,jj}` grows
linearly, every other mode vanishes. -/
noncomputable def linearMode (k : Fin 15) : ℕ → ℝ :=
  if k = nsLapIdx 0 then fun n => -((n : ℝ) + 1) else fun _ => 0

/-- The untruncated half-line Navier–Stokes data with a linearly growing viscous
mode and unit viscosity. -/
noncomputable def linearFullData : NSFullData L2N := halfLineFullData linearMode 1

theorem linearFullData_eq : linearFullData = halfLineFullData linearMode 1 := rfl

theorem linearFullData_symbol : halfLineSymbol linearMode 1 = fun m : ℕ => (m : ℝ) + 1 := by
  funext n
  simp only [halfLineSymbol, halfLineAlpha, linearMode, Fin.sum_univ_three]
  norm_num [nsVelIdx, nsGradIdx, nsLapIdx, Fin.ext_iff]

theorem norm_nsCoupling_linear (n : ℕ) :
    ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ = ((n : ℝ) + 3 / 2) := by
  have h : ((((n : ℝ) + 1 : ℝ)) : ℂ) + (((((n + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ)
      = (((2 * (n : ℝ) + 3 : ℝ)) : ℂ) := by
    push_cast
    ring
  simp only [nsCoupling, h, norm_mul, norm_neg, norm_div, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 3)]
  norm_num
  ring

theorem not_summable_nsCoupling_linear :
    ¬ Summable fun n : ℕ => 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ := by
  intro hs
  have hle : ∀ n : ℕ, 1 / (((n : ℝ) + 2)) ≤ 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ := by
    intro n
    rw [norm_nsCoupling_linear]
    have h1 : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
    have h2 : (n : ℝ) + 3 / 2 ≤ (n : ℝ) + 2 := by linarith
    exact one_div_le_one_div_of_le h1 h2
  have hsum : Summable fun n : ℕ => 1 / (((n : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hs
  have hcast : (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) = fun n : ℕ => 1 / (((n : ℝ) + 2)) := by
    funext n; push_cast; ring
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).1 (by rw [hcast]; exact hsum))

/-- **A concrete unbounded, non-commuting, essentially self-adjoint full
Navier–Stokes Hamiltonian.** -/
theorem linearFull_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn linearFullData.D linearFullData.hamiltonian := by
  refine halfLineFull_hasZeroDeficiencyOn linearMode 1 ?_
  rw [linearFullData_symbol]
  exact not_summable_nsCoupling_linear

/-- The tridiagonal operator is unbounded as soon as its couplings are. -/
theorem tridiagOp_not_bounded (c : ℕ → ℂ) (hc : ∀ C : ℝ, ∃ n, C < ‖c n‖) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖tridiagOp c f‖ ≤ C * ‖f‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := hc C
  have hb := hC (basis (k + 1))
  rw [norm_basis, mul_one] at hb
  have hcoord : ‖(((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k‖ ≤
      ‖((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N)‖ :=
    lp.norm_apply_le_norm (by norm_num) _ k
  have hval : (((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k = c k := by
    rw [tridiagOp_basis_succ]
    simp [lp.single_apply]
  rw [hval] at hcoord
  have : ‖c k‖ ≤ C := le_trans hcoord hb
  exact absurd hk (not_lt.mpr this)

theorem linearFull_not_bounded :
    ¬ ∃ C : ℝ, ∀ f : linearFullData.D, ‖linearFullData.hamiltonian f‖ ≤ C * ‖f‖ := by
  have hham : (halfLineFullData linearMode 1).hamiltonian
      = tridiagOp (nsCoupling (fun m : ℕ => (m : ℝ) + 1)) := by
    rw [halfLineFullData_hamiltonian, linearFullData_symbol]
  have hnb : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ,
      ‖tridiagOp (nsCoupling (fun m : ℕ => (m : ℝ) + 1)) f‖ ≤ C * ‖f‖ := by
    refine tridiagOp_not_bounded _ fun C => ?_
    refine ⟨⌈|C|⌉₊, ?_⟩
    rw [norm_nsCoupling_linear]
    have hc : C ≤ |C| := le_abs_self C
    have hn : |C| ≤ (⌈|C|⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  rintro ⟨C, hC⟩
  exact hnb ⟨C, fun f => by rw [← hham]; exact hC f⟩

end HalfLine

end Carleman

end BookProof.NavierStokesFlow
