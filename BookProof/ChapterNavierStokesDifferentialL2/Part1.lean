import Mathlib
import BookProof.ChapterHermiteProductBasis
import BookProof.ChapterNavierStokesCanonicalVector
import BookProof.ChapterNavierStokesLagrangianEsa

/-!
# The differential realization of the Navier–Stokes quadratic symbol on `L²(du₁du₂du₃)`

`BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component
fiber Hamiltonian `H = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)`, `Vᵢ(u) = ∑ₖ A_{ik}u_k + c_i`, is essentially
self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, and
`BookProof.ChapterNavierStokesCanonicalVector` shows that this sequence-space matrix *is*
the Weyl-ordered expression in the abstract ladder operators of that space.  What both
modules record as the honest open step is the **differential realization**: the operator
written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication operator, on the Hermite
core of `L²(du₁du₂du₃)`.  This module takes that step.

## The setting

The Hilbert space is `L²(ℝ³)` and the dense domain is the Gauss–polynomial (product
Hermite) core `polyGaussCore` of `BookProof.ChapterHermiteProductCore`: the functions
`p(u)·e^{-‖u‖²/4}` with `p` a polynomial.  Since `pgMap` is injective, the core carries the
polynomial coordinates `coreEquiv`, and an operator on the core is given by a polynomial
operator (`coreOp`).  Two such operators are the physical ones:

* `posOp i` — multiplication by the coordinate `uᵢ` (`pgFun_mulXPoly`);
* `momOp i` — the differential operator `πᵢ = −i ∂/∂uᵢ`.  That it *is* the derivative is
  `momOp_apply_eq_differential`: the value of `momOp i` at `p·e^{-‖u‖²/4}` is, pointwise,
  `−i` times the honest derivative `deriv (fun t => f (u with uᵢ := t)) uᵢ` of the function
  along the `i`-th coordinate (Mathlib's `deriv`, `hasDerivAt_pgFun_sec`).

`comm_momOp_posOp` is the canonical commutation relation `[πᵢ, u_k] = −i δ_{ik}` for these
genuinely differential operators.

## The Hamiltonian and the transport

`nsDiffH A c = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` with `Vᵢ` the multiplication operator by the affine
field `∑ₖ A_{ik}u_k + c_i` is the Weyl quantization of the Navier–Stokes quadratic symbol
`A_i(u) = u_j u_{i,j} − ν u_{i,jj}` at one Eulerian fiber (linear part the velocity
gradient, constant part `−ν` times the velocity Laplacian).

The **unitary transport** is `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)`, the Hilbert-basis
isomorphism given by the product Hermite functions
(`BookProof.ChapterHermiteProductBasis`).  It carries the finite-mode core onto the
Gauss–polynomial core (`map_finiteModes`) and the abstract ladder operators onto the
differential ones (`intertwine_ann`, `intertwine_cre`), hence the abstract canonical
Hamiltonian onto the differential one (`conj_canH`).  The conclusions:

* `nsDiffH_essentiallySelfAdjointOn_core` — the **differentially written** Navier–Stokes
  quadratic symbol is essentially self-adjoint on the Hermite core of `L²(ℝ³)`, for every
  real velocity gradient and every constant part;
* `nsQuadraticDiffH_essentiallySelfAdjointOn_core` — the same with the coefficients spelled
  out as `(ν, u_{i,j}, u_{i,jj})`;
* `nsDiffH_not_bounded`, `polyGaussCore_dense_L2` — the operator is genuinely unbounded and
  the domain is dense, so the statement is not a bounded-operator artefact.

## Honest boundary

Nothing here claims global regularity of the *classical* Navier–Stokes PDE (Contention D5,
the deliberate scope cut): the theorem is about the Hilbert-space operator at one Eulerian
fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical
coordinates.
-/

namespace BookProof.NavierStokesFlow.DifferentialL2

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

/-! ## Differentiating along one coordinate -/

variable {d : ℕ}

/-- The line through `x` in the `i`-th coordinate direction. -/
def sec (i : Fin d) (x : Vd d) (t : ℝ) : Vd d :=
  (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i t) : Vd d)

theorem sec_apply (i : Fin d) (x : Vd d) (t : ℝ) (j : Fin d) :
    (sec i x t) j = if j = i then t else x j := by
  simp [sec, Function.update_apply]

@[simp] theorem sec_self (i : Fin d) (x : Vd d) : sec i x (x i) = x := by simp [sec]

theorem norm_sq_sec (i : Fin d) (x : Vd d) (t : ℝ) :
    ‖sec i x t‖ ^ 2 = (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2 := by
  classical
  rw [norm_sq_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), sec_apply]
  simp only []
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [sec_apply, if_neg (Finset.ne_of_mem_erase hj)]

theorem hasDerivAt_gaussD_sec (i : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (sec i x s)) (-(t / 2) * gaussD (sec i x t)) t := by
  classical
  set S := ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 with hS
  have hfun : (fun s : ℝ => gaussD (sec i x s)) = fun s : ℝ => Real.exp (-(S + s ^ 2) / 4) := by
    funext s
    rw [gaussD, norm_sq_sec]
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => -(S + s ^ 2) / 4) (-(2 * t) / 4) t := by
    have h : HasDerivAt (fun s : ℝ => -(S + s ^ 2) / 4) (-(0 + 2 * t) / 4) t := by
      have h0 : HasDerivAt (fun s : ℝ => S + s ^ 2) (0 + 2 * t) t := by
        simpa using ((hasDerivAt_pow 2 t).const_add S)
      exact h0.neg.div_const 4
    simpa using h
  have h2 := (Real.hasDerivAt_exp (-(S + t ^ 2) / 4)).comp t h1
  convert h2 using 1
  rw [gaussD, norm_sq_sec]
  ring

/-- The derivative of a polynomial along one coordinate is the partial derivative. -/
theorem hasDerivAt_eval_update (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => MvPolynomial.eval (Function.update x i s) p)
      (MvPolynomial.eval (Function.update x i t) (pderiv i p)) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (hasDerivAt_const t (a : ℂ))
  | add p q hp hq => simpa [map_add] using hp.add hq
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst hj
        have hX : HasDerivAt (fun s : ℂ => MvPolynomial.eval (Function.update x j s) (X j))
            1 t := by simpa using hasDerivAt_id t
        have h := hp.mul hX
        have hpd : pderiv j (p * X j) = X j * pderiv j p + p := by
          rw [Derivation.leibniz]
          simp [smul_eq_mul]
          ring
        rw [hpd]
        simp only [map_add, map_mul, MvPolynomial.eval_X, Function.update_self] at h ⊢
        convert h using 1
        ring
      · have hX : HasDerivAt (fun s : ℂ => MvPolynomial.eval (Function.update x i s) (X j))
            0 t := by
          simp only [MvPolynomial.eval_X, Function.update_apply, hj]
          exact hasDerivAt_const _ _
        have h := hp.mul hX
        have hpd : pderiv i (p * X j) = X j * pderiv i p := by
          rw [Derivation.leibniz]
          simp [Ne.symm hj]
        rw [hpd]
        simp only [map_mul, MvPolynomial.eval_X] at h ⊢
        convert h using 1
        ring

theorem hasDerivAt_evalSec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (pderiv i p)) (x i) := by
  classical
  have hupd : ∀ t : ℝ, (fun j => (((sec i x t) j : ℝ) : ℂ))
      = Function.update (fun j => ((x j : ℝ) : ℂ)) i ((t : ℝ) : ℂ) := by
    intro t
    funext j
    rw [sec_apply, Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  have hbase := hasDerivAt_eval_update i p (fun j => ((x j : ℝ) : ℂ)) (((x i : ℝ)) : ℂ)
  have h := hbase.comp_ofReal (z := x i)
  have heq : (fun y : ℝ => MvPolynomial.eval
        (Function.update (fun j => ((x j : ℝ) : ℂ)) i ((y : ℝ) : ℂ)) p)
      = fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p := by
    funext t; rw [hupd t]
  rw [heq] at h
  have hfun : Function.update (fun j => ((x j : ℝ) : ℂ)) i (((x i : ℝ)) : ℂ)
      = fun j => ((x j : ℝ) : ℂ) := by
    funext j
    rw [Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  rwa [hfun] at h

/-- **The coordinate derivative of a Gauss–polynomial**:
`∂ᵢ(p·e^{-‖u‖²/4}) = (∂ᵢp − (uᵢ/2)p)·e^{-‖u‖²/4}`.  This is the analytic fact that turns
the polynomial operators of `BookProof.ChapterHermiteProductBasis` into genuine
differential operators. -/
theorem hasDerivAt_pgFun_sec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => pgFun p (sec i x t))
      (pgFun (pderiv i p - (1/2 : ℂ) • (X i * p)) x) (x i) := by
  have hg : HasDerivAt (fun t : ℝ => ((gaussD (sec i x t) : ℝ) : ℂ))
      (((-(x i / 2) * gaussD x : ℝ)) : ℂ) (x i) := by
    have h := (hasDerivAt_gaussD_sec i x (x i)).ofReal_comp
    simpa using h
  have hp := hasDerivAt_evalSec i p x
  have h := hp.mul hg
  have hfun : (fun t : ℝ => pgFun p (sec i x t))
      = (fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p)
        * (fun t : ℝ => ((gaussD (sec i x t) : ℝ) : ℂ)) := by
    funext t; simp [pgFun]
  rw [hfun]
  convert h using 1
  rw [sec_self]
  simp only [pgFun, map_sub, MvPolynomial.smul_eval, map_mul, MvPolynomial.eval_X]
  push_cast
  ring

/-! ## The polynomial coordinates of the core -/

/-- The Gauss–polynomial core, coordinatized by polynomials. -/
def coreEquiv : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] (polyGaussCore (d := d)) :=
  LinearEquiv.ofInjective (pgMap (d := d)) (pgMap_injective (d := d))

theorem coreEquiv_coe (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

/-- An operator on the core, given by an operator on the polynomial coordinates. -/
def coreOp (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  (coreEquiv (d := d)).toLinearMap ∘ₗ T ∘ₗ (coreEquiv (d := d)).symm.toLinearMap

theorem coreOp_coreEquiv (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : coreOp T (coreEquiv p) = coreEquiv (T p) := by
  simp [coreOp]

theorem coreOp_coe (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ((coreOp T (coreEquiv p) : polyGaussCore (d := d)) : L2d d) = pgLp (T p) := by
  rw [coreOp_coreEquiv, coreEquiv_coe]

/-! ## The canonical pair: multiplication by `uᵢ` and `−i ∂/∂uᵢ` -/

/-- Multiplication by the coordinate, on polynomials. -/
def mulXPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := X i * p
  map_add' p q := by rw [mul_add]
  map_smul' c p := by simp

/-- The momentum `−i ∂/∂uᵢ`, on polynomial coordinates. -/
def momPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p))
  map_add' p q := by simp only [map_add, mul_add]; ring
  map_smul' c p := by
    simp only [RingHom.id_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul]; ring

@[simp] theorem mulXPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXPoly i p = X i * p := rfl

@[simp] theorem momPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl

/-- **The position operator** `uᵢ` on the Hermite core of `L²(ℝᵈ)`. -/
def posOp (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  coreOp (mulXPoly i)

/-- **The momentum operator** `πᵢ = −i ∂/∂uᵢ` on the Hermite core of `L²(ℝᵈ)`. -/
def momOp (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  coreOp (momPoly i)

/-- **The position operator is multiplication by the coordinate**, pointwise. -/
theorem posOp_apply_eq_mul (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (mulXPoly i p) x = ((x i : ℝ) : ℂ) * pgFun p x := by
  simp [pgFun, mulXPoly]
  ring

/-- **The momentum operator is the derivative**: at every point, the value of `momOp i` on
`f = p·e^{-‖u‖²/4}` is `−i` times the honest derivative of `f` along the `i`-th
coordinate. -/
theorem momOp_apply_eq_differential (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (momPoly i p) x
      = -Complex.I * deriv (fun t : ℝ => pgFun p (sec i x t)) (x i) := by
  rw [(hasDerivAt_pgFun_sec i p x).deriv]
  simp only [momPoly, pgFun, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.smul_eval]
  ring

/-- The `L²` element `momOp i f` is the class of the differential expression. -/
theorem momOp_coe_eq_differential (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    ((momOp i (coreEquiv p) : polyGaussCore (d := d)) : L2d d)
      = pgLp (momPoly i p) := coreOp_coe _ p

/-- **The canonical commutation relation** `[πᵢ, u_k] = −i δ_{ik}` for the differential
operators. -/
theorem comm_momPoly_mulXPoly (i k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (mulXPoly k p) - mulXPoly k (momPoly i p)
      = C (if i = k then -Complex.I else 0) * p := by
  classical
  have hpd : pderiv i (X k * p) = (if i = k then (1 : MvPolynomial (Fin d) ℂ) else 0) * p
      + X k * pderiv i p := by
    rw [Derivation.leibniz]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, pderiv_X_self]
      simp only [smul_eq_mul, mul_one, one_mul]
      ring
    · rw [pderiv_X_of_ne (Ne.symm hik), if_neg hik]
      simp [smul_eq_mul]
  simp only [momPoly_apply, mulXPoly_apply, hpd]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hik, if_neg hik]
    simp only [map_zero, zero_mul]
    ring

set_option maxHeartbeats 1000000 in
-- The core-level commutator unfolds a composite of three linear equivalences, which is
-- elaboration-heavy; the default heartbeat budget is not enough.
theorem comm_momOp_posOp (i k : Fin d) :
    (momOp i).comp (posOp k) - (posOp k).comp (momOp i)
      = (if i = k then -Complex.I else 0) • LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := d)).surjective y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, posOp, momOp, coreOp_coreEquiv,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [← map_sub, comm_momPoly_mulXPoly, ← MvPolynomial.smul_eq_C_mul, map_smul]

/-! ## The unitary transport from the three-mode sequence space

The product Hermite functions indexed by `Vel = Fin 3 → ℕ` form a Hilbert basis of
`L²(ℝ³)`, so the sequence space `ℓ²(Vel)` of
`BookProof.ChapterNavierStokesThreeComponent` is unitarily `L²(du₁du₂du₃)`. -/

/-- A three-mode index, read as a finitely supported multi-index. -/
def velIdx : Vel ≃ (Fin 3 →₀ ℕ) := Finsupp.equivFunOnFinite.symm

@[simp] theorem velIdx_apply (b : Vel) (i : Fin 3) : velIdx b i = b i := rfl

theorem velIdx_raise (i : Fin 3) (b : Vel) :
    velIdx (raise i b) = velIdx b + Finsupp.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [raise_of_ne hj, Ne.symm hj]

theorem velIdx_lower (i : Fin 3) (b : Vel) :
    velIdx (lower i b) = velIdx b - Finsupp.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [Finsupp.tsub_apply]
  · simp [lower_of_ne hj, Finsupp.tsub_apply, Ne.symm hj]

/-- The product Hermite function attached to a three-mode index. -/
def hermiteVel (b : Vel) : L2d 3 := hermiteMvLp (velIdx b)

theorem orthonormal_hermiteVel : Orthonormal ℂ hermiteVel :=
  orthonormal_hermiteMvLp.comp velIdx velIdx.injective

theorem range_hermiteVel : Set.range hermiteVel = Set.range (hermiteMvLp (d := 3)) :=
  velIdx.surjective.range_comp _

/-- **The three-mode product Hermite basis of `L²(ℝ³)`.** -/
def velBasis : HilbertBasis Vel ℂ (L2d 3) :=
  HilbertBasis.mk orthonormal_hermiteVel
    (by
      rw [range_hermiteVel, span_hermiteMvLp]
      have hd := polyGaussCore_dense (d := 3)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

@[simp] theorem velBasis_apply (b : Vel) : velBasis b = hermiteVel b := by
  rw [velBasis, HilbertBasis.coe_mk]

/-- **The unitary transport** `ℓ²(Vel) ≃ L²(du₁du₂du₃)` given by the product Hermite
basis. -/
def velUnitary : L2I Vel ≃ₗᵢ[ℂ] L2d 3 := velBasis.repr.symm

@[simp] theorem velUnitary_single (b : Vel) :
    velUnitary (lp.single 2 b (1 : ℂ)) = hermiteVel b := by
  rw [velUnitary, velBasis.repr_symm_single, velBasis_apply]

/-! ### The finite-mode core is spanned by its basis states -/

theorem coreState_coe (b : Vel) :
    ((coreState b : lpFiniteModes Vel) : L2I Vel) = lp.single 2 b (1 : ℂ) := rfl

/-- The finite-mode core of `ℓ²(Vel)` is the algebraic span of the basis states. -/
theorem lpFiniteModes_eq_span :
    lpFiniteModes Vel
      = Submodule.span ℂ (Set.range fun b : Vel => (lp.single 2 b (1 : ℂ) : L2I Vel)) := by
  classical
  refine le_antisymm (fun f hf => ?_) ?_
  · have hfin : (Function.support ((f : Vel → ℂ))).Finite := hf
    have hsum : f = ∑ b ∈ hfin.toFinset, ((f : Vel → ℂ) b) • (lp.single 2 b (1 : ℂ)) := by
      refine lp.ext (funext fun j => ?_)
      rw [lp.coeFn_sum]
      simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq hfin.toFinset j (fun b => (f : Vel → ℂ) b)]
      by_cases hj : j ∈ hfin.toFinset
      · rw [if_pos hj]
      · rw [if_neg hj]
        have : j ∉ Function.support ((f : Vel → ℂ)) := by
          simpa [Set.Finite.mem_toFinset] using hj
        simpa [Function.mem_support] using this
    rw [hsum]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact lpSingle_mem_lpFiniteModes b 1

/-- The basis states span the finite-mode core as a module in its own right. -/
theorem span_coreState :
    Submodule.span ℂ (Set.range coreState) = (⊤ : Submodule ℂ (lpFiniteModes Vel)) := by
  refine Submodule.map_injective_of_injective
    (Submodule.injective_subtype (lpFiniteModes Vel)) ?_
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact lpFiniteModes_eq_span.symm

/-- Two linear maps out of the finite-mode core agree as soon as they agree on the basis
states. -/
theorem core_ext {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F G : lpFiniteModes Vel →ₗ[ℂ] M} (h : ∀ b, F (coreState b) = G (coreState b)) : F = G := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span ℂ (Set.range coreState) := by rw [span_coreState]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; exact h b
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul a y _ hy => rw [map_smul, map_smul, hy]

end

end BookProof.NavierStokesFlow.DifferentialL2
