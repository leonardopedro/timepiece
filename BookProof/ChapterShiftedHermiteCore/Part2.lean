import Mathlib
import BookProof.ChapterHyperbolicQuadraticEsa
import BookProof.ChapterShiftedHermiteCore.Part1

/-!
# The translated, modulated Gauss–polynomial core of `L²(ℝᵈ)`

`BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial (product Hermite) core
`polyGaussCore = { p · e^{-‖x‖²/4} }` of `L²(ℝᵈ)` and proves it dense, and
`BookProof.ChapterHyperbolicQuadraticEsa` uses it to diagonalize the diagonal quadratic
Hamiltonians `H_c = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4)`.

This module builds the **phase-space translate** of that core: for a translation vector
`a ∈ ℝᵈ` and a wave vector `k ∈ ℝᵈ`,

`D_{a,k} = { x ↦ p(x − a) · e^{-‖x−a‖²/4} · e^{i⟨k,x⟩} : p ∈ ℂ[X₀,…,X_{d-1}] }`.

This is the image of `polyGaussCore` under the Weyl (phase-space translation) unitary
`f ↦ e^{i⟨k,x⟩} f(x − a)`, and it is the natural core for a quadratic Hamiltonian that has
been *completed to a square*: it is the Hermite core recentred at the classical
equilibrium `x = a` and boosted to the classical momentum `k`.

## What is proved

* `pgFunT`, `memLp_pgFunT`, `pgLpT`, `pgMapT`, `pgMapT_injective` — the translated,
  modulated Gauss–polynomial functions are square integrable and depend injectively on the
  polynomial;
* `inner_pgLpT` — the map is **isometric**: `⟪pgLpT a k p, pgLpT a k q⟫ = ⟪pgLp p, pgLp q⟫`
  (translation invariance of Lebesgue measure and `|e^{i⟨k,x⟩}| = 1`);
* `polyGaussCoreT`, `polyGaussCoreT_dense` — the resulting core is dense in `L²(ℝᵈ)`;
* `hermiteTLp`, `orthonormal_hermiteTLp`, `span_hermiteTLp`, `hermiteTLp_total` — the
  translated, modulated product Hermite functions are an orthonormal family spanning the
  core, and total in `L²(ℝᵈ)`;
* `coreEquivT`, `coreOpT` — the core coordinatized by polynomials, and operators on it
  given by operators on the polynomial coordinates;
* `mulXTPoly`, `momTPoly`, `pgFunT_mulXTPoly`, `pgFunT_momTPoly` — **the canonical pair in
  the translated frame**: on `D_{a,k}` multiplication by `xᵢ` is `Xᵢ + aᵢ` and the momentum
  `πᵢ = −i∂/∂xᵢ` is `momPolyᵢ + kᵢ` in the polynomial coordinates, the second identity
  being an honest statement about Mathlib's `deriv` along the `i`-th coordinate line.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedHermiteCore

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}
/-! ## The translated, modulated product Hermite functions -/

/-- The translated, modulated product Hermite function
`ψ_α(x − a) e^{i⟨k,x⟩}`, normalized in `L²`. -/
def hermiteTLp (a k : Vd d) (α : Fin d →₀ ℕ) : L2d d :=
  ((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • pgLpT a k (hermiteMv α)

theorem inner_hermiteTLp (a k : Vd d) (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTLp a k α) (hermiteTLp a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by
  rw [hermiteTLp, hermiteTLp, hermiteMvLp, hermiteMvLp, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, inner_pgLpT]

theorem orthonormal_hermiteTLp (a k : Vd d) : Orthonormal ℂ (hermiteTLp (d := d) a k) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [inner_hermiteTLp]
  exact orthonormal_iff_ite.mp orthonormal_hermiteMvLp α β

theorem hermiteTLp_mem_coreT (a k : Vd d) (α : Fin d →₀ ℕ) :
    hermiteTLp a k α ∈ polyGaussCoreT a k :=
  Submodule.smul_mem _ _ (pgLpT_mem_coreT a k _)

/-- The translated, modulated Hermite functions span the translated, modulated core. -/
theorem span_hermiteTLp (a k : Vd d) :
    Submodule.span ℂ (Set.range (hermiteTLp (d := d) a k)) = polyGaussCoreT a k := by
  have hbase : Submodule.span ℂ
      (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (hermiteMv α)) = polyGaussCoreT a k := by
    have hrange : (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (hermiteMv α))
        = (pgMapT a k) '' (Set.range (hermiteMv (d := d))) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCoreT]
  rw [← hbase]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    change pgLpT a k (hermiteMv α) ∈ Submodule.span ℂ (Set.range (hermiteTLp (d := d) a k))
    have h : pgLpT a k (hermiteMv α) = ((hermiteMvNorm α : ℝ) : ℂ) • hermiteTLp a k α := by
      rw [hermiteTLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero α), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-- A vector orthogonal to the whole translated core vanishes. -/
theorem eq_zero_of_inner_coreT (a k : Vd d) (v : L2d d)
    (h : ∀ z ∈ polyGaussCoreT a k, (inner ℂ z v : ℂ) = 0) : v = 0 := by
  have hclosed : IsClosed {z : L2d d | (inner ℂ z v : ℂ) = 0} := by
    have hcont : Continuous fun z : L2d d => (inner ℂ z v : ℂ) := by fun_prop
    exact isClosed_eq hcont continuous_const
  have hsub : (Set.univ : Set (L2d d)) ⊆ {z : L2d d | (inner ℂ z v : ℂ) = 0} := by
    rw [← (polyGaussCoreT_dense a k).closure_eq]
    exact hclosed.closure_subset_iff.mpr h
  exact inner_self_eq_zero.mp (hsub (Set.mem_univ v))

/-- **The translated, modulated Hermite functions are total.** -/
theorem hermiteTLp_total (a k : Vd d) (v : L2d d)
    (h : ∀ α, (inner ℂ (hermiteTLp (d := d) a k α) v : ℂ) = 0) : v = 0 := by
  refine eq_zero_of_inner_coreT a k v fun z hz => ?_
  rw [← span_hermiteTLp a k] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨α, rfl⟩ := hz; exact h α
  | zero => simp
  | add z z' _ _ ihz ihz' => rw [inner_add_left, ihz, ihz']; ring
  | smul r z _ ih => rw [inner_smul_left, ih]; ring

/-! ## The core coordinatized by polynomials -/

/-- The translated, modulated core, coordinatized by polynomials. -/
def coreEquivT (a k : Vd d) : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] (polyGaussCoreT a k) :=
  LinearEquiv.ofInjective (pgMapT a k) (pgMapT_injective a k)

theorem coreEquivT_coe (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquivT a k p : polyGaussCoreT a k) : L2d d) = pgLpT a k p := rfl

/-- An operator on the translated core, given by an operator on the polynomial
coordinates. -/
def coreOpT (a k : Vd d) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    (polyGaussCoreT a k) →ₗ[ℂ] (polyGaussCoreT a k) :=
  (coreEquivT a k).toLinearMap ∘ₗ T ∘ₗ (coreEquivT a k).symm.toLinearMap

theorem coreOpT_coreEquivT (a k : Vd d) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : coreOpT a k T (coreEquivT a k p) = coreEquivT a k (T p) := by
  simp [coreOpT]

theorem coreOpT_coe (a k : Vd d) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ((coreOpT a k T (coreEquivT a k p) : polyGaussCoreT a k) : L2d d) = pgLpT a k (T p) := by
  rw [coreOpT_coreEquivT, coreEquivT_coe]

/-! ## The canonical pair in the translated, modulated frame -/

theorem pgFunT_apply_add (a k : Vd d) (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (p + q) x = pgFunT a k p x + pgFunT a k q x :=
  congrFun (pgFunT_add a k p q) x

theorem pgFunT_apply_smul (a k : Vd d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (c • p) x = c * pgFunT a k p x :=
  congrFun (pgFunT_smul a k c p) x

/-- The phase along the `i`-th coordinate line. -/
theorem phaseArg_sec (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseArg k (sec i x t) = phaseArg k x + k i * (t - x i) := by
  classical
  have hterm : ∀ j : Fin d, k j * (sec i x t) j
      = k j * x j + (if j = i then k i * (t - x i) else 0) := by
    intro j
    rw [sec_apply]
    by_cases hj : j = i
    · subst hj; simp; ring
    · simp [hj]
  rw [phaseArg, phaseArg, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  simp

theorem phaseFun_sec (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseFun k (sec i x t)
      = phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by
  rw [phaseFun, phaseFun, phaseArg_sec, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The derivative of the phase along the `i`-th coordinate line. -/
theorem hasDerivAt_phaseFun_sec (k x : Vd d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => phaseFun k (sec i x t))
      (phaseFun k x * (Complex.I * ((k i : ℝ) : ℂ))) (x i) := by
  have hlin : HasDerivAt
      (fun z : ℂ => Complex.I * (((k i : ℝ) : ℂ) * (z - ((x i : ℝ) : ℂ))))
      (Complex.I * ((k i : ℝ) : ℂ)) (((x i : ℝ)) : ℂ) := by
    simpa using
      ((((hasDerivAt_id (((x i : ℝ)) : ℂ)).sub_const (((x i : ℝ)) : ℂ)).const_mul
        (((k i : ℝ) : ℂ))).const_mul Complex.I)
  have hE : HasDerivAt
      (fun z : ℂ => Complex.exp (Complex.I * (((k i : ℝ) : ℂ) * (z - ((x i : ℝ) : ℂ)))))
      (Complex.I * ((k i : ℝ) : ℂ)) (((x i : ℝ)) : ℂ) := by
    simpa using hlin.cexp
  have hR := hE.comp_ofReal (z := x i)
  have hfun : (fun t : ℝ =>
        Complex.exp (Complex.I * (((k i : ℝ) : ℂ) * (((t : ℝ) : ℂ) - ((x i : ℝ) : ℂ)))))
      = fun t : ℝ => Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by
    funext t
    congr 2
    push_cast
    ring
  rw [hfun] at hR
  have hmul := hR.const_mul (phaseFun k x)
  have hfun2 : (fun t : ℝ =>
        phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)))
      = fun t : ℝ => phaseFun k (sec i x t) := by
    funext t
    rw [phaseFun_sec]
  rwa [hfun2] at hmul

/-- **The derivative of a translated, modulated Gauss–polynomial along a coordinate line.**
The translation shifts the polynomial coordinate, the modulation adds `i kᵢ`. -/
theorem hasDerivAt_pgFunT_sec (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => pgFunT a k p (sec i x t))
      (pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x) (x i) := by
  have hsec : ∀ t : ℝ, sec i x t - a = sec i (x - a) (t - a i) := by
    intro t
    ext j
    by_cases h : j = i <;> simp [sec_apply, h]
  have h1 : HasDerivAt (fun t : ℝ => pgFun p (sec i x t - a))
      (pgFun (dPoly i p) (x - a)) (x i) := by
    have hbase := hasDerivAt_pgFun_sec i p (x - a)
    have hpt : (x - a) i = x i - a i := by simp
    rw [hpt] at hbase
    have hcomp := HasDerivAt.comp_sub_const (x i) (a i) hbase
    have hfun : (fun t : ℝ => pgFun p (sec i (x - a) (t - a i)))
        = fun t : ℝ => pgFun p (sec i x t - a) := by
      funext t
      rw [hsec]
    rw [hfun] at hcomp
    simpa [dPoly_apply] using hcomp
  have h2 := hasDerivAt_phaseFun_sec k x i
  have hprod := h1.mul h2
  simp only [Pi.mul_def, sec_self] at hprod
  have hval : (fun t : ℝ => pgFun p (sec i x t - a) * phaseFun k (sec i x t))
      = fun t : ℝ => pgFunT a k p (sec i x t) := by
    funext t
    rw [pgFunT]
  rw [hval] at hprod
  have hsimp : pgFun (dPoly i p) (x - a) * phaseFun k x
      + pgFun p (x - a) * (phaseFun k x * (Complex.I * ((k i : ℝ) : ℂ)))
      = pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x := by
    rw [pgFunT, pgFunT]
    ring
  rwa [hsimp] at hprod

theorem deriv_pgFunT_sec (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i)
      = pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x :=
  (hasDerivAt_pgFunT_sec a k i p x).deriv

/-- **Multiplication by the coordinate `xᵢ` in the translated frame**: `Xᵢ + aᵢ`. -/
def mulXTPoly (a : Vd d) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  mulXPoly i + ((a i : ℝ) : ℂ) • LinearMap.id

/-- **The momentum `πᵢ = −i∂ᵢ` in the translated, modulated frame**: `momPolyᵢ + kᵢ`. -/
def momTPoly (k : Vd d) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  momPoly i + ((k i : ℝ) : ℂ) • LinearMap.id

@[simp] theorem mulXTPoly_apply (a : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXTPoly a i p = X i * p + ((a i : ℝ) : ℂ) • p := rfl

@[simp] theorem momTPoly_apply (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momTPoly k i p = momPoly i p + ((k i : ℝ) : ℂ) • p := rfl

/-- **The position operator is multiplication by the coordinate**, pointwise, on the
translated core. -/
theorem pgFunT_mulXTPoly (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (mulXTPoly a i p) x = ((x i : ℝ) : ℂ) * pgFunT a k p x := by
  rw [mulXTPoly_apply, pgFunT_apply_add, pgFunT_apply_smul]
  have hx : pgFunT a k (X i * p) x = (((x - a) i : ℝ) : ℂ) * pgFunT a k p x := by
    rw [pgFunT, pgFunT]
    have := posOp_apply_eq_mul i p (x - a)
    rw [mulXPoly_apply] at this
    rw [this]
    ring
  rw [hx]
  have hxa : ((x - a) i : ℝ) = x i - a i := by simp
  rw [hxa]
  push_cast
  ring

/-- **The momentum operator is the derivative**, pointwise, on the translated, modulated
core: `momTPoly k i` is `−i` times Mathlib's `deriv` along the `i`-th coordinate line. -/
theorem pgFunT_momTPoly (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (momTPoly k i p) x
      = -Complex.I * deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i) := by
  rw [deriv_pgFunT_sec, momTPoly_apply, pgFunT_apply_add, pgFunT_apply_smul,
    momPoly_apply' i p, pgFunT_apply_smul]
  rw [← dPoly_apply]
  linear_combination (((k i : ℝ) : ℂ) * pgFunT a k p x) * Complex.I_mul_I

end

end BookProof.ShiftedHermiteCore
