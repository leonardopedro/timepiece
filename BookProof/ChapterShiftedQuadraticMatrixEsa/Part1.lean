import Mathlib
import BookProof.ChapterShiftedQuadraticEsa
import BookProof.ChapterQuadraticRotationEsa

/-!
# The indefinite quadratic Hamiltonian **with cross terms** and an unbounded
first-order perturbation

`BookProof.ChapterQuadraticRotationPerturbed` proves that for a **positive definite** real
symmetric matrix `A` and arbitrary real `b, b'` the operator
`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, `H_A = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4)`, is essentially
self-adjoint on the Gauss–polynomial core; positive definiteness is used exactly once, to
produce the relative bound, and the indefinite case was the recorded boundary.
`BookProof.ChapterShiftedQuadraticEsa` removes the sign condition for **diagonal** weights,
by completing the square on a translated, modulated core.

This module combines the two: for **every** real symmetric **invertible** `A` — no sign
condition, so the signature may be elliptic, hyperbolic or anything in between — and
arbitrary real `b, b'`, the operator

`H = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`,  `πᵢ = −i∂/∂xᵢ`,

is symmetric and essentially self-adjoint on the translated, modulated Gauss–polynomial
core `D_{a,k}` of `BookProof.ChapterShiftedHermiteCore`, where `a = −2A⁻¹b` and
`k = −A⁻¹b'/2` are the classical equilibrium position and momentum.

The mechanism is again completing the square, now in matrix form:

`∑_{p,q} A_{pq}((π_p + k_p)(π_q + k_q) + (x_p + a_p)(x_q + a_q)/4)
   + ∑ᵢ (bᵢ(xᵢ + aᵢ) + b'ᵢ(πᵢ + kᵢ)) = H_A + const`

as soon as `A a = −2b` and `A k = −b'/2`, and `H_A` is diagonal on the *rotated* Hermite
polynomials, so the *translated, modulated, rotated* Hermite functions are an orthonormal
total family of eigenvectors of `H` in `D_{a,k}`.  No relative bound and no domination is
used; the only hypothesis is invertibility of `A`, which is exactly what is needed to
solve for the classical equilibrium.

## What is proved

* `quadPolyMatT`, `foTPoly`, `shiftedHMatPoly` — the Hamiltonian in the polynomial
  coordinates of the translated, modulated frame;
* `quadPolyMatT_apply_expand` — the expansion of the quadratic part into `H_A`, a
  first-order part and a constant;
* `shiftedHMatPoly_eq_quadPolyMat` — **completing the square** in matrix form;
* `hermiteTRLp`, `orthonormal_hermiteTRLp`, `span_hermiteTRLp`, `hermiteTRLp_total` — the
  translated, modulated, rotated product Hermite functions are an orthonormal family whose
  span is the core and which is total in `L²(ℝᵈ)`;
* `shiftedHMatOp`, `shiftedHMatOp_hermiteTRLp` — the operator and its diagonal action;
* `shiftedHMatOp_symmetric`, `shiftedHMatOp_essentiallySelfAdjoint` — **the headline**, for
  every real symmetric invertible `A` of arbitrary signature;
* `shiftedHMatOp_not_bounded`, `shiftedHMatCore_dense` — non-vacuity: the operator is
  genuinely unbounded (an invertible `A` has no zero eigenvalue) and its domain is dense;
* `shiftedHMatOp_stone_flow` — the resulting complete unitary Schrödinger flow;
* `wave_rotated_linear_essentiallySelfAdjoint` — the corollary: the rotated Minkowski
  quadratic (indefinite, with cross terms) plus an arbitrary constant external field and
  boost.

## Honest boundary

Invertibility of `A` is used exactly once, to solve `A a = −2b`, `A k = −b'/2`; if `A` is
singular and `b` has a component in the kernel the square cannot be completed (the motion
is free in that direction).  Nothing here claims a general Faris–Lavine potential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedQuadraticMatrix

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. The Hamiltonian in the translated, modulated polynomial coordinates -/

/-- The general quadratic form `∑_{p,q} A_{pq}(π_pπ_q + x_px_q/4)` in the translated,
modulated frame. -/
def quadPolyMatT (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ p, ∑ q, ((A p q : ℝ) : ℂ) •
    ((momTPoly k p).comp (momTPoly k q) + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q)))

/-- The first-order term `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` in the translated, modulated frame. -/
def foTPoly (a k : Vd d) (b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, (((b i : ℝ) : ℂ) • mulXTPoly a i + ((b' i : ℝ) : ℂ) • momTPoly k i)

/-- The full inhomogeneous quadratic Hamiltonian in the translated, modulated frame. -/
def shiftedHMatPoly (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  quadPolyMatT a k A + foTPoly a k b b'

/-- The `(p, q)` term of the translated quadratic form, expanded. -/
theorem quadTermT_apply (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d)
    (f : MvPolynomial (Fin d) ℂ) :
    ((A p q : ℝ) : ℂ) • ((momTPoly k p).comp (momTPoly k q) f
        + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q) f))
      = ((A p q : ℝ) : ℂ) • (momPoly p (momPoly q f) + (1/4 : ℂ) • (X p * (X q * f)))
        + ((A p q * k q : ℝ) : ℂ) • momPoly p f + ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f) + ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by
  simp only [LinearMap.comp_apply, momTPoly_apply, mulXTPoly_apply, map_add, map_smul,
    mul_add]
  push_cast
  module

theorem quadPolyMatT_apply_expand (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ)
    (f : MvPolynomial (Fin d) ℂ) :
    quadPolyMatT a k A f
      = quadPolyMat A f
        + ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
        + ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
        + ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by
  rw [quadPolyMatT]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    quadTermT_apply a k A p q f]
  simp only [Finset.sum_add_distrib]
  rw [quadPolyMat_apply]

theorem foTPoly_apply_expand (a k : Vd d) (b b' : Fin d → ℝ) (f : MvPolynomial (Fin d) ℂ) :
    foTPoly a k b b' f
      = ∑ i, ((b i : ℝ) : ℂ) • (X i * f) + ∑ i, ((b' i : ℝ) : ℂ) • momPoly i f
        + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f := by
  have hterm : ∀ i : Fin d,
      ((b i : ℝ) : ℂ) • mulXTPoly a i f + ((b' i : ℝ) : ℂ) • momTPoly k i f
        = ((b i : ℝ) : ℂ) • (X i * f) + ((b' i : ℝ) : ℂ) • momPoly i f
          + ((b i * a i + b' i * k i : ℝ) : ℂ) • f := by
    intro i
    simp only [mulXTPoly_apply, momTPoly_apply, smul_add, smul_smul]
    push_cast
    module
  rw [foTPoly]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul]
  push_cast
  ring

/-! ## 2. Completing the square -/

/-- The constant produced by completing the square, `(⟨a, b⟩ + ⟨b', k⟩)/2`. -/
def matShiftConst (a k : Vd d) (b b' : Fin d → ℝ) : ℝ :=
  (∑ i, a i * b i + ∑ i, b' i * k i) / 2

/-- **Completing the square, in matrix form.**  If `a` and `k` solve the classical
equilibrium equations `A a = −2b` and `A k = −b'/2`, then in the frame translated by `a`
and boosted by `k` the first-order term disappears and the Hamiltonian becomes `H_A` plus a
real constant. -/
theorem shiftedHMatPoly_eq_quadPolyMat (a k : Vd d) {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : ∀ i j, A i j = A j i) (b b' : Fin d → ℝ)
    (ha : ∀ i, ∑ j, A i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2)
    (f : MvPolynomial (Fin d) ℂ) :
    shiftedHMatPoly a k A b b' f
      = quadPolyMat A f + ((matShiftConst a k b b' : ℝ) : ℂ) • f := by
  classical
  have hS1 : ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
      = ∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h : ∑ q, ((A p q * k q : ℝ) : ℂ) = ((-(b' p) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, hk p]
    rw [← Finset.sum_smul, h]
  have hS2 : ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
      = ∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h : ∑ p, ((A p q * k p : ℝ) : ℂ) = ((-(b' q) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, ← hk q]
      exact congrArg _ (Finset.sum_congr rfl fun p _ => by rw [hsym p q])
    rw [← Finset.sum_smul, h]
  have hS3 : ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
      = ∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h : ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) = ((-(b p) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum]
      congr 1
      rw [← Finset.sum_div, ha p]
      ring
    rw [← Finset.sum_smul, h]
  have hS4 : ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
      = ∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h : ∑ p, ((A p q * a p / 4 : ℝ) : ℂ) = ((-(b q) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum]
      congr 1
      rw [← Finset.sum_div]
      have hrow : ∑ p, A p q * a p = -2 * b q := by
        rw [← ha q]
        exact Finset.sum_congr rfl fun p _ => by rw [hsym p q]
      rw [hrow]
      ring
    rw [← Finset.sum_smul, h]
  have hsum : ∑ p, ∑ q, A p q * (k p * k q + a p * a q / 4)
      = -(matShiftConst a k b b') := by
    have hstep : ∀ p : Fin d, ∑ q, A p q * (k p * k q + a p * a q / 4)
        = -(1/2) * (a p * b p) + -(1/2) * (b' p * k p) := by
      intro p
      have hexp : ∑ q, A p q * (k p * k q + a p * a q / 4)
          = k p * (∑ q, A p q * k q) + (a p * (∑ q, A p q * a q)) / 4 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
      rw [hexp, hk p, ha p]
      ring
    rw [Finset.sum_congr rfl fun p _ => hstep p, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, matShiftConst]
    ring
  have hS5 : ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f
      = ((-(matShiftConst a k b b') : ℝ) : ℂ) • f := by
    simp only [← Finset.sum_smul]
    congr 1
    have hcast : (∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ))
        = ((∑ p, ∑ q, A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, hsum]
  have hmom : (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
      + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
      + (∑ i, ((b' i : ℝ) : ℂ) • momPoly i f) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add]
    norm_num
  have hx : (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
      + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
      + (∑ i, ((b i : ℝ) : ℂ) • (X i * f)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add]
    norm_num
  have hconst : ((-(matShiftConst a k b b') : ℝ) : ℂ) • f
      + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f
      = ((matShiftConst a k b b' : ℝ) : ℂ) • f := by
    rw [← add_smul, ← Complex.ofReal_add]
    congr 2
    rw [matShiftConst]
    have hsplit : ∑ i, (b i * a i + b' i * k i)
        = (∑ i, a i * b i) + ∑ i, b' i * k i := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    ring
  rw [shiftedHMatPoly, LinearMap.add_apply, quadPolyMatT_apply_expand, foTPoly_apply_expand,
    hS1, hS2, hS3, hS4, hS5]
  rw [show quadPolyMat A f
        + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
        + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
        + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
        + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
        + ((-(matShiftConst a k b b') : ℝ) : ℂ) • f
        + ((∑ i, ((b i : ℝ) : ℂ) • (X i * f)) + (∑ i, ((b' i : ℝ) : ℂ) • momPoly i f)
            + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f)
      = quadPolyMat A f
        + ((∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
            + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
            + (∑ i, ((b' i : ℝ) : ℂ) • momPoly i f))
        + ((∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
            + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
            + (∑ i, ((b i : ℝ) : ℂ) • (X i * f)))
        + (((-(matShiftConst a k b b') : ℝ) : ℂ) • f
            + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f) from by abel]
  rw [hmom, hx, hconst]
  abel

/-! ## 3. The translated, modulated, rotated Hermite functions -/

/-- The translated, modulated, rotated product Hermite function, normalized in `L²`. -/
def hermiteTRLp (O : Matrix (Fin d) (Fin d) ℝ) (a k : Vd d) (α : Fin d →₀ ℕ) : L2d d :=
  ((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • pgLpT a k (rotPoly O (hermiteMv α))

theorem inner_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTRLp O a k α) (hermiteTRLp O a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by
  rw [hermiteTRLp, hermiteTRLp, hermiteMvLp, hermiteMvLp, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, inner_pgLpT, inner_pgLp_rotPoly hO]

theorem orthonormal_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (a k : Vd d) : Orthonormal ℂ (hermiteTRLp (d := d) O a k) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [inner_hermiteTRLp hO]
  exact orthonormal_iff_ite.mp orthonormal_hermiteMvLp α β

theorem hermiteTRLp_mem_coreT (O : Matrix (Fin d) (Fin d) ℝ) (a k : Vd d) (α : Fin d →₀ ℕ) :
    hermiteTRLp O a k α ∈ polyGaussCoreT a k :=
  Submodule.smul_mem _ _ (pgLpT_mem_coreT a k _)

theorem span_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) :
    Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k)) = polyGaussCoreT a k := by
  have hbase : Submodule.span ℂ
      (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (rotPoly O (hermiteMv α)))
      = polyGaussCoreT a k := by
    have hrange : (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (rotPoly O (hermiteMv α)))
        = ((pgMapT a k).comp (rotPoly O).toLinearMap) '' (Set.range (hermiteMv (d := d))) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCoreT]
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact ⟨rotPoly O p, rfl⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := rotPoly_surjective hO p
      exact ⟨q, by simp [hq]⟩
  rw [← hbase]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    change pgLpT a k (rotPoly O (hermiteMv α))
      ∈ Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k))
    have h : pgLpT a k (rotPoly O (hermiteMv α))
        = ((hermiteMvNorm α : ℝ) : ℂ) • hermiteTRLp O a k α := by
      rw [hermiteTRLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero α), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem hermiteTRLp_total {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (v : L2d d) (h : ∀ α, (inner ℂ (hermiteTRLp (d := d) O a k α) v : ℂ) = 0) : v = 0 := by
  refine eq_zero_of_inner_coreT a k v fun z hz => ?_
  rw [← span_hermiteTRLp hO a k] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨α, rfl⟩ := hz; exact h α
  | zero => simp
  | add z z' _ _ ihz ihz' => rw [inner_add_left, ihz, ihz']; ring
  | smul r z _ ih => rw [inner_smul_left, ih]; ring

end

end BookProof.ShiftedQuadraticMatrix
