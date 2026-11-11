import BookProof.Qym.ChapterYangMillsHermiteSpectrum
import BookProof.Toolbox.ChapterNelsonAnalyticVectors

/-!
# The polynomial form core of `gaussDirichlet`, and the Hermite analytic-vector bounds

`BookProof.Qym.ChapterYangMillsHermiteSpectrum` proves the eigenvalue relation
`gaussDirichlet (H_n) = n · H_n` and the density of the polynomial classes in `L²(γ dx)`.
Those are the two spectral inputs of Nelson's route to essential self-adjointness
(`softmodes.md`, S0 Route C).  This module supplies the *quantitative* input the analytic-vector
argument consumes, namely the growth of `‖Tⁿp‖` on the polynomial core.

## The polynomial form core

`T = −∂² + x∂` acts on polynomials by `dirichletPoly p = −p'' + X·p'`, and on the corresponding
`L²(γ dx)` classes by `polyLp ∘ dirichletPoly` — this is `dirichletPoly_eval` at the level of
functions and the definition of `polyLp` at the level of classes.  The polynomial classes are
dense (`dense_span_polyLp`), so this is the form core the analytic-vector theory wants, and the
operator is diagonal on it in the Hermite basis (`dirichletPoly_hermiteR`).

## The bound

Because `H_n` is an eigenvector with eigenvalue `n`, nothing grows but the eigenvalue:

* `dirichletPoly_iterate_hermiteR` — `Tᵐ(H_n) = nᵐ · H_n` as polynomials;
* `norm_polyLp_iterate_hermiteR` — `‖Tᵐ(H_n)‖_{L²(γ)} = nᵐ ‖H_n‖_{L²(γ)}`, i.e. the geometric
  bound with ratio `r = n` and constant `‖H_n‖`;
* `hermiteR_geometric` — the same statement in the shape of
  `BookProof.NelsonAnalytic.IsGeometric`;
* `hermiteR_summable` — `Σ rᵐ/m! ‖Tᵐ(H_n)‖ < ∞` for **every** `r > 0`, which is
  `BookProof.NelsonAnalytic.IsAnalytic` read at this core: each Hermite class is an analytic
  vector with radius `n`.

## Honest boundary

The radius is `n`, so the vectors of the core have **no common radius** — the polynomial core
satisfies Nelson's hypothesis (a dense set of analytic vectors) but not the common-radius
sufficiency condition of `NelsonAnalytic.essentiallySelfAdjointOn_of_dense_geometric`.  Two ways
out, both documented in that module: the general Nelson theorem (per-vector radii), or — since
the eigenbasis is explicit — the much cheaper eigenvector criterion.  What is still missing for
either is the same transport: promoting the polynomial classes to a *partially defined operator*
on `Lp ℝ 2 gaussMeasure` with this core, whose domain is not the compactly supported `C²` core
`gaussCore` that `gaussOp` is currently defined on.  The bounds here are the analytic half of
that transport.
-/

namespace BookProof.YangMillsHermiteAnalytic

open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.YangMillsMehlerBridge BookProof.YangMillsMehlerLp
open BookProof.YangMillsHermiteSpectrum
open scoped ENNReal

noncomputable section

/-! ## The operator on polynomials -/

/-- **The Dirichlet operator on polynomials**, `p ↦ −p'' + X·p'`.  This is `gaussDirichlet`
transported from functions to their polynomial representatives. -/
def dirichletPoly : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := -(derivative (derivative p)) + X * derivative p
  map_add' p q := by
    simp only [mul_add, map_add]
    ring
  map_smul' c p := by
    simp only [RingHom.id_apply, derivative_smul, mul_smul_comm, smul_neg, smul_add]

/-- The defining formula of `dirichletPoly`, as a rewrite rule. -/
@[simp] theorem dirichletPoly_apply (p : Polynomial ℝ) :
    dirichletPoly p = -(derivative (derivative p)) + X * derivative p := rfl

/-- **`dirichletPoly` is `gaussDirichlet` on polynomial representatives.**  This is what makes
the polynomial core a core: the operator commutes with taking the `L²(γ dx)` class. -/
theorem dirichletPoly_eval (p : Polynomial ℝ) :
    (fun x : ℝ => (dirichletPoly p).eval x) = gaussDirichlet (fun x : ℝ => p.eval x) := by
  funext x
  have h1 : deriv (fun y : ℝ => p.eval y) x = (derivative p).eval x := (p.hasDerivAt x).deriv
  have h2 : deriv (fun y : ℝ => deriv (fun z : ℝ => p.eval z) y) x
      = (derivative (derivative p)).eval x := by
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => p.eval z) y)
        = fun y : ℝ => (derivative p).eval y := funext fun y => (p.hasDerivAt y).deriv
    rw [hfun]
    exact ((derivative p).hasDerivAt x).deriv
  simp only [dirichletPoly_apply, gaussDirichlet, Polynomial.eval_add, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_X, h1, h2]

/-! ## The Hermite basis: iteration and norm -/

/-- **The eigenvalue relation on polynomials**: `−H_n'' + X·H_n' = n·H_n`.  This is
`hermiteR_ode` rearranged at the polynomial level, the exact counterpart of the function
statement `gaussDirichlet_hermiteR`. -/
theorem dirichletPoly_hermiteR (n : ℕ) : dirichletPoly (hermiteR n) = (n : ℝ) • hermiteR n := by
  have h := hermiteR_ode n
  rw [dirichletPoly_apply, Polynomial.smul_eq_C_mul]
  linear_combination -h

/-- **The iterates on the Hermite basis**: `H_n` is an eigenvector of every power of the
operator, with eigenvalue `nᵐ`. -/
theorem dirichletPoly_iterate_hermiteR (m n : ℕ) :
    (dirichletPoly^[m]) (hermiteR n) = (n : ℝ) ^ m • hermiteR n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, dirichletPoly_hermiteR, smul_smul,
      ← pow_succ]

/-- Polynomials scale their `L²(γ dx)` classes. -/
theorem polyLp_smul (c : ℝ) (p : Polynomial ℝ) : polyLp (c • p) = c • polyLp p := by
  unfold polyLp
  rw [← MemLp.toLp_const_smul (p := 2) (μ := gaussMeasure) c (memLp_eval p)]
  refine MemLp.toLp_congr (memLp_eval (c • p)) ((memLp_eval p).const_smul c) ?_
  filter_upwards with x
  simp only [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Pi.smul_apply,
    smul_eq_mul]

/-- **The analytic-vector bound.**  The `L²(γ dx)` norm of the `m`-th iterate applied to `H_n` is
exactly `nᵐ` times the norm of `H_n`: on the polynomial core the operator grows no faster than
its largest eigenvalue on the vector. -/
theorem norm_polyLp_iterate_hermiteR (m n : ℕ) :
    ‖polyLp ((dirichletPoly^[m]) (hermiteR n))‖ = (n : ℝ) ^ m * ‖polyLp (hermiteR n)‖ := by
  rw [dirichletPoly_iterate_hermiteR, polyLp_smul, norm_smul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n)]

/-- **The Hermite classes satisfy a geometric bound.**  In the shape of
`BookProof.NelsonAnalytic.IsGeometric`: the orbit of `H_n` is bounded by `‖H_n‖ · rᵐ` for every
`r ≥ n`. -/
theorem hermiteR_geometric (n : ℕ) {r : ℝ} (hr : (n : ℝ) ≤ r) (m : ℕ) :
    ‖polyLp ((dirichletPoly^[m]) (hermiteR n))‖ ≤ ‖polyLp (hermiteR n)‖ * r ^ m := by
  rw [norm_polyLp_iterate_hermiteR, mul_comm ((n : ℝ) ^ m)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (polyLp (hermiteR n)))
  exact pow_le_pow_left₀ (Nat.cast_nonneg n) hr m

/-- **Every Hermite class is an analytic vector, with every radius.**  The series
`Σ rᵐ/m! ‖Tᵐ(H_n)‖` converges for each `r > 0`, because the norm is `nᵐ ‖H_n‖` and
`Σ (r·n)ᵐ/m! = e^{rn}`.  This is `BookProof.NelsonAnalytic.IsAnalytic` read at the polynomial
core; the smallest radius that works for a *geometric* bound is `n`. -/
theorem hermiteR_summable (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun m : ℕ =>
      (r ^ m / (m.factorial : ℝ)) * ‖polyLp ((dirichletPoly^[m]) (hermiteR n))‖) := by
  have hterm : ∀ m : ℕ,
      (r ^ m / (m.factorial : ℝ)) * ‖polyLp ((dirichletPoly^[m]) (hermiteR n))‖
        = ‖polyLp (hermiteR n)‖ * ((r * (n : ℝ)) ^ m / (m.factorial : ℝ)) := by
    intro m
    rw [norm_polyLp_iterate_hermiteR, mul_pow]
    field_simp
  simp only [hterm]
  exact (Real.summable_pow_div_factorial (r * (n : ℝ))).mul_left _

/-! ## The function-level iterates -/

/-- **The iterates of `gaussDirichlet` on a polynomial representative**: on the polynomial core the
operator is literally `dirichletPoly`, so no representative choice enters the `m`-th power. -/
theorem gaussDirichlet_iterate_eval (m : ℕ) (p : Polynomial ℝ) :
    (gaussDirichlet^[m]) (fun x : ℝ => p.eval x) = fun x : ℝ => ((dirichletPoly^[m]) p).eval x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      ← dirichletPoly_eval]

/-- **The bound in the form the plan asks for**: the `m`-th iterate of `gaussDirichlet` applied to
`H_n`, measured in `L²(γ dx)`, grows like `nᵐ`. -/
theorem norm_gaussDirichlet_iterate_hermiteR (m n : ℕ) :
    ‖polyLp ((dirichletPoly^[m]) (hermiteR n))‖ = (n : ℝ) ^ m * ‖polyLp (hermiteR n)‖ :=
  norm_polyLp_iterate_hermiteR m n

end

end BookProof.YangMillsHermiteAnalytic
