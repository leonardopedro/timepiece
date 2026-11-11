import BookProof.Qym.ChapterYangMillsMehlerLp
import BookProof.Toolbox.ChapterHermiteFunctions

/-!
# S0: Hermite eigenfunctions of the Gaussian Dirichlet operator, and polynomial density

`softmodes.md` records the essential-self-adjointness gap for the Yang–Mills Dirichlet
operator `T = −Δ + x·∇` on `L²(γ dx)` and lists three standard routes (S0, "Route C").  This
module proves the two *analytic* inputs of Route C that are not blocked by missing theory:

* **(i) the eigen-relation.**  `gaussDirichlet_hermiteR`: the probabilists' Hermite polynomials are
  eigenfunctions of `gaussDirichlet f = −f'' + x f'`, with eigenvalue `n`.  The proof is the Hermite
  ODE `H'' − x H' + n H = 0` (`BookProof.HermiteCore.hermiteR_ode`) read backwards, plus the two
  polynomial-derivative identities `deriv_eval_hermiteR` and `deriv_deriv_eval_hermiteR`.
* **(ii) density of polynomials.**  `dense_span_polyLp`: the polynomial classes are dense in
  `L²(γ dx)`.  The proof has the shape of `BookProof.HermiteCore.hermiteLp_span_dense` — a vector
  orthogonal to every polynomial has all Gaussian moments zero — but the moments are taken against
  `γ dx`, not `dx`, so `integral_moment_eq` first moves the integral to Lebesgue measure, where the
  existing `ae_eq_zero_of_moments` applies to `γ^{1/2} w`.

## The convention, corrected

`softmodes.md` Route C writes the eigenfunctions as `H_n(x/√2)` with eigenvalue `2n`, and points at
`hermiteR_ode` for it.  That is the physicists' convention.  The corpus uses the probabilists'
`Polynomial.hermite` (`hermiteR`), for which `hermiteR_ode` reads `−H'' + x H' = n H`: the
eigenfunctions are `hermiteR n` itself, with no rescaling, and the eigenvalue is `n`.  The
statements below are the corrected ones, and they compose with `conj_dirichlet` and
`hermiteFun_oscillator` without a stray factor of `2`.

## Scope

Nothing here proves self-adjointness.  Route C still needs **Nelson's analytic-vector theorem**
(input (iii) of the plan), which mathlib does not have; this module only supplies the two concrete
spectral statements a Nelson argument would start from.
-/

namespace BookProof.YangMillsHermiteSpectrum

open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.YangMillsMehlerBridge BookProof.YangMillsMehlerLp
open scoped ENNReal

noncomputable section

/-! ## The two Gaussian conventions are the same function -/

/-- The Mehler root `γ^{1/2} = e^{-x²/4}` is the half weight `gaussH` of the Hermite chapter, with
the associativity of the division by `4` made explicit. -/
theorem gaussRoot_eq_gaussH (x : ℝ) : gaussRoot x = gaussH x := by
  unfold gaussRoot gaussH
  ring_nf

/-- The two factors agree: `γ^{1/2} · γ^{1/2} = γ`, i.e. `gaussH · gaussRoot = gaussRoot²`. -/
theorem gaussH_mul_gaussRoot (x : ℝ) : gaussH x * gaussRoot x = gaussRoot x ^ 2 := by
  rw [← gaussRoot_eq_gaussH]
  ring

/-- The Gaussian weight `e^{-x²/2}` is the square of the Mehler root. -/
theorem gaussW_eq_gaussRoot_sq (x : ℝ) : gaussW x = gaussRoot x ^ 2 := by
  unfold gaussW gaussRoot
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-! ## (i) The Hermite polynomials are eigenfunctions of `gaussDirichlet` -/

/-- The first derivative of a Hermite polynomial at a point, as the evaluation of the formal
derivative. -/
theorem deriv_eval_hermiteR (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => (hermiteR n).eval y) x = (derivative (hermiteR n)).eval x :=
  ((hermiteR n).hasDerivAt x).deriv

/-- The second derivative of a Hermite polynomial at a point — the same statement one order up,
with the first derivative unfolded through `deriv_eval_hermiteR`. -/
theorem deriv_deriv_eval_hermiteR (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => deriv (fun z : ℝ => (hermiteR n).eval z) y) x
      = (derivative (derivative (hermiteR n))).eval x := by
  have h : (fun y : ℝ => deriv (fun z : ℝ => (hermiteR n).eval z) y)
      = fun y : ℝ => (derivative (hermiteR n)).eval y :=
    funext fun y => deriv_eval_hermiteR n y
  rw [h]
  exact ((derivative (hermiteR n)).hasDerivAt x).deriv

/-- **The Hermite eigen-relation for the weighted Dirichlet operator.**  At every point,

`gaussDirichlet (H_n) x = n · H_n x`,

i.e. `−H_n'' + x H_n' = n H_n`.  This is `hermiteR_ode` rearranged: the ODE says
`H'' − x H' + n H = 0`, and `gaussDirichlet` is the negative of the first two of those terms. -/
theorem gaussDirichlet_eval_hermiteR (n : ℕ) (x : ℝ) :
    gaussDirichlet (fun y : ℝ => (hermiteR n).eval y) x = (n : ℝ) * (hermiteR n).eval x := by
  have hode := congrArg (Polynomial.eval x) (hermiteR_ode n)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_zero] at hode
  simp only [gaussDirichlet, deriv_deriv_eval_hermiteR n x, deriv_eval_hermiteR n x]
  linarith

/-- **The eigen-relation as an identity of functions**: `H_n` is an eigenfunction of
`gaussDirichlet` with eigenvalue `n`. -/
theorem gaussDirichlet_hermiteR (n : ℕ) :
    gaussDirichlet (fun y : ℝ => (hermiteR n).eval y)
      = fun x : ℝ => (n : ℝ) * (hermiteR n).eval x :=
  funext fun x => gaussDirichlet_eval_hermiteR n x

/-! ## The polynomials as elements of `L²(γ dx)` -/

/-- `γ^{1/2} · p` is square integrable for Lebesgue measure: its square is `p² γ`, and a polynomial
times a Gaussian is integrable (`integrable_poly_mul_gaussW`). -/
theorem memLp_gaussRoot_mul_eval (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => gaussRoot x * p.eval x) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => gaussRoot x * p.eval x)
      (volume : Measure ℝ) :=
    (measurable_gaussRoot.mul p.continuous_aeval.measurable).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  refine (integrable_poly_mul_gaussW (p * p)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Polynomial.eval_mul]
  rw [gaussW_eq_gaussRoot_sq]
  ring

/-- **Every polynomial is in `L²(γ dx)`**, by the Mehler membership equivalence
`memLp_gaussRoot_mul`: `p ∈ L²(γ dx) ⟺ γ^{1/2} p ∈ L²(dx)`. -/
theorem memLp_eval (p : Polynomial ℝ) : MemLp (fun x : ℝ => p.eval x) 2 gaussMeasure :=
  (memLp_gaussRoot_mul p.continuous_aeval.measurable).mp (memLp_gaussRoot_mul_eval p)

/-- A polynomial, as an element of `L²(γ dx)`. -/
def polyLp (p : Polynomial ℝ) : Lp ℝ 2 gaussMeasure := (memLp_eval p).toLp _

/-! ## Gaussian moments and the moment problem -/

/-- An integral of `ℂ`-valued constants is the cast of the real integral.  This is mathlib's
`integral_ofReal`, restated with the coefficient field fixed to `ℂ`: rewriting with the general
version does not fire against an integral whose measure is the default instance. -/
theorem ofReal_integral_eq (g : ℝ → ℝ) :
    ∫ x : ℝ, ((g x : ℝ) : ℂ) ∂(volume : Measure ℝ)
      = ((∫ x : ℝ, g x ∂(volume : Measure ℝ) : ℝ) : ℂ) :=
  integral_ofReal

/-- **The moment integral, moved to Lebesgue measure.**  Integrating `xᵏ · w` against
`γ dx = γ^{1/2}² dx` gives the Lebesgue integral of `(xᵏ γ^{1/2}) · (γ^{1/2} w)`, the product of the
two `L²(dx)` functions the moment problem is stated for.

The density is applied through the unconditional
`integral_withDensity_eq_integral_toReal_smul` rather than by rewriting `gaussMeasure`: `rw` cannot
unfold the measure in a goal that mentions an `Lp ℝ 2 gaussMeasure` element, because the coercion's
instance arguments carry it. -/
theorem integral_moment_eq (w : Lp ℝ 2 gaussMeasure) (k : ℕ) :
    ∫ x, x ^ k * (w : ℝ → ℝ) x ∂gaussMeasure
      = ∫ x, (x ^ k * gaussH x) * (gaussRoot x * (w : ℝ → ℝ) x) ∂(volume : Measure ℝ) := by
  have key := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    measurable_gaussDensity (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (g := fun x : ℝ => x ^ k * (w : ℝ → ℝ) x)
  refine key.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (ENNReal.ofReal (gaussRoot x ^ 2)).toReal • (x ^ k * (w : ℝ → ℝ) x)
      = (x ^ k * gaussH x) * (gaussRoot x * (w : ℝ → ℝ) x)
  rw [ENNReal.toReal_ofReal (sq_nonneg (gaussRoot x)), smul_eq_mul, ← gaussRoot_eq_gaussH]
  ring

/-- **Vanishing Gaussian moments force zero.**  If every moment `∫ xᵏ w d(γ dx)` vanishes, then
`w = 0`: multiply by `γ^{1/2}` and use `ae_eq_zero_of_moments` in `L²(dx)`, then divide by the
nowhere-vanishing `γ^{1/2}`. -/
theorem ae_eq_zero_of_moments_gaussMeasure (w : Lp ℝ 2 gaussMeasure)
    (hmom : ∀ k : ℕ, ∫ x, x ^ k * (w : ℝ → ℝ) x ∂gaussMeasure = 0) :
    (w : ℝ → ℝ) =ᵐ[gaussMeasure] 0 := by
  have hreal : ∀ k : ℕ,
      ∫ x, (x ^ k * gaussH x) * (gaussRoot x * (w : ℝ → ℝ) x) ∂(volume : Measure ℝ) = 0 := by
    intro k
    rw [← integral_moment_eq w k]
    exact hmom k
  have hC : ∀ k : ℕ, ∫ x : ℝ, ((x ^ k * gaussH x : ℝ) : ℂ)
      * ((gaussRoot x * (w : ℝ → ℝ) x : ℝ) : ℂ) ∂(volume : Measure ℝ) = 0 := by
    intro k
    have hpt : (fun x : ℝ => ((x ^ k * gaussH x : ℝ) : ℂ)
        * ((gaussRoot x * (w : ℝ → ℝ) x : ℝ) : ℂ))
        = fun x : ℝ => (((x ^ k * gaussH x) * (gaussRoot x * (w : ℝ → ℝ) x) : ℝ) : ℂ) := by
      funext x
      rw [← Complex.ofReal_mul]
    rw [hpt, ofReal_integral_eq, hreal k, Complex.ofReal_zero]
  have hzero := ae_eq_zero_of_moments ((memLp_gaussRoot_mul_lp w).ofReal) hC
  have hvol : (fun x : ℝ => gaussRoot x * (w : ℝ → ℝ) x) =ᵐ[volume] 0 := by
    filter_upwards [hzero] with x hx
    exact Complex.ofReal_eq_zero.mp hx
  have hgm : (fun x : ℝ => gaussRoot x * (w : ℝ → ℝ) x) =ᵐ[gaussMeasure] 0 :=
    absolutelyContinuous_gaussMeasure_volume.ae_eq hvol
  filter_upwards [hgm] with x hx
  exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt (gaussRoot_pos x))

/-! ## (ii) Density of the polynomials -/

/-- **The polynomials are dense in `L²(γ dx)`.**  A vector orthogonal to the span of the polynomial
classes has all Gaussian moments zero, hence vanishes by `ae_eq_zero_of_moments_gaussMeasure`. -/
theorem dense_span_polyLp :
    (⊤ : Submodule ℝ (Lp ℝ 2 gaussMeasure))
      ≤ (Submodule.span ℝ (Set.range polyLp)).topologicalClosure := by
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro w hw
  have hcoef : ∀ k : ℕ,
      (polyLp ((X : Polynomial ℝ) ^ k) : ℝ → ℝ) =ᵐ[gaussMeasure] fun x => x ^ k := by
    intro k
    refine (memLp_eval ((X : Polynomial ℝ) ^ k)).coeFn_toLp.trans ?_
    filter_upwards with x
    simp
  have hmom : ∀ k : ℕ, ∫ x, x ^ k * (w : ℝ → ℝ) x ∂gaussMeasure = 0 := by
    intro k
    have hinner : inner ℝ (polyLp ((X : Polynomial ℝ) ^ k)) w = 0 :=
      hw _ (Submodule.subset_span ⟨(X : Polynomial ℝ) ^ k, rfl⟩)
    rw [L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [hcoef k] with x hx
    rw [hx, RCLike.inner_apply]
    simp
    ring
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_eq_zero_of_moments_gaussMeasure w hmom)

end

end BookProof.YangMillsHermiteSpectrum
