/-
# S0 (continued): the `99`-coordinate product form of the Mehler bridge, with its `−99/2`

`softmodes.md`'s S0 package fixes the reference gap by a *coordinate count*: the `99`-coordinate
Gaussian Dirichlet operator is unitarily `−Δ + |x|²/4 − 99/2`, and the `−99/2` is what remains of
"one `−1/2` per coordinate".  The one-coordinate chapter proves
`U (−∂² + x∂) U⁻¹ = −∂² + x²/4 − 1/2`; the previous ledger entry that the product form "follows by
applying the identity coordinatewise" was wrong, because coordinatewise application covers only
functions of a single coordinate.

This module assembles the product form without the Laplacian Leibniz rule, by conjugating a
*coordinate derivative* twice — the same device that proves the one-coordinate identity:

  `U ∂ᵢ U⁻¹ = ∂ᵢ + xᵢ/2`,  hence  `U (−∂ᵢ²) U⁻¹ = −∂ᵢ² − xᵢ∂ᵢ − ½ − xᵢ²/4`,

so for the weighted coordinate Dirichlet operator `Dᵢ = −∂ᵢ² + xᵢ∂ᵢ` one gets
`U Dᵢ U⁻¹ = −∂ᵢ² + xᵢ²/4 − ½` per coordinate, and summing over `i` gives
`U (Σᵢ Dᵢ) U⁻¹ = −Δ + |x|²/4 − d/2`.  With `d = 99` that is the plan's `−99/2`.

All derivative facts are one-dimensional: a partial derivative is defined as the derivative of the
restriction of `F` to the affine line `xᵢ ↦ t`, so no second-order Fréchet calculus and no
`Δ(gF) = gΔF + 2⟨∇g,∇F⟩ + FΔg` is needed, and the drift `t/2` of the one-coordinate rule is applied
twice.  What is *not* claimed: this is an identity on functions with the stated one-variable
differentiability along every coordinate line; it is not a statement about `L²` domains, form cores
or self-adjoint extensions, and it makes no spectral claim.
-/
import BookProof.Qym.ChapterYangMillsMehlerBridge

namespace BookProof.YangMillsMehlerProduct

open BookProof.YangMillsMehlerBridge

noncomputable section

/-! ## The `d`-coordinate Gaussian and its factorization along a coordinate line -/

/-- The `d`-coordinate Gaussian root `γ^{1/2}(x) = exp(−|x|²/4)`. -/
def gaussRootVec {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.exp (-(∑ i, x i ^ 2) / 4)

/-- Its reciprocal `γ^{-1/2}(x) = exp(|x|²/4)`. -/
def invGaussVec {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.exp ((∑ i, x i ^ 2) / 4)

/-- `γ^{-1/2} γ^{1/2} = 1` in `d` coordinates. -/
theorem invGaussVec_mul_gaussRootVec {d : ℕ} (x : Fin d → ℝ) :
    invGaussVec x * gaussRootVec x = 1 := by
  rw [invGaussVec, gaussRootVec, ← Real.exp_add,
    show (∑ i, x i ^ 2) / 4 + -(∑ i, x i ^ 2) / 4 = 0 by ring, Real.exp_zero]

/-- `γ^{1/2} γ^{-1/2} = 1` in `d` coordinates. -/
theorem gaussRootVec_mul_invGaussVec {d : ℕ} (x : Fin d → ℝ) :
    gaussRootVec x * invGaussVec x = 1 := by
  rw [mul_comm, invGaussVec_mul_gaussRootVec]

/-- **Squaring the weight.**  In `d` coordinates the Mehler density is the pointwise square of the
root: `(γ^{1/2})² = γ`, coordinate by coordinate. -/
theorem gaussRootVec_sq {d : ℕ} (x : Fin d → ℝ) :
    gaussRootVec x ^ 2 = Real.exp (-(∑ i, x i ^ 2) / 2) := by
  rw [gaussRootVec, sq, ← Real.exp_add]
  congr 1
  ring

/-- The sum of squares changes in one coordinate only:
`Σⱼ (update y i t)ⱼ² = Σⱼ yⱼ² − yᵢ² + t²`.  This is the whole content of "the factor in the other
coordinates is a constant along the line". -/
theorem sum_sq_update {d : ℕ} (y : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    ∑ j, (Function.update y i t) j ^ 2 = (∑ j, y j ^ 2) - y i ^ 2 + t ^ 2 := by
  classical
  have hsplit : ∀ (f : Fin d → ℝ),
      ∑ j, f j ^ 2 = f i ^ 2 + ∑ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, f j ^ 2 :=
    fun f => Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) _
  have hsame : ∑ j ∈ (Finset.univ : Finset (Fin d)) \ {i},
      (Function.update y i t) j ^ 2 = ∑ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, y j ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by
      simpa using hj
    rw [Function.update_of_ne hji]
  rw [hsplit (Function.update y i t), hsplit y, hsame, Function.update_self i t y]
  ring

/-- **The weight factors along a coordinate line.**  Restricting `γ^{1/2}` to the line `xᵢ ↦ t`
leaves a one-dimensional Gaussian root times the values in the other coordinates:
`γ^{1/2}(update y i t) = γ^{1/2}(t) · γ^{1/2}(y) · γ^{-1/2}(yᵢ)`. -/
theorem gaussRootVec_update {d : ℕ} (y : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    gaussRootVec (Function.update y i t) = gaussRoot t * gaussRootVec y * invGauss (y i) := by
  rw [gaussRootVec, sum_sq_update, gaussRoot, gaussRootVec, invGauss, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- The same factorization for the reciprocal weight:
`γ^{-1/2}(update y i t) = γ^{-1/2}(t) · γ^{-1/2}(y) · γ^{1/2}(yᵢ)`. -/
theorem invGaussVec_update {d : ℕ} (y : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    invGaussVec (Function.update y i t) = invGauss t * invGaussVec y * gaussRoot (y i) := by
  rw [invGaussVec, sum_sq_update, invGauss, invGaussVec, gaussRoot, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-! ## Partial derivatives along coordinate lines -/

/-- The partial derivative of `F` in coordinate `i` at `y`, as the derivative of the restriction of
`F` to the affine line through `y` in direction `i`. -/
def pd {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) (y : Fin d → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (Function.update y i t)) (y i)

/-- The second partial derivative in coordinate `i`, i.e. the second derivative of the restriction
of `F` to that line. -/
def pd2 {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) (y : Fin d → ℝ) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => F (Function.update y i t)) s) (y i)

/-- Moving the base point along the line to a new value leaves the same line: rebasing at `t` and
reading the line at `u` is rebasing at `u`. -/
theorem line_update {d : ℕ} (y : Fin d → ℝ) (i : Fin d) (t u : ℝ) :
    Function.update (Function.update y i t) i u = Function.update y i u := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp only [Function.update_of_ne (a := j) (a' := i) h]

/-- Moving the base point along the line does not change the line: `pd F i (update y i t)` is the
derivative of the same one-variable function, evaluated at `t`. -/
theorem pd_update {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) (y : Fin d → ℝ) (t : ℝ) :
    pd F i (Function.update y i t) = deriv (fun u : ℝ => F (Function.update y i u)) t := by
  unfold pd
  rw [Function.update_self i t y]
  congr 1
  funext u
  rw [line_update y i t u]

/-- The second partial derivative is the partial derivative of the first. -/
theorem pd_pd {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) (y : Fin d → ℝ) :
    pd (fun z => pd F i z) i y = pd2 F i y := by
  have hfun : (fun t : ℝ => pd F i (Function.update y i t))
      = fun t => deriv (fun u : ℝ => F (Function.update y i u)) t :=
    funext (fun t => pd_update F i y t)
  change deriv (fun t : ℝ => pd F i (Function.update y i t)) (y i)
      = deriv (fun s : ℝ => deriv (fun t : ℝ => F (Function.update y i t)) s) (y i)
  rw [hfun]

/-! ## The conjugation identities in `d` coordinates, one coordinate at a time -/

/-- Cancelling the coordinate drift against the one-dimensional Gaussian factor: `bᵢ cᵢ = 1`
strips the weight from a product that also carries the drift `cᵢ`. -/
theorem invGaussVec_mul_cancel {d : ℕ} (y : Fin d → ℝ) (i : Fin d) (X : ℝ) :
    (invGaussVec y * gaussRoot (y i)) * (invGauss (y i) * X) = invGaussVec y * X := by
  rw [← mul_assoc (invGaussVec y * gaussRoot (y i)) (invGauss (y i)) X,
    mul_assoc (invGaussVec y) (gaussRoot (y i)) (invGauss (y i)), gaussRoot_mul_invGauss, mul_one]

/-- **`U ∂ᵢ U⁻¹ = ∂ᵢ + xᵢ/2` in `d` coordinates.**  Along the line `xᵢ ↦ t` the `d`-coordinate
weight factors into a one-dimensional Gaussian root and a constant, so the one-coordinate momentum
identity applies verbatim and the drift is `t/2 = xᵢ/2`. -/
theorem pd_invGaussVec_mul {d : ℕ} {F : (Fin d → ℝ) → ℝ} {i : Fin d} {y : Fin d → ℝ}
    (hf : HasDerivAt (fun t : ℝ => F (Function.update y i t)) (pd F i y) (y i)) :
    pd (fun z => invGaussVec z * F z) i y
      = invGaussVec y * (pd F i y + (y i / 2) * F y) := by
  have hline := hasDerivAt_invGauss_mul (f := fun t : ℝ => F (Function.update y i t)) hf
  have hscaled : HasDerivAt
      (fun t => (invGaussVec y * gaussRoot (y i)) * (invGauss t * F (Function.update y i t)))
      ((invGaussVec y * gaussRoot (y i))
        * (invGauss (y i) * (pd F i y + (y i / 2) * F y))) (y i) := by
    have h := hline.const_mul (invGaussVec y * gaussRoot (y i))
    simpa [Function.update_eq_self] using h
  have hfac : (fun t : ℝ => invGaussVec (Function.update y i t) * F (Function.update y i t))
      = fun t => (invGaussVec y * gaussRoot (y i))
          * (invGauss t * F (Function.update y i t)) := by
    funext t
    rw [invGaussVec_update]
    ring
  change deriv (fun t : ℝ => invGaussVec (Function.update y i t) * F (Function.update y i t))
      (y i) = invGaussVec y * (pd F i y + (y i / 2) * F y)
  rw [hfac, hscaled.deriv]
  exact invGaussVec_mul_cancel y i (pd F i y + (y i / 2) * F y)

/-- **The first-order identity as an operator statement.**  Multiplying by `γ^{-1/2}`,
differentiating in coordinate `i`, and multiplying back by `γ^{1/2}` returns the partial derivative
plus the drift `xᵢ/2`. -/
theorem conj_partial {d : ℕ} {F : (Fin d → ℝ) → ℝ} {i : Fin d} {y : Fin d → ℝ}
    (hf : HasDerivAt (fun t : ℝ => F (Function.update y i t)) (pd F i y) (y i)) :
    gaussRootVec y * pd (fun z => invGaussVec z * F z) i y
      = pd F i y + (y i / 2) * F y := by
  rw [pd_invGaussVec_mul hf, ← mul_assoc, gaussRootVec_mul_invGaussVec, one_mul]

/-- The partial derivative of the drift-modified function `z ↦ ∂ᵢF(z) + (zᵢ/2)F(z)`, which is what
the second application of the one-coordinate rule needs: the derivative of the drift contributes
`1/2` and the product rule contributes `(yᵢ/2)∂ᵢF(y)`. -/
theorem pd_drift_add {d : ℕ} {F : (Fin d → ℝ) → ℝ} {i : Fin d} {y : Fin d → ℝ}
    (h1 : HasDerivAt (fun t : ℝ => F (Function.update y i t)) (pd F i y) (y i))
    (h2 : HasDerivAt (fun t : ℝ => pd F i (Function.update y i t)) (pd2 F i y) (y i)) :
    pd (fun z => pd F i z + (z i / 2) * F z) i y
      = pd2 F i y + ((1 / 2) * F y + (y i / 2) * pd F i y) := by
  have hpair : HasDerivAt (fun t : ℝ => (t / 2) * F (Function.update y i t))
      ((1 / 2) * F y + (y i / 2) * pd F i y) (y i) := by
    have hlin : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) (y i) :=
      (hasDerivAt_id (y i)).div_const 2
    have hmul := hlin.mul h1
    simpa [Function.update_eq_self] using hmul
  have hsum := h2.add hpair
  have hfun : (fun t : ℝ => pd F i (Function.update y i t)
        + (Function.update y i t i / 2) * F (Function.update y i t))
      = fun t => pd F i (Function.update y i t) + (t / 2) * F (Function.update y i t) := by
    funext t
    rw [Function.update_self i t y]
  change deriv (fun t : ℝ => pd F i (Function.update y i t)
      + ((Function.update y i t) i / 2) * F (Function.update y i t)) (y i)
    = pd2 F i y + ((1 / 2) * F y + (y i / 2) * pd F i y)
  rw [hfun]
  exact hsum.deriv

/-- **`U ∂ᵢ² U⁻¹` in `d` coordinates.**  The second application of the one-coordinate rule, now to
the partial derivative itself: the drift contributes `1/2` and the double drift contributes
`xᵢ²/4`. -/
theorem pd2_invGaussVec_mul {d : ℕ} {F : (Fin d → ℝ) → ℝ} {i : Fin d} {y : Fin d → ℝ}
    (h1 : ∀ z : Fin d → ℝ,
      HasDerivAt (fun t : ℝ => F (Function.update z i t)) (pd F i z) (z i))
    (h2 : HasDerivAt (fun t : ℝ => pd F i (Function.update y i t)) (pd2 F i y) (y i)) :
    pd2 (fun z => invGaussVec z * F z) i y
      = invGaussVec y * (pd2 F i y + y i * pd F i y + (1 / 2 + y i ^ 2 / 4) * F y) := by
  have hGline : HasDerivAt (fun t : ℝ => pd F i (Function.update y i t)
      + (t / 2) * F (Function.update y i t))
      (pd2 F i y + ((1 / 2) * F y + (y i / 2) * pd F i y)) (y i) := by
    have hpair : HasDerivAt (fun t : ℝ => (t / 2) * F (Function.update y i t))
        ((1 / 2) * F y + (y i / 2) * pd F i y) (y i) := by
      have hlin : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) (y i) :=
        (hasDerivAt_id (y i)).div_const 2
      have hmul := hlin.mul (h1 y)
      simpa [Function.update_eq_self] using hmul
    exact h2.add hpair
  -- the same derivative, now with the drift written through the line point
  have hG : HasDerivAt (fun t : ℝ => (fun z => pd F i z + (z i / 2) * F z)
        (Function.update y i t)) (pd (fun z => pd F i z + (z i / 2) * F z) i y) (y i) := by
    have hmain : HasDerivAt (fun t : ℝ => (fun z => pd F i z + (z i / 2) * F z)
          (Function.update y i t))
        (pd2 F i y + ((1 / 2) * F y + (y i / 2) * pd F i y)) (y i) := by
      simpa [Function.update_self] using hGline
    rw [pd_drift_add (h1 := h1 y) (h2 := h2)]
    exact hmain
  have hfun : (fun z => pd (fun w => invGaussVec w * F w) i z)
      = fun z => invGaussVec z * (pd F i z + (z i / 2) * F z) := by
    funext z
    exact pd_invGaussVec_mul (hf := h1 z)
  rw [← pd_pd]
  simp only [hfun]
  rw [pd_invGaussVec_mul (F := fun z => pd F i z + (z i / 2) * F z) (hf := hG),
    pd_drift_add (h1 := h1 y) (h2 := h2)]
  ring

/-! ## The weighted coordinate Dirichlet operator and the product form -/

/-- The weighted coordinate Dirichlet operator `Dᵢ = −∂ᵢ² + xᵢ∂ᵢ`, whose `L²(γ)` reading is
`∂ᵢ*∂ᵢ` because the drift of the Gaussian measure is `−xᵢ`. -/
def gaussDirichletVec {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) (y : Fin d → ℝ) : ℝ :=
  -(pd2 F i y) + y i * pd F i y

/-- The coordinate-sum Laplacian `ΔF = Σᵢ ∂ᵢ²F`, which is what `Σᵢ Dᵢ` pairs with. -/
def laplaceVec {d : ℕ} (F : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ := ∑ i, pd2 F i y

/-- **The product form in one coordinate.**  Conjugating `Dᵢ = −∂ᵢ² + xᵢ∂ᵢ` by `U` gives
`−∂ᵢ² + xᵢ²/4 − 1/2`: the one-coordinate oscillator, with the drift supplying the `xᵢ²/4` and its
derivative supplying the `−1/2`. -/
theorem conj_dirichletVec_coord {d : ℕ} {F : (Fin d → ℝ) → ℝ} {i : Fin d}
    (h1 : ∀ y, HasDerivAt (fun t : ℝ => F (Function.update y i t)) (pd F i y) (y i))
    (h2 : ∀ y, HasDerivAt (fun t : ℝ => pd F i (Function.update y i t)) (pd2 F i y) (y i))
    (y : Fin d → ℝ) :
    gaussRootVec y * gaussDirichletVec (fun z => invGaussVec z * F z) i y
      = -(pd2 F i y) + (y i ^ 2 / 4 - 1 / 2) * F y := by
  have hA := conj_partial (F := F) (hf := h1 y)
  have hB := pd2_invGaussVec_mul (F := F) (h1 := h1) (h2 := h2 y)
  -- strip the weight from the conjugated derivative: `∂ᵢ(U⁻¹F) = γ^{-1/2}(∂ᵢF + xᵢF/2)`
  have hconj : pd (fun z => invGaussVec z * F z) i y
      = invGaussVec y * (pd F i y + (y i / 2) * F y) := by
    calc pd (fun z => invGaussVec z * F z) i y
        = invGaussVec y
            * (gaussRootVec y * pd (fun z => invGaussVec z * F z) i y) := by
          rw [← mul_assoc, invGaussVec_mul_gaussRootVec, one_mul]
      _ = invGaussVec y * (pd F i y + (y i / 2) * F y) := by rw [hA]
  unfold gaussDirichletVec
  rw [hB, hconj]
  have hX : gaussRootVec y
        * (-(invGaussVec y * (pd2 F i y + y i * pd F i y + (1 / 2 + y i ^ 2 / 4) * F y)))
      = -(pd2 F i y + y i * pd F i y + (1 / 2 + y i ^ 2 / 4) * F y) := by
    rw [show gaussRootVec y
          * (-(invGaussVec y * (pd2 F i y + y i * pd F i y + (1 / 2 + y i ^ 2 / 4) * F y)))
        = -(gaussRootVec y * invGaussVec y
            * (pd2 F i y + y i * pd F i y + (1 / 2 + y i ^ 2 / 4) * F y)) by ring,
      gaussRootVec_mul_invGaussVec, one_mul]
  have hY : gaussRootVec y
        * (y i * (invGaussVec y * (pd F i y + (y i / 2) * F y)))
      = y i * (pd F i y + (y i / 2) * F y) := by
    rw [show gaussRootVec y * (y i * (invGaussVec y * (pd F i y + (y i / 2) * F y)))
        = (gaussRootVec y * invGaussVec y) * (y i * (pd F i y + (y i / 2) * F y)) by ring,
      gaussRootVec_mul_invGaussVec, one_mul]
  rw [mul_add, hX, hY]
  ring

/-- The drift sum: the `−1/2` per coordinate aggregates into `−d/2`, which is the only place the
coordinate count enters. -/
theorem sum_drift {d : ℕ} {F : (Fin d → ℝ) → ℝ} (y : Fin d → ℝ) :
    ∑ i, (y i ^ 2 / 4 - 1 / 2) * F y = ((∑ i, y i ^ 2) / 4 - (d : ℝ) / 2) * F y := by
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The `d`-coordinate product form.**  Summing the one-coordinate identity over all `d`
coordinates:

  `U (Σᵢ Dᵢ) U⁻¹ = −Δ + |x|²/4 − d/2`,

with the coordinate count appearing exactly once, in the constant `−d/2`. -/
theorem conj_dirichletVec {d : ℕ} {F : (Fin d → ℝ) → ℝ}
    (h1 : ∀ (y : Fin d → ℝ) (i : Fin d),
      HasDerivAt (fun t : ℝ => F (Function.update y i t)) (pd F i y) (y i))
    (h2 : ∀ (y : Fin d → ℝ) (i : Fin d),
      HasDerivAt (fun t : ℝ => pd F i (Function.update y i t)) (pd2 F i y) (y i))
    (y : Fin d → ℝ) :
    gaussRootVec y * (∑ i, gaussDirichletVec (fun z => invGaussVec z * F z) i y)
      = -(∑ i, pd2 F i y) + ((∑ i, y i ^ 2) / 4 - (d : ℝ) / 2) * F y := by
  have hterm : ∀ i : Fin d,
      gaussRootVec y * gaussDirichletVec (fun z => invGaussVec z * F z) i y
        = -(pd2 F i y) + (y i ^ 2 / 4 - 1 / 2) * F y := by
    intro i
    exact conj_dirichletVec_coord (h1 := fun z => h1 z i) (h2 := fun z => h2 z i) y
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    Finset.sum_neg_distrib, sum_drift]

/-- **The `99`-coordinate product form, with the `−99/2`.**  This is the form `softmodes.md` asks
for: the `d`-coordinate identity at `d = 99`, where the constant is `−99/2` and the reference gap
`1/2` remains the *one-coordinate* oscillator's. -/
theorem conj_dirichletVec99 {F : (Fin 99 → ℝ) → ℝ}
    (h1 : ∀ (y : Fin 99 → ℝ) (i : Fin 99),
      HasDerivAt (fun t : ℝ => F (Function.update y i t)) (pd F i y) (y i))
    (h2 : ∀ (y : Fin 99 → ℝ) (i : Fin 99),
      HasDerivAt (fun t : ℝ => pd F i (Function.update y i t)) (pd2 F i y) (y i))
    (y : Fin 99 → ℝ) :
    gaussRootVec y * (∑ i, gaussDirichletVec (fun z => invGaussVec z * F z) i y)
      = -laplaceVec F y + ((∑ i, y i ^ 2) / 4 - (99 : ℝ) / 2) * F y := by
  have hmain := conj_dirichletVec (F := F) h1 h2 y
  simpa [laplaceVec] using hmain

end

end BookProof.YangMillsMehlerProduct
