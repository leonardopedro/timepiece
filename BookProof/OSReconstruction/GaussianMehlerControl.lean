import Mathlib
import BookProof.MCMC.KernelContract

/-!
# C1 — the finite-cutoff massive Gaussian control in Mehler coordinates

Work order: `cftproof.md` **C1**.  This module constructs the free massive scalar
reference at a finite cutoff as a genuine probability law, in the **Mehler
coordinates** where the reflection is diagonal, and proves the control's cylinder
laws, smeared moments, reflected-covariance positivity and cutoff consistency.

## The cutoff model

The field lives on **two time slices** `t = 0, 1` and a finite three-dimensional
momentum box `SpatialMode M = Fin M × Fin M × Fin M`, whose spatial dispersion is
the lattice sum `ω² k = ∑_{j=1}^{3} (k_j + 1)²`.  With `λ k = m₀² + ω² k`, the
time-direction nearest-neighbour Laplacian plus mass is the block matrix

```text
M_k = [[λ k + 2, -1], [-1, λ k + 2]],
```

whose inverse has the reflection-symmetric eigenvalues `1/(λ k + 1)` and
`1/(λ k + 3)`.  In the Mehler combinations `y± = (x₀ ± x₁)/√2` the covariance is
**diagonal**, so the law is a product of one-dimensional Gaussians:

* `variance m₀ (true, k)  = 1/(m₀² + ω² k + 1)`   (symmetric mode),
* `variance m₀ (false, k) = 1/(m₀² + ω² k + 3)`   (antisymmetric mode).

The covariance in the original slice coordinates is not diagonal — the two time
slices are correlated with `C₀₁ k = 1/((λ k + 1)(λ k + 3)) > 0` — so the control
is **not ultralocal** and it is genuinely four-dimensional: three spatial momenta
times two time slices.

## Contents

* `spatialEigenvalue`, `variance`, `variance_pos` — the finite-cutoff covariance;
* `law` and `law_isProbability` — the normalized Gaussian cylinder law;
* `marginal` — every one-mode cylinder law is `gaussianReal 0 (variance …)`;
* `charFun_one_mode` — the one-mode characteristic functional
  `∫ exp(i t y_p) dμ = exp(−variance · t²/2)`;
* `second_moment` — the smeared second moment `∫ y_p² dμ = variance`;
* `covBilin`, `reflection_invariant` — the Euclidean covariance form and its
  invariance under the time reflection;
* `posTest`, `rp_covariance` — **reflected-covariance positivity on half-space
  tests**: `C(θf, f) ≥ 0` for `f` supported on the positive-time slice;
* `badVariance`, `bad_rp_fails` — the negative control: a positive-definite
  diagonal covariance whose reflected form is *negative*, so a positive covariance
  matrix alone is insufficient (cf. `HalfSpaceInfiniteBandedCovariance`);
* `embedMehler`, `marginal_embed` — **cutoff consistency**: the one-mode cylinder
  laws of the `M` and `M + 1` cutoffs agree on the common modes, and the variances
  are cutoff-independent.

## Boundary

Two things are deliberately not claimed here.  (i) The lift of reflected-covariance
positivity to *all polynomial cylinders* needs Wick/chaos or the
boundary-conditioned kernel; this module proves the covariance form, which is the
half-space test the work order asks to check first, and the lift remains the open
step.  (ii) The continuum free field is distribution-valued: no globally
Hilbert–Schmidt `C₀^{1/2}` and no `L²(ℝ⁴)` field is asserted, and the `S'`-valued
limit as `M → ∞` is not constructed — only the consistent finite-dimensional
cylinder laws are.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BookProof.OSReconstruction

/-! ## 1. The finite-cutoff covariance -/

/-- A spatial momentum label in a three-dimensional box: three integers
`k₁, k₂, k₃`, each in `Fin M`. -/
abbrev SpatialMode (M : ℕ) := Fin M × Fin M × Fin M

/-- The lattice spatial dispersion `ω² k = ∑_{j=1}^{3} (k_j + 1)²`.  The `+ 1`
makes the lowest momentum nonzero, so the finite box has no zero mode; the value is
independent of the cutoff `M`, which is what makes the cylinder laws consistent. -/
def spatialEigenvalue {M : ℕ} (k : SpatialMode M) : ℝ :=
  ((k.1.val + 1 : ℝ) ^ 2 + (k.2.1.val + 1 : ℝ) ^ 2 + (k.2.2.val + 1 : ℝ) ^ 2)

theorem spatialEigenvalue_nonneg {M : ℕ} (k : SpatialMode M) :
    0 ≤ spatialEigenvalue k := by
  unfold spatialEigenvalue
  positivity

/-- A **Mehler mode**: the reflection parity `true` (symmetric, `y₊`) or `false`
(antisymmetric, `y₋`), together with the spatial momentum. -/
abbrev MehlerMode (M : ℕ) := Bool × SpatialMode M

/-- The **Mehler-coordinate variance** of a mode.  For `λ k = m₀² + ω² k`, the
symmetric mode has variance `1/(λ k + 1)` and the antisymmetric mode `1/(λ k + 3)`;
both come from inverting the two-slice time Laplacian. -/
def variance {M : ℕ} (m0 : ℝ) (p : MehlerMode M) : ℝ :=
  1 / (m0 ^ 2 + spatialEigenvalue p.2 + (if p.1 then 1 else 3))

theorem variance_pos {M : ℕ} (m0 : ℝ) (p : MehlerMode M) : 0 < variance m0 p := by
  unfold variance
  have h : (0 : ℝ) < m0 ^ 2 + spatialEigenvalue p.2 + (if p.1 then 1 else 3) := by
    have h1 := spatialEigenvalue_nonneg p.2
    have h2 : (0 : ℝ) < (if p.1 then (1 : ℝ) else 3) := by
      cases p.1 <;> norm_num
    nlinarith [sq_nonneg m0]
  exact one_div_pos.mpr h

/-- The symmetric mode has the **larger** variance of the two parities:
`1/(λ + 1) ≥ 1/(λ + 3)`.  This sign is what makes the reflected covariance positive. -/
theorem variance_symm_ge_antisymm {M : ℕ} (m0 : ℝ) (k : SpatialMode M) :
    variance m0 (true, k) ≥ variance m0 (false, k) := by
  have hsym : variance m0 (true, k) = 1 / (m0 ^ 2 + spatialEigenvalue k + 1) := by
    unfold variance
    simp
  have hanti : variance m0 (false, k) = 1 / (m0 ^ 2 + spatialEigenvalue k + 3) := by
    unfold variance
    simp
  rw [hsym, hanti]
  have h0 := spatialEigenvalue_nonneg k
  have hm := sq_nonneg m0
  have h1 : (0 : ℝ) < m0 ^ 2 + spatialEigenvalue k + 1 := by linarith
  exact one_div_le_one_div_of_le h1 (by linarith)

/-! ## 2. The normalized cylinder law -/

/-- The **finite-cutoff Gaussian covariance law** in Mehler coordinates: the
product of one-dimensional centered Gaussians, one for each Mehler mode. -/
def law {M : ℕ} (m0 : ℝ) : Measure (MehlerMode M → ℝ) :=
  Measure.pi fun p => gaussianReal 0 ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩

/-- The cylinder law is a **probability law**: it is a product of probability
measures, so it is normalized without any further hypothesis. -/
theorem law_isProbability {M : ℕ} (m0 : ℝ) :
    IsProbabilityMeasure (law (M := M) m0) := by
  change IsProbabilityMeasure (Measure.pi fun p : MehlerMode M =>
    gaussianReal 0 ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩)
  infer_instance

/-- The **one-mode cylinder law** is the centered Gaussian with the Mehler
variance: projecting a product measure onto one coordinate is that coordinate's
factor. -/
theorem marginal {M : ℕ} (m0 : ℝ) (p : MehlerMode M) :
    Measure.map (Function.eval p) (law m0)
      = gaussianReal 0 ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩ := by
  unfold law
  rw [Measure.pi_map_eval]
  simp [measure_univ]

/-- **The one-mode characteristic functional**:
`∫ exp(i t y_p) dμ = exp(−variance · t²/2)`.  Summing this over modes (with
independence) gives the free characteristic functional
`exp(−C₀(f,f)/2)`; the finite product is the cylinder form proved here. -/
theorem charFun_one_mode {M : ℕ} (m0 : ℝ) (p : MehlerMode M) (t : ℝ) :
    ∫ x, Complex.exp (t * x p * Complex.I) ∂(law m0)
      = Complex.exp (-(variance m0 p) * t ^ 2 / 2) := by
  have hmap : ∫ y, Complex.exp (↑t * ↑y * Complex.I)
        ∂(Measure.map (Function.eval p) (law m0))
      = ∫ x, Complex.exp (↑t * ↑(x p) * Complex.I) ∂(law m0) :=
    integral_map (μ := law m0) (φ := Function.eval p) (f := fun y : ℝ =>
      Complex.exp (↑t * ↑y * Complex.I))
      (measurable_pi_apply p).aemeasurable
      (by fun_prop : Measurable fun y : ℝ =>
        Complex.exp (↑t * ↑y * Complex.I)).aestronglyMeasurable
  rw [marginal m0 p] at hmap
  rw [← hmap]
  have hfun : (fun y : ℝ => Complex.exp (↑t * ↑y * Complex.I))
      = fun y => Complex.exp (↑(inner ℝ y t) * Complex.I) := by
    funext y
    congr 1
    have hinner : inner ℝ y t = t * y := by simp
    rw [hinner]
    push_cast
    ring
  rw [hfun]
  have h := charFun_gaussianReal (μ := 0)
    (v := ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩) t
  simp only [charFun, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_mk] at h
  rw [← show Complex.exp (-(↑(variance m0 p) * ↑t ^ 2 / 2))
      = Complex.exp (-↑(variance m0 p) * ↑t ^ 2 / 2) by
    congr 1
    ring]
  exact h

/-- The **second moment** of a one-mode cylinder: `∫ y_p² dμ = variance m₀ p`.
This is the smeared two-point function in Mehler coordinates. -/
theorem second_moment {M : ℕ} (m0 : ℝ) (p : MehlerMode M) :
    ∫ x, (x p) ^ 2 ∂(law m0) = variance m0 p := by
  have hvar : Var[id; gaussianReal 0 ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩]
      = variance m0 p := by
    rw [variance_id_gaussianReal]
    simp
  have hmean : ∫ y, y ∂(gaussianReal 0
      ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩) = 0 := integral_id_gaussianReal
  have h := variance_eq_sub (μ := gaussianReal 0
    ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩) (X := id) (memLp_id_gaussianReal 2)
  simp only [id_eq] at h
  rw [hvar, hmean] at h
  have hsq : ∫ y, y ^ 2 ∂(gaussianReal 0
      ⟨variance m0 p, le_of_lt (variance_pos m0 p)⟩) = variance m0 p := by
    simpa [pow_two] using h.symm
  have hmap : ∫ y, y ^ 2 ∂(Measure.map (Function.eval p) (law m0))
      = ∫ x, (x p) ^ 2 ∂(law m0) :=
    integral_map (μ := law m0) (φ := Function.eval p) (f := fun y : ℝ => y ^ 2)
      (measurable_pi_apply p).aemeasurable
      (by fun_prop : Measurable fun y : ℝ => y ^ 2).aestronglyMeasurable
  rw [marginal m0 p, hsq] at hmap
  exact hmap.symm

/-! ## 3. The Euclidean covariance form and the reflection -/

/-- The **covariance bilinear form** in Mehler coordinates:
`C(f, g) = ∑_p variance p · f p · g p`.  Because the Mehler covariance is diagonal,
this is the complete free two-point function. -/
def covBilin {M : ℕ} (m0 : ℝ) (f g : MehlerMode M → ℝ) : ℝ :=
  ∑ p, variance m0 p * f p * g p

theorem covBilin_self_nonneg {M : ℕ} (m0 : ℝ) (f : MehlerMode M → ℝ) :
    0 ≤ covBilin m0 f f := by
  unfold covBilin
  refine Finset.sum_nonneg fun p _ => ?_
  have h := variance_pos m0 p
  nlinarith [sq_nonneg (f p)]

/-- The **time reflection in Mehler coordinates**: the symmetric mode is
invariant and the antisymmetric mode changes sign, `θ y₊ = y₊`, `θ y₋ = −y₋`. -/
def reflectMehler {M : ℕ} (f : MehlerMode M → ℝ) : MehlerMode M → ℝ :=
  fun p => (if p.1 then 1 else -1) * f p

/-- The reflection is an involution on Mehler coordinates. -/
theorem reflectMehler_involutive {M : ℕ} (f : MehlerMode M → ℝ) :
    reflectMehler (reflectMehler f) = f := by
  funext p
  unfold reflectMehler
  cases p.1 <;> simp

/-- **The Euclidean covariance is reflection invariant**:
`C(θf, θg) = C(f, g)`.  This is the Euclidean-covariance clause of C1: the
reflection is a symmetry of the free two-point function. -/
theorem reflection_invariant {M : ℕ} (m0 : ℝ) (f g : MehlerMode M → ℝ) :
    covBilin m0 (reflectMehler f) (reflectMehler g) = covBilin m0 f g := by
  unfold covBilin reflectMehler
  refine Finset.sum_congr rfl fun p _ => ?_
  cases p.1 <;> norm_num

/-- A **half-space test** supported on the positive-time slice: in Mehler
coordinates `x₀ = (y₊ − y₋)/√2` and `x₁ = (y₊ + y₋)/√2`, so a test that depends
only on `x₁` assigns the same spatial coefficient (up to the immaterial
normalization `1/2`) to both parities. -/
def posTest {M : ℕ} (g : SpatialMode M → ℝ) : MehlerMode M → ℝ :=
  fun p => g p.2 / 2

/-- **Reflected-covariance positivity on half-space tests**: for every spatial
test `g`, `C(θf, f) ≥ 0` where `f = posTest g` is supported on the positive-time
slice.  Expanding over the parity gives
`∑_k (variance (true,k) − variance (false,k)) · g k² / 4 ≥ 0`, whose sign is
`variance_symm_ge_antisymm`. -/
theorem rp_covariance {M : ℕ} (m0 : ℝ) (g : SpatialMode M → ℝ) :
    0 ≤ covBilin m0 (reflectMehler (posTest g)) (posTest g) := by
  unfold covBilin reflectMehler posTest
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun k _ => ?_
  have hge := variance_symm_ge_antisymm m0 k
  have hsq : 0 ≤ g k * g k := mul_self_nonneg (g k)
  nlinarith

/-! ## 4. The negative control: positive covariance, negative reflected form -/

/-- The **swapped** Mehler variance, still strictly positive for every mode, so
its matrix is positive definite.  This is the banded-Toeplitz warning's sign
pattern: a positive-definite covariance need not be reflection positive. -/
def badVariance {M : ℕ} (m0 : ℝ) (p : MehlerMode M) : ℝ :=
  1 / (m0 ^ 2 + spatialEigenvalue p.2 + (if p.1 then 3 else 1))

theorem badVariance_pos {M : ℕ} (m0 : ℝ) (p : MehlerMode M) : 0 < badVariance m0 p := by
  unfold badVariance
  have h : (0 : ℝ) < m0 ^ 2 + spatialEigenvalue p.2 + (if p.1 then 3 else 1) := by
    have h1 := spatialEigenvalue_nonneg p.2
    have h2 : (0 : ℝ) < (if p.1 then (3 : ℝ) else 1) := by
      cases p.1 <;> norm_num
    nlinarith [sq_nonneg m0]
  exact one_div_pos.mpr h

/-- The covariance form of the swapped variance. -/
def badCovBilin {M : ℕ} (m0 : ℝ) (f g : MehlerMode M → ℝ) : ℝ :=
  ∑ p, badVariance m0 p * f p * g p

/-- **A positive-definite covariance with a negative reflected form.**  For the
constant spatial test `g ≡ 1`, the swapped variance makes
`C(θf, f) = ∑_k (1/(λ+3) − 1/(λ+1)) · 1/4 < 0`.  Thus checking that a covariance
matrix is positive definite does not establish reflection positivity, exactly the
point of `HalfSpaceInfiniteBandedCovariance`. -/
theorem bad_rp_fails (m0 : ℝ) (M : ℕ) :
    ∃ g : SpatialMode (M + 1) → ℝ,
      badCovBilin m0 (reflectMehler (posTest g)) (posTest g) < 0 := by
  refine ⟨fun _ => 1, ?_⟩
  unfold badCovBilin reflectMehler posTest
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_neg (fun k _ => ?_) Finset.univ_nonempty
  unfold badVariance
  norm_num
  have h0 := spatialEigenvalue_nonneg k
  have hm := sq_nonneg m0
  have h1 : (0 : ℝ) < m0 ^ 2 + spatialEigenvalue k + 1 := by linarith
  have hlt : (m0 ^ 2 + spatialEigenvalue k + 3)⁻¹
      < (m0 ^ 2 + spatialEigenvalue k + 1)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_lt_one_div_of_lt h1 (by linarith)
  linarith

/-! ## 5. Cutoff consistency of the cylinder laws -/

/-- Inclusion of a spatial mode into the next cutoff. -/
def embedSpatial {M : ℕ} (k : SpatialMode M) : SpatialMode (M + 1) :=
  (Fin.castLE (Nat.le_succ M) k.1, Fin.castLE (Nat.le_succ M) k.2.1,
    Fin.castLE (Nat.le_succ M) k.2.2)

/-- Inclusion of a Mehler mode into the next cutoff. -/
def embedMehler {M : ℕ} (p : MehlerMode M) : MehlerMode (M + 1) :=
  (p.1, embedSpatial p.2)

theorem spatialEigenvalue_embed {M : ℕ} (k : SpatialMode M) :
    spatialEigenvalue (embedSpatial k) = spatialEigenvalue k := by
  unfold spatialEigenvalue embedSpatial
  simp

/-- **The variance is cutoff-independent** on the common modes. -/
theorem variance_embed {M : ℕ} (m0 : ℝ) (p : MehlerMode M) :
    variance m0 (embedMehler p) = variance m0 p := by
  unfold variance embedMehler
  rw [spatialEigenvalue_embed]

/-- **Cylinder consistency across cutoffs**: the one-mode cylinder law of the
`M + 1` cutoff on an embedded mode equals the `M` cutoff's cylinder law.  The two
product laws therefore define one consistent family of finite-dimensional
distributions, which is the free field's cylinder convergence at this level. -/
theorem marginal_embed {M : ℕ} (m0 : ℝ) (p : MehlerMode M) :
    Measure.map (Function.eval (embedMehler p)) (law (M := M + 1) m0)
      = Measure.map (Function.eval p) (law (M := M) m0) := by
  rw [marginal m0 (embedMehler p), marginal m0 p]
  simp [variance_embed]

end BookProof.OSReconstruction
