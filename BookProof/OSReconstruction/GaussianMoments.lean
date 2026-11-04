import Mathlib

/-!
# Gaussian moments and Isserlis' theorem on a finite configuration space

Plan: `cftproof.md`, Phase 3.3.  Phase 3.3 is a *statement about a measure on the lattice
configurations*: reflection positivity needs the expectation of a product of fields, and for a
free (Gaussian) field that expectation is computed by Wick's theorem / Isserlis' theorem.  The
corpus up to now had no such measure — `MomentumBasis.lean`'s boundary note records that the
Gaussian/Wick step from the two-point function to all polynomial observables was missing, and
`ReflectionPositivity.Proof` could therefore only state reflection positivity as a hypothesis.

This module supplies the missing input: the standard Gaussian product measure on a finite
configuration space `ι → ℝ`, the one-dimensional moment recursion derived from Gaussian
integration by parts in the form `∫ y · f = ∫ f'`, and Isserlis' theorem in the form that
fixes a moment by its **multiplicity profile**: a centred Gaussian monomial moment vanishes
unless every coordinate occurs an even number of times, and otherwise is the product of the
double factorials `(m_i - 1)!!` of the multiplicities.

## Contents

* `gaussExp` — the unnormalised standard Gaussian density `exp (-y² / 2)`;
* `hasDerivAt_gaussExp` — `d/dy exp (-y²/2) = -y exp (-y²/2)`, the derivative that makes the
  integration by parts cancel;
* `integrable_pow_mul_gaussExp` — every monomial moment of the density is finite;
* **`integral_pow_mul_gaussExp_succ_succ`** — the one-dimensional Stein recursion
  `∫ y ^ (n + 2) e^{-y²/2} = (n + 1) ∫ y ^ n e^{-y²/2}`;
* `integral_pow_productGauss` — the same recursion for `gaussianReal 0 1`, with the normalisation
  constant carried explicitly;
* **`integral_pow_productGauss_two_mul` / `..._two_mul_add_one`** — the closed forms
  `∫ y ^ (2n) γ(dy) = (2n - 1)‼` and `∫ y ^ (2n + 1) γ(dy) = 0`;
* `productGauss` — the product measure on `ι → ℝ`, with its probability instance;
* **`integral_prod_pow_productGauss`** — the coordinate factorisation: the moment of a product of
  powers of the coordinates is the product of the one-dimensional moments;
* **`integral_prod_coord_productGauss`** — **Isserlis' theorem**: for any family of sites
  `f : Fin m → ι`, the moment `E[∏ k, x (f k)]` depends only on the multiplicities of `f`, and
  equals `∏ i, (m_i - 1)‼` when every multiplicity `m_i` is even, `0` otherwise.

## General covariance (the pairing form)

* `pairings N` — the pairings of `{0, …, N-1}`: fixed-point-free involutions;
* `pairingSet s` / `wickSum c s` — the involutions with support exactly `s`, and the Wick sum
  `∑_{σ} ∏_{a < σ a} c a (σ a)` over them;
* `mem_pairingSet`, `pairingSet_empty`, `wickSum_empty`, `fwd_mem`, `bwd_mem`, `prod_fwd`,
  **`wickSum_rec`** — the recursion `wickSum c s = ∑_{b ∈ s \ {min s}} c (min s) b * wickSum c (s \ {min s, b})`,
  obtained by the `σ ↦ swap (min s) b * σ` bijection on pairings;
* `gw`, `prod_pdf`, `pi_gauss_eq`, `integral_pi_gauss` — the standard product Gaussian as a
  Lebesgue density, with its normalisation constant carried explicitly;
* `hasLineDerivAt_gw`, `hasLineDerivAt_lin`, `integrable_gw_mul`, `stein_vol`, `stein_pi` — the
  Stein recursion for a product of linear forms, `∫ ∏_{j ∈ s} (w j ⬝ y) = ∑_{b ∈ s \ {a₀}} (w a₀ ⬝ w b) ∫ ∏_{j ∈ s \ {a₀, b}} (w j ⬝ y)`;
* **`wick_pi`** — `E[∏_{j ∈ s} (w j ⬝ y)] = wickSum (fun a b => w a ⬝ w b) s`;
* `pairingSet_univ_even` / `pairingSet_univ_odd` — the pairings of a full `Fin (2m)` are
  `pairings (2m)`, and `Fin (2m + 1)` carries none (an involution has even support);
* `gaussLaw A` — the centred Gaussian on `Fin N → ℝ` of covariance `A * Aᵀ`, the law of `A *ᵥ y`;
* **`integral_prod_coord_gaussLaw`** — the moment recursion in the general covariance;
* **`isserlis_gaussLaw`** — **Isserlis' theorem, general covariance**:
  `E[∏ k, z (μs k)] = ∑_{p ∈ pairings (2m)} ∏_{k < p k} (A Aᵀ) (μs k) (μs (p k))`, and the odd
  moments vanish;
* `multivariateGaussian K` — the Gaussian of covariance `K = √K √Kᵀ` (the local form of Mathlib's
  later `multivariateGaussian 0 K`, absent from the pinned toolchain);
* `sqrt_mul_transpose_sqrt` — `√K * √Kᵀ = K` for `K` positive semidefinite;
* **`isserlis_multivariateGaussian`** — the same statement with the covariance `K` itself.

The general-covariance half is ported from the accepted prove2.me solution of
`LesHouchesWidth.wick_theorem` (Nickrobbins95, 2026-09-26), whose proof is the route above; the
only adaptation is that the law is realised here as a linear image of independent standard
Gaussians rather than through `multivariateGaussian`, which this Mathlib does not have.

## Boundary

Both forms are now proved: the multiplicity form for the standard product measure, and the pairing
form — `E[∏_k X (p k)] = ∑_{pairings σ} ∏_{pairs {a,b}} C (p a) (p b)` for a Gaussian field of
covariance `C`, the form the Källén–Lehmann matching in `MomentumBasis.lean` consumes — for the
Gaussian of covariance `A Aᵀ`, resp. `K` positive semidefinite.  What is *not* here: a Gaussian
measure presented abstractly through its two-point function rather than as an explicit linear image
(the serviceable route for the lattice field is the one formalised: pick the covariance's square
root), and any statement about the continuum.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real Nat

noncomputable section

/-! ## 1. The one-dimensional density and its moment recursion -/

/-- The unnormalised standard Gaussian density `y ↦ exp (-y² / 2)`. -/
def gaussExp (y : ℝ) : ℝ := Real.exp (-(2 : ℝ)⁻¹ * y ^ 2)

/-- **The derivative of the Gaussian density**: `d/dy exp (-y²/2) = -y exp (-y²/2)`.  This is the
identity that makes Gaussian integration by parts into a moment recursion. -/
theorem hasDerivAt_gaussExp (y : ℝ) : HasDerivAt gaussExp (-(y * gaussExp y)) y := by
  have h : HasDerivAt (fun t : ℝ => -(2 : ℝ)⁻¹ * t ^ 2) (-y) y := by
    have h0 := (hasDerivAt_pow 2 y).const_mul (-(2 : ℝ)⁻¹)
    convert h0 using 1
    ring
  have h1 := h.exp
  unfold gaussExp
  convert h1 using 1
  ring

theorem continuous_gaussExp : Continuous gaussExp := by
  unfold gaussExp; fun_prop

/-- Every monomial moment of the Gaussian density is finite. -/
theorem integrable_pow_mul_gaussExp (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n * gaussExp y) := by
  have hn : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (2 : ℝ)⁻¹) (by norm_num) (s := (n : ℝ)) hn
  simpa [gaussExp, Real.rpow_natCast, mul_comm] using h

/-! ## 2. Gaussian integration by parts -/

/-- **The one-dimensional Stein recursion** for the unnormalised density:
`∫ y ^ (n + 2) exp (-y²/2) dy = (n + 1) ∫ y ^ n exp (-y²/2) dy`.

This is integration by parts with `u = exp (-y²/2)`, whose derivative `-y exp (-y²/2)` is exactly
the weight that turns `y ^ (n + 2)` into `y ^ (n + 1) · y`.  The boundary term vanishes because a
polynomial times `exp (-y²/2)` is integrable, so the product tends to `0` at both ends. -/
theorem integral_pow_mul_gaussExp_succ_succ (n : ℕ) :
    (∫ y : ℝ, y ^ (n + 2) * gaussExp y) =
      (n + 1 : ℝ) * ∫ y : ℝ, y ^ n * gaussExp y := by
  have hu : ∀ y : ℝ, HasDerivAt gaussExp (-(y * gaussExp y)) y := hasDerivAt_gaussExp
  have hv : ∀ y : ℝ, HasDerivAt (fun t : ℝ => t ^ (n + 1)) ((n + 1 : ℝ) * y ^ n) y := by
    intro y
    simpa [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hasDerivAt_pow (n + 1) y
  have huv' : Integrable (fun y : ℝ => gaussExp y * ((n + 1 : ℝ) * y ^ n)) := by
    have := (integrable_pow_mul_gaussExp n).const_mul ((n + 1 : ℝ))
    refine this.congr ?_
    filter_upwards with y
    ring
  have hu'v : Integrable (fun y : ℝ => -(y * gaussExp y) * y ^ (n + 1)) := by
    have hbase := (integrable_pow_mul_gaussExp (n + 2)).neg
    refine hbase.congr ?_
    filter_upwards with y
    simp only [Pi.neg_apply]
    rw [pow_succ]
    ring
  have huv : Integrable (fun y : ℝ => gaussExp y * y ^ (n + 1)) := by
    have := integrable_pow_mul_gaussExp (n + 1)
    refine this.congr ?_
    filter_upwards with y
    ring
  have h := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := gaussExp) (u' := fun y => -(y * gaussExp y))
    (v := fun y => y ^ (n + 1)) (v' := fun y => (n + 1 : ℝ) * y ^ n) hu hv huv' hu'v huv
  -- `h : ∫ y, gaussExp y * ((n+1) * y^n) = - ∫ y, (-(y * gaussExp y)) * y^(n+1)`
  rw [show (fun y : ℝ => gaussExp y * ((n + 1 : ℝ) * y ^ n)) =
      fun y => ((n + 1 : ℝ)) * (y ^ n * gaussExp y) from by
    funext y; ring] at h
  rw [integral_const_mul] at h
  rw [show (fun y : ℝ => -(y * gaussExp y) * y ^ (n + 1)) =
      fun y => -(y ^ (n + 2) * gaussExp y) from by
    funext y
    rw [pow_succ]
    ring] at h
  rw [integral_neg] at h
  linarith

/-! ## 3. The standard Gaussian measure and its moments -/

/-- The standard Gaussian measure as a density integral: the normalisation constant
`(√(2π))⁻¹` is carried explicitly. -/
theorem integral_pow_gaussianReal_one (n : ℕ) :
    (∫ y : ℝ, y ^ n ∂(gaussianReal 0 1)) =
      (√(2 * π))⁻¹ * ∫ y : ℝ, y ^ n * gaussExp y := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  simp only [gaussExp]
  ring

/-- **The one-dimensional moment recursion for the standard Gaussian**:
`∫ y ^ (n + 2) γ(dy) = (n + 1) ∫ y ^ n γ(dy)`. -/
theorem integral_pow_gaussianReal_one_succ_succ (n : ℕ) :
    (∫ y : ℝ, y ^ (n + 2) ∂(gaussianReal 0 1)) =
      (n + 1 : ℝ) * ∫ y : ℝ, y ^ n ∂(gaussianReal 0 1) := by
  rw [integral_pow_gaussianReal_one, integral_pow_gaussianReal_one,
    integral_pow_mul_gaussExp_succ_succ]
  ring

/-- The even moments of the standard Gaussian are the odd double factorials. -/
theorem integral_pow_gaussianReal_one_two_mul (k : ℕ) :
    (∫ y : ℝ, y ^ (2 * k) ∂(gaussianReal 0 1)) = ((2 * k - 1)‼ : ℝ) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h := integral_pow_gaussianReal_one_succ_succ (2 * k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    rw [h, ih, show 2 * k + 2 - 1 = 2 * k + 1 by omega,
      Nat.doubleFactorial_add_one (2 * k)]
    push_cast
    ring

/-- The odd moments of the standard Gaussian vanish. -/
theorem integral_pow_gaussianReal_one_two_mul_add_one (k : ℕ) :
    (∫ y : ℝ, y ^ (2 * k + 1) ∂(gaussianReal 0 1)) = 0 := by
  induction k with
  | zero =>
    simp [integral_id_gaussianReal]
  | succ k ih =>
    have h := integral_pow_gaussianReal_one_succ_succ (2 * k + 1)
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, h, ih, mul_zero]

/-- **The moment of the standard Gaussian is fixed by the parity of the exponent**: even moments
are the double factorials `(n - 1)‼`, odd moments vanish. -/
theorem integral_pow_gaussianReal_one_moment (n : ℕ) :
    (∫ y : ℝ, y ^ n ∂(gaussianReal 0 1)) = if Even n then ((n - 1)‼ : ℝ) else 0 := by
  by_cases h : Even n
  · obtain ⟨k, hk⟩ := h
    subst hk
    rw [show k + k = 2 * k by omega,
      if_pos (show Even (2 * k) from ⟨k, by omega⟩), integral_pow_gaussianReal_one_two_mul]
  · have ho : Odd n := Nat.not_even_iff_odd.mp h
    obtain ⟨k, hk⟩ := ho
    subst hk
    rw [if_neg (by omega : ¬ Even (2 * k + 1)), integral_pow_gaussianReal_one_two_mul_add_one]

/-! ## 4. The product measure on a finite configuration space -/

/-- **The standard Gaussian product measure** on the configurations `ι → ℝ`: independent standard
Gaussians on each coordinate.  This is the measure whose polynomial moments are Wick's theorem. -/
def productGauss (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance instIsProbabilityMeasureProductGauss (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (productGauss ι) := by
  unfold productGauss
  infer_instance

/-- **Coordinate factorisation**: the moment of a monomial is the product of the one-dimensional
moments of its coordinate powers. -/
theorem integral_prod_pow_productGauss {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ m i ∂(productGauss ι)) =
      ∏ i, ∫ y : ℝ, y ^ (m i) ∂(gaussianReal 0 1) := by
  simpa [productGauss] using
    integral_fintype_prod_eq_prod (μ := fun _ : ι => gaussianReal 0 1)
      (f := fun i y => y ^ m i)

/-- A product of coordinates depends only on the multiplicities of the sites: regrouping the
product over the fibres of the site map. -/
theorem prod_coord_eq_prod_pow_card {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (f : Fin m → ι) (x : ι → ℝ) :
    (∏ k, x (f k)) = ∏ j, x j ^ Fintype.card {k : Fin m // f k = j} := by
  rw [← Finset.prod_fiberwise' (g := f) (f := fun j => x j)]
  simp only [Finset.prod_const]
  simp [Fintype.card_subtype]

/-- **Isserlis' theorem, multiplicity form.**  The Gaussian moment of a product of fields at the
sites `f : Fin m → ι` is the product of the one-dimensional moments of the multiplicities: it
vanishes unless every site occurs an even number of times, and otherwise is the product of the
double factorials `(m_j - 1)‼`. -/
theorem integral_prod_coord_productGauss {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (f : Fin m → ι) :
    (∫ x : ι → ℝ, ∏ k, x (f k) ∂(productGauss ι)) =
      ∏ j, ∫ y : ℝ, y ^ Fintype.card {k : Fin m // f k = j} ∂(gaussianReal 0 1) := by
  rw [← integral_prod_pow_productGauss (ι := ι) (m := fun j => Fintype.card {k : Fin m // f k = j})]
  congr 1
  funext x
  exact prod_coord_eq_prod_pow_card f x

/-- **Isserlis' theorem in closed form**: the moment is `∏ j, (m_j - 1)‼` when every multiplicity
is even and `0` otherwise. -/
theorem isserlis_productGauss {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (f : Fin m → ι) :
    (∫ x : ι → ℝ, ∏ k, x (f k) ∂(productGauss ι)) =
      ∏ j, if Even (Fintype.card {k : Fin m // f k = j})
        then ((Fintype.card {k : Fin m // f k = j} - 1)‼ : ℝ) else 0 := by
  rw [integral_prod_coord_productGauss]
  exact Finset.prod_congr rfl fun j _ => integral_pow_gaussianReal_one_moment _

/-- A monomial moment vanishes when some site occurs an odd number of times. -/
theorem integral_prod_coord_productGauss_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (f : Fin m → ι) (j : ι) (hj : Odd (Fintype.card {k : Fin m // f k = j})) :
    (∫ x : ι → ℝ, ∏ k, x (f k) ∂(productGauss ι)) = 0 := by
  rw [isserlis_productGauss]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [if_neg (by
    rintro hE
    obtain ⟨a, ha⟩ := hj
    obtain ⟨b, hb⟩ := hE
    omega)]

/-- The moments of a single coordinate, read off from Isserlis' theorem: only that coordinate
carries a multiplicity. -/
theorem integral_pow_coord_productGauss {ι : Type*} [Fintype ι] (i : ι) (k : ℕ) :
    (∫ x : ι → ℝ, (x i) ^ k ∂(productGauss ι)) =
      if Even k then ((k - 1)‼ : ℝ) else 0 := by
  classical
  have h : (∫ x : ι → ℝ, ∏ j, x j ^ (if j = i then k else 0) ∂(productGauss ι)) =
      if Even k then ((k - 1)‼ : ℝ) else 0 := by
    rw [integral_prod_pow_productGauss]
    rw [Finset.prod_eq_single i]
    · simpa using integral_pow_gaussianReal_one_moment k
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hfun : (fun x : ι → ℝ => ∏ j, x j ^ (if j = i then k else 0)) =
      fun x => (x i) ^ k := by
    funext x
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hfun]
  exact h

/-- The square of a single coordinate has unit second moment: `E[x_i²] = 1`. -/
theorem integral_sq_coord_productGauss {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, (x i) ^ 2 ∂(productGauss ι)) = 1 := by
  classical
  simpa using integral_pow_coord_productGauss (ι := ι) i 2

/-- Odd moments of a single coordinate vanish: `E[x_i³] = 0`. -/
theorem integral_cube_coord_productGauss {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, (x i) ^ 3 ∂(productGauss ι)) = 0 := by
  classical
  simpa using integral_pow_coord_productGauss (ι := ι) i 3

/-- The fourth moment of a coordinate: `E[x_i⁴] = 3`. -/
theorem integral_pow_four_coord_productGauss {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, (x i) ^ 4 ∂(productGauss ι)) = 3 := by
  classical
  simpa using integral_pow_coord_productGauss (ι := ι) i 4


open Finset Matrix
open scoped RealInnerProductSpace MatrixOrder

/-! ## 5. Pairings, the Wick sum, and the pairing recursion -/

/-- The pairings of `{0, …, N-1}`: fixed-point-free involutions `π` (`π (π k) = k`, `π k ≠ k`). -/
def pairings (N : ℕ) : Finset (Equiv.Perm (Fin N)) :=
  Finset.univ.filter fun p => ∀ k, p (p k) = k ∧ p k ≠ k

section comb

variable {M : ℕ}

/-- The involutions with support exactly `s`: the pairings of the subset `s`. -/
def pairingSet (s : Finset (Fin M)) : Finset (Equiv.Perm (Fin M)) :=
  Finset.univ.filter (fun σ => σ * σ = 1 ∧ σ.support = s)

/-- The Wick sum over the pairings of `s`, with edge weights `c`. -/
def wickSum (c : Fin M → Fin M → ℝ) (s : Finset (Fin M)) : ℝ :=
  ∑ σ ∈ pairingSet s, ∏ a ∈ s.filter (fun a => a < σ a), c a (σ a)

lemma mem_pairingSet {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)} :
    σ ∈ pairingSet s ↔ σ * σ = 1 ∧ σ.support = s := by simp [pairingSet]

lemma pairingSet_empty : pairingSet (∅ : Finset (Fin M)) = {1} := by
  ext σ
  simp only [pairingSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.support_eq_empty_iff, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl; simp

lemma wickSum_empty (c : Fin M → Fin M → ℝ) : wickSum c (∅ : Finset (Fin M)) = 1 := by
  simp [wickSum, pairingSet_empty]

lemma invol_apply {σ : Equiv.Perm (Fin M)} (h : σ * σ = 1) (x : Fin M) : σ (σ x) = x := by
  simpa using congrArg (fun τ : Equiv.Perm (Fin M) => τ x) h

lemma swap_mul_apply_fwd {σ : Equiv.Perm (Fin M)} (h : σ * σ = 1) {a₀ b : Fin M}
    (hb : σ a₀ = b) (x : Fin M) :
    (Equiv.swap a₀ b * σ) x = if x = a₀ ∨ x = b then x else σ x := by
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  rw [Equiv.Perm.mul_apply]
  by_cases hx0 : x = a₀
  · subst hx0; simp [hb]
  by_cases hxb : x = b
  · subst hxb; simp [hσb]
  have h1 : σ x ≠ a₀ := by
    intro h'; apply hxb; rw [← invol_apply h x, h', hb]
  have h2 : σ x ≠ b := by
    intro h'; apply hx0; rw [← hb] at h'; exact σ.injective h'
  simp [hx0, hxb, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma fwd_mem {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)} (hσ : σ ∈ pairingSet s)
    {a₀ b : Fin M} (ha₀ : a₀ ∈ s) (hb : σ a₀ = b) :
    Equiv.swap a₀ b * σ ∈ pairingSet ((s.erase a₀).erase b) := by
  rw [mem_pairingSet] at hσ ⊢
  obtain ⟨h, hs⟩ := hσ
  have hne : σ a₀ ≠ a₀ := by rw [← Equiv.Perm.mem_support, hs]; exact ha₀
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  have key := swap_mul_apply_fwd h hb
  constructor
  · ext x
    rw [Equiv.Perm.mul_apply, key x, Equiv.Perm.one_apply]
    by_cases hx : x = a₀ ∨ x = b
    · simp [hx, key]
    · rw [if_neg hx, key (σ x)]
      have : ¬ (σ x = a₀ ∨ σ x = b) := by
        rintro (h' | h')
        · apply hx; right; rw [← invol_apply h x, h', hb]
        · apply hx; left; rw [← hb] at h'; exact σ.injective h'
      rw [if_neg this, invol_apply h]
  · ext x
    rw [Equiv.Perm.mem_support, key x, Finset.mem_erase, Finset.mem_erase, ← hs,
      Equiv.Perm.mem_support]
    by_cases hx0 : x = a₀
    · subst hx0; simp
    by_cases hxb : x = b
    · subst hxb; simp
    simp [hx0, hxb]

lemma bwd_mem {s : Finset (Fin M)} {τ : Equiv.Perm (Fin M)} {a₀ b : Fin M}
    (ha₀ : a₀ ∈ s) (hb : b ∈ s.erase a₀) (hτ : τ ∈ pairingSet ((s.erase a₀).erase b)) :
    Equiv.swap a₀ b * τ ∈ pairingSet s ∧ (Equiv.swap a₀ b * τ) a₀ = b := by
  rw [mem_pairingSet] at hτ ⊢
  obtain ⟨h, hs⟩ := hτ
  have hba : b ≠ a₀ := (Finset.mem_erase.1 hb).1
  have hbs : b ∈ s := (Finset.mem_erase.1 hb).2
  have hτa : τ a₀ = a₀ := by
    by_contra hc
    have := Equiv.Perm.mem_support.2 hc; rw [hs] at this; simp at this
  have hτb : τ b = b := by
    by_contra hc
    have := Equiv.Perm.mem_support.2 hc; rw [hs] at this; simp at this
  have hmid : ∀ x, x ≠ a₀ → x ≠ b → τ x ≠ a₀ ∧ τ x ≠ b := by
    intro x h0 h1
    refine ⟨fun h' => h0 (τ.injective (h'.trans hτa.symm)),
      fun h' => h1 (τ.injective (h'.trans hτb.symm))⟩
  have key : ∀ x, (Equiv.swap a₀ b * τ) x = if x = a₀ then b else if x = b then a₀ else τ x := by
    intro x
    rw [Equiv.Perm.mul_apply]
    by_cases h0 : x = a₀
    · subst h0; simp [hτa]
    by_cases h1 : x = b
    · subst h1; simp [hτb, hba]
    obtain ⟨m0, m1⟩ := hmid x h0 h1
    simp [h0, h1, Equiv.swap_apply_of_ne_of_ne m0 m1]
  refine ⟨⟨?_, ?_⟩, by simp [key]⟩
  · ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases h0 : x = a₀
    · subst h0; simp [key, hba]
    by_cases h1 : x = b
    · subst h1; simp [key, hba]
    obtain ⟨m0, m1⟩ := hmid x h0 h1
    rw [key x, if_neg h0, if_neg h1, key (τ x), if_neg m0, if_neg m1, invol_apply h]
  · ext x
    rw [Equiv.Perm.mem_support, key x]
    by_cases h0 : x = a₀
    · subst h0; simp [hba, ha₀]
    by_cases h1 : x = b
    · subst h1; simp [hba, hbs]; exact fun h => hba h.symm
    rw [if_neg h0, if_neg h1, ← Equiv.Perm.mem_support, hs]
    simp [h0, h1]

lemma prod_fwd (c : Fin M → Fin M → ℝ) {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)}
    (hσ : σ ∈ pairingSet s) {a₀ b : Fin M} (ha₀ : a₀ ∈ s) (hmin : ∀ x ∈ s, a₀ ≤ x)
    (hb : σ a₀ = b) :
    ∏ a ∈ s.filter (fun a => a < σ a), c a (σ a) =
      c a₀ b * ∏ a ∈ ((s.erase a₀).erase b).filter (fun a => a < (Equiv.swap a₀ b * σ) a),
        c a ((Equiv.swap a₀ b * σ) a) := by
  rw [mem_pairingSet] at hσ
  obtain ⟨h, hs⟩ := hσ
  have hsupp : a₀ ∈ σ.support := by rw [hs]; exact ha₀
  have hne : σ a₀ ≠ a₀ := Equiv.Perm.mem_support.1 hsupp
  have hbs : b ∈ s.erase a₀ := by
    rw [Finset.mem_erase, ← hb]
    exact ⟨hne, by rw [← hs]; exact Equiv.Perm.apply_mem_support.2 hsupp⟩
  have hab : a₀ < b :=
    lt_of_le_of_ne (hmin b (Finset.mem_of_mem_erase hbs)) (by rw [← hb]; exact hne.symm)
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  have key := swap_mul_apply_fwd h hb
  rw [Finset.prod_filter, Finset.prod_filter]
  conv_lhs => rw [← Finset.insert_erase ha₀, ← Finset.insert_erase hbs]
  rw [Finset.prod_insert (by simp [hab.ne]), Finset.prod_insert (by simp)]
  rw [hb, if_pos hab, hσb, if_neg (not_lt.2 hab.le), one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hxb : x ≠ b := (Finset.mem_erase.1 hx).1
  have hx0 : x ≠ a₀ := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
  have : ¬ (x = a₀ ∨ x = b) := by tauto
  rw [key x, if_neg this]

lemma wickSum_rec (c : Fin M → Fin M → ℝ) {s : Finset (Fin M)} (hs : s.Nonempty) :
    wickSum c s = ∑ b ∈ s.erase (s.min' hs),
      c (s.min' hs) b * wickSum c ((s.erase (s.min' hs)).erase b) := by
  have ha₀ : s.min' hs ∈ s := Finset.min'_mem s hs
  have hmin : ∀ x ∈ s, s.min' hs ≤ x := fun x hx => Finset.min'_le s x hx
  unfold wickSum
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin M) => σ (s.min' hs))
    (t := s.erase (s.min' hs))]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun σ => Equiv.swap (s.min' hs) b * σ)
      (fun τ => Equiv.swap (s.min' hs) b * τ)
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact fwd_mem hσ.1 ha₀ hσ.2
    · intro τ hτ
      obtain ⟨h1, h2⟩ := bwd_mem ha₀ hb hτ
      exact Finset.mem_filter.2 ⟨h1, h2⟩
    · intro σ _; simp [Equiv.swap_mul_self_mul]
    · intro τ _; simp [Equiv.swap_mul_self_mul]
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact prod_fwd c hσ.1 ha₀ hmin hσ.2
  · intro σ hσ
    rw [mem_pairingSet] at hσ
    have hsupp : s.min' hs ∈ σ.support := by rw [hσ.2]; exact ha₀
    rw [Finset.mem_erase]
    have h2 := Equiv.Perm.apply_mem_support.2 hsupp
    rw [hσ.2] at h2
    exact ⟨Equiv.Perm.mem_support.1 hsupp, h2⟩

end comb

/-! ## 6. The standard Gaussian on `Fin N → ℝ` and its Lebesgue density -/

section dens

variable {N : ℕ}

/-- Unnormalised standard Gaussian weight. -/
noncomputable def gw (y : Fin N → ℝ) : ℝ := Real.exp (-(∑ i, y i ^ 2) / 2)

lemma prod_pdf (y : Fin N → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (y i) = (Real.sqrt (2 * Real.pi))⁻¹ ^ N * gw y := by
  simp only [gaussianPDFReal, gw, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma pi_gauss_eq :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (volume : Measure (Fin N → ℝ)).withDensity
        (fun y => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) := by
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    setIntegral_nonneg (hs i) fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  have hint : Integrable (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) := by
    have := Integrable.fintype_prod (f := fun (_ : Fin N) (x : ℝ) => gaussianPDFReal 0 1 x)
      (μ := fun _ => volume) (fun _ => integrable_gaussianPDFReal 0 1)
    simpa [← volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  rw [← integral_indicator hbox]
  have hind : (Set.univ.pi s).indicator (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) =
      fun y => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (y i) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hy i trivial) _).symm
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by simpa [Set.mem_pi] using hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator (hs _)]

lemma integral_pi_gauss (g : (Fin N → ℝ) → ℝ) :
    ∫ y, g y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ N * ∫ y, gw y * g y := by
  have hm : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  rw [pi_gauss_eq, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    prod_pdf, smul_eq_mul, mul_assoc]

end dens

/-! ## 7. Gaussian integration by parts for products of linear forms -/

section stein

variable {N : ℕ}

lemma hasLineDerivAt_gw (y v : Fin N → ℝ) :
    HasLineDerivAt ℝ gw (-(v ⬝ᵥ y) * gw y) y v := by
  have h1 : HasDerivAt (fun t : ℝ => ∑ i, (y i + t * v i) ^ 2) (∑ i, 2 * y i * v i) 0 := by
    apply HasDerivAt.fun_sum; intro i _
    have hl : HasDerivAt (fun t : ℝ => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (y i)
    refine (hl.fun_pow 2).congr_deriv ?_
    simp
  have h3 : HasDerivAt (fun t : ℝ => gw (y + t • v))
      (Real.exp (-(∑ i, (y i + 0 * v i) ^ 2) / 2) * (-(∑ i, 2 * y i * v i) / 2)) 0 :=
    ((h1.neg).div_const 2).exp
  refine h3.congr_deriv ?_
  simp only [zero_mul, add_zero, gw, dotProduct]
  have : ∑ i, 2 * y i * v i = 2 * ∑ i, v i * y i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

lemma hasLineDerivAt_lin {ι : Type*} [DecidableEq ι] (t : Finset ι) (w : ι → Fin N → ℝ)
    (y v : Fin N → ℝ) :
    HasLineDerivAt ℝ (fun y : Fin N → ℝ => ∏ j ∈ t, w j ⬝ᵥ y)
      (∑ b ∈ t, (w b ⬝ᵥ v) * ∏ j ∈ t.erase b, w j ⬝ᵥ y) y v := by
  have := HasDerivAt.fun_finset_prod (u := t)
    (f := fun j (τ : ℝ) => w j ⬝ᵥ y + τ * (w j ⬝ᵥ v))
    (f' := fun j => w j ⬝ᵥ v) (x := 0) (fun j _ => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w j ⬝ᵥ v)).const_add (w j ⬝ᵥ y))
  have hfun : (fun τ : ℝ => ∏ j ∈ t, w j ⬝ᵥ (y + τ • v)) =
      fun τ => ∏ j ∈ t, (w j ⬝ᵥ y + τ * (w j ⬝ᵥ v)) := by
    funext τ
    simp [dotProduct_add, dotProduct_smul]
  unfold HasLineDerivAt
  rw [hfun]
  refine this.congr_deriv ?_
  simp [mul_comm]

lemma integrable_one_add_abs_pow_mul_exp {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ k * Real.exp (-b * x ^ 2)) := by
  have h : ∀ x : ℝ, (1 + |x|) ^ k * Real.exp (-b * x ^ 2) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (|x| ^ j * Real.exp (-b * x ^ 2)) := by
    intro x
    rw [add_comm, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; simp only [one_pow, mul_one]; ring
  simp_rw [h]
  apply integrable_finset_sum
  intro j _
  apply Integrable.const_mul
  have := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (j : ℝ))
    (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast, abs_of_pos (Real.exp_pos _)]

lemma abs_le_prod_one_add (z : Fin N → ℝ) (j : Fin N) : |z j| ≤ ∏ i, (1 + |z i|) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => 1 + |z i|) (Finset.mem_univ j)]
  have h1 : 1 ≤ ∏ i ∈ Finset.univ.erase j, (1 + |z i|) := by
    have hbase : ∏ i ∈ Finset.univ.erase j, (1 : ℝ) ≤ ∏ i ∈ Finset.univ.erase j, (1 + |z i|) :=
      Finset.prod_le_prod (fun i _ => by norm_num) (fun i _ => by linarith [abs_nonneg (z i)])
    simpa using hbase
  nlinarith [abs_nonneg (z j)]

lemma abs_dot_le (u z : Fin N → ℝ) : |u ⬝ᵥ z| ≤ (∑ l, |u l|) * ∏ i, (1 + |z i|) := by
  calc |u ⬝ᵥ z| ≤ ∑ l, |u l * z l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |u l| * ∏ i, (1 + |z i|) := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_prod_one_add z l) (abs_nonneg _)
    _ = (∑ l, |u l|) * ∏ i, (1 + |z i|) := (Finset.sum_mul _ _ _).symm

lemma abs_prod_dot_le {ι : Type*} (t : Finset ι) (w : ι → Fin N → ℝ) (z : Fin N → ℝ) :
    |∏ j ∈ t, w j ⬝ᵥ z| ≤ (∏ j ∈ t, ∑ l, |w j l|) * ∏ i, (1 + |z i|) ^ t.card := by
  rw [Finset.abs_prod, Finset.prod_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => abs_dot_le _ _)

lemma continuous_prod_dot {ι : Type*} (t : Finset ι) (w : ι → Fin N → ℝ) :
    Continuous (fun y : Fin N → ℝ => ∏ j ∈ t, w j ⬝ᵥ y) := by
  simp only [dotProduct]; fun_prop

lemma continuous_gw : Continuous (gw (N := N)) := by
  unfold gw; fun_prop

lemma integrable_gw_mul {ι : Type*} (t : Finset ι) (w : ι → Fin N → ℝ) :
    Integrable (fun y => gw y * ∏ j ∈ t, w j ⬝ᵥ y) := by
  have hdom : Integrable (fun z : Fin N → ℝ =>
      ∏ i, ((1 + |z i|) ^ t.card * Real.exp (-(1 / 2) * z i ^ 2))) := by
    have := Integrable.fintype_prod
      (f := fun (_ : Fin N) (x : ℝ) => (1 + |x|) ^ t.card * Real.exp (-(1 / 2) * x ^ 2))
      (μ := fun _ => volume)
      (fun _ => integrable_one_add_abs_pow_mul_exp (by norm_num) t.card)
    simpa [← volume_pi] using this
  refine (hdom.const_mul (∏ j ∈ t, ∑ l, |w j l|)).mono'
    (continuous_gw.mul (continuous_prod_dot t w)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, gw, abs_of_pos (Real.exp_pos _), Finset.prod_mul_distrib,
    ← Real.exp_sum]
  have hexp : -(∑ i, z i ^ 2) / 2 = ∑ i, -(1 / 2) * z i ^ 2 := by
    rw [← Finset.mul_sum]; ring
  rw [hexp]
  calc Real.exp (∑ i, -(1 / 2) * z i ^ 2) * |∏ j ∈ t, w j ⬝ᵥ z|
      ≤ Real.exp (∑ i, -(1 / 2) * z i ^ 2) *
          ((∏ j ∈ t, ∑ l, |w j l|) * ∏ i, (1 + |z i|) ^ t.card) :=
        mul_le_mul_of_nonneg_left (abs_prod_dot_le t w z) (Real.exp_pos _).le
    _ = _ := by ring

lemma stein_vol {ι : Type*} [DecidableEq ι] (w : ι → Fin N → ℝ) {s : Finset ι} {a₀ : ι}
    (ha₀ : a₀ ∈ s) :
    ∫ y, gw y * ∏ j ∈ s, w j ⬝ᵥ y =
      ∑ b ∈ s.erase a₀, (w a₀ ⬝ᵥ w b) * ∫ y, gw y * ∏ j ∈ (s.erase a₀).erase b, w j ⬝ᵥ y := by
  have hsplit : ∀ y : Fin N → ℝ,
      ∏ j ∈ s, w j ⬝ᵥ y = (w a₀ ⬝ᵥ y) * ∏ j ∈ s.erase a₀, w j ⬝ᵥ y :=
    fun y => (Finset.mul_prod_erase s (fun j => w j ⬝ᵥ y) ha₀).symm
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin N → ℝ))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := gw) (f' := fun y => -(w a₀ ⬝ᵥ y) * gw y)
    (g := fun y => ∏ j ∈ s.erase a₀, w j ⬝ᵥ y)
    (g' := fun y => ∑ b ∈ s.erase a₀, (w b ⬝ᵥ w a₀) * ∏ j ∈ (s.erase a₀).erase b, w j ⬝ᵥ y)
    (v := w a₀) ?_ ?_ ?_
    (fun y => hasLineDerivAt_gw y (w a₀))
    (fun y => hasLineDerivAt_lin (s.erase a₀) w y (w a₀))
  · simp only [ContinuousLinearMap.mul_apply'] at hibp
    have hL : ∫ y, gw y * ∏ j ∈ s, w j ⬝ᵥ y =
        -∫ y, -(w a₀ ⬝ᵥ y) * gw y * ∏ j ∈ s.erase a₀, w j ⬝ᵥ y := by
      rw [← integral_neg]
      congr 1; funext y; rw [hsplit]; ring
    rw [hL, ← hibp]
    simp_rw [Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl; intro b _
      rw [← integral_const_mul, dotProduct_comm (w b)]
      congr 1; funext y; ring
    · intro b _
      exact ((integrable_gw_mul _ w).const_mul (w b ⬝ᵥ w a₀)).congr
        (Filter.Eventually.of_forall fun y => by simp only; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact (integrable_gw_mul s w).neg.congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.neg_apply]; rw [hsplit]; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    simp_rw [Finset.mul_sum]
    apply integrable_finset_sum
    intro b _
    exact ((integrable_gw_mul _ w).const_mul (w b ⬝ᵥ w a₀)).congr
      (Filter.Eventually.of_forall fun y => by simp only; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact integrable_gw_mul _ w

/-- Stein recursion under the product of standard Gaussians. -/
lemma stein_pi {ι : Type*} [DecidableEq ι] (w : ι → Fin N → ℝ) {s : Finset ι} {a₀ : ι}
    (ha₀ : a₀ ∈ s) :
    ∫ y, ∏ j ∈ s, w j ⬝ᵥ y ∂(productGauss (Fin N)) =
      ∑ b ∈ s.erase a₀, (w a₀ ⬝ᵥ w b) *
        ∫ y, ∏ j ∈ (s.erase a₀).erase b, w j ⬝ᵥ y ∂(productGauss (Fin N)) := by
  simp only [productGauss]
  rw [integral_pi_gauss, stein_vol w ha₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_pi_gauss]
  ring

/-- **Wick's recursion for the standard product Gaussian.** -/
lemma wick_pi {M : ℕ} (w : Fin M → Fin N → ℝ) (s : Finset (Fin M)) :
    ∫ y, ∏ j ∈ s, w j ⬝ᵥ y ∂(productGauss (Fin N)) =
      wickSum (fun a b => w a ⬝ᵥ w b) s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [wickSum_empty]; simp
    · rw [wickSum_rec _ hs, stein_pi w (Finset.min'_mem s hs)]
      apply Finset.sum_congr rfl
      intro b _
      have hsub : (s.erase (s.min' hs)).erase b ⊂ s :=
        (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset (Finset.min'_mem s hs))
      rw [ih _ hsub]

end stein

/-! ## 8. The general-covariance Gaussian and Isserlis' theorem -/
section cov

variable {N : ℕ}

/-- The law of `A · y` for independent standard Gaussians `y`: the centred Gaussian on `Fin N → ℝ`
of covariance `A * Aᵀ`. -/
noncomputable def gaussLaw (A : Matrix (Fin N) (Fin N) ℝ) : Measure (Fin N → ℝ) :=
  (productGauss (Fin N)).map (fun y => A *ᵥ y)

lemma pairingSet_univ_even (m : ℕ) :
    pairingSet (Finset.univ : Finset (Fin (2 * m))) = pairings (2 * m) := by
  ext σ
  simp only [pairingSet, pairings, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.eq_univ_iff_forall, Equiv.Perm.mem_support]
  constructor
  · rintro ⟨h1, h2⟩; exact fun k => ⟨invol_apply h1 k, h2 k⟩
  · intro h; exact ⟨Equiv.ext fun i => by simpa using (h i).1, fun k => (h k).2⟩

lemma pairingSet_univ_odd (m : ℕ) :
    pairingSet (Finset.univ : Finset (Fin (2 * m + 1))) = ∅ := by
  ext σ
  simp only [pairingSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and]
  intro h1 h2
  have := Equiv.Perm.two_dvd_card_support (σ := σ) (by rw [pow_two]; exact h1)
  rw [h2, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **Wick's recursion for the covariance-`A * Aᵀ` Gaussian.** -/
theorem integral_prod_coord_gaussLaw {M : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (μs : Fin M → Fin N) :
    ∫ z, ∏ k, z (μs k) ∂(gaussLaw A) = wickSum (fun a b => (A * Aᵀ) (μs a) (μs b))
      Finset.univ := by
  have hmeas : Measurable (fun y : Fin N → ℝ => A *ᵥ y) := by fun_prop
  have hfm : AEStronglyMeasurable (fun z : Fin N → ℝ => ∏ k, z (μs k))
      (Measure.map (fun y : Fin N → ℝ => A *ᵥ y) (productGauss (Fin N))) :=
    (Finset.measurable_prod _ fun k _ => measurable_pi_apply (μs k)).aestronglyMeasurable
  rw [gaussLaw, integral_map hmeas.aemeasurable hfm]
  have h1 : ∫ y, ∏ k, (A *ᵥ y) (μs k) ∂(productGauss (Fin N)) =
      wickSum (fun a b => (A (μs a)) ⬝ᵥ (A (μs b))) Finset.univ := by
    have := wick_pi (fun j => A (μs j)) Finset.univ
    simpa [Matrix.mulVec] using this
  have hw : (fun a b => (A (μs a)) ⬝ᵥ (A (μs b))) = (fun a b => (A * Aᵀ) (μs a) (μs b)) := by
    funext a b
    rw [Matrix.mul_apply, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.transpose_apply]
  rw [h1, hw]

/-- **Isserlis' theorem (general covariance), pairing form.**  For any `A`, the centred Gaussian
`gaussLaw A` of covariance `A * Aᵀ` has moments given by the sum over pairings, and all odd
moments vanish. -/
theorem isserlis_gaussLaw (A : Matrix (Fin N) (Fin N) ℝ) :
    (∀ (m : ℕ) (μs : Fin (2 * m) → Fin N),
      ∫ z, ∏ k, z (μs k) ∂(gaussLaw A) =
        ∑ p ∈ pairings (2 * m),
          ∏ k ∈ Finset.univ.filter (fun k => k < p k), (A * Aᵀ) (μs k) (μs (p k))) ∧
    (∀ (m : ℕ) (μs : Fin (2 * m + 1) → Fin N),
      ∫ z, ∏ k, z (μs k) ∂(gaussLaw A) = 0) := by
  constructor
  · intro m μs
    rw [integral_prod_coord_gaussLaw, wickSum, pairingSet_univ_even]
  · intro m μs
    rw [integral_prod_coord_gaussLaw, wickSum, pairingSet_univ_odd, Finset.sum_empty]

/-- The centred Gaussian of covariance matrix `K`, as the law of `√K · y` for independent
standard Gaussians `y`.  (This is Mathlib's `multivariateGaussian 0 K`, introduced in a later
Mathlib than the one this project pins.) -/
noncomputable def multivariateGaussian (K : Matrix (Fin N) (Fin N) ℝ) : Measure (Fin N → ℝ) :=
  gaussLaw (CFC.sqrt K)

/-- The covariant matrix of `√K` is `K` itself. -/
lemma sqrt_mul_transpose_sqrt {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosSemidef) :
    CFC.sqrt K * (CFC.sqrt K)ᵀ = K := by
  set A : Matrix (Fin N) (Fin N) ℝ := CFC.sqrt K
  have hAA : A * A = K := CFC.sqrt_mul_sqrt_self K hK.nonneg
  have hsym : Aᵀ = A := by
    have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg K)
    have hherm : A.IsHermitian := hA.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hherm
    exact hherm
  rw [hsym, hAA]

/-- **Isserlis' theorem in the shape of `isserlis_productGauss`, for a general covariance.**

The generalisation is of the *covariance*, not of the index set: `isserlis_productGauss` is the
case `K = 1` of this statement, where the pairing weight `K (μs a) (μs b)` collapses to `1` when
the two factors carry the same index and to `0` otherwise, and the sum over pairings then
groups into one double factorial per coordinate.  Here `μs : Fin M → Fin d` is arbitrary — the
factors may repeat coordinates in any multiplicities, and no even/odd split is taken out (the
pairing set is empty for odd `M`, so the odd moments are covered by `wickSum` being `0`).

Note this composes the covariance from a square factor `√K`; the pairing combinatorics
(`pairingSet`, `wickSum`, `wick_pi`) is this project's, not physlib's field-operator
`WickContraction` — see the note below. -/
theorem integral_prod_coord_multivariateGaussian {d M : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.PosSemidef) (μs : Fin M → Fin d) :
    ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian K) =
      wickSum (fun a b => K (μs a) (μs b)) Finset.univ := by
  rw [multivariateGaussian, integral_prod_coord_gaussLaw]
  simp only [sqrt_mul_transpose_sqrt hK]

/-- **Isserlis' theorem for a Gaussian vector of covariance `K`** (prove2.me
`LesHouchesWidth.wick_theorem`, ported): the even moments are the sum over pairings with weights
`K`, the odd moments vanish. -/
theorem isserlis_multivariateGaussian {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosSemidef) :
    (∀ (m : ℕ) (μs : Fin (2 * m) → Fin d),
      ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian K) =
        ∑ p ∈ pairings (2 * m),
          ∏ k ∈ Finset.univ.filter (fun k => k < p k), K (μs k) (μs (p k))) ∧
    (∀ (m : ℕ) (μs : Fin (2 * m + 1) → Fin d),
      ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian K) = 0) := by
  have h := isserlis_gaussLaw (CFC.sqrt K)
  refine ⟨fun m μs => ?_, fun m μs => ?_⟩
  · simp only [multivariateGaussian]
    rw [h.1 m μs, sqrt_mul_transpose_sqrt hK]
  · simp only [multivariateGaussian]
    rw [h.2 m μs]

/-- The standard product Gaussian is the Gaussian of covariance `1`.  `√1 = 1` and `1 *ᵥ y = y`,
so the pushforward by the covariance factor is the identity. -/
theorem productGauss_eq_multivariateGaussian_one (N : ℕ) :
    productGauss (Fin N) = multivariateGaussian (1 : Matrix (Fin N) (Fin N) ℝ) := by
  rw [multivariateGaussian, gaussLaw, CFC.sqrt_one]
  simp [Matrix.one_mulVec]

/-- **The `K = 1` bridge: `wickSum` is the product of double factorials behind
`isserlis_productGauss`.**

With the identity covariance the pairing weight `if f a = f b then 1 else 0` vanishes exactly on
the pairs that join different fibres of `f`, so a pairing contributes `1` only if it pairs
faithfully inside the fibres; the weighted sum over pairings is therefore the number of such
pairings, which is `∏ j, (n_j - 1)‼` for the multiplicities `n_j` of `f`, and `0` when some
`n_j` is odd.  This identifies the two forms of Isserlis' theorem: the pairing sum
`integral_prod_coord_multivariateGaussian` and the multiplicity product
`isserlis_productGauss`.

The proof is not combinatorial: both sides are moments of the *same* measure (`productGauss`
*is* the covariance-`1` Gaussian), so the two moment computations agree. -/
theorem wickSum_identity_eq_prod_doubleFactorial {N m : ℕ} (f : Fin m → Fin N) :
    wickSum (fun a b => if f a = f b then (1 : ℝ) else 0) Finset.univ =
      ∏ j, if Even (Fintype.card {k : Fin m // f k = j}) then
        ((Fintype.card {k : Fin m // f k = j} - 1)‼ : ℝ) else 0 := by
  have h := integral_prod_coord_multivariateGaussian (1 : Matrix (Fin N) (Fin N) ℝ)
    Matrix.PosSemidef.one f
  simp only [Matrix.one_apply] at h
  rw [← h, ← productGauss_eq_multivariateGaussian_one N]
  exact isserlis_productGauss f

end cov
end

end BookProof.OSReconstruction
