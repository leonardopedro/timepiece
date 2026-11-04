import Mathlib

/-!
# Degree-two reflection positivity in Källén–Lehmann form

Plan: `cftproof.md`, Phase 3.3 — the free-field instance of "expand the half-space observable,
apply Isserlis, and match against the transfer form".

**Degree one** is `OSReconstruction.MomentumBasis.freeOSForm_eq_momentum`: for a smeared *linear*
field the Isserlis sum is the weighted sum of modulus squares `Σ_a w_a ‖Σ_p F p u_a p‖²`.  This
file is **degree two**: the lift does work one degree further than the linear statement, and it is
the last degree for which the re-match is proved here — from degree three the Isserlis sum is not
positive in general (see Honest boundary), and degrees `≥ 4` are not addressed at all.

## Setting

`S` indexes the half-space (positive Euclidean time) and `K i j = ω(φ(θ i) φ(j))` is the
reflected two-point function, i.e. the covariance across the reflection plane.  A quadratic
half-space observable is `F = Σ_{i j} a i j φ_i φ_j` with `a` symmetric (the coefficients of the
monomials are folded into `a`); its reflection is `θF = Σ_{k l} a k l φ_{θk} φ_{θl}`.  By
Isserlis the OS form is the sum over the two pairings,

`ω(θF · F) = Σ_{i j k l} a i j a k l (K i k K j l + K i l K j k)`  (`osQuadForm`).

## What is proved

* **`pairing_swap`** — the two Wick pairings of a symmetric quadratic observable sum to the same
  thing; the bijection `k ↔ l` inside the sum maps one onto the other.
* **`osQuadForm_eq_two_mul_kern`** — with that, the pairings collapse:
  `osQuadForm a K = 2 Σ_{i j} a i j (K A K)_{i j}` (`kern`) for symmetric `K`.
* **`osQuadForm_eq_two_sum_sq`** — for a covariance in transfer (Källén–Lehmann) form
  `K i j = Σ_x w x * u x i * u x j` with real modes `u` and real weights `w`,
  `osQuadForm a K = 2 Σ_{x y} w x w y (Σ_{i j} a i j u x i u y j)²`.
  The weights `w x w y` multiply the **square of the bilinear pairing of the modes** — the
  degree-two analogue of `transferForm_eq`'s `w a * ‖Σ_p F p u_a p‖²`.  It is *not* a sum of
  `|Σ_p F p u_a p|²` terms: the mode index appears twice, once in each factor.
* **`osQuadForm_nonneg`** — `0 ≤ osQuadForm a K` for `w ≥ 0`: the OS form of every quadratic
  half-space observable is positive for a Gaussian whose reflected covariance is a nonnegative
  transfer kernel.  This is the degree-two half of Phase 3.3's free-field statement.

## Honest boundary

* `osQuadForm_eq_two_sum_sq` holds for any real weights; it is the nonnegativity of `w x w y`
  that carries the positivity, so `osQuadForm_nonneg` is exactly the `w ≥ 0` case.
* **The next degree does not follow.**  Nothing here says anything about cubic or quartic
  observables.  At degree `2m` the same substitution produces products of `m` pairings with no
  collapse into one square.  Degree three fails outright, and `cftproof.md` item 2 records the
  Gaussian counterexample: on an odd subspace, where `θφ = −φ`, the cubic monomial `F = φ(p)³`
  has `θF = −F`, so `ω(θF·F) = −ω(F²) < 0`.  Even degrees `≥ 4` are open here (their Wick sums are
  permanents of the covariance, which this file does not analyse).  From degree three on it is the
  Markov property (a pointwise nonnegative transfer kernel), not Wick's theorem, that makes the
  free measure reflection positive.
* `a` is assumed *symmetric* (a quadratic form) and `K` *symmetric*; for the lattice free field
  the latter is `Re G(θp, q) = Re G(θq, p)`, a consequence of `conj_char`.  The
  complex/Hermitian case is not stated here, and no Gaussian-moment input is wired in: the
  Isserlis identity is `GaussianMoments.isserlis_multivariateGaussian`, and this file starts from
  its output form.
-/

namespace BookProof.ReflectionPositivity

open scoped BigOperators

variable {S ι : Type*} [Fintype S] [Fintype ι]

/-- The **Isserlis sum of a quadratic half-space observable**.  With `F = Σ_{i j} a i j φ_i φ_j`
and reflected covariance `K i k = ω(φ(θi) φ_k)`, this is `ω(θF · F)`: the sum over the two Wick
pairings of the four fields `φ(θi), φ(θj), φ_k, φ_l`. -/
def osQuadForm (a K : S → S → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (K i k * K j l + K i l * K j k)

/-- `(K A K)_{i j}`, the twice-multiplied kernel the two pairings collapse onto. -/
def kern (K a : S → S → ℝ) (i j : S) : ℝ := ∑ k, ∑ l, K i k * a k l * K l j

/-- Pulling a constant out of a double sum. -/
theorem pull_const (f : S → S → ℝ) (C : ℝ) :
    (∑ i, ∑ j, f i j * C) = (∑ i, ∑ j, f i j) * C := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul ..).symm

/-- Pulling a constant into a double sum. -/
theorem pull_const_left (f : S → S → ℝ) (c : ℝ) :
    (∑ i, ∑ j, c * f i j) = c * ∑ i, ∑ j, f i j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm

/-- Two pairs of nested sums commute: `Σ_i Σ_j Σ_x Σ_y = Σ_x Σ_y Σ_i Σ_j`. -/
theorem sum_comm_four (f : S → S → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ x, ∑ y, f i j x y) = ∑ x, ∑ y, ∑ i, ∑ j, f i j x y := by
  calc ∑ i, ∑ j, ∑ x, ∑ y, f i j x y
      = ∑ i, ∑ x, ∑ j, ∑ y, f i j x y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ j, ∑ y, f i j x y := by
        exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ j, f i j x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, ∑ j, f i j x y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm

/-- **The two Wick pairings of a symmetric quadratic observable agree.**  Swapping the index pair
`k ↔ l` inside the sum maps the pairing `K i l K j k` onto `K i k K j l`; this uses only that `a`
comes from a quadratic form, and not any symmetry of `K`. -/
theorem pairing_swap (a K : S → S → ℝ) (ha : ∀ i j, a i j = a j i) :
    (∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (K i l * K j k))
      = ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (K i k * K j l) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  rw [show (∑ l, ∑ k, a i j * a k l * (K i l * K j k))
        = (∑ k, ∑ l, a i j * a l k * (K i k * K j l)) from rfl]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [ha l k]

/-- **The two Wick pairings collapse.**  For symmetric `a` and symmetric reflected covariance the
Isserlis sum of a quadratic observable is twice a single pairing,
`2 Σ_{i j} a i j (K A K)_{i j}`: `pairing_swap` merges the pairings, and `K` symmetric puts the
second `K` factor of `kern` in place. -/
theorem osQuadForm_eq_two_mul_kern (a K : S → S → ℝ) (ha : ∀ i j, a i j = a j i)
    (hK : ∀ i j, K i j = K j i) :
    osQuadForm a K = 2 * ∑ i, ∑ j, a i j * kern K a i j := by
  have hsplit : osQuadForm a K
      = (∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (K i k * K j l)) +
        (∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (K i l * K j k)) := by
    unfold osQuadForm
    simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (K i k * K j l))
      = ∑ i, ∑ j, a i j * kern K a i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [kern, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hK j l]
    ring
  rw [hsplit, pairing_swap a K ha, h1, two_mul]

/-- The mode expansion of `kern`: for the transfer covariance `K i j = Σ_x w x u x i u x j`,
`(K A K)_{i j} = Σ_{x y} w x w y u x i u y j (Σ_{k l} a k l u x k u y l)`. -/
theorem kern_transfer (a : S → S → ℝ) (u : ι → S → ℝ) (w : ι → ℝ) (i j : S) :
    kern (fun i j => ∑ x, w x * u x i * u x j) a i j
      = ∑ x, ∑ y, w x * w y * u x i * u y j * (∑ k, ∑ l, a k l * u x k * u y l) := by
  have hexp : kern (fun i j => ∑ x, w x * u x i * u x j) a i j
      = ∑ k, ∑ l, ∑ x, ∑ y,
          ((w x * u x i * u x k) * a k l) * (w y * u y l * u y j) := by
    simp only [kern]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul_sum]
  rw [hexp, sum_comm_four]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Degree-two reflection positivity in Källén–Lehmann form.**  If the reflected covariance is a
transfer kernel `K i j = Σ_x w x u x i u x j` with real modes, then the Isserlis sum of a
quadratic half-space observable is `2 Σ_{x y} w x w y (Σ_{i j} a i j u x i u y j)²` — the
degree-two match of `transferForm_eq`. -/
theorem osQuadForm_eq_two_sum_sq (a : S → S → ℝ) (u : ι → S → ℝ) (w : ι → ℝ)
    (ha : ∀ i j, a i j = a j i) :
    osQuadForm a (fun i j => ∑ x, w x * u x i * u x j)
      = 2 * ∑ x, ∑ y, w x * w y * (∑ i, ∑ j, a i j * u x i * u y j) ^ 2 := by
  have hK : ∀ i j, (fun i j => ∑ x, w x * u x i * u x j) i j
      = (fun i j => ∑ x, w x * u x i * u x j) j i := by
    intro i j
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [osQuadForm_eq_two_mul_kern a _ ha hK]
  congr 1
  have hstep : ∀ i j : S, a i j * kern (fun i j => ∑ x, w x * u x i * u x j) a i j
      = ∑ x, ∑ y, (w x * w y) * (a i j * (u x i * u y j)) *
          (∑ k, ∑ l, a k l * u x k * u y l) := by
    intro i j
    rw [kern_transfer]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring_nf
  simp only [hstep]
  rw [sum_comm_four]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [pull_const, pull_const_left]
  ring_nf

/-- **Degree-two reflection positivity.**  For a Gaussian whose reflected covariance is a
nonnegative transfer kernel, the OS form of every quadratic half-space observable is
nonnegative. -/
theorem osQuadForm_nonneg (a : S → S → ℝ) (u : ι → S → ℝ) (w : ι → ℝ)
    (ha : ∀ i j, a i j = a j i) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ osQuadForm a (fun i j => ∑ x, w x * u x i * u x j) := by
  rw [osQuadForm_eq_two_sum_sq a u w ha]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => ?_)
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (hw x) (hw y)) (sq_nonneg _)

end BookProof.ReflectionPositivity
