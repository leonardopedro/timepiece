import Mathlib
import BookProof.ChapterHyperbolicQuadraticEsa
import BookProof.ChapterKatoRellichRelative
import BookProof.ChapterYangMillsHermite
import BookProof.ChapterHermiteRelativeBound.Part1

/-!
# Relatively bounded (unbounded) perturbations of the diagonal quadratic Hamiltonian

`BookProof.ChapterHyperbolicQuadraticEsa` proves that
`H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is essentially self-adjoint on the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)` for *every* real weight vector `c`, and widens the
potential class by a **bounded** real multiplier (Kato–Rellich).  This module widens it by
an **unbounded** perturbation, in the elliptic case `cᵢ ≥ c₀ > 0`:

* `posL`, `momL`, `oscL` — the position `xᵢ`, the momentum `πᵢ = −i∂ᵢ` and the
  one-coordinate oscillator `πᵢ² + xᵢ²/4`, as operators from the core into `L²`;
* `posL_symmetric`, `momL_symmetric` — both are symmetric on the core (Gaussian
  integration by parts, through `BookProof.YangMillsHermite.PolySym`);
* `inner_oscL_eq` — the form identity `⟪u, (πᵢ² + xᵢ²/4)u⟫ = ‖πᵢu‖² + ‖xᵢu‖²/4`;
* `re_inner_oscL_le_quadOp` — for weights `cᵢ ≥ c₀ > 0` the oscillator form of a single
  coordinate is dominated by the form of `H_c`: `c₀⟪u, oscᵢ u⟫ ≤ ⟪u, H_c u⟫` (the symbols
  satisfy `c₀(αᵢ + ½) ≤ ∑ⱼ cⱼ(αⱼ + ½)`);
* `norm_posL_le`, `norm_momL_le` — consequently `xᵢ` and `πᵢ` are `H_c`-bounded with
  *arbitrarily small* relative bound: `‖xᵢu‖ ≤ ε‖H_c u‖ + (2/(c₀ε))‖u‖`, and the same for
  `πᵢ`;
* HEADLINE `quadOp_add_firstOrder_essentiallySelfAdjoint` — therefore `H_c + B` is
  essentially self-adjoint on the same core for every **first-order** perturbation
  `B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` with real coefficients.  The perturbation is genuinely
  unbounded, so this is outside the reach of the bounded Kato–Rellich statement;
* `hermiteMvBasis_repr_quadOp` — the product Hermite basis *is* a diagonalizing unitary
  for `H_c`: in those coordinates the operator is multiplication by the real symbol
  `∑ᵢ cᵢ(αᵢ + ½)`;
* `harmonicOsc_add_linearPotential_essentiallySelfAdjoint` and
  `foOp_linear_apply_eq_mul` — the physical corollary: the Stark-shifted oscillator
  `−Δ + ‖x‖²/4 + ⟨b, x⟩` (a harmonic oscillator in a constant external field) is
  essentially self-adjoint on the Hermite core, the perturbation being multiplication by
  the unbounded real function `x ↦ ⟨b, x⟩`.

Two general instruments are proved on the way and are reusable: `apply_sum_of_diagonal`
and `re_inner_diagonal_le` — a diagonal operator with a real symbol acts on a finite
combination of the diagonalizing vectors coefficientwise, and the quadratic forms of two
diagonal operators are ordered by their symbols.

## Honest boundary

The strict positivity `cᵢ ≥ c₀ > 0` is used, and is not removable by this argument: in
the hyperbolic (mixed sign) case the symbol `∑ⱼ cⱼ(αⱼ + ½)` vanishes on an infinite set of
multi-indices, so `H_c` does not dominate the number operator and no relative bound of the
above kind can hold.  The general Faris–Lavine potential (bounded above by a quadratic)
therefore stays open, as recorded in `CONSOLIDATED_PLAN.md`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteRelative

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}
/-! ### The relative bounds -/

theorem norm_posL_sq_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ^ 2 ≤ (4 / c0) * (‖(u : L2d d)‖ * ‖quadOp c u‖) := by
  have h1 : ‖posL i u‖ ^ 2 / 4 ≤ (inner ℂ (u : L2d d) (oscL i u) : ℂ).re := by
    rw [re_inner_oscL_eq]
    nlinarith [sq_nonneg ‖momL i u‖]
  have h2 := re_inner_oscL_le_quadOp c hc0 hc i u
  have h3 : (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ :=
    re_inner_le_norm (𝕜 := ℂ) (u : L2d d) (quadOp c u)
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, h2, h3]

theorem norm_momL_sq_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖momL i u‖ ^ 2 ≤ (4 / c0) * (‖(u : L2d d)‖ * ‖quadOp c u‖) := by
  have h1 : ‖momL i u‖ ^ 2 ≤ (inner ℂ (u : L2d d) (oscL i u) : ℂ).re := by
    rw [re_inner_oscL_eq]
    nlinarith [sq_nonneg ‖posL i u‖]
  have h2 := re_inner_oscL_le_quadOp c hc0 hc i u
  have h3 : (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ :=
    re_inner_le_norm (𝕜 := ℂ) (u : L2d d) (quadOp c u)
  have h4 : 0 ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, h2, h3, h4]

/-- An elementary square-root step: `t² ≤ (4/c₀)AB` gives `t ≤ εA + (2/(c₀ε))B`. -/
theorem le_relBound_of_sq_le {t A B c0 e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc0 : 0 < c0) (he : 0 < e) (h : t ^ 2 ≤ (4 / c0) * (B * A)) :
    t ≤ e * A + (2 / (c0 * e)) * B := by
  have hrhs : 0 ≤ e * A + (2 / (c0 * e)) * B := by positivity
  have hsq : t ^ 2 ≤ (e * A + (2 / (c0 * e)) * B) ^ 2 := by
    have hcross : (4 / c0) * (B * A) ≤ 2 * (e * A) * ((2 / (c0 * e)) * B) := by
      have : 2 * (e * A) * ((2 / (c0 * e)) * B) = (4 / c0) * (B * A) := by
        field_simp
        ring
      rw [this]
    nlinarith [sq_nonneg (e * A), sq_nonneg ((2 / (c0 * e)) * B), h, hcross]
  nlinarith [hsq, hrhs]

theorem norm_posL_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ :=
  le_relBound_of_sq_le (norm_nonneg _) (norm_nonneg _) hc0 he
    (norm_posL_sq_le c hc0 hc i u)

theorem norm_momL_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖momL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ :=
  le_relBound_of_sq_le (norm_nonneg _) (norm_nonneg _) hc0 he
    (norm_momL_sq_le c hc0 hc i u)

/-! ## The first-order perturbation -/

/-- The first-order symbol `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)`, on polynomial coordinates. -/
def foPoly (b b' : Fin d → ℝ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, (((b i : ℝ) : ℂ) • mulXPoly i + ((b' i : ℝ) : ℂ) • momPoly i)

/-- **The first-order perturbation** `B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` on the Hermite core. -/
def foOp (b b' : Fin d → ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (foPoly b b')

set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive
theorem foOp_apply (b b' : Fin d → ℝ) (u : polyGaussCore (d := d)) :
    foOp b b' u = ∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u) := by
  simp only [foOp, foPoly, LinearMap.comp_apply, Submodule.subtype_apply, coreOp_sum,
    coreOp_add, coreOp_smul, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul]
  rfl

theorem gaussInt_zero : gaussInt (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  have h := gaussInt_smul (0 : ℂ) (0 : MvPolynomial (Fin d) ℂ)
  simpa using h

theorem polySym_zero : BookProof.YangMillsHermite.PolySym
    (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by
  intro p q
  simp [BookProof.YangMillsHermite.starP, gaussInt_zero]

theorem polySym_sum {ι : Type*} (s : Finset ι)
    (T : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, BookProof.YangMillsHermite.PolySym (T i)) :
    BookProof.YangMillsHermite.PolySym (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using polySym_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem polySym_foPoly (b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (foPoly b b') :=
  polySym_sum _ _ fun i _ =>
    (BookProof.YangMillsHermite.PolySym.real_smul (polySym_mulXPoly i)).add
      (BookProof.YangMillsHermite.PolySym.real_smul (polySym_momPoly i))

set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive
theorem foOp_symmetric (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (foOp b b') :=
  symmetricOn_of_polySym (polySym_foPoly b b')

/-- The relative bound of the first-order perturbation with respect to `H_c`. -/
theorem norm_foOp_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (b b' : Fin d → ℝ) {e : ℝ} (he : 0 < e) (u : polyGaussCore (d := d)) :
    ‖foOp b b' u‖
      ≤ (∑ i, (|b i| + |b' i|)) * (e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖) := by
  classical
  set R : ℝ := e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ with hR
  have hR0 : 0 ≤ R := by
    have : 0 ≤ 2 / (c0 * e) := by positivity
    have h1 : 0 ≤ e * ‖quadOp c u‖ := by positivity
    have h2 : 0 ≤ (2 / (c0 * e)) * ‖(u : L2d d)‖ := by positivity
    linarith
  calc ‖foOp b b' u‖
      = ‖∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u)‖ := by
        rw [foOp_apply]
    _ ≤ ∑ i, ‖((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u‖ := norm_sum_le _ _
    _ ≤ ∑ i, (|b i| + |b' i|) * R := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hb : ‖((b i : ℝ) : ℂ) • posL i u‖ = |b i| * ‖posL i u‖ := by
          rw [norm_smul]
          simp
        have hb' : ‖((b' i : ℝ) : ℂ) • momL i u‖ = |b' i| * ‖momL i u‖ := by
          rw [norm_smul]
          simp
        have h1 : ‖posL i u‖ ≤ R := norm_posL_le c hc0 hc he i u
        have h2 : ‖momL i u‖ ≤ R := norm_momL_le c hc0 hc he i u
        calc ‖((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u‖
            ≤ ‖((b i : ℝ) : ℂ) • posL i u‖ + ‖((b' i : ℝ) : ℂ) • momL i u‖ := norm_add_le _ _
          _ = |b i| * ‖posL i u‖ + |b' i| * ‖momL i u‖ := by rw [hb, hb']
          _ ≤ |b i| * R + |b' i| * R := by
              have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (b i))
              have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (b' i))
              linarith
          _ = (|b i| + |b' i|) * R := by ring
    _ = (∑ i, (|b i| + |b' i|)) * R := by rw [Finset.sum_mul]

/-- **The headline.**  For strictly positive weights `cᵢ ≥ c₀ > 0`, the operator
`H_c + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` — a diagonal quadratic Hamiltonian plus an arbitrary
*unbounded* first-order perturbation with real coefficients — is essentially self-adjoint
on the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)`. -/
theorem quadOp_add_firstOrder_essentiallySelfAdjoint (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hc : ∀ i, c0 ≤ c i) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOp c + foOp b b') := by
  classical
  set K : ℝ := ∑ i, (|b i| + |b' i|) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  set e : ℝ := 1 / (2 * (K + 1)) with he
  have he0 : 0 < e := by
    have : 0 < 2 * (K + 1) := by linarith
    positivity
  refine BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded _ _ (quadOp_symmetric c)
    (quadOp_essentiallySelfAdjoint c) (foOp_symmetric b b') (a := K * e)
    (b := K * (2 / (c0 * e))) (by positivity) ?_ (by positivity) ?_
  · rw [he]
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  · intro u
    have h := norm_foOp_le c hc0 hc b b' he0 u
    calc ‖foOp b b' u‖ ≤ K * (e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖) := h
      _ = K * e * ‖quadOp c u‖ + K * (2 / (c0 * e)) * ‖(u : L2d d)‖ := by ring

/-! ## The diagonalizing unitary -/

/-- **The Hermite unitary diagonalizes `H_c`**: the coordinates of `H_c u` in the product
Hermite basis are those of `u` multiplied by the real symbol `∑ᵢ cᵢ(αᵢ + ½)`.  This is the
spectral theorem in multiplication form for this (unbounded) operator: the Hilbert basis
`hermiteMvBasis` *is* a diagonalizing unitary `L²(ℝᵈ) ≃ ℓ²`. -/
theorem hermiteMvBasis_repr_quadOp (c : Fin d → ℝ) (u : polyGaussCore (d := d))
    (a : Fin d →₀ ℕ) :
    hermiteMvBasis.repr (quadOp c u) a
      = ((quadSymbol c a : ℝ) : ℂ) * hermiteMvBasis.repr (u : L2d d) a := by
  have hmem : hermiteMvLp a ∈ polyGaussCore (d := d) := hermiteMvLp_mem_core a
  have hsym := quadOp_symmetric c ⟨hermiteMvLp a, hmem⟩ u
  rw [quadOp_hermiteMvLp c a hmem, inner_smul_left, Complex.conj_ofReal] at hsym
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hermiteMvBasis_apply]
  exact hsym.symm

/-! ## The Stark-shifted oscillator -/

/-- The first-order perturbation with `b' = 0` is multiplication by the (unbounded) linear
function `x ↦ ⟨b, x⟩`. -/
theorem foOp_linear_apply_eq_mul (b : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (foPoly b 0 p) x = ((∑ i, b i * x i : ℝ) : ℂ) * pgFun p x := by
  classical
  have hpoly : foPoly b 0 p = ∑ i, ((b i : ℝ) : ℂ) • (X i * p) := by
    simp [foPoly, mulXPoly]
  rw [hpoly]
  have : pgFun (∑ i, ((b i : ℝ) : ℂ) • (X i * p)) x
      = ∑ i, ((b i : ℝ) : ℂ) * pgFun (X i * p) x := by
    classical
    induction (Finset.univ : Finset (Fin d)) using Finset.induction with
    | empty => simp [pgFun]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          BookProof.HyperbolicQuadratic.pgFun_add, ih,
          BookProof.HyperbolicQuadratic.pgFun_smul]
  rw [this]
  have hx : ∀ i : Fin d, pgFun ((X i : MvPolynomial (Fin d) ℂ) * p) x
      = ((x i : ℝ) : ℂ) * pgFun p x := fun i => by
    simpa using posOp_apply_eq_mul i p x
  simp_rw [hx]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Stark-shifted harmonic oscillator** `−Δ + ‖x‖²/4 + ⟨b, x⟩` is essentially
self-adjoint on the Hermite core of `L²(ℝᵈ)`.  The perturbation is the unbounded real
potential `x ↦ ⟨b, x⟩`. -/
theorem harmonicOsc_add_linearPotential_essentiallySelfAdjoint (b : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOp (fun _ => (1 : ℝ)) + foOp b 0) :=
  quadOp_add_firstOrder_essentiallySelfAdjoint _ (c0 := 1) one_pos (fun _ => le_rfl) b 0

end

end BookProof.HermiteRelative
