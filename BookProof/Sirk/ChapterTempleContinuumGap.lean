import Mathlib
import BookProof.Sirk.ChapterTempleSeparationBound
import BookProof.ChapterSpectralGapStability
import BookProof.Toolbox.ChapterFockNumberPreservingGap
import BookProof.OSReconstruction.MomentumBasis

/-!
# Chapter TempleContinuumGap — from the analytic separation to a gap of the limit operator

Plan: `softmodes.md`, Phase 5.2.  Phase 5.1 turns the analytic separation constant
`β_∞ − θ_∞ ≥ c₁ Δ_ref` into a Temple certificate at finite order.  Phase 5.2 asks for the
passage *across the limit* `H_n → H_F`: the certified edge must keep a genuine gap.

`BookProof.SpectralGapStability` supplies the abstract transfer — a quantitative gap
`GapAt A λ d` (`d‖x‖ ≤ ‖Ax − λx‖`) survives an **operator-norm** limit
(`gapAt_of_tendsto`).  What was missing is the bridge from the *spectral separation* that
Phases 3–4 produce to such a quantitative gap.  This chapter supplies it:

* **`gapAt_of_separation`** — a spectral separation `spec A ⊆ {l} ∪ [β, ∞)`, `l ≤ β`, gives a
  quantitative gap at the *window centre* `λ = (l+β)/2`:
  `((β − l)/2)‖x‖ ≤ ‖(A − λ)x‖`.  The proof is Pythagoras plus the Temple factor
  (`factor_nonneg_of_separation`, which is the continuous functional calculus `(t−l)(t−β) ≥ 0`
  on the spectrum): with `θ = ⟪x, Ax⟫` and `d = (β−l)/2`,
  `0 ≤ ‖Ax‖² − (l+β)θ + lβ‖x‖² = ‖(A−λ)x‖² − d²‖x‖²`;
* `gapAt_of_form_domination` — the same at the plan's constant: the reference gap `Δ_ref` and the
  domination constant `c₁ > 0` give a gap of `c₁Δ_ref/2` at `l + c₁Δ_ref/2`;
* **`gap_survives_norm_limit`** — the Phase 5.2 conclusion: a separation **uniform in the
  truncation order** (`∀ m, SpectralSeparation (A m) l β`) passes to any operator-norm limit `B`
  with no loss, `GapAt B ((l+β)/2) ((β−l)/2)`;
* **`notMem_spectrum_of_separation_limit`** — hence the window centre is not in the spectrum of
the limit (`notMem_spectrum_of_gapAt`): the limit's spectrum has a hole of radius `(β−l)/2`
  around the centre, i.e. `c₁Δ_ref/2` at the plan's constant.  That is the gap that Phase 5.2
  asserts.

### The strong-resolvent mode (Section 6)

Section 2 presumes an operator-norm limit.  §5.2 of the plan states the passage through the
**strong-resolvent** limit, which is what a truncation family actually delivers, so the same
transfer is carried out in that mode:

* **`certifiedResolvent`** — the left inverse of `A − λ` that the gap guarantees, with
  **`certifiedResolvent_left`** (it inverts on the left) and **`certifiedResolvent_norm`**
  (`‖R ξ‖ ≤ ‖ξ‖/d`) — the operator a strong-resolvent hypothesis speaks about, and the uniform
  bound that makes the transfer lossless;
* **`gap_survives_strongResolvent`** — pointwise convergence of the *certified* resolvents to a
  left inverse of `B − (l+b)/2` gives `B` the gap `(b−l)/2` at the window centre.  The uniform
  bound is not a hypothesis: it is `certifiedResolvent_norm`, read off the separation;
* **`notMem_spectrum_of_strongResolvent_limit`** — the spectral hole, in the strong mode;
* **`continuum_gap_of_form_domination_strongResolvent`** — the same at the plan's constant
  `c₁Δ_ref/2`, i.e. §5.2's conclusion as stated there.

## The Timepiece structure: nested Fock space, number-preserving Hamiltonian, momentum
convolution

Phase 5.2 is not a statement about an abstract bounded operator alone; in Timepiece the
Hamiltonian lives on the **nested Fock space** and is **outer-particle-conserving**.  Two
sections of this chapter put the gap proof on that structure rather than beside it.

### The nested-Fock lift (Section 3)

* `sub_const_nonneg` — a separation `spec T ⊆ {l} ∪ [β, ∞)` bounds the operator from below,
  `T − l ≥ 0` (the continuous functional calculus applied to `t ↦ t − l`);
* `form_gap_of_separation` — hence `l‖x‖² ≤ ⟪x, T x⟫` on *every* vector, which is the form in
  which the second-quantization machinery consumes a one-particle gap;
* **`nestedFock_gap_of_separation`**, **`nestedFock_gap_of_certified_edge`** — the Temple edge
  lifts to the nested Fock space: the number-conserving outer Hamiltonian `dΓ(opCol b A)`
  (`FockNumberPreservingGap`) annihilates the vacuum and has Fock energy at least `l‖u‖²` on
  every vacuum-orthogonal finite-occupation state.  The lift is `dΓ` of a one-particle `A` built
  from `a†_j a_k` only, so the particle number is conserved by construction — no pair creation,
  no inner normal-ordering rewrite — and the certified edge `l` (or `c₁Δ_ref`'s window edge) is
  exactly the Fock gap above the vacuum.

### The coincident-point product (Section 4)

The interacting outer Hamiltonian is a polynomial in the outer fields, i.e. it contains
products of fields *at the same Euclidean point*, where a naive product of distributions is
ambiguous.  Timepiece never takes that product: by the product-to-convolution theorem
(`MomentumBasis.dft_mul_eq_convolution`) a product of fields in position space is a
convolution of their momentum transforms, and *that* is the definition.

* `samePointProduct` — the product of two outer fields at the same point;
* `momentumProduct`, **`dft_samePointProduct`** — its momentum transform is the convolution
  `n⁻¹ Σ_p F̂(p) Ĝ(k−p)`, so the ambiguous object is the convolution;
* `momentumCol` — a symbol `V` gives the one-particle matrix `(k,i) ↦ n⁻¹ V̂(k−i)`;
* **`dft_mul_momentumCol`** — multiplication by `V` acts in momentum space *by that matrix*.
  Since only the momentum transfer `k − i` enters, the coincident-point product is an ordinary
  number-preserving one-particle operator, hence exactly what `dΓ` second-quantizes;
* **`momentumCol_samePointProduct`** — the one-particle coefficient of a product of two outer
  fields at the same point is itself a convolution, `n⁻² Σ_{p+q = k−i} F̂(p) Ĝ(q)`: every term
  carries conserved momentum, and no coincident-point product is ever formed;
* **`samePointProduct_form_eq_momentum`** — the *form* of the same-point product (the object the
  gap chain's form-domination consumes) is the momentum-space convolution form, by Plancherel
  (`sum_conj_dft_mul_dft`) applied to `dft_mul_momentumCol`;
* **`samePointProduct_real_self_form_nonneg`** — for a real field the squared field at a
  coincident point is a nonnegative form: the positivity (`IsPosCol`-shaped, via `isPosCol_opCol`)
  input of the `dΓ` gap chain follows from the convolution form and needs no distribution
  product.

## Where the spectral theorem is (it is not missing)

The unbounded self-adjoint spectral theorem is available in the workspace, in three places:

* **this repository** — `BookProof.ChapterSpectralMultiplication` (bounded normal, multiplication
  form with a cyclic vector), `BookProof.ChapterSpectralDirectSum` (the general bounded case),
  `BookProof.ChapterUnboundedSpectralModel` (the unbounded case by the Cayley route:
  `unbounded_multiplication_model_cyclic`, `_general`, `_separable`, and
  `model_ae_real_multiplier`), and `BookProof.Toolbox.ChapterStoneConverse` (a unitary group's
  generator is densely defined and self-adjoint, `gen`).  For the *bounded* operator that the
  certificate pipeline consumes, the continuous functional calculus (`cfc`) delivers the spectral
  content directly, and that is what this chapter uses;
* `physlib/` —
  `PhyslibAlpha/ProbabilisticTheory/HilbertSpace/Unbounded/SelfAdjointSpectralTheorem.lean`,
  `Unbounded/CayleySpectralData/SpecTheorem.lean` (`unboundedSpectralTheorem`) and
  `Unbounded/Stone.lean`.  `physlib` tracks Lean v4.35, so it is a porting source;
* `math/lean/` (the `math/OAI` snapshot, Lean v4.34.1) — its Kadison–Kastler and Dirichlet-PDE
  chapters are built on the spectral theorem for unbounded operators.

## Honest boundary

Two hypotheses remain, and they are the plan's own: the *uniform* separation of the truncations
(the analytic input of Phases 3–4, at the constant `c₁Δ_ref`) and the convergence of the
truncations to the limit.  `softmodes.md` §5.2 phrases the transfer through the strong-resolvent
limit, which is strictly weaker than norm convergence; Section 2 proves the operator-norm case
and Section 6 the strong-resolvent one, so both modes of the plan's hypothesis are covered —
neither asserts that the truncations converge.  Nothing here identifies the abstract `A` with the
Yang–Mills Hamiltonian, and no clustering input is used.

The nested-Fock lift is honest in the same way: it lifts a *certified one-particle edge* to the
number-conserving Fock Hamiltonian, and it does not manufacture the separation itself, nor does it
claim that the Yang–Mills one-particle operator is the `A` of Sections 1–2.  Section 4 resolves
the ambiguity of the same-point field product on the lattice torus (one cyclic direction; the 4D
case is the tensor product of four, as `MomentumBasis` records); it does not claim a continuum
product of distributions beyond what the convolution defines.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

open BookProof.RitzCertificate
open BookProof.SpectralGapStability
open Filter Topology

namespace BookProof.TempleContinuumGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. From a spectral separation to a quantitative gap -/

omit [CompleteSpace F] in
/-- **The Pythagorean form of the shifted norm**: for any bounded `A`, real `λ` and
`θ = ⟪x, Ax⟫` (real part, for self-adjoint `A`),

`‖(A − λ)x‖² = ‖Ax‖² − 2λθ + λ²‖x‖²`. -/
theorem norm_shift_sq {A : F →L[ℂ] F} (lam : ℝ) (x : F) :
    ‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ ^ 2
      = ‖A x‖ ^ 2 - 2 * lam * rayleigh A x + lam ^ 2 * ‖x‖ ^ 2 := by
  have happ : (A - (lam : ℝ) • (1 : F →L[ℂ] F)) x = A x - (lam : ℂ) • x := by simp
  have hsym : (inner ℂ (A x) x).re = (inner ℂ x (A x)).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) x (A x), Complex.conj_re]
  rw [happ]
  have h := @norm_sub_sq ℂ F _ _ _ (A x) (((lam : ℝ) : ℂ) • x)
  rw [h]
  rw [inner_smul_right, norm_smul]
  simp only [RCLike.mul_re, RCLike.re_to_complex, Complex.ofReal_re, RCLike.im_to_complex,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs, rayleigh]
  rw [hsym, mul_pow, sq_abs]
  ring

/-- **A spectral separation gives a quantitative gap at the window centre.**  If the spectrum of
the bounded self-adjoint `A` lies in `{l} ∪ [β, ∞)` with `l ≤ β`, then no vector is moved by less
than `(β − l)/2` by `A − (l+β)/2`:

`((β − l)/2) ‖x‖ ≤ ‖(A − (l+β)/2) x‖`.

This is the bridge between the plan's `SpectralSeparation` (produced analytically in Phases 3–4)
and the quantitative `GapAt` that `SpectralGapStability` propagates to the limit. -/
theorem gapAt_of_separation {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ}
    (hsep : SpectralSeparation A l b) : GapAt A ((l + b) / 2) ((b - l) / 2) := by
  intro x
  set lam : ℝ := (l + b) / 2 with hlam
  set d : ℝ := (b - l) / 2 with hd
  have hdnn : 0 ≤ d := by rw [hd]; linarith [hsep.1]
  have hl : lam - d = l := by rw [hlam, hd]; ring
  have hb : lam + d = b := by rw [hlam, hd]; ring
  have hsum : l + b = 2 * lam := by rw [← hl, ← hb]; ring
  have hprod : l * b = lam ^ 2 - d ^ 2 := by rw [← hl, ← hb]; ring
  -- the Temple factor is nonnegative
  have hfac := factor_nonneg_of_separation hA hsep
  have hq := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hfac).inner_nonneg_right x
  have hqre : 0 ≤ (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
      (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ).re := (Complex.le_def.mp hq).1
  rw [re_inner_factor hA l b x] at hqre
  rw [hprod, hsum] at hqre
  -- Pythagoras at the window centre
  have hpyth := norm_shift_sq (A := A) lam x
  -- combine
  have hkey : d ^ 2 * ‖x‖ ^ 2 ≤ ‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ ^ 2 := by
    rw [hpyth]
    nlinarith [sq_nonneg ‖x‖]
  have hdnn' : 0 ≤ d * ‖x‖ := mul_nonneg hdnn (norm_nonneg x)
  have hrhs : 0 ≤ ‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ := norm_nonneg _
  have hkey' : (d * ‖x‖) ^ 2 ≤ ‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ ^ 2 := by
    rw [mul_pow]
    exact hkey
  have hmain : d * ‖x‖ ≤ ‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ := by
    calc d * ‖x‖ = Real.sqrt ((d * ‖x‖) ^ 2) := (Real.sqrt_sq hdnn').symm
      _ ≤ Real.sqrt (‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ ^ 2) := Real.sqrt_le_sqrt hkey'
      _ = ‖(A - (lam : ℝ) • (1 : F →L[ℂ] F)) x‖ := Real.sqrt_sq hrhs
  simpa [ContinuousLinearMap.sub_apply] using hmain

/-- **The gap at the plan's constant.**  A reference gap `Δ_ref > 0`, a domination constant
`c₁ > 0` and the analytic separation `β = l + c₁Δ_ref` give a quantitative gap of `c₁Δ_ref/2`
at the window centre `l + c₁Δ_ref/2`. -/
theorem gapAt_of_form_domination {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l c₁ Δ : ℝ}
    (hc : 0 < c₁) (hΔ : 0 < Δ) (hsep : SpectralSeparation A l (l + c₁ * Δ)) :
    GapAt A (l + c₁ * Δ / 2) (c₁ * Δ / 2) := by
  have hgap := gapAt_of_separation hA hsep
  have hcΔ : 0 < c₁ * Δ := mul_pos hc hΔ
  have h1 : (l + (l + c₁ * Δ)) / 2 = l + c₁ * Δ / 2 := by ring
  have h2 : (l + c₁ * Δ - l) / 2 = c₁ * Δ / 2 := by ring
  rwa [h1, h2] at hgap

/-! ## 2. Across the limit -/

/-- **Phase 5.2: a uniform analytic separation survives an operator-norm limit.**  If every
truncation `A m` has its spectrum in `{l} ∪ [β, ∞)` with the *same* `l, β`, and `A m → B` in
operator norm, then `B` has a quantitative gap of `(β − l)/2` at the window centre. -/
theorem gap_survives_norm_limit (A : ℕ → F →L[ℂ] F) {B : F →L[ℂ] F} {l b : ℝ}
    (hsep : ∀ m, SpectralSeparation (A m) l b)
    (hsa : ∀ m, IsSelfAdjoint (A m))
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) :
    GapAt B ((l + b) / 2) ((b - l) / 2) :=
  gapAt_of_tendsto (fun m => gapAt_of_separation (hsa m) (hsep m)) hconv

/-- **The limit's spectrum has a hole.**  Under the hypotheses of `gap_survives_norm_limit` and
`l < β`, the window centre is not in the spectrum of the limit operator. -/
theorem notMem_spectrum_of_separation_limit (A : ℕ → F →L[ℂ] F) {B : F →L[ℂ] F} {l b : ℝ}
    (hsep : ∀ m, SpectralSeparation (A m) l b) (hsa : ∀ m, IsSelfAdjoint (A m))
    (hlt : l < b) (hB : IsSelfAdjoint B)
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) :
    (((l + b) / 2 : ℝ) : ℂ) ∉ spectrum ℂ B := by
  have hgap := gap_survives_norm_limit A hsep hsa hconv
  have hd : 0 < (b - l) / 2 := by linarith
  exact notMem_spectrum_of_gapAt hB hd hgap

/-- **Phase 5.2 at the plan's constant, across the limit**: a uniform separation
`spec (A m) ⊆ {l} ∪ [l + c₁Δ_ref, ∞)` and operator-norm convergence give the limit a gap of
`c₁Δ_ref/2` at `l + c₁Δ_ref/2`, hence a hole of that radius in its spectrum. -/
theorem continuum_gap_of_form_domination (A : ℕ → F →L[ℂ] F) {B : F →L[ℂ] F} {l c₁ Δ : ℝ}
    (hsep : ∀ m, SpectralSeparation (A m) l (l + c₁ * Δ))
    (hsa : ∀ m, IsSelfAdjoint (A m))
    (hc : 0 < c₁) (hΔ : 0 < Δ) (hB : IsSelfAdjoint B)
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) :
    GapAt B (l + c₁ * Δ / 2) (c₁ * Δ / 2)
      ∧ ((l + c₁ * Δ / 2 : ℝ) : ℂ) ∉ spectrum ℂ B := by
  have hcΔ : 0 < c₁ * Δ := mul_pos hc hΔ
  have hgap : GapAt B ((l + (l + c₁ * Δ)) / 2) (((l + c₁ * Δ) - l) / 2) :=
    gap_survives_norm_limit A (fun m => hsep m) hsa hconv
  have h1 : (l + (l + c₁ * Δ)) / 2 = l + c₁ * Δ / 2 := by ring
  have h2 : (l + c₁ * Δ - l) / 2 = c₁ * Δ / 2 := by ring
  rw [h1, h2] at hgap
  refine ⟨hgap, notMem_spectrum_of_gapAt hB (by positivity) hgap⟩

/-! ## 3. The nested-Fock lift: the certified edge is a number-conserving Fock gap

The Hamiltonian of the Timepiece formalism lives on the nested Fock space
`Fock = ℓ²(Conf)` over the one-particle modes, i.e. the direct sum `⊕ₙ Symⁿ` of the particle
sectors, and it is **outer-particle-conserving**: it is `dΓ` of a one-particle operator, built
from `a†_j a_k` only.  `BookProof.FockNumberPreservingGap` proves the lift for such an operator
from a one-particle *form* gap.  What is supplied here is the missing left end of that chain:
the Temple separation of Sections 1–2 produces, at no extra cost, the form gap that the Fock
lift consumes.

Nothing new is assumed: `sub_const_nonneg` is `cfc` of `t ↦ t − l` (the same functional calculus
that gives the Temple factor `factor_nonneg_of_separation`), and the lift itself is
`fock_gap_of_one_particle_form_gap`. -/

section NestedFock

open BookProof.FockNumberPreservingGap
open BookProof.FockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.HermiteGalerkin
open BookProof.FarisLavine

/-- **A spectral separation bounds the operator from below.**  If the spectrum of the bounded
self-adjoint `T` is `{l} ∪ [β, ∞)` with `l ≤ β`, then `T − l ≥ 0`: the shifted operator is
`cfc (t ↦ t − l)`, and that function is nonnegative on the spectrum. -/
theorem sub_const_nonneg {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) {l bb : ℝ}
    (hsep : SpectralSeparation T l bb) :
    0 ≤ (T - (l : ℝ) • (1 : F →L[ℂ] F)) := by
  have hfun : cfc (fun t : ℝ => t - l) T = (T - (l : ℝ) • (1 : F →L[ℂ] F)) := by
    rw [cfc_sub _ _ T, cfc_id' ℝ T, cfc_const l T, Algebra.algebraMap_eq_smul_one]
  rw [← hfun]
  refine cfc_nonneg ?_
  intro t ht
  rcases hsep.2 t ht with h | h
  · simp [h]
  · linarith [hsep.1]

omit [CompleteSpace F] in
/-- The real part of `⟪x, x⟫` is the norm square.  Stated explicitly because the coercion
`ℝ → ℂ` in the inner-product identity is `RCLike.ofReal`, not `Complex.ofReal`. -/
theorem inner_self_re_eq_norm_sq (x : F) : (inner ℂ x x : ℂ).re = ‖x‖ ^ 2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  have h2 : ((RCLike.ofReal ‖x‖ : ℂ) ^ 2).re = ‖x‖ ^ 2 := by
    have h3 : (RCLike.ofReal ‖x‖ : ℂ) = ((‖x‖ : ℝ) : ℂ) := rfl
    rw [h3, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [h, h2]

/-- **The form gap at the certified edge.**  A separation of the spectrum at `l` gives the
one-particle inequality `l‖x‖² ≤ ⟪x, T x⟫` for every vector — the shape in which the
second-quantization machinery consumes a one-particle gap. -/
theorem form_gap_of_separation {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) {l bb : ℝ}
    (hsep : SpectralSeparation T l bb) (x : F) :
    l * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re := by
  have hnn := sub_const_nonneg hT hsep
  have hq : 0 ≤ (inner ℂ x ((T - (l : ℝ) • (1 : F →L[ℂ] F)) x) : ℂ).re := by
    have hpos := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hnn).inner_nonneg_right x
    simpa only [Complex.zero_re] using (Complex.le_def.mp hpos).1
  have hdecomp : (inner ℂ x ((T - (l : ℝ) • (1 : F →L[ℂ] F)) x) : ℂ)
      = inner ℂ x (T x) - ((l : ℝ) : ℂ) * inner ℂ x x := by
    simp [ContinuousLinearMap.sub_apply]
  have hkey : l * (inner ℂ x x : ℂ).re ≤ (inner ℂ x (T x) : ℂ).re := by
    rw [hdecomp, Complex.sub_re, Complex.re_ofReal_mul] at hq
    linarith
  rwa [inner_self_re_eq_norm_sq] at hkey

/-- **The Temple edge is a gap of the outer, number-conserving Hamiltonian.**

Let `b` be an orthonormal basis of the one-particle space, `A` a one-particle operator on the
finite-mode core that agrees there with the bounded self-adjoint `T`, and suppose the spectrum
of `T` is separated at the edge `l ≥ 0` by `β`.  Then the second quantization
`dΓ(opCol b A)` — the outer Hamiltonian, built from `a†_j a_k` and therefore conserving the
particle number — annihilates the vacuum and has Fock energy at least `l‖u‖²` on every
vacuum-orthogonal finite-occupation state. -/
theorem nestedFock_gap_of_separation (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {T : F →L[ℂ] F}
    (hagree : ∀ x : finiteModeDomain b, (finiteModeDomain b).subtype (A x) = T x)
    (hT : IsSelfAdjoint T) {l bb : ℝ} (hsep : SpectralSeparation T l bb) (hl : 0 ≤ l) :
    dGamma (opCol b A) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        l * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re := by
  refine fock_gap_of_one_particle_form_gap b A hl ?_
  intro x
  have hform : quadForm ((finiteModeDomain b).subtype.comp A) x
      = (inner ℂ ((x : finiteModeDomain b) : F) (T ((x : finiteModeDomain b) : F)) : ℂ).re := by
    rw [quadForm, LinearMap.coe_comp, Function.comp_apply, hagree x]
  rw [hform]
  exact form_gap_of_separation hT hsep _

/-- **Phase 5.2 at the plan's constant, on the nested Fock space.**  The analytic separation
`β = l + c₁Δ_ref` (Phases 3–4) makes the outer Hamiltonian `dΓ(opCol b A)` have vacuum energy
`0` and Fock gap `l` above it.  This is the leg `softmodes.md` §5.2 attributes to `dGamma`, with
the separation supplied as a hypothesis exactly as in §5.1. -/
theorem nestedFock_gap_of_certified_edge (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {T : F →L[ℂ] F}
    (hagree : ∀ x : finiteModeDomain b, (finiteModeDomain b).subtype (A x) = T x)
    (hT : IsSelfAdjoint T) {l c₁ Δ : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ) (hl : 0 ≤ l)
    (hsep : SpectralSeparation T l (l + c₁ * Δ)) :
    GapAt T (l + c₁ * Δ / 2) (c₁ * Δ / 2) ∧
      (dGamma (opCol b A) vac = 0 ∧
        ∀ u : FockAlg, u 0 = 0 →
          l * ‖toLp u‖ ^ 2
            ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re) := by
  have hcΔ : 0 < c₁ * Δ := mul_pos hc hΔ
  refine ⟨gapAt_of_form_domination hT hc hΔ hsep, ?_⟩
  exact nestedFock_gap_of_separation b A hagree hT hsep hl

end NestedFock

/-! ## 4. The coincident-point product of outer fields is a momentum convolution

The interacting outer Hamiltonian is a polynomial in the fields, so its coefficients contain
products of fields at the *same* Euclidean point — the object whose naive definition (a product
of distributions) is ambiguous, and the place where a lattice regulator would have to be tuned.
The Timepiece formalism does not take that product.  By the product-to-convolution theorem
(`MomentumBasis.dft_mul_eq_convolution`) a product of fields in position space is a convolution
of their momentum transforms; the convolution *is* the definition, and it is a finite sum over
conserved momentum.

What Section 4 adds to the gap proof is not a new hypothesis but the identification of the
one-particle matrix the lift of Section 3 needs: multiplication by a symbol is, in momentum
space, the matrix `momentumCol`, whose entries depend only on the momentum transfer `k − i`.
That is an ordinary one-particle matrix — number-preserving — so `dΓ` applies to the
coincident-point product of outer fields with no distribution product anywhere. -/

section MomentumProduct

open scoped ComplexConjugate
open BookProof.OSReconstruction

variable {n : ℕ} [NeZero n]

/-- The product of two outer fields at the same Euclidean point. -/
def samePointProduct (F G : ZMod n → ℂ) : ZMod n → ℂ := fun x => F x * G x

/-- A real field, read as a complex one (the field of the formalism is real). -/
def realField (F : ZMod n → ℝ) : ZMod n → ℂ := fun x => (F x : ℂ)

/-- **The same-point product in momentum space**: the convolution of the two momentum
transforms.  This, not the position-space product, is the object the formalism forms. -/
def momentumProduct (F G : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ∑ p : ZMod n, ZMod.dft F p * ZMod.dft G (k - p)

/-- **The ambiguity of the coincident-point product is resolved by convolution**: the momentum
transform of the product of two outer fields at the same point is the convolution of their
transforms. -/
theorem dft_samePointProduct (F G : ZMod n → ℂ) :
    ZMod.dft (samePointProduct F G) = momentumProduct F G :=
  dft_mul_eq_convolution F G

/-- The one-particle matrix of multiplication by a symbol `V`, in the momentum basis: the
coefficient of `a†_k a_i` is the momentum *transfer* `k − i`, transformed.  Only the difference
`k − i` enters, so this is a one-particle matrix and `dΓ` of it is number preserving. -/
def momentumCol (V : ZMod n → ℂ) (k i : ZMod n) : ℂ := (n : ℂ)⁻¹ * ZMod.dft V (k - i)

/-- **Multiplication by a symbol acts by momentum convolution.**  In momentum space the
coincident-point product is the matrix `momentumCol V`, i.e. `a†_k a_i` with the momentum
transfer `k − i` — a number-preserving one-particle operator. -/
theorem dft_mul_momentumCol (V f : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft (fun x => V x * f x) k = ∑ i : ZMod n, momentumCol V k i * ZMod.dft f i := by
  rw [dft_mul_eq_convolution]
  simp only [momentumCol, Finset.mul_sum]
  refine Finset.sum_bij' (fun i _ => k - i) (fun p _ => k - p)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun i _ => by simp) (fun p _ => by simp) (fun i _ => ?_)
  simp only [sub_sub_cancel]
  ring

/-- **The coefficient of a product of two outer fields at the same point is itself a
convolution.**  `momentumCol (F·G) k i = n⁻² Σ_{p+q = k−i} F̂(p) Ĝ(q)`: every term carries
conserved momentum, and no coincident-point product is formed at any stage. -/
theorem momentumCol_samePointProduct (F G : ZMod n → ℂ) (k i : ZMod n) :
    momentumCol (samePointProduct F G) k i
      = ((n : ℂ)⁻¹) ^ 2 * ∑ p : ZMod n, ZMod.dft F p * ZMod.dft G (k - i - p) := by
  rw [momentumCol, dft_samePointProduct, momentumProduct, ← mul_assoc, ← pow_two]

/-- **Plancherel for the unnormalised transform on the torus**:
`∑ k, conj (F̂ k) Ĝ k = n ∑ x, conj (F x) G x`. -/
theorem sum_conj_dft_mul_dft (f g : ZMod n → ℂ) :
    ∑ k : ZMod n, conj (ZMod.dft f k) * ZMod.dft g k
      = (n : ℂ) * ∑ x : ZMod n, conj (f x) * g x := by
  have hconj : ∀ k : ZMod n,
      conj (ZMod.dft f k) = ∑ x : ZMod n, ZMod.stdAddChar (x * k) * conj (f x) := by
    intro k
    rw [ZMod.dft_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_eq_mul]
    rw [map_mul, conj_stdAddChar, neg_neg]
  calc ∑ k : ZMod n, conj (ZMod.dft f k) * ZMod.dft g k
      = ∑ k : ZMod n, (∑ x : ZMod n, ZMod.stdAddChar (x * k) * conj (f x)) *
          (∑ y : ZMod n, ZMod.stdAddChar (-(y * k)) * g y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hconj k, ZMod.dft_apply]
        simp only [smul_eq_mul]
    _ = ∑ k : ZMod n, ∑ x : ZMod n, ∑ y : ZMod n,
          (ZMod.stdAddChar (x * k) * conj (f x)) *
            (ZMod.stdAddChar (-(y * k)) * g y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ x : ZMod n, ∑ y : ZMod n, ∑ k : ZMod n,
          (ZMod.stdAddChar (x * k) * conj (f x)) *
            (ZMod.stdAddChar (-(y * k)) * g y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : ZMod n, ∑ y : ZMod n,
          (conj (f x) * g y) * (if x - y = 0 then (n : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [show (∑ k : ZMod n, (ZMod.stdAddChar (x * k) * conj (f x)) *
              (ZMod.stdAddChar (-(y * k)) * g y))
            = (conj (f x) * g y) *
                ∑ k : ZMod n, ZMod.stdAddChar (x * k) * ZMod.stdAddChar (-(y * k)) from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring,
          show (∑ k : ZMod n, ZMod.stdAddChar (x * k) * ZMod.stdAddChar (-(y * k)))
            = ∑ k : ZMod n, ZMod.stdAddChar (k * (x - y)) from by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← AddChar.map_add_eq_mul]
          congr 1
          ring,
          sum_char (x - y)]
    _ = ∑ x : ZMod n, ((n : ℂ) * (conj (f x) * g x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · rw [if_pos (sub_self x)]
          ring
        · intro y _ hy
          rw [if_neg (sub_ne_zero.mpr (Ne.symm hy))]
          ring
        · intro hx
          exact absurd (Finset.mem_univ x) hx
    _ = (n : ℂ) * ∑ x : ZMod n, conj (f x) * g x := by
        exact (Finset.mul_sum _ _ _).symm

/-- **The form of the coincident-point product is the momentum convolution.**  The object the
form-domination step (`softmodes.md` Phase 4) evaluates is `∑ x, conj (f x) V x f x` with `V` a
product of fields at the same point.  By Plancherel and `dft_mul_momentumCol` that form is the
momentum-space sum against the convolution matrix `momentumCol V` — the convolution, not a
coincident-point product, is what the gap proof consumes. -/
theorem samePointProduct_form_eq_momentum (F G f : ZMod n → ℂ) :
    ∑ k : ZMod n, conj (ZMod.dft f k)
        * ∑ i : ZMod n, momentumCol (samePointProduct F G) k i * ZMod.dft f i
      = (n : ℂ) * ∑ x : ZMod n, conj (f x) * samePointProduct F G x * f x := by
  have hmat : ∀ k : ZMod n,
      (∑ i : ZMod n, momentumCol (samePointProduct F G) k i * ZMod.dft f i)
        = ZMod.dft (fun x => samePointProduct F G x * f x) k :=
    fun k => (dft_mul_momentumCol (samePointProduct F G) f k).symm
  simp only [hmat]
  have h := sum_conj_dft_mul_dft f (fun x => samePointProduct F G x * f x)
  simpa only [mul_assoc] using h

/-- **The momentum-transfer matrix preserves the `ℓ²` mass of the symbol.**  Each entry is
`n⁻¹ V̂ (k − i)`, and `(k, i) ↦ k − i` is `n`-to-one, so the double sum of `‖momentumCol V k i‖²`
is `n⁻¹ ∑_l ‖V̂ l‖²`, which Plancherel turns back into `∑_x ‖V x‖²`.  So the passage from a symbol
to its momentum-transfer matrix loses nothing: the Hilbert–Schmidt mass is carried over unchanged,
which is what lets the `σ` of a position-space symbol be read off in the momentum picture. -/
theorem momentumCol_hs_mass (V : ZMod n → ℂ) :
    ∑ k : ZMod n, ∑ i : ZMod n, ‖momentumCol V k i‖ ^ 2 = ∑ x : ZMod n, ‖V x‖ ^ 2 := by
  have hcol : ∀ k : ZMod n, ∑ i : ZMod n, ‖momentumCol V k i‖ ^ 2
      = ∑ l : ZMod n, ‖(n : ℂ)⁻¹ * ZMod.dft V l‖ ^ 2 := by
    intro k
    refine Finset.sum_bij (fun i _ => k - i) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a _ b _ hab
      have h' : k - a = k - b := hab
      exact neg_inj.mp (add_left_cancel (a := k) (by simpa using h'))
    · intro b _
      exact ⟨k - b, Finset.mem_univ _, by simp⟩
    · intro a _
      simp [momentumCol]
  have hnorm : ∀ l : ZMod n, ‖(n : ℂ)⁻¹ * ZMod.dft V l‖ ^ 2
      = (n : ℝ)⁻¹ ^ 2 * ‖ZMod.dft V l‖ ^ 2 := by
    intro l
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
  have hsq : ∀ z : ℂ, (conj z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring
  have hplan : ∑ l : ZMod n, ‖ZMod.dft V l‖ ^ 2 = (n : ℝ) * ∑ x : ZMod n, ‖V x‖ ^ 2 := by
    have h := congrArg Complex.re (sum_conj_dft_mul_dft V V)
    have hW : ((n : ℂ) * ∑ x : ZMod n, conj (V x) * V x).re
        = (n : ℝ) * ∑ x : ZMod n, ‖V x‖ ^ 2 := by
      rw [Complex.mul_re]
      simp [Complex.re_sum, hsq]
    rw [Complex.re_sum, hW] at h
    simpa [hsq] using h
  have hn : (n : ℝ) ≠ 0 := by
    have := NeZero.ne n
    exact_mod_cast this
  calc ∑ k : ZMod n, ∑ i : ZMod n, ‖momentumCol V k i‖ ^ 2
      = ∑ _k : ZMod n, ∑ l : ZMod n, ‖(n : ℂ)⁻¹ * ZMod.dft V l‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => hcol k
    _ = (n : ℝ) * ∑ l : ZMod n, ‖(n : ℂ)⁻¹ * ZMod.dft V l‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    _ = ∑ x : ZMod n, ‖V x‖ ^ 2 := by
        have hsplit : ∑ l : ZMod n, ‖(n : ℂ)⁻¹ * ZMod.dft V l‖ ^ 2
            = (n : ℝ)⁻¹ ^ 2 * ∑ l : ZMod n, ‖ZMod.dft V l‖ ^ 2 := by
          rw [Finset.sum_congr rfl (fun l _ => hnorm l), ← Finset.mul_sum]
        rw [hsplit, hplan]
        have hnum : (n : ℝ) * ((n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ∑ x : ZMod n, ‖V x‖ ^ 2))
            = ∑ x : ZMod n, ‖V x‖ ^ 2 := by
          calc (n : ℝ) * ((n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ∑ x : ZMod n, ‖V x‖ ^ 2))
              = ((n : ℝ) * (n : ℝ)⁻¹)
                  * ((n : ℝ)⁻¹ * ((n : ℝ) * ∑ x : ZMod n, ‖V x‖ ^ 2)) := by ring
            _ = (n : ℝ)⁻¹ * ((n : ℝ) * ∑ x : ZMod n, ‖V x‖ ^ 2) := by
                rw [mul_inv_cancel₀ hn, one_mul]
            _ = ∑ x : ZMod n, ‖V x‖ ^ 2 := by rw [inv_mul_cancel_left₀ hn]
        rw [hnum]

/-- **The coincident-point product carries the product symbol's mass.**  Composing
`momentumCol_hs_mass` with `V = F·G`: the momentum convolution of two outer fields at the same point
has Hilbert–Schmidt mass exactly `∑_x ‖F x‖²‖G x‖²`, the `ℓ²` mass of the pointwise product — so a
bound on the coincident-point product in position space *is* a bound on the momentum-transfer
matrix in the momentum picture, with no loss. -/
theorem momentumCol_samePointProduct_hs_mass (F G : ZMod n → ℂ) :
    ∑ k : ZMod n, ∑ i : ZMod n, ‖momentumCol (samePointProduct F G) k i‖ ^ 2
      = ∑ x : ZMod n, ‖F x‖ ^ 2 * ‖G x‖ ^ 2 := by
  rw [momentumCol_hs_mass]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [samePointProduct, norm_mul, mul_pow]

/-- **The `σ` transfers to the outer-Fock form.**  For a finite one-particle matrix `T`,
`|∑_{k,i} conj(f k) T k i f i| ≤ ‖T‖_HS ‖f‖²`; in the momentum picture of a coincident-point
product `T = momentumCol (F·G)`, whose mass is `∑_x ‖F x‖²‖G x‖²` by
`momentumCol_samePointProduct_hs_mass`.  So the form of the product field is bounded by
`√(∑_x ‖F x‖²‖G x‖²) · ‖f̂‖²` — the Hilbert–Schmidt constant of the position-space symbol, read on
the momentum-transfer form. -/
theorem samePointProduct_form_hs_bound (F G f : ZMod n → ℂ) :
    ‖∑ k : ZMod n, conj (ZMod.dft f k)
        * ∑ i : ZMod n, momentumCol (samePointProduct F G) k i * ZMod.dft f i‖
      ≤ Real.sqrt (∑ x : ZMod n, ‖F x‖ ^ 2 * ‖G x‖ ^ 2) * ∑ k : ZMod n, ‖ZMod.dft f k‖ ^ 2 := by
  set T : ZMod n → ZMod n → ℂ := momentumCol (samePointProduct F G) with hT
  have hsq : ∑ k : ZMod n, ∑ i : ZMod n, ‖T k i‖ ^ 2
      = ∑ x : ZMod n, ‖F x‖ ^ 2 * ‖G x‖ ^ 2 := by
    rw [hT]
    exact momentumCol_samePointProduct_hs_mass F G
  set σ := Real.sqrt (∑ x : ZMod n, ‖F x‖ ^ 2 * ‖G x‖ ^ 2) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∑ k : ZMod n, ∑ i : ZMod n, ‖T k i‖ ^ 2 := by
    rw [hσ, Real.sq_sqrt (Finset.sum_nonneg fun x _ => by positivity), hsq]
  -- Cauchy–Schwarz on the finite matrix, with the coefficient weight on both sides
  have hrow : ∀ k : ZMod n, ‖∑ i : ZMod n, T k i * ZMod.dft f i‖
      ≤ Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2)
        * Real.sqrt (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2) := by
    intro k
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) (fun i : ZMod n => ‖T k i‖)
      (fun i : ZMod n => ‖ZMod.dft f i‖)
    have hnorm : ‖∑ i : ZMod n, T k i * ZMod.dft f i‖
        ≤ ∑ i : ZMod n, ‖T k i‖ * ‖ZMod.dft f i‖ := by
      refine (norm_sum_le (s := Finset.univ) (f := fun i : ZMod n => T k i * ZMod.dft f i)).trans ?_
      exact Finset.sum_le_sum fun i _ => le_of_eq (norm_mul _ _)
    refine hnorm.trans ?_
    have hsq2 : (∑ i : ZMod n, ‖T k i‖ * ‖ZMod.dft f i‖) ^ 2
        ≤ (∑ i : ZMod n, ‖T k i‖ ^ 2) * (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2) := hCS
    have hna : (0 : ℝ) ≤ ∑ i : ZMod n, ‖T k i‖ * ‖ZMod.dft f i‖ := by positivity
    calc ∑ i : ZMod n, ‖T k i‖ * ‖ZMod.dft f i‖
        = Real.sqrt ((∑ i : ZMod n, ‖T k i‖ * ‖ZMod.dft f i‖) ^ 2) := (Real.sqrt_sq hna).symm
      _ ≤ Real.sqrt ((∑ i : ZMod n, ‖T k i‖ ^ 2)
            * (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2)) := Real.sqrt_le_sqrt hsq2
      _ = Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2)
            * Real.sqrt (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2) := Real.sqrt_mul (by positivity) _
  have hwhole := norm_sum_le (s := Finset.univ) (f := fun k : ZMod n =>
    conj (ZMod.dft f k) * ∑ i : ZMod n, T k i * ZMod.dft f i)
  refine hwhole.trans ?_
  have hterm : ∀ k : ZMod n, ‖conj (ZMod.dft f k) * ∑ i : ZMod n, T k i * ZMod.dft f i‖
      ≤ Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2) * ‖ZMod.dft f k‖
        * Real.sqrt (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2) := by
    intro k
    rw [norm_mul, Complex.norm_conj]
    have := hrow k
    have h0 : (0 : ℝ) ≤ ‖ZMod.dft f k‖ := norm_nonneg _
    calc ‖ZMod.dft f k‖ * ‖∑ i : ZMod n, T k i * ZMod.dft f i‖
        ≤ ‖ZMod.dft f k‖ * (Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2)
            * Real.sqrt (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  set Sf := Real.sqrt (∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2) with hSf
  set M := ∑ k : ZMod n, Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2) * ‖ZMod.dft f k‖ with hM
  have hfac : ∑ k : ZMod n, Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2) * ‖ZMod.dft f k‖ * Sf
      = Sf * M := by
    rw [hM, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hfac]
  -- ∑_k a_k b_k ≤ σ √(∑ b_k²) with ∑ a_k² = σ²
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
    (fun k : ZMod n => Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2))
    (fun k : ZMod n => ‖ZMod.dft f k‖)
  have hsumsq : ∑ k : ZMod n, (Real.sqrt (∑ i : ZMod n, ‖T k i‖ ^ 2)) ^ 2 = σ ^ 2 := by
    rw [hσ2]
    exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (by positivity)
  have hM0 : (0 : ℝ) ≤ M := by
    rw [hM]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hSf2 : Sf ^ 2 = ∑ i : ZMod n, ‖ZMod.dft f i‖ ^ 2 := by
    rw [hSf, Real.sq_sqrt (by positivity)]
  rw [hsumsq] at hCS
  have hMle : M ^ 2 ≤ σ ^ 2 * Sf ^ 2 := by
    rw [hM, hSf2]
    exact hCS
  have hMle' : M ≤ σ * Sf := by
    calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM0).symm
      _ ≤ Real.sqrt (σ ^ 2 * Sf ^ 2) := Real.sqrt_le_sqrt hMle
      _ = σ * Sf := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hσ0, Real.sqrt_sq (Real.sqrt_nonneg _)]
  calc Sf * M ≤ Sf * (σ * Sf) := mul_le_mul_of_nonneg_left hMle' (Real.sqrt_nonneg _)
    _ = σ * Sf ^ 2 := by ring
    _ = σ * ∑ k : ZMod n, ‖ZMod.dft f k‖ ^ 2 := by rw [hSf2]

/-- **The squared field at a coincident point is a nonnegative form.**  For a real field `F`,
`∑ x, conj (f x) (F·F)(x) f x` is a sum of `F(x)²‖f x‖²`, hence nonnegative.  This is the
positivity input of the gap chain (`IsPosCol`-shaped, through `isPosCol_opCol`), and it is read
off the convolution form: the same-point square of a real outer field is an admissible
one-particle form, so no distribution product has to be regularised anywhere. -/
theorem samePointProduct_real_self_form_nonneg (F : ZMod n → ℝ) (f : ZMod n → ℂ) :
    0 ≤ (∑ x : ZMod n, conj (f x) * samePointProduct (realField F) (realField F) x * f x).re := by
  have hterm : ∀ x : ZMod n,
      conj (f x) * samePointProduct (realField F) (realField F) x * f x
        = (((F x) ^ 2 * Complex.normSq (f x) : ℝ) : ℂ) := by
    intro x
    have hmul : ((F x : ℂ)) * ((F x : ℂ)) = (((F x) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    calc conj (f x) * samePointProduct (realField F) (realField F) x * f x
        = (((F x) ^ 2 : ℝ) : ℂ) * (conj (f x) * f x) := by
          rw [samePointProduct, realField, hmul]
          ring
      _ = (((F x) ^ 2 : ℝ) : ℂ) * ((Complex.normSq (f x) : ℝ) : ℂ) := by
          rw [Complex.normSq_eq_conj_mul_self]
      _ = (((F x) ^ 2 * Complex.normSq (f x) : ℝ) : ℂ) := by
          push_cast
          ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Complex.re_sum]
  exact Finset.sum_nonneg fun x _ => by
    rw [Complex.ofReal_re]
    exact mul_nonneg (sq_nonneg (F x)) (Complex.normSq_nonneg (f x))

/-- **A finite chain of coincident-point factors keeps the mass multiplicative.**  Iterating
`samePointProduct`: the `ℓ²` mass of the product of `r` fields at one point is the sum of
`∏ j, ‖F j x‖²`, because `‖∏ j, F j x‖ = ∏ j, ‖F j x‖`. -/
theorem chain_hs_mass {r : ℕ} (F : Fin r → ZMod n → ℂ) :
    ∑ x : ZMod n, ‖∏ j, F j x‖ ^ 2 = ∑ x : ZMod n, ∏ j, ‖F j x‖ ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [norm_prod, Finset.prod_pow]

/-- **The momentum-transfer matrix of a finite chain preserves the product mass.**
`momentumCol_hs_mass` applied to the chain symbol `∏ j, F j x`, with `chain_hs_mass` making the
mass multiplicative: the momentum convolution of `r` coincident-point factors has Hilbert–Schmidt
mass exactly `∑_x ∏ j, ‖F j x‖²`. -/
theorem momentumCol_chain_hs_mass {r : ℕ} (F : Fin r → ZMod n → ℂ) :
    ∑ k : ZMod n, ∑ i : ZMod n, ‖momentumCol (fun x => ∏ j, F j x) k i‖ ^ 2
      = ∑ x : ZMod n, ∏ j, ‖F j x‖ ^ 2 := by
  rw [momentumCol_hs_mass, chain_hs_mass]

/-- **The `σ` of a finite chain of outer fields at one point.**  The binary bound
`samePointProduct_form_hs_bound` extends to any finite chain: the form of `∏ j, F j` is bounded by
`√(∑_x ∏ j ‖F j x‖²) · ‖f̂‖²`, the Hilbert–Schmidt constant of the chain read on the
momentum-transfer form.  No coincident-point product is formed at any stage, so the same reading
applies to every finite order of the product. -/
theorem chain_form_hs_bound {r : ℕ} (F : Fin r → ZMod n → ℂ) (f : ZMod n → ℂ) :
    ‖∑ k : ZMod n, conj (ZMod.dft f k)
        * ∑ i : ZMod n, momentumCol (fun x => ∏ j, F j x) k i * ZMod.dft f i‖
      ≤ Real.sqrt (∑ x : ZMod n, ∏ j, ‖F j x‖ ^ 2) * ∑ k : ZMod n, ‖ZMod.dft f k‖ ^ 2 := by
  have h := samePointProduct_form_hs_bound (fun x => ∏ j, F j x) (fun _ => (1 : ℂ)) f
  have hsym : samePointProduct (fun x => ∏ j, F j x) (fun _ => (1 : ℂ))
      = fun x => ∏ j, F j x := by
    funext x
    simp [samePointProduct]
  have hmass : ∑ x : ZMod n, ‖(fun x => ∏ j, F j x) x‖ ^ 2 * ‖(fun _ => (1 : ℂ)) x‖ ^ 2
      = ∑ x : ZMod n, ∏ j, ‖F j x‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_one, one_pow, mul_one, norm_prod, Finset.prod_pow]
  rw [hsym, hmass] at h
  exact h

end MomentumProduct

/-! ## 5. The same construction on the 4-torus: Plancherel, convolution, momentum conservation

Section 4 runs on a single cyclic direction `ℤ/n`.  The outer fields of a four-dimensional
gauge theory live on the tensor of four of them, `(ℤ/n)⁴`, and the statements of Section 4
hold there with *no new analysis*: the character of the 4-torus is the product of the four
one-dimensional characters, so the orthogonality relation, the product-to-convolution
theorem and Plancherel all factor through the one-dimensional ones, with the volume `n`
replaced by `n⁴` and `n⁻¹` by `n⁻⁴`.

What is checked here in addition is the **momentum-conservation form**: on the 4-torus the
momentum-space product is the sum over pairs `(p, q)` of four-momenta with `p + q = k`, and
`torus4_add_iff` records that this is equivalent to conservation in each of the four
components.  So the coincident-point product of two outer fields is, in four dimensions
exactly as in one, a sum over conserved momentum and never a product of distributions.

* `sum_charT4_mul_conj`, `sum_conj_charT4_mul_charT4` — orthogonality of the characters of
  `(ℤ/n)⁴`, `∑_k χ_k(x) conj χ_k(y) = n⁴ δ_{xy}`;
* `dftT4_mul_eq_convolution`, `dftT4_samePointProductT4` — the transform of a same-point
  product is the convolution of the transforms;
* `sum_conj_dftT4_mul_dftT4` — **Plancherel on the 4-torus**;
* `momentumColT4`, `dftT4_mul_momentumColT4`, `momentumColT4_samePointProductT4` — the
  number-preserving one-particle matrix of multiplication by a symbol, with coefficient
  `n⁻⁸ Σ_{p+q = k−i} F̂(p) Ĝ(q)` for a two-field product;
* `samePointProductT4_form_eq_momentum` — the form of the coincident-point product on the
  4-torus is the momentum-space sum against `momentumColT4`;
* `momentumProductT4_eq_sum_conserved`, `momentumProductT4_eq_sum_four_conserved`,
  `torus4_add_iff` — **momentum conservation**, as a sum over `p + q = k` and, equivalently,
  component by component;
* `realFieldT4`, `samePointProductT4_real_self_form_nonneg` — the squared real field at a
  point of the 4-torus is a nonnegative form, the positivity input of the Phase-4 chain in
  four dimensions.
-/

open scoped ComplexConjugate

open BookProof.OSReconstruction

section MomentumProductTorus4

variable {n : ℕ} [NeZero n]

/-- The 4-torus `(ℤ/n)⁴`: the tensor of the four cyclic directions, the lattice on which the
outer fields of a four-dimensional gauge theory live. -/
abbrev Torus4 := ZMod n × ZMod n × ZMod n × ZMod n

/-- The character of the 4-torus: the tensor product of the four one-dimensional characters. -/
noncomputable def charT4 (k x : Torus4 (n := n)) : ℂ :=
  char k.1 x.1 * char k.2.1 x.2.1 * char k.2.2.1 x.2.2.1 * char k.2.2.2 x.2.2.2

/-- The unnormalised Fourier transform on the 4-torus. -/
noncomputable def dftT4 (Φ : Torus4 (n := n) → ℂ) (k : Torus4 (n := n)) : ℂ :=
  ∑ x : Torus4 (n := n), charT4 k x * Φ x

theorem charT4_add (k l x : Torus4 (n := n)) : charT4 (k + l) x = charT4 k x * charT4 l x := by
  simp only [charT4, Prod.fst_add, Prod.snd_add, char_add]
  ring

theorem charT4_zero (x : Torus4 (n := n)) : charT4 0 x = 1 := by simp [charT4]

theorem charT4_neg (k x : Torus4 (n := n)) : charT4 (-k) x = conj (charT4 k x) := by
  simp only [charT4, Prod.fst_neg, Prod.snd_neg]
  rw [map_mul, map_mul, map_mul, ← conj_char, ← conj_char, ← conj_char, ← conj_char]

theorem charT4_mul_conj (p v : Torus4 (n := n)) : charT4 p v * conj (charT4 p v) = 1 := by
  rw [← charT4_neg, ← charT4_add, add_neg_cancel, charT4_zero]

theorem charT4_sub (k p v : Torus4 (n := n)) :
    charT4 (k - p) v = charT4 k v * conj (charT4 p v) := by
  have h : charT4 k v = charT4 (k - p) v * charT4 p v := by rw [← charT4_add, sub_add_cancel]
  have h2 : charT4 k v * conj (charT4 p v) = charT4 (k - p) v := by
    rw [h, mul_assoc, charT4_mul_conj, mul_one]
  rw [← h2]

theorem char_comm' (k x : ZMod n) : char k x = char x k := by simp [char, mul_comm]

/-- A sum over the 4-torus is a fourfold iterated sum. -/
theorem sum_torus4 (f : ZMod n → ZMod n → ZMod n → ZMod n → ℂ) :
    ∑ k : Torus4 (n := n), f k.1 k.2.1 k.2.2.1 k.2.2.2 = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  simp only [Fintype.sum_prod_type]

theorem sum_four_mul (F1 F2 F3 F4 : ZMod n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F1 a * F2 b * F3 c * F4 d
      = (∑ a, F1 a) * (∑ b, F2 b) * (∑ c, F3 c) * (∑ d, F4 d) := by
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

theorem sum_char_char_conj (u v : ZMod n) :
    ∑ a : ZMod n, char a u * conj (char a v) = if u = v then (n : ℂ) else 0 := by
  have h : ∀ a, char a u * conj (char a v) = char u a * conj (char v a) := by
    intro a; rw [char_comm' a u, char_comm' a v]
  rw [Finset.sum_congr rfl fun a _ => h a]
  exact sum_char_mul_conj u v

/-- **Orthogonality of the 4-torus characters**: they are orthonormal up to the volume `n⁴`,
the four one-dimensional orthogonality relations multiplied out. -/
theorem sum_charT4_mul_conj (x y : Torus4 (n := n)) :
    ∑ k : Torus4 (n := n), charT4 k x * conj (charT4 k y)
      = if x = y then (n : ℂ) ^ 4 else 0 := by
  have hterm : ∀ k : Torus4 (n := n), charT4 k x * conj (charT4 k y)
      = (char k.1 x.1 * conj (char k.1 y.1)) * (char k.2.1 x.2.1 * conj (char k.2.1 y.2.1))
        * (char k.2.2.1 x.2.2.1 * conj (char k.2.2.1 y.2.2.1))
        * (char k.2.2.2 x.2.2.2 * conj (char k.2.2.2 y.2.2.2)) := by
    intro k; simp only [charT4, map_mul]; ring
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  rw [sum_torus4 (fun a b c d =>
    (char a x.1 * conj (char a y.1)) * (char b x.2.1 * conj (char b y.2.1))
      * (char c x.2.2.1 * conj (char c y.2.2.1)) * (char d x.2.2.2 * conj (char d y.2.2.2)))]
  rw [sum_four_mul, sum_char_char_conj, sum_char_char_conj, sum_char_char_conj,
    sum_char_char_conj]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2.1 = y.2.1 <;>
    by_cases h3 : x.2.2.1 = y.2.2.1 <;> by_cases h4 : x.2.2.2 = y.2.2.2 <;>
    simp [h1, h2, h3, h4, Prod.ext_iff]
  all_goals ring

theorem sum_conj_charT4_mul_charT4 (x y : Torus4 (n := n)) :
    ∑ k : Torus4 (n := n), conj (charT4 k x) * charT4 k y
      = if x = y then (n : ℂ) ^ 4 else 0 := by
  have hif : (if y = x then (n : ℂ) ^ 4 else 0) = (if x = y then (n : ℂ) ^ 4 else 0) := by
    by_cases h : x = y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have h := sum_charT4_mul_conj y x
  rw [hif] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _ 

/-- The product of two outer fields at the same point of the 4-torus. -/
def samePointProductT4 (F G : Torus4 (n := n) → ℂ) : Torus4 (n := n) → ℂ := fun x => F x * G x

/-- **The same-point product of two outer fields on the 4-torus, in momentum space**: the
four-dimensional convolution of their transforms, every term of which carries conserved
momentum. -/
noncomputable def momentumProductT4 (F G : Torus4 (n := n) → ℂ) (k : Torus4 (n := n)) : ℂ :=
  ((n : ℂ)⁻¹) ^ 4 * ∑ p : Torus4 (n := n), dftT4 F p * dftT4 G (k - p)

/-- **The product-to-convolution theorem on the 4-torus**: the transform of the same-point
product is the convolution of the transforms. -/
theorem dftT4_mul_eq_convolution (F G : Torus4 (n := n) → ℂ) (k : Torus4 (n := n)) :
    dftT4 (fun x => F x * G x) k
      = ((n : ℂ)⁻¹) ^ 4 * ∑ p : Torus4 (n := n), dftT4 F p * dftT4 G (k - p) := by
  have hG : ∀ p : Torus4 (n := n),
      dftT4 G (k - p) = ∑ v, charT4 k v * conj (charT4 p v) * G v := by
    intro p
    rw [dftT4]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [charT4_sub]
  have hprod : ∀ p : Torus4 (n := n), dftT4 F p * dftT4 G (k - p)
      = ∑ u, ∑ v, (charT4 p u * F u) * ((charT4 k v * conj (charT4 p v)) * G v) := by
    intro p
    rw [hG p]
    change (∑ u, charT4 p u * F u) * (∑ v, charT4 k v * conj (charT4 p v) * G v)
        = ∑ u, ∑ v, (charT4 p u * F u) * ((charT4 k v * conj (charT4 p v)) * G v)
    rw [Finset.sum_mul_sum]
  rw [dftT4, Finset.sum_congr rfl fun p _ => hprod p]
  have hswap : ∑ p : Torus4 (n := n), ∑ u, ∑ v,
        (charT4 p u * F u) * ((charT4 k v * conj (charT4 p v)) * G v)
      = ∑ u, ∑ v, ∑ p, (charT4 p u * F u) * ((charT4 k v * conj (charT4 p v)) * G v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  have hinner : ∀ u v : Torus4 (n := n),
      (∑ p : Torus4 (n := n), (charT4 p u * F u) * ((charT4 k v * conj (charT4 p v)) * G v))
        = (F u * (charT4 k v * G v)) * (if u = v then (n : ℂ) ^ 4 else 0) := by
    intro u v
    rw [← sum_charT4_mul_conj u v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp only [hinner]
  have hcollapse : ∀ C : Torus4 (n := n) → Torus4 (n := n) → ℂ,
      ∑ u, ∑ v, C u v * (if u = v then (n : ℂ) ^ 4 else 0)
        = (n : ℂ) ^ 4 * ∑ u, C u u := by
    intro C
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single u]
    · rw [if_pos rfl]; ring
    · intro v _ hv
      rw [if_neg (Ne.symm hv), mul_zero]
    · intro hu; exact absurd (Finset.mem_univ u) hu
  rw [hcollapse]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h1 : ((n : ℂ)⁻¹) ^ 4 * (n : ℂ) ^ 4 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hn0, one_pow]
  rw [← mul_assoc, h1, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **The product-to-convolution theorem, in the form of `dft_samePointProduct`.** -/
theorem dftT4_samePointProductT4 (F G : Torus4 (n := n) → ℂ) :
    dftT4 (samePointProductT4 F G) = momentumProductT4 F G := by
  funext k
  exact dftT4_mul_eq_convolution F G k

/-- **Plancherel on the 4-torus**: `∑ k, conj (F̂ k) Ĝ k = n⁴ ∑ x, conj (F x) G x`. -/
theorem sum_conj_dftT4_mul_dftT4 (f g : Torus4 (n := n) → ℂ) :
    ∑ k : Torus4 (n := n), conj (dftT4 f k) * dftT4 g k
      = (n : ℂ) ^ 4 * ∑ x : Torus4 (n := n), conj (f x) * g x := by
  have hconj : ∀ k : Torus4 (n := n),
      conj (dftT4 f k) = ∑ x, conj (charT4 k x) * conj (f x) := by
    intro k
    rw [dftT4, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_mul]
  calc ∑ k : Torus4 (n := n), conj (dftT4 f k) * dftT4 g k
      = ∑ k, (∑ x, conj (charT4 k x) * conj (f x)) * (∑ y, charT4 k y * g y) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hconj k, dftT4]
    _ = ∑ k, ∑ x, ∑ y, (conj (charT4 k x) * conj (f x)) * (charT4 k y * g y) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul_sum]
    _ = ∑ x, ∑ y, ∑ k, (conj (charT4 k x) * conj (f x)) * (charT4 k y * g y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, (conj (f x) * g y) * (if x = y then (n : ℂ) ^ 4 else 0) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [← sum_conj_charT4_mul_charT4 x y, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ = (n : ℂ) ^ 4 * ∑ x : Torus4 (n := n), conj (f x) * g x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_eq_single x]
          · rw [if_pos rfl]; ring
          · intro y _ hy
            rw [if_neg (Ne.symm hy), mul_zero]
          · intro hx; exact absurd (Finset.mem_univ x) hx

/-- The one-particle matrix of multiplication by a symbol on the 4-torus: the coefficient of
`a†_k a_i` is the transform of `V` at the momentum *transfer* `k − i`. -/
noncomputable def momentumColT4 (V : Torus4 (n := n) → ℂ) (k i : Torus4 (n := n)) : ℂ :=
  ((n : ℂ)⁻¹) ^ 4 * dftT4 V (k - i)

/-- **Multiplication by a symbol on the 4-torus acts by momentum convolution.** -/
theorem dftT4_mul_momentumColT4 (V f : Torus4 (n := n) → ℂ) (k : Torus4 (n := n)) :
    dftT4 (fun x => V x * f x) k = ∑ i : Torus4 (n := n), momentumColT4 V k i * dftT4 f i := by
  rw [dftT4_mul_eq_convolution]
  simp only [momentumColT4, Finset.mul_sum]
  refine Finset.sum_bij' (fun i _ => k - i) (fun p _ => k - p)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun i _ => by simp) (fun p _ => by simp) (fun i _ => ?_)
  simp only [sub_sub_cancel]
  ring

/-- **The coefficient of a product of two outer fields at a point of the 4-torus is itself a
convolution**: `momentumColT4 (F·G) k i = n⁻⁸ Σ_{p+q = k−i} F̂(p) Ĝ(q)`, every term carrying
conserved four-momentum. -/
theorem momentumColT4_samePointProductT4 (F G : Torus4 (n := n) → ℂ) (k i : Torus4 (n := n)) :
    momentumColT4 (samePointProductT4 F G) k i
      = ((n : ℂ)⁻¹) ^ 8 * ∑ p : Torus4 (n := n), dftT4 F p * dftT4 G (k - i - p) := by
  rw [momentumColT4, show samePointProductT4 F G = (fun x => F x * G x) from rfl,
    dftT4_mul_eq_convolution, ← mul_assoc, ← pow_add]

/-- Reindexing a sum over the 4-torus by a translation: `∑_k f (k − i) = ∑_p f p`. -/
theorem sum_sub_right_t4 (i : Torus4 (n := n)) (f : Torus4 (n := n) → ℝ) :
    ∑ k : Torus4 (n := n), f (k - i) = ∑ p : Torus4 (n := n), f p := by
  refine Fintype.sum_equiv
    { toFun := fun k => k - i
      invFun := fun p => p + i
      left_inv := fun k => by simp
      right_inv := fun p => by simp } (fun k => f (k - i)) f (fun k => rfl)

/-- **Plancherel on the 4-torus, in norm form**: `∑_p ‖f̂ p‖² = n⁴ ∑_x ‖f x‖²`.  This is
`sum_conj_dftT4_mul_dftT4` with `g = f`, read through `conj z * z = ↑‖z‖²`. -/
theorem sum_norm_sq_dftT4 (f : Torus4 (n := n) → ℂ) :
    ∑ p : Torus4 (n := n), ‖dftT4 f p‖ ^ 2
      = (n : ℝ) ^ 4 * ∑ x : Torus4 (n := n), ‖f x‖ ^ 2 := by
  have hc : ∀ z : ℂ, conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have h := sum_conj_dftT4_mul_dftT4 f f
  rw [Finset.sum_congr rfl (fun k _ => hc (dftT4 f k)),
    Finset.sum_congr rfl (fun x _ => hc (f x))] at h
  have hcast : ((∑ k : Torus4 (n := n), ‖dftT4 f k‖ ^ 2 : ℝ) : ℂ)
      = ((n : ℝ) ^ 4 * ∑ x : Torus4 (n := n), ‖f x‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum]
    simpa using h
  exact Complex.ofReal_injective hcast

/-- The norm factor of the momentum column: `‖n⁻⁴ V̂(k−i)‖² = (n⁸)⁻¹ ‖V̂(k−i)‖²`. -/
theorem norm_sq_momentumColT4 (V : Torus4 (n := n) → ℂ) (k i : Torus4 (n := n)) :
    ‖momentumColT4 V k i‖ ^ 2
      = ((n : ℝ) ^ 8)⁻¹ * ‖dftT4 V (k - i)‖ ^ 2 := by
  rw [momentumColT4, norm_mul, mul_pow, norm_pow]
  have hn : ‖(((n : ℂ))⁻¹)‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hn]
  have h8 : ((((n : ℝ))⁻¹) ^ 4) ^ 2 = ((n : ℝ) ^ 8)⁻¹ := by
    rw [← pow_mul, ← inv_pow]
  rw [h8]

/-- **The momentum-transfer matrix on the 4-torus has the mass of the field.**
`momentumColT4 V k i = n⁻⁴ V̂(k−i)`, each transfer `k − i` is hit `n⁴` times, and Plancherel on
`(ℤ/n)⁴` gives `∑_p ‖V̂ p‖² = n⁴ ∑_x ‖V x‖²`; the `(n⁸)⁻¹` of the squared entries then cancels
exactly, so the mass is `∑_x ‖V x‖²` — the identity of `momentumCol_hs_mass` on the four-torus. -/
theorem momentumColT4_hs_mass (V : Torus4 (n := n) → ℂ) :
    ∑ k : Torus4 (n := n), ∑ i : Torus4 (n := n), ‖momentumColT4 V k i‖ ^ 2
      = ∑ x : Torus4 (n := n), ‖V x‖ ^ 2 := by
  have hpair : ∑ k : Torus4 (n := n), ∑ i : Torus4 (n := n), ‖dftT4 V (k - i)‖ ^ 2
      = (n : ℝ) ^ 4 * ∑ p : Torus4 (n := n), ‖dftT4 V p‖ ^ 2 := by
    rw [Finset.sum_comm]
    have hinner : ∀ i : Torus4 (n := n),
        ∑ k : Torus4 (n := n), ‖dftT4 V (k - i)‖ ^ 2
          = ∑ p : Torus4 (n := n), ‖dftT4 V p‖ ^ 2 :=
      fun i => sum_sub_right_t4 i (fun x => ‖dftT4 V x‖ ^ 2)
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    have hcard : Fintype.card (Torus4 (n := n)) = n ^ 4 := by
      change Fintype.card (ZMod n × ZMod n × ZMod n × ZMod n) = n ^ 4
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ZMod.card]
      ring
    rw [hcard, Nat.cast_pow]
  calc ∑ k : Torus4 (n := n), ∑ i : Torus4 (n := n), ‖momentumColT4 V k i‖ ^ 2
      = ∑ k : Torus4 (n := n), ∑ i : Torus4 (n := n),
          ((n : ℝ) ^ 8)⁻¹ * ‖dftT4 V (k - i)‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => norm_sq_momentumColT4 V k i
    _ = ((n : ℝ) ^ 8)⁻¹ * ∑ k : Torus4 (n := n), ∑ i : Torus4 (n := n),
          ‖dftT4 V (k - i)‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ = ((n : ℝ) ^ 8)⁻¹ * ((n : ℝ) ^ 4 * ∑ p : Torus4 (n := n), ‖dftT4 V p‖ ^ 2) := by
        rw [hpair]
    _ = ((n : ℝ) ^ 8)⁻¹ * ((n : ℝ) ^ 4
          * ((n : ℝ) ^ 4 * ∑ x : Torus4 (n := n), ‖V x‖ ^ 2)) := by
        rw [sum_norm_sq_dftT4]
    _ = ∑ x : Torus4 (n := n), ‖V x‖ ^ 2 := by
        have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
        field_simp

/-- **The form of the two-field same-point product on the 4-torus is the momentum
convolution.** -/
theorem samePointProductT4_form_eq_momentum (F G f : Torus4 (n := n) → ℂ) :
    ∑ k : Torus4 (n := n), conj (dftT4 f k)
        * ∑ i : Torus4 (n := n), momentumColT4 (samePointProductT4 F G) k i * dftT4 f i
      = (n : ℂ) ^ 4 * ∑ x : Torus4 (n := n),
          conj (f x) * samePointProductT4 F G x * f x := by
  have hmat : ∀ k : Torus4 (n := n),
      (∑ i : Torus4 (n := n), momentumColT4 (samePointProductT4 F G) k i * dftT4 f i)
        = dftT4 (fun x => samePointProductT4 F G x * f x) k :=
    fun k => (dftT4_mul_momentumColT4 (samePointProductT4 F G) f k).symm
  simp only [hmat]
  have h := sum_conj_dftT4_mul_dftT4 f (fun x => samePointProductT4 F G x * f x)
  simpa only [mul_assoc] using h

omit [NeZero n] in
theorem sub_of_add_eq_t4 {k a b : Torus4 (n := n)} (h : a + b = k) : k - a = b := by
  rw [← h, add_sub_cancel_left]

/-- The partner of `p` at fixed total momentum `k`: the bijection `p ↦ (p, k − p)` onto the
pairs summing to `k`. -/
def torus4Split (k : Torus4 (n := n)) :
    Torus4 (n := n) ≃ {pq : Torus4 (n := n) × Torus4 (n := n) // pq.1 + pq.2 = k} :=
  { toFun := fun p => ⟨(p, k - p), by rw [add_sub_cancel]⟩
    invFun := fun pq => pq.1.1
    left_inv := fun p => rfl
    right_inv := fun pq => by
      refine Subtype.ext ?_
      change ((pq.1.1, k - pq.1.1) : Torus4 (n := n) × Torus4 (n := n)) = pq.1
      rw [Prod.mk.injEq]
      exact ⟨rfl, sub_of_add_eq_t4 pq.2⟩ }

/-- **Momentum conservation on the 4-torus**: the momentum-space product is the sum over two
four-momenta whose sum is exactly `k` — the one-dimensional statement, with four-dimensional
conserved momentum. -/
theorem momentumProductT4_eq_sum_conserved (F G : Torus4 (n := n) → ℂ) (k : Torus4 (n := n)) :
    momentumProductT4 F G k
      = ((n : ℂ)⁻¹) ^ 4 * ∑ pq : {pq : Torus4 (n := n) × Torus4 (n := n) // pq.1 + pq.2 = k},
          dftT4 F pq.1.1 * dftT4 G pq.1.2 := by
  rw [momentumProductT4]
  congr 1
  refine Fintype.sum_equiv (torus4Split k) (fun p => dftT4 F p * dftT4 G (k - p))
    (fun pq => dftT4 F pq.1.1 * dftT4 G pq.1.2) (fun p => ?_)
  change dftT4 F p * dftT4 G (k - p) = dftT4 F p * dftT4 G (k - p)
  rfl

/-- **Momentum conservation, component by component.**  The 4-torus product is a fourfold sum
in which each term carries the four momentum components `kᵢ − pᵢ`: the one-dimensional
conservation law, applied in each cyclic direction and tensored. -/
theorem momentumProductT4_eq_sum_four_conserved (F G : Torus4 (n := n) → ℂ)
    (k : Torus4 (n := n)) :
    momentumProductT4 F G k
      = ((n : ℂ)⁻¹) ^ 4 * ∑ p1 : ZMod n, ∑ p2 : ZMod n, ∑ p3 : ZMod n, ∑ p4 : ZMod n,
          dftT4 F (p1, p2, p3, p4)
            * dftT4 G (k.1 - p1, k.2.1 - p2, k.2.2.1 - p3, k.2.2.2 - p4) := by
  rw [momentumProductT4, sum_torus4
    (fun a b c d => dftT4 F (a, b, c, d) * dftT4 G (k - (a, b, c, d)))]
  congr 1

omit [NeZero n] in
/-- **The splitting in coordinates**: a four-momentum splits exactly when each of its four
components does.  This is the coordinate form of the conservation law checked above. -/
theorem torus4_add_iff (p q k : Torus4 (n := n)) :
    p + q = k ↔ p.1 + q.1 = k.1 ∧ p.2.1 + q.2.1 = k.2.1
      ∧ p.2.2.1 + q.2.2.1 = k.2.2.1 ∧ p.2.2.2 + q.2.2.2 = k.2.2.2 := by
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add]

/-- A real outer field on the 4-torus, read as a complex one. -/
def realFieldT4 (F : Torus4 (n := n) → ℝ) : Torus4 (n := n) → ℂ := fun x => (F x : ℂ)

/-- **The squared field at a point of the 4-torus is a nonnegative form.**  For a real field
`F`, `Σ_x conj (f x) (F·F)(x) f x` is the sum of `F(x)²‖f x‖²` over the four-torus, hence
nonnegative — the positivity input of the Phase-4 chain in four dimensions, read off the
momentum column `momentumColT4` through `samePointProductT4_form_eq_momentum`. -/
theorem samePointProductT4_real_self_form_nonneg (F : Torus4 (n := n) → ℝ)
    (f : Torus4 (n := n) → ℂ) :
    0 ≤ (∑ x : Torus4 (n := n),
      conj (f x) * samePointProductT4 (realFieldT4 F) (realFieldT4 F) x * f x).re := by
  have hterm : ∀ x : Torus4 (n := n),
      conj (f x) * samePointProductT4 (realFieldT4 F) (realFieldT4 F) x * f x
        = (((F x) ^ 2 * Complex.normSq (f x) : ℝ) : ℂ) := by
    intro x
    have hmul : ((F x : ℂ)) * ((F x : ℂ)) = (((F x) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    calc conj (f x) * samePointProductT4 (realFieldT4 F) (realFieldT4 F) x * f x
        = (((F x) ^ 2 : ℝ) : ℂ) * (conj (f x) * f x) := by
          rw [samePointProductT4, realFieldT4, hmul]
          ring
      _ = (((F x) ^ 2 : ℝ) : ℂ) * ((Complex.normSq (f x) : ℝ) : ℂ) := by
          rw [Complex.normSq_eq_conj_mul_self]
      _ = (((F x) ^ 2 * Complex.normSq (f x) : ℝ) : ℂ) := by
          push_cast
          ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Complex.re_sum]
  exact Finset.sum_nonneg fun x _ => by
    rw [Complex.ofReal_re]
    exact mul_nonneg (sq_nonneg (F x)) (Complex.normSq_nonneg (f x))

/-- **A finite chain of coincident-point factors on the 4-torus keeps the mass multiplicative.**
The four-torus reading of `chain_hs_mass`: `‖∏ j, F j x‖ = ∏ j, ‖F j x‖` pointwise, so the `ℓ²` mass
of the chain at one point of `(ℤ/n)⁴` is the sum of the products of the squared pointwise norms. -/
theorem chain_hs_massT4 {r : ℕ} (F : Fin r → Torus4 (n := n) → ℂ) :
    ∑ x : Torus4 (n := n), ‖∏ j, F j x‖ ^ 2
      = ∑ x : Torus4 (n := n), ∏ j, ‖F j x‖ ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [norm_prod, Finset.prod_pow]

/-- **The form of a finite chain at a point of the 4-torus is its momentum-transfer form.**  The
four-torus version of the `σ` reading in `chain_form_hs_bound`: the chain `∏ j, F j` enters the form
only through `momentumColT4 (∏ j, F j)`, whose entries are the transform of the chain at the
momentum transfer `k − i`, and `chain_hs_massT4` makes the mass multiplicative.  (This section
carries the form identity rather than a Hilbert–Schmidt *bound*: `momentumCol_hs_mass` has no
two-factor analogue in `MomentumProductTorus4`, so the four-torus chain is read through the form
rather than through `momentumCol`'s mass.) -/
theorem chain_form_eq_momentumT4 {r : ℕ} (F : Fin r → Torus4 (n := n) → ℂ)
    (f : Torus4 (n := n) → ℂ) :
    ∑ k : Torus4 (n := n), conj (dftT4 f k)
        * ∑ i : Torus4 (n := n), momentumColT4 (fun x => ∏ j, F j x) k i * dftT4 f i
      = (n : ℂ) ^ 4 * ∑ x : Torus4 (n := n), conj (f x) * (∏ j, F j x) * f x := by
  have h := samePointProductT4_form_eq_momentum (fun x => ∏ j : Fin r, F j x)
    (fun _ => (1 : ℂ)) f
  have hsym : samePointProductT4 (fun x => ∏ j : Fin r, F j x) (fun _ => (1 : ℂ))
      = fun x => ∏ j : Fin r, F j x := by
    funext x
    simp [samePointProductT4]
  rw [hsym] at h
  exact h

/-- **The 4-torus chain mass bound.**  Composing `momentumColT4_hs_mass` with
`chain_hs_massT4`: the momentum-transfer matrix of a chain of `r` coincident-point factors has mass
`∑_x ∏_j ‖F_j x‖²`, exactly as `chain_form_hs_bound` reads the chain in one dimension.  So the chain
has a genuine Hilbert–Schmidt constant on `(ℤ/n)⁴`, not merely a form identity. -/
theorem momentumColT4_chain_hs_mass {r : ℕ} (F : Fin r → Torus4 (n := n) → ℂ) :
    ∑ k : Torus4 (n := n), ∑ i : Torus4 (n := n),
        ‖momentumColT4 (fun x => ∏ j, F j x) k i‖ ^ 2
      = ∑ x : Torus4 (n := n), ∏ j, ‖F j x‖ ^ 2 := by
  rw [momentumColT4_hs_mass, chain_hs_massT4]

end MomentumProductTorus4

/-! ## 6. The strong-resolvent mode: the hypothesis `softmodes.md` §5.2 states

Section 2 transfers the certified gap across an **operator-norm** limit.  `softmodes.md` §5.2
phrases the passage through the **strong-resolvent** limit (`H_n → H_F` strongly in the resolvent
sense), which is strictly weaker than norm convergence and is the mode a truncation family
delivers.  `BookProof.SpectralGapStability` already carries the abstract mechanism
(`gapAt_of_strongResolvent_limit`, `notMem_spectrum_of_strongResolvent`); what is missing there
is the *left end* — the resolvents themselves.  A strong-resolvent hypothesis speaks about
`(A_m − λ)⁻¹`, an object that has to be produced from the separation, and this section produces
it:

* **`certifiedResolvent`** — the left inverse of `A − λ` whose existence the gap gives, with
  **`certifiedResolvent_left`** and **`certifiedResolvent_norm`** (`‖R ξ‖ ≤ ‖ξ‖/d`) as its two
  properties;
* **`gap_survives_strongResolvent`** — §5.2's transfer: if the *certified* resolvents of the
truncations converge **pointwise** to a left inverse of `B − (l+b)/2`, then `B` has the same
  quantitative gap `(b−l)/2` at the window centre as the norm limit of Section 2.  The uniform
  bound is *not* a hypothesis — it is `certifiedResolvent_norm`, read off the separation;
* **`notMem_spectrum_of_strongResolvent_limit`** — hence the window centre is not in the
  spectrum of the limit;
* **`continuum_gap_of_form_domination_strongResolvent`** — the same at the plan's constant
  `c₁Δ_ref/2`, with `β = l + c₁Δ_ref`, so Phase 5.2 is available in the mode it is stated in.

What this does *not* do: it does not prove that the truncations converge in the strong-resolvent
sense (that is the open analytic question, exactly as in the norm mode), and it does not identify
`A` with the Yang–Mills Hamiltonian.
-/

section StrongResolventTransfer

/-- **The certified resolvent of a separated operator.**  For a bounded self-adjoint `A` with
`GapAt A lam d` and `d > 0`, this is the left inverse of `A − lam` whose existence
`exists_leftInverse_of_gapAt` proves — the operator a strong-resolvent hypothesis speaks about. -/
noncomputable def certifiedResolvent (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {lam d : ℝ}
    (hd : 0 < d) (h : GapAt A lam d) : F →L[ℂ] F :=
  Classical.choose (exists_leftInverse_of_gapAt hA hd h)

/-- It inverts `A − lam` on the left. -/
theorem certifiedResolvent_left (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {lam d : ℝ}
    (hd : 0 < d) (h : GapAt A lam d) (x : F) :
    certifiedResolvent A hA hd h (A x - (lam : ℂ) • x) = x :=
  (Classical.choose_spec (exists_leftInverse_of_gapAt hA hd h)).1 x

/-- Its norm is at most `d⁻¹`: the uniform resolvent bound of `softmodes.md` §5.2, which is what
makes the strong-resolvent transfer lossless. -/
theorem certifiedResolvent_norm (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {lam d : ℝ}
    (hd : 0 < d) (h : GapAt A lam d) (ξ : F) :
    ‖certifiedResolvent A hA hd h ξ‖ ≤ ‖ξ‖ / d :=
  (Classical.choose_spec (exists_leftInverse_of_gapAt hA hd h)).2 ξ

/-- **Phase 5.2 in the strong-resolvent mode.**  Let every truncation `A m` have its spectrum in
`{l} ∪ [b, ∞)`.  Then each `A m − (l+b)/2` has a certified left inverse of norm at most
`((b−l)/2)⁻¹` (`certifiedResolvent_norm`).  If those certified resolvents converge **pointwise**
to a left inverse `S` of `B − (l+b)/2`, the limit inherits the gap `(b−l)/2` at the window centre
with no loss and without any norm convergence.

So the only input the plan's hypothesis adds to the analytic separation is the pointwise
convergence of the resolvents — the uniform bound comes from the separation itself. -/
theorem gap_survives_strongResolvent (A : ℕ → F →L[ℂ] F) (hsa : ∀ m, IsSelfAdjoint (A m))
    {l b : ℝ} (hsep : ∀ m, SpectralSeparation (A m) l b) (hd : 0 < (b - l) / 2)
    {B S : F →L[ℂ] F}
    (hconv : ∀ ξ, Tendsto (fun m =>
        certifiedResolvent (A m) (hsa m) hd (gapAt_of_separation (hsa m) (hsep m)) ξ)
      atTop (𝓝 (S ξ)))
    (hS : ∀ x : F, S (B x - ((((l + b) / 2 : ℝ)) : ℂ) • x) = x) :
    GapAt B ((l + b) / 2) ((b - l) / 2) :=
  gapAt_of_strongResolvent_limit hd
    (fun m ξ => certifiedResolvent_norm (A m) (hsa m) hd
      (gapAt_of_separation (hsa m) (hsep m)) ξ)
    hconv hS

/-- **The limit's spectrum has a hole, in the strong-resolvent mode**: `softmodes.md` §5.2's
conclusion for a self-adjoint limit, where Section 2 only reaches the operator-norm mode. -/
theorem notMem_spectrum_of_strongResolvent_limit (A : ℕ → F →L[ℂ] F)
    (hsa : ∀ m, IsSelfAdjoint (A m)) {l b : ℝ}
    (hsep : ∀ m, SpectralSeparation (A m) l b) (hd : 0 < (b - l) / 2)
    {B S : F →L[ℂ] F} (hB : IsSelfAdjoint B)
    (hconv : ∀ ξ, Tendsto (fun m =>
        certifiedResolvent (A m) (hsa m) hd (gapAt_of_separation (hsa m) (hsep m)) ξ)
      atTop (𝓝 (S ξ)))
    (hS : ∀ x : F, S (B x - ((((l + b) / 2 : ℝ)) : ℂ) • x) = x) :
    (((l + b) / 2 : ℝ) : ℂ) ∉ spectrum ℂ B :=
  notMem_spectrum_of_gapAt hB hd
    (gap_survives_strongResolvent A hsa hsep hd hconv hS)

/-- **Phase 5.2 at the plan's constant, in the strong-resolvent mode.**  With the analytic
separation `β = l + c₁Δ_ref` (Phases 3–4), the certified resolvents at the window centre
`l + c₁Δ_ref/2` are bounded by `2/(c₁Δ_ref)`; if they converge pointwise to a left inverse of
`B − (l + c₁Δ_ref/2)`, the limit keeps a gap of exactly `c₁Δ_ref/2` and its spectrum has a hole
of that radius — the conclusion of `continuum_gap_of_form_domination`, under §5.2's hypothesis. -/
theorem continuum_gap_of_form_domination_strongResolvent (A : ℕ → F →L[ℂ] F)
    (hsa : ∀ m, IsSelfAdjoint (A m)) {l c₁ Δ : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : ∀ m, SpectralSeparation (A m) l (l + c₁ * Δ))
    (hd : 0 < c₁ * Δ / 2) {B S : F →L[ℂ] F} (hB : IsSelfAdjoint B)
    (hconv : ∀ ξ, Tendsto (fun m =>
        certifiedResolvent (A m) (hsa m) hd (gapAt_of_form_domination (hsa m) hc hΔ (hsep m)) ξ)
      atTop (𝓝 (S ξ)))
    (hS : ∀ x : F, S (B x - (((l + c₁ * Δ / 2 : ℝ)) : ℂ) • x) = x) :
    GapAt B (l + c₁ * Δ / 2) (c₁ * Δ / 2)
      ∧ ((l + c₁ * Δ / 2 : ℝ) : ℂ) ∉ spectrum ℂ B := by
  have hgap : GapAt B (l + c₁ * Δ / 2) (c₁ * Δ / 2) :=
    gapAt_of_strongResolvent_limit hd
      (fun m ξ => certifiedResolvent_norm (A m) (hsa m) hd
        (gapAt_of_form_domination (hsa m) hc hΔ (hsep m)) ξ)
      hconv hS
  exact ⟨hgap, notMem_spectrum_of_gapAt hB hd hgap⟩

end StrongResolventTransfer

end BookProof.TempleContinuumGap
