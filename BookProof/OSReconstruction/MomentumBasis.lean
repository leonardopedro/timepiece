import Mathlib
import BookProof.Sirk.ChapterSirkTrotterKatoGalerkin

/-!
# Momentum cells, the lattice overlap, and the exact Hamiltonian

Plan: `cftproof.md` Phases 3–4.  The reflection-positivity hypothesis of Phase 3.3 must be
read in **momentum space**: a product of fields at the same lattice site becomes a
*convolution* of their momentum-space transforms (the Fourier convolution theorem, the
discrete twin of `BookProof.NsAdvectionConvolution.fourier_mul_eq_convolution` and of the
`𝓕(f·g) = (1/n)(F ⋆ G)` identity pinned in `test/numerical-physics/navier-stokes.md`).
This module proves that identity on the finite torus and uses it to write the
Osterwalder–Schrader form of a translation-invariant two-point function as a weighted sum
over momentum.

The second half is the basis change the plan needs for the emergent Hamiltonian.  Momentum
space is itself a lattice — the dual lattice — and one may replace its plane waves by any
orthonormal family of wave packets ("cells").  The overlap matrix between such a family and
the 4D Euclidean lattice basis is unitary, which is the statement that the translation
between the two bases loses nothing; the exact Hamiltonian is the diagonal momentum
operator transported through that overlap.  No truncation enters the definition.  The
approximation is a **compression** to a subspace (a coarser lattice, or a momentum cutoff),
and `compressed_hamiltonian_tendsto` proves that the compressed Hamiltonian converges
strongly to the exact one whenever the compressions are contractions converging strongly to
the identity — the hypothesis a refining spatial lattice satisfies.

## Contents

* `conj_stdAddChar`, `char_add`, `char_add_site`, `sum_char_mul_conj` — the character
  identities on `ZMod n`;
* **`dft_convolution`** — `𝓕(F ⋆ G) = 𝓕F · 𝓕G`;
* **`dft_mul_eq_convolution`** — **the product-to-convolution theorem**,
  `𝓕(F · G) = n⁻¹ • (𝓕F ⋆ 𝓕G)`: multiplication of fields in space is convolution in
  momentum;
* `transferKernel` — the reflected two-point kernel in transfer-factorised form,
  `K x y = ∑ i, w i * u i x * conj (u i y)` (the free-field momentum modes are
  `u_k(t,x) = ρ_k^t · χ_k(x)`);
* **`transferForm_eq`** — its OS form is `∑ i, w i * ‖∑ x, F x * u i x‖²`;
* **`reflection_positivity_momentum`** — with `w i ≥ 0` that form is nonnegative: reflection
  positivity in momentum space;
* `covariance`, **`covarianceForm_eq_dft`** — for a translation-invariant symbol the two-point
  form is the weighted Plancherel sum `∑ k, w k * ‖𝓕F k‖²`, and `covarianceForm_nonneg`
  records that it is nonnegative for `w ≥ 0`;
* `freePropagator` — the free lattice propagator in Källén–Lehmann form,
  `G(p,q) = ∑ a, w a * ρ a ^ |t_p − t_q| * χ_a(x_p − x_q)`;
* **`freePropagator_reflect_eq_transfer`** — **the Källén–Lehmann factorization**: on the future
  half-space the reflected propagator equals `transferKernel (freeMode mom ρ) w`, so the transfer
  kernel of Section 2 is *derived* for the free field, not supplied;
* `timeWindow`, **`freeOSForm_eq_momentum`** — the half-space OS form of the free propagator is
  `∑ a, w a * ‖∑ p, F p * u a p‖²`, and `free_reflection_positive` records its nonnegativity;
* `freePropagator_single`, `freePropagator_single_reflect` — the explicit one-mass propagator
  and its rank-one reflected factorization;
* `overlap`, `overlap_orthonormal`, `overlap_orthonormal_pos` — the momentum/lattice overlap
  is unitary in both directions;
* `IsOrthonormalCells`, `cellLatticeOverlap`, **`cellLatticeOverlap_unitary`** — the overlap
  of a general orthonormal momentum cell family with the lattice is unitary; `cellHamiltonian`
  is the exact Hamiltonian read in the cell basis;
* `exactHamiltonian`, **`exactHamiltonian_eigenvector`** — the exact Hamiltonian in the
  lattice basis, diagonalised by the overlap (no approximation);
* **`compressed_hamiltonian_tendsto`** — the compressed (coarse-lattice) Hamiltonian
  converges strongly to the exact one;
* **`compressed_strongResolventConvergence`** — the SIRK resolvent hypothesis, closed for the
  compressed free Hamiltonian;
* **`compressed_flow_tendsto` / `compressed_flow_transfer`** — the lattice Hamiltonians' flows
  converge to the flow of the exact operator read as the unbounded `ofBounded A` (SIRK /
  Trotter–Kato);
* **`bounded_flow_tendsto_unbounded`** — strong resolvent convergence of bounded Hamiltonians to
  a genuinely unbounded self-adjoint `T` gives convergence of their flows to `T`'s: the
  bounded-to-unbounded transfer.

## Boundary

The lattice here is one cyclic direction (`ZMod n`); the 4D statement is the tensor product
of four copies and adds no mathematics, only index bookkeeping.  The two-point form is the
analytic input: passing from it to all polynomial observables is the Gaussian/Wick step,
which the corpus does not formalise (no measure on the lattice configurations — see
`docs/euclidean_cft_proof.md`).  The convergence statement is for a bounded exact
Hamiltonian, the finite-momentum-window operator this file constructs; for the unbounded
continuum operator the same estimate holds on the domain, where `‖P_N ψ − ψ‖ → 0` must be
replaced by the corresponding graph-norm convergence.
-/

namespace BookProof.OSReconstruction

open Finset Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Characters and the convolution theorem -/

/-- The character of momentum `k` at the lattice site `x`, in the sign convention of
`ZMod.dft` (`𝓕 Φ k = ∑ x, χ k x * Φ x`). -/
def char (k x : ZMod n) : ℂ := ZMod.stdAddChar (-(x * k))

@[simp]
theorem char_zero (x : ZMod n) : char (0 : ZMod n) x = 1 := by
  simp [char]

/-- Characters add in momentum: `χ (k + l) x = χ k x * χ l x`. -/
theorem char_add (k l x : ZMod n) : char (k + l) x = char k x * char l x := by
  rw [char, char, char, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Complex conjugation sends a character to the character of the negated momentum. -/
theorem conj_stdAddChar (a : ZMod n) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv]

/-- Complex conjugation sends a character to the character of the negated momentum. -/
theorem conj_char (k x : ZMod n) : conj (char k x) = char (-k) x := by
  change conj (ZMod.stdAddChar (-(x * k))) = ZMod.stdAddChar (-(x * -k))
  rw [conj_stdAddChar]
  congr 1
  ring

/-- Orthogonality of characters. -/
theorem sum_char (a : ZMod n) :
    ∑ x : ZMod n, ZMod.stdAddChar (x * a) = if a = 0 then (n : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := n)) a
    (ZMod.isPrimitive_stdAddChar n)
  simpa [ZMod.card] using h

/-- **Orthogonality in position space**: `∑ x, χ k x * conj (χ l x) = n δ_{kl}`. -/
theorem sum_char_mul_conj (k l : ZMod n) :
    ∑ x : ZMod n, char k x * conj (char l x) = if k = l then (n : ℂ) else 0 := by
  have h : ∀ x : ZMod n, char k x * conj (char l x) =
      ZMod.stdAddChar (x * (l - k)) := by
    intro x
    rw [conj_char, ← char_add, char]
    congr 1
    ring
  simp only [h, sum_char]
  simp [sub_eq_zero, eq_comm]

/-- The character is additive in position. -/
theorem char_add_site (k x y : ZMod n) : char k (x + y) = char k x * char k y := by
  rw [char, char, char, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- **The discrete convolution theorem**: `𝓕 (F ⋆ G) = 𝓕F · 𝓕G`. -/
theorem dft_convolution (F G : ZMod n → ℂ) :
    ZMod.dft (fun k => ∑ i : ZMod n, F i * G (k - i)) =
      fun k => ZMod.dft F k * ZMod.dft G k := by
  funext k
  simp only [ZMod.dft_apply, smul_eq_mul]
  calc
    ∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * ∑ i : ZMod n, F i * G (j - i)
        = ∑ j : ZMod n, ∑ i : ZMod n,
            ZMod.stdAddChar (-(j * k)) * (F i * G (j - i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ i : ZMod n, ∑ j : ZMod n,
            ZMod.stdAddChar (-(j * k)) * (F i * G (j - i)) := by
          rw [Finset.sum_comm]
    _ = ∑ i : ZMod n, (ZMod.stdAddChar (-(i * k)) * F i) *
            ∑ y : ZMod n, ZMod.stdAddChar (-(y * k)) * G y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (∑ j : ZMod n, ZMod.stdAddChar (-(j * k)) * (F i * G (j - i)))
              = ∑ y : ZMod n, ZMod.stdAddChar (-((y + i) * k)) * (F i * G y) from by
                refine (Fintype.sum_equiv (Equiv.addRight i)
                  (fun y => ZMod.stdAddChar (-((y + i) * k)) * (F i * G y))
                  (fun j => ZMod.stdAddChar (-(j * k)) * (F i * G (j - i)))
                  (fun y => ?_)).symm
                simp [add_sub_cancel_right]]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          have hy : ZMod.stdAddChar (-((y + i) * k))
              = ZMod.stdAddChar (-(y * k)) * ZMod.stdAddChar (-(i * k)) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1
            ring
          rw [hy]
          ring
    _ = (∑ x : ZMod n, ZMod.stdAddChar (-(x * k)) * F x) *
          ∑ y : ZMod n, ZMod.stdAddChar (-(y * k)) * G y := by
          rw [Finset.sum_mul]

/-- **The product-to-convolution theorem**: `𝓕 (F · G) = n⁻¹ • (𝓕F ⋆ 𝓕G)`.
Multiplication of fields in position space is a convolution in momentum space. -/
theorem dft_mul_eq_convolution (F G : ZMod n → ℂ) :
    ZMod.dft (fun x => F x * G x) =
      fun k => (n : ℂ)⁻¹ * ∑ i : ZMod n, ZMod.dft F i * ZMod.dft G (k - i) := by
  apply ZMod.dft.injective
  funext k
  have hd : ∀ H : ZMod n → ℂ, ZMod.dft (ZMod.dft H) k = (n : ℂ) * H (-k) := by
    intro H
    rw [ZMod.dft_dft]
    rfl
  have hsm : ZMod.dft (fun j => (n : ℂ)⁻¹ * ∑ i, ZMod.dft F i * ZMod.dft G (j - i)) k =
      (n : ℂ)⁻¹ * ZMod.dft (fun j => ∑ i, ZMod.dft F i * ZMod.dft G (j - i)) k := by
    rw [ZMod.dft_apply, ZMod.dft_apply]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hconv : ZMod.dft (fun j => ∑ i, ZMod.dft F i * ZMod.dft G (j - i)) k =
      ZMod.dft (ZMod.dft F) k * ZMod.dft (ZMod.dft G) k :=
    congrFun (dft_convolution (ZMod.dft F) (ZMod.dft G)) k
  rw [hd (fun x => F x * G x), hsm, hconv, hd F, hd G]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

/-! ## 2. Reflection positivity in momentum space

For a reflection-positive free field the reflected two-point function is not a scalar multiple
of the identity; it factorises through the *transfer modes* across the reflection plane (the
Källén–Lehmann representation, and on the lattice the eigenvalues `ρ_k = e^{-ω_k}` of the
emergent Hamiltonian).  In momentum space the modes are `u_k(t, x) = ρ_k ^ t * χ k x`, so this
is where the momentum decomposition enters.  The OS form is then a sum of modulus squares —
the momentum-space form of Osterwalder–Schrader positivity.

What is *not* true, and is the reason the half-space restriction is essential, is the
stronger claim that a pointwise-positive momentum symbol suffices: the reflected kernel is
the half-space kernel, and its positivity is exactly the factorisation proved below. -/

section MomentumOS

variable {ι : Type*} [Fintype ι]

/-- The reflected two-point kernel in transfer-factorised form,
`K x y = ∑ i, w i * u i x * conj (u i y)` with `w i ≥ 0` — the discrete
Källén–Lehmann representation of the free-field covariance across the reflection plane. -/
def transferKernel {P : Type*} (u : ι → P → ℂ) (w : ι → ℝ) (x y : P) : ℂ :=
  ∑ i : ι, (w i : ℂ) * (u i x * conj (u i y))

omit [NeZero n] in
/-- The double sum against one transfer mode is `S * conj S`. -/
theorem sum_mul_sum_conj {P : Type*} {S : Finset P} (u F : P → ℂ) :
    (∑ x ∈ S, ∑ y ∈ S, F x * (u x * conj (u y)) * conj (F y)) =
      (∑ x ∈ S, F x * u x) * conj (∑ x ∈ S, F x * u x) := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [map_mul]
  ring

/-- **The OS form of a transfer-factorised kernel is a sum of modulus squares** (on any finite
set `S`, in particular a half-space). -/
theorem transferForm_eq {P : Type*}
    (u : ι → P → ℂ) (w : ι → ℝ) (S : Finset P) (F : P → ℂ) :
    (∑ x ∈ S, ∑ y ∈ S, F x * transferKernel u w x y * conj (F y)) =
      ∑ i : ι, (w i : ℂ) * (Complex.normSq (∑ x ∈ S, F x * u i x) : ℂ) := by
  calc
    ∑ x ∈ S, ∑ y ∈ S, F x * transferKernel u w x y * conj (F y)
        = ∑ x ∈ S, ∑ y ∈ S, ∑ i : ι,
            F x * ((w i : ℂ) * (u i x * conj (u i y))) * conj (F y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [transferKernel, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ x ∈ S, ∑ i : ι, ∑ y ∈ S,
            F x * ((w i : ℂ) * (u i x * conj (u i y))) * conj (F y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact Finset.sum_comm
    _ = ∑ i : ι, ∑ x ∈ S, ∑ y ∈ S,
            F x * ((w i : ℂ) * (u i x * conj (u i y))) * conj (F y) :=
          Finset.sum_comm
    _ = ∑ i : ι, (w i : ℂ) *
            ((∑ x ∈ S, F x * u i x) * conj (∑ x ∈ S, F x * u i x)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hw : (∑ x ∈ S, ∑ y ∈ S,
              F x * ((w i : ℂ) * (u i x * conj (u i y))) * conj (F y))
              = (w i : ℂ) * ∑ x ∈ S, ∑ y ∈ S,
                  F x * (u i x * conj (u i y)) * conj (F y) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
          rw [hw, sum_mul_sum_conj]
    _ = ∑ i : ι, (w i : ℂ) *
            (Complex.normSq (∑ x ∈ S, F x * u i x) : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_comm (∑ x ∈ S, F x * u i x), ← Complex.normSq_eq_conj_mul_self]

omit [NeZero n] in
/-- **Reflection positivity in momentum space**: a transfer-factorised reflected kernel with
nonnegative weights is reflection positive; the OS form is a weighted sum of modulus squares. -/
theorem reflection_positivity_momentum {P : Type*}
    (u : ι → P → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (S : Finset P) (F : P → ℂ) :
    0 ≤ ∑ i : ι, w i * Complex.normSq (∑ x ∈ S, F x * u i x) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Complex.normSq_nonneg _)

/-- The translation-invariant two-point kernel with momentum symbol `w`:
`C(x,y) = ∑ k, w k * χ_k(x − y)`. -/
def covariance (w : ZMod n → ℝ) (x y : ZMod n) : ℂ :=
  ∑ k : ZMod n, (w k : ℂ) * char k (x - y)

/-- A translation-invariant kernel is a transfer kernel in the character modes. -/
theorem covariance_eq_transferKernel (w : ZMod n → ℝ) (x y : ZMod n) :
    covariance w x y = transferKernel char w x y := by
  simp only [covariance, transferKernel]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : char k x * conj (char k y) = char k (x - y) := by
    rw [conj_char]
    simp only [char]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h]

/-- **Plancherel form of the two-point OS form**: the quadratic form of a translation-invariant
covariance is the weighted Plancherel sum over the Fourier transform of the field. -/
theorem covarianceForm_eq_dft (w : ZMod n → ℝ) (F : ZMod n → ℂ) :
    (∑ x : ZMod n, ∑ y : ZMod n, F x * covariance w x y * conj (F y)) =
      ∑ k : ZMod n, (w k : ℂ) * (Complex.normSq (ZMod.dft F k) : ℂ) := by
  have hdft : ∀ k : ZMod n, (∑ x : ZMod n, F x * char k x) = ZMod.dft F k := by
    intro k
    rw [ZMod.dft_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_eq_mul]
    simp only [char]
    ring
  calc
    ∑ x : ZMod n, ∑ y : ZMod n, F x * covariance w x y * conj (F y)
        = ∑ x ∈ (Finset.univ : Finset (ZMod n)), ∑ y ∈ (Finset.univ : Finset (ZMod n)),
            F x * transferKernel char w x y * conj (F y) := by
          simp only [covariance_eq_transferKernel]
    _ = ∑ k : ZMod n, (w k : ℂ) *
          (Complex.normSq (∑ x ∈ (Finset.univ : Finset (ZMod n)), F x * char k x) : ℂ) :=
          transferForm_eq char w Finset.univ F
    _ = ∑ k : ZMod n, (w k : ℂ) * (Complex.normSq (ZMod.dft F k) : ℂ) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hdft]

/-- The Plancherel form is nonnegative for a nonnegative momentum symbol. -/
theorem covarianceForm_nonneg (w : ZMod n → ℝ) (hw : ∀ k, 0 ≤ w k) (F : ZMod n → ℂ) :
    0 ≤ ∑ k : ZMod n, w k * Complex.normSq (ZMod.dft F k) :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (Complex.normSq_nonneg _)

/-! ## 2b. The Källén–Lehmann factorization of the free lattice propagator

The transfer kernel of Section 2 is not an assumption for the free field: the lattice
propagator has a positive spectral representation, and on the future half-space it factorises
across the reflection plane.  Below, the spectral weight `w a`, the decay `ρ a` (on the lattice
`ρ a = e^{-ω_a}`) and the spatial momentum `mom a` are the Källén–Lehmann data; the reflected
propagator is *proved* to be `transferKernel (freeMode mom ρ) w`. -/

section KallenLehmann

variable {ι : Type*} [Fintype ι]

/-- The free lattice propagator in Källén–Lehmann form, on the time line `ℤ × ZMod n`. -/
def freePropagator (mom : ι → ZMod n) (w ρ : ι → ℝ) (p q : ℤ × ZMod n) : ℂ :=
  ∑ a : ι, (w a : ℂ) * (ρ a : ℂ) ^ (p.1 - q.1).natAbs * char (mom a) (p.2 - q.2)

/-- The transfer mode of spectral component `a`: the decay in reflected time times the spatial
character. -/
def freeMode (mom : ι → ZMod n) (ρ : ι → ℝ) (a : ι) (p : ℤ × ZMod n) : ℂ :=
  (ρ a : ℂ) ^ p.1.toNat * char (mom a) p.2

/-- Time reflection on the time line. -/
def timeReflect (p : ℤ × ZMod n) : ℤ × ZMod n := (-p.1, p.2)

/-- **Källén–Lehmann factorization.**  On the future half-space the reflected free propagator is
the transfer kernel of its spectral modes. -/
theorem freePropagator_reflect_eq_transfer (mom : ι → ZMod n) (w ρ : ι → ℝ)
    {p q : ℤ × ZMod n} (hp : 0 ≤ p.1) (hq : 0 ≤ q.1) :
    freePropagator mom w ρ (timeReflect p) q = transferKernel (freeMode mom ρ) w p q := by
  simp only [freePropagator, timeReflect, transferKernel, freeMode]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hexp : ((-p.1 - q.1).natAbs) = p.1.toNat + q.1.toNat := by
    have h1 : -p.1 - q.1 = -(p.1 + q.1) := by ring
    rw [h1, Int.natAbs_neg]
    omega
  rw [hexp, pow_add]
  have hch : char (mom a) p.2 * conj (char (mom a) q.2) = char (mom a) (p.2 - q.2) := by
    rw [conj_char]
    simp only [char]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [← hch]
  simp only [map_mul, map_pow, Complex.conj_ofReal]
  ring

/-- The future half-space of the time window `1 ≤ t ≤ T`. -/
def timeWindow (T : ℕ) : Finset (ℤ × ZMod n) :=
  Finset.Icc (1 : ℤ) (T : ℤ) ×ˢ Finset.univ

theorem timeWindow_pos {T : ℕ} {p : ℤ × ZMod n} (hp : p ∈ timeWindow T) : 0 ≤ p.1 := by
  have h1 : p.1 ∈ Finset.Icc (1 : ℤ) (T : ℤ) := (Finset.mem_product.mp hp).1
  have h2 := (Finset.mem_Icc.mp h1).1
  omega

/-- **The OS form of the free propagator is a sum of modulus squares.**  The reflected
propagator on the half-space is the Källén–Lehmann transfer kernel, and the OS form of that
kernel is `∑ a, w a * ‖∑ p, F p * u a p‖²`. -/
theorem freeOSForm_eq_momentum (mom : ι → ZMod n) (w ρ : ι → ℝ) (T : ℕ)
    (F : ℤ × ZMod n → ℂ) :
    (∑ p ∈ timeWindow T, ∑ q ∈ timeWindow T,
        F p * freePropagator mom w ρ (timeReflect p) q * conj (F q)) =
      ∑ a : ι, (w a : ℂ) *
        (Complex.normSq (∑ p ∈ timeWindow T, F p * freeMode mom ρ a p) : ℂ) := by
  calc
    ∑ p ∈ timeWindow T, ∑ q ∈ timeWindow T,
        F p * freePropagator mom w ρ (timeReflect p) q * conj (F q)
        = ∑ p ∈ timeWindow T, ∑ q ∈ timeWindow T,
            F p * transferKernel (freeMode mom ρ) w p q * conj (F q) := by
          refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
          rw [freePropagator_reflect_eq_transfer mom w ρ (timeWindow_pos hp) (timeWindow_pos hq)]
    _ = ∑ a : ι, (w a : ℂ) *
          (Complex.normSq (∑ p ∈ timeWindow T, F p * freeMode mom ρ a p) : ℂ) :=
          transferForm_eq (freeMode mom ρ) w (timeWindow T) F

/-- **Free-field reflection positivity in momentum space**, with the transfer kernel derived
from the propagator rather than supplied. -/
theorem free_reflection_positive (mom : ι → ZMod n) (w ρ : ι → ℝ)
    (hw : ∀ a, 0 ≤ w a) (T : ℕ) (F : ℤ × ZMod n → ℂ) :
    0 ≤ ∑ a : ι, w a *
      Complex.normSq (∑ p ∈ timeWindow T, F p * freeMode mom ρ a p) :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (Complex.normSq_nonneg _)

/-- The single-mass (explicit massive) free propagator: one spectral weight. -/
theorem freePropagator_single (mom : Unit → ZMod n) (w ρ : ℝ) (p q : ℤ × ZMod n) :
    freePropagator mom (fun _ => w) (fun _ => ρ) p q
      = (w : ℂ) * (ρ : ℂ) ^ (p.1 - q.1).natAbs * char (mom ()) (p.2 - q.2) := by
  simp [freePropagator]

/-- **Rank-one factorization of the explicit massive propagator**: on the future half-space
`G(θp, q) = w * u p * conj (u q)` with `u p = ρ ^ p.1 * χ(p.2)`. -/
theorem freePropagator_single_reflect (mom : Unit → ZMod n) (w ρ : ℝ)
    {p q : ℤ × ZMod n} (hp : 0 ≤ p.1) (hq : 0 ≤ q.1) :
    freePropagator mom (fun _ => w) (fun _ => ρ) (timeReflect p) q
      = (w : ℂ) * (freeMode mom (fun _ => ρ) () p *
          conj (freeMode mom (fun _ => ρ) () q)) := by
  rw [freePropagator_reflect_eq_transfer mom (fun _ => w) (fun _ => ρ) hp hq]
  simp [transferKernel]

end KallenLehmann

end MomentumOS

/-! ## 3. The momentum/lattice overlap and the exact Hamiltonian

The plane waves normalised by `√n` form a unitary overlap matrix `overlap k x` between the
momentum lattice and the 4D Euclidean lattice.  The exact Hamiltonian is the diagonal momentum
operator transported through it, `H x y = ∑ k, ω k * overlap k x * conj (overlap k y)`;
`exactHamiltonian_eigenvector` says the transport is exact — `overlap k ·` is an eigenvector with
eigenvalue `ω k`, with no truncation anywhere in the definition. -/

/-- `√n` as a complex number. -/
def sqrtN (n : ℕ) : ℂ := ((Real.sqrt n : ℝ) : ℂ)

theorem sqrtN_mul_conj (n : ℕ) : sqrtN n * conj (sqrtN n) = (n : ℂ) := by
  simp only [sqrtN, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg n)]
  push_cast
  ring

theorem sqrtN_ne_zero (n : ℕ) [NeZero n] : sqrtN n ≠ 0 := by
  simp only [sqrtN]
  exact_mod_cast (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (NeZero.pos n)))

/-- The overlap between the momentum mode `k` and the lattice site `x`. -/
def overlap (k x : ZMod n) : ℂ := (sqrtN n)⁻¹ * char k x

/-- The overlap matrix is **row-unitary**: momentum modes are orthonormal on the lattice. -/
theorem overlap_orthonormal (k l : ZMod n) :
    ∑ x : ZMod n, overlap k x * conj (overlap l x) = if k = l then 1 else 0 := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hx : ∀ x : ZMod n, overlap k x * conj (overlap l x) =
      (sqrtN n * conj (sqrtN n))⁻¹ * (char k x * conj (char l x)) := by
    intro x
    simp only [overlap, map_mul, Complex.conj_inv]
    rw [mul_inv_rev]
    ring
  calc
    ∑ x : ZMod n, overlap k x * conj (overlap l x)
        = ∑ x : ZMod n,
            (sqrtN n * conj (sqrtN n))⁻¹ * (char k x * conj (char l x)) :=
          Finset.sum_congr rfl fun x _ => hx x
    _ = (sqrtN n * conj (sqrtN n))⁻¹ * ∑ x : ZMod n, char k x * conj (char l x) := by
          rw [Finset.mul_sum]
    _ = (sqrtN n * conj (sqrtN n))⁻¹ * (if k = l then (n : ℂ) else 0) := by
          rw [sum_char_mul_conj]
    _ = if k = l then 1 else 0 := by
          rw [sqrtN_mul_conj]
          split_ifs <;> simp [hn]

/-- The overlap is symmetric in its two arguments. -/
theorem overlap_comm (a b : ZMod n) : overlap a b = overlap b a := by
  simp only [overlap, char, mul_comm]

/-- The overlap matrix is **column-unitary** as well (the matrix is square). -/
theorem overlap_orthonormal_pos (x y : ZMod n) :
    ∑ k : ZMod n, conj (overlap k x) * overlap k y = if x = y then 1 else 0 := by
  have hc : conj (∑ k : ZMod n, overlap x k * conj (overlap y k)) =
      ∑ k : ZMod n, conj (overlap k x) * overlap k y := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_conj, overlap_comm x k, overlap_comm y k]
  rw [← hc, overlap_orthonormal]
  split_ifs <;> simp

/-- Orthogonality with the summed index first. -/
theorem sum_conj_overlap (l k : ZMod n) :
    ∑ y : ZMod n, conj (overlap l y) * overlap k y = if l = k then 1 else 0 := by
  rw [show (∑ y : ZMod n, conj (overlap l y) * overlap k y)
      = ∑ y : ZMod n, conj (overlap y l) * overlap y k from by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [overlap_comm l y, overlap_comm k y]]
  exact overlap_orthonormal_pos l k

/-- **The exact Hamiltonian in the lattice basis**: the momentum-diagonal operator
`diag (ω)` transported through the overlap.  Nothing is truncated in this definition. -/
def exactHamiltonian (ω : ZMod n → ℝ) (x y : ZMod n) : ℂ :=
  ∑ k : ZMod n, (ω k : ℂ) * overlap k x * conj (overlap k y)

/-- The lattice form of the exact Hamiltonian is Hermitian. -/
theorem exactHamiltonian_hermitian (ω : ZMod n → ℝ) (x y : ZMod n) :
    conj (exactHamiltonian ω y x) = exactHamiltonian ω x y := by
  simp only [exactHamiltonian, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The transport is exact**: `overlap k ·` is an eigenvector of the lattice Hamiltonian
with eigenvalue `ω k`. -/
theorem exactHamiltonian_eigenvector (ω : ZMod n → ℝ) (k x : ZMod n) :
    ∑ y : ZMod n, exactHamiltonian ω x y * overlap k y = (ω k : ℂ) * overlap k x := by
  have h : ∀ y : ZMod n, exactHamiltonian ω x y * overlap k y =
      ∑ l : ZMod n,
        ((ω l : ℂ) * overlap l x) * (conj (overlap l y) * overlap k y) := by
    intro y
    rw [exactHamiltonian, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc
    ∑ y : ZMod n, exactHamiltonian ω x y * overlap k y
        = ∑ y : ZMod n, ∑ l : ZMod n,
            ((ω l : ℂ) * overlap l x) * (conj (overlap l y) * overlap k y) :=
          Finset.sum_congr rfl fun y _ => h y
    _ = ∑ l : ZMod n,
          ((ω l : ℂ) * overlap l x) * ∑ y : ZMod n,
            (conj (overlap l y) * overlap k y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ l : ZMod n, ((ω l : ℂ) * overlap l x) * (if l = k then 1 else 0) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sum_conj_overlap]
    _ = (ω k : ℂ) * overlap k x := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro l _ hlk
            rw [if_neg hlk]
            ring
          · intro hk
            simp at hk

/-! ## 3b. Momentum cells and their overlap with the lattice

Momentum space is itself a lattice.  Replacing its plane waves by any orthonormal family of
wave packets — cells, wavelets, Hermite functions — gives another orthonormal basis of the same
space.  The overlap of such a cell with a site of the 4D Euclidean lattice is the matrix element
`cellLatticeOverlap`; unitarity of that matrix is the statement that the translation between the
two bases is lossless. -/

section Cells

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A family of orthonormal momentum-space wave packets. -/
def IsOrthonormalCells (φ : ι → ZMod n → ℂ) : Prop :=
  ∀ i j : ι, ∑ k : ZMod n, conj (φ i k) * φ j k = if i = j then 1 else 0

/-- The inner product of the momentum cell `i` with the lattice site `x`. -/
def cellLatticeOverlap (φ : ι → ZMod n → ℂ) (i : ι) (x : ZMod n) : ℂ :=
  ∑ k : ZMod n, conj (φ i k) * overlap k x

omit [Fintype ι] in
/-- **The cell/lattice overlap is unitary.**  Orthonormal momentum cells have orthonormal
lattice profiles, so the two bases are related by a change of basis rather than by a lossy
approximation. -/
theorem cellLatticeOverlap_unitary (φ : ι → ZMod n → ℂ) (hφ : IsOrthonormalCells φ)
    (i j : ι) :
    ∑ x : ZMod n, cellLatticeOverlap φ i x * conj (cellLatticeOverlap φ j x) =
      if i = j then 1 else 0 := by
  have hx : ∀ x : ZMod n,
      cellLatticeOverlap φ i x * conj (cellLatticeOverlap φ j x) =
        ∑ k : ZMod n, ∑ l : ZMod n,
          (conj (φ i k) * φ j l) * (overlap k x * conj (overlap l x)) := by
    intro x
    rw [cellLatticeOverlap, cellLatticeOverlap, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_conj]
    ring
  calc
    ∑ x : ZMod n, cellLatticeOverlap φ i x * conj (cellLatticeOverlap φ j x)
        = ∑ x : ZMod n, ∑ k : ZMod n, ∑ l : ZMod n,
            (conj (φ i k) * φ j l) * (overlap k x * conj (overlap l x)) :=
          Finset.sum_congr rfl fun x _ => hx x
    _ = ∑ k : ZMod n, ∑ x : ZMod n, ∑ l : ZMod n,
            (conj (φ i k) * φ j l) * (overlap k x * conj (overlap l x)) :=
          Finset.sum_comm
    _ = ∑ k : ZMod n, ∑ l : ZMod n, ∑ x : ZMod n,
            (conj (φ i k) * φ j l) * (overlap k x * conj (overlap l x)) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : ZMod n, ∑ l : ZMod n,
          (conj (φ i k) * φ j l) * ∑ x : ZMod n,
            (overlap k x * conj (overlap l x)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ k : ZMod n, ∑ l : ZMod n,
          (conj (φ i k) * φ j l) * (if k = l then 1 else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [overlap_orthonormal]
    _ = ∑ k : ZMod n, conj (φ i k) * φ j k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_eq_single k]
          · simp
          · intro l _ hlk
            rw [if_neg (Ne.symm hlk)]
            ring
          · intro hk
            simp at hk
    _ = if i = j then 1 else 0 := hφ i j

/-- The exact Hamiltonian in the cell basis: the same momentum-diagonal operator, read
through the cell rather than the plane-wave overlap. -/
def cellHamiltonian (φ : ι → ZMod n → ℂ) (ω : ZMod n → ℝ) (i j : ι) : ℂ :=
  ∑ k : ZMod n, (ω k : ℂ) * conj (φ i k) * φ j k

end Cells

/-! ## 4. The lattice compression converges to the exact Hamiltonian -/

/-- **Compression convergence.**  If `P N` are contractions converging strongly to the
identity — a refining spatial lattice, or a sequence of momentum cutoffs — then the compressed
Hamiltonian `P N ∘ H ∘ P N` converges strongly to `H`.  The exact `H` is defined with no
truncation (Section 3); the lattice approximation is the compression, and this is the limit it
computes. -/
theorem compressed_hamiltonian_tendsto {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (H : E →L[𝕜] E) (P : ℕ → E →L[𝕜] E)
    (hP : ∀ ψ : E, Tendsto (fun N => P N ψ) atTop (𝓝 ψ))
    (hPc : ∀ N, ‖P N‖ ≤ 1) :
    ∀ ψ : E, Tendsto (fun N => P N (H (P N ψ))) atTop (𝓝 (H ψ)) := by
  intro ψ
  have hzero : Tendsto (fun N => P N (H (P N ψ - ψ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ N, ‖P N (H (P N ψ - ψ))‖ ≤ ‖H‖ * ‖P N ψ - ψ‖ := by
      intro N
      calc ‖P N (H (P N ψ - ψ))‖ ≤ ‖P N‖ * ‖H (P N ψ - ψ)‖ := (P N).le_opNorm _
        _ ≤ 1 * (‖H‖ * ‖P N ψ - ψ‖) :=
              mul_le_mul (hPc N) (H.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = ‖H‖ * ‖P N ψ - ψ‖ := one_mul _
    refine squeeze_zero (fun N => norm_nonneg _) hb ?_
    have hdiff : Tendsto (fun N => P N ψ - ψ) atTop (𝓝 0) := by
      have hsub := (hP ψ).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ) atTop (𝓝 ψ))
      simpa using hsub
    simpa using hdiff.norm.const_mul ‖H‖
  have hsecond : Tendsto (fun N => P N (H ψ) - H ψ) atTop (𝓝 0) := by
    have hsub := (hP (H ψ)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => H ψ) atTop (𝓝 (H ψ)))
    simpa using hsub
  have hsum : Tendsto (fun N => P N (H (P N ψ - ψ)) + (P N (H ψ) - H ψ)) atTop (𝓝 0) := by
    simpa using hzero.add hsecond
  have hEq : (fun N => P N (H (P N ψ))) =
      fun N => P N (H (P N ψ - ψ)) + (P N (H ψ) - H ψ) + H ψ := by
    funext N
    calc P N (H (P N ψ))
        = P N (H ((P N ψ - ψ) + ψ)) := by rw [sub_add_cancel]
      _ = P N (H (P N ψ - ψ) + H ψ) := by rw [map_add]
      _ = P N (H (P N ψ - ψ)) + P N (H ψ) := by rw [map_add]
      _ = P N (H (P N ψ - ψ)) + (P N (H ψ) - H ψ) + H ψ := by abel
  rw [hEq]
  simpa using hsum.add_const (H ψ)

/-! ## 5. From the bounded lattice Hamiltonian to the unbounded one (SIRK / Trotter–Kato)

The convergence theorem above is for a bounded exact Hamiltonian.  The SIRK chapters supply
the unbounded half: `ChapterSirkTrotterKato` proves that strong resolvent convergence of
self-adjoint operators transfers to their unitary groups (Trotter–Kato), and
`ChapterSirkTrotterKatoGalerkin` identifies a bounded self-adjoint operator with the unbounded
self-adjoint operator `ofBounded A` on the full domain.  Composing the two with
`compressed_hamiltonian_tendsto` gives the limit statement: the bounded lattice Hamiltonians'
flows converge to the flow of the unbounded exact Hamiltonian.  For a genuinely unbounded
generator `T`, the same transfer holds from resolvent convergence — that hypothesis is exactly
`StrongResolventConvergence`, the interface the SIRK per-system theorems target. -/

section SirkBridge

open BookProof.ChapterSirkTrotterKato
open scoped InnerProductSpace

variable {Hil : Type*} [NormedAddCommGroup Hil] [InnerProductSpace ℂ Hil] [CompleteSpace Hil]

/-- A compression of a self-adjoint operator by a self-adjoint projection is self-adjoint. -/
theorem isSelfAdjoint_compression (A P : Hil →L[ℂ] Hil) (hA : IsSelfAdjoint A)
    (hP : IsSelfAdjoint P) : IsSelfAdjoint (P ∘L A ∘L P) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  have hA' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hP' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP
  intro x y
  change ⟪P (A (P x)), y⟫_ℂ = ⟪x, P (A (P y))⟫_ℂ
  calc ⟪P (A (P x)), y⟫_ℂ = ⟪A (P x), P y⟫_ℂ := hP' _ _
    _ = ⟪P x, A (P y)⟫_ℂ := hA' _ _
    _ = ⟪x, P (A (P y))⟫_ℂ := hP' _ _

/-- **The SIRK resolvent hypothesis, closed for the compressed free Hamiltonian.**  Strong
operator convergence of the compressions gives strong resolvent convergence to the exact
operator — the hypothesis Trotter–Kato consumes, with no further analytic input. -/
theorem compressed_strongResolventConvergence (A : Hil →L[ℂ] Hil) (hA : IsSelfAdjoint A)
    (P : ℕ → Hil →L[ℂ] Hil) (hPs : ∀ N, IsSelfAdjoint (P N))
    (hPc : ∀ N, ‖P N‖ ≤ 1) (hP : ∀ u : Hil, Tendsto (fun N => P N u) atTop (𝓝 u)) :
    StrongResolventConvergence (ofBounded A hA)
      (fun N => ofBounded (P N ∘L A ∘L P N)
        (isSelfAdjoint_compression A (P N) hA (hPs N))) :=
  strongResolventConvergence_ofBounded
    (fun N => isSelfAdjoint_compression A (P N) hA (hPs N)) hA
    (fun u => compressed_hamiltonian_tendsto A P hP hPc u)

/-- **The flows of the lattice compressions converge to the flow of the exact Hamiltonian**,
read as the unbounded self-adjoint operator `ofBounded A` (SIRK/Trotter–Kato). -/
theorem compressed_flow_tendsto (A : Hil →L[ℂ] Hil) (hA : IsSelfAdjoint A)
    (P : ℕ → Hil →L[ℂ] Hil) (hPs : ∀ N, IsSelfAdjoint (P N))
    (hPc : ∀ N, ‖P N‖ ≤ 1) (hP : ∀ u : Hil, Tendsto (fun N => P N u) atTop (𝓝 u))
    (v : Hil) (t : ℝ) :
    Tendsto (fun N => (ofBounded (P N ∘L A ∘L P N)
        (isSelfAdjoint_compression A (P N) hA (hPs N))).stoneU t v) atTop
      (𝓝 ((ofBounded A hA).stoneU t v)) :=
  flow_tendsto_of_strong_tendsto (fun N => isSelfAdjoint_compression A (P N) hA (hPs N)) hA
    (fun u => compressed_hamiltonian_tendsto A P hP hPc u) v t

/-- The same convergence, uniformly on a bounded time interval. -/
theorem compressed_flow_transfer (A : Hil →L[ℂ] Hil) (hA : IsSelfAdjoint A)
    (P : ℕ → Hil →L[ℂ] Hil) (hPs : ∀ N, IsSelfAdjoint (P N))
    (hPc : ∀ N, ‖P N‖ ≤ 1) (hP : ∀ u : Hil, Tendsto (fun N => P N u) atTop (𝓝 u))
    (v : Hil) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    TendstoUniformlyOn
      (fun N t => (ofBounded (P N ∘L A ∘L P N)
        (isSelfAdjoint_compression A (P N) hA (hPs N))).stoneU t v)
      (fun t => (ofBounded A hA).stoneU t v) atTop (Set.Icc (-T₀) T₀) :=
  flow_transfer_of_strong_tendsto (fun N => isSelfAdjoint_compression A (P N) hA (hPs N)) hA
    (fun u => compressed_hamiltonian_tendsto A P hP hPc u) v hT₀

open BookProof.HermiteGalerkin in
/-- A Galerkin projection (the orthogonal projection onto a block subspace of a nested
refinement) is a contraction. -/
theorem galerkinProjection_norm_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    ‖(galerkinSpan b m).starProjection‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using (galerkinSpan b m).norm_starProjection_apply_le x

open BookProof.HermiteGalerkin in
/-- **The block/Galerkin refinement instantiates the convergence theorem.**  The projections
onto the nested spans of a Hilbert basis are a common-space refinement family converging
strongly to the identity (`galerkinProj_tendsto`), so the compressed Hamiltonian's resolvents
converge to the exact operator's — the SIRK hypothesis, closed for the Galerkin/block
refinement.  (`BalabanRG.blockAveragingOp` is the same construction at a *fixed* partition:
its target is `Sector (k+1)`, so it is not by itself a common-space refinement family.) -/
theorem galerkin_strongResolventConvergence {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) (b : HilbertBasis ℕ ℂ F) :
    StrongResolventConvergence (ofBounded A hA)
      (fun m => ofBounded (galerkinCompression A b m)
        (isSelfAdjoint_galerkinCompression hA b m)) := by
  simpa [galerkinCompression] using
    compressed_strongResolventConvergence A hA
      (fun m => (galerkinSpan b m).starProjection)
      (fun m => isSelfAdjoint_starProjection (galerkinSpan b m))
      (fun m => galerkinProjection_norm_le b m)
      (fun u => galerkinProj_tendsto b u)

open BookProof.HermiteGalerkin in
/-- The flows of the Galerkin/block compressions converge to the exact flow — the instantiated
form of `compressed_flow_tendsto`. -/
theorem galerkin_compressed_flow_tendsto {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) (b : HilbertBasis ℕ ℂ F)
    (v : F) (t : ℝ) :
    Tendsto (fun m => (ofBounded (galerkinCompression A b m)
        (isSelfAdjoint_galerkinCompression hA b m)).stoneU t v) atTop
      (𝓝 ((ofBounded A hA).stoneU t v)) :=
  compressed_flow_tendsto A hA
    (fun m => (galerkinSpan b m).starProjection)
    (fun m => isSelfAdjoint_starProjection (galerkinSpan b m))
    (fun m => galerkinProjection_norm_le b m)
    (fun u => galerkinProj_tendsto b u) v t

/-- **In the limit the bounded Hamiltonians *are* the unbounded one**: strong resolvent
convergence to a genuinely unbounded self-adjoint `T` gives convergence of the flows — the
SIRK/Trotter–Kato transfer. -/
theorem bounded_flow_tendsto_unbounded (A : ℕ → Hil →L[ℂ] Hil)
    (hA : ∀ N, IsSelfAdjoint (A N))
    (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint Hil)
    (hres : StrongResolventConvergence T (fun N => ofBounded (A N) (hA N)))
    (v : Hil) (t : ℝ) :
    Tendsto (fun N => (ofBounded (A N) (hA N)).stoneU t v) atTop (𝓝 (T.stoneU t v)) :=
  trotterKato_tendsto T (fun N => ofBounded (A N) (hA N)) hres v t

end SirkBridge

end

end BookProof.OSReconstruction
