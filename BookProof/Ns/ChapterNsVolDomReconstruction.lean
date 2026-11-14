/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The Fourier reconstruction of `det F − 1`, as far as it is algebraic

§63 was careful about where its proof stopped: `normForm_grad_sq` and `not_volDom_normForm` are
statements about the *normal form* `c(εt)²`, and the passage from the model's own penalty
`volPot kappa kv = (κ/2) Σ_q |(det F − 1)^(q)|²` to that normal form was measurement — the Fourier
reconstruction of `det F − 1` — not proof.

This file moves part of that boundary.  Two things are proved here and nothing more.

**1. The discrete grid is orthogonal.**  On an `N`-point grid with `ω = exp(2πi/N)`,

  `∑_{j<N} ω^{mj} = 0` unless `N ∣ m`, and `= N` when `m = 0`      (`dft_orthogonal`, `dft_zero`),

which is the algebraic content of "the dual grid is orthogonal": a single mode is invisible to every
other mode's average.  No measure theory is involved — the grid is finite, and this is the geometric
series plus `ω^N = 1`.

**2. A single-mode residual is exactly its coefficient.**  If the residual's spectrum is supported at
the zero mode — the definition, on a finite grid, of a *spatially constant* residual — then the penalty
is the constant's square:

  `volPot kappa kv = (κ/2) Λ²`      (`volPot_of_single_mode`),

and with `Λ = c·ε·t` on §63's shear family,

  `volPot kappa kv = (κ/2)(c·ε·t)²`      (`volPot_of_shear_constant`),

i.e. exactly the coefficient `c` of the normal form `normForm c` that §63 refutes domination for.  So
the *transfer of the constant* is a theorem.

**What is still not proved.**  The assembly that takes position-space data to that spectrum:
`volPot`'s sum over `waveSet` is asserted at the coefficient level, and the identity
`(1/N) Σ_j |R(a_j)|² = Σ_q |R̂_q|²` (unitarity of the discrete transform) is not formalized here.  The
hypothesis `hspec` below *is* that reconstruction, assumed rather than derived; what the lemmas do is
show that once it is available, the remaining algebra is exact and the constant transfers with no loss.
-/

import BookProof.Ns.ChapterNsLagrangianDetConvolution
import BookProof.Ns.ChapterNsVolDomExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace BookProof.NsVolDomReconstruction

open MvPolynomial
open BookProof.NsVolDomExpansion BookProof.NsLagrangianDet

noncomputable section

/-! ## 1. The discrete grid is orthogonal -/

/-- The `N`-th root of unity used by the grid. -/
def gridRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- **Discrete orthogonality.**  The grid average of a nonzero mode vanishes: multiplying by
`ω^{m·j}` and summing over the grid kills everything the grid cannot resolve, i.e. everything whose
mode number is not a multiple of `N`. -/
theorem dft_orthogonal (N : ℕ) (hN : 0 < N) (m : ℕ) (h : ¬ N ∣ m) :
    ∑ j ∈ Finset.range N, gridRoot N ^ (m * j) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hne : gridRoot N ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
  have hne' : Complex.exp (2 * Real.pi * Complex.I / N) ^ m ≠ 1 := hne
  simp only [gridRoot, pow_mul]
  rw [geom_sum_eq hne']
  have hpow : (Complex.exp (2 * Real.pi * Complex.I / N) ^ m) ^ N = 1 := by
    rw [← pow_mul, pow_mul', hζ.pow_eq_one, one_pow]
  rw [hpow]
  simp

/-- The zero mode is counted with full weight `N`: the grid is normalised so that a constant
survives its own average. -/
theorem dft_zero (N : ℕ) : ∑ _j ∈ Finset.range N, gridRoot N ^ (0 * _j) = (N : ℂ) := by
  simp

/-! ## 2. A single-mode residual is its coefficient -/

open Classical in
/-- **The reconstruction at a single mode.**  If the residual `det F − 1` has no nonzero Fourier
coefficient and its zero coefficient is the real constant `Λ`, then the penalty is `(κ/2)Λ²` — the
constant is carried through without distortion.  This is the step §63 called measurement; what is
assumed is the spectrum (`hspec`, `hz`), what is proved is that nothing else enters. -/
theorem volPot_of_single_mode {K : Type*} [Fintype K] (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) := by
  classical
  unfold volPot
  rw [Finset.sum_eq_single (0 : Fin 3 → ℝ)]
  · rw [hz]
    have hc : conjP (K := K) (MvPolynomial.C ((Λ : ℝ) : ℂ))
        = MvPolynomial.C ((Λ : ℝ) : ℂ) := by
      simp [conjP]
    rw [hc, MvPolynomial.smul_eq_C_mul]
    repeat rw [← map_mul]
    congr 1
    push_cast
    ring
  · intro q hq hq0
    rw [hspec q hq hq0]
    simp
  · intro hnot
    exact absurd h0 hnot

open Classical in
/-- **The constant transfers on the shear family.**  If the residual's spectrum is the single mode
`Λ = c·ε·t` — the shear amplitude times the tilt times `c` — then the model's penalty is
`(κ/2)(c·ε·t)²`, i.e. `(κ/2)` times the value of §63's normal form `normForm c` at `(t, ε)`.  So
the `c` that `not_volDom_normForm` refutes for every `c ≠ 0` is the *measured* constant, not a
re-scaling of the model. -/
theorem volPot_of_shear_constant {K : Type*} [Fintype K] (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C (((c * ε * t : ℝ) : ℂ))) :
    volPot kappa kv
      = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode kappa (c * ε * t) kv h0 hspec hz

/-- The same statement against §63's normal form: the penalty's value is `(κ/2)` times
`normForm c` evaluated at the shear amplitude and tilt. -/
theorem volPot_of_shear_constant_normForm {K : Type*} [Fintype K] (kappa c ε t : ℝ)
    (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C (((c * ε * t : ℝ) : ℂ))) :
    volPot kappa kv = MvPolynomial.C ((kappa / 2 : ℝ) : ℂ) *
      MvPolynomial.C (((c * ε * t) ^ 2 : ℝ) : ℂ) := by
  rw [volPot_of_shear_constant kappa c ε t kv h0 hspec hz, ← map_mul]
  congr 1
  push_cast
  ring

end

end BookProof.NsVolDomReconstruction
