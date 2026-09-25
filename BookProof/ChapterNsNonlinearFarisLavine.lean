import BookProof.ChapterNsKoopman
import BookProof.ChapterFarisLavineDenseCore

/-!
# The nonlinear Navier–Stokes Koopman generator and the Faris–Lavine criterion

The operator is the Koopman–von Neumann generator of `ChapterNsKoopman`,

```
H_NS = ½ Σ_m (π_m F_m + F_m π_m),      F_m(u) = −ν λ_m u_m + Σ_{j,k} b_{mjk} u_j u_k ,
```

with the **exact quadratic advection** `B(u,u)`: no linearization and no perturbative
splitting.  The coefficients `b_{mjk}` are the momentum-space (convolution) form of
`(u·∇)u` followed by the Leray projection.  The spatial derivative becomes the symbol `i k`, and
the product `u_j ∂_j u_m` becomes the triad convolution `Σ_{p+q=k} i (û_p · q) û_q`
(`NsAdvectionConvolution.fourier_advection_convolution`).  The only properties of the
coefficients used are the two structural identities recorded in `NsSystem`: Leray's energy
identity `Σ_m u_m B_m(u,u) = 0` and the Liouville identity `div_u B = 0`.

## The comparison operator

The Faris–Lavine criterion needs a positive `N` with `𝒟(N) ⊆ 𝒟(H)` and `±i[H,N] ≤ cN`.  The
Leray energy `E = 1 + ‖u‖²` has the right commutator, since `i[H_NS, E] = −2ν Σ λ_m u_m²` and the
advection drops out by Leray's identity (`NsKoopman.commForm_kvn_energy_bound`).  But `E` does not
dominate the first-order operator `H_NS`.  This module takes

```
N_NS := H_NS² + E = H_NS² + 1 + ‖u‖² .
```

It is positive, and its form is `⟪x, N x⟫ = ‖H x‖² + ⟪x, E x⟫ ≥ ‖x‖²`
(`nsSquareComparison_quadForm`).  It dominates `H_NS`: `‖H x‖ ≤ ‖N x‖ + ‖x‖`
(`nsSquareComparison_relBound`).  Its commutation relation with `H_NS` is exact:
`H_NS` commutes with `H_NS²`, so

```
⟪x, i[H_NS, N_NS] x⟫ = ⟪x, i[H_NS, E] x⟫ = ⟪x, (−2ν Σ λ_m u_m²) x⟫
|⟪x, i[H_NS, N_NS] x⟫| ≤ 2νΛ ⟪x, N_NS x⟫
```

(`nsSquareComparison_commForm`, `nsSquareComparison_commForm_bound`).  Here `Λ` bounds the
Stokes eigenvalues `λ_m = |k_m|²`.  All of this holds on the Gauss–polynomial core, for the full
nonlinear operator.

## The conclusion

`nsKoopman_esa_of_squareComparison_esa`: **if `N_NS` is essentially self-adjoint on the core,
then so is the nonlinear Navier–Stokes generator `H_NS`.**  The proof is the core form of
Faris–Lavine, `FarisLavine.essentiallySelfAdjointOn_of_square_comparison`.

## Honest boundary

* The one input that is **not** proved is the essential self-adjointness of `N_NS` itself
  (equivalently, since `N_NS ≥ 1`, density of `(N_NS + 1)` applied to the core).  It is carried
  as an explicit hypothesis.  This is a genuine reduction, not a proof of essential
  self-adjointness of `H_NS`.  The commutator part of Faris–Lavine is fully discharged, and what
  is left is the self-adjointness of the positive operator `N_NS`.
* Why no simpler `N` was used: a comparison operator for a first-order generator must be
  invariant under the classical flow up to a bounded exponential rate, in both time directions.
  For a polynomial `N` built from `u` and `π`, the quadratic advection makes the
  linearized flow stretch the momenta at a rate proportional to `|u|`, which is unbounded.
  So no polynomial in `u`, `π` of the harmonic-oscillator type satisfies `±i[H,N] ≤ cN`.  The
  invariant `H_NS` itself, plus the energy, is the algebraic choice that does.  This argument
  is informal and is not formalized here.
* The constant `2νΛ` depends on the largest Stokes eigenvalue kept.  With **all** Fourier modes
  (no truncation) the commutator `2ν Σ |k|² |û_k|²` is not bounded by any multiple of
  `1 + ‖u‖²`.  This reflects the fact that viscous Navier–Stokes is not well posed backward in
  time, so a unitary (two-sided) Koopman group cannot be expected in infinite dimensions.  The
  statements here are for every finite set of modes, with the exact nonlinearity on those modes.
-/

namespace BookProof.NsNonlinearFarisLavine

open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman

noncomputable section

variable {d : ℕ} (S : NsSystem d)

/-- The nonlinear Navier–Stokes generator as a map of the Gauss–polynomial core into itself. -/
def nsKoopmanCore : (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  (coreRepPoly d).op (kvnPoly S)

theorem nsKoopmanOp_eq_subtype_comp :
    nsKoopmanOp S = (polyGaussCore (d := d)).subtype ∘ₗ nsKoopmanCore S := rfl

/-- **The comparison operator** `N_NS = H_NS² + (1 + ‖u‖²)` on the Gauss–polynomial core. -/
def nsSquareComparison : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  nsKoopmanOp S ∘ₗ nsKoopmanCore S + nsEnergyOp (d := d)

theorem nsSquareComparison_symmetricOn :
    SymmetricOn (polyGaussCore (d := d)) (nsSquareComparison S) :=
  symmetricOn_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S)
    nsEnergyOp_symmetricOn

/-- `⟪x, N_NS x⟫ = ‖H_NS x‖² + ⟪x, (1 + ‖u‖²) x⟫`. -/
theorem nsSquareComparison_quadForm (x : polyGaussCore (d := d)) :
    quadForm (nsSquareComparison S) x
      = ‖nsKoopmanOp S x‖ ^ 2 + quadForm (nsEnergyOp (d := d)) x :=
  quadForm_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S) x

/-- **`N_NS ≥ 1`.** -/
theorem nsSquareComparison_quadForm_ge (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsSquareComparison S) x := by
  rw [nsSquareComparison_quadForm]
  have := nsEnergyOp_quadForm_ge x
  nlinarith [sq_nonneg ‖nsKoopmanOp S x‖]

theorem nsSquareComparison_quadForm_nonneg (x : polyGaussCore (d := d)) :
    0 ≤ quadForm (nsSquareComparison S) x :=
  le_trans (by positivity) (nsSquareComparison_quadForm_ge S x)

/-- **`N_NS` dominates the nonlinear generator**: `‖H_NS x‖ ≤ ‖N_NS x‖ + ‖x‖`. -/
theorem nsSquareComparison_relBound (x : polyGaussCore (d := d)) :
    ‖nsKoopmanOp S x‖ ≤ ‖nsSquareComparison S x‖ + ‖(x : L2d d)‖ :=
  norm_le_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S)
    nsEnergyOp_quadForm_nonneg x

/-- **The exact commutation relation**: `⟪x, i[H_NS, N_NS] x⟫` is the expectation of the viscous
energy flux `F·∇E = −2ν Σ_m λ_m u_m²`.  The square `H_NS²` commutes with `H_NS`, and by
Leray's identity the nonlinear advection contributes nothing. -/
theorem nsSquareComparison_commForm (x : polyGaussCore (d := d)) :
    commForm (nsKoopmanOp S) (nsSquareComparison S) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (fluxPoly S * (coreRepPoly d).equiv.symm x)).re := by
  rw [← commForm_kvn_energy S x]
  exact commForm_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S) x

/-- **The Faris–Lavine commutator inequality for `N_NS`**:
`|⟪x, i[H_NS, N_NS] x⟫| ≤ 2νΛ ⟪x, N_NS x⟫`, where `Λ ≥ λ_m` for every mode. -/
theorem nsSquareComparison_commForm_bound {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (x : polyGaussCore (d := d)) :
    |commForm (nsKoopmanOp S) (nsSquareComparison S) x|
      ≤ (2 * S.nu * L) * quadForm (nsSquareComparison S) x := by
  have hcf : commForm (nsKoopmanOp S) (nsSquareComparison S) x
      = commForm (nsKoopmanOp S) (nsEnergyOp (d := d)) x :=
    commForm_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S) x
  rw [hcf]
  refine le_trans (commForm_kvn_energy_bound S hL hL0 x) ?_
  have hc : 0 ≤ 2 * S.nu * L := mul_nonneg (by linarith [S.nu_nonneg]) hL0
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [nsSquareComparison_quadForm]
  nlinarith [sq_nonneg ‖nsKoopmanOp S x‖]

/-- **Faris–Lavine for the nonlinear Navier–Stokes generator.**  For every mainstream system
(exact quadratic advection, every finite set of modes), if the positive comparison operator
`N_NS = H_NS² + 1 + ‖u‖²` is essentially self-adjoint on the Gauss–polynomial core, then the
nonlinear Koopman generator `H_NS` is essentially self-adjoint there. -/
theorem nsKoopman_esa_of_squareComparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsSquareComparison S)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsKoopmanOp S) := by
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℝ, (∀ i, S.lam i ≤ L) ∧ 0 ≤ L :=
    ⟨∑ i, S.lam i, fun i => Finset.single_le_sum (fun j _ => S.lam_nonneg j)
      (Finset.mem_univ i), Finset.sum_nonneg fun j _ => S.lam_nonneg j⟩
  exact essentiallySelfAdjointOn_of_square_comparison polyGaussCore_dense (nsKoopmanCore S)
    (nsEnergyOp (d := d)) (2 * S.nu * L) (nsKoopmanOp_symmetricOn S) nsEnergyOp_symmetricOn
    (mul_nonneg (by linarith [S.nu_nonneg]) hL0) nsEnergyOp_quadForm_nonneg
    (commForm_kvn_energy_bound S hL hL0) hN

end

end BookProof.NsNonlinearFarisLavine
