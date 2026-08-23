# Essential self-adjointness of the wave operator — plan ↦ Lean map

This note records how the four-phase plan for a Strichartz-type theorem
(essential self-adjointness of the hyperbolic operator `□ + V` on `L²(ℝ^{1+n})`)
was carried out, and what is and is not proved.

Everything listed below is `sorry`-free and axiom-free (only `propext`,
`Classical.choice`, `Quot.sound`), and the whole `BookProof` library builds.

## Phase 1 — unbounded operators, von Neumann deficiency indices

The project already contained exactly the requested framework, so it was reused
rather than duplicated (`BookProof/ChapterFarisLavine.lean`):

| Plan | Lean |
| --- | --- |
| `LinearPMap` (operator on a domain) | a linear map `D →ₗ[ℂ] F` out of a `Submodule ℂ F` |
| `IsSymmetric` | `BookProof.FarisLavine.SymmetricOn` |
| deficiency space at `z` | `BookProof.FarisLavine.DeficiencyTrivialAt` |
| `IsEssentiallySelfAdjoint` | `BookProof.FarisLavine.EssentiallySelfAdjointOn` (both deficiency spaces vanish) |

## Phase 2 — the hyperbolic operator

`BookProof/ChapterStrichartzWave.lean`

| Plan | Lean |
| --- | --- |
| `SpaceTime n` | `BookProof.StrichartzWave.SpaceTime n = EuclideanSpace ℝ (Fin (1+n))`, index `0` = time |
| the domain (smooth test functions) | `schwartzDomain` — the Schwartz functions as a submodule of `L²`; an operator on Schwartz space is transported to `L²` by `opL2` |
| `□ = -∂_t² + Δ_x` (`+` constant potential) | `waveOp n κ`, the Minkowski case of the general `constCoeffOp c w κ = ∑ i, c i • ∂_{w i}² + κ` |
| the symbol | `symbolFn`, and `fourier_constCoeffOp_apply`: `𝓕 (P f) = symbol · 𝓕 f` |

The core is the Schwartz space rather than `C_c^∞`; this is the natural core here
because it is invariant under the Fourier transform, which the proof uses.

## Phase 3 — cut-offs and the energy step

* `exists_smooth_cutoff` — for every radius `R`, a smooth compactly supported
  cut-off equal to `1` on the ball of radius `R`, with values in `[0,1]`,
  vanishing outside the ball of radius `R+1`, and with bounded gradient.

For a *constant-coefficient* operator the light-cone/energy estimates can be
replaced by an exact computation on the Fourier side, and that is the route taken:
under Plancherel (`MeasureTheory.Lp.fourierTransformₗᵢ`) the operator becomes
multiplication by the **real** symbol, so

* symmetry (`constCoeffOp_symmetric`, `wave_symmetric`) is immediate, and
* the deficiency equation is killed by dividing test functions by `symbol - z̄`
  (`integral_conj_mul_symbol_sub_eq_zero`, `constCoeffOp_deficiencyTrivial`).

The potential is then added by a perturbation theorem instead of an energy estimate.

## Phase 4 — the theorems

| Statement | Lean |
| --- | --- |
| `□ + κ` (real constant `κ`) is essentially self-adjoint on the Schwartz core of `L²(ℝ^{1+n})` | `BookProof.StrichartzWave.wave_essentiallySelfAdjoint` |
| general constant-coefficient real-symbol operators (includes the Laplacian) | `BookProof.StrichartzWave.constCoeffOp_essentiallySelfAdjoint` |
| Kato–Rellich: a bounded symmetric perturbation preserves essential self-adjointness | `BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded` (`BookProof/ChapterKatoRellichDeficiency.lean`) |
| `□ + V` for a real, essentially bounded potential `V` | `BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint` (`BookProof/ChapterWaveBoundedPotential.lean`) |

The Kato–Rellich step is proved from scratch in the deficiency formulation by an
explicit Neumann series over *finite* sums of domain vectors, so no closure or
spectral theory for unbounded operators is required.

## What is not covered

The potential class of the plan — unbounded `V` with `‖∇V x‖ ≤ c‖x‖ + d` — is
**not** proved here.  The results above cover real potentials that are essentially
bounded (and, exactly, all constant-coefficient operators with real symbol).
Unbounded potentials require the genuine variable-coefficient energy argument,
for which the cut-off lemma of Phase 3 is the first ingredient.

## Wave 2026-08-18b — unbounded potentials and general real symbols

`BookProof/ChapterWaveUnboundedPotential.lean` (`sorry`-free / `axiom`-free,
registered in `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`)
takes up the "What is not covered" paragraph above and settles the part of it that
is unconditional.

| Statement | Lean |
| --- | --- |
| multiplication by a real potential of temperate growth (every polynomial: unbounded, no semiboundedness) is symmetric on the Schwartz core | `potentialOp_symmetric` |
| … and essentially self-adjoint | `potentialOp_essentiallySelfAdjoint` |
| the polynomial example `W x = ‖x‖^{2k}` (unbounded, bounded below) | `polynomialPotential_essentiallySelfAdjoint` |
| `□ + W` is a well-defined symmetric operator on the Schwartz core for every real `W` of temperate growth | `wave_add_potentialOp_symmetric` |
| the multiplication operator of this module *is* the bounded `mulL2` when the potential is essentially bounded | `opL2_potentialOp_eq_mulL2` |
| plan step (a)+(b): for every radius `R` a truncation `W_R` of temperate growth agreeing with `W` on the ball of radius `R`, with `□ + W_R` essentially self-adjoint | `wave_add_truncatedPotential_essentiallySelfAdjoint` |
| **every** real symbol of temperate growth gives an essentially self-adjoint Fourier multiplier (all constant-coefficient real-symbol operators, any order) | `multiplierOp_essentiallySelfAdjoint` |
| the constant-coefficient operators of Phase 2 are exactly the quadratic-symbol multipliers | `constCoeffOp_eq_multiplierOp` |
| example: the polyharmonic operator `(-Δ)^k` | `polyharmonic_multiplier_essentiallySelfAdjoint` |

So both "pure" cases are now closed with unbounded coefficients: an arbitrary real
polynomial **in the position variables** and an arbitrary real polynomial **in the
momentum variables** each give an essentially self-adjoint operator on the Schwartz
core.  What remains open is exactly the non-commuting mixture `□ + W`.

### Why step (c) is not a formality — a sign warning

With the convention used here, `□ = -∂_t² + Δ_x`.  A Fourier transform in the time
variable turns `□ + W` (for `W` a function of the space variables) into the fibre
operators `4π²τ² - (-Δ_x - W)`.  A potential **bounded below** therefore makes the
fibre Schrödinger operator `-Δ_x - W` unbounded **below**; for `W = x⁴` this is the
limit-circle operator `-d²/dx² - x⁴`, whose deficiency indices are `(2,2)` — a
classical fact from the literature, *not* formalized here — so the fibres, and
hence `□ + W`, are not essentially self-adjoint.  The hypothesis
under which the localization argument can close is the opposite sign: `W` bounded
above by a quadratic for `□ = -∂_t² + Δ_x`, i.e. `W` bounded below for the
opposite-signature convention `□ = ∂_t² - Δ_x` of the physics literature (the
Sears / Faris–Lavine class `V ≥ -c|x|²` in the elliptic normalization).  Nothing in
the module claims the unbounded mixed case, and the plan item should be read with
this sign correction.

## Wave 2026-08-18c — the non-commuting mixed case (elliptic prototype)

The previous wave closed both *commuting* halves and left "the non-commuting
mixture" open.  `BookProof/ChapterHarmonicOscillatorEsa.lean` (`sorry`-free /
`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`) settles the prototypical mixed case in the
elliptic (Sears / Faris–Lavine) normalization, where a joint eigenbasis is
explicitly available:

> the harmonic oscillator `H = -d²/dx² + x²/4`, whose potential is an unbounded
> polynomial and whose kinetic and potential terms do not commute, is essentially
> self-adjoint on the Hermite core of `L²(ℝ)`.

| Statement | Lean |
| --- | --- |
| eigenvalue equation for the complexified Hermite functions, `-ψ_n'' + (x²/4) ψ_n = (n + ½) ψ_n` | `hermiteC_oscillator` |
| the harmonic oscillator as the diagonal operator with symbol `n + ½` on the Hermite core | `harmonicOscOp` |
| **identification**: on the `n`-th basis vector it is the `L²` class of `x ↦ -ψ_n''(x) + (x²/4) ψ_n(x)`, with Mathlib's `deriv` | `harmonicOscOp_apply_eq_differential` |
| symmetry on the core | `harmonicOsc_symmetric` |
| **essential self-adjointness** | `harmonicOsc_essentiallySelfAdjoint` |
| the operator is genuinely unbounded | `harmonicOsc_not_bounded` |

The reused ingredients are `BookProof/ChapterHermiteFunctions.lean` (the Hermite
orthonormal basis of `L²(ℝ)` and the real eigen-equation `hermiteFun_oscillator`)
and `BookProof/ChapterStrichartzHermiteQG.lean` (a diagonal operator with an
arbitrary real symbol on the Hermite core is symmetric and has trivial deficiency
at every non-real point).  What is new is the identification of the diagonal
operator with the differential expression, which is what makes the statement a
theorem about `-d²/dx² + x²/4` rather than about a diagonal matrix.

This is the sign-correct case flagged above: it is the elliptic normalization,
where the potential is bounded below.  The hyperbolic mixture still needs the
fibrewise argument recorded in `CONSOLIDATED_PLAN.md` §9.5.

## Wave 2026-08-21 — the hyperbolic mixture with an indefinite quadratic potential

`BookProof/ChapterHyperbolicQuadraticEsa.lean` (`sorry`-free / `axiom`-free,
registered in `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`,
cited from `Book/DiffeomorphismsGravity.lean`) takes the "hyperbolic mixture" left
open by the wave above, in the case where the potential is quadratic and diagonal
in the coordinates — the case in which a joint eigenbasis exists.

| Statement | Lean |
| --- | --- |
| `−∂ᵢ² + xᵢ²/4` in the canonical pair `πᵢ = −i∂ᵢ`, `xᵢ·`, and its Hermite eigenvalue `αᵢ + ½` | `oscPoly`, `oscPoly_apply`, `oscPoly_hermiteMv` |
| `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` on the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)`, and its diagonal action | `quadOp`, `quadSymbol`, `quadOp_hermiteMvLp` |
| symmetry, and **essential self-adjointness for every real `c`** (no sign condition) | `quadOp_symmetric`, `quadOp_essentiallySelfAdjoint` |
| the operator is genuinely unbounded; the core is dense | `quadOp_not_bounded`, `polyGaussCore_dense_L2` |
| the pointwise identification with the differential expression (Mathlib's `deriv`, twice, along each coordinate line) | `deriv_pgFun_sec`, `deriv2_pgFun_sec`, `quadPoly_apply_eq_differential` |
| **the Minkowski case**: `□ + V`, `V(t,x) = (t² − ‖x‖²)/4`, with `□ = −∂_t² + Δ_x` | `minkowskiCoeff`, `wave_indefiniteQuadratic_essentiallySelfAdjoint`, `minkowski_apply_eq_differential` |
| a bounded real potential may be added (Kato–Rellich): *diagonal quadratic plus bounded* | `quadOp_add_boundedPotential_essentiallySelfAdjoint`, `quadOp_add_realBoundedPotential_essentiallySelfAdjoint` |
| reusable instruments: a diagonal operator with a real symbol on an orthonormal spanning family | `symmetricOn_of_diagonal`, `deficiencyTrivialAt_of_diagonal` |

This is the sign-correct hyperbolic case flagged in the sign warning above: the
potential `V(t,x) = (t² − ‖x‖²)/4` is bounded above by the quadratic
`(t² + ‖x‖²)/4`, is unbounded above and below, and does not commute with `□`.

### What is still not covered

A *general* potential bounded above by a quadratic.  The proof here is by the
joint eigenbasis, which exists only for the diagonal quadratic family
`∑ᵢ cᵢxᵢ²/4`; the fibrewise / direct-integral argument for a general
Faris–Lavine potential remains open.  Nothing is claimed for the opposite sign.

## Unbounded (relatively bounded) perturbations, 2026-08-21b

`BookProof/ChapterHermiteRelativeBound.lean` (namespace `BookProof.HermiteRelative`,
`sorry`-free / `axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`, cited from `Book/DiffeomorphismsGravity.lean`)
widens the potential class of the diagonal quadratic Hamiltonian beyond bounded
perturbations, in the **elliptic** case `cᵢ ≥ c₀ > 0`.

| Statement | Lean |
| --- | --- |
| the position `xᵢ`, momentum `πᵢ` and one-coordinate oscillator `πᵢ² + xᵢ²/4` as operators from the Hermite core into `L²` | `posL`, `momL`, `oscL` |
| both are symmetric on the core (Gaussian integration by parts, via `YangMillsHermite.PolySym`) | `posL_symmetric`, `momL_symmetric`, `symmetricOn_of_polySym` |
| the form identity `⟪u, (πᵢ² + xᵢ²/4)u⟫ = ‖πᵢu‖² + ‖xᵢu‖²/4` | `re_inner_oscL_eq` |
| the symbol comparison `c₀(αᵢ + ½) ≤ ∑ⱼ cⱼ(αⱼ + ½)`, as a comparison of quadratic forms | `re_inner_oscL_le_quadOp`, `re_inner_diagonal_le` |
| `xᵢ` and `πᵢ` are `H_c`-bounded with **arbitrarily small** relative bound | `norm_posL_le`, `norm_momL_le` |
| **`H_c + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint** (Kato–Rellich, relative form) | `foOp`, `foOp_symmetric`, `quadOp_add_firstOrder_essentiallySelfAdjoint` |
| the product Hermite basis is a **diagonalizing unitary**: `H_c` becomes multiplication by its symbol on `ℓ²` | `hermiteMvBasis_repr_quadOp` |
| the corollary: the **Stark-shifted oscillator** `−Δ + ‖x‖²/4 + ⟨b, x⟩`, the perturbation being multiplication by the unbounded function `x ↦ ⟨b, x⟩` | `foOp_linear_apply_eq_mul`, `harmonicOsc_add_linearPotential_essentiallySelfAdjoint` |

### What is still not covered

The strict positivity `cᵢ ≥ c₀ > 0` is used and is not removable by this
argument: in the hyperbolic case the symbol `∑ⱼ cⱼ(αⱼ + ½)` vanishes on an
infinite set of multi-indices, so `H_c` does not dominate the number operator and
no relative bound of this kind can hold.  The general Faris–Lavine potential
(bounded above by a quadratic) therefore remains open.

## Non-diagonal quadratic forms of arbitrary signature, 2026-08-21c

`BookProof/ChapterQuadraticRotationEsa.lean` (namespace
`BookProof.QuadraticRotation`, `sorry`-free / `axiom`-free, registered in
`BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`, cited from
`Book/DiffeomorphismsGravity.lean`) removes the *diagonality* restriction: the
quadratic form need no longer be diagonal in the coordinates.

| Statement | Lean |
| --- | --- |
| the orthogonal substitution `Xᵢ ↦ ∑ⱼ Oⱼᵢ Xⱼ` on polynomial coordinates, and its chain rule | `rotPoly`, `pderiv_rotPoly`, `rotPoly_surjective` |
| the canonical pair transforms contravariantly with the **same** matrix | `rotPoly_mulXPoly`, `rotPoly_momPoly` |
| `H_A = ∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)`, and the conjugation identity `H_c ↦ H_{O diag(c) Oᵀ}` | `quadPolyMat`, `rotConj`, `quadPolyMat_rotPoly`, `quadPolyMat_diagonal` |
| rotation invariance of the Gaussian weight: the substitution is unitary on the core | `rotIso`, `integral_comp_rotIso`, `gaussInt_rotPoly`, `inner_pgLp_rotPoly` |
| the rotated product Hermite functions: orthonormal, spanning the core, joint eigenvectors of `H_A` | `rotHermiteLp`, `orthonormal_rotHermiteLp`, `span_rotHermiteLp`, `quadOpMat_rotHermiteLp` |
| **symmetry and essential self-adjointness for every real symmetric `A`** (arbitrary signature) | `quadOpMat_symmetric`, `quadOpMat_essentiallySelfAdjoint` |
| the spectral theorem for real symmetric matrices supplies `O` and `c` | `exists_rotConj`, `exists_rotConj_eigenvalues` |
| the operator is genuinely unbounded whenever `A ≠ 0` | `quadOpMat_not_bounded` |
| the **rotated wave operator**: `□ + V` in rotated coordinates, neither part diagonal | `wave_rotated_essentiallySelfAdjoint` |

## The general inhomogeneous elliptic quadratic Hamiltonian, 2026-08-21d

`BookProof/ChapterQuadraticRotationPerturbed.lean` (namespace
`BookProof.QuadraticRotationPerturbed`, `sorry`-free / `axiom`-free, registered and
certified in the same three places) combines the previous two waves.

| Statement | Lean |
| --- | --- |
| the rotated Hermite functions as a **Hilbert basis**, and the rotation **unitary** of `L²(ℝᵈ)` | `rotHermiteBasis`, `rotU`, `rotU_hermiteMvLp` |
| on the core the unitary *is* the polynomial substitution, so it preserves the core | `rotU_pgLp`, `rotU_mem_core` |
| the first-order symbol transforms with the same matrix: `b, b' ↦ Ob, Ob'` | `rotVec`, `rotPoly_foPoly`, `rotVec_transpose` |
| the intertwining relation on the core | `rotU_intertwine` |
| positive definiteness gives a uniform positive lower bound on the eigenvalues | `exists_lower_bound_eigenvalues` |
| **`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is symmetric and essentially self-adjoint** for positive definite `A` | `quadOpMat_add_firstOrder_symmetric`, `quadOpMat_add_firstOrder_essentiallySelfAdjoint` |
| the corollary: an **anisotropic oscillator with cross terms in a constant field** | `anisotropicOsc_add_linearPotential_essentiallySelfAdjoint` |

### What is still not covered

Positive definiteness of `A` is used exactly once, and for the same reason as in
the wave above: in the indefinite case the symbol vanishes on infinitely many
multi-indices, so no relative bound for the first-order term holds.  The
unperturbed indefinite case is covered (`quadOpMat_essentiallySelfAdjoint`).  A
general Faris–Lavine potential is still not covered by any of these waves.

## Singular quadratic forms and explicit dynamics, 2026-08-21g

Two new modules, both `sorry`-free / `axiom`-free, registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean` and cited from
`Book/DiffeomorphismsGravity.lean`.

`BookProof/ChapterShiftedQuadraticDegenerate.lean` (namespace
`BookProof.ShiftedQuadraticDegenerate`) drops the invertibility hypothesis of the
matrix wave: completing the square needs only a *solution* of the classical
equilibrium equations, and for symmetric `A` that is exactly orthogonality to the
kernel.

| Statement | Lean |
| --- | --- |
| solvability of `A a = w` implies `w ⊥ ker A` | `equilibrium_orthogonal_to_kernel` |
| conversely, `w ⊥ ker A` implies solvability | `exists_equilibrium` |
| the criterion, both directions | `exists_equilibrium_iff` |
| **`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is symmetric and essentially self-adjoint** for *every* real symmetric `A` with a classical equilibrium | `shiftedHMatOp_symmetric_of_equilibrium`, `shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium` |
| the intrinsic form: `b, b' ⊥ ker A` gives a dense core, symmetry, ESA and a complete unitary flow | `exists_shiftedHMat_esa_of_kernel_orthogonal` |
| the concrete degenerate diagonal case (weights allowed to vanish) | `diagonal_degenerate_essentiallySelfAdjoint` |

`BookProof/ChapterStoneEigenflow.lean` (namespace `BookProof.StoneEigenflow`) makes
the dynamics explicit on the eigenbasis.

| Statement | Lean |
| --- | --- |
| a self-adjoint extension keeps the eigenvectors of the core operator | `isSelfAdjointExtension_eigenvector` |
| **any Stone flow acts on an eigenvector by the phase `e^{−iλt}`** | `stoneFlow_apply_eigenvector`, `stoneFlow_apply_core_eigenvector` |
| a symmetric ESA core operator with eigenvectors generates a diagonal flow | `exists_diagonal_stone_flow` |
| the quadratic family: `U t ψ_α = e^{−iE_αt} ψ_α`, `E_α = ∑ᵢ cᵢ(αᵢ + ½) + const` | `ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow`, `exists_shiftedH_diagonal_flow` |

### What is still not covered

Orthogonality of `b, b'` to `ker A` is necessary, not technical: in a kernel
direction the Hamiltonian degenerates to the first-order operator `bᵢxᵢ + b'ᵢπᵢ`,
which has no `L²` eigenvector, so no Hermite-type eigenbasis argument reaches it.
A general Faris–Lavine potential is still not covered by any of these waves.

## Fourier multipliers with a real symbol, 2026-08-21g

`BookProof/ChapterFourierMultiplierEsa.lean` (namespace `BookProof.FourierMultiplierEsa`)
turns the Plancherel proof of Phase 3 into a reusable instrument and applies it to
first-order operators.

| Statement | Lean |
| --- | --- |
| a Fourier multiplier with a real, smooth symbol is symmetric on the Schwartz core | `symmetricOn_of_real_symbol` |
| ... and has vanishing deficiency spaces, hence is **essentially self-adjoint** | `deficiencyTrivialAt_of_real_symbol`, `essentiallySelfAdjointOn_of_real_symbol` |
| the momentum operator `π_w = −i∂_w` is the multiplier with symbol `2π⟪ξ,w⟫` | `momentumOp`, `fourier_momentumOp_apply` |
| **`∑ᵢ cᵢ π_{wᵢ}` is essentially self-adjoint** on the Schwartz core | `firstOrderOp_essentiallySelfAdjoint`, `momentumOp_essentiallySelfAdjoint` |
| second order + first order + constant, `∑ᵢ cᵢ∂_{wᵢ}² + ∑ᵢ aᵢ(−i∂_{wᵢ}) + κ` | `mixedOp_essentiallySelfAdjoint` |

### What is still not covered

An operator mixing a *linear potential* with a momentum term, `⟨b,x⟩ + ⟨b',π⟩` with both
`b, b' ≠ 0`, is not a constant-coefficient Fourier multiplier, and has no `L²`
eigenvector, so neither this route nor the Hermite-eigenbasis route of the quadratic
family covers it.
