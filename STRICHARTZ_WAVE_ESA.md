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
