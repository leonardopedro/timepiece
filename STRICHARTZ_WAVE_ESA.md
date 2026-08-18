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
