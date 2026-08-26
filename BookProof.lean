import BookProof.ChapterA
import BookProof.ChapterA1
import BookProof.ChapterA3
import BookProof.ChapterA3b
import BookProof.ChapterA3c
import BookProof.ChapterA3d
import BookProof.ChapterA3e
import BookProof.ChapterA3f
import BookProof.ChapterA3g
import BookProof.ChapterA3h
import BookProof.ChapterA3i
import BookProof.ChapterA3j
import BookProof.ChapterA3k
import BookProof.ChapterA3l
import BookProof.ChapterA3m
import BookProof.ChapterA3n
import BookProof.ChapterA3o
import BookProof.ChapterA3p
import BookProof.ChapterA3q
import BookProof.ChapterA3r
import BookProof.ChapterA3s
import BookProof.ChapterA3t
import BookProof.ChapterA3u
import BookProof.ChapterA3v
import BookProof.ChapterA4
import BookProof.ChapterA4b
import BookProof.ChapterA4c
import BookProof.ChapterA4d
import BookProof.ChapterA5
import BookProof.ChapterA4e
import BookProof.ChapterA4f
import BookProof.ChapterA4g
import BookProof.ChapterB
import BookProof.ChapterB3
import BookProof.ChapterB3b
import BookProof.Complexification
import BookProof.ChapterA1b
import BookProof.ChapterA1Prop5
import BookProof.ChapterA1c
import BookProof.ChapterA1d
import BookProof.ChapterA1e
import BookProof.ChapterA1f
import BookProof.ChapterA1g
import BookProof.ChapterA1h
import BookProof.ChapterA2
import BookProof.ChapterA2b
import BookProof.ChapterA2c
import BookProof.ChapterA2d
import BookProof.ChapterA2e
import BookProof.ChapterC
import BookProof.ChapterD
import BookProof.ChapterE
import BookProof.ChapterG
import BookProof.ChapterG2
import BookProof.ChapterB7
import BookProof.ChapterU
import BookProof.ChapterF1
import BookProof.ChapterF2
import BookProof.ChapterA4h
import BookProof.ChapterA3w
import BookProof.ChapterA3x
import BookProof.ChapterBoseEinstein
import BookProof.ChapterThermalMaxEntropy
import BookProof.ChapterLinftyMultiplication
import BookProof.ChapterH1
import BookProof.ChapterH2
import BookProof.ChapterF3
import BookProof.ChapterF4
import BookProof.ChapterH3
import BookProof.ChapterF5
import BookProof.ChapterF6
import BookProof.ChapterH4
import BookProof.ChapterF7
import BookProof.ChapterB4
import BookProof.ChapterEntropy
import BookProof.ChapterE2
import BookProof.ChapterE3
import BookProof.ChapterE4
import BookProof.ChapterReconstruct
import BookProof.ChapterClassicalLimit
import BookProof.ChapterJointUnitary
import BookProof.ChapterHolomorphic
import BookProof.ChapterNavierStokes
import BookProof.ChapterNavierStokesFlow
import BookProof.ChapterNavierStokesCauchy
import BookProof.ChapterNavierStokesEsa
import BookProof.ChapterNavierStokesDeficiency
import BookProof.ChapterFarisLavine
import BookProof.ChapterKatoRellichDeficiency
import BookProof.ChapterKatoRellichRelative
import BookProof.ChapterStrichartzWave
import BookProof.ChapterWaveBoundedPotential
import BookProof.ChapterWaveUnboundedPotential
import BookProof.ChapterHarmonicOscillatorEsa
import BookProof.ChapterNavierStokesFullEsa
import BookProof.ChapterNavierStokesLagrangianEsa
import BookProof.ChapterNavierStokesLagrangianKatoRellich
import BookProof.ChapterNavierStokesFockSpace
import BookProof.ChapterNavierStokesFockEsa
import BookProof.ChapterNavierStokesFockContinuum
import BookProof.ChapterNavierStokesFockLagrangian
import BookProof.ChapterNavierStokesFockParcels
import BookProof.ChapterNavierStokesSecondQuant
import BookProof.ChapterNavierStokesFarisLavineLift
import BookProof.ChapterNavierStokesFockFarisLavine
import BookProof.ChapterNavierStokesIkebeKato
import BookProof.ChapterNavierStokesMomentumEsa
import BookProof.ChapterNavierStokesMomentumPerturbation
import BookProof.ChapterNavierStokesHermiteFarisLavine
import BookProof.ChapterNavierStokesBilinearEsa
import BookProof.ChapterNavierStokesAffineFiberEsa
import BookProof.ChapterNavierStokesAffineBlockEsa
-- The sign-flip unitary `x_n ↦ (−1)ⁿ x_n`: essential self-adjointness is a
-- unitary invariant, so the affine fiber and block Hamiltonians are essentially
-- self-adjoint for a fiber constant of *arbitrary* sign, not only `c ≥ 0`.
import BookProof.ChapterNavierStokesSignFlip
-- Hopping Hamiltonians with signed, non-monotone amplitudes, and the finite
-- family instrument built from them.
import BookProof.ChapterNavierStokesSignedShift
-- The three coupled velocity components at one fiber: `H = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)`
-- with `Vᵢ(u) = ∑ₖ A_{ik} uₖ + cᵢ` for an arbitrary real matrix `A` and vector `c`.
import BookProof.ChapterNavierStokesThreeComponent
-- The same fiber Hamiltonian written canonically: ladder operators on the three-mode
-- Hermite core, the canonical pairs `uᵢ = (aᵢ + aᵢ†)/√2`, `πᵢ = i(aᵢ† - aᵢ)/√2` with the
-- full CCR, and the identification `∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ) = velH A c`.
import BookProof.ChapterNavierStokesCanonicalVector
-- The product Hermite orthonormal basis of `L²(ℝᵈ)`: the normalized Gauss-polynomial
-- functions `ψ_α`, their orthonormality and completeness, and the ladder relations
-- `a†ψ_α = √(α_i+1)ψ_{α+e}`, `aψ_α = √α_i ψ_{α−e}` at the level of polynomials.
import BookProof.ChapterHermiteProductBasis
-- The differential realization of the same fiber Hamiltonian on `L²(du₁du₂du₃)`:
-- `πᵢ = −i ∂/∂uᵢ` as a genuine derivative, `uᵢ` as a genuine multiplication operator,
-- the unitary transport from the three-mode sequence space, and essential
-- self-adjointness of `∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` on the Hermite core of `L²(ℝ³)`.
import BookProof.ChapterNavierStokesDifferentialL2
-- Essential self-adjointness selects a unique self-adjoint operator: the closure
-- of the graph, its uniqueness, and the positivity-free Hashimoto/SIRK selection.
import BookProof.ChapterEsaClosure
-- The Hashimoto/SIRK shift-invert limit selects the Navier-Stokes generator.
import BookProof.ChapterNavierStokesHashimoto
import BookProof.ChapterNavierStokesHermiteCanonical
import BookProof.ChapterNavierStokesShiftHamiltonian
import BookProof.ChapterNavierStokesFockManyMode
import BookProof.ChapterNavierStokesFockCanonical
import BookProof.ChapterNavierStokesEulerian
import BookProof.ChapterNavierStokesGaugeY
import BookProof.ChapterNavierStokesGaugeY2
import BookProof.ChapterGaugeFixing
import BookProof.ChapterQuantumGravityDensitized
import BookProof.ChapterQuantumGravityHalfDensity
import BookProof.ChapterYangMillsFriedrichs
import BookProof.ChapterYangMillsFriedrichsLimit
import BookProof.ChapterHermiteGalerkinFriedrichs
import BookProof.ChapterHermiteFunctions
import BookProof.ChapterStrichartzHermiteQG
import BookProof.ChapterSpinStatistics
import BookProof.ChapterMajoranaFourier
import BookProof.ChapterMajoranaProp61
import BookProof.ChapterMajoranaProp74
import BookProof.ChapterMajoranaProp76
import BookProof.ChapterParity
import BookProof.ChapterCPTHamiltonian
import BookProof.ChapterSphericalBessel
import BookProof.ChapterNoLebesgue
import BookProof.ChapterNoUniformCountable
import BookProof.ChapterCountablePartition
import BookProof.ChapterBijectionProbability
import BookProof.ChapterMeasurementLLN
import BookProof.ChapterGravityProjector
import BookProof.ChapterGravityMetric
import BookProof.ChapterGravityTimeProj
import BookProof.ChapterGravityInvMetric
import BookProof.ChapterGravitySplit
import BookProof.ChapterGravityGenInverse
import BookProof.ChapterGravityIrrep
import BookProof.ChapterLorentzTranslation
import BookProof.ChapterSuperBracket
import BookProof.ChapterLorentzGroup
import BookProof.ChapterLorentzOrthochronous
import BookProof.ChapterLorentzDecomp
import BookProof.ChapterDoubleSlit
import BookProof.ChapterPauliLorentz
import BookProof.ChapterPauliSU2
import BookProof.ChapterPinOmega
import BookProof.ChapterPinDoubleCover
import BookProof.ChapterLorentzRealRep
import BookProof.ChapterLorentzRealRepSum
import BookProof.ChapterLorentzRealRepFull
import BookProof.ChapterLorentzRealRepDirect
import BookProof.ChapterLittleGroup
import BookProof.ChapterIPin
import BookProof.ChapterSE2
import BookProof.ChapterLocalization
import BookProof.ChapterCPTParity
import BookProof.ChapterCPTPT
import BookProof.ChapterParityQL
import BookProof.ChapterParityHiggs
import BookProof.ChapterParitySU2
import BookProof.ChapterParityCustodial
import BookProof.ChapterParityChirality
import BookProof.ChapterParityMajoranaQuant
import BookProof.ChapterParityHypercharge
import BookProof.ChapterParityZ4
import BookProof.ChapterBell
import BookProof.ChapterTsirelson
import BookProof.ChapterInverseTransform
import BookProof.ChapterDeterministic
import BookProof.ChapterTimeTranslation
import BookProof.ChapterIrreversible
import BookProof.ChapterIrreversibleDynamics
import BookProof.ChapterTrajectory
import BookProof.ChapterWeakValue
import BookProof.ChapterContinuityUnitary
import BookProof.ChapterContinuityUnitaryInfinite
import BookProof.ChapterBornMeasure
import BookProof.ChapterUnboundedPosition
import BookProof.ChapterUnitaryTransport
import BookProof.ChapterCausality
import BookProof.ChapterMassGap
import BookProof.ChapterLocalOperators
import BookProof.ChapterQuadraticOrdering
import BookProof.ChapterGhostField
import BookProof.ChapterYangMillsSU3
import BookProof.ChapterYangMillsBianchi
import BookProof.ChapterYangMillsFieldStrength
import BookProof.ChapterMajoranaClifford
import BookProof.ChapterBRSTNilpotent
import BookProof.ChapterWeylHamiltonian
import BookProof.ChapterFreeEMField
import BookProof.ChapterBosonicCCR
import BookProof.ChapterElectroweakFieldStrength
import BookProof.ChapterGleason2D
import BookProof.ChapterQuantizationWeyl
import BookProof.ChapterKernelBound
import BookProof.ChapterMarkovEntropy
import BookProof.ChapterConditional
import BookProof.ChapterBayesInference
import BookProof.ChapterConservative
import BookProof.ChapterSymmetryRep
import BookProof.ChapterGleasonPureMixed
import BookProof.ChapterCollapseDiagonal
import BookProof.ChapterDensitySpectral
import BookProof.ChapterEulerStochastic
import BookProof.ChapterEulerNState
import BookProof.ChapterEulerComplexQuat
import BookProof.ChapterEulerDensityMatrix
import BookProof.ChapterEulerGenericDensity
import BookProof.ChapterEulerCountableChain
import BookProof.ChapterSternGerlach
import BookProof.ChapterFreeFieldGaussian
import BookProof.ChapterFreeFieldSphere
import BookProof.ChapterFreeFieldSphereSupport
import BookProof.ChapterFreeFieldSphereFixpoint
import BookProof.ChapterBornPhaseFiber
import BookProof.ChapterFreeFieldBorn
import BookProof.ChapterFreeFieldBornSurj
import BookProof.ChapterFreeFieldBornCont
import BookProof.ChapterFreeFieldBornGauge
import BookProof.ChapterFreeFieldBornQuotient
import BookProof.ChapterFreeFieldBornSectionBij
import BookProof.ChapterFreeFieldBornHomeo
import BookProof.ChapterFreeFieldBornSignGauge
import BookProof.ChapterFreeFieldBornSignFiber
import BookProof.ChapterFreeFieldBornSignAction
import BookProof.ChapterFreeFieldBornSignHom
import BookProof.ChapterFreeFieldBornSignMatrix
import BookProof.ChapterFreeFieldBornSignOrientation
import BookProof.ChapterFreeFieldBornSignOrientationCard
import BookProof.ChapterFreeFieldBornSignOrientationKernel
import BookProof.ChapterFreeFieldBornSignOrientationSubgroup
import BookProof.ChapterFreeFieldBornSignOrientationQuotient
import BookProof.ChapterFreeFieldBornSignRepresentation
import BookProof.ChapterFreeFieldBornFiberCard
import BookProof.ChapterFreeFieldBornFiberCardGeneral
import BookProof.ChapterFreeFieldBornFiberTwo
import BookProof.ChapterFreeFieldBornFiberBounds
import BookProof.ChapterFreeFieldBornFiberDeterministic
import BookProof.ChapterFreeFieldBornFiberInterior
import BookProof.ChapterFreeFieldBornFiberSpectrum
import BookProof.ChapterFreeFieldBornFiberStabilizer
import BookProof.ChapterPriorDependence
import BookProof.ChapterPriorOdds
import BookProof.ChapterNoBestPrior
import BookProof.ChapterUniformPrior
import BookProof.ChapterUniformPriorPosterior
import BookProof.ChapterMAPNull
import BookProof.ChapterConsciousnessNullMeasure
import BookProof.ChapterMaxEntropy
import BookProof.ChapterDeepLearningSampling
import BookProof.ChapterDeepLearningEnsemble
import BookProof.ChapterDutchBook
import BookProof.ChapterSequentialBayes
import BookProof.ChapterDeepLearningMAP
import BookProof.ChapterProbabilityClockStochastic
import BookProof.ChapterTotalVariance
import BookProof.ChapterRoadmapAudit
import BookProof.RandomMap2Audit
import BookProof.ChapterSelectingEvents
import BookProof.ChapterBaryonAsymmetry
import BookProof.ChapterParitySU3
import BookProof.ChapterFreeFieldConstraint
import BookProof.ChapterConservativeDiagonal
import BookProof.ChapterGellMann
import BookProof.ChapterHierarchicalBayesComposition
import BookProof.ChapterHierarchicalBayes
import BookProof.ChapterFiniteBayesHierarchy
import BookProof.ChapterOdeComplexification
import BookProof.ChapterRieszFischer
import BookProof.ChapterPaFreeCompletion
import BookProof.ChapterDefinabilityFragment

import BookProof.ChapterFiniteArithmeticPrior
import BookProof.ChapterCountableDefinability
import BookProof.ChapterProbabilityInterface

-- Wave (August 2026): coordinate Solovay–Kopperman substrate and cross-dimensional
-- embedding, kernel transport, and the average/maximal error norms.
import BookProof.Substrate
import BookProof.ChapterSolovay
import BookProof.ChapterSolovayCoordinates
import BookProof.ChapterMehlerOrthogonalInvariance
import BookProof.ChapterMehlerUniqueness
import BookProof.ChapterAtomicDecomposition
import BookProof.ChapterAbelianVonNeumannFinite
import BookProof.ChapterMixedPrior
import BookProof.ChapterSolovayCrossDim
import BookProof.ChapterKopperman
import BookProof.ChapterG3
import BookProof.ChapterKernelTransport
import BookProof.ChapterErrorNorms
import BookProof.ChapterGravityProjDirectSum
import BookProof.ChapterSchurFiniteDim
import BookProof.ChapterGammaCommutant

-- Wave (August 2026): the new chapter `Book/CoherentState.lean` — the coherent-state
-- overlap, Softmax as the Born rule, the attention output as an expectation value,
-- and the provable statistical core of the temperature identity.
import BookProof.ChapterCoherentOverlap
import BookProof.ChapterCoherentOverlapComplex
import BookProof.ChapterSoftmaxBorn
import BookProof.ChapterObservableExpectation
import BookProof.ChapterObservableOperator
import BookProof.ChapterCoherentTemperature
import BookProof.ChapterCoherentOccupation
import BookProof.ChapterSoftmaxSharpness
import BookProof.ChapterCoherentGeometry
import BookProof.ChapterSoftmaxOrder
import BookProof.ChapterAttentionEntropy

-- Wave (August 2026): Priority 4 of `PLAN_LEAN_SPECIALIST_UNPROVED.md` — the
-- concrete-model discharge of the Pauli fundamental theorem's `EXTERNAL` flag:
-- the commutant of the fixed 4×4 Majorana/Dirac γ-matrices is exactly the scalars.
import BookProof.ChapterPauliCommutant

-- Wave (August 2026): Priority 5.1 of `PLAN_LEAN_SPECIALIST_UNPROVED.md` — the
-- probabilistic reading of the density-matrix spectral decomposition (diagonal =
-- marginal, unitary = doubly stochastic conditional).
import BookProof.ChapterDensityMarginalConditional

-- Wave (August 2026): the finite (type I_n) case of the abelian von Neumann
-- classification, replacing the `True` placeholder in `ChapterSelectingEvents`.
import BookProof.ChapterAbelianDiagonal
import BookProof.ChapterAbelianDiagonalCountable
import BookProof.ChapterGravityRankSplit
import BookProof.ChapterEll2Separable

-- Wave (August 2026, third pass of `PLAN_LEAN_SPECIALIST_UNPROVED.md`):
-- Schur's lemma in its full commutant form in finite dimensions, and Weyl's
-- unitarian trick (complete reducibility of unitary representations).
import BookProof.ChapterSchurFullFiniteDim
import BookProof.ChapterUnitaryCompleteReducibility

-- Wave (August 2026): goal A.4 of the book's Proof-Plans appendix — the spectral
-- energy bound and the resulting absence of a finite-time singularity.
import BookProof.ChapterSpectralEnergyBound
import BookProof.ChapterMaschkeFiniteGroup

-- Wave (2026-08-09, `PLAN_LEAN_SPECIALIST_COHERENT.md` Part F): the finite
-- algebraic core of the coherent-state temperature identity (F.4) and the mixed
-- (atomic ⊕ diffuse) class of the abelian von Neumann list (F.5).
import BookProof.ChapterThermalTemperatureCore
import BookProof.ChapterAbelianMixture

-- Wave (2026-08-09, Part F.1-F.3): the QFM dimensional-reduction thread — the
-- inversion-free Krylov shortcut, the Krylov projection as a spectral low-pass
-- filter, and the offline compilation of Tomographic Subspace Recovery.
import BookProof.ChapterH5
import BookProof.ChapterH6
import BookProof.ChapterF8

-- Wave (2026-08-09, Part G): the shared analytic core, promoted out of
-- `PnpProof/` so that it depends only on Mathlib.  These modules are already
-- pulled in transitively; the explicit imports record them as part of the
-- library's public surface.
import BookProof.PhysMeasureBasis
import BookProof.PhysFunctionalAnalysis
import BookProof.PhysHSGaussian
import BookProof.PhysMehler

-- Wave (2026-08-09, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): the
-- Gaussian derivation of the attention temperature `τ = n̄ + ½` from the overlap
-- of displaced thermal states, and the Hermiticity / unitarity layer of the QFM
-- Krylov reduction.
import BookProof.ChapterDisplacedThermalOverlap
import BookProof.ChapterDisplacedThermalMulti
import BookProof.ChapterH7

-- Wave (2026-08-14, `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`): the SIRK
-- approximation orders nest — subspace tower, the block compatibility of the
-- reduced generators, the projection refinement of the approximants, and the
-- nested error bands.
import BookProof.ChapterH8
import BookProof.ChapterH8Bases

-- Wave (2026-08-15, continuation of `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`): the
-- spectral side of the nesting — the numerical ranges, operator norms and Ritz
-- values of the reduced generators nest, `W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)`.
import BookProof.ChapterH9

-- Wave (2026-08-09, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): the
-- quantum fidelity of coherent states (attention as normalized fidelity) and the
-- fluctuation–response law of the attention temperature.
import BookProof.ChapterCoherentFidelity
import BookProof.ChapterSoftmaxFluctuation
import BookProof.ChapterSoftmaxMaxEntropy
import BookProof.ChapterEntropyTemperature

-- Wave (2026-08-09, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): the
-- relative entropy between two attention temperatures, the convexity of the
-- attention free energy, and the position-space realization of the coherent
-- overlap as an honest `L²(ℝ)` inner product of Gaussian wave packets.
import BookProof.ChapterSoftmaxDivergence
import BookProof.ChapterLogPartitionConvex
import BookProof.ChapterCoherentPositionSpace
import BookProof.ChapterSoftmaxStability

-- Wave (2026-08-09, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): the
-- score Jacobian of attention, the value aggregation of the head, attention
-- masking as Bayesian conditioning, and the symmetry group of the coherent-state
-- Born weights.
import BookProof.ChapterSoftmaxJacobian
import BookProof.ChapterAttentionOutput
import BookProof.ChapterAttentionMasking
import BookProof.ChapterCoherentDynamics
import BookProof.ChapterAttentionFactorization
import BookProof.ChapterRotaryPosition

-- Wave (2026-08-10, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): the
-- quantitative retrieval bounds of an attention head, its permutation
-- equivariance, multi-head attention as a mixture, and the cross-entropy
-- learning signal of a Softmax layer.
import BookProof.ChapterAttentionRetrieval
import BookProof.ChapterAttentionEquivariance
import BookProof.ChapterAttentionMixture
import BookProof.ChapterCrossEntropyGradient

-- Wave (2026-08-10, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): how many
-- keys a head effectively reads (collision entropy / participation ratio), how
-- concentrated the Born measurement can be, attention as a Markov kernel with a
-- Doeblin contraction, and the `1/√d` scaling of the dot-product scores.
import BookProof.ChapterAttentionCollision
import BookProof.ChapterAttentionConcentration
import BookProof.ChapterAttentionMarkov
import BookProof.ChapterScaledDotProduct
import BookProof.ChapterAttentionOutputVariance

-- Wave (2026-08-10, information-theoretic pass, part 2): the low-rank bottleneck
-- of a single head, layer normalization as gauge fixing, the sinusoidal
-- positional encoding, and the mixing of a deep stack of one attention layer.
import BookProof.ChapterAttentionLowRank
import BookProof.ChapterLayerNorm
import BookProof.ChapterSinusoidalPosition
import BookProof.ChapterAttentionMixing

-- Wave (2026-08-10, continuation of `PLAN_LEAN_SPECIALIST_COHERENT.md`): turning
-- the temperature knob (monotonicity of the winner's weight, the entropy floor of
-- a bounded head), the attention sink as a common rescaling, coarse-graining the
-- keys (the data-processing inequality for attention), the QK circuit with its
-- `GL(d)` gauge freedom, and the residual stream (a contractive block never
-- overwrites it).
import BookProof.ChapterAttentionTemperature
import BookProof.ChapterAttentionSink
import BookProof.ChapterAttentionCoarseGrain
import BookProof.ChapterAttentionQKCircuit
import BookProof.ChapterResidualStream

-- Wave: the free energy as a soft maximum (`log Z/β` is the largest score up to
-- `log m/β`), the exact `ℓ¹` price of sparse/top-k attention, the OV circuit (the
-- writing-side counterpart of the QK circuit), the vanishing learning signal of a
-- saturated head, and the identification of a logit bias with a Bayesian prior.
import BookProof.ChapterAttentionFreeEnergy
import BookProof.ChapterAttentionSparse
import BookProof.ChapterAttentionOVCircuit
import BookProof.ChapterAttentionSaturation
import BookProof.ChapterAttentionPrior

-- Wave: incremental decoding (the KV cache is an exact convex update), the
-- locality of a distance-penalized head, the calibration of the temperature by the
-- attention entropy, and the optimality of the top-`k` shortlist.
import BookProof.ChapterAttentionStreaming
import BookProof.ChapterAttentionLocality
import BookProof.ChapterAttentionCalibration
import BookProof.ChapterAttentionTopK

-- Wave (2026-08-10, `CONSOLIDATED_PLAN.md` GAP-1): the Fock-space derivation of the
-- zero-point half in `τ = n̄ + ½` from the fidelity of a displaced thermal state
-- with a coherent state.
import BookProof.ChapterCoherentThermalFidelity

-- Wave (2026-08-10, `CONSOLIDATED_PLAN.md` §4.1/§4.4/§4.5/§4.6): the infinite
-- dimensionality of the Kopperman tail, the wave-function of a finite joint law,
-- the separable probability space with an arbitrary finite law, and the explicit
-- product disintegration.
import BookProof.ChapterSolovayTailDimension
import BookProof.ChapterSolovaySeparableExistence

-- Wave (2026-08-10, `CONSOLIDATED_PLAN.md` §4.2): the Hilbert-space form of the
-- Solovay–Kopperman tensor product.
import BookProof.ChapterSolovayHilbertTensor

-- Wave (2026-08-10, `CONSOLIDATED_PLAN.md` GAP-2): the purely atomic condensation
-- of the abelian von Neumann classification.
import BookProof.ChapterAbelianAtomicCondensation

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, diffuse half): the `L∞(μ)`
-- multiplication algebra is its own commutant, hence maximal abelian.
import BookProof.ChapterLinftyMaximalAbelian

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` §4.2, completeness half): the pure
-- tensors are total in `L²(μ ⊗ ν)`.
import BookProof.ChapterTensorCompleteness

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the Gelfand step): a state of a
-- commutative unital C*-algebra is the vector state of a multiplication
-- representation on the `L²` space of a Borel probability measure.
import BookProof.ChapterAbelianGelfandModel

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the operator model): the spectral
-- theorem in multiplication form — a normal operator with a cyclic unit vector is
-- multiplication by `z` on `L²` of a probability measure on its spectrum.
import BookProof.ChapterSpectralMultiplication

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the von Neumann level): the
-- commutant and bicommutant of the algebra generated by a normal operator with a
-- cyclic vector are the unitary copy of `L∞(μ)` acting by multiplication.
import BookProof.ChapterSpectralCommutant

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the reduction to the cyclic
-- case): every complex Hilbert space is the orthogonal direct sum of subspaces
-- cyclic for a given normal operator.
import BookProof.ChapterCyclicDecomposition

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the direct-sum form): the cyclic
-- decomposition as a Hilbert sum, and the projections onto its summands as elements
-- of the commutant of the algebra generated by the operator.
import BookProof.ChapterCyclicDirectSum

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the assembly): every normal
-- operator is a direct sum of multiplication operators — the spectral multiplication
-- model with no cyclic vector assumed.
import BookProof.ChapterSpectralDirectSum

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, dropping the single generator):
-- an *arbitrary* unital `*`-representation of `C(X, ℂ)` with a cyclic unit vector is
-- unitarily multiplication on `L²(μ)` — the measure model of an abstract abelian
-- algebra, with no generator produced.
import BookProof.ChapterAbelianCyclicModel

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the von Neumann level without a
-- generator): the commutant and bicommutant of such a represented abelian algebra
-- are the unitary copy of `L∞(μ)`, so the algebra is maximal abelian.
import BookProof.ChapterAbelianCyclicCommutant

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the general structure theorem):
-- every unital `*`-representation of `C(X, ℂ)` — i.e. every abelian algebra of
-- operators — is a direct sum of multiplication representations, with no cyclic
-- vector, no generator and no separability assumed.
import BookProof.ChapterAbelianDirectSum

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the classification bookkeeping):
-- every finite measure splits into a purely atomic part (a countable sum of point
-- masses) and a diffuse part, so each summand of the abelian multiplication model
-- falls into the manuscript's atomic / diffuse / mixed classes.
import BookProof.ChapterMeasureAtomicDiffuse

-- Wave (2026-08-11, `CONSOLIDATED_PLAN.md` GAP-2, the diffuse standard type): the
-- distribution function of an atomless Borel probability measure on the line pushes
-- it forward to Lebesgue measure on `[0, 1]`, so every diffuse summand measure is a
-- copy of the uniform measure — the `L∞[0,1]` entry of the classification list.
import BookProof.ChapterDiffuseCdfModel

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the diffuse standard type at the
-- operator level): composition with the distribution function is a *unitary* from
-- `L²[0,1]` onto `L²(μ)` carrying multiplication by `g` to multiplication by `g ∘ F`,
-- so the multiplication algebra of a diffuse measure *is* the `L∞[0,1]` model.
import BookProof.ChapterDiffuseUnitaryModel

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the atomic standard type): for a
-- purely atomic measure the normalised point masses are a Hilbert basis of `L²(μ)`
-- and every multiplication operator is diagonal in it — the `I_n` / `ℓ∞(ℕ)` entries
-- of the classification list.
import BookProof.ChapterAtomicDiagonalModel

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the reassembly): `L²(μ)` splits
-- along a measurable set as the Hilbert sum of the two restricted `L²` spaces, with
-- the multiplication operators split accordingly.
import BookProof.ChapterLpRestrictSplit

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the reassembly): rescaling a
-- measure by a nonzero finite constant gives a unitary of the `L²` spaces which
-- carries multiplication by a symbol to multiplication by the same symbol, so the
-- models of the list may be stated for probability measures without loss.
import BookProof.ChapterLpScaleMeasure

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the reassembly): the atomic and
-- the diffuse model are glued into the classification list itself — every Borel
-- probability measure on the line falls into exactly one of the five standard types
-- `I_n`, `ℓ∞(ℕ)`, `L∞[0,1]`, `L∞[0,1] ⊕ I_n`, `L∞[0,1] ⊕ ℓ∞(ℕ)`.
import BookProof.ChapterAbelianClassificationList

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, exhaustiveness): the Borel
-- isomorphism theorem transports a summand on any standard Borel space to the line,
-- so every summand of the general abelian model realises one of the five standard
-- types of the classification list.
import BookProof.ChapterStandardBorelClassification

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the metrizability residue): for a
-- compact Hausdorff spectrum, metrizability of the spectrum is *equivalent* to
-- separability of the algebra of continuous functions, so the standing hypothesis of
-- the exhaustiveness theorem is discharged for every separable commutative unital
-- C*-algebra (Gelfand duality).
import BookProof.ChapterSeparableSpectrum

-- Wave (2026-08-12, `CONSOLIDATED_PLAN.md` GAP-2, the metrizability residue closed for a
-- separably acting algebra): a separable `L²` is carried by a countable family of
-- continuous functions to a standard Borel space, so every summand of an abelian algebra
-- acting on a separable Hilbert space realises one of the five standard types.
import BookProof.ChapterSeparableL2Model

-- Wave (2026-08-17, the shift-invert extension of the Hermite/Galerkin
-- Friedrichs-selection theorem): in the Hashimoto algorithm the operator that is
-- actually iterated is the shift-inverted resolvent `R = (H + γ)⁻¹`, which is
-- bounded (`‖R‖ ≤ 1/γ`) for every positive symmetric `H`, however unbounded.  The
-- bounded Galerkin convergence theory therefore reaches unbounded Hamiltonians,
-- and `R` determines the self-adjoint extension uniquely.
import BookProof.ChapterHashimotoShiftInvert

-- The same theory with the shifts the Shift-invert Rational Krylov method really
-- uses: `γ` complex with non-zero imaginary part (which makes `γ I − A` invertible
-- for every self-adjoint `A`, with no positivity), and a different shift at every
-- step, with the rational Krylov structure that follows.
import BookProof.ChapterHashimotoComplexShifts

-- Wave (2026-08-18, `CONSOLIDATED_PLAN.md` §11.4 items 1 and 2): the Friedrichs
-- extension theorem itself, **with no boundedness hypothesis** — the form inner
-- product on the domain, its completion, the Riesz representation of the
-- resolvent `(H + 1)⁻¹` and the extension `S⁻¹ − 1`.  This discharges the named
-- Friedrichs hypothesis of `ChapterYangMillsFriedrichs` outright, gives the
-- Weyl-gauge Hamiltonian a Friedrichs extension in the unbounded case, and
-- combines with the shift-invert theory so that the Hashimoto/SIRK limit selects
-- the *constructed* extension in the occupation-number (Hermite) realization.
import BookProof.ChapterFriedrichsExtension

-- Wave (2026-08-18, `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F): the *field-space*
-- realization of the gauge-fixed Yang–Mills Hamiltonian.  The Gauss–polynomial
-- (product Hermite) core `p(x) e^{-‖x‖²/4}` of `L²(ℝᵈ)` is built and shown dense,
-- an orthonormal basis adapted to it is produced, and the fields act on it as
-- genuine multiplication and differentiation operators: coordinates `A_{j,a}`,
-- momenta `π = −i ∂/∂A` (symmetric by Gaussian integration by parts), the
-- magnetic field `B_{ia} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`, and the
-- Weyl ordering `½(PQ + QP)` demanded by `[A, π] = i`.  The resulting
-- `H₁ = ½Σπ² + ½ΣB²` is symmetric and positive on the core, so the Friedrichs
-- extension theorem and the Hashimoto/SIRK selection theorem apply to it.
import BookProof.ChapterHermiteProductCore
import BookProof.ChapterYangMillsHermite
-- Part F.11: the *second quantization* of that one-particle Hamiltonian on the
-- finite-occupation states over the core: the Fock space `ℓ²(ℕ →₀ ℕ)`, the
-- ladder operators with `[a_j, a_j†] = 1`, `dΓ(A) = Σ ⟪e_j, A e_k⟫ a_j† a_k`, its
-- symmetry and positivity, and its Friedrichs extension.
import BookProof.ChapterFockSecondQuantization

-- The general Stone theorem on a separable Hilbert space (`ChapterStoneResolvent`
-- through `ChapterStoneSeparable`): an unbounded self-adjoint operator `A` generates a
-- weakly measurable one-parameter unitary group `e^{-itA}`, every weakly measurable
-- one-parameter unitary group on a separable Hilbert space arises this way from its
-- self-adjoint infinitesimal generator, and the two constructions are mutually inverse.
import BookProof.ChapterStoneTheorem
import BookProof.ChapterStoneSeparable

-- The Stone bridge and the concrete flows: `ChapterStoneBridge` packages a
-- selected self-adjoint extension (`IsSelfAdjointExtension` /
-- `IsPositiveSelfAdjointExtension`) into the bundled `UnboundedSelfAdjoint`
-- structure that Stone's theorem consumes, and `ChapterStoneFlows` instantiates
-- the complete unitary flow for the Eulerian NS (`ns_stone_flow`), Lagrangian NS
-- (`lagrangian_stone_flow`, `diagKR_stone_flow`) and QYM (`ym_fock_stone_flow`)
-- Hamiltonians.
import BookProof.ChapterStoneBridge
import BookProof.ChapterStoneFlows

-- The canonical (ladder) realization of the Lagrangian Navier-Stokes Hamiltonian:
-- the parcel momenta and viscous gradients as the non-commuting canonical pairs of
-- the trajectory-space Hermite basis, the identity `½∑Pᵢ² + ν∑Qᵢ² = ω(N + 3/2)`,
-- essential self-adjointness of the full transformed Hamiltonian on that core, and
-- the complete unitary flow it generates.
import BookProof.ChapterNavierStokesLagrangianCanonical

-- Wave 2026-08-21 (backlog item A1, the hyperbolic mixed case): the non-commuting
-- mixture `□ + V` with an *indefinite quadratic* potential.  For an arbitrary real
-- weight vector `c` (no sign condition, so the signature may be hyperbolic) the
-- operator `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is symmetric and essentially self-adjoint on
-- the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`, with the pointwise
-- identification of the differential expression; the Minkowski weights
-- `(1, −1, …, −1)` give `□ + V`, `V(t,x) = (t² − ‖x‖²)/4`, in the convention
-- `□ = −∂_t² + Δ_x` of `ChapterStrichartzWave`.
import BookProof.ChapterHyperbolicQuadraticEsa
-- Relatively bounded (unbounded) perturbations of the diagonal quadratic
-- Hamiltonian: for strictly positive weights `cᵢ ≥ c₀ > 0` the position and
-- momentum operators are `H_c`-bounded with arbitrarily small relative bound, so
-- `H_c` plus any first-order term `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` — in particular the
-- Stark-shifted oscillator `−Δ + ‖x‖²/4 + ⟨b, x⟩` — is essentially self-adjoint
-- on the same Hermite core.
import BookProof.ChapterHermiteRelativeBound
-- General (non-diagonal) quadratic Hamiltonians of arbitrary signature: for every
-- real symmetric matrix `A`, the operator `H_A = ∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)`
-- with `π_k = −i∂/∂x_k` is symmetric and essentially self-adjoint on the
-- Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.  The route is the orthogonal
-- change of coordinates that diagonalizes `A`, which acts on the core as a unitary
-- substitution and carries the diagonal Hamiltonian onto `H_A`.
import BookProof.ChapterQuadraticRotationEsa
-- The general *inhomogeneous* elliptic quadratic Hamiltonian: for a positive definite
-- real symmetric matrix `A` and arbitrary real vectors `b, b'`, the operator
-- `H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` — a general elliptic quadratic form with cross terms
-- plus a general unbounded first-order term — is symmetric and essentially
-- self-adjoint on the same Gauss–polynomial core.  The rotated Hermite functions are
-- upgraded to a Hilbert basis, which turns the orthogonal substitution into an honest
-- unitary `rotU` of `L²(ℝᵈ)`; essential self-adjointness is a unitary invariant, so the
-- Kato–Rellich theorem of `ChapterHermiteRelativeBound` transfers.
import BookProof.ChapterQuadraticRotationPerturbed
-- The translated, modulated Gauss–polynomial core of `L²(ℝᵈ)`: the functions
-- `p(x − a) e^{−‖x − a‖²/4} e^{i⟨k, x⟩}` for `p` a complex polynomial.  Translating by
-- `a` and modulating by `k` is a unitary substitution of `L²`, so this core is dense and
-- carries an orthonormal Hermite family; it is the frame adapted to a classical
-- equilibrium at position `a` with momentum `k`.
import BookProof.ChapterShiftedHermiteCore
-- The *indefinite* inhomogeneous quadratic Hamiltonian: for weights `cᵢ ≠ 0` of
-- arbitrary sign and arbitrary real `b, b'`, the operator
-- `H = ∑ᵢ (cᵢ(πᵢ² + xᵢ²/4) + bᵢ xᵢ + b'ᵢ πᵢ)` is symmetric and essentially self-adjoint
-- on the translated, modulated core with `aᵢ = −2bᵢ/cᵢ`, `kᵢ = −b'ᵢ/(2cᵢ)`.  Completing
-- the square replaces the Kato–Rellich argument of `ChapterHermiteRelativeBound`, which
-- needs a definite `c`; the Minkowski weights give `□ + V + ⟨b, x⟩ + ⟨b', π⟩`.
import BookProof.ChapterShiftedQuadraticEsa
-- The *indefinite* inhomogeneous quadratic Hamiltonian **with cross terms**: for every
-- real symmetric *invertible* matrix `A` of arbitrary signature and arbitrary real
-- `b, b'`, the operator `H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` is symmetric and essentially
-- self-adjoint on the translated, modulated core with `a = −2A⁻¹b`, `k = −A⁻¹b'/2`.
-- Completing the square in matrix form combines the orthogonal diagonalization of
-- `ChapterQuadraticRotationEsa` with the phase-space translation of
-- `ChapterShiftedQuadraticEsa`, and removes the positive definiteness that the
-- Kato–Rellich route of `ChapterQuadraticRotationPerturbed` needs.
import BookProof.ChapterShiftedQuadraticMatrixEsa
-- The Stone flow acts on eigenvectors by a phase: `U t ψ = e^{−iλt} ψ` whenever
-- `T ψ = λψ`, so the abstract existence of the unitary group of a Hamiltonian with an
-- eigenbasis becomes an explicit solution of the Schrödinger equation.
import BookProof.ChapterStoneEigenflow
-- The inhomogeneous quadratic Hamiltonian with a *singular* quadratic form: for every
-- real symmetric `A` (invertible or not) whose classical equilibrium equations
-- `A a = −2b`, `A k = −b'/2` are solvable — equivalently, `b, b' ⊥ ker A` — the operator
-- `H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` is symmetric and essentially self-adjoint on the
-- translated, modulated core, and its flow acts on the Hermite eigenbasis by a phase.
import BookProof.ChapterShiftedQuadraticDegenerate
-- Fourier multipliers with a real symbol: the Plancherel argument of
-- `ChapterStrichartzWave` extracted as a reusable instrument, and applied to the
-- *first-order* operators it did not cover — the momentum family `∑ᵢ cᵢ(−i∂_{wᵢ})` and
-- the full `∑ᵢ cᵢ∂_{wᵢ}² + ∑ᵢ aᵢ(−i∂_{wᵢ}) + κ` — on the Schwartz core of `L²(V)`.
import BookProof.ChapterFourierMultiplierEsa
-- The mixed first-order operator `⟪x, b⟫ − i ∂_m`: a linear potential *and* a momentum
-- term in the same direction, the one residual case of the quadratic family that neither
-- the Hermite eigenbasis (no `L²` eigenvector) nor the Fourier multiplier route (not
-- constant-coefficient) can reach.  The quadratic gauge `e^{iθ}` with `∂_m θ = −⟪x, b⟫`
-- intertwines it with the pure momentum operator, giving symmetry and essential
-- self-adjointness on the Schwartz core of `L²(V)` for arbitrary `b, m`.
import BookProof.ChapterMixedLinearEsa
-- The same quadrature `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` on the **Gauss–polynomial (product Hermite)
-- core** — the core the whole quadratic family lives on.  A moment lemma without an `L²`
-- hypothesis settles the purely positional case, and the metaplectic rotation, which on
-- that core is the diagonal phase `ψ_α ↦ ζ^α ψ_α`, rotates it onto the general one, for
-- arbitrary real `b, b'`.
import BookProof.ChapterQuadratureEsa
-- A Carleman criterion on the product Hermite basis: a square-summable family satisfying
-- the nearest-neighbour recursion with a real diagonal and constant ladder amplitudes at a
-- non-real point vanishes (the flux through the boundary faces of a multi-index cube grows
-- like `√N`, and `∑ 1/√N = ∞`).  Consequence: for *arbitrary* real weights `c` and
-- *arbitrary* real `b, b'`, `∑ᵢ cᵢ(πᵢ² + xᵢ²/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially
-- self-adjoint on the plain Gauss–polynomial core — no ellipticity, no sign condition, no
-- classical equilibrium, no change of core.
import BookProof.ChapterHermiteCarlemanEsa
-- The same flux argument for a **two-step** recursion: hops `α ↦ α ± eᵢ` and
-- `α ↦ α ± 2eᵢ`, with amplitudes `O(N)` on a boundary face of thickness two.  Disjointness
-- of the faces is replaced by a multiplicity bound, and the Carleman divergence used is
-- `∑ 1/(N+1) = ∞`.
import BookProof.ChapterCarlemanTwoStep
-- Consequence of the two-step criterion: for *arbitrary* real `p, q, s, b, b'`, the general
-- **mode-diagonal** quadratic Hamiltonian
-- `∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint
-- on the plain Gauss–polynomial core.  Elliptic, hyperbolic or parabolic in each mode, any
-- signs, degenerate modes allowed; in particular the generator of dilations
-- `½∑ᵢ(xᵢπᵢ + πᵢxᵢ)`.
import BookProof.ChapterModeQuadraticEsa
-- The Carleman flux argument rerun on the **simplex** shells `{α : |α| ≤ N}`, the grading
-- by total degree adapted to a general quadratic ladder.  Degree-preserving mode-exchange
-- hops `α ↦ α − eⱼ + eᵢ` carry zero flux when their amplitude matrix is Hermitian;
-- degree-changing pair hops `α ↦ α ± (eᵢ + eⱼ)` leak only through a boundary shell of
-- thickness two.  The Carleman divergence used is again `∑ 1/(N+2) = ∞`.
import BookProof.ChapterCarlemanSimplex
-- Consequence of the simplex criterion: the **general** real quadratic-plus-linear
-- Hamiltonian `∑_{i,j} (Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, for
-- arbitrary real matrices `P, Q, S` and vectors `b, b'`, is essentially self-adjoint on the
-- plain Gauss–polynomial core.  Distinct modes may now be coupled arbitrarily — no
-- ellipticity, no definiteness, no non-degeneracy, no classical equilibrium.
import BookProof.ChapterFullQuadraticEsa
-- The spectral theorem in multiplication form for an **unbounded** self-adjoint operator:
-- the missing existence step behind `ChapterUnitaryTransport`.  The resolvent
-- `R = (A − i)⁻¹` is bounded, injective, normal, with range exactly the domain of `A`, so
-- the bounded multiplication model applies to it; the measure is carried by the Cayley
-- circle `|z|² = Im z` and gives no mass to `z = 0`, so `A` is multiplication by the real
-- function `Re z/|z|²` on a Hilbert sum of `L²(μ)` spaces.
import BookProof.ChapterUnboundedSpectralModel
-- The Faris–Lavine bounds for an **infinite sum** of operators: a summable family of
-- symmetric operators on the maximal domain of a comparison symbol, each relatively
-- bounded by the comparison operator and each with commutator form dominated by it, sums
-- to an operator essentially self-adjoint on the finite-mode core.
import BookProof.ChapterOperatorSeriesEsa
-- The general quadratic Hamiltonian of a boson field with **infinitely many modes**:
-- `H = ∑ᵢ ωᵢ aᵢ†aᵢ + ∑ₖ (gₖ a^{†Pₖ}a^{Qₖ} + conj(gₖ) a^{†Qₖ}a^{Pₖ})` on the Fock space
-- `ℓ²(ι →₀ ℕ)`, with an arbitrary mode set, an arbitrary non-negative (possibly unbounded)
-- dispersion `ω`, and an arbitrary family of quadratic interaction terms subject only to
-- `∑ₖ ‖gₖ‖(ω(Pₖ) + ω(Qₖ) + 2) < ∞`, is essentially self-adjoint on the finite-particle
-- core.  Bogoliubov pair creation is the special case `Pₖ = eₘ + eₙ`, `Qₖ = 0`.
import BookProof.ChapterFockQuadraticEsa
-- Fibrewise essential self-adjointness **glues**: a deficiency space of an orthogonal
-- direct sum is the direct sum of the fibre deficiency spaces, so if every fibre operator
-- is essentially self-adjoint on its core then `⊕ᵢ Hᵢ` is essentially self-adjoint on the
-- algebraic direct sum of the cores — no relative bound, no comparison operator, no
-- commutator estimate.  Applied to the *whole* continuum Fock space `⊕ₙ L²(ℝⁿ)` of the
-- parcel picture, this upgrades the one-sector statement of
-- `ChapterNavierStokesFockContinuum` to the second-quantized Hamiltonian
-- `ĥ = ∫ w(ξ)a†(ξ)a(ξ)dξ` itself, for an arbitrary measurable field `w`.
import BookProof.ChapterDirectSumEsa
-- A Carleman (flux) criterion for **general lattice hops** `α ↦ α + p − m`, including the
-- non-monotone mode-exchange hop `α ↦ α ± (eᵢ − eⱼ)` produced by a quadratic Hamiltonian
-- coupling two distinct modes.  The flux through the boundary of a multi-index cube now has
-- two layers — outgoing (`obd`) and incoming (`ibd`) — and both are controlled by Bessel
-- multiplicity bounds, so a square-summable solution of a general-hop recursion with a real
-- diagonal and amplitudes `O(N)` at a non-real point vanishes (`ladderH_eq_zero`).
import BookProof.ChapterCarlemanGeneralHop
-- The Hashimoto/SIRK shift-invert selection for the **differential** Navier–Stokes fiber
-- generator: the operator written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication
-- operator on the Hermite core of `L²(du₁du₂du₃)` is symmetric there (Gauss symmetry of the
-- Weyl-ordered polynomial operator), so its closure is the unique self-adjoint extension and
-- the rational-Krylov shift-invert data of the algorithm determine it completely.  This
-- brings the differential realization to parity with the abstract sequence-space layer.
import BookProof.ChapterNavierStokesDiffHashimoto
-- The `f(R) = (M²/2)R + αR²` (Starobinsky) potentials: the ghost-free scalar–tensor form of
-- the action, the Einstein-frame scalaron potential with its non-negativity, plateau and
-- exponential wall, and the completed square that makes the conformal-mode potential bounded
-- below — together with the resulting `R + αR²` mode Hamiltonian, its essential
-- self-adjointness on a dense maximal domain and the unitary flow Stone's theorem gives it.
import BookProof.ChapterStarobinskyPotential
-- The scalaron sector with its exponential wall: multiplication by an *arbitrary smooth*
-- real potential — no temperate growth, no boundedness, no semiboundedness — is essentially
-- self-adjoint on the dense compactly supported smooth core of L², the Starobinsky potential
-- being a case in point (it is proved not to be of temperate growth); every localization of
-- `□ + V` is essentially self-adjoint on the Schwartz core; and the `R + αR²` mode
-- Hamiltonian including the scalaron potential is essentially self-adjoint, bounded below by
-- `−M⁴/(16α)`, with a complete unitary flow.
import BookProof.ChapterScalaronCoreEsa
-- From one particle to the nested Fock space: the sector-wise scalaron Hamiltonian
-- `⊕ₙ ∑ⱼ (V₃(R_c ⱼ) + V(φ ⱼ))` on `⊕ₙ L²(ℝ^(n×2))` is densely defined, symmetric,
-- essentially self-adjoint and generates the unitary group — the one-particle theorem of
-- `ChapterScalaronCoreEsa` glued over the finite-particle sectors by the direct-sum
-- instrument of `ChapterDirectSumEsa`; likewise in the mode (Hermite) realisation.
import BookProof.ChapterScalaronFockEsa
-- Part F.11: the *second quantization* of that one-particle Hamiltonian on the
-- finite-occupation states over the core: the Fock space `ℓ²(ℕ →₀ ℕ)`, the
-- ladder operators with `[a_j, a_j†] = 1`, `dΓ(A) = Σ ⟪e_j, A e_k⟫ a_j† a_k`, its
-- symmetry and positivity, and its Friedrichs extension.
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterFermionFock
import BookProof.ChapterGradedFock
import BookProof.ChapterGradedFriedrichs
import BookProof.ChapterGradedHashimoto
import BookProof.ChapterKrylovShiftSpan
-- The two Faris–Lavine inequalities for the Navier–Stokes quadratic symbol written as an
-- actual *differential* operator on `L²(du₁du₂du₃)`: the comparison operator is the
-- differential harmonic oscillator `2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, identified with the transported
-- number operator by the polynomial identity `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½`; the relative bound
-- `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` and the form-commutator bound `|⟪f, i[H,N]f⟫| ≤ c⟪f, Nf⟫` hold on
-- the Gauss–polynomial core and on the maximal domain, yielding essential self-adjointness of
-- the differential symbol by the Faris–Lavine criterion applied in `L²(ℝ³)` itself.
import BookProof.ChapterNavierStokesDiffFarisLavine
-- Step 2 of the scalaron strand: the conformal-mode potential after the *densitized* change
-- of variables `e = y²`.  The transformed potential `V₃(y²)` is still bounded below by
-- `−M⁴/(16α)` (and at `α = 0` still unbounded, so the bound comes from `αR²`, not from the
-- densitization); the half-density unitary of `ChapterQuantumGravityHalfDensity` carries the
-- bounded-energy core of `L²((0,∞), de)` onto that of `L²((0,∞), 2y dy)` and intertwines the
-- two multiplication Hamiltonians, so essential self-adjointness transfers along it; and a
-- pointwise lower bound on a multiplier is semiboundedness of the multiplication operator.
import BookProof.ChapterScalaronDensitizedTransfer
-- The end-to-end SIRK/Hashimoto reliability assembly (plan §12, Gap 1): the pointwise
-- Crouzeix core `sirk_error_bound_at` weakens the compression-transfer hypothesis to the
-- single Krylov seed, which is where the rational transfer of `ChapterH8` is available; with
-- that, `sirk_end_to_end` carries **no** transfer hypothesis and produces the eq.-(12) bound
-- `‖flow v − V ψ(B) V∗ v‖ ≤ 2C e^{−hm} Dmin ‖v‖` from the isometry, the Krylov invariance of
-- the range and the invertibility of the rational denominator.  One convex Crouzeix domain
-- serves both bounds (`crouzeix_domain_transfer`), the reduced flows converge to the exact
-- one and — for time-independent constants — uniformly in time; the reconstruction step
-- `V ∘ V∗` is the orthogonal projection onto the retained subspace.
import BookProof.ChapterSirkEndToEnd
-- The multi-shift forward-sequence span identity (plan §12, Gap 4b): the forward sequence
-- `w₀ = v₀`, `wₖ₊₁ = (H − zₖ I) wₖ` of an arbitrary shift schedule spans exactly the standard
-- Krylov subspace, so the choice of shifts changes the basis but never the compressed space.
-- The general principle is the triangular criterion `triangularSpan_eq_krylovSpan`.
import BookProof.ChapterSirkMultiShift
-- The restart cycle of the SIRK numerics and its accumulated error (plan §12, Gap 4a): two
-- contractive propagators differing by `ε` in the strong sense differ by at most `n·ε` after
-- `n` restart cycles, so restarting multiplies the `e^{−hm}` per-cycle guarantee by the cycle
-- count and nothing worse.
import BookProof.ChapterSirkRestart
-- Whitening independence of the reduced operator (plan §12, Gap 4c): two isometric embeddings
-- with the same range induce the same orthogonal projection, are related by a unitary change
-- of whitening, give unitarily conjugate compressions, and produce literally the same
-- reconstructed SIRK operator `P X P` on the ambient space.
import BookProof.ChapterSirkWhitening
-- The Gram whitening the numerics actually performs: the synthesis map of the raw Krylov
-- vectors, its Gram operator/matrix, and the fact that a whitening `T∗GT = 1` is an
-- isometric embedding of the retained subspace — so the whitening-independence theorems
-- above apply to it, and such a whitening exists (plan §12, Gap 4c, existence half).
import BookProof.ChapterSirkGramWhitening
-- The numerical Gram cutoff: with an eigendecomposition of the Gram operator and every
-- discarded eigenvalue at most `tol`, every raw Krylov vector lies within `√tol` of the
-- retained subspace, so the geometric truncation parameter `δ` of the module above is
-- bounded by the quantity the code thresholds; and the inverse-square-root embedding
-- `V = W U_R Λ_R^{-1/2}` the solver builds is an isometric embedding of that subspace
-- (plan §12, Gap 4c, the recorded residue).
import BookProof.ChapterSirkGramCutoff
-- The Crouzeix domain of the shift-invert (plan §12, Gap 2, the abstract half): the operator
-- the algorithm iterates is the resolvent, so its numerical range — and that of every Krylov
-- compression of it — is fixed by the shift alone.  Positive generator at a real shift `γ > 0`:
-- the real segment `[0, γ⁻¹]`.  Indefinite generator at a non-real shift: the disc of radius
-- `|Im γ|⁻¹`.  Hence the SIRK constants `C`, `Dmin` may be measured uniformly in the reduction
-- order `m`.
import BookProof.ChapterSirkSpectralGeometry
-- The same, per physical system (plan §12, Gap 2, the concrete half): the Crouzeix domain of
-- QYM (Friedrichs route, a segment), of NS Eulerian in both the sequence-space and the
-- differential realization, of NS Lagrangian (abstract and the concrete Kato–Rellich model)
-- and of the gauge-fixed `R + αR²` quantum-gravity mode Hamiltonian, whose shift-invert
-- (`qgR2_shiftInvert_selects`) is constructed here for the first time from the ESA-selected
-- extension.
import BookProof.ChapterSirkPerSystem
-- The rank-truncated Gram case (plan §12, Gap 4c, the remaining half): truncating the whitened
-- basis is a further compression of the reduced operator, and the transfer identity it breaks is
-- restored up to the discarded part of the seed, so the end-to-end bound survives with one
-- additive term `‖r(X)‖ · ‖v − P v‖`.
import BookProof.ChapterSirkTruncation
-- The unitary-group transfer for bounded generators (plan §12, Gap 3, the bounded half): the
-- exponential is Lipschitz on balls of a Banach algebra, `‖exp a − exp b‖ ≤ ‖a − b‖ e^{M}`, so
-- the propagators of two bounded generators differ by at most `|t| ‖a − b‖ e^{|t| M}` — uniformly
-- on every compact time interval.
import BookProof.ChapterSirkGroupTransfer

-- `ChapterSirkTrotterKato`: the **unbounded** half of plan §12 Gap 3 — the Trotter–Kato
-- theorem for the unbounded self-adjoint operators of `ChapterStoneResolvent`: strong
-- convergence of the resolvents `(Aₙ − i)⁻¹ → (A − i)⁻¹` implies strong convergence of the
-- unitary flows `e^{−itAₙ} → e^{−itA}`, uniformly for `t` in a bounded interval.
import BookProof.ChapterSirkTrotterKato

-- `ChapterSirkTrotterKatoGalerkin`: the Galerkin instance of the transfer — the unitary
-- flows of the Rayleigh–Ritz compressions converge to the flow of the selected generator,
-- uniformly on bounded time intervals (in the regime where the operator is bounded on its
-- domain, as in `ChapterHermiteGalerkinFriedrichs`).
import BookProof.ChapterSirkTrotterKatoGalerkin

-- `ChapterSirkLagrangianCanonical`: the two Lagrangian realizations of plan §12 Gap 2 that
-- had essential self-adjointness but no Hashimoto/SIRK companion — the canonical
-- (non-commuting ladder) realization and the Fock/momentum (continuum symbols)
-- realization — get their shift-invert selection, Crouzeix domain and Stone flow.
import BookProof.ChapterSirkLagrangianCanonical

-- `ChapterSirkRitzSpectrum`: the spectral reading of the Rayleigh–Ritz limit (plan §12
-- Gap 2, QYM).  The bottom of the spectrum of a bounded self-adjoint operator is the
-- bottom of its numerical range (`sInf_spectrum_eq_rayleighInf`), so the Ritz values of
-- the Hermite/Galerkin truncations converge to the bottom of the spectrum of the operator
-- the algorithm selects.
import BookProof.ChapterSirkRitzSpectrum

-- `ChapterSirkDiffusiveDecay`: the laminar decay rate (plan §12 Gap 2, NS Lagrangian).
-- A coercive generator has `‖e^{−tA} v‖ ≤ e^{−μt} ‖v‖`, and the SIRK compression of a
-- coercive generator is coercive with the same constant, so the reduced model reproduces
-- the decay rate exactly.
import BookProof.ChapterSirkDiffusiveDecay

-- `ChapterQgHermiteCore`: the QG one-particle Hamiltonian is well defined on the
-- Gauss–polynomial (Hermite) core (plan §10.6.1, target 1).  The Gaussian tail dominates
-- every exponential, so multiplication by the exponentially growing scalaron potential —
-- and by the full potential of the reduced `(R_c, φ)` sector — maps the core into `L²`,
-- and the core is invariant under the kinetic term.
import BookProof.ChapterQgHermiteCore

-- `ChapterQgHermiteFriedrichs`: the QG one-particle Hamiltonian `−Δ + W` on the
-- Gauss–polynomial (Hermite) core is symmetric, bounded below by the lower bound of its
-- potential, and therefore has a canonical semibounded self-adjoint (Friedrichs)
-- realization (plan §10.6.1, towards target 4 — existence and canonical choice of the
-- realization, *not* essential self-adjointness).
import BookProof.ChapterQgHermiteFriedrichs

-- `ChapterQgHermiteOscillatorEsa`: **essential** self-adjointness on the Gauss–polynomial
-- (Hermite) core for the harmonic (conformal-mode) potential, in every dimension, via a
-- general eigenbasis criterion; plus its Stone flow and its stability under bounded
-- perturbations (plan §10.6.1, target 4 for the parabolic potential).
import BookProof.ChapterQgHermiteOscillatorEsa

-- `ChapterScalaronHermiteEsa`: **essential** self-adjointness on the Gauss–polynomial
-- (Hermite) core for an *exponentially growing* potential — the Starobinsky scalaron
-- potential and the full `V₃(R_c) + V(φ)` sector potential.  The moment/Fourier uniqueness
-- argument is generalized from square-integrable data to data of Gaussian exponential
-- decay, which is what `(W − z)w` satisfies when `W` is unbounded (plan §10.6.1, target 4
-- for the scalaron potential term).
import BookProof.ChapterScalaronHermiteEsa

-- `ChapterHermiteExpWall`: the negative half of plan §10.6.1, target 2 (which the plan
-- itself flags as "needs restating").  The Kato–Rellich route to essential self-adjointness
-- of `−Δ + V` on the Hermite core is *not available*: along the monomial core family
-- `ψ_N = x^N e^{−x²/4}` the exponential wall grows like `N⁴` while the kinetic term and the
-- conformal-mode oscillator grow only cubically, so the scalaron potential is not
-- relatively bounded with respect to either — not with a small relative bound, and not
-- with any pair of constants.
import BookProof.ChapterHermiteExpWall

-- `ChapterHermiteQuadraticEsa`: the *positive* counterpart of `ChapterHermiteExpWall`, and
-- the unbounded-perturbation half of plan §10.6.1, target 4.  The harmonic potential
-- `‖x‖²/4` is relatively bounded with respect to `−Δ + ‖x‖²/4` with relative constant `1`
-- (`norm_sq_harmPoly_mul_le`, proved from the Gaussian anticommutator identity), hence every
-- continuous potential dominated by `a‖x‖²/4 + b` with `a < 1` — unbounded perturbations
-- included — leaves the Gauss–polynomial (Hermite) core a core
-- (`harmonic_add_subquadratic_essentiallySelfAdjoint`), with growth-form and scaled-oscillator
-- corollaries and the conformal-mode instance `confV_essentiallySelfAdjoint` for `0 < α < 1/2`.
import BookProof.ChapterHermiteQuadraticEsa

-- `ChapterFriedrichsCanonical`: the Friedrichs extension is *canonical* — packaged as a
-- named operator (`friedrichsOp` on `friedrichsDomain`), it is a positive self-adjoint
-- extension, it dominates every symmetric extension whose domain lies in the form domain
-- (`friedrichs_canonical`), and it is therefore the unique self-adjoint extension with that
-- property (`friedrichs_unique_selfAdjoint`); with the QG scalaron instance.
import BookProof.ChapterFriedrichsCanonical

-- Wave (2026-08-24, gate re-run): four modules that existed in the tree but were in no
-- build target — registered here so `lake build` verifies them.
--
-- `ChapterNavierStokesCarleman`: Carleman's criterion for a tridiagonal (Jacobi) operator
-- on `ℓ²(ℕ)` (`∑ 1/|c_n| = ∞ ⇒ essential self-adjointness`, by the telescoping Wronskian),
-- and its Navier–Stokes instance: the half-line realization of the **full** Hamiltonian —
-- symmetric-difference momentum, multiplication modes, hence genuinely non-commuting —
-- is essentially self-adjoint whenever the Navier–Stokes symbol satisfies Carleman's
-- growth condition, with a concrete unbounded (linearly growing) instance.
import BookProof.ChapterNavierStokesCarleman

-- `ChapterSoftmaxTemperatureMonotone`, `ChapterAttentionResponse`,
-- `ChapterAttentionCapacity`: the attention-layer monotone sharpening law, the
-- vector-valued fluctuation–response law of the head output, and the memory capacity of a
-- head storing `m` separated key–value pairs.
import BookProof.ChapterSoftmaxTemperatureMonotone
import BookProof.ChapterAttentionResponse
import BookProof.ChapterAttentionCapacity

-- Wave (2026-08-24g, plan §9 backlog item 3, the reduction of the unbounded layer to a
-- bounded one).
--
-- `ChapterCayleyTransform`: the **Cayley transform** `V = (A − i)(A + i)⁻¹` of a densely
-- defined self-adjoint operator, built from the resolvents of `ChapterStoneResolvent`: it
-- is unitary, satisfies `V(A + i)ψ = (A − i)ψ`, `1` is not an eigenvalue of `V`,
-- `ran(1 − V) = D(A)` is dense, and `A = i(1 + V)(1 − V)⁻¹`.
import BookProof.ChapterCayleyTransform

-- `ChapterCayleyInverse`: the converse — the basic criterion "symmetric with `A ± i` onto
-- ⇒ self-adjoint", and the inverse Cayley transform of a unitary `V` with `1 − V`
-- injective, which is self-adjoint on `ran(1 − V)`; the two constructions are mutually
-- inverse, so the unbounded layer is faithfully encoded by a bounded (unitary) object.
import BookProof.ChapterCayleyInverse

-- `ChapterCayleySpectralModel`: composing the two previous modules with the bounded
-- spectral theorem of `ChapterSpectralMultiplication` — the resolvent `(A + i)⁻¹` is the
-- *continuous* function `(1 − z)/(2i)` of the Cayley transform, so an unbounded
-- self-adjoint operator whose Cayley transform has a cyclic vector is multiplication by
-- `i(1 + z)/(1 − z)` on `L²(μ)`, stated through the bounded symbol pair `(g, h)`.
import BookProof.ChapterCayleySpectralModel

-- Wave (2026-08-25d, plan §12.2 Gap 5 — the physical-subspace (BRST) leakage of the
-- truncated dynamics, quantified at the level of the generators).
--
-- `ChapterBrstTruncationLeakage`: for bounded self-adjoint generators the unitary flow
-- `e^{-itH}` carries a commuting BRST charge along, so the exact dynamics leaks nothing; a
-- Duhamel estimate then bounds the leakage of the *truncated* flow `e^{-itPHP}` by
-- `‖Ω‖ ‖(1 − P)HP‖ ‖x‖ t` — the rate is the block of the Hamiltonian the truncation
-- discards — with a restart version accumulating linearly in the number of cycles and a
-- bridge that discharges the `ε` hypothesis of `ChapterSirkRestart.brst_leakage_bound`.
import BookProof.ChapterBrstTruncationLeakage

-- Wave (2026-08-25e, plan §10.6.1 target 3 — the Carleman flux extension to
-- **unbounded-hop** (infinite-range) Hermitian kernels).
--
-- `ChapterCarlemanUnboundedHop`: the earlier flux modules (`ChapterHermiteCarlemanEsa`,
-- `ChapterCarlemanTwoStep`, `ChapterCarlemanGeneralHop`) all assume a *finite* hop range.
-- Here the cut flux of a Hermitian kernel `a n k` on `ℕ` is bounded by an amplitude
-- envelope `A N` times a "cut mass" weighted by the tails `Θ` of a hop profile `θ`, so a
-- square-summable solution of `∑ₖ a n k u k = z u n` at a non-real `z` vanishes whenever
-- `θ` has finite first moment and `∑ 1/A = ∞` (Carleman's condition) — the diagonal is
-- unconstrained.  Transported to `ℓ²(ℕ)` this gives triviality of both deficiency spaces,
-- essential self-adjointness on the finite-mode core and a Stone flow, and the module ends
-- with a genuinely infinite-range instance: arbitrary real diagonal with off-diagonal
-- entries `(1 + min n k) ρ^{|n−k|}`, `0 ≤ ρ < 1`, every row of which has infinitely many
-- non-zero entries.
import BookProof.ChapterCarlemanUnboundedHop

-- Wave (2026-08-25f, plan §12.2 Gap 5 — the BRST leakage for an **unbounded** Hamiltonian).
--
-- `ChapterBrstUnboundedLeakage`: the previous leakage module assumes a bounded generator.
-- Here the exact generator is an arbitrary unbounded self-adjoint operator `T` with its
-- Stone group `e^{-itT}`, and the truncated generator is the compression `P T P` to a
-- finite-dimensional retained subspace of the domain — the finite-`m` object the solver
-- integrates.  A Duhamel estimate against the strongly continuous group gives the flow
-- error `‖e^{-itPTP}x − e^{-itT}x‖ ≤ ‖(1 − P)TP‖ ‖x‖ t` and the leakage bound
-- `‖Ω(e^{-itPTP}x)‖ ≤ ‖Ωx‖ + ‖Ω‖ ‖(1 − P)TP‖ ‖x‖ t` for an observable commuting with the
-- exact group: both are controlled by the discarded off-diagonal block alone.
import BookProof.ChapterBrstUnboundedLeakage

-- Wave (2026-08-25g, plan §10.6.2 item 4 — the BRST-*reduced transfer*).
--
-- `ChapterBrstReducedTransfer`: the evolution must map the physical subspace to itself and
-- descend to BRST cohomology `ker Ω / closure (range Ω)` (the §10.3 caveat).  For a bounded
-- nilpotent BRST charge `Ω` and any family commuting with it, the closed and the exact
-- states are invariant (the latter by a continuity argument), so the family induces a map
-- on cohomology; for a one-parameter isometric group this reduced transfer is a group of
-- linear automorphisms preserving the quotient (BRST) norm.  Instantiated at the Stone
-- group `e^{-itT}` of an unbounded self-adjoint Hamiltonian commuting with `Ω`.
import BookProof.ChapterBrstReducedTransfer

-- Wave (2026-08-25h, plan §10.6.2 item 4 / QG Part F — the concrete 3D gauge-fixed
-- *gravity* Hamiltonian and its BRST charge).
--
-- `ChapterQuantumGravity3DGauge`: the gauge-fixed 3D gravity Hamiltonian written on the
-- Gauss–polynomial core of `L²(ℝ⁸⁴)` (`84 = 4 + 16 + 64` densitized-tetrad coordinates),
-- with the Weyl-ordered coordinate/momentum products, the canonical commutation relations
-- `[x_j, π_k] = i δ_{jk}`, symmetry of the Hamiltonian on the core and the Friedrichs
-- extension of its elliptic (positive-signature) truncation.  The physical signature is
-- indefinite, so no Friedrichs claim is made for the full operator.
import BookProof.ChapterQuantumGravity3DGauge

-- `ChapterQuantumGravityBrstCharge`: the BRST charge of that field space.  The abstract
-- theorem `brst_full_nilpotent` gives `Ω² = 0` for `Ω = Σ_a G_a χ_a − ½ Σ f_{abe} χ_a χ_b β_e`
-- whenever the constraints close into a Lie algebra with real structure constants obeying
-- the Jacobi identity.  It is instantiated on `ℂ[x₀,…,x₈₃] ⊗ Λ(ℂ¹⁹)` — the polynomial core
-- tensored with the `ℤ₂¹⁹` ghost occupation space — with the `gl(84)` constraint generators
-- `x_j ∂_k`, and specialized to a concrete non-abelian family (`aff(1)`), so the
-- construction is not vacuous.
import BookProof.ChapterQuantumGravityBrstCharge

-- Wave (2026-08-26, plan §10.6.1 / §10.6.2 item 2 — the `R + αR²` Hamiltonian on the
-- *compactly supported smooth* core).
--
-- `ChapterQgOneParticleCcEsa`: essential self-adjointness of `−Δ + ‖x‖²/4 + V` on the core
-- `C_c^∞(ℝᵈ)` of `L²(ℝᵈ)`, for every smooth `V` dominated by `a‖x‖²/4 + b` with `a < 1`.
-- The Gauss–polynomial (Hermite) core statement of `ChapterHermiteQuadraticEsa` is
-- transported down to the smaller compactly supported core by a graph-norm cut-off
-- argument (`deficiencyTrivialAt_of_graphApprox`, `exists_cc_graph_approx`), which is what
-- the applications and the second quantisation use: the conformal mode (`confVCc_esa`), the
-- reduced `(R_c, φ)` sector (`sectorQuadCc_esa`), the `n`-particle sector
-- (`qgNParticleCc_esa`) and the finite-particle Fock space (`qgFockCc_esa`), each with its
-- Stone flow.  The exponentially growing scalaron wall is not covered — only the quadratic
-- potential class that the Hermite core provides.
import BookProof.ChapterQgOneParticleCcEsa

-- Wave (2026-08-26b, plan §10.6.2 item 3 / QG Part E — the graded Fock space).
--
-- `ChapterQuantumGravityFock`: the book's graded quantum-gravity Fock space
-- `Γˢ(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴×ℤ₂¹⁹))`.  The bosonic half is reused from
-- `ChapterFockSecondQuantization`; the new content is the fermionic (ghost) half and the
-- `ℤ₂` grading: the Jordan–Wigner sign, the ladder operators `fermAnn`/`fermCre` with the
-- canonical anticommutation relations (`car_fermAnn_fermCre`, `car_fermAnn_fermCre_of_ne`,
-- `car_fermAnn_fermAnn`, `car_fermCre_fermCre`) and the adjoint pairing
-- (`inner_fermCre_left`), the parity operator `fermGrade` with the oddness of the ladder
-- operators, the graded bracket `superBracket`, the graded state space `QGGraded` with
-- `qgCCR` / `qgGhostCar`, and the graded Fock Hamiltonian `qgGradedHam` — essentially
-- self-adjoint (`qgGradedFock_esa`) with its unitary group (`qgGradedFock_stone_flow`) and
-- no positivity or boundedness assumption on the boson or ghost energies.
import BookProof.ChapterQuantumGravityFock

-- Wave (2026-08-26c, plan §10.6.2 item 4 — the last join): a **bounded** nilpotent BRST
-- charge on the *completed* graded Hilbert space `ℓ²(GradedIdx)`, so that the reduced
-- transfer of `ChapterBrstReducedTransfer` (which needs a bounded charge on a complete
-- space) applies to a concrete gravity object.
--
-- `ChapterQgBrstCompleted`: a bounded weighted-shift calculus on `ℓ²` (`wshift`), the
-- dressed ghost creation operators `brstTerm` with `brstTerm_comp_self` /
-- `brstTerm_anticomm`, the charge `qgBrstCharge` with `qgBrstCharge_nilpotent` and
-- `qgBrstCharge_ne_zero`, the commuting unitary group `qgPhase` (`qgPhase_zero`,
-- `qgPhase_group`, `qgPhase_isometry`, `qgPhase_comm_brst`, `qgPhase_single`) and the
-- reduced transfer `qgBrstTransfer` with `qgPhase_mem_physicalStates`,
-- `qgBrstTransfer_comp`, `qgBrstTransfer_bijective` and `qgBrstTransfer_infDist`.
import BookProof.ChapterQgBrstCompleted

-- Wave (2026-08-26d, plan §10.6.1 / §10.6.2 item 2 — the exponential scalaron wall).
--
-- `ChapterWeakSecondDerivative`: a self-contained one-dimensional distributional regularity
-- toolkit — the du Bois-Reymond lemmas (`ae_eq_const_of_integral_deriv_smul_eq_zero`,
-- `ae_eq_affine_of_integral_deriv2_smul_eq_zero`), integration by parts against the
-- primitive of a merely locally integrable function
-- (`integral_deriv_mul_indefiniteIntegral`) and the regularity theorems
-- `exists_ae_eq_doubleAntideriv_add_affine` / `exists_deriv2_of_weak_eq`: an `L¹_loc` weak
-- solution of `u'' = c·u` with continuous `c` agrees a.e. with a genuine `C²` solution.
--
-- `ChapterScalaronWallEsa`: with that regularity in hand, the *non-perturbative* route to
-- the Starobinsky wall.  `−d²/dx² + V` is essentially self-adjoint on the compactly
-- supported smooth core of `L²(ℝ)` for **every** smooth `V ≥ 0`
-- (`wallHam_essentiallySelfAdjoint`), with no growth hypothesis: a deficiency vector solves
-- `W'' = (V ∓ i)W`, so `|W|²` is convex, non-negative and integrable, hence zero
-- (`eq_zero_of_convexOn_nonneg_integrable`, `ode_solution_eq_zero`).  This covers the
-- exponentially growing scalaron potential (`starobinskyWall_esa`,
-- `starobinskyWall_stone_flow`), which no perturbative comparison with the harmonic core
-- can reach (`ChapterHermiteExpWall`).
import BookProof.ChapterWeakSecondDerivative
import BookProof.ChapterScalaronWallEsa
