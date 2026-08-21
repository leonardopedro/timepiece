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
