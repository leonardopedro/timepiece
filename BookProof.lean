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
import BookProof.ChapterScalaronEdge
import BookProof.ChapterVielbeinFiberFock
import BookProof.ChapterQedFockGapChain
import BookProof.ChapterNavierStokesFiberGap

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
-- Sums of one-particle Hamiltonians in **differing bases** (plan QG-3.2-exec): a coupling
-- built from one-particle Hermitian operators conserves the particle number, so its
-- commutator form against the *diagonal* comparison operator `N = dΓ(ω) + 𝒩 + 1` vanishes
-- identically.  Faris–Lavine then applies with commutator constant `0`, and the weighted
-- gate of `ChapterFockQuadraticEsa` degrades to the unweighted `∑ₖ ‖gₖ‖ < ∞`: a family of
-- one-particle operators, each diagonal in **its own** basis and none in the working
-- alphabet, is essentially self-adjoint on the finite-particle core.  Includes the nested
-- Fock-space instantiation and the non-commutativity witness.
import BookProof.ChapterFockDifferingBasesEsa
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

-- `ChapterSirkRitzMinMax`: the higher Rayleigh–Ritz levels and the Ritz gap (plan §12
-- Gap 2, QYM).  The Courant–Fischer min–max levels of a bounded operator, the levels
-- computed inside a Galerkin truncation, and the convergence of the latter to the former
-- — hence convergence of the computed gap to the min–max gap.
import BookProof.ChapterSirkRitzMinMax

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
import BookProof.ChapterQgPhysicalSectorIdentity
-- `ChapterQgCouplingDGammaSum` (plan QG-3.2-exec (i)): the coupling sum in differing
-- bases — second quantization is additive in the one-particle datum, so the lifted
-- coupling is a single `dΓ`, with an unconditional Friedrichs extension and essential
-- self-adjointness on the finite-occupation core whenever the *total* one-particle
-- operator is diagonal in the working basis.
import BookProof.ChapterQgCouplingDGammaSum
-- `ChapterConformalSignFlip` (plan QG-2 / 29f Case B): the sign bookkeeping of the
-- densitized conformal direction — `H ↦ −H` reflects the spectral parameter, essential
-- self-adjointness is invariant under it, and a real shift only translates the parameter.
-- So the wrong-sign-kinetic fiber `−K + V` is ESA iff the positive-kinetic `K − V` is.
import BookProof.ChapterConformalSignFlip
-- `ChapterDirectSumEdge` (plan QG-3.4, derived case): the edge of an orthogonal direct
-- sum.  On the algebraic direct sum of the fibre cores both the squared norm and the
-- energy are finite sums over the support, so fibre form bounds `⟪u, Hᵢu⟫ ≥ νᵢ‖u‖²` glue:
-- any common lower bound `ν ≤ νᵢ` is an edge of `⊕ᵢHᵢ`, strict when `ν > 0`.
import BookProof.ChapterDirectSumEdge
-- `ChapterQgMultiHalfDensity` (plan QG-1): the multi-dimensional half-density unitary.
-- The densitized change of variables `(y, ξ) ↦ (y², ξ)` — the conformal coordinate
-- squared, all other field directions untouched — is measure preserving from `(2y dy) ⊗ μ`
-- to `de ⊗ μ`, hence a Hilbert-space unitary of the corresponding `L²` spaces; it carries
-- the bounded-energy cores onto each other, intertwines the physical and densitized
-- multiplication operators, and so runs the Part D.4 transfer on the field space.
import BookProof.ChapterQgMultiHalfDensity

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

-- Wave (2026-08-26g, plan §13 — the certified numerical bounds and the mass gap).
--
-- `ChapterSirkFinitePrecision`: the finite-precision certificate layer (T1–T5).  The
-- Rayleigh–Ritz residual bound `exists_eigenvalue_dist_le_residual` (Parlett: the
-- *computed* vector against the *exact* operator), the eigendecomposition backward
-- error with Weyl in enclosure form (`backward_error_weyl`,
-- `backward_error_weyl_symm`), the unconditional Ritz upper bound
-- `ground_le_rayleigh` and its honest lower-bound counterpart `temple_lower_bound`
-- (Temple's inequality — the informal `λ₀ ≥ θ − ‖r‖` is not valid on its own), the
-- Cauchy–Schwarz observable propagation `observable_propagation(_band)` and the
-- interval-enclosure core `CertInterval` with its arithmetic soundness theorems.
--
-- `ChapterSirkCertifiedGap`: the certified mass gap of the *truncated* Hamiltonian
-- (T6, T7).  The parity split as an exact symmetry (`paritySector`,
-- `paritySector_invariant`, `sectorRestrict_isSymmetric`), the sector ground energy
-- `sectorGround` with its spectral identification `sectorGround_eq_inf_eigenvalues`,
-- Temple inside a sector (`sectorGround_ge_temple`), the certified-gap theorem
-- `certified_parity_gap` with `certified_parity_gap_pos`, the nested-selection block
-- lemma `resolvent_commutes_parity` / `resolvent_mapsTo_paritySector`, the stopping
-- rule `certifiedGap_tendsto` / `certifiedGap_eventually_pos` / `certifiedGap_sound`,
-- and the instantiation from an emitted certificate (`GapCertificate`,
-- `qcdG2M4_certified_gap`).  The continuum (gap-preserving norm-resolvent) leg stays
-- the recorded boundary: every statement is about the finite-dimensional truncation.
import BookProof.ChapterSirkFinitePrecision
import BookProof.ChapterSirkCertifiedGap

-- Wave (2026-08-27, plan §12.4 — the per-system end-to-end SIRK bound).
--
-- `ChapterSirkPerSystemFlowBound`: the composition of `ChapterSirkEndToEnd` (the assembly,
-- Gap 1) with `ChapterSirkPerSystem` (the Crouzeix domain of each physical shift-invert,
-- Gap 2) into one named flow-error theorem per system — `ym_sirk_flow_error_bound` (QYM,
-- the Friedrichs route, `Σ = [0, γ⁻¹]`), `ns_sirk_flow_error_bound` and
-- `nsDiff_sirk_flow_error_bound` (NS Eulerian, sequence space and differential),
-- `lagrangian_sirk_flow_error_bound` / `diagKR_sirk_flow_error_bound` (NS Lagrangian) and
-- `qgR2_sirk_flow_error_bound` (QG) — plus the `m → ∞` convergence corollaries
-- `ym_sirk_flow_error_tendsto_zero` / `qgR2_sirk_flow_error_tendsto_zero`.  The order-`m`
-- data is bundled as `RationalScheme` / `IsSirkScheme` (non-vacuous:
-- `isSirkScheme_trivial`), and the two adjoint side conditions the earlier statements
-- carried are now derived from isometry alone (`adjoint_comp_self_of_isometry`,
-- `norm_adjoint_apply_le_of_isometry`).  Crouzeix's inequality and the `e^{−hm}`
-- deformation remain named hypotheses (fields `cxX`, `cxB`), never axioms.
import BookProof.ChapterSirkPerSystemFlowBound

-- Wave (2026-08-27, attached plan: essential self-adjointness of `-Δ + V` for a fast-growing,
-- non-polynomial potential by the Simader–Faris–Lavine cutoff/commutator energy method).
--
-- `ChapterSchrodingerCutoffEsa`: the one-dimensional cutoff argument, carried out with no
-- unproved input.  It supplies the plan's Milestone 2 (the operator `-f'' + V f` on the
-- compactly supported twice-differentiable core, and its symmetry `schrodingerOp_symmetric`),
-- Milestone 3 (the rescaled smooth cutoff with `|χ_R'| ≤ C/R`, `exists_scaled_cutoff`),
-- Milestone 4 (`cutoff_energy_estimate`: `∫_{[-R,R]} |u|² ≤ (2C²/R²)‖u‖²_{L²}` for a
-- square-integrable classical solution of `-u'' + V u = z u` with `Re z + 1 ≤ V`) and
-- Milestone 5 (`l2_classical_solution_eq_zero`: the limit `R → ∞`).  Milestone 1, the abstract
-- Hilbert-space criterion, is already in the project as `EssentiallySelfAdjointOn` /
-- `DeficiencyTrivialAt` of `BookProof.ChapterFarisLavine`, so it is not duplicated here.
-- The application is `schrodinger_exp_deficiency_trivial` for `V(x) = eˣ + e⁻ˣ`.
import BookProof.ChapterSchrodingerCutoffEsa

-- Also from that wave: the plan's headline object as an actual essential-self-adjointness
-- statement.  `ChapterExpPotentialEsa` verifies that `V(x) = eˣ + e⁻ˣ` is smooth and bounded
-- below and reads off `expPotential_esa` — `-d²/dx² + (eˣ + e⁻ˣ)` is essentially self-adjoint
-- on the compactly supported smooth core of `L²(ℝ)` — together with its unitary flow
-- `expPotential_stone_flow` and the `cosh` restatement `coshPotential_esa`, from the
-- no-growth-restriction theorem `wallHam_essentiallySelfAdjoint_of_bddBelow` already in the
-- project.
import BookProof.ChapterExpPotentialEsa

-- And the packaging lemma §9 item 1 of `CONSOLIDATED_PLAN.md` asked for.
-- `ChapterWallEsaSemibounded` supplies the Green identity on the compactly supported smooth
-- core (`⟪(-d²/dx² + V) f, f⟫ = ∫ |f'|² + ∫ V |f|²`, one integration by parts) and reads off
-- `wallHamBddBelow_semibounded`: if `V ≥ -c` then the quadratic form of `wallHam V hV` is
-- bounded below by `-c`.  This is the semiboundedness the Hashimoto/SIRK shift-invert schemes
-- work with, promised by the `ChapterWallEsaBddBelow` docstring and previously absent.
import BookProof.ChapterWallEsaSemibounded

-- Wave (2026-08-27d, plan §13.7 — the instantiation seam and the table around T6).
--
-- `ChapterSirkCertificateReader` (T8): the reader that was missing between the kernel's
-- certificate emitter and the Lean T6 theorem.  Decimal literals are parsed *exactly*
-- (`Decimal`, `parseDec`: a mantissa and a power of ten, so `-0.4231` is `-4231/10^4`) —
-- no `Float` appears anywhere — and `parseCertificate` turns emitted NDJSON into the two
-- sector records, from which `ndjsonLower` reads the certified lower bound
-- `θᵒ − θᵉ − (δᵒ + δᵉ)`.  `gap_ge_of_ndjson` / `gap_pos_of_ndjson` are T6 consumed through
-- the reader: conditional on the enclosures the certificate asserts, and about the
-- truncated operator only.  `formatExample_parse` / `formatExample_lower` /
-- `formatExample_certified_gap` work the wire format through end to end on the recorded
-- `g = 2`, `m = 4` aggregates (measured gap 1.9875, width 0.0555, lower bound 1.932).
import BookProof.ChapterSirkCertificateReader

-- `ChapterSirkGapTable` (T11, T12): the table around T6 and the finite-size extrapolation.
-- `gap_le_of_certificate` adds the upper half of T6, so with the reverse enclosures a
-- certificate *encloses* the gap (`certified_gap_mem_interval`); `certified_gap_table` and
-- `certified_gap_table_interval` state that per coupling constant, and
-- `qcdG2M4_strongCoupling_consistent` checks the one recorded row against the analytic
-- strong-coupling value (`g²/2 = 2` does lie in the certified window `[1.932, 2.043]`).
-- `richardson`, `richardson_exact` and `richardson_error` are the conditional
-- Richardson-extrapolation theorem the plan asks for (with the plan's ratio corrected to
-- `(l₂/l₁)^p − 1`); the evaluation `richardson_qym_g4` on the recorded finite-size data is
-- a numerical record, not a claim about the thermodynamic limit.
import BookProof.ChapterSirkGapTable

-- `ChapterSpectralGapStability` (plan §13.7, the continuum leg — its abstract core).  The
-- quantitative gap `GapAt A lam d` (`d‖x‖ ≤ ‖Ax − λx‖`) degrades by at most the
-- perturbation (`gapAt_perturb`) and survives an operator-norm limit with no loss at all
-- (`gapAt_of_tendsto`); for a bounded self-adjoint operator a positive quantitative gap at a
-- real `λ` keeps `λ` out of the spectrum (`notMem_spectrum_of_gapAt`, proved from
-- injectivity, closed range and symmetry).  Together:
-- `notMem_spectrum_of_uniform_gap` and `spectrum_disjoint_of_uniform_window` — a uniform gap
-- of the approximants is inherited by the limit.  This is the implication the continuum leg
-- needs; whether the truncation family converges in the required sense is the open analytic
-- question and is asserted nowhere.
import BookProof.ChapterSpectralGapStability

-- `ChapterFockOneParticleGap` (CONSOLIDATED_PLAN.md, top work package — "Hashimoto
-- observable to the real-Hamiltonian gap").  The **one-particle** observable and its free
-- nested-Fock lift, in the algebraic Fock space of `ChapterFockSecondQuantization`.  For a
-- one-particle Hamiltonian diagonal in the chosen basis (`diagCol e`, the free
-- outer-particle hypothesis) the second quantization is diagonal on configurations with
-- eigenvalue `Σ_k β_k e_k` (`dGamma_diagCol_single`, `dGamma_diagCol_apply`); the vacuum has
-- energy zero (`dGamma_diagCol_vac`, `numberOp_vac`); a one-particle creation has energy
-- exactly `e k` (`dGamma_diagCol_one_particle`, `fock_energy_one_particle`); the further
-- shift `h₊ ↦ h₊ + μ` is exactly the number-operator shift `dΓ(h₊) + μN`
-- (`dGamma_diagCol_shift`).  Hence the **free `dΓ` lift**: with `h₊ ≥ μI ≥ 0` every
-- vacuum-orthogonal finite-particle state has Fock energy at least `μ‖·‖²`
-- (`fock_gap_quadForm`, `fock_gap_of_one_particle_gap`).  Nested certified bands with
-- vanishing widths that all enclose the lowest positive one-particle energy of one *fixed*
-- operator determine it (`band_endpoints_tendsto`, `le_of_band`), and the composition is
-- `fock_mass_gap_of_certified_bands`, instantiated at the recorded `g = 2, m = 4`
-- certificate number in `qcdG2M4_fock_gap_of_one_particle_enclosure`.
-- `sInf_nonvacuumEnergies` identifies the free Fock gap with the one-particle edge;
-- `fock_gap_of_operator_spectral_edge` and `fock_mass_gap_of_certified_bands_operator` run
-- the same argument from a bounded self-adjoint one-particle operator with an eigenbasis,
-- with the bands enclosing `sInf (spectrum ℝ A)`; and
-- `one_particle_edge_ge_of_parity_certificate` makes the parity-to-one-particle
-- representation translation an explicit hypothesis rather than an appeal to a generic
-- parity gap.  The enclosure of the *infinite* operator's one-particle edge by the finite
-- certificate is a hypothesis of these theorems, never a conclusion: `1.932` remains a
-- certified truncated number and no mass gap of the physical Hamiltonian is claimed.
import BookProof.ChapterFockOneParticleGap

-- `ChapterFriedrichsFormGap` (CONSOLIDATED_PLAN.md, top work package).  The **infinite**
-- selected operator inherits the lower bound of its core: if the densely defined positive
-- symmetric Hamiltonian satisfies `⟪x, H x⟫ ≥ μ‖x‖²` on its domain, the Friedrichs
-- extension constructed in `ChapterFriedrichsExtension` — the operator whose Hashimoto
-- shift-invert at `γ = 1` is the resolvent `S`, i.e. the operator the algorithm selects —
-- satisfies `⟪y, A y⟫ ≥ μ‖y‖²` on its whole domain (`friedrichs_extension_form_gap`).  The
-- proof is carried out in the form completion (`formSpace_norm_bound`); no boundedness and
-- no spectral theorem for unbounded operators are used.
import BookProof.ChapterFriedrichsFormGap

-- `ChapterBandEnclosure` (CONSOLIDATED_PLAN.md, top work package).  **The band-enclosure
-- hypothesis of `ChapterFockOneParticleGap`, derived.**  `NestedBands` abstracts the
-- already-proved band containment (`ChapterH8.sirk_band_contained`); the key theorem
-- `band_enclosure_of_nested` shows that if the order-`m` approximant lies in the order-`m`
-- band and the approximants converge, then the limit lies in *every* band, since for
-- `n ≥ m` the order-`n` band is inside the order-`m` one, which is closed.  With vanishing
-- widths the enclosed point is unique and the endpoints converge to it
-- (`band_limit_unique`, `band_enclosure_endpoints_tendsto`); the exponentially shrinking
-- SIRK bands are the recorded instance (`sirk_nestedBands`,
-- `sirk_band_widths_tendsto_zero`, `sirk_band_enclosure`).  Feeding in the
-- Hashimoto/Galerkin Ritz values and their convergence theorems gives the enclosure for the
-- *selected* operator: `ritz_band_enclosure_of_nested` (bounded regime, edge
-- `sInf (spectrum ℝ A)`) and `fock_mass_gap_of_nested_ritz_bands`, which composes it with
-- the free `dΓ` lift so that no enclosure hypothesis remains; and, with no boundedness at
-- all, `friedrichs_form_gap_of_nested_ritz_bands`, where the certified bands enclose the
-- form bottom of the core and the Friedrichs extension inherits the bound.
-- `shiftInvert_band_enclosure` transports a band enclosure through `lam = nu⁻¹ − γ`.
import BookProof.ChapterBandEnclosure

-- `ChapterRitzCertificate` (CONSOLIDATED_PLAN.md, top work package).  **The per-order
-- finite certificate, derived.**  The 2026-08-28 wave left the emitter's two claims as
-- inputs: that the order-`m` Ritz value lies in the order-`m` band, and that the bands
-- nest.  Both are proved here.  *The band*: for a bounded self-adjoint `A`, a unit Ritz
-- vector `x` with Rayleigh quotient `θ` and residual `ε` brackets the spectral edge by
-- itself — `sInf (spectrum ℝ A) ≤ θ` (Rayleigh–Ritz, `sInf_spectrum_le_rayleigh`) and, by
-- **Temple's inequality** `temple_lower_bound`, `sInf (spectrum ℝ A) ≥ θ − ε²/(β − θ)`
-- whenever the spectrum below `β` is the edge alone (`SpectralSeparation`); the positivity
-- of the Temple factor `(A − λ₁)(A − β)` comes from the continuous functional calculus
-- (`factor_nonneg`).  Both endpoints are finite-computation outputs, so `temple_band_mem`
-- is an *emitted* band that encloses the edge of the infinite operator by theorem.  *The
-- nesting*: `runLo`/`runHi`, the running intersection of any family of bands, is nested by
-- construction (`runBands_nested`), still encloses (`mem_runBand`) and is no wider
-- (`runBand_width_le`, `runBand_widths_tendsto_zero`).  Composed:
-- `temple_nested_certificate` and `fock_mass_gap_of_temple_certificates`, a Fock mass gap
-- for the free second quantization from finite Rayleigh/residual data with no band
-- hypothesis at all.
import BookProof.ChapterRitzCertificate

-- `ChapterFockNumberPreservingGap` (CONSOLIDATED_PLAN.md, top work package).  **The `dΓ`
-- lift beyond the diagonal case.**  The free lift of `ChapterFockOneParticleGap` assumed a
-- one-particle Hamiltonian diagonal in the occupation-number basis; only *number
-- preservation* is really needed.  `shiftCol` is the shifted one-particle matrix `h − μ`,
-- `dGamma_shiftCol` proves `dΓ(h − μ) = dΓ(h) − μN` for an arbitrary matrix (via
-- `creVec_sub`, `creVec_smul`), `dGamma_vac` annihilates the vacuum for every matrix, and
-- `number_quadForm_ge` gives `⟪u, N u⟫ ≥ ‖u‖²` on vacuum-orthogonal states.  Hence
-- `fock_gap_of_number_preserving`: a one-particle gap in the numerically checked form
-- `h − μ ≥ 0` yields Fock energy `≥ μ‖u‖²` on every vacuum-orthogonal finite-particle
-- state, with no diagonalization and no eigenbasis; `fock_gap_of_number_preserving_op` is
-- the Fock-space form, `isPosCol_shiftCol_diagCol` shows the diagonal case is an instance,
-- and `fock_gap_of_one_particle_form_gap` consumes exactly the form bound
-- `⟪x, h x⟫ ≥ μ‖x‖²` that the certificate chain produces.  Pair creation and other
-- particle-number-changing terms remain excluded.
import BookProof.ChapterFockNumberPreservingGap

-- `ChapterFockInteractionStability` (CONSOLIDATED_PLAN.md, top work package).  **How far a
-- gap survives a number-changing interaction.**  The `dΓ` route still assumes the Fock
-- Hamiltonian preserves particle number; this chapter replaces that qualitative hypothesis
-- by a quantitative one.  `gap_persists_of_relative_form_bound` is the abstract statement:
-- if the unperturbed form has gap `μ` on a set `S` and the perturbing form satisfies
-- `|v x| ≤ a q x + b‖x‖²` with `a ≤ 1`, the perturbed form has gap `(1 − a)μ − b` on `S`,
-- with `gap_persists_of_bounded_form` the `a = 0` case and `gap_persists_pos` the condition
-- for the surviving gap to be strictly positive.  `interaction_form_bound` bounds a bounded
-- operator's form by its norm, and `fock_gap_of_bounded_interaction` /
-- `fock_gap_of_one_particle_form_gap_interaction` apply this to `dΓ(h) + V` with `V` an
-- **arbitrary** bounded operator on Fock space — nothing forces `V` to commute with the
-- number operator, so pair creation is permitted, and the gap `μ − ‖V‖` survives.  This is
-- a perturbative statement only: the physical interaction terms are unbounded, and no mass
-- gap of the physical Hamiltonian is claimed.
import BookProof.ChapterFockInteractionStability

-- `ChapterTempleSeparationNecessary` (CONSOLIDATED_PLAN.md, top work package).  **The
-- spectral-separation input of Temple's inequality cannot be removed.**  `separation_necessary`
-- exhibits, for every `M`, a bounded self-adjoint operator on a two-dimensional Hilbert space
-- and a unit trial vector whose Rayleigh quotient and residual both vanish — an exact
-- eigenvector, the best finite data possible — while `sInf (spectrum ℝ A) ≤ -M`.  So no lower
-- bound on the spectral edge in terms of `rayleigh` and `resid` alone can be valid, and the
-- a priori hypothesis `RitzCertificate.SpectralSeparation` is a genuine side condition rather
-- than an artifact of the proof.
import BookProof.ChapterTempleSeparationNecessary

-- `ChapterFockFieldPerturbation` (CONSOLIDATED_PLAN.md, top work package).  **A genuinely
-- unbounded, genuinely number-changing perturbation.**  `ChapterFockInteractionStability`
-- leaves the relatively-form-bounded statement without a supplied domination; this chapter
-- supplies one for the field operator `Φ(f) = a†(f) + a(f)`.  `norm_annVec_le` is the
-- `N^{1/2}` estimate `‖a(f) u‖ ≤ ‖f‖⟪u, N u⟫^{1/2}`, `abs_re_inner_fieldVec_le` the form
-- estimate, `fieldVec_relative_form_bound` the domination
-- `|Re⟪u, Φ(f) u⟫| ≤ (t/μ)Re⟪u, dΓ(h) u⟫ + (‖f‖²/t)‖u‖²`, and
-- `fock_gap_of_field_perturbation` the resulting gap `(μ − 2‖f‖)‖u‖²` on vacuum-orthogonal
-- states.  `fieldVec_vac` and `fieldVec_unbounded` record that `Φ(f)` neither preserves the
-- particle number nor is bounded, so this is not a corollary of the bounded theory.  The
-- perturbation is linear in the field; cubic and quartic Yang–Mills terms are not covered,
-- and no mass gap of the physical Hamiltonian is claimed.
import BookProof.ChapterFockFieldPerturbation

-- `ChapterYangMillsFockGapChain` (CONSOLIDATED_PLAN.md, "Next specialist package —
-- instantiate the abstract gap chain").  **The abstract chain, instantiated for the concrete
-- gauge-fixed Yang–Mills one-particle Hamiltonian.**  `isPosCol_shiftCol_opCol_of_form_gap`
-- turns a one-particle *form* gap on the finite-mode core into the matrix condition
-- `h − μ ≥ 0`; `ym_fock_vacuum_annihilated` records unconditionally that the outer vacuum is
-- an exact zero-energy eigenstate of `dΓ(H₁)`; `ym_fock_gap_of_one_particle_form_gap` and
-- `ym_fock_mass_gap_of_one_particle_form_gap` lift a one-particle form gap for
-- `ymHamiltonian (coreRepBasis e) fabc` to the final nested-Fock Hamiltonian, the latter
-- together with the positive self-adjoint (Friedrichs) extension of
-- `ChapterFockSecondQuantization.ym_fock_friedrichs_extension`; and
-- `ym_fock_gap_of_field_perturbation` adds the unbounded number-changing field coupling of
-- `ChapterFockFieldPerturbation`.  `ym_fock_gap_of_nested_ritz_bands` feeds the certified
-- band data in through `BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands`, so that no
-- displayed Ritz value is read as a lower bound.  Everything is **conditional on the
-- one-particle form gap**, which is not proved: the SIRK/Hashimoto certificate remains a
-- finite-truncation statement and no mass gap of the physical Yang–Mills Hamiltonian is
-- claimed.
import BookProof.ChapterYangMillsFockGapChain

-- `ChapterFockPairPerturbation` (CONSOLIDATED_PLAN.md, top work package).  **The next degree:
-- a quadratic, pair-creating unbounded perturbation.**  `ChapterFockFieldPerturbation` covers
-- the linear coupling `Φ(f)`, which changes the particle number by one; this chapter covers
-- `P(f,g) = a†(f)a†(g) + a(g)a(f)`, which changes it by two.  `annVec_creVec` is the vector
-- canonical commutation relation `a(g)a†(g) = a†(g)a(g) + ‖g‖²`, `norm_creVec_sq` the exact
-- identity `‖a†(g)u‖² = ‖a(g)u‖² + ‖g‖²‖u‖²` and `norm_creVec_le` the `(N+1)^{1/2}` estimate
-- that a quadratic term needs.  `pairVec_relative_form_bound` dominates the pair form by the
-- free form with no additive remainder on vacuum-orthogonal states, and
-- `fock_gap_of_pair_perturbation` leaves the gap `(μ − 2√2‖f‖‖g‖)‖u‖²`;
-- `fock_gap_of_one_particle_form_gap_pair` and `ym_fock_gap_of_pair_perturbation` feed it from
-- the certificate chain and from the concrete gauge-fixed Yang–Mills datum.  `pairVec_vac` and
-- `pairVec_unbounded` record that the term is genuinely number-changing and genuinely
-- unbounded.  Cubic and quartic Yang–Mills interaction terms are still not covered, and no
-- mass gap of the physical Hamiltonian is claimed.
import BookProof.ChapterFockPairPerturbation

-- `ChapterFockCubicUnbounded` (CONSOLIDATED_PLAN.md, top work package).  **Where the
-- form-domination route stops.**  `ChapterFockFieldPerturbation` and
-- `ChapterFockPairPerturbation` keep a gap through a linear and a quadratic unbounded
-- coupling by dominating the perturbing form by the free form.  This chapter shows that the
-- boundary at degree two is real and not an artefact of the write-up: for the single-mode
-- cubic term `cubeA k = (a_k†)³ + (a_k)³`, `cubic_no_relative_form_bound` produces, for
-- *every* pair of constants `a, b`, a vacuum-orthogonal finite-particle state violating
-- `a·⟪u,Nu⟫ + b‖u‖² ≥ Re⟪u, C_k u⟫`, so the relative-form-bound hypothesis of
-- `ChapterFockInteractionStability.gap_persists_of_relative_form_bound` is unattainable at
-- degree three; and `fock_gap_fails_for_cubic` shows the consequence, that `dΓ(N) + lam·C_k`
-- is unbounded below on the vacuum-orthogonal sector for every `lam > 0`.  The witnesses are
-- the explicit two-term states `|n⟩ + c|n+3⟩`, whose number form, norm and cubic form are
-- computed exactly (`trial_numberQuad`, `trial_norm_sq`, `trial_cubic_form`).  `cubeA` is a
-- single-mode term, not the full Yang–Mills cubic vertex, and a physical cubic term comes
-- with a quartic term bounded below: `trial_cubic_quartic_bounded_below` makes that precise
-- along the same family, showing that adding `quartA k = (a_k†)²(a_k)²` restores the lower
-- bound `-(lam⁴/4 + 2lam²)‖u‖²`.  What is proved is that *this route* cannot reach degree
-- three, not that no gap exists.  No mass gap of the physical Hamiltonian is claimed.
import BookProof.ChapterFockCubicUnbounded

-- `ChapterFockCubicQuarticStability` (CONSOLIDATED_PLAN.md, top work package, next step 2).
-- The positive companion of `ChapterFockCubicUnbounded`, freed from its trial family: the
-- cubic term `C_k = (a_k†)³ + (a_k)³` and its normal-ordered quartic partner
-- `Q_k = (a_k†)²(a_k)²` are controlled together on *every* finite state.  The forms are
-- rewritten as norms — `quart_form_eq` (`Re⟪u, Q_k u⟫ = ‖a_k²u‖²`), `cubic_form_eq`
-- (`Re⟪u, C_k u⟫ = 2Re⟪a_k²u, a_k†u⟫`), `norm_creA_sq` (the single-mode CCR
-- `‖a_k†v‖² = ‖a_k v‖² + ‖v‖²`) and `sq_norm_annA_le_mul` (Cauchy–Schwarz
-- `‖a_k u‖² ≤ ‖u‖‖a_k†a_k u‖`) — and combined into
-- `mode_cubic_quartic_bounded_below` and `numberForm_cubic_quartic_bounded_below`:
-- `mu⟪u,Nu⟫ + lam·Re⟪u,C_k u⟫ + Re⟪u,Q_k u⟫ ≥ -(2lam² + (2lam² + ½ − mu)²/2)‖u‖²` for every
-- `mu ≥ 0`, every coupling `lam` and every finite `u`, with the `mu = 1` corollary
-- `trial_cubic_quartic_bounded_below_general`, the multi-mode sums
-- `multiMode_cubic_quartic_bounded_below` and
-- `dGamma_multiMode_cubic_quartic_bounded_below` — one copy of the free form pays for the
-- interaction of every mode in a finite set, the constant growing linearly in its
-- cardinality — and the one-particle-gap version `dGamma_cubic_quartic_bounded_below`.
-- Semiboundedness is not a gap: the constant is negative, and `C_k`, `Q_k` are single-mode
-- terms, not the physical Yang–Mills vertices.
import BookProof.ChapterFockCubicQuarticStability

-- `ChapterScalaronFockGapChain` (CONSOLIDATED_PLAN.md, top work package, next step 3):
-- the abstract gap chain instantiated for a sector whose one-particle energy is a positive
-- constant `m`, and then for the Starobinsky scalaron mass `m = 1/√(12α)` on the Hermite
-- basis of `L²(ℝ)`.  For the constant one-particle operator `constOnePart b m = m·1` the
-- one-particle form gap is an *identity* (`constOnePart_quadForm`), so every hypothesis the
-- Yang–Mills instantiation had to carry is discharged: `const_fock_gap` and
-- `const_fock_mass_gap` give `dΓ(m·1)Ω = 0`, the bound `Re⟪u, dΓ(m·1)u⟫ ≥ m‖u‖²` on
-- vacuum-orthogonal finite states and a positive self-adjoint (Friedrichs) extension;
-- `const_fock_gap_of_field_perturbation` keeps the gap `(m − 2‖f‖)` under the unbounded,
-- number-changing coupling `Φ(f)` when `2‖f‖ < m`; and
-- `const_fock_cubic_quartic_bounded_below` keeps the energy bounded below when the
-- single-mode cubic couplings and their normal-ordered quartic partners are added.
-- `scalaron_fock_mass_gap`, `scalaron_fock_gap_of_field_perturbation` and
-- `scalaron_fock_cubic_quartic_bounded_below` are the instantiations at
-- `scalaronMass α = 1/√(12α)`.  What is unconditional is the *lift*: that the `R²` sector's
-- one-particle operator is that constant is a modelling statement of the enclosure
-- doctrine, not a theorem here, and no claim about Yang–Mills is made.
import BookProof.ChapterScalaronFockGapChain

-- `ChapterFockDiagonalGapChain` (CONSOLIDATED_PLAN.md, top work package, next step 3): the
-- same chain for a *diagonal* one-particle energy, the shape the free sectors of the
-- enclosure doctrine have.  `modeBasis b` exhibits the finite-mode core as a free module on
-- the orthonormal family `b`, `diagOnePart b w` is the operator `e_k ↦ ω_k e_k`, and
-- `diagOnePart_inner` computes its sesquilinear form in coordinates; from that,
-- `diagOnePart_symmetricOn` and — the point — `diagOnePart_quadForm_ge`, the one-particle
-- form gap `⟪x, D x⟫ ≥ m‖x‖²` whenever every mode energy satisfies `ω_k ≥ m`.  Hence
-- `diag_fock_gap`, `diag_fock_mass_gap`, `diag_fock_gap_of_field_perturbation` and
-- `diag_fock_cubic_quartic_bounded_below` without any certificate hypothesis, and the free
-- massive instance `freeField_fock_mass_gap` at the relativistic dispersion
-- `freeDispersion m p k = √(p_k² + m²)`.  Massless dispersion gives `m = 0`, i.e. positivity
-- and no gap; that a physical sector is diagonal in the mode basis is a modelling input, not
-- a theorem here.
import BookProof.ChapterFockDiagonalGapChain

-- `ChapterGaussCoordCombo` (plan §state 28j next steps, item 1): the one-coordinate Hermite
-- calculus on the Gauss–polynomial core.  `gaussInt_hermiteFactor_mul` is the relative
-- orthogonality statement — the Gaussian integral of `He_m(x_i)He_n(x_i)R` vanishes when
-- `m ≠ n` and `R` does not involve `x_i` — and `coordCombo i c p K` is the finite Hermite
-- combination `Σ_{k≤K} c_k He_{2k+p}(x_i)` whose Gaussian square norm `gaussInt_coordCombo_sq`
-- computes.  `gaussInt_prod_coordFactor` multiplies such one-coordinate factors across a
-- finite set of coordinates.
import BookProof.ChapterGaussCoordCombo

-- `ChapterSqueezedGaussStates` (plan §state 28j next steps, item 1): truncated squeezed
-- states.  `squeezeState i v M` is the truncated Hermite expansion `Σ_{m≤M} (vᵐ/m!) He_{2m}(x_i)`
-- of a rescaled Gaussian, `op_squeezeState` computes `(αx_i + γ∂_i)` on it in closed form, and
-- `coordComboSum_opCoef_le` bounds the resulting Gaussian square norm by
-- `κ²/(1−4v²) + α²(2M+1)(4v²)^M` with `κ = α(1+2v) + 2γv`.  Hence `exists_position_small` and
-- `exists_momentum_small`: the position quotient `‖x_i Q‖²/‖Q‖²` and the momentum quotient
-- `‖(−x_i/2 + ∂_i)Q‖²/‖Q‖²` can both be made arbitrarily small on the core.
import BookProof.ChapterSqueezedGaussStates

-- `ChapterYangMillsAbelianNoGap` (plan §state 28j next steps, item 1): **the one-particle form
-- gap hypothesis of `ChapterYangMillsFockGapChain` is false in the abelian case.**  For
-- vanishing structure constants the gauge-fixed Yang–Mills quadratic form is
-- `½Σ‖π_m x‖² + ½Σ‖B_m x‖²` with momenta acting only on the 24 field coordinates and the
-- magnetic term linear in the momentum-free derivative coordinates; widening in the former and
-- narrowing in the latter drives the Rayleigh quotient to zero.  `exists_core_state_small_energy`
-- produces, for every `ε > 0`, a nonzero core state of energy at most `ε‖x‖²`, and
-- `ym_abelian_no_one_particle_form_gap` concludes that no `μ > 0` works.  This is a negative
-- result about `fabc = 0` only; it says nothing about the non-abelian case beyond the fact that
-- no proof of the hypothesis can be uniform in the structure constants.
import BookProof.ChapterYangMillsAbelianNoGap

-- `ChapterQgDerivativeRealization` (plan QG-3.2-exec (ii)): the concrete 84-dimensional
-- derivative-variable fixing `E = ∂e` on the coordinate algebra of
-- `ChapterQuantumGravity3DGauge`.  A tetrad field polynomial in the spacetime coordinates
-- together with the 64 promoted derivative fields determines a point `configPoint` of the
-- coordinate space (`configPoint_idxX/idxE/idxDE`, and `idx_cases`: the three index families
-- exhaust `Fin 84`).  `gaugeFieldPoly = E − ∂e` is the concrete `v − dφ`; its zero locus
-- `Fixed` is realized (`jetDeriv_fixed`), is not automatic (`exists_not_fixed`), and on it the
-- coordinate point is the 1-jet of the tetrad field (`configPoint_eq_jetPoint_of_fixed`).
-- Hence the torsion coordinate polynomial evaluates to the actual antisymmetrized derivative
-- (`eval_torsionPoly_jetPoint`), the tetrad–torsion cross coupling reduces to field values
-- (`eval_crossCouplingPoly_jetPoint`, non-vacuously by `couplingValue_ne_zero`), and *every*
-- coupling polynomial is determined by the tetrad field alone (`eval_eq_of_fixed_of_comp_eq` —
-- no new independent modes).  Section 4 builds the gauge-fixing system with the honest
-- exterior derivative `∂_μ`, in which `gaugeField = 0 ↔ E = ∂e`
-- (`qgFixing_gaugeField_eq_zero_iff`), and runs the abstract theorems of
-- `ChapterQgPhysicalSectorIdentity` with that hypothesis discharged.
import BookProof.ChapterQgDerivativeRealization

-- `ChapterSirkBandLedger` (plan QYM-1 task 1): the emitted certified bands are *nested
-- compatible* enclosures in the sense `ChapterBandEnclosure` requires.  A `BandRecord` carries
-- an operator tag, a mesh order and two exact decimal endpoints (no `Float` anywhere);
-- `parseLedger` reads the NDJSON band stream with the exact-decimal parser of
-- `ChapterSirkCertificateReader`; `ledgerLo`/`ledgerHi` adapt a finite ledger to the band
-- functions `ℕ → ℝ` the chain consumes.  `LedgerWf` is the decidable compatibility check —
-- same operator tag throughout, orders `0, 1, 2, …`, lower ends nondecreasing and upper ends
-- nonincreasing, every band an enclosure — and `nestedBands_of_wf` is the theorem.  Composing:
-- `ritz_band_enclosure_of_ledger` (every ledger band encloses the spectral edge of the selected
-- bounded operator) and `friedrichs_form_gap_of_ledger` (a certified form gap of the Friedrichs
-- extension, with no vanishing-width hypothesis, which is why a *finite* ledger suffices).
-- `ledger_width_tendsto_zero_iff` records what a finite ledger cannot certify: band collapse.
import BookProof.ChapterSirkBandLedger

-- `ChapterTruncationGapLift` (plan QYM-1 task 2): the bridge from a *certified truncated* gap
-- to the *infinite* one-particle operator, and on to the outer-enclosed final Hamiltonian.
-- `tailSpan b m` is the span of the basis vectors the order-`m` truncation never sees; it is
-- orthogonal to `galerkinSpan b m` (`inner_eq_zero_of_mem_galerkin_tail`) and together they
-- exhaust the finite-mode core (`galerkinSpan_sup_tailSpan`), so every core vector splits
-- as `v = x + w` with `‖v‖² = ‖x‖² + ‖w‖²`.  Two statements result.  The cheap one,
-- `gap_of_uniform_truncated_gap`: a gap holding at *every* order with the same `μ` gives the
-- core form gap with no analytic input.  The real one, `gap_of_level_gap_and_tail`: a gap
-- certified at a *single* order `m`, plus tail coercivity `⟪w, H w⟫ ≥ μ‖w‖²` on `tailSpan b m`
-- and a coupling bound `|Re⟪x, H w⟫| ≤ ε‖x‖‖w‖` across the split, gives the core form gap
-- `μ − ε` (`quadForm_add_of_symmetricOn` is the exact block identity behind it, so the
-- coupling term is not an error one may drop).  `quadForm_ge_of_le_ritzInf_on` converts a Ritz
-- bound on a truncation subspace into a form bound there, and
-- `ym_fock_gap_of_truncated_gap_and_tail`, `ym_fock_mass_gap_of_truncated_gap_and_tail` and
-- `ym_fock_gap_of_band_and_tail` compose the lift with the gauge-fixed Yang–Mills `dΓ` chain.
-- Honest boundary: tail coercivity and the coupling bound are *hypotheses* — the named
-- analytic input of QYM-1 task 3 — and are not proved for the Yang–Mills operator here.
import BookProof.ChapterTruncationGapLift

-- `ChapterSchurGershgorinGap` (plan QYM-1 task 3): the two analytic inputs of the lift, proved
-- from *matrix-element data*.  `entry b H i j = ⟪bᵢ, H bⱼ⟫` is the number a certificate records.
-- Gershgorin: if on an index set the diagonal entries are at least `dᵢ` and the off-diagonal
-- absolute row sums at most `rᵢ`, then the energy form is at least `inf (dᵢ − rᵢ)` times the norm
-- squared on the span of those modes (`quadForm_sum_ge`, `quadForm_ge_of_gershgorin_on`,
-- `quadForm_ge_of_gershgorin`); with the index set `{i | m ≤ i}` this is exactly the tail
-- coercivity the lift assumes (`tail_coercive_of_gershgorin`).  Schur: if every row sum and
-- every column sum of the off-diagonal block `{i < m} × {m ≤ j}` is at most `ε`, then
-- `|⟪x, H w⟫| ≤ ε‖x‖‖w‖` across the split (`abs_inner_block_le`, `coupling_bound_of_schur`) —
-- the coupling bound the lift assumes.  Composing with `gap_of_level_gap_and_tail` gives
-- `gap_of_level_gap_and_matrix_bounds` and the strict positivity `strict_pos_of_matrix_bounds`
-- (`λ₁(H₁|core) ≥ μ − ε > 0`), and `ym_fock_gap_of_truncated_gap_and_matrix_bounds` /
-- `ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds` run them through the gauge-fixed
-- Yang–Mills `dΓ` chain.  Honest boundary: what is proved is the *implication*; whether the
-- Yang–Mills entries satisfy the inequalities is a computation on the entries, not settled here.
import BookProof.ChapterSchurGershgorinGap

-- `ChapterWallDeficiencyObstruction` (plan QG-2, "Case B"): the converse of the ODE step of
-- `ChapterScalaronWallEsa`.  Double integration by parts against a compactly supported weight
-- (`integral_conj_deriv2_mul`) shows that a square-integrable classical solution of
-- `W'' = (V − z)W` (`IsL2Ode`) satisfies the deficiency identity `⟪Hv, W⟫ = z⟪v, W⟫` for every
-- `v` in the compactly supported smooth core (`inner_eq_of_ode`); hence a nonzero solution
-- obstructs triviality of the deficiency space (`not_deficiencyTrivialAt_of_l2_solution`) and,
-- with the regularity direction already proved, one gets the two-way Weyl characterisation
-- `deficiencyTrivialAt_iff_no_l2_solution` — the deficiency space *is* the space of `L²`
-- classical solutions, for every smooth real `V` and every `z`.  Consequences:
-- `isL2Ode_conj` (conjugation exchanges the two indices for real `V`),
-- `not_essentiallySelfAdjointOn_of_l2_solution` (one nonzero solution at `i` refutes ESA), and
-- `no_l2_solution_of_nonneg` (consistency with the `V ≥ 0` theorem).  The criterion is shown
-- non-vacuous by a worked instance: the Gaussian ground state of `V(x) = x² − 1`
-- (`gaussianState_isL2Ode`, `not_deficiencyTrivialAt_harmonicShifted_zero`).
import BookProof.ChapterWallDeficiencyObstruction

-- `ChapterLimitCircleExample` (plan QG-2 sign warning, Case B): the previous module's criterion
-- applied to an *explicit* potential.  Starting from the solution rather than the potential,
-- `W = e^{p+iq}` with `q'(x) = -(1+x²)/2` and `p(x) = arctan x - ½ log(1+x²)` makes the imaginary
-- part of `W''/W` identically `-1`, so `W` solves `W'' = (V - i)W` for the smooth real potential
-- `lcV x = (2x²-4x)/(1+x²)² - (1+x²)²/4` (asymptotically `-x⁴/4`, the classical limit-circle
-- profile), and `‖W x‖² = e^{2 arctan x}/(1+x²) ≤ e^π/(1+x²)` is integrable.  Hence
-- `lcSol_isL2Ode`, `lcV_not_deficiencyTrivialAt_I`, **`lcV_not_essentiallySelfAdjoint`** and
-- `exists_smooth_potential_not_essentiallySelfAdjoint`: essential self-adjointness on the
-- compactly supported smooth core genuinely fails for a smooth real potential, so the
-- non-negativity hypothesis of `wallHam_essentiallySelfAdjoint` is not removable.
import BookProof.ChapterLimitCircleExample

-- `ChapterConformalFiberDeficiency` (plan QG-2, Case B — the conformal fiber): the same
-- criterion applied to a potential of the *conformal-fiber profile*.  The wrong-sign
-- densitized conformal direction carries the non-negative Starobinsky exponential wall; after
-- the rescaling `-24·((1/24)d²/dy² + U + 1/32) = -d²/dy² + V` the potential
-- `V = -24(U + 1/32)` is unbounded below exponentially at `-∞` and constant at `+∞`.  Running
-- the ODE backwards with the exponential phase `q'(y) = 1 + e^{-y}` forces
-- `p(y) = -log cosh(y/2)`, so `W = e^{p+iq}` solves `W'' = (cfV - i)W` with
-- `‖W y‖² = 1/cosh²(y/2) ≤ 4/(1+y²)` integrable, where
-- `cfV y = 1/4 - 1/(2 cosh²(y/2)) - (1+e^{-y})²`.  Hence `cfSol_isL2Ode`,
-- `cfV_not_deficiencyTrivialAt_I`/`_negI`, **`cfV_not_essentiallySelfAdjoint`**, and the wall
-- form `cfWall_nonneg`, `cfWall_tendsto_atBot`, `cfWall_tendsto_atTop`, `cfV_eq_wall`,
-- packaged as `exists_wall_potential_wrongSign_not_essentiallySelfAdjoint`: a non-negative
-- exponential wall does *not* restore essential self-adjointness once the kinetic term carries
-- the conformal (wrong) sign.
import BookProof.ChapterConformalFiberDeficiency

-- `ChapterBddBelowWallEsa` (plan QG-2, Case A — the one-dimensional input): the sharp
-- companion of the two counterexamples above.  `ode_solution_eq_zero_of_bddBelow` replaces the
-- convexity argument of `ChapterScalaronWallEsa` (which needs `V ≥ 0`) by a cutoff energy
-- estimate: with `ζ_r(x) = g(x/r)` a rescaled bump, the compactly supported function
-- `ζ_r²·conj(W)·W'` integrates its derivative to zero, whose real part bounds the cutoff
-- kinetic energy `∫ζ_r²|W'|² ≤ 4M²‖W‖² + 2K‖W‖²` uniformly in `r` (this is the only place the
-- lower bound `V ≥ -K` is used), and whose imaginary part then gives
-- `|Im z|·∫ζ_r²|W|² ≤ (C + M²‖W‖²)/r → 0`, forcing `W = 0`.  Hence
-- `wallHam_deficiencyTrivialAt_of_bddBelow` and
-- **`wallHam_essentiallySelfAdjoint_of_bddBelow`**: `-d²/dx² + V` is essentially self-adjoint
-- on the compactly supported smooth core of `L²(ℝ)` for every smooth `V` bounded below, with
-- no growth and no sign hypothesis.  Together with `ChapterLimitCircleExample` and
-- `ChapterConformalFiberDeficiency` this makes the dichotomy sharp in the direction that
-- matters for the plan: a wall bounded below always closes the deficiency spaces, and once the
-- kinetic sign is wrong the wall is unbounded below and the conclusion genuinely fails.
import BookProof.ChapterBddBelowWallEsa

-- `ChapterBddBelowFiberSumEsa` (plan QG-2, Case A — the composed operator): the companion
-- of `ChapterBddBelowWallEsa`.  Each fibre `−d²/dx_i² + V_i` (with `V_i` smooth and bounded
-- below, each with its own constant) is glued into one operator on the orthogonal direct sum
-- `ℓ²(i : ι, L²(ℝ))`, `H = ⊕ᵢ (−d²/dxᵢ² + Vᵢ)`.  The gluing instrument is
-- `DirectSumEsa.dsOp_essentiallySelfAdjointOn` (a deficiency space of an orthogonal direct sum
-- is the direct sum of the fibre deficiency spaces), so no relative bound, comparison operator
-- or commutator estimate is needed: **`fiberSumHam_essentiallySelfAdjoint_of_bddBelow`**, the
-- unitary flow `fiberSumHam_stone_flow`, and under a *uniform* fibre lower bound the form bound
-- `fiberSumHam_semibounded`.  The physical instance of QG-3.3's derived fibre list is
-- `qgFiberSum_esa` (d shear directions with harmonic walls plus one scalaron direction with the
-- Starobinsky wall) and `qgFiberSum_nonneg_form`.  Honest boundary: the decomposition is an
-- orthogonal direct sum of one-dimensional fibres, not a tensor product — nothing here claims
-- `−Δ + V` on `L²(ℝᵈ)` — and the wrong-sign conformal direction is Case B, where the
-- conclusion is false (`ChapterConformalFiberDeficiency`).
import BookProof.ChapterBddBelowFiberSumEsa

-- `ChapterHalfLineLimitCircle` (plan QG-2 / 29f Case B — the endpoint): the *free* half-line
-- kinetic operator `−d²/dy²` on the compactly supported smooth core of `L²((0,∞))` is **not**
-- essentially self-adjoint.  The densitized conformal direction lives on the half line
-- `y = √e ∈ (0,∞)` (the degenerate-tetrad endpoint `e = 0`), and this module exhibits its
-- purest failure mechanism: `deficiencyFun y = exp(−λy)` with `λ² = −i` is square integrable
-- on `(0,∞)` and satisfies the adjoint deficiency identity `⟪−v'', w⟫ = i⟪v, w⟫` for every test
-- `v`, so **`hlKin_not_deficiencyTrivialAt_I`** and **`hlKin_not_essentiallySelfAdjointOn`**;
-- by the sign-flip theorem of `ChapterConformalSignFlip` also
-- `hlKin_neg_not_essentiallySelfAdjointOn` (the wrong-sign `+d²/dy²` the densitized direction
-- carries).  `hlCore_ne_bot` shows the core is not vacuous.  Honest boundary: what is proved is
-- the endpoint (limit-circle) mechanism for the *free* kinetic, not a potential `V(y)`, and not
-- a statement about the multi-dimensional densitized operator.
import BookProof.ChapterHalfLineLimitCircle
