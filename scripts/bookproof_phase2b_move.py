#!/usr/bin/env python3
"""BOOKPROOF_SPLIT_PLAN.md Phase 2.2b: folder the operator-core residue ("Other").

Phase 2.2 (`scripts/bookproof_phase2_move.py`) moved only the modules that a §2 *name*
family classifies, and left 237 operator-core modules flat because assigning them needs a
reading of each module (§1 "measurement first").  This script is the record of that
reading: every residue module's header (`/-! # … -/` title and the chapter it cites) was
read and the module assigned, by hand, to a §2 area.  The table below *is* the decision;
nothing here is inferred from names at run time.

Areas are the §2 folders, including `Probability/` (the measure / Born / Bayes / prior /
abelian-classification material).  One module stays flat by decision:
`RandomMap2Audit` (a quarantine audit of the RandomMap2 track, not BookProof content).

The rewriting is the Phase 1 recipe (`scripts/bookproof_phase1_move.py`).

Usage:  python3 scripts/bookproof_phase2b_move.py [--dry-run]
"""
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_components as ic  # noqa: E402
from bookproof_phase1_move import apply_moves  # noqa: E402

# area -> modules (names without the `BookProof.` prefix), from reading each header.
AREAS = {
    "Probability": """
        ChapterAbelianAtomicCondensation ChapterAbelianClassificationList
        ChapterAbelianCyclicCommutant ChapterAbelianCyclicModel ChapterAbelianDiagonal
        ChapterAbelianDiagonalCountable ChapterAbelianDirectSum ChapterAbelianGelfandModel
        ChapterAbelianMixture ChapterAtomicDecomposition ChapterAtomicDiagonalModel
        ChapterBayesInference ChapterBornMeasure ChapterConservativeDiagonal
        ChapterContinuityUnitary ChapterContinuityUnitaryInfinite
        ChapterCyclicDecomposition ChapterCyclicDirectSum ChapterDiffuseCdfModel
        ChapterDiffuseUnitaryModel ChapterDoubleSlit ChapterFiniteBayesHierarchy
        ChapterFreeFieldBorn ChapterFreeFieldBornCont ChapterFreeFieldBornFiberBounds
        ChapterFreeFieldBornFiberCard ChapterFreeFieldBornFiberCardGeneral
        ChapterFreeFieldBornFiberDeterministic ChapterFreeFieldBornFiberInterior
        ChapterFreeFieldBornFiberSpectrum ChapterFreeFieldBornFiberStabilizer
        ChapterFreeFieldBornFiberTwo ChapterFreeFieldBornGauge ChapterFreeFieldBornHomeo
        ChapterFreeFieldBornQuotient ChapterFreeFieldBornSectionBij
        ChapterFreeFieldBornSignAction ChapterFreeFieldBornSignFiber
        ChapterFreeFieldBornSignGauge ChapterFreeFieldBornSignHom
        ChapterFreeFieldBornSignMatrix ChapterFreeFieldBornSignOrientation
        ChapterFreeFieldBornSignOrientationCard ChapterFreeFieldBornSignOrientationKernel
        ChapterFreeFieldBornSignOrientationQuotient ChapterFreeFieldBornSignOrientationSubgroup
        ChapterFreeFieldBornSignRepresentation ChapterFreeFieldBornSurj
        ChapterFreeFieldConstraint ChapterFreeFieldGaussian ChapterFreeFieldSphere
        ChapterFreeFieldSphereFixpoint ChapterFreeFieldSphereSupport
        ChapterHierarchicalBayes ChapterHierarchicalBayesComposition ChapterHolomorphic
        ChapterJointUnitary ChapterKopperman ChapterLinftyMaximalAbelian
        ChapterLinftyMultiplication ChapterLpRestrictSplit ChapterLpScaleMeasure
        ChapterMeasureAtomicDiffuse ChapterMehlerOrthogonalInvariance ChapterMehlerUniqueness
        ChapterMixedPrior ChapterPriorDependence ChapterPriorOdds ChapterSelectingEvents
        ChapterSeparableL2Model ChapterSeparableSpectrum ChapterSolovay
        ChapterSolovayCoordinates ChapterSolovayCrossDim ChapterSolovayHilbertTensor
        ChapterSolovaySeparableExistence ChapterSolovayTailDimension
        ChapterSpectralCommutant ChapterSpectralDirectSum ChapterSpectralMultiplication
        ChapterStandardBorelClassification ChapterStatementOperator ChapterTrajectory
        ChapterU ChapterUnboundedPosition ChapterUniformPrior ChapterUniformPriorPosterior
        ChapterWeakValue
    """,
    "Toolbox": """
        ChapterBoundedDGammaEsa ChapterCayleyInverse ChapterCayleySpectralModel
        ChapterCayleyTransform ChapterClosureUniqueness ChapterComplexShiftCore
        ChapterConvolutionCalc ChapterCoreBoundsEsa ChapterDegEnergyEstimate
        ChapterDegKatoEsa ChapterDiagonalDGammaEsa ChapterDirectSumEdge ChapterDirectSumEsa
        ChapterEsaFarisLavineIndex ChapterEsaOneParticleDGamma ChapterEsaPairDGamma
        ChapterEsaRealShift ChapterFiniteSectionSingleTime ChapterFlowDGammaEsa
        ChapterFourierMultiplierEsa ChapterFullQuadraticEsa ChapterGaussCoordCombo
        ChapterGaussCoreQuadBounds ChapterGradedFock ChapterGradedFriedrichs
        ChapterGraphCoreTransfer ChapterGroupAverageEsa ChapterHarmonicOscillatorEsa
        ChapterHyperbolicQuadraticEsa ChapterL2TensorPowerUnitary ChapterMixedLinearEsa
        ChapterModeQuadraticEsa ChapterMollifierL2 ChapterNonnegResolvent
        ChapterNonnegSemigroup ChapterNonnegSemigroupGenerator ChapterNonnegSquareRoot
        ChapterNonnegUnitaryGroup ChapterOperatorSeriesEsa ChapterPermutationSectorEsa
        ChapterPolarPartialIsometry ChapterPositiveSquareRootUnique ChapterProve2meReuse
        ChapterQuadraticFockEsa ChapterQuadraticRotationEsa ChapterQuadraticRotationPerturbed
        ChapterQuadratureEsa ChapterRadialMollifier ChapterReducingSubspaceEsa
        ChapterScalarDGammaEsa ChapterSchrodingerCutoffEsa ChapterSecondQuantizationCoreEsa
        ChapterSelfAdjointCoreEsa ChapterShiftedHermiteCore ChapterShiftedQuadraticDegenerate
        ChapterShiftedQuadraticEsa ChapterShiftedQuadraticMatrixEsa ChapterSqSumFarisLavine
        ChapterSqSumFockEsa ChapterSqSumOuterFamily ChapterSqSumOuterSingleTime
        ChapterSqueezedGaussStates ChapterStrichartzWave ChapterTwoParticleSectorEsa
        ChapterUnboundedPolar ChapterUnboundedSpectralModel
        ChapterUnitaryTransport ChapterVonNeumannCore ChapterWaveBoundedPotential
        ChapterWaveUnboundedPotential ChapterWeakSecondDerivative
    """,
    "Qg": """
        ChapterBddBelowFiberSumEsa ChapterBddBelowWallEsa ChapterConformalFiberDeficiency
        ChapterConformalSignFlip ChapterExpPotentialEsa ChapterHalfLineLimitCircle
        ChapterLimitCircleExample ChapterStrichartzHermiteQG ChapterWallDeficiencyObstruction
        ChapterWallEsaBddBelow ChapterWallEsaSemibounded
    """,
    "Qym": """
        ChapterBRSTNilpotent ChapterBookBrstGaugeFixing ChapterBookBrstInstances
        ChapterBookBrstYangMills ChapterBrstReducedTransfer ChapterBrstTruncationLeakage
        ChapterBrstUnboundedLeakage ChapterGaugeCasimirAverage ChapterGaugeComprehensiveFixing
        ChapterGaugeFixing ChapterGaugeIncompleteFixing ChapterGaugeMechanicsCharge
        ChapterGaugeParametrization ChapterGaugeShiftExample ChapterGellMann ChapterGhostField
        ChapterGhostMajoranaRep ChapterQymTimeIndependentFlow ChapterSuperBracket
    """,
    "Ns": "ChapterKoopmanLyapunovFarisLavine ChapterLiftedComparisonEsa",
    "Sirk": """
        ChapterBandEnclosure ChapterGradedBandSchurEsa ChapterGradedHashimoto ChapterH8Bases
        ChapterMinMaxSpectrum ChapterNumericalRangeCrouzeix ChapterNumericalRangeSemigroup
        ChapterRelationShiftInvert ChapterSchurGershgorinGap ChapterSpectralGapStability
        ChapterTruncationGapLift
    """,
    "Ode": "ChapterMomentumChartEsa ChapterPaleyWienerSampling ChapterShannonSampling",
    "Attention": """
        ChapterBoseEinstein ChapterCrossEntropyGradient ChapterDisplacedThermalMulti
        ChapterDisplacedThermalOverlap ChapterEntropyTemperature ChapterLogPartitionConvex
        ChapterObservableExpectation ChapterObservableOperator ChapterResidualStream
        ChapterRotaryPosition ChapterScaledDotProduct ChapterSequentialBayes
        ChapterSinusoidalPosition ChapterThermalTemperatureCore
    """,
    "Textbook": """
        ChapterCPTHamiltonian ChapterCPTPT ChapterCPTParity ChapterGammaCommutant
        ChapterLocalization ChapterLorentzRealRep ChapterLorentzRealRepDirect
        ChapterLorentzRealRepFull ChapterLorentzRealRepSum ChapterMajoranaFourier
        ChapterMajoranaProp74 ChapterPauliCommutant ChapterPauliConsequences
        ChapterPauliFundamental ChapterPinDoubleCover ChapterPinOmega ChapterSE2
    """,
}
STAY_FLAT = {"RandomMap2Audit"}


def plan_moves():
    area_of = {}
    for area, names in AREAS.items():
        for n in names.split():
            assert n not in area_of, n
            area_of[n] = area
    moves, unassigned = {}, []
    for comp, _roots in ic.components("BookProof"):
        if ic.component_name(comp) != "BookProofOperatorCore":
            continue
        for mod in comp:
            rest = mod[len("BookProof."):]
            if "." in rest or rest in STAY_FLAT:
                continue
            if rest not in area_of:
                unassigned.append(rest)
                continue
            area = area_of[rest]
            moves[mod] = (area, f"BookProof.{area}.{rest}")
    stale = set(area_of) - {m[len("BookProof."):] for m in moves}
    return moves, sorted(unassigned), sorted(stale)


if __name__ == "__main__":
    moves, unassigned, stale = plan_moves()
    print(collections.Counter(a for a, _ in moves.values()))
    if unassigned:
        print("unassigned (stay flat):", " ".join(unassigned))
    if stale:
        print("table entries not found flat in the core (already moved?):", " ".join(stale))
    apply_moves(moves, "BOOKPROOF_PHASE2B_MOVES.md",
                "# BookProof Phase 2.2b move map\n\nGenerated by `scripts/bookproof_phase2b_move.py` "
                "(BOOKPROOF_SPLIT_PLAN.md Phase 2.2b: the operator-core residue, assigned by "
                "reading each module header). `BookProof.RandomMap2Audit` stays at the top level. ",
                "--dry-run" in sys.argv)
