-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.polySym_foPoly
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterYangMillsHermite

open BookProof.HermiteRelative

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

variable {d : ℕ}

theorem BookProof.HermiteRelative.polySym_foPoly (b b' : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (foPoly b b') := by sorry
