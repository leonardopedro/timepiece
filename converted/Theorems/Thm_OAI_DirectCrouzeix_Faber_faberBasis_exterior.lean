/-
prove2.me platform library module `Theorems.Thm_OAI_DirectCrouzeix_Faber_faberBasis_exterior`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_DirectCrouzeix_Faber_faberBasis_exterior.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_106 u_107
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.faberBasis_exterior {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    {v : ℂ} (hv : v ∈ ball 0 R) (hv0 : v ≠ 0)
    (hH : ∀ u ∈ ball 0 R, chordDenominator c g u v ≠ 0) (k : ℕ) :
    (faberBasis c g k).eval (exterior c g v⁻¹) = v⁻¹^k +
      taylorCoeff (fun u => correction c g u v) k := by sorry
