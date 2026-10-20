/-
prove2.me platform library module `Theorems.Thm_OAI_DirectCrouzeix_Faber_energy_orthogonal_positiveSeries`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_DirectCrouzeix_Faber_energy_orthogonal_positiveSeries.lean` (platform Mathlib rev 0df444a360ea).
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries {N : ℕ} (C : Fin N → E)
    (r : Angle → E) (hr : Continuous r) (hfreq : ∀ j : ℤ, 0 ≤ j → fourierCoeff r j = 0) :
    (∫ t, ‖positiveSeries C t+r t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖r t‖^2 ∂angularMeasure := by sorry
