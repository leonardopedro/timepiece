/-
prove2.me platform library module `Theorems.Thm_OAI_DirectCrouzeix_exists_singular_pair`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_DirectCrouzeix_exists_singular_pair.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

open OAI OAI.DirectCrouzeix
universe u_37 u_38 u_39 u_40
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.exists_singular_pair {ι : Type u_38} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hT : 0 < ‖T‖) :
    ∃ x y : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      T x = (‖T‖ : ℂ) • y ∧
      ContinuousLinearMap.adjoint T y = (‖T‖ : ℂ) • x := by sorry
