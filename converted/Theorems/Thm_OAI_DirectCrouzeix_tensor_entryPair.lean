/-
prove2.me platform library module `Theorems.Thm_OAI_DirectCrouzeix_tensor_entryPair`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_DirectCrouzeix_tensor_entryPair.lean` (platform Mathlib rev 0df444a360ea).
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

theorem OAI.DirectCrouzeix.tensor_entryPair {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y)
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (A ⊗ₖ C) (hsVector X)) =
      entryPair (Yᴴ * A * X) C := by sorry
