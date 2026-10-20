/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
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

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

abbrev MatrixPolynomial (m : ℕ) := Polynomial (Matrix (Fin m) (Fin m) ℂ)

def matrixPolynomialValue {m : ℕ} (z : ℂ) :
    MatrixPolynomial m →+* Matrix (Fin m) (Fin m) ℂ :=
  Polynomial.eval₂RingHom' (RingHom.id _) (z • 1) (by
    intro C
    change C * (z • 1) = (z • 1) * C
    simp [])

@[simp] theorem matrixPolynomialValue_C {m : ℕ} (z : ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) : matrixPolynomialValue z (Polynomial.C C) = C := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem matrixPolynomialValue_X {m : ℕ} (z : ℂ) :
    matrixPolynomialValue (m := m) z Polynomial.X = z • 1 := by
  exact Polynomial.eval₂_X _ _

def scalarMatrixPolynomial {m : ℕ} (p : Polynomial ℂ) : MatrixPolynomial m :=
  p.map (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ))

def faberPolynomial {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) : MatrixPolynomial m :=
  ∑ k : Fin N, Polynomial.C (C k) * scalarMatrixPolynomial (b k)

def polynomialEnergy {m : ℕ} (h : BoundaryCircle → ℂ) (G : MatrixPolynomial m) : ℝ :=
  ∫ t, hsSq (matrixPolynomialValue (h t) G) ∂circleMeasure

end DirectCrouzeix

end

end OAI
