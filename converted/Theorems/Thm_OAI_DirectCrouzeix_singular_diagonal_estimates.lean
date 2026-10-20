/-
prove2.me platform library module `Theorems.Thm_OAI_DirectCrouzeix_singular_diagonal_estimates`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_DirectCrouzeix_singular_diagonal_estimates.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory

theorem OAI.DirectCrouzeix.singular_diagonal_estimates {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) (hsVector X) =
      (γ : ℂ) • hsVector Y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) (hsVector Y) =
      (γ : ℂ) • hsVector X) :
    let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
    (hsSq (Xᴴ * Polynomial.aeval A (b 0) * X) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Xᴴ * Polynomial.aeval A (b (k+1)) * X) ≤ a / γ^2) ∧
    (hsSq (Yᴴ * Polynomial.aeval A (b 0) * Y) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Yᴴ * Polynomial.aeval A (b (k+1)) * Y) ≤ a / γ^2) := by sorry
