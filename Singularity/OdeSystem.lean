import Mathlib

/-!
# S2: ODE System Representation

Define the ODE system type and its polynomial RHS.

## Key definitions

- `ODESystem M` — an autonomous polynomial ODE system in M variables
- `evalRHS sys x` — evaluate the RHS at a point x : Fin M → ℝ
- `order sys` — total degree of the polynomial system
-/

open Polynomial

/-- An autonomous polynomial ODE system in M variables.
    Each equation is `dx_i/dt = f_i(x)` where `f_i` is a polynomial
    in the i-th variable (univariate). For multivariate polynomials,
    use `MvPolynomial`. -/
structure ODESystem (M : ℕ) where
  vars : Fin M → String
  rhs : Fin M → Polynomial ℝ

/-- Evaluate the RHS at a point x : Fin M → ℝ.
    Each component `rhs i` is evaluated at `x i`. -/
def ODESystem.evalRHS {M : ℕ} (sys : ODESystem M) (x : Fin M → ℝ) : Fin M → ℝ :=
  fun i => (sys.rhs i).eval (x i)

/-- Total order (maximum degree) of the ODE system.
    This is the maximum natDegree across all rhs polynomials. -/
noncomputable def ODESystem.order {M : ℕ} (sys : ODESystem M) : ℕ :=
  if h : (Finset.univ : Finset (Fin M)).Nonempty then
    Finset.sup' (Finset.univ : Finset (Fin M)) h fun i =>
      (sys.rhs i).natDegree
  else
    0

/-- Check if the ODE system is linear (all rhs are linear polynomials). -/
noncomputable def ODESystem.isLinear {M : ℕ} (sys : ODESystem M) : Bool :=
  decide (∀ i, (sys.rhs i).natDegree ≤ 1)

/-- Construct a simple 1D ODE: dx/dt = f(x) where f is a polynomial. -/
noncomputable def mk1D (f : Polynomial ℝ) : ODESystem 1 :=
  { vars := fun _ => "x"
    rhs := fun _ => f
  }
