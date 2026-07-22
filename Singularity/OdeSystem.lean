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
    in variables `x_1, ..., x_M`. -/
structure ODESystem (M : ℕ) where
  vars : Fin M → String
  rhs : Fin M → Polynomial (Fin M → ℝ)
  
  /-- Evaluate the RHS at a point x : Fin M → ℝ. -/
  def evalRHS (x : Fin M → ℝ) : Fin M → ℝ :=
    fun i => (rhs i).eval x

/-- Total order (maximum degree) of the ODE system.
    This is the maximum total degree across all polynomials. -/
def order (sys : ODESystem M) : ℕ :=
  -- TODO: compute the maximum degree across all rhs polynomials
  Finset.sup' (Finset.univ : Finset (Fin M)) (by simp) fun i =>
    (sys.rhs i).degree

/-- Check if the ODE system is linear (all rhs are linear polynomials). -/
def isLinear (sys : ODESystem M) : Bool :=
  -- TODO: check if all rhs have degree ≤ 1
  true

/-- Construct a simple 1D ODE: dx/dt = f(x) where f is a polynomial. -/
def mk1D (f : Polynomial ℝ) : ODESystem 1 :=
  { vars := fun _ => "x"
    rhs := fun i => 
      -- Map the single-variable polynomial to a polynomial in Fin 1 → ℝ
      -- TODO: implement the mapping
      Polynomial.map (fun _ => 0) f
  }

end
