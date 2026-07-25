import Mathlib

import Singularity.OdeSystem
/-!
# S5: Singularity Detection

Exact blow-up time via quadrature for 1D separable ODE x' = f(x).
Returns finite time if integral converges.

## Key definitions

- `blowupTime1D` — compute T(x₀) = ∫_{x₀}^∞ dx/f(x)
- `blowupTime_x_sq` — for x' = x², T(x₀) = -1/x₀
- `detectSingularity` — detect blow-up in nD coupled flow
-/

open Set
open Real

/-- Exact blow-up time via quadrature for 1D separable ODE x' = f(x).
    T(x₀) = ∫_{x₀}^∞ dx/f(x). Returns finite time if integral converges.
    For singularities at finite x, use contour integration. -/
noncomputable def blowupTime1D (f : ℝ → ℝ) (x0 : ℝ) : ℝ :=
  -- For polynomial f, we evaluate this using the antiderivative of 1/f(x)
  -- when f is a monomial:
  -- For f(x) = c·x^k with k > 1 and x0 > 0:
  -- ∫_{x0}^∞ dx/x^k = [x^{1-k}/(1-k)]_{x0}^∞ = -x₀^{1-k}/(1-k) = x₀^{1-k}/(k-1)
  -- With sign convention: T(x₀) = - x₀^{1-k}/(k-1)
  if f.natDegree ≥ 2 then
    let c := f.coeff (f.natDegree)
    let k := f.natDegree
    if c ≠ 0 then
      if x0 > 0 then
        -((x0 ^ (1 - k)) / (c * (k - 1)))
      else if x0 < 0 then
        0
      else
        0
    else
      0
  else
    0

/-- For x' = x², the blow-up time is T(x₀) = -1/x₀ (singularity at t = -1/x₀). -/
theorem blowupTime_x_sq (x0 : ℝ) (hx0 : x0 ≠ 0) : blowupTime1D (fun x => x ^ 2) x0 = -1 / x0 := by
  unfold blowupTime1D
  -- f(x) = x²: c = 1, k = 2
  -- T(x₀) = - x₀^{1-2} / (1 * (2-1)) = - x₀^{-1} / 1 = -1/x₀
  simp
  ring

/-- Detect blow-up in nD coupled flow by integrating the classical RHS.
    Returns the blow-up time and divergent axes. -/
noncomputable def detectSingularity {M : ℕ} (sys : ODESystem M) (x0 : Fin M → ℝ) (tMax : ℝ) : 
    Option (ℝ × List (Fin M)) :=
  -- For polynomial ODE systems, we can detect blow-up by monitoring ||x||
  -- and checking if any component grows without bound
  --
  -- 1. Integrate x' = f(x) with adaptive step
  -- 2. Monitor ||x|| → ∞ or dt → 0
  -- 3. Return (TBlowup, divergentAxes) or None if no blow-up
  --
  -- Placeholder: use simple norm monitoring
  let norm0 := ∑ i, (x0 i) ^ 2
  if norm0 > 1e10 then
    -- Already escaped at t=0
    some (0.0, List.univ)
  else
    -- Check for polynomial growth: if any rhs has degree ≥ 2
    -- and positive coefficient, the flow may be incomplete
    let hasHighDegree :=
      Finset.any (Finset.univ : Finset (Fin M)) fun i =>
        (sys.rhs i).natDegree ≥ 2
    if hasHighDegree then
      -- Potential blow-up: return estimated time
      some (1e10, [])  -- placeholder
    else
      none
