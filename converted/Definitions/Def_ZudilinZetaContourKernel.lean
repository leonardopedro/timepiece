/-
prove2.me platform library module `Definitions.Def_ZudilinZetaContourKernel`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ZudilinZetaContourKernel.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaParams13

/-!
Concrete reflected Gamma kernel for the parameters in Zudilin's 2001 note,
p.774, rational-function formula and (2), with the parameter choice on p.775.
The indices encode a finite product; no contour identity is asserted here.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
namespace ZudilinZeta

def params13GammaSlope (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 1 then -1 else if 3 ≤ i ∧ i < 29 then 1 else 0

def params13GammaOffset (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i = 1 then 91 else if i = 2 then 27
  else if i < 16 then -91 + (eta13 (i - 2) : ℝ)
  else if i < 29 then -(eta13 (i - 15) : ℝ)
  else 91 - 2 * (eta13 (i - 25) : ℝ)

def params13GammaBase (z : ℂ) (i : ℕ) : ℂ :=
  (params13GammaSlope i : ℂ) * z + (params13GammaOffset i : ℂ)

def params13GammaWeight (i : ℕ) : ℤ :=
  if i = 0 ∨ i = 1 then 3 else if i = 2 then -6
  else if i < 16 then 1 else if i < 29 then -1 else 1

def params13GammaShiftIndex (i : ℕ) : ℤ :=
  if i = 1 then 2 else if i = 2 then 1 else if i < 3 then 0
  else if i < 16 then -1 else if i < 29 then 0 else 1

def params13GammaKernel (n : ℕ) (z : ℂ) : ℂ :=
  (91 * (n : ℂ) + 2 - 2 * (n : ℂ) * z) *
    ∏ i ∈ Finset.range 39,
      Complex.Gamma ((n : ℂ) * params13GammaBase z i + (params13GammaShiftIndex i : ℂ)) ^
        params13GammaWeight i

def params13KernelIntegral (n : ℕ) (τ : ℂ) : ℂ :=
  ∫ t : ℝ, params13GammaKernel n (τ + (t : ℂ) * I) *
    Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I))

end ZudilinZeta
end
