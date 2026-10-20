/-
prove2.me platform library module `Definitions.Def_FastFourierTransform_dft`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_FastFourierTransform_dft.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace FastFourierTransform

/-- The discrete Fourier transform (DFT) of length `n`:
`dft n x k = ∑_{m < n} x m * exp (-2 π i m k / n)`. -/
noncomputable def dft (n : ℕ) (x : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n,
    x m * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ)))

end FastFourierTransform
