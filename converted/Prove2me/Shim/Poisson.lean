import Mathlib

/-!
# Shim: the Herglotz–Riesz and Poisson kernels

Stands in for the kernels `herglotzRieszKernel` and `poissonKernel` of the platform Mathlib,
which the pinned Mathlib lacks.  For a centre `c`, an interior point `w` and a boundary point
`z`, the Herglotz–Riesz kernel is `((z - c) + (w - c)) / ((z - c) - (w - c))` and the Poisson
kernel is its real part, `(‖z - c‖² - ‖w - c‖²) / ‖z - w‖²`.
-/

/-- The Herglotz–Riesz kernel `((z - c) + (w - c)) / ((z - c) - (w - c))`. -/
noncomputable def herglotzRieszKernel (c w z : ℂ) : ℂ :=
  ((z - c) + (w - c)) / ((z - c) - (w - c))

/-- The Poisson kernel: the real part of the Herglotz–Riesz kernel. -/
noncomputable def poissonKernel (c w z : ℂ) : ℝ :=
  (herglotzRieszKernel c w z).re
