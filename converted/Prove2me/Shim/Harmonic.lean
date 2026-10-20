import Mathlib

/-!
# Shim: continuity of harmonic functions

`HarmonicOnNhd.continuousOn` (platform Mathlib) is absent from the pinned Mathlib; it follows from
the `C²` regularity that is part of `HarmonicAt`.
-/

theorem InnerProductSpace.HarmonicOnNhd.continuousOn {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}
    (h : InnerProductSpace.HarmonicOnNhd f s) : ContinuousOn f s :=
  fun x hx => (h x hx).1.continuousAt.continuousWithinAt
