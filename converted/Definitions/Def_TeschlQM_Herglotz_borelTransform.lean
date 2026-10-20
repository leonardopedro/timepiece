/-
prove2.me platform library module `Definitions.Def_TeschlQM_Herglotz_borelTransform`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Herglotz_borelTransform.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, (3.60) (also (3.40)): the **Borel transform** of a Borel measure `μ` on `ℝ`,
`F(z) = ∫_ℝ 1/(λ − z) dμ(λ)`. -/
noncomputable def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ

end TeschlQM.Herglotz
