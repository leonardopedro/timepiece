/-
prove2.me platform library module `Definitions.Def_TeschlODE_SturmLiouville_SLInner`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_SturmLiouville_SLInner.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 155, (5.52): the weighted scalar product `⟨f, g⟩ = ∫_a^b f(x)* g(x) r(x) dx`
on `H₀ = C([a, b], ℂ)`, conjugate linear in the first argument. The norm of `H₀` is
`‖f‖ = √(Re ⟨f, f⟩)` (5.20). Every use applies it to functions continuous on `[a, b]`. -/
noncomputable def SLInner (r : ℝ → ℝ) (a b : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x in a..b, starRingEnd ℂ (f x) * g x * (r x : ℂ)

end TeschlODE.SturmLiouville
