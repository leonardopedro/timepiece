/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_wronskian`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_wronskian.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_quasiDeriv

namespace TeschlQM.SturmLiouville

/-- Teschl (9.5), p. 182: the modified Wronskian
`W_x(f₁, f₂) = (p (f₁ f₂′ − f₁′ f₂))(x) = f₁(x) (p f₂′)(x) − (p f₁′)(x) f₂(x)`.
There is no complex conjugation. -/
noncomputable def wronskian (L : SLData) (x : ℝ) (f₁ f₂ : ℝ → ℂ) : ℂ :=
  f₁ x * quasiDeriv L f₂ x - quasiDeriv L f₁ x * f₂ x

/-- Teschl, p. 182, after (9.7): `W_a(f₁, f₂) = lim_{x → a} W_x(f₁, f₂)`, the limit taken inside
`I`. The limit exists for `f₁, f₂ ∈ D(τ)` by (9.7); `limUnder` returns an unspecified value
when it does not exist, and the mission only evaluates it where the book's limit exists. -/
noncomputable def wronskianLeft (L : SLData) (f₁ f₂ : ℝ → ℂ) : ℂ :=
  limUnder L.atLeft (fun x => wronskian L x f₁ f₂)

/-- Teschl, p. 182: `W_b(f₁, f₂) = lim_{x → b} W_x(f₁, f₂)`, the limit taken inside `I`. -/
noncomputable def wronskianRight (L : SLData) (f₁ f₂ : ℝ → ℂ) : ℂ :=
  limUnder L.atRight (fun x => wronskian L x f₁ f₂)

end TeschlQM.SturmLiouville
