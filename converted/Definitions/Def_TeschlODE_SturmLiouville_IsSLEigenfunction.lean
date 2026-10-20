/-
prove2.me platform library module `Definitions.Def_TeschlODE_SturmLiouville_IsSLEigenfunction`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_SturmLiouville_IsSLEigenfunction.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_SLDomain

namespace TeschlODE.SturmLiouville

/-- Teschl §5.2, p. 149, (5.37), applied to the Sturm–Liouville operator `L` on `D(L)` (§5.4,
(5.53)–(5.55)): `f` is an eigenfunction of `L` for the eigenvalue `z ∈ ℂ` if `f ∈ D(L)`, `f` is a
nonzero element of `H₀ = C([a, b], ℂ)` (it does not vanish identically on `[a, b]`), and
`L f = z f` on `[a, b]`. -/
def IsSLEigenfunction (p q r : ℝ → ℝ) (a b α β : ℝ) (z : ℂ) (f : ℝ → ℂ) : Prop :=
  SLDomain p a b α β f ∧ (∃ x ∈ Set.Icc a b, f x ≠ 0) ∧
    ∀ x ∈ Set.Icc a b, SLOp p q r a b f x = z * f x

end TeschlODE.SturmLiouville
