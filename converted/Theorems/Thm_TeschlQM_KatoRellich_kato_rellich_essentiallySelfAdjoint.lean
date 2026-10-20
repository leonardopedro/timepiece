/-
prove2.me platform library module `Theorems.Thm_TeschlQM_KatoRellich_kato_rellich_essentiallySelfAdjoint`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_TeschlQM_KatoRellich_kato_rellich_essentiallySelfAdjoint.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Theorem 6.4 (Kato–Rellich), p. 135, essentially self-adjoint case. If `A` is essentially
self-adjoint and `B` is symmetric with `A`-bound less than one, then `A + B` with
`𝔇(A + B) = 𝔇(A)` is essentially self-adjoint, `𝔇(Ā) ⊆ 𝔇(B̄)` and `\overline{A + B} = Ā + B̄`.
If moreover `A ≥ γ` and (6.1) holds with constants `a < 1`, `b`, then
`A + B ≥ γ - max(a|γ| + b, b/(1 - a))` (the book's `b/(a - 1)` corrected, as in `kato_rellich`). -/
theorem kato_rellich_essentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsEssentiallySelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ TeschlQM.Shared.IsEssentiallySelfAdjoint (A + B) ∧
      A.closure.domain ≤ B.closure.domain ∧ (A + B).closure = A.closure + B.closure ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b → TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B) (γ - max (a * |γ| + b) (b / (1 - a))) := by sorry

end TeschlQM.KatoRellich
