/-
prove2.me platform library module `Theorems.Thm_KochHF_slater_projection_rules`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_KochHF_slater_projection_rules.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem slater_projection_rules {K N : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (φ : Fin K → ℂ) :
    cannOrb φ *ᵥ slater α = cannOrb (occProj α φ) *ᵥ slater α ∧
    cdagOrb φ *ᵥ slater α = cdagOrb (φ - occProj α φ) *ᵥ slater α := by sorry

end KochHF
