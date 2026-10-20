import Mathlib

/-!
# Shim: translation of Schwartz functions

The platform Mathlib provides `SchwartzMap.compSubConstCLM`, the translation
`f ↦ (x ↦ f (x - a))` on Schwartz space, which the pinned Mathlib lacks.  The converted
modules only use it applied, as `f.compSubConstCLM 𝕜 a`, together with its simp lemma
`compSubConstCLM_apply`; the shim provides exactly that, built from the pinned
`SchwartzMap.compCLMOfAntilipschitz`.
-/

open scoped SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The translate `x ↦ f (x - a)` of a Schwartz function `f`. -/
noncomputable def compSubConstCLM (f : 𝓢(E, F)) (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (a : E) : 𝓢(E, F) :=
  compCLMOfAntilipschitz 𝕜 (K := 1) (g := fun x => x - a)
    ((Function.HasTemperateGrowth.id').sub (Function.HasTemperateGrowth.const a))
    (AntilipschitzWith.of_le_mul_dist fun x y => by simp [dist_eq_norm]) f

@[simp] theorem compSubConstCLM_apply (f : 𝓢(E, F)) (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (a x : E) : f.compSubConstCLM 𝕜 a x = f (x - a) := rfl

end SchwartzMap
