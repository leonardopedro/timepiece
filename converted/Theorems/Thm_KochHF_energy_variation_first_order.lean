/-
prove2.me platform library module `Theorems.Thm_KochHF_energy_variation_first_order`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_KochHF_energy_variation_first_order.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem energy_variation_first_order {K N : ℕ} (H : FockOp K) (α : Fin N → Fin K → ℂ)
    (M : Matrix (Fin K) (Fin K) ℂ) (hM : M.IsHermitian) :
    HasDerivAt
      (fun t : ℝ => matEl (slater α)
        (NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * H *
          NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M)) (slater α))
      (Complex.I * matEl (slater α) (oneBodyOp M * H - H * oneBodyOp M) (slater α)) 0 := by sorry

end KochHF
