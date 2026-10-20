/-
prove2.me platform library module `Definitions.Def_clifford6_casimir_data`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_clifford6_casimir_data.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace Clifford6

/-- The Euclidean quadratic form diag(1,1,1,1,1,1) on R^6. -/
noncomputable def Q60 : QuadraticForm ℝ (Fin 6 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ => 1)

/-- The i-th orthonormal generator of Cl(6,0). -/
noncomputable def e6 (i : Fin 6) : CliffordAlgebra Q60 :=
  CliffordAlgebra.ι Q60 (Pi.single i 1)

/-- The odd-grade sector Cl⁻(6,0) = grades 1, 3, 5. -/
noncomputable def oddSector : Submodule ℝ (CliffordAlgebra Q60) :=
  CliffordAlgebra.evenOdd Q60 1

/-- First generator of the active su(2) triple: e₀e₂. -/
noncomputable def E1 : CliffordAlgebra Q60 := e6 0 * e6 2

/-- Second generator: e₂e₅. -/
noncomputable def E2 : CliffordAlgebra Q60 := e6 2 * e6 5

/-- Third generator: e₀e₅. -/
noncomputable def E3 : CliffordAlgebra Q60 := e6 0 * e6 5

end Clifford6
