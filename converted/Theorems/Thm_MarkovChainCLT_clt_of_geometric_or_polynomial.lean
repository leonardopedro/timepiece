/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_clt_of_geometric_or_polynomial`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_clt_of_geometric_or_polynomial.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 2** (case 1: Chan–Geyer 1994): a Harris ergodic chain satisfying one
of: (1) geometric ergodicity with `E_π |f|^{2+δ} < ∞` for some `δ > 0`;
(2) polynomial ergodicity of order `m` with integrable constant and
`E_π |f|^{2+δ} < ∞` with `mδ > 2+δ`; (3) polynomial ergodicity of order `m > 1`
with integrable constant and `f` bounded `π`-a.s. — satisfies the CLT for every
initial distribution. -/

theorem MarkovChainCLT.clt_of_geometric_or_polynomial {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcase :
      (GeometricallyErgodic P π ∧
        ∃ δ : ℝ, 0 < δ ∧ Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (∃ m δ : ℝ, 0 < δ ∧ 2 + δ < m * δ ∧ PolynomiallyErgodicL1 P π m ∧
        Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (∃ m : ℝ, 1 < m ∧ PolynomiallyErgodicL1 P π m ∧
        ∃ B : ℝ, ∀ᵐ x ∂π, |f x| < B)) :
    SatisfiesCLT P π f := by sorry
