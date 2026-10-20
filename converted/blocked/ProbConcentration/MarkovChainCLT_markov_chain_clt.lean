/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 641ee81d-e96a-4dbb-a181-3cf8c1787fc9
* original name       : `MarkovChainCLT.markov_chain_clt`
* title               : The Markov chain CLT: six sufficient conditions (Jones Thm 9, mission goal)
* statement author    : Shuze Chen
* solution author     : LukeBernese (submission b6c47d58-0def-467d-9cff-96b24d9fac52,
                        accepted 2026-09-08T16:08:15.73309+00:00)
* source              : G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, Theorem 9, the summary theorem (arXiv v2 p. 13)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/prob-concentration/MarkovChainCLT.markov_chain_clt.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/MarkovChainCLT_markov_chain_clt.diff`.
-/
import Theorems.Thm_MarkovChainCLT_clt_of_geometric_or_polynomial
import Theorems.Thm_MarkovChainCLT_clt_of_geometric_of_log_moment
import Theorems.Thm_MarkovChainCLT_clt_of_geometric_reversible
import Theorems.Thm_MarkovChainCLT_clt_of_uniformly_ergodic
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

/-- **Theorem 9** (Jones 2004, §4), the mission goal.  Each of the six regimes is
exactly the hypothesis of one of the four corollaries of the mission, so the summary
theorem is assembled by dispatching on `hcase`. -/
theorem _root_.Prove2me.Solution.MarkovChainCLT_markov_chain_clt {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcase :
      (∃ m : ℝ, 1 < m ∧ PolynomiallyErgodicL1 P π m ∧
        ∃ B : ℝ, ∀ᵐ x ∂π, |f x| < B) ∨
      (∃ m δ : ℝ, 0 < δ ∧ 2 + δ < m * δ ∧ PolynomiallyErgodicL1 P π m ∧
        Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (GeometricallyErgodic P π ∧
        ∃ δ : ℝ, 0 < δ ∧ Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (GeometricallyErgodic P π ∧
        Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) ∨
      (GeometricallyErgodic P π ∧ Kernel.IsReversible P π ∧ MemLp f 2 π) ∨
      (UniformlyErgodic P π ∧ MemLp f 2 π)) :
    SatisfiesCLT P π f := by
  rcases hcase with hpolyB | hpolyδ | hgeoδ | hgeolog | hgeorev | huni
  -- (1) polynomially ergodic of order `m > 1` with a bounded `f`: Corollary 2, third case.
  · exact clt_of_geometric_or_polynomial P π hP f hf (Or.inr (Or.inr hpolyB))
  -- (2) polynomially ergodic with `mδ > 2 + δ` and a `2+δ` moment: Corollary 2, second case.
  · exact clt_of_geometric_or_polynomial P π hP f hf (Or.inr (Or.inl hpolyδ))
  -- (3) geometrically ergodic with a `2+δ` moment: Corollary 2, first case.
  · exact clt_of_geometric_or_polynomial P π hP f hf (Or.inl hgeoδ)
  -- (4) geometrically ergodic with an `f² log⁺|f|` moment: Corollary 3.
  · exact clt_of_geometric_of_log_moment P π hP f hf hgeolog.1 hgeolog.2
  -- (5) geometrically ergodic, reversible, `f ∈ L²`: Corollary 4.
  · exact clt_of_geometric_reversible P π hP f hf hgeorev.1 hgeorev.2.1 hgeorev.2.2
  -- (6) uniformly ergodic, `f ∈ L²`: Corollary 5.
  · exact clt_of_uniformly_ergodic P π hP f hf huni.1 huni.2

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.markov_chain_clt {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcase :
      (∃ m : ℝ, 1 < m ∧ PolynomiallyErgodicL1 P π m ∧
        ∃ B : ℝ, ∀ᵐ x ∂π, |f x| < B) ∨
      (∃ m δ : ℝ, 0 < δ ∧ 2 + δ < m * δ ∧ PolynomiallyErgodicL1 P π m ∧
        Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (GeometricallyErgodic P π ∧
        ∃ δ : ℝ, 0 < δ ∧ Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (GeometricallyErgodic P π ∧
        Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) ∨
      (GeometricallyErgodic P π ∧ Kernel.IsReversible P π ∧ MemLp f 2 π) ∨
      (UniformlyErgodic P π ∧ MemLp f 2 π)) :
    SatisfiesCLT P π f :=
  _root_.Prove2me.Solution.MarkovChainCLT_markov_chain_clt P π hP f hf hcase



end Prove2meStatement
