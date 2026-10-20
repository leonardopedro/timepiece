/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : b681bf18-e4c5-4347-a9ee-5cc978d1c4b1
* original name       : `SubsetSumNP.subsetSum_npComplete`
* title               : Binary SUBSET SUM is NP-complete
* statement author    : wurtle
* solution author     : wurtle (submission 6ec17d47-70d3-4ff1-8aea-ee3f4dd38427,
                        accepted 2026-10-06T04:12:29.638672+00:00)
* source              : Richard M. Karp, Reducibility Among Combinatorial Problems, Complexity of Computer Computations, Plenum Press, pp. 85–103, 1972. Binary integer encoding p. 89; Main Theorem and problem 18 (equality-KNAPSACK), pp. 94–95; EXACT COVER-to-KNAPSACK reduction p. 100. https://doi.org/10.1007/978-1-4684-2001-2_9 The positive-input variant uses an alternate direct 3-SAT proof, rather than attributing that construction to Karp. Alternate direct 3-SAT proof: Mark Bun, BU CS332, Lecture 23: More NP-completeness, April 29, 2024, slides 18–23. https://cs-people.bu.edu/mbun/courses/332_S24/slides/CS332-Lec23.pdf Planned prerequisite: https://prove2.me/theorems/77c6ed06-10e8-4214-b81f-e88ba13a984b ; proved backend: https://prove2.me/theorems/d82e8682-c490-4742-a5e5-dd3a0b870b90
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/logos-confluence/SubsetSumNP.subsetSum_npComplete.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/SubsetSumNP_subsetSum_npComplete.diff`.
-/
import Theorems.Thm_SubsetSumNP_inNP
import Theorems.Thm_SubsetSumNP_threeSAT_reduces_subsetSum
import Theorems.Thm_KSat_sat_ram_threeCNF_normalizer
import Theorems.Thm_WordRAM_Complexity_polynomial_backend_exists
import Theorems.Thm_CookLevin_sat_npComplete
import Theorems.Thm_CookLevin_polyTimeComputable_comp

set_option autoImplicit false

private theorem normalizer_polytime
    (B : WordRAM.Complexity.PolynomialBackend)
    (A : WordRAM.Complexity.Algorithm .restricted)
    (f : List Bool → List Bool)
    (h : WordRAM.Complexity.RAMPolyTimeComputable A f) :
    CookLevin.IsPolyTimeComputable f := by
  obtain ⟨a,b,hrun⟩ := h
  obtain ⟨c,d,sim⟩ := B.functions A a b
  refine ⟨sim.machine,sim.tapes,sim.alphabet,c,d,sim.legal,?_⟩
  intro x
  exact sim.simulates x (f x) (hrun x).1 (hrun x).2

private theorem threeCNF_encoding (φ : CookLevin.Formula) (h : KSat.IsKCNF 3 φ) :
    KSat.KSAT 3 (CookLevin.encodeFormula φ) ↔ CookLevin.Satisfiable φ := by
  constructor
  · rintro ⟨ψ,he,_,hs⟩
    have hsame := CookLevin.encodeFormula_injective he
    exact hsame.symm ▸ hs
  · intro hs; exact ⟨φ,rfl,h,hs⟩

theorem _root_.Prove2me.Solution.SubsetSumNP_subsetSum_npComplete : CookLevin.NPComplete SubsetSumNP.SUBSET_SUM := by
  refine ⟨SubsetSumNP.inNP,?_⟩
  obtain ⟨B⟩ := WordRAM.Complexity.polynomial_backend_exists
  obtain ⟨A,f,hram,hnormal⟩ := KSat.sat_ram_threeCNF_normalizer
  have hf := normalizer_polytime B A f hram
  obtain ⟨g,hg,hgcorrect⟩ := SubsetSumNP.threeSAT_reduces_subsetSum
  have hSAT : ∀ x, CookLevin.SAT x ↔ KSat.KSAT 3 (f x) := by
    intro x
    obtain ⟨φ,hout,hwidth,hsat⟩ := hnormal x
    rw [hout]
    exact hsat.trans (threeCNF_encoding φ hwidth).symm
  intro L hL
  obtain ⟨r,hr,hrcorrect⟩ := CookLevin.sat_npComplete.2 L hL
  refine ⟨fun x => g (f (r x)),
    CookLevin.polyTimeComputable_comp (fun x => f (r x)) g
      (CookLevin.polyTimeComputable_comp r f hr hf) hg,?_⟩
  intro x
  exact (hrcorrect x).trans ((hSAT (r x)).trans (hgcorrect (f (r x))))

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

set_option autoImplicit false

theorem SubsetSumNP.subsetSum_npComplete :
    CookLevin.NPComplete SubsetSumNP.SUBSET_SUM := by
  first
  | exact _root_.Prove2me.Solution.SubsetSumNP_subsetSum_npComplete
  | (apply _root_.Prove2me.Solution.SubsetSumNP_subsetSum_npComplete <;> assumption)


end Prove2meStatement
