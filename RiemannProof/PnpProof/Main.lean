import Mathlib
import PnpProof.Foundations
import PnpProof.Counting
import PnpProof.Model
import PnpProof.Comparator

/-!
# Part 5: Main theorems

* `selection_not_history` (T1)
* `almost_all_not_computable` (T2)
* `model_P_ne_NP` (T3)
* `mixed_to_continuous` (the §5→§6 conversion glue)
* `model_P_ne_NP_circuit` (T3, circuit form — N1)
* `model_vs_clay_disjointness` (T5: the Tier-C disjointness, made checkable)
* `realistic_version` (T4, OPEN)

See `PNP_IMPLEMENTATION_PLAN.md`, Part 6, for what is deliberately *not*
formalized (the Clay bridge, Turing-machine time bounds, etc.).
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace PnpProof

instance : NoAtoms prior := ⟨prior_atomless⟩

/-! ### T1. Selection by conditioning is well-defined, yet no history realizes it -/

theorem selection_not_history :
    (squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure) ∧
    (∀ y₀ : ℝ, squareMeasure {p : ℝ × ℝ | p.2 = y₀} = 0) ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (Y : ℕ → Ω → ℝ),
      (∀ n, Measurable (Y n)) → (∀ n y, P {ω | Y n ω = y} = 0) →
      ∀ y₀, P {ω | ∃ n, Y n ω = y₀} = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact selection_exists;
  · intro y₀;
    erw [ MeasureTheory.Measure.restrict_apply' ];
    · exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_mono_null ( show { p : ℝ × ℝ | p.2 = y₀ } ∩ Icc 0 1 ×ˢ Icc 0 1 ⊆ { p : ℝ × ℝ | p.2 = y₀ } from fun x hx => hx.1 ) ( by erw [ show { p : ℝ × ℝ | p.2 = y₀ } = ( Set.univ : Set ℝ ) ×ˢ { y₀ } by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ; norm_num ) );
    · exact measurableSet_Icc.prod measurableSet_Icc;
  · -- Apply the hypothesis `h_no_history` to conclude the proof.
    apply PnpProof.no_history

/-! ### T2. With prior probability 1, the selected function is not computable -/

theorem almost_all_not_computable :
    prior {g : C(K, ℝ) | ∃ c : Nat.Partrec.Code, ComputesSelection c g} = 0 := by
  exact countable_null prior countable_computable_selections

/-! ### M5. The verifier on bit-encoded dyadic data -/

/-- The verifier: candidate output `u` is accepted between truncated CDF values
    `glo` and `ghi`. -/
def verifyBits (glo ghi u : ℕ) : Bool := decide (glo ≤ u ∧ u ≤ ghi)

/-
The verifier is computable: candidate verification is cheap.
-/
theorem verifyBits_computable :
    Computable (fun p : ℕ × ℕ × ℕ => verifyBits p.1 p.2.1 p.2.2) := by
  -- The function `decide (glo ≤ u ∧ u ≤ ghi)` is primitive recursive, hence computable.
  have h_decide_computable : Primrec (fun p : ℕ × ℕ × ℕ => decide (p.1 ≤ p.2.2 ∧ p.2.2 ≤ p.2.1)) := by
    have h_decide_computable : Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      convert Primrec.nat_le using 1;
      constructor <;> intro h <;> rw [ PrimrecRel ] at *;
      · convert h using 1;
        constructor <;> intro h <;> rw [ PrimrecPred ] at * <;> aesop;
      · grind +suggestions;
    convert Primrec.and.comp ( h_decide_computable.comp ( Primrec.fst.comp ( Primrec.id ) |> Primrec.pair <| Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) ) ( h_decide_computable.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd.comp ( Primrec.id ) ) ) ) using 1;
    grind;
  convert h_decide_computable.to_comp using 1

/-! ### T3. Separation within the model -/

/-- In the model of `pnp.tex` §§3–6: verification of a candidate output is a
    computable (cheap) operation, while no deterministic machine computes the
    selected function on a set of priors of full measure.

    This is a theorem **about this model**. It is NOT the Clay Millennium
    statement `P ≠ NP`, and no claim of implication is formalized — see Part 6
    of `PNP_IMPLEMENTATION_PLAN.md`. -/
theorem model_P_ne_NP :
    Computable (fun p : ℕ × ℕ × ℕ => verifyBits p.1 p.2.1 p.2.2) ∧
    prior {g : C(K, ℝ) | ∃ c : Nat.Partrec.Code, ComputesSelection c g} = 0 := by
  exact ⟨verifyBits_computable, almost_all_not_computable⟩

/-! ### The §5→§6 conversion glue -/

theorem mixed_to_continuous {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (h : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧ (∀ x, ν {x} = 0) := by
  refine ⟨?_, ?_, ?_⟩
  exact ( μ { x | μ { x } ≠ 0 } ᶜ ) ⁻¹ • μ.restrict { x | μ { x } ≠ 0 } ᶜ;
  · constructor;
    simp +decide [ ENNReal.inv_mul_cancel h ];
  · intro x; by_cases hx : μ { x } = 0 <;> simp_all +decide [ Set.compl_def ] ;

/-! ### M5 / N1. The `O(k)` comparator-circuit upgrade of the NP side

`model_P_ne_NP_circuit` strengthens the NP side of `model_P_ne_NP`: instead of
merely asserting computability of the verifier (`verifyBits_computable`), it
exhibits, for every resolution `k ≥ 1`, an explicit Boolean comparator
`Circuit (3*k) (s+1)` of size `s ≤ 50*k + 50` (built in `Comparator.lean`) that
decides `verifyBits glo ghi u = (glo ≤ u ∧ u ≤ ghi)` on three `k`-bit numbers
packed little-endian by `bitsOf`. The big-endian ripple comparator is driven by
the bit recursion `div_pow_succ_compare` (now in `Comparator.lean`). This is a
NEW theorem stated beside `model_P_ne_NP`; the latter is left untouched, and the
development remains sorry-free and axiom-free. -/

/-- **T3, circuit form (N1).** In the model of `pnp.tex` §§3–6: verification of
    a candidate output is performed by an explicit `O(k)`-size Boolean circuit
    (a comparator on the `k`-bit dyadic data), while no deterministic machine
    computes the selected function on a set of priors of full measure.

    This is a theorem **about this model**. It is NOT the Clay Millennium
    statement `P ≠ NP`, and no claim of implication is formalized — see Part 6
    of `PNP_IMPLEMENTATION_PLAN.md`. -/
theorem model_P_ne_NP_circuit :
    (∀ k : ℕ, 1 ≤ k → ∃ s, s ≤ 50 * k + 50 ∧ ∃ C : Circuit (3*k) (s+1),
        ∀ glo ghi u : Fin (2^k),
          C.eval (bitsOf k glo ghi u) = verifyBits glo ghi u) ∧
    prior {g : C(K, ℝ) | ∃ c : Nat.Partrec.Code, ComputesSelection c g} = 0 := by
  refine ⟨fun k hk => ?_, almost_all_not_computable⟩
  obtain ⟨s, hs, C, hC⟩ := verify_circuit_cheap k hk
  exact ⟨s, hs, C, fun glo ghi u => by rw [hC glo ghi u]; rfl⟩

/-! ### T5. The model/Clay disjointness, made checkable -/

/-- A language `L : ℕ → Bool` — a decision problem on finite (encoded) inputs,
    the kind of object the Clay P vs NP statement quantifies over — *decides
    the selection* `g` when, queried on the encoded triple
    `(resolution, input index, candidate output index)`, it answers exactly
    whether the candidate is the dyadic index of `g`'s output at that
    resolution. This is how a Clay-style language would have to present the
    model's data without being handed the selection as an oracle. -/
def DecidesSelection (L : ℕ → Bool) (g : C(K, ℝ)) : Prop :=
  ∀ k : ℕ, ∀ x : K, (x : ℝ) ∈ Ico (0:ℝ) 1 → g x ∈ Ico (0:ℝ) 1 ∧
    ∀ j : Fin (2^k),
      (L (Nat.pair k (Nat.pair (dyadicIndex k (x : ℝ)) j)) = true ↔
        dyadicIndex k (g x) = j)

/-- The points of `K` below `1` are dense in `K`. -/
theorem dense_selection_domain : Dense {x : K | (x : ℝ) ∈ Ico (0:ℝ) 1} := by
  rw [Metric.dense_iff]
  intro x r hr
  rcases lt_or_eq_of_le x.2.2 with hx | hx
  · exact ⟨x, Metric.mem_ball_self hr, ⟨x.2.1, hx⟩⟩
  · have hm0 : 0 < min (r/2) (1/2) := lt_min (by linarith) (by norm_num)
    have hm1 : min (r/2) (1/2) ≤ r/2 := min_le_left _ _
    have hm2 : min (r/2) (1/2) ≤ 1/2 := min_le_right _ _
    refine ⟨⟨1 - min (r/2) (1/2), Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩,
      ?_, Set.mem_Ico.mpr ⟨by linarith, by linarith⟩⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have h1 : (1 - min (r/2) (1/2)) - (x : ℝ) = -(min (r/2) (1/2)) := by
      rw [hx]; ring
    rw [h1, abs_neg, abs_of_pos hm0]
    linarith

/-- A language decides at most one selection (mirrors
    `computesSelection_unique`). -/
theorem decidesSelection_unique (L : ℕ → Bool) (g h : C(K, ℝ))
    (hg : DecidesSelection L g) (hh : DecidesSelection L h) : g = h := by
  have key : ∀ x : K, (x : ℝ) ∈ Ico (0:ℝ) 1 → g x = h x := by
    intro x hx
    have hidx : ∀ k : ℕ, dyadicIndex k (g x) = dyadicIndex k (h x) := by
      intro k
      have h1 := (hg k x hx).2 (dyadicIndex k (g x))
      have h2 := (hh k x hx).2 (dyadicIndex k (g x))
      exact (h2.mp (h1.mpr rfl)).symm
    have hbound : ∀ k : ℕ, |g x - h x| < (2^k : ℝ)⁻¹ := by
      intro k
      have hgmem := mem_dyadic_index (k := k) (hg k x hx).1
      have hhmem := mem_dyadic_index (k := k) (hh k x hx).1
      rw [← hidx k] at hhmem
      exact dyadic_width hgmem hhmem
    exact sub_eq_zero.mp (by
      simpa using le_antisymm
        (le_of_tendsto_of_tendsto' tendsto_const_nhds
          (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
          fun k => le_of_lt (hbound k))
        (abs_nonneg _))
  exact DFunLike.coe_injective
    (Continuous.ext_on dense_selection_domain g.continuous h.continuous
      fun x hx => key x hx)

/-- The selections decided by some computable language form a countable set
    (mirrors `countable_computable_selections`). -/
theorem countable_language_decided_selections :
    {g : C(K, ℝ) | ∃ L : ℕ → Bool, Computable L ∧ DecidesSelection L g}.Countable := by
  have hsub : {g : C(K, ℝ) | ∃ L : ℕ → Bool, Computable L ∧ DecidesSelection L g} ⊆
      ⋃ L ∈ {L : ℕ → Bool | Computable L}, {g : C(K, ℝ) | DecidesSelection L g} := by
    rintro g ⟨L, hL, hLg⟩
    exact Set.mem_biUnion hL hLg
  exact Set.Countable.mono hsub
    (countable_computable_bool.biUnion fun L _ =>
      Set.Subsingleton.countable fun g hg h hh => decidesSelection_unique L g h hg hh)

/-- Prior-almost-surely, NO computable language decides the selected
    function's data. Compare `almost_all_not_computable`: this variant is
    phrased for Clay-style decision problems (`ℕ → Bool`) rather than codes. -/
theorem selection_not_language_decidable :
    prior {g : C(K, ℝ) | ∃ L : ℕ → Bool, Computable L ∧ DecidesSelection L g} = 0 :=
  countable_null prior countable_language_decided_selections

/-- **T5: the model/Clay disjointness theorem (Tier C, made checkable).**

    Let `NP` be ANY collection of languages all of whose members are
    computable — as is every faithful formalization of the Clay classes `P`
    and `NP`, since `NP ⊆ EXPTIME` and exponential-time machines are total.
    Then, prior-almost-surely, no member of the collection decides the
    selected function's data: the model's hard object lies outside the entire
    arena in which the Clay problem is played.

    Consequently the model separation `model_P_ne_NP` exhibits no `NP`
    language outside `P`, and the Clay statement says nothing about this
    model: the two statements concern disjoint arenas. This theorem is the
    machine-checked form of that disjointness. It is NOT the Clay Millennium
    statement `P ≠ NP`, it does not define the Clay classes, and no
    implication in either direction between `model_P_ne_NP` and the Clay
    statement is formalized — see Part 6 of `PNP_IMPLEMENTATION_PLAN.md`. -/
theorem model_vs_clay_disjointness (NP : Set (ℕ → Bool))
    (hNP : ∀ L ∈ NP, Computable L) :
    prior {g : C(K, ℝ) | ∃ L ∈ NP, DecidesSelection L g} = 0 := by
  refine measure_mono_null ?_ selection_not_language_decidable
  rintro g ⟨L, hL, hLg⟩
  exact ⟨L, hNP L hL, hLg⟩

/-! ### T4. Realistic version (§7) — OPEN

The §7 argument ("an approximately-deterministic selection admits no
polynomial-time approximation in the `L^∞` sense, prior-a.s.") is only a sketch
in `pnp.tex`; there is no complete English proof to transcribe, and stating a
precise, non-vacuous, and faithful Lean statement is itself a research task.

Note in particular that a *purely analytic* approximation statement would be
false: polynomials are dense in `C([0,1])` and in `L²([0,1])` (see
`SphereGaussian` / standard Stone–Weierstrass), so every continuous selection
function is uniformly approximable by polynomials.  The §7 claim concerns
*computational* (polynomial-time) approximation, which is a different and
subtler notion.  We therefore deliberately leave T4 unformalized rather than
commit to a possibly-incorrect statement.  See `PNP_IMPLEMENTATION_PLAN.md`,
Part 5/T4. -/

end PnpProof
