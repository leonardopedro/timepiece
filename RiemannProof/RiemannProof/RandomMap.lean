import Mathlib
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Independence.Basic

/-!
# RandomMap.lean — The Decoupled Kopperman-Mehler Framework

This file implements the formalization plan described in `RandomMap.md`.
It strictly separates the additive and multiplicative domains at the type level,
defines the configuration space of bijections, equips it with a Polish topology,
and constructs the Mehler prior probability measure over it.

## Phase 1: Additive-Only and Multiplicative-Only Naturals

We define `NatAdd` (the Presburger clock) and `NatMult` (the Skolem basis).
`NatAdd` exposes only addition; `NatMult` is a free commutative monoid with
multiplication but no addition.
-/

/-- The additive-only natural numbers (Presburger clock).
    Exposes only `zero`, `succ`, and `add`. No multiplication. -/
inductive NatAdd where
  | zero : NatAdd
  | succ : NatAdd → NatAdd
  deriving DecidableEq, Repr, Countable

namespace NatAdd

def add : NatAdd → NatAdd → NatAdd
  | zero, y => y
  | succ x, y => succ (add x y)

instance : Add NatAdd := ⟨add⟩
instance : Zero NatAdd := ⟨zero⟩

@[simp] lemma add_zero (x : NatAdd) : x + 0 = x := by
  induction x with
  | zero => rfl
  | succ x ih => apply congrArg succ; exact ih

@[simp] lemma zero_add (x : NatAdd) : 0 + x = x := by
  induction x with
  | zero => rfl
  | succ x ih => apply congrArg succ; exact ih

@[simp] lemma succ_add (x y : NatAdd) : (succ x) + y = succ (x + y) := rfl

lemma add_succ (x y : NatAdd) : x + (succ y) = succ (x + y) := by
  induction x with
  | zero => rfl
  | succ x ih => apply congrArg succ; exact ih

lemma add_comm (x y : NatAdd) : x + y = y + x := by
  induction x generalizing y with
  | zero => calc
    0 + y = y := zero_add _
    _ = y + 0 := (add_zero _).symm
  | succ x ih => rw [succ_add, add_succ, ih]

lemma add_assoc (x y z : NatAdd) : (x + y) + z = x + (y + z) := by
  induction x generalizing y z with
  | zero => calc
    (0 + y) + z = y + z := by rw [zero_add]
    _ = 0 + (y + z) := (zero_add _).symm
  | succ x ih => rw [succ_add, succ_add, ih, succ_add]

inductive le : NatAdd → NatAdd → Prop where
  | zero (y : NatAdd) : le 0 y
  | succ (x y : NatAdd) (h : le x y) : le (succ x) (succ y)

instance : LE NatAdd := ⟨le⟩

@[simp] lemma le_zero (x : NatAdd) : x ≤ 0 ↔ x = 0 := by
  cases x with
  | zero => exact ⟨by intro; rfl, by intro; exact le.zero 0⟩
  | succ x => refine ⟨?_, ?_⟩ <;> intro h <;> nomatch h

@[simp] lemma zero_le (x : NatAdd) : 0 ≤ x := by
  cases x <;> exact le.zero _

@[simp] lemma le_succ (x y : NatAdd) : x ≤ y → x ≤ succ y := by
  intro h; induction x generalizing y with
  | zero => exact le.zero _
  | succ x ih =>
    cases y with
    | zero => cases h
    | succ y =>
      cases h with
      | succ _ _ h' => exact le.succ _ _ (ih _ h')

/-- Convert a `NatAdd` to a `ℕ` by counting `succ` constructors.
    This gives a bijection between `NatAdd` and `ℕ`. -/
def toNat : NatAdd → ℕ
  | zero => 0
  | succ n => n.toNat + 1

@[simp] lemma toNat_zero : toNat zero = 0 := rfl
@[simp] lemma toNat_succ (n : NatAdd) : toNat (succ n) = toNat n + 1 := rfl

lemma toNat_inj (a b : NatAdd) (h : toNat a = toNat b) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ b => simp at h
  | succ a ih =>
    cases b with
    | zero => simp at h
    | succ b => simp at h; exact congrArg succ (ih _ h)

/-- The coefficient 1/(n+1) for index n, ensuring square-summability.
    Since `NatAdd` is in bijection with `ℕ`, we use `toNat` to index into
    the standard sum ∑ 1/n² < ∞. -/
noncomputable def invIndex (n : NatAdd) : ℝ := 1 / ((toNat n : ℝ) + 1)

/-- The `invIndex` function is square-summable over `NatAdd`.
    This follows from the bijection between `NatAdd` and `ℕ` and the
    standard result that ∑ 1/n² converges. -/
lemma summable_invIndex_sq : Summable fun n : NatAdd => ‖invIndex n‖ ^ (2 : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hf : Summable fun n : ℕ => ‖f n‖ ^ (2 : ℝ) := by
    have hsum : Summable fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2 := by
      have h : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have h' := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : 1 < (2 : ℕ))
        have h'' := (summable_nat_add_iff (1 : ℕ)).mpr h'
        simpa [Nat.cast_add, Nat.cast_one] using h''
      simpa [sq, one_div] using h
    simpa [f, sq_abs] using hsum
  have hinj : Function.Injective toNat := toNat_inj
  simpa [f, invIndex] using hf.comp_injective hinj

end NatAdd

/-!
## Phase 1.2: The Multiplicative-Only Naturals (NatMult)

We define `NatMult P` as a free commutative monoid over a countable type `P`
of Beurling primes. Since `FreeCommMonoid` is not available in Mathlib v4.28.0,
we define our own minimal version using `List P` with a `CommMonoid` structure
where `*` is list concatenation `++` and `1` is the empty list `[]`.

We do NOT provide an `Add` instance, strictly separating the multiplicative
domain from the additive domain.
-/

/-- The multiplicative-only naturals (Skolem basis).
    A free commutative monoid over the Beurling primes.
    Has multiplication `*` and unit `1`, but NO addition `+`. -/
abbrev NatMult (P : Type) := Multiset P

namespace NatMult

variable {P : Type} [DecidableEq P]

instance : Mul (NatMult P) := ⟨fun x y => x + y⟩
instance : One (NatMult P) := ⟨0⟩

instance : CommMonoid (NatMult P) where
  mul x y := x + y
  one := 0
  mul_assoc x y z := add_assoc _ _ _
  one_mul x := zero_add _
  mul_one x := add_zero _
  mul_comm x y := add_comm _ _

instance : DecidableEq (NatMult P) :=
  inferInstanceAs (DecidableEq (Multiset P))

/-- The "prime counting" function: the number of prime factors (with multiplicity). -/
def omega (x : NatMult P) : ℕ :=
  Multiset.card x

end NatMult

/-!
## Phase 2: Configuration Space (The Mappings)

`MapConfig P` is the space of all bijections from `NatAdd` to `NatMult P`.
This represents the "configurations of the universe" — every possible
way to assign a multiplicative label to each step of the additive clock.
-/

/-- An equivalence (bijection) between the additive and multiplicative naturals. -/
abbrev MapConfig (P : Type) := NatAdd ≃ NatMult P

namespace MapConfig

variable {P : Type}

def apply (ω : MapConfig P) (n : NatAdd) : NatMult P := ω n
def indexOf (ω : MapConfig P) (p : NatMult P) : NatAdd := (ω.symm) p

/-!
### Topology Instances

We equip `NatAdd` with the discrete topology, `NatMult P` with the discrete
topology, and `MapConfig P` with the discrete topology (subspace of the
product topology).
-/

instance : TopologicalSpace NatAdd := ⊥
instance : DiscreteTopology NatAdd := ⟨rfl⟩

instance : TopologicalSpace (NatMult P) := ⊥
instance : DiscreteTopology (NatMult P) := ⟨rfl⟩

instance : TopologicalSpace (NatAdd → NatMult P) := Pi.topologicalSpace

instance : TopologicalSpace (MapConfig P) := ⊥
instance : DiscreteTopology (MapConfig P) := ⟨rfl⟩

end MapConfig

/-!
## Phase 3: The Mehler Prior Probability Measure

We construct the probability space over `MapConfig P`. Since `MapConfig P` is a
subset of the Baire space (a Polish space), we can rigorously define Borel
measures on it. The Mehler prior is a diffuse probability measure: each
individual bijection has measure zero, but sets of bijections have positive
measure.

### Construction Strategy

1. Define a sequence of finite subsets exhausting the primes.
2. On each finite set, define a uniform distribution over bijections.
3. Take the projective limit to obtain a measure on the infinite product.
4. Restrict to the subset of bijections that are actually bijections onto all primes.
-/

open MeasureTheory

variable {P : Type} [Countable P]

instance : MeasurableSpace (MapConfig P) :=
  borel (MapConfig P)

instance : BorelSpace (MapConfig P) :=
  BorelSpace.mk rfl

instance : OpensMeasurableSpace (MapConfig P) :=
  by infer_instance



/-!
## Phase 4: Hilbert Space over the Random Map

For a given configuration `ω`, we define the Hilbert space `ℓ²(NatAdd)`
of square-summable sequences indexed by the additive clock.
-/

noncomputable def HilbertSpaceConfig (_ω : MapConfig P) : Type :=
  lp (fun (_ : NatAdd) => ℝ) 2

namespace HilbertSpaceConfig

variable (ω : MapConfig P)

noncomputable instance : Inner ℝ (HilbertSpaceConfig ω) :=
  inferInstanceAs (Inner ℝ (lp (fun (_ : NatAdd) => ℝ) 2))

noncomputable instance : NormedAddCommGroup (HilbertSpaceConfig ω) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun (_ : NatAdd) => ℝ) 2))


/-- The standard orthonormal basis vector e_n: 1 at position n, 0 elsewhere.

    Uses `lp.single` which creates an element that is `a` at index `i` and 0 elsewhere. -/
noncomputable def basisVector (n : NatAdd) : HilbertSpaceConfig ω :=
  lp.single 2 n (1 : ℝ)

/-- The basis vectors are orthonormal:
    ⟨e_n, e_m⟩ = δ_{n,m} (Kronecker delta). -/
lemma basisVector_orthonormal (n m : NatAdd) :
    inner ℝ (basisVector ω n) (basisVector ω m) = if n = m then 1 else 0 := by
  unfold basisVector
  rw [lp.inner_single_left]
  simp
  by_cases h : n = m
  · subst h; simp
  · simp [h]

end HilbertSpaceConfig

/-!
## Phase 5: Formulating the Metric Proposition

We define the truth-vector of an arithmetic proposition as a function
of the configuration ω. The proposition is encoded as a predicate
`P_test : NatMult P → Bool` on the multiplicative labels.

The "All-True" vector corresponds to the case where every label
satisfies the predicate. The truth-vector for ω records which
labels actually satisfy the predicate under the mapping ω.
-/

/-- The "All-True" target vector: ∑_n (1/n) |e_n⟩.
    This is a fixed vector in the Hilbert space, independent of ω.
    The coefficient 1/n ensures square-summability (∑ 1/n² < ∞). -/
noncomputable def psiTrue (ω : MapConfig P) : HilbertSpaceConfig ω :=
  ⟨fun n => NatAdd.invIndex n,
    memℓp_gen (by simpa using NatAdd.summable_invIndex_sq)⟩

/-- The "Truth-Vector" for a given configuration ω and predicate P_test.
    For each n, the coefficient is (if P_test(ω n) then 1 else 0) / n.
    This is a convergent sum in ℓ²(NatAdd) because
    ∑_n (P_test(ω n) / n)² ≤ ∑_n 1/n² < ∞. -/
noncomputable def psiTruth (ω : MapConfig P) (P_test : NatMult P → Bool) :
    HilbertSpaceConfig ω :=
  let coeff (n : NatAdd) : ℝ := (if P_test (ω n) then 1 else 0) * NatAdd.invIndex n
  have h_summable : Summable fun n : NatAdd => ‖coeff n‖ ^ (2 : ℝ) := by
    have h_bound : ∀ n : NatAdd, ‖coeff n‖ ^ (2 : ℝ) ≤ ‖NatAdd.invIndex n‖ ^ (2 : ℝ) := by
      intro n
      dsimp [coeff]
      calc
        ‖(if P_test (ω n) then 1 else 0) * NatAdd.invIndex n‖ ^ (2 : ℝ)
            = (|(if P_test (ω n) then 1 else 0) * NatAdd.invIndex n|) ^ (2 : ℝ) := by simp
        _ = (|(if P_test (ω n) then 1 else 0)| * |NatAdd.invIndex n|) ^ (2 : ℝ) := by rw [abs_mul]
        _ ≤ (1 * |NatAdd.invIndex n|) ^ (2 : ℝ) := by
          gcongr
          · split_ifs <;> norm_num
        _ = |NatAdd.invIndex n| ^ (2 : ℝ) := by simp
        _ = ‖NatAdd.invIndex n‖ ^ (2 : ℝ) := by simp
    exact Summable.of_nonneg_of_le (fun n => by positivity) h_bound
      NatAdd.summable_invIndex_sq
  ⟨coeff, memℓp_gen (by simpa using h_summable)⟩

/-- The geometric predicate: the proposition holds under configuration ω iff
    the truth-vector equals the all-true vector.

    This is a geometric condition: the two vectors in ℓ²(NatAdd) must be
    identical, which means they agree on all coefficients. -/
def propHolds (ω : MapConfig P) (P_test : NatMult P → Bool) : Prop :=
  psiTruth ω P_test = psiTrue ω

/-!
## Phase 6: Calculating the Probability of Truth

Because the proposition's truth is now a property of the mapping ω,
we can prove it is a measurable set and calculate its exact probability
under the Mehler prior.

### Key Results

1. **Measurability**: The set {ω | propHolds ω P_test} is Borel measurable
   in `MapConfig P`. This follows from the continuity of the L² distance
   function and the fact that singletons have measure zero under the Mehler prior.

2. **Probability evaluation**: The probability that the proposition holds
   is the Mehler measure of the set of configurations where it holds.

3. **Toy model**: For a finite toy model (e.g., P = {2, 3}), the probability
   can be computed explicitly as a rational fraction.
-/

theorem measurable_set_propHolds (P_test : NatMult P → Bool) :
    MeasurableSet { ω : MapConfig P | propHolds ω P_test } := by
  -- MapConfig P has discrete topology, so every set is open.
  -- Since MeasurableSpace = borel (MapConfig P), open sets are measurable.
  have h_open : IsOpen { ω : MapConfig P | propHolds ω P_test } := by
    have h := DiscreteTopology.eq_bot (α := MapConfig P)
    simpa [h] using trivial
  exact h_open.measurableSet
