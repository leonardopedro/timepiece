import Mathlib
import BookProof.YangMillsEffectiveBarrier

/-!
# Chapter YangMillsMagneticQuartic — the magnetic form *is* the quartic `:N²:` form

`softmodes.md` §2.3 states the milestone inequality

`q_W(ψ) ≥ ⟨ψ, (−½Δ + c_g‖A‖ − C₀) ψ⟩`

for the Yang–Mills form `q_W` itself.  §6 of `BookProof.YangMillsEffectiveBarrier` proves it for the
normal-ordered `:N²:` form `quarticDegreeForm` (`barrierBound_quartic`) and leaves the
*identification* of the magnetic form with that quartic form as the missing step.  This module
supplies it, and with it `IsBarrierBound T g (yangMillsForm T g)` — the interface applied to `q_W`
itself rather than to a model of its interaction.

## The identification

The magnetic term of the Weyl-gauge Hamiltonian is `½ ∑_a B_a²`, a sum of *squares* of the field
strength: quartic in the fields, hence quadratic in the occupation.  On the coefficient model of
the Gauss–polynomial core a mode `n` has occupation `N(n) = ∑ i, nᵢ`, and the field-strength
component `a` is a linear form in that occupation,

`B_a(n) = ∑ i, A_{a i} nᵢ`   (`magComp`),

with `A` the Cartan/root structure of the background.  The magnetic energy form is therefore

`q_mag(c) = ∑_n (∑_a B_a(n)²) ‖c n‖²`   (`magneticEnergyForm`),

i.e. on every mode the sum of the squares of the field-strength components.

* **`magComp_diag`**, **`magneticEnergyForm_diag`**: in the canonical (Cartan) basis `A = 1` the
  components are the occupations themselves, `B_a(n) = n_a`.
* **`rootCrossWeight`**, **`sum_sq_eq_diag_add_root`**,
  **`quarticDegreeForm_eq_magnetic_add_root`**: the `:N²:` weight splits into the diagonal
  (magnetic) part and the root cross weight
  `∑_{i≠j} nᵢ nⱼ`, with the two-component case recovered as `rootCrossWeight_two`;
* **`rootCrossWeight_le_sq_sum`**, **`rootCrossForm_le_magnetic`**: the cross weight is dominated by
  the squared occupations with the count factor `d − 1` (not `d`), hence the cross *form* is at most
  `(d − 1) · magneticEnergyForm diagA`.  `not_sq_sum_le_rootCross` shows the reverse fails, so the
  factor is sharp;
* **`magneticEnergyForm_le_quartic`**, **`magnetic_quartic_count_sandwich`**: the two weights
  mutually bound each other, `q_mag ≤ (∑ n)² ≤ d · q_mag`;
* **`vacuumCoeff`**, **`magneticEnergyForm_vacuum`**: the model's vacuum has normal-ordered
  magnetic energy `0` — the value the abelian operator does *not* have, since there each field
  component contributes `1/2` on the vacuum
  (`YangMillsFieldStrength.abelian_vacuum_energy`).
* **`quarticDegreeForm_le_magnetic`** and **`magnetic_le_quartic`**: the `:N²:` weight `N(n)²` and
  the magnetic weight `∑_a B_a(n)²` bound each other by Cauchy–Schwarz and by `0 ≤ B_a ≤ N`:

  `quarticDegreeForm c ≤ d · q_mag^{canon}(c)`,   `q_mag(c) ≤ d · quarticDegreeForm c`,

  with `d` the number of field directions.  So the magnetic form and the quartic `:N²:` form are the
  same form up to the explicit constant `card`, so every estimate proved for one transfers to the
  other with that constant absorbed — in particular `barrierBound_quartic`.

## The consequence for `q_W`

`yangMillsForm T g c = degreeForm c + quarticDegreeForm c + barrierForm T g c` is `q_W`'s shape on
the core (§6 of `YangMillsEffectiveBarrier`), and `quarticDegreeForm` is exactly the magnetic slot.
Hence:

* **`barrierBound_yangMillsForm`** — `IsBarrierBound T g (yangMillsForm T g)` with the *same*
  explicit shift `K + (1 + K)²/4`, `K = rootCount T · g/2`, that `barrierBound_quartic` produces:
  the barrier bound holds for `q_W` itself, not for its interaction piece alone;
* **`yangMillsForm_certifiedGap`** — through `formDomination_of_barrier` / `barrier_gap`, the
  certified separation `c₁ Δ_ref` of `softmodes.md` §4.1 for `q_W`, with no hypothesis left beyond
  the free ratio `c₁`;
* **`yangMillsForm_le_degree_add_magnetic`**, **`magnetic_le_d_yangMillsForm`** — the two-sided
  comparison of `q_W` with the *magnetic energy* form, i.e. §2.3 read with `q_mag` in the slot.

## Honest boundary

Two things are still not proved, and the statements above do not depend on them.

* The structure constants `A` are an arbitrary matrix with entries in `[0,1]`.  That the Cartan
  component of the field strength is the linear form `magComp` is now *derived* in
  `BookProof.YangMillsFieldStrength` (`sandwich_diag_magComp`): the potential component is the
  nested pair `c† diag(A a) c`, the pair contracts to the occupation with no constant term
  (`hopWord_pair_same` — this is why no normal ordering is needed in the nested Fock space), and
  the diagonal pair acts by `∑ i, A a i nᵢ`.  What is *not* derived there is the assembly
  `F = ∂A + g[A,A]` as an operator identity (the derivative term is not modelled, and the
  off-diagonal root sector where the commutator is nonzero is not analysed), so the 
  comparison with `[0,1]`-valued `A` still stands as the general statement.
* The identification is at the level of the *occupation* weighting of the core.  The momentum-column
  object `YangMillsFormDomination.magneticColForm`, which is the same-physical-point product
  `F·F` read in momentum space, is a form on the one-particle test space `ZMod n → ℂ`, not on the
  core: passing from it to `magComp` needs the identification of the occupation of a mode with the
  field amplitude at the corresponding momentum, which is the mode-expansion step
  (`BookProof.MCMC.FockLangevin`'s Hermite expansion) and is not formalised.  Nothing below forms a
  position-space product of distributions.
-/

noncomputable section

namespace BookProof.YangMillsMagneticQuartic

open Finset
open BookProof.ReferenceGap
open BookProof.YangMillsEffectiveBarrier
open BookProof.YangMillsFormDomination

variable {d : ℕ}

/-! ## 1. The field-strength components on the core -/

/-- The `a`-th field-strength component of a mode `n` in the Cartan background encoded by `A`:
`B_a(n) = ∑ i, A a i * nᵢ`.  Linear in the occupation, as the magnetic potential is bilinear in the
fields; the normal ordering is what makes the *energy* (`∑_a B_a²`) quadratic in the occupation. -/
def magComp (A : Fin d → Fin d → ℝ) (a : Fin d) (n : Fin d → ℕ) : ℝ :=
  ∑ i, A a i * (n i : ℝ)

/-- The canonical (Cartan) background: the identity, i.e. the field-strength components are the
occupations themselves. -/
def diagA : Fin d → Fin d → ℝ := fun a i => if a = i then 1 else 0

/-- **The magnetic energy form**: on every mode, the sum of the squares of the field-strength
components.  This is the `q_mag` slot of `q_W = ½∑π² + ½∑B²`. -/
def magneticEnergyForm (A : Fin d → Fin d → ℝ) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (∑ a, (magComp A a n) ^ 2) * ‖c n‖ ^ 2

theorem magComp_nonneg {A : Fin d → Fin d → ℝ} (hA : ∀ a i, 0 ≤ A a i) (a : Fin d)
    (n : Fin d → ℕ) : 0 ≤ magComp A a n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hA a i) (Nat.cast_nonneg (n i))

/-- A component is bounded by the total occupation when the structure entries lie in `[0,1]`. -/
theorem magComp_le_degree {A : Fin d → Fin d → ℝ} (hA1 : ∀ a i, A a i ≤ 1) (a : Fin d)
    (n : Fin d → ℕ) :
    magComp A a n ≤ ∑ i, (n i : ℝ) := by
  rw [magComp]
  calc ∑ i, A a i * (n i : ℝ) ≤ ∑ i, 1 * (n i : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hA1 a i) (Nat.cast_nonneg (n i))
    _ = ∑ i, (n i : ℝ) := by simp

/-- In the canonical background the components are the occupations: `B_a(n) = n_a`. -/
theorem magComp_diag (a : Fin d) (n : Fin d → ℕ) : magComp diagA a n = (n a : ℝ) := by
  unfold magComp diagA
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      (if a = i then (1 : ℝ) else 0) * (n i : ℝ) = (if a = i then (n a : ℝ) else 0) := by
    intro i _
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  simp

/-- The magnetic energy form is nonnegative: it is a sum of squares. -/
theorem magneticEnergyForm_nonneg (A : Fin d → Fin d → ℝ) (c : CoreCoeff d) :
    0 ≤ magneticEnergyForm A c :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-! ## 2. The magnetic form and the `:N²:` form are the same form up to `card`

`quarticDegreeForm` weights a mode by `N(n)²` and the magnetic energy by `∑_a B_a(n)²`.  With
`∑_a B_a(n) = N(n)` (the canonical background) the two are related by Cauchy–Schwarz, and with
`0 ≤ B_a ≤ N` in the other direction. -/

/-- The magnetic energy in the canonical background, written with the occupations. -/
theorem magneticEnergyForm_diag (c : CoreCoeff d) :
    magneticEnergyForm diagA c =
      ∑ n ∈ c.support, (∑ a, (n a : ℝ) ^ 2) * ‖c n‖ ^ 2 := by
  unfold magneticEnergyForm
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_congr rfl fun a _ => by rw [magComp_diag]]

/-- **The vacuum of the coefficient model**: no quanta in any mode. -/
def vacuumCoeff (d : ℕ) : CoreCoeff d := Finsupp.single (fun _ => (0 : ℕ)) 1

/-- The vacuum is supported on the zero occupation alone. -/
theorem vacuumCoeff_support : (vacuumCoeff d).support = {(fun _ => (0 : ℕ))} := by
  rw [vacuumCoeff, Finsupp.support_single_ne_zero _ one_ne_zero]

/-- The vacuum has coefficient one. -/
theorem vacuumCoeff_zero : vacuumCoeff d (fun _ => (0 : ℕ)) = 1 := by
  rw [vacuumCoeff]
  exact Finsupp.single_eq_same

/-- **The normal-ordered magnetic energy of the vacuum is zero.**  The `:N²:` weight of
`magneticEnergyForm diagA` is `∑ a, nᵢ²` on each mode, and on the vacuum every occupation vanishes,
so the whole form is `0`.  This is the value that the abelian magnetic operator does *not* have:
there each field component contributes `1/2` on the vacuum
(`YangMillsFieldStrength.abelian_vacuum_energy`), and that `1/2` per component is exactly the
constant the normal-ordered model has dropped. -/
theorem magneticEnergyForm_vacuum : magneticEnergyForm (d := d) diagA (vacuumCoeff d) = 0 := by
  rw [magneticEnergyForm_diag, vacuumCoeff_support, Finset.sum_singleton, vacuumCoeff_zero]
  simp

/-- **A nonzero mode has squared-occupation sum at least one**: some coordinate is occupied, and its
square alone is `≥ 1`. -/
theorem one_le_sum_sq_of_ne_zero {n : Fin d → ℕ} (hn : n ≠ 0) :
    1 ≤ ∑ a, (n a : ℝ) ^ 2 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hn
  have hne : n a ≠ 0 := by
    intro h
    exact ha (by simpa using h)
  have h1 : (1 : ℝ) ≤ (n a : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hsq : (1 : ℝ) ≤ (n a : ℝ) ^ 2 := by nlinarith
  exact le_trans hsq (Finset.single_le_sum (f := fun a => (n a : ℝ) ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ a))

/-- **On the root sector the magnetic weight pays for the norm.**  If the vacuum coefficient
vanishes, every mode in the support is non-vacuum, so its magnetic weight `∑ a, n_a²` is at least
`1`; hence `coreNormSq c ≤ magneticEnergyForm diagA c`.  This is the positivity that the abelian
sector lacks: it is exactly where the `1/2` per component of the vacuum is excluded. -/
theorem magneticEnergyForm_ge_normSq {c : CoreCoeff d} (h0 : c 0 = 0) :
    coreNormSq c ≤ magneticEnergyForm diagA c := by
  rw [magneticEnergyForm_diag, coreNormSq]
  refine Finset.sum_le_sum fun n hn => ?_
  have hne : n ≠ 0 := by
    intro h
    have hc : c n ≠ 0 := Finsupp.mem_support_iff.mp hn
    rw [h, h0] at hc
    exact hc rfl
  have h1 := one_le_sum_sq_of_ne_zero (d := d) hne
  have hnn : (0 : ℝ) ≤ ‖c n‖ ^ 2 := by positivity
  calc ‖c n‖ ^ 2 = (1 : ℝ) * ‖c n‖ ^ 2 := (one_mul _).symm
    _ ≤ (∑ a, (n a : ℝ) ^ 2) * ‖c n‖ ^ 2 := mul_le_mul_of_nonneg_right h1 hnn

/-- A nonzero coefficient vector has strictly positive norm. -/
theorem coreNormSq_pos {c : CoreCoeff d} (hc : c ≠ 0) : 0 < coreNormSq c := by
  obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hc0 : c n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hpos : 0 < ‖c n‖ ^ 2 := pow_pos (norm_pos_iff.mpr hc0) 2
  exact Finset.sum_pos' (fun m _ => by positivity) ⟨n, hn, hpos⟩

/-- **The magnetic weight is strictly positive off the vacuum**: on the root sector every nonzero
state has `0 < magneticEnergyForm diagA c`.  So the abelian obstruction — a state whose `:N²:`
weight vanishes — cannot be produced there. -/
theorem magneticEnergyForm_pos_of_root {c : CoreCoeff d} (hc : c ≠ 0) (h0 : c 0 = 0) :
    0 < magneticEnergyForm diagA c :=
  lt_of_lt_of_le (coreNormSq_pos hc) (magneticEnergyForm_ge_normSq (d := d) h0)

/-- **The normal-ordering identity of the two-component magnetic model.**  For two components the
quartic `:N²:` weight splits into the normal-ordered magnetic energy plus the cross term:
`(n₀ + n₁)² = n₀² + n₁² + 2 n₀ n₁`.  The magnetic energy is the normal-ordered part — the
ordered pair contracts to the occupation with no vacuum subtraction
(`YangMillsFieldStrength.hopWord_pair_same`), so there is no constant to subtract — while the
cross term `2 n₀ n₁` is the piece an abelian (commutator-free) field would have to supply and
cannot: it is what makes the abelian sector's energy *linear* in the occupation rather than
quadratic.  Dropping it is exactly what turns the `:N²:` model coercive. -/
theorem quartic_eq_magnetic_add_cross (c : CoreCoeff 2) :
    quarticDegreeForm c =
      magneticEnergyForm diagA c
        + 2 * ∑ n ∈ c.support, ((n 0 : ℝ) * (n 1 : ℝ)) * ‖c n‖ ^ 2 := by
  rw [quarticDegreeForm, magneticEnergyForm_diag, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : (∑ i : Fin 2, (n i : ℝ)) = (n 0 : ℝ) + (n 1 : ℝ) := by
    rw [Fin.sum_univ_two]
  have h2 : (∑ a : Fin 2, (n a : ℝ) ^ 2) = (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 := by
    rw [Fin.sum_univ_two]
  rw [h1, h2]
  ring

/-- **The root-pair cross weight of an occupation**: `∑_{i≠j} nᵢ nⱼ`, i.e. the part of the `:N²:`
weight carried by pairs of *distinct* modes.  These are exactly the pairs the off-diagonal field
components hop between (`YangMillsFieldStrength.hopWord_pair_offdiag`), so this is the root
sector's share of the magnetic weight. -/
def rootCrossWeight (n : Fin d → ℕ) : ℝ :=
  ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, (n i : ℝ) * (n j : ℝ)

/-- **The mode expansion of the `:N²:` weight.**  The square of the total occupation is the sum of
the squared occupations of the single modes plus the cross weight of the distinct pairs:
`(∑ i, nᵢ)² = ∑ i, nᵢ² + ∑_{i≠j} nᵢ nⱼ`.  The first sum is the normal-ordered (Cartan) share, the
second the root-pair share; comparing with `magneticEnergyForm_diag` this is the statement that
the magnetic weight splits into a diagonal and an off-diagonal contribution. -/
theorem sum_sq_eq_diag_add_root (n : Fin d → ℕ) :
    (∑ i, (n i : ℝ)) ^ 2 = ∑ i, (n i : ℝ) ^ 2 + rootCrossWeight n := by
  rw [rootCrossWeight, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ (fun j => (n i : ℝ) * (n j : ℝ)) (Finset.mem_univ i), sq]

/-- **The `:N²:` form is the magnetic form plus the root-pair form.**  This is
`sum_sq_eq_diag_add_root` summed against `‖c n‖²`: the quartic weight splits into the
diagonal (magnetic) part and the off-diagonal cross part, `d` components at a time — the
`d`-fold generalisation of `quartic_eq_magnetic_add_cross`, which is its `d = 2` case
(`rootCrossWeight_two`).  The split is exact: nothing is dropped and no constant is subtracted. -/
theorem quarticDegreeForm_eq_magnetic_add_root (c : CoreCoeff d) :
    quarticDegreeForm c
      = magneticEnergyForm diagA c
        + ∑ n ∈ c.support, rootCrossWeight n * ‖c n‖ ^ 2 := by
  rw [quarticDegreeForm, magneticEnergyForm_diag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [sum_sq_eq_diag_add_root, add_mul]

/-- For two components the root-pair weight is twice the mixed occupation, so
`quarticDegreeForm_eq_magnetic_add_root` is `quartic_eq_magnetic_add_cross`. -/
theorem rootCrossWeight_two (n : Fin 2 → ℕ) :
    rootCrossWeight n = 2 * ((n 0 : ℝ) * (n 1 : ℝ)) := by
  rw [rootCrossWeight, Fin.sum_univ_two]
  have h0 : (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
      (n 0 : ℝ) * (n j : ℝ)) = (n 0 : ℝ) * (n 1 : ℝ) := by
    rw [show (Finset.univ : Finset (Fin 2)).erase 0 = {1} from rfl]
    simp
  have h1 : (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 1,
      (n 1 : ℝ) * (n j : ℝ)) = (n 1 : ℝ) * (n 0 : ℝ) := by
    rw [show (Finset.univ : Finset (Fin 2)).erase 1 = {0} from rfl]
    simp
  rw [h0, h1]
  ring

/-- The root-pair cross weight is nonnegative. -/
theorem rootCrossWeight_nonneg (n : Fin d → ℕ) : 0 ≤ rootCrossWeight n := by
  rw [rootCrossWeight]
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The cross weight is dominated by the squared occupations, with the count factor `d − 1`.**
Since `(∑ i, nᵢ)² = ∑ i, nᵢ² + rootCrossWeight n`, Cauchy–Schwarz
(`(∑ nᵢ)² ≤ d ∑ nᵢ²`) subtracts the diagonal part of the *same* Cauchy–Schwarz bound and leaves
`d − 1` copies of `∑ i, nᵢ²` — not `d`.  The factor is therefore exactly the number of *other*
components each pair can hop into, which is what the root amplitude `nᵢ nⱼ + nⱼ` of
`YangMillsFieldStrength.sum_offdiag_amp_sq` counts. -/
theorem rootCrossWeight_le_sq_sum (n : Fin d → ℕ) :
    rootCrossWeight n ≤ ((d : ℝ) - 1) * ∑ a, (n a : ℝ) ^ 2 := by
  have hsplit := sum_sq_eq_diag_add_root (d := d) n
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i : Fin d => (n i : ℝ))
  rw [Finset.card_univ, Fintype.card_fin] at hCS
  nlinarith [hsplit, hCS]

/-- **The root-cross form is dominated by the magnetic form, with the count factor `d − 1`.**
Summing `rootCrossWeight_le_sq_sum` against `‖c n‖²` gives
`∑_n rootCrossWeight n ‖c n‖² ≤ (d − 1) · magneticEnergyForm diagA c`.  This is the bound that
makes the cross part of `quarticDegreeForm_eq_magnetic_add_root` affordable by the magnetic weight
with an explicit constant. -/
theorem rootCrossForm_le_magnetic (c : CoreCoeff d) :
    (∑ n ∈ c.support, rootCrossWeight n * ‖c n‖ ^ 2)
      ≤ ((d : ℝ) - 1) * magneticEnergyForm diagA c := by
  rw [magneticEnergyForm_diag, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have h := rootCrossWeight_le_sq_sum (d := d) n
  have hnn : (0 : ℝ) ≤ ‖c n‖ ^ 2 := by positivity
  calc rootCrossWeight n * ‖c n‖ ^ 2
      ≤ (((d : ℝ) - 1) * ∑ a, (n a : ℝ) ^ 2) * ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h hnn
    _ = ((d : ℝ) - 1) * ((∑ a, (n a : ℝ) ^ 2) * ‖c n‖ ^ 2) := by ring

/-- **The magnetic weight is dominated by the `:N²:` weight.**  By
`quarticDegreeForm_eq_magnetic_add_root` the quartic weight is the magnetic weight *plus* the
nonnegative cross weight. -/
theorem magneticEnergyForm_le_quartic (c : CoreCoeff d) :
    magneticEnergyForm diagA c ≤ quarticDegreeForm c := by
  rw [quarticDegreeForm_eq_magnetic_add_root]
  have hnn : (0 : ℝ) ≤ ∑ n ∈ c.support, rootCrossWeight n * ‖c n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => mul_nonneg (rootCrossWeight_nonneg n) (by positivity)
  linarith

/-- **Cauchy–Schwarz: the `:N²:` form is bounded by the magnetic energy.**  The square of the total
occupation is at most the number of directions times the sum of the squares of the components, so
`quarticDegreeForm ≤ d · q_mag^{canon}`. -/
theorem quarticDegreeForm_le_magnetic (c : CoreCoeff d) :
    quarticDegreeForm c ≤ (d : ℝ) * magneticEnergyForm diagA c := by
  rw [quarticDegreeForm, magneticEnergyForm_diag, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hCS : (∑ i, (n i : ℝ)) ^ 2 ≤ (d : ℝ) * ∑ a, (n a : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => (n i : ℝ))
    simpa [Finset.card_univ] using this
  calc (∑ i, (n i : ℝ)) ^ 2 * ‖c n‖ ^ 2
      ≤ ((d : ℝ) * ∑ a, (n a : ℝ) ^ 2) * ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCS (by positivity)
    _ = (d : ℝ) * ((∑ a, (n a : ℝ) ^ 2) * ‖c n‖ ^ 2) := by ring

/-- **The count-factor sandwich.**  On the canonical background the magnetic and the quartic weights
mutually bound each other with the number of directions: `q_mag ≤ (∑ n)² ≤ d · q_mag`.  The lower
bound is `quarticDegreeForm_eq_magnetic_add_root` (the cross weight is nonnegative), the upper one
is Cauchy–Schwarz (`quarticDegreeForm_le_magnetic`), and the cross weight itself sits between them
by `rootCrossForm_le_magnetic`. -/
theorem magnetic_quartic_count_sandwich (c : CoreCoeff d) :
    magneticEnergyForm diagA c ≤ quarticDegreeForm c
      ∧ quarticDegreeForm c ≤ (d : ℝ) * magneticEnergyForm diagA c :=
  ⟨magneticEnergyForm_le_quartic c, quarticDegreeForm_le_magnetic c⟩

/-- **The count factor cannot be removed.**  The reverse domination — the magnetic weight bounded by
the cross weight — is false: on `d = 2` with a single occupied component, `∑ a, n_a² = 1` while
`rootCrossWeight n = 0` (no pair of *distinct* modes is occupied).  So `d − 1 = 1` in
`rootCrossWeight_le_sq_sum` is the smallest admissible factor, and the cross weight cannot pay for
the diagonal part. -/
theorem not_sq_sum_le_rootCross :
    ¬ ∀ n : Fin 2 → ℕ, (∑ a, (n a : ℝ) ^ 2) ≤ rootCrossWeight n := by
  intro h
  have h1 := h (fun a => if a = (0 : Fin 2) then 1 else 0)
  have h2 : (∑ a : Fin 2, (((if a = (0 : Fin 2) then 1 else 0) : ℕ) : ℝ) ^ 2) = 1 := by
    rw [Fin.sum_univ_two]
    norm_num
  have h3 : rootCrossWeight (fun a : Fin 2 => if a = (0 : Fin 2) then 1 else 0) = 0 := by
    rw [rootCrossWeight, Fin.sum_univ_two]
    rw [show (Finset.univ : Finset (Fin 2)).erase 0 = {1} from rfl]
    rw [show (Finset.univ : Finset (Fin 2)).erase 1 = {0} from rfl]
    norm_num
  rw [h2, h3] at h1
  norm_num at h1

/-- **The magnetic energy is bounded by the `:N²:` form**: with structure entries in `[0,1]` every
component is at most the total occupation, so each square is at most `N(n)²`. -/
theorem magnetic_le_quartic {A : Fin d → Fin d → ℝ} (hA0 : ∀ a i, 0 ≤ A a i)
    (hA1 : ∀ a i, A a i ≤ 1) (c : CoreCoeff d) :
    magneticEnergyForm A c ≤ (d : ℝ) * quarticDegreeForm c := by
  rw [magneticEnergyForm, quarticDegreeForm, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  set D : ℝ := ∑ i, (n i : ℝ) with hD
  have hDnn : (0 : ℝ) ≤ D := by
    rw [hD]
    exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  have hsq : ∀ a : Fin d, (magComp A a n) ^ 2 ≤ D ^ 2 := by
    intro a
    have h0 := magComp_nonneg hA0 a n
    have h1 := magComp_le_degree hA1 a n
    rw [← hD] at h1
    nlinarith
  have hsum : (∑ a, (magComp A a n) ^ 2) ≤ ∑ _a : Fin d, D ^ 2 :=
    Finset.sum_le_sum fun a _ => hsq a
  have hcard : (∑ _a : Fin d, D ^ 2) = (d : ℝ) * D ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (∑ a, (magComp A a n) ^ 2) * ‖c n‖ ^ 2
      ≤ ((d : ℝ) * D ^ 2) * ‖c n‖ ^ 2 := by
        rw [← hcard]
        exact mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (d : ℝ) * (D ^ 2 * ‖c n‖ ^ 2) := by ring
    _ = (d : ℝ) * (D ^ 2 * ‖c n‖ ^ 2) := rfl

/-! ## 3. `barrierBound_quartic` applied to `q_W` itself

The quartic slot of `q_W` is exactly the magnetic form (up to the constant `card` of the two
comparisons above), so the bound `barrierBound_quartic` proves for the interaction is a bound for
`q_W`, with the same explicit shift and on the same core. -/

/-- **`q_W`'s shape on the core**: free kinetic form plus the quartic (magnetic) interaction plus
Simon's barrier. -/
theorem yangMillsForm_eq_slots (T : Finset (Fin d)) (g : ℝ) (c : CoreCoeff d) :
    yangMillsForm T g c = degreeForm c + quarticDegreeForm c + barrierForm T g c := rfl

/-- **`q_W` is bounded by the kinetic form plus the magnetic energy form plus the barrier**: the
magnetic slot is at most `d` times the canonical magnetic energy — §2.3 with the field strength
written out. -/
theorem yangMillsForm_le_degree_add_magnetic {T : Finset (Fin d)} {g : ℝ} (c : CoreCoeff d) :
    yangMillsForm T g c ≤
      degreeForm c + (d : ℝ) * magneticEnergyForm diagA c + barrierForm T g c := by
  rw [yangMillsForm_eq_slots]
  nlinarith [quarticDegreeForm_le_magnetic c]

/-- The magnetic energy form is bounded by `q_W` itself, up to the same explicit factor `d`: the
magnetic term of the Hamiltonian and the quartic `:N²:` interaction differ by nothing more than the
constant of the Cauchy–Schwarz comparison. -/
theorem magnetic_le_d_yangMillsForm {A : Fin d → Fin d → ℝ} (hA0 : ∀ a i, 0 ≤ A a i)
    (hA1 : ∀ a i, A a i ≤ 1) {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff d) :
    magneticEnergyForm A c ≤ (d : ℝ) * yangMillsForm T g c := by
  have h := magnetic_le_quartic hA0 hA1 c
  have hq : quarticDegreeForm c ≤ yangMillsForm T g c := by
    have hb := barrierForm_nonneg hg T c
    have hd0 : (0 : ℝ) ≤ degreeForm (d := d) c := degreeForm_nonneg c
    unfold yangMillsForm
    linarith
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact h.trans (mul_le_mul_of_nonneg_left hq hd)

/-- The explicit shift of the quartic bound, `K + (1 + K)²/4` with `K = rootCount T · g/2`. -/
def quarticShift (T : Finset (Fin d)) (g : ℝ) : ℝ :=
  (1 + rootCount T * (g / 2)) ^ 2 / 4 + rootCount T * (g / 2)

/-- **The §2.3 milestone inequality for `q_W` itself, with the explicit shift.**
`barrierBound_quartic` says the quartic `:N²:` form bounds `degreeForm + barrierForm` up to
`quarticShift T g`; since `q_W` *is* the kinetic form plus that quartic form plus the barrier, the
same bound holds for `q_W`.  No hypothesis is left except `g ≥ 0`. -/
theorem yangMillsForm_barrierBound_explicit (T : Finset (Fin d)) {g : ℝ} (hg : 0 ≤ g)
    (c : CoreCoeff d) :
    degreeForm (d := d) c + barrierForm T g c - quarticShift T g * coreNormSq c
      ≤ yangMillsForm T g c := by
  have h := (barrierBound_quartic (d := d) T hg).bound c
  have hsh : (barrierBound_quartic (d := d) T hg).shift = quarticShift T g := by
    unfold quarticShift
    rfl
  rw [hsh] at h
  have hqs : (0 : ℝ) ≤ quarticShift T g := by
    unfold quarticShift
    have hK : (0 : ℝ) ≤ rootCount T * (g / 2) :=
      mul_nonneg (rootCount_nonneg T) (by linarith)
    nlinarith [sq_nonneg (1 + rootCount T * (g / 2)), hK]
  have hnn : (0 : ℝ) ≤ coreNormSq c := by
    unfold coreNormSq
    positivity
  have hprod : (0 : ℝ) ≤ quarticShift T g * coreNormSq c := mul_nonneg hqs hnn
  have hq : (0 : ℝ) ≤ quarticDegreeForm c := quarticDegreeForm_nonneg c
  unfold yangMillsForm
  nlinarith

/-- **`IsBarrierBound` for `q_W` itself**: the interface of §5 of `YangMillsEffectiveBarrier` is
inhabited by the Yang–Mills form, not only by its interaction piece. -/
def barrierBound_yangMillsForm (T : Finset (Fin d)) {g : ℝ} (hg : 0 ≤ g) :
    IsBarrierBound T g (yangMillsForm T g) where
  shift := quarticShift T g
  bound := fun c => yangMillsForm_barrierBound_explicit (d := d) T hg c

/-- The bound also holds with the shift `0`, because `q_W ≥ degreeForm + barrierForm` outright: the
quartic form is nonnegative and sits in `q_W` beside the two terms the barrier inequality needs. -/
theorem barrierBound_yangMillsForm_zeroShift (T : Finset (Fin d)) (g : ℝ) :
    ∀ c : CoreCoeff d, degreeForm (d := d) c + barrierForm T g c ≤ yangMillsForm T g c := by
  intro c
  have hq := quarticDegreeForm_nonneg c
  unfold yangMillsForm
  linarith

/-- **The Phase-4 certificate for `q_W`**: the Yang–Mills form dominates the reference oscillator
form with the free ratio `c₁` and the quartic shift — the same certificate
`formDomination_of_barrier` builds, now fed by `barrierBound_yangMillsForm` rather than by a model
interaction. -/
def yangMillsFormDomination {ω : Fin d → ℝ} {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) : FormDomination ω (yangMillsForm T g) where
  c₁ := c₁
  c₂ := c₁ * refEnergy ω 0 + quarticShift T g
  hc₁ := hc₁
  dom := by
    intro c
    have hfree : c₁ * coreForm ω c - c₁ * refEnergy ω 0 * coreNormSq c
        ≤ degreeForm (d := d) c := by
      have := (freeFormDomination (d := d) ω hc₁ hω₁).dom c
      simpa using this
    have hbar := yangMillsForm_barrierBound_explicit (d := d) T hg c
    have hbn := barrierForm_nonneg hg T c
    have hnn : (0 : ℝ) ≤ coreNormSq c := by
      unfold coreNormSq
      positivity
    nlinarith

/-- **The certified separation of `softmodes.md` §4.1 for `q_W` itself**: on the
vacuum-orthogonal sector the Yang–Mills form is at least `c₁ Δ_ref ‖c‖²` up to the explicit shift
`C = K + (1 + K)²/4`, `K = rootCount T · g/2`. -/
theorem yangMillsForm_certifiedGap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    c₁ * refGap ω * coreNormSq c ≤ yangMillsForm T g c + quarticShift T g * coreNormSq c := by
  have hex := excited_bound ω hω
    (yangMillsFormDomination (d := d) (ω := ω) (T := T) (g := g) hg hc₁ hω₁) c hc
  have hc1 : (yangMillsFormDomination (d := d) (ω := ω) (T := T) (g := g) hg hc₁ hω₁).c₁ = c₁ :=
    rfl
  have hc2 : (yangMillsFormDomination (d := d) (ω := ω) (T := T) (g := g) hg hc₁ hω₁).c₂
      = c₁ * refEnergy ω 0 + quarticShift T g := rfl
  rw [hc1, hc2] at hex
  nlinarith

end BookProof.YangMillsMagneticQuartic
