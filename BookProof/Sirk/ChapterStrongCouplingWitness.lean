import Mathlib
import BookProof.Sirk.ChapterMassErrorArithmetic

/-!
# Chapter StrongCouplingWitness — the U5 witness contract and its soundness

`softmodes.md` U5 asks for **one** specified strong coupling at which a certified
first-excitation mass exceeds its entire energy-error budget, with a recorded positive
rational margin.  Real numerical data lives in `../unfer` and is not trusted by Lean;
what this module supplies is the *contract* such data must inhabit and the soundness
theorem that an inhabited witness proves a strictly positive mass.

The four parameters of U0 are kept distinct: coupling `g_star`, physical cutoff `L`,
Krylov dimension `m`, rational order `q`, and the shift budget `N_shift`.  `g_sc` is a
**declared** dimensionless strong-coupling threshold; it is not the lattice-era `g²/2`
prediction (`ChapterSirkGapTable.strongCoupling`), which U5 explicitly excludes as a
candidate for the unchanged operator.

## Honest boundary

* The ordered true resolvent values `mu₀, mu₁` (the min–max/counting output of U3),
  the whole-space error `e_R ≤ e` and the uniform denominator margin `u0` are *fields*
  of the witness, not theorems here.  Instantiating them for `ymHamiltonian` is the
  open analytic work; this module says exactly what would have to be supplied.
* A witness at `g_star` is a statement about the operator it is instantiated on.  It is
  **not** a proof at all couplings, and it does not remove spatial, ultraviolet or
  infrared regulators.  The outer-vacuum lift (U4) needs a separate absolute bound.
* No numerical row is claimed here: `qcdG2M4Row` in `ChapterSirkGapTable` is a
  historical truncated/reflection diagnostic, not an inhabitant of this contract.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.SirkStrongCouplingWitness

open BookProof.ChapterMassErrorArithmetic

/-- The data U5 requires at one coupling, together with the proofs that the full-space
    and margin inputs have been discharged for it.  Every numerical field is a datum;
    every `Prop` field is an obligation a concrete campaign must meet. -/
structure StrongCouplingWitness where
  /-- The declared dimensionless strong-coupling threshold. -/
  g_sc : ℝ
  /-- The certified coupling, with `g_sc ≤ g_star`. -/
  g_star : ℝ
  /-- The physical basis / mode cutoff `L`. -/
  L : ℕ
  /-- The retained Krylov dimension `m`. -/
  m : ℕ
  /-- The rational / shift order `q`. -/
  q : ℕ
  /-- The shift budget `N`, distinct from `m` and from outer particle number. -/
  N_shift : ℕ
  /-- The energy scale `s(g_star) > 0`. -/
  s : ℝ
  /-- The fixed dimensionless shift `κ > 0`. -/
  kappa : ℝ
  /-- The whole-space resolvent error bound `e_R ≤ e`. -/
  e : ℝ
  /-- A denominator margin uniform over all admitted Krylov dimensions. -/
  u0 : ℝ
  /-- Largest certified resolvent value (ground). -/
  mu0hat : ℝ
  /-- Next certified resolvent value (first excitation). -/
  mu1hat : ℝ
  /-- The ordered true resolvent values supplied by the spectral count. -/
  mu0 : ℝ
  mu1 : ℝ
  /-- The recorded positive rational margin `η`. -/
  eta : ℝ

  hg_sc_pos : 0 < g_sc
  hg_star : g_sc ≤ g_star
  hs_pos : 0 < s
  hkappa_pos : 0 < kappa
  he_pos : 0 < e
  he_u0 : e < u0
  hu0_le_mu1 : u0 ≤ mu1hat
  hmu1_le_mu0 : mu1hat ≤ mu0hat
  hmu0 : |mu0 - mu0hat| ≤ e
  hmu1 : |mu1 - mu1hat| ≤ e
  heta_pos : 0 < eta
  hmargin : eta ≤ massHat s mu0hat mu1hat - uniformGapError s e u0

namespace StrongCouplingWitness

/-- The margin `η` is the witness's certified lower bound on the excitation mass. -/
def certifiedMass (W : StrongCouplingWitness) : ℝ :=
  massHat W.s W.mu0hat W.mu1hat - uniformGapError W.s W.e W.u0

theorem certifiedMass_eq (W : StrongCouplingWitness) :
    W.certifiedMass = massHat W.s W.mu0hat W.mu1hat - uniformGapError W.s W.e W.u0 := rfl

/-- The recorded margin is positive, so the witness is not vacuous. -/
theorem certifiedMass_pos (W : StrongCouplingWitness) : 0 < W.certifiedMass := by
  dsimp [certifiedMass]
  linarith [W.heta_pos, W.hmargin]

/-- The whole two-level error is below the dimension-independent envelope. -/
theorem uniform_error (W : StrongCouplingWitness) :
    gapError W.s W.e W.mu0hat W.mu1hat ≤ uniformGapError W.s W.e W.u0 := by
  exact gapError_uniform (le_of_lt W.hs_pos) W.he_pos W.he_u0 W.hu0_le_mu1 W.hmu1_le_mu0

/-- The witness stays above its declared strong-coupling threshold. -/
theorem above_threshold (W : StrongCouplingWitness) : W.g_sc ≤ W.g_star := W.hg_star

/-- Soundness: the certified mass is a lower bound on the true excitation mass. -/
theorem certifiedMass_le_mass (W : StrongCouplingWitness) :
    W.certifiedMass ≤ mass W.s W.mu0 W.mu1 := by
  have he1 : W.e < W.mu1hat := lt_of_lt_of_le W.he_u0 W.hu0_le_mu1
  have hclose := mass_error_bound (le_of_lt W.hs_pos) W.he_pos he1 W.hmu1_le_mu0
    W.hmu0 W.hmu1
  have hEg := W.uniform_error
  have hleft := (abs_le.mp hclose).1
  dsimp [certifiedMass]
  linarith

/-- **U5 soundness.**  An inhabited witness proves a strictly positive inner excitation
    mass at its coupling.  The conclusion concerns only the operator the data describes. -/
theorem mass_positive (W : StrongCouplingWitness) : 0 < mass W.s W.mu0 W.mu1 :=
  lt_of_lt_of_le W.certifiedMass_pos W.certifiedMass_le_mass

/-- The same conclusion through the margin-test lemma of the arithmetic layer. -/
theorem mass_positive_of_margin (W : StrongCouplingWitness) :
    0 < mass W.s W.mu0 W.mu1 := by
  have he1 : W.e < W.mu1hat := lt_of_lt_of_le W.he_u0 W.hu0_le_mu1
  have hclose := mass_error_bound (le_of_lt W.hs_pos) W.he_pos he1 W.hmu1_le_mu0
    W.hmu0 W.hmu1
  have hEg := W.uniform_error
  have hgaplt : gapError W.s W.e W.mu0hat W.mu1hat < massHat W.s W.mu0hat W.mu1hat := by
    linarith [W.heta_pos, W.hmargin, hEg]
  exact positive_margin hclose hgaplt

/-- The ground energy lies in its certified inverse-resolvent window. -/
theorem ground_energy_window (W : StrongCouplingWitness) :
    W.s * (1 / (W.mu0hat + W.e) - W.kappa) ≤ W.s * (1 / W.mu0 - W.kappa) ∧
      W.s * (1 / W.mu0 - W.kappa) ≤ W.s * (1 / (W.mu0hat - W.e) - W.kappa) := by
  have he0 : W.e < W.mu0hat :=
    lt_of_lt_of_le W.he_u0 (le_trans W.hu0_le_mu1 W.hmu1_le_mu0)
  exact energy_interval (le_of_lt W.hs_pos) W.he_pos he0 W.hmu0

/-- The first-excitation energy lies in its certified inverse-resolvent window. -/
theorem excited_energy_window (W : StrongCouplingWitness) :
    W.s * (1 / (W.mu1hat + W.e) - W.kappa) ≤ W.s * (1 / W.mu1 - W.kappa) ∧
      W.s * (1 / W.mu1 - W.kappa) ≤ W.s * (1 / (W.mu1hat - W.e) - W.kappa) := by
  have he1 : W.e < W.mu1hat := lt_of_lt_of_le W.he_u0 W.hu0_le_mu1
  exact energy_interval (le_of_lt W.hs_pos) W.he_pos he1 W.hmu1

/-- The plan's raw lower bound `s[1/(muhat₁+e) − 1/(muhat₀−e)]` is also available and
    is implied by the stronger uniform certified mass. -/
theorem mass_lower_bound_of_witness (W : StrongCouplingWitness) :
    W.s * (1 / (W.mu1hat + W.e) - 1 / (W.mu0hat - W.e)) ≤ mass W.s W.mu0 W.mu1 := by
  have he1 : W.e < W.mu1hat := lt_of_lt_of_le W.he_u0 W.hu0_le_mu1
  exact mass_lower_bound (s := W.s) (κ := W.kappa) (le_of_lt W.hs_pos) W.he_pos he1
    W.hmu1_le_mu0 W.hmu0 W.hmu1

end StrongCouplingWitness

end BookProof.SirkStrongCouplingWitness
