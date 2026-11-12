import Mathlib
import BookProof.Qym.ChapterYangMillsHermite
import BookProof.Qym.ChapterYangMillsSoftDirections
import BookProof.YangMillsMagneticQuartic

/-!
# The field strength `F = ∂A + g[A,A]`: derivative part, commutator part, and the root sector

`softmodes.md` §2.1–2.3 and `BookProof.YangMillsMagneticQuartic` argue about the magnetic field
strength component by component.  The field strength itself is already in the corpus, twice:

* `BookProof.YangMillsHermite.magPoly fabc i a` — the pure Yang–Mills magnetic field
  `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})` on the Gauss–polynomial core of
  `L²(ℝ⁹⁹)`, a real polynomial in the `99 = 3 + 24 + 72` coordinates (`idxA` for `A_{j,a}`,
  `idxD` for the independent derivative coordinates `∂_j A_{k,a}`), used by
  `ymHamiltonian = ½ Σ π² + ½ Σ B²`;
* `BookProof.Sm.ChapterSmHamiltonian.smMagG` / `smMagW` / `smMagB` — the same shape for the
  Standard Model, with the coupling written out as `g_s • Σ f_{abc} A_{j,b} A_{k,c}`.

This chapter takes those definitions as they are (nothing is redefined) and proves the three
structural facts the magnetic-quartic analysis needs:

1. **`F = ∂A + g[A,A]`** — `magPoly = magDeriv + magComm` (`magPoly_eq_deriv_add`), the first
   summand linear in the configuration (`∂_j A_{k,a}`), the second the non-abelian commutator
   term `ε_{ijk} f_{abc} A_{j,b} A_{k,c}`.  Both have real coefficients, so on the core the
   split is a split into *two symmetric multiplication operators* (`magOps_apply_eq`,
   `magOpsDeriv_symmetricOn`, `magOpsComm_symmetricOn`): the operator identity `B = B^∂ + B^{[·,·]}`
   is an identity of operators on the core, not merely of polynomials.
2. **The commutator term is the Lie bracket.**  `2 • ∑_{jk} ε_{ijk} F_{jk} = ∑_{jk} ε_{ijk}
   (F_{jk} − F_{kj})` (`two_smul_levi_contract`) — the ε-contraction of *any* bilinear form is
   the ε-contraction of its antisymmetrisation, so `magComm` is `½ ε_{ijk} [A_j, A_k]` and
   vanishes whenever the bilinear form is symmetric (`magComm_eq_zero_of_symmetric`).  This is
   the Cartan statement: `[A_μ, A_ν] = 0` for fields in a Cartan direction, so there the field
   strength *is* `∂A` and its components are linear in the configuration — which is the
   situation `magComp`/`magneticEnergyForm` of `BookProof.YangMillsMagneticQuartic` describe.
3. **The full energy, with nothing dropped.**  `magEnergy = Σ_{i,a} B_{ia}²` is the sum of
   `magEnergyQuad` (the derivative square, the quadratic term the Cartan comparison keeps),
   `magEnergyCross` (cubic) and `magEnergyQuart` (the commutator square, quartic)
   (`magEnergy_eq_parts`), and the corresponding multiplication operators add up
   (`mulOp_magEnergy_eq`, `magEnergyOps_apply_eq`), so the cubic and quartic interactions are
   retained in the form on the core and are not absorbed into a quadratic model.  Summed over the
   `24` field components this is the physical-core energy identity
   (`magEnergy_form_eq`, `ymHamiltonian_quadForm_split`): the kinetic square plus the derivative
   square, the cross term and the commutator square.
5. **The relative bound** (§3c).  `B = ∂A + [A,A]` and the plan's estimate
   `‖X + Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)‖Y‖²` hold mode by mode, so the cross term is bounded by
   `ε` of the quadratic energy and `ε⁻¹` of the quartic one (`magEnergy_form_ge_split`); a quartic
   relative bound with ratio `κ < 1` then leaves `1 − ε − (ε⁻¹ − 1)κ` of the quadratic energy, and
   the choice `ε = 1/2`, `κ = 1/4` leaves a quarter (`magEnergy_form_ge_quarter`, and
   `ymHamiltonian_quadForm_ge_of_quart_bound` for the Hamiltonian).
6. **The mode identification** (§3d).  The product-Hermite basis `coreBasis e` is enumerated by the
   occupation multi-index, so `coeffToCore` embeds the coefficient model `CoreCoeff d` isometrically
   into `L²(ℝᵈ)` (`coeffToCore_norm_sq`), and the occupation of a mode is the total degree of its
   monomial (`totalDegree_occMonomial`).  With the *magnetic-energy* form identified with
   `magneticEnergyForm` (`ModeIdentification`), the coefficient model's quartic bound transfers:
   `Σ‖Bx‖² ≥ (degreeForm + barrierForm − shift ‖x‖²)/24`, hence the Hamiltonian's form is at least
   `(1/48)` of `degreeForm + barrierForm − shift ‖x‖²`
   (`ymHamiltonian_quadForm_ge_of_identification`) and a certified gap with the constant `c₁/48`
   (`s2_gap_constant`).  The §3c hypothesis itself is
   *not* available: `not_quartic_relativeBound` shows the quartic `:N²:` form is not relatively
   bounded by the degree form plus a norm shift in the coefficient model.
7. **The root sector is quartic.**  In the two-dimensional root plane of `su(2)`
   (`rootPlus = E₊`, `rootMinus = E₋`, `cartanH = diag(1,−1)`) the bracket of two off-diagonal
   fields is again Cartan, with the *determinant* of the root amplitudes as its coefficient
   (`rootField_commutator`), and the magnetic energy of that component is the square of that
   determinant (`root_energy`).  It is nonnegative and vanishes exactly when the two root
   amplitudes are parallel (`root_energy_eq_zero_iff`); for hermitian fields it is
   `4 (Im (a₁ \bar a₂))²` (`root_energy_hermitian`).  So the quartic interaction lives entirely
   in the off-diagonal sector, which is why it is invisible to the Cartan linear form.

## No normal ordering in the potential

`magComm` is built from products `X (idxA j b) * X (idxA k c)` and enters the Hamiltonian
through `mulOp`, and multiplication operators compose *exactly*: `mulOp (p * q) = mulOp p ∘
mulOp q` (`mulOp_mul`).  The quartic term is therefore the plain composite of two multiplication
operators, with no Weyl symmetrisation and no vacuum subtraction.  `weylProd` is needed only for
the `πA` cross terms, where the canonical commutator `[A_j, π_j] = i`
(`commutator_coord_mom`) is nonzero; the field strength itself, being a function of the
coordinates alone, is ordered once and for all by the product.

## Honest boundary

Nothing here is dynamical: no spectral statement, no mass gap, no claim that the split survives
any limit.  The energy decomposition of §3b is a *map* of the full field strength into the
comparison calculation.  §3c proves the *cross*-term relative bound unconditionally — it is
Cauchy–Schwarz and AM–GM on the split, with no information about the interaction — and then the
constant arithmetic that turns a relative bound for the quartic part into a positive coefficient
on the quadratic energy.  The relative bound for the quartic part itself is taken as a hypothesis
(`magEnergy_form_ge_of_quart_bound`): on the concrete core the commutator square is a quartic
potential, and bounding it by the quadratic energy with a fixed ratio is the Kato-type estimate the
coefficient model supplies
(`YangMillsMagneticQuartic.magnetic_le_quartic`, `YangMillsEffectiveBarrier.barrierBound_quartic`)
once the mode identification between that model and the `99`-coordinate core is formalised — it is
not derived from the split, and no cutoff uniformity is claimed.
The derivative coordinates `∂_j A_{k,a}` are the book's independent configuration
coordinates (`idxD`), so `magDeriv` is a multiplication operator by construction and the
"derivative" is not the `pderiv` of a field.  The root-sector computation is the `su(2)` block:
it shows what the commutator term does off the Cartan directions, not that a general `f_{abc}`
decomposes into such blocks.
-/

namespace BookProof.YangMillsFieldStrengthSplit

open Matrix MvPolynomial
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.HermiteGalerkin
open BookProof.FarisLavine

noncomputable section

/-! ## 1. The split `F = ∂A + g[A,A]` -/

/-- The **derivative part** of the magnetic field: `ε_{ijk} ∂_j A_{k,a}`, linear in the
configuration coordinates `idxD`. -/
def magDeriv (i : Fin 3) (a : Fin 8) : MvPolynomial (Fin 99) ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • X (idxD j k a)

/-- The `(j,k)` component of the **commutator bilinear form**: `f_{abc} A_{j,b} A_{k,c}`. -/
def magBilin (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (j k : Fin 3) (a : Fin 8) :
    MvPolynomial (Fin 99) ℂ :=
  ∑ b : Fin 8, ∑ c : Fin 8, ((fabc a b c : ℝ) : ℂ) • (X (idxA j b) * X (idxA k c))

/-- The **commutator part** of the magnetic field: `ε_{ijk} f_{abc} A_{j,b} A_{k,c}`, the
non-abelian `g[A,A]` term, quadratic in the configuration. -/
def magComm (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    MvPolynomial (Fin 99) ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • magBilin fabc j k a

/-- **`F = ∂A + g[A,A]`**: the field strength is the derivative part plus the commutator part.
No hypothesis on the structure constants `fabc` (not even antisymmetry) is used — the split is
the definition of `magPoly` regrouped. -/
theorem magPoly_eq_deriv_add (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    magPoly fabc i a = magDeriv i a + magComm fabc i a := by
  simp only [magPoly, magDeriv, magComm, magBilin, smul_add, Finset.sum_add_distrib]

/-- The derivative part has real coefficients, hence acts by a symmetric multiplication
operator on the core. -/
theorem realCoeff_magDeriv (i : Fin 3) (a : Fin 8) : RealCoeff (magDeriv i a) :=
  RealCoeff.sum fun _ _ => RealCoeff.sum fun _ _ => RealCoeff.smul (realCoeff_X _)

/-- The commutator part has real coefficients: the quartic term is a symmetric multiplication
operator, like the linear one. -/
theorem realCoeff_magComm (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    RealCoeff (magComm fabc i a) :=
  RealCoeff.sum fun _ _ => RealCoeff.sum fun _ _ => RealCoeff.smul
    (RealCoeff.sum fun _ _ => RealCoeff.sum fun _ _ =>
      RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _)))

/-- **The potential part of a product is ordered by the product.**  Multiplication operators
compose exactly, `mulOp (p * q) = mulOp p ∘ mulOp q`, so a field polynomial that is a product of
coordinates — the quartic `A_{j,b} A_{k,c}` of the commutator term included — needs no
Weyl symmetrisation and no vacuum subtraction.  (`weylProd` is required only for the `πA` cross
terms, where `commutator_coord_mom` is nonzero.) -/
theorem mulOp_mul (p q : MvPolynomial (Fin 99) ℂ) :
    mulOp (p * q) = (mulOp p).comp (mulOp q) :=
  LinearMap.mulLeft_mul ℂ _ p q

/-! ## 2. The split on the core -/

variable {D : Submodule ℂ (L2d 99)}

set_option maxHeartbeats 1000000 in
-- Expanding the `99`-coordinate magnetic energy into its derivative and commutator parts
-- produces large normal forms; the default heartbeat budget does not reach them.
-- the `CoreRep.op`/`mulOp` unfoldings need more than the default budget
/-- **The operator identity on the core**: the magnetic-field operator `B_{i a}` is the sum of
the derivative operator and the commutator operator.  Both are multiplication operators by real
polynomials, hence Gauss symmetric. -/
theorem magOps_apply_eq (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24)
    (x : D) :
    magOps Φ fabc m x = Φ.op (mulOp (magDeriv (decodeSpace m) (decodeColor m))) x
      + Φ.op (mulOp (magComm fabc (decodeSpace m) (decodeColor m))) x := by
  have hpoly : magPoly fabc (decodeSpace m) (decodeColor m)
      = magDeriv (decodeSpace m) (decodeColor m)
        + magComm fabc (decodeSpace m) (decodeColor m) := magPoly_eq_deriv_add fabc _ _
  have hmul : mulOp (magDeriv (decodeSpace m) (decodeColor m)
        + magComm fabc (decodeSpace m) (decodeColor m)) (Φ.equiv.symm x)
      = mulOp (magDeriv (decodeSpace m) (decodeColor m)) (Φ.equiv.symm x)
        + mulOp (magComm fabc (decodeSpace m) (decodeColor m)) (Φ.equiv.symm x) := by
    simp [mulOp_apply, add_mul]
  rw [magOps, CoreRep.op_apply, hpoly, hmul]
  exact map_add _ _ _

/-- The derivative half of the field strength is a symmetric operator on the core. -/
theorem magOpsDeriv_symmetricOn (Φ : CoreRep 99 D) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (Φ.op (mulOp (magDeriv (decodeSpace m) (decodeColor m))))) :=
  Φ.symmetricOn_op (mulOp_polySym (realCoeff_magDeriv _ _))

/-- The commutator half of the field strength is a symmetric operator on the core. -/
theorem magOpsComm_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (m : Fin 24) :
    SymmetricOn D
      (D.subtype.comp (Φ.op (mulOp (magComm fabc (decodeSpace m) (decodeColor m))))) :=
  Φ.symmetricOn_op (mulOp_polySym (realCoeff_magComm fabc _ _))

/-! ## 3. The commutator part is the Lie bracket -/

/-- The Levi-Civita symbol is antisymmetric in its last two indices. -/
theorem levi_antisymm (i j k : Fin 3) : levi i k j = -levi i j k := by
  simp only [levi]
  push_cast
  ring

/-- **Contracting with `ε` antisymmetrises.**  For *any* bilinear form `F` (no symmetry and no
antisymmetry assumed) the `ε`-contraction of `F` is half the `ε`-contraction of `F − Fᵀ`:
`2 ε_{ijk}F_{jk} = ε_{ijk}(F_{jk} − F_{kj})`.  This is why the non-abelian term is a
commutator, `½ ε_{ijk}[A_j, A_k]`, and it is the only place the antisymmetry of `ε` is used. -/
theorem two_smul_levi_contract (F : Fin 3 → Fin 3 → MvPolynomial (Fin 99) ℂ) (i : Fin 3) :
    (2 : ℂ) • (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • F j k)
      = ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • (F j k - F k j) := by
  fin_cases i <;> simp only [Fin.sum_univ_three, levi] <;> push_cast <;> module

/-- **The `ε`–`ε` contraction**: `∑_i ε_{ijk} ε_{ilm} = δ_{jl}δ_{km} − δ_{jm}δ_{kl}`, the sharp
identity behind the magnetic-energy contraction (the `ε` analogue of the Pauli-matrix product). -/
theorem levi_contract (j k l m : Fin 3) :
    (∑ i : Fin 3, levi i j k * levi i l m)
      = (if j = l ∧ k = m then 1 else 0) - (if j = m ∧ k = l then 1 else 0) := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;>
    simp [Fin.sum_univ_three, levi] <;> norm_num

/-- **The `ε`-contraction of two bilinear forms, as a polynomial identity.**  Contracting two
`ε`-contractions gives the two traces `P_{jk}Q_{jk}` minus the transposed one `P_{jk}Q_{kj}`:
`∑_i (ε_{ijk}P_{jk})(ε_{ilm}Q_{lm}) = ∑_{jk}(P_{jk}Q_{jk} − P_{jk}Q_{kj})`.  No symmetry is
assumed on either form. -/
theorem eps_contract_poly (P Q : Fin 3 → Fin 3 → MvPolynomial (Fin 99) ℂ) :
    (∑ i : Fin 3, (∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • P j k)
        * (∑ l : Fin 3, ∑ m : Fin 3, ((levi i l m : ℝ) : ℂ) • Q l m))
      = ∑ j : Fin 3, ∑ k : Fin 3, (P j k * Q j k - P j k * Q k j) := by
  simp only [Fin.sum_univ_three]
  norm_num [levi]
  ring

/-- The square case: `∑_i (ε_{ijk}P_{jk})² = ∑_{jk}(P_{jk}² − P_{jk}P_{kj})`. -/
theorem magPoly_sq_contract (P : Fin 3 → Fin 3 → MvPolynomial (Fin 99) ℂ) :
    (∑ i : Fin 3, (∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • P j k) ^ 2)
      = ∑ j : Fin 3, ∑ k : Fin 3, (P j k ^ 2 - P j k * P k j) := by
  simpa [pow_two] using eps_contract_poly P P

/-- **The commutator part vanishes for commuting fields.**  If the bilinear form `A_{j,b}A_{k,c}`
is symmetric in `(j,b) ↔ (k,c)` — which is what `[A_j, A_k] = 0` means, in particular for
fields taking values in a Cartan direction — then `g[A,A]` contributes nothing and the field
strength is the derivative part alone.  This is the sector in which the magnetic components are
linear in the configuration, the setting of `BookProof.YangMillsMagneticQuartic`. -/
theorem magComm_eq_zero_of_symmetric (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (a : Fin 8) (i : Fin 3)
    (hsym : ∀ j k : Fin 3, magBilin fabc j k a = magBilin fabc k j a) :
    magComm fabc i a = 0 := by
  have h := two_smul_levi_contract (fun j k => magBilin fabc j k a) i
  have hzero :
      ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • (magBilin fabc j k a - magBilin fabc k j a) = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [hsym j k, sub_self, smul_zero]
  rw [hzero] at h
  have hS : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • magBilin fabc j k a) = 0 := by
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  simpa only [magComm] using hS

/-- The abelian case: with vanishing structure constants `magComm = 0` and the field strength is
the derivative part, `F = ∂A`. -/
theorem magComm_zero (i : Fin 3) (a : Fin 8) :
    magComm (fun _ _ _ => 0) i a = 0 := by
  simp [magComm, magBilin]

/-! ## 3b. The full magnetic energy `Σ B²` and its parts

The comparison calculation (`YangMillsFormClosureNonDiagonal`, and the quartic `:N²:` form of
`YangMillsMagneticQuartic`) is stated for a **quadratic** magnetic weight — the Cartan sector, where
`B` is linear in the configuration.  This section is the map from the full non-abelian field
strength into that calculation: the magnetic energy `Σ_{i,a} B_{ia}²` is the derivative square
plus a cross term plus the commutator square, and the two latter terms are the cubic and quartic
interactions the diagonal comparison does not see.  Nothing is dropped: the sum of the three parts
is the full energy, and the operator identity below is what makes it a statement about forms on
the core rather than about polynomials.

What this section does *not* do is the coercivity estimate: it does not bound the cross and
commutator parts by the quadratic form, and it makes no claim uniform in any cutoff.  Those are
separate analytic inputs.
-/

/-- The **full magnetic energy** `Σ_{i,a} B_{ia}²` — the potential `½ Σ B²` of the Weyl-gauge
Hamiltonian up to the factor `½`.  It is quartic in the fields. -/
def magEnergy (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : MvPolynomial (Fin 99) ℂ :=
  ∑ i : Fin 3, ∑ a : Fin 8, magPoly fabc i a ^ 2

/-- The **derivative part** of the magnetic energy: `Σ_{i,a} (∂A)_{ia}²`, quadratic in the
configuration.  This is the term the Cartan-sector comparison keeps. -/
def magEnergyQuad : MvPolynomial (Fin 99) ℂ :=
  ∑ i : Fin 3, ∑ a : Fin 8, magDeriv i a ^ 2

/-- The **cross term** `2 Σ_{i,a} (∂A)_{ia} g[A,A]_{ia}`, cubic in the configuration. -/
def magEnergyCross (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : MvPolynomial (Fin 99) ℂ :=
  ∑ i : Fin 3, ∑ a : Fin 8, (2 : ℂ) • (magDeriv i a * magComm fabc i a)

/-- The **commutator square** `Σ_{i,a} g[A,A]_{ia}²`, quartic in the configuration. -/
def magEnergyQuart (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : MvPolynomial (Fin 99) ℂ :=
  ∑ i : Fin 3, ∑ a : Fin 8, magComm fabc i a ^ 2

/-- **The full energy is the sum of its three parts**: nothing is truncated. -/
theorem magEnergy_eq_parts (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    magEnergy fabc = magEnergyQuad + magEnergyCross fabc + magEnergyQuart fabc := by
  rw [magEnergy, magEnergyQuad, magEnergyCross, magEnergyQuart]
  simp only [magPoly_eq_deriv_add]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pow_two, pow_two, pow_two,
    show (2 : ℂ) • (magDeriv i a * magComm fabc i a)
        = magDeriv i a * magComm fabc i a + magDeriv i a * magComm fabc i a
      from two_smul ℂ _]
  ring

/-- The field strength itself has real coefficients, as the sum of its two real halves. -/
theorem realCoeff_magPoly (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    RealCoeff (magPoly fabc i a) := by
  rw [magPoly_eq_deriv_add]
  exact RealCoeff.add (realCoeff_magDeriv i a) (realCoeff_magComm fabc i a)

/-- The bilinear entry of the **full** field strength — derivative *plus* commutator — so that
`B_{ia} = ∑_{jk} ε_{ijk} (magFullBilin)_{jk,a}` holds definitionally. -/
noncomputable def magFullBilin (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (j k : Fin 3) (a : Fin 8) :
    MvPolynomial (Fin 99) ℂ :=
  X (idxD j k a) + magBilin fabc j k a

/-- `B_{ia}` is the `ε`-contraction of `magFullBilin`, definitionally. -/
theorem magPoly_eq_sum_levi_magFullBilin (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3)
    (a : Fin 8) :
    magPoly fabc i a
      = ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • magFullBilin fabc j k a := rfl

/-- **The full magnetic energy contracted with `ε` and `f`.**  Summing the square of the
`ε`-contraction over the magnetic index `i` and using `magPoly_sq_contract` gives
`Σ_{ia} B_{ia}² = Σ_{a,j,k} (P_{jka}² − P_{jka}P_{kja})`, with `P = magFullBilin = ∂A + f[A,A]`.
The `ε` weights are gone, the `f` weights sit inside `P`, and the transposed term
`P_{jka}P_{kja}` is exactly where the commutator survives: for `f = 0` it is symmetric and
cancels only against the diagonal if `∂_j A_{k,a} ∂_k A_{j,a}` does not — the derivative cross
term.  No truncation is made. -/
theorem magEnergy_eq_contract (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    magEnergy fabc
      = ∑ a : Fin 8, ∑ j : Fin 3, ∑ k : Fin 3,
          (magFullBilin fabc j k a ^ 2
            - magFullBilin fabc j k a * magFullBilin fabc k j a) := by
  rw [magEnergy, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := magPoly_sq_contract (fun j k => magFullBilin fabc j k a)
  simpa only [magPoly_eq_sum_levi_magFullBilin] using h

/-! ### 3b.2 Structure constants: antisymmetry, Jacobi, and the quartic colour factor

The model carries `f_{abc}` as a *free* three-index tensor; nothing in the polynomial construction
forces it to be a Lie-bracket coefficient.  These two hypotheses are therefore added explicitly,
and what follows is exactly what they buy: the repeated-index vanishing, the cyclic colour tensor,
and the factor `2` in the quartic energy.
-/

/-- **Antisymmetry** of the structure constants in their last two indices, `f_{a b c} = −f_{a c b}`,
the property that makes `f_{abc} A_b A_c` a commutator rather than a symmetric square. -/
def IsAntisymmetric (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : Prop :=
  ∀ a b c, fabc a b c = -fabc a c b

/-- **The Jacobi identity** in structure-constant form: the cyclic sum of the colour tensor
`K_{a b c d} = Σ_e f_{a b e} f_{c d e}` vanishes. -/
def SatisfiesJacobi (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : Prop :=
  ∀ a b c d : Fin 8, ∑ e : Fin 8,
    (fabc a b e * fabc c d e + fabc b c e * fabc a d e + fabc c a e * fabc b d e) = 0

/-- A structure constant with a repeated index vanishes under antisymmetry. -/
theorem fabc_self_eq_zero {fabc : Fin 8 → Fin 8 → Fin 8 → ℝ} (hanti : IsAntisymmetric fabc)
    (a c : Fin 8) : fabc a c c = 0 := by
  have h := hanti a c c
  linarith

/-- The colour tensor `K_{a b c d} = Σ_e f_{a b e} f_{c d e}`. -/
def colourTensor (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (a b c d : Fin 8) : ℝ :=
  ∑ e : Fin 8, fabc a b e * fabc c d e

/-- **Jacobi is exactly the cyclic vanishing of the colour tensor.** -/
theorem colourTensor_cyclic {fabc : Fin 8 → Fin 8 → Fin 8 → ℝ} (hjac : SatisfiesJacobi fabc)
    (a b c d : Fin 8) :
    colourTensor fabc a b c d + colourTensor fabc b c a d + colourTensor fabc c a b d = 0 := by
  unfold colourTensor
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact hjac a b c d

/-- **The quartic colour factor from antisymmetry.**  If `P` is antisymmetric in its two indices —
as `f_{abc} A_{j,b} A_{k,c}` is once `f` is — then the transposed term of the `ε`-contraction is
minus the direct one, and the contraction **doubles**:
`Σ_{jk}(P_{jk}² − P_{jk}P_{kj}) = 2·Σ_{jk} P_{jk}²`.  The factor `2` is the colour-factor content of
the quartic magnetic energy: the commutator's antisymmetry turns the `ε` contraction into twice the
direct square. -/
theorem colour_contraction_double (P : Fin 3 → Fin 3 → ℂ) (hP : ∀ j k, P k j = -P j k) :
    (∑ j : Fin 3, ∑ k : Fin 3, (P j k * P j k - P j k * P k j))
      = 2 * ∑ j : Fin 3, ∑ k : Fin 3, P j k * P j k := by
  have h : ∀ j k : Fin 3, P j k * P j k - P j k * P k j = 2 * (P j k * P j k) := by
    intro j k
    rw [hP j k]
    ring
  calc (∑ j : Fin 3, ∑ k : Fin 3, (P j k * P j k - P j k * P k j))
      = (∑ j : Fin 3, ∑ k : Fin 3, 2 * (P j k * P j k)) := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h j k
    _ = 2 * ∑ j : Fin 3, ∑ k : Fin 3, P j k * P j k := by
        simp only [Finset.mul_sum]

/-! ### 3b.2b The `su(2)` structure constants, and the colour factor explicitly

§3b.2 leaves `f_{abc}` free and derives only what antisymmetry and Jacobi buy.  Here the tensor is
*instantiated*: on the first three of the eight colour indices it is the Levi-Civita symbol,
```
f_{abc} = ε_{abc}   (a, b, c < 3),      f_{abc} = 0   otherwise,
```
which is exactly the `su(2)` structure-constant tensor `ε_{abc}` in the adjoint of `su(2)`
(`su2Struct`, with the three slots `su2Slot i`).  The remaining five colour directions are abelian
in this instantiation, so the model then carries `su(2) × U(1)⁵`; every statement below is about the
`su(2)` block, and the `U(1)` directions are invisible to it.

What becomes *computable* once the tensor is concrete:

* **the hypotheses are met**: `IsAntisymmetric su2Struct` (`su2Struct_antisym`, from the
  antisymmetry of `ε`) and `SatisfiesJacobi su2Struct` (`su2Struct_jacobi`) — so every theorem of
  §3b.2 applies to this tensor with no side conditions left;
* **the colour tensor**, explicitly:
  `K_{abcd} = Σ_e f_{abe} f_{cde} = δ_{ac}δ_{bd} − δ_{ad}δ_{bc}` (`colourTensor_su2`) — the
  `ε`–`ε` contraction of §3b.0 with the summed index in the third slot;
* **the colour factor**: `Σ_{ab} f_{abe} f_{abd} = 2 δ_{ed}` (`su2_casimir_adjoint`), so the adjoint
  Casimir is `C_A = 2` (`su2_casimir_adjoint_value`), and contracting both indices as well gives
  `Σ_{abc} f_{abc}² = C_A · dim(adj) = 2 · 3 = 6` (`su2_colourWeight_sum`).  This is the number that
  multiplies the squared amplitude in the perturbative reading; it is *computed* from the structure
  constants, not assumed.

Where the number `2` enters *this* model: `colour_contraction_double` already shows that
antisymmetry doubles the `ε`-contraction of the quartic colour energy, and the Casimir above is the
same `2` — the quartic energy of the non-abelian term is `2` times the direct square, with the `2`
traceable to `ε_{abc}ε_{abd} = 2δ_{cd}` once the sum runs over the block.

**Boundary (superseded by §3b.2c).**  This section computes the *adjoint* colour factor from the
structure constants alone.  The *fundamental* Casimir `C_F = 3/4` needs a fundamental representation
(`T^a = σ^a/2`), which §3b.2c supplies; the two numbers are proved from the same `ε_{abc}`.
-/

/-- The **`su(2)` colour slots**: the first three of the eight colour indices, where the non-abelian
structure constants live in this instantiation. -/
def su2Slot (i : Fin 3) : Fin 8 := ⟨i.val, by omega⟩

/-- The three slots are distinct. -/
theorem su2Slot_injective : Function.Injective su2Slot := by
  intro i j h
  have hv : i.val = j.val := congrArg (fun x : Fin 8 => x.val) h
  exact Fin.ext hv

/-- **The `su(2)` structure constants** on the eight colour indices: `f_{abc} = ε_{abc}` on the
three `su(2)` slots and `0` off them.  The remaining five colour directions are abelian, so this
is the `su(2) × U(1)⁵` instantiation of the free tensor `fabc`. -/
def su2Struct (a b c : Fin 8) : ℝ :=
  if h : a.val < 3 ∧ b.val < 3 ∧ c.val < 3 then
    levi ⟨a.val, h.1⟩ ⟨b.val, h.2.1⟩ ⟨c.val, h.2.2⟩
  else 0

/-- On the `su(2)` slots the instantiated tensor **is** `ε`. -/
theorem su2Struct_slot (i j k : Fin 3) :
    su2Struct (su2Slot i) (su2Slot j) (su2Slot k) = levi i j k := by
  unfold su2Struct
  simp only [su2Slot, Fin.val_mk]
  rw [dif_pos ⟨i.isLt, j.isLt, k.isLt⟩]

/-- Off the `su(2)` block the tensor vanishes in its first index. -/
theorem su2Struct_zero_left (a b c : Fin 8) (h : 3 ≤ a.val) : su2Struct a b c = 0 := by
  unfold su2Struct
  rw [dif_neg]
  omega

/-- Off the `su(2)` block the tensor vanishes in its second index. -/
theorem su2Struct_zero_mid (a b c : Fin 8) (h : 3 ≤ b.val) : su2Struct a b c = 0 := by
  unfold su2Struct
  rw [dif_neg]
  omega

/-- Off the `su(2)` block the tensor vanishes in its third index. -/
theorem su2Struct_zero_right (a b c : Fin 8) (h : 3 ≤ c.val) : su2Struct a b c = 0 := by
  unfold su2Struct
  rw [dif_neg]
  omega

/-- `ε` is antisymmetric in its last two indices. -/
theorem levi_antisym (i j k : Fin 3) : levi i j k = -levi i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [levi]

/-- **Sums over the eight colour indices reduce to sums over the `su(2)` block** when the summand
vanishes off it: `∑_{e<8} g(e) = ∑_{i<3} g(slot i)`.  This is the bookkeeping lemma that makes
every colour computation below a computation over `Fin 3`. -/
theorem sum_fin8_eq_sum_su2 (g : Fin 8 → ℝ) (hg : ∀ e : Fin 8, 3 ≤ e.val → g e = 0) :
    ∑ e : Fin 8, g e = ∑ i : Fin 3, g (su2Slot i) := by
  have himg : (Finset.univ.filter (fun e : Fin 8 => e.val < 3))
      = (Finset.univ : Finset (Fin 3)).image su2Slot := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨⟨e.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  have h1 : ∑ e ∈ Finset.univ.filter (fun e : Fin 8 => e.val < 3), g e = ∑ e : Fin 8, g e := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    have h3 : 3 ≤ x.val := by
      by_contra hlt
      exact hx (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega)
    exact hg x h3
  rw [← h1, himg, Finset.sum_image]
  intro i _ j _ h
  exact su2Slot_injective h

/-- **The `su(2)` tensor is antisymmetric**, so §3b.2's `fabc_self_eq_zero` and the doubling of the
quartic energy apply to it. -/
theorem su2Struct_antisym : IsAntisymmetric su2Struct := by
  intro a b c
  unfold su2Struct
  by_cases h : a.val < 3 ∧ b.val < 3 ∧ c.val < 3
  · obtain ⟨ha, hb, hc⟩ := h
    rw [dif_pos ⟨ha, hb, hc⟩, dif_pos ⟨ha, hc, hb⟩, levi_antisym]
  · have h' : ¬ (a.val < 3 ∧ c.val < 3 ∧ b.val < 3) := by tauto
    rw [dif_neg h, dif_neg h']
    ring

set_option maxHeartbeats 2000000 in
-- The identity reduces to 81 concrete three-term `Fin 3` sums; the default budget is too small.
/-- **The `su(2)` tensor satisfies Jacobi**: the cyclic `ε` identity, `su(2)` being simple.
With `su2Struct_antisym` this means no hypothesis of §3b.2 is left open for this tensor. -/
theorem su2Struct_jacobi : SatisfiesJacobi su2Struct := by
  intro a b c d
  by_cases h : a.val < 3 ∧ b.val < 3 ∧ c.val < 3 ∧ d.val < 3
  · obtain ⟨ha, hb, hc, hd⟩ := h
    obtain ⟨a', rfl⟩ : ∃ a' : Fin 3, su2Slot a' = a := ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
    obtain ⟨b', rfl⟩ : ∃ b' : Fin 3, su2Slot b' = b := ⟨⟨b.val, hb⟩, Fin.ext rfl⟩
    obtain ⟨c', rfl⟩ : ∃ c' : Fin 3, su2Slot c' = c := ⟨⟨c.val, hc⟩, Fin.ext rfl⟩
    obtain ⟨d', rfl⟩ : ∃ d' : Fin 3, su2Slot d' = d := ⟨⟨d.val, hd⟩, Fin.ext rfl⟩
    have hg : ∀ e : Fin 8, 3 ≤ e.val →
        su2Struct (su2Slot a') (su2Slot b') e * su2Struct (su2Slot c') (su2Slot d') e
        + su2Struct (su2Slot b') (su2Slot c') e * su2Struct (su2Slot a') (su2Slot d') e
        + su2Struct (su2Slot c') (su2Slot a') e * su2Struct (su2Slot b') (su2Slot d') e = 0 := by
      intro e he
      rw [su2Struct_zero_right (su2Slot a') (su2Slot b') e he,
        su2Struct_zero_right (su2Slot c') (su2Slot d') e he,
        su2Struct_zero_right (su2Slot b') (su2Slot c') e he,
        su2Struct_zero_right (su2Slot a') (su2Slot d') e he,
        su2Struct_zero_right (su2Slot c') (su2Slot a') e he,
        su2Struct_zero_right (su2Slot b') (su2Slot d') e he]
      norm_num
    rw [sum_fin8_eq_sum_su2 (g := fun e : Fin 8 =>
      su2Struct (su2Slot a') (su2Slot b') e * su2Struct (su2Slot c') (su2Slot d') e
      + su2Struct (su2Slot b') (su2Slot c') e * su2Struct (su2Slot a') (su2Slot d') e
      + su2Struct (su2Slot c') (su2Slot a') e * su2Struct (su2Slot b') (su2Slot d') e) hg]
    simp only [su2Struct_slot]
    fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> fin_cases d' <;>
      simp only [Fin.sum_univ_three, levi] <;> norm_num
  · have hz : ∀ e : Fin 8,
        su2Struct a b e * su2Struct c d e + su2Struct b c e * su2Struct a d e
        + su2Struct c a e * su2Struct b d e = 0 := by
      intro e
      by_cases hb3 : b.val < 3
      · by_cases hc3 : c.val < 3
        · by_cases hd3 : d.val < 3
          · have ha3 : 3 ≤ a.val := by
              by_contra hlt
              exact h ⟨by omega, hb3, hc3, hd3⟩
            rw [su2Struct_zero_left a b e ha3, su2Struct_zero_left a d e ha3,
              su2Struct_zero_mid c a e ha3]
            norm_num
          · have hd3' : 3 ≤ d.val := by omega
            rw [su2Struct_zero_mid c d e hd3', su2Struct_zero_mid a d e hd3',
              su2Struct_zero_mid b d e hd3']
            norm_num
        · rw [su2Struct_zero_mid b c e (by omega), su2Struct_zero_left c d e (by omega),
            su2Struct_zero_left c a e (by omega)]
          norm_num
      · rw [su2Struct_zero_mid a b e (by omega), su2Struct_zero_left b c e (by omega),
          su2Struct_zero_left b d e (by omega)]
        norm_num
    exact Finset.sum_eq_zero fun e _ => hz e

/-- **The colour tensor of the `su(2)` instantiation**, explicitly:
`K_{abcd} = Σ_e f_{abe}f_{cde} = δ_{ac}δ_{bd} − δ_{ad}δ_{bc}` on the `su(2)` slots — the `ε`–`ε`
contraction with the summed index in the third slot, and the identity behind the quartic colour
energy of §3b.2. -/
theorem colourTensor_su2 (a b c d : Fin 3) :
    colourTensor su2Struct (su2Slot a) (su2Slot b) (su2Slot c) (su2Slot d)
      = (if a = c ∧ b = d then 1 else 0) - (if a = d ∧ b = c then 1 else 0) := by
  have hg : ∀ e : Fin 8, 3 ≤ e.val →
      su2Struct (su2Slot a) (su2Slot b) e * su2Struct (su2Slot c) (su2Slot d) e = 0 := by
    intro e he
    rw [su2Struct_zero_right (su2Slot a) (su2Slot b) e he,
      su2Struct_zero_right (su2Slot c) (su2Slot d) e he]
    norm_num
  unfold colourTensor
  rw [sum_fin8_eq_sum_su2 (g := fun e : Fin 8 =>
    su2Struct (su2Slot a) (su2Slot b) e * su2Struct (su2Slot c) (su2Slot d) e) hg]
  simp only [su2Struct_slot]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Fin.sum_univ_three, levi] <;> norm_num

/-- **The `su(2)` colour factor (adjoint Casimir)**, derived and not assumed:
`Σ_{ab} f_{abe}f_{abd} = 2 δ_{ed}`, i.e. `C_A = 2`. -/
theorem su2_casimir_adjoint (i j : Fin 3) :
    ∑ a : Fin 8, ∑ b : Fin 8, su2Struct a b (su2Slot i) * su2Struct a b (su2Slot j)
      = if i = j then 2 else 0 := by
  have hinner : ∀ a : Fin 8,
      ∑ b : Fin 8, su2Struct a b (su2Slot i) * su2Struct a b (su2Slot j)
        = ∑ b' : Fin 3, su2Struct a (su2Slot b') (su2Slot i) *
            su2Struct a (su2Slot b') (su2Slot j) := by
    intro a
    refine sum_fin8_eq_sum_su2 (g := fun b : Fin 8 =>
      su2Struct a b (su2Slot i) * su2Struct a b (su2Slot j)) ?_
    intro b hb
    change su2Struct a b (su2Slot i) * su2Struct a b (su2Slot j) = 0
    rw [su2Struct_zero_mid a b (su2Slot i) hb]
    norm_num
  simp only [hinner]
  have hg : ∀ a : Fin 8, 3 ≤ a.val →
      (∑ b' : Fin 3, su2Struct a (su2Slot b') (su2Slot i) *
        su2Struct a (su2Slot b') (su2Slot j)) = 0 := by
    intro a ha
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [su2Struct_zero_left a (su2Slot b') (su2Slot i) ha]
    norm_num
  rw [sum_fin8_eq_sum_su2 (g := fun a : Fin 8 => ∑ b' : Fin 3,
    su2Struct a (su2Slot b') (su2Slot i) * su2Struct a (su2Slot b') (su2Slot j)) hg]
  simp only [su2Struct_slot]
  fin_cases i <;> fin_cases j <;> simp only [Fin.sum_univ_three] <;> norm_num [levi]

/-- **`C_A = 2` for the instantiated `su(2)`**: the diagonal entry of the adjoint Casimir. -/
theorem su2_casimir_adjoint_value :
    ∑ a : Fin 8, ∑ b : Fin 8, su2Struct a b (su2Slot 0) * su2Struct a b (su2Slot 0) = 2 := by
  rw [su2_casimir_adjoint 0 0]
  norm_num

/-- **The total colour weight** `Σ_{abc} f_{abc}² = C_A · dim(adj) = 2 · 3 = 6`, the number that
multiplies a squared amplitude in the perturbative reading — computed from the structure constants,
not assumed. -/
theorem su2_colourWeight_sum :
    ∑ c : Fin 3, ∑ a : Fin 8, ∑ b : Fin 8,
        su2Struct a b (su2Slot c) * su2Struct a b (su2Slot c) = 6 := by
  simp only [su2_casimir_adjoint]
  norm_num

/-! ### 3b.2c The fundamental representation, and `C_F = 3/4`

§3b.2b computed the *adjoint* colour factor `C_A = 2` and left the fundamental one open, because a
fundamental Casimir needs a fundamental representation.  Here it is: `T^a = σ^a / 2` on `ℂ²`
(`fundRep`, built from the Pauli matrices `pauli`), with the same structure constants that §3b.2b
instantiated.

* **it is a representation**: `fundRep_commutator` is `[T^a, T^b] = i ε^{abc} T^c`, and
  `fundRep_commutator_su2Struct` restates it against the chapter's own tensor
  `su2Struct (su2Slot a) (su2Slot b) (su2Slot c)`, so the fundamental and the adjoint are
  representations of *one* algebra;
* **the Casimir**: `pauli_sq` is `σ^a σ^a = 1`, hence `fundRep_sq` (`(T^a)² = ¼ · 1`), and summing
  gives `su2_casimir_fundamental`: `Σ_a T^a T^a = (3/4) · 1`.  That scalar is `C_F = 3/4`;
* **the trace normalisation**: `fundRep_trace_mul` is `tr(T^a T^b) = δ^{ab}/2`, i.e. `T_F = 1/2` for
  these generators.

So the two colour factors are *computed*, from the same `ε`, and they differ as they should:
`C_A = 2` for the adjoint (`su2_casimir_adjoint_value`), `C_F = 3/4` for the fundamental.  At
`N = 2` this is the familiar `C_A = N = 2` and `C_F = (N² − 1)/(2N) = 3/4`, and the ratio
`C_A/C_F = 8/3` that a `C_A`-versus-`C_F` comparison needs is now two proved numbers rather than a
convention.

**Boundary.**  These matrices act on the representation space `ℂ²`, which the chapter's Fock model
does not carry as a mode factor.  Nothing here asserts that the Fock space decomposes into
fundamental multiplets, or that the quartic colour energy of §3b.2b is improved by `C_F`; what is
established is the representation, its commutators, its Casimir and its trace normalisation.
-/

/-- The Pauli matrices `σ₁, σ₂, σ₃` as a `Fin 3`-indexed family of `2 × 2` complex matrices. -/
def pauli (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]] a

/-- **The Pauli matrices square to `1`**: `σ^a σ^a = 1` for each `a`. -/
theorem pauli_sq (a : Fin 3) : pauli a * pauli a = 1 := by
  fin_cases a <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- A shape `simp` needs for the Pauli algebra: `i (x i) = −x`. -/
theorem i_mul_mul_i (x : ℂ) : Complex.I * (x * Complex.I) = -x := by
  calc Complex.I * (x * Complex.I) = (Complex.I * Complex.I) * x := by ring
    _ = -x := by rw [Complex.I_mul_I]; ring

/-- The same shape with a scalar in front of each factor: `(x i)(y i) = −xy`. -/
theorem mul_I_mul_I (x y : ℂ) : (x * Complex.I) * (y * Complex.I) = -(x * y) := by
  calc (x * Complex.I) * (y * Complex.I) = (x * y) * (Complex.I * Complex.I) := by ring
    _ = -(x * y) := by rw [Complex.I_mul_I]; ring

/-- The **fundamental representation** of `su(2)`: `T^a = σ^a / 2`, acting on `ℂ²`. -/
def fundRep (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • pauli a

/-- **Each generator squares to `¼`**: `(T^a)² = 1/4 · 1`, the Pauli square halved twice. -/
theorem fundRep_sq (a : Fin 3) :
    fundRep a * fundRep a = (1 / 4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [fundRep, Matrix.smul_mul, Matrix.mul_smul, pauli_sq, smul_smul]
  norm_num

/-- **The fundamental Casimir is `C_F = 3/4`**: `Σ_a T^a T^a = (3/4) · 1`.  The sum of the three
squared generators is a *scalar* matrix, which is exactly what makes it a Casimir, and the scalar is
`3 · ¼`. -/
theorem su2_casimir_fundamental :
    ∑ a : Fin 3, fundRep a * fundRep a = (3 / 4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Fin.sum_univ_three, fundRep_sq, fundRep_sq, fundRep_sq, ← add_smul, ← add_smul]
  norm_num

/-- **The fundamental representation is a representation**: `[T^a, T^b] = i ε^{abc} T^c`, i.e. the
`su(2)` commutation relations with the same `ε` that `su2Struct` instantiates — in signs and
normalisation the ones the adjoint carries. -/
theorem fundRep_commutator (a b : Fin 3) :
    fundRep a * fundRep b - fundRep b * fundRep a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • fundRep c) := by
  fin_cases a <;> fin_cases b <;>
    rw [Fin.sum_univ_three] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [fundRep, pauli, levi, Matrix.smul_apply, i_mul_mul_i, mul_I_mul_I] <;>
      ring

/-- **The same commutators against the chapter's structure constants**: with
`su2Struct (su2Slot a) (su2Slot b) (su2Slot c)`, the fundamental generators close on themselves with
*the tensor §3b.2b uses for the adjoint*.  This is what makes `C_A = 2` and `C_F = 3/4` two Casimirs
of one algebra rather than two unrelated constants. -/
theorem fundRep_commutator_su2Struct (a b : Fin 3) :
    fundRep a * fundRep b - fundRep b * fundRep a
      = Complex.I • (∑ c : Fin 3,
          (su2Struct (su2Slot a) (su2Slot b) (su2Slot c) : ℂ) • fundRep c) := by
  rw [fundRep_commutator]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [su2Struct_slot]

/-- **The trace normalisation `T_F = 1/2`**: `tr(T^a T^b) = δ^{ab}/2`.  Together with
`su2_casimir_fundamental` this fixes both standard convention-dependent numbers of the fundamental
representation, from the matrices themselves. -/
theorem fundRep_trace_mul (a b : Fin 3) :
    (fundRep a * fundRep b).trace = if a = b then (1 / 2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [fundRep, pauli, Matrix.trace, mul_I_mul_I] <;>
    norm_num

/-! ### 3b.1 What the field-strength operator does to a mode

`mag_eq_root` would say that `B_{ia}` acts on the embedded modes like the occupation number of the
`A` coordinate.  It does not, and the reason is visible one monomial at a time: the derivative
coordinates `∂_j A_{k,a}` are *independent* coordinates in the book's parametrisation, so
multiplication by `X (idxD j k a)` **raises** the occupation of that coordinate.  The two lemmas
below record this: a coordinate acts on a monomial as a different monomial, hence as a shift, never
as a scalar.  This is the obstruction `mag_eq_root` runs into; the `:N²:` form needs the
normal-ordered Wick contraction of this multiplication operator, not its diagonal part. -/

/-- **A coordinate raises its own occupation**: `X i * monomial m z = monomial (m + e_i) z`. -/
theorem mulOp_X_monomial (i : Fin 99) (m : Fin 99 →₀ ℕ) (z : ℂ) :
    mulOp (X i) (monomial m z) = monomial (m + Finsupp.single i 1) z := by
  simp [mulOp_apply, X, monomial_mul, add_comm]

/-- **A coordinate is never scalar on a monomial**: the raised exponent vector is different from
`m`, so no monomial is an eigenvector of `X i`.  Hence the derivative half of `B_{ia}` has no
diagonal basis of occupations, which is exactly what `mag_eq_root` would need. -/
theorem mulOp_X_monomial_ne (i : Fin 99) (m : Fin 99 →₀ ℕ) (z : ℂ) (hz : z ≠ 0) :
    mulOp (X i) (monomial m z) ≠ monomial m z := by
  intro h
  rw [mulOp_X_monomial] at h
  have hexp : m + Finsupp.single i 1 = m := by
    rcases (MvPolynomial.monomial_eq_monomial_iff _ _ _ _).mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hz
  have hs : Finsupp.single i (1 : ℕ) = 0 :=
    add_left_cancel (a := m) (by rw [hexp, add_zero])
  exact one_ne_zero (Finsupp.single_eq_zero.mp hs)

/-- **`magPoly` has no constant term**: every term is at least linear in some coordinate, so the
magnetic field raises the degree of every mode. -/
theorem coeff_zero_magPoly (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    MvPolynomial.coeff 0 (magPoly fabc i a) = 0 := by
  rw [← MvPolynomial.constantCoeff_eq]
  simp [magPoly]

/-- **The Wick contraction of a coordinate with its derivative is the identity**:
`∂ᵢ (Xᵢ p) = p + Xᵢ ∂ᵢ p`, i.e. `[∂ᵢ, Xᵢ] = 1`.  This `1` is the contraction constant that the
normal-ordered `:N²:` absorbs, and it is exactly what separates `Σ_m ‖B_m ψ‖²` from `Σ_a n_a²`. -/
theorem pderiv_X_mul (i : Fin 99) (p : MvPolynomial (Fin 99) ℂ) :
    MvPolynomial.pderiv i (X i * p) = p + X i * MvPolynomial.pderiv i p := by
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, one_mul]

/-- **Normal ordering at the operator level**: the derivative of `Xᵢ p` differs from `Xᵢ ∂ᵢ p` by
exactly the identity, so the contraction constant is one. -/
theorem normalOrder_contraction (i : Fin 99) (p : MvPolynomial (Fin 99) ℂ) :
    MvPolynomial.pderiv i (mulOp (X i) p) - mulOp (X i) (MvPolynomial.pderiv i p) = p := by
  rw [mulOp_apply, mulOp_apply, pderiv_X_mul]
  ring

/-- **`B_ia` is off-diagonal in the occupation basis**: its multiplication has zero diagonal
coefficient at every monomial, so no mode is a `B`-eigenvector.  This is the precise sense in which
`mag_eq_root` cannot hold for `magOps`, and it is the polynomial-level form of the contraction
constant above. -/
theorem magPoly_mul_monomial_ne (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8)
    (m : Fin 99 →₀ ℕ) :
    mulOp (magPoly fabc i a) (monomial m 1) ≠ monomial m 1 := by
  intro h
  have hc : MvPolynomial.coeff m (magPoly fabc i a * monomial m 1)
      = MvPolynomial.coeff m (monomial m 1) :=
    congrArg (fun p => MvPolynomial.coeff m p) (by simpa [mulOp_apply] using h)
  have h1 : MvPolynomial.coeff m (magPoly fabc i a * monomial m 1)
      = MvPolynomial.coeff 0 (magPoly fabc i a) * 1 := by
    have := MvPolynomial.coeff_mul_monomial (0 : Fin 99 →₀ ℕ) m (1 : ℂ) (magPoly fabc i a)
    simpa using this
  rw [h1, coeff_zero_magPoly, zero_mul] at hc
  simp at hc

/-! ### 3b.3 The normal-ordered square of a linear field on a mode

`magPoly_mul_monomial_ne` shows that `B_{ia}` cannot be identified with an occupation number:
multiplication by the field raises the occupation.  The object that *does* have a mode-by-mode
expectation is the normal-ordered square `:B²:`, and this subsection computes it for the linear
(derivative) half of the field.

A **mode state** is the monomial `ψ_m = monomial m 1`.  In the coefficient inner product
`⟨p, q⟩ = ∑_s conj(p_s) q_s` the monomials are orthonormal, so `ψ_m` is a unit vector and the Fock
expectation of an endomorphism `T` in that state is the single coefficient `⟨ψ_m, T ψ_m⟩ =
(T ψ_m)_m` (`modeExp`).  Multiplication by `X_i` raises the occupation and `pderiv i` lowers it;
`pderiv i` is the adjoint of `mulOp (X i)` in this inner product.  A **linear field**
`L = ∑_t c_t X_{l_t}` with real coefficients (the field components of this model are real) has
adjoint `L† = ∑_t c_t ∂_{l_t}` (`linField`, `linFieldAdj`).

The computation is the Wick contraction `[∂_l, X_{l'}] = δ_{ll'}` of `pderiv_X_mul`, one coordinate
at a time.  With `l` injective, `⟨ψ_m, L†L ψ_m⟩ = ∑_t c_t² (1 + m_{l_t})`
(`modeExp_linField_adj_comp`): one unit per field component — the contraction — plus the
occupation `m_{l_t}`.  Subtracting the contraction leaves the normal-ordered expectation
`∑_t c_t² m_{l_t}` (`modeExp_linField_normalOrdered`), i.e. **normal ordering is exactly "replace
`1 + n` by `n`"**, mode by mode.

Applied to the derivative half `B^∂_{ia} = ε_{ijk} ∂_j A_{k,a}` this gives
`⟨ψ_m, :(B^∂_{ia})²: ψ_m⟩ = ∑_{jk} ε_{ijk}² m_{∂_j A_{k,a}}` with contraction
`∑_{jk} ε_{ijk}² = 2` — the two transverse polarisations of `B_{ia}` — and `6` after summing over
the magnetic index, `48 = 24 · 2` over all `24` field components (`levi_sq_sum_magnetic`,
`levi_sq_sum_all_complex`).

What this section does **not** cover: the commutator half `f_{abc} A_b A_c` is quadratic, so its
square is quartic and its normal-ordered expectation is a four-field Wick contraction.  The
derivative half is the linear case, and for it the mode expectation is complete.
-/

/-- The **mode state** of a mode: the monomial with exponent vector `m`, in the
monomial-orthonormal representation of the Fock space. -/
def modeState (m : Fin 99 →₀ ℕ) : MvPolynomial (Fin 99) ℂ := MvPolynomial.monomial m 1

/-- The **Fock expectation in the mode state `ψ_m`**: the monomial basis is orthonormal, so
`⟨ψ_m, T ψ_m⟩` is the single coefficient of `ψ_m` in `T ψ_m`. -/
def modeExp (m : Fin 99 →₀ ℕ) (T : Module.End ℂ (MvPolynomial (Fin 99) ℂ)) : ℂ :=
  MvPolynomial.coeff m (T (modeState m))

/-- The derivative of a coordinate is a Kronecker symbol: `∂_i X_j = δ_{ij}`, as a `0/1`
polynomial — the elementary contraction. -/
theorem pderiv_X_eq_ite (i j : Fin 99) :
    (MvPolynomial.pderiv i (MvPolynomial.X j) : MvPolynomial (Fin 99) ℂ)
      = if i = j then 1 else 0 := by
  rw [MvPolynomial.pderiv_X]
  by_cases h : i = j
  · subst j; simp
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

/-- **Annihilation after creation is diagonal**: `∂_i (X_l · monomial m a)` has coefficient
`a · mᵢ` at `m` when `i = l`, and `0` otherwise.  This is the `n` of "`1 + n`", with no `+1`
because the derivative stands on the left. -/
theorem coeff_X_mul_pderiv_monomial (l i : Fin 99) (m : Fin 99 →₀ ℕ) (a : ℂ) :
    MvPolynomial.coeff m (MvPolynomial.X l * MvPolynomial.pderiv i (MvPolynomial.monomial m a))
      = if i = l then a * (m i : ℂ) else 0 := by
  by_cases h : i = l
  · subst i
    rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.coeff_smul]
    simp [mul_comm]
  · rw [if_neg h, MvPolynomial.pderiv_monomial]
    have hne : MvPolynomial.X l * MvPolynomial.monomial (m - Finsupp.single i 1) (a * ↑(m i))
        = MvPolynomial.monomial (Finsupp.single l 1 + (m - Finsupp.single i 1)) (a * ↑(m i)) := by
      rw [MvPolynomial.X, MvPolynomial.monomial_mul]
      simp
    rw [hne]
    have hkey : Finsupp.single l 1 + (m - Finsupp.single i 1) ≠ m := by
      intro he
      have hv := congrArg (fun s : Fin 99 →₀ ℕ => s l) he
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same] at hv
      have h2 : Finsupp.single i (1 : ℕ) l = 0 := Finsupp.single_eq_of_ne (Ne.symm h)
      rw [h2] at hv
      omega
    simp [MvPolynomial.coeff_monomial, hkey]

/-- The same statement on the mode state: `∂_i (X_l ψ_m)` has coefficient `mᵢ` at `m` when
`i = l`, and `0` otherwise. -/
theorem coeff_X_mul_pderiv_modeState (l i : Fin 99) (m : Fin 99 →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.X l * MvPolynomial.pderiv i (modeState m))
      = if i = l then (m i : ℂ) else 0 := by
  rw [modeState, coeff_X_mul_pderiv_monomial]
  simp

/-- **The contraction constant is one**: `⟨ψ_m, ∂_l X_{l'} ψ_m⟩ = δ_{ll'}(1 + m_l)`.  The `1` is
`[∂_l, X_l] = 1` and the `m_l` is the occupation; this is the whole content of the normal-ordering
computation below. -/
theorem coeff_pderiv_X_mul (l l' : Fin 99) (m : Fin 99 →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.pderiv l (MvPolynomial.X l' * modeState m))
      = if l = l' then 1 + (m l : ℂ) else 0 := by
  rw [MvPolynomial.pderiv_mul, pderiv_X_eq_ite]
  have h1 : MvPolynomial.coeff m
      ((if l = l' then (1 : MvPolynomial (Fin 99) ℂ) else 0) * modeState m)
      = if l = l' then 1 else 0 := by
    split_ifs with h
    · rw [one_mul]; simp [modeState]
    · rw [zero_mul]; simp
  rw [MvPolynomial.coeff_add, h1, coeff_X_mul_pderiv_modeState]
  split_ifs with h
  · ring
  · ring

/-- A **linear field** `L = ∑_t c_t X_{l_t}` with real coefficients `c_t` on the coordinates
`l_t`. -/
def linField {ι : Type*} [Fintype ι] (c : ι → ℝ) (l : ι → Fin 99) : MvPolynomial (Fin 99) ℂ :=
  ∑ t, ((c t : ℝ) : ℂ) • MvPolynomial.X (l t)

/-- The **adjoint** `L† = ∑_t c_t ∂_{l_t}` of a linear field: creation `X` replaced by
annihilation `∂`, with the same real coefficients. -/
def linFieldAdj {ι : Type*} [Fintype ι] (c : ι → ℝ) (l : ι → Fin 99) :
    Module.End ℂ (MvPolynomial (Fin 99) ℂ) :=
  ∑ t, ((c t : ℝ) : ℂ) • (MvPolynomial.pderiv (l t)).toLinearMap

/-- The adjoint acts term by term. -/
theorem linFieldAdj_apply {ι : Type*} [Fintype ι] (c : ι → ℝ) (l : ι → Fin 99)
    (p : MvPolynomial (Fin 99) ℂ) :
    linFieldAdj c l p = ∑ t, ((c t : ℝ) : ℂ) • MvPolynomial.pderiv (l t) p := by
  simp [linFieldAdj, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Multiplication by a linear field acts term by term. -/
theorem mulOp_linField_apply {ι : Type*} [Fintype ι] (c : ι → ℝ) (l : ι → Fin 99)
    (p : MvPolynomial (Fin 99) ℂ) :
    mulOp (linField c l) p = ∑ t, ((c t : ℝ) : ℂ) • (MvPolynomial.X (l t) * p) := by
  rw [linField, mulOp_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => smul_mul_assoc _ _ _

set_option maxHeartbeats 1000000 in
-- Expanding the `99`-coordinate magnetic energy into its derivative and commutator parts
-- produces large normal forms; the default heartbeat budget does not reach them.
-- The `ι`-indexed double sum and its cross-term cancellation need more than the default budget.
/-- **The un-ordered expectation of a linear field's square**: for an injective family of
coordinates, `⟨ψ_m, L†L ψ_m⟩ = ∑_t c_t² (1 + m_{l_t})`.  Each component contributes its
contraction `1` and its occupation `m_{l_t}`; the cross terms `l_t ≠ l_{t'}` cancel because
`∂_{l_t} X_{l_{t'}}` is off-diagonal in the monomial basis (`coeff_pderiv_X_mul`). -/
theorem modeExp_linField_adj_comp {ι : Type*} [Fintype ι] (c : ι → ℝ) (l : ι → Fin 99)
    (hinj : Function.Injective l) (m : Fin 99 →₀ ℕ) :
    modeExp m (linFieldAdj c l ∘ₗ mulOp (linField c l))
      = ∑ t, ((c t : ℝ) : ℂ) ^ 2 * (1 + (m (l t) : ℂ)) := by
  classical
  rw [modeExp, LinearMap.comp_apply, linFieldAdj_apply, mulOp_linField_apply]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, map_sum,
    Derivation.map_smul]
  have hstep : ∀ t t' : ι,
      MvPolynomial.coeff m (MvPolynomial.pderiv (l t) (MvPolynomial.X (l t') * modeState m))
        = if t = t' then 1 + (m (l t) : ℂ) else 0 := by
    intro t t'
    rw [coeff_pderiv_X_mul]
    by_cases h : t = t'
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun hl => h (hinj hl))]
  simp only [hstep]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single t]
  · simp only [if_true]
    ring_nf
  · intro t' _ hne
    rw [if_neg (Ne.symm hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

/-- **The normal-ordered expectation of a linear field's square**: subtracting the contraction
`∑_t c_t²` from `modeExp_linField_adj_comp` leaves `∑_t c_t² m_{l_t}`.  Normal ordering is exactly
the removal of the `1` of `1 + n` at every component, so the surviving expectation is the weighted
occupation. -/
theorem modeExp_linField_normalOrdered {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (l : ι → Fin 99) (hinj : Function.Injective l) (m : Fin 99 →₀ ℕ) :
    modeExp m (linFieldAdj c l ∘ₗ mulOp (linField c l)) - ∑ t, ((c t : ℝ) : ℂ) ^ 2
      = ∑ t, ((c t : ℝ) : ℂ) ^ 2 * (m (l t) : ℂ) := by
  rw [modeExp_linField_adj_comp c l hinj m]
  have hsplit : ∑ t, ((c t : ℝ) : ℂ) ^ 2 * (1 + (m (l t) : ℂ))
      = ∑ t, (((c t : ℝ) : ℂ) ^ 2 + ((c t : ℝ) : ℂ) ^ 2 * (m (l t) : ℂ)) := by
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hsplit]
  simp only [Finset.sum_add_distrib]
  ring

/-- For a fixed colour index, the derivative coordinates `(j,k) ↦ ∂_j A_{k,a}` are distinct: `24j +
8k + a` determines the pair. -/
theorem idxD_pair_injective (a : Fin 8) :
    Function.Injective (fun t : Fin 3 × Fin 3 => idxD t.1 t.2 a) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  have hv := congrArg Fin.val h
  simp only [idxD] at hv
  have hj : j.val = j'.val := by omega
  have hk : k.val = k'.val := by omega
  simp [Fin.ext_iff, hj, hk]

/-- The derivative half `B^∂_{ia} = ε_{ijk} ∂_j A_{k,a}` is a linear field in `(j,k)`. -/
theorem magDeriv_eq_linField (i : Fin 3) (a : Fin 8) :
    magDeriv i a
      = linField (fun t : Fin 3 × Fin 3 => levi i t.1 t.2) (fun t => idxD t.1 t.2 a) := by
  rw [linField, Fintype.sum_prod_type]
  rfl

/-- The adjoint of the derivative half of `B_{ia}`: the `ε`-weighted combination of the derivative
coordinate operators. -/
def magDerivAdj (i : Fin 3) (a : Fin 8) : Module.End ℂ (MvPolynomial (Fin 99) ℂ) :=
  linFieldAdj (fun t : Fin 3 × Fin 3 => levi i t.1 t.2) (fun t => idxD t.1 t.2 a)

/-- **The un-ordered square of one magnetic component on a mode**:
`⟨ψ_m, (B^∂_{ia})† B^∂_{ia} ψ_m⟩ = ∑_{jk} ε_{ijk}² (1 + m_{∂_j A_{k,a}})`. -/
theorem modeExp_magDeriv_adj_comp (i : Fin 3) (a : Fin 8) (m : Fin 99 →₀ ℕ) :
    modeExp m (magDerivAdj i a ∘ₗ mulOp (magDeriv i a))
      = ∑ j : Fin 3, ∑ k : Fin 3,
          ((levi i j k : ℝ) : ℂ) ^ 2 * (1 + (m (idxD j k a) : ℂ)) := by
  rw [magDerivAdj, magDeriv_eq_linField,
    modeExp_linField_adj_comp _ _ (idxD_pair_injective a) m, Fintype.sum_prod_type]

/-- **The normal-ordered square of one magnetic component on a mode**: subtracting the contraction
`∑_{jk} ε_{ijk}²` leaves `∑_{jk} ε_{ijk}² m_{∂_j A_{k,a}}` — the `ε`-weighted occupation of the
derivative coordinates. -/
theorem modeExp_magDeriv_normalOrdered (i : Fin 3) (a : Fin 8) (m : Fin 99 →₀ ℕ) :
    modeExp m (magDerivAdj i a ∘ₗ mulOp (magDeriv i a))
        - ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) ^ 2
      = ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) ^ 2 * (m (idxD j k a) : ℂ) := by
  rw [magDerivAdj, magDeriv_eq_linField,
    ← Fintype.sum_prod_type (f := fun t : Fin 3 × Fin 3 => ((levi i t.1 t.2 : ℝ) : ℂ) ^ 2),
    ← Fintype.sum_prod_type
      (f := fun t : Fin 3 × Fin 3 => ((levi i t.1 t.2 : ℝ) : ℂ) ^ 2 * (m (idxD t.1 t.2 a) : ℂ)),
    modeExp_linField_normalOrdered _ _ (idxD_pair_injective a) m]

/-- **The contraction of one magnetic component is `2`**: `∑_{jk} ε_{ijk}² = 2`, the two
transverse polarisations of `B_{ia}`. -/
theorem levi_sq_sum_magnetic (i : Fin 3) :
    ∑ j : Fin 3, ∑ k : Fin 3, (levi i j k) ^ 2 = 2 := by
  fin_cases i <;> simp only [Fin.sum_univ_three] <;> norm_num [levi]

/-- The same count over the complex numbers. -/
theorem levi_sq_sum_magnetic_complex (i : Fin 3) :
    ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) ^ 2 = 2 := by
  fin_cases i <;> simp only [Fin.sum_univ_three] <;> norm_num [levi]

/-- The contraction summed over the three magnetic components of one colour index: `6`. -/
theorem levi_sq_sum_total :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (levi i j k) ^ 2 = 6 := by
  simp only [Fin.sum_univ_three]
  norm_num [levi]

/-- The contraction summed over the magnetic index, over the complex numbers: `6`. -/
theorem levi_sq_sum_total_complex :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) ^ 2 = 6 := by
  simp only [Fin.sum_univ_three]
  norm_num [levi]

/-- The total contraction of the `24` magnetic components: `48 = 24 · 2`. -/
theorem levi_sq_sum_all_complex :
    ∑ _a : Fin 8, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ((levi i j k : ℝ) : ℂ) ^ 2 = 48 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, levi_sq_sum_total_complex]
  norm_num

/-- **The magnetic component's square, with its contraction made explicit**:
`⟨ψ_m, (B^∂_{ia})† B^∂_{ia} ψ_m⟩ = 2 + ∑_{jk} ε_{ijk}² m_{∂_j A_{k,a}}`.  The `2` is the
zero-point contribution of `B_{ia}` that normal ordering removes. -/
theorem modeExp_magDeriv_sq (i : Fin 3) (a : Fin 8) (m : Fin 99 →₀ ℕ) :
    modeExp m (magDerivAdj i a ∘ₗ mulOp (magDeriv i a))
      = 2 + ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) ^ 2 * (m (idxD j k a) : ℂ) := by
  rw [modeExp_magDeriv_adj_comp]
  have hsplit : ∑ j : Fin 3, ∑ k : Fin 3,
        ((levi i j k : ℝ) : ℂ) ^ 2 * (1 + (m (idxD j k a) : ℂ))
      = ∑ j : Fin 3, ∑ k : Fin 3, (((levi i j k : ℝ) : ℂ) ^ 2
          + ((levi i j k : ℝ) : ℂ) ^ 2 * (m (idxD j k a) : ℂ)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsplit]
  simp only [Finset.sum_add_distrib]
  rw [levi_sq_sum_magnetic_complex i]

/-- **The normal-ordered sum of `B²` over the magnetic index, on a mode**: subtracting the total
contraction `6` of the three components leaves the `ε`-weighted occupations. -/
theorem modeExp_magSum_normalOrdered (a : Fin 8) (m : Fin 99 →₀ ℕ) :
    (∑ i : Fin 3, modeExp m (magDerivAdj i a ∘ₗ mulOp (magDeriv i a)))
        - ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          ((levi i j k : ℝ) : ℂ) ^ 2 * (m (idxD j k a) : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => modeExp_magDeriv_normalOrdered i a m

/-- **The normal-ordered sum of `B²` over all `24` components, on a mode**: the contraction
removed is `48`, and what survives is the `ε`-weighted occupation of every derivative coordinate. -/
theorem modeExp_magAll_normalOrdered (m : Fin 99 →₀ ℕ) :
    (∑ a : Fin 8, ∑ i : Fin 3, modeExp m (magDerivAdj i a ∘ₗ mulOp (magDeriv i a)))
        - ∑ _a : Fin 8, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            ((levi i j k : ℝ) : ℂ) ^ 2
      = ∑ a : Fin 8, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          ((levi i j k : ℝ) : ℂ) ^ 2 * (m (idxD j k a) : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => modeExp_magDeriv_normalOrdered i a m

/-- The full magnetic energy has real coefficients, so its operator is Gauss symmetric. -/
theorem realCoeff_magEnergy (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : RealCoeff (magEnergy fabc) := by
  refine RealCoeff.sum fun i _ => RealCoeff.sum fun a _ => ?_
  rw [pow_two]
  exact RealCoeff.mul (realCoeff_magPoly fabc i a) (realCoeff_magPoly fabc i a)

/-- Multiplication operators add: `mulOp (p + q) = mulOp p + mulOp q`. -/
theorem mulOp_add (p q : MvPolynomial (Fin 99) ℂ) : mulOp (p + q) = mulOp p + mulOp q := by
  refine LinearMap.ext fun r => ?_
  rw [LinearMap.add_apply]
  exact add_mul p q r

/-- The multiplication operator of the full energy is the sum of the three parts'. -/
theorem mulOp_magEnergy_eq (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    mulOp (magEnergy fabc)
      = mulOp magEnergyQuad + mulOp (magEnergyCross fabc) + mulOp (magEnergyQuart fabc) := by
  rw [magEnergy_eq_parts, mulOp_add, mulOp_add]

set_option maxHeartbeats 3000000 in
-- Expanding the `99`-coordinate magnetic energy into its derivative and commutator parts
-- produces large normal forms; the default heartbeat budget does not reach them.
/-- **The energy operator on the core is the sum of the parts' operators.**  The quadratic half is
the Cartan-sector comparison operator, so this is also the statement that the cubic and quartic
interactions survive the map into the comparison instead of being absorbed by it. -/
theorem magEnergyOps_apply_eq (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    Φ.op (mulOp (magEnergy fabc)) x
      = Φ.op (mulOp (magEnergyQuad)) x + Φ.op (mulOp (magEnergyCross fabc)) x
        + Φ.op (mulOp (magEnergyQuart fabc)) x := by
  rw [CoreRep.op_apply, mulOp_magEnergy_eq]
  simp only [CoreRep.op_apply, LinearMap.add_apply, map_add]

/-- The full magnetic energy operator is symmetric on the core. -/
theorem magEnergyOps_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    SymmetricOn D (D.subtype.comp (Φ.op (mulOp (magEnergy fabc)))) :=
  Φ.symmetricOn_op (mulOp_polySym (realCoeff_magEnergy fabc))

/-! ## 3c. Relative bounds: the cross term and the commutator square

`YangMillsSoftDirections.norm_add_sq_ge_split` is the plan's starting estimate
`‖X + Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)‖Y‖²`.  Applied mode by mode to `B = ∂A + [A,A]` it is the
relative bound for §3b's cross term: the cubic term costs at most `ε` of the derivative square and
charges `ε⁻¹` of the commutator square, so the quadratic energy survives with coefficient `1 − ε`
and the loss is paid by the quartic part.  `magEnergy_form_eq` is the same statement as an exact
identity — the physical-core energy of §3b read component by component — and
`magEnergy_form_ge_of_quart_bound` is the step that closes S2: a quartic part relatively bounded by
the quadratic energy with ratio `κ` leaves `1 − ε − (ε⁻¹ − 1)κ` of that energy, which at
`ε = 1/2`, `κ = 1/4` is a quarter.  -/

/-- The polarization identity of a complex inner product space, in the shape the split uses. -/
theorem norm_add_sq_complex {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (u v : F) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (inner ℂ u v : ℂ).re + ‖v‖ ^ 2 := by
  rw [@norm_add_sq ℂ]
  simp

/-- The **derivative part of the magnetic field on the core**, indexed as `magOps` is. -/
def magDerivOps (Φ : CoreRep 99 D) (m : Fin 24) : D →ₗ[ℂ] D :=
  Φ.op (mulOp (magDeriv (decodeSpace m) (decodeColor m)))

/-- The **commutator part of the magnetic field on the core**, indexed as `magOps` is. -/
def magCommOps (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) :
    D →ₗ[ℂ] D :=
  Φ.op (mulOp (magComm fabc (decodeSpace m) (decodeColor m)))

/-- `CoreRep.op` is additive in its polynomial operator. -/
theorem coreRep_op_add (Φ : CoreRep 99 D)
    (S T : Module.End ℂ (MvPolynomial (Fin 99) ℂ)) : Φ.op (S + T) = Φ.op S + Φ.op T := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, CoreRep.op_apply, map_add]

/-- **`B = ∂A + [A,A]` on the core**: `magOps` is the sum of its derivative and commutator
parts, so the split of §1 holds for the magnetic *operator*, not only for the polynomial. -/
theorem magOps_eq_split (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) :
    magOps Φ fabc m = magDerivOps Φ m + magCommOps Φ fabc m := by
  simp only [magOps, magDerivOps, magCommOps, magPoly_eq_deriv_add, mulOp_add, coreRep_op_add]

set_option maxHeartbeats 1000000 in
-- Expanding the `99`-coordinate magnetic energy into its derivative and commutator parts
-- produces large normal forms; the default heartbeat budget does not reach them.
/-- **The magnetic energy, mode by mode**: `‖B_m x‖²` is the derivative square, plus twice the
real cross term, plus the commutator square. -/
theorem norm_magOps_sq_eq (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D)
    (m : Fin 24) :
    ‖(((magOps Φ fabc m) x : D) : L2d 99)‖ ^ 2
      = ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2
        + 2 * (inner ℂ (((magDerivOps Φ m) x : D) : L2d 99)
            (((magCommOps Φ fabc m) x : D) : L2d 99)).re
        + ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 := by
  have hsplit : (((magOps Φ fabc m) x : D) : L2d 99)
      = (((magDerivOps Φ m) x : D) : L2d 99)
        + (((magCommOps Φ fabc m) x : D) : L2d 99) := by
    rw [magOps_eq_split, LinearMap.add_apply]
    rfl
  rw [hsplit, norm_add_sq_complex]

set_option maxHeartbeats 1000000 in
-- Expanding the `99`-coordinate magnetic energy into its derivative and commutator parts
-- produces large normal forms; the default heartbeat budget does not reach them.
/-- **The physical-core energy identity**: summed over the `24` field components, the magnetic
form is the derivative square plus the cross term plus the commutator square.  Nothing is dropped
and no term is absorbed into a quadratic model. -/
theorem magEnergy_form_eq (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    (∑ m : Fin 24, ‖(((magOps Φ fabc m) x : D) : L2d 99)‖ ^ 2)
      = (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
        + 2 * ∑ m : Fin 24,
            (inner ℂ (((magDerivOps Φ m) x : D) : L2d 99)
              (((magCommOps Φ fabc m) x : D) : L2d 99)).re
        + ∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 := by
  calc (∑ m : Fin 24, ‖(((magOps Φ fabc m) x : D) : L2d 99)‖ ^ 2)
      = ∑ m : Fin 24,
          (‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2
            + 2 * (inner ℂ (((magDerivOps Φ m) x : D) : L2d 99)
                (((magCommOps Φ fabc m) x : D) : L2d 99)).re
            + ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2) :=
        Finset.sum_congr rfl fun m _ => norm_magOps_sq_eq Φ fabc x m
    _ = (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          + (∑ m : Fin 24,
              2 * (inner ℂ (((magDerivOps Φ m) x : D) : L2d 99)
                (((magCommOps Φ fabc m) x : D) : L2d 99)).re)
          + ∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 :=
        by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          + 2 * ∑ m : Fin 24,
              (inner ℂ (((magDerivOps Φ m) x : D) : L2d 99)
                (((magCommOps Φ fabc m) x : D) : L2d 99)).re
          + ∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 :=
        by rw [Finset.mul_sum]

set_option maxHeartbeats 1000000 in
-- The split of the energy over the `24` components is stated as a rewriting problem whose
-- terms carry the `99`-coordinate core representation; the default budget is not enough.
/-- **The relative bound for the cross and commutator parts.**  For every `ε > 0` the magnetic
energy is at least `(1 − ε)` of the derivative square minus `(ε⁻¹ − 1)` of the commutator square:
the cubic cross term costs at most the fraction `ε` of the quadratic energy, and its loss is
charged to the quartic part.  This is `norm_add_sq_ge_split` summed over the `24` field
components; it is unconditional — no information about the interaction enters. -/
theorem magEnergy_form_ge_split (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D)
    {ε : ℝ} (hε : 0 < ε) :
    (1 - ε) * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
        - (ε⁻¹ - 1) * (∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2)
      ≤ ∑ m : Fin 24, ‖(((magOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  have hsplit : (((magOps Φ fabc m) x : D) : L2d 99)
      = (((magDerivOps Φ m) x : D) : L2d 99)
        + (((magCommOps Φ fabc m) x : D) : L2d 99) := by
    rw [magOps_eq_split, LinearMap.add_apply]
    rfl
  rw [hsplit]
  exact BookProof.YangMillsSoftDirections.norm_add_sq_ge_split (E := L2d 99)
    (X := (((magDerivOps Φ m) x : D) : L2d 99))
    (Y := (((magCommOps Φ fabc m) x : D) : L2d 99)) hε

/-- **S2 coercivity from a quartic relative bound.**  If the commutator square is relatively bounded
by the derivative square with ratio `κ` and shift `b`,
`Σ‖C_m x‖² ≤ κ Σ‖D_m x‖² + b‖x‖²`, then for any `0 < ε < 1` the full magnetic energy still
contains `1 − ε − (ε⁻¹ − 1)κ` of the derivative energy:
`(1 − ε − (ε⁻¹ − 1)κ) Σ‖D_m x‖² − (ε⁻¹ − 1)b‖x‖² ≤ Σ‖B_m x‖²`.  This is the step that turns a
relative bound strictly below `1` into a positive coefficient on the quadratic energy; the
relative bound on the quartic part is the hypothesis, not a consequence of the split. -/
theorem magEnergy_form_ge_of_quart_bound (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {ε κ b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbound : ∀ x : D,
      (∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2)
        ≤ κ * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          + b * ‖(x : L2d 99)‖ ^ 2)
    (x : D) :
    (1 - ε - (ε⁻¹ - 1) * κ)
        * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
        - (ε⁻¹ - 1) * b * ‖(x : L2d 99)‖ ^ 2
      ≤ ∑ m : Fin 24, ‖(((magOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 := by
  have hmain := magEnergy_form_ge_split Φ fabc x hε0
  have hinv : 1 ≤ ε⁻¹ := by
    have h1 : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε0.ne'
    have h2 : ε * ε⁻¹ ≤ 1 * ε⁻¹ := mul_le_mul_of_nonneg_right hε1.le (inv_nonneg.mpr hε0.le)
    linarith
  have hcoe : 0 ≤ ε⁻¹ - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left (hbound x) hcoe
  nlinarith [hmul, hmain]

/-- The plan's concrete choice `ε = 1/2` with relative bound `κ = 1/4`: a quarter of the
derivative energy survives, at the price of the shift `b‖x‖²`. -/
theorem magEnergy_form_ge_quarter (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    {b : ℝ}
    (hbound : ∀ x : D,
      (∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2)
        ≤ (1 / 4) * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          + b * ‖(x : L2d 99)‖ ^ 2)
    (x : D) :
    (1 / 4) * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
        - b * ‖(x : L2d 99)‖ ^ 2
      ≤ ∑ m : Fin 24, ‖(((magOps Φ fabc m) x : D) : L2d 99)‖ ^ 2 := by
  have h := magEnergy_form_ge_of_quart_bound Φ fabc (ε := 1 / 2) (κ := 1 / 4) (b := b)
    (by norm_num) (by norm_num) hbound x
  have hcoef : 1 - 1 / 2 - ((1 / 2 : ℝ)⁻¹ - 1) * (1 / 4) = 1 / 4 := by norm_num
  have hcoef2 : ((1 / 2 : ℝ)⁻¹ - 1) * b = b := by
    rw [show ((1 / 2 : ℝ)⁻¹ - 1) = 1 by norm_num, one_mul]
  simp only [hcoef, hcoef2] at h
  exact h

set_option maxHeartbeats 1000000 in
-- Expanding the `99`-coordinate magnetic energy into its derivative and commutator parts
-- produces large normal forms; the default heartbeat budget does not reach them.
/-- **The physical-core energy identity for the Hamiltonian**: `H₁`'s form is the kinetic square
plus the magnetic energy, and the magnetic half is the derivative square plus the cross term plus
the commutator square.  This is `ymHamiltonian_quadForm` with §3b's decomposition substituted, i.e.
`½Σπ² + ½Σ(∂A + [A,A])²` with nothing truncated. -/
theorem ymHamiltonian_quadForm_split (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : D) :
    quadForm (ymHamiltonian Φ fabc) x
      = 1 / 2 * (∑ m : Fin 24, ‖(((piOps Φ m) x : D) : L2d 99)‖ ^ 2)
        + 1 / 2 * ((∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          + 2 * ∑ m : Fin 24,
              (inner ℂ (((magDerivOps Φ m) x : D) : L2d 99)
                (((magCommOps Φ fabc m) x : D) : L2d 99)).re
          + ∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2) := by
  rw [ymHamiltonian_quadForm, magEnergy_form_eq]

/-- **The S2 coercivity shape on the core**: the kinetic square plus the coercive magnetic
lower bound is a lower bound for the Yang–Mills form, with the quartic relative bound as the only
input. -/
theorem ymHamiltonian_quadForm_ge_of_quart_bound (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {ε κ b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbound : ∀ x : D,
      (∑ m : Fin 24, ‖(((magCommOps Φ fabc m) x : D) : L2d 99)‖ ^ 2)
        ≤ κ * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          + b * ‖(x : L2d 99)‖ ^ 2)
    (x : D) :
    1 / 2 * (∑ m : Fin 24, ‖(((piOps Φ m) x : D) : L2d 99)‖ ^ 2)
        + 1 / 2 * ((1 - ε - (ε⁻¹ - 1) * κ)
            * (∑ m : Fin 24, ‖(((magDerivOps Φ m) x : D) : L2d 99)‖ ^ 2)
          - (ε⁻¹ - 1) * b * ‖(x : L2d 99)‖ ^ 2)
      ≤ quadForm (ymHamiltonian Φ fabc) x := by
  rw [ymHamiltonian_quadForm_split]
  have h := magEnergy_form_ge_of_quart_bound Φ fabc hε0 hε1 hbound x
  have heq := magEnergy_form_eq Φ fabc x
  linarith

/-! ## 3d. The mode identification with the coefficient model

§3c relates the two halves of `Σ B²`, but it needs a *quartic relative bound* in the direction
`quartic ≤ κ · quadratic + b‖·‖²` to convert the estimate into a coercivity statement.  That
direction is not available: on the coefficient model of `BookProof.YangMillsFormDomination` the
quartic slot is the normal-ordered `:N²:` form `quarticDegreeForm`, and
**`not_quartic_relativeBound`** shows that no `κ, b` make it small against `degreeForm` — the
quartic grows like `N²` where the degree form grows like `N`, so the ratio is unbounded.

What the coefficient model *does* supply is the reverse inequality
(`YangMillsEffectiveBarrier.barrierBound_quartic`): the quartic form dominates the degree form
plus Simon's barrier, up to an explicit shift.  So coercivity is reached by *identifying* the
core's magnetic energy with the model's `magneticEnergyForm`, not by bounding the quartic from
above.  This section states that identification and proves what it yields.

* **`modeVec`**, **`coeffToCore`**, **`coeffToCore_norm_sq`** — the concrete half.  The adapted
  orthonormal basis `coreBasis e` is indexed by `ℕ ≃ (Fin d →₀ ℕ)`, so a coefficient vector is
  sent to `∑ n, c n • ψ_n` and that map is an isometry: `‖coeffToCore c‖² = coreNormSq c`.
* **`totalDegree_occMonomial`** — the occupation of a mode is the degree of its monomial,
  `totalDegree (∏ i, X i ^ nᵢ) = ∑ i, nᵢ`; this is the sense in which the model's multi-index *is*
  the degree vector of the field-space polynomial.
* **`ModeIdentification`** — the interface: an isometric map of coefficient vectors into the core
  whose magnetic form is `magneticEnergyForm diagA`.  This is the mode-expansion step
  (occupation ↔ field amplitude) that the earlier chapters record as unformalised; the theorems
  below are what it is *for*.
* **`magEnergy_ge_of_identification`**, **`ymHamiltonian_quadForm_ge_of_identification`**,
  **`s2_gap_constant`** — the transfers: the barrier bound becomes coercivity of the core's form,
  with the explicit constants `1/24` and `1/48` and the certified gap `c₁ Δ_ref / 48`.
* **`not_modeIdentification_abelian`** — the abelian sector is a *counterexample*, not an
  inhabitant: the `:N²:` magnetic form vanishes at the vacuum while the abelian magnetic operator
  is injective there, so the identification fails on the normal-ordering constant.
* **`s2FormDomination`**, **`s2_ground_threshold`**, **`s2_excited_threshold`** — the constant as
  a `FormDomination` certificate, so the thresholds are those of the certificate machinery;
* **`s2FormDomination_c₁`**, **`s2FormDomination_c₂`**, **`s2_certified_separation`**,
  **`s2_separation_pos`**, **`s2_certified_gap`**, **`s2_gap_threshold_pos`** — the certificate
  driven through the chapter's gap chain: ratio `c₁/48`, shift `(c₁μ₀ + quarticShift)/48`,
  separation `c₁Δ_ref/48 > 0`, the excited-sector bound in the `quartic_certified_gap` shape, and
  positivity of the threshold exactly when `quarticShift < c₁ Δ_ref`.
* **`colourIndex`**, **`embedIndex`**, **`modeVec99`**, **`embedL2`**, **`embedL2_norm_sq`**,
  **`embedL2_mem_polyGaussCore`**, **`embedCore`**, **`embedCore_norm_sq`** — the
  `L²(ℝ²⁴) → L²(ℝ⁹⁹)` embedding: the occupation of mode `m` is placed on the gauge coordinate
  `A_{j,a}`, which is an orthonormal subfamily of the `ℝ⁹⁹` adapted basis, so the embedding is an
  isometry with no Mehler analysis, and it lands on `polyGaussCore`.  This discharges the
  `norm_sq` field of the root-sector identification for the concrete candidate;
* **`mulOp_X_monomial`**, **`mulOp_X_monomial_ne`** — what `magOps` does to a mode: the derivative
  coordinate is independent, so multiplication by `X (idxD j k a)` *raises* its occupation and is
  never scalar on a monomial.  This is the obstruction to `mag_eq_root`: the field-strength
  operator is not diagonal in the occupation basis, and the `:N²:` form needs the normal-ordered
  contraction, not the diagonal part;
* **`levi_contract`**, **`eps_contract_poly`**, **`magPoly_sq_contract`**, **`magFullBilin`**,
  **`magEnergy_eq_contract`** — the `ε`–`ε` contraction `∑_i ε_{ijk}ε_{ilm} = δ_{jl}δ_{km} −
  δ_{jm}δ_{kl}` and its polynomial form, giving `Σ_{ia}B_{ia}² = Σ_{a,j,k}(P² − P·Pᵀ)` with
  `P = ∂A + f[A,A]`: the `ε` weights disappear and the `f` weights sit inside `P`;
* **The honest boundary of the identification**: `mag_eq_root` is *not* derivable from
  `magOps` — `mulOp_X_monomial_ne` shows the derivative half shifts every mode, so no occupation
  vector is an eigenvector;
* **`IsAntisymmetric`**, **`SatisfiesJacobi`**, **`fabc_self_eq_zero`**, **`colourTensor`**,
  **`colourTensor_cyclic`**, **`colour_contraction_double`** — the structure-constant hypotheses
  and what they buy: a repeated index vanishes, Jacobi *is* the cyclic vanishing of the colour
  tensor, and antisymmetry makes the `ε` contraction of an antisymmetric pair **double** — the
  factor `2` of the quartic colour energy;
* **`su2Slot`**, **`su2Struct`**, **`su2Struct_slot`**, **`su2Struct_zero_left`**,
  **`su2Struct_zero_mid`**, **`su2Struct_zero_right`**, **`sum_fin8_eq_sum_su2`** — the *instance*:
  `f_{abc} = ε_{abc}` on the first three colour indices and `0` off them is the `su(2)`
  structure-constant tensor, so the free `fabc` of §3b.2 can be read concretely;
* **`levi_antisym`**, **`su2Struct_antisym`**, **`su2Struct_jacobi`** — the instance **satisfies**
  the two hypotheses of §3b.2, so no side condition is left open for it;
* **`colourTensor_su2`**, **`su2_casimir_adjoint`**, **`su2_casimir_adjoint_value`**,
  **`su2_colourWeight_sum`** — the colour factor, computed:
  `K_{abcd} = δ_{ac}δ_{bd} − δ_{ad}δ_{bc}`,
  `Σ_{ab} f_{abe}f_{abd} = 2δ_{ed}` (`C_A = 2`), and `Σ_{abc} f_{abc}² = C_A·dim(adj) = 6`;
* **`pauli`**, **`fundRep`**, **`fundRep_commutator`**, **`su2_casimir_fundamental`**,
  **`fundRep_trace_mul`** — the **fundamental representation** `T^a = σ^a/2` on `ℂ²`: it closes with
  the same `ε` (`fundRep_commutator_su2Struct` against `su2Struct`), its Casimir is `C_F = 3/4`
  (`Σ_a T^a T^a = (3/4)·1`), and `tr(T^a T^b) = δ^{ab}/2`.  So `C_A = 2` and `C_F = 3/4` are both
  computed from the instantiating `ε`, each in its own representation;
* **`pderiv_X_mul`**, **`normalOrder_contraction`**, **`coeff_zero_magPoly`**,
  **`magPoly_mul_monomial_ne`** — the normal-ordered side: `[∂ᵢ, Xᵢ] = 1` is the contraction
  constant, and `magPoly`'s multiplication is off-diagonal at every monomial, so the `:N²:` form is
  the contracted quantity, not the diagonal of `magOps`;
* **`modeState`**, **`modeExp`**, **`pderiv_X_eq_ite`**, **`coeff_X_mul_pderiv_monomial`**,
  **`coeff_X_mul_pderiv_modeState`**, **`coeff_pderiv_X_mul`** — the mode expectation, which
  `magPoly_mul_monomial_ne` makes necessary: in the monomial-orthonormal representation the mode
  state is a unit vector, so its expectation is one coefficient, and the elementary contraction
  `⟨ψ_m, ∂_l X_{l'} ψ_m⟩ = δ_{ll'}(1 + m_l)` is computed exactly;
* **`linField`**, **`linFieldAdj`**, **`linFieldAdj_apply`**, **`mulOp_linField_apply`**,
  **`modeExp_linField_adj_comp`**, **`modeExp_linField_normalOrdered`** — a linear field
  `L = ∑_t c_t X_{l_t}` with its adjoint `L† = ∑_t c_t ∂_{l_t}`: for injective `l`,
  `⟨ψ_m, L†L ψ_m⟩ = ∑_t c_t²(1 + m_{l_t})`, so *normal ordering is exactly "replace `1 + n` by
  `n`"*, leaving `∑_t c_t² m_{l_t}`;
* **`idxD_pair_injective`**, **`magDeriv_eq_linField`**, **`magDerivAdj`**,
  **`modeExp_magDeriv_adj_comp`**, **`modeExp_magDeriv_normalOrdered`**, **`modeExp_magDeriv_sq`**
  — the derivative half of the field is a linear field, and its square's mode expectation is
  `2 + ∑_{jk} ε_{ijk}² m_{∂_j A_{k,a}}`: the contraction of one magnetic component is `2`;
* **`levi_sq_sum_magnetic`**, **`levi_sq_sum_total`**, **`levi_sq_sum_all_complex`**,
  **`levi_sq_sum_magnetic_complex`**, **`levi_sq_sum_total_complex`** — the `ε` counts: `2` per
  magnetic component (two transverse polarisations), `6` per colour index, `48 = 24 · 2` over all
  `24` components — the zero-point magnetic energy normal ordering removes;
* **`modeExp_magSum_normalOrdered`**, **`modeExp_magAll_normalOrdered`** — the normal-ordered sum
  of `B²` on a mode, first over the magnetic index and then over all `24` components: the
  `ε`-weighted occupation of every derivative coordinate;
* **The boundary of this computation**: the derivative half is *linear*, so its square is
  quadratic and its mode expectation is the Wick contraction above.  The commutator half
  `f_{abc}A_b A_c` is quadratic, so its square is quartic and off-diagonal at every monomial — its
  normal-ordered expectation is a four-field contraction, not the two-field one proved here;
* **`rootDomain`**, **`mem_rootDomain`**, **`rootDomain_ne_top`**, **`root_spectral_gap`** — the
  root sector as a form domain (the kernel of evaluation at the vacuum) and the positive
  root-sector gap `(c₁ Δ_ref − quarticShift)/48` that holds on it, where the whole-core threshold
  is spoilt by the vacuum;
* **`norm_sq_apply_zero_le_coreNormSq`**, **`rootDomain_eq_span_excited`** — the root domain is the
  **vacuum-orthogonal core**: `‖c 0‖² ≤ coreNormSq c`, and a core vector has no vacuum component
  exactly when it is a finite combination of the *excited* occupation basis vectors, so the density
  here is algebraic (the excited span *is* the orthogonal core), not analytic;
* **`rootDomain_closed_of_tendsto`**, **`closure_rootDomain_iff`** — the root domain is closed under
  `coreNormSq` limits, so its closure is itself; this is the only topology the coefficient model
  supports (there is no completed space, so limits are sequence limits);
* **`root_spectral_gap_on_closure`** — the gap on the closure, i.e. for any point that is a
  `coreNormSq` limit of root-domain vectors: no limiting argument on the quartic form is used (and
  none is available — `quadForm (ymHamiltonian …)` is not known to be continuous in `coreNormSq`);
* **`coreLp`**, **`coreToLp`**, **`norm_coreToLp_sq`**, **`norm_sq_eq_tsum`** — the ℓ² completion
  of the coefficient model, the embedding of the finitely supported core into it (isometric:
  `coreNormSq` is the squared ℓ² norm), and the norm formula `‖f‖² = ∑' n, ‖f n‖²`;
* **`vacuumOrthogonal`**, **`isClosed_vacuumOrthogonal`**, **`mem_closure_rootDomain_image`**,
  **`closure_rootDomain_image_eq`** — the vacuum-orthogonal closed subspace of the completion, and
  the analytic density statement: finite-support root vectors are dense in it, so its closure **is**
  that subspace;
* **`refFormLp`**, **`ref_spectral_gap_closure`** — the reference form on its natural (unbounded)
  domain in ℓ², and `href_spectral_gap` extended to it: the gap holds on the completion wherever the
  form is finite, with summability carried as a hypothesis.  The quartic Yang–Mills form has no ℓ²
  analogue here, and none is claimed;
* **`fundMode`**, **`colourModeVec`**, **`colourEnergy`** — the `ℂ²` colour factor of a mode: the
  completion carries a colour fibre, and on `c ⊗ v` the Casimir multiplies `v` by `C_F = 3/4` while
  leaving the Fock coefficients `c n` untouched (`colourEnergy_colourModeVec`);
* **`colourEnergyOp`**, **`norm_colourEnergyOp`**, **`norm_colourEnergyOp_eq`**, **`adjRep`**,
  **`adjModeVec`**, **`adjColourEnergy`** — the colour factor as an operator, and the gluon factor:
  `colourEnergy` is `(3/4) • id` on the whole completion (`colourEnergy_eq_smul`), so it is a
  continuous linear map with norm exactly `3/4`; `adjRep` is the adjoint representation on `ℂ³`
  (`[T^a, T^b] = i ε^{abc}T^c`, `adjRep_commutator`) with Casimir `C_A = 2` (`adjRep_casimir`), so
  `c ⊗ v` carries `2 v` (`adjColourEnergy_adjModeVec`) and `C_A/C_F = 8/3` (`casimir_ratio`);
* **`colourSpace`**, **`colouredCore`**, **`colouredHamiltonian`**, **`colourFibre`** — the colour
  fibre attached to the field core, with `H ⊗ 1 + 1 ⊗ C` acting componentwise; on the elementary
  tensor `x ⊗ v` the form is `‖v‖² (quadForm H x + C ‖x‖²)`
  (`colouredHamiltonian_smul_one_quadForm`), hence `C_F = 3/4` inside `quadForm (ymHamiltonian …)`
  (`colouredHamiltonian_fundamental_quadForm`) and `C_A = 2`
  (`colouredHamiltonian_adjoint_quadForm`);
* **`colouredHamiltonian_smul_one_quadForm_core`**, **`colourFibre_repr`**,
  **`colourSum`** — the same identities on the *whole* coloured core: the form of a diagonal colour
  energy is the sum over components of the field form plus `µ.re` times the component norm squared,
  and every core element is a finite sum of elementary tensors (`colourFibre_repr`, `colourSum`),
  whose form is `colouredHamiltonian_smul_one_quadForm_sum`;
* **`colouredHamiltonian_quadForm_core`** (general `C`), **`colouredHamiltonian_swap_quadForm`**
  — the coloured form for a colour matrix that is *not* diagonal: the colour part is the double
  sum `Σ_i Σ_j C_ij ⟨u_i, u_j⟩` (`colouredHamiltonian_inner_core`), so the off-diagonal entries
  contribute the mixed terms; for `C = [[0, 1], [1, 0]]` the form is
  `quadForm H u₀ + quadForm H u₁ + 2 Re ⟨u₀, u₁⟩`, a cross term no `µ • 1` can produce;
* **`mesonRep_commutator`**, **`glueballRep_commutator`** — the two total actions *are*
  representations: `[A^a, A^b] = i ε^{abc}A^c` on `colourVec 4` and `colourVec 9`, proved by the
  Kronecker-sum argument (`kronSum`, `kronSum_mul`, `kronSum_commutator`) on the product basis and
  carried over by the row-major relabellings `mesonEquiv`/`glueballEquiv`, so no entry check is
  involved;
* **`mesonSinglet`**, **`glueballSinglet`** — the singlets of the two *squares*: `2 ⊗ 2 = 3 ⊕ 1`
  with `ε` as the singlet (`mesonCoeff_mem`) and `3 ⊗ 3 = 5 ⊕ 3 ⊕ 1` with the trace `δ`
  (`glueballCoeff_mem`); each singlet space is exactly one line (`mesonSinglet_eq_span`,
  `glueballSinglet_eq_span`) and the line is nonzero (`mesonSingletVec_ne_zero`,
  `glueballSingletVec_ne_zero`), so unlike `ℂ² ⊗ ℂ³` these fibres do carry colour-neutral
  states `—` a quark–antiquark `ε` and a glueball trace `δ`;
* **`mesonSymm`**, **`mesonAlt`**, **`meson_isCompl`**, **`mesonSymm_finrank`** — the *meson*
  square split: the slot swap `mesonFlipIdx` gives symmetric and antisymmetric parts, disjoint and
  spanning (`meson_disjoint`, `meson_sup`), so `ℂ² ⊗ ℂ² = mesonAlt ⊕ mesonSymm` with
  `mesonAlt = span{ε}` one-dimensional (`mesonAlt_eq_span`, `mesonAlt_finrank`) and the triplet
  `mesonSymm` of dimension `3`; both parts are closed under every total action
  (`mesonAct_mem_symm`, `mesonAct_mem_alt`), the swap symmetry of the action being
  `mesonRep_flip_row`;
* **`colourTerm_star_eq`**, **`colourPair_re_symm`**, **`colourDiag_re`**,
  **`colouredHamiltonian_quadForm_re_split`** — the **Hermitian-`C`** form: for `C` with
  `Cᴴ = C` the colour term `Σ_i Σ_j C_ij ⟨u_i, u_j⟩` equals its own star (it is real), the `(j,i)`
  and `(i,j)` off-diagonal contributions agree, and the form splits as
  `Σ_i (quadForm H u_i + (C_ii).re ‖u_i‖²)` + the off-diagonal real parts;
* **`colourPairSum_eq_two_mul_upper`** — the same symmetry as an identity of sums: the
  off-diagonal part over `j ≠ i` is twice its sum over `i < j`, since each unordered pair is counted
  twice with one real value;
* **`colouredHamiltonian_symmetricOn`** — and the *operator*: for `Cᴴ = C` the coloured
  Hamiltonian is symmetric on the whole coloured core,
  `⟨(H ⊗ 1 + 1 ⊗ C) u, v⟩ = ⟨u, (H ⊗ 1 + 1 ⊗ C) v⟩` — the field half by
  `ymHamiltonian_symmetricOn`, the colour half by Hermiticity (`conj C_ij = C_ji` under `i ↔ j`);
* **`colourSinglet`**, **`colourSinglet_eq_bot`** — the colour singlet over the combined
  `ℂ² ⊗ ℂ³` fibre: the total action `pairRep` is `T^a ⊗ 1 + 1 ⊗ T^a`
  on `colourVec 6` (`pairSlotFst`, `pairSlotSnd`), and the vectors it annihilates are only the
  zero one (`colourSinglet_eq_bot`) — `2 ⊗ 3 = 4 ⊕ 2` has no trivial summand, so a
  fundamental and an adjoint mode over one field core are never colour-neutral together
  (`colourSinglet_fibre_trivial`);
* **`pairRep_commutator`** — that total action *is* a representation: `[A^a, A^b] = i ε^{abc}A^c`,
  proved on the product basis (`pairRepProd`, `pairRepProd_commutator`) where the two mixed
  products `T^a ⊗ T^b` cancel between the two orders, and transported to `colourVec 6` along
  `pairEquiv` (`pairRep_eq_reindex`);
* **`colourActCLM`**, **`colourEnergyCLM`** — the two coloured actions as *bounded operators* on the
  completion: `‖colourActCLM a f‖ ≤ (1/2)‖f‖`, the constant being sharp because
  `‖T^a v‖ = ‖v‖/2` pointwise (`norm_fundRep_mulVec`), and `colourEnergyCLM` is `C_F` times the
  identity, `colourEnergyCLM = (3/4) • 1`, so `‖colourEnergyOp d‖ = 3/4` exactly
  (`norm_colourEnergyOp_eq`).  Neither touches the Fock coefficients (`colourActOp_colourModeVec`);
* **`colourActCLM_commutator`**, **`sum_colourActCLM_comp`** — those operators are a representation
  of `su(2)`: `[A^a, A^b] = i ε^{abc} A^c` on the completion with the chapter's own `ε`, and the
  Casimir of the representation is `Σ_a (A^a)² = colourEnergyCLM`, i.e. `C_F` times the identity.
  Boundedness is what makes the commutator equality hypothesis-free, which the unbounded
  Hamiltonian does not allow;
* **`norm_colourActCLM`** — the constant `1/2` is attained and not merely a bound: `‖A^a f‖ = ‖f‖/2`
  for every `f` (`colourActOp_norm`), so `‖colourActCLM a‖ = 1/2` exactly;
* **`colourGroupElement_mem_unitary`**, **`colourGroupActCLM_mul`** — the exponentiated action:
  `exp (i θ T^a)`, written in closed form, is a unitary `2 × 2` element and gives a one-parameter
  group of bounded operators on the completion.  It is a group of invertible operators and *not* a
  unitary group: the fibre carries the sup norm, `fundMode` has no inner-product structure, and the
  fibre norm is not preserved (the operator constant is `2`, not `1`);
* **`coreNormSq_tendsto`**, **`gap_closed_in_coreLp`**, **`root_spectral_gap_closed`**,
  **`root_ground_bound_closed`** — closedness of the bound: a lower bound `K‖·‖² ≤ q` survives an
  ℓ² limit whenever the form values converge, so the S2 gap and the certificate's ground threshold
  hold at the limit of a form-convergent root-domain sequence.  This needs no continuity of `q`, and
  it is closedness of the bound, not a Friedrichs extension;
* **`RootFormDomination`**, **`root_ground_bound`**, **`root_excited_bound`**,
  **`s2RootFormDomination`** — the domination certificate with `dom` required only on the root
  sector, which `RootModeIdentification` supplies;
* **`rootSector`**, **`RootModeIdentification`**, **`toRootModeIdentification`** — the
  identification restricted to the root sector (no vacuum component): every unrestricted one
  restricts, and this is the structure the abelian argument does not refute;
* **`vacuumCoeff_not_rootSector`**, **`root_sector_magnetic_pos`** — the obstruction is isolated at
  the vacuum: the `not_modeIdentification_abelian` witness lies outside the root sector, and on it
  every nonzero state has strictly positive `:N²:` weight (`magneticEnergyForm_ge_normSq`);
* **`magEnergy_ge_of_rootIdentification`** — the S2 barrier transfer needs only the root-sector
  identity, so the vacuum case is not needed for the analytic chain;
* **`ymHamiltonian_quadForm_ge_of_rootIdentification`**, **`s2_gap_constant_root`**,
  **`s2_excited_threshold_root`** — the S2 certificate carried onto the root sector: the shape
  inequality, the ratio `c₁/48`, and the usable threshold `(c₁ Δ_ref − quarticShift)/48` all hold
  with `RootModeIdentification` on exactly the sector where the identification can be true.
* **The root-sector half of the form expansion** is proved in the sibling modules rather than
  here: `YangMillsMagneticQuartic.rootCrossWeight`,
  `YangMillsMagneticQuartic.quarticDegreeForm_eq_magnetic_add_root` (the `:N²:` weight is the
  magnetic weight plus the cross weight `∑_{i≠j} nᵢ nⱼ`), and
  `YangMillsFieldStrength.hopWord_pair_offdiag` with `sum_offdiag_amp_sq` (the root pair hops with
  squared amplitude `nᵢ nⱼ + nⱼ`).  What remains of `ModeIdentification` is the passage from that
  one-pair amplitude to `∑_m ‖[A,A]_m ψ_n‖²`.
-/

section ModeIdentification

variable {d : ℕ}

open BookProof.ReferenceGap BookProof.YangMillsFormDomination
open BookProof.YangMillsEffectiveBarrier BookProof.YangMillsMagneticQuartic

/-- The monomial of a mode: the coordinate monomial `∏ i, X i ^ nᵢ`, i.e. the monomial with
exponent vector `n`. -/
def occMonomial (n : Fin d → ℕ) : MvPolynomial (Fin d) ℂ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm n) 1

/-- **Occupation is degree**: the total degree of the mode monomial is the total occupation
`∑ i, nᵢ`.  This is the identification of the model's multi-index with the field-space degree. -/
theorem totalDegree_occMonomial (n : Fin d → ℕ) :
    (occMonomial n).totalDegree = ∑ i, n i := by
  rw [occMonomial, MvPolynomial.totalDegree_monomial _ one_ne_zero, Finsupp.sum]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro i _ hi
  simpa using hi

/-- The index of the occupation multi-index `n` in the adapted basis `coreBasis e`. -/
def modeIndex (e : ℕ ≃ (Fin d →₀ ℕ)) (n : Fin d → ℕ) : ℕ :=
  e.symm (Finsupp.equivFunOnFinite.symm n)

/-- Distinct occupations give distinct basis indices. -/
theorem modeIndex_injective (e : ℕ ≃ (Fin d →₀ ℕ)) : Function.Injective (modeIndex e) := by
  intro n m h
  exact Finsupp.equivFunOnFinite.symm.injective (e.symm.injective h)

/-- The product-Hermite basis vector of a mode. -/
def modeVec (e : ℕ ≃ (Fin d →₀ ℕ)) : (Fin d → ℕ) → L2d d :=
  fun n => (coreBasis e) (modeIndex e n)

/-- The mode vectors are orthonormal, being a subfamily of the adapted basis. -/
theorem modeVec_orthonormal (e : ℕ ≃ (Fin d →₀ ℕ)) : Orthonormal ℂ (modeVec e) :=
  (coreBasis e).orthonormal.comp _ (modeIndex_injective e)

/-- **The coefficient model as a subspace of `L²(ℝᵈ)`**, through the adapted product-Hermite
basis. -/
def coeffToCore (e : ℕ ≃ (Fin d →₀ ℕ)) (c : CoreCoeff d) : L2d d :=
  ∑ n ∈ c.support, c n • modeVec e n

/-- **The embedding is an isometry**: `‖∑ n, c n ψ_n‖² = ∑ n, ‖c n‖²`. -/
theorem coeffToCore_norm_sq (e : ℕ ≃ (Fin d →₀ ℕ)) (c : CoreCoeff d) :
    ‖coeffToCore e c‖ ^ 2 = coreNormSq c := by
  have hv := modeVec_orthonormal (d := d) e
  have hinner := hv.inner_sum (v := modeVec e) (fun n => c n) (fun n => c n) c.support
  rw [coeffToCore]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (x := ∑ n ∈ c.support, c n • modeVec e n)]
  rw [hinner, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RCLike.conj_mul]
  exact RCLike.re_ofReal_pow (‖c n‖) 2

/-! ### 3d.0 The `L²(ℝ²⁴) → L²(ℝ⁹⁹)` embedding

The identification `ModeIdentification.toCore` has to land in `D ≤ L²(ℝ⁹⁹)`, but the coefficient
model's adapted basis lives in `L²(ℝ²⁴)`.  The bridge is the distinguished injection of the `24`
gauge coordinates into the `99` coordinates: put the occupation of mode `m` on the coordinate
`A_{j,a}` with `m ↦ (j, a)`, and zero elsewhere.  Read in the adapted Hermite basis of
`L²(ℝ⁹⁹)` this is an *orthonormal family*, so the embedding is an isometry with no Mehler analysis:
the norm identity is the orthonormality of `coreBasis e`, exactly as for `coeffToCore`. -/

/-- The distinguished injection of the `24` field/colour pairs into the `99` coordinates: the
coordinate of the gauge field `A_{j,a}` carried by the `m`-th pair. -/
def colourIndex (m : Fin 24) : Fin 99 := idxA (decodeSpace m) (decodeColor m)

/-- The distinguished injection is injective: the pair `(j, a)` is recovered from the coordinate,
and the coordinate determines the division and remainder by `8`. -/
theorem colourIndex_injective : Function.Injective colourIndex := by
  intro m n h
  have h2 : (decodeSpace m, decodeColor m) = (decodeSpace n, decodeColor n) :=
    idxA_injective (a₁ := (decodeSpace m, decodeColor m))
      (a₂ := (decodeSpace n, decodeColor n)) h
  obtain ⟨hsp, hco⟩ := Prod.mk.inj h2
  have hs : m.val / 8 = n.val / 8 := congrArg Fin.val hsp
  have hc : m.val % 8 = n.val % 8 := congrArg Fin.val hco
  have hm := Nat.div_add_mod m.val 8
  have hn := Nat.div_add_mod n.val 8
  apply Fin.ext
  omega

/-- The index in `L²(ℝ⁹⁹)`'s adapted basis of the mode `n` of the `24`-component model, with the
occupation on the distinguished gauge coordinates and zero elsewhere. -/
noncomputable def embedIndex (e : ℕ ≃ (Fin 99 →₀ ℕ)) (n : Fin 24 → ℕ) : ℕ :=
  e.symm (Finsupp.mapDomain colourIndex (Finsupp.equivFunOnFinite.symm n))

/-- Distinct occupations give distinct `ℝ⁹⁹` basis indices: `mapDomain` is injective along the
distinguished injection, and the two equivalences are bijections. -/
theorem embedIndex_injective (e : ℕ ≃ (Fin 99 →₀ ℕ)) :
    Function.Injective (embedIndex e) := by
  intro n m h
  have h' : Finsupp.mapDomain colourIndex (Finsupp.equivFunOnFinite.symm n)
      = Finsupp.mapDomain colourIndex (Finsupp.equivFunOnFinite.symm m) :=
    e.symm.injective h
  exact Finsupp.equivFunOnFinite.symm.injective
    (Finsupp.mapDomain_injective colourIndex_injective h')

/-- The mode vector of the `24`-component model, read as a vector of `L²(ℝ⁹⁹)` through the
distinguished gauge coordinates. -/
noncomputable def modeVec99 (e : ℕ ≃ (Fin 99 →₀ ℕ)) (n : Fin 24 → ℕ) : L2d 99 :=
  (coreBasis e) (embedIndex e n)

/-- The embedded mode vectors are orthonormal, being a subfamily of the adapted `ℝ⁹⁹` basis. -/
theorem modeVec99_orthonormal (e : ℕ ≃ (Fin 99 →₀ ℕ)) :
    Orthonormal ℂ (modeVec99 e) :=
  (coreBasis e).orthonormal.comp _ (embedIndex_injective e)

/-- **The `L²(ℝ²⁴) → L²(ℝ⁹⁹)` embedding**: the coefficient model read through the distinguished
gauge coordinates.  This is the concrete candidate for `ModeIdentification.toCore`. -/
noncomputable def embedL2 (e : ℕ ≃ (Fin 99 →₀ ℕ)) (c : CoreCoeff 24) : L2d 99 :=
  ∑ n ∈ c.support, c n • modeVec99 e n

/-- **The embedding is an isometry**: `‖embedL2 e c‖² = ∑ n, ‖c n‖² = coreNormSq c`.  Only
orthonormality of the adapted basis is used — no Mehler kernel and no Gaussian integral. -/
theorem embedL2_norm_sq (e : ℕ ≃ (Fin 99 →₀ ℕ)) (c : CoreCoeff 24) :
    ‖embedL2 e c‖ ^ 2 = coreNormSq c := by
  have hv := modeVec99_orthonormal e
  have hinner := hv.inner_sum (v := modeVec99 e) (fun n => c n) (fun n => c n) c.support
  rw [embedL2]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (x := ∑ n ∈ c.support, c n • modeVec99 e n)]
  rw [hinner, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RCLike.conj_mul]
  exact RCLike.re_ofReal_pow (‖c n‖) 2

/-- **The embedding lands on the Gauss–polynomial core**: a finite combination of adapted basis
vectors is in the finite-mode domain, which is `polyGaussCore`. -/
theorem embedL2_mem_polyGaussCore (e : ℕ ≃ (Fin 99 →₀ ℕ)) (c : CoreCoeff 24) :
    embedL2 e c ∈ polyGaussCore (d := 99) := by
  rw [← finiteModeDomain_coreBasis e]
  rw [embedL2, finiteModeDomain]
  refine Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨embedIndex e n, rfl⟩

/-- **The concrete `toCore` candidate**, on the Gauss–polynomial core of `L²(ℝ⁹⁹)`: the coefficient
model read through the distinguished gauge coordinates.  Its `norm_sq` field is `embedCore_norm_sq`;
what remains of `RootModeIdentification` is `mag_eq_root` only. -/
noncomputable def embedCore (e : ℕ ≃ (Fin 99 →₀ ℕ)) (c : CoreCoeff 24) :
    polyGaussCore (d := 99) :=
  ⟨embedL2 e c, embedL2_mem_polyGaussCore e c⟩

/-- **The `norm_sq` field of the root-sector identification**, discharged for the concrete
candidate: `‖embedCore e c‖² = coreNormSq c`. -/
theorem embedCore_norm_sq (e : ℕ ≃ (Fin 99 →₀ ℕ)) (c : CoreCoeff 24) :
    ‖(((embedCore e c : polyGaussCore (d := 99)) : L2d 99))‖ ^ 2 = coreNormSq c :=
  embedL2_norm_sq e c

/-- **The quartic `:N²:` form is not relatively bounded by the degree form.**  For every `κ` and
`b` there is a core coefficient with `quarticDegreeForm c > κ · degreeForm c + b · ‖c‖²`: taking a
single mode of occupation `N` gives `(dN)² > κ (dN) + b` for `N` large.  So the §3c hypothesis
cannot be discharged on this core, and the coercivity of the magnetic form has to come from the
barrier inequality (`barrierBound_quartic`), not from a relative bound in this direction. -/
theorem not_quartic_relativeBound {d : ℕ} (hd : 0 < d) (κ b : ℝ) :
    ¬ ∀ c : CoreCoeff d, quarticDegreeForm c ≤ κ * degreeForm c + b * coreNormSq c := by
  intro h
  set M : ℝ := |κ| + |b| + 2 with hM
  have hM2 : (2 : ℝ) ≤ M := by
    have h1 : (0 : ℝ) ≤ |κ| := abs_nonneg κ
    have h2 : (0 : ℝ) ≤ |b| := abs_nonneg b
    rw [hM]
    linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨N, hN⟩ := exists_nat_gt (M / (d : ℝ))
  set s : ℝ := (d : ℝ) * N with hs
  have hMs : M < s := by
    have hpos : (d : ℝ) * (M / (d : ℝ)) < (d : ℝ) * N :=
      mul_lt_mul_of_pos_left hN hdR
    rw [mul_div_cancel₀ M (ne_of_gt hdR)] at hpos
    exact hpos
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  set n₀ : Fin d → ℕ := fun _ => N with hn₀
  set c : CoreCoeff d := Finsupp.single n₀ (1 : ℂ) with hc
  have hsupp : c.support = {n₀} := by
    rw [hc, Finsupp.support_single_ne_zero _ one_ne_zero]
  have hdeg : (∑ i : Fin d, ((n₀ i : ℕ) : ℝ)) = s := by
    rw [hn₀, hs]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hc_one : c n₀ = 1 := by
    rw [hc]
    exact Finsupp.single_eq_same
  have hq : quarticDegreeForm c = s ^ 2 := by
    rw [quarticDegreeForm, hsupp, Finset.sum_singleton, hdeg, hc_one, norm_one]
    ring
  have hdform : degreeForm c = s := by
    rw [degreeForm, hsupp, Finset.sum_singleton, hdeg, hc_one, norm_one]
    ring
  have hnorm : coreNormSq c = 1 := by
    rw [coreNormSq, hsupp, Finset.sum_singleton, hc_one, norm_one]
    norm_num
  have hbound := h c
  rw [hq, hdform, hnorm] at hbound
  have hk : κ * s ≤ |κ| * s := mul_le_mul_of_nonneg_right (le_abs_self κ) (le_of_lt hs0)
  have hb : b ≤ |b| := le_abs_self b
  have hbs : |b| ≤ |b| * s := by nlinarith [abs_nonneg b]
  have hMs' : M * s ≤ s * s := mul_le_mul_of_nonneg_right (le_of_lt hMs) (le_of_lt hs0)
  have hsum : (|κ| + |b|) * s ≤ s * s - 2 * s := by
    have : M * s = (|κ| + |b|) * s + 2 * s := by rw [hM]; ring
    linarith
  nlinarith [hbound, hk, hb, hbs, hsum, hs0]

/-- **The mode identification.**  An isometric map of coefficient vectors into the core whose
magnetic-energy form is the coefficient model's `magneticEnergyForm diagA`.  The isometry half is
proved by `coeffToCore_norm_sq`; the form half is the mode-expansion step (occupation ↔ field
amplitude), which is the content this structure isolates. -/
structure ModeIdentification (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) where
  /-- the identification of coefficient vectors with core vectors. -/
  toCore : CoreCoeff 24 → D
  /-- it is an isometry for the two norms. -/
  norm_sq : ∀ c : CoreCoeff 24, ‖((toCore c : D) : L2d 99)‖ ^ 2 = coreNormSq c
  /-- the core's magnetic energy is the coefficient model's magnetic form. -/
  mag_eq : ∀ c : CoreCoeff 24,
    (∑ m : Fin 24, ‖(((magOps Φ fabc m) (toCore c) : D) : L2d 99)‖ ^ 2)
      = magneticEnergyForm (d := 24) diagA c

/-- **Coercivity of the core's magnetic form, transferred from the barrier bound.**  The model's
quartic `:N²:` form dominates the degree form plus Simon's barrier up to `quarticShift`, and the
canonical-background magnetic form is at least a `1/24` fraction of that quartic form, so
`Σ‖Bx‖² ≥ (degreeForm + barrierForm − shift ‖x‖²)/24`.  No relative-bound hypothesis is used. -/
theorem magEnergy_ge_of_identification (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (MI : ModeIdentification Φ fabc)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff 24) :
    1 / 24 * (degreeForm c + barrierForm T g c - quarticShift (d := 24) T g * coreNormSq c)
      ≤ ∑ m : Fin 24, ‖(((magOps Φ fabc m) (MI.toCore c) : D) : L2d 99)‖ ^ 2 := by
  rw [MI.mag_eq c]
  have hquart := quarticDegreeForm_le_magnetic (d := 24) c
  have hbar := (barrierBound_quartic (d := 24) T hg).bound c
  have hsh : (barrierBound_quartic (d := 24) T hg).shift = quarticShift (d := 24) T g := rfl
  rw [hsh] at hbar
  have hstep : 1 / 24 * (degreeForm c + barrierForm T g c
      - quarticShift (d := 24) T g * coreNormSq c) ≤ 1 / 24 * quarticDegreeForm c :=
    mul_le_mul_of_nonneg_left hbar (by norm_num)
  have hq24 : 1 / 24 * quarticDegreeForm c ≤ magneticEnergyForm (d := 24) diagA c := by
    have h1 := mul_le_mul_of_nonneg_left hquart (by norm_num : (0 : ℝ) ≤ 1 / 24)
    calc 1 / 24 * quarticDegreeForm c
        ≤ 1 / 24 * (24 * magneticEnergyForm (d := 24) diagA c) := h1
      _ = magneticEnergyForm (d := 24) diagA c := by ring
  exact hstep.trans hq24

/-- **The S2 shape on the core, unconditionally in the interaction**: the Hamiltonian's form is at
least `(1/48)(degreeForm + barrierForm − shift ‖x‖²)`, because the kinetic square is nonnegative
and the magnetic square is at least the transferred bound of
`magEnergy_ge_of_identification`. -/
theorem ymHamiltonian_quadForm_ge_of_identification (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (MI : ModeIdentification Φ fabc)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff 24) :
    1 / 48 * (degreeForm c + barrierForm T g c - quarticShift (d := 24) T g * coreNormSq c)
      ≤ quadForm (ymHamiltonian Φ fabc) (MI.toCore c) := by
  rw [ymHamiltonian_quadForm_split]
  have hmag := magEnergy_ge_of_identification Φ fabc MI (T := T) (g := g) hg c
  have heq := magEnergy_form_eq Φ fabc (MI.toCore c)
  have hpi : (0 : ℝ) ≤ ∑ m : Fin 24, ‖(((piOps Φ m) (MI.toCore c) : D) : L2d 99)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **The S2 gap constant**: on the identified core the form dominates the reference oscillator
form with the explicit ratio `c₁/48` and the explicit shift
`(c₁ μ₀ + quarticShift)/48`.  The constant is `1/48 = 1/(2 · 24)` for `c₁ = 1`: the factor `2` is
the kinetic-plus-magnetic split of `H₁`, the `24` the Cauchy–Schwarz count of the field
components. -/
theorem s2_gap_constant (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ} {T : Finset (Fin 24)} {g : ℝ}
    (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24) :
    c₁ / 48 * coreForm ω c
        - ((c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (MI.toCore c) := by
  have hdom := (freeFormDomination (d := 24) ω hc₁ hω₁).dom c
  have hdom' : c₁ * coreForm ω c - c₁ * refEnergy ω 0 * coreNormSq c ≤ degreeForm c := by
    simpa using hdom
  have hbase := ymHamiltonian_quadForm_ge_of_identification Φ fabc MI (T := T) (g := g) hg c
  have hbar := barrierForm_nonneg hg T c
  linarith

/-! ### 3d.1 The abelian sector does **not** inhabit the identification

`ModeIdentification` demands the core's magnetic energy equal the normal-ordered `:N²:` form, which
vanishes on the vacuum.  On the abelian sector (`fabc = 0`) the magnetic polynomial is the linear
`∂A` slot `∑ j k, levi i j k • X (idxD j k a)`, whose vacuum matrix element is **not** zero.  So the
abelian sector is a counterexample, not an inhabitant: the constant it carries is precisely the
normal-ordering constant that the `:N²:` weight has already dropped
(`YangMillsMagneticQuartic.quartic_eq_magnetic_add_cross`).  Its value is `1/2` per field
component, and `0` for the normal-ordered form on the same state
(`YangMillsFieldStrength.abelian_vacuum_energy`,
`YangMillsMagneticQuartic.magneticEnergyForm_vacuum`). -/

/-- Multiplication by a nonzero polynomial is injective, `MvPolynomial` being a domain. -/
theorem mulOp_eq_zero_imp {p : MvPolynomial (Fin 99) ℂ} (hp : p ≠ 0)
    {q : MvPolynomial (Fin 99) ℂ} (h : mulOp p q = 0) : q = 0 := by
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hp
  · exact h0

/-- The abelian magnetic polynomial is nonzero: the term `levi 0 1 2 • X (idxD 1 2 0)` has
coefficient one, evaluated at the point that is `1` on the coordinate `idxD 1 2 0`. -/
theorem magPoly_zero_ne : magPoly (fun _ _ _ => (0 : ℝ)) 0 0 ≠ 0 := by
  intro h
  have hev := congrArg
    (MvPolynomial.eval (fun s : Fin 99 => if s = idxD 1 2 0 then (1 : ℂ) else 0)) h
  simp only [map_zero] at hev
  rw [magPoly] at hev
  simp only [Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, add_zero, map_sum] at hev
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at hev
  norm_num [idxD, levi] at hev

/-- The `0`-th magnetic operator on the abelian sector is injective: its polynomial is nonzero,
and the core rep is an isomorphism. -/
theorem magOps_abelian_injective (Φ : CoreRep 99 D) {x : D}
    (hx : magOps Φ (fun _ _ _ => (0 : ℝ)) ⟨0, by omega⟩ x = 0) : x = 0 := by
  have hx' : Φ.op (mulOp (magPoly (fun _ _ _ => (0 : ℝ)) 0 0)) x = 0 := by
    simpa [magOps, decodeSpace, decodeColor] using hx
  have h1 : mulOp (magPoly (fun _ _ _ => (0 : ℝ)) 0 0) (Φ.equiv.symm x) = 0 := by
    have := congrArg Φ.equiv.symm hx'
    simpa [CoreRep.op_apply] using this
  have h2 : Φ.equiv.symm x = 0 := mulOp_eq_zero_imp magPoly_zero_ne h1
  exact Φ.equiv.symm.injective (by simpa using h2)

/-- **The abelian sector does not inhabit `ModeIdentification`.**  The `:N²:` magnetic form
vanishes at the vacuum while the abelian magnetic operator is injective there, so the form
identity of `ModeIdentification` fails already on the vacuum vector: the abelian energy carries
the normal-ordering constant that the normal-ordered `:N²:` model has subtracted. -/
theorem not_modeIdentification_abelian (Φ : CoreRep 99 D) :
    ¬ Nonempty (ModeIdentification Φ (fun _ _ _ => (0 : ℝ))) := by
  rintro ⟨MI⟩
  set n₀ : Fin 24 → ℕ := fun _ => 0 with hn₀
  set c₀ : CoreCoeff 24 := Finsupp.single n₀ 1 with hc₀
  have hz : magneticEnergyForm (d := 24) diagA c₀ = 0 := by
    rw [magneticEnergyForm, hc₀, Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.sum_singleton]
    simp [magComp, hn₀]
  have hmag := MI.mag_eq c₀
  rw [hz] at hmag
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ =>
    sq_nonneg (‖(((magOps Φ (fun _ _ _ => (0 : ℝ)) m) (MI.toCore c₀) : D) : L2d 99)‖))).mp hmag
  have hnorm : ‖((MI.toCore c₀ : D) : L2d 99)‖ ^ 2 = 1 := by
    rw [MI.norm_sq, coreNormSq, hc₀, Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.sum_singleton]
    norm_num
  have hx : MI.toCore c₀ ≠ 0 := by
    intro h
    rw [h] at hnorm
    simp at hnorm
  have hm := hterm ⟨0, by omega⟩ (Finset.mem_univ _)
  have hnorm0 : ‖(((magOps Φ (fun _ _ _ => (0 : ℝ)) ⟨0, by omega⟩) (MI.toCore c₀) : D) :
      L2d 99)‖ = 0 := by
    simpa using (sq_eq_zero_iff.mp hm)
  have hzero : magOps Φ (fun _ _ _ => (0 : ℝ)) ⟨0, by omega⟩ (MI.toCore c₀) = 0 :=
    Subtype.ext (by simpa using hnorm0)
  exact hx (magOps_abelian_injective Φ hzero)

/-! ### 3d.2 The S2 constant as a `FormDomination` certificate -/

/-- **The S2 gap constant is a `FormDomination` certificate on the identified core.**  The
Hamiltonian's form dominates the reference oscillator form with ratio `c₁/48` and shift
`(c₁ μ₀ + quarticShift)/48`, so the whole certificate machinery of
`BookProof.YangMillsFormDomination` — `ground_bound`, `excited_bound`, `certified_separation`,
`certified_gap_pos` — applies verbatim to the Yang–Mills form. -/
def s2FormDomination (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ} {T : Finset (Fin 24)} {g : ℝ}
    (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    FormDomination ω (fun c => quadForm (ymHamiltonian Φ fabc) (MI.toCore c)) where
  c₁ := c₁ / 48
  c₂ := (c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48
  hc₁ := by positivity
  dom := fun c => s2_gap_constant Φ fabc MI hg hc₁ hω₁ c

/-- **The certified ground threshold.**  Whole-core, the S2 certificate says the Yang–Mills form
is bounded below by `−(quarticShift / 48) ‖x‖²`: the barrier's shift is the price of the
normal-ordering constant, and no positive threshold is claimed on the whole core. -/
theorem s2_ground_threshold (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24) :
    -(quarticShift (d := 24) T g / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (MI.toCore c) := by
  have h := ground_bound (d := 24) ω hω
    (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁) c
  simp only [s2FormDomination] at h
  have hc : c₁ / 48 * refEnergy ω 0 - (c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48
      = -(quarticShift (d := 24) T g / 48) := by ring
  rwa [hc] at h

/-- **The certified excitation threshold.**  On the vacuum-orthogonal sector the certificate pays
for the reference gap: the Yang–Mills form is bounded below by
`(c₁ Δ_ref − quarticShift)/48 · ‖x‖²`.  This is the S2 number in its usable form — the shift is
what remains of the normal-ordering constant after the `:N²:` model has dropped it. -/
theorem s2_excited_threshold (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24) (hc : c 0 = 0) :
    ((c₁ * refGap ω - quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (MI.toCore c) := by
  have h := excited_bound (d := 24) ω hω
    (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁) c hc
  simp only [s2FormDomination] at h
  have hc' : c₁ / 48 * (refEnergy ω 0 + refGap ω)
      - (c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48
      = (c₁ * refGap ω - quarticShift (d := 24) T g) / 48 := by ring
  rwa [hc'] at h

/-! ### 3d.3 The root-sector structure, with the obstruction isolated

§3d.1 shows that the abelian sector cannot inhabit `ModeIdentification`, and the witness it uses is
the *vacuum* coefficient.  The quantitative form of that witness is the `1/2` per component of
`YangMillsFieldStrength.abelian_vacuum_energy`, and the complementary fact is
`magneticEnergyForm_ge_normSq`: off the vacuum the `:N²:` weight pays for the norm itself.  So the
honest structure is the identification *restricted to the root sector* — no vacuum component —
which is exactly `ModeIdentification` minus the state where the abelian defect lives. -/

/-- The **root sector** of the coefficient model: no vacuum component. -/
def rootSector (c : CoreCoeff 24) : Prop := c 0 = 0

/-- **The mode identification off the vacuum.**  Same data as `ModeIdentification`, but the form
identity is required only on the root sector.  This is the structure the abelian argument does *not*
refute, and it is where the non-abelian identification has to be built
(`root_sector_magnetic_pos`: the `:N²:` weight is strictly positive on every nonzero root-sector
state, so the obstruction — a state with vanishing weight — has no root-sector instance). -/
structure RootModeIdentification (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) where
  /-- the identification of coefficient vectors with core vectors. -/
  toCore : CoreCoeff 24 → D
  /-- it is an isometry for the two norms. -/
  norm_sq : ∀ c : CoreCoeff 24, ‖((toCore c : D) : L2d 99)‖ ^ 2 = coreNormSq c
  /-- the form identity, on the root sector only. -/
  mag_eq_root : ∀ c : CoreCoeff 24, rootSector c →
    (∑ m : Fin 24, ‖(((magOps Φ fabc m) (toCore c) : D) : L2d 99)‖ ^ 2)
      = magneticEnergyForm (d := 24) diagA c

/-- Every unrestricted identification restricts to the root sector. -/
def toRootModeIdentification (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) : RootModeIdentification Φ fabc where
  toCore := MI.toCore
  norm_sq := MI.norm_sq
  mag_eq_root := fun c _ => MI.mag_eq c

/-- **The abelian witness is outside the root sector**: the vacuum coefficient has component `1`,
so the state where `not_modeIdentification_abelian` bites is not available to the restricted
structure. -/
theorem vacuumCoeff_not_rootSector : ¬ rootSector (vacuumCoeff 24) := by
  intro h
  have h1 : vacuumCoeff 24 (fun _ => (0 : ℕ)) = 1 := vacuumCoeff_zero
  have h2 : vacuumCoeff 24 (fun _ => (0 : ℕ)) = 0 := h
  rw [h1] at h2
  norm_num at h2

/-- **No obstruction on the root sector**: every nonzero root-sector state has a strictly positive
`:N²:` weight, so no state there can be the `not_modeIdentification_abelian` witness. -/
theorem root_sector_magnetic_pos (c : CoreCoeff 24) (hc : c ≠ 0) (h : rootSector c) :
    0 < magneticEnergyForm (d := 24) diagA c :=
  magneticEnergyForm_pos_of_root hc h

/-- **The S2 transfer only needs the root-sector identification.**  The barrier bound
(`magEnergy_ge_of_identification`) is applied to a single `c`; restricting `mag_eq` to the root
sector therefore costs nothing on that sector: on every root-sector coefficient the core's magnetic
energy is at least `(degreeForm + barrierForm − shift ‖·‖²)/24`.  So the vacuum case is not needed
for S2 — it is needed only to state the identification globally. -/
theorem magEnergy_ge_of_rootIdentification (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (RI : RootModeIdentification Φ fabc)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff 24) (hc : rootSector c) :
    1 / 24 * (degreeForm c + barrierForm T g c - quarticShift (d := 24) T g * coreNormSq c)
      ≤ ∑ m : Fin 24, ‖(((magOps Φ fabc m) (RI.toCore c) : D) : L2d 99)‖ ^ 2 := by
  rw [RI.mag_eq_root c hc]
  have hquart := quarticDegreeForm_le_magnetic (d := 24) c
  have hbar := (barrierBound_quartic (d := 24) T hg).bound c
  have hsh : (barrierBound_quartic (d := 24) T hg).shift = quarticShift (d := 24) T g := rfl
  rw [hsh] at hbar
  have hstep : 1 / 24 * (degreeForm c + barrierForm T g c
      - quarticShift (d := 24) T g * coreNormSq c) ≤ 1 / 24 * quarticDegreeForm c :=
    mul_le_mul_of_nonneg_left hbar (by norm_num)
  have hq24 : 1 / 24 * quarticDegreeForm c ≤ magneticEnergyForm (d := 24) diagA c := by
    have h1 := mul_le_mul_of_nonneg_left hquart (by norm_num : (0 : ℝ) ≤ 1 / 24)
    calc 1 / 24 * quarticDegreeForm c
        ≤ 1 / 24 * (24 * magneticEnergyForm (d := 24) diagA c) := h1
      _ = magneticEnergyForm (d := 24) diagA c := by ring
  exact hstep.trans hq24

/-- **The S2 shape on the core, on the root sector, with the weaker structure.**  Same as
`ymHamiltonian_quadForm_ge_of_identification`, but using only `mag_eq_root`, so it holds for every
root-sector coefficient (`c 0 = 0`).  The vacuum case is not needed for the shape inequality. -/
theorem ymHamiltonian_quadForm_ge_of_rootIdentification (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (RI : RootModeIdentification Φ fabc)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff 24) (hc : rootSector c) :
    1 / 48 * (degreeForm c + barrierForm T g c - quarticShift (d := 24) T g * coreNormSq c)
      ≤ quadForm (ymHamiltonian Φ fabc) (RI.toCore c) := by
  rw [ymHamiltonian_quadForm_split]
  have hmag := magEnergy_ge_of_rootIdentification Φ fabc RI (T := T) (g := g) hg c hc
  have heq := magEnergy_form_eq Φ fabc (RI.toCore c)
  have hpi : (0 : ℝ) ≤ ∑ m : Fin 24, ‖(((piOps Φ m) (RI.toCore c) : D) : L2d 99)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **The S2 gap constant on the root sector.**  The root-sector analogue of `s2_gap_constant`:
the same ratio `c₁/48` and shift `(c₁ μ₀ + quarticShift)/48`, valid for every root-sector
coefficient. -/
theorem s2_gap_constant_root (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (RI : RootModeIdentification Φ fabc) {ω : Fin 24 → ℝ} {T : Finset (Fin 24)} {g : ℝ}
    (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24)
    (hc : rootSector c) :
    c₁ / 48 * coreForm ω c
        - ((c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (RI.toCore c) := by
  have hdom := (freeFormDomination (d := 24) ω hc₁ hω₁).dom c
  have hdom' : c₁ * coreForm ω c - c₁ * refEnergy ω 0 * coreNormSq c ≤ degreeForm c := by
    simpa using hdom
  have hbase := ymHamiltonian_quadForm_ge_of_rootIdentification Φ fabc RI (T := T) (g := g) hg c hc
  have hbar := barrierForm_nonneg hg T c
  linarith

/-- **The certified excitation threshold on the root sector.**  The usable S2 number: on the
root sector the Yang–Mills form is at least `(c₁ Δ_ref − quarticShift)/48 · ‖x‖²`.  This is the
analogue of `s2_excited_threshold` with the weaker `RootModeIdentification`, and it is exactly the
sector where the identification can hold. -/
theorem s2_excited_threshold_root (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (RI : RootModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24) (hc : rootSector c) :
    ((c₁ * refGap ω - quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (RI.toCore c) := by
  have hgap := href_spectral_gap (d := 24) ω hω c hc
  have hconst := s2_gap_constant_root Φ fabc RI (ω := ω) (T := T) (g := g) hg hc₁ hω₁ c hc
  have hc₁' : (0 : ℝ) ≤ c₁ / 48 := by positivity
  have h1 : (c₁ / 48) * ((refEnergy ω 0 + refGap ω) * coreNormSq c)
      ≤ (c₁ / 48) * coreForm ω c :=
    mul_le_mul_of_nonneg_left hgap hc₁'
  have h2 : (c₁ / 48) * coreForm ω c
      - ((c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (RI.toCore c) := hconst
  have h3 : (c₁ / 48) * ((refEnergy ω 0 + refGap ω) * coreNormSq c)
        - ((c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48) * coreNormSq c
      = ((c₁ * refGap ω - quarticShift (d := 24) T g) / 48) * coreNormSq c := by ring
  linarith [h1, h2, h3]

/-- **A restricted-form domination certificate.**  `FormDomination` quantified over the whole core;
this one requires the domination inequality only on the root sector, which is exactly what
`RootModeIdentification` can supply.  It is a different object, not a weakening: the `dom` field is
the statement actually needed for the sector's spectral bound. -/
structure RootFormDomination (ω : Fin 24 → ℝ) (q : CoreCoeff 24 → ℝ) where
  /-- the domination ratio. -/
  c₁ : ℝ
  /-- the additive shift. -/
  c₂ : ℝ
  /-- the ratio is positive. -/
  hc₁ : 0 < c₁
  /-- the domination inequality, on the root sector only. -/
  dom : ∀ c : CoreCoeff 24, rootSector c → c₁ * coreForm ω c - c₂ * coreNormSq c ≤ q c

/-- **The restricted ground bound**: the whole-core `ground_bound` restricted to the root sector. -/
theorem root_ground_bound (ω : Fin 24 → ℝ) (hω : ∀ i, 0 < ω i)
    {q : CoreCoeff 24 → ℝ} (D : RootFormDomination ω q) (c : CoreCoeff 24)
    (hc : rootSector c) :
    (D.c₁ * refEnergy ω 0 - D.c₂) * coreNormSq c ≤ q c := by
  have h1 : D.c₁ * (refEnergy ω 0 * coreNormSq c) ≤ D.c₁ * coreForm ω c :=
    mul_le_mul_of_nonneg_left (coreForm_ge_vacuum ω hω c) D.hc₁.le
  have h2 := D.dom c hc
  nlinarith

/-- **The restricted excited bound**: the `excited_bound` of the whole-core certificate, now on
the root sector, where `href_spectral_gap` applies. -/
theorem root_excited_bound (ω : Fin 24 → ℝ) (hω : ∀ i, 0 < ω i)
    {q : CoreCoeff 24 → ℝ} (D : RootFormDomination ω q) (c : CoreCoeff 24)
    (hc : rootSector c) :
    (D.c₁ * (refEnergy ω 0 + refGap ω) - D.c₂) * coreNormSq c ≤ q c := by
  have h1 : D.c₁ * ((refEnergy ω 0 + refGap ω) * coreNormSq c) ≤ D.c₁ * coreForm ω c :=
    mul_le_mul_of_nonneg_left (href_spectral_gap ω hω c hc) D.hc₁.le
  have h2 := D.dom c hc
  nlinarith

/-- **The S2 certificate as a restricted-form domination**, built from the root-sector gap
constant: ratio `c₁/48`, shift `(c₁ μ₀ + quarticShift)/48`, on the root sector. -/
noncomputable def s2RootFormDomination (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (RI : RootModeIdentification Φ fabc) {ω : Fin 24 → ℝ} {T : Finset (Fin 24)} {g : ℝ}
    (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    RootFormDomination ω (fun c => quadForm (ymHamiltonian Φ fabc) (RI.toCore c)) where
  c₁ := c₁ / 48
  c₂ := (c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48
  hc₁ := by positivity
  dom := fun c hc => s2_gap_constant_root Φ fabc RI (T := T) (g := g) hg hc₁ hω₁ c hc

/-! #### The root-sector spectral gap on its domain

`RootFormDomination` lives on the root sector, which is the kernel of evaluation at the vacuum
multi-index — a submodule, hence a legitimate form domain, and one that already excludes the vacuum.
On it the *excited* threshold applies to every element, so the certificate gives a genuine positive
lower bound rather than a threshold that can be spoilt by the vacuum. -/

/-- The **root domain**: the root sector as a submodule, the kernel of evaluation at the vacuum
occupation.  Since `rootSector` is a linear condition, no separate closure of the sector is needed:
the S2 comparison is an inequality between continuous quadratic forms and holds pointwise on this
submodule. -/
def rootDomain : Submodule ℂ (CoreCoeff 24) := LinearMap.ker (Finsupp.lapply 0)

/-- Membership in the root domain is exactly the root-sector condition. -/
theorem mem_rootDomain {c : CoreCoeff 24} : c ∈ rootDomain ↔ rootSector c := Iff.rfl

/-- The root domain is not the whole core: the vacuum is outside it. -/
theorem rootDomain_ne_top : rootDomain ≠ ⊤ := by
  intro h
  have hmem : BookProof.YangMillsMagneticQuartic.vacuumCoeff 24 ∈ rootDomain := by
    rw [h]
    trivial
  exact vacuumCoeff_not_rootSector ((mem_rootDomain).mp hmem)

/-- **The root-sector spectral gap.**  On the root domain the S2 certificate's *excited* threshold
applies to every element, since no element there has a vacuum component.  Hence the form is bounded
below by `(c₁ Δ_ref − quarticShift)/48 · ‖c‖²` — a genuine gap above the reference vacuum, unlike
the whole-core threshold `s2_ground_threshold`, which the vacuum spoils.  This is the usable form of
`s2RootFormDomination`: the certificate together with its domain. -/
theorem root_spectral_gap (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (RI : RootModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24) (hdom : c ∈ rootDomain) :
    ((c₁ * refGap ω - quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (RI.toCore c) := by
  have h := root_excited_bound ω hω
    (s2RootFormDomination Φ fabc RI (T := T) (g := g) hg hc₁ hω₁) c
    ((mem_rootDomain).mp hdom)
  simp only [s2RootFormDomination] at h
  have hc' : c₁ / 48 * (refEnergy ω 0 + refGap ω)
      - (c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48
      = (c₁ * refGap ω - quarticShift (d := 24) T g) / 48 := by ring
  rwa [hc'] at h

/-! #### The root domain is the excited span, and the gap passes to its closure

`rootDomain` is the kernel of evaluation at the vacuum.  In the coefficient model this is exactly
the vacuum-orthogonal core: the standard expansion of a finitely supported family shows that a core
vector has no vacuum component if and only if it is a finite combination of the *excited* occupation
basis vectors (`rootDomain_eq_span_excited`).  Density is therefore algebraic, not analytic: the
excited span **is** the vacuum-orthogonal core, and the only closedness statement available in this
model is closedness under `coreNormSq` limits (`rootDomain_closed_of_tendsto`,
`closure_rootDomain_iff`).  Since that closure is the domain itself, the root-sector gap holds on it
verbatim (`root_spectral_gap_on_closure`); no limiting argument on the quartic form is used, and
none would be available — `quadForm (ymHamiltonian …)` is not known to be continuous in
`coreNormSq`.
-/

/-- **The vacuum coefficient is bounded by the core norm**: `‖c 0‖² ≤ coreNormSq c`, because
`coreNormSq` is the sum of the squared moduli **including** the vacuum summand.  This is the only
continuity the vacuum coefficient has in the coefficient model. -/
theorem norm_sq_apply_zero_le_coreNormSq (c : CoreCoeff 24) :
    ‖c 0‖ ^ 2 ≤ coreNormSq c := by
  rw [coreNormSq]
  by_cases h : (0 : Fin 24 → ℕ) ∈ c.support
  · exact Finset.single_le_sum (f := fun n => ‖c n‖ ^ 2) (fun i _ => by positivity) h
  · have hz : c 0 = 0 := Finsupp.notMem_support_iff.mp h
    rw [hz, norm_zero, zero_pow (by norm_num)]
    exact Finset.sum_nonneg fun i _ => by positivity

/-- **The root domain is the span of the excited basis.**  A core vector with no vacuum component is
a finite linear combination of the occupation basis vectors other than the vacuum: the support
cannot contain `0`, so every term of the standard expansion
`c = ∑_{n ∈ support} c n • single n 1` is an excited basis vector.  This is the algebraic form of
"the root domain is the vacuum-orthogonal core": it is exactly the span of the states orthogonal to
the vacuum. -/
theorem rootDomain_eq_span_excited :
    rootDomain = Submodule.span ℂ (Set.range (fun p : {n : Fin 24 → ℕ // n ≠ 0} =>
      (Finsupp.single p.1 (1 : ℂ) : CoreCoeff 24))) := by
  refine le_antisymm ?_ ?_
  · intro c hc
    have hc0 : c 0 = 0 := hc
    have hdecomp : (∑ n ∈ c.support, c n • (Finsupp.single n (1 : ℂ) : CoreCoeff 24)) = c := by
      ext m
      rw [Finsupp.finset_sum_apply]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      have e1 : (∑ n ∈ c.support, c n * (if n = m then (1 : ℂ) else 0))
          = ∑ n ∈ c.support, (if n = m then c n else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hnm : n = m <;> simp [hnm]
      rw [e1, Finset.sum_ite_eq']
      by_cases hm : m ∈ c.support
      · simp [hm]
      · simp [hm, (Finsupp.notMem_support_iff.mp hm)]
    rw [← hdecomp]
    refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨⟨n, ?_⟩, rfl⟩
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hn) hc0
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    change (Finsupp.single p.1 (1 : ℂ) : CoreCoeff 24) 0 = 0
    rw [Finsupp.single_eq_of_ne (Ne.symm p.2)]

/-- **The root domain is closed under norm limits** on the core: a sequence of core vectors with no
vacuum component whose `coreNormSq` distance to `c` tends to `0` has no vacuum component either,
because `‖(s k) 0 − c 0‖² ≤ coreNormSq (s k − c)` and the left side is the constant `‖c 0‖²`.  This
is the only closedness the coefficient model supports — there is no completed space here, so limits
are `coreNormSq`-limits of sequences. -/
theorem rootDomain_closed_of_tendsto (s : ℕ → CoreCoeff 24) (hs : ∀ k, s k ∈ rootDomain)
    (c : CoreCoeff 24)
    (hlim : Filter.Tendsto (fun k => coreNormSq (s k - c)) Filter.atTop (nhds (0 : ℝ))) :
    c ∈ rootDomain := by
  have hb : ∀ k, ‖c 0‖ ^ 2 ≤ coreNormSq (s k - c) := by
    intro k
    have h := norm_sq_apply_zero_le_coreNormSq (s k - c)
    have hs0 : (s k) 0 = 0 := mem_rootDomain.mp (hs k)
    have h0 : (s k - c) 0 = -c 0 := by
      rw [Finsupp.sub_apply, hs0]
      simp
    rwa [h0, norm_neg] at h
  have hle : ‖c 0‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds (x := ‖c 0‖ ^ 2) (f := Filter.atTop)) hlim
      (Filter.Eventually.of_forall hb)
  have hnorm : ‖c 0‖ = 0 := by
    have h2 : ‖c 0‖ ^ 2 = 0 := le_antisymm hle (by positivity)
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  change c 0 = 0
  exact norm_eq_zero.mp hnorm

/-- **The closure of the root domain is the root domain.**  A core vector is a `coreNormSq` limit of
root-domain vectors exactly when it lies in the root domain: one direction is
`rootDomain_closed_of_tendsto`, the other the constant sequence. -/
theorem closure_rootDomain_iff (c : CoreCoeff 24) :
    (∃ s : ℕ → CoreCoeff 24, (∀ k, s k ∈ rootDomain) ∧
        Filter.Tendsto (fun k => coreNormSq (s k - c)) Filter.atTop (nhds (0 : ℝ)))
      ↔ c ∈ rootDomain := by
  constructor
  · rintro ⟨s, hs, hlim⟩
    exact rootDomain_closed_of_tendsto s hs c hlim
  · intro hc
    refine ⟨fun _ => c, fun _ => hc, ?_⟩
    have hzero : coreNormSq (c - c) = 0 := by simp [coreNormSq]
    simp only [hzero]
    exact tendsto_const_nhds

/-- **The gap holds on the closure of the root domain.**  Stated for a vector that is a `coreNormSq`
limit of root-domain vectors — i.e. for a point of the closure — the S2 gap follows from
`root_spectral_gap`, because the closure *is* the root domain (`closure_rootDomain_iff`): no
limiting argument on the quartic form is needed, and none would be available, since
`quadForm (ymHamiltonian …)` is not known to be continuous in `coreNormSq`. -/
theorem root_spectral_gap_on_closure (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (RI : RootModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (s : ℕ → CoreCoeff 24) (hs : ∀ k, s k ∈ rootDomain)
    (c : CoreCoeff 24)
    (hlim : Filter.Tendsto (fun k => coreNormSq (s k - c)) Filter.atTop (nhds (0 : ℝ))) :
    ((c₁ * refGap ω - quarticShift (d := 24) T g) / 48) * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (RI.toCore c) :=
  root_spectral_gap Φ fabc RI hω hg hc₁ hω₁ c
    (rootDomain_closed_of_tendsto s hs c hlim)

/-! #### The ℓ² completion: the root domain is dense, and the gap holds on it

The coefficient model is finitely supported, so "the closure of the root domain" can only mean the
completion.  This section builds it: `coreLp` is `ℓ²` on the occupation multi-indices, `coreToLp`
reads a core vector there, and `vacuumOrthogonal` is the closed subspace of vectors with no vacuum
component.  Finite-support root vectors are dense in that subspace (`closure_rootDomain_image_eq`),
which is the analytic form of §3d.3: what is "the excited span" there is literally a dense subspace
here.

The reference form is *unbounded* — `refEnergy` grows with the total occupation — so it is not a
function on all of `ℓ²`.  `refFormLp` is defined where its defining series converges, and the gap
statement carries that summability as a hypothesis; the gap survives the limit unchanged
(`ref_spectral_gap_closure`), the termwise bound of `href_spectral_gap` becoming a `tsum`
comparison.

What this section does **not** do is extend the Yang–Mills form to the completion: `quadForm
(ymHamiltonian …)` is quartic and not continuous in the `ℓ²` norm, so the right-hand side of
`root_spectral_gap` has no `ℓ²` analogue here, and none is claimed.
-/

open scoped ENNReal

variable {d : ℕ}

/-- The ℓ² completion of the coefficient model: square-summable families on the occupation
multi-indices. -/
abbrev coreLp (d : ℕ) := lp (fun _ : Fin d → ℕ => ℂ) 2

/-- The finite-support coefficient vector `c`, viewed in the completion. -/
noncomputable def coreToLp (c : CoreCoeff d) : coreLp d :=
  ∑ n ∈ c.support, lp.single 2 n (c n)

/-- A finite combination of coordinate basis vectors, read at `m`: it is `φ m` when `m` is one of
the indices used and zero otherwise. -/
theorem sum_single_apply (s : Finset (Fin d → ℕ)) (φ : (Fin d → ℕ) → ℂ) (m : Fin d → ℕ) :
    ((∑ i ∈ s, lp.single 2 i (φ i)) : coreLp d) m = if m ∈ s then φ m else 0 := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  by_cases hm : m ∈ s
  · rw [Finset.sum_eq_single m (fun b _ hbm => Pi.single_eq_of_ne' hbm _)
      (fun h => absurd hm h)]
    simp [hm]
  · rw [Finset.sum_eq_zero (fun x hx =>
        Pi.single_eq_of_ne' (fun h => hm (by rw [← h]; exact hx)) _), if_neg hm]

/-- **The embedding reads back the coefficients**: on its support `coreToLp c` is `c`. -/
theorem coreToLp_apply (c : CoreCoeff d) (n : Fin d → ℕ) : coreToLp c n = c n := by
  classical
  rw [coreToLp, sum_single_apply]
  by_cases hn : n ∈ c.support
  · simp [hn]
  · rw [if_neg hn, Finsupp.notMem_support_iff.mp hn]

/-- **The `ℓ²` norm is the completed core norm**: `‖f‖² = ∑' n, ‖f n‖²`. -/
theorem norm_sq_eq_tsum (f : coreLp d) : ‖f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, h2]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (tsum_nonneg fun n => by positivity)]

/-- **The embedding is isometric for the core norm**: `coreNormSq` is the squared `ℓ²` norm of the
image.  So `coreNormSq`-convergence is `ℓ²`-convergence on finite-support vectors, and the two
notions of closure of §3d.3 meet here. -/
theorem norm_coreToLp_sq (c : CoreCoeff d) : ‖coreToLp c‖ ^ 2 = coreNormSq c := by
  have hzero : ∀ n ∉ c.support, ‖coreToLp c n‖ ^ 2 = 0 := by
    intro n hn
    rw [coreToLp_apply, Finsupp.notMem_support_iff.mp hn]
    simp
  rw [norm_sq_eq_tsum, tsum_eq_sum hzero, coreNormSq]
  exact Finset.sum_congr rfl fun n _ => by rw [coreToLp_apply]

/-- Evaluation of a completion vector at one multi-index is continuous — in fact `1`-Lipschitz,
because `‖f i‖ ≤ ‖f‖`. -/
theorem continuous_apply_coreLp (i : Fin d → ℕ) : Continuous fun f : coreLp d => f i := by
  have h : LipschitzWith 1 fun f : coreLp d => f i := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    have h := lp.norm_apply_le_norm (p := 2) (by simp) (f - g) i
    simp only [lp.coeFn_sub, Pi.sub_apply] at h
    simpa [dist_eq_norm] using h
  exact h.continuous

/-- The vacuum-orthogonal subspace of the completion: the vectors with no vacuum component. -/
def vacuumOrthogonal (d : ℕ) : Submodule ℂ (coreLp d) where
  carrier := {f | f 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro f g hf hg
    change (f + g) 0 = 0
    rw [lp.coeFn_add, Pi.add_apply, hf, hg, add_zero]
  smul_mem' := by
    intro a f hf
    change (a • f) 0 = 0
    rw [lp.coeFn_smul, Pi.smul_apply, hf, smul_zero]

/-- The vacuum-orthogonal subspace is closed: it is the preimage of `{0}` under a continuous
functional. -/
theorem isClosed_vacuumOrthogonal (d : ℕ) : IsClosed (vacuumOrthogonal d : Set (coreLp d)) :=
  isClosed_eq (continuous_apply_coreLp 0) continuous_const

/-- Root-domain vectors land in the vacuum-orthogonal subspace: the embedding preserves the
vanishing vacuum coefficient. -/
theorem coreToLp_mem_vacuumOrthogonal {c : CoreCoeff 24} (hc : c ∈ rootDomain) :
    coreToLp c ∈ vacuumOrthogonal 24 := by
  change coreToLp c 0 = 0
  rw [coreToLp_apply]
  exact mem_rootDomain.mp hc

/-- **Finite-support root vectors are dense in the vacuum-orthogonal subspace.**  Given `f` with no
vacuum component and `ε > 0`, the canonical finitely supported approximations of `lp.hasSum_single`
produce a root-domain vector within `ε` of `f` — the truncation is a `Finsupp`, and it inherits
`f 0 = 0`. -/
theorem mem_closure_rootDomain_image (f : coreLp 24) (hf : f 0 = 0) :
    f ∈ closure (coreToLp '' (rootDomain : Set (CoreCoeff 24))) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  have ht : Filter.Tendsto (fun s : Finset (Fin 24 → ℕ) => ∑ i ∈ s, lp.single 2 i (f i))
      Filter.atTop (nhds f) := lp.hasSum_single (p := 2) (by simp) f
  obtain ⟨s, hs⟩ := ((Metric.tendsto_nhds.mp ht) ε hε).exists
  have hs' : dist (∑ i ∈ s, lp.single 2 i (f i)) f < ε := hs
  let g : (Fin 24 → ℕ) → ℂ := fun n => if n ∈ s then f n else 0
  have hfin : (Function.support g).Finite :=
    s.finite_toSet.subset (by
      intro n hn
      by_contra hns
      have hns' : n ∉ s := by simpa using hns
      have hz : g n = 0 := by
        change (if n ∈ s then f n else 0) = 0
        rw [if_neg hns']
      exact hn hz)
  let c : CoreCoeff 24 := Finsupp.ofSupportFinite g hfin
  have hc_apply : ∀ n, c n = g n := fun n =>
    congrFun (Finsupp.ofSupportFinite_coe (f := g) (hf := hfin)) n
  have hc0 : c 0 = 0 := by
    rw [hc_apply]
    simp only [g]
    simp [hf]
  have hcore : coreToLp c = ∑ i ∈ s, lp.single 2 i (f i) := by
    ext m
    rw [coreToLp_apply, hc_apply, sum_single_apply]
  refine ⟨coreToLp c, ⟨c, mem_rootDomain.mpr hc0, rfl⟩, ?_⟩
  rw [hcore, dist_comm]
  exact hs'

/-- **The closure of the root domain is the vacuum-orthogonal subspace**: one inclusion is the
closedness of the subspace, the other is density.  This is the completion's version of
`closure_rootDomain_iff`. -/
theorem closure_rootDomain_image_eq :
    closure (coreToLp '' (rootDomain : Set (CoreCoeff 24)))
      = (vacuumOrthogonal 24 : Set (coreLp 24)) := by
  refine le_antisymm ?_ ?_
  · refine closure_minimal ?_ (isClosed_vacuumOrthogonal 24)
    rintro _ ⟨c, hc, rfl⟩
    exact coreToLp_mem_vacuumOrthogonal hc
  · intro f hf
    exact mem_closure_rootDomain_image f hf

/-- The reference form on the completion, where its series converges — the natural domain of the
unbounded harmonic form, not all of `ℓ²`. -/
noncomputable def refFormLp (ω : Fin 24 → ℝ) (f : coreLp 24) : ℝ :=
  ∑' n, refEnergy ω n * ‖f n‖ ^ 2

/-- **The reference gap on the `ℓ²` completion.**  `href_spectral_gap` is a termwise inequality over
finitely supported vectors; on the form domain of the completion the same comparison holds with the
finite sum replaced by a `tsum`.  Summability of the form is carried as a hypothesis — this is the
unbounded part, and `‖f‖²` is recovered from `norm_sq_eq_tsum`. -/
theorem ref_spectral_gap_closure {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i) (f : coreLp 24)
    (h0 : f 0 = 0) (hsum : Summable fun n => refEnergy ω n * ‖f n‖ ^ 2) :
    (refEnergy ω 0 + refGap ω) * ‖f‖ ^ 2 ≤ refFormLp ω f := by
  have hE0 : 0 < refEnergy ω 0 := by
    rw [refEnergy_zero]
    exact Finset.sum_pos (fun i _ => by linarith [hω i]) Finset.univ_nonempty
  have hc : 0 < refEnergy ω 0 + refGap ω := by
    have := refGap_pos hω
    linarith
  have hterm : ∀ n, (refEnergy ω 0 + refGap ω) * ‖f n‖ ^ 2 ≤ refEnergy ω n * ‖f n‖ ^ 2 := by
    intro n
    rcases eq_or_ne n (0 : Fin 24 → ℕ) with rfl | hn
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (refEnergy_ge_vacuum_add_gap hω hn) (by positivity)
  have hsum' : Summable fun n => ‖f n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hsum.mul_left (1 / (refEnergy ω 0 + refGap ω)))
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
    simpa [mul_comm] using hterm n
  rw [norm_sq_eq_tsum, refFormLp, ← tsum_mul_left]
  exact (hsum'.mul_left _).tsum_le_tsum hterm hsum

/-! #### The `ℂ²` colour factor of a mode

`fundMode d` is the ℓ² completion of the occupation core *with* a colour factor: square-summable
families on `Fin d → ℕ` valued in `ℂ²`.  A core vector with a colour vector attached is
`colourModeVec c v`, and `colourEnergy` is the quadratic Casimir `Σ_a T^a T^a` acting on the colour
factor only.

`colourEnergy_colourModeVec` is the content: on `c ⊗ v` the Casimir multiplies `v` by `C_F = 3/4`
and leaves the Fock coefficients `c n` untouched.  This is the mode-factor form of
`su2_casimir_fundamental` — the colour factor is dressed with the number content, and `C_F` still
extracts as a scalar.

**Boundary.**  `colourAct` and `colourEnergy` are first defined on the underlying families; the
bounded operators `colourActCLM`/`colourEnergyCLM` below extend them to the completion, and
`colourEnergyOp` is the Casimir as a scalar multiple of the identity.  What is not done here is a
decomposition of `fundMode d` into colour multiplets, or an identification of this completion with
the field fibre `colouredCore` built further down.
-/

/-- The Fock core completed with a colour `ℂ²` factor: square-summable families on the occupation
multi-indices, valued in `ℂ²`. -/
abbrev fundMode (d : ℕ) := lp (fun _ : Fin d → ℕ => Fin 2 → ℂ) 2

/-- A finite combination of coordinate basis vectors valued in a normed space, read at `m`. -/
theorem sum_single_apply_gen {E : Type*} [NormedAddCommGroup E] (s : Finset (Fin d → ℕ))
    (φ : (Fin d → ℕ) → E) (m : Fin d → ℕ) :
    ((∑ i ∈ s, lp.single 2 i (φ i)) : lp (fun _ : Fin d → ℕ => E) 2) m
      = if m ∈ s then φ m else 0 := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  by_cases hm : m ∈ s
  · rw [Finset.sum_eq_single m (fun b _ hbm => Pi.single_eq_of_ne' hbm _)
      (fun h => absurd hm h)]
    simp [hm]
  · rw [Finset.sum_eq_zero (fun x hx =>
        Pi.single_eq_of_ne' (fun h => hm (by rw [← h]; exact hx)) _), if_neg hm]

/-- A core vector with a fixed colour vector attached: the Fock factor and the colour factor side by
side in the coloured completion. -/
noncomputable def colourModeVec (c : CoreCoeff d) (v : Fin 2 → ℂ) : fundMode d :=
  ∑ n ∈ c.support, lp.single 2 n (c n • v)

/-- `colourModeVec` is `c n • v` coefficientwise, and zero off the core support. -/
theorem colourModeVec_apply (c : CoreCoeff d) (v : Fin 2 → ℂ) (n : Fin d → ℕ) :
    colourModeVec c v n = c n • v := by
  classical
  rw [colourModeVec, sum_single_apply_gen]
  by_cases hn : n ∈ c.support
  · simp [hn]
  · rw [if_neg hn, Finsupp.notMem_support_iff.mp hn, zero_smul]

/-- The colour action of a generator on the `ℂ²` factor, at the level of the underlying families. -/
def colourAct (a : Fin 3) (f : fundMode d) : (Fin d → ℕ) → (Fin 2 → ℂ) :=
  fun n => (fundRep a).mulVec (f n)

/-- **The colour energy**: the quadratic Casimir `Σ_a T^a T^a` acting on the colour factor, at the
level of the underlying families. -/
noncomputable def colourEnergy (f : fundMode d) : (Fin d → ℕ) → (Fin 2 → ℂ) :=
  fun n => ∑ a : Fin 3, (fundRep a).mulVec ((fundRep a).mulVec (f n))

/-- **The Casimir matrix acts as `C_F`**: `(Σ_a T^a T^a).mulVec v = (3/4) • v`, straight from
`su2_casimir_fundamental`. -/
theorem casimir_mulVec (v : Fin 2 → ℂ) :
    (∑ a : Fin 3, fundRep a * fundRep a).mulVec v = (3 / 4 : ℂ) • v := by
  rw [su2_casimir_fundamental, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The three colour summands reassemble into the Casimir matrix. -/
theorem sum_mulVec_mulVec (v : Fin 2 → ℂ) :
    (∑ a : Fin 3, (fundRep a).mulVec ((fundRep a).mulVec v))
      = (∑ a : Fin 3, fundRep a * fundRep a).mulVec v := by
  rw [Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun a _ => Matrix.mulVec_mulVec v (fundRep a) (fundRep a)

/-- **The colour energy carries `C_F` and leaves the Fock factor alone.**  On a mode vector `c ⊗ v`
the Casimir multiplies the colour vector by `3/4` and does not touch the coefficients `c n`. -/
theorem colourEnergy_colourModeVec (c : CoreCoeff d) (v : Fin 2 → ℂ) :
    colourEnergy (colourModeVec c v) = fun n => c n • ((3 / 4 : ℂ) • v) := by
  funext n
  rw [colourEnergy, colourModeVec_apply]
  have hmul : ∀ a : Fin 3,
      (fundRep a).mulVec ((fundRep a).mulVec (c n • v))
        = c n • ((fundRep a).mulVec ((fundRep a).mulVec v)) := by
    intro a
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [hmul, ← Finset.smul_sum, sum_mulVec_mulVec, casimir_mulVec]

/-- The same statement in the form the colour energy is usually quoted in: `C_F` times the identity
on the coloured factor. -/
theorem colourEnergy_colourModeVec_eq (c : CoreCoeff d) (v : Fin 2 → ℂ) :
    colourEnergy (colourModeVec c v) = fun n => (3 / 4 : ℂ) • (colourModeVec c v n) := by
  rw [colourEnergy_colourModeVec]
  funext n
  rw [colourModeVec_apply, smul_smul, smul_smul]
  congr 1
  ring

/-! #### The colour energy on the completion, and the `ℂ³` gluon factor

`colourEnergy` is a scalar on the whole completion, not only on mode vectors: for *every* `f` in
`fundMode d` it is `(3/4) • f` coefficientwise (`colourEnergy_eq_smul`), so it extends to the
continuous linear map `colourEnergyOp`, with operator norm at most `3/4` (`colourEnergyOp_apply`,
`norm_colourEnergyOp`).  That removes the boundary of the section above: the colour Casimir is a
bounded operator on the ℓ² completion, not only a formula on `c ⊗ v`.

The gluon side is the adjoint representation on `ℂ³`: `adjRep` is `(T^a)_{bc} = −i ε^{abc}`, its
commutators are `[T^a, T^b] = i ε^{abc} T^c` (`adjRep_commutator`) — the same algebra `fundRep`
carries — and its Casimir is `2 · 1` (`adjRep_casimir`), so `C_A = 2` is now a matrix identity and
not only the scalar `su2_casimir_adjoint`.  A mode vector with a colour `ℂ³` factor is
`adjModeVec c v`, on which the adjoint colour energy multiplies `v` by `2`
(`adjColourEnergy_adjModeVec`).

So the two colour factors are mode factors of one completion: `C_F = 3/4` on the `ℂ²` factor and
`C_A = 2` on the `ℂ³` factor, in the ratio `8/3` (`casimir_ratio`), each the eigenvalue of its own
Casimir.

**Boundary.**  Here the two factors sit over the same occupation labels but are not combined into
one space.  The section after `casimir_ratio` attaches them to the field core and folds `C_F`/`C_A`
into `quadForm (ymHamiltonian …)`, on elementary tensors only.  The norm of `colourEnergyOp` is
exactly `3/4` (`norm_colourEnergyOp_eq`).
-/

/-- **The colour energy is the scalar `C_F` on all of the completion**: for every `f`, the Casimir
multiplies each coefficient by `3/4`.  The mode-vector statement `colourEnergy_colourModeVec` is the
special case `f = colourModeVec c v`. -/
theorem colourEnergy_eq_smul (f : fundMode d) :
    colourEnergy f = fun n => (3 / 4 : ℂ) • f n := by
  funext n
  simp only [colourEnergy, sum_mulVec_mulVec, casimir_mulVec]

/-- **The colour energy as a continuous linear operator**: `C_F` times the identity on the coloured
completion.  This is the operator the completion carries, rather than the coefficient formula. -/
noncomputable def colourEnergyOp (d : ℕ) : fundMode d →L[ℂ] fundMode d :=
  (3 / 4 : ℂ) • ContinuousLinearMap.id ℂ (fundMode d)

/-- The operator agrees coefficientwise with `colourEnergy`, so no information is lost in passing to
the completion. -/
theorem colourEnergyOp_apply (d : ℕ) (f : fundMode d) (n : Fin d → ℕ) :
    colourEnergyOp d f n = colourEnergy f n := by
  rw [colourEnergyOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    colourEnergy_eq_smul]
  simp

/-- **Boundedness**: the colour energy is a continuous operator on the completion with norm at most
`C_F = 3/4`; the bound is attained, so the norm is exactly `3/4` (`norm_colourEnergyOp_eq`). -/
theorem norm_colourEnergyOp (d : ℕ) : ‖colourEnergyOp d‖ ≤ 3 / 4 := by
  have hc : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by
    simp
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun f => ?_
  rw [colourEnergyOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, hc]

/-- **The colour energy operator has norm exactly `C_F = 3/4`**: the bound of
`norm_colourEnergyOp` is attained.  `colourEnergyOp` is `(3/4) • 1`, so a single nonzero mode vector
realises the norm. -/
theorem norm_colourEnergyOp_eq (d : ℕ) : ‖colourEnergyOp d‖ = 3 / 4 := by
  refine le_antisymm (norm_colourEnergyOp d) ?_
  have hc : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by simp
  set v : Fin 2 → ℂ := fun j => if j = 0 then 1 else 0 with hv
  have hv0 : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [hv] at h0
  set f : fundMode d := lp.single 2 (0 : Fin d → ℕ) v with hf
  have hf0 : f ≠ 0 := by
    intro h
    have h0 : f 0 = 0 := by rw [h]; rfl
    rw [hf, lp.single_apply] at h0
    exact hv0 (by simpa using h0)
  have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hfv : colourEnergyOp d f = (3 / 4 : ℂ) • f := by
    rw [colourEnergyOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  have hle := ContinuousLinearMap.le_opNorm (colourEnergyOp d) f
  rw [hfv, norm_smul, hc] at hle
  exact le_of_mul_le_mul_right hle hpos

/-- **The adjoint representation of `su(2)` on `ℂ³`**: `(T^a)_{bc} = −i ε^{abc}`, the gluon factor.
Its Casimir below is `C_A = 2`, the matrix form of `su2_casimir_adjoint`. -/
def adjRep (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun b c => (-Complex.I) * (levi a b c : ℂ)

/-- The adjoint commutator for the first index `a = 0`, by the `27` entry checks of the case
analysis.  Split out so that no single declaration needs a raised heartbeat budget. -/
theorem adjRep_commutator_zero (b : Fin 3) (i j : Fin 3) :
    (adjRep 0 * adjRep b - adjRep b * adjRep 0) i j
      = (Complex.I • (∑ c : Fin 3, (levi 0 b c : ℂ) • adjRep c)) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply, adjRep]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three, levi] <;> norm_num

/-- The adjoint commutator for the first index `a = 1`. -/
theorem adjRep_commutator_one (b : Fin 3) (i j : Fin 3) :
    (adjRep 1 * adjRep b - adjRep b * adjRep 1) i j
      = (Complex.I • (∑ c : Fin 3, (levi 1 b c : ℂ) • adjRep c)) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply, adjRep]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three, levi] <;> norm_num

/-- The adjoint commutator for the first index `a = 2`. -/
theorem adjRep_commutator_two (b : Fin 3) (i j : Fin 3) :
    (adjRep 2 * adjRep b - adjRep b * adjRep 2) i j
      = (Complex.I • (∑ c : Fin 3, (levi 2 b c : ℂ) • adjRep c)) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply, adjRep]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three, levi] <;> norm_num

/-- **`adjRep` is a representation**: `[T^a, T^b] = i ε^{abc} T^c`, against the same `ε` as
`fundRep_commutator`.  So the fundamental and the adjoint are representations of one algebra in the
mode-factor language as well. -/
theorem adjRep_commutator (a b : Fin 3) :
    adjRep a * adjRep b - adjRep b * adjRep a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • adjRep c) := by
  ext i j
  fin_cases a
  · exact adjRep_commutator_zero b i j
  · exact adjRep_commutator_one b i j
  · exact adjRep_commutator_two b i j

/-- **The adjoint Casimir is `C_A = 2`**: `Σ_a (T^a)² = 2 · 1` on `ℂ³`, the matrix form of
`su2_casimir_adjoint`. -/
theorem adjRep_casimir :
    ∑ a : Fin 3, adjRep a * adjRep a = (2 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, adjRep]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three, levi] <;> norm_num

/-- **The adjoint Casimir acts as `C_A = 2`**: `(Σ_a T^a T^a).mulVec v = 2 • v`. -/
theorem adjRep_casimir_mulVec (v : Fin 3 → ℂ) :
    (∑ a : Fin 3, adjRep a * adjRep a).mulVec v = (2 : ℂ) • v := by
  rw [adjRep_casimir, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The Fock core completed with a colour `ℂ³` factor: the gluon mode space. -/
abbrev adjMode (d : ℕ) := lp (fun _ : Fin d → ℕ => Fin 3 → ℂ) 2

/-- A core vector with a gluon colour vector attached: the adjoint counterpart of
`colourModeVec`. -/
noncomputable def adjModeVec (c : CoreCoeff d) (v : Fin 3 → ℂ) : adjMode d :=
  ∑ n ∈ c.support, lp.single 2 n (c n • v)

/-- `adjModeVec` is `c n • v` coefficientwise, and zero off the core support. -/
theorem adjModeVec_apply (c : CoreCoeff d) (v : Fin 3 → ℂ) (n : Fin d → ℕ) :
    adjModeVec c v n = c n • v := by
  classical
  rw [adjModeVec, sum_single_apply_gen]
  by_cases hn : n ∈ c.support
  · simp [hn]
  · rw [if_neg hn, Finsupp.notMem_support_iff.mp hn, zero_smul]

/-- The **adjoint colour energy**: the Casimir `Σ_a T^a T^a` of `ℂ³` acting on the colour factor. -/
noncomputable def adjColourEnergy (f : adjMode d) : (Fin d → ℕ) → (Fin 3 → ℂ) :=
  fun n => ∑ a : Fin 3, (adjRep a).mulVec ((adjRep a).mulVec (f n))

/-- **The adjoint colour energy carries `C_A = 2` and leaves the Fock factor alone**: on `c ⊗ v` the
adjoint Casimir multiplies the colour vector by `2`. -/
theorem adjColourEnergy_adjModeVec (c : CoreCoeff d) (v : Fin 3 → ℂ) :
    adjColourEnergy (adjModeVec c v) = fun n => c n • ((2 : ℂ) • v) := by
  funext n
  rw [adjColourEnergy, adjModeVec_apply]
  have hmul : ∀ a : Fin 3,
      (adjRep a).mulVec ((adjRep a).mulVec (c n • v))
        = c n • ((adjRep a).mulVec ((adjRep a).mulVec v)) := by
    intro a
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [hmul, ← Finset.smul_sum]
  have hsum : (∑ a : Fin 3, (adjRep a).mulVec ((adjRep a).mulVec v))
      = (∑ a : Fin 3, adjRep a * adjRep a).mulVec v := by
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun a _ => Matrix.mulVec_mulVec v (adjRep a) (adjRep a)
  rw [hsum, adjRep_casimir_mulVec]

/-- **The ratio of the two colour factors**: `C_A/C_F = 2/(3/4) = 8/3`, the factor a
`C_A`-versus-`C_F` comparison multiplies by. -/
theorem casimir_ratio : (2 : ℝ) / (3 / 4) = 8 / 3 := by norm_num

/-! #### The colour fibre over the field core, and `C_F`/`C_A` inside the field form

The colour factors above live on the coefficient completion.  Attached to the *field* core they give
a genuine `H ⊗ 1 + 1 ⊗ C`: `colourSpace N = PiLp 2 (fun _ : Fin N => L2d 99)` is the core with `N`
colour components, `colouredCore N D` requires every component to lie in `D`, and
`colouredHamiltonian Φ fabc N C` acts componentwise by `ymHamiltonian Φ fabc` plus the colour matrix
`C` mixing the components (`colouredHamiltonian_ofLp`).  The elementary tensor `x ⊗ v` is
`colourFibre x v`, the family `i ↦ v i • x`.

For a diagonal colour energy `C = µ • 1` the form collapses to the field form plus `µ` times the
field norm squared (`colouredHamiltonian_smul_one_inner`,
`colouredHamiltonian_smul_one_quadForm`), and the two Casimirs are diagonal with exactly the values
of the operator section: `∑ a, T^a T^a = (3/4) • 1` on `ℂ²` (`su2_casimir_fundamental`) and `2 • 1`
on `ℂ³` (`adjRep_casimir`).  Hence on `x ⊗ v` one has
`quadForm (H + C) (x ⊗ v) = ‖v‖² (quadForm H x + C ‖x‖²)`, and likewise with `C_A = 2`
(`colouredHamiltonian_fundamental_quadForm`, `colouredHamiltonian_adjoint_quadForm`): the colour
factors are now eigenvalues inside `quadForm`, not only on the coefficient model.

Nor is this an elementary-tensor-only statement.  Since `H ⊗ 1 + 1 ⊗ (µ • 1)` is diagonal in the
colour components, the form splits componentwise for *every* `u` in the coloured core
(`colouredHamiltonian_smul_one_inner_core`, `colouredHamiltonian_smul_one_quadForm_core`, and with
the Casimirs `colouredHamiltonian_fundamental_quadForm_core`/`..._adjoint_quadForm_core`), and every
core element is a finite sum of elementary tensors (`colourFibre_repr`, `colourSum`) — so the finite
sum `∑ k, x k ⊗ v k` is covered with its cross terms inside the components (`colourSum_ofLp`,
`colouredHamiltonian_smul_one_quadForm_sum`).

**Boundary.**  The identity holds for a diagonal colour energy `µ • 1` on the whole coloured core; a
general colour matrix `C` is still evaluated only through its diagonal part, nothing is claimed
about the norm of the coloured operator, and the Fock/occupation completion carrying
`colourEnergyOp` is still a separate model, not identified here with this fibre.
-/

/-- The colour-completed Hilbert space over the `99`-coordinate field space: `N` colour components
with the ℓ² norm. -/
abbrev colourSpace (N : ℕ) : Type := PiLp 2 (fun _ : Fin N => L2d 99)

/-- The colour fibre `ℂ^N`, with the ℓ² inner product. -/
abbrev colourVec (N : ℕ) : Type := PiLp 2 (fun _ : Fin N => ℂ)

/-- The colour-completed **core**: every colour component lies in `D`. -/
def colouredCore (N : ℕ) (D : Submodule ℂ (L2d 99)) : Submodule ℂ (colourSpace N) where
  carrier := {u | ∀ i, WithLp.ofLp u i ∈ D}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro u v hu hv i
    rw [PiLp.add_apply]
    exact D.add_mem (hu i) (hv i)
  smul_mem' := by
    intro c u hu i
    rw [PiLp.smul_apply]
    exact D.smul_mem c (hu i)

set_option maxHeartbeats 1000000 in
-- Elaborating the colour-completed core requires unfolding `PiLp` coercions through the
-- submodule `D`; the default heartbeat budget is not enough.
/-- **The coloured Hamiltonian `H ⊗ 1 + 1 ⊗ C`** on the colour-completed core: the field Hamiltonian
acts on each colour component and the colour matrix `C` mixes the components. -/
noncomputable def colouredHamiltonian {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (N : ℕ) (C : Matrix (Fin N) (Fin N) ℂ) :
    colouredCore N D →ₗ[ℂ] colourSpace N where
  toFun u :=
    WithLp.toLp 2 fun i =>
      ymHamiltonian Φ fabc ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
        + ∑ j : Fin N, C i j • (WithLp.ofLp (u : colourSpace N) j)
  map_add' u v := by
    apply WithLp.ofLp_injective
    funext i
    simp only [WithLp.ofLp_add, Submodule.coe_add, Pi.add_apply]
    have hsub : (⟨WithLp.ofLp (u : colourSpace N) i + WithLp.ofLp (v : colourSpace N) i,
        (u + v).2 i⟩ : D) = ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
          + ⟨WithLp.ofLp (v : colourSpace N) i, v.2 i⟩ := Subtype.ext rfl
    rw [hsub, map_add]
    simp only [smul_add, Finset.sum_add_distrib]
    abel
  map_smul' c u := by
    apply WithLp.ofLp_injective
    funext i
    simp only [WithLp.ofLp_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    have hsub : (⟨c • WithLp.ofLp (u : colourSpace N) i, (c • u).2 i⟩ : D)
        = c • ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩ := Subtype.ext rfl
    rw [hsub, map_smul]
    simp only [smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (smul_comm c (C i j) _).symm

/-- The component of the coloured Hamiltonian at a colour index: the field Hamiltonian on that
component plus the `C`-weighted sum of all components. -/
theorem colouredHamiltonian_ofLp {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (u : colouredCore N D) (i : Fin N) :
    (colouredHamiltonian Φ fabc N C u : colourSpace N).ofLp i
      = ymHamiltonian Φ fabc ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
        + ∑ j : Fin N, C i j • (WithLp.ofLp (u : colourSpace N) j) := rfl

/-- A diagonal colour energy `µ • 1` acts on each colour component by `µ`. -/
theorem colouredHamiltonian_smul_one_ofLp {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (μ : ℂ) (u : colouredCore N D)
    (i : Fin N) :
    (colouredHamiltonian Φ fabc N (μ • (1 : Matrix (Fin N) (Fin N) ℂ)) u :
        colourSpace N).ofLp i
      = ymHamiltonian Φ fabc ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
        + μ • (WithLp.ofLp (u : colourSpace N) i) := by
  rw [colouredHamiltonian_ofLp]
  congr 1
  simp [Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq]

/-- The elementary tensor `x ⊗ v` of the field core with a colour fibre: the component at `i` is
`v i • x`. -/
noncomputable def colourFibre {D : Submodule ℂ (L2d 99)} (x : D) (v : colourVec N) :
    colouredCore N D :=
  ⟨WithLp.toLp 2 (fun i => WithLp.ofLp v i • (x : L2d 99)),
    fun i => D.smul_mem (WithLp.ofLp v i) x.2⟩

set_option maxHeartbeats 1000000 in
-- The coloured form is computed by unfolding the `colourFibre` coercions and the
-- `PiLp` inner product; the default heartbeat budget is not enough.
/-- **The form of `H ⊗ 1 + 1 ⊗ (µ • 1)` on an elementary tensor**: the colour norm squared times the
field form plus `µ` times the field norm squared. -/
theorem colouredHamiltonian_smul_one_inner {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (μ : ℂ)
    (x : D) (v : colourVec N) :
    (inner ℂ (colourFibre (D := D) x v : colourSpace N)
        (colouredHamiltonian Φ fabc N (μ • (1 : Matrix (Fin N) (Fin N) ℂ))
          (colourFibre (D := D) x v)) : ℂ)
      = inner ℂ v v * (inner ℂ (x : L2d 99) (ymHamiltonian Φ fabc x)
          + μ * inner ℂ (x : L2d 99) (x : L2d 99)) := by
  rw [PiLp.inner_apply]
  have hcomp : ∀ i : Fin N,
      (colourFibre (D := D) x v : colourSpace N).ofLp i
        = WithLp.ofLp v i • (x : L2d 99) := fun i => rfl
  simp only [hcomp, colouredHamiltonian_smul_one_ofLp]
  have hH : ∀ (c : ℂ) (y : D),
      (ymHamiltonian Φ fabc ⟨c • (y : L2d 99), D.smul_mem c y.2⟩ : L2d 99)
        = c • ymHamiltonian Φ fabc y := by
    intro c y
    have hsub : (⟨c • (y : L2d 99), D.smul_mem c y.2⟩ : D) = c • y := Subtype.ext rfl
    rw [hsub, map_smul]
  have hterm : ∀ i : Fin N,
      inner ℂ (WithLp.ofLp v i • (x : L2d 99))
        ((ymHamiltonian Φ fabc ⟨WithLp.ofLp v i • (x : L2d 99),
            D.smul_mem (WithLp.ofLp v i) x.2⟩ : L2d 99)
          + μ • (WithLp.ofLp v i • (x : L2d 99)))
      = inner ℂ (WithLp.ofLp v i) (WithLp.ofLp v i)
        * (inner ℂ (x : L2d 99) (ymHamiltonian Φ fabc x)
          + μ * inner ℂ (x : L2d 99) (x : L2d 99)) := by
    intro i
    rw [hH]
    simp only [inner_add_right, inner_smul_left, inner_smul_right, smul_smul,
      RCLike.inner_apply]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [← Finset.sum_mul, PiLp.inner_apply]

set_option maxHeartbeats 1000000 in
-- Unfolding the coloured quadratic form to the field form is a large `PiLp` reduction;
-- the default heartbeat budget is not enough.
/-- **The colour energy `µ • 1` folded into the field form**: on `x ⊗ v` the coloured quadratic form
is the colour norm squared times the field form plus `µ.re` times the field norm squared. -/
theorem colouredHamiltonian_smul_one_quadForm {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (μ : ℂ)
    (hμ : μ.im = 0) (x : D) (v : colourVec N) :
    quadForm (colouredHamiltonian Φ fabc N (μ • (1 : Matrix (Fin N) (Fin N) ℂ)))
        (colourFibre (D := D) x v)
      = ‖v‖ ^ 2 * (quadForm (ymHamiltonian Φ fabc) x + μ.re * ‖(x : L2d 99)‖ ^ 2) := by
  have hsymm := ymHamiltonian_symmetricOn Φ fabc
  have hvv_im : (inner ℂ v v : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) v
  have hvv_re : (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hQ0 : (inner ℂ (x : L2d 99) (ymHamiltonian Φ fabc x) : ℂ).im = 0 :=
    quadForm_im _ hsymm x
  have hQ1 : (inner ℂ (x : L2d 99) (x : L2d 99) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (x : L2d 99)
  have hQ1re : (inner ℂ (x : L2d 99) (x : L2d 99) : ℂ).re = ‖(x : L2d 99)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x : L2d 99)
  rw [quadForm, colouredHamiltonian_smul_one_inner]
  have hsum : (inner ℂ (x : L2d 99) (ymHamiltonian Φ fabc x)
        + μ * inner ℂ (x : L2d 99) (x : L2d 99) : ℂ)
      = (((quadForm (ymHamiltonian Φ fabc) x
          + μ.re * ‖(x : L2d 99)‖ ^ 2 : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, quadForm, hμ]
    · simp [Complex.add_im, Complex.mul_im, hμ, hQ0]
  rw [hsum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hvv_im, hvv_re]
  ring

/-- **`C_F = 3/4` inside the field form**: on the fundamental colour fibre (`ℂ²`) the coloured
Hamiltonian's form is the field form plus `C_F` times the field norm squared. -/
theorem colouredHamiltonian_fundamental_quadForm {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) (v : colourVec 2) :
    quadForm (colouredHamiltonian Φ fabc 2 (∑ a : Fin 3, fundRep a * fundRep a))
        (colourFibre (D := D) x v)
      = ‖v‖ ^ 2 * (quadForm (ymHamiltonian Φ fabc) x
          + (3 / 4) * ‖(x : L2d 99)‖ ^ 2) := by
  rw [su2_casimir_fundamental]
  simpa using colouredHamiltonian_smul_one_quadForm Φ fabc (3 / 4 : ℂ) (by norm_num) x v

/-- **`C_A = 2` inside the field form**: on the adjoint colour fibre (`ℂ³`) the coloured
Hamiltonian's form is the field form plus `C_A` times the field norm squared. -/
theorem colouredHamiltonian_adjoint_quadForm {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) (v : colourVec 3) :
    quadForm (colouredHamiltonian Φ fabc 3 (∑ a : Fin 3, adjRep a * adjRep a))
        (colourFibre (D := D) x v)
      = ‖v‖ ^ 2 * (quadForm (ymHamiltonian Φ fabc) x + 2 * ‖(x : L2d 99)‖ ^ 2) := by
  rw [adjRep_casimir]
  simpa using colouredHamiltonian_smul_one_quadForm Φ fabc (2 : ℂ) (by norm_num) x v

/-- **The form of `H ⊗ 1 + 1 ⊗ (µ • 1)` on the whole coloured core**: because the colour energy is
diagonal in the colour components, its inner product against any `u` splits into the field inner
products of the components plus `µ` times their norms. -/
theorem colouredHamiltonian_smul_one_inner_core {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (μ : ℂ)
    (u : colouredCore N D) :
    (inner ℂ (u : colourSpace N)
        (colouredHamiltonian Φ fabc N (μ • (1 : Matrix (Fin N) (Fin N) ℂ)) u) : ℂ)
      = ∑ i : Fin N, (inner ℂ (WithLp.ofLp (u : colourSpace N) i)
            (ymHamiltonian Φ fabc ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩)
          + μ * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
              (WithLp.ofLp (u : colourSpace N) i)) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [colouredHamiltonian_smul_one_ofLp, inner_add_right, inner_smul_right]

/-- **The colour energy `µ • 1` folded into the field form, on the whole coloured core**: for an
arbitrary `u` the coloured quadratic form is the sum over colour components of the field form plus
`µ.re` times the component norm squared.  No decomposition of `u` into elementary tensors is
assumed, so this is the identity on finite sums of `x ⊗ v` too
(`colouredHamiltonian_smul_one_quadForm_sum`), and — with `colourFibre_repr` — on all of the
core. -/
theorem colouredHamiltonian_smul_one_quadForm_core {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (μ : ℂ)
    (hμ : μ.im = 0) (u : colouredCore N D) :
    quadForm (colouredHamiltonian Φ fabc N (μ • (1 : Matrix (Fin N) (Fin N) ℂ))) u
      = ∑ i : Fin N, (quadForm (ymHamiltonian Φ fabc)
            ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
          + μ.re * ‖WithLp.ofLp (u : colourSpace N) i‖ ^ 2) := by
  rw [quadForm, colouredHamiltonian_smul_one_inner_core, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hQ1 : (inner ℂ (WithLp.ofLp (u : colourSpace N) i)
      (WithLp.ofLp (u : colourSpace N) i) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (WithLp.ofLp (u : colourSpace N) i)
  have hQ1re : (inner ℂ (WithLp.ofLp (u : colourSpace N) i)
      (WithLp.ofLp (u : colourSpace N) i) : ℂ).re
      = ‖WithLp.ofLp (u : colourSpace N) i‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.ofLp (u : colourSpace N) i)
  simp only [Complex.add_re, Complex.mul_re, quadForm, hμ, hQ1, hQ1re]
  ring

/-- **`C_F = 3/4` inside the field form on the whole core**. -/
theorem colouredHamiltonian_fundamental_quadForm_core {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (u : colouredCore 2 D) :
    quadForm (colouredHamiltonian Φ fabc 2 (∑ a : Fin 3, fundRep a * fundRep a)) u
      = ∑ i : Fin 2, (quadForm (ymHamiltonian Φ fabc)
            ⟨WithLp.ofLp (u : colourSpace 2) i, u.2 i⟩
          + (3 / 4) * ‖WithLp.ofLp (u : colourSpace 2) i‖ ^ 2) := by
  rw [su2_casimir_fundamental]
  simpa using colouredHamiltonian_smul_one_quadForm_core Φ fabc (3 / 4 : ℂ) (by norm_num) u

/-- **`C_A = 2` inside the field form on the whole core**. -/
theorem colouredHamiltonian_adjoint_quadForm_core {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (u : colouredCore 3 D) :
    quadForm (colouredHamiltonian Φ fabc 3 (∑ a : Fin 3, adjRep a * adjRep a)) u
      = ∑ i : Fin 3, (quadForm (ymHamiltonian Φ fabc)
            ⟨WithLp.ofLp (u : colourSpace 3) i, u.2 i⟩
          + 2 * ‖WithLp.ofLp (u : colourSpace 3) i‖ ^ 2) := by
  rw [adjRep_casimir]
  simpa using colouredHamiltonian_smul_one_quadForm_core Φ fabc (2 : ℂ) (by norm_num) u

/-- The `i`-th unit vector of the colour fibre. -/
noncomputable def colourUnit {N : ℕ} (i : Fin N) : colourVec N :=
  WithLp.toLp 2 fun j => if j = i then 1 else 0

/-- **Every element of the coloured core is a finite sum of elementary tensors**, namely of its
components against the unit colour vectors.  Hence the core-wide identities above extend the
elementary-tensor ones from a single `x ⊗ v` to finite sums, and because the finite sum here
exhausts the components they hold on all of the core. -/
theorem colourFibre_repr {D : Submodule ℂ (L2d 99)} {N : ℕ} (u : colouredCore N D) :
    (∑ i : Fin N, colourFibre (D := D) ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
        (colourUnit i)) = u := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_sum]
  funext j
  simp only [colourFibre, colourUnit, WithLp.ofLp_toLp]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [show j ≠ b from Ne.symm hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A finite sum `∑ k, x k ⊗ v k` of elementary tensors in the coloured core. -/
noncomputable def colourSum {D : Submodule ℂ (L2d 99)} {ι : Type} {N : ℕ}
    (s : Finset ι) (x : ι → D) (v : ι → colourVec N) : colouredCore N D :=
  Finset.sum s fun k => colourFibre (D := D) (x k) (v k)

/-- **The colour components of a finite sum of elementary tensors**: the `i`-th component mixes the
summands, it is `∑ k, v k i • x k`.  This is where the cross terms between summands live. -/
theorem colourSum_ofLp {D : Submodule ℂ (L2d 99)} {ι : Type} {N : ℕ}
    (s : Finset ι) (x : ι → D) (v : ι → colourVec N) (i : Fin N) :
    (colourSum s x v : colourSpace N).ofLp i
      = Finset.sum s fun k => WithLp.ofLp (v k) i • (x k : L2d 99) := by
  rw [colourSum, Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]
  rfl

/-- **The coloured form of a finite sum of elementary tensors**: it is the sum over colour
components of the field form of the mixed component `∑ k, v k i • x k`, plus `µ.re` times that
component's norm squared.  The cross terms between summands are carried by the components, so this
is not a sum of the per-tensor values of `colouredHamiltonian_smul_one_quadForm`. -/
theorem colouredHamiltonian_smul_one_quadForm_sum {D : Submodule ℂ (L2d 99)}
    (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (μ : ℂ) (hμ : μ.im = 0)
    {ι : Type} (s : Finset ι) (x : ι → D) (v : ι → colourVec N) :
    quadForm (colouredHamiltonian Φ fabc N (μ • (1 : Matrix (Fin N) (Fin N) ℂ)))
        (colourSum s x v)
      = ∑ i : Fin N, (quadForm (ymHamiltonian Φ fabc)
            ⟨Finset.sum s fun k => WithLp.ofLp (v k) i • (x k : L2d 99),
              D.sum_mem fun k _ => D.smul_mem (WithLp.ofLp (v k) i) (x k).2⟩
          + μ.re * ‖Finset.sum s fun k => WithLp.ofLp (v k) i • (x k : L2d 99)‖ ^ 2) := by
  rw [colouredHamiltonian_smul_one_quadForm_core Φ fabc μ hμ (colourSum s x v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (⟨Finset.sum s fun k => WithLp.ofLp (v k) i • (x k : L2d 99),
        D.sum_mem fun k _ => D.smul_mem (WithLp.ofLp (v k) i) (x k).2⟩ : D)
      = ⟨WithLp.ofLp ((colourSum s x v : colourSpace N)) i, (colourSum s x v).2 i⟩ :=
    Subtype.ext (colourSum_ofLp s x v i).symm
  rw [hsub, ← colourSum_ofLp s x v i]
/-! #### The coloured form with a general colour matrix

The diagonal fold above evaluates `C = µ • 1` only through `µ`.  With a general `C` the colour
part is not a scalar: `colouredHamiltonian` mixes the components and its cross terms survive.
The identity is

`⟨u, (H ⊗ 1 + 1 ⊗ C) u⟩ = Σ_i ⟨u_i, H u_i⟩ + Σ_i Σ_j C_ij ⟨u_i, u_j⟩`

(`colouredHamiltonian_inner_core`) and, in form language,
`quadForm = Σ_i quadForm H u_i + Σ_i Re (Σ_j C_ij ⟨u_i, u_j⟩)`
(`colouredHamiltonian_quadForm_core`); the second double sum is exactly what the diagonal version
drops.

`colouredHamiltonian_swap_quadForm` is an off-diagonal case in closed form: with
`C = [[0, 1], [1, 0]]` the two components exchange and the form is
`quadForm H u₀ + quadForm H u₁ + 2 Re ⟨u₀, u₁⟩`.  The cross term `2 Re ⟨u₀, u₁⟩` is invisible
to any diagonal `µ • 1`, so off-diagonal colour matrix entries genuinely change the form and are
not a relabelling of the two Casimir scalars.

For a **Hermitian** `C` the colour part is real and symmetric, and this is the Hermitian form the
name suggests: the double sum `Σ_i Σ_j C_ij ⟨u_i, u_j⟩` equals its own star
(`colourTerm_star_eq`), the `(j, i)` and `(i, j)` contributions of the off-diagonal part agree
(`colourPair_re_symm`) so the off-diagonal sum is twice its `i < j` part
(`colourPairSum_eq_two_mul_upper`), and the form splits into the *real* diagonal
`(C_ii).re ‖u_i‖²` plus the real parts of the off-diagonal entries
(`colouredHamiltonian_quadForm_re_split`).

The **operator** is symmetric as well, not only its form: for `Cᴴ = C`
`colouredHamiltonian` satisfies `⟨(H ⊗ 1 + 1 ⊗ C) u, v⟩ = ⟨u, (H ⊗ 1 + 1 ⊗ C) v⟩` on the whole
coloured core (`colouredHamiltonian_symmetricOn`).  The field half is
`ymHamiltonian_symmetricOn`, and the colour half is the Hermiticity itself: the `(i, j)` entry of
the colour part is `conj C_ij`, which `i ↔ j` of the double sum turns back into the `(i, j)` entry
of the other side.

**Boundary.**  `colouredHamiltonian_quadForm_core` holds for every `u` in the coloured core and
uses no symmetry of `C`: it is an identity of complex inner products taken before the real part.
Symmetry on the core is not essential self-adjointness, and no deficiency index, closedness or
domain statement is claimed; a bound on the cross term is also not claimed.

The route to that statement is already laid, and it is a *direct-sum* one, not a Fock one.
`colourSpace N` is the `N`-fold `ℓ²` sum of `L²(ℝ⁹⁹)` and the field half of `colouredHamiltonian`
is the direct sum of the operators `ymHamiltonian Φ fabc`.  The two spaces are *isometric* rather
than definitionally equal (`lp` is a subtype of `PreLp`, related to `PiLp` by `lpPiLpₗᵢ`), and over
that isometry the coloured core is the algebraic direct sum of `N` copies of the field core.  So
`colouredHamiltonian_symmetricOn` is the constant-family case `G = fun _ => L2d 99` of the toolbox
theorem `BookProof.DirectSumEsa.dsOp_symmetricOn`, and the same decomposition gives essential
self-adjointness: `dsOp_essentiallySelfAdjointOn` glues per-fibre essential self-adjointness — for
`D = polyGaussCore 99` and `Φ = coreRepPoly 99` that per-fibre input is `ym_h_esa` in
`Qym/ChapterYangMillsNonAbelianEsa.lean` — to essential self-adjointness of `H ⊗ 1`, and `1 ⊗ C`
is finite-rank on the colour factor, a bounded symmetric perturbation, which leaves the deficiency
spaces alone.  No Faris–Lavine hypothesis is needed for that: `H` is already
known to be essentially self-adjoint by the Gauss-polynomial/Deg–Kato route, and the colour mixing
is bounded, so there is no relative-bounded potential left to estimate.  The statement cannot be
made *here* — `Qym/ChapterYangMillsNonAbelianEsa.lean` imports this module — and the nested-Fock
lift `ym_dGamma_esa` is a different operator (`dΓ(H)` on `𝓕_fin`, not `H ⊗ 1_C` on
`L²(ℝ⁹⁹; ℂ^N)`), so it does not transfer to `colouredHamiltonian`.
-/

/-- **The coloured inner product with a general colour matrix**: the field part is the sum over
components of the field inner product, and the colour part is the double sum `Σ_i Σ_j C_ij
⟨u_i, u_j⟩` — the off-diagonal entries contribute the mixed terms. -/
theorem colouredHamiltonian_inner_core {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (u : colouredCore N D) :
    (inner ℂ (u : colourSpace N) (colouredHamiltonian Φ fabc N C u) : ℂ)
      = ∑ i : Fin N, (inner ℂ (WithLp.ofLp (u : colourSpace N) i)
            (ymHamiltonian Φ fabc ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩)
          + ∑ j : Fin N, C i j * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
              (WithLp.ofLp (u : colourSpace N) j)) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [colouredHamiltonian_ofLp, inner_add_right, inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]

/-- **The coloured quadratic form with a general colour matrix**: the sum over components of the
field form plus the real part of the double sum `Σ_i Σ_j C_ij ⟨u_i, u_j⟩`.  For a diagonal
`C = µ • 1` the double sum collapses to `µ.re ∑_i ‖u_i‖²`
(`colouredHamiltonian_smul_one_quadForm_core`). -/
theorem colouredHamiltonian_quadForm_core {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (u : colouredCore N D) :
    quadForm (colouredHamiltonian Φ fabc N C) u
      = ∑ i : Fin N, (quadForm (ymHamiltonian Φ fabc)
            ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
          + (∑ j : Fin N, C i j * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
              (WithLp.ofLp (u : colourSpace N) j)).re) := by
  rw [quadForm, colouredHamiltonian_inner_core, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.add_re, quadForm]

/-- **An off-diagonal colour matrix in closed form**: with `C = [[0, 1], [1, 0]]` the two colour
components exchange and the form is the two field forms plus the cross term `2 Re ⟨u₀, u₁⟩`.
No diagonal `µ • 1` produces that term, so the off-diagonal part is seen in the form itself. -/
theorem colouredHamiltonian_swap_quadForm {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (u : colouredCore 2 D) :
    quadForm (colouredHamiltonian Φ fabc 2 !![0, 1; 1, 0]) u
      = quadForm (ymHamiltonian Φ fabc)
          ⟨WithLp.ofLp (u : colourSpace 2) 0, u.2 0⟩
        + quadForm (ymHamiltonian Φ fabc)
            ⟨WithLp.ofLp (u : colourSpace 2) 1, u.2 1⟩
        + 2 * (inner ℂ (WithLp.ofLp (u : colourSpace 2) 0)
            (WithLp.ofLp (u : colourSpace 2) 1)).re := by
  rw [colouredHamiltonian_quadForm_core, Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (inner ℂ (WithLp.ofLp (u : colourSpace 2) 1)
      (WithLp.ofLp (u : colourSpace 2) 0)).re
      = (inner ℂ (WithLp.ofLp (u : colourSpace 2) 0)
        (WithLp.ofLp (u : colourSpace 2) 1)).re from by
    rw [← inner_conj_symm, Complex.conj_re]]
  ring

/-- **The diagonal colour coefficient is real for a Hermitian matrix**: `(C_ii ⟨x, x⟩).re` is
`(C_ii).re ‖x‖²`, because `⟨x, x⟩ = ‖x‖²` is real. -/
theorem colourDiag_re {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (x : L2d 99) (i : Fin N) :
    (C i i * inner ℂ x x).re = (C i i).re * ‖x‖ ^ 2 := by
  have h : inner ℂ x x = (↑‖x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  rw [h, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- **The colour term of the form is real for a Hermitian colour matrix**: the double sum
`Σ_i Σ_j C_ij ⟨u_i, u_j⟩` equals its own star.  Transposing the entry and the inner product at
once — `C_ij ↦ C_ji`, which Hermiticity identifies with `conj C_ij`, and `⟨u_i, u_j⟩ ↦
⟨u_j, u_i⟩ = conj ⟨u_i, u_j⟩` — is the substitution `i ↔ j` of the double sum, so the sum is fixed
by conjugation. -/
theorem colourTerm_star_eq {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → L2d 99)
    (hC : C.conjTranspose = C) :
    star (∑ i, ∑ j, C i j * inner ℂ (u i) (u j))
      = ∑ i, ∑ j, C i j * inner ℂ (u i) (u j) := by
  have key : star (∑ i, ∑ j, C i j * inner ℂ (u i) (u j))
      = ∑ i, ∑ j, C j i * inner ℂ (u j) (u i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have his : star (inner ℂ (u i) (u j)) = inner ℂ (u j) (u i) := by simp
    have hc : star (C i j) = C j i := by
      rw [← Matrix.conjTranspose_apply, hC]
    rw [StarMul.star_mul, his, hc, mul_comm]
  rw [key, Finset.sum_comm]

/-- **The off-diagonal pair contribution is symmetric**: for a Hermitian `C` the `(j, i)` term is
the `(i, j)` one, so the off-diagonal part of the colour term is a sum over unordered pairs, each
counted twice with the same real value. -/
theorem colourPair_re_symm {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → L2d 99)
    (hC : C.conjTranspose = C) (i j : Fin N) :
    (C j i * inner ℂ (u j) (u i)).re = (C i j * inner ℂ (u i) (u j)).re := by
  have h1 : C j i = star (C i j) := by
    rw [← Matrix.conjTranspose_apply, hC]
  have h2 : inner ℂ (u j) (u i) = star (inner ℂ (u i) (u j)) := by simp
  rw [h1, h2, ← StarMul.star_mul]
  have h3 : (star (inner ℂ (u i) (u j) * C i j)).re
      = (inner ℂ (u i) (u j) * C i j).re :=
    Complex.conj_re (inner ℂ (u i) (u j) * C i j)
  rw [h3, mul_comm (C i j) (inner ℂ (u i) (u j))]

/-- **The off-diagonal colour sum is twice its `i < j` part**: for a Hermitian colour matrix the
ordered pairs `(i, j)` and `(j, i)` contribute the same real value, so the sum over `j ≠ i` counts
each unordered pair twice. -/
theorem colourPairSum_eq_two_mul_upper {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (u : Fin N → L2d 99) (hC : C.conjTranspose = C) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        (C i j * inner ℂ (u i) (u j)).re
      = 2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (C i j * inner ℂ (u i) (u j)).re := by
  set g : Fin N → Fin N → ℝ := fun i j => (C i j * inner ℂ (u i) (u j)).re with hg
  have hsymm : ∀ i j : Fin N, g j i = g i j := fun i j => colourPair_re_symm C u hC i j
  -- The `erase` of the diagonal splits into the two strict orderings.
  have hsplit : ∀ i : Fin N,
      ∑ j ∈ Finset.univ.erase i, g i j
        = ∑ j ∈ Finset.univ.filter (fun j => i < j), g i j
          + ∑ j ∈ Finset.univ.filter (fun j => j < i), g i j := by
    intro i
    have hpos : (Finset.univ.erase i).filter (fun j => i < j)
        = Finset.univ.filter (fun j => i < j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        refine ⟨?_, h⟩
        simp only [Fin.lt_def] at h
        omega
    have hneg : (Finset.univ.erase i).filter (fun j => ¬ i < j)
        = Finset.univ.filter (fun j => j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
        Fin.lt_def]
      omega
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ.erase i)
      (p := fun j => i < j), hpos, hneg]
  -- The two orderings are interchanged by `i ↔ j`, with the same value by symmetry.
  have hif_lo : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => j < i), g i j
      = ∑ i : Fin N, ∑ j : Fin N, (if j < i then g i j else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
  have hif_up : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g i j
      = ∑ i : Fin N, ∑ j : Fin N, (if i < j then g i j else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
  have hswap : ∑ i : Fin N, ∑ j : Fin N, (if j < i then g i j else 0)
      = ∑ i : Fin N, ∑ j : Fin N, (if i < j then g i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : a < b
    · simp only [h, g, if_true]
      exact hsymm a b
    · simp [h]
  calc ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g i j
      = ∑ i : Fin N, (∑ j ∈ Finset.univ.filter (fun j => i < j), g i j
          + ∑ j ∈ Finset.univ.filter (fun j => j < i), g i j) :=
        Finset.sum_congr rfl fun i _ => hsplit i
    _ = (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g i j)
          + ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => j < i), g i j :=
        Finset.sum_add_distrib
    _ = (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g i j)
          + ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g i j := by
        rw [hif_lo, hswap, ← hif_up]
    _ = 2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g i j :=
        (two_mul _).symm

/-- **The coloured form split into its diagonal and off-diagonal colour parts**: the diagonal
contribution is `(C_ii).re ‖u_i‖²` and the off-diagonal one is the real part of the off-diagonal
entries.  No symmetry of `C` is used; for a Hermitian `C` the diagonal coefficient is real
(`colourDiag_re`) and the two orientations of each off-diagonal pair agree
(`colourPair_re_symm`), so this is the form's real symmetric split. -/
theorem colouredHamiltonian_quadForm_re_split {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (u : colouredCore N D) :
    quadForm (colouredHamiltonian Φ fabc N C) u
      = ∑ i : Fin N, (quadForm (ymHamiltonian Φ fabc)
            ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
          + (C i i).re * ‖WithLp.ofLp (u : colourSpace N) i‖ ^ 2)
        + ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
            (C i j * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
              (WithLp.ofLp (u : colourSpace N) j)).re := by
  rw [colouredHamiltonian_quadForm_core]
  have hsplit : ∀ i : Fin N,
      (∑ j : Fin N, C i j * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
        (WithLp.ofLp (u : colourSpace N) j)).re
        = (C i i).re * ‖WithLp.ofLp (u : colourSpace N) i‖ ^ 2
          + ∑ j ∈ Finset.univ.erase i,
              (C i j * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
                (WithLp.ofLp (u : colourSpace N) j)).re := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Complex.add_re,
      Complex.re_sum, colourDiag_re]
  simp only [hsplit]
  simp only [Finset.sum_add_distrib, add_assoc]

/-- **The coloured Hamiltonian is symmetric on the coloured core** for a Hermitian colour matrix:
`⟪(H ⊗ 1 + 1 ⊗ C) u, v⟫ = ⟪u, (H ⊗ 1 + 1 ⊗ C) v⟫`. -/
theorem colouredHamiltonian_symmetricOn {D : Submodule ℂ (L2d 99)} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : C.conjTranspose = C) :
    SymmetricOn (colouredCore N D) (colouredHamiltonian Φ fabc N C) := by
  intro u v
  have hcomp : ∀ (w : colouredCore N D) (i : Fin N),
      (colouredHamiltonian Φ fabc N C w : colourSpace N).ofLp i
        = ymHamiltonian Φ fabc ⟨WithLp.ofLp (w : colourSpace N) i, w.2 i⟩
          + ∑ j : Fin N, C i j • WithLp.ofLp (w : colourSpace N) j :=
    fun w i => colouredHamiltonian_ofLp Φ fabc C w i
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [hcomp, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  have h1 : (∑ i : Fin N, (inner ℂ
        (ymHamiltonian Φ fabc ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩)
        (WithLp.ofLp (v : colourSpace N) i) : ℂ))
      = ∑ i : Fin N, (inner ℂ (WithLp.ofLp (u : colourSpace N) i)
          (ymHamiltonian Φ fabc ⟨WithLp.ofLp (v : colourSpace N) i, v.2 i⟩) : ℂ) :=
    Finset.sum_congr rfl fun i _ => ymHamiltonian_symmetricOn Φ fabc
      ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩
      ⟨WithLp.ofLp (v : colourSpace N) i, v.2 i⟩
  have hstep : ∀ i j : Fin N,
      star (C i j) * inner ℂ (WithLp.ofLp (u : colourSpace N) j)
          (WithLp.ofLp (v : colourSpace N) i)
        = C j i * inner ℂ (WithLp.ofLp (u : colourSpace N) j)
            (WithLp.ofLp (v : colourSpace N) i) := by
    intro i j
    rw [← Matrix.conjTranspose_apply, hC]
  have h2 : (∑ i : Fin N, ∑ j : Fin N,
        star (C i j) * inner ℂ (WithLp.ofLp (u : colourSpace N) j)
          (WithLp.ofLp (v : colourSpace N) i))
      = ∑ i : Fin N, ∑ j : Fin N, C i j * inner ℂ (WithLp.ofLp (u : colourSpace N) i)
          (WithLp.ofLp (v : colourSpace N) j) := by
    simp only [hstep]
    rw [Finset.sum_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1]
  exact add_left_cancel_iff.mpr h2

/-! #### The colour singlet over the combined `ℂ² ⊗ ℂ³` fibre

The two colour factors of the sections above are exactly the two irreps a colour-singlet
question has to put together: the fundamental `ℂ²` (`C_F = 3/4`) and the adjoint `ℂ³`
(`C_A = 2`).  Over one field core they are a single fibre of six colour components,
`colourVec 6`, the colour index being row-major — `3 * (fundamental slot) + (adjoint slot)`
(`pairSlotFst`, `pairSlotSnd`).  The total colour action on that fibre is the Kronecker sum
`A^a = T^a ⊗ 1 + 1 ⊗ T^a` (`pairRep`), and the **colour-singlet space** `colourSinglet` is
the part of the fibre that action annihilates: the vectors of vanishing total colour charge.

`colourSinglet_eq_bot` is the content — **it is `{0}`**.  The total action has no invariant
vector in `ℂ² ⊗ ℂ³`: `2 ⊗ 3 = 4 ⊕ 2` is a quartet and a doublet with no trivial
summand, so a fundamental mode and an adjoint mode over one field core cannot be
colour-neutral together.  The computation needs six diagonal entries, two from each action:
`A^0` kills `v 3` and `v 0`, `A^1` kills `v 4` and `v 1`, `A^2` kills `v 5` and `v 2`.  In
fibre language the singlet is trivial over *every* field core
(`colourSinglet_fibre_trivial`);  that is the fibre form of the same six-entry computation.

The total action is also a **representation**: `[A^a, A^b] = i ε^{abc}A^c`
(`pairRep_commutator`), the total-colour counterpart of `[T^a, T^b] = i ε^{abc}T^c`.  The proof
is not a `6 × 6` entry check.  On the product basis (`pairRepProd`) the product of two actions is
the four-term expansion `pairRepProd_mul`, and the two *mixed* terms `T^a ⊗ T^b`, `T^b ⊗ T^a` are
equal in the two orders, so they cancel and only the two factor commutators survive
(`pairRepProd_commutator`); `pairEquiv` is the row-major relabelling that carries this back to
`pairRep` (`pairRep_eq_reindex`).

**Boundary.**  Built here: the singlet space of the fundamental/adjoint pair, the fact that it
is trivial, and the representation property of the total action.  Not built: the decomposition
of `ℂ² ⊗ ℂ³` into its two irreducible summands.  The pairs that *do* carry a singlet —
`ℂ² ⊗ ℂ²`, the meson, and `ℂ³ ⊗ ℂ³`, the glueball — are the next section.
-/

/-- The fundamental slot of a colour index in the combined `ℂ² ⊗ ℂ³` fibre: `i / 3`. -/
def pairSlotFst (i : Fin 6) : Fin 2 := ⟨i.val / 3, by have := i.isLt; omega⟩

/-- The adjoint slot of a colour index in the combined `ℂ² ⊗ ℂ³` fibre: `i % 3`. -/
def pairSlotSnd (i : Fin 6) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- **The total colour action on `ℂ² ⊗ ℂ³`**: the Kronecker sum `T^a ⊗ 1 + 1 ⊗ T^a` in the row-major
basis of the combined fibre, so that the first factor acts on the fundamental slot and the second on
the adjoint slot. -/
noncomputable def pairRep (a : Fin 3) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => fundRep a (pairSlotFst i) (pairSlotFst j) *
      (if pairSlotSnd i = pairSlotSnd j then 1 else 0) +
    (if pairSlotFst i = pairSlotFst j then 1 else 0) * adjRep a (pairSlotSnd i) (pairSlotSnd j)

/-- **The total colour action in the product basis.**  `pairRep` read on the pair of colour slots
rather than on the row-major colour index: the Kronecker sum `T^a ⊗ 1 + 1 ⊗ T^a` built from
`Matrix.kroneckerMap`, so that the two factors are visibly separate. -/
noncomputable def pairRepProd (a : Fin 3) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  Matrix.kroneckerMap (· * ·) (fundRep a) (1 : Matrix (Fin 3) (Fin 3) ℂ) +
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (adjRep a)

/-- **A product of two total actions**: the two same-slot products `T^a T^b ⊗ 1`, `1 ⊗ T^a T^b`
and the two mixed ones `T^a ⊗ T^b`, `T^b ⊗ T^a`.  The mixed terms are what cancel in the
commutator. -/
theorem pairRepProd_mul (a b : Fin 3) :
    pairRepProd a * pairRepProd b
      = Matrix.kroneckerMap (· * ·) (fundRep a * fundRep b) (1 : Matrix (Fin 3) (Fin 3) ℂ)
        + Matrix.kroneckerMap (· * ·) (fundRep a) (adjRep b)
        + Matrix.kroneckerMap (· * ·) (fundRep b) (adjRep a)
        + Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (adjRep a * adjRep b) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp [pairRepProd, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  ring

/-- **The Kronecker sum is a representation**: `[T^a ⊗ 1 + 1 ⊗ T^a, T^b ⊗ 1 + 1 ⊗ T^b] = i ε^{abc}
(T^c ⊗ 1 + 1 ⊗ T^c)`.  By `pairRepProd_mul` the two mixed products are the same in the two
orders, so the difference is `[T^a, T^b] ⊗ 1 + 1 ⊗ [T^a, T^b]`, and `fundRep_commutator` with
`adjRep_commutator` finish. -/
theorem pairRepProd_commutator (a b : Fin 3) :
    pairRepProd a * pairRepProd b - pairRepProd b * pairRepProd a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • pairRepProd c) := by
  have hsub1 :
      Matrix.kroneckerMap (· * ·) (fundRep a * fundRep b)
          (1 : Matrix (Fin 3) (Fin 3) ℂ)
        - Matrix.kroneckerMap (· * ·) (fundRep b * fundRep a)
            (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = Matrix.kroneckerMap (· * ·) (fundRep a * fundRep b - fundRep b * fundRep a)
          (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext p q
    simp [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.one_apply]
    split <;> ring
  have hsub4 :
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
          (adjRep a * adjRep b)
        - Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (adjRep b * adjRep a)
      = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
          (adjRep a * adjRep b - adjRep b * adjRep a) := by
    ext p q
    simp [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.one_apply]
    split <;> ring
  have hkey :
      pairRepProd a * pairRepProd b - pairRepProd b * pairRepProd a
        = Matrix.kroneckerMap (· * ·) (fundRep a * fundRep b - fundRep b * fundRep a)
            (1 : Matrix (Fin 3) (Fin 3) ℂ)
          + Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (adjRep a * adjRep b - adjRep b * adjRep a) := by
    rw [pairRepProd_mul a b, pairRepProd_mul b a,
      show
        (Matrix.kroneckerMap (· * ·) (fundRep a * fundRep b)
            (1 : Matrix (Fin 3) (Fin 3) ℂ)
          + Matrix.kroneckerMap (· * ·) (fundRep a) (adjRep b)
          + Matrix.kroneckerMap (· * ·) (fundRep b) (adjRep a)
          + Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
              (adjRep a * adjRep b))
        - (Matrix.kroneckerMap (· * ·) (fundRep b * fundRep a)
            (1 : Matrix (Fin 3) (Fin 3) ℂ)
          + Matrix.kroneckerMap (· * ·) (fundRep b) (adjRep a)
          + Matrix.kroneckerMap (· * ·) (fundRep a) (adjRep b)
          + Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
              (adjRep b * adjRep a))
        = (Matrix.kroneckerMap (· * ·) (fundRep a * fundRep b)
              (1 : Matrix (Fin 3) (Fin 3) ℂ)
            - Matrix.kroneckerMap (· * ·) (fundRep b * fundRep a)
              (1 : Matrix (Fin 3) (Fin 3) ℂ))
          + (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
                (adjRep a * adjRep b)
            - Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
                (adjRep b * adjRep a)) from by abel,
      hsub1, hsub4]
  have hfinal :
      Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • pairRepProd c)
        = Matrix.kroneckerMap (· * ·)
            (Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • fundRep c))
            (1 : Matrix (Fin 3) (Fin 3) ℂ)
          + Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • adjRep c)) := by
    ext p q
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only [pairRepProd, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib, mul_add]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hkey, fundRep_commutator a b, adjRep_commutator a b, ← hfinal]

/-- The row-major relabelling of the combined fibre: `(fundamental slot, adjoint slot) ↦
3 * fundamental + adjoint`, i.e. `pairSlotFst`/`pairSlotSnd` read backwards. -/
noncomputable def pairEquiv : Fin 2 × Fin 3 ≃ Fin 6 where
  toFun p := ⟨3 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun i := (pairSlotFst i, pairSlotSnd i)
  left_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · simp [pairSlotFst]
      omega
    · simp [pairSlotSnd]
  right_inv i := by
    ext
    simp only [pairSlotFst, pairSlotSnd]
    omega

/-- **`pairRep` is `pairRepProd` transported along `pairEquiv`**: the row-major colour index of the
combined fibre is the product basis read through the relabelling, so the two definitions of the
total action agree. -/
theorem pairRep_eq_reindex (a : Fin 3) :
    pairRep a = Matrix.reindex pairEquiv pairEquiv (pairRepProd a) := by
  ext i j
  simp [pairRep, pairRepProd, pairEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.add_apply, Matrix.one_apply, pairSlotFst, pairSlotSnd]

/-- **`pairRep` is a representation of `su(2)` on the combined fibre**: the total colour actions
obey `[A^a, A^b] = i ε^{abc}A^c`, the total-colour form of `[T^a, T^b] = i ε^{abc}T^c`.  Nothing
is computed entrywise: `pairRepProd_commutator` is the content and `pairEquiv` is an algebra
equivalence, so the identity transports to `colourVec 6`. -/
theorem pairRep_commutator (a b : Fin 3) :
    pairRep a * pairRep b - pairRep b * pairRep a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • pairRep c) := by
  simp only [pairRep_eq_reindex, ← Matrix.reindexAlgEquiv_apply ℂ ℂ pairEquiv]
  simp only [← map_mul, ← map_sub, ← map_smul, ← map_sum]
  rw [pairRepProd_commutator]

/-- **The colour-singlet space** of the combined `ℂ² ⊗ ℂ³` fibre: the vectors annihilated by
every one of the three total colour actions. -/
noncomputable def colourSinglet : Submodule ℂ (colourVec 6) where
  carrier := {v | ∀ a, (pairRep a).mulVec (WithLp.ofLp v) = 0}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro u w hu hw a
    rw [WithLp.ofLp_add, Matrix.mulVec_add, hu a, hw a, add_zero]
  smul_mem' := by
    intro c u hu a
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, hu a, smul_zero]

/-- Membership in `colourSinglet` is annihilation by all three total colour actions. -/
theorem colourSinglet_mem (v : colourVec 6) :
    v ∈ colourSinglet ↔ ∀ a, (pairRep a).mulVec (WithLp.ofLp v) = 0 := Iff.rfl

/-- **The singlet space of `ℂ² ⊗ ℂ³` is trivial**: a vector whose total colour charge vanishes is
zero.  The six diagonal entries of the three total actions already force every coordinate to vanish,
which is the `su(2)` fact `2 ⊗ 3 = 4 ⊕ 2` — no trivial summand. -/
theorem colourSinglet_eq_bot : colourSinglet = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [colourSinglet_mem] at hv
  have h0 : WithLp.ofLp v 0 = 0 := by
    simpa [pairRep, Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairSlotFst, pairSlotSnd,
      fundRep, pauli, adjRep, levi] using congrFun (hv 0) 3
  have h1 : WithLp.ofLp v 1 = 0 := by
    simpa [pairRep, Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairSlotFst, pairSlotSnd,
      fundRep, pauli, adjRep, levi] using congrFun (hv 1) 4
  have h2 : WithLp.ofLp v 2 = 0 := by
    simpa [pairRep, Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairSlotFst, pairSlotSnd,
      fundRep, pauli, adjRep, levi] using congrFun (hv 2) 2
  have h3 : WithLp.ofLp v 3 = 0 := by
    simpa [pairRep, Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairSlotFst, pairSlotSnd,
      fundRep, pauli, adjRep, levi] using congrFun (hv 0) 0
  have h4 : WithLp.ofLp v 4 = 0 := by
    simpa [pairRep, Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairSlotFst, pairSlotSnd,
      fundRep, pauli, adjRep, levi] using congrFun (hv 1) 1
  have h5 : WithLp.ofLp v 5 = 0 := by
    simpa [pairRep, Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairSlotFst, pairSlotSnd,
      fundRep, pauli, adjRep, levi] using congrFun (hv 2) 5
  apply WithLp.ofLp_injective
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- **No colour singlet over a field core**: a singlet of the combined fibre, placed over any field
core `x`, is the zero element — the fibre carries no colour-neutral vector to begin with. -/
theorem colourSinglet_fibre_trivial {D : Submodule ℂ (L2d 99)} (x : D) (v : colourVec 6)
    (hv : v ∈ colourSinglet) : colourFibre (D := D) x v = 0 := by
  have hzero : v = 0 := by
    rw [colourSinglet_eq_bot] at hv
    simpa using hv
  rw [hzero]
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext i
  simp [colourFibre]

/-! #### The meson and glueball singlets: `ℂ² ⊗ ℂ²` and `ℂ³ ⊗ ℂ³`

The fundamental/adjoint pair has no singlet (previous section).  The pairs that do carry one are the
two *squares*, and both are built here the same way: the total action `T^a ⊗ 1 + 1 ⊗ T^a`, with the
same irrep in both slots.

* **Meson**, `ℂ² ⊗ ℂ²` — `mesonRep` on `colourVec 4`, colour index `2 * fst + snd`.  The
  antisymmetric tensor `ε` (`mesonCoeff`, `mesonSingletVec`) is annihilated by all three total
  actions (`mesonCoeff_mem`), and the singlet space is exactly the line it spans
  (`mesonSinglet_eq_span`): `2 ⊗ 2 = 3 ⊕ 1`, one singlet, antisymmetric — the quark–antiquark
  channel, the two colour indices contracted with `ε`.
* **Glueball**, `ℂ³ ⊗ ℂ³` — `glueballRep` on `colourVec 9`, colour index `3 * fst + snd`.  The
  trace `δ` (`glueballCoeff`, `glueballSingletVec`) is a singlet (`glueballCoeff_mem`), and again
  the singlet space is exactly its line (`glueballSinglet_eq_span`): `3 ⊗ 3 = 5 ⊕ 3 ⊕ 1`, the
  singlet being `Σ_a |a⟩|a⟩` — a trace because the adjoint generators are antisymmetric.

Both singlet vectors are nonzero (`mesonSingletVec_ne_zero`, `glueballSingletVec_ne_zero`), so
neither space is trivial.  That contrast with `colourSinglet_eq_bot` is the point of the section:
whether a colour-neutral state exists is a property of the *pair of irreps*, not of the colour
group.

Both total actions are also **representations** of `su(2)`: `[T^a ⊗ 1 + 1 ⊗ T^a, T^b ⊗ 1 + 1 ⊗ T^b]
= i ε^{abc}(T^c ⊗ 1 + 1 ⊗ T^c)` (`mesonRep_commutator`, `glueballRep_commutator`), proved on the
product basis and transported along the row-major relabelling, not entrywise.

**Boundary.**  Each singlet space is proved to be exactly one line, by exhibiting the invariant
vector and showing that the common kernel of the three total actions has no other direction.  The
meson square is split completely: `meson_isCompl` gives `ℂ² ⊗ ℂ² = mesonAlt ⊕ mesonSymm` with
`1` and `3` dimensions, both invariant.  For the glueball square only the antisymmetric/symmetric
separation is not carried out here, so `3 ⊗ 3 = 5 ⊕ 3 ⊕ 1` is not yet a decomposition of
submodules in this chapter — the trace line is proved to be a singlet, but no complement inside the
traceless symmetric part, and no `Λ²` summand, is exhibited.  Also not claimed: norms or
closedness of these actions.  The singlet proofs are coordinate checks —
`glueballRep_zero_mulVec` and its siblings give the three total actions of the glueball fibre in
closed form — not a Clebsch–Gordan expansion.
-/

/-- The fundamental slot of a colour index in `ℂ² ⊗ ℂ²`: `i / 2`. -/
def mesonSlotFst (i : Fin 4) : Fin 2 := ⟨i.val / 2, by have := i.isLt; omega⟩

/-- The second fundamental slot of a colour index in `ℂ² ⊗ ℂ²`: `i % 2`. -/
def mesonSlotSnd (i : Fin 4) : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The adjoint slot of a colour index in `ℂ³ ⊗ ℂ³`: `i / 3`. -/
def glueballSlotFst (i : Fin 9) : Fin 3 := ⟨i.val / 3, by have := i.isLt; omega⟩

/-- The second adjoint slot of a colour index in `ℂ³ ⊗ ℂ³`: `i % 3`. -/
def glueballSlotSnd (i : Fin 9) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- **The total colour action on `ℂ² ⊗ ℂ²`**: the Kronecker sum `T^a ⊗ 1 + 1 ⊗ T^a` of the
fundamental generators, in the row-major basis of the four-component fibre. -/
noncomputable def mesonRep (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => fundRep a (mesonSlotFst i) (mesonSlotFst j) *
      (if mesonSlotSnd i = mesonSlotSnd j then 1 else 0) +
    (if mesonSlotFst i = mesonSlotFst j then 1 else 0) *
      fundRep a (mesonSlotSnd i) (mesonSlotSnd j)

/-- **The total colour action on `ℂ³ ⊗ ℂ³`**: the Kronecker sum `T^a ⊗ 1 + 1 ⊗ T^a` of the
adjoint generators, in the row-major basis of the nine-component fibre. -/
noncomputable def glueballRep (a : Fin 3) : Matrix (Fin 9) (Fin 9) ℂ :=
  fun i j => adjRep a (glueballSlotFst i) (glueballSlotFst j) *
      (if glueballSlotSnd i = glueballSlotSnd j then 1 else 0) +
    (if glueballSlotFst i = glueballSlotFst j then 1 else 0) *
      adjRep a (glueballSlotSnd i) (glueballSlotSnd j)

/-! ##### The two total actions are representations

`mesonRep` and `glueballRep` are each a **Kronecker sum** `T^a ⊗ 1 + 1 ⊗ T^a` of one irrep with
itself, so neither representation property is a `4 × 4` or `9 × 9` entry check: it is the general
fact that a Kronecker sum of two representations is a representation.  `kronSum` is that total
action on a product basis, over an arbitrary index type; `kronSum_mul` multiplies two of them (the
mixed `T^a ⊗ T^b` terms appear in both orders), and `kronSum_commutator_gen` is the abstract
commutator: if the one-slot families commute up to `X` and `Y`, so does the Kronecker sum.  The
mixed terms cancel there because they occur in both orders, not because of any property of `su(2)`;
only the corollary `kronSum_commutator` puts `[T^a, T^b] = i ε^{abc}T^c` in both slots and
absorbs the structure-constant sum.  The row-major relabellings `mesonEquiv`/`glueballEquiv` carry
that to `colourVec 4`/`colourVec 9`, so `mesonRep_commutator` and `glueballRep_commutator` are
transport along an algebra equivalence.
-/

/-- The Kronecker sum of two families of matrices, indexed by an arbitrary type: nothing here
sees `su(2)` or the structure constants. -/
noncomputable def kronSum {κ m n : Type*} [DecidableEq m] [DecidableEq n]
    (T : κ → Matrix m m ℂ) (S : κ → Matrix n n ℂ)
    (a : κ) : Matrix (m × n) (m × n) ℂ :=
  Matrix.kroneckerMap (· * ·) (T a) (1 : Matrix n n ℂ) +
    Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S a)

/-- The Kronecker product of a product is the product of the Kronecker products. -/
theorem kronMap_mul {m n : Type*} [Fintype m] [Fintype n]
    (A A' : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    Matrix.kroneckerMap (· * ·) A B * Matrix.kroneckerMap (· * ·) A' B'
      = Matrix.kroneckerMap (· * ·) (A * A') (B * B') := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The Kronecker product of a difference, on the left factor. -/
theorem kronMap_sub {m n : Type*}
    (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A' B
      = Matrix.kroneckerMap (· * ·) (A - A') B := by
  ext p q
  simp [Matrix.sub_apply, sub_mul]

/-- The Kronecker product of a difference, on the right factor. -/
theorem kronMap_sub_right {m n : Type*}
    (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A B'
      = Matrix.kroneckerMap (· * ·) A (B - B') := by
  ext p q
  simp [Matrix.sub_apply, mul_sub]

/-- **A product of two Kronecker sums**: the two same-slot products and the two mixed ones. -/
theorem kronSum_mul {κ m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (T : κ → Matrix m m ℂ) (S : κ → Matrix n n ℂ) (a b : κ) :
    kronSum T S a * kronSum T S b
      = Matrix.kroneckerMap (· * ·) (T a * T b) (1 : Matrix n n ℂ)
        + Matrix.kroneckerMap (· * ·) (T a) (S b)
        + Matrix.kroneckerMap (· * ·) (T b) (S a)
        + Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S a * S b) := by
  unfold kronSum
  rw [add_mul, mul_add, mul_add, kronMap_mul, kronMap_mul, kronMap_mul, kronMap_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- **The commutator of a Kronecker sum, with no structure constants in sight**: if the
one-slot families `T` and `S` commute up to arbitrary matrices `X` and `Y`, then the Kronecker
sum commutes up to the two Kronecker products.  The two mixed terms `T a ⊗ S b` and `T b ⊗ S a`
appear in both products in both orders, so they cancel; nothing else is used. -/
theorem kronSum_commutator_gen {κ m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (T : κ → Matrix m m ℂ) (S : κ → Matrix n n ℂ)
    (X : κ → κ → Matrix m m ℂ) (Y : κ → κ → Matrix n n ℂ)
    (hT : ∀ a b, T a * T b - T b * T a = X a b)
    (hS : ∀ a b, S a * S b - S b * S a = Y a b) (a b : κ) :
    kronSum T S a * kronSum T S b - kronSum T S b * kronSum T S a
      = Matrix.kroneckerMap (· * ·) (X a b) (1 : Matrix n n ℂ)
        + Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (Y a b) := by
  have hkey :
      kronSum T S a * kronSum T S b - kronSum T S b * kronSum T S a
        = Matrix.kroneckerMap (· * ·) (T a * T b) (1 : Matrix n n ℂ)
            - Matrix.kroneckerMap (· * ·) (T b * T a) (1 : Matrix n n ℂ)
          + (Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S a * S b)
            - Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S b * S a)) := by
    have hab :
        Matrix.kroneckerMap (· * ·) (T a * T b) (1 : Matrix n n ℂ)
            + Matrix.kroneckerMap (· * ·) (T a) (S b)
            + Matrix.kroneckerMap (· * ·) (T b) (S a)
            + Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S a * S b)
          - (Matrix.kroneckerMap (· * ·) (T b * T a) (1 : Matrix n n ℂ)
            + Matrix.kroneckerMap (· * ·) (T b) (S a)
            + Matrix.kroneckerMap (· * ·) (T a) (S b)
            + Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S b * S a))
        = (Matrix.kroneckerMap (· * ·) (T a * T b) (1 : Matrix n n ℂ)
              - Matrix.kroneckerMap (· * ·) (T b * T a) (1 : Matrix n n ℂ))
          + (Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S a * S b)
              - Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) (S b * S a)) := by
      abel
    rw [kronSum_mul T S a b, kronSum_mul T S b a, hab]
  rw [hkey, kronMap_sub, kronMap_sub_right, hT a b, hS a b]

/-- **The Kronecker sum is a representation** of `su(2)` whenever both factors are. -/
theorem kronSum_commutator {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (T : Fin 3 → Matrix m m ℂ) (S : Fin 3 → Matrix n n ℂ)
    (hT : ∀ a b : Fin 3,
      T a * T b - T b * T a = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • T c))
    (hS : ∀ a b : Fin 3,
      S a * S b - S b * S a = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • S c))
    (a b : Fin 3) :
    kronSum T S a * kronSum T S b - kronSum T S b * kronSum T S a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • kronSum T S c) := by
  have hgen := kronSum_commutator_gen T S
    (fun a b => Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • T c))
    (fun a b => Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • S c)) hT hS a b
  have hfinal :
      Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • kronSum T S c)
        = Matrix.kroneckerMap (· * ·)
            (Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • T c)) (1 : Matrix n n ℂ)
          + Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ)
            (Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • S c)) := by
    ext p q
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only [kronSum, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib, mul_add]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hgen, ← hfinal]

/-- The row-major relabelling `ℂ² ⊗ ℂ² → ℂ⁴`. -/
noncomputable def mesonEquiv : Fin 2 × Fin 2 ≃ Fin 4 where
  toFun p := ⟨2 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun i := (mesonSlotFst i, mesonSlotSnd i)
  left_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · simp [mesonSlotFst]
      omega
    · simp [mesonSlotSnd]
  right_inv i := by
    ext
    simp only [mesonSlotFst, mesonSlotSnd]
    omega

/-- `mesonRep` is the Kronecker sum of two fundamental actions, in row-major order. -/
theorem mesonRep_eq_reindex (a : Fin 3) :
    mesonRep a = Matrix.reindex mesonEquiv mesonEquiv (kronSum fundRep fundRep a) := by
  ext i j
  simp [mesonRep, kronSum, mesonEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.add_apply, Matrix.one_apply, mesonSlotFst, mesonSlotSnd]

/-- **`mesonRep` is a representation of `su(2)` on `ℂ² ⊗ ℂ²`.** -/
theorem mesonRep_commutator (a b : Fin 3) :
    mesonRep a * mesonRep b - mesonRep b * mesonRep a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • mesonRep c) := by
  simp only [mesonRep_eq_reindex, ← Matrix.reindexAlgEquiv_apply ℂ ℂ mesonEquiv]
  simp only [← map_mul, ← map_sub, ← map_smul, ← map_sum]
  rw [kronSum_commutator fundRep fundRep fundRep_commutator fundRep_commutator]

/-- The row-major relabelling `ℂ³ ⊗ ℂ³ → ℂ⁹`. -/
noncomputable def glueballEquiv : Fin 3 × Fin 3 ≃ Fin 9 where
  toFun p := ⟨3 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun i := (glueballSlotFst i, glueballSlotSnd i)
  left_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · simp [glueballSlotFst]
      omega
    · simp [glueballSlotSnd]
  right_inv i := by
    ext
    simp only [glueballSlotFst, glueballSlotSnd]
    omega

/-- `glueballRep` is the Kronecker sum of two adjoint actions, in row-major order. -/
theorem glueballRep_eq_reindex (a : Fin 3) :
    glueballRep a = Matrix.reindex glueballEquiv glueballEquiv (kronSum adjRep adjRep a) := by
  ext i j
  simp [glueballRep, kronSum, glueballEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.add_apply, Matrix.one_apply, glueballSlotFst, glueballSlotSnd]

/-- **`glueballRep` is a representation of `su(2)` on `ℂ³ ⊗ ℂ³`.** -/
theorem glueballRep_commutator (a b : Fin 3) :
    glueballRep a * glueballRep b - glueballRep b * glueballRep a
      = Complex.I • (∑ c : Fin 3, (levi a b c : ℂ) • glueballRep c) := by
  simp only [glueballRep_eq_reindex, ← Matrix.reindexAlgEquiv_apply ℂ ℂ glueballEquiv]
  simp only [← map_mul, ← map_sub, ← map_smul, ← map_sum]
  rw [kronSum_commutator adjRep adjRep adjRep_commutator adjRep_commutator]

/-- **The meson singlet space**: the vectors of the `ℂ² ⊗ ℂ²` fibre annihilated by every one
of the three total colour actions. -/
noncomputable def mesonSinglet : Submodule ℂ (colourVec 4) where
  carrier := {v | ∀ a, (mesonRep a).mulVec (WithLp.ofLp v) = 0}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro u w hu hw a
    rw [WithLp.ofLp_add, Matrix.mulVec_add, hu a, hw a, add_zero]
  smul_mem' := by
    intro c u hu a
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, hu a, smul_zero]

/-- **The glueball singlet space**: the vectors of the `ℂ³ ⊗ ℂ³` fibre annihilated by every one
of the three total colour actions. -/
noncomputable def glueballSinglet : Submodule ℂ (colourVec 9) where
  carrier := {v | ∀ a, (glueballRep a).mulVec (WithLp.ofLp v) = 0}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro u w hu hw a
    rw [WithLp.ofLp_add, Matrix.mulVec_add, hu a, hw a, add_zero]
  smul_mem' := by
    intro c u hu a
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, hu a, smul_zero]

/-- Membership in `mesonSinglet` is annihilation by all three total colour actions. -/
theorem mesonSinglet_mem (v : colourVec 4) :
    v ∈ mesonSinglet ↔ ∀ a, (mesonRep a).mulVec (WithLp.ofLp v) = 0 := Iff.rfl

/-- Membership in `glueballSinglet` is annihilation by all three total colour actions. -/
theorem glueballSinglet_mem (v : colourVec 9) :
    v ∈ glueballSinglet ↔ ∀ a, (glueballRep a).mulVec (WithLp.ofLp v) = 0 := Iff.rfl

/-- The antisymmetric tensor `ε` in the row-major basis of `ℂ² ⊗ ℂ²`: `ε₀₁ = 1`, `ε₁₀ = -1`. -/
def mesonCoeff : Fin 4 → ℂ := ![0, 1, -1, 0]

/-- The trace `δ` in the row-major basis of `ℂ³ ⊗ ℂ³`: `δᵢⱼ = 1` for `i = j`. -/
def glueballCoeff : Fin 9 → ℂ := ![1, 0, 0, 0, 1, 0, 0, 0, 1]

/-- The meson singlet vector: `ε` as an element of the `ℂ² ⊗ ℂ²` fibre. -/
def mesonSingletVec : colourVec 4 := WithLp.toLp 2 mesonCoeff

/-- The glueball singlet vector: `δ` as an element of the `ℂ³ ⊗ ℂ³` fibre. -/
def glueballSingletVec : colourVec 9 := WithLp.toLp 2 glueballCoeff

/-- **The antisymmetric tensor is a colour singlet** of `ℂ² ⊗ ℂ²`: all three total actions
annihilate `ε`, which is the `su(2)` tensor `2 ⊗ 2 ⊇ 1`. -/
theorem mesonCoeff_mem : mesonSingletVec ∈ mesonSinglet := by
  rw [mesonSinglet_mem]
  intro a
  ext k
  fin_cases a <;> fin_cases k <;>
    simp [mesonRep, mesonSlotFst, mesonSlotSnd, mesonSingletVec, mesonCoeff, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four, fundRep, pauli]

-- The glueball computations expand nine-term dot products of `adjRep` entries; the raised budget
-- keeps each of the nine coordinate goals inside one elaboration.
section glueballComputation

set_option maxHeartbeats 1000000

/-- **The first total colour action on `ℂ³ ⊗ ℂ³`, in closed form**: the nine components of
`(T⁰ ⊗ 1 + 1 ⊗ T⁰) v`, each one or two coordinates of `v`. -/
theorem glueballRep_zero_mulVec (v : Fin 9 → ℂ) :
    (glueballRep 0).mulVec v
      = ![0, -Complex.I * v 2, Complex.I * v 1, -Complex.I * v 6,
          Complex.I * (-v 5 - v 7), Complex.I * (v 4 - v 8), Complex.I * v 3,
          Complex.I * (v 4 - v 8), Complex.I * (v 5 + v 7)] := by
  ext k
  fin_cases k <;>
    simp [glueballRep, glueballSlotFst, glueballSlotSnd, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, adjRep, levi] <;>
    norm_num [levi] <;> ring

/-- **The second total colour action on `ℂ³ ⊗ ℂ³`, in closed form.** -/
theorem glueballRep_one_mulVec (v : Fin 9 → ℂ) :
    (glueballRep 1).mulVec v
      = ![Complex.I * (v 2 + v 6), Complex.I * v 7, Complex.I * (v 8 - v 0),
          Complex.I * v 5, 0, -Complex.I * v 3, Complex.I * (v 8 - v 0),
          -Complex.I * v 1, Complex.I * (-v 2 - v 6)] := by
  ext k
  fin_cases k <;>
    simp [glueballRep, glueballSlotFst, glueballSlotSnd, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, adjRep, levi] <;>
    norm_num [levi] <;> ring

/-- **The third total colour action on `ℂ³ ⊗ ℂ³`, in closed form.** -/
theorem glueballRep_two_mulVec (v : Fin 9 → ℂ) :
    (glueballRep 2).mulVec v
      = ![Complex.I * (-v 1 - v 3), Complex.I * (v 0 - v 4), -Complex.I * v 5,
          Complex.I * (v 0 - v 4), Complex.I * (v 1 + v 3), Complex.I * v 2,
          -Complex.I * v 7, Complex.I * v 6, 0] := by
  ext k
  fin_cases k <;>
    simp [glueballRep, glueballSlotFst, glueballSlotSnd, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, adjRep, levi] <;>
    norm_num [levi] <;> ring

/-- **The trace is a colour singlet** of `ℂ³ ⊗ ℂ³`: all three total actions annihilate `δ`,
which is the `su(2)` tensor `3 ⊗ 3 ⊇ 1` — the adjoint generators are antisymmetric, so the trace
survives. -/
theorem glueballCoeff_mem : glueballSingletVec ∈ glueballSinglet := by
  rw [glueballSinglet_mem]
  intro a
  ext k
  fin_cases a <;> fin_cases k <;>
    simp [glueballRep, glueballSlotFst, glueballSlotSnd, glueballSingletVec, glueballCoeff,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, adjRep, levi] <;>
    norm_num [levi]

end glueballComputation

/-- **The meson singlet space is one line**: every vector whose total colour charge vanishes is a
multiple of the antisymmetric tensor `ε`, which is itself a singlet (`mesonCoeff_mem`).  So the
singlet of `ℂ² ⊗ ℂ²` is one-dimensional, unlike the trivial singlet of `ℂ² ⊗ ℂ³`. -/
theorem mesonSinglet_eq_span :
    mesonSinglet = Submodule.span ℂ ({mesonSingletVec} : Set (colourVec 4)) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mesonSinglet_mem] at hv
    have h0 : WithLp.ofLp v 0 = 0 := by
      simpa [mesonRep, mesonSlotFst, mesonSlotSnd, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        fundRep, pauli] using congrFun (hv 2) 0
    have h3 : WithLp.ofLp v 3 = 0 := by
      simpa [mesonRep, mesonSlotFst, mesonSlotSnd, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        fundRep, pauli] using congrFun (hv 2) 3
    have h12 : WithLp.ofLp v 1 + WithLp.ofLp v 2 = 0 := by
      have e := congrFun (hv 0) 0
      simp [mesonRep, mesonSlotFst, mesonSlotSnd, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        fundRep, pauli] at e
      linear_combination 2 * e
    have h2 : WithLp.ofLp v 2 = -WithLp.ofLp v 1 := by
      linear_combination h12
    rw [Submodule.mem_span_singleton]
    refine ⟨WithLp.ofLp v 1, ?_⟩
    apply WithLp.ofLp_injective
    funext k
    fin_cases k <;>
      simp [mesonSingletVec, mesonCoeff, h0, h2, h3]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact mesonCoeff_mem

/-- **The glueball singlet space is one line**: every vector whose total colour charge vanishes is a
multiple of the trace `δ`, which is itself a singlet (`glueballCoeff_mem`).  So the singlet of
`ℂ³ ⊗ ℂ³` is one-dimensional — the glueball of `3 ⊗ 3 = 5 ⊕ 3 ⊕ 1`. -/
theorem glueballSinglet_eq_span :
    glueballSinglet = Submodule.span ℂ ({glueballSingletVec} : Set (colourVec 9)) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [glueballSinglet_mem] at hv
    have h2 : WithLp.ofLp v 2 = 0 := by
      have e : -Complex.I * WithLp.ofLp v 2 = 0 := by
        simpa [glueballRep_zero_mulVec] using congrFun (hv 0) 1
      exact (mul_eq_zero.mp e).resolve_left (by simp)
    have h3 : WithLp.ofLp v 3 = 0 := by
      have e : Complex.I * WithLp.ofLp v 3 = 0 := by
        simpa [glueballRep_zero_mulVec] using congrFun (hv 0) 6
      exact (mul_eq_zero.mp e).resolve_left (by simp)
    have h6 : WithLp.ofLp v 6 = 0 := by
      have e : -Complex.I * WithLp.ofLp v 6 = 0 := by
        simpa [glueballRep_zero_mulVec] using congrFun (hv 0) 3
      exact (mul_eq_zero.mp e).resolve_left (by simp)
    have h5 : WithLp.ofLp v 5 = 0 := by
      have e : Complex.I * WithLp.ofLp v 5 = 0 := by
        simpa [glueballRep_one_mulVec] using congrFun (hv 1) 3
      exact (mul_eq_zero.mp e).resolve_left (by simp)
    have h7 : WithLp.ofLp v 7 = 0 := by
      have e : Complex.I * WithLp.ofLp v 7 = 0 := by
        simpa [glueballRep_one_mulVec] using congrFun (hv 1) 1
      exact (mul_eq_zero.mp e).resolve_left (by simp)
    have h8 : WithLp.ofLp v 8 = WithLp.ofLp v 0 := by
      have e : Complex.I * (WithLp.ofLp v 8 - WithLp.ofLp v 0) = 0 := by
        simpa [glueballRep_one_mulVec] using congrFun (hv 1) 2
      exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by simp))
    have h4 : WithLp.ofLp v 4 = WithLp.ofLp v 8 := by
      have e : Complex.I * (WithLp.ofLp v 4 - WithLp.ofLp v 8) = 0 := by
        simpa [glueballRep_zero_mulVec] using congrFun (hv 0) 7
      exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by simp))
    have h13 : WithLp.ofLp v 1 + WithLp.ofLp v 3 = 0 := by
      have e : Complex.I * (-WithLp.ofLp v 1 - WithLp.ofLp v 3) = 0 := by
        simpa [glueballRep_two_mulVec] using congrFun (hv 2) 0
      have h : -WithLp.ofLp v 1 - WithLp.ofLp v 3 = 0 :=
        (mul_eq_zero.mp e).resolve_left (by simp)
      linear_combination -h
    have h1 : WithLp.ofLp v 1 = 0 := by
      rw [h3] at h13
      simpa using h13
    rw [Submodule.mem_span_singleton]
    refine ⟨WithLp.ofLp v 0, ?_⟩
    apply WithLp.ofLp_injective
    funext k
    fin_cases k <;>
      simp [glueballSingletVec, glueballCoeff, h1, h2, h3, h4, h5, h6, h7, h8]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact glueballCoeff_mem

/-- The meson singlet vector is nonzero, so the meson singlet space is not the zero space. -/
theorem mesonSingletVec_ne_zero : mesonSingletVec ≠ 0 := by
  intro h
  have := congrArg (fun u : colourVec 4 => WithLp.ofLp u 1) h
  simp [mesonSingletVec, mesonCoeff] at this

/-- The glueball singlet vector is nonzero, so the glueball singlet space is not the zero space. -/
theorem glueballSingletVec_ne_zero : glueballSingletVec ≠ 0 := by
  intro h
  have := congrArg (fun u : colourVec 9 => WithLp.ofLp u 0) h
  simp [glueballSingletVec, glueballCoeff] at this

/-! #### The colour actions as bounded operators, and the `su(2)` representation

`colourAct` and `colourEnergy` extend to continuous linear maps on the completion, with the sharp
pointwise constant `‖T^a v‖ = ‖v‖/2` (`norm_fundRep_mulVec`).  Composing the operators composes the
matrices (`colourActOp_comp_apply`), so every matrix identity of `fundRep` lifts to an operator
identity with no analytic work: `[A^a, A^b] = i ε^{abc} A^c` and `Σ_a (A^a)² = C_F · 1` hold on
`fundMode d` without a domain hypothesis, which the unbounded `ymHamiltonian` does not allow. -/

def flip2 (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem flip2_involutive (i : Fin 2) : flip2 (flip2 i) = i := by
  fin_cases i <;> simp [flip2]

theorem norm_fundRep_mulVec (a : Fin 3) (v : Fin 2 → ℂ) :
    ‖(fundRep a).mulVec v‖ = ‖v‖ / 2 := by
  have hcoord : ∀ i : Fin 2,
      ‖(fundRep a).mulVec v i‖ = ‖v (if a = 2 then i else flip2 i)‖ / 2 := by
    intro i
    by_cases ha : a = 2
    · subst ha
      fin_cases i <;>
        simp [fundRep, pauli, Matrix.mulVec, div_eq_mul_inv, mul_comm]
    · have ha01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp_all
      rcases ha01 with rfl | rfl <;> fin_cases i <;>
        simp [fundRep, pauli, Matrix.mulVec, flip2, ha, div_eq_mul_inv, mul_comm]
  have hle : ‖(fundRep a).mulVec v‖ ≤ ‖v‖ / 2 := by
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    rw [hcoord i]
    exact div_le_div_of_nonneg_right (norm_le_pi_norm v _) (by norm_num)
  have hrev : ∀ i : Fin 2, ‖v i‖ ≤ 2 * ‖(fundRep a).mulVec v‖ := by
    intro i
    have hkey : (if a = 2 then (if a = 2 then i else flip2 i)
        else flip2 (if a = 2 then i else flip2 i)) = i := by
      by_cases ha : a = 2
      · simp [ha]
      · simp only [ha, if_false, flip2_involutive]
    have h := hcoord (if a = 2 then i else flip2 i)
    rw [hkey] at h
    have h2 := norm_le_pi_norm ((fundRep a).mulVec v) (if a = 2 then i else flip2 i)
    rw [h] at h2
    linarith
  have hge : ‖v‖ ≤ 2 * ‖(fundRep a).mulVec v‖ := by
    rw [pi_norm_le_iff_of_nonempty]
    exact hrev
  linarith

theorem fundMode_norm_sq_eq_tsum (f : fundMode d) : ‖f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, h2]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (tsum_nonneg fun n => by positivity)]

theorem colourAct_norm_le (a : Fin 3) (f : fundMode d) (n : Fin d → ℕ) :
    ‖colourAct a f n‖ ≤ ‖f n‖ / 2 := by
  rw [colourAct, norm_fundRep_mulVec]

theorem colourAct_memℓp (a : Fin 3) (f : fundMode d) : Memℓp (colourAct a f) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [h2, Real.rpow_two] using (lp.memℓp f).summable hp
  refine memℓp_gen ?_
  rw [h2]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hf.mul_left (1 / 4))
  have h := colourAct_norm_le a f n
  have hnn : 0 ≤ ‖colourAct a f n‖ := norm_nonneg _
  calc ‖colourAct a f n‖ ^ 2 ≤ (‖f n‖ / 2) ^ 2 := pow_le_pow_left₀ hnn h 2
    _ = 1 / 4 * ‖f n‖ ^ 2 := by ring

theorem colourActOp_norm_le (a : Fin 3) (f : fundMode d) :
    ‖(⟨colourAct a f, colourAct_memℓp a f⟩ : fundMode d)‖ ≤ ‖f‖ / 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [h2, Real.rpow_two] using (lp.memℓp f).summable hp
  have hterm : ∀ n : Fin d → ℕ, ‖colourAct a f n‖ ^ 2 ≤ 1 / 4 * ‖f n‖ ^ 2 := by
    intro n
    have h := colourAct_norm_le a f n
    have hnn : 0 ≤ ‖colourAct a f n‖ := norm_nonneg _
    have hmul : ‖colourAct a f n‖ * ‖colourAct a f n‖
        ≤ (‖f n‖ / 2) * (‖f n‖ / 2) := mul_self_le_mul_self hnn h
    calc ‖colourAct a f n‖ ^ 2 = ‖colourAct a f n‖ * ‖colourAct a f n‖ := pow_two _
      _ ≤ (‖f n‖ / 2) * (‖f n‖ / 2) := hmul
      _ = 1 / 4 * ‖f n‖ ^ 2 := by ring
  have hsum : Summable fun n => 1 / 4 * ‖f n‖ ^ 2 := hf.mul_left (1 / 4)
  have hsum' : Summable fun n => ‖colourAct a f n‖ ^ 2 :=
    hsum.of_nonneg_of_le (fun n => by positivity) hterm
  have hbound : ∑' n, ‖colourAct a f n‖ ^ 2 ≤ (‖f‖ / 2) ^ 2 := by
    calc ∑' n, ‖colourAct a f n‖ ^ 2 ≤ ∑' n, 1 / 4 * ‖f n‖ ^ 2 :=
          hsum'.tsum_le_tsum hterm hsum
      _ = 1 / 4 * ∑' n, ‖f n‖ ^ 2 := tsum_mul_left
      _ = 1 / 4 * ‖f‖ ^ 2 := by rw [← fundMode_norm_sq_eq_tsum]
      _ = (‖f‖ / 2) ^ 2 := by ring
  have hsq : ‖(⟨colourAct a f, colourAct_memℓp a f⟩ : fundMode d)‖ ^ 2
      ≤ (‖f‖ / 2) ^ 2 := by
    rw [fundMode_norm_sq_eq_tsum]
    exact hbound
  calc ‖(⟨colourAct a f, colourAct_memℓp a f⟩ : fundMode d)‖
      = |‖(⟨colourAct a f, colourAct_memℓp a f⟩ : fundMode d)‖| :=
        (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ |‖f‖ / 2| := sq_le_sq.mp hsq
    _ = ‖f‖ / 2 := abs_of_nonneg (by positivity)

/-- The colour action as a vector of the coloured completion. -/
noncomputable def colourActOp (a : Fin 3) (f : fundMode d) : fundMode d :=
  ⟨colourAct a f, colourAct_memℓp a f⟩

theorem colourActOp_apply (a : Fin 3) (f : fundMode d) (n : Fin d → ℕ) :
    colourActOp a f n = (fundRep a).mulVec (f n) := rfl

/-- **The colour action leaves the Fock coefficients alone**: on `c ⊗ v` it acts as
`c ⊗ (T^a v)`. -/
theorem colourActOp_colourModeVec (a : Fin 3) (c : CoreCoeff d) (v : Fin 2 → ℂ) :
    colourActOp a (colourModeVec c v) = colourModeVec c ((fundRep a).mulVec v) := by
  ext n
  rw [colourActOp_apply, colourModeVec_apply, colourModeVec_apply, Matrix.mulVec_smul]

theorem colourActOp_add (a : Fin 3) (f g : fundMode d) :
    colourActOp a (f + g) = colourActOp a f + colourActOp a g := by
  ext n
  simp only [colourActOp, colourAct, lp.coeFn_add, Pi.add_apply, Matrix.mulVec_add]

theorem colourActOp_smul (a : Fin 3) (c : ℂ) (f : fundMode d) :
    colourActOp a (c • f) = c • colourActOp a f := by
  ext n
  simp only [colourActOp, colourAct, lp.coeFn_smul, Pi.smul_apply, Matrix.mulVec_smul]

/-- **The colour action on the completion** as a linear map. -/
noncomputable def colourActLinear (a : Fin 3) : fundMode d →ₗ[ℂ] fundMode d where
  toFun := colourActOp a
  map_add' := colourActOp_add a
  map_smul' := colourActOp_smul a

/-- **The colour action is bounded, with constant `1/2`** — the sharp one, since `‖T^a v‖ = ‖v‖/2`
pointwise. -/
noncomputable def colourActCLM (a : Fin 3) : fundMode d →L[ℂ] fundMode d :=
  (colourActLinear a).mkContinuous (1 / 2) fun f => by
    simpa [div_eq_mul_inv, mul_comm] using colourActOp_norm_le a f

theorem colourActCLM_norm_le (a : Fin 3) (f : fundMode d) :
    ‖colourActCLM a f‖ ≤ (1 / 2) * ‖f‖ := by
  simpa [div_eq_mul_inv, mul_comm] using colourActOp_norm_le a f


/-- **The colour energy as a bounded operator**: `C_F` times the identity. -/
noncomputable def colourEnergyCLM : fundMode d →L[ℂ] fundMode d :=
  (3 / 4 : ℂ) • ContinuousLinearMap.id ℂ (fundMode d)

theorem colourEnergyCLM_apply (f : fundMode d) : colourEnergyCLM f = colourEnergyOp d f := rfl

/-! ##### The colour operators are a representation of `su(2)`

Boundedness alone does not make the colour action a symmetry; the algebra has to lift too.  It does:
on the completion the generators satisfy `[A^a, A^b] = i ε^{abc} A^c` (`colourActCLM_commutator`),
and the Casimir is the sum of their squares, `Σ_a (A^a)² = C_F · 1` (`sum_colourActCLM_comp`).  So
`colourEnergyCLM` is the Casimir *operator* of the representation, not merely the number `3/4`
acting on one colour vector.

Nothing new about `Fin 2 → ℂ` is needed: the coefficientwise statements are the matrix identities
already in this chapter (`fundRep_commutator`, `su2_casimir_fundamental`), carried to `f n` through
`Matrix.mulVec_mulVec` (`colourActOp_comp_apply`).  Because the generators are *bounded*, the
commutator equality holds on the whole completion with no domain or common-core hypothesis — which
is precisely what the unbounded Yang–Mills Hamiltonian does not offer.

**Boundary.**  A representation of the compact algebra on `fundMode d` is not a statement that the
Fock coefficients are organised into colour multiplets: no invariant subspace, no decomposition and
no spectral consequence is claimed, and the exponentiated group action is not constructed.
-/

/-- **The commutator of the generators, applied to a colour vector**:
`[T^a, T^b] v = i ε^{abc} T^c v`, read off `fundRep_commutator`. -/
theorem fundRep_mulVec_commutator (a b : Fin 3) (v : Fin 2 → ℂ) :
    (fundRep a).mulVec ((fundRep b).mulVec v) - (fundRep b).mulVec ((fundRep a).mulVec v)
      = ∑ c : Fin 3, (Complex.I * (levi a b c : ℂ)) • ((fundRep c).mulVec v) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.mulVec v) (fundRep_commutator a b)
  rw [show (∑ c : Fin 3, (Complex.I * (levi a b c : ℂ)) • ((fundRep c).mulVec v))
      = ∑ c : Fin 3, Complex.I • ((levi a b c : ℂ) • ((fundRep c).mulVec v)) from by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_smul]]
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec, Finset.smul_sum] using h

/-- **Composing the colour action multiplies the matrices**: coefficient by coefficient,
`A^a (A^b f) = (T^a T^b) f`. -/
theorem colourActOp_comp_apply (a b : Fin 3) (f : fundMode d) (n : Fin d → ℕ) :
    colourActOp a (colourActOp b f) n = (fundRep a * fundRep b).mulVec (f n) := by
  simp [colourActOp_apply, ← Matrix.mulVec_mulVec]

/-- The commutator of the colour operators, coefficientwise. -/
theorem colourActOp_commutator_apply (a b : Fin 3) (f : fundMode d) (n : Fin d → ℕ) :
    (colourActOp a (colourActOp b f) - colourActOp b (colourActOp a f)) n
      = ∑ c : Fin 3, (Complex.I * (levi a b c : ℂ)) • colourActOp c f n := by
  simp only [Pi.sub_apply, lp.coeFn_sub, colourActOp_comp_apply, ← Matrix.mulVec_mulVec]
  rw [fundRep_mulVec_commutator]
  simp [colourActOp_apply]

/-- **The colour operators are a representation of `su(2)`**: `[A^a, A^b] = i ε^{abc} A^c` on the
completion, with the same `ε` as `fundRep_commutator` and `su2Struct`. -/
theorem colourActOp_commutator (a b : Fin 3) (f : fundMode d) :
    colourActOp a (colourActOp b f) - colourActOp b (colourActOp a f)
      = ∑ c : Fin 3, (Complex.I * (levi a b c : ℂ)) • colourActOp c f := by
  ext n i
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply]
  exact congrFun (colourActOp_commutator_apply a b f n) i

/-- The Casimir family is literally the sum of the squared generators, coefficientwise. -/
theorem colourEnergy_eq_sum_sq (f : fundMode d) (n : Fin d → ℕ) :
    colourEnergy f n = ∑ a : Fin 3, (fundRep a).mulVec ((fundRep a).mulVec (f n)) := rfl

/-- **The Casimir operator is the sum of the squares of the generators**:
`Σ_a A^a A^a = C_F · 1`, on the whole completion. -/
theorem sum_colourActOp_comp (f : fundMode d) :
    ∑ a : Fin 3, colourActOp a (colourActOp a f) = colourEnergyOp d f := by
  ext n
  rw [show (∑ a : Fin 3, colourActOp a (colourActOp a f)) n
      = ∑ a : Fin 3, (fundRep a).mulVec ((fundRep a).mulVec (f n)) from by
    simp [colourActOp_comp_apply, ← Matrix.mulVec_mulVec]]
  rw [colourEnergyOp_apply d f n, colourEnergy_eq_sum_sq]

theorem colourActCLM_apply (a : Fin 3) (f : fundMode d) : colourActCLM a f = colourActOp a f :=
  rfl

/-- **The bounded colour operators carry the same commutators**: no domain hypothesis is needed,
because `colourActCLM a` is bounded. -/
theorem colourActCLM_commutator (a b : Fin 3) (f : fundMode d) :
    colourActCLM a (colourActCLM b f) - colourActCLM b (colourActCLM a f)
      = ∑ c : Fin 3, (Complex.I * (levi a b c : ℂ)) • colourActCLM c f := by
  simpa [colourActCLM_apply] using colourActOp_commutator a b f

/-- **`colourEnergyCLM` is the Casimir operator**: it equals `Σ_a (colourActCLM a)²`. -/
theorem sum_colourActCLM_comp (f : fundMode d) :
    ∑ a : Fin 3, colourActCLM a (colourActCLM a f) = colourEnergyCLM f := by
  simpa [colourActCLM_apply, colourEnergyCLM_apply] using sum_colourActOp_comp f
/-! ##### The operator norm is attained

`colourActCLM_norm_le` bounded the colour action by `1/2`; `colourActOp_norm` upgrades it to an
identity, so `norm_colourActCLM` is an equality of operator norms rather than a bound.  Nothing is
lost on the completion: the `ℓ²` norm is a sum of squares, and the sharp pointwise factor `1/2`
survives termwise.

**Boundary.**  An attained norm says the constant `1/2` is sharp; it does not make `A^a` an
isometry, and no spectral statement about the colour factor follows.
-/

/-- **The bound is attained.**  The pointwise identity `‖T^a v‖ = ‖v‖/2` upgrades from an inequality
on the completion to an equality: `‖A^a f‖ = ‖f‖/2` for every `f`, since the `ℓ²` norm squares and
the squares sum. -/
theorem colourActOp_norm (a : Fin 3) (f : fundMode d) : ‖colourActOp a f‖ = ‖f‖ / 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [h2, Real.rpow_two] using (lp.memℓp f).summable hp
  have hterm : ∀ n : Fin d → ℕ, ‖colourActOp a f n‖ ^ 2 = 1 / 4 * ‖f n‖ ^ 2 := by
    intro n
    rw [colourActOp_apply, norm_fundRep_mulVec]
    ring
  have hsum : ∑' n, ‖colourActOp a f n‖ ^ 2 = 1 / 4 * ‖f‖ ^ 2 := by
    rw [tsum_congr hterm, tsum_mul_left, ← fundMode_norm_sq_eq_tsum]
  have hsq : ‖colourActOp a f‖ ^ 2 = (‖f‖ / 2) ^ 2 := by
    rw [fundMode_norm_sq_eq_tsum, hsum]
    ring
  have habs := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at habs

/-- A nonzero coloured vector, so that the operator norm is a genuine supremum over nonzero `f`. -/
noncomputable def colourProbeVec (d : ℕ) : fundMode d :=
  lp.single 2 (0 : Fin d → ℕ) (fun i : Fin 2 => if i = 0 then 1 else 0)

theorem colourProbeVec_ne_zero (d : ℕ) : colourProbeVec d ≠ 0 := by
  intro h
  have hv : ‖(colourProbeVec d : fundMode d)‖ = 0 := by rw [h, norm_zero]
  rw [colourProbeVec, lp.norm_single (p := (2 : ℝ≥0∞)) (by norm_num) (0 : Fin d → ℕ) _] at hv
  have hfib : (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  exact hfib (norm_eq_zero.mp hv)

/-- **The operator norm of the colour action is exactly `1/2`**, not merely at most `1/2`. -/
theorem norm_colourActCLM (a : Fin 3) : ‖colourActCLM (d := d) a‖ = 1 / 2 := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (colourActCLM_norm_le (d := d) a)) ?_
  have hx : colourProbeVec d ≠ 0 := colourProbeVec_ne_zero d
  have hpos : 0 < ‖(colourProbeVec d : fundMode d)‖ := norm_pos_iff.mpr hx
  have h := ContinuousLinearMap.ratio_le_opNorm (colourActCLM (d := d) a) (colourProbeVec d)
  rw [colourActCLM_apply, colourActOp_norm] at h
  have h' : ‖(colourProbeVec d : fundMode d)‖ / 2 / ‖(colourProbeVec d : fundMode d)‖ = 1 / 2 := by
    field_simp
  linarith [h, h'.le, h'.ge]
/-! ##### The exponentiated colour action

`[A^a, A^b] = i ε^{abc} A^c` is the algebra of a *compact* group, and it is the group, not the
algebra, that acts on states.  This section exponentiates: `colourGroupElement a θ` is
`exp (i θ T^a)` in closed form, `cos(θ/2) · 1 + 2i sin(θ/2) · T^a` — the exponential series sums to
this because `(T^a)² = (1/4) · 1` (`fundRep_sq`) — and it is a genuine unitary element
(`colourGroupElement_mem_unitary`, an algebraic `star` statement needing no norm at all), with the
group law `U(s) U(t) = U(s + t)`.

Acting coefficientwise on the completion gives a one-parameter group of bounded operators
(`colourGroupActCLM_mul`), each invertible with inverse the opposite parameter.

**Boundary — a group of *units*, not a unitary group.**  `fundMode d` carries the sup norm on the
fibre `Fin 2 → ℂ`: there is no `InnerProductSpace ℂ (Fin 2 → ℂ)` instance, so "unitary operator on
`fundMode`" is not even a well-typed predicate here, and the fibre norm is genuinely not preserved
(`colourGroupActCLM` is bounded by the constant `2`, not `1`).  What is unitary is the `2 × 2`
factor; a unitary action on the completion would need the Euclidean fibre norm.  No spectral
consequence, and no `su(2)`-multiplet structure of the coefficients, is claimed.
-/

/-- Act coefficientwise on the coloured completion by a `2 × 2` colour matrix. -/
noncomputable def matrixAct (M : Matrix (Fin 2) (Fin 2) ℂ) (f : fundMode d) :
    (Fin d → ℕ) → (Fin 2 → ℂ) := fun n => M.mulVec (f n)

/-- A coefficientwise colour matrix acts on the completion as soon as it is bounded on the colour
vector. -/
theorem matrixAct_memℓp (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (f : fundMode d) :
    Memℓp (matrixAct M f) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [h2, Real.rpow_two] using (lp.memℓp f).summable hp
  refine memℓp_gen ?_
  rw [h2]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hf.mul_left (C ^ 2))
  have hb := h (f n)
  calc ‖matrixAct M f n‖ ^ 2 ≤ (C * ‖f n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = C ^ 2 * ‖f n‖ ^ 2 := by ring

noncomputable def matrixActOp (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (f : fundMode d) : fundMode d :=
  ⟨matrixAct M f, matrixAct_memℓp M h f⟩

theorem matrixActOp_apply (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (f : fundMode d) (n : Fin d → ℕ) :
    matrixActOp M h f n = M.mulVec (f n) := rfl

theorem matrixActOp_add (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (f g : fundMode d) :
    matrixActOp M h (f + g) = matrixActOp M h f + matrixActOp M h g := by
  ext n
  simp only [matrixActOp, matrixAct, lp.coeFn_add, Pi.add_apply, Matrix.mulVec_add]

theorem matrixActOp_smul (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (c : ℂ) (f : fundMode d) :
    matrixActOp M h (c • f) = c • matrixActOp M h f := by
  ext n
  simp only [matrixActOp, matrixAct, lp.coeFn_smul, Pi.smul_apply, Matrix.mulVec_smul]

noncomputable def matrixActLinear (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) : fundMode d →ₗ[ℂ] fundMode d where
  toFun := matrixActOp M h
  map_add' := matrixActOp_add M h
  map_smul' := matrixActOp_smul M h

theorem matrixActOp_norm_le (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (hC : 0 ≤ C) (f : fundMode d) :
    ‖matrixActOp M h f‖ ≤ C * ‖f‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [h2, Real.rpow_two] using (lp.memℓp f).summable hp
  have hterm : ∀ n : Fin d → ℕ, ‖matrixActOp M h f n‖ ^ 2 ≤ C ^ 2 * ‖f n‖ ^ 2 := by
    intro n
    have hb := h (f n)
    calc ‖matrixActOp M h f n‖ ^ 2 ≤ (C * ‖f n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = C ^ 2 * ‖f n‖ ^ 2 := by ring
  have hsum : Summable fun n => C ^ 2 * ‖f n‖ ^ 2 := hf.mul_left (C ^ 2)
  have hsum' : Summable fun n => ‖matrixActOp M h f n‖ ^ 2 :=
    hsum.of_nonneg_of_le (fun n => by positivity) hterm
  have hsq : ‖matrixActOp M h f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [show (C * ‖f‖) ^ 2 = C ^ 2 * ‖f‖ ^ 2 by ring, fundMode_norm_sq_eq_tsum]
    calc ∑' n, ‖matrixActOp M h f n‖ ^ 2 ≤ ∑' n, C ^ 2 * ‖f n‖ ^ 2 :=
          hsum'.tsum_le_tsum hterm hsum
      _ = C ^ 2 * ∑' n, ‖f n‖ ^ 2 := tsum_mul_left
      _ = C ^ 2 * ‖f‖ ^ 2 := by rw [← fundMode_norm_sq_eq_tsum]
  calc ‖matrixActOp M h f‖ = Real.sqrt (‖matrixActOp M h f‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((C * ‖f‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C * ‖f‖ := Real.sqrt_sq (mul_nonneg hC (norm_nonneg _))

noncomputable def matrixActCLM (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (hC : 0 ≤ C) :
    fundMode d →L[ℂ] fundMode d :=
  (matrixActLinear M h).mkContinuous C fun f => matrixActOp_norm_le M h hC f

theorem matrixActCLM_apply (M : Matrix (Fin 2) (Fin 2) ℂ) {C : ℝ}
    (h : ∀ v : Fin 2 → ℂ, ‖M.mulVec v‖ ≤ C * ‖v‖) (hC : 0 ≤ C) (f : fundMode d) :
    matrixActCLM M h hC f = matrixActOp M h f := rfl

/-- **The exponentiated colour generator**, `exp (i θ T^a)`, in closed form:
`cos(θ/2) · 1 + 2i sin(θ/2) · T^a`.  This is what the exponential series sums to, because
`(T^a)² = (1/4) · 1` (`fundRep_sq`); it is written out rather than exponentiated because the
`2 × 2` matrices carry no `NormedRing` instance. -/
noncomputable def colourGroupElement (a : Fin 3) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (θ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (2 * Complex.I * (Real.sin (θ / 2) : ℂ)) • fundRep a

theorem colourGroupElement_zero (a : Fin 3) : colourGroupElement a 0 = 1 := by
  simp [colourGroupElement]

theorem star_fundRep (a : Fin 3) : star (fundRep a) = fundRep a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [fundRep, pauli, Matrix.star_apply]

/-- The inverse of the exponentiated generator is its conjugate transpose. -/
theorem star_colourGroupElement (a : Fin 3) (θ : ℝ) :
    star (colourGroupElement a θ) = colourGroupElement a (-θ) := by
  have h1 : star ((Real.cos (θ / 2) : ℂ)) = (Real.cos (θ / 2) : ℂ) := Complex.conj_ofReal _
  have h2 : star (2 * Complex.I * (Real.sin (θ / 2) : ℂ))
      = -(2 * Complex.I * (Real.sin (θ / 2) : ℂ)) := by
    rw [StarMul.star_mul, StarMul.star_mul]
    have hs : star ((Real.sin (θ / 2) : ℂ)) = ((Real.sin (θ / 2) : ℂ)) := Complex.conj_ofReal _
    have h2c : star (2 : ℂ) = 2 := by norm_num
    have hsI : star (Complex.I) = -Complex.I := by simp
    rw [hs, h2c, hsI]
    ring
  have h3 : (Real.cos (-θ / 2) : ℂ) = (Real.cos (θ / 2) : ℂ) := by
    rw [show -θ / 2 = -(θ / 2) by ring, Real.cos_neg]
  have h4 : (Real.sin (-θ / 2) : ℂ) = -(Real.sin (θ / 2) : ℂ) := by
    rw [show -θ / 2 = -(θ / 2) by ring, Real.sin_neg, Complex.ofReal_neg]
  have h5 : star (fundRep a) = fundRep a := star_fundRep a
  unfold colourGroupElement
  simp_all

/-- **The exponentiated generators multiply by adding the parameters**: `U(s) U(t) = U(s + t)`.
This is the addition formula for `cos` and `sin` on half-angles, using `(T^a)² = (1/4) · 1`. -/
theorem colourGroupElement_mul (a : Fin 3) (s t : ℝ) :
    colourGroupElement a s * colourGroupElement a t = colourGroupElement a (s + t) := by
  have hs : s / 2 + t / 2 = (s + t) / 2 := by ring
  have hc : Real.cos ((s + t) / 2)
      = Real.cos (s / 2) * Real.cos (t / 2) - Real.sin (s / 2) * Real.sin (t / 2) := by
    rw [← hs, Real.cos_add]
  have hsn : Real.sin ((s + t) / 2)
      = Real.sin (s / 2) * Real.cos (t / 2) + Real.cos (s / 2) * Real.sin (t / 2) := by
    rw [← hs, Real.sin_add]
  simp only [colourGroupElement, hc, hsn, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, fundRep_sq, smul_smul]
  ext i j
  simp [Matrix.add_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem colourGroupElement_mul_neg (a : Fin 3) (θ : ℝ) :
    colourGroupElement a θ * colourGroupElement a (-θ) = 1 := by
  rw [colourGroupElement_mul]
  simp [colourGroupElement_zero]

/-- **The colour factor carries a genuine unitary element**: `exp (i θ T^a)` is unitary in the
`2 × 2` matrices — an algebraic statement about `star`, needing no norm at all. -/
theorem colourGroupElement_mem_unitary (a : Fin 3) (θ : ℝ) :
    colourGroupElement a θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff]
  constructor
  · rw [star_colourGroupElement]
    simpa [colourGroupElement_zero] using colourGroupElement_mul a (-θ) θ
  · rw [star_colourGroupElement]
    simpa [colourGroupElement_zero] using colourGroupElement_mul a θ (-θ)

/-- The colour-vector norm bound behind the action on the completion: the generator part is a
similarity with factor `1/2`, so the whole group element costs at most a factor `2`. -/
theorem colourGroupElement_norm_le (a : Fin 3) (θ : ℝ) (v : Fin 2 → ℂ) :
    ‖(colourGroupElement a θ).mulVec v‖ ≤ 2 * ‖v‖ := by
  have hc : ‖((Real.cos (θ / 2) : ℂ))‖ ≤ 1 := by
    have h : ‖((Real.cos (θ / 2) : ℂ))‖ = |Real.cos (θ / 2)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h]
    exact Real.abs_cos_le_one _
  have hs : ‖(2 * Complex.I * (Real.sin (θ / 2) : ℂ))‖ ≤ 2 := by
    have h : ‖(2 * Complex.I * (Real.sin (θ / 2) : ℂ))‖ = 2 * |Real.sin (θ / 2)| := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [h]
    have := Real.abs_sin_le_one (θ / 2)
    linarith
  rw [colourGroupElement, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  calc ‖((Real.cos (θ / 2) : ℂ)) • v + (2 * Complex.I * (Real.sin (θ / 2) : ℂ)) •
        (fundRep a).mulVec v‖
      ≤ ‖((Real.cos (θ / 2) : ℂ)) • v‖ + ‖(2 * Complex.I * (Real.sin (θ / 2) : ℂ)) •
          (fundRep a).mulVec v‖ := norm_add_le _ _
    _ = ‖((Real.cos (θ / 2) : ℂ))‖ * ‖v‖ +
          ‖(2 * Complex.I * (Real.sin (θ / 2) : ℂ))‖ * ‖(fundRep a).mulVec v‖ := by
        rw [norm_smul, norm_smul]
    _ ≤ 1 * ‖v‖ + 2 * (‖v‖ / 2) := by
        have hmul := norm_fundRep_mulVec a v
        have h1 := mul_le_mul_of_nonneg_right hc (norm_nonneg v)
        have h2 := mul_le_mul hs hmul.le (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = 2 * ‖v‖ := by ring

/-- **The exponentiated colour action on the completion**: `exp (i θ T^a)` acting
coefficientwise. -/
noncomputable def colourGroupAct (a : Fin 3) (θ : ℝ) (f : fundMode d) : fundMode d :=
  matrixActOp (colourGroupElement a θ) (colourGroupElement_norm_le a θ) f

theorem colourGroupAct_apply (a : Fin 3) (θ : ℝ) (f : fundMode d) (n : Fin d → ℕ) :
    colourGroupAct a θ f n = (colourGroupElement a θ).mulVec (f n) := rfl

/-- The exponentiated colour action as a bounded operator. -/
noncomputable def colourGroupActCLM (a : Fin 3) (θ : ℝ) : fundMode d →L[ℂ] fundMode d :=
  matrixActCLM (colourGroupElement a θ) (colourGroupElement_norm_le a θ) (by norm_num : (0 : ℝ) ≤ 2)

theorem colourGroupActCLM_apply (a : Fin 3) (θ : ℝ) (f : fundMode d) :
    colourGroupActCLM a θ f = colourGroupAct a θ f := rfl

theorem colourGroupAct_comp (a : Fin 3) (s t : ℝ) (f : fundMode d) :
    colourGroupAct a s (colourGroupAct a t f) = colourGroupAct a (s + t) f := by
  ext n
  rw [colourGroupAct_apply, colourGroupAct_apply, colourGroupAct_apply, Matrix.mulVec_mulVec,
    colourGroupElement_mul]

/-- **The exponentiated colour action is a one-parameter group of operators**: `U(s) U(t) = U(s+t)`
as bounded operators on the completion. -/
theorem colourGroupActCLM_mul (a : Fin 3) (s t : ℝ) :
    colourGroupActCLM (d := d) a s * colourGroupActCLM a t = colourGroupActCLM a (s + t) := by
  ext f
  simp only [ContinuousLinearMap.mul_apply, colourGroupActCLM_apply, colourGroupAct_comp]

/-- Each operator of the one-parameter group is invertible, with inverse the opposite parameter. -/
theorem colourGroupActCLM_mul_neg (a : Fin 3) (θ : ℝ) :
    colourGroupActCLM (d := d) a θ * colourGroupActCLM a (-θ) = 1 := by
  rw [colourGroupActCLM_mul]
  ext f
  simp [colourGroupActCLM_apply, colourGroupAct_apply, colourGroupElement_zero]

theorem colourGroupActCLM_neg_mul (a : Fin 3) (θ : ℝ) :
    colourGroupActCLM (d := d) a (-θ) * colourGroupActCLM a θ = 1 := by
  rw [colourGroupActCLM_mul]
  ext f
  simp [colourGroupActCLM_apply, colourGroupAct_apply, colourGroupElement_zero]

/-! #### The Hilbert completion: a genuine unitary colour group

`fundMode d` puts the sup norm on its colour fibre `Fin 2 → ℂ`.  No norm making that space an inner
product space can be the sup norm, since the parallelogram law fails, so `InnerProductSpace ℂ
(fundMode d)` does not exist and "`colourGroupActCLM a θ` is unitary" is not a well-typed
predicate.  `fundHilbert d` carries the same occupation multi-indices with the Euclidean colour
fibre.  It is an inner product space through `lp.inner_eq_tsum`, and on it the same exponentiated
colour group acts by genuine unitary operators:

* `eucMatCLM` is a colour matrix as a continuous linear map of the Euclidean fibre; a unitary
  matrix preserves the fibre inner product (`eucMatCLM_inner_of_unitary`) and hence its norm
  (`eucMatCLM_norm_of_unitary`), and the adjoint is the conjugate transpose
  (`eucMatCLM_adjoint_eq`).
* `hilbActOp`/`hilbActCLM` act coefficientwise by such a matrix, and an isometry of the fibre
  gives an isometry of the Hilbert sum (`hilbActOp_inner`, `hilbActOp_norm`).
* `colourGroupActHilbert a θ` is the exponentiated generator on `fundHilbert d`; it is unitary
  (`colourGroupActHilbert_mem_unitary`), isometric (`colourGroupActHilbert_norm`) and its group
  law holds (`colourGroupActHilbert_mul`).

**Boundary.**  This is a different normed space, not a second norm on `fundMode d`: the two
completions share their coefficients (`ofLp_hilbActCoeff`) but not their norms, and nothing here
identifies one completion with the fibre `colouredCore` below.  No spectral consequence is
claimed.
-/

/-- The occupation-indexed coefficients with the Euclidean (Hilbert) colour fibre. -/
abbrev fundHilbert (d : ℕ) := lp (fun _ : Fin d → ℕ => EuclideanSpace ℂ (Fin 2)) 2

noncomputable def eucMatCLM (M : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

theorem eucMatCLM_apply_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    eucMatCLM M v = WithLp.toLp 2 (M *ᵥ WithLp.ofLp v) := by
  rw [show eucMatCLM M v = Matrix.toEuclideanLin M v from rfl, Matrix.toLpLin_apply]

theorem eucMatCLM_one : eucMatCLM (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext v
  simp [eucMatCLM]

theorem eucMatCLM_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    eucMatCLM (A * B) = eucMatCLM A * eucMatCLM B := by
  ext v
  simp only [eucMatCLM_apply_eq, ContinuousLinearMap.mul_apply, WithLp.ofLp_toLp,
    Matrix.mulVec_mulVec]

theorem eucMatCLM_adjoint (M : Matrix (Fin 2) (Fin 2) ℂ) :
    eucMatCLM M.conjTranspose = ContinuousLinearMap.adjoint (eucMatCLM M) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have h : Matrix.toEuclideanLin M.conjTranspose = LinearMap.adjoint (Matrix.toEuclideanLin M) :=
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint M
  rw [show eucMatCLM M.conjTranspose x = Matrix.toEuclideanLin M.conjTranspose x from rfl,
    show eucMatCLM M y = Matrix.toEuclideanLin M y from rfl, h]
  exact LinearMap.adjoint_inner_left (Matrix.toEuclideanLin M) y x

theorem eucMatCLM_star (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (eucMatCLM M) = eucMatCLM (star M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose]
  exact (eucMatCLM_adjoint M).symm

theorem eucMatCLM_adjoint_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ContinuousLinearMap.adjoint (eucMatCLM M) = eucMatCLM (star M) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact eucMatCLM_star M

theorem eucMatCLM_adjoint_star (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ContinuousLinearMap.adjoint (eucMatCLM (star M)) = eucMatCLM M := by
  rw [eucMatCLM_adjoint_eq, star_star]

/-- **A unitary colour matrix preserves the fibre inner product.** -/
theorem eucMatCLM_inner_of_unitary {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : star U * U = 1) (v w : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (eucMatCLM U v) (eucMatCLM U w) = inner ℂ v w := by
  have hcomp : eucMatCLM (star U) * eucMatCLM U = 1 := by
    rw [← eucMatCLM_mul, hU, eucMatCLM_one]
  calc inner ℂ (eucMatCLM U v) (eucMatCLM U w)
      = inner ℂ v (ContinuousLinearMap.adjoint (eucMatCLM U) (eucMatCLM U w)) :=
        (ContinuousLinearMap.adjoint_inner_right (eucMatCLM U) v (eucMatCLM U w)).symm
    _ = inner ℂ v (eucMatCLM (star U) (eucMatCLM U w)) := by rw [eucMatCLM_adjoint_eq]
    _ = inner ℂ v ((eucMatCLM (star U) * eucMatCLM U) w) := by
        rw [ContinuousLinearMap.mul_apply]
    _ = inner ℂ v w := by rw [hcomp, ContinuousLinearMap.one_apply]

theorem eucMatCLM_norm_of_inner {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM U v) (eucMatCLM U w) = inner ℂ v w)
    (v : EuclideanSpace ℂ (Fin 2)) : ‖eucMatCLM U v‖ = ‖v‖ := by
  have h := hInner v v
  have hsq : ‖eucMatCLM U v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) _, norm_sq_eq_re_inner (𝕜 := ℂ) _, h]
  nlinarith [norm_nonneg (eucMatCLM U v), norm_nonneg v]

theorem eucMatCLM_norm_of_unitary {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : star U * U = 1) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖eucMatCLM U v‖ = ‖v‖ :=
  eucMatCLM_norm_of_inner (eucMatCLM_inner_of_unitary hU) v

/-- The coefficientwise action of a colour matrix on the Hilbert completion. -/
noncomputable def hilbActCoeff (M : Matrix (Fin 2) (Fin 2) ℂ) (f : fundHilbert d) :
    (Fin d → ℕ) → EuclideanSpace ℂ (Fin 2) := fun n => eucMatCLM M (f n)

/-- The Hilbert and sup-norm completions agree coefficientwise: the colour matrix acts on the
readable `ℂ²` vector in both. -/
theorem ofLp_hilbActCoeff (M : Matrix (Fin 2) (Fin 2) ℂ) (f : fundHilbert d)
    (n : Fin d → ℕ) :
    WithLp.ofLp (hilbActCoeff M f n) = M *ᵥ WithLp.ofLp (f n) := by
  rw [hilbActCoeff, eucMatCLM_apply_eq, WithLp.ofLp_toLp]

theorem hilbActCoeff_memℓp (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f : fundHilbert d) :
    Memℓp (hilbActCoeff M f) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf : Summable fun n => ‖f n‖ ^ 2 := by
    simpa only [h2, Real.rpow_two] using (lp.memℓp f).summable hp
  refine memℓp_gen ?_
  rw [h2]
  simp only [Real.rpow_two]
  simpa only [hilbActCoeff, eucMatCLM_norm_of_inner hInner] using hf

noncomputable def hilbActOp (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f : fundHilbert d) :
    fundHilbert d :=
  ⟨hilbActCoeff M f, hilbActCoeff_memℓp M hInner f⟩

theorem hilbActOp_apply (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f : fundHilbert d)
    (n : Fin d → ℕ) :
    (hilbActOp M hInner f : fundHilbert d) n = eucMatCLM M (f n) := rfl

theorem hilbActOp_add (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f g : fundHilbert d) :
    hilbActOp M hInner (f + g) = hilbActOp M hInner f + hilbActOp M hInner g := by
  apply Subtype.ext
  funext n
  simp only [hilbActOp_apply, lp.coeFn_add, Pi.add_apply, map_add]

theorem hilbActOp_smul (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (c : ℂ) (f : fundHilbert d) :
    hilbActOp M hInner (c • f) = c • hilbActOp M hInner f := by
  apply Subtype.ext
  funext n
  simp only [hilbActOp_apply, lp.coeFn_smul, Pi.smul_apply, map_smul]

theorem hilbActOp_inner (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f g : fundHilbert d) :
    inner ℂ (hilbActOp M hInner f) (hilbActOp M hInner g) = inner ℂ f g := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr fun n => hInner (f n) (g n)

theorem hilbActOp_norm (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f : fundHilbert d) :
    ‖(hilbActOp M hInner f : fundHilbert d)‖ = ‖f‖ := by
  have h := hilbActOp_inner M hInner f f
  have hsq : ‖(hilbActOp M hInner f : fundHilbert d)‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) _, norm_sq_eq_re_inner (𝕜 := ℂ) _, h]
  nlinarith [norm_nonneg (hilbActOp M hInner f : fundHilbert d), norm_nonneg f]

noncomputable def hilbActLinear (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) :
    fundHilbert d →ₗ[ℂ] fundHilbert d where
  toFun := hilbActOp M hInner
  map_add' := hilbActOp_add M hInner
  map_smul' := hilbActOp_smul M hInner

noncomputable def hilbActCLM (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) :
    fundHilbert d →L[ℂ] fundHilbert d :=
  (hilbActLinear M hInner).mkContinuous 1 fun f => by
    change ‖(hilbActOp M hInner f : fundHilbert d)‖ ≤ 1 * ‖f‖
    rw [hilbActOp_norm M hInner f, one_mul]

theorem hilbActCLM_apply (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w) (f : fundHilbert d) :
    hilbActCLM M hInner f = hilbActOp M hInner f := rfl

theorem hilbActOp_comp (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM A v) (eucMatCLM A w) = inner ℂ v w)
    (hB : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM B v) (eucMatCLM B w) = inner ℂ v w)
    (hAB : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM (A * B) v) (eucMatCLM (A * B) w) = inner ℂ v w)
    (f : fundHilbert d) :
    hilbActOp A hA (hilbActOp B hB f) = hilbActOp (A * B) hAB f := by
  apply Subtype.ext
  funext n
  change eucMatCLM A (eucMatCLM B (f n)) = eucMatCLM (A * B) (f n)
  rw [eucMatCLM_mul, ContinuousLinearMap.mul_apply]

theorem eucMatCLM_inner_comp (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM A v) (eucMatCLM A w) = inner ℂ v w)
    (hB : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM B v) (eucMatCLM B w) = inner ℂ v w) :
    ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM (A * B) v) (eucMatCLM (A * B) w) = inner ℂ v w := by
  intro v w
  rw [eucMatCLM_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hA, hB]

theorem hilbActCLM_mul (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM A v) (eucMatCLM A w) = inner ℂ v w)
    (hB : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM B v) (eucMatCLM B w) = inner ℂ v w)
    (hAB : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM (A * B) v) (eucMatCLM (A * B) w) = inner ℂ v w) :
    hilbActCLM (d := d) A hA * hilbActCLM B hB = hilbActCLM (A * B) hAB := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.mul_apply, hilbActCLM_apply, hilbActCLM_apply, hilbActCLM_apply]
  exact hilbActOp_comp A B hA hB hAB f

theorem hilbActCLM_congr {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : M = N)
    (hM : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w)
    (hN : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM N v) (eucMatCLM N w) = inner ℂ v w) :
    hilbActCLM (d := d) M hM = hilbActCLM N hN := by
  subst h
  rfl

theorem eucMatCLM_one_inner : ∀ v w : EuclideanSpace ℂ (Fin 2),
    inner ℂ (eucMatCLM (1 : Matrix (Fin 2) (Fin 2) ℂ) v)
      (eucMatCLM (1 : Matrix (Fin 2) (Fin 2) ℂ) w) = inner ℂ v w := by
  intro v w
  rw [eucMatCLM_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]

theorem hilbActCLM_one (h1 : ∀ v w : EuclideanSpace ℂ (Fin 2),
    inner ℂ (eucMatCLM (1 : Matrix (Fin 2) (Fin 2) ℂ) v)
      (eucMatCLM (1 : Matrix (Fin 2) (Fin 2) ℂ) w) = inner ℂ v w) :
    hilbActCLM (d := d) 1 h1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [hilbActCLM_apply, ContinuousLinearMap.one_apply]
  apply Subtype.ext
  funext n
  simp only [hilbActOp_apply, eucMatCLM_one, ContinuousLinearMap.one_apply]

theorem hilbActOp_inner_adjoint (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w)
    (hN : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM N v) (eucMatCLM N w) = inner ℂ v w)
    (hpair : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) w = inner ℂ v (eucMatCLM N w)) (f g : fundHilbert d) :
    inner ℂ (hilbActOp M hM f) g = inner ℂ f (hilbActOp N hN g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr fun n => hpair (f n) (g n)

theorem hilbActCLM_adjoint_eq (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w)
    (hMs : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM (star M) v) (eucMatCLM (star M) w) = inner ℂ v w) :
    ContinuousLinearMap.adjoint (hilbActCLM (d := d) M hM) = hilbActCLM (star M) hMs := by
  refine (ContinuousLinearMap.eq_adjoint_iff (hilbActCLM (d := d) (star M) hMs)
    (hilbActCLM (d := d) M hM)).mpr ?_ |>.symm
  intro f g
  simp only [hilbActCLM_apply]
  refine hilbActOp_inner_adjoint (star M) M hMs hM (fun v w => ?_) f g
  rw [show inner ℂ (eucMatCLM (star M) v) w
      = inner ℂ v (ContinuousLinearMap.adjoint (eucMatCLM (star M)) w) from
    (ContinuousLinearMap.adjoint_inner_right (eucMatCLM (star M)) v w).symm,
    eucMatCLM_adjoint_star]

/-! #### The exponentiated colour action on the Hilbert completion -/

/-- The colour group element is an isometry of the Euclidean fibre. -/
theorem colourGroupElement_isometry (a : Fin 3) (θ : ℝ) :
    ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM (colourGroupElement a θ) v)
        (eucMatCLM (colourGroupElement a θ) w) = inner ℂ v w :=
  eucMatCLM_inner_of_unitary (Unitary.mem_iff.mp (colourGroupElement_mem_unitary a θ)).1

/-- The exponentiated colour generator acting on the Hilbert completion. -/
noncomputable def colourGroupActHilbert (a : Fin 3) (θ : ℝ) :
    fundHilbert d →L[ℂ] fundHilbert d :=
  hilbActCLM (colourGroupElement a θ) (colourGroupElement_isometry a θ)

theorem colourGroupActHilbert_apply (a : Fin 3) (θ : ℝ) (f : fundHilbert d) :
    colourGroupActHilbert a θ f = hilbActOp (colourGroupElement a θ)
      (colourGroupElement_isometry a θ) f := rfl

theorem colourGroupActHilbert_inner (a : Fin 3) (θ : ℝ) (f g : fundHilbert d) :
    inner ℂ (colourGroupActHilbert a θ f) (colourGroupActHilbert a θ g) = inner ℂ f g := by
  rw [colourGroupActHilbert_apply, colourGroupActHilbert_apply]
  exact hilbActOp_inner _ (colourGroupElement_isometry a θ) f g

/-- **The exponentiated colour action is an isometry of the Hilbert completion.** -/
theorem colourGroupActHilbert_norm (a : Fin 3) (θ : ℝ) (f : fundHilbert d) :
    ‖colourGroupActHilbert a θ f‖ = ‖f‖ := by
  rw [colourGroupActHilbert_apply]
  exact hilbActOp_norm _ (colourGroupElement_isometry a θ) f

/-- **The group law on the completion**: `U(s) U(t) = U(s + t)`. -/
theorem colourGroupActHilbert_mul (a : Fin 3) (s t : ℝ) :
    colourGroupActHilbert (d := d) a s * colourGroupActHilbert a t
      = colourGroupActHilbert a (s + t) := by
  rw [colourGroupActHilbert, colourGroupActHilbert, colourGroupActHilbert]
  rw [hilbActCLM_mul (colourGroupElement a s) (colourGroupElement a t)
    (colourGroupElement_isometry a s) (colourGroupElement_isometry a t)
    (eucMatCLM_inner_comp (colourGroupElement a s) (colourGroupElement a t)
      (colourGroupElement_isometry a s) (colourGroupElement_isometry a t))]
  exact hilbActCLM_congr (colourGroupElement_mul a s t) _
    (colourGroupElement_isometry a (s + t))

/-- **The exponentiated colour group acts by genuine unitary operators** on the Hilbert
completion: the adjoint of `U(θ)` is `U(−θ)` and both products are the identity. -/
theorem colourGroupActHilbert_mem_unitary (a : Fin 3) (θ : ℝ) :
    colourGroupActHilbert (d := d) a θ ∈ unitary (fundHilbert d →L[ℂ] fundHilbert d) := by
  have hU := Unitary.mem_iff.mp (colourGroupElement_mem_unitary a θ)
  have hstar : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM (star (colourGroupElement a θ)) v)
        (eucMatCLM (star (colourGroupElement a θ)) w) = inner ℂ v w := by
    refine eucMatCLM_inner_of_unitary ?_
    rw [star_star]
    exact hU.2
  have hT : colourGroupActHilbert (d := d) a θ
      = hilbActCLM (colourGroupElement a θ) (colourGroupElement_isometry a θ) := rfl
  have hstar_eq : star (hilbActCLM (d := d) (colourGroupElement a θ)
        (colourGroupElement_isometry a θ)) = hilbActCLM (star (colourGroupElement a θ)) hstar := by
    rw [ContinuousLinearMap.star_eq_adjoint, hilbActCLM_adjoint_eq]
  rw [Unitary.mem_iff]
  constructor
  · rw [hT, hstar_eq]
    rw [hilbActCLM_mul (star (colourGroupElement a θ)) (colourGroupElement a θ) hstar
      (colourGroupElement_isometry a θ)
      (eucMatCLM_inner_comp (star (colourGroupElement a θ)) (colourGroupElement a θ)
        hstar (colourGroupElement_isometry a θ))]
    rw [hilbActCLM_congr hU.1 _ eucMatCLM_one_inner]
    exact hilbActCLM_one eucMatCLM_one_inner
  · rw [hT, hstar_eq]
    rw [hilbActCLM_mul (colourGroupElement a θ) (star (colourGroupElement a θ))
      (colourGroupElement_isometry a θ) hstar
      (eucMatCLM_inner_comp (colourGroupElement a θ) (star (colourGroupElement a θ))
        (colourGroupElement_isometry a θ) hstar)]
    rw [hilbActCLM_congr hU.2 _ eucMatCLM_one_inner]
    exact hilbActCLM_one eucMatCLM_one_inner


/-! #### Closedness of the bound: the Friedrichs side

`gap_closed_in_coreLp` is the statement a Friedrichs-type extension consumes.  The inequality
`K‖·‖² ≤ q` is preserved when the sequence converges in the completion and the form values converge
to `L` — no continuity of `q` on the core is assumed, only that its values along the sequence
converge.  That is exactly what a closure argument can supply, and exactly what is *missing* if one
tries to pass `root_spectral_gap` to limits without it.

Two consequences: the S2 gap itself holds at such a limit (`root_spectral_gap_closed`), and so does
the ground threshold of any restricted domination certificate (`root_ground_bound_closed`).

**Boundary.**  This is closedness — lower semicontinuity — of the *bound*, not the construction of a
self-adjoint Friedrichs extension: no operator is produced here, and the "form domain" is still `ℓ²`
together with "the defining series is finite", not a completed form space.
-/

/-- The embedding is additive. -/
theorem coreToLp_add (a b : CoreCoeff d) : coreToLp (a + b) = coreToLp a + coreToLp b := by
  ext n
  rw [coreToLp_apply, lp.coeFn_add, Pi.add_apply, coreToLp_apply, coreToLp_apply,
    Finsupp.add_apply]

/-- The embedding is additive on differences. -/
theorem coreToLp_sub (a b : CoreCoeff d) : coreToLp (a - b) = coreToLp a - coreToLp b := by
  ext n
  rw [coreToLp_apply, lp.coeFn_sub, Pi.sub_apply, coreToLp_apply, coreToLp_apply,
    Finsupp.sub_apply]

/-- **The core norm is continuous along `ℓ²` limits**: if `coreNormSq (s k − c) → 0` then
`coreNormSq (s k) → coreNormSq c`.  The isometry `norm_coreToLp_sq` turns the coefficient norm into
the `ℓ²` norm, along which the norm (and its square) is continuous. -/
theorem coreNormSq_tendsto {s : ℕ → CoreCoeff 24} {c : CoreCoeff 24}
    (h : Filter.Tendsto (fun k => coreNormSq (s k - c)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => coreNormSq (s k)) Filter.atTop (nhds (coreNormSq c)) := by
  have hd : Filter.Tendsto (fun k => coreToLp (s k - c)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnn : Filter.Tendsto (fun k => ‖coreToLp (s k - c)‖ ^ 2) Filter.atTop (nhds 0) := by
      simpa [norm_coreToLp_sq] using h
    have hsqrt : Filter.Tendsto (fun k => Real.sqrt (‖coreToLp (s k - c)‖ ^ 2))
        Filter.atTop (nhds 0) := by
      simpa using hnn.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hconv : Filter.Tendsto (fun k => coreToLp (s k)) Filter.atTop (nhds (coreToLp c)) := by
    have := hd.add (tendsto_const_nhds (x := coreToLp c))
    simpa [coreToLp_sub, sub_add_cancel] using this
  have := (hconv.norm).pow 2
  simpa [norm_coreToLp_sq] using this

/-- **The lower bound is closed under `ℓ²` limits.**  If `K * coreNormSq (s k) ≤ q (s k)` holds
along a sequence whose images converge to `f` in the completion, and the form values converge to
`L`, then `K * ‖f‖² ≤ L`.  Only convergence of `q` along the sequence is used — not continuity of
`q` — so this is available for forms that are nowhere continuous on the core. -/
theorem gap_closed_in_coreLp {q : CoreCoeff 24 → ℝ} {K : ℝ} {s : ℕ → CoreCoeff 24}
    (hbound : ∀ k, K * coreNormSq (s k) ≤ q (s k)) {f : coreLp 24}
    (hconv : Filter.Tendsto (fun k => coreToLp (s k)) Filter.atTop (nhds f))
    {L : ℝ} (hq : Filter.Tendsto (fun k => q (s k)) Filter.atTop (nhds L)) :
    K * ‖f‖ ^ 2 ≤ L := by
  have hlim : Filter.Tendsto (fun k => K * ‖coreToLp (s k)‖ ^ 2) Filter.atTop
      (nhds (K * ‖f‖ ^ 2)) := by
    have h2 : Filter.Tendsto (fun k => ‖coreToLp (s k)‖ ^ 2) Filter.atTop (nhds (‖f‖ ^ 2)) :=
      (hconv.norm).pow 2
    simpa using (tendsto_const_nhds (x := K)).mul h2
  refine le_of_tendsto_of_tendsto hlim hq (Filter.Eventually.of_forall fun k => ?_)
  simpa [norm_coreToLp_sq] using hbound k

/-- **The S2 gap is closed under `ℓ²` limits**: the right-hand side of `root_spectral_gap` is known
only on the core, but the *inequality* passes to the completion along a form-convergent root-domain
sequence.  This is the Friedrichs-type statement the extension question needs — lower
semicontinuity of the form along core sequences, with no continuity of `quadForm (ymHamiltonian …)`
assumed. -/
theorem root_spectral_gap_closed (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (RI : RootModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (s : ℕ → CoreCoeff 24) (hs : ∀ k, s k ∈ rootDomain)
    {f : coreLp 24} (hconv : Filter.Tendsto (fun k => coreToLp (s k)) Filter.atTop (nhds f))
    {L : ℝ}
    (hq : Filter.Tendsto (fun k => quadForm (ymHamiltonian Φ fabc) (RI.toCore (s k)))
      Filter.atTop (nhds L)) :
    ((c₁ * refGap ω - quarticShift (d := 24) T g) / 48) * ‖f‖ ^ 2 ≤ L :=
  gap_closed_in_coreLp (q := fun c => quadForm (ymHamiltonian Φ fabc) (RI.toCore c))
    (K := (c₁ * refGap ω - quarticShift (d := 24) T g) / 48)
    (fun k => root_spectral_gap Φ fabc RI hω hg hc₁ hω₁ (s k) (hs k)) hconv hq

/-- **Any restricted domination certificate is closed under `ℓ²` limits**: the ground threshold of a
`RootFormDomination` passes to the completion the same way.  Stated for a general form `q`, so it
applies to whatever the certificate is instantiated at. -/
theorem root_ground_bound_closed {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {q : CoreCoeff 24 → ℝ} (D : RootFormDomination ω q) (s : ℕ → CoreCoeff 24)
    (hs : ∀ k, s k ∈ rootDomain) {f : coreLp 24}
    (hconv : Filter.Tendsto (fun k => coreToLp (s k)) Filter.atTop (nhds f)) {L : ℝ}
    (hq : Filter.Tendsto (fun k => q (s k)) Filter.atTop (nhds L)) :
    (D.c₁ * refEnergy ω 0 - D.c₂) * ‖f‖ ^ 2 ≤ L :=
  gap_closed_in_coreLp (q := q) (K := D.c₁ * refEnergy ω 0 - D.c₂)
    (fun k => root_ground_bound ω hω D (s k) (hs k)) hconv hq

/-! #### The certificate inside the gap chain

`s2FormDomination` is an ordinary `FormDomination`, so the chapter's chain applies to it
without any restatement of its own: its ratio and shift are the derived numbers below, its two
thresholds are `ground_bound`/`excited_bound` (`s2_ground_threshold`, `s2_excited_threshold`),
and their separation is the chain's `certified_separation` with the S2 constants substituted.
The last two theorems are the usable form: the excited sector gains `c₁ Δ_ref / 48` per unit
norm, and that gain is *positive* exactly when the barrier shift is smaller than it. -/

/-- The certificate's ratio is the S2 constant: `c₁/48`. -/
theorem s2FormDomination_c₁ (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ}
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₁ = c₁ / 48 := rfl

/-- The certificate's shift is `(c₁ μ₀ + quarticShift)/48`. -/
theorem s2FormDomination_c₂ (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ}
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₂
      = (c₁ * refEnergy ω 0 + quarticShift (d := 24) T g) / 48 := rfl

/-- **The chain's certified separation, instantiated at the S2 certificate**: the ground and
excited comparison thresholds differ by `c₁/48 · Δ_ref`. -/
theorem s2_certified_separation (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ}
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    ((s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₁ * refEnergy ω 0
        - (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₂)
      + (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₁ * refGap ω
      = (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₁
          * (refEnergy ω 0 + refGap ω)
        - (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₂ :=
  certified_separation _

/-- The S2 separation is strictly positive: `0 < (c₁/48) · Δ_ref`. -/
theorem s2_separation_pos (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    0 < (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).c₁ * refGap ω := by
  have h := mul_pos (s2FormDomination Φ fabc MI (T := T) (g := g) hg hc₁ hω₁).hc₁
    (refGap_pos hω)
  simpa using h

/-- **The S2 gap in the shape the chain uses** (`quartic_certified_gap`): on the
vacuum-orthogonal sector the Yang–Mills form is at least `c₁ Δ_ref / 48` per unit norm, up to the
barrier shift `quarticShift / 48`. -/
theorem s2_certified_gap (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (MI : ModeIdentification Φ fabc) {ω : Fin 24 → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin 24)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff 24) (hc : c 0 = 0) :
    c₁ / 48 * refGap ω * coreNormSq c
      ≤ quadForm (ymHamiltonian Φ fabc) (MI.toCore c)
        + (quarticShift (d := 24) T g / 48) * coreNormSq c := by
  have h := s2_excited_threshold Φ fabc MI (T := T) (g := g) hω hg hc₁ hω₁ c hc
  nlinarith

/-- **When the S2 threshold is positive**: the excited comparison threshold is strictly positive
exactly when the reference gap, scaled by the ratio, exceeds the barrier's shift. -/
theorem s2_gap_threshold_pos {T : Finset (Fin 24)} {g : ℝ} {c₁ : ℝ} {ω : Fin 24 → ℝ}
    (hgap : quarticShift (d := 24) T g < c₁ * refGap ω) :
    0 < (c₁ * refGap ω - quarticShift (d := 24) T g) / 48 := by
  have h : 0 < c₁ * refGap ω - quarticShift (d := 24) T g := by linarith
  linarith

end ModeIdentification

/-! ## 4. The root sector: the quartic magnetic energy

The minimal non-abelian block is `su(2)`, with the Cartan generator `H = diag(1,−1)` and the two
root generators `E₊`, `E₋`.  A field with only off-diagonal components is
`A = a E₊ + b E₋`, i.e. `rootField a b`. -/

/-- The raising root generator `E₊`. -/
def rootPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The lowering root generator `E₋`. -/
def rootMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The Cartan generator `H = diag(1,−1)`. -/
def cartanH : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- A field in the **root plane**: `A = a E₊ + b E₋`, off-diagonal, i.e. with no Cartan part. -/
def rootField (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := a • rootPlus + b • rootMinus

theorem rootPlus_sq : rootPlus * rootPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_sq : rootMinus * rootMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootPlus_mul_rootMinus : rootPlus * rootMinus = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootPlus, rootMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_mul_rootPlus : rootMinus * rootPlus = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootPlus, rootMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- **[E₊, E₋] = H**: the bracket of the two root directions is Cartan. -/
theorem root_commutator : rootPlus * rootMinus - rootMinus * rootPlus = cartanH := by
  rw [rootPlus_mul_rootMinus, rootMinus_mul_rootPlus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartanH]

/-- **The bracket of two root fields is Cartan, with the root determinant as coefficient**:
`[a₁E₊ + b₁E₋, a₂E₊ + b₂E₋] = (a₁b₂ − b₁a₂) H`.  The commutator of two fields that have *only*
root components is nonzero precisely when the two root amplitudes are not parallel. -/
theorem rootField_commutator (a₁ b₁ a₂ b₂ : ℂ) :
    rootField a₁ b₁ * rootField a₂ b₂ - rootField a₂ b₂ * rootField a₁ b₁
      = (a₁ * b₂ - b₁ * a₂) • cartanH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootField, rootPlus, rootMinus, cartanH, Matrix.smul_apply] <;> ring

/-- The sum of the squared entries of a Cartan multiple: `‖c H‖² = 2‖c‖²`. -/
theorem sum_normSq_smul_cartanH (c : ℂ) :
    ∑ i, ∑ j, ‖(c • cartanH : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 = 2 * ‖c‖ ^ 2 := by
  simp [cartanH, Matrix.smul_apply, Fin.sum_univ_two]
  ring

/-- **The magnetic energy of the root sector is the square of the root determinant**:
`½ Σ_{ij} ‖[A₁,A₂]_{ij}‖² = ‖a₁b₂ − b₁a₂‖²`.  This is the quartic interaction: the energy of the
commutator term is a *square*, hence nonnegative, and of fourth order in the root fields. -/
theorem root_energy (a₁ b₁ a₂ b₂ : ℂ) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, ‖(rootField a₁ b₁ * rootField a₂ b₂
        - rootField a₂ b₂ * rootField a₁ b₁) i j‖ ^ 2 = ‖a₁ * b₂ - b₁ * a₂‖ ^ 2 := by
  rw [rootField_commutator, sum_normSq_smul_cartanH]
  ring

/-- The same for real root amplitudes: the energy is `(x₁y₂ − y₁x₂)²`. -/
theorem root_energy_real (x₁ y₁ x₂ y₂ : ℝ) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, ‖(rootField (x₁ : ℂ) (y₁ : ℂ) * rootField (x₂ : ℂ) (y₂ : ℂ)
        - rootField (x₂ : ℂ) (y₂ : ℂ) * rootField (x₁ : ℂ) (y₁ : ℂ)) i j‖ ^ 2
      = (x₁ * y₂ - y₁ * x₂) ^ 2 := by
  rw [root_energy]
  rw [show ((x₁ : ℂ) * y₂ - y₁ * x₂) = ((x₁ * y₂ - y₁ * x₂ : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The root energy vanishes exactly on parallel root amplitudes** — i.e. on the "commuting"
(rank-one, Cartan-after-a-gauge-rotation) configurations, and nowhere else. -/
theorem root_energy_eq_zero_iff (x₁ y₁ x₂ y₂ : ℝ) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, ‖(rootField (x₁ : ℂ) (y₁ : ℂ) * rootField (x₂ : ℂ) (y₂ : ℂ)
        - rootField (x₂ : ℂ) (y₂ : ℂ) * rootField (x₁ : ℂ) (y₁ : ℂ)) i j‖ ^ 2 = 0
      ↔ x₁ * y₂ = y₁ * x₂ := by
  rw [root_energy_real, sq_eq_zero_iff, sub_eq_zero]

/-- For hermitian root fields (`b = \bar a`, so `A† = A`) the energy is
`4 (Im (a₁ \bar a₂))²` — the quartic invariant of the off-diagonal sector. -/
theorem root_energy_hermitian (a₁ a₂ : ℂ) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, ‖(rootField a₁ (starRingEnd ℂ a₁) * rootField a₂ (starRingEnd ℂ a₂)
        - rootField a₂ (starRingEnd ℂ a₂) * rootField a₁ (starRingEnd ℂ a₁)) i j‖ ^ 2
      = 4 * (Complex.im (a₁ * starRingEnd ℂ a₂)) ^ 2 := by
  rw [root_energy]
  have h : a₁ * starRingEnd ℂ a₂ - starRingEnd ℂ a₁ * a₂
      = ((2 * (a₁ * starRingEnd ℂ a₂).im : ℝ) : ℂ) * Complex.I := by
    have hc := Complex.sub_conj (a₁ * starRingEnd ℂ a₂)
    simpa [map_mul] using hc
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hsq : |2 * (a₁ * starRingEnd ℂ a₂).im| ^ 2
      = 4 * (a₁ * starRingEnd ℂ a₂).im ^ 2 := by
    rw [abs_mul, mul_pow]
    norm_num
  rw [hsq]

/-! ## 4. The degree class the comparison calculation consumes

The comparison calculation is stated for a potential of **bounded polynomial degree**: it needs the
weight to grow at most quartically, so that it is dominated by the graph norm it is compared with.
This section records that the full nonabelian field strength lands in that class, component by
component and summed: `B` has total degree `≤ 2` in the `99` coordinates, and the magnetic weight
`W = Σ B² + 1` — the `W` of `2H + 1 = −Δ_S + W` — has total degree `≤ 4`.  The cubic terms are
the cross terms of `∂A` with `[A,A]` and the quartic ones are the square of `[A,A]`. -/

/-- The derivative part is linear. -/
theorem totalDegree_magDeriv_le (i : Fin 3) (a : Fin 8) : (magDeriv i a).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  rw [MvPolynomial.totalDegree_X]

/-- The commutator bilinear form is quadratic. -/
theorem totalDegree_magBilin_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (j k : Fin 3) (a : Fin 8) :
    (magBilin fabc j k a).totalDegree ≤ 2 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun c _ => ?_
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]

/-- The commutator part is quadratic. -/
theorem totalDegree_magComm_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    (magComm fabc i a).totalDegree ≤ 2 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  exact totalDegree_magBilin_le fabc j k a

/-- The field-strength component is at most quadratic: `∂A` contributes degree `1` and `[A,A]`
degree `2`, with no assumption on the structure constants. -/
theorem totalDegree_magPoly_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    (magPoly fabc i a).totalDegree ≤ 2 := by
  rw [magPoly_eq_deriv_add]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  exact max_le ((totalDegree_magDeriv_le i a).trans (by norm_num))
    (totalDegree_magComm_le fabc i a)

/-- Its square is quartic. -/
theorem totalDegree_magPoly_sq_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    ((magPoly fabc i a) ^ 2).totalDegree ≤ 4 := by
  rw [pow_two]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h := totalDegree_magPoly_le fabc i a
  omega

/-- **The comparison weight**: `W = Σ_m B_m² + 1`, over the same `24 = 3 × 8` field/colour pairs the
one-particle Hamiltonian sums over.  This is the potential in `2H + 1 = −Δ_S + W`. -/
noncomputable def magWeight (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : MvPolynomial (Fin 99) ℂ :=
  (∑ m : Fin 24, (magPoly fabc (decodeSpace m) (decodeColor m)) ^ 2) + 1

/-- **The field-strength polynomial lands in the comparison's degree class**: `W` is a polynomial of
total degree at most `4` in the `99` coordinates. -/
theorem totalDegree_magWeight_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    (magWeight fabc).totalDegree ≤ 4 := by
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  refine max_le ?_ ?_
  · refine (MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_).trans (le_refl 4)
    exact totalDegree_magPoly_sq_le fabc (decodeSpace m) (decodeColor m)
  · rw [show (1 : MvPolynomial (Fin 99) ℂ) = C 1 from rfl, MvPolynomial.totalDegree_C]
    norm_num

/-! ## 5. The weight is a nonnegative potential

The comparison also needs `W` to be a *potential*: nonnegative, so that it can only raise the
energy.
It is, for a structural reason — `W = Σ B² + 1` and every `B_m` has real coefficients, so at a real
configuration each square is a genuine real square.  This closes the "the field strength is a
legitimate potential" chain: `B` quadratic (degree class), `W` quartic and nonnegative. -/

/-- The unit polynomial has real coefficients. -/
theorem realCoeff_one : RealCoeff (1 : MvPolynomial (Fin 99) ℂ) := by
  rw [RealCoeff, starP]
  exact map_one _

/-- **The weight `W` has real coefficients**, being a sum of squares plus one. -/
theorem realCoeff_magWeight (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : RealCoeff (magWeight fabc) := by
  unfold magWeight
  refine RealCoeff.add ?_ realCoeff_one
  refine RealCoeff.sum fun m _ => ?_
  rw [pow_two]
  exact (realCoeff_magPoly fabc (decodeSpace m) (decodeColor m)).mul
    (realCoeff_magPoly fabc (decodeSpace m) (decodeColor m))

/-- A real-coefficient polynomial takes real values at real points: the imaginary part vanishes. -/
theorem RealCoeff.eval_im_eq_zero {p : MvPolynomial (Fin 99) ℂ} (hp : RealCoeff p) (x : Vd 99) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p).im = 0 := by
  have h := eval_starP p x
  rw [show starP p = p from hp] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The value of the weight at a real configuration, as a real number. -/
noncomputable def magWeightEval (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : Vd 99) : ℝ :=
  ((magWeight fabc).eval (fun i => ((x i : ℝ) : ℂ))).re

/-- A complex number with vanishing imaginary part has a real square: `z² = ↑(z.re)²`. -/
theorem eq_ofReal_sq_re {z : ℂ} (h : z.im = 0) : z ^ 2 = ((z.re ^ 2 : ℝ) : ℂ) := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h)
  rw [hz, ← Complex.ofReal_pow]
  simp

/-- **`W` at a real configuration is a sum of squares plus one.** -/
theorem magWeightEval_eq (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : Vd 99) :
    magWeightEval fabc x
      = (∑ m : Fin 24, ((magPoly fabc (decodeSpace m) (decodeColor m)).eval
          (fun i => ((x i : ℝ) : ℂ))).re ^ 2) + 1 := by
  have hsum : (magWeight fabc).eval (fun i => ((x i : ℝ) : ℂ))
      = ((∑ m : Fin 24, ((magPoly fabc (decodeSpace m) (decodeColor m)).eval
          (fun i => ((x i : ℝ) : ℂ))).re ^ 2 : ℝ) : ℂ) + 1 := by
    simp only [magWeight, map_add, map_sum, map_one, map_pow]
    congr 1
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact eq_ofReal_sq_re (RealCoeff.eval_im_eq_zero
      (realCoeff_magPoly fabc (decodeSpace m) (decodeColor m)) x)
  rw [magWeightEval, hsum]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]

/-- **`W ≥ 0`**: the quartic weight is a nonnegative potential.  Together with
`totalDegree_magWeight_le` this is the pair of facts the comparison calculation asks of the field
strength: the shape (quartic) and the sign. -/
theorem magWeightEval_nonneg (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : Vd 99) :
    0 ≤ magWeightEval fabc x := by
  rw [magWeightEval_eq]
  have h : 0 ≤ ∑ m : Fin 24, ((magPoly fabc (decodeSpace m) (decodeColor m)).eval
      (fun i => ((x i : ℝ) : ℂ))).re ^ 2 := Finset.sum_nonneg fun m _ => sq_nonneg _
  linarith

/-! ##### The meson square splits as `1 ⊕ 3`

The singlet is one line of the `ℂ² ⊗ ℂ²` fibre (`mesonSinglet_eq_span`).  This section exhibits the
other summand: the symmetric tensors, invariant under every total action because that action is
invariant under the slot swap, of dimension `4 - 1 = 3`.  The decomposition is `1 ⊕ 3` —
antisymmetric singlet plus symmetric triplet — and both summands are subrepresentations.
-/

/-- The slot swap on the row-major index of `ℂ² ⊗ ℂ²`. -/
def mesonFlipIdx (i : Fin 4) : Fin 4 := ⟨2 * (i.val % 2) + i.val / 2, by omega⟩

/-- The slot swap is an involution on the four row-major indices. -/
@[simp] theorem mesonFlipIdx_involutive (i : Fin 4) : mesonFlipIdx (mesonFlipIdx i) = i := by
  ext
  simp only [mesonFlipIdx]
  omega

/-- The slot swap as a vector operation on `ℂ² ⊗ ℂ²`. -/
def mesonFlipVec (v : colourVec 4) : colourVec 4 :=
  WithLp.toLp 2 fun i => WithLp.ofLp v (mesonFlipIdx i)

/-- Component `i` of the slot-swapped vector is component `mesonFlipIdx i` of `v`. -/
@[simp] theorem mesonFlipVec_ofLp (v : colourVec 4) (i : Fin 4) :
    WithLp.ofLp (mesonFlipVec v) i = WithLp.ofLp v (mesonFlipIdx i) := rfl

/-- **The slot swap is an involution.** -/
theorem mesonFlipVec_involutive (v : colourVec 4) : mesonFlipVec (mesonFlipVec v) = v := by
  apply WithLp.ofLp_injective
  funext i
  simp

/-- The **symmetric part** of the meson square fibre. -/
def mesonSymm : Submodule ℂ (colourVec 4) where
  carrier := {v | ∀ i, WithLp.ofLp v (mesonFlipIdx i) = WithLp.ofLp v i}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro u w hu hw i
    simp only [WithLp.ofLp_add, Pi.add_apply]
    rw [hu i, hw i]
  smul_mem' := by
    intro c u hu i
    simp only [WithLp.ofLp_smul, Pi.smul_apply]
    rw [hu i]

/-- The **antisymmetric part** of the meson square fibre. -/
def mesonAlt : Submodule ℂ (colourVec 4) where
  carrier := {v | ∀ i, WithLp.ofLp v (mesonFlipIdx i) = -WithLp.ofLp v i}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro u w hu hw i
    simp only [WithLp.ofLp_add, Pi.add_apply]
    rw [hu i, hw i]
    ring
  smul_mem' := by
    intro c u hu i
    simp only [WithLp.ofLp_smul, Pi.smul_apply]
    rw [hu i, smul_neg]

/-- A vector that is both symmetric and antisymmetric vanishes. -/
theorem meson_disjoint : mesonAlt ⊓ mesonSymm = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  obtain ⟨hva, hvs⟩ := Submodule.mem_inf.mp hv
  have hv0 : v = 0 := by
    apply WithLp.ofLp_injective
    funext i
    have h1 : WithLp.ofLp v (mesonFlipIdx i) = -WithLp.ofLp v i := hva i
    have h2 : WithLp.ofLp v (mesonFlipIdx i) = WithLp.ofLp v i := hvs i
    have hx : WithLp.ofLp v i = -WithLp.ofLp v i := by
      calc WithLp.ofLp v i = WithLp.ofLp v (mesonFlipIdx i) := h2.symm
        _ = -WithLp.ofLp v i := h1
    have h3 : (2 : ℂ) * WithLp.ofLp v i = 0 := by
      rw [two_mul]
      linear_combination hx
    have h4 : WithLp.ofLp v i = 0 := (mul_eq_zero.mp h3).resolve_left two_ne_zero
    rw [h4]
    simp
  rw [hv0]
  exact Submodule.zero_mem _

/-- Every vector of the square fibre splits into a symmetric and an antisymmetric part. -/
theorem meson_sup : mesonAlt ⊔ mesonSymm = ⊤ := by
  refine le_antisymm le_top fun v _ => ?_
  have ha : (2⁻¹ : ℂ) • (v - mesonFlipVec v) ∈ mesonAlt := by
    intro i
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sub, Pi.sub_apply, Pi.smul_apply,
      mesonFlipVec_ofLp, smul_eq_mul]
    rw [mesonFlipIdx_involutive]
    ring
  have hs : (2⁻¹ : ℂ) • (v + mesonFlipVec v) ∈ mesonSymm := by
    intro i
    simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Pi.add_apply, Pi.smul_apply,
      mesonFlipVec_ofLp, smul_eq_mul]
    rw [mesonFlipIdx_involutive]
    ring
  refine Submodule.mem_sup.mpr ⟨_, ha, _, hs, ?_⟩
  have hsum : (v - mesonFlipVec v) + (v + mesonFlipVec v) = (2 : ℂ) • v := by
    rw [two_smul]
    abel
  calc (2⁻¹ : ℂ) • (v - mesonFlipVec v) + (2⁻¹ : ℂ) • (v + mesonFlipVec v)
      = (2⁻¹ : ℂ) • ((v - mesonFlipVec v) + (v + mesonFlipVec v)) := (smul_add ..).symm
    _ = (2⁻¹ : ℂ) • ((2 : ℂ) • v) := by rw [hsum]
    _ = v := by rw [smul_smul]; norm_num

/-- **The meson fibre is the direct sum of its antisymmetric and symmetric parts.** -/
theorem meson_isCompl : IsCompl mesonAlt mesonSymm :=
  ⟨disjoint_iff.mpr meson_disjoint, codisjoint_iff.mpr meson_sup⟩

/-- The antisymmetric part is exactly the singlet line. -/
theorem mesonAlt_eq_span : mesonAlt = Submodule.span ℂ {mesonSingletVec} := by
  refine le_antisymm (fun v hv => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    have hzero : ∀ i : Fin 4, mesonFlipIdx i = i → WithLp.ofLp v i = 0 := by
      intro i hi
      have h := hv i
      rw [hi] at h
      have hx : WithLp.ofLp v i = -WithLp.ofLp v i := h
      have h3 : (2 : ℂ) * WithLp.ofLp v i = 0 := by
        rw [two_mul]
        linear_combination hx
      exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
    have h0 : WithLp.ofLp v 0 = 0 := by
      refine hzero 0 ?_
      simp [mesonFlipIdx]
    have h3 : WithLp.ofLp v 3 = 0 := by
      refine hzero 3 ?_
      simp [mesonFlipIdx]
    have h1 : WithLp.ofLp v 1 = -WithLp.ofLp v 2 := by
      have h := hv 2
      simp [mesonFlipIdx] at h
      linear_combination h
    refine ⟨WithLp.ofLp v 1, ?_⟩
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [mesonSingletVec, mesonCoeff, h0, h1, h3]
  · rw [Submodule.span_singleton_le_iff_mem]
    intro i
    fin_cases i <;> simp [mesonSingletVec, mesonCoeff, mesonFlipIdx]

/-- The antisymmetric part of the meson square is one-dimensional. -/
theorem mesonAlt_finrank : Module.finrank ℂ mesonAlt = 1 := by
  rw [mesonAlt_eq_span, finrank_span_singleton mesonSingletVec_ne_zero]

/-- **The symmetric part of the meson square is three-dimensional**: the triplet. -/
theorem mesonSymm_finrank : Module.finrank ℂ mesonSymm = 3 := by
  have h := Submodule.finrank_add_eq_of_isCompl meson_isCompl
  rw [mesonAlt_finrank] at h
  have h4 : Module.finrank ℂ (colourVec 4) = 4 := by simp [colourVec]
  omega

/-- The total colour action as a vector operation on the meson fibre. -/
def mesonAct (a : Fin 3) (v : colourVec 4) : colourVec 4 :=
  WithLp.toLp 2 ((mesonRep a).mulVec (WithLp.ofLp v))

/-- The components of the total action are the matrix–vector product. -/
@[simp] theorem mesonAct_ofLp (a : Fin 3) (v : colourVec 4) :
    WithLp.ofLp (mesonAct a v) = (mesonRep a).mulVec (WithLp.ofLp v) := rfl

/-- The total action is invariant under the slot swap. -/
theorem mesonRep_flip_row (a : Fin 3) (i j : Fin 4) :
    mesonRep a (mesonFlipIdx i) j = mesonRep a i (mesonFlipIdx j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [mesonRep, mesonFlipIdx, mesonSlotFst, mesonSlotSnd, fundRep, pauli]

/-- The permutation, inserted in the sum as a reindexing. -/
theorem meson_sum_flip (f : Fin 4 → ℂ) :
    (∑ j : Fin 4, f (mesonFlipIdx j)) = ∑ k : Fin 4, f k :=
  Equiv.sum_comp (Function.Involutive.toPerm mesonFlipIdx mesonFlipIdx_involutive) f

/-- **The symmetric part is closed under every total colour action.** -/
theorem mesonAct_mem_symm (a : Fin 3) {v : colourVec 4} (hv : v ∈ mesonSymm) :
    mesonAct a v ∈ mesonSymm := by
  intro i
  simp only [mesonAct_ofLp, Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => by rw [mesonRep_flip_row])]
  rw [(meson_sum_flip
    (fun k => mesonRep a i (mesonFlipIdx k) * WithLp.ofLp v k)).symm]
  simp only [mesonFlipIdx_involutive]
  exact Finset.sum_congr rfl fun k _ => by rw [hv k]

/-- **The antisymmetric part is closed under every total colour action.** -/
theorem mesonAct_mem_alt (a : Fin 3) {v : colourVec 4} (hv : v ∈ mesonAlt) :
    mesonAct a v ∈ mesonAlt := by
  intro i
  simp only [mesonAct_ofLp, Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => by rw [mesonRep_flip_row])]
  rw [(meson_sum_flip
    (fun k => mesonRep a i (mesonFlipIdx k) * WithLp.ofLp v k)).symm]
  simp only [mesonFlipIdx_involutive]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hv k])]
  simp only [mul_neg, Finset.sum_neg_distrib]

end

end BookProof.YangMillsFieldStrengthSplit
