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
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.FarisLavine

noncomputable section

set_option maxHeartbeats 1000000

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

end

end BookProof.YangMillsFieldStrengthSplit
