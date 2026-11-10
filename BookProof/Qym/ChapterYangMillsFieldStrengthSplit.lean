import Mathlib
import BookProof.Qym.ChapterYangMillsHermite

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
   retained in the form on the core and are not absorbed into a quadratic model.
4. **The root sector is quartic.**  In the two-dimensional root plane of `su(2)`
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
comparison calculation, not a coercivity estimate: it does not bound the cubic and quartic parts
by the quadratic form and says nothing about cutoff uniformity — those remain separate inputs.
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
