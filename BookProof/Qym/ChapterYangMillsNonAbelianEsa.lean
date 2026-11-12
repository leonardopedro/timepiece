import Mathlib
import BookProof.Toolbox.ChapterHermiteGraphApprox
import BookProof.Qym.ChapterYangMillsHermite
import BookProof.Qym.ChapterYangMillsFieldStrengthSplit
import BookProof.ChapterEsaOneParticleDGamma

/-!
# The non-abelian Yang–Mills one-particle Hamiltonian is essentially self-adjoint

The tree had essential self-adjointness of the gauge-fixed Yang–Mills Hamiltonian only in the
abelian (quadratic) case (`BookProof/Qym/ChapterYangMillsAbelianEsa.lean`).  The Kato-type
theorem of `BookProof/Toolbox/ChapterDegKatoEsa.lean` and its transfer to the Gauss–polynomial core
(`BookProof/Toolbox/ChapterHermiteGraphApprox.lean`) hold for an arbitrary real polynomial potential
`W ≥ 1` and an arbitrary set `S` of momentum-carrying coordinates.  This module instantiates
them for the **non-abelian** Hamiltonian `ymHamiltonian`, for arbitrary real structure
constants `f_{abc}`:

* `deficiencyTrivialAt_of_esa` — for a symmetric operator on a Hilbert space, trivial
  deficiency at `± i` gives trivial deficiency at every non-real point;
* `essentiallySelfAdjointOn_affine` — hence `a • K + b` (`a > 0`, `b` real) is essentially
  self-adjoint whenever `K` is;
* `weylPoly_eq_hamCoreS`, `weylPoly_esa` — any Weyl-type operator `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j²`
  on the Gauss–polynomial core, with momenta in distinct coordinates and real polynomial
  fields `Φ_j`, satisfies `2H + 1 = −Δ_S + W` with `W = Σ_j Φ_j² + 1`, hence is essentially
  self-adjoint;
* `ymHamiltonian_eq_weylPoly` — the non-abelian Yang–Mills Hamiltonian is such an operator,
  with `S` the 24 gauge-field coordinates `A_{j,a}` and `Φ` the 24 magnetic fields `B_{ia}`;
* **`ym_h_esa`** — the non-abelian gauge-fixed Yang–Mills one-particle Hamiltonian
  `H = ½ Σ π² + ½ Σ B²` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝ⁹⁹)`;
* **`ym_dGamma_esa`** — its second quantization `dΓ(H)` (one-particle `H` enclosed between a
  creation on the left and an annihilation on the right) is essentially self-adjoint on the
  finite-particle domain over that core, by the lift of `BookProof/ChapterEsaOneParticleDGamma`;
* **`colourFieldOp_esa`** — the direct sum of `N` copies of `H` on the coloured core is essentially
  self-adjoint, by the single-component deficiency argument (each component of a deficiency
  vector is a deficiency vector of `H`);
* **`deficiencyTrivialAt_of_symmetric_perturbation`** — a symmetric perturbation `K` (bounded or
  not, all that is used is `⟪K u, w⟫ = ⟪u, K w⟫`) adds no deficiency vector: both `w` and the
  graph limit of `A` are graph-limit pairs at the same level, uniqueness is `A`'s trivial
  deficiency, and the reality of `⟪z, u⟫` forces `d ‖w‖² = 0`;
* **`colouredHamiltonian_esa`** — hence `H ⊗ 1 + 1 ⊗ C` on `L²(ℝ⁹⁹; ℂ^N)` is essentially
  self-adjoint for every Hermitian colour matrix `C`, with no relative bound and no comparison
  operator.  This is the statement the split chapter's `colouredHamiltonian_symmetricOn` stops
  short of; it lives here because this module imports the split chapter.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.YangMillsNonAbelianEsa

open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.HermiteGraphApprox
open BookProof.TensorCore BookProof.DirectSumEsa BookProof.SecondQuantizationCore

noncomputable section

/-! ## 1. Essential self-adjointness is stable under positive affine maps -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

/-- For a symmetric operator on a Hilbert space, essential self-adjointness (trivial
deficiency at `± i`) gives trivial deficiency at **every** non-real point. -/
theorem deficiencyTrivialAt_of_esa (K : D →ₗ[ℂ] F) (hK : SymmetricOn D K)
    (hesa : EssentiallySelfAdjointOn D K) {σ : ℂ} (hσ : σ.im ≠ 0) :
    DeficiencyTrivialAt D K σ := by
  have hI : ((1 : ℝ) : ℂ) * Complex.I = Complex.I := by simp
  have hdense : Dense (Set.range fun x : D => K x - (((1 : ℝ) : ℂ) * Complex.I) • (x : F)) := by
    rw [hI]
    refine dense_range_of_deficiencyTrivialAt K Complex.I ?_
    rw [Complex.conj_I]
    exact hesa.2
  refine deficiencyTrivialAt_of_dense_range K hK 1 one_ne_zero σ hσ hdense ?_
  rw [hI]
  exact hesa.1

/-- **A positive affine image of an essentially self-adjoint operator is essentially
self-adjoint**: `a • K + b` for real `a > 0` and real `b`. -/
theorem essentiallySelfAdjointOn_affine (K : D →ₗ[ℂ] F) (hK : SymmetricOn D K)
    (hesa : EssentiallySelfAdjointOn D K) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    EssentiallySelfAdjointOn D ((a : ℂ) • K + (b : ℂ) • D.subtype) := by
  have key : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt D ((a : ℂ) • K + (b : ℂ) • D.subtype) z := by
    intro z hz w hw
    have hσ : ((z - b) / a).im ≠ 0 := by
      rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_ne_zero hz ha.ne'
    refine deficiencyTrivialAt_of_esa K hK hesa hσ w fun v => ?_
    have hv := hw v
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_add_left,
      inner_smul_left, inner_smul_left, Complex.conj_ofReal, Complex.conj_ofReal,
      Submodule.subtype_apply] at hv
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    field_simp
    linear_combination hv
  exact ⟨key _ (by simp), key _ (by simp)⟩

end Abstract

/-! ## 2. Transport of polynomial operators to the core, in any dimension -/

section Transport

variable {d : ℕ}

theorem equiv_pgLp_d (p : MvPolynomial (Fin d) ℂ) :
    (coreRepPoly d).equiv p = ⟨pgLp p, pgLp_mem_core p⟩ :=
  Subtype.ext ((coreRepPoly d).coe_equiv p)

theorem equiv_symm_pgLp_d (p : MvPolynomial (Fin d) ℂ) :
    (coreRepPoly d).equiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  rw [← equiv_pgLp_d p, LinearEquiv.symm_apply_apply]

theorem op_pgLp_d (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin d) ℂ) :
    (coreRepPoly d).op T ⟨pgLp p, pgLp_mem_core p⟩ = ⟨pgLp (T p), pgLp_mem_core _⟩ := by
  refine Subtype.ext ?_
  rw [CoreRep.coe_op, equiv_symm_pgLp_d]

/-- The momentum operator squared is the twisted second derivative. -/
theorem momOp_momOp_d (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j (momOp j p) = -coreD j (coreD j p) := by
  have hstep : ∀ r : MvPolynomial (Fin d) ℂ, momOp j r = (-Complex.I) • coreD j r := by
    intro r
    rw [momOp_apply, coreD]
    congr 1
    congr 1
    rw [MvPolynomial.smul_eq_C_mul]
    norm_num
  rw [hstep, hstep, coreD_smul, smul_smul]
  have hII : (-Complex.I) * (-Complex.I) = -1 := by
    simp [Complex.I_mul_I]
  rw [hII]
  module

end Transport

/-! ## 3. A Weyl-type operator with polynomial fields is a degenerate Schrödinger operator -/

section General

variable {d k r : ℕ}

/-- The Weyl-type operator `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j²` on the Gauss–polynomial core of
`L²(ℝᵈ)`: momenta in the coordinates `idx m`, multiplication by the polynomials `Φ_j`. -/
def weylPoly (idx : Fin k → Fin d) (Φ : Fin r → MvPolynomial (Fin d) ℂ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  weylOp (fun m => (coreRepPoly d).op (momOp (idx m))) (fun j => (coreRepPoly d).op (mulOp (Φ j)))

/-- The potential `W = Σ_j Φ_j² + 1`. -/
def weylPotPoly (Φ : Fin r → MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  (∑ j : Fin r, Φ j * Φ j) + C ((1 : ℝ) : ℂ)

theorem realCoeff_weylPotPoly {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) :
    RealCoeff (weylPotPoly Φ) :=
  (RealCoeff.sum fun j _ => (hΦ j).mul (hΦ j)).add (realCoeff_C_real' 1)

theorem polyW_weylPotPoly {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j))
    (x : Vd d) : polyW (weylPotPoly Φ) x = (∑ j : Fin r, (polyW (Φ j) x) ^ 2) + 1 := by
  have hphi : ∀ j : Fin r, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (Φ j)
      = ((polyW (Φ j) x : ℝ) : ℂ) :=
    fun j => (polyW_ofReal (hΦ j) x).symm
  have key : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (weylPotPoly Φ)
      = (∑ j : Fin r, ((polyW (Φ j) x : ℝ) : ℂ) ^ 2) + ((1 : ℝ) : ℂ) := by
    simp only [weylPotPoly, map_add, map_sum, map_mul, MvPolynomial.eval_C, hphi, sq]
  have hcast : (∑ j : Fin r, ((polyW (Φ j) x : ℝ) : ℂ) ^ 2) + ((1 : ℝ) : ℂ)
      = (((∑ j : Fin r, (polyW (Φ j) x) ^ 2) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [polyW, key, hcast, Complex.ofReal_re]

/-- The potential is bounded below by `1`. -/
theorem one_le_polyW_weylPotPoly {Φ : Fin r → MvPolynomial (Fin d) ℂ}
    (hΦ : ∀ j, RealCoeff (Φ j)) (x : Vd d) : 1 ≤ polyW (weylPotPoly Φ) x := by
  rw [polyW_weylPotPoly hΦ]
  have h : (0 : ℝ) ≤ ∑ j : Fin r, (polyW (Φ j) x) ^ 2 := by positivity
  linarith

theorem sum_momOp_eq_kinPolyS {idx : Fin k → Fin d} (hidx : Function.Injective idx)
    (p : MvPolynomial (Fin d) ℂ) :
    (∑ m : Fin k, momOp (idx m) (momOp (idx m) p)) = kinPolyS (Finset.image idx Finset.univ) p := by
  have h : ∀ m : Fin k, momOp (idx m) (momOp (idx m) p)
      = -coreD (idx m) (coreD (idx m) p) := fun m => momOp_momOp_d _ p
  rw [Finset.sum_congr rfl fun m _ => h m, kinPolyS,
    Finset.sum_image (fun a _ b _ hab => hidx hab)]
  simp only [Finset.sum_neg_distrib]

set_option maxHeartbeats 1000000 in
-- the identification unfolds the operator on the core through several coercions
/-- **A Weyl-type operator with polynomial fields is a degenerate Schrödinger operator.**  On
the Gauss–polynomial core, `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j² = ½(−Δ_S + W) − ½` with
`S = idx(Fin k)` (the coordinates must be distinct) and `W = Σ_j Φ_j² + 1`. -/
theorem weylPoly_eq_hamCoreS {idx : Fin k → Fin d} (hidx : Function.Injective idx)
    {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) :
    weylPoly idx Φ
      = (((1 / 2 : ℝ)) : ℂ) • hamCoreS (polyW (weylPotPoly Φ)) (continuous_polyW _)
          (expBounded_polyW _) (Finset.image idx Finset.univ)
        + (((-1 / 2 : ℝ)) : ℂ) • (polyGaussCore (d := d)).subtype := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  have hpgsum : ∀ (n : ℕ) (f : Fin n → MvPolynomial (Fin d) ℂ),
      (∑ i : Fin n, pgLp (f i)) = pgLp (∑ i : Fin n, f i) := by
    intro n f
    rw [← HermiteProductCore.pgMap_apply, map_sum]
    rfl
  have hmap : ∀ q : MvPolynomial (Fin d) ℂ, pgLp q = pgMap (d := d) q := fun _ => rfl
  have hlhs : weylPoly idx Φ ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (((1 / 2 : ℝ) : ℂ) • ((∑ m : Fin k, momOp (idx m) (momOp (idx m) p))
          + ∑ j : Fin r, Φ j * (Φ j * p))) := by
    have hpi : ∀ m : Fin k,
        (((coreRepPoly d).op (momOp (idx m)) ((coreRepPoly d).op (momOp (idx m))
            ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := d)) : L2d d)
          = pgLp (momOp (idx m) (momOp (idx m) p)) := by
      intro m
      rw [op_pgLp_d, op_pgLp_d]
    have hmag : ∀ j : Fin r,
        (((coreRepPoly d).op (mulOp (Φ j)) ((coreRepPoly d).op (mulOp (Φ j))
            ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := d)) : L2d d)
          = pgLp (Φ j * (Φ j * p)) := by
      intro j
      rw [op_pgLp_d, op_pgLp_d, mulOp_apply, mulOp_apply]
    rw [weylPoly, weylOp_apply, Finset.sum_congr rfl fun m _ => hpi m,
      Finset.sum_congr rfl fun j _ => hmag j, hpgsum, hpgsum]
    simp only [hmap, ← map_smul, ← map_add]
  have hrhs : ((((1 / 2 : ℝ)) : ℂ) • hamCoreS (polyW (weylPotPoly Φ)) (continuous_polyW _)
          (expBounded_polyW _) (Finset.image idx Finset.univ)
        + (((-1 / 2 : ℝ)) : ℂ) • (polyGaussCore (d := d)).subtype)
        ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (((1 / 2 : ℝ) : ℂ) • (kinPolyS (Finset.image idx Finset.univ) p
          + weylPotPoly Φ * p) + ((-1 / 2 : ℝ) : ℂ) • p) := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hamCoreS_pgLp,
      hamPolyS, potLp_polyW_eq (realCoeff_weylPotPoly hΦ), Submodule.subtype_apply]
    have hcoe : ((⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl
    rw [hcoe]
    simp only [hmap, ← map_smul, ← map_add]
  rw [hlhs, hrhs]
  congr 1
  rw [sum_momOp_eq_kinPolyS hidx, weylPotPoly]
  simp only [add_mul, Finset.sum_mul, mul_assoc]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  have hneg : (C (((-1 / 2 : ℝ)) : ℂ) : MvPolynomial (Fin d) ℂ) = -C (((1 / 2 : ℝ)) : ℂ) := by
    rw [← map_neg]
    congr 1
    push_cast
    ring
  rw [hneg, Complex.ofReal_one, map_one]
  ring

/-- **A Weyl-type operator with real polynomial fields and momenta in distinct coordinates is
essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᵈ)`.** -/
theorem weylPoly_esa {idx : Fin k → Fin d} (hidx : Function.Injective idx)
    {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (weylPoly idx Φ) := by
  rw [weylPoly_eq_hamCoreS hidx hΦ]
  exact essentiallySelfAdjointOn_affine _ (hamCoreS_symmetricOn _ _ _ _)
    (hamCoreS_esa (weylPotPoly Φ) (realCoeff_weylPotPoly hΦ) (one_le_polyW_weylPotPoly hΦ) _)
    (by norm_num) _

end General

/-! ## 4. The non-abelian Yang–Mills instance -/

/-- The coordinate of the `m`-th gauge-field component `A_{j,a}`. -/
def ymIdx (m : Fin 24) : Fin 99 := idxA (decodeSpace m) (decodeColor m)

theorem ymIdx_injective : Function.Injective ymIdx := by
  intro m m' h
  have := congrArg Fin.val h
  simp only [ymIdx, idxA, decodeSpace, decodeColor] at this
  apply Fin.ext
  omega

/-- The `m`-th magnetic-field polynomial `B_{ia}`. -/
def ymMag (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) : MvPolynomial (Fin 99) ℂ :=
  magPoly fabc (decodeSpace m) (decodeColor m)

/-- On the Gauss–polynomial core the Yang–Mills Hamiltonian is the Weyl-type operator with
momenta in the 24 gauge-field coordinates and the 24 magnetic fields as polynomials; hence
`2H + 1 = −Δ_S + W` with `W = Σ_{i,a} B_{ia}² + 1`. -/
theorem ymHamiltonian_eq_weylPoly (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ymHamiltonian (coreRepPoly 99) fabc = weylPoly ymIdx (ymMag fabc) := rfl

/-- **The field-strength polynomial in the comparison's notation.**  The weight `W` of
`2H + 1 = −Δ_S + W` is exactly `magWeight`: the sum of the squares of the `24` magnetic components,
the same terms the split `B = ∂A + [A,A]` and the degree bound of
`ChapterYangMillsFieldStrengthSplit` are stated for. -/
theorem magWeight_eq_sum_ymMag (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    BookProof.YangMillsFieldStrengthSplit.magWeight fabc
      = (∑ m : Fin 24, (ymMag fabc m) ^ 2) + 1 :=
  rfl

/-- **The comparison hypothesis supplied by the field strength.**  Every magnetic component has
total degree `≤ 2`, so the weight `W` the comparison calculation sees has total degree `≤ 4` in the
`99` coordinates — the quartic growth class. -/
theorem totalDegree_ymMag_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) :
    (ymMag fabc m).totalDegree ≤ 2 :=
  BookProof.YangMillsFieldStrengthSplit.totalDegree_magPoly_le fabc (decodeSpace m) (decodeColor m)

theorem totalDegree_magWeight_le (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    (BookProof.YangMillsFieldStrengthSplit.magWeight fabc).totalDegree ≤ 4 :=
  BookProof.YangMillsFieldStrengthSplit.totalDegree_magWeight_le fabc

/-- **The non-abelian gauge-fixed Yang–Mills one-particle Hamiltonian
`H = ½ Σ π² + ½ Σ B²` is essentially self-adjoint on the Gauss–polynomial core of
`L²(ℝ⁹⁹)`**, for arbitrary real structure constants `f_{abc}`.  This is a one-particle
statement. -/
theorem ym_h_esa (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 99)) (ymHamiltonian (coreRepPoly 99) fabc) := by
  rw [ymHamiltonian_eq_weylPoly]
  exact weylPoly_esa ymIdx_injective fun m => realCoeff_magPoly fabc _ _

/-- `L²(ℝᵈ)` as a bundled inner product space, the one-particle space of the enclosure. -/
def L2dSpace (d : ℕ) : IPSpace := ⟨L2d d⟩

instance (d : ℕ) : CompleteSpace (L2dSpace d).carrier :=
  inferInstanceAs (CompleteSpace (L2d d))

/-- **The second-quantized non-abelian Yang–Mills Hamiltonian is essentially self-adjoint.**
`dH = dΓ(H) = Σ_{i,j} H_{ij} C†(e_i) A(e_j)` — the one-particle Hamiltonian enclosed between
a creation on the left and an annihilation on the right — is essentially self-adjoint on the
finite-particle domain `𝓕_fin(D)` built from the Gauss–polynomial core `D` of `L²(ℝ⁹⁹)`,
for arbitrary real structure constants. -/
theorem ym_dGamma_esa (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore (L2dSpace 99) (polyGaussCore (d := 99))
        (polyGaussCore (d := 99)) n))
      (dGammaCoreOp (L2dSpace 99) (polyGaussCore (d := 99))
        (ymHamiltonian (coreRepPoly 99) fabc) (polyGaussCore (d := 99))) :=
  EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa (Hs := L2dSpace 99)
    (ymHamiltonian (coreRepPoly 99) fabc) polyGaussCore_dense
    (ymHamiltonian_symmetricOn _ fabc) (ym_h_esa fabc)

/-! ## 5. The coloured operator

The split chapter states symmetry of `colouredHamiltonian Φ fabc N C` on the coloured core and
stops there.  The deficiency argument needs no relative bound: the field half is a direct sum of
copies of the one-particle Hamiltonian, and the colour half is a symmetric perturbation, which
cannot support a deficiency vector. -/

noncomputable section Coloured

open BookProof.YangMillsFieldStrengthSplit

variable {D : Submodule ℂ (L2d 99)} {N : ℕ}

/-- The `i`-th colour component of a coloured-core element, read as an element of the field core. -/
def colourComponent (u : colouredCore N D) (i : Fin N) : D :=
  ⟨WithLp.ofLp (u : colourSpace N) i, u.2 i⟩

@[simp] theorem colourComponent_coe (u : colouredCore N D) (i : Fin N) :
    ((colourComponent u i : D) : L2d 99) = WithLp.ofLp (u : colourSpace N) i := rfl

theorem colourComponent_add (u v : colouredCore N D) (i : Fin N) :
    colourComponent (u + v) i = colourComponent u i + colourComponent v i :=
  Subtype.ext (by simp [colourComponent])

theorem colourComponent_smul (c : ℂ) (u : colouredCore N D) (i : Fin N) :
    colourComponent (c • u) i = c • colourComponent u i :=
  Subtype.ext (by simp [colourComponent])

/-- The vector supported in a single colour component. -/
def colourSingle (i : Fin N) (v : L2d 99) : colourSpace N :=
  WithLp.toLp 2 (fun j => if j = i then v else 0)

@[simp] theorem colourSingle_ofLp (i : Fin N) (v : L2d 99) (j : Fin N) :
    (colourSingle i v : colourSpace N).ofLp j = if j = i then v else 0 := rfl

theorem colourSingle_mem (i : Fin N) {v : L2d 99} (hv : v ∈ D) :
    colourSingle (N := N) i v ∈ colouredCore N D := by
  intro j
  rw [colourSingle_ofLp]
  by_cases hj : j = i
  · rw [if_pos hj]; exact hv
  · rw [if_neg hj]; exact Submodule.zero_mem _

@[simp] theorem colourSingle_mem_coe (i : Fin N) {v : L2d 99} (hv : v ∈ D) :
    ((⟨colourSingle (N := N) i v, colourSingle_mem i hv⟩ : colouredCore N D) : colourSpace N)
      = colourSingle i v := rfl

/-- **Single components pair with a single component of the other vector.** -/
theorem inner_colourSingle_left (i : Fin N) (v : L2d 99) (w : colourSpace N) :
    inner ℂ (colourSingle i v : colourSpace N) w
      = inner ℂ v (WithLp.ofLp w i) := by
  rw [PiLp.inner_apply]
  simp only [colourSingle, WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The field half `H ⊗ 1` of the coloured Hamiltonian, on the coloured core. -/
def colourFieldOp (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (N : ℕ) :
    colouredCore N D →ₗ[ℂ] colourSpace N where
  toFun u := WithLp.toLp 2 (fun i => ymHamiltonian Φ fabc (colourComponent u i))
  map_add' u v := by
    apply WithLp.ofLp_injective
    funext i
    simp only [WithLp.ofLp_add, Pi.add_apply, colourComponent_add]
    exact map_add (ymHamiltonian Φ fabc) _ _
  map_smul' c u := by
    apply WithLp.ofLp_injective
    funext i
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply, colourComponent_smul]
    exact map_smul (ymHamiltonian Φ fabc) c _

theorem colourFieldOp_ofLp (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (u : colouredCore N D) (i : Fin N) :
    (colourFieldOp Φ fabc N u : colourSpace N).ofLp i
      = ymHamiltonian Φ fabc (colourComponent u i) := rfl

theorem colourFieldOp_colourSingle (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (i : Fin N) (v : D) :
    colourFieldOp Φ fabc N ⟨colourSingle i (v : L2d 99), colourSingle_mem i v.2⟩
      = colourSingle i (ymHamiltonian Φ fabc v) := by
  apply WithLp.ofLp_injective
  funext j
  by_cases hj : j = i
  · subst hj
    simp [colourFieldOp_ofLp, colourComponent]
  · simp only [colourFieldOp_ofLp, colourComponent, colourSingle_ofLp, if_neg hj]
    exact congrArg (ymHamiltonian Φ fabc) (Subtype.ext rfl) |>.trans (map_zero _)

/-- The colour half `1 ⊗ C`: the matrix `C` acting on the colour components. -/
def colourMix (C : Matrix (Fin N) (Fin N) ℂ) (u : colourSpace N) : colourSpace N :=
  WithLp.toLp 2 (fun i => ∑ j : Fin N, C i j • WithLp.ofLp u j)

@[simp] theorem colourMix_ofLp (C : Matrix (Fin N) (Fin N) ℂ) (u : colourSpace N) (i : Fin N) :
    (colourMix C u : colourSpace N).ofLp i = ∑ j : Fin N, C i j • WithLp.ofLp u j := rfl

theorem colourFieldOp_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    SymmetricOn (colouredCore N D) (colourFieldOp Φ fabc N) := by
  intro u v
  simp only [PiLp.inner_apply, colourFieldOp_ofLp]
  exact Finset.sum_congr rfl fun i _ =>
    ymHamiltonian_symmetricOn Φ fabc (colourComponent u i) (colourComponent v i)

/-- **Single components see only the fibre**: the deficiency identity of the field operator is the
field deficiency identity, component by component. -/
theorem colourFieldOp_deficiencyTrivialAt {z : ℂ} (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (h : DeficiencyTrivialAt D (ymHamiltonian Φ fabc) z) :
    DeficiencyTrivialAt (colouredCore N D) (colourFieldOp Φ fabc N) z := by
  intro w hw
  apply WithLp.ofLp_injective
  funext i
  refine h (WithLp.ofLp w i) fun v => ?_
  have hv := hw ⟨colourSingle i (v : L2d 99), colourSingle_mem i v.2⟩
  simp only [colourFieldOp_colourSingle, inner_colourSingle_left] at hv
  exact hv

theorem colourFieldOp_esa (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (h : EssentiallySelfAdjointOn D (ymHamiltonian Φ fabc)) :
    EssentiallySelfAdjointOn (colouredCore N D) (colourFieldOp Φ fabc N) :=
  ⟨colourFieldOp_deficiencyTrivialAt Φ fabc h.1,
    colourFieldOp_deficiencyTrivialAt Φ fabc h.2⟩

/-- **The colour half is symmetric** for a Hermitian colour matrix. -/
theorem colourMix_inner (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.conjTranspose = C)
    (u w : colourSpace N) :
    (inner ℂ (colourMix C u) w : ℂ) = inner ℂ u (colourMix C w) := by
  simp only [PiLp.inner_apply, colourMix_ofLp, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right]
  rw [Finset.sum_comm]
  have hentry : ∀ i j : Fin N, starRingEnd ℂ (C i j) = C j i := by
    intro i j
    have h : C.conjTranspose j i = C j i := by rw [hC]
    simpa [Matrix.conjTranspose_apply] using h
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hentry i j

/-! ### Symmetric perturbations do not create deficiency vectors

The perturbation is not assumed bounded or even linear: what the argument uses is only the
pairing symmetry `⟪K u, w⟫ = ⟪u, K w⟫`.  (On a Hilbert space an everywhere-defined linear map
with that symmetry is automatically bounded, so nothing is lost.) -/

section Perturbation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {Dom : Submodule ℂ F}

/-- **A symmetric perturbation does not create deficiency vectors.**  If `A` is symmetric with no
deficiency vector at any non-real point, and `B v = A v + K v` where `K` is everywhere defined
with `⟪K u, w⟫ = ⟪u, K w⟫`, then `B` has no deficiency vector at `d i` either (`d ≠ 0` real).

The proof reads both `w` and the graph limit of `A` provided by `exists_weak_graph_limit` as
graph-limit pairs at the same level; uniqueness of that pair is exactly `A`'s trivial deficiency
at `d i`, and the reality of `⟪z, u⟫` then forces `d ‖w‖² = 0`. -/
theorem deficiencyTrivialAt_of_symmetric_perturbation (A B : Dom →ₗ[ℂ] F) (K : F → F)
    {d : ℝ} (hd : d ≠ 0) (hA : SymmetricOn Dom A)
    (hall : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt Dom A z)
    (hB : ∀ v : Dom, B v = A v + K (v : F))
    (hK : ∀ u w : F, (inner ℂ (K u) w : ℂ) = inner ℂ u (K w)) :
    DeficiencyTrivialAt Dom B ((d : ℂ) * Complex.I) := by
  intro w hw
  have hdi : ((d : ℂ) * Complex.I).im ≠ 0 := by
    simpa [Complex.mul_im] using hd
  -- the deficiency identity of `A`, with the vector `(d i) • w - K w`
  have hwA : ∀ v : Dom, (inner ℂ (A v) w : ℂ)
      = inner ℂ (v : F) (((d : ℂ) * Complex.I) • w - K w) := by
    intro v
    have h := hw v
    rw [hB v, inner_add_left, hK (v : F) w] at h
    rw [inner_sub_right, inner_smul_right, eq_sub_iff_add_eq]
    exact h
  have hstar : starRingEnd ℂ ((d : ℂ) * Complex.I) = -((d : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hdens : Dense (Set.range fun x : Dom => A x - ((d : ℂ) * Complex.I) • (x : F)) := by
    refine dense_range_of_deficiencyTrivialAt A ((d : ℂ) * Complex.I) ?_
    rw [hstar]
    refine hall _ ?_
    have him : (-((d : ℂ) * Complex.I)).im = -d := by simp [Complex.mul_im]
    rw [him]
    exact neg_ne_zero.mpr hd
  obtain ⟨u, z, hu, hzu, hzim⟩ :=
    exists_weak_graph_limit A hA d hd hdens (-(K w))
  -- both pairs are graph limits at the same level, so they agree
  have hdiff : z - (((d : ℂ) * Complex.I) • w - K w) = ((d : ℂ) * Complex.I) • (u - w) := by
    have hz : z = ((d : ℂ) * Complex.I) • u - K w := by
      have h : z = -(K w) + ((d : ℂ) * Complex.I) • u := sub_eq_iff_eq_add.mp hzu
      rw [h]
      abel
    rw [hz, smul_sub]
    abel
  have huv : ∀ v : Dom, (inner ℂ (A v) (u - w) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (v : F) (u - w) := by
    intro v
    calc inner ℂ (A v) (u - w)
        = inner ℂ (A v) u - inner ℂ (A v) w := inner_sub_right ..
      _ = inner ℂ (v : F) z
            - inner ℂ (v : F) (((d : ℂ) * Complex.I) • w - K w) := by rw [hu v, hwA v]
      _ = inner ℂ (v : F) (z - (((d : ℂ) * Complex.I) • w - K w)) :=
          (inner_sub_right ..).symm
      _ = inner ℂ (v : F) (((d : ℂ) * Complex.I) • (u - w)) := by rw [hdiff]
      _ = ((d : ℂ) * Complex.I) * inner ℂ (v : F) (u - w) := inner_smul_right ..
  have huw : u = w := sub_eq_zero.mp (hall _ hdi (u - w) huv)
  have hzw : z = ((d : ℂ) * Complex.I) • w - K w := by
    have h1 : z = -(K w) + ((d : ℂ) * Complex.I) • w := by
      rw [huw] at hzu
      exact sub_eq_iff_eq_add.mp hzu
    rw [h1]
    abel
  -- the graph limit has real `⟪z, u⟫`
  rw [hzw, huw] at hzim
  have hval : (inner ℂ (((d : ℂ) * Complex.I) • w - K w) w : ℂ)
      = -(((d : ℂ) * Complex.I) * inner ℂ w w) - (inner ℂ (K w) w : ℂ) := by
    rw [inner_sub_left, inner_smul_left, hstar]
    ring
  rw [hval] at hzim
  have hKreal : ((inner ℂ (K w) w : ℂ)).im = 0 := by
    have h2 : (inner ℂ (K w) w : ℂ) = starRingEnd ℂ (inner ℂ (K w) w) := by
      calc (inner ℂ (K w) w : ℂ) = inner ℂ w (K w) := hK w w
        _ = starRingEnd ℂ (inner ℂ (K w) w) := (inner_conj_symm w (K w)).symm
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    linarith
  have hselfre : ((inner ℂ w w : ℂ)).re = ‖w‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) w
  have hselfim : ((inner ℂ w w : ℂ)).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) w
  have hprod : (-(((d : ℂ) * Complex.I) * inner ℂ w w)).im = -d * ‖w‖ ^ 2 := by
    rw [Complex.neg_im, Complex.mul_im]
    have him : ((d : ℂ) * Complex.I).im = d := by simp [Complex.mul_im]
    have hre : ((d : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [hre, him, hselfim, mul_zero, zero_add, hselfre]
    ring
  rw [Complex.sub_im, hprod, hKreal, sub_zero] at hzim
  rcases mul_eq_zero.mp (by linarith [hzim] : d * ‖w‖ ^ 2 = 0) with h | h
  · exact absurd h hd
  · exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

end Perturbation

/-- **The coloured Hamiltonian is `H ⊗ 1 + 1 ⊗ C`.** -/
theorem colouredHamiltonian_eq_field_add_mix (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (C : Matrix (Fin N) (Fin N) ℂ)
    (u : colouredCore N D) :
    colouredHamiltonian Φ fabc N C u
      = colourFieldOp Φ fabc N u + colourMix C (u : colourSpace N) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [colouredHamiltonian_ofLp, colourFieldOp_ofLp, WithLp.ofLp_add, Pi.add_apply,
    colourMix_ofLp, colourComponent]

/-- **The coloured non-abelian Yang–Mills Hamiltonian `H ⊗ 1 + 1 ⊗ C` is essentially
self-adjoint** on the coloured core, for a Hermitian colour matrix `C` and arbitrary real
structure constants.  The field half is the direct sum of `N` copies of `ym_h_esa` glued
component by component, and the colour half is a symmetric perturbation, which cannot support a
deficiency vector.  No relative bound and no comparison operator are used. -/
theorem colouredHamiltonian_esa (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.conjTranspose = C) :
    EssentiallySelfAdjointOn (colouredCore N (polyGaussCore (d := 99)))
      (colouredHamiltonian (coreRepPoly 99) fabc N C) := by
  have hAesa : EssentiallySelfAdjointOn (colouredCore N (polyGaussCore (d := 99)))
      (colourFieldOp (coreRepPoly 99) fabc N) :=
    colourFieldOp_esa _ fabc (ym_h_esa fabc)
  have hAsym : SymmetricOn (colouredCore N (polyGaussCore (d := 99)))
      (colourFieldOp (coreRepPoly 99) fabc N) := colourFieldOp_symmetricOn _ fabc
  have hall : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt
      (colouredCore N (polyGaussCore (d := 99))) (colourFieldOp (coreRepPoly 99) fabc N) z :=
    fun z hz => deficiencyTrivialAt_of_esa _ hAsym hAesa hz
  have hpert := fun (d : ℝ) (hd : d ≠ 0) =>
    deficiencyTrivialAt_of_symmetric_perturbation _ _ (colourMix C) hd hAsym hall
      (fun v => colouredHamiltonian_eq_field_add_mix _ fabc C v)
      (fun u w => colourMix_inner C hC u w)
  refine ⟨?_, ?_⟩
  · simpa using hpert 1 one_ne_zero
  · simpa using hpert (-1) (by norm_num)

end Coloured


end

end BookProof.YangMillsNonAbelianEsa
