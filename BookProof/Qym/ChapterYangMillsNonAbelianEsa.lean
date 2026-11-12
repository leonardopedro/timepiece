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
  short of; it lives here because this module imports the split chapter;
* **`colouredCore_polyGaussCore_dense`** — the coloured core is dense in the coloured Hilbert
  space (from `dense_colouredCore`, which needs density of the field core);
* **`colouredHamiltonian_extension_eq_closure`** — that extension is *the closure*: every
  self-adjoint extension of `H ⊗ 1 + 1 ⊗ C` is `clExt`, so there is no boundary condition left to
  choose and the Stone flow is the flow of a determined operator;
* **`exists_stone_flow_of_colouredHamiltonian`** — the Stone bridge applied to the two inputs
  above: `H ⊗ 1 + 1 ⊗ C` has a self-adjoint extension — pinned to that closure — and a complete
  unitary flow;
* **`colourMix_norm_of_unitary`, `colourMixIsometryEquiv`** — for a unitary colour matrix
  (`star C * C = 1`) the colour half `1 ⊗ C` is norm-preserving on `colourSpace N`, hence a
  linear isometric equivalence, for **every** `N` (the `N = 2` case was the only one available);
* **`colourMix_colouredHamiltonian`, `colourMix_clExt_colouredHamiltonian`** — unitary colour
  conjugation transports the generator: `1 ⊗ U` intertwines `H ⊗ 1 + 1 ⊗ (U* C U)` with
  `H ⊗ 1 + 1 ⊗ C` on the core, and by `clExt_comp_of_bounded_intertwines` (a bounded map carries
  graph closures into graph closures) the same identity holds between the closures;
* **`colourMix_colourSpread_eigenvector`, `colourSpread_ne_zero`** — a colour eigenvector spread
  over a field vector is a nonzero eigenvector of the colour half with the same eigenvalue (the
  only spectral content the colour half carries; see the spectrum boundary note below);
* **`colourMix_colourFibre`, `colourVecAct_two_eq_eucMatCLM`, `hilbActOp_hilbFibre`** — the
  colour half of the Hamiltonian acts on the fibre of an elementary tensor, and on the
  fundamental fibre that action is `eucMatCLM`, the very operator the `fundHilbert` completion
  applies coefficientwise; the completion embeds the same fibre at `hilbFibre`, and both ambient
  spaces act on it through the single operator `colourVecAct`.

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

/-! ### The colour mixing is an isometry of the coloured space

The colour half `1 ⊗ C` is defined componentwise.  For a unitary colour matrix it preserves the
inner product — and hence the norm — of `colourSpace N = PiLp 2 (fun _ : Fin N => L2d 99)` for
*every* `N`, not only on the fibre.  The proof is the matrix computation `star C * C = 1` seen
through the adjoint `colourMix (star C)`, exactly as on the Euclidean fibre.
-/

theorem colourMix_add (C : Matrix (Fin N) (Fin N) ℂ) (u w : colourSpace N) :
    colourMix C (u + w) = colourMix C u + colourMix C w := by
  apply WithLp.ofLp_injective
  funext i
  simp only [colourMix_ofLp, WithLp.ofLp_add, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem colourMix_smul (C : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (u : colourSpace N) :
    colourMix C (c • u) = c • colourMix C u := by
  apply WithLp.ofLp_injective
  funext i
  simp only [colourMix_ofLp, WithLp.ofLp_smul, Pi.smul_apply]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (smul_comm c (C i j) (WithLp.ofLp u j)).symm

/-- The colour mixing as a linear map. -/
def colourMixLinear (C : Matrix (Fin N) (Fin N) ℂ) : colourSpace N →ₗ[ℂ] colourSpace N where
  toFun := colourMix C
  map_add' := colourMix_add C
  map_smul' := colourMix_smul C

theorem colourMixLinear_apply (C : Matrix (Fin N) (Fin N) ℂ) (u : colourSpace N) :
    colourMixLinear C u = colourMix C u := rfl

theorem colourMix_one (u : colourSpace N) :
    colourMix (1 : Matrix (Fin N) (Fin N) ℂ) u = u := by
  apply WithLp.ofLp_injective
  funext i
  rw [colourMix_ofLp]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · simp

theorem colourMix_mul (C C' : Matrix (Fin N) (Fin N) ℂ) (u : colourSpace N) :
    colourMix C (colourMix C' u) = colourMix (C * C') u := by
  apply WithLp.ofLp_injective
  funext i
  simp only [colourMix_ofLp, Matrix.mul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (Finset.sum_smul).symm

/-- **The adjoint of the colour mixing is the conjugate-transpose matrix.** -/
theorem colourMix_adjoint (C : Matrix (Fin N) (Fin N) ℂ) (u w : colourSpace N) :
    (inner ℂ (colourMix C u) w : ℂ) = inner ℂ u (colourMix (star C) w) := by
  simp only [PiLp.inner_apply, colourMix_ofLp, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    congrArg (fun c => c * inner ℂ (WithLp.ofLp u j) (WithLp.ofLp w i))
      (Matrix.star_apply C j i).symm

/-- **A unitary colour matrix preserves the inner product** of the coloured space. -/
theorem colourMix_inner_of_unitary {C : Matrix (Fin N) (Fin N) ℂ} (hC : star C * C = 1)
    (u w : colourSpace N) :
    (inner ℂ (colourMix C u) (colourMix C w) : ℂ) = inner ℂ u w := by
  calc (inner ℂ (colourMix C u) (colourMix C w) : ℂ)
      = inner ℂ u (colourMix (star C) (colourMix C w)) := colourMix_adjoint C u _
    _ = inner ℂ u (colourMix (star C * C) w) := by rw [colourMix_mul]
    _ = inner ℂ u w := by rw [hC, colourMix_one]

/-- **A unitary colour matrix is norm-preserving on the coloured space.** -/
theorem colourMix_norm_of_unitary {C : Matrix (Fin N) (Fin N) ℂ} (hC : star C * C = 1)
    (u : colourSpace N) : ‖colourMix C u‖ = ‖u‖ := by
  have h := colourMix_inner_of_unitary hC u u
  have hsq : ‖colourMix C u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) _, norm_sq_eq_re_inner (𝕜 := ℂ) _, h]
  nlinarith [norm_nonneg (colourMix C u), norm_nonneg u]

theorem colourMix_isometry_of_unitary {C : Matrix (Fin N) (Fin N) ℂ} (hC : star C * C = 1) :
    Isometry (colourMix C) := by
  refine Isometry.of_dist_eq fun u w => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h : colourMix C (u - w) = colourMix C u - colourMix C w :=
    map_sub (colourMixLinear C) u w
  rw [← h]
  exact colourMix_norm_of_unitary hC (u - w)

/-- **A unitary colour matrix is a linear isometric equivalence** of the coloured space: the
colour half `1 ⊗ C` of the coloured Hamiltonian is a unitary operator, with inverse `1 ⊗ C*`. -/
def colourMixIsometryEquiv {C : Matrix (Fin N) (Fin N) ℂ} (hC : star C * C = 1) :
    colourSpace N ≃ₗᵢ[ℂ] colourSpace N where
  toFun := colourMix C
  invFun := colourMix (star C)
  left_inv u := by
    show colourMix (star C) (colourMix C u) = u
    rw [colourMix_mul, hC, colourMix_one]
  right_inv u := by
    show colourMix C (colourMix (star C) u) = u
    rw [colourMix_mul, mul_eq_one_comm.mp hC, colourMix_one]
  map_add' := colourMix_add C
  map_smul' := colourMix_smul C
  norm_map' u := colourMix_norm_of_unitary hC u

/-! ### The colour mixing on the coloured core and as a bounded operator

`colourMix` acts componentwise, so it preserves the coloured core and commutes with the field
half `H ⊗ 1`.  For a unitary colour matrix it is norm preserving, hence a bounded operator of
`colourSpace N`; those are the three inputs of the conjugation theorem below.
-/

/-- **The colour mixing preserves the coloured core**: each output component is a finite
`ℂ`-linear combination of components of `u`, all of which lie in the field core. -/
theorem colourMix_mem_core (C : Matrix (Fin N) (Fin N) ℂ) {u : colourSpace N}
    (hu : u ∈ colouredCore N D) : colourMix C u ∈ colouredCore N D := by
  intro i
  rw [colourMix_ofLp]
  exact Submodule.sum_mem D fun j _ => Submodule.smul_mem D (C i j) (hu j)

/-- The colour mixing as an endomorphism of the coloured core. -/
def colourMixCore (C : Matrix (Fin N) (Fin N) ℂ) :
    colouredCore N D →ₗ[ℂ] colouredCore N D where
  toFun u := ⟨colourMix C (u : colourSpace N), colourMix_mem_core C u.2⟩
  map_add' u w := Subtype.ext (by simp only [Submodule.coe_add, colourMix_add])
  map_smul' c u := Subtype.ext (by simp only [SetLike.val_smul, RingHom.id_apply, colourMix_smul])

@[simp] theorem colourMixCore_coe (C : Matrix (Fin N) (Fin N) ℂ) (u : colouredCore N D) :
    ((colourMixCore C u : colouredCore N D) : colourSpace N) = colourMix C (u : colourSpace N) :=
  rfl

/-- **The colour mixing as a bounded operator** of the coloured Hilbert space, for a unitary
colour matrix; its operator norm is `1` (`colourMix_norm_of_unitary`). -/
noncomputable def colourMixCLM {U : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1) :
    colourSpace N →L[ℂ] colourSpace N :=
  (colourMixLinear U).mkContinuous 1 fun u => by
    rw [colourMixLinear_apply, one_mul]
    exact le_of_eq (colourMix_norm_of_unitary hU u)

@[simp] theorem colourMixCLM_apply {U : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1)
    (u : colourSpace N) : colourMixCLM hU u = colourMix U u := rfl

/-- **The colour half commutes with the field half**: both act componentwise, the field
operator preserves finite sums and scalar multiples, and the matrix only mixes components. -/
theorem colourMix_colourFieldOp (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (C : Matrix (Fin N) (Fin N) ℂ) (u : colouredCore N D) :
    colourMix C (colourFieldOp Φ fabc N u) = colourFieldOp Φ fabc N (colourMixCore C u) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [colourMix_ofLp, colourFieldOp_ofLp]
  have hcomp : colourComponent (colourMixCore C u) i
      = ∑ j : Fin N, C i j • colourComponent u j := by
    refine Subtype.ext ?_
    simp only [colourComponent_coe, colourMixCore_coe, colourMix_ofLp, Submodule.coe_sum,
      Submodule.coe_smul]
  rw [hcomp, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    (map_smul (ymHamiltonian Φ fabc) (C i j) (colourComponent u j)).symm

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

/-- **Colour conjugation replaces `C` by `U* C U`.**  For a colour matrix `U` with
`U * U* = 1` the colour half `1 ⊗ U` intertwines `H ⊗ 1 + 1 ⊗ (U* C U)` with `H ⊗ 1 + 1 ⊗ C`:
the field half commutes with `1 ⊗ U`, and `U * (U* C U) = C * U` collapses the two copies of
`U` on the colour side. -/
theorem colourMix_colouredHamiltonian (Φ : CoreRep 99 D)
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {U C : Matrix (Fin N) (Fin N) ℂ}
    (hU : U * star U = 1) (u : colouredCore N D) :
    colourMix U (colouredHamiltonian Φ fabc N (star U * C * U) u)
      = colouredHamiltonian Φ fabc N C (colourMixCore U u) := by
  have hmat : U * (star U * C * U) = C * U := by
    rw [← mul_assoc, ← mul_assoc, hU, one_mul]
  calc colourMix U (colouredHamiltonian Φ fabc N (star U * C * U) u)
      = colourMix U (colourFieldOp Φ fabc N u)
          + colourMix U (colourMix (star U * C * U) (u : colourSpace N)) := by
        rw [colouredHamiltonian_eq_field_add_mix]
        exact colourMix_add U _ _
    _ = colourFieldOp Φ fabc N (colourMixCore U u)
          + colourMix (U * (star U * C * U)) (u : colourSpace N) := by
        rw [colourMix_colourFieldOp, colourMix_mul]
    _ = colourFieldOp Φ fabc N (colourMixCore U u)
          + colourMix (C * U) (u : colourSpace N) := by
        rw [hmat]
    _ = colourFieldOp Φ fabc N (colourMixCore U u)
          + colourMix C (colourMix U (u : colourSpace N)) := by
        rw [← colourMix_mul]
    _ = colouredHamiltonian Φ fabc N C (colourMixCore U u) := by
        refine (congrArg (fun w => colourFieldOp Φ fabc N (colourMixCore U u) + w)
          (congrArg (colourMix C) (colourMixCore_coe U u).symm)).trans ?_
        exact (colouredHamiltonian_eq_field_add_mix Φ fabc C (colourMixCore U u)).symm

/-! ### The colour eigenvalues are eigenvalues of the colour half

A colour vector spread over one field vector gives a vector of the coloured space whose `i`-th
component is `v i • φ`.  For an eigenvector of the colour matrix this is an eigenvector of
`colourMix C` with the same eigenvalue, because the matrix mixes only the colour labels and the
field factor rides along untouched.  That is the whole spectral content the colour half carries
here; the boundary note of the Stone bridge below records what is *not* available about the
spectrum of the closure.
-/

/-- The colour vector `v` spread over a single field vector `φ`. -/
def colourSpread (v : colourVec N) (φ : L2d 99) : colourSpace N :=
  WithLp.toLp 2 fun i => WithLp.ofLp v i • φ

@[simp] theorem colourSpread_ofLp (v : colourVec N) (φ : L2d 99) (i : Fin N) :
    (colourSpread v φ : colourSpace N).ofLp i = WithLp.ofLp v i • φ := rfl

/-- **A colour eigenvector is an eigenvector of the colour half**, with the same eigenvalue. -/
theorem colourMix_colourSpread_eigenvector (C : Matrix (Fin N) (Fin N) ℂ) {v : colourVec N}
    {a : ℂ} (hv : ∀ i, ∑ j : Fin N, C i j * WithLp.ofLp v j = a * WithLp.ofLp v i)
    (φ : L2d 99) : colourMix C (colourSpread v φ) = a • colourSpread v φ := by
  apply WithLp.ofLp_injective
  funext i
  simp only [colourMix_ofLp, colourSpread_ofLp, WithLp.ofLp_smul, Pi.smul_apply, smul_smul]
  rw [← Finset.sum_smul, hv i]

/-- The spread of a nonzero colour vector over a nonzero field vector is nonzero, so the
eigenvector above is a genuine one. -/
theorem colourSpread_ne_zero {v : colourVec N} (hv : v ≠ 0) {φ : L2d 99} (hφ : φ ≠ 0) :
    colourSpread v φ ≠ 0 := by
  intro h
  have hzero : ∀ i, WithLp.ofLp v i = 0 := by
    intro i
    have h1 : (colourSpread v φ : colourSpace N).ofLp i = 0 := by rw [h]; simp
    rw [colourSpread_ofLp] at h1
    exact (smul_eq_zero.1 h1).resolve_right hφ
  have hv0 : v = 0 := by
    apply WithLp.ofLp_injective
    funext i
    simpa using hzero i
  exact hv hv0

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

/-! ### The Stone bridge: the coloured Hamiltonian generates a flow

Essential self-adjointness is the hypothesis of
`BookProof.StoneBridge.exists_stone_flow_of_esa`, which needs one more input: the core must be
dense.  `dense_colouredCore` (in the split chapter) supplies it from density of the field core,
and `polyGaussCore_dense` is that density.  With the two in place the QYM one-particle
generator on the coloured space is no longer a formal expression: it *has* a self-adjoint
extension and a complete one-parameter unitary group solving the Schrödinger equation.

**Boundary.**  The generator is the closure of `H ⊗ 1 + 1 ⊗ C` on the coloured core
(`colouredHamiltonian_extension_eq_closure`), not a differential expression restricted to an
independently chosen boundary condition: essential self-adjointness leaves no choice.

**Boundary (spectrum).**  No spectral statement about `T.op` is claimed, and none is reachable
from what this tree contains.  The unbounded spectrum is not defined here: `BookProof.EsaClosure`
supplies the closure, `BookProof.ChapterStoneResolvent` the resolvent `(A - il)⁻¹` on the
imaginary axis, and `spectrum` otherwise appears only for *bounded* operators, so there is no
`σ(T.op)` for a spectrum of `H ⊗ 1` plus colour eigenvalues to contain.  The natural candidate
`σ(A + B) ⊆ σ(A) + σ(B)` is false anyway for non-commuting self-adjoint `A`, `B`; its true
one-sided form needs a resolvent bound at *real* spectral distance and a Neumann series, neither
of which exists here.  What *is* proved is the colour side of such a statement: a colour
eigenvector spreads to an eigenvector of `1 ⊗ C` with the same eigenvalue
(`colourMix_colourSpread_eigenvector`).
-/

/-- The coloured core over the Gauss–polynomial field core is dense in the coloured Hilbert
space. -/
theorem colouredCore_polyGaussCore_dense (N : ℕ) :
    Dense ((colouredCore N (polyGaussCore (d := 99)) : Submodule ℂ (colourSpace N)) :
      Set (colourSpace N)) :=
  dense_colouredCore polyGaussCore_dense N

/-- **The extension is the closure of the graph, so there is no boundary condition to fix.**
Essential self-adjointness gives deficiency indices `(0, 0)`, and then *every* self-adjoint
extension of `H ⊗ 1 + 1 ⊗ C` coincides with `clExt` — the operator of the closure of the graph on
the coloured Gauss–polynomial core.  This is `isSelfAdjointExtension_unique_of_esa` applied to
`colouredHamiltonian_esa`. -/
theorem colouredHamiltonian_extension_eq_closure (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.conjTranspose = C)
    {Dom : Submodule ℂ (colourSpace N)} (A : Dom →ₗ[ℂ] colourSpace N)
    (hA : BookProof.EsaClosure.IsSelfAdjointExtension
      (colouredHamiltonian (coreRepPoly 99) fabc N C) A) :
    Dom = BookProof.EsaClosure.clDom (colouredHamiltonian (coreRepPoly 99) fabc N C) ∧
      ∀ (x : colourSpace N) (h : x ∈ Dom)
        (h' : x ∈ BookProof.EsaClosure.clDom (colouredHamiltonian (coreRepPoly 99) fabc N C)),
        A ⟨x, h⟩ = BookProof.EsaClosure.clExt (colouredHamiltonian (coreRepPoly 99) fabc N C)
          (colouredCore_polyGaussCore_dense N)
          (colouredHamiltonian_symmetricOn _ fabc C hC) ⟨x, h'⟩ :=
  BookProof.EsaClosure.isSelfAdjointExtension_unique_of_esa
    (colouredHamiltonian_esa fabc C hC) hA
    ⟨fun v => ⟨BookProof.EsaClosure.coe_mem_clDom _ v,
        BookProof.EsaClosure.clExt_extends _ _ _ v⟩,
      BookProof.EsaClosure.clExt_symmetricOn _ _ _,
      BookProof.EsaClosure.clExt_selfAdjointCriterion _ _ _
        (colouredHamiltonian_esa fabc C hC)⟩

/-! ### Colour conjugation transports the generator

`colourMix_colouredHamiltonian` is a statement about the core.  It lifts to the closures by a
general fact: a bounded map intertwining two core operators on a dense core maps the closed
graph of one into the closed graph of the other, because the graph map `(x, y) ↦ (B x, B y)` is
continuous.  The closure is closed, so the image of the closure lands in the closure of the
image, which is contained in the target closure.
-/

section Intertwining

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {Dom : Submodule ℂ F}

/-- **The closed graph is transported by a bounded intertwining map.** -/
theorem clGraph_image_subset (T S : Dom →ₗ[ℂ] F) (B : F →L[ℂ] F)
    (hB : ∀ v : Dom, B (v : F) ∈ Dom)
    (hint : ∀ v : Dom, B (T v) = S ⟨B (v : F), hB v⟩) :
    (fun p : F × F => (B p.1, B p.2)) '' (BookProof.EsaClosure.clGraph T : Set (F × F))
      ⊆ (BookProof.EsaClosure.clGraph S : Set (F × F)) := by
  have hg : Continuous fun p : F × F => (B p.1, B p.2) :=
    (B.continuous.comp continuous_fst).prodMk (B.continuous.comp continuous_snd)
  have hsub : (fun p : F × F => (B p.1, B p.2)) ''
      (BookProof.EsaClosure.opGraph T : Set (F × F)) ⊆
      (BookProof.EsaClosure.clGraph S : Set (F × F)) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨v, hh, hvp⟩ : ∃ v : Dom, ∃ h : (v : F) ∈ Dom, ((v : F), T ⟨v, h⟩) = p := by
      simpa [BookProof.EsaClosure.opGraph_eq_range] using hp
    rw [← hvp]
    change (B (v : F), B (T ⟨(v : F), hh⟩)) ∈ (BookProof.EsaClosure.clGraph S : Set (F × F))
    rw [hint v]
    exact BookProof.EsaClosure.mem_clGraph_of_mem_opGraph
      (BookProof.EsaClosure.mem_opGraph S ⟨B (v : F), hB v⟩)
  refine (image_closure_subset_closure_image
    (s := (BookProof.EsaClosure.opGraph T : Set (F × F))) hg).trans ?_
  refine (closure_mono hsub).trans ?_
  exact subset_of_eq (BookProof.EsaClosure.clGraph_isClosed S).closure_eq

/-- **The domain of the closure is transported.** -/
theorem mem_clDom_of_bounded_intertwines (T S : Dom →ₗ[ℂ] F) (B : F →L[ℂ] F)
    (hB : ∀ v : Dom, B (v : F) ∈ Dom)
    (hint : ∀ v : Dom, B (T v) = S ⟨B (v : F), hB v⟩) {x : F}
    (hx : x ∈ BookProof.EsaClosure.clDom T) : B x ∈ BookProof.EsaClosure.clDom S := by
  obtain ⟨y, hy⟩ := BookProof.EsaClosure.mem_clDom_iff.1 hx
  exact BookProof.EsaClosure.mem_clDom_iff.2
    ⟨B y, clGraph_image_subset T S B hB hint ⟨_, hy, rfl⟩⟩

/-- **The closures are intertwined.**  With `T`, `S` densely defined and symmetric and
`B (T v) = S (B v)` on the core, `B` conjugates `clExt T` into `clExt S`; no completeness,
positivity or self-adjointness is used, only that the graph closures are closed. -/
theorem clExt_comp_of_bounded_intertwines (T S : Dom →ₗ[ℂ] F)
    (hdense : Dense (Dom : Set F)) (hsymT : SymmetricOn Dom T) (hsymS : SymmetricOn Dom S)
    (B : F →L[ℂ] F) (hB : ∀ v : Dom, B (v : F) ∈ Dom)
    (hint : ∀ v : Dom, B (T v) = S ⟨B (v : F), hB v⟩) (x : BookProof.EsaClosure.clDom T) :
    BookProof.EsaClosure.clExt S hdense hsymS
        ⟨B (x : F), mem_clDom_of_bounded_intertwines T S B hB hint x.2⟩
      = B (BookProof.EsaClosure.clExt T hdense hsymT x) :=
  BookProof.EsaClosure.clFun_unique hdense hsymS
    (clGraph_image_subset T S B hB hint ⟨_, BookProof.EsaClosure.clFun_spec T x, rfl⟩)

end Intertwining

/-- A Hermitian colour matrix stays Hermitian under conjugation by a colour matrix. -/
theorem conjTranspose_colourConj {U C : Matrix (Fin N) (Fin N) ℂ}
    (hC : C.conjTranspose = C) : (star U * C * U).conjTranspose = star U * C * U := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hC]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [mul_assoc]

/-- **A unitary colour mixing maps the domain of the closure into the domain of the
conjugated closure.** -/
theorem colourMix_mem_clDom_colouredHamiltonian (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ}
    {U C : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1)
    (x : BookProof.EsaClosure.clDom
      (colouredHamiltonian (coreRepPoly 99) fabc N (star U * C * U))) :
    colourMixCLM hU (x : colourSpace N) ∈
      BookProof.EsaClosure.clDom (colouredHamiltonian (coreRepPoly 99) fabc N C) := by
  have hU' : U * star U = 1 := mul_eq_one_comm.mp hU
  refine mem_clDom_of_bounded_intertwines (T := colouredHamiltonian (coreRepPoly 99) fabc N
      (star U * C * U)) (S := colouredHamiltonian (coreRepPoly 99) fabc N C)
    (B := colourMixCLM hU) (hB := fun v => colourMix_mem_core U v.2) (hint := fun v => ?_) x.2
  rw [colourMixCLM_apply]
  have h := colourMix_colouredHamiltonian (coreRepPoly 99) fabc (U := U) (C := C) hU' v
  rw [h]
  exact congrArg _ (Subtype.ext rfl)

/-- **Unitary colour conjugation conjugates the QYM generator.**  The closure of
`H ⊗ 1 + 1 ⊗ (U* C U)` is carried by `1 ⊗ U` onto the closure of `H ⊗ 1 + 1 ⊗ C`:
`clExt (1 ⊗ C) ∘ (1 ⊗ U) = (1 ⊗ U) ∘ clExt (1 ⊗ U* C U)` on the domain of the latter.  Since
both closures are the unique self-adjoint extensions (`colouredHamiltonian_extension_eq_closure`),
this is a statement about `T.op` for the extension `T` of the Stone bridge, not about a chosen
boundary condition. -/
theorem colourMix_clExt_colouredHamiltonian (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ}
    {U C : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1) (hC : C.conjTranspose = C)
    (x : BookProof.EsaClosure.clDom
      (colouredHamiltonian (coreRepPoly 99) fabc N (star U * C * U))) :
    BookProof.EsaClosure.clExt (colouredHamiltonian (coreRepPoly 99) fabc N C)
        (colouredCore_polyGaussCore_dense N) (colouredHamiltonian_symmetricOn _ fabc C hC)
        ⟨colourMixCLM hU (x : colourSpace N),
          colourMix_mem_clDom_colouredHamiltonian fabc hU x⟩
      = colourMixCLM hU (BookProof.EsaClosure.clExt
          (colouredHamiltonian (coreRepPoly 99) fabc N (star U * C * U))
          (colouredCore_polyGaussCore_dense N)
          (colouredHamiltonian_symmetricOn _ fabc (star U * C * U) (conjTranspose_colourConj hC))
          x) := by
  have hU' : U * star U = 1 := mul_eq_one_comm.mp hU
  refine clExt_comp_of_bounded_intertwines (T := colouredHamiltonian (coreRepPoly 99) fabc N
      (star U * C * U)) (S := colouredHamiltonian (coreRepPoly 99) fabc N C)
    (colouredCore_polyGaussCore_dense N) _ _ (B := colourMixCLM hU)
    (hB := fun v => colourMix_mem_core U v.2) (hint := fun v => ?_) x
  rw [colourMixCLM_apply]
  have h := colourMix_colouredHamiltonian (coreRepPoly 99) fabc (U := U) (C := C) hU' v
  rw [h]
  exact congrArg _ (Subtype.ext rfl)

/-- **The QYM flow on the coloured core.**  For every Hermitian colour energy matrix `C`, the
coloured Hamiltonian `H ⊗ 1 + 1 ⊗ C` has a self-adjoint extension `T.op` — with domain exactly
`clDom` and values exactly `clExt`, so the extension is determined and not chosen — and a
complete one-parameter unitary group `U` that solves `d/dt U t x = -i T.op (U t x)` on the
domain. -/
theorem exists_stone_flow_of_colouredHamiltonian (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.conjTranspose = C) :
    ∃ (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint (colourSpace N))
      (U : ℝ → (colourSpace N →L[ℂ] colourSpace N)),
      BookProof.EsaClosure.IsSelfAdjointExtension
          (colouredHamiltonian (coreRepPoly 99) fabc N C) T.op ∧
        T.domain = BookProof.EsaClosure.clDom (colouredHamiltonian (coreRepPoly 99) fabc N C) ∧
        (∀ (x : colourSpace N) (h : x ∈ T.domain)
          (h' : x ∈ BookProof.EsaClosure.clDom (colouredHamiltonian (coreRepPoly 99) fabc N C)),
          T.op ⟨x, h⟩ = BookProof.EsaClosure.clExt
            (colouredHamiltonian (coreRepPoly 99) fabc N C)
            (colouredCore_polyGaussCore_dense N)
            (colouredHamiltonian_symmetricOn _ fabc C hC) ⟨x, h'⟩) ∧
        BookProof.StoneBridge.IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ :=
    BookProof.EsaClosure.exists_isSelfAdjointExtension_of_esa
      (colouredHamiltonian (coreRepPoly 99) fabc N C) (colouredCore_polyGaussCore_dense N)
      (colouredHamiltonian_symmetricOn _ fabc C hC) (colouredHamiltonian_esa fabc C hC)
  obtain ⟨hdom, hval⟩ := colouredHamiltonian_extension_eq_closure fabc C hC (A := A) hA
  let T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint (colourSpace N) :=
    BookProof.StoneBridge.unboundedSelfAdjointOf (colouredCore_polyGaussCore_dense N) hA
  refine ⟨T, T.stoneU, hA, hdom, ?_, BookProof.StoneBridge.isStoneFlow_stoneU T⟩
  intro x h h'
  exact hval x h h'

/-! ### The colour matrix on the fibre is the completion's operator

`colourVec N = PiLp 2 (fun _ : Fin N => ℂ)`, and `colourVec 2` is *definitionally*
`EuclideanSpace ℂ (Fin 2)`, the colour fibre of the `fundHilbert` completion.  So the operator
that `hilbActCLM` applies coefficientwise (`eucMatCLM C`) is the operator the field-side mixing
ties to the fibre: on an elementary tensor `x ⊗ v` the colour half of the Hamiltonian acts on `v`
alone, and at `N = 2` that action is `eucMatCLM C`.  In particular a unitary matrix of length two
acts isometrically on the fibre, which is the same isometry `hilbActOp_norm` uses coefficientwise.
-/

/-- The colour matrix acting on the colour fibre, in the shape `colourMix` uses. -/
noncomputable def colourVecAct {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (v : colourVec N) :
    colourVec N :=
  WithLp.toLp 2 (fun i => ∑ j : Fin N, C i j • WithLp.ofLp v j)

/-- **`1 ⊗ C` on an elementary tensor acts on the fibre**: the field-side mixing of the colour
components is the colour matrix on `v` alone. -/
theorem colourMix_colourFibre {D : Submodule ℂ (L2d 99)} (x : D) {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (v : colourVec N) :
    colourMix C (colourFibre x v : colourSpace N) = colourFibre x (colourVecAct C v) := by
  apply WithLp.ofLp_injective
  funext i
  have h1 : ∀ j : Fin N, ((colourFibre x v : colouredCore N D) : colourSpace N).ofLp j
      = WithLp.ofLp v j • (x : L2d 99) := fun j => rfl
  have h2 : ((colourFibre x (colourVecAct C v) : colouredCore N D) : colourSpace N).ofLp i
      = (∑ j : Fin N, C i j • WithLp.ofLp v j) • (x : L2d 99) := rfl
  rw [colourMix_ofLp, h2, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [h1 j, smul_smul, smul_eq_mul]

/-- **On the fundamental fibre the field-side mixing is `eucMatCLM`**, the operator the Hilbert
completion applies coefficientwise (`hilbActCoeff`). -/
theorem colourVecAct_two_eq_eucMatCLM (C : Matrix (Fin 2) (Fin 2) ℂ) (v : colourVec 2) :
    colourVecAct C v = eucMatCLM C v := by
  rw [eucMatCLM_apply_eq]
  apply WithLp.ofLp_injective
  funext i
  simp only [colourVecAct, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, smul_eq_mul]

/-- **A unitary colour matrix acts isometrically on the fundamental fibre**, transported from
`eucMatCLM_norm_of_unitary` along `colourVecAct_two_eq_eucMatCLM`. -/
theorem colourVecAct_norm_of_unitary {C : Matrix (Fin 2) (Fin 2) ℂ} (hC : star C * C = 1)
    (v : colourVec 2) : ‖colourVecAct C v‖ = ‖v‖ := by
  rw [colourVecAct_two_eq_eucMatCLM]
  exact eucMatCLM_norm_of_unitary hC v

/-! ### The completion carries the same colour fibre

`colourSpace 2` and `fundHilbert d` are *not* the same Hilbert space: the first is
`L²(ℝ⁹⁹) ⊗ ℂ²` (`PiLp 2 (fun _ : Fin 2 => L2d 99)`) and the second is `ℓ²(ℕ^d) ⊗ ℂ²`
(`lp (fun _ : Fin d → ℕ => EuclideanSpace ℂ (Fin 2)) 2`).  No canonical isometry between their
base factors exists in the tree, so no identification of the completions is claimed here — an
arbitrary `HilbertBasis` reindexing would be non-canonical and would not intertwine the colour
actions.

What *is* canonical is the colour factor.  Both spaces contain the common fibre
`colourVec 2 = EuclideanSpace ℂ (Fin 2)`: field-side on an elementary tensor `x ⊗ v`
(`colourFibre`, `colourMix_colourFibre`), completion-side as the vector supported at one
occupation multi-index (`hilbFibre`).  On that fibre both act through the *single* operator
`colourVecAct`, which at `N = 2` is `eucMatCLM` (`colourMix_colourFibre`,
`hilbActOp_hilbFibre_colourVecAct`).  So the unitary colour group acts on the same fibre by the
same operator on both sides, even though the ambient completions differ.
-/

/-- The colour fibre inside the Hilbert completion, supported on a single occupation
multi-index. -/
noncomputable def hilbFibre (d : ℕ) (n : Fin d → ℕ) (v : EuclideanSpace ℂ (Fin 2)) :
    fundHilbert d :=
  lp.single 2 n v

theorem hilbFibre_apply (d : ℕ) (n : Fin d → ℕ) (v : EuclideanSpace ℂ (Fin 2))
    (m : Fin d → ℕ) : (hilbFibre d n v : fundHilbert d) m = if m = n then v else 0 := by
  rw [hilbFibre, lp.single_apply, Pi.single_apply]

theorem hilbActOp_hilbFibre (d : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w)
    (n : Fin d → ℕ) (v : EuclideanSpace ℂ (Fin 2)) :
    hilbActOp M hInner (hilbFibre d n v) = hilbFibre d n (eucMatCLM M v) := by
  apply Subtype.ext
  funext m
  rw [hilbActOp_apply, hilbFibre_apply, hilbFibre_apply]
  by_cases hm : m = n
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, map_zero]

/-- **The completion and the field act on the colour fibre by the same operator.** -/
theorem hilbActOp_hilbFibre_colourVecAct (d : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hInner : ∀ v w : EuclideanSpace ℂ (Fin 2),
      inner ℂ (eucMatCLM M v) (eucMatCLM M w) = inner ℂ v w)
    (n : Fin d → ℕ) (v : colourVec 2) :
    hilbActOp M hInner (hilbFibre d n v) = hilbFibre d n (colourVecAct M v) := by
  rw [hilbActOp_hilbFibre, colourVecAct_two_eq_eucMatCLM]

/-- **The exponentiated colour group acts on the completion through the field-side fibre
operator**: `colourGroupActHilbert` on the vector supported at `n` is the vector supported at
`n` with the fibre acted on by `colourVecAct`. -/
theorem colourGroupActHilbert_hilbFibre (d : ℕ) (a : Fin 3) (θ : ℝ)
    (n : Fin d → ℕ) (v : colourVec 2) :
    colourGroupActHilbert (d := d) a θ (hilbFibre d n v)
      = hilbFibre d n (colourVecAct (colourGroupElement a θ) v) := by
  rw [colourGroupActHilbert_apply, hilbActOp_hilbFibre, colourVecAct_two_eq_eucMatCLM]

end Coloured


end

end BookProof.YangMillsNonAbelianEsa
