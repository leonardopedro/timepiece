import Mathlib
import BookProof.ChapterHermiteGraphApprox
import BookProof.ChapterYangMillsHermite
import BookProof.ChapterEsaOneParticleDGamma

/-!
# The non-abelian Yang–Mills one-particle Hamiltonian is essentially self-adjoint

The tree had essential self-adjointness of the gauge-fixed Yang–Mills Hamiltonian only in the
abelian (quadratic) case (`BookProof/ChapterYangMillsAbelianEsa.lean`).  The Kato-type
theorem of `BookProof/ChapterDegKatoEsa.lean` and its transfer to the Gauss–polynomial core
(`BookProof/ChapterHermiteGraphApprox.lean`) hold for an arbitrary real polynomial potential
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
  finite-particle domain over that core, by the lift of `BookProof/ChapterEsaOneParticleDGamma`.

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

end

end BookProof.YangMillsNonAbelianEsa
