import Mathlib
import BookProof.Toolbox.ChapterTensorSumEsa
import BookProof.Qym.ChapterYangMillsNonAbelianEsa
import BookProof.Qg.ChapterConformalSignFlip
import BookProof.Toolbox.ChapterEsaRealShift
import BookProof.Ode.ChapterOdeChartTransfer
import BookProof.Toolbox.ChapterL2TensorPowerUnitary

/-!
# QG-D-C.1 — the continuum flat densitized operator: trivial deficiency at every non-real `z`

`CONSOLIDATED_PLAN.md` §"2026-10-15b", row QG-D-C.1 (and the corrected wording recorded in
§"2026-10-15d").

After the densitized change of variables the gauge-fixed gravity Hamiltonian has the
**flat**, constant-coefficient, *indefinite* principal part

  `(1/16) Σ_a ∂²-part  −  (1/24) ∂_y²-part`,   symbol `qgSymbol ξ ξ_y = (1/16)|ξ|² − (1/24)ξ_y²`,

on the continuum field space `ℝⁿ × ℝ` (`n = 83` spatial/shear directions plus the
densitized conformal coordinate `y`, i.e. `L²(ℝ⁸⁴)`).  This module proves the row's
conclusion — `DeficiencyTrivialAt` at **every** non-real `z`, hence essential
self-adjointness and a complete unitary flow — for that operator with a polynomial
potential, **under the sign condition that makes the statement true**:

  `H = (1/16)(−Δ_x) + V_s(x)  − [ (1/24)(−∂_y²) + V_c(y) ]`,

with `V_s` and `V_c` real polynomials **bounded below**.  The conformal potential enters
with the same sign as the conformal kinetic term — exactly the sign of the densitized
`− e·Q_b = − y²·Q_b` term for `Q_b ≥ 0`.

## Why a sign condition is part of the statement

For the opposite sign (the conformal potential *bounded below* in `H` itself, e.g.
`+y⁴`), the conformal fibre `−(1/24)(−∂_y²) + V(y)` is, after the global sign flip
(`ConformalSignFlip.wrongSignKinetic_esa_iff`), a Schrödinger operator with a potential
unbounded *below*: the Weyl limit-circle class where essential self-adjointness fails
(`−d²/dy² − y⁴` has deficiency indices `(2,2)`; the project proves the failure for explicit
smooth potentials of this class in `ChapterLimitCircleExample` and
`ChapterConformalFiberDeficiency`).  Tensoring with a spatial oscillator eigenvector carries
such a deficiency vector to one of the full operator (an argument recorded here, not
formalized), so "flat d'Alembertian + arbitrary
polynomial potential" is not essentially self-adjoint in general, and the row can only be
proved with the sign condition above.  Non-separable (mixed `x`–`y`) polynomial potentials
are not covered here.

## What is proved

**Abstract (any two Hilbert spaces).**
* `flatOp A B = A ⊗ 1 − 1 ⊗ B` on `D_A ⊗ D_B` inside `H ⊗̂ K`;
* `flatOp_symmetricOn`, `flatOp_dense`, **`flatOp_esa`**, **`flatOp_deficiencyTrivialAt`**
  (every non-real `z`), `flatOp_stone_flow` — for `A`, `B` symmetric and essentially
  self-adjoint on dense domains; no sign, semiboundedness or relative bound on `H` itself.

**The QG instance on the Gauss–polynomial cores.**
* `spatialOp n q b = (1/16)(−Δ_{ℝⁿ} + polyW q) + b` and `confOp q' b' = (1/24)(−∂_y² + polyW q') + b'`,
  i.e. `(1/16)(−Δ) + V_s` with `V_s = polyW q / 16 + b`, and `(1/24)(−∂²) + V_c` with
  `V_c = polyW q' / 24 + b'`; every real polynomial bounded below has this form;
* `spatialOp_esa`, `confOp_esa` (Kato-type theorem `HermiteGraphApprox.hamCoreS_esa`);
* `qgFlatOp`, **`qgFlat_esa`**, **`qgFlat_deficiencyTrivialAt`** on `L²(ℝⁿ) ⊗̂ L²(ℝ)`.

**The concrete continuum space `L²(ℝⁿ × ℝ)`.**
* `prodUnitary : L²(μ) ⊗̂ L²(ν) ≃ₗᵢ L²(μ ⊗ ν)` (the unitary extending
  `a ⊗ c ↦ ((x, y) ↦ a x · c y)`, `prodUnitary_tmul`, `prodUnitary_tmul_ae`);
* `qgFlatCore`, `qgFlatL2Op` — the operator transported to `L²(ℝⁿ × ℝ)`, with domain the
  span of the products `f(x) g(y)` of Gauss–polynomial functions, and
  `qgFlatL2Op_tmul` (its action on a product);
* **`qgFlatL2_esa`**, **`qgFlatL2_deficiencyTrivialAt`**, **`qgFlatL2_stone_flow`** — the
  continuum statement of QG-D-C.1, and **`qgFlat84_deficiencyTrivialAt`** — the `n = 83`
  instance on `L²(ℝ⁸³ × ℝ) ≅ L²(ℝ⁸⁴)`.

**Into the transfer (QG-D-C.2 without `hflat`).**
* `esa_of_unitary_intertwines` / **`qg_flat_transfer_esa`** — any physical operator carried by
  a unitary onto the flat core and intertwined with `qgFlatL2Op` is essentially
  self-adjoint and has trivial deficiency at every non-real `z`: the flat input is now a
  theorem rather than the hypothesis `hflat`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgFlatContinuumEsa

open MeasureTheory
open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumEsa
  BookProof.YangMillsNonAbelianEsa BookProof.HermiteProductCore BookProof.DegSchrodinger
  BookProof.HermiteGraphApprox BookProof.ChapterStoneResolvent BookProof.StoneBridge
  BookProof.OdeChartTransfer BookProof.EsaClosure BookProof.GraphCore

noncomputable section

/-! ## 1. The abstract flat operator `A ⊗ 1 − 1 ⊗ B` -/

section Abstract

variable {Hs Ks : IPSpace} {DA : Submodule ℂ Hs.carrier} {DB : Submodule ℂ Ks.carrier}

/-- **The flat (indefinite) separated operator** `A ⊗ 1 − 1 ⊗ B` on `D_A ⊗ D_B`, inside the
completed tensor product `H ⊗̂ K`. -/
def flatOp (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier) :
    cpairDom Hs Ks DA DB →ₗ[ℂ] ctensor Hs Ks :=
  cpairOp Hs Ks DA DB A (-B)

theorem flatOp_symmetricOn (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (hsymA : SymmetricOn DA A) (hsymB : SymmetricOn DB B) :
    SymmetricOn (cpairDom Hs Ks DA DB) (flatOp A B) :=
  symmetricOn_cpairOp Hs Ks DA DB A (-B) hsymA (ConformalSignFlip.symmetricOn_neg hsymB)

theorem flatOp_dense (hdenseA : Dense (DA : Set Hs.carrier))
    (hdenseB : Dense (DB : Set Ks.carrier)) :
    Dense (cpairDom Hs Ks DA DB : Set (ctensor Hs Ks)) :=
  dense_cpairDom Hs Ks DA DB hdenseA hdenseB

variable [CompleteSpace Hs.carrier] [CompleteSpace Ks.carrier]

/-- **The flat separated operator is essentially self-adjoint** as soon as both factors are
symmetric and essentially self-adjoint on dense domains. -/
theorem flatOp_esa (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (hdenseA : Dense (DA : Set Hs.carrier)) (hdenseB : Dense (DB : Set Ks.carrier))
    (hsymA : SymmetricOn DA A) (hsymB : SymmetricOn DB B)
    (hesaA : EssentiallySelfAdjointOn DA A) (hesaB : EssentiallySelfAdjointOn DB B) :
    EssentiallySelfAdjointOn (cpairDom Hs Ks DA DB) (flatOp A B) :=
  essentiallySelfAdjointOn_cpairDom_esa A (-B) hdenseA hdenseB hsymA
    (ConformalSignFlip.symmetricOn_neg hsymB) hesaA (ConformalSignFlip.essentiallySelfAdjointOn_neg hesaB)

/-- **Trivial deficiency at every non-real `z`** for the flat separated operator. -/
theorem flatOp_deficiencyTrivialAt (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (hdenseA : Dense (DA : Set Hs.carrier)) (hdenseB : Dense (DB : Set Ks.carrier))
    (hsymA : SymmetricOn DA A) (hsymB : SymmetricOn DB B)
    (hesaA : EssentiallySelfAdjointOn DA A) (hesaB : EssentiallySelfAdjointOn DB B)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (cpairDom Hs Ks DA DB) (flatOp A B) z :=
  EsaRealShift.deficiencyTrivialAt_of_essentiallySelfAdjointOn
    (flatOp_symmetricOn A B hsymA hsymB)
    (flatOp_esa A B hdenseA hdenseB hsymA hsymB hesaA hesaB) hz

/-- The flat separated operator generates a complete unitary (Stone) flow. -/
theorem flatOp_stone_flow (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (hdenseA : Dense (DA : Set Hs.carrier)) (hdenseB : Dense (DB : Set Ks.carrier))
    (hsymA : SymmetricOn DA A) (hsymB : SymmetricOn DB B)
    (hesaA : EssentiallySelfAdjointOn DA A) (hesaB : EssentiallySelfAdjointOn DB B) :
    ∃ (G : UnboundedSelfAdjoint (ctensor Hs Ks))
      (U : ℝ → (ctensor Hs Ks →L[ℂ] ctensor Hs Ks)),
      IsSelfAdjointExtension (flatOp A B) G.op ∧ IsStoneFlow G U :=
  exists_stone_flow_of_esa _ (flatOp_dense hdenseA hdenseB)
    (flatOp_symmetricOn A B hsymA hsymB) (flatOp_esa A B hdenseA hdenseB hsymA hsymB hesaA hesaB)

end Abstract

/-! ## 2. The factors: scaled Schrödinger operators with polynomial potentials -/

section Factors

open BookProof.YangMillsHermite MvPolynomial

variable {d : ℕ}

/-- **A scaled Schrödinger operator** `a(−Δ + polyW q) + b` on the Gauss–polynomial core of
`L²(ℝᵈ)`: kinetic coefficient `a`, potential `a·polyW q + b`. -/
def schOp (d : ℕ) (a : ℝ) (q : MvPolynomial (Fin d) ℂ) (b : ℝ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (a : ℂ) • hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) Finset.univ
    + (b : ℂ) • (polyGaussCore (d := d)).subtype

theorem schOp_symmetricOn (a : ℝ) (q : MvPolynomial (Fin d) ℂ) (b : ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (schOp d a q b) := by
  intro x y
  have h := hamCoreS_symmetricOn (polyW q) (continuous_polyW q) (expBounded_polyW q)
    Finset.univ x y
  simp only [schOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal, h]

theorem schOp_esa {a : ℝ} (ha : 0 < a) (q : MvPolynomial (Fin d) ℂ) (hq : RealCoeff q)
    (hq1 : ∀ x, 1 ≤ polyW q x) (b : ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (schOp d a q b) :=
  essentiallySelfAdjointOn_affine _
    (hamCoreS_symmetricOn (polyW q) (continuous_polyW q) (expBounded_polyW q) Finset.univ)
    (hamCoreS_esa q hq hq1 Finset.univ) ha b

/-- **Every real polynomial potential that is bounded below is of the form used by `schOp`**:
if `polyW p ≥ c`, then for `a > 0` there is a real polynomial `q` with `polyW q ≥ 1` and
`a · polyW q + (c − a) = polyW p`.  So `schOp d a q (c − a) = a(−Δ) + polyW p`. -/
theorem exists_schOp_repr {a : ℝ} (ha : 0 < a) (p : MvPolynomial (Fin d) ℂ) (hp : RealCoeff p)
    {c : ℝ} (hc : ∀ x, c ≤ polyW p x) :
    ∃ q : MvPolynomial (Fin d) ℂ, RealCoeff q ∧ (∀ x, 1 ≤ polyW q x) ∧
      ∀ x, a * polyW q x + (c - a) = polyW p x := by
  refine ⟨((a⁻¹ : ℝ) : ℂ) • (p + C (((-c : ℝ)) : ℂ)) + C (((1 : ℝ)) : ℂ),
    ((hp.add (realCoeff_C_real' _)).smul).add (realCoeff_C_real' _), ?_, ?_⟩
  · intro x
    have hx := hc x
    have : polyW (((a⁻¹ : ℝ) : ℂ) • (p + C (((-c : ℝ)) : ℂ)) + C (((1 : ℝ)) : ℂ)) x
        = a⁻¹ * (polyW p x - c) + 1 := by
      simp [polyW, MvPolynomial.smul_eval]
      ring
    rw [this]
    have : 0 ≤ a⁻¹ * (polyW p x - c) := mul_nonneg (inv_nonneg.2 ha.le) (by linarith)
    linarith
  · intro x
    have : polyW (((a⁻¹ : ℝ) : ℂ) • (p + C (((-c : ℝ)) : ℂ)) + C (((1 : ℝ)) : ℂ)) x
        = a⁻¹ * (polyW p x - c) + 1 := by
      simp [polyW, MvPolynomial.smul_eval]
      ring
    rw [this]
    field_simp
    ring

/-- The **spatial (shear) factor** `(1/16)(−Δ_{ℝⁿ}) + V_s`, `V_s = polyW q / 16 + b`. -/
def spatialOp (n : ℕ) (q : MvPolynomial (Fin n) ℂ) (b : ℝ) :
    (polyGaussCore (d := n)) →ₗ[ℂ] L2d n :=
  schOp n (1 / 16) q b

/-- The **conformal factor** `(1/24)(−∂_y²) + V_c`, `V_c = polyW q / 24 + b`, on `L²(ℝ)`. -/
def confOp (q : MvPolynomial (Fin 1) ℂ) (b : ℝ) : (polyGaussCore (d := 1)) →ₗ[ℂ] L2d 1 :=
  schOp 1 (1 / 24) q b

end Factors

/-! ## 3. The QG flat operator on `L²(ℝⁿ) ⊗̂ L²(ℝ)` -/

section QgTensor

open BookProof.YangMillsHermite

variable (n : ℕ)

/-- The flat core `D_n ⊗ D_1` (Gauss–polynomial cores) inside `L²(ℝⁿ) ⊗̂ L²(ℝ)`. -/
abbrev qgTensorCore : Submodule ℂ (ctensor (L2dSpace n) (L2dSpace 1)) :=
  cpairDom (L2dSpace n) (L2dSpace 1) (polyGaussCore (d := n)) (polyGaussCore (d := 1))

/-- **The densitized flat gravity operator**
`H = (1/16)(−Δ_x) + V_s(x) − [(1/24)(−∂_y²) + V_c(y)]` on `D_n ⊗ D_1`. -/
def qgFlatOp (qs : MvPolynomial (Fin n) ℂ) (bs : ℝ) (qc : MvPolynomial (Fin 1) ℂ) (bc : ℝ) :
    qgTensorCore n →ₗ[ℂ] ctensor (L2dSpace n) (L2dSpace 1) :=
  flatOp (Hs := L2dSpace n) (Ks := L2dSpace 1) (spatialOp n qs bs) (confOp qc bc)

theorem qgFlat_symmetricOn (qs : MvPolynomial (Fin n) ℂ) (bs : ℝ) (qc : MvPolynomial (Fin 1) ℂ)
    (bc : ℝ) : SymmetricOn (qgTensorCore n) (qgFlatOp n qs bs qc bc) :=
  flatOp_symmetricOn (Hs := L2dSpace n) (Ks := L2dSpace 1) _ _
    (schOp_symmetricOn _ _ _) (schOp_symmetricOn _ _ _)

theorem qgTensorCore_dense : Dense (qgTensorCore n : Set (ctensor (L2dSpace n) (L2dSpace 1))) :=
  flatOp_dense (Hs := L2dSpace n) (Ks := L2dSpace 1) polyGaussCore_dense polyGaussCore_dense

/-- **QG-D-C.1 on the tensor-product space: the flat densitized operator is essentially
self-adjoint**, for real polynomials `qs`, `qc` with `polyW ≥ 1` (equivalently, by
`exists_schOp_repr`, for any real polynomial potentials `V_s`, `V_c` bounded below). -/
theorem qgFlat_esa {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs) (hqs1 : ∀ x, 1 ≤ polyW qs x)
    (bs : ℝ) {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc) (hqc1 : ∀ x, 1 ≤ polyW qc x)
    (bc : ℝ) : EssentiallySelfAdjointOn (qgTensorCore n) (qgFlatOp n qs bs qc bc) :=
  flatOp_esa (Hs := L2dSpace n) (Ks := L2dSpace 1) _ _ polyGaussCore_dense polyGaussCore_dense
    (schOp_symmetricOn _ _ _) (schOp_symmetricOn _ _ _)
    (schOp_esa (by norm_num) qs hqs hqs1 bs) (schOp_esa (by norm_num) qc hqc hqc1 bc)

/-- **QG-D-C.1 on the tensor-product space: trivial deficiency at every non-real `z`.** -/
theorem qgFlat_deficiencyTrivialAt {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs)
    (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ) {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc)
    (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (qgTensorCore n) (qgFlatOp n qs bs qc bc) z :=
  EsaRealShift.deficiencyTrivialAt_of_essentiallySelfAdjointOn (qgFlat_symmetricOn n _ _ _ _)
    (qgFlat_esa n hqs hqs1 bs hqc hqc1 bc) hz

end QgTensor

/-! ## 4. The concrete continuum space `L²(ℝⁿ × ℝ)` -/

section Concrete

open BookProof.YangMillsHermite BookProof.L2TensorPower BookProof.NsScalarVectorCurry

/-- **The product unitary** `L²(ℝⁿ) ⊗̂ L²(ℝᵐ) ≃ L²(ℝⁿ × ℝᵐ)`: the unique unitary extending
`a ⊗ c ↦ ((x, y) ↦ a x · c y)`. -/
def prodUnitary (n m : ℕ) :
    ctensor (L2dSpace n) (L2dSpace m) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd m)) :=
  (LinearEquiv.refl ℂ ((L2dSpace n).carrier ⊗[ℂ] (L2dSpace m).carrier)).extendOfIsometry
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap
    (prodTensorₗᵢ (volume : Measure (Vd n)) (volume : Measure (Vd m))).toLinearMap
    UniformSpace.Completion.denseRange_coe
    (denseRange_prodTensor (μ := (volume : Measure (Vd n))) (ν := (volume : Measure (Vd m))))
    (fun x => by simp; exact LinearIsometry.norm_map _ x)

theorem prodUnitary_coe (n m : ℕ) (x : (L2dSpace n).carrier ⊗[ℂ] (L2dSpace m).carrier) :
    prodUnitary n m (x : ctensor (L2dSpace n) (L2dSpace m))
      = prodTensorₗᵢ (volume : Measure (Vd n)) (volume : Measure (Vd m)) x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

theorem prodUnitary_tmul (n m : ℕ) (a : L2d n) (c : L2d m) :
    prodUnitary n m (((a ⊗ₜ[ℂ] c : (L2dSpace n).carrier ⊗[ℂ] (L2dSpace m).carrier)) :
      ctensor (L2dSpace n) (L2dSpace m)) = prodMk a c := by
  rw [prodUnitary_coe]
  rfl

/-- The pointwise formula: the image of `a ⊗ c` is `(x, y) ↦ a x · c y` almost everywhere. -/
theorem prodUnitary_tmul_ae (n m : ℕ) (a : L2d n) (c : L2d m) :
    (prodUnitary n m (((a ⊗ₜ[ℂ] c : (L2dSpace n).carrier ⊗[ℂ] (L2dSpace m).carrier)) :
      ctensor (L2dSpace n) (L2dSpace m)) : Vd n × Vd m → ℂ)
      =ᵐ[volume] fun z => (a : Vd n → ℂ) z.1 * (c : Vd m → ℂ) z.2 := by
  rw [prodUnitary_tmul]
  exact coeFn_prodMk a c

variable (n : ℕ)

/-- **The flat core in `L²(ℝⁿ × ℝ)`**: the image of `D_n ⊗ D_1`, i.e. the span of the products
`f(x) g(y)` of Gauss–polynomial functions. -/
abbrev qgFlatCore : Submodule ℂ (Lp ℂ 2 (volume : Measure (Vd n × Vd 1))) :=
  conjDomain (prodUnitary n 1) (qgTensorCore n)

/-- **The densitized flat gravity operator on `L²(ℝⁿ × ℝ)`**,
`H = (1/16)(−Δ_x) + V_s(x) − [(1/24)(−∂_y²) + V_c(y)]`, on `qgFlatCore n`. -/
def qgFlatL2Op (qs : MvPolynomial (Fin n) ℂ) (bs : ℝ) (qc : MvPolynomial (Fin 1) ℂ) (bc : ℝ) :
    qgFlatCore n →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1)) :=
  conjOp (prodUnitary n 1) (qgTensorCore n) (qgFlatOp n qs bs qc bc)

/-- The product state `a ⊗ c` as an element of the tensor core. -/
def tensorElt (a : polyGaussCore (d := n)) (c : polyGaussCore (d := 1)) : qgTensorCore n :=
  ⟨pairEmb (L2dSpace n) (L2dSpace 1)
    (inclPair (L2dSpace n) (L2dSpace 1) (polyGaussCore (d := n)) (polyGaussCore (d := 1))
      (a ⊗ₜ[ℂ] c)), mem_pushDom (pairEmb (L2dSpace n) (L2dSpace 1))
      (⟨_, ⟨a ⊗ₜ[ℂ] c, rfl⟩⟩ : pairDom (L2dSpace n) (L2dSpace 1) _ _)⟩

theorem prodUnitary_tensorElt (a : polyGaussCore (d := n)) (c : polyGaussCore (d := 1)) :
    prodUnitary n 1 (tensorElt n a c : ctensor (L2dSpace n) (L2dSpace 1))
      = prodMk (a : L2d n) (c : L2d 1) := by
  have h : (tensorElt n a c : ctensor (L2dSpace n) (L2dSpace 1))
      = ((((a : L2d n) ⊗ₜ[ℂ] (c : L2d 1) : (L2dSpace n).carrier ⊗[ℂ] (L2dSpace 1).carrier)) :
        ctensor (L2dSpace n) (L2dSpace 1)) := by
    simp only [tensorElt, inclPair_tmul]
    rfl
  rw [h, prodUnitary_tmul]

/-- A product of two Gauss–polynomial functions lies in the flat core. -/
theorem prodMk_mem_qgFlatCore (a : polyGaussCore (d := n)) (c : polyGaussCore (d := 1)) :
    prodMk (a : L2d n) (c : L2d 1) ∈ qgFlatCore n := by
  rw [← prodUnitary_tensorElt]
  exact (conjEquiv (prodUnitary n 1) (qgTensorCore n) (tensorElt n a c)).2

set_option maxHeartbeats 8000000 in
/-- **The action on a product state**: `H (f ⊗ g) = (A f) ⊗ g − f ⊗ (B g)`, i.e.
`(x, y) ↦ (A f)(x) g(y) − f(x) (B g)(y)`. -/
theorem qgFlatL2Op_tmul (qs : MvPolynomial (Fin n) ℂ) (bs : ℝ) (qc : MvPolynomial (Fin 1) ℂ)
    (bc : ℝ) (a : polyGaussCore (d := n)) (c : polyGaussCore (d := 1)) :
    qgFlatL2Op n qs bs qc bc ⟨prodMk (a : L2d n) (c : L2d 1), prodMk_mem_qgFlatCore n a c⟩
      = prodMk (spatialOp n qs bs a) (c : L2d 1) - prodMk (a : L2d n) (confOp qc bc c) := by
  have hconj : (⟨prodMk (a : L2d n) (c : L2d 1), prodMk_mem_qgFlatCore n a c⟩ : qgFlatCore n)
      = conjEquiv (prodUnitary n 1) (qgTensorCore n) (tensorElt n a c) :=
    Subtype.ext (by rw [conjEquiv_coe, prodUnitary_tensorElt])
  have hop : qgFlatOp n qs bs qc bc (tensorElt n a c)
      = pairEmb (L2dSpace n) (L2dSpace 1)
          (sumPoly (L2dSpace n) (L2dSpace 1) _ _ (spatialOp n qs bs) (-confOp qc bc)
            (a ⊗ₜ[ℂ] c)) :=
    cpairOp_apply (L2dSpace n) (L2dSpace 1) _ _ _ _ (tensorElt n a c) (a ⊗ₜ[ℂ] c) rfl
  refine (congrArg (qgFlatL2Op n qs bs qc bc) hconj).trans ?_
  have h2 : qgFlatL2Op n qs bs qc bc (conjEquiv (prodUnitary n 1) (qgTensorCore n)
      (tensorElt n a c)) = prodUnitary n 1 (qgFlatOp n qs bs qc bc (tensorElt n a c)) :=
    conjOp_conjEquiv _ _ _ _
  rw [h2, hop]
  change prodUnitary n 1 ((sumPoly (L2dSpace n) (L2dSpace 1) _ _ (spatialOp n qs bs)
    (-confOp qc bc) (a ⊗ₜ[ℂ] c) : (L2dSpace n).carrier ⊗[ℂ] (L2dSpace 1).carrier) :
      ctensor (L2dSpace n) (L2dSpace 1)) = _
  rw [sumPoly_tmul, UniformSpace.Completion.coe_add, map_add, prodUnitary_tmul, prodUnitary_tmul]
  have hneg : prodMk (a : L2d n) ((-confOp qc bc) c) = -prodMk (a : L2d n) (confOp qc bc c) :=
    (prodBil (μ := (volume : Measure (Vd n))) (ν := (volume : Measure (Vd 1)))
      (a : L2d n)).map_neg (confOp qc bc c)
  rw [sub_eq_add_neg, ← hneg]
  rfl

theorem qgFlatCore_dense : Dense (qgFlatCore n : Set (Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))) :=
  conjDomain_dense _ (qgTensorCore_dense n)

theorem qgFlatL2_symmetricOn (qs : MvPolynomial (Fin n) ℂ) (bs : ℝ) (qc : MvPolynomial (Fin 1) ℂ)
    (bc : ℝ) : SymmetricOn (qgFlatCore n) (qgFlatL2Op n qs bs qc bc) :=
  conj_symmetricOn _ (qgFlat_symmetricOn n qs bs qc bc)

/-- **QG-D-C.1, continuum form: the flat densitized gravity operator on `L²(ℝⁿ × ℝ)` with
polynomial potentials `V_s(x) − V_c(y)` (`V_s`, `V_c` bounded below) is essentially
self-adjoint on the span of the Gauss–polynomial product states.** -/
theorem qgFlatL2_esa {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs)
    (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ) {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc)
    (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ) :
    EssentiallySelfAdjointOn (qgFlatCore n) (qgFlatL2Op n qs bs qc bc) :=
  conj_essentiallySelfAdjointOn _ (qgFlat_esa n hqs hqs1 bs hqc hqc1 bc)

/-- **QG-D-C.1, continuum form: `DeficiencyTrivialAt` at every non-real `z`.** -/
theorem qgFlatL2_deficiencyTrivialAt {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs)
    (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ) {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc)
    (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (qgFlatCore n) (qgFlatL2Op n qs bs qc bc) z :=
  conj_deficiencyTrivialAt _ (qgFlat_deficiencyTrivialAt n hqs hqs1 bs hqc hqc1 bc hz)

/-- **QG-D-C.1 → QG-D-C.3 (continuum flat side)**: the flat densitized operator generates a
complete unitary (Stone) flow on `L²(ℝⁿ × ℝ)`. -/
theorem qgFlatL2_stone_flow {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs)
    (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ) {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc)
    (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ) :
    ∃ (G : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure (Vd n × Vd 1))))
      (U : ℝ → (Lp ℂ 2 (volume : Measure (Vd n × Vd 1)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vd n × Vd 1)))),
      IsSelfAdjointExtension (qgFlatL2Op n qs bs qc bc) G.op ∧ IsStoneFlow G U :=
  exists_stone_flow_of_esa _ (qgFlatCore_dense n) (qgFlatL2_symmetricOn n qs bs qc bc)
    (qgFlatL2_esa n hqs hqs1 bs hqc hqc1 bc)

/-- **The field-space instance**: `83` flat spatial/shear directions plus the densitized
conformal coordinate, i.e. `L²(ℝ⁸³ × ℝ) ≅ L²(ℝ⁸⁴)`. -/
theorem qgFlat84_deficiencyTrivialAt {qs : MvPolynomial (Fin 83) ℂ} (hqs : RealCoeff qs)
    (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ) {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc)
    (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (qgFlatCore 83) (qgFlatL2Op 83 qs bs qc bc) z :=
  qgFlatL2_deficiencyTrivialAt 83 hqs hqs1 bs hqc hqc1 bc hz

end Concrete

/-! ## 5. Into the transfer: the flat input as a theorem -/

section Transfer

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- **Unitary transfer of the deficiency.**  If the unitary `W` carries the domain `D` onto
`D'` and intertwines `H` with `H'`, trivial deficiency of `H'` at `z` gives it for `H`. -/
theorem deficiencyTrivialAt_of_unitary_intertwines (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} (H : D →ₗ[ℂ] F) (H' : D' →ₗ[ℂ] G)
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, H' ⟨W (x : F), hmap x⟩ = W (H x)) {z : ℂ}
    (h : DeficiencyTrivialAt D' H' z) : DeficiencyTrivialAt D H z := by
  intro w hw
  have hWw : W w = 0 := by
    refine h (W w) fun y => ?_
    obtain ⟨x, hx⟩ := hsurj y
    have hy : y = ⟨W (x : F), hmap x⟩ := Subtype.ext hx.symm
    rw [hy, hint x, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
    exact hw x
  simpa using congrArg W.symm hWw

/-- Essential self-adjointness transfers along the same data. -/
theorem esa_of_unitary_intertwines (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} (H : D →ₗ[ℂ] F) (H' : D' →ₗ[ℂ] G)
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, H' ⟨W (x : F), hmap x⟩ = W (H x))
    (h : EssentiallySelfAdjointOn D' H') : EssentiallySelfAdjointOn D H :=
  ⟨deficiencyTrivialAt_of_unitary_intertwines W H H' hmap hsurj hint h.1,
    deficiencyTrivialAt_of_unitary_intertwines W H H' hmap hsurj hint h.2⟩

open BookProof.YangMillsHermite in
/-- **QG-D-C.2 with the flat input discharged.**  Any physical realization `H` of the
gravity Hamiltonian that a unitary `W` carries onto the flat core `qgFlatCore n` and
intertwines with the flat densitized operator `qgFlatL2Op` (the role of the half-density
unitary) has trivial deficiency at every non-real `z` and is essentially self-adjoint.  The
former hypothesis `hflat` is supplied by `qgFlatL2_deficiencyTrivialAt`. -/
theorem qg_flat_transfer_esa (n : ℕ) {D : Submodule ℂ F}
    (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vd n × Vd 1))) (H : D →ₗ[ℂ] F)
    {qs : MvPolynomial (Fin n) ℂ} (hqs : RealCoeff qs) (hqs1 : ∀ x, 1 ≤ polyW qs x) (bs : ℝ)
    {qc : MvPolynomial (Fin 1) ℂ} (hqc : RealCoeff qc) (hqc1 : ∀ x, 1 ≤ polyW qc x) (bc : ℝ)
    (hmap : ∀ x : D, W (x : F) ∈ qgFlatCore n)
    (hsurj : ∀ y : qgFlatCore n, ∃ x : D, W (x : F) = (y : Lp ℂ 2 _))
    (hint : ∀ x : D, qgFlatL2Op n qs bs qc bc ⟨W (x : F), hmap x⟩ = W (H x)) :
    EssentiallySelfAdjointOn D H ∧ ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt D H z :=
  ⟨esa_of_unitary_intertwines W H _ hmap hsurj hint (qgFlatL2_esa n hqs hqs1 bs hqc hqc1 bc),
    fun _ hz => deficiencyTrivialAt_of_unitary_intertwines W H _ hmap hsurj hint
      (qgFlatL2_deficiencyTrivialAt n hqs hqs1 bs hqc hqc1 bc hz)⟩

end Transfer

end

end BookProof.QgFlatContinuumEsa
