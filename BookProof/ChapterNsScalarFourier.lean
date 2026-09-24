import BookProof.ChapterNsPartialFourier
import BookProof.ChapterNsScalarVectorCurry

/-!
# The spatial-only Fourier transform on the **scalar** one-particle space

`BookProof.ChapterNsPartialFourier` built the partial (spatial-only) Fourier transform on the
*fibred* model `L²(V; L²(W))` of the Navier–Stokes one-particle space, and
`BookProof.ChapterNsScalarVectorCurry` identified that model with the *scalar* one,
`L²(V × W)`, by the unitary `curryLI`.  This module is what the identification unblocks: the
spatial transform **on the scalar space of two variables**, obtained by conjugation,

* `nsScalarFourier : L²(V × W) ≃ₗᵢ[ℂ] L²(V × W)` — `curryLI ∘ nsPartialFourier ∘ curryLI.symm`,
  with `nsScalarFourier_norm` its Plancherel identity;
* `scalarFibreOp T` — an operator of the fibre variable alone, transported to the scalar space;
  `scalarFibreOp_prodMk` identifies it on the product generators as the expected `1 ⊗ T`,
  `(x, y) ↦ a x * c y ↦ (x, y) ↦ a x * (T c) y`;
* `nsScalarFourier_scalarFibreOp` — the fibre-blindness of the spatial transform, now stated on
  the scalar space: the spatial transform commutes with every operator `1 ⊗ T` of the fibre
  variable;
* `nsScalarFourier_prodMk_eq` — the transform, computed on a product generator, is again the
  scalar picture of the corresponding fibred computation.

Everything here is a conjugation of a proved statement by a proved unitary; no new analysis
enters.
-/

open MeasureTheory

namespace BookProof.NsScalarFourier

open BookProof.NsPartialFourier BookProof.NsScalarVectorCurry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable (V W) in
/-- **The spatial-only Fourier transform of the scalar Navier–Stokes one-particle space**
`L²(ℝ^d_x × ℝ^m_u)`: the fibred transform of `ChapterNsPartialFourier`, conjugated by the
scalar–vector identification `curryLI`. -/
def nsScalarFourier :
    Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) :=
  (curryLI.symm.trans (nsPartialFourier V W)).trans curryLI

/-- Plancherel for the scalar spatial transform. -/
theorem nsScalarFourier_norm (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    ‖nsScalarFourier V W g‖ = ‖g‖ := (nsScalarFourier V W).norm_map g

theorem nsScalarFourier_apply (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W g = curryLI (nsPartialFourier V W (curryLI.symm g)) := rfl

variable (V) in
/-- An operator **of the fibre variable alone**, on the scalar space of two variables: the
pointwise action of `T` in the fibre, transported by `curryLI`.  On the product generators it is
`1 ⊗ T` (`scalarFibreOp_prodMk`). -/
def scalarFibreOp (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) :
    Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) :=
  (curryLI.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((fibreOp V T).comp (curryLI.symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem scalarFibreOp_apply (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    scalarFibreOp V T g = curryLI (fibreOp V T (curryLI.symm g)) := rfl

/-- The pointwise fibre operator acts on a fibred generator in the fibre only. -/
theorem fibreOp_fibMk (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) :
    fibreOp V T (fibMk a c) = fibMk a (T c) := by
  refine Lp.ext ?_
  filter_upwards [T.coeFn_compLp (fibMk a c), coeFn_fibMk a c, coeFn_fibMk a (T c)]
    with x h1 h2 h3
  rw [fibreOp_apply, h1, h2, h3, map_smul]

/-- **The fibre operator is `1 ⊗ T`.**  On the product generator `(x, y) ↦ a x * c y` the
transported operator acts in the second variable only. -/
theorem scalarFibreOp_prodMk (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (a : Lp ℂ 2 (volume : Measure V)) (c : Lp ℂ 2 (volume : Measure W)) :
    scalarFibreOp V T (prodMk a c) = prodMk a (T c) := by
  rw [scalarFibreOp_apply, ← curryLI_fibMk (μ := (volume : Measure V)) (ν := (volume : Measure W)),
    LinearIsometryEquiv.symm_apply_apply, fibreOp_fibMk, curryLI_fibMk]

/-- **The spatial transform leaves the fibre variable alone**, on the scalar space: it commutes
with every operator `1 ⊗ T` of the fibre variable. -/
theorem nsScalarFourier_scalarFibreOp
    (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W (scalarFibreOp V T g) = scalarFibreOp V T (nsScalarFourier V W g) := by
  rw [nsScalarFourier_apply, scalarFibreOp_apply, scalarFibreOp_apply, nsScalarFourier_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    nsPartialFourier_fibreOp]

/-- The scalar transform of a product generator is the scalar picture of the fibred transform of
the corresponding fibred generator. -/
theorem nsScalarFourier_prodMk_eq (a : Lp ℂ 2 (volume : Measure V))
    (c : Lp ℂ 2 (volume : Measure W)) :
    nsScalarFourier V W (prodMk a c) = curryLI (nsPartialFourier V W (fibMk a c)) := by
  rw [nsScalarFourier_apply,
    ← curryLI_fibMk (μ := (volume : Measure V)) (ν := (volume : Measure W)),
    LinearIsometryEquiv.symm_apply_apply]

/-- In particular the scalar spatial transform commutes with the Fourier transform **of the fibre
variable**: the two partial transforms of the two variables are independent. -/
theorem nsScalarFourier_fibreFourier
    (g : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))) :
    nsScalarFourier V W (scalarFibreOp V (fibreFourierCLM W) g)
      = scalarFibreOp V (fibreFourierCLM W) (nsScalarFourier V W g) :=
  nsScalarFourier_scalarFibreOp _ g

end

end BookProof.NsScalarFourier
