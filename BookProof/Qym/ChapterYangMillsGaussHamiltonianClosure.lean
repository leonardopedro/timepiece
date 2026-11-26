import BookProof.Qym.ChapterYangMillsGaussClosure
import BookProof.Qym.ChapterYangMillsNonAbelianEsa

/-!
# The Hamiltonian's closure and the Gauss charge

`BookProof/Qym/ChapterYangMillsGaussSkew.lean` proves `[H, 𝒢_d] = 0` on the
Gauss–polynomial core, but for the *transported polynomial* Hamiltonian
`Φ.op (ymHamPoly G)`; its docstring names the identification with the analytic
`ymHamiltonian` as a rewrite it does not carry out.  `ChapterYangMillsGaussClosure`
builds the closure of `𝒢_d` from skewness.  `ChapterYangMillsNonAbelianEsa`
proves the analytic Hamiltonian is essentially self-adjoint on that same core
(`ym_h_esa`).

This module joins the three:

* **`coreOp_ymHamPoly_eq_ymHamiltonian`** — the bridge: the transported
  polynomial Hamiltonian *is* `ymHamiltonian (coreRepPoly 99) G.f`, pointwise on
  the core.  It is a rewrite chain through `weylOpDom`, `piOps`, `magOps`, not a
  new analytic fact.
* **`ymHamiltonian_comm_gauss_core`** — hence `[H, 𝒢_d] = 0` on the core for
  the operator that is actually essentially self-adjoint.
* **`hamClosure`, `hamClosure_isSelfAdjointExtension`,
  `hamClosure_unique`** — the closure of `H` built from the ESA input, proved to
  be the (unique) self-adjoint extension of `H` on the core.  Domain and values
  are pinned by `isSelfAdjointExtension_unique_of_esa`, so this is the operator
  the Stone flow of `ChapterYangMillsNonAbelianEsa` evolves.
* **`hamClosure_comm_gaussClosure_core`** — the two *closed* operators commute
  on the shared Gauss core: `Ā (H̄ x) = H̄ (Ā x)` for `x` in the core, where `Ā`
  is the closure of `𝒢_d` and `H̄` the closure of `H`.  This is the core-level
  form of the `DomPreserve` / `StrongCommute` hypotheses of
  `ChapterBrstReducedTransferUnbounded` for the closed pair.

## Boundary

The commutation above is **on the core**, which lies in both domains.  It is not
stated for all of `dom H̄`, and cannot be with the tools here: invariance of
`dom Ā` under `H̄` needs a regularity/graph-norm input, exactly the missing
input recorded for the reverse inclusion `dom A† ⊆ dom A` in
`ChapterYangMillsGaussSkewAdjoint`.  Neither the unitary group `e^{−it𝒢_d}` nor
skew-adjointness of `Ā` is claimed; the ghost sector is untouched.
-/

open MvPolynomial

namespace BookProof.Qym.GaussHamiltonianClosure

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.YangMillsFriedrichs
open BookProof.Qym.GaussSkew BookProof.Qym.GaussClosure BookProof.EsaClosure
open BookProof.FarisLavine BookProof.YangMillsNonAbelianEsa

noncomputable section

/-- The Gauss core of the one-particle field space, the domain of both the
analytic Hamiltonian and the charge. -/
abbrev PolyCore : Submodule ℂ (L2d 99) := polyGaussCore (d := 99)

/-- The Gauss constraint as an endomorphism of the core (the transported
`ymGaussPoly`). -/
def gaussEndo (G : GaugeAlgebra 8) (d : Fin 8) : Module.End ℂ PolyCore :=
  (coreRepPoly 99).op (ymGaussPoly G d)

/-- The transported polynomial Hamiltonian as an endomorphism of the core. -/
def hamEndo (G : GaugeAlgebra 8) : Module.End ℂ PolyCore :=
  (coreRepPoly 99).op (ymHamPoly G)

/-! ## The analytic Hamiltonian on the core -/

/-- **The bridge**: on the Gauss core the transported polynomial Hamiltonian is
the analytic `ymHamiltonian`.  This is the rewrite the skew chapter leaves open;
it is what lets the core commutation below be stated for the operator
`ym_h_esa` makes essentially self-adjoint. -/
theorem coreOp_ymHamPoly_eq_ymHamiltonian (G : GaugeAlgebra 8) (x : PolyCore) :
    ymHamiltonian (coreRepPoly 99) G.f x = ((hamEndo G x : PolyCore) : L2d 99) := by
  simp only [hamEndo, ymHamiltonian, weylOp, weylOpDom, ymHamPoly,
    piOps, magOps, coreRep_op_smul, coreRep_op_add, coreRep_op_sum,
    ← coreRep_op_mul, ← Module.End.mul_eq_comp, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    Submodule.subtype_apply]
  simp

/-- **`H` commutes with `𝒢_d` on the Gauss core, for the analytic Hamiltonian**:
`H (𝒢_d x) = 𝒢_d (H x)`, both read through their core endomorphisms.  This is
`coreRep_ham_comm_gauss_apply` transported across
`coreOp_ymHamPoly_eq_ymHamiltonian`. -/
theorem ymHamiltonian_comm_gauss_core (G : GaugeAlgebra 8) (d : Fin 8) (x : PolyCore) :
    ymHamiltonian (coreRepPoly 99) G.f (gaussEndo G d x)
      = ((gaussEndo G d (hamEndo G x) : PolyCore) : L2d 99) := by
  rw [coreOp_ymHamPoly_eq_ymHamiltonian]
  simpa [hamEndo, gaussEndo] using
    coreRep_ham_comm_gauss_apply G d (coreRepPoly 99) x

/-! ## The closure of the Hamiltonian -/

/-- **The closure of the Yang–Mills Hamiltonian**, built from the graph closure
of `ymHamiltonian` on the Gauss core. -/
def hamClosure (G : GaugeAlgebra 8) :
    clDom (ymHamiltonian (coreRepPoly 99) G.f) →ₗ[ℂ] L2d 99 :=
  clExt (ymHamiltonian (coreRepPoly 99) G.f) (polyGaussCore_dense (d := 99))
    (ymHamiltonian_symmetricOn (coreRepPoly 99) G.f)

/-- On the core the closed Hamiltonian agrees with `ymHamiltonian`. -/
theorem hamClosure_apply_core (G : GaugeAlgebra 8) (x : PolyCore) :
    hamClosure G ⟨((x : PolyCore) : L2d 99), coe_mem_clDom _ x⟩
      = ymHamiltonian (coreRepPoly 99) G.f x :=
  clExt_extends _ _ _ x

/-- The closure of `H` is symmetric on its domain. -/
theorem hamClosure_symmetricOn (G : GaugeAlgebra 8) :
    SymmetricOn (clDom (ymHamiltonian (coreRepPoly 99) G.f)) (hamClosure G) :=
  clExt_symmetricOn _ _ _

/-- **The closure of `H` is a self-adjoint extension of `H` on the core.**  The
values clause is `clExt_extends`, symmetry is `clExt_symmetricOn`, and the
self-adjointness criterion is `ym_h_esa` fed to `clExt_selfAdjointCriterion`. -/
theorem hamClosure_isSelfAdjointExtension (G : GaugeAlgebra 8) :
    IsSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) G.f) (hamClosure G) :=
  ⟨fun v => ⟨coe_mem_clDom _ v, clExt_extends _ _ _ v⟩,
    clExt_symmetricOn _ _ _,
    clExt_selfAdjointCriterion _ _ _ (ym_h_esa G.f)⟩

/-- **Uniqueness**: every self-adjoint extension of the analytic Hamiltonian on
the core has the domain and the values of `hamClosure`.  So the closed operator
is determined by the core, not chosen. -/
theorem hamClosure_unique (G : GaugeAlgebra 8) {Dom : Submodule ℂ (L2d 99)}
    {A : Dom →ₗ[ℂ] L2d 99} (hA : IsSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) G.f) A) :
    Dom = clDom (ymHamiltonian (coreRepPoly 99) G.f) ∧
      ∀ (x : L2d 99) (h : x ∈ Dom)
        (h' : x ∈ clDom (ymHamiltonian (coreRepPoly 99) G.f)),
        A ⟨x, h⟩ = hamClosure G ⟨x, h'⟩ :=
  isSelfAdjointExtension_unique_of_esa (ym_h_esa G.f) hA
    (hamClosure_isSelfAdjointExtension G)

/-! ## The two closed operators commute on the core -/

set_option maxHeartbeats 800000 in
-- the `clExt`/`clDom` instances need more than the default budget
/-- **The closed Hamiltonian and the closed charge commute on the shared Gauss
core**: `Ā (H̄ x) = H̄ (Ā x)` for `x` in the core, with `Ā` the closure of `𝒢_d`
and `H̄` the closure of `H`.  Both closures act on the core as the operators
themselves (`gaussPMap_closure_apply_core`, `hamClosure_apply_core`), so the
identity is the core commutation `ymHamiltonian_comm_gauss_core`. -/
theorem hamClosure_comm_gaussClosure_core (G : GaugeAlgebra 8) (d : Fin 8) (x : PolyCore) :
    (gaussPMap G d (coreRepPoly 99)).closure
        (Submodule.inclusion (LinearPMap.le_closure (gaussPMap G d (coreRepPoly 99))).1
          ⟨((hamEndo G x : PolyCore) : L2d 99), (hamEndo G x).2⟩)
      = hamClosure G
          ⟨((gaussEndo G d x : PolyCore) : L2d 99),
            coe_mem_clDom (ymHamiltonian (coreRepPoly 99) G.f) (gaussEndo G d x)⟩ := by
  rw [gaussPMap_closure_apply_core, hamClosure, clExt_extends]
  exact (ymHamiltonian_comm_gauss_core G d x).symm

end

end BookProof.Qym.GaussHamiltonianClosure
