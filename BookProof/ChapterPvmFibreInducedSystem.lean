import Mathlib
import BookProof.ChapterPvmInducedSystem
import BookProof.ChapterL2FibreSum

/-!
# The induced system on `L²(X, μ; K)` with a multiplicity (fibre) Hilbert space

`BookProof.ChapterPvmInducedSystem` writes an arbitrary projection-valued measure as the
`ℓ²`-sum of the multiplication systems of the cyclic pieces, indexed by a multiplicity set
`S`.  `BookProof.ChapterL2FibreSum` identifies, for a countable index `ι`, the `ℓ²`-sum of
copies of `L²(X, μ)` with the vector-valued space `L²(X, μ; ℓ²(ι))` of Mackey's *induced*
system.  Putting the two together gives the induced system in the form of
`BookProof.ChapterMackeyQuasiInvariant`: a **single** unitary onto `L²(X, μ; K)` with the
fibre (multiplicity) Hilbert space `K = ℓ²(ι)`, carrying `P(E)` to multiplication by `1_E`.

## Results

* `lpCongr` — the identification of the `L²` spaces of two equal measures, and
  `lpCongr_symm_proj`, its compatibility with multiplication by indicators.
* **`induced_system_of_isHilbertSum`** — if `H` is the Hilbert sum of countably many copies
  of `L²(X, μ)` along isometries carrying multiplication by `1_E` to `P(E)`, then there is a
  unitary `W : H ≃ L²(X, μ; ℓ²(ι))` with `W (P(E) v) = 1_E · W v`: the system *is* the
  induced one on the fibre `ℓ²(ι)`.
* **`pvm_induced_system_homogeneous`** — the concrete form: a projection-valued measure with
  a countable total orthogonal cyclic family whose fibre measures are all the *same* measure
  `μ` (homogeneous multiplicity) is unitarily the multiplication system on `L²(X, μ; ℓ²(S))`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmFibreInducedSystem

open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The `L²` spaces of two equal measures -/

/-- Equal measures have the same `L²` space. -/
noncomputable def lpCongr {μ ν : Measure X} (h : μ = ν) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν := by
  subst h
  exact LinearIsometryEquiv.refl ℂ _

theorem lpCongr_symm_proj {μ ν : Measure X} (h : μ = ν) {E : Set X} (hE : MeasurableSet E)
    (f : Lp ℂ 2 ν) :
    (lpCongr h).symm (proj ν hE f) = proj μ hE ((lpCongr h).symm f) := by
  subst h
  rfl

/-! ## The abstract form -/

/-- **A projection-valued measure whose space is the Hilbert sum of countably many copies of
`L²(X, μ)`, compatibly with multiplication by indicators, is the induced (multiplication)
system on `L²(X, μ; ℓ²(ι))`.** -/
theorem induced_system_of_isHilbertSum {ι : Type*} [Countable ι]
    (P : Pvm X H) (μ : Measure X) (V : ∀ _ : ι, Lp ℂ 2 μ →ₗᵢ[ℂ] H)
    (hsum : IsHilbertSum ℂ (fun _ : ι => Lp ℂ 2 μ) V)
    (hint : ∀ (i : ι) (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 μ),
      V i (proj μ hE f) = P.p E (V i f)) :
    ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre ι) 2 μ,
      ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v) := by
  classical
  refine ⟨hsum.linearIsometryEquiv.trans (fibreEquiv (ι := ι) μ).symm, ?_⟩
  intro E hE v
  set U := hsum.linearIsometryEquiv with hU
  set F := fibreEquiv (ι := ι) μ with hF
  -- both sides have the same image under the unitary `F`
  have hgoal : F (F.symm (U (P.p E v))) = F (proj μ hE (F.symm (U v))) := by
    rw [LinearIsometryEquiv.apply_symm_apply]
    refine lp.ext ?_
    funext i
    have hleft : U (P.p E v) i = proj μ hE (U v i) :=
      linearIsometryEquiv_intertwine hsum (P.p E) (fun _ : ι => projCLM μ hE)
        (fun _ u => ChapterL2FibreSum.norm_proj_le μ hE u) (fun i u => hint i E hE u) v i
    have hright : F (proj μ hE (F.symm (U v))) i = proj μ hE (F (F.symm (U v)) i) :=
      fibreEquiv_proj μ hE (F.symm (U v)) i
    rw [hleft, hright, LinearIsometryEquiv.apply_symm_apply]
  have := congrArg F.symm hgoal
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply] at this
  exact this

/-! ## The homogeneous case of the cyclic decomposition -/

section Homogeneous

variable {P : Pvm X H} {S : Set H} {μ : Measure X}

/-- The model of the piece of `ψ`, read on the common measure `μ`. -/
noncomputable def homEmb (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] H :=
  (swIsom P (ψ : H)).comp (lpCongr (hmu ψ)).symm.toLinearIsometry

theorem homEmb_apply (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) (f : Lp ℂ 2 μ) :
    homEmb hmu ψ f = swIsom P (ψ : H) ((lpCongr (hmu ψ)).symm f) := rfl

theorem homEmb_proj (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) {E : Set X}
    (hE : MeasurableSet E) (f : Lp ℂ 2 μ) :
    homEmb hmu ψ (proj μ hE f) = P.p E (homEmb hmu ψ f) := by
  rw [homEmb_apply, homEmb_apply, lpCongr_symm_proj (hmu ψ) hE f]
  exact swCLM_proj P (ψ : H) hE _

theorem isHilbertSum_homEmb (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) :
    IsHilbertSum ℂ (fun _ : S => Lp ℂ 2 μ) (homEmb hmu) := by
  refine IsHilbertSum.mk ?_ ?_
  · intro x y hxy u v
    exact inner_swIsom_eq_zero
      (hS.orth (x : H) x.2 (y : H) y.2 (Subtype.coe_injective.ne hxy)) _ _
  · have hsub : Submodule.span ℂ (familyOrbit P S)
        ≤ ⨆ ψ : S, LinearMap.range (homEmb hmu ψ).toLinearMap := by
      rw [Submodule.span_le]
      rintro v hv
      obtain ⟨ψ, hψ, hv⟩ := Set.mem_iUnion₂.mp hv
      obtain ⟨E, hE, rfl⟩ := hv
      refine Submodule.mem_iSup_of_mem ⟨ψ, hψ⟩ ?_
      refine ⟨lpCongr (hmu ⟨ψ, hψ⟩)
        (indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ)), ?_⟩
      change homEmb hmu ⟨ψ, hψ⟩ _ = _
      rw [homEmb_apply, LinearIsometryEquiv.symm_apply_apply]
      exact swCLM_indicator P ψ hE
    intro v _
    have hv : v ∈ closure ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H) :=
      hdense v
    have hmono := closure_mono (fun w hw => hsub hw) hv
    rwa [← Submodule.topologicalClosure_coe] at hmono

/-- **The induced system with a multiplicity (fibre) Hilbert space.**  If a projection-valued
measure has a countable total orthogonal cyclic family whose fibre measures are all the same
measure `μ` — the homogeneous multiplicity case — then it *is* the induced system of
`BookProof.ChapterMackeyQuasiInvariant` on `L²(X, μ; K)` with fibre `K = ℓ²(S)`: there is a
unitary `W : H ≃ L²(X, μ; ℓ²(S))` carrying `P(E)` to multiplication by the indicator of
`E`. -/
theorem pvm_induced_system_homogeneous [Countable S] (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) :
    ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre S) 2 μ,
      ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v) := by
  classical
  exact induced_system_of_isHilbertSum P μ (homEmb hmu) (isHilbertSum_homEmb hS hdense hmu)
    (fun ψ E hE f => homEmb_proj hmu ψ hE f)

end Homogeneous

end BookProof.ChapterPvmFibreInducedSystem
