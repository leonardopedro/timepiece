import BookProof.Phi4.ChapterScalarMehler
import BookProof.ChapterBrstUnboundedLeakage
import BookProof.ChapterFiniteSectionSingleTime
import BookProof.Toolbox.ChapterDegreeEnumeration
import BookProof.ChapterQuadraticFockEsa

/-!
# Shifted solves of finite scalar Mehler Hamiltonians

A degree-ordered Hermite window eventually contains each polynomial seed. On that
seed the compressed Hamiltonian then acts as the projection of the full column.
The common-core criterion turns this observation into convergence of the solves.
-/
namespace BookProof.Phi4.Model

open Filter Topology HermiteProductCore HermiteGalerkin DegreeEnumeration QuadFockEsa
open EsaClosure BrstUnboundedLeakage ChapterStoneResolvent ChapterSirkTrotterKato
open FiniteSectionSingleTime QgTruncationResolvent SirkSingleTime

noncomputable section

variable {d k r : ℕ} (M : Model d k r) (hd : 0 < d)

/-- Finite occupation window ordered by total Mehler degree. -/
def window (n : ℕ) := galerkinSpan (hermBasisN (degreeEnum hd)) n

instance (n : ℕ) : FiniteDimensional ℂ (window hd n) :=
  galerkinSpan_finiteDimensional _ _

variable {T : UnboundedSelfAdjoint (L2d d)} (ext : IsSelfAdjointExtension M.innerHam T.op)

include ext in
theorem window_le_domain (n : ℕ) : window hd n ≤ T.domain := by
  intro x hx
  have hm := galerkinSpan_le_finiteModeDomain _ _ hx
  rw [finiteModeDomain_hermBasisN] at hm
  exact (ext.1 ⟨x, hm⟩).choose

/-- The bounded self-adjoint P h P, extended by zero off its window. -/
def windowHam (n : ℕ) :=
  ofBounded (truncGen T (window hd n) (M.window_le_domain hd ext n))
    (truncGen_isSelfAdjoint ..)

/-- Shifted finite Hamiltonians converge at every nonzero imaginary shift.
Their unitary groups converge on each vector uniformly on compact time intervals. -/
theorem window_solve_convergence :
    (∀ (l : ℝ), l ≠ 0 → ∀ x : L2d d, Tendsto (fun n => (M.windowHam hd ext n).resCLM l x)
      atTop (𝓝 (T.resCLM l x))) ∧
    ∀ (x : L2d d) (t : ℝ), 0 ≤ t →
      TendstoUniformlyOn (fun n s => (M.windowHam hd ext n).stoneU s x)
        (fun s => T.stoneU s x) atTop (Set.Icc (-t) t) := by
  let b := hermBasisN (degreeEnum hd)
  let A := fun n => truncGen T (window hd n) (M.window_le_domain hd ext n)
  have hS n := isSelfAdjointExtension_ofBounded (A n) (truncGen_isSelfAdjoint ..) polyGaussCore
  have hconv (x : polyGaussCore (d := d)) :
      Tendsto (fun n => A n (x : L2d d)) atTop (𝓝 (M.innerHam x)) := by
    have hx : (x : L2d d) ∈ finiteModeDomain b := by
      simpa only [b, finiteModeDomain_hermBasisN] using x.property
    obtain ⟨N, hN⟩ := exists_mem_galerkinSpan b hx
    apply (galerkinProj_tendsto b (M.innerHam x)).congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hm : (x : L2d d) ∈ window hd n := galerkinSpan_mono b hn hN
    change _ = projOp (window hd n) (opProj T _ _ (x : L2d d))
    rw [opProj_apply_of_mem _ _ _ hm, (ext.1 x).choose_spec]
    rfl
  have hstrong : StrongResolventConvergence T (M.windowHam hd ext) :=
    strongResolventConvergence_of_core M.inner_esa ext hS hconv
  exact ⟨fun l hl => strongResAt_of_ne_zero one_ne_zero hl hstrong,
    fun v t ht => trotterKato_tendstoUniformlyOn _ _ hstrong v ht⟩

end
end BookProof.Phi4.Model
