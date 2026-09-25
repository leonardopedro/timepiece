import Mathlib
import BookProof.ChapterNavierStokesFullLagrangianFock
import BookProof.ChapterNavierStokesFullEulerianFock
import BookProof.ChapterYangMillsNonAbelianEsa
import BookProof.ChapterEsaClosureCore

/-!
# ESA of the full (interacting) Lagrangian Navier–Stokes Hamiltonian on the finite-parcel core

`BookProof.ChapterNavierStokesFullLagrangianFock` defines the full Lagrangian Hamiltonian
`lagFullFockHam` on the nested Fock space `⊕ₙ L²(ℝ^{36n})`, with the finite-parcel core
`lagFockCore` (finitely many nonzero sectors, each a Gauss–polynomial). Its `n`-parcel sector
`lagSectorHam n = ½ Σ π² + ½ Σ form²` is interacting: the gauge-fixing forms couple
neighbouring parcels, and the Piola (`cof F · q`) and `det F − 1` forms have degree 2 and 3. So
it is not the second quantization of a one-body operator. That module proved only that
a positive self-adjoint (Friedrichs) extension exists.

Closing the gap needs no new analysis. Two existing theorems of the project do it:

* `YangMillsNonAbelianEsa.weylPoly_esa`: any operator `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j²` on the
  Gauss–polynomial core of `L²(ℝᵈ)` is essentially self-adjoint when the momenta sit in
  distinct coordinates and the `Φ_j` are real polynomials. The proof writes `2H + 1 = −Δ_S + W`
  with `W = Σ Φ_j² + 1 ≥ 1` and uses the project's Kato-type theorem for degenerate
  Schrödinger operators with polynomial potentials.
* `DirectSumEsa.dsOp_essentiallySelfAdjointOn`: fibrewise essential self-adjointness glues to
  the orthogonal direct sum on the algebraic direct-sum core.

Proved here:

* `lagIdx_injective`: the 24 momentum directions of each parcel are distinct coordinates;
* `lagSectorHam_eq_weylPoly`: the `n`-parcel sector is such a Weyl-type operator (`rfl`);
* **`lagSectorHam_esa`**: every `n`-parcel sector is essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝ^{36n})`;
* **`lagFullFockHam_esa`**: the full Lagrangian Hamiltonian is essentially self-adjoint on
  the finite-parcel core `lagFockCore`;
* `lagFullFockHam_selfAdjointExtension_unique`: because the Hamiltonian is essentially
  self-adjoint, every self-adjoint extension of it has the same domain and values as the
  lifted Friedrichs realization `lagOuterComparison` of the earlier module, which is
  therefore *the* self-adjoint realization.

The Eulerian companion `BookProof.ChapterNavierStokesFullEulerianFock` has exactly the same
structure (21 coordinates and 12 momenta per parcel), and section 2 closes it the same way:
`nsSectorHam_esa`, **`nsFullFockHam_esa`** and `nsFullFockHam_selfAdjointExtension_unique`.

These hold for all real couplings `λ, λ', μ, g`. The statement is about the auxiliary
sum-of-squares operator of the earlier module, not about the (non-semibounded) Koopman
generator.
-/

namespace BookProof.NsFullLagrangianEsa

open MvPolynomial
open BookProof.NsFullLagrangian BookProof.YangMillsNonAbelianEsa BookProof.YangMillsHermite
open BookProof.YangMillsFriedrichs BookProof.HermiteProductCore BookProof.DirectSumEsa
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.EsaClosure

noncomputable section

/-- The global coordinate carrying the `m`-th momentum of the `n`-parcel sector. -/
def lagIdx (n : ℕ) (m : Fin (n * 24)) : Fin (n * 36) :=
  ycoord (finProdFinEquiv.symm m).1 (momIdx (finProdFinEquiv.symm m).2)

/-- The constraint forms of the `n`-parcel sector, as polynomials. -/
def lagForms (lam lam' mu gg : ℝ) (n : ℕ) (m : Fin (n * 28)) : MvPolynomial (Fin (n * 36)) ℂ :=
  lagFormOf lam lam' mu gg (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2

theorem momIdx_injective : Function.Injective momIdx := by
  intro s t h
  have hv := congrArg Fin.val h
  have hs := s.isLt
  have ht := t.isLt
  apply Fin.ext
  simp only [momIdx, xiIdx, vIdx, fIdx, vgIdx] at hv
  split_ifs at hv <;> simp only at hv <;> omega

/-- The momentum coordinates of the `n`-parcel sector are pairwise distinct. -/
theorem lagIdx_injective (n : ℕ) : Function.Injective (lagIdx n) := by
  intro m m' h
  simp only [lagIdx, ycoord] at h
  have h2 := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at h2
  apply finProdFinEquiv.symm.injective
  exact Prod.ext h2.1 (momIdx_injective h2.2)

theorem realCoeff_lagForms (lam lam' mu gg : ℝ) (n : ℕ) (m : Fin (n * 28)) :
    RealCoeff (lagForms lam lam' mu gg n m) :=
  realCoeff_lagFormOf _ _ _ _ _ _

/-- The `n`-parcel Lagrangian Hamiltonian is the Weyl-type operator with momenta in the
coordinates `lagIdx n` and the constraint forms as fields. -/
theorem lagSectorHam_eq_weylPoly (lam lam' mu gg : ℝ) (n : ℕ) :
    lagSectorHam lam lam' mu gg n = weylPoly (lagIdx n) (lagForms lam lam' mu gg n) := rfl

/-- **Every `n`-parcel sector of the full Lagrangian Navier–Stokes Hamiltonian is essentially
self-adjoint** on the Gauss–polynomial core of `L²(ℝ^{36n})`, for all real couplings. -/
theorem lagSectorHam_esa (lam lam' mu gg : ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 36)) (lagSectorHam lam lam' mu gg n) := by
  rw [lagSectorHam_eq_weylPoly]
  exact weylPoly_esa (lagIdx_injective n) (realCoeff_lagForms lam lam' mu gg n)

/-- **The full (interacting) Lagrangian Navier–Stokes Hamiltonian is essentially self-adjoint
on the finite-parcel core** `lagFockCore ⊂ ⊕ₙ L²(ℝ^{36n})`, for all real couplings. -/
theorem lagFullFockHam_esa (lam lam' mu gg : ℝ) :
    EssentiallySelfAdjointOn lagFockCore (lagFullFockHam lam lam' mu gg) :=
  dsOp_essentiallySelfAdjointOn _ fun n => lagSectorHam_esa lam lam' mu gg n

/-- **The self-adjoint realization is unique.** Any self-adjoint extension of the full
Lagrangian Hamiltonian on the finite-parcel core has the same domain and the same values as
the lifted Friedrichs realization `lagOuterComparison`. -/
theorem lagFullFockHam_selfAdjointExtension_unique (lam lam' mu gg : ℝ)
    {Dom : Submodule ℂ lagFockSpace} {A : Dom →ₗ[ℂ] lagFockSpace}
    (hA : IsSelfAdjointExtension (lagFullFockHam lam lam' mu gg) A) :
    Dom = (lagOuterComparison lam lam' mu gg).dom ∧
      ∀ (x : lagFockSpace) (h : x ∈ Dom) (h' : x ∈ (lagOuterComparison lam lam' mu gg).dom),
        A ⟨x, h⟩ = (lagOuterComparison lam lam' mu gg).op ⟨x, h'⟩ := by
  have hF := lagFullOuterN_isPositiveSelfAdjointExtension lam lam' mu gg
  exact isSelfAdjointExtension_unique_of_esa (lagFullFockHam_esa lam lam' mu gg) hA
    ⟨hF.1, hF.2.1, hF.2.2.2⟩

/-! ## 2. The Eulerian companion -/

/-- The global coordinate carrying the `m`-th momentum of the Eulerian `n`-parcel sector. -/
def eulIdx (n : ℕ) (m : Fin (n * 12)) : Fin (n * 21) :=
  NsFullEuler.ycoord (finProdFinEquiv.symm m).1 (NsFullEuler.momIdx (finProdFinEquiv.symm m).2)

/-- The constraint forms of the Eulerian `n`-parcel sector, as polynomials. -/
def eulForms (nu lam mu gg : ℝ) (n : ℕ) (m : Fin (n * 19)) : MvPolynomial (Fin (n * 21)) ℂ :=
  NsFullEuler.nsFormOf nu lam mu gg (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2

theorem eulMomIdx_injective : Function.Injective NsFullEuler.momIdx := by
  intro s t h
  have hv := congrArg Fin.val h
  have hs := s.isLt
  have ht := t.isLt
  apply Fin.ext
  simp only [NsFullEuler.momIdx, NsFullEuler.uIdx, NsFullEuler.dIdx] at hv
  split_ifs at hv <;> simp only at hv <;> omega

/-- The momentum coordinates of the Eulerian `n`-parcel sector are pairwise distinct. -/
theorem eulIdx_injective (n : ℕ) : Function.Injective (eulIdx n) := by
  intro m m' h
  simp only [eulIdx, NsFullEuler.ycoord] at h
  have h2 := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at h2
  apply finProdFinEquiv.symm.injective
  exact Prod.ext h2.1 (eulMomIdx_injective h2.2)

/-- The Eulerian `n`-parcel Hamiltonian is a Weyl-type operator. -/
theorem nsSectorHam_eq_weylPoly (nu lam mu gg : ℝ) (n : ℕ) :
    NsFullEuler.nsSectorHam nu lam mu gg n = weylPoly (eulIdx n) (eulForms nu lam mu gg n) :=
  rfl

/-- **Every `n`-parcel sector of the full Eulerian Navier–Stokes Hamiltonian is essentially
self-adjoint** on the Gauss–polynomial core of `L²(ℝ^{21n})`, for all real couplings. -/
theorem nsSectorHam_esa (nu lam mu gg : ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 21))
      (NsFullEuler.nsSectorHam nu lam mu gg n) := by
  rw [nsSectorHam_eq_weylPoly]
  exact weylPoly_esa (eulIdx_injective n) fun m => NsFullEuler.realCoeff_nsFormOf _ _ _ _ _ _

/-- **The full (interacting) Eulerian Navier–Stokes Hamiltonian is essentially self-adjoint
on the finite-parcel core** `nsFockCore ⊂ ⊕ₙ L²(ℝ^{21n})`, for all real couplings. -/
theorem nsFullFockHam_esa (nu lam mu gg : ℝ) :
    EssentiallySelfAdjointOn NsFullEuler.nsFockCore (NsFullEuler.nsFullFockHam nu lam mu gg) :=
  dsOp_essentiallySelfAdjointOn _ fun n => nsSectorHam_esa nu lam mu gg n

/-- **The Eulerian self-adjoint realization is unique**: it is the lifted Friedrichs
realization `nsOuterComparison`. -/
theorem nsFullFockHam_selfAdjointExtension_unique (nu lam mu gg : ℝ)
    {Dom : Submodule ℂ NsFullEuler.nsFockSpace} {A : Dom →ₗ[ℂ] NsFullEuler.nsFockSpace}
    (hA : IsSelfAdjointExtension (NsFullEuler.nsFullFockHam nu lam mu gg) A) :
    Dom = (NsFullEuler.nsOuterComparison nu lam mu gg).dom ∧
      ∀ (x : NsFullEuler.nsFockSpace) (h : x ∈ Dom)
        (h' : x ∈ (NsFullEuler.nsOuterComparison nu lam mu gg).dom),
        A ⟨x, h⟩ = (NsFullEuler.nsOuterComparison nu lam mu gg).op ⟨x, h'⟩ := by
  have hF := NsFullEuler.nsFullOuterN_isPositiveSelfAdjointExtension nu lam mu gg
  exact isSelfAdjointExtension_unique_of_esa (nsFullFockHam_esa nu lam mu gg) hA
    ⟨hF.1, hF.2.1, hF.2.2.2⟩

end

end BookProof.NsFullLagrangianEsa
