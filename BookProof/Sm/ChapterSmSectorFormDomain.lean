/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmFormDomainComparison
import BookProof.Sm.ChapterSmPhysicalReductionEsa

/-!
# P4 in one parity sector of the coupled space

`SM_ESA_COMPLETION_PLAN` P4 asks for the self-bound of the quartic potential,
`PotSelfBound` / `FormDomainComparison`.  §44 reduced the *closure* of the matter
normal form to its two parity sectors.  The natural next question — the one this
module answers — is whether the same reduction can help P4: is the analytic
input, restricted to one parity sector, weaker than the input on the whole
coupled space?

It is not, and the reason is structural rather than analytic.  The model parity
`coupledParity` is diagonal on the outer occupation index,
`(coupledParity f).ofLp A = fockSign A • f.ofLp A` (`fockSign A = (-1)^{|A|}`),
and it does not touch the inner `163`-coordinate factor at all.  Consequently
**every elementary tensor is a parity eigenvector**: for a single outer
occupation `A` and any inner vector `v`,

`coupledParity (deltaFun A v) = fockSign A • deltaFun A v`,

so the inner factor sits inside each sector whole.  The input of P4 is exactly a
statement about that inner factor: it is an inequality for the class of all
Gauss-polynomial test functions, and that whole class appears, unchanged and with
the same norm (`deltaFun_norm`), inside each sector.  The sector bound at
`deltaFun A v` therefore *is* the scalar bound at `v`.

Hence P4 does not decompose: the parity split localises the closure, not the
elliptic estimate, and a proof of the sector self-bound would already be a proof
of the whole one.  Both sectors inherit the identical open problem, and the sharp
constant is the same in both.  `PotSelfBound` remains a hypothesis; nothing here
proves it.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmSectorFormDomain

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore
open BookProof.SmFullMatter BookProof.SmFullCoupledCore
open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmFormDomainComparison
open BookProof.SmKineticElliptic BookProof.SmFarisLavine
open BookProof.SmPhysicalReduction BookProof.DegSchrodinger
open BookProof.SmComparisonEsa

noncomputable section

/-! ## 1. Elementary tensors of the coupled space -/

/-- **The elementary tensor at a single outer occupation**: the outer index `A` carries the inner
vector `v` and every other index carries zero.  This is the class of vectors on which the parity is
decided by `A` alone. -/
def deltaFun (A : Finset (Fin 96)) (v : L2d 163) : SmCoupledSpace :=
  WithLp.toLp 2 (fun B => if B = A then v else 0)

/-- The value of an elementary tensor at its own index. -/
@[simp] theorem deltaFun_ofLp_self (A : Finset (Fin 96)) (v : L2d 163) :
    (deltaFun A v).ofLp A = v := by
  rw [deltaFun, WithLp.ofLp_toLp, if_pos rfl]

/-- The value of an elementary tensor at every other index. -/
theorem deltaFun_ofLp_ne {A B : Finset (Fin 96)} (h : B ≠ A) (v : L2d 163) :
    (deltaFun A v).ofLp B = 0 := by
  rw [deltaFun, WithLp.ofLp_toLp, if_neg h]

/-- **The norm of an elementary tensor is the inner norm**: the outer support is a single index, so
nothing is lost or added by embedding. -/
theorem deltaFun_norm (A : Finset (Fin 96)) (v : L2d 163) : ‖deltaFun A v‖ = ‖v‖ := by
  have hsq : ‖deltaFun A v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [coupledSpace_norm_sq,
      Finset.sum_eq_single A (fun B _ hB => by rw [deltaFun_ofLp_ne hB, norm_zero]; ring)
        (fun h => absurd (Finset.mem_univ A) h)]
    rw [deltaFun_ofLp_self]
  calc ‖deltaFun A v‖ = Real.sqrt (‖deltaFun A v‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖v‖ ^ 2) := by rw [hsq]
    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)

/-- **An elementary tensor at an inner core element lies in the common core**, since all its other
components are zero. -/
theorem deltaFun_mem_core {v : L2d 163} (hv : v ∈ polyGaussCore (d := 163)) (A : Finset (Fin 96)) :
    deltaFun A v ∈ SmCoupledCore := by
  intro B
  by_cases h : B = A
  · subst h
    rw [deltaFun_ofLp_self]
    exact hv
  · rw [deltaFun_ofLp_ne h]
    exact (polyGaussCore (d := 163)).zero_mem

/-- The inner component of an elementary tensor, as an element of the inner core. -/
theorem coreComp_deltaFun {v : L2d 163} (hv : v ∈ polyGaussCore (d := 163))
    (A : Finset (Fin 96)) :
    coreComp (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore) A
      = ⟨v, hv⟩ := by
  refine Subtype.ext ?_
  rw [coe_coreComp, deltaFun_ofLp_self]

/-- Every other inner component of an elementary tensor is zero. -/
theorem coreComp_deltaFun_ne {v : L2d 163} (hv : v ∈ polyGaussCore (d := 163))
    {A B : Finset (Fin 96)} (h : B ≠ A) :
    ((coreComp (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore) B :
        polyGaussCore (d := 163)) : L2d 163) = 0 := by
  rw [coe_coreComp, deltaFun_ofLp_ne h]

/-! ## 2. Every elementary tensor is a parity eigenvector -/

/-- **The parity of an elementary tensor is the sign of its outer occupation.**  The inner factor is
untouched, which is the whole point: `deltaFun A v` belongs to the even sector when `|A|` is even and
to the odd sector when `|A|` is odd, whatever `v` is. -/
theorem coupledParity_deltaFun (A : Finset (Fin 96)) (v : L2d 163) :
    coupledParity (deltaFun A v) = fockSign A • deltaFun A v := by
  refine WithLp.ofLp_injective 2 (funext fun B => ?_)
  rw [coupledParity_apply, PiLp.smul_apply]
  by_cases h : B = A
  · subst h
    rw [deltaFun_ofLp_self]
  · rw [deltaFun_ofLp_ne h]; simp

/-- The even sector contains an elementary tensor iff its outer occupation is even.  In particular the
even sector contains `deltaFun ∅ v` for every inner vector, so the whole inner test class is present
in that sector. -/
theorem deltaFun_mem_evenSpace_iff (A : Finset (Fin 96)) (v : L2d 163) (hv : v ≠ 0) :
    deltaFun A v ∈ evenSpace coupledParity ↔ fockSign A = 1 := by
  rw [mem_evenSpace_iff, coupledParity_deltaFun]
  have hne : deltaFun A v ≠ 0 := by
    intro h0
    apply hv
    have h' := congrArg (fun w => w.ofLp A) h0
    simpa [deltaFun_ofLp_self] using h'
  constructor
  · intro h
    have h' : fockSign A • deltaFun A v = (1 : ℂ) • deltaFun A v := by
      rw [one_smul]
      exact h
    exact (smul_left_inj hne).mp h'
  · intro h
    rw [h, one_smul]

/-! ## 3. The coupled tensor acts componentwise on an elementary tensor -/

/-- **A coupled elementary tensor `T ⊗ I` sends an elementary tensor to an elementary tensor**: the
outer support is unchanged and the inner factor becomes `T v`.  This is what makes the sector
inequality at `deltaFun A v` literally the scalar inequality at `v`. -/
theorem coupledOp_one_deltaFun (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {v : L2d 163}
    (hv : v ∈ polyGaussCore (d := 163)) (A : Finset (Fin 96)) :
    coupledOp T 1 (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore)
      = deltaFun A (T ⟨v, hv⟩) := by
  refine WithLp.ofLp_injective 2 (funext fun B => ?_)
  rw [coupledOp_one_apply]
  by_cases h : B = A
  · rw [h, coreComp_deltaFun hv A, deltaFun_ofLp_self]
  · rw [deltaFun_ofLp_ne h]
    -- every other component of the tensor is `T` applied to a zero component
    have hzero : coreComp (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore) B = 0 :=
      Subtype.ext (coreComp_deltaFun_ne hv h)
    rw [hzero, map_zero]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- The shifted comparison `(N ⊗ I) + 1` at an elementary tensor, in the same elementary form. -/
theorem coupledOp_one_add_deltaFun (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {v : L2d 163}
    (hv : v ∈ polyGaussCore (d := 163)) (A : Finset (Fin 96)) :
    coupledOp N 1 (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore)
        + (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore)
      = deltaFun A (N ⟨v, hv⟩ + v) := by
  refine WithLp.ofLp_injective 2 (funext fun B => ?_)
  rw [PiLp.add_apply]
  by_cases h : B = A
  · rw [h, coupledOp_one_apply, coreComp_deltaFun hv A, deltaFun_ofLp_self,
      deltaFun_ofLp_self]
  · rw [deltaFun_ofLp_ne h]
    have hzero : coreComp (⟨deltaFun A v, deltaFun_mem_core hv A⟩ : SmCoupledCore) B = 0 :=
      Subtype.ext (coreComp_deltaFun_ne hv h)
    rw [coupledOp_one_apply, hzero, map_zero, deltaFun_ofLp_ne h]; simp

/-! ## 4. The sector statement is not weaker than the scalar one -/

/-- The empty outer occupation is even. -/
theorem fockSign_empty : fockSign (∅ : Finset (Fin 96)) = 1 := by
  rw [fockSign, Finset.card_empty, pow_zero]

/-- A single outer occupation is odd. -/
theorem fockSign_singleton (i : Fin 96) : fockSign ({i} : Finset (Fin 96)) = (-1 : ℂ) := by
  rw [fockSign, Finset.card_singleton, pow_one]

/-- **A sector-wise relative bound is a bound for the scalar factor.**  Let `T` and `N` be the kinetic
and comparison operators of the inner `163`-coordinate problem, and suppose the coupled version
`T ⊗ I` is bounded by `N ⊗ I + 1` *only on the even parity sector*.  Evaluating at the elementary
tensor of the empty outer occupation — which is even, `fockSign ∅ = 1` — recovers the scalar
inequality for every inner core vector.

So restricting P4's input to one parity sector does not weaken it: the sector statement already
implies the whole scalar statement, which in turn is `FormDomainComparison` / `PotSelfBound`. -/
theorem scalarBound_of_evenSectorBound (T N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    {c : ℝ}
    (h : ∀ f : SmCoupledCore, coupledParity (f : SmCoupledSpace) = f →
      ‖coupledOp T 1 f‖ ≤ c * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖)
    (x : polyGaussCore (d := 163)) :
    ‖T x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  set f : SmCoupledCore := ⟨deltaFun ∅ (x : L2d 163), deltaFun_mem_core x.2 ∅⟩ with hf
  have hfpar : coupledParity (f : SmCoupledSpace) = f := by
    have hcoe : (f : SmCoupledSpace) = deltaFun ∅ (x : L2d 163) := rfl
    rw [hcoe, coupledParity_deltaFun, fockSign_empty, one_smul]
  have hb := h f hfpar
  have hcoe : (f : SmCoupledSpace) = deltaFun ∅ (x : L2d 163) := rfl
  rw [hcoe] at hb
  rw [hf, coupledOp_one_deltaFun T x.2 ∅, coupledOp_one_add_deltaFun N x.2 ∅,
    deltaFun_norm, deltaFun_norm] at hb
  exact hb

/-- **The same statement for the odd sector**, at the outer occupation `{0}`: the odd sector is just
as large as the even one, so a bound there is also a bound for the scalar factor. -/
theorem scalarBound_of_oddSectorBound (T N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    {c : ℝ}
    (h : ∀ f : SmCoupledCore, coupledParity (f : SmCoupledSpace) = (-1 : ℂ) • f →
      ‖coupledOp T 1 f‖ ≤ c * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖)
    (x : polyGaussCore (d := 163)) :
    ‖T x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  set f : SmCoupledCore := ⟨deltaFun ({0} : Finset (Fin 96)) (x : L2d 163),
    deltaFun_mem_core x.2 {0}⟩ with hf
  have hfpar : coupledParity (f : SmCoupledSpace) = (-1 : ℂ) • f := by
    have hcoe : (f : SmCoupledSpace) = deltaFun ({0} : Finset (Fin 96)) (x : L2d 163) := rfl
    rw [hcoe, coupledParity_deltaFun, fockSign_singleton]
  have hb := h f hfpar
  have hcoe : (f : SmCoupledSpace) = deltaFun ({0} : Finset (Fin 96)) (x : L2d 163) := rfl
  rw [hcoe] at hb
  rw [hf, coupledOp_one_deltaFun T x.2 {0}, coupledOp_one_add_deltaFun N x.2 {0},
    deltaFun_norm, deltaFun_norm] at hb
  exact hb

/-! ## 5. Transport of the named input into a sector -/

/-- **`FormDomainComparison` inside a parity sector is the same inequality.**  The named input of
§32, read on the elementary tensors of any single outer occupation, is literally the scalar
statement: the two sides are transported by `deltaFun`, and `deltaFun` is an isometry. -/
theorem sectorComparison_iff_formDomainComparison (P : SmParams) (c0 c : ℝ)
    (A : Finset (Fin 96)) :
    FormDomainComparison P c0 c
      ↔ ∀ p : MvPolynomial (Fin 163) ℂ,
          ‖deltaFun A (pgLp (kinPolyS smS p))‖
            ≤ c * ‖deltaFun A (pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p)‖ := by
  constructor
  · intro h p
    rw [deltaFun_norm, deltaFun_norm]
    exact h p
  · intro h p
    have := h p
    rwa [deltaFun_norm, deltaFun_norm] at this

/-- **The sector input carries no information about the sector.**  For every outer occupation `A`,
the sector statement at `A` is equivalent to the whole scalar statement of §32 — so a proof of the
`FormDomainComparison` restricted to any one sector is a proof of the full input, and no sector is
easier than another. -/
theorem sectorComparison_const_in_sector (P : SmParams) (c0 c : ℝ) (A A' : Finset (Fin 96)) :
    (∀ p : MvPolynomial (Fin 163) ℂ,
        ‖deltaFun A (pgLp (kinPolyS smS p))‖
          ≤ c * ‖deltaFun A (pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p)‖)
      ↔ (∀ p : MvPolynomial (Fin 163) ℂ,
        ‖deltaFun A' (pgLp (kinPolyS smS p))‖
          ≤ c * ‖deltaFun A' (pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p)‖) :=
  (sectorComparison_iff_formDomainComparison P c0 c A).symm.trans
    (sectorComparison_iff_formDomainComparison P c0 c A')

end

end BookProof.SmSectorFormDomain
