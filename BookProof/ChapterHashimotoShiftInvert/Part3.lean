import Mathlib
import BookProof.ChapterHermiteGalerkinFriedrichs
import BookProof.ChapterComplexShiftCore
import BookProof.ChapterHashimotoShiftInvert.Part2

/-!
# The shift-invert (Hashimoto) trick: the Galerkin/Friedrichs selection theorem
for **unbounded** Hamiltonians

`BookProof.ChapterHermiteGalerkinFriedrichs` proves that a Galerkin/Rayleigh–Ritz
truncation in a complete (Hermite) basis converges — strongly, and in the strong
resolvent sense — to the positive self-adjoint (Friedrichs) extension of the
matrix it is fed, under a standing hypothesis that the operator is **bounded**
on its domain.

That hypothesis is not a restriction on the *physics* the Hashimoto algorithm
does, because the algorithm never applies `H` itself: it applies the
*shift-inverted* operator `R = (H + γ)⁻¹`.  And `R` is bounded — indeed
`‖R‖ ≤ 1/γ` — for **every** positive symmetric `H`, however unbounded, purely
because of positivity.  This module makes that precise and closes the gap:

* `norm_shiftMap_ge` — the shift bound `‖(A + γ)x‖ ≥ γ‖x‖` for a positive
  symmetric operator.  This is why the *effective* Hamiltonian is bounded even
  when `H` is not.
* `closed_of_selfAdjointCriterion`, `shiftRange_isClosed`, `shiftRange_dense`,
  `shiftMap_surjective` — for a positive self-adjoint operator (in the sense of
  `IsPositiveSelfAdjointExtension`) the shifted operator `A + γ` is a bijection
  of its domain onto the whole space.  No boundedness is used.
* `IsShiftInvert`, `exists_isShiftInvert` — hence the bounded inverse
  `R = (A + γ)⁻¹` exists as a genuine element of `F →L[ℂ] F`, with
  `‖R‖ ≤ γ⁻¹` (`IsShiftInvert.opNorm_le`), self-adjoint
  (`IsShiftInvert.isSelfAdjoint`), positive and injective.
* `IsShiftInvert.dom_eq_range`, `IsShiftInvert.apply_eq`,
  `shiftInvert_determines` — `R` remembers everything: its range is the domain
  of `A`, and `A = R⁻¹ − γ` there.  Two positive self-adjoint operators with the
  same shift-invert are the same operator.
* `galerkinCompression_shiftInvert_tendsto`,
  `galerkinResolvent_shiftInvert_tendsto` — the bounded Galerkin theory of
  `BookProof.ChapterHermiteGalerkinFriedrichs` applies verbatim to `R`.
* `hashimoto_shiftInvert_selects_friedrichs` — the headline, **with no
  boundedness hypothesis anywhere**: for a symmetric positive matrix in a
  complete basis and any positive self-adjoint extension `A` of it (the
  Friedrichs extension being one), the shift-inverted operator `R = (A+γ)⁻¹` is
  bounded, the Galerkin truncations of `R` converge strongly to `R` (this is
  precisely strong resolvent convergence of the truncations to `A`), and `R`
  determines `A` uniquely — so the algorithm selects that extension and no
  other.
* `ell2UnboundedExample` and `unbounded_shiftInvert_example` — the hypotheses
  are satisfied by a genuinely **unbounded** operator: the diagonal operator
  `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, whose shift-invert at `γ = 1` is the bounded
  diagonal operator `eₙ ↦ eₙ/(n+1)`.  The boundedness hypothesis of
  `hermiteGalerkin_selects_friedrichs` fails for this `A`
  (`ell2UnboundedExample_unbounded`), while the theorems here apply.

This module treats one **real positive** shift `γ`, where invertibility of
`A + γ` comes from positivity of `A`.  The shifts the Shift-invert Rational
Krylov method actually uses are complex with non-zero imaginary part (which
makes `γ I − A` invertible for every self-adjoint `A`, positive or not), and
they change from step to step; that generalisation, in the same namespace, is
`BookProof.ChapterHashimotoComplexShifts`, whose
`isShiftInvertC_neg_of_isShiftInvert` relates the two notions.
-/

namespace BookProof.HashimotoShiftInvert

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

/-! ## Part 6 — a genuinely unbounded example -/

section Example

open scoped InnerProductSpace ENNReal

/-! ### The diagonal operator on `ℓ²(ℕ, ℂ)` -/

theorem memlp_diagFun {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    Memℓp (fun n => (c n : ℂ) * x n) 2 := by
  have hx : Summable fun n => ‖(x : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp x).summable (by norm_num)
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx)
  have h1 : ‖(c n : ℂ) * (x : ℕ → ℂ) n‖ = |c n| * ‖(x : ℕ → ℂ) n‖ := by
    simp [Complex.norm_real]
  have hle : |c n| * ‖(x : ℕ → ℂ) n‖ ≤ ‖(x : ℕ → ℂ) n‖ := by
    nlinarith [abs_nonneg (c n), hc n, norm_nonneg ((x : ℕ → ℂ) n)]
  rw [h1, show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  exact Real.rpow_le_rpow (by positivity) hle (by norm_num)

/-- The diagonal (multiplication) operator on `ℓ²(ℕ, ℂ)` with real coefficients
bounded by one, as a linear map. -/
noncomputable def diagLin {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun x := ⟨fun n => (c n : ℂ) * x n, memlp_diagFun hc x⟩
  map_add' x y := by
    apply lp.ext; funext n; simp [mul_add]
  map_smul' a x := by
    apply lp.ext; funext n; simp; ring

@[simp] theorem diagLin_apply {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagLin hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (c n : ℂ) * x n := rfl

theorem diagLin_norm_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    ‖diagLin hc x‖ ≤ ‖x‖ := by
  refine lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x) ?_
  rw [lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((memlp_diagFun hc x).summable (by norm_num)) ((lp.memℓp x).summable (by norm_num))
  have h1 : ‖((diagLin hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n‖ = |c n| * ‖(x : ℕ → ℂ) n‖ := by
    rw [diagLin_apply]; simp [Complex.norm_real]
  have hle : |c n| * ‖(x : ℕ → ℂ) n‖ ≤ ‖(x : ℕ → ℂ) n‖ := by
    nlinarith [abs_nonneg (c n), hc n, norm_nonneg ((x : ℕ → ℂ) n)]
  rw [h1, show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  exact Real.rpow_le_rpow (by positivity) hle (by norm_num)

/-- The diagonal operator as a bounded operator, of norm at most one. -/
noncomputable def diagCLM {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  (diagLin hc).mkContinuous 1 (by simpa using diagLin_norm_le hc)

@[simp] theorem diagCLM_apply {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagCLM hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (c n : ℂ) * x n := rfl

theorem diagCLM_norm_apply_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    ‖diagCLM hc x‖ ≤ ‖x‖ := diagLin_norm_le hc x

theorem diagCLM_symmetric {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x y : ℓ²(ℕ, ℂ)) :
    (inner ℂ (diagCLM hc x) y : ℂ) = inner ℂ x (diagCLM hc y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  rw [diagCLM_apply, diagCLM_apply]
  simp [RCLike.inner_apply, map_mul]
  ring

theorem diagCLM_isSelfAdjoint {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) :
    IsSelfAdjoint (diagCLM hc) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (diagCLM_symmetric hc)

theorem diagCLM_injective {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (hne : ∀ n, c n ≠ 0) :
    Function.Injective (diagCLM hc) := by
  intro x y hxy
  apply lp.ext
  funext n
  have h := congrArg (fun z : ℓ²(ℕ, ℂ) => (z : ℕ → ℂ) n) hxy
  simp only [diagCLM_apply] at h
  have hc0 : (c n : ℂ) ≠ 0 := by exact_mod_cast hne n
  exact mul_left_cancel₀ hc0 h

/-! ### The unbounded example: `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)` -/

/-- The coefficients `1/(n+1)` of the shift-inverted operator. -/
noncomputable def invCoeff (n : ℕ) : ℝ := 1 / (n + 1)

theorem invCoeff_pos (n : ℕ) : 0 < invCoeff n := by
  have : (0:ℝ) < (n : ℝ) + 1 := by positivity
  simpa [invCoeff] using this

theorem invCoeff_le_one (n : ℕ) : invCoeff n ≤ 1 := by
  have h1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [invCoeff, div_le_one (by positivity)]
  exact h1

theorem invCoeff_abs_le_one (n : ℕ) : |invCoeff n| ≤ 1 := by
  rw [abs_of_pos (invCoeff_pos n)]
  exact invCoeff_le_one n

theorem invCoeff_ne_zero (n : ℕ) : invCoeff n ≠ 0 := ne_of_gt (invCoeff_pos n)

/-- **The effective (shift-inverted) Hamiltonian of the example**: the bounded
diagonal operator `eₙ ↦ eₙ/(n+1)`. -/
noncomputable def ell2ShiftInvert : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) := diagCLM invCoeff_abs_le_one

theorem ell2ShiftInvert_injective : Function.Injective ell2ShiftInvert :=
  diagCLM_injective invCoeff_abs_le_one invCoeff_ne_zero

theorem ell2ShiftInvert_isSelfAdjoint : IsSelfAdjoint ell2ShiftInvert :=
  diagCLM_isSelfAdjoint invCoeff_abs_le_one

/-- The square root coefficients, used to see that `R ≤ 1`. -/
noncomputable def sqrtInvCoeff (n : ℕ) : ℝ := Real.sqrt (invCoeff n)

theorem sqrtInvCoeff_abs_le_one (n : ℕ) : |sqrtInvCoeff n| ≤ 1 := by
  have h0 : 0 ≤ sqrtInvCoeff n := Real.sqrt_nonneg _
  rw [abs_of_nonneg h0, sqrtInvCoeff]
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (invCoeff_le_one n)

theorem ell2ShiftInvert_eq_sq (x : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert x = diagCLM sqrtInvCoeff_abs_le_one (diagCLM sqrtInvCoeff_abs_le_one x) := by
  apply lp.ext
  funext n
  rw [ell2ShiftInvert, diagCLM_apply, diagCLM_apply, diagCLM_apply, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul]
  norm_cast
  rw [sqrtInvCoeff, Real.mul_self_sqrt (invCoeff_pos n).le]

/-- **The shift-inverted operator is `≤ 1`**, which is what makes the associated
unbounded operator positive. -/
theorem ell2ShiftInvert_le_one (v : ℓ²(ℕ, ℂ)) :
    (1 : ℝ) * ‖ell2ShiftInvert v‖ ^ 2 ≤ (inner ℂ (ell2ShiftInvert v) v : ℂ).re := by
  set S := diagCLM sqrtInvCoeff_abs_le_one with hS
  have hsq : ell2ShiftInvert v = S (S v) := ell2ShiftInvert_eq_sq v
  have hinner : (inner ℂ (ell2ShiftInvert v) v : ℂ) = inner ℂ (S v) (S v) := by
    rw [hsq]
    exact diagCLM_symmetric sqrtInvCoeff_abs_le_one (S v) v
  have hre : (inner ℂ (ell2ShiftInvert v) v : ℂ).re = ‖S v‖ ^ 2 := by
    rw [hinner, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hnorm : ‖ell2ShiftInvert v‖ ≤ ‖S v‖ := by
    rw [hsq]
    exact diagCLM_norm_apply_le sqrtInvCoeff_abs_le_one (S v)
  rw [hre, one_mul]
  nlinarith [norm_nonneg (ell2ShiftInvert v), norm_nonneg (S v)]

/-- **The unbounded Hamiltonian of the example**: `A = R⁻¹ − 1`, i.e. `A eₙ = n eₙ`,
on the domain `range R = {x : ∑ (n+1)²|xₙ|² < ∞}`. -/
noncomputable def ell2UnboundedExample :
    LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) →ₗ[ℂ] ℓ²(ℕ, ℂ) :=
  invShiftOperator ell2ShiftInvert ell2ShiftInvert_injective 1

theorem ell2UnboundedExample_isShiftInvert :
    IsShiftInvert ell2UnboundedExample 1 ell2ShiftInvert :=
  isShiftInvert_invShiftOperator ell2ShiftInvert ell2ShiftInvert_injective 1

/-- The `k`-th basis vector of `ℓ²(ℕ, ℂ)` is in the range of `R`: indeed
`R ((k+1) eₖ) = eₖ`. -/
theorem ell2ShiftInvert_smul_single (k : ℕ) :
    ell2ShiftInvert (((k : ℂ) + 1) • lp.single 2 k (1 : ℂ)) = lp.single 2 k (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [ell2ShiftInvert, diagCLM_apply]
  by_cases hn : n = k
  · subst hn
    have hne : ((n : ℂ) + 1) ≠ 0 := by
      rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero n
    have hcoe : ((invCoeff n : ℝ) : ℂ) = ((n : ℂ) + 1)⁻¹ := by
      rw [invCoeff]
      push_cast
      rw [one_div]
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_eq_same, hcoe,
      smul_eq_mul, mul_one]
    field_simp
  · simp [lp.single_apply, Pi.single_eq_of_ne hn]

theorem ell2Basis_apply (k : ℕ) : (ell2Basis k : ℓ²(ℕ, ℂ)) = lp.single 2 k (1 : ℂ) :=
  lp.ext_iff.mpr (congrArg Subtype.val (HilbertBasis.repr_self ell2Basis k))

theorem ell2Basis_mem_range (k : ℕ) :
    (ell2Basis k : ℓ²(ℕ, ℂ))
      ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) :=
  ⟨((k : ℂ) + 1) • lp.single 2 k (1 : ℂ), by
    rw [ell2Basis_apply]; exact ell2ShiftInvert_smul_single k⟩

/-- The finite-mode (Hermite-type) domain sits inside the domain of the
unbounded operator, so the algorithm's matrix elements are all defined. -/
theorem finiteModeDomain_le_range :
    finiteModeDomain ell2Basis
      ≤ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) := by
  rw [finiteModeDomain, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact ell2Basis_mem_range k

/-- **The matrix the algorithm is given**: the unbounded operator restricted to
finite linear combinations of basis vectors. -/
noncomputable def ell2ExampleMatrix : finiteModeDomain ell2Basis →ₗ[ℂ] ℓ²(ℕ, ℂ) :=
  ell2UnboundedExample.comp (Submodule.inclusion finiteModeDomain_le_range)

/-- **The example is a positive self-adjoint (Friedrichs) extension of its
matrix** — with no boundedness anywhere. -/
theorem ell2Example_isPositiveSelfAdjointExtension :
    IsPositiveSelfAdjointExtension ell2ExampleMatrix ell2UnboundedExample :=
  invShiftOperator_isPositiveSelfAdjointExtension ell2ShiftInvert ell2ShiftInvert_injective 1
    ell2ShiftInvert_isSelfAdjoint ell2ShiftInvert_le_one finiteModeDomain_le_range
    ell2ExampleMatrix (fun _ => rfl)

theorem norm_single_one (k : ℕ) : ‖(lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ))‖ = 1 := by
  rw [lp.norm_single (by norm_num)]
  simp

/-- **The example really is unbounded**: the matrix elements the algorithm is
fed satisfy no bound `‖Hx‖ ≤ C‖x‖`, because `H eₖ = k eₖ`.  So the boundedness
hypothesis of `hermiteGalerkin_selects_friedrichs` fails here, while the
shift-invert theorems apply. -/
theorem ell2ExampleMatrix_unbounded (C : ℝ) :
    ∃ x : finiteModeDomain ell2Basis, C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hmem : (lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ)) ∈ finiteModeDomain ell2Basis := by
    rw [← ell2Basis_apply]
    exact Submodule.subset_span ⟨k, rfl⟩
  refine ⟨⟨lp.single 2 k (1 : ℂ), hmem⟩, ?_⟩
  have hrange : (lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ))
      ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) :=
    finiteModeDomain_le_range hmem
  have hpre : preim ell2ShiftInvert ⟨lp.single 2 k (1 : ℂ), hrange⟩
      = ((k : ℂ) + 1) • lp.single 2 k (1 : ℂ) :=
    preim_eq _ ell2ShiftInvert_injective _ (ell2ShiftInvert_smul_single k)
  have hval : ell2ExampleMatrix ⟨lp.single 2 k (1 : ℂ), hmem⟩
      = (k : ℂ) • lp.single 2 k (1 : ℂ) := by
    change ell2UnboundedExample ⟨lp.single 2 k (1 : ℂ), hrange⟩ = _
    rw [ell2UnboundedExample, invShiftOperator_apply, hpre]
    push_cast
    module
  rw [hval, norm_smul, norm_single_one]
  simp only [mul_one, Complex.norm_natCast]
  exact hk

/-- **The Hashimoto/Galerkin selection theorem for a genuinely unbounded
Hamiltonian.**  For the operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)` — unbounded, by the
last clause — with shift `γ = 1`:

* the effective (shift-inverted) Hamiltonian `R = (A+1)⁻¹` is a bounded
  self-adjoint operator of norm at most one;
* its Galerkin truncations, and their resolvents, converge strongly to it;
* `R` determines the domain (and hence the operator): no other self-adjoint
  operator has the same shift-invert.

So the bounded convergence theory of the Galerkin truncation does reach the
unbounded Hamiltonian, through the shift-invert. -/
theorem hashimoto_shiftInvert_unbounded_example :
    IsShiftInvert ell2UnboundedExample 1 ell2ShiftInvert ∧
    ‖ell2ShiftInvert‖ ≤ 1 ∧ IsSelfAdjoint ell2ShiftInvert ∧
    (∀ u : ℓ²(ℕ, ℂ), Tendsto
      (fun m : ℕ => galerkinCompression ell2ShiftInvert ell2Basis m u) atTop
        (nhds (ell2ShiftInvert u))) ∧
    (∀ z : ℂ, z.im ≠ 0 → ∀ u : ℓ²(ℕ, ℂ), Tendsto
      (fun m : ℕ => resolvent (galerkinCompression ell2ShiftInvert ell2Basis m) z u) atTop
        (nhds (resolvent ell2ShiftInvert z u))) ∧
    (∀ (Dom' : Submodule ℂ (ℓ²(ℕ, ℂ))) (A' : Dom' →ₗ[ℂ] ℓ²(ℕ, ℂ)),
      IsShiftInvert A' 1 ell2ShiftInvert →
      Dom' = LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) ∧
    (∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
      C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖) := by
  obtain ⟨R, hR, hnorm, hsa, -, hstrong, hres, huniq⟩ :=
    hashimoto_shiftInvert_selects_friedrichs ell2Basis ell2ExampleMatrix ell2UnboundedExample
      ell2Example_isPositiveSelfAdjointExtension (γ := 1) one_pos
  have hReq : R = ell2ShiftInvert :=
    isShiftInvert_unique hR ell2UnboundedExample_isShiftInvert
  subst hReq
  refine ⟨hR, by simpa only [inv_one] using hnorm, hsa, hstrong, hres, ?_,
    ell2ExampleMatrix_unbounded⟩
  intro Dom' A' hA'
  exact (huniq Dom' A' hA').1

end Example

end BookProof.HashimotoShiftInvert
