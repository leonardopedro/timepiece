import Mathlib
import BookProof.Sm.ChapterSmReverseEllipticResidual

/-!
# The form-domain comparison, as a named input with its reductions

Work order: `SM_ESA_COMPLETION_PLAN.md` §32.

## 1. Why a name

§31 showed that the reverse elliptic estimate is exactly the non-negativity of
`‖Δ_S p‖² + 2 ℜ⟪−Δ_S p, W p + p⟫`, and that the sign route cannot reach it.  The honest statement of
the missing input is a **domain** statement, and a domain statement deserves a name rather than
another restatement of `hpoly`.  Write `N = −Δ_S + W + 1`.  The input is

```text
‖−Δ_S p‖  ≤  c ‖N p‖        for every polynomial p,        (FormDomainComparison)
```

i.e. the graph norm of `N` dominates the `H²` norm of `p`.  In form language: the domain of the
closed form of `N` — `H¹` intersected with `L²(W)` — is contained in the `H²` domain, and the
inclusion is bounded.  This is precisely the step that elliptic regularity supplies for a
polynomial potential and that the corpus does not contain; naming it makes the gap quotable instead
of embedding it in a passing remark.

`FormDomainComparison` is defined in `BookProof.SmFormDomainComparison`.

## 2. The reductions, both ways

The name is not a weaker hypothesis, and the module proves that rather than asserting it:

* `formDomainComparison_of_potSelfBound` — a self-bound with constant `β ≥ 0` gives the comparison
  with constant `1 + β`, by the triangle inequality `‖Δ p‖ ≤ ‖N p‖ + ‖W p + p‖`;
* `potSelfBound_of_formDomainComparison` — conversely the comparison with constant `c` gives the
  self-bound with constant `1 + c`; this is §26's `potSelfBound_of_kinetic_bound` under the name of
  the object it uses;
* `exists_potSelfBound_iff_exists_formDomainComparison` — therefore `PotSelfBound` for some
  non-negative constant exists **iff** the form-domain comparison does.  The named input is the
  reverse estimate, not a weaker stand-in for it, and a worker who discharges one has discharged
  both.

## 3. The half that the form language does give

What the quadratic form does give without elliptic regularity is coercivity, and the module records
it so that the difference between the two statements is visible:

* `form_coercive` — `‖p‖² ≤ ℜ⟪p, N p⟫`, from `ℜ⟪−Δ_S p, p⟫ = ∑_j ‖∇_j p‖² ≥ 0` (§31) and the
  pointwise non-negativity of the quartic `W` (§23);
* `norm_le_shiftNorm_of_coercive` — hence `‖p‖ ≤ ‖N p‖`, by Cauchy–Schwarz.

So `H¹ ∩ L²(W) ⊆ D(N)` with a norm bound is available, and it is the whole of what the form gives.
It is `H²`, one derivative higher, that needs the named input — which is why no amount of coercivity
closes `PotSelfBound`.

Everything here is `sorry`-free and `axiom`-free.  `FormDomainComparison` is *not* proved for the
SM's quartic `W`; it is the named open input, and `PotSelfBound` remains a hypothesis downstream.
-/

namespace BookProof.SmFormDomainComparison

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine BookProof.SmKineticElliptic BookProof.SmKineticGarding
open BookProof.SmGaussWeightedIbp BookProof.SmGradInterpolation BookProof.QuadratureEsa
open BookProof.SmReverseEllipticResidual

noncomputable section

/-! ## 1. The named input -/

/-- **The form-domain comparison**: the graph norm of `N = −Δ_S + W + 1` dominates the `H²` norm,
`‖−Δ_S p‖ ≤ c ‖N p‖` for every polynomial `p`.

In form language this says the domain of the closed form of `N` is contained in the `H²` domain with
a bounded inclusion.  It is *equivalent* to `PotSelfBound` (see
`exists_potSelfBound_iff_exists_formDomainComparison`) and is **not** proved for the SM's quartic
`W`; it is the named open input of the reverse elliptic estimate. -/
def FormDomainComparison (P : SmParams) (c0 c : ℝ) : Prop :=
  ∀ p : MvPolynomial (Fin 163) ℂ,
    ‖pgLp (kinPolyS smS p)‖
      ≤ c * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖

/-- The comparison read as a statement about the Laplace term alone. -/
theorem formDomainComparison_iff (P : SmParams) (c0 c : ℝ) :
    FormDomainComparison P c0 c
      ↔ ∀ p : MvPolynomial (Fin 163) ℂ,
        ‖pgLp (kinPolyS smS p)‖
          ≤ c * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ := Iff.rfl

/-! ## 2. The comparison from a self-bound, and back -/

/-- **A self-bound gives the comparison**: `‖−Δ_S p‖ ≤ ‖N p‖ + ‖W p + p‖ ≤ (1 + β) ‖N p‖`.  The
triangle inequality is §22's `kinetic_le_shift_add_pot`, and the second step is `PotSelfBound`. -/
theorem formDomainComparison_of_potSelfBound (P : SmParams) (c0 : ℝ) {β : ℝ}
    (h : PotSelfBound P c0 β) : FormDomainComparison P c0 (1 + β) := by
  intro p
  have h1 : ‖pgLp (kinPolyS smS p)‖
      ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖
        + ‖pgLp (smPotPoly P c0 * p) + pgLp p‖ :=
    kinetic_le_shift_add_pot P c0 p
  have h2 : ‖pgLp (smPotPoly P c0 * p) + pgLp p‖
      ≤ β * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ := h p
  set S : ℝ := ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖
  have hS0 : 0 ≤ S := norm_nonneg _
  calc ‖pgLp (kinPolyS smS p)‖ ≤ S + β * S := by linarith
    _ = (1 + β) * S := by ring

/-- **The comparison gives the self-bound**, at constant `1 + c`: §26's
`potSelfBound_of_kinetic_bound`, stated for the named input. -/
theorem potSelfBound_of_formDomainComparison (P : SmParams) (c0 : ℝ) {c : ℝ}
    (h : FormDomainComparison P c0 c) : PotSelfBound P c0 (1 + c) :=
  potSelfBound_of_kinetic_bound P c0 h

/-- **The named input is not weaker than the self-bound**: a non-negative self-bound exists if and
only if the form-domain comparison does.  Both directions are the two reductions above. -/
theorem exists_potSelfBound_iff_exists_formDomainComparison (P : SmParams) (c0 : ℝ) :
    (∃ β : ℝ, 0 ≤ β ∧ PotSelfBound P c0 β)
      ↔ ∃ c : ℝ, 0 ≤ c ∧ FormDomainComparison P c0 c := by
  constructor
  · rintro ⟨β, hβ0, hβ⟩
    exact ⟨1 + β, by linarith, formDomainComparison_of_potSelfBound P c0 hβ⟩
  · rintro ⟨c, hc0, hc⟩
    exact ⟨1 + c, by linarith, potSelfBound_of_formDomainComparison P c0 hc⟩

/-! ## 3. The half the form itself gives: coercivity -/

/-- **Coercivity of the comparison form**: `‖p‖² ≤ ℜ⟪p, N p⟫`.  The Dirichlet energy is
non-negative (§31's `re_inner_kinPolyS_self`) and the quartic potential is pointwise non-negative
(§23's `smPotPoly_nonneg`), so both weighted terms contribute with the right sign. -/
theorem form_coercive (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (p : MvPolynomial (Fin 163) ℂ) :
    ‖pgLp p‖ ^ 2
      ≤ (inner ℂ (pgLp p)
        (pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p)).re := by
  have hW : cpoly (smPotPoly P c0) = smPotPoly P c0 := realCoeff_smPotPoly P c0
  have hW0 : ∀ x : Vd 163,
      0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (smPotPoly P c0)).re :=
    smPotPoly_nonneg P hc0
  set K : L2d 163 := pgLp (kinPolyS smS p) with hK
  set Wp : L2d 163 := pgLp (smPotPoly P c0 * p) with hWp
  have hN : pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p
      = K + Wp + pgLp p := by
    rw [pgLp_add']
  rw [hN, inner_add_right, inner_add_right, Complex.add_re, Complex.add_re]
  have h1 : 0 ≤ (inner ℂ (pgLp p) K).re := by
    have hsym : (inner ℂ (pgLp p) K).re = (inner ℂ K (pgLp p)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym, hK, re_inner_kinPolyS_self]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ (inner ℂ (pgLp p) Wp).re := by
    have hsym : (inner ℂ (pgLp p) Wp).re = (inner ℂ Wp (pgLp p)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym, hWp, inner_pgLp_pgLp]
    exact gaussInt_weighted_self_nonneg _ _ hW hW0
  have h3 : (inner ℂ (pgLp p) (pgLp p)).re = ‖pgLp p‖ ^ 2 := by
    rw [inner_pgLp_pgLp, ← norm_pgLp_sq]
  linarith

/-- **`‖p‖ ≤ ‖N p‖` from coercivity**, by Cauchy–Schwarz: the form bound gives
`‖p‖² ≤ ‖p‖ ‖N p‖`. -/
theorem norm_le_shiftNorm_of_coercive (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (p : MvPolynomial (Fin 163) ℂ) :
    ‖pgLp p‖
      ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ := by
  set N : L2d 163 := pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p with hN
  have hco := form_coercive P hc0 p
  have hle : ‖pgLp p‖ ^ 2 ≤ ‖pgLp p‖ * ‖N‖ := by
    refine hco.trans ?_
    have h1 : |(inner ℂ (pgLp p) N).re| ≤ ‖(inner ℂ (pgLp p) N : ℂ)‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖(inner ℂ (pgLp p) N : ℂ)‖ ≤ ‖pgLp p‖ * ‖N‖ := norm_inner_le_norm _ _
    have h3 : (inner ℂ (pgLp p) N).re ≤ |(inner ℂ (pgLp p) N).re| := le_abs_self _
    exact h3.trans (h1.trans h2)
  rcases eq_or_lt_of_le (norm_nonneg (pgLp p)) with h0 | hpos
  · rw [← h0]
    exact norm_nonneg N
  · exact le_of_mul_le_mul_left (by simpa [pow_two] using hle) hpos

end

end BookProof.SmFormDomainComparison
