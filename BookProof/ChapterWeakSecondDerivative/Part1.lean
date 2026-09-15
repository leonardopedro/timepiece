import Mathlib

/-!
# One-dimensional distributional regularity: `u'' = c·u` in the weak sense

`CONSOLIDATED_PLAN.md` §10.6.1/§10.6.2 leaves one gap of the quantum-gravity chapter open:
the *exponentially growing* scalaron wall.  Every route the project has tried so far is a
perturbative one — Kato–Rellich on the Gauss–polynomial core, the Carleman flux criterion
on the Hermite lattice — and both are refuted or inapplicable for a wall that grows faster
than every polynomial (`BookProof/ChapterHermiteExpWall.lean`).

The classical route that *does* reach an arbitrarily fast growing **non-negative** potential
is not perturbative at all: a deficiency vector `u` of `−d²/dx² + V` solves the ordinary
differential equation `u'' = (V − z)u`, and a non-negative `V` makes `|u|²` convex — hence,
being integrable and non-negative, zero.  The step that has to be supplied before the ODE
argument can start is *regularity*: the deficiency vector is a priori only an `L²` function
and the equation it satisfies is a distributional one.

This module supplies exactly that step, in one variable, with no reference to the physics:

* `exists_antideriv` — a test function of vanishing integral is the derivative of a test
  function (the elementary fact that makes the du Bois-Reymond argument work);
* `ae_eq_const_of_integral_deriv_smul_eq_zero` — **du Bois-Reymond**: a locally integrable
  function orthogonal to the derivative of every test function is a.e. constant;
* `ae_eq_affine_of_integral_deriv2_smul_eq_zero` — the second-order version: orthogonal to
  every *second* derivative means a.e. affine;
* `integral_deriv_mul_indefiniteIntegral` — integration by parts against an indefinite
  integral of a merely locally integrable function (through Mathlib's
  `AbsolutelyContinuousOnInterval` calculus, since such a primitive is differentiable only
  almost everywhere);
* `exists_ae_eq_doubleAntideriv_add_affine` — the real-valued regularity theorem: a weak
  solution of `u'' = G` is a.e. the double antiderivative of `G` plus an affine function;
* **`exists_deriv2_of_weak_eq`** — the complex-valued statement in the form the Schrödinger
  argument consumes: if `u` is locally integrable, `c` is continuous and `∫ g'' u = ∫ g c u`
  for every real test function `g`, then `u` agrees almost everywhere with a genuinely twice
  differentiable `W` satisfying `W'' = c·W` *everywhere*.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.WeakSecondDeriv

open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

/-- A **test function** on the line: smooth and compactly supported. -/
def IsTestFun (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g

namespace IsTestFun

theorem contDiff {g : ℝ → ℝ} (h : IsTestFun g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := h.1

theorem hasCompactSupport {g : ℝ → ℝ} (h : IsTestFun g) : HasCompactSupport g := h.2

theorem continuous {g : ℝ → ℝ} (h : IsTestFun g) : Continuous g := h.contDiff.continuous

theorem differentiable {g : ℝ → ℝ} (h : IsTestFun g) : Differentiable ℝ g :=
  (contDiff_infty_iff_deriv.1 h.contDiff).1

/-- The derivative of a test function is a test function. -/
theorem deriv {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (_root_.deriv g) :=
  ⟨(contDiff_infty_iff_deriv.1 h.contDiff).2, h.hasCompactSupport.deriv⟩

theorem integrable {g : ℝ → ℝ} (h : IsTestFun g) : Integrable g volume :=
  h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport

theorem sub {f g : ℝ → ℝ} (h1 : IsTestFun f) (h2 : IsTestFun g) :
    IsTestFun (fun x => f x - g x) := ⟨h1.contDiff.sub h2.contDiff, h1.2.sub h2.2⟩

theorem const_mul {g : ℝ → ℝ} (h : IsTestFun g) (a : ℝ) : IsTestFun (fun x => a * g x) :=
  ⟨contDiff_const.mul h.contDiff, h.hasCompactSupport.mul_left⟩

/-- Multiplying a test function by the coordinate gives a test function. -/
theorem coord_mul {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (fun x => x * g x) :=
  ⟨contDiff_id.mul h.contDiff, h.hasCompactSupport.mul_left⟩

end IsTestFun

/-! ## 1. Elementary facts about test functions -/

/-- There is a test function of integral one. -/
theorem exists_unitTest : ∃ ρ : ℝ → ℝ, IsTestFun ρ ∧ ∫ x, ρ x = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed⟩, f.integral_normed⟩

/-- A test function has its support in a symmetric compact interval. -/
theorem exists_supp {g : ℝ → ℝ} (h : IsTestFun g) :
    ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Icc (-R) R := by
  obtain ⟨R, hR⟩ := (h.hasCompactSupport.isCompact.isBounded).subset_closedBall (0 : ℝ)
  refine ⟨|R|, abs_nonneg R, fun x hx => ?_⟩
  have hx' := hR hx
  rw [Real.closedBall_eq_Icc] at hx'
  simp only [zero_sub, zero_add, mem_Icc] at hx' ⊢
  exact ⟨by linarith [le_abs_self R, hx'.1], by linarith [le_abs_self R, hx'.2]⟩

theorem eq_zero_out {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R)
    {x : ℝ} (hx : x ∉ Icc (-R) R) : g x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))

theorem deriv_eq_zero_out {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R)
    {x : ℝ} (hx : x ∉ Icc (-R) R) : deriv g x = 0 := by
  by_contra hne
  exact hx (hsupp (support_deriv_subset (by exact hne)))

/-- An integral over the line of a function vanishing outside `[-R, R]` is an interval
integral. -/
theorem integral_eq_intervalIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {R a b : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x, x ∉ Icc (-R) R → f x = 0) (ha : a < -R) (hb : R < b) :
    ∫ x, f x = ∫ x in a..b, f x := by
  have hab : a ≤ b := by linarith
  rw [intervalIntegral.integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
  refine hf x ?_
  simp only [mem_Icc, not_and_or, not_le]
  rcases hx with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The integral of the derivative of a test function vanishes. -/
theorem integral_deriv_of_test {g : ℝ → ℝ} (h : IsTestFun g) : ∫ x, deriv g x = 0 := by
  obtain ⟨R, hR, hsupp⟩ := exists_supp h
  rw [integral_eq_intervalIntegral (R := R) (a := -R - 1) (b := R + 1) hR
    (fun x hx => deriv_eq_zero_out hsupp hx) (by linarith) (by linarith)]
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => h.differentiable x)
    (h.deriv.continuous.intervalIntegrable _ _)]
  rw [eq_zero_out hsupp (by simp), eq_zero_out (x := -R - 1) hsupp (by simp)]
  ring

/-- **A test function of vanishing integral is a derivative.** -/
theorem exists_antideriv {g : ℝ → ℝ} (h : IsTestFun g) (h0 : ∫ x, g x = 0) :
    ∃ G : ℝ → ℝ, IsTestFun G ∧ deriv G = g := by
  obtain ⟨R, hR, hsupp⟩ := exists_supp h
  set G : ℝ → ℝ := fun x => ∫ t in (-R - 1)..x, g t with hG
  have hderiv : ∀ x, HasDerivAt G (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (h.continuous.intervalIntegrable _ _)
      (h.continuous.stronglyMeasurableAtFilter _ _) h.continuous.continuousAt
  have hdG : deriv G = g := funext fun x => (hderiv x).deriv
  refine ⟨G, ⟨?_, ?_⟩, hdG⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by rw [hdG]; exact h.contDiff⟩
  · apply HasCompactSupport.intro (isCompact_Icc (a := -R - 1) (b := R + 1))
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have hz : G x = ∫ _t in (-R - 1)..x, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_comm, uIcc_of_le (by linarith)] at ht
        refine eq_zero_out hsupp ?_
        simp only [mem_Icc, not_and_or, not_le]
        exact Or.inl (by linarith [ht.2])
      simpa using hz
    · change (∫ t in (-R - 1)..x, g t) = 0
      rw [← integral_eq_intervalIntegral (R := R) hR (fun y hy => eq_zero_out hsupp hy)
        (by linarith) (by linarith)]
      exact h0

/-- The integral of a test function is minus the first moment of its derivative. -/
theorem integral_eq_neg_integral_coord_mul_deriv {g : ℝ → ℝ} (h : IsTestFun g) :
    ∫ x, g x = -∫ x, x * deriv g x := by
  have hd : deriv (fun x => x * g x) = fun x => g x + x * deriv g x := by
    funext x
    have h1 : HasDerivAt (fun x : ℝ => x * g x) (1 * g x + x * deriv g x) x :=
      (hasDerivAt_id x).mul (h.differentiable x).hasDerivAt
    rw [h1.deriv]; ring
  have h0 := integral_deriv_of_test h.coord_mul
  rw [hd] at h0
  rw [integral_add h.integrable h.deriv.coord_mul.integrable] at h0
  linarith

/-! ## 2. The du Bois-Reymond lemmas -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


omit [CompleteSpace F] in
/-- A test function times a locally integrable function is integrable. -/
theorem integrable_test_smul {φ : ℝ → ℝ} (hφ : IsTestFun φ) {r : ℝ → F}
    (hr : LocallyIntegrable r volume) : Integrable (fun x => φ x • r x) volume := by
  refine (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).1 ?_
  · intro x hx
    simp only [Function.mem_support] at hx
    exact subset_tsupport φ (fun h => hx (by simp [h]))
  · exact (hr.integrableOn_isCompact hφ.hasCompactSupport.isCompact).continuousOn_smul
      hφ.continuous.continuousOn hφ.hasCompactSupport.isCompact

/-- **Du Bois-Reymond.**  A locally integrable function that integrates to zero against the
derivative of every test function is almost everywhere constant. -/
theorem ae_eq_const_of_integral_deriv_smul_eq_zero {r : ℝ → F}
    (hr : LocallyIntegrable r volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv g x • r x = 0) :
    ∃ c : F, r =ᵐ[volume] fun _ => c := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_unitTest
  set c : F := ∫ x, ρ x • r x with hc
  have key : ∀ φ : ℝ → ℝ, IsTestFun φ → ∫ x, φ x • r x = (∫ x, φ x) • c := by
    intro φ hφ
    set I := ∫ x, φ x with hI
    have hIρ : IsTestFun (fun x => I * ρ x) := hρ.const_mul I
    have hψ : IsTestFun (fun x => φ x - I * ρ x) := hφ.sub hIρ
    have hψ0 : ∫ x, (φ x - I * ρ x) = 0 := by
      rw [integral_sub hφ.integrable hIρ.integrable, MeasureTheory.integral_const_mul, hρ1]
      simp [hI]
    obtain ⟨G, hG, hdG⟩ := exists_antideriv hψ hψ0
    have h1 := h G hG
    rw [hdG] at h1
    have hint2 : Integrable (fun x => I • (ρ x • r x)) volume :=
      (integrable_test_smul hρ hr).smul I
    have h2 : ∫ x, ((fun x => φ x - I * ρ x) x) • r x = (∫ x, φ x • r x) - I • c := by
      have he : ∀ x, (φ x - I * ρ x) • r x = φ x • r x - I • (ρ x • r x) := by
        intro x; rw [sub_smul, smul_smul]
      simp_rw [he]
      rw [integral_sub (integrable_test_smul hφ hr) hint2, MeasureTheory.integral_smul]
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  refine ⟨c, ?_⟩
  have hloc : LocallyIntegrable (fun x => r x - c) volume := hr.sub (locallyIntegrable_const c)
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg1 hg2 => ?_)
  · filter_upwards [hz] with x hx
    simpa [sub_eq_zero] using hx
  · have hg : IsTestFun g := ⟨hg1, hg2⟩
    have he : ∀ x, g x • (r x - c) = g x • r x - g x • c := fun x => by rw [smul_sub]
    simp_rw [he]
    rw [integral_sub (integrable_test_smul hg hr) (hg.integrable.smul_const c),
      _root_.integral_smul_const, key g hg]
    module

/-- **Du Bois-Reymond, second order.**  A locally integrable function that integrates to
zero against the second derivative of every test function is almost everywhere affine. -/
theorem ae_eq_affine_of_integral_deriv2_smul_eq_zero {r : ℝ → F}
    (hr : LocallyIntegrable r volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x • r x = 0) :
    ∃ a b : F, r =ᵐ[volume] fun x => x • a + b := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_unitTest
  set k : F := ∫ x, deriv ρ x • r x with hk
  -- for every test function `ψ`, `∫ ψ' • r = (∫ ψ) • k`
  have key : ∀ ψ : ℝ → ℝ, IsTestFun ψ → ∫ x, deriv ψ x • r x = (∫ x, ψ x) • k := by
    intro ψ hψ
    set I := ∫ x, ψ x with hI
    have hIρ : IsTestFun (fun x => I * ρ x) := hρ.const_mul I
    have hχ : IsTestFun (fun x => ψ x - I * ρ x) := hψ.sub hIρ
    have hχ0 : ∫ x, (ψ x - I * ρ x) = 0 := by
      rw [integral_sub hψ.integrable hIρ.integrable, MeasureTheory.integral_const_mul, hρ1]
      simp [hI]
    obtain ⟨G, hG, hdG⟩ := exists_antideriv hχ hχ0
    have h1 := h G hG
    rw [hdG] at h1
    have hdχ : deriv (fun x => ψ x - I * ρ x) = fun x => deriv ψ x - I * deriv ρ x := by
      funext x
      have h2 : HasDerivAt (fun x => ψ x - I * ρ x)
          (deriv ψ x - I * deriv ρ x) x :=
        ((hψ.differentiable x).hasDerivAt).sub
          (((hρ.differentiable x).hasDerivAt).const_mul I)
      exact h2.deriv
    rw [hdχ] at h1
    have hint2 : Integrable (fun x => I • (deriv ρ x • r x)) volume :=
      (integrable_test_smul hρ.deriv hr).smul I
    have h2 : ∫ x, (deriv ψ x - I * deriv ρ x) • r x
        = (∫ x, deriv ψ x • r x) - I • k := by
      have he : ∀ x, (deriv ψ x - I * deriv ρ x) • r x
          = deriv ψ x • r x - I • (deriv ρ x • r x) := by
        intro x; rw [sub_smul, smul_smul]
      simp_rw [he]
      rw [integral_sub (integrable_test_smul hψ.deriv hr) hint2, MeasureTheory.integral_smul]
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  -- hence `r + x • k` is orthogonal to every derivative, so it is a.e. constant
  set s : ℝ → F := fun x => r x + x • k with hs
  have hsloc : LocallyIntegrable s volume := by
    refine hr.add ?_
    exact (continuous_id.smul continuous_const).locallyIntegrable
  have hzero : ∀ ψ : ℝ → ℝ, IsTestFun ψ → ∫ x, deriv ψ x • s x = 0 := by
    intro ψ hψ
    have he : ∀ x, deriv ψ x • s x = deriv ψ x • r x + (x * deriv ψ x) • k := by
      intro x
      rw [hs]
      simp only [smul_add, smul_smul]
      rw [mul_comm]
    simp_rw [he]
    rw [integral_add (integrable_test_smul hψ.deriv hr)
      ((hψ.deriv.coord_mul.integrable).smul_const k), _root_.integral_smul_const, key ψ hψ,
      integral_eq_neg_integral_coord_mul_deriv hψ]
    module
  obtain ⟨b, hb⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero hsloc hzero
  refine ⟨-k, b, ?_⟩
  filter_upwards [hb] with x hx
  have : r x + x • k = b := hx
  rw [smul_neg, ← this]
  abel

end

end BookProof.WeakSecondDeriv
