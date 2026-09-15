import Mathlib
import BookProof.ChapterWeakSecondDerivative.Part1

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

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-! ## 3. Integration by parts against an indefinite integral -/

/-- The primitive of a locally integrable function is absolutely continuous on every
interval containing the base point. -/
theorem absolutelyContinuous_primitive {G : ℝ → ℝ} (hG : LocallyIntegrable G volume)
    {a b c : ℝ} (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, G t) a b :=
  IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (hG.integrableOn_isCompact isCompact_uIcc).intervalIntegrable hc

/-- A test function is absolutely continuous on every interval. -/
theorem absolutelyContinuous_test {g : ℝ → ℝ} (hg : IsTestFun g) (a b : ℝ) :
    AbsolutelyContinuousOnInterval g a b := by
  obtain ⟨x₀, hx₀⟩ := hg.deriv.continuous.norm.exists_forall_ge_of_hasCompactSupport
    hg.deriv.hasCompactSupport.norm
  refine (LipschitzWith.lipschitzOnWith (K := ⟨‖deriv g x₀‖, norm_nonneg _⟩)
    (lipschitzWith_of_nnnorm_deriv_le hg.differentiable fun x => ?_)).absolutelyContinuousOnInterval
  rw [← NNReal.coe_le_coe]
  simpa using hx₀ x

/-- **Integration by parts against an indefinite integral.**  For a locally integrable `G`
the primitive `x ↦ ∫_c^x G` is absolutely continuous, so it can be integrated by parts
against a test function although it is differentiable only almost everywhere. -/
theorem integral_deriv_mul_indefiniteIntegral {G : ℝ → ℝ}
    (hG : LocallyIntegrable G volume) (c : ℝ) {g : ℝ → ℝ} (hg : IsTestFun g) :
    ∫ x, deriv g x * (∫ t in c..x, G t) = -∫ x, g x * G x := by
  obtain ⟨R, hR, hsupp⟩ := exists_supp hg
  set A : ℝ → ℝ := fun x => ∫ t in c..x, G t with hA
  set a := min (-R - 1) (c - 1) with hadef
  set b := max (R + 1) (c + 1) with hbdef
  have ha : a < -R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb : R < b := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hab : a ≤ b := by linarith
  have hcmem : c ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨le_trans (min_le_right _ _) (by linarith), le_trans (by linarith) (le_max_right _ _)⟩
  have hga : g a = 0 := by
    refine eq_zero_out hsupp ?_
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inl (by linarith)
  have hgb : g b = 0 := by
    refine eq_zero_out hsupp ?_
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inr (by linarith)
  have hL : ∫ x, deriv g x * A x = ∫ x in a..b, deriv g x * A x :=
    integral_eq_intervalIntegral hR
      (fun x hx => by rw [deriv_eq_zero_out hsupp hx, zero_mul]) ha hb
  have hRHS : ∫ x, g x * G x = ∫ x in a..b, g x * G x :=
    integral_eq_intervalIntegral hR
      (fun x hx => by rw [eq_zero_out hsupp hx, zero_mul]) ha hb
  have hby := (absolutelyContinuous_primitive hG hcmem).integral_mul_deriv_eq_deriv_mul
    (absolutelyContinuous_test hg a b)
  have hdA : ∫ x in a..b, deriv A x * g x = ∫ x in a..b, G x * g x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hG] with x hx _
    rw [(hx c).deriv]
  rw [hdA, hga, hgb] at hby
  rw [hL, hRHS]
  have hcomm : ∫ x in a..b, deriv g x * A x = ∫ x in a..b, A x * deriv g x := by
    simp_rw [mul_comm]
  have hcomm2 : ∫ x in a..b, G x * g x = ∫ x in a..b, g x * G x := by
    simp_rw [mul_comm]
  rw [hcomm, hby, ← hcomm2]
  ring

/-! ## 4. The real regularity theorem -/

/-- The double antiderivative of a locally integrable function. -/
def doubleAntideriv (G : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, ∫ s in (0 : ℝ)..t, G s

theorem continuous_primitive_of_locallyIntegrable {G : ℝ → ℝ}
    (hG : LocallyIntegrable G volume) (c : ℝ) :
    Continuous fun x => ∫ t in c..x, G t :=
  intervalIntegral.continuous_primitive
    (fun _ _ => (hG.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) c

/-- The double antiderivative is a weak solution of `u'' = G`. -/
theorem integral_deriv2_mul_doubleAntideriv {G : ℝ → ℝ} (hG : LocallyIntegrable G volume)
    {g : ℝ → ℝ} (hg : IsTestFun g) :
    ∫ x, deriv (deriv g) x * doubleAntideriv G x = ∫ x, g x * G x := by
  have hA : LocallyIntegrable (fun t => ∫ s in (0 : ℝ)..t, G s) volume :=
    (continuous_primitive_of_locallyIntegrable hG 0).locallyIntegrable
  rw [show doubleAntideriv G = fun x => ∫ t in (0 : ℝ)..x, (fun t => ∫ s in (0:ℝ)..t, G s) t from
    rfl, integral_deriv_mul_indefiniteIntegral hA 0 hg.deriv,
    integral_deriv_mul_indefiniteIntegral hG 0 hg]
  ring

/-- **Regularity of weak solutions of `u'' = G`, real case.** -/
theorem exists_ae_eq_doubleAntideriv_add_affine {u G : ℝ → ℝ}
    (hu : LocallyIntegrable u volume) (hG : LocallyIntegrable G volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x * u x = ∫ x, g x * G x) :
    ∃ a b : ℝ, u =ᵐ[volume] fun x => doubleAntideriv G x + (a * x + b) := by
  have hB : Continuous (doubleAntideriv G) := by
    have hA : LocallyIntegrable (fun t => ∫ s in (0 : ℝ)..t, G s) volume :=
      (continuous_primitive_of_locallyIntegrable hG 0).locallyIntegrable
    exact continuous_primitive_of_locallyIntegrable hA 0
  set r : ℝ → ℝ := fun x => u x - doubleAntideriv G x with hr
  have hrloc : LocallyIntegrable r volume := hu.sub hB.locallyIntegrable
  have hzero : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x • r x = 0 := by
    intro g hg
    have he : ∀ x, deriv (deriv g) x • r x
        = deriv (deriv g) x * u x - deriv (deriv g) x * doubleAntideriv G x := by
      intro x; simp [hr, smul_eq_mul, mul_sub]
    simp_rw [he]
    have hi1 : Integrable (fun x => deriv (deriv g) x * u x) volume := by
      simpa [smul_eq_mul] using integrable_test_smul (F := ℝ) hg.deriv.deriv hu
    have hi2 : Integrable (fun x => deriv (deriv g) x * doubleAntideriv G x) volume := by
      simpa [smul_eq_mul] using
        integrable_test_smul (F := ℝ) hg.deriv.deriv hB.locallyIntegrable
    rw [integral_sub hi1 hi2, h g hg, integral_deriv2_mul_doubleAntideriv hG hg, sub_self]
  obtain ⟨a, b, hab⟩ := ae_eq_affine_of_integral_deriv2_smul_eq_zero hrloc hzero
  refine ⟨a, b, ?_⟩
  filter_upwards [hab] with x hx
  have : u x - doubleAntideriv G x = x • a + b := hx
  simp only [smul_eq_mul] at this
  linarith [this]

/-! ## 5. Calculus for the double antiderivative -/

/-- The double antiderivative only sees the almost-everywhere class of its argument. -/
theorem doubleAntideriv_congr_ae {G H : ℝ → ℝ} (h : G =ᵐ[volume] H) :
    doubleAntideriv G = doubleAntideriv H := by
  have hinner : ∀ t : ℝ, (∫ s in (0 : ℝ)..t, G s) = ∫ s in (0 : ℝ)..t, H s := by
    intro t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [h] with s hs _ using hs
  funext x
  simp only [doubleAntideriv]
  simp_rw [hinner]

/-- The primitive of a continuous function is differentiable, with the expected derivative. -/
theorem hasDerivAt_primitive_of_continuous {H : ℝ → ℝ} (hH : Continuous H) (x : ℝ) :
    HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, H t) (H x) x :=
  (hH.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- The double antiderivative of a continuous function is differentiable, with the primitive
as derivative. -/
theorem hasDerivAt_doubleAntideriv {H : ℝ → ℝ} (hH : Continuous H) (x : ℝ) :
    HasDerivAt (doubleAntideriv H) (∫ t in (0 : ℝ)..x, H t) x :=
  hasDerivAt_primitive_of_continuous
    (continuous_primitive_of_locallyIntegrable hH.locallyIntegrable 0) x

/-- The double antiderivative of a locally integrable function is continuous. -/
theorem continuous_doubleAntideriv {G : ℝ → ℝ} (hG : LocallyIntegrable G volume) :
    Continuous (doubleAntideriv G) :=
  continuous_primitive_of_locallyIntegrable
    (continuous_primitive_of_locallyIntegrable hG 0).locallyIntegrable 0

/-! ## 6. The complex regularity theorem -/

/-- **Regularity of weak solutions of `u'' = c·u`.**  A locally integrable weak solution of
`u'' = c·u` with a *continuous* coefficient `c` agrees almost everywhere with a genuinely
twice differentiable solution. -/
theorem exists_deriv2_of_weak_eq {u : ℝ → ℂ} (hu : LocallyIntegrable u volume)
    {c : ℝ → ℂ} (hc : Continuous c)
    (h : ∀ g : ℝ → ℝ, IsTestFun g →
      ∫ x, ((deriv (deriv g) x : ℝ) : ℂ) * u x = ∫ x, ((g x : ℝ) : ℂ) * (c x * u x)) :
    ∃ W W' : ℝ → ℂ, (∀ x, HasDerivAt W (W' x) x) ∧
      (∀ x, HasDerivAt W' (c x * W x) x) ∧ u =ᵐ[volume] W := by
  -- the inhomogeneity `P = c·u` is locally integrable
  have hPloc : LocallyIntegrable (fun x => c x * u x) volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    simpa [smul_eq_mul] using
      (hu.integrableOn_isCompact hk).continuousOn_smul hc.continuousOn hk
  have hre_loc : ∀ {f : ℝ → ℂ}, LocallyIntegrable f volume →
      LocallyIntegrable (fun x => (f x).re) volume := by
    intro f hf x
    obtain ⟨s, hs, hint⟩ := hf x
    exact ⟨s, hs, hint.re⟩
  have him_loc : ∀ {f : ℝ → ℂ}, LocallyIntegrable f volume →
      LocallyIntegrable (fun x => (f x).im) volume := by
    intro f hf x
    obtain ⟨s, hs, hint⟩ := hf x
    exact ⟨s, hs, hint.im⟩
  have hint_u : ∀ g : ℝ → ℝ, IsTestFun g →
      Integrable (fun x => ((g x : ℝ) : ℂ) * u x) volume := by
    intro g hg
    simpa [Complex.real_smul] using integrable_test_smul (F := ℂ) hg hu
  have hint_P : ∀ g : ℝ → ℝ, IsTestFun g →
      Integrable (fun x => ((g x : ℝ) : ℂ) * (c x * u x)) volume := by
    intro g hg
    simpa [Complex.real_smul] using integrable_test_smul (F := ℂ) hg hPloc
  -- real and imaginary parts of the weak equation
  have hEqRe : ∀ g : ℝ → ℝ, IsTestFun g →
      ∫ x, deriv (deriv g) x * (u x).re = ∫ x, g x * (c x * u x).re := by
    intro g hg
    have e1 : (∫ x, ((deriv (deriv g) x : ℝ) : ℂ) * u x).re
        = ∫ x, deriv (deriv g) x * (u x).re := by
      simpa using (Complex.reCLM.integral_comp_comm (hint_u _ hg.deriv.deriv)).symm
    have e2 : (∫ x, ((g x : ℝ) : ℂ) * (c x * u x)).re = ∫ x, g x * (c x * u x).re := by
      simpa using (Complex.reCLM.integral_comp_comm (hint_P _ hg)).symm
    rw [← e1, ← e2, h g hg]
  have hEqIm : ∀ g : ℝ → ℝ, IsTestFun g →
      ∫ x, deriv (deriv g) x * (u x).im = ∫ x, g x * (c x * u x).im := by
    intro g hg
    have e1 : (∫ x, ((deriv (deriv g) x : ℝ) : ℂ) * u x).im
        = ∫ x, deriv (deriv g) x * (u x).im := by
      simpa using (Complex.imCLM.integral_comp_comm (hint_u _ hg.deriv.deriv)).symm
    have e2 : (∫ x, ((g x : ℝ) : ℂ) * (c x * u x)).im = ∫ x, g x * (c x * u x).im := by
      simpa using (Complex.imCLM.integral_comp_comm (hint_P _ hg)).symm
    rw [← e1, ← e2, h g hg]
  obtain ⟨a₁, b₁, h1⟩ :=
    exists_ae_eq_doubleAntideriv_add_affine (hre_loc hu) (hre_loc hPloc) hEqRe
  obtain ⟨a₂, b₂, h2⟩ :=
    exists_ae_eq_doubleAntideriv_add_affine (him_loc hu) (him_loc hPloc) hEqIm
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ → ℂ, W = fun x =>
      ((doubleAntideriv (fun y => (c y * u y).re) x + (a₁ * x + b₁) : ℝ) : ℂ)
        + ((doubleAntideriv (fun y => (c y * u y).im) x + (a₂ * x + b₂) : ℝ) : ℂ) * Complex.I :=
    ⟨_, rfl⟩
  -- `W` is continuous and almost everywhere equal to `u`
  have haffine : ∀ a b : ℝ, Continuous fun x : ℝ => a * x + b := fun a b =>
    (continuous_const.mul continuous_id).add continuous_const
  have hcW : Continuous W := by
    rw [hWdef]
    exact ((Complex.continuous_ofReal.comp
        ((continuous_doubleAntideriv (hre_loc hPloc)).add (haffine a₁ b₁)))).add
      ((Complex.continuous_ofReal.comp
        ((continuous_doubleAntideriv (him_loc hPloc)).add (haffine a₂ b₂))).mul continuous_const)
  have hWae : u =ᵐ[volume] W := by
    filter_upwards [h1, h2] with x hx1 hx2
    have e : W x = ((u x).re : ℂ) + ((u x).im : ℂ) * Complex.I := by
      rw [hWdef, hx1, hx2]
    rw [e, Complex.re_add_im]
  -- replace the inhomogeneity by the *continuous* function `c·W`
  have hPQ : (fun x => c x * u x) =ᵐ[volume] fun x => c x * W x := by
    filter_upwards [hWae] with x hx
    rw [hx]
  have hQcont : Continuous fun x => c x * W x := hc.mul hcW
  -- name the two real components of `c·W`, so that they no longer mention `W` syntactically
  obtain ⟨Qre, hQredef⟩ : ∃ f : ℝ → ℝ, f = fun x => (c x * W x).re := ⟨_, rfl⟩
  obtain ⟨Qim, hQimdef⟩ : ∃ f : ℝ → ℝ, f = fun x => (c x * W x).im := ⟨_, rfl⟩
  have hQre : Continuous Qre := by
    rw [hQredef]; exact Complex.continuous_re.comp hQcont
  have hQim : Continuous Qim := by
    rw [hQimdef]; exact Complex.continuous_im.comp hQcont
  have hsum : ∀ x, ((Qre x : ℝ) : ℂ) + ((Qim x : ℝ) : ℂ) * Complex.I = c x * W x := by
    intro x
    rw [hQredef, hQimdef]
    exact Complex.re_add_im _
  have hDre : doubleAntideriv (fun y => (c y * u y).re) = doubleAntideriv Qre := by
    refine doubleAntideriv_congr_ae ?_
    filter_upwards [hPQ] with x hx
    rw [hQredef, hx]
  have hDim : doubleAntideriv (fun y => (c y * u y).im) = doubleAntideriv Qim := by
    refine doubleAntideriv_congr_ae ?_
    filter_upwards [hPQ] with x hx
    rw [hQimdef, hx]
  rw [hDre, hDim] at hWdef
  refine ⟨W, fun x =>
    (((∫ t in (0 : ℝ)..x, Qre t) + a₁ : ℝ) : ℂ)
      + (((∫ t in (0 : ℝ)..x, Qim t) + a₂ : ℝ) : ℂ) * Complex.I, ?_, ?_, hWae⟩
  · intro x
    have d1 : HasDerivAt (fun y => doubleAntideriv Qre y + (a₁ * y + b₁))
        ((∫ t in (0 : ℝ)..x, Qre t) + a₁) x := by
      refine (hasDerivAt_doubleAntideriv hQre x).add ?_
      simpa using ((hasDerivAt_id x).const_mul a₁).add_const b₁
    have d2 : HasDerivAt (fun y => doubleAntideriv Qim y + (a₂ * y + b₂))
        ((∫ t in (0 : ℝ)..x, Qim t) + a₂) x := by
      refine (hasDerivAt_doubleAntideriv hQim x).add ?_
      simpa using ((hasDerivAt_id x).const_mul a₂).add_const b₂
    rw [hWdef]
    exact d1.ofReal_comp.add (d2.ofReal_comp.mul_const Complex.I)
  · intro x
    have d1 : HasDerivAt (fun y => (∫ t in (0 : ℝ)..y, Qre t) + a₁) (Qre x) x :=
      (hasDerivAt_primitive_of_continuous hQre x).add_const a₁
    have d2 : HasDerivAt (fun y => (∫ t in (0 : ℝ)..y, Qim t) + a₂) (Qim x) x :=
      (hasDerivAt_primitive_of_continuous hQim x).add_const a₂
    have hd := d1.ofReal_comp.add (d2.ofReal_comp.mul_const Complex.I)
    rw [← hsum x]
    exact hd

end

end BookProof.WeakSecondDeriv
