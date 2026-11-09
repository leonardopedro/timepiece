/-
# S0: the complexification of the Gaussian Dirichlet operator

`ChapterYangMillsGaussForm` proves that `T = −Δ + x·∇` is a densely defined symmetric operator on
the *real* Hilbert space `L²(γ dx)`.  The Friedrichs construction of `ChapterYangMillsFriedrichs`
and the deficiency-space analysis of essential self-adjointness both live on a **complex** Hilbert
space, so this module builds the `ℂ`-valued operator and its form.

Mathlib has no complexification of real Hilbert spaces and no bundled `Lp.re`/`Lp.im` maps, so the
complex operator is not a transport of `gaussOp`: it is defined by the same formula on `ℂ`-valued
representatives and related to the real operator component by component.

**What is proved here.**

* `gaussDirichletC` — `f ↦ −f'' + x f'` for `f : ℝ → ℂ`, with the *real* derivative (`deriv` is
  `ℝ`-linear), so it is `ℂ`-linear in `f`;
* `deriv_re`/`deriv_im` — the real derivative commutes with taking the real and imaginary parts
  (`Complex.reCLM`/`imCLM` composed with `HasDerivAt`), and `gaussDirichletC_re`/`_im` — the complex
  operator restricts to the real operator on both components:
  `(T f).re = T (f.re)` and `(T f).im = T (f.im)`;
* `continuous_gaussDirichletC`, `hasCompactSupport_gaussDirichletC`, and `memLp_gaussDirichletC` —
  the complex operator maps smooth compactly supported functions into `L²(γ dx)`, assembled from the
  real membership theorem through `memLp_re_im_iff`;
* `integral_gaussWeight_innerC_comm` — **symmetry of the weighted pairing**,
  `∫ γ ⟪T F, G⟫ = ∫ γ ⟪F, T G⟫`: both sides split into real and imaginary parts, and each of the
  four resulting real pairings is the real chapter's `integral_gaussDirichlet_mul_comm`;
* `gaussCoreC`, `gaussCoreRepC`, `gaussDirichletC_congr_ae`, `gaussDirichletC_add`,
  `gaussDirichletC_const_mul`, and the `ℂ`-linear partial map `gaussOpC` with the `C²` core as
  domain — the operator on `Lp ℂ 2 gaussMeasure` classes;
* `gaussOpC_inner_comm` — symmetry on the core, `⟪T f, g⟫_ℂ = ⟪f, T g⟫_ℂ`;
* `gaussOpC_inner_self_eq_re` — the real part of the diagonal is
  `gaussForm F.re F.re + gaussForm F.im F.im`, and `gaussOpC_quadForm_nonneg` — **positivity**: the
  Friedrichs hypothesis `0 ≤ (⟪f, T f⟫_ℂ).re`;
* `gaussOpC_symmetric` and `gaussOpC_form_closable` — the Friedrichs handoff: the two hypotheses in
  the form `ChapterYangMillsFriedrichs` consumes, and its `form_closable` applied to `gaussOpC`.

**What is not proved here.**  Self-adjointness (equivalently essential self-adjointness) of the
closure is absent exactly as in the real chapter: it needs deficiency indices of
`−f'' + x f' = ±i f` or `H¹(γ)` elliptic regularity, neither of which this mathlib provides.  See
the S0 entry of `softmodes.md`.
-/
import BookProof.Qym.ChapterYangMillsGaussForm
import BookProof.Qym.ChapterYangMillsFriedrichs

namespace BookProof.YangMillsGaussFormComplex

open BookProof.YangMillsGaussForm BookProof.YangMillsMehlerBridge BookProof.YangMillsMehlerLp
  BookProof.YangMillsFriedrichs BookProof.FarisLavine MeasureTheory

open scoped ComplexConjugate ComplexInnerProductSpace

noncomputable section

/-! ## `−Δ + x·∇` on complex-valued functions -/

/-- The complex-valued `−Δ + x·∇` on representatives, `f ↦ −f'' + x f'` — the same formula as
`gaussDirichlet`, read for `ℂ`-valued functions.  The derivative is the real one (`deriv` is
`ℝ`-linear), which is what makes the map `ℂ`-linear in `f`. -/
def gaussDirichletC (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(deriv (fun y => deriv f y) x) + (x : ℂ) * deriv f x

/-- **The real derivative commutes with taking real parts.**  `re` is a continuous linear map
`ℂ →L[ℝ] ℝ`, so its composition with a `HasDerivAt` is again one with the composed derivative. -/
theorem deriv_re (f : ℝ → ℂ) {x : ℝ} (h : DifferentiableAt ℝ f x) :
    deriv (fun y => (f y).re) x = (deriv f x).re := by
  have hd : HasDerivAt f (deriv f x) x := h.hasDerivAt
  have hcomp : HasDerivAt (fun y => (f y).re) ((deriv f x).re) x := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    simpa using this
  exact hcomp.deriv

/-- **The real derivative commutes with taking imaginary parts.** -/
theorem deriv_im (f : ℝ → ℂ) {x : ℝ} (h : DifferentiableAt ℝ f x) :
    deriv (fun y => (f y).im) x = (deriv f x).im := by
  have hd : HasDerivAt f (deriv f x) x := h.hasDerivAt
  have hcomp : HasDerivAt (fun y => (f y).im) ((deriv f x).im) x := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd
    simpa using this
  exact hcomp.deriv

/-- **The complex operator splits into real and imaginary parts.**  On the real part it is the real
operator applied to the real part of the representative. -/
theorem gaussDirichletC_re {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    (gaussDirichletC f x).re = gaussDirichlet (fun y => (f y).re) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hfd : DifferentiableAt ℝ f x := hf1.differentiable (by norm_num) x
  have hdd : DifferentiableAt ℝ (deriv f) x := hd1.differentiable (by norm_num) x
  have h2 : deriv (fun y => deriv (fun z => (f z).re) y) x = (deriv (deriv f) x).re := by
    have hfun : deriv (fun z => (f z).re) = fun z => (deriv f z).re := by
      funext z
      exact deriv_re f (hf1.differentiable (by norm_num) z)
    rw [hfun]
    exact deriv_re (deriv f) hdd
  simp only [gaussDirichlet, gaussDirichletC, Complex.add_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, h2, deriv_re f (x := x) hfd]

/-- **The complex operator splits into real and imaginary parts.**  On the imaginary part it is the
real operator applied to the imaginary part of the representative. -/
theorem gaussDirichletC_im {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    (gaussDirichletC f x).im = gaussDirichlet (fun y => (f y).im) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hfd : DifferentiableAt ℝ f x := hf1.differentiable (by norm_num) x
  have hdd : DifferentiableAt ℝ (deriv f) x := hd1.differentiable (by norm_num) x
  have h2 : deriv (fun y => deriv (fun z => (f z).im) y) x = (deriv (deriv f) x).im := by
    have hfun : deriv (fun z => (f z).im) = fun z => (deriv f z).im := by
      funext z
      exact deriv_im f (hf1.differentiable (by norm_num) z)
    rw [hfun]
    exact deriv_im (deriv f) hdd
  simp only [gaussDirichlet, gaussDirichletC, Complex.add_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, h2, deriv_im f (x := x) hfd]

/-- **The complex operator is continuous on `C²` functions**: `f''` is continuous because `f'` is
`C¹`, and `f'` is continuous because `f` is `C²`. -/
theorem continuous_gaussDirichletC {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) :
    Continuous (gaussDirichletC f) := by
  have hd2 : Continuous (fun x => deriv (fun y => deriv f y) x) :=
    (hf.deriv' : ContDiff ℝ 1 (deriv f)).continuous_deriv le_rfl
  have hd1 : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  exact ((hd2.neg).add (Complex.continuous_ofReal.mul hd1))

/-- **The complex operator preserves compact support**: both summands are supported in the support
of `f'` and `f''`. -/
theorem hasCompactSupport_gaussDirichletC {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (gaussDirichletC f) := by
  have h2 : HasCompactSupport (fun x => -(deriv (fun y => deriv f y) x)) :=
    (HasCompactSupport.deriv (HasCompactSupport.deriv hf)).neg
  have h1 : HasCompactSupport (fun x : ℝ => (x : ℂ) * deriv f x) :=
    (HasCompactSupport.deriv hf).mul_left (f := fun x : ℝ => (x : ℂ))
  have hsum := h2.add h1
  simpa only [gaussDirichletC, Pi.add_apply] using hsum

/-- Transporting `MemLp` along an a.e. equality.  (This mathlib has `MemLp.toLp_congr` but no
`MemLp.congr`.) -/
theorem memLp_congr_ae {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E} {p : ENNReal}
    (h : MemLp f p gaussMeasure) (hfg : f =ᵐ[gaussMeasure] g) : MemLp g p gaussMeasure :=
  ⟨h.1.congr hfg, by rw [← eLpNorm_congr_ae hfg]; exact h.2⟩

/-- **The complex operator maps smooth compactly supported functions into `L²(γ dx)`.**  The real
part of the image is the real operator applied to `f.re` and the imaginary part is the real operator
applied to `f.im`, so `memLp_re_im_iff` plus `memLp_gaussDirichlet` proves both at once. -/
theorem memLp_gaussDirichletC {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    MemLp (gaussDirichletC f) 2 gaussMeasure := by
  have hre : ContDiff ℝ 2 (fun y => (f y).re) := by
    have := (Complex.reCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hf
    simpa using this
  have him : ContDiff ℝ 2 (fun y => (f y).im) := by
    have := (Complex.imCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hf
    simpa using this
  have hrec : HasCompactSupport (fun y => (f y).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have himc : HasCompactSupport (fun y => (f y).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  refine memLp_re_im_iff.mp ⟨?_, ?_⟩
  · exact memLp_congr_ae (f := gaussDirichlet (fun y => (f y).re))
      (g := fun x => (gaussDirichletC f x).re) (p := 2)
      (memLp_gaussDirichlet hre hrec)
      (Filter.Eventually.of_forall fun x => (gaussDirichletC_re hf x).symm)
  · exact memLp_congr_ae (f := gaussDirichlet (fun y => (f y).im))
      (g := fun x => (gaussDirichletC f x).im) (p := 2)
      (memLp_gaussDirichlet him himc)
      (Filter.Eventually.of_forall fun x => (gaussDirichletC_im hf x).symm)

/-! ## Symmetry of the complex pairing

The Friedrichs hypotheses consume symmetry of the *operator*.  On representatives that is
`∫ γ · ⟪T f, g⟫ = ∫ γ · ⟪f, T g⟫`, where `⟪a, b⟫ = b * conj a`.  Both inner products split
into products of real and imaginary parts, and each of the four resulting real pairings is the real
symmetry `integral_gaussDirichlet_mul_comm` read with `f.re`/`f.im`/`g.re`/`g.im`; the complex
integral is then reassembled from its real and imaginary parts with `integral_re`/`integral_im`.

Everything here is an integral against `volume` with the explicit weight `γ` — no `gaussMeasure` is
involved — exactly as in the real chapter. -/

/-- **The real operator is continuous on `C²` functions.**  The real chapter only needs this
inline; the pairing estimates here want it on its own, for `f.re` and `f.im`. -/
theorem continuous_gaussDirichlet {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (gaussDirichlet f) := by
  have hd2 : Continuous (fun x => deriv (fun y => deriv f y) x) :=
    (hf.deriv' : ContDiff ℝ 1 (deriv f)).continuous_deriv le_rfl
  have hd1 : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  exact hd2.neg.add (continuous_id.mul hd1)

/-- **Weighted products with one compactly supported factor are integrable.**  The weight is
continuous, so a continuous multiple of a compactly supported function is a continuous compactly
supported function. -/
theorem integrable_gaussWeight_mul {a b : ℝ → ℝ} (ha : Continuous a)
    (hac : HasCompactSupport a) (hb : Continuous b) :
    Integrable (fun x => gaussWeight x * a x * b x) := by
  refine ((contDiff_gaussWeight.continuous.mul ha).mul hb).integrable_of_hasCompactSupport ?_
  convert hac.mul_left (f := fun x => gaussWeight x * b x) using 1
  ext x
  simp only [Pi.mul_apply]
  ring

/-- **The complex pairing integral is integrable.**  `gaussDirichletC F` is continuous and
compactly supported, `G` is continuous, and the weight is continuous, so the whole product is a
continuous compactly supported function. -/
theorem integrable_gaussWeight_innerC {F G : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hG : Continuous G) :
    Integrable (fun x => (gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫) := by
  have hw : Continuous fun x : ℝ => (gaussWeight x : ℂ) :=
    Complex.continuous_ofReal.comp contDiff_gaussWeight.continuous
  have hin : Continuous fun x => ⟪gaussDirichletC F x, G x⟫ :=
    (continuous_gaussDirichletC hF).inner hG
  have hcs : HasCompactSupport fun x => ⟪gaussDirichletC F x, G x⟫ := by
    have hconj : HasCompactSupport fun x => (starRingEnd ℂ) (gaussDirichletC F x) :=
      (hasCompactSupport_gaussDirichletC hFc).comp_left (g := starRingEnd ℂ) (by simp)
    have h := hconj.mul_right (f' := G)
    simpa only [Pi.mul_apply, RCLike.inner_apply'] using h
  exact (hw.mul hin).integrable_of_hasCompactSupport
    (hcs.mul_left (f := fun x => (gaussWeight x : ℂ)))

/-- **The pairing integral is integrable with the operator in the second slot.**  This is the mirror
of `integrable_gaussWeight_innerC`: now the compact support comes from `gaussDirichletC G`. -/
theorem integrable_gaussWeight_innerC' {F G : ℝ → ℂ} (hF : Continuous F) (hG : ContDiff ℝ 2 G)
    (hGc : HasCompactSupport G) :
    Integrable (fun x => (gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫) := by
  have hw : Continuous fun x : ℝ => (gaussWeight x : ℂ) :=
    Complex.continuous_ofReal.comp contDiff_gaussWeight.continuous
  have hin : Continuous fun x => ⟪F x, gaussDirichletC G x⟫ :=
    hF.inner (continuous_gaussDirichletC hG)
  have hcs : HasCompactSupport fun x => ⟪F x, gaussDirichletC G x⟫ := by
    have h := (hasCompactSupport_gaussDirichletC hGc).mul_left
      (f := fun x => (starRingEnd ℂ) (F x))
    simpa only [Pi.mul_apply, RCLike.inner_apply'] using h
  exact (hw.mul hin).integrable_of_hasCompactSupport
    (hcs.mul_left (f := fun x => (gaussWeight x : ℂ)))

/-- **The complex operator is symmetric.**  With `⟪a, b⟫ = b * conj a` on the representatives, the
weighted pairing of `gaussDirichletC F` against `G` equals the weighted pairing of `F` against
`gaussDirichletC G`.  Both sides are `∫ γ (T F.re · G.re + T F.im · G.im)` after reading real parts
and `∫ γ (T F.re · G.im − T F.im · G.re)` after reading imaginary parts, and the real symmetry
turns each of those four real pairings into the same expression with the roles of `F` and `G`
exchanged. -/
theorem integral_gaussWeight_innerC_comm {F G : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ 2 G) (hGc : HasCompactSupport G) :
    ∫ x, (gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫
      = ∫ x, (gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫ := by
  have hFr : ContDiff ℝ 2 (fun y => (F y).re) := by
    have := (Complex.reCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hF
    simpa using this
  have hFi : ContDiff ℝ 2 (fun y => (F y).im) := by
    have := (Complex.imCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hF
    simpa using this
  have hGr : ContDiff ℝ 2 (fun y => (G y).re) := by
    have := (Complex.reCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hG
    simpa using this
  have hGi : ContDiff ℝ 2 (fun y => (G y).im) := by
    have := (Complex.imCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hG
    simpa using this
  have hFrc : HasCompactSupport (fun y => (F y).re) :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hFic : HasCompactSupport (fun y => (F y).im) :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have hGrc : HasCompactSupport (fun y => (G y).re) :=
    hGc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hGic : HasCompactSupport (fun y => (G y).im) :=
    hGc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have iL := integrable_gaussWeight_innerC hF hFc hG.continuous
  have iR := integrable_gaussWeight_innerC' hF.continuous hG hGc
  have hGc' : Continuous fun x => (G x).re := Complex.continuous_re.comp hG.continuous
  have hGs : Continuous fun x => (G x).im := Complex.continuous_im.comp hG.continuous
  have hFre : Continuous fun x => (F x).re := Complex.continuous_re.comp hF.continuous
  have hFim : Continuous fun x => (F x).im := Complex.continuous_im.comp hF.continuous
  refine Complex.ext ?_ ?_
  · have hLre : (∫ x, (gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).re
        = ∫ x, ((gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).re :=
      (Complex.reCLM.integral_comp_comm iL).symm
    have hRre : (∫ x, (gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).re
        = ∫ x, ((gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).re :=
      (Complex.reCLM.integral_comp_comm iR).symm
    rw [hLre, hRre]
    have hL : ∀ x, ((gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).re
        = gaussWeight x * (gaussDirichlet (fun y => (F y).re) x * (G x).re
            + gaussDirichlet (fun y => (F y).im) x * (G x).im) := by
      intro x
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, RCLike.inner_apply,
        Complex.mul_re, Complex.conj_re, Complex.conj_im, gaussDirichletC_re hF x,
        gaussDirichletC_im hF x]
      ring
    have hR : ∀ x, ((gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).re
        = gaussWeight x * ((F x).re * gaussDirichlet (fun y => (G y).re) x
            + (F x).im * gaussDirichlet (fun y => (G y).im) x) := by
      intro x
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, RCLike.inner_apply,
        Complex.mul_re, Complex.conj_re, Complex.conj_im, gaussDirichletC_re hG x,
        gaussDirichletC_im hG x]
      ring
    have h1 : Integrable fun x => gaussWeight x * gaussDirichlet (fun y => (F y).re) x * (G x).re :=
      integrable_gaussWeight_mul (continuous_gaussDirichlet hFr)
        (hasCompactSupport_gaussDirichlet hFrc) hGc'
    have h2 : Integrable fun x => gaussWeight x * gaussDirichlet (fun y => (F y).im) x * (G x).im :=
      integrable_gaussWeight_mul (continuous_gaussDirichlet hFi)
        (hasCompactSupport_gaussDirichlet hFic) hGs
    have h3 : Integrable fun x => gaussWeight x * (F x).re * gaussDirichlet (fun y => (G y).re) x :=
      integrable_gaussWeight_mul hFre hFrc (continuous_gaussDirichlet hGr)
    have h4 : Integrable fun x => gaussWeight x * (F x).im * gaussDirichlet (fun y => (G y).im) x :=
      integrable_gaussWeight_mul hFim hFic (continuous_gaussDirichlet hGi)
    calc ∫ x, ((gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).re
        = ∫ x, gaussWeight x * (gaussDirichlet (fun y => (F y).re) x * (G x).re
            + gaussDirichlet (fun y => (F y).im) x * (G x).im) :=
          integral_congr_ae (Filter.Eventually.of_forall hL)
      _ = ∫ x, (gaussWeight x * gaussDirichlet (fun y => (F y).re) x * (G x).re
            + gaussWeight x * gaussDirichlet (fun y => (F y).im) x * (G x).im) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x, gaussWeight x * gaussDirichlet (fun y => (F y).re) x * (G x).re)
            + ∫ x, gaussWeight x * gaussDirichlet (fun y => (F y).im) x * (G x).im :=
          integral_add h1 h2
      _ = (∫ x, gaussWeight x * (F x).re * gaussDirichlet (fun y => (G y).re) x)
            + ∫ x, gaussWeight x * (F x).im * gaussDirichlet (fun y => (G y).im) x := by
          rw [integral_gaussDirichlet_mul_comm hFr hFrc hGr hGrc,
            integral_gaussDirichlet_mul_comm hFi hFic hGi hGic]
      _ = ∫ x, (gaussWeight x * (F x).re * gaussDirichlet (fun y => (G y).re) x
            + gaussWeight x * (F x).im * gaussDirichlet (fun y => (G y).im) x) :=
          (integral_add h3 h4).symm
      _ = ∫ x, gaussWeight x * ((F x).re * gaussDirichlet (fun y => (G y).re) x
            + (F x).im * gaussDirichlet (fun y => (G y).im) x) :=
          (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)).symm
      _ = ∫ x, ((gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).re :=
          (integral_congr_ae (Filter.Eventually.of_forall hR)).symm
  · have hLim : (∫ x, (gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).im
        = ∫ x, ((gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).im :=
      (Complex.imCLM.integral_comp_comm iL).symm
    have hRim : (∫ x, (gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).im
        = ∫ x, ((gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).im :=
      (Complex.imCLM.integral_comp_comm iR).symm
    rw [hLim, hRim]
    have hL : ∀ x, ((gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).im
        = gaussWeight x * (gaussDirichlet (fun y => (F y).re) x * (G x).im
            - gaussDirichlet (fun y => (F y).im) x * (G x).re) := by
      intro x
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, RCLike.inner_apply,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, gaussDirichletC_re hF x,
        gaussDirichletC_im hF x]
      ring
    have hR : ∀ x, ((gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).im
        = gaussWeight x * ((F x).re * gaussDirichlet (fun y => (G y).im) x
            - (F x).im * gaussDirichlet (fun y => (G y).re) x) := by
      intro x
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, RCLike.inner_apply,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, gaussDirichletC_re hG x,
        gaussDirichletC_im hG x]
      ring
    have h1 : Integrable fun x => gaussWeight x * gaussDirichlet (fun y => (F y).re) x * (G x).im :=
      integrable_gaussWeight_mul (continuous_gaussDirichlet hFr)
        (hasCompactSupport_gaussDirichlet hFrc) hGs
    have h2 : Integrable fun x => gaussWeight x * gaussDirichlet (fun y => (F y).im) x * (G x).re :=
      integrable_gaussWeight_mul (continuous_gaussDirichlet hFi)
        (hasCompactSupport_gaussDirichlet hFic) hGc'
    have h3 : Integrable fun x => gaussWeight x * (F x).re * gaussDirichlet (fun y => (G y).im) x :=
      integrable_gaussWeight_mul hFre hFrc (continuous_gaussDirichlet hGi)
    have h4 : Integrable fun x => gaussWeight x * (F x).im * gaussDirichlet (fun y => (G y).re) x :=
      integrable_gaussWeight_mul hFim hFic (continuous_gaussDirichlet hGr)
    calc ∫ x, ((gaussWeight x : ℂ) * ⟪gaussDirichletC F x, G x⟫).im
        = ∫ x, gaussWeight x * (gaussDirichlet (fun y => (F y).re) x * (G x).im
            - gaussDirichlet (fun y => (F y).im) x * (G x).re) :=
          integral_congr_ae (Filter.Eventually.of_forall hL)
      _ = ∫ x, (gaussWeight x * gaussDirichlet (fun y => (F y).re) x * (G x).im
            - gaussWeight x * gaussDirichlet (fun y => (F y).im) x * (G x).re) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x, gaussWeight x * gaussDirichlet (fun y => (F y).re) x * (G x).im)
            - ∫ x, gaussWeight x * gaussDirichlet (fun y => (F y).im) x * (G x).re :=
          integral_sub h1 h2
      _ = (∫ x, gaussWeight x * (F x).re * gaussDirichlet (fun y => (G y).im) x)
            - ∫ x, gaussWeight x * (F x).im * gaussDirichlet (fun y => (G y).re) x := by
          rw [integral_gaussDirichlet_mul_comm hFr hFrc hGi hGic,
            integral_gaussDirichlet_mul_comm hFi hFic hGr hGrc]
      _ = ∫ x, (gaussWeight x * (F x).re * gaussDirichlet (fun y => (G y).im) x
            - gaussWeight x * (F x).im * gaussDirichlet (fun y => (G y).re) x) :=
          (integral_sub h3 h4).symm
      _ = ∫ x, gaussWeight x * ((F x).re * gaussDirichlet (fun y => (G y).im) x
            - (F x).im * gaussDirichlet (fun y => (G y).re) x) :=
          (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)).symm
      _ = ∫ x, ((gaussWeight x : ℂ) * ⟪F x, gaussDirichletC G x⟫).im :=
          (integral_congr_ae (Filter.Eventually.of_forall hR)).symm

/-! ## The operator on `L²(γ dx)` classes

Everything above is a statement about *representatives*.  The operator the Friedrichs construction
acts on lives on `Lp ℂ 2 gaussMeasure` classes, so this section mirrors the real chapter's class
layer: the `C²`-compactly-supported core as a `ℂ`-submodule, a chosen representative,
well-definedness on classes (`gaussDirichletC_congr_ae`), additivity and `ℂ`-homogeneity, and
finally `gaussOpC` as a `ℂ`-linear partial map with the `C²` core as domain. -/

/-- The compactly supported `C²` core of `L²(γ dx)`, as a complex submodule: the classes having a
representative of class `C²` with compact support. -/
def gaussCoreC : Submodule ℂ (Lp ℂ 2 gaussMeasure) where
  carrier := {f | ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ HasCompactSupport F
    ∧ ⇑f =ᵐ[gaussMeasure] F}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, by
    filter_upwards [Lp.coeFn_zero (μ := gaussMeasure) (p := 2) (E := ℂ)] with x hx using hx⟩
  add_mem' := by
    rintro f g ⟨F, hF, hFc, hFe⟩ ⟨G, hG, hGc, hGe⟩
    exact ⟨F + G, hF.add hG, hFc.add hGc, (Lp.coeFn_add f g).trans (hFe.add hGe)⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hFc, hFe⟩
    refine ⟨fun x => c * F x, contDiff_const.mul hF, hFc.mul_left (f := fun _ => c), ?_⟩
    exact (Lp.coeFn_smul c f).trans ((hFe.const_smul c).trans
      (Filter.Eventually.of_forall fun x => by simp))

/-- A chosen representative of a complex core class: `C²` with compact support. -/
noncomputable def gaussCoreRepC (f : gaussCoreC) : ℝ → ℂ :=
  Classical.choose (show ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ HasCompactSupport F
    ∧ ⇑(f : Lp ℂ 2 gaussMeasure) =ᵐ[gaussMeasure] F from f.2)

/-- The chosen representative has the three properties the core promises. -/
theorem gaussCoreRepC_spec (f : gaussCoreC) :
    ContDiff ℝ 2 (gaussCoreRepC f) ∧ HasCompactSupport (gaussCoreRepC f)
      ∧ (f : Lp ℂ 2 gaussMeasure) =ᵐ[gaussMeasure] gaussCoreRepC f :=
  Classical.choose_spec (show ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ HasCompactSupport F
    ∧ ⇑(f : Lp ℂ 2 gaussMeasure) =ᵐ[gaussMeasure] F from f.2)

/-- **A continuous `ℂ`-valued function that is zero `γ`-a.e. is zero.**  Same argument as in the
real chapter: the zero set is closed, its complement is a null open set, and `gaussMeasure` is
positive on nonempty opens. -/
theorem eq_of_ae_eq_gaussMeasure_C {f g : ℝ → ℂ} (h : f =ᵐ[gaussMeasure] g)
    (hf : Continuous f) (hg : Continuous g) : f = g :=
  Measure.eq_of_ae_eq h hf hg

/-- **`gaussDirichletC` respects a.e. equality**, so the representative choice is invisible. -/
theorem gaussDirichletC_congr_ae {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (h : F =ᵐ[gaussMeasure] G) : gaussDirichletC F = gaussDirichletC G := by
  rw [eq_of_ae_eq_gaussMeasure_C h hF hG]

/-- **The complex operator is additive** on `C²` functions. -/
theorem gaussDirichletC_add {F G : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    gaussDirichletC (F + G) = gaussDirichletC F + gaussDirichletC G := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' : ContDiff ℝ 1 (deriv F)).differentiable (by norm_num)
  have hdG' : Differentiable ℝ (deriv G) :=
    (hG.deriv' : ContDiff ℝ 1 (deriv G)).differentiable (by norm_num)
  funext x
  have hd : deriv (F + G) = deriv F + deriv G :=
    funext fun y => deriv_add (hdF y) (hdG y)
  have h2 : deriv (fun y => deriv (F + G) y) x
      = deriv (fun y => deriv F y) x + deriv (fun y => deriv G y) x := by
    rw [show (fun y => deriv (F + G) y) = deriv F + deriv G from hd]
    exact deriv_add (hdF' x) (hdG' x)
  simp only [gaussDirichletC, Pi.add_apply, h2, deriv_add (hdF x) (hdG x)]
  ring

/-- **The complex operator is `ℂ`-homogeneous** on `C²` functions: the derivative is real-linear, so
multiplying the function by `c : ℂ` multiplies the image by `c`. -/
theorem gaussDirichletC_const_mul {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (c : ℂ) :
    gaussDirichletC (fun x => c * F x) = fun x => c * gaussDirichletC F x := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' : ContDiff ℝ 1 (deriv F)).differentiable (by norm_num)
  have h1 : (fun y => deriv (fun z => c * F z) y) = fun y => c * deriv F y := by
    funext y
    exact deriv_const_mul c (hdF y)
  funext x
  have h2 : deriv (fun y => deriv (fun z => c * F z) y) x
      = c * deriv (fun y => deriv F y) x := by
    rw [h1]
    exact deriv_const_mul c (hdF' x)
  simp only [gaussDirichletC, h2, deriv_const_mul c (hdF x)]
  ring

/-- `toLp` commutes with a complex scalar multiple of the representative. -/
theorem memLp_toLp_const_mul_C (c : ℂ) {G : ℝ → ℂ} (hG : MemLp G 2 gaussMeasure)
    (h : MemLp (fun x => c * G x) 2 gaussMeasure) :
    h.toLp (fun x => c * G x) = c • hG.toLp G := by
  apply Lp.ext
  have h1 : ⇑(h.toLp (fun x => c * G x)) =ᵐ[gaussMeasure] (fun x => c * G x) :=
    MemLp.coeFn_toLp h
  have h2 : ⇑(c • hG.toLp G) =ᵐ[gaussMeasure] c • ⇑(hG.toLp G) := Lp.coeFn_smul c _
  have h3 : (c • ⇑(hG.toLp G)) =ᵐ[gaussMeasure] (fun x => c * G x) :=
    ((MemLp.coeFn_toLp hG).const_smul c).trans
      (Filter.Eventually.of_forall fun x => by simp)
  exact h1.trans (h2.trans h3).symm

/-- The operator applied to a complex core class: `T` of the chosen representative. -/
noncomputable def gaussOpFunC (f : gaussCoreC) : Lp ℂ 2 gaussMeasure :=
  MemLp.toLp (gaussDirichletC (gaussCoreRepC f))
    (memLp_gaussDirichletC (gaussCoreRepC_spec f).1 (gaussCoreRepC_spec f).2.1)

/-- **`gaussOpFunC` computes `T` on any admissible representative.** -/
theorem gaussOpFunC_eq_toLp {f : gaussCoreC} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hFe : (f : Lp ℂ 2 gaussMeasure) =ᵐ[gaussMeasure] F) :
    gaussOpFunC f = MemLp.toLp (gaussDirichletC F) (memLp_gaussDirichletC hF hFc) := by
  have hds : gaussDirichletC (gaussCoreRepC f) = gaussDirichletC F :=
    gaussDirichletC_congr_ae (gaussCoreRepC_spec f).1.continuous hF.continuous
      ((gaussCoreRepC_spec f).2.2.symm.trans hFe)
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun hds))

/-- **The operator is additive on the complex core.** -/
theorem gaussOpFunC_add (f g : gaussCoreC) :
    gaussOpFunC (f + g) = gaussOpFunC f + gaussOpFunC g := by
  have hf := gaussCoreRepC_spec f
  have hg := gaussCoreRepC_spec g
  have hsum : ((f + g : gaussCoreC) : Lp ℂ 2 gaussMeasure) =ᵐ[gaussMeasure]
      gaussCoreRepC f + gaussCoreRepC g := by
    have h1 : ((f + g : gaussCoreC) : Lp ℂ 2 gaussMeasure)
        = (f : Lp ℂ 2 gaussMeasure) + g := Submodule.coe_add f g
    rw [h1]
    exact (Lp.coeFn_add _ _).trans (hf.2.2.add hg.2.2)
  calc gaussOpFunC (f + g)
      = MemLp.toLp (gaussDirichletC (gaussCoreRepC f + gaussCoreRepC g))
          (memLp_gaussDirichletC (hf.1.add hg.1) (hf.2.1.add hg.2.1)) :=
        gaussOpFunC_eq_toLp (f := f + g) (F := gaussCoreRepC f + gaussCoreRepC g)
          (hf.1.add hg.1) (hf.2.1.add hg.2.1) hsum
    _ = MemLp.toLp (gaussDirichletC (gaussCoreRepC f) + gaussDirichletC (gaussCoreRepC g))
          ((memLp_gaussDirichletC hf.1 hf.2.1).add (memLp_gaussDirichletC hg.1 hg.2.1)) :=
        MemLp.toLp_congr _ _
          (Filter.Eventually.of_forall (congrFun (gaussDirichletC_add hf.1 hg.1)))
    _ = MemLp.toLp (gaussDirichletC (gaussCoreRepC f)) (memLp_gaussDirichletC hf.1 hf.2.1)
          + MemLp.toLp (gaussDirichletC (gaussCoreRepC g))
            (memLp_gaussDirichletC hg.1 hg.2.1) :=
        MemLp.toLp_add _ _
    _ = gaussOpFunC f + gaussOpFunC g := by
        rw [gaussOpFunC_eq_toLp (f := f) (F := gaussCoreRepC f) hf.1 hf.2.1 hf.2.2,
          gaussOpFunC_eq_toLp (f := g) (F := gaussCoreRepC g) hg.1 hg.2.1 hg.2.2]

/-- **The operator is `ℂ`-homogeneous on the complex core.** -/
theorem gaussOpFunC_smul (c : ℂ) (f : gaussCoreC) :
    gaussOpFunC (c • f) = c • gaussOpFunC f := by
  have hf := gaussCoreRepC_spec f
  have hsm : ((c • f : gaussCoreC) : Lp ℂ 2 gaussMeasure) =ᵐ[gaussMeasure]
      fun x => c * gaussCoreRepC f x := by
    have h1 : ((c • f : gaussCoreC) : Lp ℂ 2 gaussMeasure)
        = c • (f : Lp ℂ 2 gaussMeasure) := Submodule.coe_smul c f
    rw [h1]
    exact (Lp.coeFn_smul c _).trans ((hf.2.2.const_smul c).trans
      (Filter.Eventually.of_forall fun x => by simp))
  have hc : ContDiff ℝ 2 (fun x => c * gaussCoreRepC f x) :=
    contDiff_const.mul hf.1
  have hcc : HasCompactSupport (fun x => c * gaussCoreRepC f x) :=
    hf.2.1.mul_left (f := fun _ => c)
  have hcG : MemLp (fun x => c * gaussDirichletC (gaussCoreRepC f) x) 2 gaussMeasure :=
    memLp_congr_ae ((memLp_gaussDirichletC hf.1 hf.2.1).const_smul c)
      (Filter.Eventually.of_forall fun x => by simp)
  calc gaussOpFunC (c • f)
      = MemLp.toLp (gaussDirichletC (fun x => c * gaussCoreRepC f x))
          (memLp_gaussDirichletC hc hcc) :=
        gaussOpFunC_eq_toLp (f := c • f) (F := fun x => c * gaussCoreRepC f x) hc hcc hsm
    _ = MemLp.toLp (fun x => c * gaussDirichletC (gaussCoreRepC f) x) hcG :=
        MemLp.toLp_congr _ _
          (Filter.Eventually.of_forall (congrFun (gaussDirichletC_const_mul hf.1 c)))
    _ = c • MemLp.toLp (gaussDirichletC (gaussCoreRepC f))
          (memLp_gaussDirichletC hf.1 hf.2.1) :=
        memLp_toLp_const_mul_C c _ hcG
    _ = c • gaussOpFunC f := by
        rw [gaussOpFunC_eq_toLp (f := f) (F := gaussCoreRepC f) hf.1 hf.2.1 hf.2.2]

/-- The complex operator as a `ℂ`-linear map on its core. -/
noncomputable def gaussOpLinearMapC : gaussCoreC →ₗ[ℂ] Lp ℂ 2 gaussMeasure where
  toFun := gaussOpFunC
  map_add' := gaussOpFunC_add
  map_smul' := gaussOpFunC_smul

/-- **`T = −Δ + x·∇` as a partially defined `ℂ`-linear operator on `L²(γ dx)`**, with the
`C²`-compactly-supported core as domain.  This is the object the Friedrichs construction and the
deficiency analysis act on. -/
noncomputable def gaussOpC : Lp ℂ 2 gaussMeasure →ₗ.[ℂ] Lp ℂ 2 gaussMeasure where
  domain := gaussCoreC
  toFun := gaussOpLinearMapC

/-- On the core, `gaussOpC` is `gaussOpFunC`, by definition. -/
theorem gaussOpC_apply (f : gaussCoreC) : gaussOpC f = gaussOpFunC f := rfl

/-! ## Symmetry and positivity on classes -/

/-- **Integration against `γ dx` is a weighted Lebesgue integral** for `ℂ`-valued integrands. -/
theorem integral_gaussMeasure_eq_integral_gaussWeight_C (h : ℝ → ℂ) :
    ∫ x, h x ∂gaussMeasure = ∫ x, (gaussWeight x : ℂ) * h x := by
  rw [gaussMeasure, integral_withDensity_eq_integral_toReal_smul measurable_gaussDensity
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussWeight, ENNReal.toReal_ofReal (sq_nonneg (gaussRoot x))]
  rw [Complex.real_smul]

/-- **`gaussOpC` is symmetric on its core.**  The matrix element `⟪T f, g⟫` is the weighted pairing
`∫ γ ⟪T F, G⟫` and the mirror one is `∫ γ ⟪F, T G⟫`; `integral_gaussWeight_innerC_comm` identifies
them. -/
theorem gaussOpC_inner_comm (f g : gaussCoreC) :
    inner ℂ (gaussOpC f) (g : Lp ℂ 2 gaussMeasure)
      = inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC g) := by
  have hf := gaussCoreRepC_spec f
  have hg := gaussCoreRepC_spec g
  have hmemf := memLp_gaussDirichletC hf.1 hf.2.1
  have hmemg := memLp_gaussDirichletC hg.1 hg.2.1
  have hL : inner ℂ (gaussOpC f) (g : Lp ℂ 2 gaussMeasure)
      = ∫ x, (gaussWeight x : ℂ) *
          ⟪gaussDirichletC (gaussCoreRepC f) x, gaussCoreRepC g x⟫ := by
    calc inner ℂ (gaussOpC f) (g : Lp ℂ 2 gaussMeasure)
        = ∫ x, ⟪⇑(MemLp.toLp (gaussDirichletC (gaussCoreRepC f)) hmemf) x,
            ⇑(g : Lp ℂ 2 gaussMeasure) x⟫ ∂gaussMeasure := by
          rw [gaussOpC_apply,
            gaussOpFunC_eq_toLp (f := f) (F := gaussCoreRepC f) hf.1 hf.2.1 hf.2.2,
            L2.inner_def]
      _ = ∫ x, (gaussWeight x : ℂ) *
            ⟪⇑(MemLp.toLp (gaussDirichletC (gaussCoreRepC f)) hmemf) x,
              ⇑(g : Lp ℂ 2 gaussMeasure) x⟫ :=
          integral_gaussMeasure_eq_integral_gaussWeight_C _
      _ = ∫ x, (gaussWeight x : ℂ) *
            ⟪gaussDirichletC (gaussCoreRepC f) x, gaussCoreRepC g x⟫ := by
          refine integral_congr_ae ?_
          filter_upwards [absolutelyContinuous_volume_gaussMeasure.ae_eq (MemLp.coeFn_toLp hmemf),
            absolutelyContinuous_volume_gaussMeasure.ae_eq hg.2.2] with x hx hy
          rw [hx, hy]
  have hR : inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC g)
      = ∫ x, (gaussWeight x : ℂ) *
          ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC g) x⟫ := by
    calc inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC g)
        = ∫ x, ⟪⇑(f : Lp ℂ 2 gaussMeasure) x,
            ⇑(MemLp.toLp (gaussDirichletC (gaussCoreRepC g)) hmemg) x⟫ ∂gaussMeasure := by
          rw [gaussOpC_apply,
            gaussOpFunC_eq_toLp (f := g) (F := gaussCoreRepC g) hg.1 hg.2.1 hg.2.2,
            L2.inner_def]
      _ = ∫ x, (gaussWeight x : ℂ) *
            ⟪⇑(f : Lp ℂ 2 gaussMeasure) x,
              ⇑(MemLp.toLp (gaussDirichletC (gaussCoreRepC g)) hmemg) x⟫ :=
          integral_gaussMeasure_eq_integral_gaussWeight_C _
      _ = ∫ x, (gaussWeight x : ℂ) *
            ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC g) x⟫ := by
          refine integral_congr_ae ?_
          filter_upwards [absolutelyContinuous_volume_gaussMeasure.ae_eq hf.2.2,
            absolutelyContinuous_volume_gaussMeasure.ae_eq (MemLp.coeFn_toLp hmemg)] with x hx hy
          rw [hx, hy]
  rw [hL, hR, integral_gaussWeight_innerC_comm hf.1 hf.2.1 hg.1 hg.2.1]

/-- **The diagonal of the complex quadratic form is a sum of two real Dirichlet forms.**  The
operator is symmetric, so the diagonal is real up to the pairing's convention; reading real parts,
`⟪f, T f⟫_ℂ` becomes `gaussForm F.re F.re + gaussForm F.im F.im`, a sum of two nonnegative reals. -/
theorem gaussOpC_inner_self_eq_re (f : gaussCoreC) :
    (inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC f)).re
      = gaussForm (fun x => (gaussCoreRepC f x).re) (fun x => (gaussCoreRepC f x).re)
        + gaussForm (fun x => (gaussCoreRepC f x).im) (fun x => (gaussCoreRepC f x).im) := by
  have hf := gaussCoreRepC_spec f
  have hmemf := memLp_gaussDirichletC hf.1 hf.2.1
  have hFr : ContDiff ℝ 2 (fun x => (gaussCoreRepC f x).re) := by
    have := (Complex.reCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hf.1
    simpa using this
  have hFi : ContDiff ℝ 2 (fun x => (gaussCoreRepC f x).im) := by
    have := (Complex.imCLM.contDiff (n := (2 : WithTop ℕ∞))).comp hf.1
    simpa using this
  have hFrc : HasCompactSupport (fun x => (gaussCoreRepC f x).re) :=
    hf.2.1.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hFic : HasCompactSupport (fun x => (gaussCoreRepC f x).im) :=
    hf.2.1.comp_left (g := fun z : ℂ => z.im) (by simp)
  have hinner : inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC f)
      = ∫ x, (gaussWeight x : ℂ) *
          ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC f) x⟫ := by
    calc inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC f)
        = ∫ x, ⟪⇑(f : Lp ℂ 2 gaussMeasure) x,
            ⇑(MemLp.toLp (gaussDirichletC (gaussCoreRepC f)) hmemf) x⟫ ∂gaussMeasure := by
          rw [gaussOpC_apply,
            gaussOpFunC_eq_toLp (f := f) (F := gaussCoreRepC f) hf.1 hf.2.1 hf.2.2,
            L2.inner_def]
      _ = ∫ x, (gaussWeight x : ℂ) *
            ⟪⇑(f : Lp ℂ 2 gaussMeasure) x,
              ⇑(MemLp.toLp (gaussDirichletC (gaussCoreRepC f)) hmemf) x⟫ :=
          integral_gaussMeasure_eq_integral_gaussWeight_C _
      _ = ∫ x, (gaussWeight x : ℂ) *
            ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC f) x⟫ := by
          refine integral_congr_ae ?_
          filter_upwards [absolutelyContinuous_volume_gaussMeasure.ae_eq hf.2.2,
            absolutelyContinuous_volume_gaussMeasure.ae_eq (MemLp.coeFn_toLp hmemf)] with x hx hy
          rw [hx, hy]
  have hint := integrable_gaussWeight_innerC' (F := gaussCoreRepC f)
    (G := gaussCoreRepC f) hf.1.continuous hf.1 hf.2.1
  have hre : (∫ x, (gaussWeight x : ℂ) *
        ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC f) x⟫).re
      = ∫ x, ((gaussWeight x : ℂ) *
        ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC f) x⟫).re :=
    (Complex.reCLM.integral_comp_comm hint).symm
  have hpt : ∀ x, ((gaussWeight x : ℂ) *
        ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC f) x⟫).re
      = gaussWeight x * (gaussDirichlet (fun y => (gaussCoreRepC f y).re) x
          * (gaussCoreRepC f x).re
          + gaussDirichlet (fun y => (gaussCoreRepC f y).im) x * (gaussCoreRepC f x).im) := by
    intro x
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, RCLike.inner_apply,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, gaussDirichletC_re hf.1 x,
      gaussDirichletC_im hf.1 x]
    ring
  have i1 : Integrable fun x => gaussWeight x *
      gaussDirichlet (fun y => (gaussCoreRepC f y).re) x * (gaussCoreRepC f x).re :=
    integrable_gaussWeight_mul (continuous_gaussDirichlet hFr)
      (hasCompactSupport_gaussDirichlet hFrc) (Complex.continuous_re.comp hf.1.continuous)
  have i2 : Integrable fun x => gaussWeight x *
      gaussDirichlet (fun y => (gaussCoreRepC f y).im) x * (gaussCoreRepC f x).im :=
    integrable_gaussWeight_mul (continuous_gaussDirichlet hFi)
      (hasCompactSupport_gaussDirichlet hFic) (Complex.continuous_im.comp hf.1.continuous)
  have hform1 : gaussForm (fun x => (gaussCoreRepC f x).re) (fun x => (gaussCoreRepC f x).re)
      = ∫ x, gaussWeight x * gaussDirichlet (fun y => (gaussCoreRepC f y).re) x
          * (gaussCoreRepC f x).re :=
    gaussForm_eq_integral_gaussDirichlet hFr hFrc (hFr.of_le (by norm_num))
  have hform2 : gaussForm (fun x => (gaussCoreRepC f x).im) (fun x => (gaussCoreRepC f x).im)
      = ∫ x, gaussWeight x * gaussDirichlet (fun y => (gaussCoreRepC f y).im) x
          * (gaussCoreRepC f x).im :=
    gaussForm_eq_integral_gaussDirichlet hFi hFic (hFi.of_le (by norm_num))
  calc (inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC f)).re
      = ∫ x, ((gaussWeight x : ℂ) *
          ⟪gaussCoreRepC f x, gaussDirichletC (gaussCoreRepC f) x⟫).re := by
        rw [hinner, hre]
    _ = ∫ x, gaussWeight x * (gaussDirichlet (fun y => (gaussCoreRepC f y).re) x
          * (gaussCoreRepC f x).re
          + gaussDirichlet (fun y => (gaussCoreRepC f y).im) x * (gaussCoreRepC f x).im) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x, (gaussWeight x * gaussDirichlet (fun y => (gaussCoreRepC f y).re) x
          * (gaussCoreRepC f x).re
          + gaussWeight x * gaussDirichlet (fun y => (gaussCoreRepC f y).im) x
            * (gaussCoreRepC f x).im) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = (∫ x, gaussWeight x * gaussDirichlet (fun y => (gaussCoreRepC f y).re) x
          * (gaussCoreRepC f x).re)
          + ∫ x, gaussWeight x * gaussDirichlet (fun y => (gaussCoreRepC f y).im) x
              * (gaussCoreRepC f x).im :=
        integral_add i1 i2
    _ = gaussForm (fun x => (gaussCoreRepC f x).re) (fun x => (gaussCoreRepC f x).re)
          + gaussForm (fun x => (gaussCoreRepC f x).im) (fun x => (gaussCoreRepC f x).im) := by
        rw [hform1, hform2]

/-- **`gaussOpC` is bounded below by `0` in the form sense** — the Friedrichs positivity
hypothesis, on the `ℂ`-valued core.  The real part of the diagonal is a sum of two Dirichlet forms
(`gaussOpC_inner_self_eq_re`), and each is nonnegative (`gaussForm_self_nonneg`). -/
theorem gaussOpC_quadForm_nonneg (f : gaussCoreC) :
    0 ≤ (inner ℂ (f : Lp ℂ 2 gaussMeasure) (gaussOpC f)).re := by
  rw [gaussOpC_inner_self_eq_re]
  exact add_nonneg (gaussForm_self_nonneg _) (gaussForm_self_nonneg _)

/-! ## The Friedrichs handoff

With the two hypotheses in hand — `SymmetricOn` and positivity of the quadratic form — the
Friedrichs machine of `ChapterYangMillsFriedrichs` applies verbatim: the form of `gaussOpC` is
closable, so its closure adds no spurious elements and the Friedrichs extension exists.  This is the
`ℂ`-valued counterpart of the real chapter's `gaussOp_isClosable`. -/

/-- **`gaussOpC` is symmetric on its core**, in the `SymmetricOn` form the Friedrichs chapter
consumes. -/
theorem gaussOpC_symmetric : SymmetricOn gaussCoreC gaussOpLinearMapC := gaussOpC_inner_comm

/-- **The form of `gaussOpC` is closable.**  This is `form_closable` applied to the symmetry and
positivity just proved: a sequence Cauchy in the form norm and tending to `0` in `L²(γ dx)` has form
norm tending to `0`. -/
theorem gaussOpC_form_closable (x : ℕ → gaussCoreC)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, formNormSq gaussOpLinearMapC (x p - x q) < ε)
    (hzero : Filter.Tendsto (fun n => ((x n : Lp ℂ 2 gaussMeasure))) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => formNormSq gaussOpLinearMapC (x n)) Filter.atTop (nhds 0) :=
  form_closable gaussOpC_symmetric gaussOpC_quadForm_nonneg x hCauchy hzero

end
end BookProof.YangMillsGaussFormComplex
