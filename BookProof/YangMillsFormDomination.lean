import Mathlib
import BookProof.ChapterReferenceGap
import BookProof.Sirk.ChapterTempleContinuumGap

/-!
# Chapter YangMillsFormDomination — form domination and comparison thresholds

`softmodes.md` Phase 4 asks for the step that turns a *comparison of quadratic forms* into a
*gap*: if the Yang–Mills form `q_W` dominates the reference form `q_ref` of
`BookProof.ReferenceGap`,

`q_W(c) ≥ c₁ · q_ref(c) − c₂ · ‖c‖²   (c₁ > 0, c₂ ∈ ℝ)`   on the Gauss–polynomial core,

then this chapter bounds the form below on the whole core and on the reference-vacuum
complement. The difference of those LOWER thresholds is `c₁ · Δ_ref`; this alone does not
separate the two actual lowest eigenvalues of `q_W`.

## What is proved, and what is not

Proved here:

* `coreForm_ge_vacuum` — the reference form is minimized at the vacuum (`μ₀ ≤ μ_n` for every
  multi-index `n`), so domination bounds the *ground* level too, not only the excited one;
* `ground_bound`, `excited_bound` — the two level bounds
  `c₁μ₀ − c₂` and `c₁(μ₀ + Δ_ref) − c₂`, the second one on the vacuum-orthogonal sector;
* `certified_separation` — the algebraic identity between these comparison thresholds;
  `certified_gap_pos` proves their difference positive, not a physical spectral gap;
* `formDomination_self` — the certificate is inhabited (`q_ref` dominates itself), so the
  structure is not vacuous;
* `FormDomination.add_nonneg` — the Phase-4 monotonicity step in the form the interaction
  enters it: domination survives the addition of any pointwise nonnegative form;
* `magneticColForm`, `magneticColForm_eq_position`, `magneticColForm_nonneg` — the magnetic
  two-field term read through the **momentum column** `momentumCol` of
  `BookProof.TempleContinuumGap` (§4): a model product is expressed as a momentum convolution
  and its form is nonnegative, giving a candidate comparison `q_mag` that
  `FormDomination.add_nonneg` absorbs.  No position-space product of distributions is formed
  anywhere in the chain;
* `magneticColFormT4`, `magneticColFormT4_eq_position`, `magneticColFormT4_nonneg` — the same
  on the 4-torus `(ℤ/n)⁴`, through `momentumColT4` of §5 of that chapter: the four-dimensional
  magnetic form is a convolution over conserved four-momentum and is nonnegative.

**Not** proved here, and not claimed: that the Yang–Mills form `q_W` actually dominates
`q_ref` with some `c₁ > 0`.  That is the analytic content of Phase 4 (`ym_form_dominates_href`
in `softmodes.md` §4.3, deliverable `BookProof.YangMillsFormDomination.lean`): it needs the
magnetic potential's coercivity of Phase 2 and the polymer/perturbation control of
`ChapterFockFieldPerturbation`/`ChapterFockInteractionStability` on the same core.  What this
chapter supplies is comparison-threshold arithmetic. An actual inner excitation-gap theorem
also needs an upper bound on the target ground energy and control of the target ground
projection. For the final outer-vacuum gap, prove an absolute `h ≥ m I`, `m > 0`, instead.
The convolution models here do not identify the physical QYM field-strength polynomial;
spatial-derivative elimination by convolution is the NS/QG device only.
-/

noncomputable section

namespace BookProof.YangMillsFormDomination

open Finset
open BookProof.ReferenceGap

variable {d : ℕ}

/-! ## The certificate -/

/-- **A form-domination certificate.**  `q` dominates the reference form of the anisotropic
oscillator with ratio `c₁ > 0` up to the additive shift `c₂‖c‖²`, on the whole core. -/
structure FormDomination (ω : Fin d → ℝ) (q : CoreCoeff d → ℝ) where
  /-- the domination ratio. -/
  c₁ : ℝ
  /-- the additive shift. -/
  c₂ : ℝ
  /-- the ratio is positive, i.e. the comparison is not trivial. -/
  hc₁ : 0 < c₁
  /-- the domination inequality itself, on the Gauss–polynomial core. -/
  dom : ∀ c : CoreCoeff d, c₁ * coreForm ω c - c₂ * coreNormSq c ≤ q c

/-- The certificate is inhabited: the reference form dominates itself with `c₁ = 1`, `c₂ = 0`. -/
def formDomination_self (ω : Fin d → ℝ) : FormDomination ω (coreForm ω) where
  c₁ := 1
  c₂ := 0
  hc₁ := one_pos
  dom := fun _ => by rw [one_mul, zero_mul, sub_zero]

/-! ## The reference form is minimized at the vacuum -/

/-- The excitation energy is nonnegative, so the vacuum multi-index is a ground level of the
reference form: `μ₀ ‖c‖² ≤ q_ref(c)` for every core state. -/
theorem coreForm_ge_vacuum (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i) (c : CoreCoeff d) :
    refEnergy ω 0 * coreNormSq c ≤ coreForm ω c := by
  rw [coreForm, coreNormSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hdiff := refEnergy_sub_zero ω n
  have hnn : 0 ≤ ∑ i, ω i * (n i : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hω i).le (by positivity)
  have hvac : refEnergy ω 0 ≤ refEnergy ω n := by linarith
  exact mul_le_mul_of_nonneg_right hvac (by positivity)

/-! ## The two level bounds -/

/-- Whole-core lower threshold. Transferring this to a spectral lower bound requires the
form/closure realization; it is not an upper bound on the target ground energy. -/
theorem ground_bound (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i) {q : CoreCoeff d → ℝ}
    (D : FormDomination ω q) (c : CoreCoeff d) :
    (D.c₁ * refEnergy ω 0 - D.c₂) * coreNormSq c ≤ q c := by
  have h1 : D.c₁ * (refEnergy ω 0 * coreNormSq c) ≤ D.c₁ * coreForm ω c :=
    mul_le_mul_of_nonneg_left (coreForm_ge_vacuum ω hω c) D.hc₁.le
  have h2 := D.dom c
  nlinarith

/-- **Excited level.**  On the vacuum-orthogonal sector the reference form is at least
`(μ₀ + Δ_ref)‖c‖²` (`href_spectral_gap`), so domination pushes the level up by `Δ_ref`. -/
theorem excited_bound [Nonempty (Fin d)] (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i)
    {q : CoreCoeff d → ℝ} (D : FormDomination ω q) (c : CoreCoeff d) (hc : c 0 = 0) :
    (D.c₁ * (refEnergy ω 0 + refGap ω) - D.c₂) * coreNormSq c ≤ q c := by
  have h1 : D.c₁ * ((refEnergy ω 0 + refGap ω) * coreNormSq c) ≤ D.c₁ * coreForm ω c :=
    mul_le_mul_of_nonneg_left (href_spectral_gap ω hω c hc) D.hc₁.le
  have h2 := D.dom c
  nlinarith

/-! ## The certified separation -/

/-- The two comparison thresholds differ by `c₁ · Δ_ref`. This algebraic identity does not
bound a spectral gap: `ground_bound` is a lower bound, not a ground-energy upper bound. -/
theorem certified_separation [Nonempty (Fin d)] {ω : Fin d → ℝ} {q : CoreCoeff d → ℝ}
    (D : FormDomination ω q) :
    (D.c₁ * refEnergy ω 0 - D.c₂) + D.c₁ * refGap ω
      = D.c₁ * (refEnergy ω 0 + refGap ω) - D.c₂ := by
  ring

/-- The difference of comparison thresholds is positive whenever the reference gap is. -/
theorem certified_gap_pos [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {q : CoreCoeff d → ℝ} (D : FormDomination ω q) :
    0 < D.c₁ * (refEnergy ω 0 + refGap ω) - D.c₂
      - (D.c₁ * refEnergy ω 0 - D.c₂) := by
  have hg : 0 < refGap ω := refGap_pos hω
  nlinarith [D.hc₁, hg]

/-! ## A concrete inhabitant: the free (quadratic) part

The free part of the Weyl-gauge Yang–Mills Hamiltonian is `½ Σᵢ πᵢ²` — quadratic.  In
oscillator units its quadratic form on the Hermite core is the *degree* form
`∑ n, (∑ i, nᵢ)‖c n‖²`: the form of `−Δ`, where the vacuum carries degree `0` and each
excitation of the `i`-th coordinate adds `1`.  This section proves that the degree form
really does dominate the reference form — a genuine, non-self-referential inhabitant of
`FormDomination`, and the concrete instance of the Phase-4 comparison on which the whole
circle of ideas rests.  The admissible ratio is any `c₁` with `0 < c₁` and `c₁ ωᵢ ≤ 1`; such a
`c₁` always exists (`exists_free_ratio`). -/

/-- The *degree* form `∑ n, (∑ i, nᵢ) ‖c n‖²`: the quadratic form of the free kinetic part
`−Δ` in oscillator units. -/
def degreeForm (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (∑ i, (n i : ℝ)) * ‖c n‖ ^ 2

/-- The degree form is nonnegative. -/
theorem degreeForm_nonneg (c : CoreCoeff d) : 0 ≤ degreeForm c :=
  Finset.sum_nonneg fun n _ =>
    mul_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)) (sq_nonneg _)

/-- The zero-point shift is exactly what separates the two forms: for `c₁ωᵢ ≤ 1`,
`c₁(μ(n) − μ(0)) = c₁ ∑ ωᵢ nᵢ ≤ ∑ nᵢ`, so the degree of `n` pays for the excitation energy. -/
theorem scaled_refEnergy_sub_zero_le_degree (ω : Fin d → ℝ) {c₁ : ℝ}
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (n : Fin d → ℕ) :
    c₁ * refEnergy ω n - c₁ * refEnergy ω 0 ≤ ∑ i, (n i : ℝ) := by
  have hsub := refEnergy_sub_zero ω n
  have hsum : c₁ * (∑ i, ω i * (n i : ℝ)) ≤ ∑ i, (n i : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hℓ : (c₁ * ω i) * (n i : ℝ) ≤ 1 * (n i : ℝ) :=
      mul_le_mul_of_nonneg_right (hω₁ i) (by positivity)
    nlinarith
  calc c₁ * refEnergy ω n - c₁ * refEnergy ω 0
      = c₁ * (refEnergy ω n - refEnergy ω 0) := by ring
    _ = c₁ * (∑ i, ω i * (n i : ℝ)) := by rw [hsub]
    _ ≤ ∑ i, (n i : ℝ) := hsum

/-- **The free quadratic part inhabits the certificate.**  With `c₁ > 0` and `c₁ωᵢ ≤ 1`, the
degree form dominates the reference form with ratio `c₁` and shift `c₂ = c₁μ₀`. -/
def freeFormDomination (ω : Fin d → ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    FormDomination ω (degreeForm (d := d)) where
  c₁ := c₁
  c₂ := c₁ * refEnergy ω 0
  hc₁ := hc₁
  dom := by
    intro c
    rw [degreeForm, coreForm, coreNormSq, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have hpt := scaled_refEnergy_sub_zero_le_degree ω hω₁ n
    have hnn : (0 : ℝ) ≤ ‖c n‖ ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hpt hnn
    nlinarith

/-- An admissible ratio always exists: `c₁ = (1 + ∑ᵢ ωᵢ)⁻¹` is positive and satisfies
`c₁ωᵢ ≤ 1`, since `ωᵢ ≤ ∑ⱼ ωⱼ`. -/
theorem exists_free_ratio [Nonempty (Fin d)] (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ i, c₁ * ω i ≤ 1 := by
  have hsumpos : 0 < ∑ j, ω j := Finset.sum_pos (fun j _ => hω j) Finset.univ_nonempty
  refine ⟨(1 + ∑ j, ω j)⁻¹, inv_pos.mpr (by linarith), fun i => ?_⟩
  have hle : ω i ≤ ∑ j, ω j :=
    Finset.single_le_sum (s := Finset.univ) (f := ω) (fun j _ => (hω j).le) (Finset.mem_univ i)
  have h1 : (1 + ∑ j, ω j)⁻¹ * ω i = ω i / (1 + ∑ j, ω j) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [h1]
  exact (div_le_one (by linarith)).mpr (by linarith)

/-- **A concrete certified gap.**  On the vacuum-orthogonal sector the free kinetic form is at
least `c₁Δ_ref · ‖c‖²`: the degree form inherits the reference gap. -/
theorem degreeForm_ge_gap [Nonempty (Fin d)] (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    c₁ * refGap ω * coreNormSq c ≤ degreeForm c := by
  have h := excited_bound ω hω (freeFormDomination (d := d) ω hc₁ hω₁) c hc
  have hc1 : (freeFormDomination (d := d) ω hc₁ hω₁).c₁ = c₁ := rfl
  have hc2 : (freeFormDomination (d := d) ω hc₁ hω₁).c₂ = c₁ * refEnergy ω 0 := rfl
  rw [hc1, hc2] at h
  have hshift : c₁ * (refEnergy ω 0 + refGap ω) - c₁ * refEnergy ω 0 = c₁ * refGap ω := by
    ring
  rwa [hshift] at h

/-! ## The interacting (quartic) part

`H_W = ½ Σᵢ πᵢ² + ½ Σ_a B_a²`: the magnetic term is a sum of *squares* of the field operators, so
its quadratic form is nonnegative — `⟨ψ, ½Σ B_a² ψ⟩ = ½ Σ_a ‖B_a ψ‖² ≥ 0`.  Consequently the
interacting part can never spoil the Phase-4 comparison: domination is monotone under adding a
nonnegative form.  That is the entire role the quartic term plays at the level of quadratic
forms, and it is what the certificate needs.

What stays open, and is not claimed: identifying the Yang–Mills magnetic form with a specific
quartic form on the core and controlling its *negative* normal-ordered pieces (`a†a†a†a`,
`a†a†aa` against the diagonal `:N²:` part).  Those are the analytic estimates of
`ChapterFockInteractionStability`; the monotonicity below is what makes them the only remaining
ingredient. -/

/-- **Domination is monotone in the dominated form**: if `q ≤ q'` pointwise on the core, a
certificate for `q` is a certificate for `q'` with the same constants.  Applied to
`q' = q_free + q_mag` with `q_mag ≥ 0`, this is the statement that the quartic Yang–Mills term
cannot break the comparison. -/
def FormDomination.mono {ω : Fin d → ℝ} {q q' : CoreCoeff d → ℝ}
    (D : FormDomination ω q) (hqq' : ∀ c : CoreCoeff d, q c ≤ q' c) : FormDomination ω q' where
  c₁ := D.c₁
  c₂ := D.c₂
  hc₁ := D.hc₁
  dom := fun c => (D.dom c).trans (hqq' c)

/-- A quartic, normal-ordered interaction form: `∑ n, (∑ i, nᵢ)² ‖c n‖²`, the square of the
particle degree — a two-particle `:N²:` term of the kind the magnetic potential produces. -/
def quarticDegreeForm (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (∑ i, (n i : ℝ)) ^ 2 * ‖c n‖ ^ 2

/-- The quartic interaction form is nonnegative. -/
theorem quarticDegreeForm_nonneg (c : CoreCoeff d) : 0 ≤ quarticDegreeForm c :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Free plus interacting part.**  Adding the quartic term to the free degree form preserves
the certificate: `degreeForm + quarticDegreeForm` dominates the reference form with the same
`c₁`, `c₂`. -/
def interactingFormDomination (ω : Fin d → ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    FormDomination ω (fun c => degreeForm c + quarticDegreeForm c) :=
  (freeFormDomination (d := d) ω hc₁ hω₁).mono fun c => by
    have := quarticDegreeForm_nonneg c
    linarith

/-- **The gap survives the interaction.**  On the vacuum-orthogonal sector the free-plus-quartic
form is still at least `c₁Δ_ref · ‖c‖²`. -/
theorem interactingForm_ge_gap [Nonempty (Fin d)] (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    c₁ * refGap ω * coreNormSq c ≤ degreeForm c + quarticDegreeForm c := by
  have hfree := degreeForm_ge_gap (d := d) ω hω hc₁ hω₁ c hc
  have hint := quarticDegreeForm_nonneg c
  linarith

/-! ## The two-field same-point product, through the momentum column

The interaction above is fed in as an abstract nonnegative form.  This section supplies the
concrete object on the lattice side, and it does so in the shape the chain consumes: the
magnetic term is the **momentum column** `momentumCol` of §4 of `BookProof.TempleContinuumGap`.

`momentumCol (F·F) k i` is the one-particle matrix of multiplication by the same-point
product of two outer fields; its entries depend only on the momentum transfer `k − i` and are
themselves a convolution `n⁻² Σ_{p+q = k−i} F̂(p) F̂(q)` over **conserved momentum**.  The form
`magneticColForm` that Phase 4 evaluates is the momentum-space sum against that column; by
Plancherel it equals `n` times the position-space form of the same-point product, and by the
positivity of a real field's square it is nonnegative.  So the interaction enters Phase 4 as
an object that is a convolution at every stage, and `FormDomination.add_nonneg` is the only
form-domination input it has to satisfy — there is no position-space product anywhere in the
chain. -/

section MagneticMomentumColumn

open scoped ComplexConjugate
open BookProof.TempleContinuumGap

variable {n : ℕ} [NeZero n]

/-- **Domination is preserved by adding a nonnegative form.**  This is the Phase-4 step in the
form the interaction enters it: the magnetic term only has to be nonnegative, and the
certificate's constants survive unchanged. -/
def FormDomination.add_nonneg {ω : Fin d → ℝ} {q : CoreCoeff d → ℝ} (D : FormDomination ω q)
    (qMag : CoreCoeff d → ℝ) (hMag : ∀ c : CoreCoeff d, 0 ≤ qMag c) :
    FormDomination ω (fun c => q c + qMag c) :=
  D.mono fun c => by linarith [hMag c]

/-- **The magnetic two-field form, read through the momentum column**: the Phase-4 form of the
same-point product `F·F` of a real outer field with itself, in momentum space. -/
noncomputable def magneticColForm (F : ZMod n → ℝ) (f : ZMod n → ℂ) : ℝ :=
  (∑ k : ZMod n, conj (ZMod.dft f k)
      * ∑ i : ZMod n, momentumCol (samePointProduct (realField F) (realField F)) k i
          * ZMod.dft f i).re

/-- **The momentum column of the two-field product is a convolution over conserved momentum**:
every coefficient of the magnetic form is `n⁻² Σ_{p+q = k−i} F̂(p) F̂(q)`. -/
theorem magneticColForm_conservedMomentum (F : ZMod n → ℝ) (k i : ZMod n) :
    momentumCol (samePointProduct (realField F) (realField F)) k i
      = ((n : ℂ)⁻¹) ^ 2 * ∑ p : ZMod n,
          ZMod.dft (realField F) p * ZMod.dft (realField F) (k - i - p) :=
  momentumCol_samePointProduct _ _ k i

/-- **The magnetic form is `n` times the position-space form of the same-point product** — the
Plancherel identification that lets Phase 4 consume the momentum column in place of a
position-space product. -/
theorem magneticColForm_eq_position (F : ZMod n → ℝ) (f : ZMod n → ℂ) :
    magneticColForm F f
      = (n : ℝ) * (∑ x : ZMod n,
          conj (f x) * samePointProduct (realField F) (realField F) x * f x).re := by
  have h := samePointProduct_form_eq_momentum (realField F) (realField F) f
  have hre : ((n : ℂ) * (∑ x : ZMod n,
      conj (f x) * samePointProduct (realField F) (realField F) x * f x)).re
        = (n : ℝ) * (∑ x : ZMod n,
          conj (f x) * samePointProduct (realField F) (realField F) x * f x).re := by
    rw [Complex.mul_re]
    simp
  unfold magneticColForm
  rw [h, hre]

/-- **The magnetic two-field term is a nonnegative form.**  For a real outer field `F` the
momentum-column form of `F·F` is `n Σ_x F(x)²‖f x‖² ≥ 0`: the interaction is exactly the kind
of perturbation `FormDomination.add_nonneg` absorbs, and no coincident-point product of
distributions is regularised anywhere. -/
theorem magneticColForm_nonneg (F : ZMod n → ℝ) (f : ZMod n → ℂ) : 0 ≤ magneticColForm F f := by
  rw [magneticColForm_eq_position]
  have hpos := samePointProduct_real_self_form_nonneg F f
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact mul_nonneg hn hpos

/-! ### The same chain on the 4-torus

The physical dimension is four, and §5 of `BookProof.TempleContinuumGap` carries the whole
construction over: the characters of `(ℤ/n)⁴` are products of the one-dimensional ones, the
momentum column is `momentumColT4`, and conserved momentum is four-dimensional.  The
Phase-4 form of the magnetic term in four dimensions is therefore the same object with
`n` replaced by `n⁴`; it is nonnegative for a real field, which is all
`FormDomination.add_nonneg` asks. -/

/-- **The magnetic two-field form on the 4-torus**, read through `momentumColT4`. -/
noncomputable def magneticColFormT4 (F : Torus4 (n := n) → ℝ)
    (f : Torus4 (n := n) → ℂ) : ℝ :=
  (∑ k : Torus4 (n := n), conj (dftT4 f k)
      * ∑ i : Torus4 (n := n),
          momentumColT4 (samePointProductT4 (realFieldT4 F) (realFieldT4 F)) k i * dftT4 f i).re

/-- **The 4-torus magnetic form is `n⁴` times the position-space form of the two-field
product** — Plancherel in four dimensions. -/
theorem magneticColFormT4_eq_position (F : Torus4 (n := n) → ℝ)
    (f : Torus4 (n := n) → ℂ) :
    magneticColFormT4 F f
      = ((n : ℝ) ^ 4) * (∑ x : Torus4 (n := n),
          conj (f x) * samePointProductT4 (realFieldT4 F) (realFieldT4 F) x * f x).re := by
  have h := samePointProductT4_form_eq_momentum (realFieldT4 F) (realFieldT4 F) f
  have hpow : ((n : ℂ) ^ 4) = (((n : ℝ) ^ 4 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_pow]
  have hre : (((n : ℂ) ^ 4) * (∑ x : Torus4 (n := n),
      conj (f x) * samePointProductT4 (realFieldT4 F) (realFieldT4 F) x * f x)).re
        = ((n : ℝ) ^ 4) * (∑ x : Torus4 (n := n),
          conj (f x) * samePointProductT4 (realFieldT4 F) (realFieldT4 F) x * f x).re := by
    rw [hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold magneticColFormT4
  rw [h, hre]

/-- **The magnetic two-field term on the 4-torus is a nonnegative form**: the four-dimensional
instance of the `q_mag` that `FormDomination.add_nonneg` absorbs. -/
theorem magneticColFormT4_nonneg (F : Torus4 (n := n) → ℝ)
    (f : Torus4 (n := n) → ℂ) : 0 ≤ magneticColFormT4 F f := by
  rw [magneticColFormT4_eq_position]
  have hpos := samePointProductT4_real_self_form_nonneg F f
  exact mul_nonneg (by positivity) hpos

end MagneticMomentumColumn

end BookProof.YangMillsFormDomination
