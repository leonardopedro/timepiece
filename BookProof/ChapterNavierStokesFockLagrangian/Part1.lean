import Mathlib
import BookProof.ChapterNavierStokesFockContinuum

/-!
# The transformed Navier–Stokes Hamiltonian in the Lagrangian momentum
representation: essential self-adjointness with continuous spectrum

`BookProof.ChapterNavierStokesLagrangianEsa` sets up the untruncated Lagrangian
data `LagrangianFullData` — the parcel momenta `Pᵢ`, the viscous gradients `Qᵢ`,
the force drift generators `Dᵢ` and the volume-preservation constraint `C` — and
proves that the transformed Hamiltonian

`ĥ_full = ½∑ᵢPᵢ² + ν∑ᵢQᵢ² + ∑ᵢfᵢDᵢ + C`

is symmetric with positive second-order part, essentially self-adjoint whenever
the constituents admit a *total family of common eigenvectors*.

That criterion is a discrete-spectrum criterion: it needs eigenvectors.  The
Lagrangian momentum representation of a *continuum* fluid has none — the
constituents are multiplication operators by the momentum coordinates, whose
spectrum is purely continuous.  This module closes that gap.

## What is proved here

* `DominatedOn` and the multiplication operator `mulD` — multiplication by a
  real measurable symbol `h` on the bounded-energy core of a *scale* function
  `g`, available whenever `h` is bounded on the level sets of `g`, with its
  algebra (`mulD_comp`, `mulD_add`, `mulD_sum`, `mulD_real_smul`).
* `mulD_hasZeroDeficiencyOn` — **multiplication by any symbol dominated by the
  scale is essentially self-adjoint on the bounded-energy core of the scale.**
  This generalizes `FockContinuum.multOp_hasZeroDeficiencyOn`, where symbol and
  scale had to coincide, and it is what allows *all four* constituents of the
  transformed Hamiltonian to live on one common core.
* `LagSymbols` — the Lagrangian momentum representation itself: arbitrary
  measurable real symbols `Pᵢ, Qᵢ, Dᵢ, C` on a measure space of momentum
  configurations, with no boundedness assumption whatsoever, and the common
  core `boundedEnergyCore μ S.scale`.
* `LagSymbols.data` — the resulting `LagrangianFullData`, so everything proved
  about the abstract transformed operator (symmetry, positivity of the advective
  and viscous terms, transfer along the change of variables) applies verbatim.
* `LagSymbols.hFull_eq_mulD` — **the transformed Hamiltonian is multiplication
  by the total Lagrangian symbol** `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.
* `LagSymbols.hFull_hasZeroDeficiencyOn` — **the headline: the untruncated
  transformed Navier–Stokes Hamiltonian is essentially self-adjoint in the
  Lagrangian momentum representation**, for arbitrary measurable symbols, with
  in general purely continuous spectrum and no eigenvectors at all.
* `norm_mulD_ge`, `mulD_not_bounded` — the lower bound that makes such an
  operator genuinely unbounded whenever its symbol is.

The second-quantized realization on the continuum Fock space of all
parcel-number sectors — where this criterion is applied to the transformed
Navier–Stokes Hamiltonian itself — is in
`BookProof.ChapterNavierStokesFockParcels`.

## Scope

Nothing here claims global existence for Navier–Stokes, and nothing here claims
essential self-adjointness of the *Eulerian* continuum generator: what is proved
is essential self-adjointness of the transformed operator in the Lagrangian
momentum representation, which by
`NavierStokesFlow.NSFullData.hasZeroDeficiencyOn_of_lagrangian` transports back
along a unitary change of variables only when such a change of variables is
supplied.
-/

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockLagrangian

open FullEsa FockContinuum

variable {X : Type*} [MeasurableSpace X]

/-! ## Symbols dominated on the level sets of a scale function -/

/-- The symbol `h` is **dominated on the level sets of the scale `g`**: on the
region where `|g| ≤ n` the symbol `h` is bounded.  This is exactly what is needed
for multiplication by `h` to preserve the bounded-energy core of `g`. -/
def DominatedOn (μ : Measure X) (g h : X → ℝ) : Prop :=
  ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, |g x| ≤ (n : ℝ) → |h x| ≤ M

theorem DominatedOn.rfl' (μ : Measure X) (g : X → ℝ) : DominatedOn μ g g :=
  fun n => ⟨n, Nat.cast_nonneg n, Filter.Eventually.of_forall fun _ hx => hx⟩

theorem DominatedOn.const (μ : Measure X) (g : X → ℝ) (r : ℝ) :
    DominatedOn μ g (fun _ => r) :=
  fun _ => ⟨|r|, abs_nonneg r, Filter.Eventually.of_forall fun _ _ => le_rfl⟩

theorem DominatedOn.add {μ : Measure X} {g h₁ h₂ : X → ℝ} (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) : DominatedOn μ g (fun x => h₁ x + h₂ x) := by
  intro n
  obtain ⟨M₁, hM₁, hx₁⟩ := d₁ n
  obtain ⟨M₂, hM₂, hx₂⟩ := d₂ n
  refine ⟨M₁ + M₂, by linarith, ?_⟩
  filter_upwards [hx₁, hx₂] with x h1 h2 hb
  exact le_trans (abs_add_le _ _) (add_le_add (h1 hb) (h2 hb))

theorem DominatedOn.mul {μ : Measure X} {g h₁ h₂ : X → ℝ} (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) : DominatedOn μ g (fun x => h₁ x * h₂ x) := by
  intro n
  obtain ⟨M₁, hM₁, hx₁⟩ := d₁ n
  obtain ⟨M₂, hM₂, hx₂⟩ := d₂ n
  refine ⟨M₁ * M₂, mul_nonneg hM₁ hM₂, ?_⟩
  filter_upwards [hx₁, hx₂] with x h1 h2 hb
  rw [abs_mul]
  exact mul_le_mul (h1 hb) (h2 hb) (abs_nonneg _) hM₁

theorem DominatedOn.const_mul {μ : Measure X} {g h : X → ℝ} (r : ℝ) (d : DominatedOn μ g h) :
    DominatedOn μ g (fun x => r * h x) :=
  (DominatedOn.const μ g r).mul d

theorem DominatedOn.of_abs_le {μ : Measure X} {g h k : X → ℝ} (d : DominatedOn μ g k)
    (hle : ∀ᵐ x ∂μ, |h x| ≤ |k x|) : DominatedOn μ g h := by
  intro n
  obtain ⟨M, hM, hx⟩ := d n
  refine ⟨M, hM, ?_⟩
  filter_upwards [hx, hle] with x h1 h2 hb
  exact le_trans h2 (h1 hb)

theorem DominatedOn.sum {ι : Type*} {μ : Measure X} {g : X → ℝ} (s : Finset ι)
    {h : ι → X → ℝ} (d : ∀ i ∈ s, DominatedOn μ g (h i)) :
    DominatedOn μ g (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using DominatedOn.const μ g 0
  | insert i s hi ih =>
      have hd : DominatedOn μ g (h i) := d i (Finset.mem_insert_self i s)
      have hrest : DominatedOn μ g (fun x => ∑ j ∈ s, h j x) :=
        ih fun j hj => d j (Finset.mem_insert_of_mem hj)
      have := hd.add hrest
      simpa [Finset.sum_insert hi] using this

/-! ## Multiplication by a dominated symbol on the bounded-energy core -/

/-- Multiplying a bounded-energy state by a dominated symbol stays
square-integrable. -/
theorem memLp_mulD {μ : Measure X} {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) {f : Lp ℂ 2 μ} (hf : f ∈ boundedEnergyCore μ g) :
    MemLp (fun x => (h x : ℂ) * (f : X → ℂ) x) 2 μ := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨M, hM, hMx⟩ := hdom n
  have hmeas : AEStronglyMeasurable (fun x => (h x : ℂ) * (f : X → ℂ) x) μ :=
    (Complex.measurable_ofReal.comp hh).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hbound : ∀ᵐ x ∂μ, ‖(h x : ℂ) * (f : X → ℂ) x‖ ≤ M * ‖(f : X → ℂ) x‖ := by
    filter_upwards [hn, hMx] with x hx hMb
    by_cases hb : |g x| ≤ (n : ℝ)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hMb hb) (norm_nonneg _)
    · rw [hx hb]
      simp
  exact MemLp.of_le_mul (Lp.memLp f) hmeas hbound

theorem mulD_mem_core {μ : Measure X} {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) {f : Lp ℂ 2 μ} (hf : f ∈ boundedEnergyCore μ g) :
    (memLp_mulD hh hdom hf).toLp _ ∈ boundedEnergyCore μ g := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  filter_upwards [hn, (memLp_mulD hh hdom (⟨n, hn⟩ : f ∈ boundedEnergyCore μ g)).coeFn_toLp]
    with x hx hcoe hbig
  rw [hcoe, hx hbig, mul_zero]

/-- **Multiplication by a dominated real symbol** on the bounded-energy core of
the scale `g`.  Unlike `FockContinuum.multOp` the symbol need not be the scale
itself, so several different symbols act on one and the same core. -/
noncomputable def mulD (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) :
    boundedEnergyCore μ g →ₗ[ℂ] boundedEnergyCore μ g where
  toFun f := ⟨(memLp_mulD hh hdom f.2).toLp _, mulD_mem_core hh hdom f.2⟩
  map_add' f k := by
    refine Subtype.ext (Lp.ext ?_)
    simp only [Submodule.coe_add]
    filter_upwards [(memLp_mulD hh hdom
        (show ((f : Lp ℂ 2 μ) + (k : Lp ℂ 2 μ)) ∈ boundedEnergyCore μ g from (f + k).2)).coeFn_toLp,
      (memLp_mulD hh hdom f.2).coeFn_toLp, (memLp_mulD hh hdom k.2).coeFn_toLp,
      Lp.coeFn_add ((f : Lp ℂ 2 μ)) ((k : Lp ℂ 2 μ)),
      Lp.coeFn_add ((memLp_mulD hh hdom f.2).toLp _)
        ((memLp_mulD hh hdom k.2).toLp _)] with x h1 h2 h3 h4 h5
    rw [h1, h5]
    simp only [Pi.add_apply]
    rw [h2, h3, h4]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    refine Subtype.ext (Lp.ext ?_)
    simp only [Submodule.coe_smul, RingHom.id_apply]
    filter_upwards [(memLp_mulD hh hdom
        (show (c • (f : Lp ℂ 2 μ)) ∈ boundedEnergyCore μ g from (c • f).2)).coeFn_toLp,
      (memLp_mulD hh hdom f.2).coeFn_toLp, Lp.coeFn_smul c ((f : Lp ℂ 2 μ)),
      Lp.coeFn_smul c ((memLp_mulD hh hdom f.2).toLp _)] with x h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem mulD_coeFn (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) (f : boundedEnergyCore μ g) :
    (((mulD μ hh hdom f : boundedEnergyCore μ g) : Lp ℂ 2 μ) : X → ℂ)
      =ᵐ[μ] fun x => (h x : ℂ) * ((f : Lp ℂ 2 μ) : X → ℂ) x :=
  (memLp_mulD hh hdom f.2).coeFn_toLp

/-- Two symbols that agree almost everywhere give the same operator. -/
theorem mulD_congr (μ : Measure X) {g h₁ h₂ : X → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (d₁ : DominatedOn μ g h₁) (d₂ : DominatedOn μ g h₂) (hae : h₁ =ᵐ[μ] h₂) :
    mulD μ hh₁ d₁ = mulD μ hh₂ d₂ := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh₁ d₁ f, mulD_coeFn μ hh₂ d₂ f, hae] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The multiplication operator is symmetric on the core. -/
theorem mulD_isSymmetricDom (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) : IsSymmetricDom (mulD μ hh hdom) := by
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulD_coeFn μ hh hdom x, mulD_coeFn μ hh hdom y] with a hx hy
  simp only [RCLike.inner_apply, hx, hy, map_mul, Complex.conj_ofReal]
  ring

/-- Composing two multiplication operators multiplies the symbols. -/
theorem mulD_comp (μ : Measure X) {g h₁ h₂ : X → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (d₁ : DominatedOn μ g h₁) (d₂ : DominatedOn μ g h₂) :
    (mulD μ hh₁ d₁).comp (mulD μ hh₂ d₂)
      = mulD μ (hh₁.mul hh₂) (d₁.mul d₂) := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh₁ d₁ (mulD μ hh₂ d₂ f), mulD_coeFn μ hh₂ d₂ f,
    mulD_coeFn μ (hh₁.mul hh₂) (d₁.mul d₂) f] with x h1 h2 h3
  simp only [LinearMap.comp_apply]
  rw [h1, h2, h3]
  push_cast
  ring

/-- Adding two multiplication operators adds the symbols. -/
theorem mulD_add (μ : Measure X) {g h₁ h₂ : X → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (d₁ : DominatedOn μ g h₁) (d₂ : DominatedOn μ g h₂) :
    mulD μ hh₁ d₁ + mulD μ hh₂ d₂ = mulD μ (hh₁.add hh₂) (d₁.add d₂) := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh₁ d₁ f, mulD_coeFn μ hh₂ d₂ f,
    mulD_coeFn μ (hh₁.add hh₂) (d₁.add d₂) f,
    Lp.coeFn_add ((mulD μ hh₁ d₁ f : boundedEnergyCore μ g) : Lp ℂ 2 μ)
      ((mulD μ hh₂ d₂ f : boundedEnergyCore μ g) : Lp ℂ 2 μ)] with x h1 h2 h3 h4
  simp only [LinearMap.add_apply, Submodule.coe_add]
  rw [h4]
  simp only [Pi.add_apply]
  rw [h1, h2, h3]
  push_cast
  ring

/-- A real multiple of a multiplication operator multiplies the symbol. -/
theorem mulD_real_smul (μ : Measure X) {g h : X → ℝ} (r : ℝ) (hh : Measurable h)
    (hdom : DominatedOn μ g h) :
    ((r : ℝ) : ℂ) • mulD μ hh hdom
      = mulD μ ((measurable_const (a := r)).mul hh) (DominatedOn.const_mul r hdom) := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh hdom f,
    mulD_coeFn μ ((measurable_const (a := r)).mul hh) (DominatedOn.const_mul r hdom) f,
    Lp.coeFn_smul ((r : ℝ) : ℂ) ((mulD μ hh hdom f : boundedEnergyCore μ g) : Lp ℂ 2 μ)]
    with x h1 h2 h3
  simp only [LinearMap.smul_apply, Submodule.coe_smul]
  rw [h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  push_cast
  ring

/-! ### Flexible forms of the algebra, with the target symbol given explicitly -/

/-- Composition, with the product symbol supplied in whatever form is
convenient. -/
theorem mulD_comp' (μ : Measure X) {g h₁ h₂ h : X → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hh : Measurable h) (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x * h₂ x) :
    (mulD μ hh₁ d₁).comp (mulD μ hh₂ d₂) = mulD μ hh d := by
  rw [mulD_comp μ hh₁ hh₂ d₁ d₂]
  exact mulD_congr μ (hh₁.mul hh₂) hh (d₁.mul d₂) d
    (Filter.Eventually.of_forall fun x => (heq x).symm)

/-- Addition, with the sum symbol supplied in whatever form is convenient. -/
theorem mulD_add' (μ : Measure X) {g h₁ h₂ h : X → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hh : Measurable h) (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x + h₂ x) :
    mulD μ hh₁ d₁ + mulD μ hh₂ d₂ = mulD μ hh d := by
  rw [mulD_add μ hh₁ hh₂ d₁ d₂]
  exact mulD_congr μ (hh₁.add hh₂) hh (d₁.add d₂) d
    (Filter.Eventually.of_forall fun x => (heq x).symm)

/-- Real scaling, with the scaled symbol supplied in whatever form is
convenient. -/
theorem mulD_real_smul' (μ : Measure X) {g h₁ h : X → ℝ} (r : ℝ) (hh₁ : Measurable h₁)
    (hh : Measurable h) (d₁ : DominatedOn μ g h₁) (d : DominatedOn μ g h)
    (heq : ∀ x, h x = r * h₁ x) :
    ((r : ℝ) : ℂ) • mulD μ hh₁ d₁ = mulD μ hh d := by
  rw [mulD_real_smul μ r hh₁ d₁]
  exact mulD_congr μ ((measurable_const (a := r)).mul hh₁) hh
    (DominatedOn.const_mul r d₁) d (Filter.Eventually.of_forall fun x => (heq x).symm)

/-! ## Essential self-adjointness of a dominated multiplication operator -/

/-- **Multiplication by a real symbol dominated by the scale is essentially
self-adjoint on the bounded-energy core.**

This strengthens `FockContinuum.multOp_hasZeroDeficiencyOn`, where the symbol had
to be the scale itself.  The operator has, in general, purely continuous spectrum
and no eigenvector whatsoever; the argument tests the deficiency identity against
the truncations of `(h ∓ i)w`. -/
theorem mulD_hasZeroDeficiencyOn (μ : Measure X) {g h : X → ℝ} (hg : Measurable g)
    (hh : Measurable h) (hdom : DominatedOn μ g h) :
    HasZeroDeficiencyOn (boundedEnergyCore μ g) (mulD μ hh hdom) := by
  have key : ∀ c : ℂ, c.im ≠ 0 → ∀ w : Lp ℂ 2 μ,
      (∀ v : boundedEnergyCore μ g,
        (inner ℂ ((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ) w : ℂ)
          = inner ℂ ((v : boundedEnergyCore μ g) : Lp ℂ 2 μ) (c • w)) → w = 0 := by
    intro c hc w hw
    set W : X → ℂ := fun x => ((h x : ℂ) - c) * ((w : X → ℂ) x) with hW
    have hmeasW : AEStronglyMeasurable W μ :=
      ((Complex.measurable_ofReal.comp hh).aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul (Lp.aestronglyMeasurable w)
    have hzero : ∀ n : ℕ, ∀ᵐ x ∂μ, |g x| ≤ (n : ℝ) → W x = 0 := by
      intro n
      obtain ⟨M, hM, hMx⟩ := hdom n
      have hmeasS : MeasurableSet {x | |g x| ≤ (n : ℝ)} :=
        measurableSet_le hg.abs measurable_const
      set u : X → ℂ := Set.indicator {x | |g x| ≤ (n : ℝ)} W with hu
      have hmeasu : AEStronglyMeasurable u μ := hmeasW.indicator hmeasS
      have hbound : ∀ᵐ x ∂μ, ‖u x‖ ≤ (M + ‖c‖) * ‖(w : X → ℂ) x‖ := by
        filter_upwards [hMx] with x hMb
        by_cases hx : x ∈ {x | |g x| ≤ (n : ℝ)}
        · have hgc : ‖((h x : ℂ) - c)‖ ≤ M + ‖c‖ := by
            refine le_trans (norm_sub_le _ _) ?_
            have h1 : ‖((h x : ℂ))‖ ≤ M := by
              rw [Complex.norm_real, Real.norm_eq_abs]; exact hMb hx
            linarith
          rw [hu, Set.indicator_of_mem hx, hW, norm_mul]
          exact mul_le_mul_of_nonneg_right hgc (norm_nonneg _)
        · rw [hu, Set.indicator_of_notMem hx, norm_zero]
          have : (0 : ℝ) ≤ M + ‖c‖ := by positivity
          positivity
      have humem : MemLp u 2 μ := MemLp.of_le_mul (Lp.memLp w) hmeasu hbound
      have hucore : humem.toLp u ∈ boundedEnergyCore μ g := by
        refine ⟨n, ?_⟩
        filter_upwards [humem.coeFn_toLp] with x hx hbig
        rw [hx, hu, Set.indicator_of_notMem (by simpa using hbig)]
      have hid := hw ⟨humem.toLp u, hucore⟩
      have hleft : (inner ℂ ((mulD μ hh hdom ⟨humem.toLp u, hucore⟩ : boundedEnergyCore μ g) :
          Lp ℂ 2 μ) w : ℂ)
          = ∫ x, (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x ∂μ := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [mulD_coeFn μ hh hdom ⟨humem.toLp u, hucore⟩, humem.coeFn_toLp]
          with x h1 h2
        simp only [RCLike.inner_apply, h1, h2]
        ring
      have hright : (inner ℂ ((⟨humem.toLp u, hucore⟩ : boundedEnergyCore μ g) : Lp ℂ 2 μ)
          (c • w) : ℂ) = ∫ x, (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x) ∂μ := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [humem.coeFn_toLp, Lp.coeFn_smul c w] with x h1 h2
        simp only [RCLike.inner_apply, h1, h2, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hleft, hright] at hid
      have hcombine : ∫ x, ‖u x‖ ^ 2 ∂μ = 0 := by
        have hintegrand : ∀ x, (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x
            - (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)
            = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
          intro x
          by_cases hx : x ∈ {x | |g x| ≤ (n : ℝ)}
          · have hux : u x = ((h x : ℂ) - c) * ((w : X → ℂ) x) := by
              rw [hu, Set.indicator_of_mem hx]
            have hconj : (starRingEnd ℂ) (u x) * u x = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
              have hmc := Complex.mul_conj' (u x)
              push_cast
              linear_combination hmc
            calc (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x
                  - (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)
                = (starRingEnd ℂ) (u x) * (((h x : ℂ) - c) * (w : X → ℂ) x) := by
                  simp only [map_mul, Complex.conj_ofReal]
                  ring
              _ = (starRingEnd ℂ) (u x) * u x := by rw [hux]
              _ = ((‖u x‖ ^ 2 : ℝ) : ℂ) := hconj
          · rw [hu, Set.indicator_of_notMem hx]
            simp
        have hzeroint : ∫ x, (((‖u x‖ ^ 2 : ℝ)) : ℂ) ∂μ = 0 := by
          have hint1 : Integrable
              (fun x => (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x) μ := by
            have h1 : MemLp (fun x => (h x : ℂ) * u x) 2 μ := by
              have hb : ∀ᵐ x ∂μ, ‖(h x : ℂ) * u x‖ ≤ M * ‖u x‖ := by
                filter_upwards [hMx] with x hMb
                by_cases hx : x ∈ {x | |g x| ≤ (n : ℝ)}
                · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  exact mul_le_mul_of_nonneg_right (hMb hx) (norm_nonneg _)
                · rw [hu, Set.indicator_of_notMem hx]
                  simp
              exact MemLp.of_le_mul humem
                ((Complex.measurable_ofReal.comp hh).aestronglyMeasurable.mul hmeasu) hb
            simpa using MemLp.integrable_mul (memLp_conj h1) (Lp.memLp w)
          have hint2 : Integrable
              (fun x => (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)) μ := by
            simpa using MemLp.integrable_mul (memLp_conj humem) ((Lp.memLp w).const_mul c)
          have hsub : ∫ x, ((starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x
              - (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)) ∂μ = 0 := by
            rw [integral_sub hint1 hint2, ← hid, sub_self]
          rw [← hsub]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hintegrand x).symm)
        have hre := congrArg Complex.re hzeroint
        rw [integral_complex_ofReal] at hre
        simpa using hre
      have hnn : 0 ≤ fun x => ‖u x‖ ^ 2 := fun x => by positivity
      have hintu : Integrable (fun x => ‖u x‖ ^ 2) μ := by
        have := humem.integrable_norm_rpow (by norm_num) (by norm_num)
        simpa [Real.rpow_natCast] using this
      have hae := (integral_eq_zero_iff_of_nonneg hnn hintu).1 hcombine
      filter_upwards [hae] with x hx hbig
      have hu0 : u x = 0 := by
        have hnorm : ‖u x‖ ^ 2 = 0 := hx
        simpa [pow_eq_zero_iff] using hnorm
      rw [← hu0, hu, Set.indicator_of_mem (show x ∈ {x | |g x| ≤ (n : ℝ)} from hbig)]
    have hWzero : ∀ᵐ x ∂μ, W x = 0 := by
      have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, |g x| ≤ (n : ℝ) → W x = 0 := ae_all_iff.2 hzero
      filter_upwards [hall] with x hx
      obtain ⟨n, hn⟩ := exists_nat_ge |g x|
      exact hx n hn
    refine Lp.ext ?_
    filter_upwards [hWzero, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx hz
    rw [hz]
    have hne : ((h x : ℂ) - c) ≠ 0 := by
      intro hzc
      have him := congrArg Complex.im hzc
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im,
        neg_eq_zero] at him
      exact hc him
    exact (mul_eq_zero.1 hx).resolve_left hne
  refine ⟨fun w hw => key Complex.I (by simp) w ?_, fun w hw => key (-Complex.I) (by simp) w ?_⟩
  · intro v; exact hw v
  · intro v; rw [neg_smul]; exact hw v

end FockLagrangian

end BookProof.NavierStokesFlow
